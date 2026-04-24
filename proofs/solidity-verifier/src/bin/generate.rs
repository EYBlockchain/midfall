//! Generate Solidity contracts + fixture files for the poseidon example.
//!
//! Running `cargo run --bin generate` will:
//!   1. Build the SRS, keygen VK/PK, and prove the poseidon circuit using
//!      the Keccak256 transcript.
//!   2. Dump the proof, instance, and execution trace to `fixtures/`.
//!   3. Render `contracts/PoseidonVerifyingKey.sol` with the runtime data.
//!
//! The verifier contract `contracts/PoseidonVerifier.sol` is *not*
//! regenerated — its logic is circuit-agnostic within the constraints baked
//! into the VK blob. Only the VK contract depends on the circuit.

use std::{fs, io::Write, path::PathBuf};

use midnight_curves::Fq;
use midnight_solidity_verifier::{
    codegen::{render_verifying_key, VkInfo},
    eip2537::fq_to_be,
    poseidon_fixture::PoseidonFixture,
};

fn main() {
    let here: PathBuf = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("CARGO_MANIFEST_DIR");
    let fixtures = here.join("fixtures");
    let contracts = here.join("contracts");
    fs::create_dir_all(&fixtures).expect("mkdir fixtures");
    fs::create_dir_all(&contracts).expect("mkdir contracts");

    let k = std::env::var("POSEIDON_K").ok().and_then(|s| s.parse().ok()).unwrap_or(6u32);
    let seed: u64 = std::env::var("POSEIDON_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(1);

    eprintln!("[1/4] building poseidon proof (k={k}, seed={seed})");
    let fx = PoseidonFixture::build(k, seed);

    eprintln!("[2/4] extracting VK info");
    let vk_info = VkInfo::from_live(fx.vk.vk(), &fx.srs);

    eprintln!(
        "      k={} n={} cs_degree={} blinding={}\n      fixed_cols={} perm_cols={} advice_cols={} inst_cols={} challenges={} phases={} simple_sels={}\n      advice_q={} fixed_q={} inst_q={}\n      lookups={} trashcans={} perm_chunks={} quotient_limbs={}\n      proof_size={} bytes",
        vk_info.k, vk_info.n, vk_info.cs_degree, vk_info.blinding_factors,
        vk_info.num_fixed_columns,
        vk_info.num_permutation_columns,
        vk_info.num_advice_columns,
        vk_info.num_instance_columns,
        vk_info.num_challenges,
        vk_info.num_phases,
        vk_info.num_simple_selectors,
        vk_info.num_advice_queries,
        vk_info.num_fixed_queries,
        vk_info.num_instance_queries,
        vk_info.num_lookups,
        vk_info.num_trashcans,
        vk_info.num_permutation_chunks,
        vk_info.num_quotient_limbs,
        fx.proof.len(),
    );

    eprintln!("[3/4] writing Solidity VK contract");
    let sol = render_verifying_key(&vk_info);
    fs::write(contracts.join("PoseidonVerifyingKey.sol"), sol).expect("write sol");

    eprintln!("[4/4] dumping proof + instance");
    fs::write(fixtures.join("proof.bin"), &fx.proof).expect("write proof");
    fs::write(fixtures.join("instance.be"), fq_to_be(&fx.instance)).expect("write instance");

    // Also dump the VK blob separately so tests don't have to deploy the VK
    // contract when they just want to cross-check the byte layout.
    let mut blob = Vec::new();
    write_vk_blob(&vk_info, &mut blob);
    fs::write(fixtures.join("vk.bin"), blob).expect("write vk blob");

    // Also dump compressed bytes of the G1 identity for the Solidity side
    // to consume (instead of hard-coding 0xc0 || zeros and hoping the
    // BLS encoding matches).
    {
        use group::{Group, GroupEncoding};
        let id: midnight_curves::G1Projective =
            <midnight_curves::G1Projective as Group>::identity();
        let b = <midnight_curves::G1Projective as GroupEncoding>::to_bytes(&id);
        fs::write(fixtures.join("identity_g1_compressed.bin"), b.as_ref()).unwrap();
        eprintln!(
            "      G1 identity compressed = 0x{}",
            hex::encode(b.as_ref())
        );
    }

    // Emit algebra-primitive fixtures so the forge test can unit-test the
    // Solidity Fr/Lagrange/interpolation helpers against blst/midnight-
    // proofs before relying on them from the full verifier.
    //
    // File layout (big-endian, all scalars 32 bytes):
    //   fixtures/algebra_fixtures.bin:
    //       [0  .. 32)   omega
    //       [32 .. 64)   n (as an Fr element)
    //       [64 .. 96)   x  (random challenge)
    //       [96 ..128)   xn = x^n
    //       [128..160)   a  (random Fr)
    //       [160..192)   a_inv
    //       [192..224)   nb_lagrange_evals N (uint256 BE)
    //       [224.. ... ) L_0(x), L_1(x), ..., L_{N-1}(x)  (32 bytes each)
    {
        use ff::{Field, PrimeField};
        let domain = fx.vk.vk().get_domain();
        let omega = domain.get_omega();
        let n: u64 = vk_info.n;
        let n_fq = Fq::from(n);
        // Use a deterministic "random" x challenge independent of the proof
        // (constants chosen to match a future forge test fixture).
        let x_bytes: [u8; 32] = [
            0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,
            0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x01,
            0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,
            0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,
        ];
        let x = {
            let mut le = x_bytes;
            le.reverse();
            Fq::from_repr(le).unwrap()
        };
        let xn = x.pow_vartime([n]);

        let a = Fq::from(0x1234_5678_9abc_defu64);
        let a_inv = a.invert().unwrap();

        // L_i(x) for i in 0..n (full domain).
        let lagrange_evals: Vec<Fq> =
            domain.l_i_range(x, xn, 0..(n as i32)).iter().copied().collect();

        let mut blob = Vec::new();
        blob.extend_from_slice(&fq_to_be(&omega));
        blob.extend_from_slice(&fq_to_be(&n_fq));
        blob.extend_from_slice(&fq_to_be(&x));
        blob.extend_from_slice(&fq_to_be(&xn));
        blob.extend_from_slice(&fq_to_be(&a));
        blob.extend_from_slice(&fq_to_be(&a_inv));
        // Pad u64 big-endian length to a full 32-byte word MSB-first so that
        // Solidity's `mload` (big-endian uint256) sees the length directly.
        blob.extend_from_slice(&[0u8; 24]);
        blob.extend_from_slice(&(lagrange_evals.len() as u64).to_be_bytes());
        for e in &lagrange_evals { blob.extend_from_slice(&fq_to_be(e)); }
        fs::write(fixtures.join("algebra_fixtures.bin"), &blob).unwrap();
        eprintln!(
            "      algebra fixtures written ({} bytes, {} Lagrange evals)",
            blob.len(),
            lagrange_evals.len(),
        );
    }

    // Emit the gate-expression bytecode fixture. For every polynomial of
    // every gate in the ConstraintSystem, encode the expression tree as
    // compact RPN bytecode and evaluate it against a deterministic
    // environment. The Solidity test loads this file and runs its own
    // bytecode interpreter, asserting byte-for-byte that its result
    // matches the Rust-computed value.
    //
    // File layout (all 32-byte values BE):
    //   [ 0.. 32)  x           (same as algebra fixture for consistency)
    //   [32.. 64)  beta        = Fq::from(500)
    //   [64.. 96)  gamma       = Fq::from(501)
    //   [96..128)  theta       = Fq::from(502)
    //   [128..160) trash       = Fq::from(503)
    //   [160..192) l_0         = Fq::from(700)
    //   [192..224) l_last      = Fq::from(701)
    //   [224..256) l_blind     = Fq::from(702)
    //   [256..288) nFixed (u256 BE)
    //     [..]     fe[0], fe[1], ...
    //   [     ]    nAdvice   (u256 BE) + ae[...]
    //   [     ]    nInstance (u256 BE) + ie[...]
    //   [     ]    nChallenge(u256 BE) + ch[...]
    //   [     ]    nGates    (u256 BE)
    //     for each gate polynomial:
    //       u256 BE bytecode_len
    //       bytecode
    //       32 bytes expected value BE
    {
        use ff::{Field, PrimeField};
        use midnight_solidity_verifier::expr_bytecode::{encode_expression, eval_bytecode, OP_FIXED, OP_ADVICE, OP_INSTANCE, OP_CHALLENGE, OP_L_0, OP_L_LAST, OP_L_BLIND, OP_BETA, OP_GAMMA, OP_THETA, OP_TRASH, OP_X};
        let vk_inner = fx.vk.vk();
        let cs = vk_inner.cs();

        // Deterministic env.
        let x_bytes: [u8; 32] = [
            0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,
            0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x01,
            0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,
            0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,
        ];
        let x = { let mut le = x_bytes; le.reverse(); Fq::from_repr(le).unwrap() };
        let beta = Fq::from(500u64);
        let gamma = Fq::from(501u64);
        let theta = Fq::from(502u64);
        let trash = Fq::from(503u64);
        let l_0 = Fq::from(700u64);
        let l_last = Fq::from(701u64);
        let l_blind = Fq::from(702u64);

        let n_fixed = cs.num_fixed_columns();
        let n_advice = cs.advice_queries().len();
        let n_instance = cs.instance_queries().len();
        let n_challenges = cs.num_challenges();

        let fixed_evals: Vec<Fq> = (0..n_fixed)
            .map(|i| if cs.has_simple_selector_col(i) { Fq::ONE } else { Fq::from(200u64 + i as u64) })
            .collect();
        let advice_evals: Vec<Fq> = (0..n_advice).map(|i| Fq::from(100u64 + i as u64)).collect();
        let instance_evals: Vec<Fq> = (0..n_instance).map(|i| Fq::from(300u64 + i as u64)).collect();
        let challenges: Vec<Fq> = (0..n_challenges).map(|i| Fq::from(400u64 + i as u64)).collect();

        let mut blob: Vec<u8> = Vec::new();
        let mut push_fq = |blob: &mut Vec<u8>, v: &Fq| { blob.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |blob: &mut Vec<u8>, v: u64| {
            blob.extend_from_slice(&[0u8; 24]);
            blob.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &x);
        push_fq(&mut blob, &beta);
        push_fq(&mut blob, &gamma);
        push_fq(&mut blob, &theta);
        push_fq(&mut blob, &trash);
        push_fq(&mut blob, &l_0);
        push_fq(&mut blob, &l_last);
        push_fq(&mut blob, &l_blind);

        push_u256(&mut blob, n_fixed as u64);
        for v in &fixed_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, n_advice as u64);
        for v in &advice_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, n_instance as u64);
        for v in &instance_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, n_challenges as u64);
        for v in &challenges { push_fq(&mut blob, v); }

        // Gates.
        let all_polys: Vec<&midnight_proofs::plonk::Expression<Fq>> =
            cs.gates().iter().flat_map(|g| g.polynomials().iter()).collect();

        push_u256(&mut blob, all_polys.len() as u64);

        let lookup = |op: u8, idx: u16| -> Fq {
            let i = idx as usize;
            match op {
                OP_FIXED => fixed_evals[i],
                OP_ADVICE => advice_evals[i],
                OP_INSTANCE => instance_evals[i],
                OP_CHALLENGE => challenges[i],
                _ => unreachable!(),
            }
        };
        let special = |op: u8| -> Fq {
            match op {
                OP_L_0 => l_0,
                OP_L_LAST => l_last,
                OP_L_BLIND => l_blind,
                OP_BETA => beta,
                OP_GAMMA => gamma,
                OP_THETA => theta,
                OP_TRASH => trash,
                OP_X => x,
                _ => unreachable!(),
            }
        };

        for poly in &all_polys {
            let bc = encode_expression(poly);
            // Sanity-check: bytecode-evaluated value must equal native.
            let (v_bc, consumed) = eval_bytecode(&bc, &lookup, &special);
            assert_eq!(consumed, bc.len(), "bytecode not fully consumed");
            let v_native = poly.evaluate(
                &|c| c,
                &|_| panic!("selector"),
                &|q| fixed_evals[q.index().unwrap()],
                &|q| advice_evals[q.index.unwrap()],
                &|q| instance_evals[q.index.unwrap()],
                &|ch| challenges[ch.index()],
                &|a| -a, &|a, b| a + b, &|a, b| a * b, &|a, k| a * k,
            );
            assert_eq!(v_bc, v_native, "bytecode != native for a gate polynomial");

            push_u256(&mut blob, bc.len() as u64);
            blob.extend_from_slice(&bc);
            push_fq(&mut blob, &v_native);
        }

        fs::write(fixtures.join("gate_eval_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      gate eval fixture written ({} bytes, {} gate polys, {} fixed/{} advice/{} instance/{} challenge)",
            blob.len(),
            all_polys.len(),
            n_fixed, n_advice, n_instance, n_challenges,
        );
    }

    // Emit the permutation-expressions fixture. Replicates the logic of
    // `midnight_proofs::plonk::permutation::expressions` (which is
    // pub(in crate::plonk), not accessible to external callers) using
    // deterministic inputs, and dumps both the inputs + the 7 expression
    // outputs that the poseidon circuit produces (1 first-set + 1
    // last-set + 2 cross-boundary + 3 main-chunk).
    //
    // File layout (all 32-byte values BE):
    //   [0..32)    beta
    //   [32..64)   gamma
    //   [64..96)   x
    //   [96..128)  l_0
    //   [128..160) l_last
    //   [160..192) l_blind
    //   [192..224) DELTA (for cross-check with Solidity's hardcoded constant)
    //   [224..256) num_chunks (u256 BE)
    //     for each chunk i in 0..num_chunks:
    //       32 bytes: prod_eval
    //       32 bytes: next_eval
    //       32 bytes: last_eval (zero if None)
    //       1 byte:   has_last (0 or 1)
    //       31 bytes: padding
    //   [..]       num_perm_evals (u256 BE)
    //     [..]     perm_eval × n
    //   [..]       num_advice_evals (u256 BE)
    //     [..]     advice_eval × n
    //   [..]       num_fixed_evals (u256 BE)
    //     [..]     fixed_eval × n
    //   [..]       num_instance_evals (u256 BE)
    //     [..]     instance_eval × n
    //   [..]       num_expressions (u256 BE)
    //     [..]     expression × n  (Rust-computed expected values)
    {
        use ff::{Field, PrimeField};
        let vk_inner = fx.vk.vk();
        let cs = vk_inner.cs();
        use midnight_proofs::plonk::Any;
        use midnight_proofs::poly::Rotation;

        let perm_columns = cs.permutation().get_columns();
        let chunk_len = cs.degree() - 2;
        let n_perm_cols = perm_columns.len();
        let n_chunks = (n_perm_cols + chunk_len - 1) / chunk_len;
        let n_advice = cs.advice_queries().len();
        let n_fixed = cs.num_fixed_columns();
        let n_instance = cs.instance_queries().len();

        // Deterministic synthetic env.
        let beta = Fq::from(500u64);
        let gamma = Fq::from(501u64);
        let x = Fq::from(1337u64);
        let l_0 = Fq::from(700u64);
        let l_last = Fq::from(701u64);
        let l_blind = Fq::from(702u64);

        // One prod/next/last triple per chunk. Last chunk has no
        // `permutation_product_last_eval` (its "next" set doesn't exist).
        struct EvSet { prod: Fq, next: Fq, last: Option<Fq> }
        let sets: Vec<EvSet> = (0..n_chunks)
            .map(|i| EvSet {
                prod: Fq::from(1000u64 + i as u64 * 10),
                next: Fq::from(1001u64 + i as u64 * 10),
                last: if i + 1 < n_chunks { Some(Fq::from(1002u64 + i as u64 * 10)) } else { None },
            })
            .collect();

        let perm_evals: Vec<Fq> = (0..n_perm_cols).map(|i| Fq::from(2000u64 + i as u64)).collect();
        let advice_evals: Vec<Fq> = (0..n_advice).map(|i| Fq::from(100u64 + i as u64)).collect();
        let fixed_evals: Vec<Fq> = (0..n_fixed)
            .map(|i| if cs.has_simple_selector_col(i) { Fq::ONE } else { Fq::from(200u64 + i as u64) })
            .collect();
        let instance_evals: Vec<Fq> = (0..n_instance).map(|i| Fq::from(300u64 + i as u64)).collect();

        // Replica of `permutation::expressions`. See
        //   /Users/Julien.Coolen/midfall/proofs/src/plonk/permutation.rs:180+
        // for the authoritative Rust source.
        let eval_col = |column: &midnight_proofs::plonk::Column<Any>| -> Fq {
            match column.column_type() {
                Any::Advice(_) => {
                    let q = cs.advice_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).expect("advice cur");
                    advice_evals[q]
                }
                Any::Fixed => {
                    let q = cs.fixed_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).expect("fixed cur");
                    fixed_evals[q]
                }
                Any::Instance => {
                    let q = cs.instance_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).expect("instance cur");
                    instance_evals[q]
                }
            }
        };

        let mut expressions: Vec<Fq> = Vec::new();
        // First set constraint: l_0 * (1 - z_0.prod_eval)
        if let Some(first) = sets.first() {
            expressions.push(l_0 * (Fq::ONE - first.prod));
        }
        // Last set constraint: l_last * (z_l.prod² - z_l.prod)
        if let Some(last) = sets.last() {
            expressions.push((last.prod * last.prod - last.prod) * l_last);
        }
        // Cross-chunk boundary: for each set after the first,
        //   (set.prod - prev.last) * l_0
        for i in 1..n_chunks {
            let prev_last = sets[i - 1].last.expect("non-last chunk has last_eval");
            expressions.push((sets[i].prod - prev_last) * l_0);
        }
        // Main chunk constraints.
        for (chunk_idx, set) in sets.iter().enumerate() {
            let col_start = chunk_idx * chunk_len;
            let col_end = std::cmp::min(col_start + chunk_len, n_perm_cols);
            let cols = &perm_columns[col_start..col_end];
            let pevs = &perm_evals[col_start..col_end];

            let mut left = set.next;
            for (col, pev) in cols.iter().zip(pevs.iter()) {
                left *= eval_col(col) + beta * pev + gamma;
            }
            let mut right = set.prod;
            let mut current_delta = (beta * x) * Fq::DELTA.pow_vartime([(chunk_idx * chunk_len) as u64]);
            for col in cols.iter() {
                right *= eval_col(col) + current_delta + gamma;
                current_delta *= Fq::DELTA;
            }
            expressions.push((left - right) * (Fq::ONE - (l_last + l_blind)));
        }

        // Serialise.
        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &beta);
        push_fq(&mut blob, &gamma);
        push_fq(&mut blob, &x);
        push_fq(&mut blob, &l_0);
        push_fq(&mut blob, &l_last);
        push_fq(&mut blob, &l_blind);
        push_fq(&mut blob, &Fq::DELTA);
        push_u256(&mut blob, n_chunks as u64);
        for set in &sets {
            push_fq(&mut blob, &set.prod);
            push_fq(&mut blob, &set.next);
            push_fq(&mut blob, &set.last.unwrap_or(Fq::ZERO));
            blob.push(if set.last.is_some() { 1 } else { 0 });
            blob.extend_from_slice(&[0u8; 31]);
        }
        push_u256(&mut blob, perm_evals.len() as u64);
        for v in &perm_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, advice_evals.len() as u64);
        for v in &advice_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, fixed_evals.len() as u64);
        for v in &fixed_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, instance_evals.len() as u64);
        for v in &instance_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, expressions.len() as u64);
        for v in &expressions { push_fq(&mut blob, v); }

        fs::write(fixtures.join("perm_expressions_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      perm expressions fixture written ({} bytes, {} expressions, {} chunks, {} cols)",
            blob.len(),
            expressions.len(),
            n_chunks,
            n_perm_cols,
        );
    }

    // Emit the lookup-expressions fixture (Phase A2a). Replicates the
    // algorithm of `logup::Evaluated::expressions`
    // (proofs/src/plonk/logup.rs:400+, pub(in crate::plonk)) using
    // deterministic inputs, and dumps the scalar inputs + the expected
    // sequence of expressions that Solidity's `_lookupExpressions` must
    // reproduce byte-for-byte.
    //
    // File layout (per lookup concatenated, but poseidon has just 1):
    //   [32]  theta        [32] beta      [32] l_0
    //   [32]  l_last       [32] l_blind
    //   [32]  accumulator_eval
    //   [32]  accumulator_next_eval
    //   [32]  multiplicities_eval
    //   [32]  num_helpers (u256 BE)
    //     [32] × num_helpers  helper_evals
    //   [32]  num_advice_evals
    //     [32] × n   advice_evals
    //   [32]  num_fixed_evals
    //     [32] × n   fixed_evals
    //   [32]  num_instance_evals
    //     [32] × n   instance_evals
    //   [32]  num_challenges
    //     [32] × n   challenges
    //   [32]  num_expected
    //     [32] × n   expected  (Rust-computed expressions())
    {
        use ff::{Field, PrimeField};
        let vk_inner = fx.vk.vk();
        let cs = vk_inner.cs();

        // Take the first (and only) lookup. Multi-lookup is handled by
        // re-running this per lookup in production.
        assert_eq!(cs.lookups().len(), 1, "poseidon has a single lookup");
        let batched = &cs.lookups()[0];
        let chunked = batched.chunk_by_degree(cs.degree());
        let input_chunks = chunked.input_expression_chunks();
        let table_exprs = chunked.table_expressions();
        let selector_expr = chunked.selector_expression();
        let n_chunks = input_chunks.len();

        // Deterministic synthetic env (different offsets from perm).
        let theta = Fq::from(800u64);
        let beta = Fq::from(801u64);
        let l_0 = Fq::from(900u64);
        let l_last = Fq::from(901u64);
        let l_blind = Fq::from(902u64);
        let accumulator_eval = Fq::from(3000u64);
        let accumulator_next_eval = Fq::from(3001u64);
        let multiplicities_eval = Fq::from(3002u64);

        let n_advice = cs.advice_queries().len();
        let n_fixed = cs.num_fixed_columns();
        let n_instance = cs.instance_queries().len();
        let n_challenges = cs.num_challenges();

        let advice_evals: Vec<Fq> = (0..n_advice).map(|i| Fq::from(4000u64 + i as u64)).collect();
        let fixed_evals: Vec<Fq> = (0..n_fixed)
            .map(|i| if cs.has_simple_selector_col(i) { Fq::ONE } else { Fq::from(5000u64 + i as u64) })
            .collect();
        let instance_evals: Vec<Fq> = (0..n_instance).map(|i| Fq::from(6000u64 + i as u64)).collect();
        let challenges: Vec<Fq> = (0..n_challenges).map(|i| Fq::from(7000u64 + i as u64)).collect();

        let helper_evals: Vec<Fq> = (0..n_chunks).map(|i| Fq::from(8000u64 + i as u64)).collect();

        // Native Expression<F> evaluation closures.
        let eval_expression = |expr: &midnight_proofs::plonk::Expression<Fq>| -> Fq {
            expr.evaluate(
                &|c| c,
                &|_| panic!("virtual selector"),
                &|q| fixed_evals[q.index().unwrap()],
                &|q| advice_evals[q.index.unwrap()],
                &|q| instance_evals[q.index.unwrap()],
                &|ch| challenges[ch.index()],
                &|a: Fq| -a,
                &|a: Fq, b: Fq| a + b,
                &|a: Fq, b: Fq| a * b,
                &|a: Fq, k: Fq| a * k,
            )
        };

        // compress_expressions: fold-with-theta as in the Rust source.
        let compress_exprs = |exprs: &[midnight_proofs::plonk::Expression<Fq>]| -> Fq {
            exprs.iter().fold(Fq::ZERO, |acc, e| acc * theta + eval_expression(e))
        };

        // Replica of logup::Evaluated::expressions.
        let active_rows = Fq::ONE - (l_last + l_blind);
        let compressed_table = compress_exprs(table_exprs);
        let selector_val = eval_expression(selector_expr);
        let boundary = (l_0 + l_last) * accumulator_eval;

        let mut sum_helpers = Fq::ZERO;
        let mut expected: Vec<Fq> = Vec::new();
        expected.push(boundary);

        for (i, chunk) in input_chunks.iter().enumerate() {
            let helper_eval = helper_evals[i];
            // For each parallel lookup in the chunk:
            //   compress_exprs(lookup_cols) + beta
            let compressed_with_beta: Vec<Fq> = chunk
                .iter()
                .map(|parallel_lookup| compress_exprs(parallel_lookup) + beta)
                .collect();
            let product: Fq = compressed_with_beta.iter().fold(Fq::ONE, |a, b| a * b);
            let sum: Fq = compressed_with_beta
                .iter()
                .map(|f| product * f.invert().unwrap())
                .fold(Fq::ZERO, |a, b| a + b);
            sum_helpers += helper_eval;
            expected.push(helper_eval * product - sum);
        }

        // accumulator_constraint = ((acc_next - acc - sel·Σh)·(t+β) + m)·active_rows
        let acc_constraint = {
            let diff = (accumulator_next_eval - accumulator_eval - selector_val * sum_helpers)
                * (compressed_table + beta)
                + multiplicities_eval;
            diff * active_rows
        };
        expected.push(acc_constraint);

        // Serialise.
        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &theta);
        push_fq(&mut blob, &beta);
        push_fq(&mut blob, &l_0);
        push_fq(&mut blob, &l_last);
        push_fq(&mut blob, &l_blind);
        push_fq(&mut blob, &accumulator_eval);
        push_fq(&mut blob, &accumulator_next_eval);
        push_fq(&mut blob, &multiplicities_eval);
        push_u256(&mut blob, helper_evals.len() as u64);
        for v in &helper_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, advice_evals.len() as u64);
        for v in &advice_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, fixed_evals.len() as u64);
        for v in &fixed_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, instance_evals.len() as u64);
        for v in &instance_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, challenges.len() as u64);
        for v in &challenges { push_fq(&mut blob, v); }
        push_u256(&mut blob, expected.len() as u64);
        for v in &expected { push_fq(&mut blob, v); }

        fs::write(fixtures.join("lookup_expressions_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      lookup expressions fixture written ({} bytes, {} expressions, {} chunks)",
            blob.len(),
            expected.len(),
            n_chunks,
        );
    }

    // Emit the trashcan-expressions fixture (Phase A2b). Replicates
    // `midnight_proofs::plonk::trash::Evaluated::expressions`
    // (proofs/src/plonk/trash.rs:57+, pub(crate)) using deterministic
    // inputs, and dumps the scalar inputs + the expected one-per-
    // trashcan expression that Solidity's `_trashExpressions` must
    // reproduce byte-for-byte.
    //
    // File layout:
    //   [32]  trash_challenge (τ)
    //   [32]  num_trashcans (u256 BE)
    //     [32] × n   trash_eval per trashcan
    //   [32]  num_advice_evals
    //     [32] × n   advice_evals
    //   [32]  num_fixed_evals
    //     [32] × n   fixed_evals
    //   [32]  num_instance_evals
    //     [32] × n   instance_evals
    //   [32]  num_challenges
    //     [32] × n   challenges
    //   [32]  num_expected
    //     [32] × n   expected (Rust-computed expressions)
    {
        use ff::{Field, PrimeField};
        let vk_inner = fx.vk.vk();
        let cs = vk_inner.cs();

        let trashcans = cs.trashcans();
        let n_trash = trashcans.len();

        // Deterministic synthetic env.
        let trash_challenge = Fq::from(950u64);
        let trash_evals: Vec<Fq> =
            (0..n_trash).map(|i| Fq::from(9500u64 + i as u64)).collect();

        let n_advice = cs.advice_queries().len();
        let n_fixed = cs.num_fixed_columns();
        let n_instance = cs.instance_queries().len();
        let n_challenges = cs.num_challenges();

        let advice_evals: Vec<Fq> = (0..n_advice).map(|i| Fq::from(11000u64 + i as u64)).collect();
        let fixed_evals: Vec<Fq> = (0..n_fixed)
            .map(|i| if cs.has_simple_selector_col(i) { Fq::ONE } else { Fq::from(12000u64 + i as u64) })
            .collect();
        let instance_evals: Vec<Fq> = (0..n_instance).map(|i| Fq::from(13000u64 + i as u64)).collect();
        let challenges: Vec<Fq> = (0..n_challenges).map(|i| Fq::from(14000u64 + i as u64)).collect();

        let eval_expression = |expr: &midnight_proofs::plonk::Expression<Fq>| -> Fq {
            expr.evaluate(
                &|c| c,
                &|_| panic!("virtual selector"),
                &|q| fixed_evals[q.index().unwrap()],
                &|q| advice_evals[q.index.unwrap()],
                &|q| instance_evals[q.index.unwrap()],
                &|ch| challenges[ch.index()],
                &|a: Fq| -a,
                &|a: Fq, b: Fq| a + b,
                &|a: Fq, b: Fq| a * b,
                &|a: Fq, k: Fq| a * k,
            )
        };

        // Replica of trash::Evaluated::expressions.
        let mut expected: Vec<Fq> = Vec::new();
        for (i, arg) in trashcans.iter().enumerate() {
            let compressed_constraints = arg
                .constraint_expressions()
                .iter()
                .map(&eval_expression)
                .fold(Fq::ZERO, |acc, eval| acc * trash_challenge + eval);
            let q = eval_expression(arg.selector());
            let expr = compressed_constraints - (Fq::ONE - q) * trash_evals[i];
            expected.push(expr);
        }

        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &trash_challenge);
        push_u256(&mut blob, trash_evals.len() as u64);
        for v in &trash_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, advice_evals.len() as u64);
        for v in &advice_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, fixed_evals.len() as u64);
        for v in &fixed_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, instance_evals.len() as u64);
        for v in &instance_evals { push_fq(&mut blob, v); }
        push_u256(&mut blob, challenges.len() as u64);
        for v in &challenges { push_fq(&mut blob, v); }
        push_u256(&mut blob, expected.len() as u64);
        for v in &expected { push_fq(&mut blob, v); }

        fs::write(fixtures.join("trashcan_expressions_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      trashcan expressions fixture written ({} bytes, {} expressions, {} trashcans)",
            blob.len(),
            expected.len(),
            n_trash,
        );
    }

    // Emit the `partially_evaluate_identities` full-driver fixture
    // (Phase A3). This uses the SAME deterministic synthetic env as
    // the four component fixtures but concatenates their outputs in
    // the canonical Rust order (gates → perm → lookup → trash) and
    // annotates each with the selector column that
    // `partially_evaluate_identities` pairs it with.
    //
    // File layout (all 32-byte BE unless noted):
    //   [32] x     [32] β   [32] γ   [32] θ   [32] τ
    //   [32] l_0   [32] lLast  [32] lBlind
    //   u256 | advice_evals
    //   u256 | fixed_evals
    //   u256 | instance_evals
    //   u256 | challenges
    //   # perm bits:
    //   u256 num_perm_chunks
    //     per chunk: 32B prod + 32B next + 32B last + 1B hasLast + 31B pad
    //   u256 | perm_evals
    //   # lookup bits (for the single poseidon lookup):
    //   [32] accumulator_eval
    //   [32] accumulator_next_eval
    //   [32] multiplicities_eval
    //   u256 | helper_evals
    //   # trash bits:
    //   u256 | trash_evals  (per trashcan)
    //   # expected:
    //   u256 num_expected
    //     per expected: 4B selector_idx (0xFFFFFFFF = None) + 32B scalar
    {
        use ff::{Field, PrimeField};
        let vk_inner = fx.vk.vk();
        let cs = vk_inner.cs();
        use midnight_proofs::plonk::Any;
        use midnight_proofs::poly::Rotation;

        // Single shared deterministic env (numerically distinct from
        // the 4 component fixtures to catch env-leak bugs).
        let x = Fq::from(1111u64);
        let beta = Fq::from(2222u64);
        let gamma = Fq::from(3333u64);
        let theta = Fq::from(4444u64);
        let trash_challenge = Fq::from(5555u64);
        let l_0 = Fq::from(6666u64);
        let l_last = Fq::from(7777u64);
        let l_blind = Fq::from(8888u64);

        let n_advice = cs.advice_queries().len();
        let n_fixed = cs.num_fixed_columns();
        let n_instance = cs.instance_queries().len();
        let n_challenges = cs.num_challenges();

        let advice_evals: Vec<Fq> = (0..n_advice).map(|i| Fq::from(10000u64 + i as u64)).collect();
        let fixed_evals: Vec<Fq> = (0..n_fixed)
            .map(|i| if cs.has_simple_selector_col(i) { Fq::ONE } else { Fq::from(20000u64 + i as u64) })
            .collect();
        let instance_evals: Vec<Fq> = (0..n_instance).map(|i| Fq::from(30000u64 + i as u64)).collect();
        let challenges: Vec<Fq> = (0..n_challenges).map(|i| Fq::from(40000u64 + i as u64)).collect();

        // ---- Permutation env ----
        let perm_columns = cs.permutation().get_columns();
        let perm_chunk_len = cs.degree() - 2;
        let n_perm_cols = perm_columns.len();
        let n_perm_chunks = (n_perm_cols + perm_chunk_len - 1) / perm_chunk_len;

        struct PSet { prod: Fq, next: Fq, last: Option<Fq> }
        let perm_sets: Vec<PSet> = (0..n_perm_chunks)
            .map(|i| PSet {
                prod: Fq::from(50000u64 + i as u64 * 10),
                next: Fq::from(50001u64 + i as u64 * 10),
                last: if i + 1 < n_perm_chunks { Some(Fq::from(50002u64 + i as u64 * 10)) } else { None },
            })
            .collect();
        let perm_evals: Vec<Fq> = (0..n_perm_cols).map(|i| Fq::from(60000u64 + i as u64)).collect();

        // ---- Lookup env (poseidon has one) ----
        let n_lookups = cs.lookups().len();
        assert_eq!(n_lookups, 1, "driver fixture assumes one lookup");
        let lk_arg = &cs.lookups()[0];
        let lk_chunked = lk_arg.chunk_by_degree(cs.degree());
        let n_lk_chunks = lk_chunked.input_expression_chunks().len();
        let accumulator_eval = Fq::from(70001u64);
        let accumulator_next_eval = Fq::from(70002u64);
        let multiplicities_eval = Fq::from(70003u64);
        let helper_evals: Vec<Fq> = (0..n_lk_chunks).map(|i| Fq::from(80000u64 + i as u64)).collect();

        // ---- Trashcan env ----
        let trashcans = cs.trashcans();
        let n_trash = trashcans.len();
        let trash_evals: Vec<Fq> = (0..n_trash).map(|i| Fq::from(90000u64 + i as u64)).collect();

        // -------------------- Replica --------------------
        let eval_expression = |expr: &midnight_proofs::plonk::Expression<Fq>| -> Fq {
            expr.evaluate(
                &|c| c,
                &|_| panic!("virtual selector"),
                &|q| fixed_evals[q.index().unwrap()],
                &|q| advice_evals[q.index.unwrap()],
                &|q| instance_evals[q.index.unwrap()],
                &|ch| challenges[ch.index()],
                &|a: Fq| -a,
                &|a: Fq, b: Fq| a + b,
                &|a: Fq, b: Fq| a * b,
                &|a: Fq, k: Fq| a * k,
            )
        };

        let mut expected: Vec<(Option<u32>, Fq)> = Vec::new();

        // 1. Gate polynomials.
        for gate in cs.gates().iter() {
            let sel = gate.queried_selectors().iter().find(|s| s.is_simple()).map(|s| s.index() as u32);
            for poly in gate.polynomials().iter() {
                let v = eval_expression(poly);
                expected.push((sel, v));
            }
        }

        // 2. Permutation.
        let eval_col = |column: &midnight_proofs::plonk::Column<Any>| -> Fq {
            match column.column_type() {
                Any::Advice(_) => {
                    let q = cs.advice_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).unwrap();
                    advice_evals[q]
                }
                Any::Fixed => {
                    let q = cs.fixed_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).unwrap();
                    fixed_evals[q]
                }
                Any::Instance => {
                    let q = cs.instance_queries().iter().position(|(c, rot)| {
                        c.index() == column.index() && rot.0 == Rotation::cur().0
                    }).unwrap();
                    instance_evals[q]
                }
            }
        };
        if let Some(first) = perm_sets.first() {
            expected.push((None, l_0 * (Fq::ONE - first.prod)));
        }
        if let Some(last) = perm_sets.last() {
            expected.push((None, (last.prod * last.prod - last.prod) * l_last));
        }
        for i in 1..n_perm_chunks {
            let prev_last = perm_sets[i - 1].last.unwrap();
            expected.push((None, (perm_sets[i].prod - prev_last) * l_0));
        }
        for (chunk_idx, set) in perm_sets.iter().enumerate() {
            let col_start = chunk_idx * perm_chunk_len;
            let col_end = std::cmp::min(col_start + perm_chunk_len, n_perm_cols);
            let cols = &perm_columns[col_start..col_end];
            let pevs = &perm_evals[col_start..col_end];

            let mut left = set.next;
            for (col, pev) in cols.iter().zip(pevs.iter()) {
                left *= eval_col(col) + beta * pev + gamma;
            }
            let mut right = set.prod;
            let mut current_delta = (beta * x) * Fq::DELTA.pow_vartime([(chunk_idx * perm_chunk_len) as u64]);
            for col in cols.iter() {
                right *= eval_col(col) + current_delta + gamma;
                current_delta *= Fq::DELTA;
            }
            expected.push((None, (left - right) * (Fq::ONE - (l_last + l_blind))));
        }

        // 3. Lookup.
        let compress_exprs = |exprs: &[midnight_proofs::plonk::Expression<Fq>]| -> Fq {
            exprs.iter().fold(Fq::ZERO, |acc, e| acc * theta + eval_expression(e))
        };
        let active_rows = Fq::ONE - (l_last + l_blind);
        let compressed_table = compress_exprs(lk_chunked.table_expressions());
        let selector_val = eval_expression(lk_chunked.selector_expression());
        expected.push((None, (l_0 + l_last) * accumulator_eval));
        let mut sum_helpers = Fq::ZERO;
        for (i, chunk) in lk_chunked.input_expression_chunks().iter().enumerate() {
            let helper_eval = helper_evals[i];
            let cwb: Vec<Fq> = chunk.iter().map(|pl| compress_exprs(pl) + beta).collect();
            let product: Fq = cwb.iter().fold(Fq::ONE, |a, b| a * b);
            let sum: Fq = cwb.iter().map(|f| product * f.invert().unwrap()).fold(Fq::ZERO, |a, b| a + b);
            sum_helpers += helper_eval;
            expected.push((None, helper_eval * product - sum));
        }
        let diff = (accumulator_next_eval - accumulator_eval - selector_val * sum_helpers)
            * (compressed_table + beta)
            + multiplicities_eval;
        expected.push((None, diff * active_rows));

        // 4. Trashcan.
        for (i, arg) in trashcans.iter().enumerate() {
            let compressed = arg.constraint_expressions().iter().map(&eval_expression)
                .fold(Fq::ZERO, |acc, e| acc * trash_challenge + e);
            let q = eval_expression(arg.selector());
            expected.push((None, compressed - (Fq::ONE - q) * trash_evals[i]));
        }

        // -------------------- Serialise --------------------
        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]); b.extend_from_slice(&v.to_be_bytes());
        };
        let push_arr = |b: &mut Vec<u8>, arr: &[Fq]| {
            push_u256(b, arr.len() as u64);
            for v in arr { push_fq(b, v); }
        };

        push_fq(&mut blob, &x);
        push_fq(&mut blob, &beta);
        push_fq(&mut blob, &gamma);
        push_fq(&mut blob, &theta);
        push_fq(&mut blob, &trash_challenge);
        push_fq(&mut blob, &l_0);
        push_fq(&mut blob, &l_last);
        push_fq(&mut blob, &l_blind);
        push_arr(&mut blob, &advice_evals);
        push_arr(&mut blob, &fixed_evals);
        push_arr(&mut blob, &instance_evals);
        push_arr(&mut blob, &challenges);

        push_u256(&mut blob, perm_sets.len() as u64);
        for set in &perm_sets {
            push_fq(&mut blob, &set.prod);
            push_fq(&mut blob, &set.next);
            push_fq(&mut blob, &set.last.unwrap_or(Fq::ZERO));
            blob.push(if set.last.is_some() { 1 } else { 0 });
            blob.extend_from_slice(&[0u8; 31]);
        }
        push_arr(&mut blob, &perm_evals);

        push_fq(&mut blob, &accumulator_eval);
        push_fq(&mut blob, &accumulator_next_eval);
        push_fq(&mut blob, &multiplicities_eval);
        push_arr(&mut blob, &helper_evals);

        push_arr(&mut blob, &trash_evals);

        push_u256(&mut blob, expected.len() as u64);
        for (sel, v) in &expected {
            let sel_be = sel.unwrap_or(0xFFFFFFFFu32);
            blob.extend_from_slice(&sel_be.to_be_bytes());
            push_fq(&mut blob, v);
        }

        fs::write(fixtures.join("partial_eval_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      partial-eval driver fixture written ({} bytes, {} scalars, {} with selector)",
            blob.len(),
            expected.len(),
            expected.iter().filter(|(s, _)| s.is_some()).count(),
        );

        // Phase B: compute_linearization_commitment fixture.
        // Replicates the Rust algorithm (linearization/verifier.rs:45+)
        // using the SAME `expected` (selector_idx, eval) pairs we
        // just computed and a deterministic y/xn/splitting_factor.
        //
        // File layout:
        //   [32]  y
        //   [32]  xn
        //   [32]  splitting_factor
        //   [32]  num_quotient_limbs
        //     [128 × n]  quotient_limb commitments (EIP-2537)
        //   [32]  num_identity_scalars
        //   for each: 4B selector + 32B scalar  (≡ partial_eval_fixture
        //     tail; duplicated here so the forge test doesn't have to
        //     cross-load)
        //   [32]  num_output_points
        //     [128 × n]  output points (EIP-2537)
        //     [32 × n]   output scalars
        //   [32]  expected_eval
        use std::collections::BTreeMap;
        use group::Group;
        let y = Fq::from(987u64);
        let xn_val = Fq::from(654u64);
        let splitting_factor = Fq::from(321u64);

        let num_limbs = vk_info.num_quotient_limbs;
        // Deterministic G1 points for quotient-limb commitments.
        let gen = <midnight_curves::G1Projective as Group>::generator();
        let quotient_limbs: Vec<midnight_curves::G1Projective> =
            (0..num_limbs).map(|i| gen * Fq::from(9000u64 + i as u64)).collect();

        // Replica of compute_linearization_commitment.
        let mut identities_scalars: Vec<Fq> = Vec::new();
        let mut identities_points: Vec<midnight_curves::G1Projective> = Vec::new();
        let mut splitting_pow = Fq::ONE - xn_val;
        for q in &quotient_limbs {
            identities_scalars.push(splitting_pow);
            identities_points.push(*q);
            splitting_pow *= splitting_factor;
        }

        // Group by selector (None < Some(a) < Some(b) for a<b).
        let mut grouped: BTreeMap<Option<usize>, Fq> = BTreeMap::new();
        let mut y_pow = Fq::ONE;
        for (col_idx, eval) in expected.iter().rev() {
            let key = col_idx.map(|c| c as usize);
            *grouped.entry(key).or_insert(Fq::ZERO) += y_pow * eval;
            y_pow *= y;
        }

        let mut expected_eval = Fq::ZERO;
        for (col_idx, eval) in grouped.into_iter() {
            match col_idx {
                Some(c) => {
                    let comm: midnight_curves::G1Projective =
                        vk_inner.fixed_commitments()[c].into();
                    identities_points.push(comm);
                    identities_scalars.push(eval);
                }
                None => { expected_eval -= eval; }
            }
        }

        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &y);
        push_fq(&mut blob, &xn_val);
        push_fq(&mut blob, &splitting_factor);
        push_u256(&mut blob, num_limbs as u64);
        for q in &quotient_limbs {
            blob.extend_from_slice(
                &midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(q),
            );
        }

        // Identity scalars (mirrors partial_eval_fixture tail):
        push_u256(&mut blob, expected.len() as u64);
        for (sel, v) in &expected {
            let sel_be = sel.unwrap_or(0xFFFFFFFFu32);
            blob.extend_from_slice(&sel_be.to_be_bytes());
            push_fq(&mut blob, v);
        }

        push_u256(&mut blob, identities_points.len() as u64);
        for p in &identities_points {
            blob.extend_from_slice(
                &midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(p),
            );
        }
        for s in &identities_scalars { push_fq(&mut blob, s); }
        push_fq(&mut blob, &expected_eval);

        fs::write(fixtures.join("linearization_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      linearization fixture written ({} bytes, {} quotient limbs, {} output points)",
            blob.len(),
            num_limbs,
            identities_points.len(),
        );

        // Phase C1: query-schedule fixture.
        // Dump each distinct rotation's expected `ω^at · x` for a
        // deterministic x, so the forge test can verify that the
        // Solidity rotation helper produces identical values.
        //
        // File layout:
        //   [32]  x
        //   [32]  num_distinct_rotations
        //     per rotation:
        //       [4]  i32 rotation
        //       [32] expected ω^rotation · x
        //   [32] num_advice_queries
        //     [1] rotation_idx × n
        //   [32] num_fixed_queries
        //     [1] rotation_idx × n
        //   [32] num_instance_queries
        //     [1] rotation_idx × n
        let x_rot = Fq::from(7777u64);
        let omega = vk_inner.get_domain().get_omega();

        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };

        push_fq(&mut blob, &x_rot);
        push_u256(&mut blob, vk_info.distinct_rotations.len() as u64);
        for &r in &vk_info.distinct_rotations {
            blob.extend_from_slice(&(r as u32).to_be_bytes());
            // ω^r · x: use positive pow for positive r, inverse-ω pow for negative.
            let rotated = if r == 0 {
                x_rot
            } else if r > 0 {
                x_rot * omega.pow_vartime([r as u64])
            } else {
                let inv_omega = omega.invert().unwrap();
                x_rot * inv_omega.pow_vartime([(-r) as u64])
            };
            push_fq(&mut blob, &rotated);
        }
        push_u256(&mut blob, vk_info.advice_query_rotation_idx.len() as u64);
        blob.extend_from_slice(&vk_info.advice_query_rotation_idx);
        push_u256(&mut blob, vk_info.fixed_query_rotation_idx.len() as u64);
        blob.extend_from_slice(&vk_info.fixed_query_rotation_idx);
        push_u256(&mut blob, vk_info.instance_query_rotation_idx.len() as u64);
        blob.extend_from_slice(&vk_info.instance_query_rotation_idx);

        fs::write(fixtures.join("query_schedule_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      query schedule fixture written ({} bytes, {} rotations, {}/{}/{} queries a/f/i)",
            blob.len(),
            vk_info.distinct_rotations.len(),
            vk_info.advice_query_rotation_idx.len(),
            vk_info.fixed_query_rotation_idx.len(),
            vk_info.instance_query_rotation_idx.len(),
        );

        // Phase C2 (step 1): Lagrange + Horner f_eval fold fixture.
        //
        // The Rust verifier's `multi_prepare` computes, after
        // multi-open batching, a scalar `f_eval` by reverse-folding
        // over all point sets (proofs/src/poly/kzg/mod.rs:330-340):
        //
        //   acc = 0
        //   for (points, evals, proof_eval) in zip(..).rev():
        //       r_eval = eval(lagrange_interp(points, evals), x3)
        //       den    = ∏(x3 − point_j)
        //       eval_i = (proof_eval − r_eval) / den
        //       acc    = acc · x2 + eval_i
        //
        // Fixture layout (all 32B BE unless noted):
        //   [32] x2   [32] x3
        //   [32] num_sets  (u256)
        //     per set:
        //       [32] m (size of the point set)
        //       [32] × m   points
        //       [32] × m   evals
        //       [32]       proof_eval
        //   [32] expected_f_eval
        let x2 = Fq::from(2024u64);
        let x3 = Fq::from(2025u64);
        // Synthetic heterogeneous point sets to exercise multi-size
        // scenarios (the poseidon proof's actual point sets have
        // sizes 1, 1, 1, 2 — Lagrange interp reduces to identity on
        // singletons but still exercises the denominator product).
        let sets: Vec<(Vec<Fq>, Vec<Fq>, Fq)> = vec![
            (
                vec![Fq::from(11u64)],
                vec![Fq::from(101u64)],
                Fq::from(1001u64),
            ),
            (
                vec![Fq::from(22u64), Fq::from(33u64)],
                vec![Fq::from(202u64), Fq::from(303u64)],
                Fq::from(2002u64),
            ),
            (
                vec![Fq::from(44u64), Fq::from(55u64), Fq::from(66u64)],
                vec![Fq::from(404u64), Fq::from(505u64), Fq::from(606u64)],
                Fq::from(3003u64),
            ),
        ];
        let lagrange_interp_at_x3 = |points: &[Fq], evals: &[Fq]| -> Fq {
            let n = points.len();
            let mut result = Fq::ZERO;
            for i in 0..n {
                let mut num = Fq::ONE;
                let mut den = Fq::ONE;
                for j in 0..n {
                    if i == j { continue; }
                    num *= x3 - points[j];
                    den *= points[i] - points[j];
                }
                result += evals[i] * num * den.invert().unwrap();
            }
            result
        };

        let mut acc = Fq::ZERO;
        for (pts, evs, proof_eval) in sets.iter().rev() {
            let r_eval = lagrange_interp_at_x3(pts, evs);
            let den: Fq = pts.iter().fold(Fq::ONE, |a, p| a * (x3 - p));
            let eval_i = (*proof_eval - r_eval) * den.invert().unwrap();
            acc = acc * x2 + eval_i;
        }

        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };
        push_fq(&mut blob, &x2);
        push_fq(&mut blob, &x3);
        push_u256(&mut blob, sets.len() as u64);
        for (pts, evs, proof_eval) in &sets {
            push_u256(&mut blob, pts.len() as u64);
            for p in pts { push_fq(&mut blob, p); }
            for e in evs { push_fq(&mut blob, e); }
            push_fq(&mut blob, proof_eval);
        }
        push_fq(&mut blob, &acc);

        fs::write(fixtures.join("feval_fold_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      f_eval fold fixture written ({} bytes, {} sets, sizes {:?})",
            blob.len(),
            sets.len(),
            sets.iter().map(|(p, _, _)| p.len()).collect::<Vec<_>>(),
        );

        // Phase C3: pairing-RHS equivalence fixture.
        //
        // Runs the Rust verifier's `prepare` on the full poseidon
        // proof, obtains the resulting DualMSM, evaluates its left
        // and right MSM accumulators to single G1 points, and
        // serialises them as 48-byte compressed encodings (plus
        // their computed EIP-2537 uncompressed 128-byte forms for
        // debugging / cross-check convenience).
        //
        // These two points (together with the VK's s·G2 and −G2)
        // are exactly what the final pairing check consumes:
        //    e(left, s·G2) · e(right, −G2) == 1
        //
        // File layout:
        //   [48] left_compressed
        //   [48] right_compressed
        //   [128] left_eip2537     (optional; for cross-debugging)
        //   [128] right_eip2537
        //   [1]  expected_pairing_ok   (always 0x01 here)
        use group::GroupEncoding;
        use midnight_curves::G1Projective;
        use midnight_proofs::{
            plonk::prepare,
            poly::kzg::KZGCommitmentScheme,
            transcript::{CircuitTranscript, Transcript},
        };

        let mut transcript = CircuitTranscript::<
            sha3::Keccak256,
        >::init_from_bytes(&fx.proof);
        let instance_col: [Fq; 1] = [fx.instance];
        let instance_ref: &[&[Fq]] = &[&instance_col];
        let pis: &[&[&[Fq]]] = &[instance_ref];
        let committed_col: [G1Projective; 1] =
            [<G1Projective as Group>::identity()];
        let committed: &[&[G1Projective]] = &[&committed_col];

        let dual_msm = prepare::<
            Fq,
            KZGCommitmentScheme<midnight_curves::Bls12>,
            CircuitTranscript<sha3::Keccak256>,
        >(
            fx.vk.vk(),
            committed,
            pis,
            &mut transcript,
        )
        .expect("prepare");

        let (left_terms, right_terms) = dual_msm.split();
        let mut left_eval: G1Projective = G1Projective::identity();
        for (_, s, b) in left_terms.iter() {
            left_eval = left_eval + (**b * **s);
        }
        let mut right_eval: G1Projective = G1Projective::identity();
        for (_, s, b) in right_terms.iter() {
            right_eval = right_eval + (**b * **s);
        }

        // Sanity-check via the DualMSM's own `check` method, which wraps
        // the multi-miller-loop + final exponentiation.
        let verifier_params = fx.srs.verifier_params();
        let cloned_dual = dual_msm.clone();
        let ok_rust = cloned_dual.check(&verifier_params);
        assert!(
            ok_rust,
            "Rust-side pairing check should pass on a valid proof",
        );

        let left_compressed =
            <G1Projective as GroupEncoding>::to_bytes(&left_eval);
        let right_compressed =
            <G1Projective as GroupEncoding>::to_bytes(&right_eval);

        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(left_compressed.as_ref());
        blob.extend_from_slice(right_compressed.as_ref());
        blob.push(0x01);
        fs::write(fixtures.join("pairing_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      pairing fixture written ({} bytes, Rust-side check = {})",
            blob.len(),
            ok_rust,
        );

        // Phase C2a: construct_intermediate_sets equivalence fixture.
        //
        // Ports a synthetic (commitment_id, point_value) query list
        // through a faithful Rust replica of
        // `proofs/src/poly/kzg/utils.rs::construct_intermediate_sets`,
        // capturing:
        //   - per-commitment FIFO order + point_indices (query-
        //     insertion order per commitment),
        //   - set_idx per commitment (FIFO dedup of the sorted
        //     point_index set, in commitment-iteration order),
        //   - point_sets[s] = sorted ascending point VALUES of set s.
        //
        // Input layout mimics a poseidon-shaped workload:
        //   3 commitments × 3 rotations cross-product (9 queries),
        //   plus a handful of duplicated commitments queried at
        //   only the "cur" rotation to stress the size-1 set case.
        //
        // File layout:
        //   [4] nQueries
        //     per query: [4] commitment_id, [32] point_value
        //   [4] nCommitments
        //     per commitment:
        //       [4] commitment_id
        //       [4] set_idx
        //       [4] num_point_indices
        //         per: [4] point_idx       (query-insertion order)
        //   [4] nSets
        //     per set:
        //       [4] size
        //         per: [32] point_value    (sorted ascending by
        //                                   point_idx, not by value)
        struct IntermSet {
            commitment_ids: Vec<u32>,
            commitment_set_idx: Vec<u32>,
            commitment_point_idx: Vec<Vec<u32>>,
            point_sets: Vec<Vec<Fq>>, // sorted ascending by point_idx
        }
        fn compute_intermediate_sets(queries: &[(u32, Fq)]) -> IntermSet {
            // FIFO point_value → point_idx.
            let mut unique_points: Vec<Fq> = Vec::new();
            let mut q_pidx: Vec<u32> = Vec::with_capacity(queries.len());
            for (_, pv) in queries {
                let p_idx = match unique_points.iter().position(|p| p == pv) {
                    Some(k) => k,
                    None => {
                        unique_points.push(*pv);
                        unique_points.len() - 1
                    }
                };
                q_pidx.push(p_idx as u32);
            }
            // FIFO commitment dedup + per-commitment point_indices.
            let mut c_ids: Vec<u32> = Vec::new();
            let mut c_pts: Vec<Vec<u32>> = Vec::new();
            for (qi, (cid, _)) in queries.iter().enumerate() {
                let c_pos = match c_ids.iter().position(|c| c == cid) {
                    Some(k) => k,
                    None => {
                        c_ids.push(*cid);
                        c_pts.push(Vec::new());
                        c_ids.len() - 1
                    }
                };
                // Rust's construct_intermediate_sets rejects duplicate
                // (commitment, point) queries. Our fixture uses distinct
                // rotations per query so this never triggers.
                c_pts[c_pos].push(q_pidx[qi]);
            }
            // FIFO set dedup (per sorted point_index set).
            let mut c_set_idx: Vec<u32> = Vec::with_capacity(c_ids.len());
            let mut set_owner: Vec<usize> = Vec::new();
            let mut sorted_sets: Vec<Vec<u32>> = Vec::new();
            for (c, pts) in c_pts.iter().enumerate() {
                let mut sorted = pts.clone();
                sorted.sort();
                let idx = match sorted_sets.iter().position(|s| s == &sorted) {
                    Some(k) => k,
                    None => {
                        sorted_sets.push(sorted.clone());
                        set_owner.push(c);
                        sorted_sets.len() - 1
                    }
                };
                c_set_idx.push(idx as u32);
            }
            // Build point_sets: sorted ascending by point_idx → point_value.
            let mut point_sets: Vec<Vec<Fq>> = Vec::with_capacity(sorted_sets.len());
            for sorted in &sorted_sets {
                let mut ps = Vec::with_capacity(sorted.len());
                for &pi in sorted {
                    ps.push(unique_points[pi as usize]);
                }
                point_sets.push(ps);
            }
            IntermSet {
                commitment_ids: c_ids,
                commitment_set_idx: c_set_idx,
                commitment_point_idx: c_pts,
                point_sets,
            }
        }

        // Synthetic query list shaped like a poseidon verifier would
        // produce: 3 rotations (cur, next, last) × 3 commitments +
        // 3 size-1 queries.
        let p0 = Fq::from(1001u64);
        let p1 = Fq::from(1002u64);
        let p2 = Fq::from(1003u64);
        let queries: Vec<(u32, Fq)> = vec![
            (10, p0), (10, p1), (10, p2),   // commitment 10 at 3 points
            (11, p0), (11, p2),             // commitment 11 at 2 points
            (12, p0),                       // commitment 12 at 1 point (new set)
            (13, p1),                       // commitment 13 at 1 point (new set)
            (14, p0),                       // commitment 14 at 1 point, same set as 12
        ];
        let result = compute_intermediate_sets(&queries);

        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(&(queries.len() as u32).to_be_bytes());
        for (cid, pv) in &queries {
            blob.extend_from_slice(&cid.to_be_bytes());
            blob.extend_from_slice(&fq_to_be(pv));
        }
        blob.extend_from_slice(&(result.commitment_ids.len() as u32).to_be_bytes());
        for (i, cid) in result.commitment_ids.iter().enumerate() {
            blob.extend_from_slice(&cid.to_be_bytes());
            blob.extend_from_slice(&result.commitment_set_idx[i].to_be_bytes());
            let pidx = &result.commitment_point_idx[i];
            blob.extend_from_slice(&(pidx.len() as u32).to_be_bytes());
            for &pi in pidx {
                blob.extend_from_slice(&pi.to_be_bytes());
            }
        }
        blob.extend_from_slice(&(result.point_sets.len() as u32).to_be_bytes());
        for ps in &result.point_sets {
            blob.extend_from_slice(&(ps.len() as u32).to_be_bytes());
            for pv in ps {
                blob.extend_from_slice(&fq_to_be(pv));
            }
        }
        fs::write(fixtures.join("interm_sets_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      intermediate-sets fixture written ({} bytes, {} queries, {} commitments, {} sets)",
            blob.len(),
            queries.len(),
            result.commitment_ids.len(),
            result.point_sets.len(),
        );

        // Phase C2b: per-set x1-inner-product evals fold fixture.
        //
        // Given:
        //   - commitment_set_idx[c] (from C2a),
        //   - per-commitment evals in sorted-set order
        //     (commitment_evals[c][j] = eval at the j-th point in
        //     the sorted point set of the set c belongs to),
        //   - challenge x1,
        // the Rust verifier computes, for each set s:
        //   q_eval_sets[s][j] = Σ_{c ∈ set s, FIFO} x1^{pos_c_in_s} ·
        //                       commitment_evals[c][j]
        // where `pos_c_in_s` is c's iteration position within the
        // FIFO commitment order restricted to set s.
        //
        // Fixture layout:
        //   [4] num_commitments
        //     per commitment: [4] set_idx, [4] evals_len,
        //                     [32] × evals_len per-point evals
        //   [4] x1 offset sentinel (always 0xDEADBEEF for struct boundary)
        //   [32] x1
        //   [4] num_sets
        //     per set:
        //       [4] size
        //         per: [32] expected q_eval_sets[s][j]
        //
        // The commitments here are the same 5-commitment workload
        // from the C2a fixture; evals per commitment are synthetic
        // but deterministic (commit_id * 100 + point_idx).
        use ff::Field as _;
        let x1 = Fq::from(777u64);
        let mut c_evals: Vec<Vec<Fq>> = Vec::with_capacity(result.commitment_ids.len());
        for (c, cid) in result.commitment_ids.iter().enumerate() {
            let set_len = result.point_sets[result.commitment_set_idx[c] as usize].len();
            let mut ev = Vec::with_capacity(set_len);
            for j in 0..set_len {
                ev.push(Fq::from(*cid as u64 * 100u64 + j as u64));
            }
            c_evals.push(ev);
        }
        // Rust replica of the x1 evals fold.
        let n_sets = result.point_sets.len();
        let mut q_evals: Vec<Vec<Fq>> = Vec::with_capacity(n_sets);
        for s in 0..n_sets {
            let set_size = result.point_sets[s].len();
            let mut folded = vec![Fq::ZERO; set_size];
            let mut x1_pow = Fq::ONE;
            // Iterate commitments in FIFO order, picking those in set s.
            for c in 0..result.commitment_ids.len() {
                if result.commitment_set_idx[c] as usize != s {
                    continue;
                }
                for j in 0..set_size {
                    folded[j] += x1_pow * c_evals[c][j];
                }
                x1_pow *= x1;
            }
            q_evals.push(folded);
        }

        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(&(result.commitment_ids.len() as u32).to_be_bytes());
        for c in 0..result.commitment_ids.len() {
            blob.extend_from_slice(&result.commitment_set_idx[c].to_be_bytes());
            blob.extend_from_slice(&(c_evals[c].len() as u32).to_be_bytes());
            for ev in &c_evals[c] {
                blob.extend_from_slice(&fq_to_be(ev));
            }
        }
        blob.extend_from_slice(&0xDEADBEEF_u32.to_be_bytes());
        blob.extend_from_slice(&fq_to_be(&x1));
        blob.extend_from_slice(&(n_sets as u32).to_be_bytes());
        for s in 0..n_sets {
            blob.extend_from_slice(&(q_evals[s].len() as u32).to_be_bytes());
            for e in &q_evals[s] {
                blob.extend_from_slice(&fq_to_be(e));
            }
        }
        fs::write(fixtures.join("x1_evals_fold_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      x1-evals-fold fixture written ({} bytes, {} sets, sizes {:?})",
            blob.len(),
            n_sets,
            q_evals.iter().map(|v| v.len()).collect::<Vec<_>>(),
        );

        // Phase C2c: x4 outer DualMSM fold fixture.
        //
        // Ports the x4-power outer fold from
        // \`KZGCommitmentScheme::multi_prepare\` (kzg/mod.rs:340-410).
        // For each commitment c in FIFO order, its final-right-MSM
        // scalar is
        //   comm_scalar[c] = x4^{setIdx[c]} · x1^{posInSet[c]}
        // where \`posInSet[c]\` is c's FIFO position within set
        // \`setIdx[c]\`. The f_com commitment picks up
        //   f_com_scalar = x4^{nSets}
        // and the DualMSM-assembly terms are
        //   pi_scalar = x3    (for π in the right MSM)
        //   g_scalar  = −v    (for G1 in the right MSM)
        //   v         = Σ_{s<nSets} x4^s · qEvalsOnX3[s] +
        //               x4^{nSets} · f_eval
        //
        // Fixture layout:
        //   [4] num_commitments
        //     per commitment: [4] set_idx, [4] pos_in_set
        //   [4] num_sets
        //   [32] x1  [32] x4  [32] x3  [32] f_eval
        //   per set: [32] qEvalsOnX3[s]
        //   [32] expected_v
        //   per commitment: [32] expected_comm_scalar
        //   [32] expected_f_com_scalar
        //   [32] expected_pi_scalar
        //   [32] expected_g_scalar
        let n_c = result.commitment_ids.len();
        let mut pos_in_set: Vec<u32> = vec![0; n_c];
        let mut set_counters: Vec<u32> = vec![0; n_sets];
        for c in 0..n_c {
            let s = result.commitment_set_idx[c] as usize;
            pos_in_set[c] = set_counters[s];
            set_counters[s] += 1;
        }

        let x4 = Fq::from(333u64);
        let x3_outer = Fq::from(222u64);
        let f_eval = Fq::from(4444u64);
        let q_evals_on_x3: Vec<Fq> = (0..n_sets)
            .map(|s| Fq::from((s as u64 + 1) * 1111))
            .collect();

        // v = Σ x4^s · qEvalsOnX3[s] + x4^nSets · f_eval
        let mut v_scalar = Fq::ZERO;
        let mut x4_pow = Fq::ONE;
        for s in 0..n_sets {
            v_scalar += x4_pow * q_evals_on_x3[s];
            x4_pow *= x4;
        }
        v_scalar += x4_pow * f_eval;
        let f_com_scalar = x4_pow;                  // x4^nSets
        // Per-commitment: x4^{setIdx} · x1^{posInSet}.
        let mut comm_scalars: Vec<Fq> = Vec::with_capacity(n_c);
        for c in 0..n_c {
            let s = result.commitment_set_idx[c] as usize;
            let i = pos_in_set[c] as u64;
            let mut x4_s = Fq::ONE;
            for _ in 0..s { x4_s *= x4; }
            let mut x1_i = Fq::ONE;
            for _ in 0..i { x1_i *= x1; }
            comm_scalars.push(x4_s * x1_i);
        }
        let pi_scalar = x3_outer;
        let g_scalar = -v_scalar;

        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(&(n_c as u32).to_be_bytes());
        for c in 0..n_c {
            blob.extend_from_slice(&result.commitment_set_idx[c].to_be_bytes());
            blob.extend_from_slice(&pos_in_set[c].to_be_bytes());
        }
        blob.extend_from_slice(&(n_sets as u32).to_be_bytes());
        blob.extend_from_slice(&fq_to_be(&x1));
        blob.extend_from_slice(&fq_to_be(&x4));
        blob.extend_from_slice(&fq_to_be(&x3_outer));
        blob.extend_from_slice(&fq_to_be(&f_eval));
        for qe in &q_evals_on_x3 { blob.extend_from_slice(&fq_to_be(qe)); }
        blob.extend_from_slice(&fq_to_be(&v_scalar));
        for sc in &comm_scalars { blob.extend_from_slice(&fq_to_be(sc)); }
        blob.extend_from_slice(&fq_to_be(&f_com_scalar));
        blob.extend_from_slice(&fq_to_be(&pi_scalar));
        blob.extend_from_slice(&fq_to_be(&g_scalar));
        fs::write(fixtures.join("x4_outer_fold_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      x4-outer-fold fixture written ({} bytes, {} commitments, {} sets)",
            blob.len(),
            n_c,
            n_sets,
        );

        // Phase D1: Lagrange-aux (l_0, l_last, l_blind) fixture.
        //
        // Ports proofs/src/plonk/mod.rs:506-513:
        //   l_evals = l_i_range(x, xn, -(bf+1)..=0)
        //   l_last  = l_evals[0]
        //   l_blind = Σ l_evals[1..1+bf]
        //   l_0     = l_evals[1 + bf]
        //
        // Uses a deterministic synthetic x (not the transcript-
        // derived one — Phase D2 will wire that) + the real
        // poseidon circuit's omega, n, blinding_factors so the
        // helper is tested against the exact parameters it will
        // consume inside verify().
        //
        // File layout (all 32B BE unless noted):
        //   [32] x
        //   [32] xn
        //   [32] n (stored as uint256; actual value < 2^64)
        //   [32] omega
        //   [32] blinding_factors (stored as uint256; actual < 2^32)
        //   [32] expected_l_0
        //   [32] expected_l_last
        //   [32] expected_l_blind
        let x_d = Fq::from(0xD1u64);
        let bf = vk_info.blinding_factors as u64;
        let n_d = vk_info.n;
        let omega_d = vk_inner.get_domain().get_omega();
        let xn_d = x_d.pow_vartime([n_d]);
        let domain_d = vk_inner.get_domain();
        let l_evals_d = domain_d.l_i_range(x_d, xn_d, -((bf + 1) as i32)..=0);
        assert_eq!(l_evals_d.len() as u64, 2 + bf);
        let l_last_d = l_evals_d[0];
        let mut l_blind_d = Fq::ZERO;
        for i in 1..=bf as usize {
            l_blind_d += l_evals_d[i];
        }
        let l_0_d = l_evals_d[1 + bf as usize];

        let mut blob: Vec<u8> = Vec::new();
        let push_fq = |b: &mut Vec<u8>, v: &Fq| { b.extend_from_slice(&fq_to_be(v)); };
        let push_u256 = |b: &mut Vec<u8>, v: u64| {
            b.extend_from_slice(&[0u8; 24]);
            b.extend_from_slice(&v.to_be_bytes());
        };
        push_fq(&mut blob, &x_d);
        push_fq(&mut blob, &xn_d);
        push_u256(&mut blob, n_d);
        push_fq(&mut blob, &omega_d);
        push_u256(&mut blob, bf);
        push_fq(&mut blob, &l_0_d);
        push_fq(&mut blob, &l_last_d);
        push_fq(&mut blob, &l_blind_d);

        fs::write(fixtures.join("lagrange_aux_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      lagrange-aux fixture written ({} bytes, n={}, bf={})",
            blob.len(),
            n_d,
            bf,
        );

        // Phase D2: transcript-evals signature fixture.
        //
        // Re-parses the real poseidon proof's transcript in the
        // same eval-read order as verify() and dumps:
        //   - the total eval count (nEvals)
        //   - the positional signature Σ i · eval_i mod FR_MODULUS
        // over the flat read sequence.
        //
        // File layout (all 32B BE unless noted):
        //   [32] num_evals
        //   [32] signature
        let mut trans = CircuitTranscript::<sha3::Keccak256>::init_from_bytes(&fx.proof);

        // Absorb vk.transcript_repr + instance (matches verify()).
        let repr: Fq = fx.vk.vk().transcript_repr();
        trans.common(&repr).unwrap();
        // committed instance identity placeholder.
        let committed_proj: G1Projective = G1Projective::identity();
        trans.common(&committed_proj).unwrap();
        // instance length + instance value.
        trans.common(&Fq::from(1u64)).unwrap();
        trans.common(&fx.instance).unwrap();

        // Phase reads: advice commitments, challenges, lookup_mult,
        // perm products, lookup, trashcans, quotient limbs. These
        // don't feed into the eval signature (they're G1 commitments
        // + challenges), so we just advance the transcript.
        for _ in 0..vk_info.num_advice_columns {
            let _: G1Projective = trans.read().unwrap();
        }
        let _advice_challenges: Vec<Fq> =
            (0..vk_info.num_challenges).map(|_| trans.squeeze_challenge()).collect();
        let theta_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_lookups {
            let _: G1Projective = trans.read().unwrap();
        }
        let beta_d3: Fq  = trans.squeeze_challenge();
        let gamma_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_permutation_chunks {
            let _: G1Projective = trans.read().unwrap();
        }
        let total_lookup_helpers: usize = vk_info.lookup_num_chunks.iter().sum();
        let total_lookup_commits = total_lookup_helpers + vk_info.num_lookups;
        for _ in 0..total_lookup_commits {
            let _: G1Projective = trans.read().unwrap();
        }
        let trash_challenge_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_trashcans {
            let _: G1Projective = trans.read().unwrap();
        }
        let _y: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_quotient_limbs {
            let _: G1Projective = trans.read().unwrap();
        }
        let x_d3: Fq = trans.squeeze_challenge();

        // Eval reads — collect in the exact order verify() does.
        let mut evals_flat: Vec<Fq> = Vec::new();
        for _ in 0..vk_info.num_committed_instance_evals {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }
        for _ in 0..vk_info.num_advice_queries {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }
        for _ in 0..vk_info.num_fixed_queries {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }
        for _ in 0..vk_info.num_permutation_columns {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }
        for i in 0..vk_info.num_permutation_chunks {
            let e_cur: Fq  = trans.read().unwrap(); evals_flat.push(e_cur);
            let e_next: Fq = trans.read().unwrap(); evals_flat.push(e_next);
            if i + 1 != vk_info.num_permutation_chunks {
                let e_last: Fq = trans.read().unwrap(); evals_flat.push(e_last);
            }
        }
        let total_lookup_evals = total_lookup_helpers + vk_info.num_lookups * 3;
        for _ in 0..total_lookup_evals {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }
        for _ in 0..vk_info.num_trashcans {
            let e: Fq = trans.read().unwrap();
            evals_flat.push(e);
        }

        let mut sig = Fq::ZERO;
        for (i, e) in evals_flat.iter().enumerate() {
            sig += Fq::from(i as u64) * e;
        }

        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(&[0u8; 24]);
        blob.extend_from_slice(&(evals_flat.len() as u64).to_be_bytes());
        blob.extend_from_slice(&fq_to_be(&sig));
        fs::write(fixtures.join("evals_signature_fixture.bin"), &blob).unwrap();
        eprintln!(
            "      evals-signature fixture written ({} bytes, {} evals)",
            blob.len(),
            evals_flat.len(),
        );

        // -------------- Phase D3: partial_eval_signature -------------
        //
        // Replays the transcript-derived env through the replica of
        // `partially_evaluate_identities` (same pattern used by
        // `partial_eval_fixture`) and dumps the positional signature
        // `Σ i · (selector_i + scalar_i) mod FR`.
        //
        // File layout:
        //   [32] num_scalars
        //   [32] signature
        {
            use midnight_proofs::plonk::Any;
            use midnight_proofs::poly::Rotation;
            let vk_inner = fx.vk.vk();
            let cs = vk_inner.cs();

            // Re-slice evals_flat in transcript-read order.
            let mut pos = 0usize;
            let committed_instance_evals_t = &evals_flat[pos..pos + vk_info.num_committed_instance_evals];
            pos += vk_info.num_committed_instance_evals;
            let advice_evals_t = &evals_flat[pos..pos + vk_info.num_advice_queries];
            pos += vk_info.num_advice_queries;
            let fixed_evals_t = &evals_flat[pos..pos + vk_info.num_fixed_queries];
            pos += vk_info.num_fixed_queries;
            let perm_common_t = &evals_flat[pos..pos + vk_info.num_permutation_columns];
            pos += vk_info.num_permutation_columns;
            // Interleaved (cur, next, last?) per perm chunk:
            let mut perm_sets_t: Vec<(Fq, Fq, Option<Fq>)> = Vec::new();
            for i in 0..vk_info.num_permutation_chunks {
                let c = evals_flat[pos]; pos += 1;
                let n = evals_flat[pos]; pos += 1;
                let last = if i + 1 != vk_info.num_permutation_chunks {
                    let l = evals_flat[pos]; pos += 1;
                    Some(l)
                } else { None };
                perm_sets_t.push((c, n, last));
            }
            // Lookup (single, numLookups=1 guarded below).
            assert_eq!(vk_info.num_lookups, 1);
            let m_eval_t = evals_flat[pos]; pos += 1;
            let helper_evals_t: Vec<Fq> = (0..total_lookup_helpers).map(|_| {
                let v = evals_flat[pos]; pos += 1; v
            }).collect();
            let acc_eval_t = evals_flat[pos]; pos += 1;
            let acc_next_eval_t = evals_flat[pos]; pos += 1;
            let trash_evals_t: Vec<Fq> = (0..vk_info.num_trashcans).map(|_| {
                let v = evals_flat[pos]; pos += 1; v
            }).collect();
            let _ = (pos, committed_instance_evals_t);

            // Lagrange aux at x (matches Phase D1 helper).
            let xn_d3 = x_d3.pow_vartime([vk_info.n]);
            let bf_i = vk_info.blinding_factors as i32;
            let l_evals = vk_inner.get_domain().l_i_range(x_d3, xn_d3, -(bf_i + 1)..=0);
            let l_last = l_evals[0];
            let l_blind: Fq = l_evals[1..=bf_i as usize].iter().copied().sum();
            let l_0 = l_evals[1 + bf_i as usize];

            // Build fixed_evals[col] with 1s for simple selectors (per
            // `cs.has_simple_selector_col(col)`), injecting transcript
            // values at remaining positions. Matches
            // _buildFixedEvalsFull on the Sol side.
            let n_fixed_cols = cs.num_fixed_columns();
            let mut fx_evals: Vec<Fq> = Vec::with_capacity(n_fixed_cols);
            let mut ti = 0usize;
            for c in 0..n_fixed_cols {
                if cs.has_simple_selector_col(c) {
                    fx_evals.push(Fq::ONE);
                } else {
                    fx_evals.push(fixed_evals_t[ti]); ti += 1;
                }
            }

            // Instance evals collapse: `instance * l_0` per query
            // (poseidon has num_committed_instance_evals=0, single
            // non-committed col of length 1 at rotation 0).
            let inst_collapsed = fx.instance * l_0;
            let instance_evals: Vec<Fq> = (0..vk_info.num_instance_queries)
                .map(|_| inst_collapsed).collect();

            let challenges: Vec<Fq> = Vec::new();
            let advice_evals = advice_evals_t.to_vec();

            let eval_expression = |expr: &midnight_proofs::plonk::Expression<Fq>| -> Fq {
                expr.evaluate(
                    &|c| c, &|_| panic!("virtual selector"),
                    &|q| fx_evals[q.index().unwrap()],
                    &|q| advice_evals[q.index.unwrap()],
                    &|q| instance_evals[q.index.unwrap()],
                    &|ch| challenges[ch.index()],
                    &|a: Fq| -a, &|a, b| a + b, &|a, b| a * b, &|a, k| a * k,
                )
            };

            let mut expected: Vec<(Option<u32>, Fq)> = Vec::new();

            // 1. Gates.
            for gate in cs.gates().iter() {
                let sel = gate.queried_selectors().iter()
                    .find(|s| s.is_simple())
                    .map(|s| s.index() as u32);
                for poly in gate.polynomials().iter() {
                    expected.push((sel, eval_expression(poly)));
                }
            }

            // 2. Permutation.
            let eval_col = |col: &midnight_proofs::plonk::Column<Any>| -> Fq {
                match col.column_type() {
                    Any::Advice(_) => {
                        let q = cs.advice_queries().iter().position(|(c, rot)|
                            c.index() == col.index() && rot.0 == Rotation::cur().0
                        ).unwrap();
                        advice_evals[q]
                    }
                    Any::Fixed => {
                        let q = cs.fixed_queries().iter().position(|(c, rot)|
                            c.index() == col.index() && rot.0 == Rotation::cur().0
                        ).unwrap();
                        fx_evals[q]
                    }
                    Any::Instance => {
                        let q = cs.instance_queries().iter().position(|(c, rot)|
                            c.index() == col.index() && rot.0 == Rotation::cur().0
                        ).unwrap();
                        instance_evals[q]
                    }
                }
            };
            let perm_columns = cs.permutation().get_columns();
            let perm_chunk_len = cs.degree() - 2;
            let n_perm_cols = perm_columns.len();
            let n_perm_chunks = vk_info.num_permutation_chunks;
            if let Some(first) = perm_sets_t.first() {
                expected.push((None, l_0 * (Fq::ONE - first.0)));
            }
            if let Some(last) = perm_sets_t.last() {
                expected.push((None, (last.0 * last.0 - last.0) * l_last));
            }
            for i in 1..n_perm_chunks {
                let prev_last = perm_sets_t[i - 1].2.unwrap();
                expected.push((None, (perm_sets_t[i].0 - prev_last) * l_0));
            }
            for (chunk_idx, set) in perm_sets_t.iter().enumerate() {
                let col_start = chunk_idx * perm_chunk_len;
                let col_end = std::cmp::min(col_start + perm_chunk_len, n_perm_cols);
                let cols = &perm_columns[col_start..col_end];
                let pevs = &perm_common_t[col_start..col_end];
                let mut left = set.1;
                for (col, pev) in cols.iter().zip(pevs.iter()) {
                    left *= eval_col(col) + beta_d3 * pev + gamma_d3;
                }
                let mut right = set.0;
                let mut current_delta = (beta_d3 * x_d3)
                    * Fq::DELTA.pow_vartime([(chunk_idx * perm_chunk_len) as u64]);
                for col in cols.iter() {
                    right *= eval_col(col) + current_delta + gamma_d3;
                    current_delta *= Fq::DELTA;
                }
                expected.push((None, (left - right) * (Fq::ONE - (l_last + l_blind))));
            }

            // 3. Lookup (single).
            let lk_arg = &cs.lookups()[0];
            let lk_chunked = lk_arg.chunk_by_degree(cs.degree());
            let compress_exprs = |exprs: &[midnight_proofs::plonk::Expression<Fq>]| -> Fq {
                exprs.iter().fold(Fq::ZERO, |acc, e| acc * theta_d3 + eval_expression(e))
            };
            let active_rows = Fq::ONE - (l_last + l_blind);
            let compressed_table = compress_exprs(lk_chunked.table_expressions());
            let selector_val = eval_expression(lk_chunked.selector_expression());
            expected.push((None, (l_0 + l_last) * acc_eval_t));
            let mut sum_helpers = Fq::ZERO;
            for (i, chunk) in lk_chunked.input_expression_chunks().iter().enumerate() {
                let helper_eval = helper_evals_t[i];
                let cwb: Vec<Fq> = chunk.iter().map(|pl| compress_exprs(pl) + beta_d3).collect();
                let product: Fq = cwb.iter().fold(Fq::ONE, |a, b| a * b);
                let sum: Fq = cwb.iter().map(|f| product * f.invert().unwrap()).fold(Fq::ZERO, |a, b| a + b);
                sum_helpers += helper_eval;
                expected.push((None, helper_eval * product - sum));
            }
            let diff = (acc_next_eval_t - acc_eval_t - selector_val * sum_helpers)
                * (compressed_table + beta_d3) + m_eval_t;
            expected.push((None, diff * active_rows));

            // 4. Trashcan.
            for (i, arg) in cs.trashcans().iter().enumerate() {
                let compressed = arg.constraint_expressions().iter().map(&eval_expression)
                    .fold(Fq::ZERO, |acc, e| acc * trash_challenge_d3 + e);
                let q = eval_expression(arg.selector());
                expected.push((None, compressed - (Fq::ONE - q) * trash_evals_t[i]));
            }

            // Positional signature: Σ i · (sel_as_fq + scalar) mod FR.
            let mut sig_d3 = Fq::ZERO;
            for (i, (sel, v)) in expected.iter().enumerate() {
                let sel_fq = Fq::from(sel.unwrap_or(0xFFFFFFFFu32) as u64);
                sig_d3 += Fq::from(i as u64) * (sel_fq + v);
            }

            let mut pblob: Vec<u8> = Vec::new();
            pblob.extend_from_slice(&[0u8; 24]);
            pblob.extend_from_slice(&(expected.len() as u64).to_be_bytes());
            pblob.extend_from_slice(&fq_to_be(&sig_d3));
            fs::write(fixtures.join("partial_eval_signature_fixture.bin"), &pblob).unwrap();
            eprintln!(
                "      partial-eval-signature fixture written ({} bytes, {} scalars)",
                pblob.len(),
                expected.len(),
            );
        }
    }

    // Emit a (compressed, EIP-2537 uncompressed) fixture pair for each of
    // the proof's G1 points. The forge test uses these to unit-test the
    // Solidity decompression function before attempting the full pairing.
    {
        use group::{Group, GroupEncoding};
        let mut pairs: Vec<u8> = Vec::new();
        let mut write_pair = |p: &midnight_curves::G1Projective| {
            let c: <midnight_curves::G1Projective as GroupEncoding>::Repr =
                <midnight_curves::G1Projective as GroupEncoding>::to_bytes(p);
            let u = midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(p);
            pairs.extend_from_slice(c.as_ref()); // 48 bytes
            pairs.extend_from_slice(&u);         // 128 bytes
        };

        // Use the SRS generator and two random-ish points from the fixed
        // commitments as test vectors.
        write_pair(&<midnight_curves::G1Projective as Group>::generator());
        for c in fx.vk.vk().fixed_commitments().iter().take(3) {
            write_pair(c);
        }
        fs::write(fixtures.join("decomp_pairs.bin"), &pairs).unwrap();
        eprintln!(
            "      decomp fixture pairs written ({} bytes = {} x (48+128))",
            pairs.len(),
            pairs.len() / 176,
        );
    }

    eprintln!("OK — see {}/ for generated files", contracts.display());
    eprintln!("         {}/ for fixtures", fixtures.display());
}

fn write_vk_blob(vk: &VkInfo, out: &mut impl Write) {
    out.write_all(&vk.transcript_repr_be).unwrap();
    out.write_all(&vk.omega_be).unwrap();

    let mut c1 = [0u8; 32];
    c1[0..8].copy_from_slice(&vk.n.to_be_bytes());
    c1[8..12].copy_from_slice(&vk.k.to_be_bytes());
    c1[12..16].copy_from_slice(&(vk.num_advice_columns as u32).to_be_bytes());
    c1[16..20].copy_from_slice(&(vk.num_fixed_columns as u32).to_be_bytes());
    c1[20..24].copy_from_slice(&(vk.num_instance_columns as u32).to_be_bytes());
    c1[24..28].copy_from_slice(&(vk.num_challenges as u32).to_be_bytes());
    c1[28..32].copy_from_slice(&(vk.num_phases as u32).to_be_bytes());
    out.write_all(&c1).unwrap();

    let mut c2 = [0u8; 32];
    c2[0..4].copy_from_slice(&(vk.cs_degree as u32).to_be_bytes());
    c2[4..8].copy_from_slice(&(vk.num_simple_selectors as u32).to_be_bytes());
    c2[8..12].copy_from_slice(&(vk.blinding_factors as u32).to_be_bytes());
    c2[12..16].copy_from_slice(&(vk.num_advice_queries as u32).to_be_bytes());
    c2[16..20].copy_from_slice(&(vk.num_fixed_queries as u32).to_be_bytes());
    c2[20..24].copy_from_slice(&(vk.num_instance_queries as u32).to_be_bytes());
    c2[24..28].copy_from_slice(&(vk.num_lookups as u32).to_be_bytes());
    c2[28..32].copy_from_slice(&(vk.num_trashcans as u32).to_be_bytes());
    out.write_all(&c2).unwrap();

    let total_lookup_helpers: u32 = vk.lookup_num_chunks.iter().map(|&c| c as u32).sum();
    let mut c3 = [0u8; 32];
    c3[0..4].copy_from_slice(&(vk.num_permutation_columns as u32).to_be_bytes());
    c3[4..8].copy_from_slice(&(vk.num_permutation_chunks as u32).to_be_bytes());
    c3[8..12].copy_from_slice(&(vk.num_quotient_limbs as u32).to_be_bytes());
    c3[12..16].copy_from_slice(&total_lookup_helpers.to_be_bytes());
    c3[16..20].copy_from_slice(&(vk.num_committed_instance_evals as u32).to_be_bytes());
    out.write_all(&c3).unwrap();

    for c in &vk.fixed_comms_eip2537 { out.write_all(c).unwrap(); }
    for c in &vk.perm_comms_eip2537  { out.write_all(c).unwrap(); }
    out.write_all(&vk.s_g2_eip2537).unwrap();
    out.write_all(&vk.neg_g2_eip2537).unwrap();
}
