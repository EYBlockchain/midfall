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
