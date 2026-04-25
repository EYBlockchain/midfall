//! Generate Solidity contracts + fixture files for a supported circuit.
//!
//! Running `cargo run --bin generate` (default: poseidon) will:
//!   1. Build the SRS, keygen VK/PK, and prove the target circuit using
//!      the Keccak256 transcript.
//!   2. Dump the proof, instance, and execution trace to
//!      `fixtures/<circuit>/`.
//!   3. Render `contracts/circuits/<circuit>/<Name>VerifyingKey.sol`
//!      with the runtime data.
//!
//! The verifier contract `contracts/PoseidonVerifier.sol` is *not*
//! regenerated — its logic is circuit-agnostic within the constraints baked
//! into the VK blob (see ARCHITECTURE.md §7.2 for the current poseidon-
//! specific shortcuts that block non-poseidon circuits from verifying).
//! Only the VK contract depends on the circuit.
//!
//! Phase 0: only the `poseidon` circuit is wired. Phase 1 adds
//! `--circuit rsa-signature`.

use std::{fs, io::Write, path::PathBuf};

use midnight_curves::Fq;
use midnight_solidity_verifier::{
    circuits::poseidon::PoseidonFixture,
    codegen::{render_verifying_key, VkInfo},
    eip2537::fq_to_be,
};

fn main() {
    let here: PathBuf = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("CARGO_MANIFEST_DIR");

    // Per-circuit output roots. In Phase 0 the only wired circuit is
    // poseidon; `bin/generate.rs` still has no CLI flag, which is
    // added in Phase 1.
    let circuit_name = "poseidon";
    let fixtures = here.join("fixtures").join(circuit_name);
    let contracts_root = here.join("contracts");
    let circuit_contracts = contracts_root.join("circuits").join(circuit_name);
    fs::create_dir_all(&fixtures).expect("mkdir fixtures");
    fs::create_dir_all(&circuit_contracts).expect("mkdir circuit contracts dir");

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
    fs::write(circuit_contracts.join("PoseidonVerifyingKey.sol"), sol)
        .expect("write sol");

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

    // Emit verifier-equivalent fixtures produced by driving the REAL verifier.
    //
    // Uses the `debug-trace-hooks` feature on midnight-proofs to capture the
    // canonical sequence of intermediate scalars from `prepare()` rather than
    // re-implementing verifier algorithms in a fixture generator. The only
    // fixtures emitted here are the ones sourced directly from
    // `prepare()`, the transcript parser, and VK helpers:
    //   - verifier_trace.bin        (instrumented trace of prepare())
    //   - pairing_fixture.bin       (dual_msm.split().check())
    //   - right_g1_fixture.bin      (dual_msm.right as EIP-2537)
    //   - right_msm_inputs_digest   (keccak digest of right MSM concat)
    //   - right_msm_terms_fixture.bin  (per-term right MSM labels/scalars/points)
    //   - query_schedule_fixture.bin  (VK distinct rotations * x)
    //   - lagrange_aux_fixture.bin  (l_0 / l_last / l_blind from domain helper)
    //   - evals_signature_fixture.bin  (transcript eval positional signature)
    {
        use ff::Field;
        use group::Group;
        let vk_inner = fx.vk.vk();

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

        // Debug: print the advice_queries list used by `prepare`.
        eprintln!("  ---- prepare-time advice_queries ----");
        for (qi, (col, rot)) in
            fx.vk.vk().cs().advice_queries().iter().enumerate()
        {
            eprintln!(
                "      q={:2} col={} rot={}",
                qi, col.index(), rot.0
            );
        }

        // Enable the midnight-proofs debug-trace recorder so that every
        // instrumented emission point (`partial_eval.*`, `linearization.*`,
        // `permutation.*`, `logup.*`, `trash.*`, `multi_prepare.*`) pushes
        // into a thread-local event buffer. This replaces the per-algorithm
        // replica fixtures with values sourced from the *real* verifier.
        midnight_proofs::debug_trace::start();
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
        let trace_events = midnight_proofs::debug_trace::stop();
        eprintln!(
            "      debug-trace captured {} events during prepare()",
            trace_events.len(),
        );

        // Serialize the captured events into `fixtures/verifier_trace.bin`.
        //
        // File layout (all integers are big-endian):
        //   [4]  magic  = b"MTR1"        (Midnight TRace v1)
        //   [4]  num_events (u32)
        //     per event:
        //       [4]  tag_len (u32)
        //       [..] tag bytes (UTF-8, not NUL-terminated)
        //       [4]  payload_len (u32)
        //       [..] payload bytes (scalar: 32 BE; u64: 8 BE; i32: 4 BE)
        //
        // Scalars are encoded as canonical 32-byte big-endian (mirrors
        // `fq_to_be`). Unknown future emission types are opaque to the
        // Solidity consumer and can be skipped by reading
        // `payload_len` bytes.
        {
            let mut blob: Vec<u8> = Vec::new();
            blob.extend_from_slice(b"MTR1");
            blob.extend_from_slice(&(trace_events.len() as u32).to_be_bytes());
            for ev in &trace_events {
                let tag = ev.tag.as_bytes();
                blob.extend_from_slice(&(tag.len() as u32).to_be_bytes());
                blob.extend_from_slice(tag);
                blob.extend_from_slice(&(ev.payload.len() as u32).to_be_bytes());
                blob.extend_from_slice(&ev.payload);
            }
            fs::write(fixtures.join("verifier_trace.bin"), &blob).unwrap();
            eprintln!(
                "      verifier_trace fixture written ({} bytes, {} events)",
                blob.len(),
                trace_events.len(),
            );
            // Emit a small histogram of emission sites so the operator can
            // eyeball coverage without loading the fixture.
            let mut tag_counts: std::collections::BTreeMap<&str, usize> =
                std::collections::BTreeMap::new();
            for ev in &trace_events {
                // Collapse bracketed indices so, e.g.,
                //   "partial_eval.identity[0].scalar"
                //   "partial_eval.identity[1].scalar"
                // both bucket under "partial_eval.identity[*].scalar".
                let mut out = String::with_capacity(ev.tag.len());
                let mut in_br = false;
                for c in ev.tag.chars() {
                    if c == '[' {
                        in_br = true;
                        out.push('[');
                        out.push('*');
                    } else if c == ']' {
                        in_br = false;
                        out.push(']');
                    } else if !in_br {
                        out.push(c);
                    }
                }
                *tag_counts
                    .entry(Box::leak(out.into_boxed_str()))
                    .or_insert(0) += 1;
            }
            eprintln!("      debug-trace coverage by tag:");
            for (tag, n) in tag_counts.iter() {
                eprintln!("        {:<45} × {}", tag, n);
            }
        }

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

        // Phase D8 debug: print v and related scalars recovered from
        // dual_msm.right (term 49 = -G with scalar v; term 47 = f_com
        // with scalar x4^nSets).
        {
            let (_, right_terms_dbg) = dual_msm.split();
            let n = right_terms_dbg.len();
            eprintln!("      right terms: {}", n);
            for i in [0, 1, n - 3, n - 2, n - 1].iter() {
                let (lbl, s, _) = right_terms_dbg[*i];
                eprintln!("        term[{}] label={} scalar={}", i, lbl, hex::encode(fq_to_be(s)));
            }
            // term[n-1] is -G with scalar v, term[n-3] is f_com with scalar x4^nSets.
            let v = right_terms_dbg[n - 1].1;
            let f_com_scalar = right_terms_dbg[n - 3].1;
            eprintln!("      rust v = {}", hex::encode(fq_to_be(v)));
            eprintln!("      rust f_com_scalar = {}", hex::encode(fq_to_be(f_com_scalar)));
            let pi_scalar = right_terms_dbg[n - 2].1;
            eprintln!("      rust x3 (pi_scalar) = {}", hex::encode(fq_to_be(pi_scalar)));

            // Extract the per-set x4 multipliers on the right MSM's set
            // sections. Before f_com (at n-3), the preceding terms are
            // set-by-set MSM flattenings. We can read the first term of
            // each sorted set (which carries the "sorted set 0" ==
            // scalar 1 token) to recover x4 by looking at set-boundary
            // transitions. Simpler: print all term scalars and find
            // "new set" markers manually.
            // All right-term scalars for detailed diff.
            eprintln!("      all right term scalars:");
            for (i, (lbl, s, _)) in right_terms_dbg.iter().enumerate() {
                eprintln!("        rt[{:2}] lbl={:25} scalar={}", i, format!("{}", lbl), hex::encode(fq_to_be(s)));
            }
            eprintln!("  fixed_queries (col, rot):");
            for (qi, (col, rot)) in fx.vk.vk().cs().fixed_queries().iter().enumerate() {
                eprintln!("    fq[{:2}] col={} rot={}", qi, col.index(), rot.0);
            }
            let simple: Vec<usize> = (0..fx.vk.vk().cs().num_fixed_columns()).filter(|&i| fx.vk.vk().cs().has_simple_selector_col(i)).collect();
            eprintln!("  simple_selectors: {:?}", simple);
        }

        // Phase D8 debug: right_g1 EIP-2537 bytes + keccak digest so the
        // Solidity side can compare its emitted right_g1 against the
        // Rust-side reference.
        {
            use sha3::{Digest, Keccak256};
            let right_eip =
                midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(
                    &right_eval,
                );
            let digest = Keccak256::digest(&right_eip);
            let mut b: Vec<u8> = Vec::new();
            b.extend_from_slice(&right_eip);
            b.extend_from_slice(&digest);
            fs::write(fixtures.join("right_g1_fixture.bin"), &b).unwrap();
            eprintln!(
                "      right-g1 fixture written ({} bytes = 128 + 32)",
                b.len(),
            );
        }

        // Phase D8 inputs digest: emit the Rust DualMSM.right as the
        // concatenation of (scalar_be || eip2537_point) in insertion
        // order, plus its keccak digest, so the Solidity `verify()`
        // emission of `right_msm_inputs_digest` can be matched
        // bit-for-bit against this fixture.
        {
            use sha3::{Digest, Keccak256};
            let (_, right_terms) = dual_msm.split();
            let mut concat: Vec<u8> = Vec::new();
            for (_lbl, scalar, base) in right_terms.iter() {
                concat.extend_from_slice(&fq_to_be(scalar));
                let pt =
                    midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(
                        base,
                    );
                concat.extend_from_slice(&pt);
            }
            let digest = Keccak256::digest(&concat);
            let mut b: Vec<u8> = Vec::new();
            b.extend_from_slice(&digest);
            b.extend_from_slice(
                &(right_terms.len() as u64).to_be_bytes(),
            );
            fs::write(
                fixtures.join("right_msm_inputs_digest_fixture.bin"),
                &b,
            ).unwrap();
            eprintln!(
                "      right-msm-inputs-digest fixture written ({} bytes, {} terms)",
                b.len(),
                right_terms.len(),
            );
        }

        // Phase D8 per-term dump: emit the Rust DualMSM.right as a
        // list of (label, scalar, point) entries in DualMSM insertion
        // order. Solidity-side D8 MSM assembly will be compared against
        // this fixture to find the first mismatching term.
        //
        // File layout:
        //   [4] n
        //     per term:
        //       [4] label_len
        //       [label_len]  label_bytes   (e.g. "advice_0", "fixed_3",
        //                                   "linearization_poly",
        //                                   "-G", "π", "f_com")
        //       [32] scalar_be
        //       [128] eip2537_point
        {
            let (_, right_terms) = dual_msm.split();
            let mut b: Vec<u8> = Vec::new();
            b.extend_from_slice(&(right_terms.len() as u32).to_be_bytes());
            for (label, scalar, base) in right_terms.iter() {
                let lb = format!("{}", label);
                let lb_bytes = lb.as_bytes();
                b.extend_from_slice(
                    &(lb_bytes.len() as u32).to_be_bytes()
                );
                b.extend_from_slice(lb_bytes);
                b.extend_from_slice(&fq_to_be(scalar));
                let pt =
                    midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(
                        base,
                    );
                b.extend_from_slice(&pt);
            }
            fs::write(
                fixtures.join("right_msm_terms_fixture.bin"),
                &b,
            ).unwrap();
            eprintln!(
                "      right-msm-terms fixture written ({} bytes, {} terms)",
                b.len(),
                right_terms.len(),
            );
        }

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
        let _theta_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_lookups {
            let _: G1Projective = trans.read().unwrap();
        }
        let _beta_d3: Fq  = trans.squeeze_challenge();
        let _gamma_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_permutation_chunks {
            let _: G1Projective = trans.read().unwrap();
        }
        let total_lookup_helpers: usize = vk_info.lookup_num_chunks.iter().sum();
        let total_lookup_commits = total_lookup_helpers + vk_info.num_lookups;
        for _ in 0..total_lookup_commits {
            let _: G1Projective = trans.read().unwrap();
        }
        let _trash_challenge_d3: Fq = trans.squeeze_challenge();
        for _ in 0..vk_info.num_trashcans {
            let _: G1Projective = trans.read().unwrap();
        }
        let _y_d4: Fq = trans.squeeze_challenge();
        let mut quot_limbs_d4: Vec<G1Projective> = Vec::new();
        for _ in 0..vk_info.num_quotient_limbs {
            quot_limbs_d4.push(trans.read().unwrap());
        }
        let _x_d3: Fq = trans.squeeze_challenge();

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

    // Debug: advice_queries list.
    {
        eprintln!("  ---- advice_queries (col, rot) ----");
        for (qi, (c, r)) in vk_info_debug_advice_queries(&fx).iter().enumerate() {
            eprintln!("    q={:2} col={} rot={}", qi, c, r);
        }
    }

    // Adversarial matrix (Phase F1).
    //
    // Emit a small set of pre-computed rejection fixtures derived from
    // the canonical valid proof + instance. Each entry must be rejected
    // by `verify()` (either returns false or reverts). Consumers:
    //
    //   * test/PoseidonVerifier.t.sol::test_adversarial_matrix_all_rejected
    //   * tests/pbt.rs::adversarial_matrix_all_rejected
    //
    // File layout (all integers BE):
    //   [u32]  version = 1
    //   [u32]  num_entries
    //   per entry:
    //     [u8]   kind (0=proof_bit, 1=proof_byte, 2=proof_trunc,
    //                  3=proof_extend, 4=wrong_instance)
    //     [u8]   label_len  (label is ASCII, <= 64 bytes)
    //     [...]  label bytes
    //     [32]   instance BE
    //     [u32]  proof_len
    //     [...]  proof bytes
    {
        struct Entry {
            kind: u8,
            label: &'static str,
            instance_be: [u8; 32],
            proof: Vec<u8>,
        }
        const KIND_PROOF_BIT: u8 = 0;
        const KIND_PROOF_BYTE: u8 = 1;
        const KIND_PROOF_TRUNC: u8 = 2;
        const KIND_PROOF_EXT: u8 = 3;
        const KIND_WRONG_INST: u8 = 4;

        let valid_proof = fx.proof.clone();
        let valid_inst_be = fq_to_be(&fx.instance);
        let pn = valid_proof.len();
        assert!(pn >= 128, "proof unexpectedly short: {pn} bytes");

        let mut entries: Vec<Entry> = Vec::new();

        // 1. Bit-flip in the transcript-prefix region (byte 50, bit 7).
        {
            let mut p = valid_proof.clone();
            p[50] ^= 0x80;
            entries.push(Entry {
                kind: KIND_PROOF_BIT,
                label: "bit_early",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 2. Bit-flip in the middle of the proof (scalar-reads region).
        {
            let mut p = valid_proof.clone();
            p[pn / 2] ^= 0x08;
            entries.push(Entry {
                kind: KIND_PROOF_BIT,
                label: "bit_mid",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 3. Bit-flip near the tail (inside the π region).
        {
            let mut p = valid_proof.clone();
            p[pn - 48] ^= 0x01;
            entries.push(Entry {
                kind: KIND_PROOF_BIT,
                label: "bit_late",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 4. Byte overwrite: zero out byte 0 (clobbers first commitment's
        //    compression tag).
        {
            let mut p = valid_proof.clone();
            p[0] = 0;
            entries.push(Entry {
                kind: KIND_PROOF_BYTE,
                label: "byte_zero_head",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 5. Byte overwrite: 0xFF at roughly 1/3 of the proof.
        {
            let mut p = valid_proof.clone();
            p[pn / 3] = 0xFF;
            entries.push(Entry {
                kind: KIND_PROOF_BYTE,
                label: "byte_ff_mid",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 6. Truncated proof: drop the last 48 bytes (removes π entirely
        //    -> trips `require(remaining >= 48 && ...)` in verify()).
        {
            let p = valid_proof[..pn - 48].to_vec();
            entries.push(Entry {
                kind: KIND_PROOF_TRUNC,
                label: "trunc_48",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 7. Extended proof: append 17 arbitrary bytes
        //    (non-multiple-of-32 -> trips `(remaining - 48) % 32 != 0`).
        {
            let mut p = valid_proof.clone();
            p.extend_from_slice(&[0xabu8; 17]);
            entries.push(Entry {
                kind: KIND_PROOF_EXT,
                label: "ext_17",
                instance_be: valid_inst_be,
                proof: p,
            });
        }
        // 8. Wrong instance: XOR the last byte with 0x01 — smallest
        //    possible delta, guaranteed to diverge the Fiat-Shamir
        //    sequence from the first squeeze onwards.
        {
            let mut inst = valid_inst_be;
            inst[31] ^= 0x01;
            entries.push(Entry {
                kind: KIND_WRONG_INST,
                label: "inst_xor1",
                instance_be: inst,
                proof: valid_proof.clone(),
            });
        }

        // Serialise.
        let version: u32 = 1;
        let mut blob: Vec<u8> = Vec::new();
        blob.extend_from_slice(&version.to_be_bytes());
        blob.extend_from_slice(&(entries.len() as u32).to_be_bytes());
        for e in &entries {
            let lab = e.label.as_bytes();
            assert!(lab.len() <= 64, "label '{}' too long", e.label);
            blob.push(e.kind);
            blob.push(lab.len() as u8);
            blob.extend_from_slice(lab);
            blob.extend_from_slice(&e.instance_be);
            blob.extend_from_slice(&(e.proof.len() as u32).to_be_bytes());
            blob.extend_from_slice(&e.proof);
        }
        fs::write(fixtures.join("adversarial_fixtures.bin"), &blob).unwrap();
        eprintln!(
            "      adversarial matrix written ({} bytes, {} entries)",
            blob.len(),
            entries.len(),
        );
        for (i, e) in entries.iter().enumerate() {
            eprintln!(
                "        [{:02}] kind={} label={:<16} inst=0x{}... proof={}B",
                i,
                e.kind,
                e.label,
                hex::encode(&e.instance_be[..4]),
                e.proof.len(),
            );
        }
    }

    eprintln!("OK — see {}/ for generated files", circuit_contracts.display());
    eprintln!("         {}/ for fixtures", fixtures.display());
}

fn vk_info_debug_advice_queries(
    fx: &midnight_solidity_verifier::poseidon_fixture::PoseidonFixture,
) -> Vec<(usize, i32)> {
    fx.vk
        .vk()
        .cs()
        .advice_queries()
        .iter()
        .map(|(c, r)| (c.index(), r.0))
        .collect()
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
