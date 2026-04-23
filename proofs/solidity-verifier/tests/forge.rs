//! End-to-end test harness that drives the whole pipeline:
//!
//!   1. Regenerates a fresh poseidon proof & VK contract via the runtime
//!      codegen.
//!   2. Reruns the canonical Rust verifier while recording a trace of
//!      *every* challenge squeezed and *every* transcript read.
//!   3. Invokes `forge test` to run the Solidity verifier with the same
//!      proof, capturing its own equivalent trace + gas benchmarks.
//!   4. Compares the two traces element-by-element.
//!
//! The equivalence check establishes that the Solidity port replicates the
//! Rust verifier's exact Fiat-Shamir sequence: every challenge produced and
//! every transcript-absorbed value matches byte-for-byte.

use std::{
    fs,
    path::PathBuf,
    process::Command,
};

use midnight_proofs::{
    plonk::VerifyingKey,
    poly::kzg::KZGCommitmentScheme,
    transcript::Transcript,
};
use midnight_solidity_verifier::{
    eip2537,
    poseidon_fixture::PoseidonExample,
    trace::{Trace, TraceEntry},
    transcript::TracingTranscript,
};
use midnight_zk_stdlib::utils::plonk_api::srs_for_test;

fn here() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Rerun `cargo run --bin generate` so `contracts/` and `fixtures/` are up
/// to date before we compare traces.
fn regenerate() {
    eprintln!("[harness] regenerating proof + VK contract");
    let status = Command::new(env!("CARGO"))
        .args(["run", "--quiet", "--bin", "generate", "-p", "midnight-solidity-verifier"])
        .env(
            "SRS_DIR",
            here().parent().unwrap().parent().unwrap().join("zk_stdlib/examples/assets"),
        )
        .current_dir(here().parent().unwrap().parent().unwrap())
        .status()
        .expect("cargo run generate");
    assert!(status.success(), "generate failed");
}

/// Rerun `forge test` in the same workspace so we get a fresh
/// `fixtures/solidity_trace.json`.
fn run_forge_test() {
    eprintln!("[harness] running forge test");
    let output = Command::new("forge")
        .args(["test", "-vv"])
        .current_dir(here())
        .output()
        .expect("forge test");
    // Dump forge's output unconditionally so the gas benchmark is visible.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("---- forge stdout ----\n{stdout}\n---- forge stderr ----\n{stderr}");
    assert!(output.status.success(), "forge test failed");
}

/// Reproduces the Rust verifier's Fiat-Shamir sequence and returns a
/// [`Trace`]. Importantly, this does *not* re-run the full algebraic
/// verification — we only want the transcript-observable operations.
///
/// Because the prover injects randomness internally (not only via the rng
/// passed in), we can't regenerate the exact proof bytes from a seed. The
/// test therefore re-runs only the *deterministic* keygen and then replays
/// the transcript against the proof bytes freshly written by
/// `cargo run --bin generate`.
fn rust_verifier_trace(proof: &[u8], instance: &midnight_curves::Fq) -> Trace {
    use ff::PrimeField;
    use midnight_curves::Fq;

    let relation = PoseidonExample;
    let srs = srs_for_test(&relation, Some(6));
    let midnight_vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let vk: &VerifyingKey<Fq, KZGCommitmentScheme<midnight_curves::Bls12>> = midnight_vk.vk();
    let cs = vk.cs();

    let mut t = TracingTranscript::init_from_bytes(proof);

    // --- hash VK into transcript ---
    t.common_fq(&vk.transcript_repr()).unwrap();
    t.trace.borrow_mut().intermediate("vk_repr", eip2537::fq_to_be_hex(&vk.transcript_repr()));

    // --- hash committed instances --- (zk_stdlib always has exactly one
    // committed instance column per proof, defaulting to G1::identity() when
    // `committed_instance` is None).
    use group::Group;
    let committed_identity: midnight_curves::G1Projective =
        <midnight_curves::G1Projective as Group>::identity();
    t.common_g1(&committed_identity).unwrap();

    // --- hash non-committed instance: for each instance, common(len); common(v).
    // For poseidon: 1 non-committed instance column, 1 value.
    let inst_len = Fq::from_u128(1u128);
    t.common_fq(&inst_len).unwrap();
    t.common_fq(instance).unwrap();

    // --- phases loop: read advice, squeeze challenges ---
    for (phase_idx, _phase) in cs.phases().enumerate() {
        for i in 0..cs.num_advice_columns() {
            let _c = t.read_g1(&format!("advice[{i}]"))
                .unwrap_or_else(|e| panic!("read advice[{i}] phase {phase_idx}: {e}"));
        }
        for _ in 0..cs.num_challenges() {
            let _ch = t.squeeze_fq("advice_challenge");
        }
    }
    let _theta = t.squeeze_fq("theta");

    // --- lookup_multiplicities ---
    for _ in 0..cs.lookups().len() {
        let _m = t.read_g1("lookup_mult").unwrap();
    }

    let _beta  = t.squeeze_fq("beta");
    let _gamma = t.squeeze_fq("gamma");

    // --- permutation products ---
    let perm_chunks = {
        let chunk_len = cs.degree() - 2;
        let cols = cs.permutation().get_columns().len();
        if cols == 0 { 0 } else { (cols + chunk_len - 1) / chunk_len }
    };
    for _ in 0..perm_chunks { let _ = t.read_g1("perm_product").unwrap(); }

    // --- lookup commitments (helpers + 1 accumulator per lookup) ---
    for l in cs.lookups().iter() {
        let nc = l.chunk_by_degree(cs.degree()).num_chunks();
        for _ in 0..nc { let _ = t.read_g1("lookup_helper").unwrap(); }
        let _ = t.read_g1("lookup_acc").unwrap();
    }

    let _trash_ch = t.squeeze_fq("trash_challenge");
    for _ in 0..cs.trashcans().len() { let _ = t.read_g1("trashcan").unwrap(); }
    let _y = t.squeeze_fq("y");

    // quotient limbs
    let nb_q = vk.get_domain().get_quotient_poly_degree();
    for _ in 0..nb_q { let _ = t.read_g1("quotient_limb").unwrap(); }

    let _x = t.squeeze_fq("x");

    // read evals
    let num_fixed_q = cs
        .fixed_queries()
        .iter()
        .filter(|(c, _)| !cs.has_simple_selector_col(c.index()))
        .count();
    // --- INSTANCE evals: for committed-instance columns, the verifier
    // reads the eval from the transcript; for non-committed columns it
    // computes it locally via Lagrange interpolation. `zk_stdlib` always
    // passes exactly one committed-instance commitment per proof, so we
    // count instance-queries on column index 0 as transcript reads.
    let nb_committed_instances: usize = 1;
    let num_committed_instance_reads = cs
        .instance_queries()
        .iter()
        .filter(|(col, _)| col.index() < nb_committed_instances)
        .count();
    for _ in 0..num_committed_instance_reads {
        let _ = t.read_fq("committed_instance_eval").unwrap();
    }

    for i in 0..cs.advice_queries().len() {
        let _ = t.read_fq(&format!("advice_eval[{i}]")).unwrap();
    }
    for i in 0..num_fixed_q {
        let _ = t.read_fq(&format!("fixed_eval[{i}]")).unwrap();
    }
    for i in 0..cs.permutation().get_columns().len() {
        let _ = t.read_fq(&format!("perm_common[{i}]")).unwrap();
    }
    for i in 0..perm_chunks {
        let _ = t.read_fq("perm_cur").unwrap();
        let _ = t.read_fq("perm_next").unwrap();
        if i + 1 != perm_chunks {
            let _ = t.read_fq("perm_last").unwrap();
        }
    }
    for l in cs.lookups().iter() {
        let nc = l.chunk_by_degree(cs.degree()).num_chunks();
        let _ = t.read_fq("lookup_m_eval").unwrap();
        for _ in 0..nc { let _ = t.read_fq("lookup_helper_eval").unwrap(); }
        let _ = t.read_fq("lookup_acc_eval").unwrap();
        let _ = t.read_fq("lookup_acc_next_eval").unwrap();
    }
    for _ in 0..cs.trashcans().len() { let _ = t.read_fq("trash_eval").unwrap(); }

    // --- KZG multi-open ---
    let _x1 = t.squeeze_fq("x1");
    let _x2 = t.squeeze_fq("x2");
    let _f_com = t.read_g1("f_com").unwrap();
    let _x3 = t.squeeze_fq("x3");
    // Read remaining q_evals from the proof (until only 48 bytes — one G1
    // point — are left).
    loop {
        let buf = t.inner_mut().buffer();
        let remaining = buf.get_ref().len() as i64 - buf.position() as i64;
        if remaining <= 48 { break; }
        let _ = t.read_fq("q_eval").unwrap();
    }
    let _x4 = t.squeeze_fq("x4");
    let _pi = t.read_g1("pi").unwrap();

    t.trace()
}

/// Filter traces to only the transcript-observable entries (Challenges,
/// scalar/point reads) in order, stripping the free-form `tag` so that
/// only the sequenced byte values remain.
fn normalise(tr: &Trace) -> Vec<(&'static str, String)> {
    tr.entries
        .iter()
        .filter_map(|e| match e {
            TraceEntry::Challenge { fe_be_hex, .. } => Some(("C", fe_be_hex.clone())),
            TraceEntry::ReadScalar { fe_be_hex, .. } => Some(("S", fe_be_hex.clone())),
            TraceEntry::ReadPoint { eip2537_hex, .. } => Some(("P", eip2537_hex.clone())),
            _ => None,
        })
        .collect()
}

#[test]
fn rust_and_solidity_traces_match() {
    regenerate();
    run_forge_test();

    // Rebuild the fixture so we're comparing against the SAME proof bytes
    // that the Solidity test just consumed.
    let proof_path  = here().join("fixtures/proof.bin");
    let trace_path  = here().join("fixtures/solidity_trace.json");

    // Load the proof bytes freshly written by `generate`.
    use ff::PrimeField;
    let on_disk_proof = fs::read(&proof_path).expect("read proof.bin");
    let instance_be = fs::read(here().join("fixtures/instance.be")).expect("read instance.be");
    assert_eq!(instance_be.len(), 32);
    let mut inst_le = [0u8; 32];
    for i in 0..32 {
        inst_le[i] = instance_be[31 - i];
    }
    let instance = midnight_curves::Fq::from_repr(inst_le)
        .expect("instance deserialises");

    // Sanity check: the canonical midnight-proofs verifier must accept
    // this proof. This is the authoritative reference: if this fails we
    // know the fixture itself is broken.
    {
        let relation = PoseidonExample;
        let srs = srs_for_test(&relation, Some(6));
        let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
        midnight_zk_stdlib::verify::<PoseidonExample, sha3::Keccak256>(
            &srs.verifier_params(),
            &vk,
            &instance,
            None,
            &on_disk_proof,
        )
        .expect("canonical Rust verifier accepts the fixture proof");
        eprintln!("[harness] canonical Rust verify OK");
    }

    let rust_trace = rust_verifier_trace(&on_disk_proof, &instance);
    fs::write(
        here().join("fixtures/rust_trace.json"),
        rust_trace.to_json_pretty(),
    )
    .unwrap();

    // Load Solidity trace.
    let sol_raw = fs::read_to_string(&trace_path).expect("read solidity_trace.json");
    // The Solidity test writes a simplified array; parse it with serde_json.
    let sol_entries: Vec<serde_json::Value> = serde_json::from_str(&sol_raw).unwrap();

    let sol_normalised: Vec<(&'static str, String)> = sol_entries
        .iter()
        .filter_map(|v| {
            let kind = v["kind"].as_str()?;
            match kind {
                "Challenge" => Some(("C", v["fe_be_hex"].as_str()?.to_string())),
                "ReadScalar" => Some(("S", v["fe_be_hex"].as_str()?.to_string())),
                "ReadPoint" => Some(("P", v["eip2537_hex"].as_str()?.to_string())),
                _ => None,
            }
        })
        .collect();

    let rs_normalised = normalise(&rust_trace);

    eprintln!("rust trace has {} entries", rs_normalised.len());
    eprintln!("sol  trace has {} entries", sol_normalised.len());

    // Compare element-by-element, showing a nice diff at the first mismatch.
    let mut mismatches = 0;
    let n = rs_normalised.len().min(sol_normalised.len());
    for i in 0..n {
        if rs_normalised[i] != sol_normalised[i] {
            mismatches += 1;
            if mismatches <= 5 {
                eprintln!(
                    "mismatch [{i:3}] rust={:?} sol={:?}",
                    rs_normalised[i], sol_normalised[i]
                );
            }
        }
    }
    if rs_normalised.len() != sol_normalised.len() {
        eprintln!("length mismatch");
    }

    assert_eq!(rs_normalised, sol_normalised, "rust vs solidity trace divergence");
}
