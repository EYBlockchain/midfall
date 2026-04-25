//! Rust-driven revm smoke test for the RSA-signature circuit.
//!
//! Parallels `test/RsaSignatureVerifier.t.sol` — deploys the generic
//! `PlonkVerifier` wired to `RsaSignatureVerifyingKey` and calls
//! `verify(publicInputs, proof)` on the fixture produced by
//! `bin/generate_rsa`.
//!
//! Running under `cargo test --test rsa` takes ~1 second (Solidity
//! artifacts must exist; proof generation is a separate
//! `--ignored` step below).

mod common;

use std::{fs, process::Command};

use common::{Harness, RSA_SIGNATURE};

/// Regenerate the RSA fixtures if any of them are missing.  Skipped
/// by default because a fresh `generate_rsa` run takes ~30s.
fn ensure_rsa_fixtures() {
    let fixtures = common::root_dir().join("fixtures").join(RSA_SIGNATURE.fixtures_subdir);
    let missing = ["proof.bin", "instance.bin"]
        .iter()
        .any(|f| !fixtures.join(f).exists());
    if !missing {
        return;
    }
    eprintln!("[rsa] fixtures missing — running `cargo run --bin generate_rsa`");
    let status = Command::new(env!("CARGO"))
        .args([
            "run",
            "--quiet",
            "--release",
            "-p",
            "midnight-solidity-verifier",
            "--bin",
            "generate_rsa",
        ])
        .env(
            "SRS_DIR",
            common::root_dir().parent().unwrap().parent().unwrap()
                .join("zk_stdlib/examples/assets"),
        )
        .current_dir(common::root_dir().parent().unwrap().parent().unwrap())
        .status()
        .expect("cargo run generate_rsa");
    assert!(status.success(), "generate_rsa failed");
}

fn read_public_inputs(path: &std::path::Path) -> Vec<[u8; 32]> {
    let blob = fs::read(path).expect("read instance.bin");
    assert!(blob.len() >= 8, "instance blob too short");
    let mut n_be = [0u8; 8];
    n_be.copy_from_slice(&blob[0..8]);
    let n = u64::from_be_bytes(n_be) as usize;
    assert_eq!(blob.len(), 8 + 32 * n, "instance blob size mismatch");
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let mut limb = [0u8; 32];
        limb.copy_from_slice(&blob[8 + 32 * i..8 + 32 * (i + 1)]);
        out.push(limb);
    }
    out
}

#[test]
fn rsa_harness_verifies_fixture_proof() {
    ensure_rsa_fixtures();

    let fixtures = common::root_dir().join("fixtures").join(RSA_SIGNATURE.fixtures_subdir);
    let proof = fs::read(fixtures.join("proof.bin")).expect("read proof.bin");
    let public_inputs = read_public_inputs(&fixtures.join("instance.bin"));

    let (mut h, dep) = Harness::fresh_for(RSA_SIGNATURE, None, None);
    let ok = h.verify_multi(&dep, &public_inputs, &proof);
    assert!(ok, "Rust-driven RSA verify returned false");
}
