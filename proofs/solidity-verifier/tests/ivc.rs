//! Rust-driven revm smoke test for the IVC single-circuit aggregation.
//!
//! Parallels `test/IvcVerifier.t.sol` — deploys the generic
//! `PlonkVerifier` wired to `IvcVerifyingKey` and calls
//! `verify(publicInputs, proof)` on the fixture produced by
//! `bin/generate_ivc`.
//!
//! Running under `cargo test --test ivc` is fast (Solidity artifacts
//! must exist; the IVC chain itself is regenerated only when the
//! fixtures are missing — a fresh `generate_ivc` run takes ~90-120 s
//! in release because of the k=19 IVC circuit).

mod common;

use std::{fs, process::Command};

use common::{Harness, IVC};

/// Regenerate the IVC fixtures if any of them are missing.  Skipped
/// by default because a fresh `generate_ivc` run takes ~90-120 s.
fn ensure_ivc_fixtures() {
    let fixtures = common::root_dir().join("fixtures").join(IVC.fixtures_subdir);
    let missing = ["proof.bin", "instance.bin"]
        .iter()
        .any(|f| !fixtures.join(f).exists());
    if !missing {
        return;
    }
    eprintln!("[ivc] fixtures missing — running `cargo run --bin generate_ivc`");
    let status = Command::new(env!("CARGO"))
        .args([
            "run",
            "--quiet",
            "--release",
            "-p",
            "midnight-solidity-verifier",
            "--bin",
            "generate_ivc",
        ])
        .env(
            "SRS_DIR",
            common::root_dir()
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("zk_stdlib/examples/assets"),
        )
        .current_dir(common::root_dir().parent().unwrap().parent().unwrap())
        .status()
        .expect("cargo run generate_ivc");
    assert!(status.success(), "generate_ivc failed");
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
fn ivc_harness_verifies_fixture_proof() {
    ensure_ivc_fixtures();

    let fixtures = common::root_dir().join("fixtures").join(IVC.fixtures_subdir);
    let proof = fs::read(fixtures.join("proof.bin")).expect("read proof.bin");
    let public_inputs = read_public_inputs(&fixtures.join("instance.bin"));

    let (mut h, dep) = Harness::fresh_for(IVC, None, None);
    // Direct call with a much larger gas budget — IVC has 110 public
    // inputs which means 110 Lagrange evaluations on the verifier
    // side, well beyond the 30M default cap.  Surface the actual
    // execution status so we can distinguish "verify returned false"
    // from "out of gas / revert".
    let cd = common::encode_verify_calldata(&public_inputs, &proof);
    let (ok, out) = h.call_raw_with_gas(dep.verifier_addr, cd, 1_000_000_000);
    if !ok {
        // Decode an `Error(string)` revert reason if present.
        if out.len() >= 4 + 64 {
            let selector = &out[0..4];
            // selector("Error(string)") = 0x08c379a0
            if selector == [0x08, 0xc3, 0x79, 0xa0] {
                let len = u64::from_be_bytes(out[4 + 32 + 24..4 + 32 + 32].try_into().unwrap())
                    as usize;
                let s = std::str::from_utf8(&out[4 + 64..4 + 64 + len]).unwrap_or("<non-utf8>");
                panic!("verify() reverted with: {s:?}");
            }
        }
        panic!(
            "verify() reverted, raw out (len {}) = 0x{}",
            out.len(),
            hex::encode(&out)
        );
    }
    let accepted = out.len() >= 32 && out[..32].iter().any(|b| *b != 0);
    assert!(accepted, "Rust-driven IVC verify returned false");
}
