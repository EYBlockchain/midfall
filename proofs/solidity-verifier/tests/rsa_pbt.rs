//! RSA-signature property-based tests.
//!
//! Mirrors the cheap subset of `tests/pbt.rs` but reuses the **cached**
//! RSA proof + VK fixture instead of regenerating one per iteration —
//! `generate_rsa` runs the heavy biguint prover and takes ~30 s per
//! invocation, which is unworkable for property fuzzing. Each property
//! below operates by tampering with the cached artifacts and asserting
//! that the deployed `PlonkVerifier(RsaSignatureVerifyingKey)` rejects.
//!
//! All tests are `#[ignore]` by default. Run with:
//!     cargo test -p midnight-solidity-verifier --test rsa_pbt --release \
//!         -- --ignored --test-threads=1
//!
//! Wall time: ≈4 s per test for `CASES = 8` iterations on an M2-class
//! machine (after the one-off ~30 s `generate_rsa` priming run).

mod common;

use std::{fs, process::Command};

use proptest::prelude::*;

use crate::common::{encode_verify_calldata, Deployed, Harness, RSA_SIGNATURE};

/// Low iteration count keeps PBT smoke-fast. Bump locally when fuzzing.
const CASES: u32 = 8;

fn ensure_rsa_fixtures() {
    let fixtures = common::root_dir()
        .join("fixtures")
        .join(RSA_SIGNATURE.fixtures_subdir);
    let missing = ["proof.bin", "instance.bin"]
        .iter()
        .any(|f| !fixtures.join(f).exists());
    if !missing {
        return;
    }
    eprintln!("[rsa-pbt] fixtures missing — running `cargo run --bin generate_rsa`");
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
            common::root_dir()
                .parent()
                .unwrap()
                .parent()
                .unwrap()
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
    (0..n)
        .map(|i| {
            let mut limb = [0u8; 32];
            limb.copy_from_slice(&blob[8 + 32 * i..8 + 32 * (i + 1)]);
            limb
        })
        .collect()
}

fn cached_fixture() -> (Vec<u8>, Vec<[u8; 32]>) {
    ensure_rsa_fixtures();
    let fixtures = common::root_dir()
        .join("fixtures")
        .join(RSA_SIGNATURE.fixtures_subdir);
    let proof = fs::read(fixtures.join("proof.bin")).expect("read proof.bin");
    let pis = read_public_inputs(&fixtures.join("instance.bin"));
    (proof, pis)
}

fn fresh_rsa() -> (Harness, Deployed) {
    Harness::fresh_for(RSA_SIGNATURE, None, None)
}

/* -------------------------------------------------------------------- *
 *  Positive control: cached proof verifies.                            *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 1,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn rsa_pbt_cached_proof_verifies(_dummy: u8) {
        let (proof, pis) = cached_fixture();
        let (mut h, dep) = fresh_rsa();
        let ok = h.verify_multi(&dep, &pis, &proof);
        prop_assert!(ok, "cached RSA proof was rejected");
    }
}

/* -------------------------------------------------------------------- *
 *  Negative: malleated proof → verify() rejects.                       *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn rsa_pbt_rejects_malleated_proofs(bit_idx in 0usize..(2288 * 8)) {
        let (proof, pis) = cached_fixture();
        let mut mutated = proof.clone();
        let idx = (bit_idx / 8) % mutated.len();
        let bit = 1u8 << ((bit_idx % 8) as u8);
        mutated[idx] ^= bit;
        prop_assume!(mutated != proof);

        let (mut h, dep) = fresh_rsa();
        let ok = h.verify_multi(&dep, &pis, &mutated);
        prop_assert!(
            !ok,
            "verify accepted a malleated RSA proof (bit_idx {bit_idx})"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Negative: perturbed public input → verify() rejects.                *
 *                                                                      *
 *  RSA's `publicInputs` is a 22-limb byte32[] — flipping a bit in any  *
 *  of the limbs changes the Lagrange-evaluated instance polynomial    *
 *  and breaks the Fiat-Shamir transcript.                              *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn rsa_pbt_rejects_wrong_public_inputs(limb_idx in 0usize..22, bit in 0u8..255) {
        let (proof, mut pis) = cached_fixture();
        prop_assume!(limb_idx < pis.len());
        // Flip a low-order bit in the chosen limb so the result stays
        // in-range (below FR_MODULUS) for the verifier's range check.
        let byte_off = (bit as usize / 8) % 31 + 1; // skip the high byte
        pis[limb_idx][byte_off] ^= 1u8 << (bit % 8);

        let (mut h, dep) = fresh_rsa();
        let ok = h.verify_multi(&dep, &pis, &proof);
        prop_assert!(
            !ok,
            "verify accepted a perturbed public input (limb {limb_idx})"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Negative: malformed calldata (length truncation) → verify rejects.  *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn rsa_pbt_rejects_truncated_proof(trunc in 1usize..256) {
        let (proof, pis) = cached_fixture();
        prop_assume!(trunc < proof.len());
        let truncated = &proof[..proof.len() - trunc];

        let (mut h, dep) = fresh_rsa();
        // Build the calldata directly so the public-input prefix stays
        // valid; only the proof tail is short.
        let cd = encode_verify_calldata(&pis, truncated);
        let (call_ok, out) = h.verify_raw(&dep, cd);
        let accepted = Harness::raw_is_accept(call_ok, &out);
        prop_assert!(
            !accepted,
            "verify accepted a truncated proof (trunc {trunc})"
        );
    }
}
