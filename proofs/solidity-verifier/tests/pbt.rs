//! Property-based tests for the Solidity verifier.
//!
//! Analogous to the `pbt_solidity_*` patterns used elsewhere in the
//! workspace, but adapted to the Poseidon fixture that is the single
//! circuit this crate targets. The tests use `proptest` over the
//! `(seed, ...)` strategy space, and invoke the Solidity verifier
//! in-process via `revm` (see [`common::Harness`]).
//!
//! All tests are `#[ignore]` by default because:
//!   * `PoseidonFixture::build(6, seed)` runs a full KZG prove, which is
//!     heavy (~0.5–1 s in release; worse in debug).
//!   * The Solidity verify call itself performs ~32 pairing / EIP-2537
//!     operations and costs another ~100–300 ms per iteration.
//! Run with `cargo test -p midnight-solidity-verifier --test pbt --release -- --ignored`.
//!
//! Iteration count is intentionally low (8 cases per property) to keep
//! wall time bounded; bump it locally when you need deeper fuzzing.

mod common;

use std::fs;

use midnight_curves::Fq;
use midnight_solidity_verifier::{
    eip2537::fq_to_be,
    poseidon_fixture::PoseidonFixture,
};
use proptest::prelude::*;

use crate::common::{
    encode_verify_calldata, mutate_first_large_hex_literal, overwrite_u256_word,
    Deployed, Harness,
};

/// Poseidon example is fixed at k=6 in `zk_stdlib/examples/poseidon.rs`.
/// Varying `k` in PBT would require a parametric circuit; for this crate
/// we only vary the prover seed.
const K: u32 = 6;

/// Low iteration count keeps PBT smoke-fast. Bump locally when fuzzing.
const CASES: u32 = 8;

fn fx(seed: u64) -> PoseidonFixture {
    PoseidonFixture::build(K, seed)
}

fn instance_be(fx: &PoseidonFixture) -> [u8; 32] {
    fq_to_be(&fx.instance)
}

fn harness_for(fx: &PoseidonFixture) -> (Harness, Deployed) {
    // Always regenerate the VK contract + proof fixture on disk so the
    // deployed VK matches the proof. The harness picks up the freshly
    // built bytecode from `out/`.
    regen_contracts_to_match(fx);
    Harness::fresh()
}

/// Re-render the VK contract on disk to match `fx.vk` and re-run forge
/// build IF the source actually changed. The poseidon VK is
/// seed-independent, so after the first call every subsequent call is a
/// cheap file-content compare.
fn regen_contracts_to_match(fx: &PoseidonFixture) {
    use midnight_solidity_verifier::codegen::{render_verifying_key, VkInfo};
    let vk_info = VkInfo::from_live(fx.vk.vk(), &fx.srs);
    let sol = render_verifying_key(&vk_info);
    let vk_path = common::root_dir().join("contracts/PoseidonVerifyingKey.sol");

    let existing = fs::read_to_string(&vk_path).unwrap_or_default();
    // Also dump the VK blob so the mutated-VK tests can slice it.
    let vk_blob = midnight_solidity_verifier::codegen::vk_blob(&vk_info);
    let vk_bin_path = common::root_dir().join("fixtures/vk.bin");
    fs::write(&vk_bin_path, &vk_blob).expect("write vk.bin");

    if existing == sol {
        // VK contract unchanged — just make sure artifacts exist.
        common::ensure_build(false);
        return;
    }
    fs::write(&vk_path, sol).expect("write VK contract");
    common::ensure_build(true);
}

/* -------------------------------------------------------------------- *
 *  Determinism                                                         *
 * -------------------------------------------------------------------- */

/// Building the poseidon fixture twice with the same seed must produce
/// byte-identical instance and VK rendering. Proof bytes are NOT
/// asserted here because `midnight-proofs`' prover consumes randomness
/// beyond the seeded prover-rng (blinding values pulled from the
/// runtime OsRng), which makes proofs non-deterministic across runs
/// even for the same seed.
#[test]
#[ignore = "expensive property test; run in release mode"]
fn poseidon_render_is_deterministic_for_same_seed() {
    use midnight_solidity_verifier::codegen::{render_verifying_key, VkInfo};
    for seed in [0u64, 7, 99] {
        let a = fx(seed);
        let b = fx(seed);
        assert_eq!(a.instance, b.instance, "instance diverges (seed {seed})");
        let vi_a = VkInfo::from_live(a.vk.vk(), &a.srs);
        let vi_b = VkInfo::from_live(b.vk.vk(), &b.srs);
        assert_eq!(
            render_verifying_key(&vi_a),
            render_verifying_key(&vi_b),
            "VK rendering diverges (seed {seed})"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Positive: valid proof → verify() accepts.                           *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn pbt_solidity_verifies_poseidon_proofs(seed: u64) {
        let f = fx(seed);
        let (mut h, dep) = harness_for(&f);
        let ok = h.verify(&dep, instance_be(&f), &f.proof);
        prop_assert!(ok, "verify rejected a valid proof (seed {seed})");
    }
}

/* -------------------------------------------------------------------- *
 *  Negative: wrong instance → verify() rejects.                        *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn pbt_solidity_rejects_wrong_instances(seed: u64, delta: u64) {
        let f = fx(seed);
        // Perturb the instance by a non-zero Fr offset.
        let d = if delta == 0 { 1 } else { delta };
        let wrong = f.instance + Fq::from(d);
        prop_assume!(wrong != f.instance);
        let (mut h, dep) = harness_for(&f);
        let ok = h.verify(&dep, fq_to_be(&wrong), &f.proof);
        prop_assert!(!ok, "verify accepted a wrong instance (seed {seed})");
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
    fn pbt_solidity_rejects_malleated_proofs(seed: u64, bit_idx in 0usize..4096) {
        let f = fx(seed);
        let mut mutated = f.proof.clone();
        let idx = (bit_idx / 8) % mutated.len();
        let bit = 1u8 << ((bit_idx % 8) as u8);
        mutated[idx] ^= bit;
        prop_assume!(mutated != f.proof);
        let (mut h, dep) = harness_for(&f);
        let ok = h.verify(&dep, instance_be(&f), &mutated);
        prop_assert!(
            !ok,
            "verify accepted a malleated proof (seed {seed}, bit_idx {bit_idx})"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Negative: wrong VK → verify() rejects.                              *
 * -------------------------------------------------------------------- */

proptest! {
    #![proptest_config(ProptestConfig {
        cases: CASES,
        .. ProptestConfig::default()
    })]

    #[test]
    #[ignore = "expensive property test; run in release mode"]
    fn pbt_solidity_rejects_wrong_verifying_keys(seed: u64, pos_hint: u32) {
        // For the poseidon example the VK is seed-independent, so we
        // can't naively swap VKs between fixtures. Instead, mutate ONE
        // byte of the deployed VK blob (the verifier reads the blob
        // via `extcodecopy`, so patching the runtime code is equivalent
        // to deploying a tampered VK contract). The blob is large
        // enough that every position maps to a structurally-meaningful
        // field (transcript_repr / G1 commitments / gate bytecode /
        // query schedule), so any single-bit perturbation must make
        // the verifier reject.
        let f = fx(seed);
        let (_, setup_dep) = harness_for(&f);  // prime artifacts + fixtures/vk.bin

        let vk_path = common::root_dir().join("fixtures/vk.bin");
        let vk_blob = fs::read(&vk_path).expect("read vk.bin");
        prop_assume!(!vk_blob.is_empty());
        let idx = (pos_hint as usize) % vk_blob.len();
        let mut mutated = vk_blob;
        mutated[idx] ^= 0x01;

        let (mut h, dep) = Harness::fresh_with(Some(mutated), None);
        // Sanity: the mutated runtime code is attached at the same vk_addr.
        assert_eq!(setup_dep.vk_addr, dep.vk_addr);
        let ok = h.verify(&dep, instance_be(&f), &f.proof);
        prop_assert!(
            !ok,
            "verify accepted a mutated VK (seed {seed}, blob_pos {idx})"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Malformed calldata variants                                         *
 * -------------------------------------------------------------------- */

#[test]
#[ignore = "solidity/EVM-heavy; run in release mode"]
fn malformed_calldata_variants_are_rejected() {
    let f = fx(0);
    let (mut h, dep) = harness_for(&f);

    // Baseline: valid calldata must be accepted. This guards against a
    // broken harness that would make the negative cases trivially true.
    let valid = encode_verify_calldata(instance_be(&f), &f.proof);
    let (ok, out) = h.verify_raw(&dep, valid.clone());
    assert!(
        Harness::raw_is_accept(ok, &out),
        "baseline valid calldata was rejected"
    );

    // Flipped selector: verify reverts because the contract has no
    // matching function.
    let mut wrong_selector = valid.clone();
    wrong_selector[0] ^= 0x01;

    // Empty proof: `encode_verify_calldata` with a zero-length proof —
    // transcript reads fail immediately.
    let empty_proof = encode_verify_calldata(instance_be(&f), &[]);

    // Truncated proof: drop 64 bytes off the tail so we reliably slice
    // into real proof data (the poseidon fixture's calldata has only
    // 16 bytes of padding, so a 1-byte drop would silently target the
    // zero-filler instead).
    let truncated = valid[..valid.len() - 64].to_vec();

    // Claimed proof length is 32 bytes longer than the actual data, so
    // the ABI decoder tries to read past the calldata end and reverts.
    let mut wrong_proof_len = valid.clone();
    let proof_len_word_off = 4 + 32 + 32;
    let proof_len = f.proof.len();
    overwrite_u256_word(
        &mut wrong_proof_len,
        proof_len_word_off,
        proof_len as u64 + 32,
    );

    // Flipped instance byte: changes the public input so the Fiat-Shamir
    // sequence diverges from the prover's, which makes the first
    // sampled challenge wrong and cascades into a pairing mismatch.
    let mut wrong_instance = valid.clone();
    wrong_instance[4] ^= 0x01;

    for (name, cd) in [
        ("wrong selector", wrong_selector),
        ("empty proof", empty_proof),
        ("truncated proof", truncated),
        ("wrong proof length header", wrong_proof_len),
        ("flipped instance byte", wrong_instance),
    ] {
        let (ok, out) = h.verify_raw(&dep, cd);
        assert!(
            !Harness::raw_is_accept(ok, &out),
            "verify() accepted malformed calldata: {name}"
        );
    }
}

/* -------------------------------------------------------------------- *
 *  Mutated VK contract → verify() rejects.                             *
 * -------------------------------------------------------------------- */

#[test]
#[ignore = "solidity/EVM-heavy; run in release mode"]
fn mutated_vk_contract_is_rejected() {
    let f = fx(0);
    // First regenerate the VK contract to match this fixture, so the
    // baseline accepts.
    regen_contracts_to_match(&f);

    // Read the VK source, mutate the hex literal, write to a temporary
    // copy in the same directory so forge picks it up, then rebuild.
    let vk_path = common::root_dir().join("contracts/PoseidonVerifyingKey.sol");
    let backup = fs::read_to_string(&vk_path).expect("read VK");

    let mutated = mutate_first_large_hex_literal(&backup);
    assert_ne!(mutated, backup, "mutation must change the source");
    fs::write(&vk_path, &mutated).expect("write mutated VK");

    // Rebuild so forge emits the mutated blob, then restore the original.
    let rebuild = std::panic::catch_unwind(|| {
        common::ensure_build(true);
        let (mut h, dep) = Harness::fresh();
        h.verify(&dep, instance_be(&f), &f.proof)
    });

    // Restore the original source regardless of the test outcome.
    fs::write(&vk_path, &backup).expect("restore VK");
    common::ensure_build(true);

    let ok = rebuild.expect("test body panicked");
    assert!(!ok, "verify() accepted a mutated VK contract");
}
