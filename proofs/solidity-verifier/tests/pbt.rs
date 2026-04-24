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
        // to deploying a tampered VK contract).
        //
        // Historical note — the test used to pick `pos_hint % blob_len`
        // uniformly over every byte, but that is too strong: some blob
        // bytes are *structurally-invariant* under single-bit mutation
        // and cannot possibly produce a rejection:
        //
        //   * Gate-bytecode `OP_FIXED idx` arguments that point at a
        //     simple-selector column. Simple selectors never appear in
        //     the transcript; `_buildFixedEvalsFull` injects the
        //     implicit constant `1` for every simple-selector column,
        //     so flipping e.g. `OP_FIXED(15)` → `OP_FIXED(14)` (both
        //     simple selectors in the poseidon VK, which has
        //     simple_selector_cols = [13, 14, 15, 17]) leaves the gate
        //     polynomial's numerical value at x unchanged.
        //   * `gate_selector_cols` entries that point at interchangeable
        //     simple selectors (they fall into the same grouping
        //     bucket in the linearization MSM).
        //   * Zero-padding bytes at the tail of constants 3
        //     (blob[148..160)), which `_loadVk` never reads.
        //
        // These positions belong to legitimate equivalence classes in
        // the VK encoding, not to a verifier soundness bug — an
        // attacker gets nothing by flipping them. To keep the
        // rejection property meaningful we restrict `pos_hint` to the
        // cryptographic regions where a single-bit flip provably
        // changes either a Fiat-Shamir input or a curve point
        // consumed by the pairing:
        //
        //   [0..32)                  transcript_repr (Fq digest)
        //   [32..64)                 omega           (Fq)
        //   [160..fc_end)            fixed_comms     (G1 points)
        //   [fc_end..pc_end)         perm_comms      (G1 points)
        //   [pc_end..pc_end+256)     s_g2            (G2 point)
        //   [pc_end+256..ng2_end)    neg_g2          (G2 point)
        //
        // Any single-bit flip in these regions either (a) alters the
        // Fiat-Shamir seed and cascades into a wrong first challenge
        // and a failed pairing, (b) yields an off-curve point that
        // the EIP-2537 pairing precompile rejects, or (c) yields a
        // valid-but-wrong curve point that makes the pairing
        // identity fail. The packed constants [64..160) and the
        // post-core sections [ng2_end..) are deliberately excluded
        // because they contain padding and the interpreter-level
        // redundancies described above.
        let f = fx(seed);
        let (_, setup_dep) = harness_for(&f);  // prime artifacts + fixtures/vk.bin

        let vk_path = common::root_dir().join("fixtures/vk.bin");
        let vk_blob = fs::read(&vk_path).expect("read vk.bin");
        prop_assume!(vk_blob.len() >= 160);

        // Recover the G1/G2 region boundaries by parsing the blob
        // headers (constants 1 at [64..96), constants 3 at [128..160))
        // so the safe mutation window tracks the actual VK layout.
        //
        // Layout:
        //   constants 1 @ 64:
        //     [ 0..  8) n                     (u64)
        //     [ 8.. 12) k                     (u32)
        //     [12.. 16) num_advice_columns    (u32)
        //     [16.. 20) num_fixed_columns     (u32)  <-- blob[80..84)
        //     ...
        //   constants 3 @ 128:
        //     [ 0..  4) num_permutation_columns (u32) <-- blob[128..132)
        //     ...
        let num_fixed_cols = u32::from_be_bytes(
            vk_blob[80..84].try_into().unwrap(),
        ) as usize;
        let num_perm_cols = u32::from_be_bytes(
            vk_blob[128..132].try_into().unwrap(),
        ) as usize;
        let fc_start = 160;
        let fc_end = fc_start + num_fixed_cols * 128;
        let pc_end = fc_end + num_perm_cols * 128;
        let ng2_end = pc_end + 256 /* s_g2 */ + 256 /* neg_g2 */;
        prop_assume!(ng2_end <= vk_blob.len());

        // Virtual concatenation of the two safe regions:
        //   region 1 = [0..64)            (transcript_repr || omega)
        //   region 2 = [fc_start..ng2_end) (G1 commitments || G2 points)
        // pick a byte uniformly within the concatenation, then map
        // back to the real blob offset.
        let region1_len = 64;
        let region2_len = ng2_end - fc_start;
        let total_safe = region1_len + region2_len;
        let pick = (pos_hint as usize) % total_safe;
        let idx = if pick < region1_len {
            pick
        } else {
            fc_start + (pick - region1_len)
        };

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

/* -------------------------------------------------------------------- *
 *  Adversarial matrix replay                                           *
 * -------------------------------------------------------------------- */

/// Load `fixtures/adversarial_fixtures.bin` (produced by
/// `src/bin/generate.rs` Phase F1) and drive every entry through the
/// in-process verifier via `Harness::verify_raw`, asserting rejection
/// in every case. Uses the same binary manifest that
/// `test_adversarial_matrix_all_rejected` in the forge suite consumes.
///
/// This complements the per-property PBT tests by replaying a
/// deterministic pre-recorded set of rejection vectors — so a change
/// to the verifier that silently un-covers one of the rejection paths
/// is caught even when `proptest` happens to pick different seeds.
#[test]
#[ignore = "solidity/EVM-heavy; run in release mode"]
fn adversarial_matrix_all_rejected() {
    let f = fx(1);
    let (mut h, dep) = harness_for(&f);

    // Baseline sanity: the canonical on-disk proof must be accepted
    // (the manifest's rejection assertions are only meaningful against
    // a working baseline — otherwise a stuck-at-reject verifier would
    // vacuously pass).
    let baseline_proof =
        fs::read(common::root_dir().join("fixtures/proof.bin"))
            .expect("read proof.bin");
    let baseline_inst_raw =
        fs::read(common::root_dir().join("fixtures/instance.be"))
            .expect("read instance.be");
    assert_eq!(baseline_inst_raw.len(), 32, "instance.be must be 32 bytes");
    let mut baseline_inst = [0u8; 32];
    baseline_inst.copy_from_slice(&baseline_inst_raw);
    assert!(
        h.verify(&dep, baseline_inst, &baseline_proof),
        "baseline on-disk proof rejected — harness/fixture mismatch",
    );

    let manifest =
        fs::read(common::root_dir().join("fixtures/adversarial_fixtures.bin"))
            .expect("read adversarial_fixtures.bin");
    assert!(manifest.len() >= 8, "adversarial manifest truncated");

    let read_u32 = |b: &[u8], o: usize| -> u32 {
        u32::from_be_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
    };

    let mut off = 0usize;
    let version = read_u32(&manifest, off);
    off += 4;
    assert_eq!(version, 1, "unsupported adversarial manifest version");
    let num = read_u32(&manifest, off) as usize;
    off += 4;
    assert!(num > 0, "empty adversarial matrix");

    for i in 0..num {
        let kind = manifest[off];
        off += 1;
        let lab_len = manifest[off] as usize;
        off += 1;
        let label = std::str::from_utf8(&manifest[off..off + lab_len])
            .expect("utf-8 label")
            .to_string();
        off += lab_len;
        let mut inst = [0u8; 32];
        inst.copy_from_slice(&manifest[off..off + 32]);
        off += 32;
        let plen = read_u32(&manifest, off) as usize;
        off += 4;
        let proof = manifest[off..off + plen].to_vec();
        off += plen;

        // Use verify_raw so entries whose calldata-shape makes the
        // verifier revert (trunc/ext) are also counted as "rejected"
        // (revert on the low-level call yields ok == false).
        let cd = common::encode_verify_calldata(inst, &proof);
        let (ok, out) = h.verify_raw(&dep, cd);
        let accepted = Harness::raw_is_accept(ok, &out);
        assert!(
            !accepted,
            "adversarial entry [{i}] kind={kind} '{label}' accepted by verify()",
        );
    }
    assert_eq!(off, manifest.len(), "trailing bytes in adversarial manifest");
}
