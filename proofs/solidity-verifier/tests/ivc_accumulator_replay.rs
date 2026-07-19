// SPDX-License-Identifier: CC0-1.0
//! CI-runnable adversarial replay of the public-accumulator decode path.
//!
//! The accumulator decoder in `templates/partials/verifier/AccumulatorHelpers.yul`
//! had no executing test coverage. The tests that looked like they covered it
//! -- `accumulator_decoder_rejects_noncanonical_infinity` and friends in
//! `src/lowering/tests.rs` -- are `verifier_template.contains("...")` string
//! greps over the raw template. They assert the guard *text* exists and never
//! render, compile, or run it. That is why the always-false `and` guard in
//! `load_acc_coord_shifted` survived: those greps passed for as long as the
//! identity branch was dead code.
//!
//! The only executing accumulator tests live in `tests/ivc_keccak_solidity.rs`,
//! which proves a k=20 decider from scratch and needs ~300 MB of SRS, so it is
//! gated behind `HALO2_SOLIDITY_RUN_IVC_BENCH=1` and never runs in CI.
//!
//! This test closes that gap by replaying *pre-rendered* artifacts. Because it
//! ships the generated Solidity and the matching calldata rather than a
//! verifying key, it needs neither SRS nor a proving run nor
//! `midnight-aggregation` -- only solc and revm. A verifier cannot be rendered
//! from a VK without the full SRS (`SolidityGenerator` consumes
//! `params.g_lagrange()`), which is what rules out a vk.bin-based replay.
//!
//! Regenerate the fixtures with:
//!
//! ```text
//! HALO2_SOLIDITY_RUN_IVC_BENCH=1 \
//!   SRS_DIR=/path/to/midfall/zk_stdlib/examples/assets \
//!   cargo test --release \
//!     --features evm,truncated-challenges,in-circuit-fewer-point-sets \
//!     --test ivc_keccak_solidity -- --nocapture
//! ```
//!
//! then copy `target/ivc-keccak-solidity-dump/{Halo2Verifier.sol,
//! Halo2VerifyingKey.sol,Halo2QuotientEvaluator.sol,calldata.bin}` into
//! `fixtures/ivc/` and update the commit stamp in `fixtures/ivc/README.md`.
//!
//! The fixture describes its own accumulator placement: the offset, limb count
//! and `has_accumulator` flag are parsed back out of the rendered verifying-key
//! payload, and the infinity encoding out of the verifier's own constants, so
//! this file carries no second copy that could drift.
//!
//! Staleness caveat: these are a snapshot of the codegen that produced them.
//! The fixture is self-consistent, so it keeps passing after a codegen change
//! -- it just stops testing current output. `fixtures/ivc/README.md` records
//! the source commit so drift is auditable; detecting it automatically would
//! require re-rendering, which needs the SRS again.

#![cfg(feature = "evm")]

use std::path::PathBuf;

use halo2_solidity_verifier::{compile_solidity_with_runs, CallOutcome, Evm};

/// The IVC verifier is large, so it is rendered and benched at `runs = 1`.
const SOLC_OPTIMIZE_RUNS: u32 = 1;
/// Generous cap so an unexpected loop reports OutOfGas rather than masquerading
/// as a revert.
const GAS_CAP: u64 = 5_000_000_000;
/// ABI prologue: selector, proof head, instances head, then the proof length
/// word. The proof payload starts immediately after.
const PROOF_PAYLOAD_START: usize = 4 + 0x40 + 0x20;

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/ivc")
}

fn read_fixture(name: &str) -> Vec<u8> {
    let path = fixture_dir().join(name);
    std::fs::read(&path)
        .unwrap_or_else(|err| panic!("missing IVC fixture {}: {err}", path.display()))
}

fn read_fixture_string(name: &str) -> String {
    String::from_utf8(read_fixture(name)).expect("fixture should be UTF-8")
}

/// Read a labelled VK payload word out of the rendered verifying-key source.
///
/// The generator emits each header word as
/// `mstore(add(payload, 0x...), 0x...) // name`, so the fixture describes its
/// own accumulator placement and this test does not have to carry a second
/// copy that could drift out of sync with the artifact.
fn vk_payload_word(vk_solidity: &str, name: &str) -> u64 {
    let suffix = format!("// {name}");
    let line = vk_solidity
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("mstore(") && line.ends_with(&suffix))
        .unwrap_or_else(|| panic!("verifying-key source has no `{name}` payload word"));
    let value = line
        .rsplit_once("0x")
        .expect("payload word should be hex")
        .1
        .split_whitespace()
        .next()
        .expect("payload word should have a value")
        .trim_end_matches(')');
    u64::from_str_radix(value.trim_start_matches('0'), 16).unwrap_or(0)
}

fn read_u256_word(calldata: &[u8], offset: usize) -> u64 {
    let word = &calldata[offset..offset + 0x20];
    assert!(
        word[..24].iter().all(|b| *b == 0),
        "word at {offset:#x} does not fit in u64"
    );
    u64::from_be_bytes(word[24..].try_into().unwrap())
}

fn assert_reverts(outcome: CallOutcome, case: &str) {
    match outcome {
        CallOutcome::Revert { .. } => {}
        CallOutcome::Success { output, .. } => panic!(
            "{case}: verifier accepted a proof it must reject (output = 0x{})",
            hex::encode(output)
        ),
        CallOutcome::Halt { reason, .. } => {
            panic!("{case}: expected a revert but the call halted ({reason})")
        }
    }
}

/// Replay the shipped IVC accumulator fixture, then mutate the accumulator
/// public inputs and assert every mutation is rejected.
///
/// The accept baseline is what gives the rejections meaning: without it a
/// "rejects" assertion could pass because the verifier rejects everything.
#[test]
fn ivc_accumulator_decoder_rejects_malformed_public_accumulator() {
    let verifier_solidity = read_fixture_string("Halo2Verifier.sol");
    let vk_solidity = read_fixture_string("Halo2VerifyingKey.sol");
    let quotient_solidity = read_fixture_string("Halo2QuotientEvaluator.sol");
    let calldata = read_fixture("calldata.bin");

    assert_eq!(
        vk_payload_word(&vk_solidity, "has_accumulator"),
        1,
        "fixture must be a public-accumulator render, otherwise this test \
         exercises none of AccumulatorHelpers.yul"
    );
    let final_acc_offset = vk_payload_word(&vk_solidity, "acc_offset") as usize;
    let num_acc_limbs = vk_payload_word(&vk_solidity, "num_acc_limbs");

    // Derive the accumulator's calldata position from the ABI layout; the
    // fixture describes its own instance-space offset via the VK payload.
    let proof_len = read_u256_word(&calldata, PROOF_PAYLOAD_START - 0x20) as usize;
    let instances_len_word = PROOF_PAYLOAD_START + proof_len;
    let first_acc_word = instances_len_word + 0x20 + final_acc_offset * 0x20;
    // 7 limbs of 56 bits pack 4 to a field element, so each coordinate takes 2
    // words and each point 4, with one scalar word following.
    assert_eq!(
        num_acc_limbs, 7,
        "limb count changed; the word arithmetic below no longer holds"
    );
    let lhs_scalar_word = first_acc_word + 4 * 0x20;
    let rhs_first_word = lhs_scalar_word + 0x20;
    let rhs_scalar_word = rhs_first_word + 4 * 0x20;
    assert!(
        rhs_scalar_word + 0x20 <= calldata.len(),
        "accumulator words run past the fixture calldata; the fixture is inconsistent"
    );

    // Guard the offset arithmetic above. Without this, a miscomputed
    // `first_acc_word` would still make every mutation below revert -- for the
    // wrong reason -- and the test would pass while exercising nothing.
    //
    // Four 56-bit limbs occupy the low 224 bits of a packed word, so the top
    // four bytes of every accumulator coordinate word must be zero. Random
    // proof or instance bytes would not satisfy this.
    for (index, word_start) in [first_acc_word, rhs_first_word]
        .into_iter()
        .flat_map(|point| (0..4).map(move |w| point + w * 0x20))
        .enumerate()
    {
        assert_eq!(
            &calldata[word_start..word_start + 4],
            &[0u8; 4],
            "accumulator coordinate word {index} at {word_start:#x} has non-zero high bytes; \
             the computed accumulator offset does not point at packed limbs"
        );
    }

    let mut evm = Evm::default();
    let vk_address = evm.create(compile_solidity_with_runs(&vk_solidity, SOLC_OPTIMIZE_RUNS));
    let quotient_address = evm.create(compile_solidity_with_runs(
        &quotient_solidity,
        SOLC_OPTIMIZE_RUNS,
    ));
    let verifier_address = evm.create_with_two_address_args(
        compile_solidity_with_runs(&verifier_solidity, SOLC_OPTIMIZE_RUNS),
        vk_address,
        quotient_address,
    );

    match evm.try_call_with_gas(verifier_address, calldata.clone(), GAS_CAP) {
        CallOutcome::Success { output, .. } => {
            let expected: Vec<u8> = [vec![0u8; 31], vec![1]].concat();
            assert_eq!(
                output, expected,
                "fixture proof should verify; the fixture and calldata may be out of sync"
            );
        }
        CallOutcome::Revert { gas_used, output } => panic!(
            "fixture proof was rejected (gas_used = {gas_used}, output = 0x{}); \
             regenerate fixtures/ivc -- see this file's header",
            hex::encode(output)
        ),
        CallOutcome::Halt { gas_used, reason } => {
            panic!("fixture proof halted (gas_used = {gas_used}, reason = {reason})")
        }
    }

    // Limbs are 56 bits packed 4 to a word, so the first word carries 224
    // significant bits. Byte 3 is the lowest unused high byte in the
    // big-endian word: setting it keeps the value below the Fr modulus, so
    // only `check_acc_coord_packing` can catch it.
    let mut bad_packing = calldata.clone();
    bad_packing[first_acc_word + 3] ^= 0x01;
    assert_reverts(
        evm.try_call_with_gas(verifier_address, bad_packing, GAS_CAP),
        "non-canonical accumulator limb packing",
    );

    // Perturb a coordinate and zero its scalar, so the term cannot be
    // dismissed as a no-op multiply and has to fail the point decode.
    for (case, point_word, scalar_word) in [
        (
            "malformed LHS accumulator point",
            first_acc_word,
            lhs_scalar_word,
        ),
        (
            "malformed RHS accumulator point",
            rhs_first_word,
            rhs_scalar_word,
        ),
    ] {
        let mut malformed = calldata.clone();
        malformed[point_word + 31] ^= 0x01;
        malformed[scalar_word..scalar_word + 0x20].fill(0);
        assert_reverts(
            evm.try_call_with_gas(verifier_address, malformed, GAS_CAP),
            case,
        );
    }

    // Substituting the canonical point at infinity for a real accumulator term
    // must not verify. This is the encoding `is_acc_encoded_identity` accepts,
    // so it exercises the identity path rather than the range check.
    for (case, point_word) in [
        (
            "LHS accumulator replaced with encoded infinity",
            first_acc_word,
        ),
        (
            "RHS accumulator replaced with encoded infinity",
            rhs_first_word,
        ),
    ] {
        let mut identity = calldata.clone();
        write_encoded_identity(&mut identity, point_word, &verifier_solidity);
        assert_reverts(
            evm.try_call_with_gas(verifier_address, identity, GAS_CAP),
            case,
        );
    }
}

/// Read a rendered `uint256 internal constant NAME = 0x...;` out of the
/// fixture's verifier source.
///
/// Parsing the constants back out of the artifact under test keeps this file
/// from carrying a second copy of them: if codegen ever changes the encoding,
/// the vector below follows automatically instead of silently testing a stale
/// literal.
fn solidity_constant(source: &str, name: &str) -> [u8; 0x20] {
    let needle = format!("constant {name} ");
    let line = source
        .lines()
        .map(str::trim)
        .find(|line| line.starts_with("uint256") && line.contains(&needle))
        .unwrap_or_else(|| panic!("verifier source has no constant `{name}`"));
    let hex_value = line
        .split_once("0x")
        .expect("constant should be hex")
        .1
        .trim_end_matches(';')
        .trim();
    let bytes = hex::decode(format!("{hex_value:0>64}"))
        .unwrap_or_else(|err| panic!("constant `{name}` is not hex: {err}"));
    bytes.try_into().expect("constant should be one EVM word")
}

/// Overwrite the four accumulator coordinate words at `point_word` with the
/// canonical encoded point at infinity.
///
/// This is the exact quadruple `is_acc_encoded_identity` accepts: `p - 1` in
/// every packed word, with the identity flag (one radix base) folded into the
/// first word of `x`.
fn write_encoded_identity(calldata: &mut [u8], point_word: usize, verifier_solidity: &str) {
    for (index, name) in [
        "BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG",
        "BLS_P_MINUS_ONE_PACKED_1",
        "BLS_P_MINUS_ONE_PACKED_0",
        "BLS_P_MINUS_ONE_PACKED_1",
    ]
    .into_iter()
    .enumerate()
    {
        let word = solidity_constant(verifier_solidity, name);
        let at = point_word + index * 0x20;
        calldata[at..at + 0x20].copy_from_slice(&word);
    }
}
