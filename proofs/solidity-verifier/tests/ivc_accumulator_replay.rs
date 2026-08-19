// SPDX-License-Identifier: CC0-1.0
//! CI-runnable adversarial replay of the public-accumulator decode path.
//!
//! The accumulator decoder in
//! `templates/partials/verifier/AccumulatorHelpers.yul` had no executing test
//! coverage. The tests that looked like they covered it
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
//! Two fixtures are replayed, covering both accumulator encodings:
//!
//! - `fixtures/ivc` -- the IVC Keccak decider, `AccumulatorEncoding::new`,
//!   which carries explicit lhs/rhs scalars.
//! - `fixtures/moonlight-wrap` -- the Moonlight wrap decider, `point_pair`,
//!   which does not. Its `expected_acc_has_carried_scalars = false` arms were
//!   previously only ever compiled, never executed against a proof.
//!
//! Each fixture's README records its provenance and regeneration command.
//!
//! A fixture describes itself: the accumulator offset, limb count and
//! `has_accumulator` flag are parsed back out of the rendered verifying-key
//! payload, the encoding kind is recovered from the payload width, and the
//! infinity encoding comes from the verifier's own constants. So this file
//! carries no per-fixture constants that could drift from the artifacts.
//!
//! Staleness caveat: these are snapshots of the codegen that produced them.
//! A fixture is self-consistent, so the replay keeps passing after a codegen
//! change -- it just stops testing current output. The commit stamp in each
//! README makes drift auditable; detecting it automatically would require
//! re-rendering, which needs the SRS again.

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

fn fixture_dir(fixture: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures").join(fixture)
}

fn read_fixture(fixture: &str, name: &str) -> Vec<u8> {
    let path = fixture_dir(fixture).join(name);
    std::fs::read(&path).unwrap_or_else(|err| panic!("missing fixture {}: {err}", path.display()))
}

fn read_fixture_string(fixture: &str, name: &str) -> String {
    String::from_utf8(read_fixture(fixture, name)).expect("fixture should be UTF-8")
}

/// Read an optional fixture file. Split renders ship a quotient evaluator;
/// single-contract renders do not.
fn read_optional_fixture_string(fixture: &str, name: &str) -> Option<String> {
    let path = fixture_dir(fixture).join(name);
    std::fs::read_to_string(path).ok()
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

fn assert_reverts(outcome: CallOutcome, case: &str) -> u64 {
    match outcome {
        CallOutcome::Revert { gas_used, .. } => gas_used,
        CallOutcome::Success { output, .. } => panic!(
            "{case}: verifier accepted a proof it must reject (output = 0x{})",
            hex::encode(output)
        ),
        CallOutcome::Halt { reason, .. } => {
            panic!("{case}: expected a revert but the call halted ({reason})")
        }
    }
}

/// Assert a revert that happened *before* the transcript was built.
///
/// Every accumulator word is also absorbed into the Keccak transcript, so any
/// mutation inside the instance region changes the challenges and would fail at
/// the pairing even if its dedicated decoder guard were deleted. Anchoring on
/// gas distinguishes the two: `validate_public_accumulator` runs before the
/// transcript, so a guard that fires costs a small fraction of a full run.
/// Without this, a deleted guard would leave the test passing for the wrong
/// reason.
fn assert_reverts_before_transcript(outcome: CallOutcome, accepted_gas: u64, case: &str) {
    let gas_used = assert_reverts(outcome, case);
    let ceiling = accepted_gas / 2;
    assert!(
        gas_used < ceiling,
        "{case}: reverted after {gas_used} gas, but an accumulator decode guard should \
         fire before the transcript (under {ceiling}, vs {accepted_gas} for a full \
         accepted run). This revert came from a later stage, so the guard under test \
         may no longer be reachable."
    );
}

/// Assert a revert that happened only *after* the full verification ran.
///
/// This is the signature of a Fiat-Shamir binding failure: the input was
/// structurally valid, so every range, packing, and framing check passed and
/// the proof failed at the final pairing. A cheap revert here would mean some
/// earlier check rejected the input instead, which proves nothing about
/// binding.
fn assert_reverts_at_pairing(outcome: CallOutcome, accepted_gas: u64, case: &str) {
    let gas_used = assert_reverts(outcome, case);
    let floor = accepted_gas / 4 * 3;
    assert!(
        gas_used > floor,
        "{case}: reverted after only {gas_used} gas (expected over {floor}, near the \
         {accepted_gas} of a full accepted run). An early check rejected this input, so \
         it does not exercise instance binding."
    );
}

/// The IVC decider carries explicit lhs/rhs scalars
/// (`AccumulatorEncoding::new`).
#[test]
fn ivc_accumulator_decoder_rejects_malformed_public_accumulator() {
    replay_accumulator_fixture("ivc");
}

/// The Moonlight wrap decider uses the scalar-free `point_pair` encoding, whose
/// `expected_acc_has_carried_scalars = false` arms were previously only ever
/// compiled, never executed against a proof.
#[test]
fn wrap_point_pair_decoder_rejects_malformed_public_accumulator() {
    replay_accumulator_fixture("moonlight-wrap");
}

/// Replay a rendered accumulator fixture, then mutate the proof and public
/// inputs and assert every mutation is rejected.
///
/// The accept baseline is what gives the rejections meaning: without it a
/// "rejects" assertion could pass because the verifier rejects everything.
fn replay_accumulator_fixture(fixture: &str) {
    let verifier_solidity = read_fixture_string(fixture, "Halo2Verifier.sol");
    let vk_solidity = read_fixture_string(fixture, "Halo2VerifyingKey.sol");
    let calldata = read_fixture(fixture, "calldata.bin");

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
    let instance_count = read_u256_word(&calldata, instances_len_word);
    let first_acc_word = instances_len_word + 0x20 + final_acc_offset * 0x20;
    // 7 limbs of 56 bits pack 4 to a field element, so each coordinate takes 2
    // words and each point 4.
    assert_eq!(
        num_acc_limbs, 7,
        "limb count changed; the word arithmetic below no longer holds"
    );

    // Recover the encoding kind from the payload width rather than hardcoding
    // it per fixture: the accumulator occupies the instance tail, so eight
    // words is `point_pair` and ten is the scalar-carrying encoding.
    let acc_words = instance_count as usize - final_acc_offset;
    let has_carried_scalars = match acc_words {
        8 => false,
        10 => true,
        other => panic!(
            "unexpected accumulator payload of {other} words; expected 8 (point_pair) \
             or 10 (point-and-scalar)"
        ),
    };
    let scalar_stride = if has_carried_scalars { 0x20 } else { 0 };
    let lhs_scalar_word = first_acc_word + 4 * 0x20;
    let rhs_first_word = lhs_scalar_word + scalar_stride;
    let rhs_scalar_word = rhs_first_word + 4 * 0x20;
    let acc_end_word = rhs_scalar_word + scalar_stride;
    assert!(
        acc_end_word <= calldata.len(),
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
    let verifier_code = compile_solidity_with_runs(&verifier_solidity, SOLC_OPTIMIZE_RUNS);
    // Split renders pin a separately deployed quotient evaluator; single
    // contract renders take the verifying key alone.
    let verifier_address = match read_optional_fixture_string(fixture, "Halo2QuotientEvaluator.sol")
    {
        Some(quotient_solidity) => {
            let quotient_address = evm.create(compile_solidity_with_runs(
                &quotient_solidity,
                SOLC_OPTIMIZE_RUNS,
            ));
            evm.create_with_two_address_args(verifier_code, vk_address, quotient_address)
        }
        None => evm.create_with_address_arg(verifier_code, vk_address),
    };

    // Cost of a full accepted run, used below to attribute reverts to a stage:
    // an accumulator decode guard fires long before this, a binding failure
    // costs almost exactly this much.
    let accepted_gas;
    match evm.try_call_with_gas(verifier_address, calldata.clone(), GAS_CAP) {
        CallOutcome::Success {
            output, gas_used, ..
        } => {
            let expected: Vec<u8> = [vec![0u8; 31], vec![1]].concat();
            assert_eq!(
                output, expected,
                "fixture proof should verify; the fixture and calldata may be out of sync"
            );
            accepted_gas = gas_used;
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
        if has_carried_scalars {
            malformed[scalar_word..scalar_word + 0x20].fill(0);
        }
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

    // The canonical infinity above short-circuits at `is_acc_encoded_identity`,
    // so it never enters `load_acc_point`'s coordinate-decoding branch. The two
    // cases below are the non-canonical routes to the same nulled operand, and
    // each is caught by a different guard inside that branch.
    //
    // 1. Identity flag on `x`, honest `y`. `x` decodes to zero and sets `x_is_id`,
    //    but `y` does not, so the malformed-infinity check (`iszero(or(or(x_hi,
    //    x_lo), or(y_hi, y_lo)))`) must reject. Without it, `load_acc_point` would
    //    still write EIP-2537 infinity into the accumulator slot while `y` was
    //    arbitrary.
    for (case, point_word) in [
        (
            "LHS accumulator identity flag with honest y",
            first_acc_word,
        ),
        (
            "RHS accumulator identity flag with honest y",
            rhs_first_word,
        ),
    ] {
        let mut flagged = calldata.clone();
        // Only the two `x` words; `y` keeps its honest value.
        write_encoded_coordinate(&mut flagged, point_word, true, &verifier_solidity);
        assert_reverts_before_transcript(
            evm.try_call_with_gas(verifier_address, flagged, GAS_CAP),
            accepted_gas,
            case,
        );
    }

    // 2. Both coordinates carry the codec's zero sentinel (`p - 1`) with no
    //    identity flag. Every packing and field check accepts this, so the
    //    `decoded_zero` guard is the only thing separating "the codec's zero" from
    //    "EIP-2537's point at infinity".
    for (case, point_word) in [
        (
            "LHS accumulator decodes to zero without the identity flag",
            first_acc_word,
        ),
        (
            "RHS accumulator decodes to zero without the identity flag",
            rhs_first_word,
        ),
    ] {
        let mut decoded_zero = calldata.clone();
        write_encoded_coordinate(&mut decoded_zero, point_word, false, &verifier_solidity);
        write_encoded_coordinate(
            &mut decoded_zero,
            point_word + 2 * 0x20,
            false,
            &verifier_solidity,
        );
        assert_reverts_before_transcript(
            evm.try_call_with_gas(verifier_address, decoded_zero, GAS_CAP),
            accepted_gas,
            case,
        );
    }

    // ---------------------------------------------------------------------
    // Calldata framing. These attacks need no layout knowledge at all.
    // ---------------------------------------------------------------------
    let instance_count = read_u256_word(&calldata, instances_len_word);
    let mut framing_cases: Vec<(String, Vec<u8>)> = Vec::new();

    let mut trailing = calldata.clone();
    trailing.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    framing_cases.push(("extra trailing calldata".into(), trailing));

    let mut truncated = calldata.clone();
    truncated.pop();
    framing_cases.push(("truncated calldata".into(), truncated));

    let mut wrong_selector = calldata.clone();
    wrong_selector[3] ^= 0x01;
    framing_cases.push(("wrong function selector".into(), wrong_selector));

    for (case, offset, value) in [
        ("wrong proof ABI head", 0x04, 0x60),
        ("wrong instances ABI head", 0x24, 0x20),
        (
            "short proof length",
            PROOF_PAYLOAD_START - 0x20,
            proof_len as u64 - 0x20,
        ),
        (
            "long proof length",
            PROOF_PAYLOAD_START - 0x20,
            proof_len as u64 + 0x20,
        ),
        (
            "wrong instance array length",
            instances_len_word,
            instance_count + 1,
        ),
    ] {
        let mut mutated = calldata.clone();
        write_u256_word(&mut mutated, offset, value);
        framing_cases.push((case.into(), mutated));
    }

    for (case, mutated) in framing_cases {
        assert_reverts(
            evm.try_call_with_gas(verifier_address, mutated, GAS_CAP),
            &case,
        );
    }

    // ---------------------------------------------------------------------
    // Curve-level attacks on every proof commitment.
    //
    // The repacked proof opens with a run of EIP-2537 padded G1 points, so the
    // run length is discovered from the padding signature rather than
    // hardcoded: a regenerated fixture with a different commitment count stays
    // covered.
    // ---------------------------------------------------------------------
    let g1_count = padded_g1_block_count(&calldata, PROOF_PAYLOAD_START, proof_len);
    assert!(
        g1_count >= 8,
        "expected a run of padded G1 commitments at the proof head, found {g1_count}; \
         the fixture proof layout changed"
    );

    let p_hi = solidity_constant(&verifier_solidity, "BLS_P_HI");
    let mut p_lo = solidity_constant(&verifier_solidity, "BLS_P_MINUS_ONE_LO");
    // p - 1 ends in ...aaaa, so incrementing cannot carry out of the low byte.
    p_lo[31] += 1;

    for index in 0..g1_count {
        let at = PROOF_PAYLOAD_START + index * G1_PADDED_BYTES;

        // (0, 1) is field-canonical but off the curve: y^2 = x^3 + 4 gives
        // 1 != 4, so the G1 precompiles must reject it.
        let mut off_curve = calldata.clone();
        off_curve[at..at + G1_PADDED_BYTES].fill(0);
        off_curve[at + G1_PADDED_BYTES - 1] = 1;

        // x = p exactly: one past the largest canonical coordinate.
        let mut base_modulus = calldata.clone();
        base_modulus[at..at + 0x20].copy_from_slice(&p_hi);
        base_modulus[at + 0x20..at + 0x40].copy_from_slice(&p_lo);

        // EIP-2537 pads each 48-byte coordinate with 16 leading zero bytes.
        // Setting one is a non-canonical encoding of an otherwise valid point.
        let mut bad_padding = calldata.clone();
        bad_padding[at] ^= 0x01;

        for (label, mutated) in [
            ("off-curve", off_curve),
            ("base-modulus", base_modulus),
            ("non-canonical padding", bad_padding),
        ] {
            assert_reverts(
                evm.try_call_with_gas(verifier_address, mutated, GAS_CAP),
                &format!("{label} G1 at proof commitment {index}"),
            );
        }
    }

    // ---------------------------------------------------------------------
    // Scalar canonicality across the evaluation block that follows the
    // commitments, plus the non-accumulator public inputs.
    // ---------------------------------------------------------------------
    let fr_modulus = solidity_constant(&verifier_solidity, "FR_MODULUS");
    let evals_start = PROOF_PAYLOAD_START + g1_count * G1_PADDED_BYTES;
    let evals_end = PROOF_PAYLOAD_START + proof_len;
    assert!(
        evals_start < evals_end && (evals_end - evals_start).is_multiple_of(0x20),
        "evaluation block is not a whole number of words"
    );

    for (index, at) in (evals_start..evals_end).step_by(0x20).enumerate() {
        let mut noncanonical = calldata.clone();
        noncanonical[at..at + 0x20].copy_from_slice(&fr_modulus);
        assert_reverts(
            evm.try_call_with_gas(verifier_address, noncanonical, GAS_CAP),
            &format!("proof scalar {index} set to the Fr modulus"),
        );
    }

    // The accumulator words are covered above; sweep the remaining public
    // inputs for scalar canonicality.
    let first_instance_word = instances_len_word + 0x20;
    for index in 0..instance_count as usize {
        let at = first_instance_word + index * 0x20;
        if (first_acc_word..rhs_scalar_word + 0x20).contains(&at) {
            continue;
        }
        let mut noncanonical = calldata.clone();
        noncanonical[at..at + 0x20].copy_from_slice(&fr_modulus);
        assert_reverts(
            evm.try_call_with_gas(verifier_address, noncanonical, GAS_CAP),
            &format!("public input {index} set to the Fr modulus"),
        );
    }

    // ---------------------------------------------------------------------
    // Instance binding: a valid proof must not verify against different public
    // inputs.
    //
    // Every other mutation in this file is independently caught by a range,
    // packing, or framing check, so all of them would still revert if instance
    // absorption regressed -- wrong order, wrong count, wrong endianness, or
    // instances simply never absorbed. This case is the only one that fails
    // *because* the transcript binds the instances: the mutated word stays a
    // canonical field element and well inside its slot, so nothing but the
    // Fiat-Shamir challenges can distinguish it.
    //
    // The accumulator words are excluded because they have their own decode
    // guards; a revert there would not be attributable to binding.
    assert!(
        final_acc_offset > 0,
        "fixture has no non-accumulator public input to test instance binding with"
    );
    for index in 0..final_acc_offset {
        let at = first_instance_word + index * 0x20;
        let mut rebound = calldata.clone();
        // Flip the low bit: the nearest possible value, still canonical.
        rebound[at + 31] ^= 0x01;
        assert!(
            rebound[at..at + 0x20] < fr_modulus[..],
            "public input {index} left non-canonical by the bit flip; pick another mutation"
        );
        assert_ne!(
            &rebound[at..at + 0x20],
            &calldata[at..at + 0x20],
            "public input {index} was not actually modified"
        );
        assert_reverts_at_pairing(
            evm.try_call_with_gas(verifier_address, rebound, GAS_CAP),
            accepted_gas,
            &format!("public input {index} changed to a different canonical value"),
        );
    }
}

/// EIP-2537 padded G1: `x_hi, x_lo, y_hi, y_lo`.
const G1_PADDED_BYTES: usize = 4 * 0x20;

/// Count the leading run of EIP-2537 padded G1 points in the repacked proof.
///
/// Each coordinate is a 48-byte field element left-padded to 64 bytes, so the
/// high word of `x` and of `y` both start with sixteen zero bytes. Evaluation
/// scalars do not share that signature, which is what ends the run.
fn padded_g1_block_count(calldata: &[u8], proof_start: usize, proof_len: usize) -> usize {
    let mut count = 0;
    while (count + 1) * G1_PADDED_BYTES <= proof_len {
        let at = proof_start + count * G1_PADDED_BYTES;
        let x_pad_zero = calldata[at..at + 16].iter().all(|b| *b == 0);
        let y_pad_zero = calldata[at + 0x40..at + 0x50].iter().all(|b| *b == 0);
        if !(x_pad_zero && y_pad_zero) {
            break;
        }
        count += 1;
    }
    count
}

/// Write `value` as a big-endian EVM word at `offset`.
fn write_u256_word(calldata: &mut [u8], offset: usize, value: u64) {
    calldata[offset..offset + 0x20].fill(0);
    calldata[offset + 0x18..offset + 0x20].copy_from_slice(&value.to_be_bytes());
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
/// Overwrite the two packed words of one accumulator coordinate at
/// `coord_word` with the codec's zero sentinel `p - 1`, optionally folding in
/// the identity flag (one radix base) as the encoder does for `x`.
///
/// Unlike [`write_encoded_identity`] this touches a single coordinate, so the
/// result is deliberately *not* the canonical infinity quadruple and does not
/// short-circuit `is_acc_encoded_identity`.
fn write_encoded_coordinate(
    calldata: &mut [u8],
    coord_word: usize,
    with_identity_flag: bool,
    verifier_solidity: &str,
) {
    let first = if with_identity_flag {
        "BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG"
    } else {
        "BLS_P_MINUS_ONE_PACKED_0"
    };
    for (index, name) in [first, "BLS_P_MINUS_ONE_PACKED_1"].into_iter().enumerate() {
        let word = solidity_constant(verifier_solidity, name);
        let at = coord_word + index * 0x20;
        calldata[at..at + 0x20].copy_from_slice(&word);
    }
}

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
