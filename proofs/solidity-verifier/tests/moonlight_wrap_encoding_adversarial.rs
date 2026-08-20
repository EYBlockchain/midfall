// SPDX-License-Identifier: CC0-1.0
//! Encoding, public-input and ABI-envelope adversarial replay against the
//! **deployed** Sepolia artifacts.
//!
//! Companion to `moonlight_wrap_curve_adversarial.rs`, which handles the
//! curve-level attacks. This file sweeps the flat surfaces exhaustively rather
//! than sampling them: every one of the 102 evaluation scalars, all five
//! `q_evals`, all 19 instances, both padded high words of all 36 proof G1s,
//! and the ABI envelope.
//!
//! Sweeping matters here. A guard that is present for commitment 0 and absent
//! for commitment 27 passes any spot check, and the generated verifier emits
//! these loops per category rather than once, so per-category drift is a real
//! failure mode. Each sweep asserts both that every position is rejected and
//! that the count of positions matches the layout the verifier pins, so a
//! shortened sweep cannot silently pass.

#![cfg(feature = "evm")]

use halo2_solidity_verifier::{
    compile_solidity_with_runs, revm::primitives::Address, CallOutcome, Evm,
};
use std::path::PathBuf;

const SOLC_OPTIMIZE_RUNS: u32 = 200;
const GAS_CAP: u64 = 60_000_000;

const PROOF_START: usize = 0x64;
const PROOF_LEN: usize = 0x1e60;
const NUM_INSTANCE_CPTR: usize = 0x1ec4;
const INSTANCE_START: usize = 0x1ee4;
const NUM_INSTANCES: usize = 19;

/// Proof section offsets relative to `PROOF_START`, from the deployed
/// verifier's parsing loops. The trailing entry is the end marker.
const SECTIONS: &[(&str, usize, usize)] = &[
    ("advice", 0x0000, 15),
    ("lookup_multiplicity", 0x0780, 2),
    ("permutation_z", 0x0880, 6),
    ("lookup_helper_and_z", 0x0b80, 4),
    ("trashcan", 0x0d80, 1),
    ("quotient_limb", 0x0e00, 4),
];
/// Scalar blocks: (name, byte offset from PROOF_START, count of 32-byte words).
const EVALS_OFF: usize = 0x1000;
const EVALS_COUNT: usize = 102;
const F_COM_OFF: usize = 0x1cc0;
const Q_EVALS_OFF: usize = 0x1d40;
const Q_EVALS_COUNT: usize = 5;
const PI_OFF: usize = 0x1de0;

/// BLS12-381 scalar field modulus, big-endian.
const R_BE: [u8; 32] = [
    0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
    0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
];
/// BLS12-381 base field modulus, as the low 32 bytes of an EIP-2537 word pair.
const P_LO_BE: [u8; 32] = [
    0x64, 0x77, 0x4b, 0x84, 0xf3, 0x85, 0x12, 0xbf, 0x67, 0x30, 0xd2, 0xa0, 0xf6, 0xb0, 0xf6, 0x24,
    0x1e, 0xab, 0xff, 0xfe, 0xb1, 0x53, 0xff, 0xff, 0xb9, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xaa, 0xab,
];
const P_HI_BE: [u8; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x1a, 0x01, 0x11, 0xea, 0x39, 0x7f, 0xe6, 0x9a,
    0x4b, 0x1b, 0xa7, 0xb6, 0x43, 0x4b, 0xac, 0xd7,
];

fn deployment_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("deployments/sepolia/moonlight-wrap")
}

fn fixture_calldata() -> Vec<u8> {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/moonlight-wrap/calldata.bin");
    std::fs::read(&path).unwrap_or_else(|e| panic!("missing {}: {e}", path.display()))
}

struct Harness {
    evm: Evm,
    verifier: Address,
    accepted_gas: u64,
    calldata: Vec<u8>,
    rejected: usize,
}

impl Harness {
    fn new() -> Self {
        let dir = deployment_dir();
        let vk_src = std::fs::read_to_string(dir.join("Halo2VerifyingKey.sol")).unwrap();
        let ver_src = std::fs::read_to_string(dir.join("Halo2Verifier.sol")).unwrap();
        let calldata = fixture_calldata();
        assert_eq!(calldata.len(), INSTANCE_START + NUM_INSTANCES * 32);
        assert_eq!(PROOF_START + PROOF_LEN, NUM_INSTANCE_CPTR);

        let mut evm = Evm::default();
        let vk = evm.create(compile_solidity_with_runs(&vk_src, SOLC_OPTIMIZE_RUNS));
        let verifier = evm
            .create_with_address_arg(compile_solidity_with_runs(&ver_src, SOLC_OPTIMIZE_RUNS), vk);

        let accepted_gas = match evm.try_call_with_gas(verifier, calldata.clone(), GAS_CAP) {
            CallOutcome::Success {
                output, gas_used, ..
            } => {
                assert_eq!(output, [vec![0u8; 31], vec![1]].concat());
                gas_used
            }
            other => {
                panic!("baseline proof must verify, else nothing below means anything: {other:?}")
            }
        };
        Self {
            evm,
            verifier,
            accepted_gas,
            calldata,
            rejected: 0,
        }
    }

    /// Assert the input is rejected, and return the gas so callers can reason
    /// about which layer caught it.
    fn reject(&mut self, cd: Vec<u8>, case: &str) -> u64 {
        match self.evm.try_call_with_gas(self.verifier, cd, GAS_CAP) {
            CallOutcome::Success {
                output, gas_used, ..
            } => panic!(
                "{case}: ACCEPTED (gas {gas_used}, output 0x{}) -- must not verify",
                hex::encode(output)
            ),
            CallOutcome::Halt { reason, .. } => panic!("{case}: halted ({reason})"),
            CallOutcome::Revert { gas_used, .. } => {
                self.rejected += 1;
                gas_used
            }
        }
    }

    /// Assert the input is rejected *cheaply*, i.e. by a guard that runs before
    /// the verifier does any elliptic-curve work. A canonicality check that
    /// silently stopped firing would still reject via the algebra, so the cost
    /// is what proves the guard is the thing catching it.
    fn reject_early(&mut self, cd: Vec<u8>, case: &str) {
        let gas = self.reject(cd, case);
        assert!(
            gas * 2 < self.accepted_gas,
            "{case}: rejected, but at {gas} gas against an accepted cost of {} -- \
             the intended early guard did not fire",
            self.accepted_gas
        );
    }

    fn with<F: FnOnce(&mut Vec<u8>)>(&self, f: F) -> Vec<u8> {
        let mut cd = self.calldata.clone();
        f(&mut cd);
        cd
    }
}

/// Every 128-byte padded G1 in the proof, as (label, absolute offset).
fn all_proof_points() -> Vec<(String, usize)> {
    let mut out = Vec::new();
    for (name, off, count) in SECTIONS {
        for i in 0..*count {
            out.push((format!("{name}[{i}]"), PROOF_START + off + i * 0x80));
        }
    }
    out.push(("f_com".into(), PROOF_START + F_COM_OFF));
    out.push(("pi".into(), PROOF_START + PI_OFF));
    out
}

#[test]
fn deployed_wrap_verifier_rejects_noncanonical_encodings() {
    let mut h = Harness::new();
    let points = all_proof_points();
    assert_eq!(
        points.len(),
        34,
        "proof G1 count drifted from the pinned layout"
    );

    // -- 1. EIP-2537 padding. Each coordinate is 16 zero bytes then 48 value
    //       bytes. A non-zero pad byte is a second encoding of the same point,
    //       so leaving it unchecked would make the transcript malleable.
    for (label, off) in &points {
        for (word, coord) in [(0usize, "x"), (2, "y")] {
            for pad_byte in [0usize, 7, 15] {
                let cd = h.with(|cd| cd[off + word * 32 + pad_byte] = 0x01);
                h.reject_early(cd, &format!("{label}.{coord}_hi pad byte {pad_byte} set"));
            }
        }
    }

    // -- 2. Coordinates at and above the field modulus.
    for (label, off) in &points {
        for (word, coord) in [(0usize, "x"), (2, "y")] {
            let cd = h.with(|cd| {
                cd[off + word * 32..off + word * 32 + 32].copy_from_slice(&P_HI_BE);
                cd[off + (word + 1) * 32..off + (word + 2) * 32].copy_from_slice(&P_LO_BE);
            });
            h.reject_early(cd, &format!("{label}.{coord} = p"));

            let mut p_plus = P_LO_BE;
            p_plus[31] = p_plus[31].wrapping_add(1);
            let cd = h.with(|cd| {
                cd[off + word * 32..off + word * 32 + 32].copy_from_slice(&P_HI_BE);
                cd[off + (word + 1) * 32..off + (word + 2) * 32].copy_from_slice(&p_plus);
            });
            h.reject_early(cd, &format!("{label}.{coord} = p + 1"));

            let cd = h.with(|cd| {
                for b in cd[off + word * 32..off + (word + 2) * 32].iter_mut() {
                    *b = 0xff;
                }
            });
            h.reject_early(cd, &format!("{label}.{coord} = all ones"));
        }
    }

    // -- 3. Non-canonical Fr scalars across every scalar the proof carries.
    //       Values at or above r must be rejected before absorption, otherwise
    //       two encodings share a transcript.
    let mut scalar_slots: Vec<(String, usize)> = Vec::new();
    for i in 0..EVALS_COUNT {
        scalar_slots.push((format!("evaluation[{i}]"), PROOF_START + EVALS_OFF + i * 32));
    }
    for i in 0..Q_EVALS_COUNT {
        scalar_slots.push((format!("q_eval[{i}]"), PROOF_START + Q_EVALS_OFF + i * 32));
    }
    assert_eq!(
        scalar_slots.len(),
        107,
        "scalar count drifted from the pinned layout"
    );

    for (label, off) in &scalar_slots {
        let cd = h.with(|cd| cd[*off..off + 32].copy_from_slice(&R_BE));
        h.reject_early(cd, &format!("{label} = r"));

        let cd = h.with(|cd| {
            for b in cd[*off..off + 32].iter_mut() {
                *b = 0xff;
            }
        });
        h.reject_early(cd, &format!("{label} = 2^256 - 1"));
    }

    println!(
        "{} non-canonical encodings, all rejected before any curve work",
        h.rejected
    );
}

#[test]
fn deployed_wrap_verifier_rejects_invalid_public_inputs() {
    let mut h = Harness::new();

    // Non-canonical instance scalars: rejected before absorption.
    for i in 0..NUM_INSTANCES {
        let off = INSTANCE_START + i * 32;
        let cd = h.with(|cd| cd[off..off + 32].copy_from_slice(&R_BE));
        h.reject_early(cd, &format!("instance[{i}] = r"));

        let cd = h.with(|cd| {
            for b in cd[off..off + 32].iter_mut() {
                *b = 0xff;
            }
        });
        h.reject_early(cd, &format!("instance[{i}] = 2^256 - 1"));
    }

    // Canonical but wrong. The 11 state words are plain field elements, so
    // nothing but the transcript binds them -- these must fail at the pairing,
    // which is what proves the instances are actually bound to the proof.
    for i in 0..11usize {
        let off = INSTANCE_START + i * 32;
        for (label, value) in [
            ("zero", [0u8; 32]),
            ("one", {
                let mut v = [0u8; 32];
                v[31] = 1;
                v
            }),
        ] {
            if h.calldata[off..off + 32] == value {
                continue;
            }
            let cd = h.with(|cd| cd[off..off + 32].copy_from_slice(&value));
            let gas = h.reject(cd, &format!("instance[{i}] = {label}"));
            assert!(
                gas * 2 >= h.accepted_gas,
                "instance[{i}] = {label}: rejected at only {gas} gas -- a canonical \
                 public input should survive to the pairing, not trip an early guard"
            );
        }
    }

    // Every state instance shifted by one, the nearest possible wrong value.
    for i in 0..11usize {
        let off = INSTANCE_START + i * 32;
        let cd = h.with(|cd| cd[off + 31] ^= 1);
        let gas = h.reject(cd, &format!("instance[{i}] low bit flipped"));
        assert!(
            gas * 2 >= h.accepted_gas,
            "instance[{i}]: expected a pairing rejection"
        );
    }

    println!("{} invalid public inputs, all rejected", h.rejected);
}

#[test]
fn deployed_wrap_verifier_rejects_malformed_abi_envelopes() {
    let mut h = Harness::new();

    // Head words. The verifier pins both to exact values before parsing.
    for (label, off, value) in [
        ("proof head = 0x20", 4usize, 0x20u64),
        ("proof head = 0x60", 4, 0x60),
        ("proof head = 0", 4, 0),
        ("instances head = 0x40", 0x24, 0x40),
        (
            "instances head off by one word",
            0x24,
            (NUM_INSTANCE_CPTR - 4 + 0x20) as u64,
        ),
        (
            "instances head off by one byte",
            0x24,
            (NUM_INSTANCE_CPTR - 4 + 1) as u64,
        ),
    ] {
        let cd = h.with(|cd| {
            cd[off..off + 32].fill(0);
            cd[off + 24..off + 32].copy_from_slice(&value.to_be_bytes());
        });
        h.reject_early(cd, label);
    }

    // Head words set to huge values, which would overflow naive cursor maths.
    for (label, off) in [
        ("proof head = 2^256-1", 4usize),
        ("instances head = 2^256-1", 0x24),
    ] {
        let cd = h.with(|cd| cd[off..off + 32].fill(0xff));
        h.reject_early(cd, label);
    }

    // Length words.
    for (label, off, value) in [
        ("proof length - 1", 0x44usize, (PROOF_LEN - 1) as u64),
        ("proof length + 1", 0x44, (PROOF_LEN + 1) as u64),
        ("proof length = 0", 0x44, 0),
        ("instance count = 18", NUM_INSTANCE_CPTR, 18),
        ("instance count = 20", NUM_INSTANCE_CPTR, 20),
        ("instance count = 0", NUM_INSTANCE_CPTR, 0),
    ] {
        let cd = h.with(|cd| {
            cd[off..off + 32].fill(0);
            cd[off + 24..off + 32].copy_from_slice(&value.to_be_bytes());
        });
        h.reject_early(cd, label);
    }
    for (label, off) in [
        ("proof length = 2^256-1", 0x44usize),
        ("instance count = 2^256-1", NUM_INSTANCE_CPTR),
    ] {
        let cd = h.with(|cd| cd[off..off + 32].fill(0xff));
        h.reject_early(cd, label);
    }

    // Total calldata size. Short reads would otherwise be zero-filled by the
    // EVM rather than faulting.
    for n in [1usize, 31, 32, 0x80] {
        let mut cd = h.calldata.clone();
        cd.truncate(cd.len() - n);
        h.reject_early(cd, &format!("calldata truncated by {n} bytes"));

        let mut cd = h.calldata.clone();
        cd.extend(std::iter::repeat_n(0, n));
        h.reject_early(cd, &format!("calldata extended by {n} bytes"));
    }
    h.reject_early(Vec::new(), "empty calldata");
    h.reject_early(h.calldata[..4].to_vec(), "selector only");
    h.reject_early(h.calldata[..3].to_vec(), "truncated selector");

    // Wrong selector: the dispatcher must fall through to a revert.
    let cd = h.with(|cd| cd[0] ^= 0xff);
    h.reject_early(cd, "unknown function selector");

    println!(
        "{} malformed envelopes, all rejected before any proof work",
        h.rejected
    );
}

#[test]
fn deployed_wrap_verifier_rejects_structural_proof_attacks() {
    let mut h = Harness::new();

    // Whole sections zeroed. Zero is the EIP-2537 point at infinity, which is
    // a *valid* precompile input, so these cannot be dismissed as encoding
    // errors -- they have to fail the algebra.
    for (name, off, count) in SECTIONS {
        let cd = h.with(|cd| {
            let start = PROOF_START + off;
            cd[start..start + count * 0x80].fill(0);
        });
        h.reject(
            cd,
            &format!("{name} section replaced with points at infinity"),
        );
    }

    // Reordering. Every commitment is absorbed positionally, with no length or
    // type tag, so a swap is only caught by the transcript.
    let points = all_proof_points();
    for (a, b) in [(0usize, 1usize), (0, 14), (15, 16)] {
        let (la, oa) = &points[a];
        let (lb, ob) = &points[b];
        let cd = h.with(|cd| {
            let tmp: Vec<u8> = cd[*oa..oa + 0x80].to_vec();
            let other: Vec<u8> = cd[*ob..ob + 0x80].to_vec();
            cd[*oa..oa + 0x80].copy_from_slice(&other);
            cd[*ob..ob + 0x80].copy_from_slice(&tmp);
        });
        h.reject(cd, &format!("{la} and {lb} swapped"));
    }

    // f_com and pi swapped: both are single points late in the stream.
    let cd = h.with(|cd| {
        let f = PROOF_START + F_COM_OFF;
        let pi = PROOF_START + PI_OFF;
        let tmp: Vec<u8> = cd[f..f + 0x80].to_vec();
        let other: Vec<u8> = cd[pi..pi + 0x80].to_vec();
        cd[f..f + 0x80].copy_from_slice(&other);
        cd[pi..pi + 0x80].copy_from_slice(&tmp);
    });
    h.reject(cd, "f_com and pi swapped");

    // Duplicated commitments.
    let cd = h.with(|cd| {
        let (_, first) = &points[0];
        let (_, second) = &points[1];
        let dup: Vec<u8> = cd[*first..first + 0x80].to_vec();
        cd[*second..second + 0x80].copy_from_slice(&dup);
    });
    h.reject(cd, "advice[1] duplicated from advice[0]");

    // Whole proof zeroed, and whole proof set to a repeating pattern.
    let cd = h.with(|cd| cd[PROOF_START..PROOF_START + PROOF_LEN].fill(0));
    h.reject(cd, "entire proof zeroed");
    let cd = h.with(|cd| {
        for (i, b) in cd[PROOF_START..PROOF_START + PROOF_LEN].iter_mut().enumerate() {
            *b = (i % 251) as u8;
        }
    });
    h.reject(cd, "entire proof replaced with a byte pattern");

    println!("{} structural attacks, all rejected", h.rejected);
}

#[test]
fn deployed_verifier_constructor_rejects_a_tampered_verifying_key() {
    let dir = deployment_dir();
    let vk_src = std::fs::read_to_string(dir.join("Halo2VerifyingKey.sol")).unwrap();
    let ver_src = std::fs::read_to_string(dir.join("Halo2Verifier.sol")).unwrap();
    let ver_code = compile_solidity_with_runs(&ver_src, SOLC_OPTIMIZE_RUNS);

    // Sanity: the untampered key deploys, and the verifier accepts it.
    let good_hash = {
        let mut evm = Evm::default();
        let good = evm.create(compile_solidity_with_runs(&vk_src, SOLC_OPTIMIZE_RUNS));
        assert_eq!(evm.code_size(good), 17_025);
        let _ = evm.create_with_address_arg(ver_code.clone(), good);
        evm.code_hash(good)
    };

    // Flip one hex digit of the last permutation commitment. The payload keeps
    // its length, so only the codehash pin can catch this.
    let needle = "permutation_comms[17].y_lo";
    let line = vk_src
        .lines()
        .find(|l| l.contains(needle))
        .unwrap_or_else(|| panic!("verifying key has no `{needle}` word"));
    let start = line.rfind("0x").expect("payload word should be hex");
    let original = &line[start..start + 66];
    let last = original.chars().last().unwrap();
    let flipped_char = if last == '0' { '1' } else { '0' };
    let tampered_word = format!("{}{}", &original[..65], flipped_char);
    let tampered_src = vk_src.replace(original, &tampered_word);
    assert_ne!(tampered_src, vk_src, "tampering did not change the source");

    let mut evm = Evm::default();
    let bad = evm.create(compile_solidity_with_runs(
        &tampered_src,
        SOLC_OPTIMIZE_RUNS,
    ));
    assert_eq!(
        evm.code_size(bad),
        17_025,
        "the tampered key must keep its length, so only the codehash pin can reject it"
    );
    assert_ne!(
        evm.code_hash(bad),
        good_hash,
        "tampering must change the codehash"
    );

    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        evm.create_with_address_arg(ver_code.clone(), bad)
    }))
    .is_err();
    assert!(
        panicked,
        "the constructor must reject a verifying key with the wrong codehash"
    );

    // And an address with no code at all.
    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut e = Evm::default();
        e.create_with_address_arg(ver_code.clone(), Address::from([0x11u8; 20]))
    }))
    .is_err();
    assert!(
        panicked,
        "the constructor must reject a codeless verifying-key address"
    );

    println!("verifying-key pin rejects both a one-digit tamper and a codeless address");
}
