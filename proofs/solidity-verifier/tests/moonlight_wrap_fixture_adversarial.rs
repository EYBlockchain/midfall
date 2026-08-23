// SPDX-License-Identifier: CC0-1.0
//! Adversarial replay against the **fixture** render of the Moonlight wrap
//! verifier, i.e. `fixtures/moonlight-wrap/{Halo2Verifier.sol,
//! Halo2VerifyingKey.sol}`.
//!
//! The two existing adversarial suites -- `moonlight_wrap_curve_adversarial`
//! and `moonlight_wrap_encoding_adversarial` -- target
//! `deployments/sepolia/moonlight-wrap`, the older `^0.8.24` render that is
//! actually on chain. That render predates the typed-error taxonomy, so those
//! suites can only assert *that* a call reverted.
//!
//! This file targets the newer fixture pair and asserts three things per case
//! instead of one:
//!
//!   1. the input is rejected;
//!   2. it is rejected with the **specific** typed error the design assigns to
//!      that failure class (a guard that fires but reports the wrong taxonomy
//!      is a real defect: `docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md`
//!      routes incident response off these selectors);
//!   3. it is rejected at the right **depth**, measured in gas -- an encoding
//!      guard must fire long before the pairing, and a binding failure must
//!      fire only at the pairing. Without the depth anchor a deleted guard
//!      still leaves a green test, because every mutation inside the
//!      transcript also breaks Fiat-Shamir.
//!
//! Coverage is organised by attack surface:
//!
//!   * ABI envelope (heads, lengths, calldatasize, selector)
//!   * verifying-key binding (constructor pin, per-proof re-check, tampering)
//!   * scalar canonicality (every eval, every q_eval, every instance)
//!   * G1 encoding (EIP-2537 padding, coordinates >= p, all 34 proof points)
//!   * curve membership and r-order subgroup
//!   * Fiat-Shamir binding (single-bit mutations that must survive to the
//!     pairing, commitment swaps, valid-but-wrong points)
//!   * public IVC accumulator codec
//!   * cross-artifact confusion (another fixture's calldata)

#![cfg(feature = "evm")]

use halo2_solidity_verifier::{
    compile_solidity_with_runs, revm::primitives::Address, CallOutcome, Evm,
};
use std::path::PathBuf;

/// The fixture header pins solc 0.8.30; the replay suite renders this artifact
/// at `runs = 1` because it is large. Keep both properties here.
const SOLC_OPTIMIZE_RUNS: u32 = 1;
/// Generous, so an unexpected loop reports OutOfGas rather than a revert.
const GAS_CAP: u64 = 5_000_000_000;

// ---------------------------------------------------------------------------
// Layout, read back from the fixture verifier's own constants. Every value
// here is asserted against the rendered source in `pinned_layout_matches_source`
// so a codegen change cannot silently invalidate the sweeps below.
// ---------------------------------------------------------------------------

const PROOF_LEN_CPTR: usize = 0x44;
const PROOF_START: usize = 0x64;
const PROOF_LEN: usize = 0x1e60;
const NUM_INSTANCE_CPTR: usize = 0x1ec4;
const INSTANCE_START: usize = 0x1ee4;
const NUM_INSTANCES: usize = 19;
/// `acc_offset = 11`: the accumulator occupies the trailing 8 of 19 instances.
const ACC_OFFSET: usize = 11;
const LIMB_BITS: u32 = 56;
const NUM_LIMBS: usize = 7;
const LIMBS_PER_WORD: usize = 4;

/// Proof G1 sections: (name, byte offset from `PROOF_START`, count).
const SECTIONS: &[(&str, usize, usize)] = &[
    ("advice", 0x0000, 15),
    ("lookup_multiplicity", 0x0780, 2),
    ("permutation_z", 0x0880, 6),
    ("lookup_helper_and_z", 0x0b80, 4),
    ("trashcan", 0x0d80, 1),
    ("quotient_limb", 0x0e00, 4),
];
const EVALS_OFF: usize = 0x1000;
const EVALS_COUNT: usize = 102;
const F_COM_OFF: usize = 0x1cc0;
const Q_EVALS_OFF: usize = 0x1d40;
const Q_EVALS_COUNT: usize = 5;
const PI_OFF: usize = 0x1de0;

/// Typed-error selectors declared by the fixture verifier.
const ERR_BAD_CALLDATA_SHAPE: [u8; 4] = [0x1b, 0x99, 0xe3, 0x7c];
const ERR_NON_CANONICAL_SCALAR: [u8; 4] = [0x77, 0x53, 0x00, 0x42];
const ERR_BAD_POINT_ENCODING: [u8; 4] = [0xf2, 0x79, 0x05, 0xec];
const ERR_PRECOMPILE_FAILED: [u8; 4] = [0x84, 0xe8, 0x16, 0x92];
const ERR_PROOF_REJECTED: [u8; 4] = [0xc3, 0xb0, 0xd8, 0xcd];

/// BLS12-381 scalar-field modulus, big-endian.
const R_BE: [u8; 32] = [
    0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
    0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
];
const P_HEX: &str = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";

// ---------------------------------------------------------------------------
// Fixture I/O
// ---------------------------------------------------------------------------

fn fixture_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/moonlight-wrap")
}

fn fixture_source(name: &str) -> String {
    let path = fixture_dir().join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("missing {}: {e}", path.display()))
}

fn fixture_calldata() -> Vec<u8> {
    let path = fixture_dir().join("calldata.bin");
    std::fs::read(&path).unwrap_or_else(|e| panic!("missing {}: {e}", path.display()))
}

// ---------------------------------------------------------------------------
// Minimal BLS12-381 G1 arithmetic over the integers, used to build adversarial
// points. Every constructed vector is self-checked against `on_curve` /
// `in_subgroup` before it is used, so no magic constants are trusted.
// ---------------------------------------------------------------------------

type Big = num_bigint::BigUint;

fn p() -> Big {
    Big::parse_bytes(P_HEX.as_bytes(), 16).expect("modulus should parse")
}

fn r_order() -> Big {
    Big::parse_bytes(
        b"73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
        16,
    )
    .expect("scalar modulus should parse")
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Pt {
    Inf,
    Aff(Big, Big),
}

fn f_sub(a: &Big, b: &Big) -> Big {
    let m = p();
    ((a % &m) + &m - (b % &m)) % &m
}

fn f_inv(a: &Big) -> Big {
    let m = p();
    a.modpow(&(&m - Big::from(2u32)), &m)
}

fn pt_add(lhs: &Pt, rhs: &Pt) -> Pt {
    let m = p();
    match (lhs, rhs) {
        (Pt::Inf, q) => q.clone(),
        (q, Pt::Inf) => q.clone(),
        (Pt::Aff(x1, y1), Pt::Aff(x2, y2)) => {
            if x1 == x2 && (y1 + y2) % &m == Big::from(0u32) {
                return Pt::Inf;
            }
            let lam = if lhs == rhs {
                (Big::from(3u32) * x1 * x1 % &m) * f_inv(&(Big::from(2u32) * y1 % &m)) % &m
            } else {
                f_sub(y2, y1) * f_inv(&f_sub(x2, x1)) % &m
            };
            let x3 = f_sub(&f_sub(&(&lam * &lam % &m), x1), x2);
            let y3 = f_sub(&(&lam * f_sub(x1, &x3) % &m), y1);
            Pt::Aff(x3, y3)
        }
    }
}

fn pt_mul(pt: &Pt, k: &Big) -> Pt {
    let mut acc = Pt::Inf;
    for bit in format!("{k:b}").chars() {
        acc = pt_add(&acc, &acc);
        if bit == '1' {
            acc = pt_add(&acc, pt);
        }
    }
    acc
}

fn on_curve(x: &Big, y: &Big) -> bool {
    let m = p();
    (y * y) % &m == (x * x % &m * x + Big::from(4u32)) % &m
}

fn in_subgroup(pt: &Pt) -> bool {
    pt_mul(pt, &r_order()) == Pt::Inf
}

/// `p % 4 == 3`, so a square root is `a^((p+1)/4)` when one exists.
fn sqrt_f(a: &Big) -> Option<Big> {
    let m = p();
    let s = a.modpow(&((&m + Big::from(1u32)) / Big::from(4u32)), &m);
    (&s * &s % &m == a % &m).then_some(s)
}

/// Smallest-x curve point outside the r-order subgroup.
fn non_subgroup_point() -> (Big, Big) {
    let m = p();
    for x in 1u32..10_000 {
        let xb = Big::from(x);
        let rhs = (&xb * &xb % &m * &xb + Big::from(4u32)) % &m;
        let Some(y) = sqrt_f(&rhs) else { continue };
        if !on_curve(&xb, &y) || in_subgroup(&Pt::Aff(xb.clone(), y.clone())) {
            continue;
        }
        return (xb, y);
    }
    panic!("no non-subgroup point found in the search range");
}

fn generator() -> (Big, Big) {
    (
        Big::parse_bytes(b"17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb", 16).unwrap(),
        Big::parse_bytes(b"08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1", 16).unwrap(),
    )
}

fn word_bytes(v: &Big) -> [u8; 32] {
    let raw = v.to_bytes_be();
    assert!(raw.len() <= 32, "value does not fit in one EVM word");
    let mut out = [0u8; 32];
    out[32 - raw.len()..].copy_from_slice(&raw);
    out
}

/// EIP-2537 padded uncompressed G1: per coordinate, 16 zero bytes then 48
/// big-endian bytes; 128 bytes total.
fn padded_g1(x: &Big, y: &Big) -> [u8; 128] {
    let mut out = [0u8; 128];
    for (slot, coord) in [(0usize, x), (64, y)] {
        let raw = coord.to_bytes_be();
        assert!(raw.len() <= 48, "coordinate does not fit in 48 bytes");
        out[slot + 64 - 48 + (48 - raw.len())..slot + 64].copy_from_slice(&raw);
    }
    out
}

/// Read a padded G1 back out of calldata.
fn read_g1(cd: &[u8], off: usize) -> (Big, Big) {
    (
        Big::from_bytes_be(&cd[off + 16..off + 64]),
        Big::from_bytes_be(&cd[off + 80..off + 128]),
    )
}

// ---------------------------------------------------------------------------
// Accumulator public-input codec: publish `(coord - 1) mod p` as seven
// radix-2^56 limbs, packed four-then-three into two native words.
// ---------------------------------------------------------------------------

/// Pack a raw 392-bit value into the two native words the codec uses, with no
/// `- 1` shift. Used to build vectors whose *shifted* value is out of field.
fn raw_limbs(e: &Big) -> (Big, Big) {
    let mask = (Big::from(1u32) << LIMB_BITS) - Big::from(1u32);
    let limb = |i: usize| (e >> (LIMB_BITS * i as u32)) & &mask;
    let mut w0 = Big::from(0u32);
    for i in 0..LIMBS_PER_WORD {
        w0 |= limb(i) << (LIMB_BITS * i as u32);
    }
    let mut w1 = Big::from(0u32);
    for i in LIMBS_PER_WORD..NUM_LIMBS {
        w1 |= limb(i) << (LIMB_BITS * (i - LIMBS_PER_WORD) as u32);
    }
    (w0, w1)
}

/// The codec publishes `(coord - 1) mod p`, so encoding is exactly `raw_limbs`
/// applied to the shifted value.
fn encode_coord(coord: &Big) -> (Big, Big) {
    raw_limbs(&f_sub(coord, &Big::from(1u32)))
}

// ---------------------------------------------------------------------------
// Transaction gas model.
//
// revm charges `gas_used = max(legacy_intrinsic + execution, eip7623_floor)`.
// This calldata is 8,516 bytes, so the floor is large -- 315,890 gas against a
// legacy intrinsic of 138,956 -- and it swallows the whole cost of a cheap
// rejection. A naive `gas_used < accepted_gas / 2` anchor therefore measures
// the calldata size and nothing else: a flipped selector, which executes only
// the Solidity dispatcher, reports exactly the same 315,890 as a guard that ran
// the accumulator decoder and two G1MSMs.
//
// Both quantities depend on the calldata's own zero/non-zero byte counts, so
// they must be recomputed per mutated input rather than cached once.
// ---------------------------------------------------------------------------

fn zero_and_nonzero(cd: &[u8]) -> (u64, u64) {
    let zero = cd.iter().filter(|b| **b == 0).count() as u64;
    (zero, cd.len() as u64 - zero)
}

/// Pre-EIP-7623 intrinsic cost: 21000 + 4/zero byte + 16/non-zero byte.
fn legacy_intrinsic(cd: &[u8]) -> u64 {
    let (zero, nonzero) = zero_and_nonzero(cd);
    21_000 + 4 * zero + 16 * nonzero
}

/// EIP-7623 floor: 21000 + 10 gas per token, tokens = zero + 4*non-zero.
fn calldata_floor(cd: &[u8]) -> u64 {
    let (zero, nonzero) = zero_and_nonzero(cd);
    21_000 + 10 * (zero + 4 * nonzero)
}

/// Execution gas, exactly when the transaction billed above its floor and as an
/// upper bound when it did not.
fn execution_gas(cd: &[u8], gas_used: u64) -> u64 {
    gas_used.saturating_sub(legacy_intrinsic(cd))
}

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

struct Harness {
    evm: Evm,
    verifier: Address,
    /// Total transaction gas for the honest fixture proof.
    accepted_gas: u64,
    /// Execution-only gas for that run, i.e. above the legacy intrinsic.
    accepted_exec: u64,
    calldata: Vec<u8>,
    rejected: usize,
}

impl Harness {
    fn new() -> Self {
        let vk_src = fixture_source("Halo2VerifyingKey.sol");
        let ver_src = fixture_source("Halo2Verifier.sol");
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
                assert_eq!(
                    output,
                    [vec![0u8; 31], vec![1]].concat(),
                    "verifyProof must ABI-return true"
                );
                gas_used
            }
            other => panic!(
                "baseline fixture proof must verify, else nothing below means anything: {other:?}"
            ),
        };
        let accepted_exec = execution_gas(&calldata, accepted_gas);
        Self {
            evm,
            verifier,
            accepted_gas,
            accepted_exec,
            calldata,
            rejected: 0,
        }
    }

    fn call(&mut self, cd: Vec<u8>) -> CallOutcome {
        self.evm.try_call_with_gas(self.verifier, cd, GAS_CAP)
    }

    /// Reject, returning `(gas, revert payload)`.
    fn reject(&mut self, cd: Vec<u8>, case: &str) -> (u64, Vec<u8>) {
        match self.call(cd) {
            CallOutcome::Success {
                output, gas_used, ..
            } => panic!(
                "{case}: ACCEPTED (gas {gas_used}, output 0x{}) -- this input must not verify",
                hex::encode(output)
            ),
            CallOutcome::Halt { reason, .. } => panic!("{case}: halted ({reason})"),
            CallOutcome::Revert { gas_used, output } => {
                self.rejected += 1;
                (gas_used, output)
            }
        }
    }

    /// Reject with an exact typed-error selector.
    fn reject_with(&mut self, cd: Vec<u8>, err: [u8; 4], case: &str) -> u64 {
        let (gas, payload) = self.reject(cd, case);
        assert_eq!(
            payload.len(),
            4,
            "{case}: expected a 4-byte typed error, got 0x{}",
            hex::encode(&payload)
        );
        assert_eq!(
            payload[..],
            err[..],
            "{case}: rejected with 0x{} but the taxonomy assigns 0x{}",
            hex::encode(&payload),
            hex::encode(err)
        );
        gas
    }

    /// Reject with a typed error raised by a guard that runs before the
    /// verifier does any substantial work.
    ///
    /// The anchor is that the whole transaction bills at its EIP-7623 calldata
    /// floor: the guard's execution cost is entirely absorbed, which bounds it
    /// at `floor - legacy_intrinsic` (176,934 gas for the unmutated fixture,
    /// 17.3% of an accepted run's execution). That is a real bound but not a
    /// tight one, and no transaction-level measurement can do better --
    /// execution below the floor is unobservable. It is still far stronger than
    /// comparing against the accepted total, which for this calldata size is
    /// satisfied by the floor alone and therefore measures nothing.
    fn reject_early(&mut self, cd: Vec<u8>, err: [u8; 4], case: &str) {
        let floor = calldata_floor(&cd);
        let gas = self.reject_with(cd, err, case);
        assert!(
            gas <= floor,
            "{case}: billed {gas} gas against a calldata floor of {floor}, so it \
             executed at least {} gas beyond the floor -- the intended early guard \
             did not fire",
            gas - floor
        );
    }

    /// Reject only after the whole verification ran, i.e. at the pairing.
    /// This is the signature of a Fiat-Shamir binding failure: the input was
    /// structurally valid, so every range, packing and framing check passed.
    fn reject_at_pairing(&mut self, cd: Vec<u8>, case: &str) {
        let want = self.accepted_exec / 4 * 3;
        let intrinsic = legacy_intrinsic(&cd);
        let gas = self.reject_with(cd, ERR_PROOF_REJECTED, case);
        let exec = gas.saturating_sub(intrinsic);
        assert!(
            exec > want,
            "{case}: executed only {exec} gas (expected over {want}, near the {} of \
             an accepted run). An earlier check rejected this input, so it does not \
             exercise binding.",
            self.accepted_exec
        );
    }

    /// Reject with an exact typed error, after substantial work. Used for
    /// failures that can only surface at a precompile or the pairing, where
    /// the error is not necessarily `ProofRejected`.
    fn reject_late(&mut self, cd: Vec<u8>, err: [u8; 4], case: &str) {
        let want = self.accepted_exec / 4;
        let intrinsic = legacy_intrinsic(&cd);
        let gas = self.reject_with(cd, err, case);
        let exec = gas.saturating_sub(intrinsic);
        assert!(
            exec > want,
            "{case}: executed only {exec} gas (expected over {want}); an early guard \
             caught it, so this case does not test what it claims to"
        );
    }

    fn with<F: FnOnce(&mut Vec<u8>)>(&self, f: F) -> Vec<u8> {
        let mut cd = self.calldata.clone();
        f(&mut cd);
        cd
    }
}

/// Every 128-byte padded G1 in the proof, as (label, absolute calldata offset).
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

// ===========================================================================
// 0. The layout constants above must match the rendered source.
// ===========================================================================

#[test]
fn pinned_layout_matches_fixture_source() {
    let ver = fixture_source("Halo2Verifier.sol");
    let vk = fixture_source("Halo2VerifyingKey.sol");

    let expect = |needle: &str| {
        assert!(
            ver.contains(needle),
            "fixture verifier no longer contains `{needle}` -- the constants in this \
             test file have drifted from the artifact under test"
        );
    };
    expect("PROOF_LEN_CPTR = 0x44");
    expect("PROOF_CPTR = 0x64");
    expect("NUM_INSTANCE_CPTR = 0x1ec4");
    expect("INSTANCE_CPTR = 0x1ee4");
    expect("eq(0x1e60, calldataload(PROOF_LEN_CPTR))");
    expect("eq(19, calldataload(NUM_INSTANCE_CPTR))");
    expect("eq(calldatasize(), add(INSTANCE_CPTR, 0x0260))");
    // Typed-error selector constants.
    expect("ERR_BAD_CALLDATA_SHAPE      = 0x1b99e37c");
    expect("ERR_VK_MISMATCH             = 0xa447d73e");
    expect("ERR_NON_CANONICAL_SCALAR    = 0x77530042");
    expect("ERR_BAD_POINT_ENCODING      = 0xf27905ec");
    expect("ERR_PRECOMPILE_FAILED       = 0x84e81692");
    expect("ERR_PROOF_REJECTED          = 0xc3b0d8cd");

    for (name, want) in [
        ("num_instances", 19u64),
        ("acc_offset", 11),
        ("num_acc_limbs", 7),
        ("num_acc_limb_bits", 56),
        ("has_accumulator", 1),
    ] {
        let suffix = format!("// {name}");
        let line = vk
            .lines()
            .map(str::trim)
            .find(|l| l.starts_with("mstore(") && l.ends_with(&suffix))
            .unwrap_or_else(|| panic!("verifying key has no `{name}` word"));
        let hex = line.rsplit_once("0x").unwrap().1.split(')').next().unwrap();
        let got = u64::from_str_radix(hex.trim_start_matches('0'), 16).unwrap_or(0);
        assert_eq!(got, want, "verifying-key `{name}` drifted");
    }

    // The field moduli this file carries must be the ones the verifier uses.
    // Hardcoding them is unavoidable (they are curve parameters), but they can
    // be anchored so a copy-paste error cannot survive.
    assert!(
        ver.contains(&format!("FR_MODULUS        = 0x{}", hex::encode(R_BE))),
        "R_BE does not match the verifier's FR_MODULUS"
    );
    let p_bytes = p().to_bytes_be();
    assert_eq!(p_bytes.len(), 48, "p should be 48 bytes");
    assert!(
        ver.contains(&format!("BLS_P_HI             = 0x{}", hex::encode(word_bytes(&(p() >> 256))))),
        "P_HEX does not match the verifier's BLS_P_HI"
    );
    assert!(
        ver.contains(&format!(
            "BLS_P_MINUS_ONE_LO   = 0x{}",
            hex::encode(word_bytes(&((p() - Big::from(1u32)) & ((Big::from(1u32) << 256) - Big::from(1u32)))))
        )),
        "P_HEX does not match the verifier's BLS_P_MINUS_ONE_LO"
    );

    // The section table must match the parser's own loop bounds, in order.
    // The verifier walks the proof with `for { let end := add(proof_cptr, N) }`
    // per contiguous run; the two lookup accumulator commitments and f_com and
    // pi are read by standalone `common_uncompressed_g1` calls with no loop, so
    // they do not appear here.
    let bounds: Vec<usize> = ver
        .match_indices("let end := add(proof_cptr, 0x")
        .map(|(i, m)| {
            let rest = &ver[i + m.len()..];
            let hex = &rest[..rest.find(')').expect("loop bound should close")];
            usize::from_str_radix(hex, 16).expect("loop bound should be hex")
        })
        .collect();
    // Derived from SECTIONS, not written out a second time. The one place the
    // parser's shape is not a direct function of the table is the
    // lookup_helper_and_z run: the verifier emits one loop per lookup for the
    // helper commitments and reads each accumulator commitment with a
    // standalone call, so 4 commitments render as two 0x80 loops.
    let mut want: Vec<usize> = Vec::new();
    for (name, _, count) in SECTIONS {
        match *name {
            "lookup_helper_and_z" => {
                assert_eq!(count % 2, 0, "each lookup contributes one helper and one accumulator");
                want.extend(std::iter::repeat(0x80).take(count / 2));
            }
            _ => want.push(count * 0x80),
        }
    }
    want.push(EVALS_COUNT * 0x20);
    want.push(Q_EVALS_COUNT * 0x20);
    assert_eq!(
        bounds, want,
        "the parser's loop bounds no longer match the section table in this file"
    );

    // The proof section table must tile the proof exactly.
    let g1_bytes: usize = SECTIONS.iter().map(|(_, _, c)| c * 0x80).sum();
    assert_eq!(g1_bytes, EVALS_OFF, "G1 sections do not tile up to the evals");
    assert_eq!(EVALS_OFF + EVALS_COUNT * 0x20, F_COM_OFF);
    assert_eq!(F_COM_OFF + 0x80, Q_EVALS_OFF);
    assert_eq!(Q_EVALS_OFF + Q_EVALS_COUNT * 0x20, PI_OFF);
    assert_eq!(PI_OFF + 0x80, PROOF_LEN);
}

// ===========================================================================
// 1. ABI envelope. The verifier is a hand-rolled calldata parser sitting
//    behind a Solidity `external` signature, so the dynamic-argument heads,
//    the two length words and `calldatasize` are all load-bearing.
//
//    Two rejection layers exist here and the tests below distinguish them:
//    solc's own ABI decoder (bare `revert(0, 0)`, no payload) runs first, and
//    the generated typed guards run inside the function body. Anything the
//    decoder can already prove out of bounds never reaches the taxonomy.
// ===========================================================================

/// Classify an envelope rejection: `Some(head)` for anything carrying a 4-byte
/// selector, `None` for solc's bare `revert(0, 0)`.
///
/// A longer payload is a real outcome, not a harness bug -- `Error(string)` and
/// `Panic(uint256)` are 36+ bytes -- so return its head and let the caller's
/// assertion name the case that produced it rather than panicking here.
fn envelope_class(payload: &[u8]) -> Option<[u8; 4]> {
    (payload.len() >= 4).then(|| payload[..4].try_into().unwrap())
}

#[test]
fn fixture_verifier_rejects_malformed_abi_envelope() {
    let mut h = Harness::new();
    let mut typed = 0usize;
    let mut bare = 0usize;

    // -- selector. Anything but verifyProof(bytes,uint256[]) must not reach
    //    the parser at all.
    let mut wrong_selector = h.calldata.clone();
    wrong_selector[0] ^= 0xff;
    let (_, payload) = h.reject(wrong_selector, "unknown function selector");
    assert!(
        envelope_class(&payload).is_none(),
        "an unknown selector should hit the Solidity dispatcher fallback, not a typed \
         verifier error (got 0x{})",
        hex::encode(&payload)
    );

    // -- dynamic-argument heads. Both are pinned to exact literals by the
    //    early guard in verifyProof; heads that solc can already prove out of
    //    bounds are stopped one layer earlier.
    for (name, at) in [("proof head", 0x04usize), ("instances head", 0x24)] {
        for delta in [1i64, -1, 0x20, -0x20] {
            let cd = h.with(|cd| {
                let cur = u64::from_be_bytes(cd[at + 24..at + 32].try_into().unwrap()) as i64;
                let new = (cur + delta) as u64;
                cd[at + 24..at + 32].copy_from_slice(&new.to_be_bytes());
            });
            let case = format!("{name} {delta:+}");
            let (gas, payload) = h.reject(cd, &case);
            assert!(
                gas * 2 < h.accepted_gas,
                "{case}: rejected at {gas} gas -- an envelope guard should be cheap"
            );
            match envelope_class(&payload) {
                Some(sel) => {
                    assert_eq!(
                        sel, ERR_BAD_CALLDATA_SHAPE,
                        "{case}: typed error must be BadCalldataShape, got 0x{}",
                        hex::encode(sel)
                    );
                    typed += 1;
                }
                None => bare += 1,
            }
        }
    }
    assert!(
        typed > 0 && bare > 0,
        "head sweep should reach both rejection layers (typed {typed}, bare {bare})"
    );

    // -- proof length word. The heads are still exact, and every one of these
    //    lengths keeps the instance array inside calldata, so solc's decoder
    //    accepts the envelope and the generated guard is the one that fires.
    //    Requiring the typed error (rather than accepting a bare revert) is
    //    what keeps this case covering the guard: if these ever degraded to
    //    decoder rejections the loop would still "pass" while testing solc.
    for delta in [1i64, -1, 0x20, -0x20] {
        let cd = h.with(|cd| {
            let new = (PROOF_LEN as i64 + delta) as u64;
            cd[PROOF_LEN_CPTR + 24..PROOF_LEN_CPTR + 32].copy_from_slice(&new.to_be_bytes());
        });
        h.reject_early(
            cd,
            ERR_BAD_CALLDATA_SHAPE,
            &format!("proof length {delta:+}"),
        );
    }

    // -- instance count word. Both heads and the proof length are intact, so
    //    every one of these must carry the typed error.
    for wrong in [0u64, 1, 18] {
        let cd = h.with(|cd| {
            cd[NUM_INSTANCE_CPTR + 24..NUM_INSTANCE_CPTR + 32].copy_from_slice(&wrong.to_be_bytes())
        });
        h.reject_early(
            cd,
            ERR_BAD_CALLDATA_SHAPE,
            &format!("instance count = {wrong}"),
        );
    }
    // A larger count runs off the end of calldata, so solc stops it first.
    for wrong in [20u64, u32::MAX as u64] {
        let cd = h.with(|cd| {
            cd[NUM_INSTANCE_CPTR + 24..NUM_INSTANCE_CPTR + 32].copy_from_slice(&wrong.to_be_bytes())
        });
        h.reject(cd, &format!("instance count = {wrong}"));
    }

    // -- calldatasize. Appended bytes are the classic relayer/multicall
    //    hazard: an ERC-2771 forwarder that suffixes the sender address would
    //    otherwise hand the parser a valid proof with junk behind it. Nothing
    //    in the ABI layout is wrong here, so only the generated
    //    `calldatasize()` equality can catch it.
    for extra in [1usize, 20, 32, 64] {
        let mut cd = h.calldata.clone();
        cd.extend(std::iter::repeat(0u8).take(extra));
        h.reject_early(
            cd,
            ERR_BAD_CALLDATA_SHAPE,
            &format!("{extra} trailing calldata bytes"),
        );
    }
    // -- truncation.
    for short in [1usize, 32, 0x260] {
        let mut cd = h.calldata.clone();
        cd.truncate(cd.len() - short);
        h.reject(cd, &format!("calldata truncated by {short}"));
    }
    // -- nothing but the selector.
    let cd = h.calldata[..4].to_vec();
    h.reject(cd, "selector only");

    assert_eq!(h.rejected, 26, "envelope sweep shrank unexpectedly");
    println!(
        "envelope heads: {typed} rejected by the typed guard, {bare} stopped earlier by \
         solc's ABI decoder (bare revert, no selector)"
    );
}

// ===========================================================================
// 2. Verifying-key binding. The verifier pins the VK by runtime length and
//    codehash at construction AND again on every proof.
// ===========================================================================

/// Deploy `verifier(vk)` and report whether construction succeeded.
fn try_deploy_pair(vk_src: &str, ver_code: &[u8]) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut evm = Evm::default();
        let vk = evm.create(compile_solidity_with_runs(vk_src, SOLC_OPTIMIZE_RUNS));
        evm.create_with_address_arg(ver_code.to_vec(), vk);
    }))
    .is_ok()
}

/// Alter one payload word of the verifying-key source, keeping the runtime
/// length identical so only the codehash pin can catch the change.
fn tamper_vk_word(vk_src: &str, label: &str) -> String {
    let line = vk_src
        .lines()
        .find(|l| l.trim_end().ends_with(&format!("// {label}")))
        .unwrap_or_else(|| panic!("vk source has no `{label}` word"));
    let (head, tail) = line.rsplit_once("0x").unwrap();
    let (value, rest) = tail.split_once(')').unwrap();
    let mut v: Vec<char> = value.chars().collect();
    let last = v.len() - 1;
    v[last] = if v[last] == '0' { '1' } else { '0' };
    let tampered = format!("{head}0x{}){rest}", v.into_iter().collect::<String>());
    let out = vk_src.replace(line, &tampered);
    assert_ne!(out, vk_src, "tamper of `{label}` did not apply");
    out
}

#[test]
fn fixture_verifier_binds_its_verifying_key() {
    let vk_src = fixture_source("Halo2VerifyingKey.sol");
    let ver_src = fixture_source("Halo2Verifier.sol");
    let ver_code = compile_solidity_with_runs(&ver_src, SOLC_OPTIMIZE_RUNS);

    // -- (a) the honest pair deploys, so the rejections below mean something.
    assert!(
        try_deploy_pair(&vk_src, &ver_code),
        "the fixture verifier must deploy against its own verifying key"
    );

    // -- (b) one altered payload word anywhere in the VK must be refused at
    //    construction. Cover a header word, a base point, a quotient VM
    //    constant, the packed quotient program, and a commitment.
    for label in [
        "vk_digest",
        "omega",
        "neg_s_g2_y_c1_lo",
        "quotient_const",
        "quotient_program",
    ] {
        let bad = tamper_vk_word(&vk_src, label);
        assert!(
            !try_deploy_pair(&bad, &ver_code),
            "constructing against a VK with a tampered `{label}` word must revert"
        );
    }

    // -- (c) a VK address with no code at all.
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut e = Evm::default();
            e.create_with_address_arg(ver_code.clone(), Address::repeat_byte(0x42));
        }))
        .is_err(),
        "constructing the verifier against an EOA / empty account must revert"
    );

    // -- (d) the runtime re-check: the same length but a different codehash is
    //    rejected on every proof, not only at construction. Deploy honestly,
    //    then point a second verifier at the tampered VK -- construction is
    //    where the pin bites first, so assert the pair cannot even be formed.
    let bad = tamper_vk_word(&vk_src, "num_instances");
    let mut e = Evm::default();
    let good = e.create(compile_solidity_with_runs(&vk_src, SOLC_OPTIMIZE_RUNS));
    let evil = e.create(compile_solidity_with_runs(&bad, SOLC_OPTIMIZE_RUNS));
    assert_eq!(
        e.code_size(good),
        e.code_size(evil),
        "the tampered VK must keep the same runtime length so only the codehash pin \
         can distinguish it"
    );
    assert_ne!(
        e.code_hash(good),
        e.code_hash(evil),
        "tampering must move the codehash"
    );
}

// ===========================================================================
// 3. Scalar canonicality. Every Fr word the parser reads must be < r, both to
//    keep the transcript injective and to keep quotient arithmetic sound.
//    Swept exhaustively: a guard present for eval 0 and missing for eval 101
//    passes any spot check.
// ===========================================================================

#[test]
fn fixture_verifier_rejects_noncanonical_scalars() {
    let mut h = Harness::new();
    let r_plus_one = {
        let mut v = R_BE;
        v[31] += 1;
        v
    };
    let max = [0xffu8; 32];

    // -- 102 polynomial evaluations.
    for i in 0..EVALS_COUNT {
        let at = PROOF_START + EVALS_OFF + i * 32;
        for (name, val) in [("r", R_BE), ("r+1", r_plus_one), ("2^256-1", max)] {
            let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&val));
            h.reject_early(
                cd,
                ERR_NON_CANONICAL_SCALAR,
                &format!("eval[{i}] = {name}"),
            );
        }
    }

    // -- 5 q_evals.
    for i in 0..Q_EVALS_COUNT {
        let at = PROOF_START + Q_EVALS_OFF + i * 32;
        for (name, val) in [("r", R_BE), ("2^256-1", max)] {
            let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&val));
            h.reject_early(cd, ERR_NON_CANONICAL_SCALAR, &format!("q_eval[{i}] = {name}"));
        }
    }

    // -- public instances outside the accumulator window. These are checked in
    //    the transcript loop via the deferred `success` flag.
    for i in 0..ACC_OFFSET {
        let at = INSTANCE_START + i * 32;
        for (name, val) in [("r", R_BE), ("2^256-1", max)] {
            let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&val));
            h.reject_early(cd, ERR_NON_CANONICAL_SCALAR, &format!("instance[{i}] = {name}"));
        }
    }

    // -- accumulator instance words are decoded *before* the transcript, so a
    //    word >= r is caught by the limb-packing guard, not the Fr guard.
    for i in ACC_OFFSET..NUM_INSTANCES {
        let at = INSTANCE_START + i * 32;
        let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&R_BE));
        h.reject_early(cd, ERR_BAD_POINT_ENCODING, &format!("acc instance[{i}] = r"));
    }

    assert_eq!(
        h.rejected,
        EVALS_COUNT * 3 + Q_EVALS_COUNT * 2 + ACC_OFFSET * 2 + (NUM_INSTANCES - ACC_OFFSET),
        "canonicality sweep did not cover the pinned number of positions"
    );
}

// ===========================================================================
// 4. G1 encoding. Proof commitments arrive as EIP-2537 padded uncompressed
//    points: per coordinate, 16 zero bytes then 48 value bytes. Both the
//    padding and the `< p` bound are transcript-malleability guards -- the
//    verifier hashes the raw 128 calldata bytes, so a second encoding of the
//    same point would be a second transcript for the same proof.
//    Swept over all 34 proof points and both coordinates.
// ===========================================================================

#[test]
fn fixture_verifier_rejects_bad_g1_encodings() {
    let mut h = Harness::new();
    let points = all_proof_points();
    assert_eq!(points.len(), 34, "proof G1 count drifted from the pinned layout");

    let p_hi = word_bytes(&(p() >> 256));
    let p_lo = word_bytes(&(&p() & ((Big::from(1u32) << 256) - Big::from(1u32))));

    // -- (a) non-zero EIP-2537 pad bytes.
    for (label, off) in &points {
        for (word, coord) in [(0usize, "x"), (2, "y")] {
            for pad_byte in [0usize, 7, 15] {
                let cd = h.with(|cd| cd[off + word * 32 + pad_byte] = 0x01);
                h.reject_early(
                    cd,
                    ERR_BAD_POINT_ENCODING,
                    &format!("{label}.{coord}_hi pad byte {pad_byte} set"),
                );
            }
        }
    }

    // -- (b) coordinates at and above the base-field modulus. `p` itself is
    //    the interesting case: it is a valid 381-bit string and reduces to 0.
    for (label, off) in &points {
        for (word, coord) in [(0usize, "x"), (2, "y")] {
            for (name, add) in [("p", 0u32), ("p+1", 1)] {
                let v = p() + Big::from(add);
                let hi = word_bytes(&(&v >> 256));
                let lo = word_bytes(&(&v & ((Big::from(1u32) << 256) - Big::from(1u32))));
                let cd = h.with(|cd| {
                    cd[off + word * 32..off + word * 32 + 32].copy_from_slice(&hi);
                    cd[off + (word + 1) * 32..off + (word + 2) * 32].copy_from_slice(&lo);
                });
                h.reject_early(
                    cd,
                    ERR_BAD_POINT_ENCODING,
                    &format!("{label}.{coord} = {name}"),
                );
            }
        }
    }
    // Sanity: the vectors above really are p and p+1 in split form.
    assert_eq!(
        Big::from_bytes_be(&p_hi) * (Big::from(1u32) << 256) + Big::from_bytes_be(&p_lo),
        p()
    );

    assert_eq!(h.rejected, 34 * 2 * 3 + 34 * 2 * 2, "encoding sweep shrank");
}

// ===========================================================================
// 5. Curve membership and subgroup. The verifier performs NO on-curve and NO
//    subgroup check of its own; `common_uncompressed_g1` documents that it
//    defers both to the EIP-2537 precompiles on the grounds that every
//    absorbed commitment is later consumed by a G1MSM or a pairing. These
//    cases execute that claim.
// ===========================================================================

#[test]
fn fixture_verifier_defers_curve_checks_to_the_precompiles() {
    let mut h = Harness::new();

    // Vectors, self-checked so no magic constant can drift.
    let (nx, ny) = non_subgroup_point();
    assert!(on_curve(&nx, &ny), "vector must be on the curve");
    assert!(
        !in_subgroup(&Pt::Aff(nx.clone(), ny.clone())),
        "vector must be outside the r-order subgroup"
    );
    let non_sub = padded_g1(&nx, &ny);

    // (0, 2): the only curve point with x = 0, and h-torsion.
    let zero_two = {
        let x = Big::from(0u32);
        let y = Big::from(2u32);
        assert!(on_curve(&x, &y));
        assert!(!in_subgroup(&Pt::Aff(x.clone(), y.clone())));
        padded_g1(&x, &y)
    };

    // An off-curve point with a perfectly legal encoding.
    let off_curve = {
        let x = Big::from(1u32);
        let y = Big::from(1u32);
        assert!(!on_curve(&x, &y));
        padded_g1(&x, &y)
    };

    // Substitute into a representative point from every proof category, plus
    // f_com and pi.
    let targets: Vec<(String, usize)> = SECTIONS
        .iter()
        .map(|(name, off, _)| ((*name).to_string(), PROOF_START + off))
        .chain([
            ("f_com".to_string(), PROOF_START + F_COM_OFF),
            ("pi".to_string(), PROOF_START + PI_OFF),
        ])
        .collect();

    for (label, off) in &targets {
        for (name, bytes) in [
            ("non-subgroup", &non_sub),
            ("(0,2) h-torsion", &zero_two),
            ("off-curve", &off_curve),
        ] {
            let cd = h.with(|cd| cd[*off..off + 128].copy_from_slice(bytes));
            // The verifier has no curve check, so these survive parsing and
            // die inside a precompile. Record which typed error results.
            // Measured: every one of these lands on PrecompileFailed after the
            // full quotient and PCS work, inside the fused 78-pair G1MSM. The
            // verifier has no curve check of its own, so the caller pays a
            // complete verification (~1.04M gas of execution, 87% of an
            // accepted run) before EIP-2537 rejects the point -- and the
            // rejection is then reported as a chain fault rather than a proof
            // fault. See `accumulator_offcurve_points_are_reported_as_
            // precompile_failures` for the same defect on the public-input
            // side.
            h.reject_late(cd, ERR_PRECOMPILE_FAILED, &format!("{label} := {name}"));
        }
    }

    // Valid, in-subgroup, but simply the WRONG point: the generator, and the
    // negation of the point already there. These pass every encoding, curve
    // and subgroup check and can only fail at the pairing.
    let (gx, gy) = generator();
    assert!(in_subgroup(&Pt::Aff(gx.clone(), gy.clone())));
    let gen_bytes = padded_g1(&gx, &gy);
    for (label, off) in &targets {
        let cd = h.with(|cd| cd[*off..off + 128].copy_from_slice(&gen_bytes));
        h.reject_at_pairing(cd, &format!("{label} := G1 generator"));

        let (x, y) = read_g1(&h.calldata, *off);
        if y == Big::from(0u32) {
            continue;
        }
        let neg = padded_g1(&x, &f_sub(&Big::from(0u32), &y));
        let cd = h.with(|cd| cd[*off..off + 128].copy_from_slice(&neg));
        h.reject_at_pairing(cd, &format!("{label} := -{label}"));
    }

    // The point at infinity is a legal EIP-2537 encoding (four zero words), so
    // it must survive to the pairing rather than being rejected as malformed.
    for (label, off) in &targets {
        let cd = h.with(|cd| cd[*off..off + 128].fill(0));
        h.reject_late(cd, ERR_PROOF_REJECTED, &format!("{label} := point at infinity"));
    }

    // 8 targets x (3 invalid points + generator + negation + infinity), minus
    // the negations skipped for a y = 0 coordinate (none in this fixture).
    assert_eq!(
        h.rejected,
        8 * 6,
        "curve sweep shrank: a target or a vector was dropped"
    );
}


// ===========================================================================
// 6. Fiat-Shamir binding. Every mutation below is *structurally perfect*:
//    canonical scalars, canonical padded points, exact calldata size. The only
//    thing wrong with them is that they are not the proof the transcript
//    commits to. They must therefore survive every guard and die at the
//    pairing -- which is also what proves the guards above are not accidentally
//    doing the rejecting.
// ===========================================================================

#[test]
fn fixture_verifier_binds_every_proof_field_into_the_transcript() {
    let mut h = Harness::new();
    let r = r_order();

    // -- (a) every one of the 102 evaluations, bumped by one mod r.
    for i in 0..EVALS_COUNT {
        let at = PROOF_START + EVALS_OFF + i * 32;
        let cur = Big::from_bytes_be(&h.calldata[at..at + 32]);
        let next = (cur + Big::from(1u32)) % &r;
        let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&word_bytes(&next)));
        h.reject_at_pairing(cd, &format!("eval[{i}] += 1"));
    }

    // -- (b) every q_eval.
    for i in 0..Q_EVALS_COUNT {
        let at = PROOF_START + Q_EVALS_OFF + i * 32;
        let cur = Big::from_bytes_be(&h.calldata[at..at + 32]);
        let next = (cur + Big::from(1u32)) % &r;
        let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&word_bytes(&next)));
        h.reject_at_pairing(cd, &format!("q_eval[{i}] += 1"));
    }

    // -- (c) every non-accumulator public instance. This is the check that
    //    matters most to an integrator: a proof must not verify against a
    //    public input it was not produced for.
    for i in 0..ACC_OFFSET {
        let at = INSTANCE_START + i * 32;
        let cur = Big::from_bytes_be(&h.calldata[at..at + 32]);
        let next = (cur + Big::from(1u32)) % &r;
        let cd = h.with(|cd| cd[at..at + 32].copy_from_slice(&word_bytes(&next)));
        h.reject_at_pairing(cd, &format!("instance[{i}] += 1"));
    }
    // ...and instance zeroed, which is the shape a caller-supplied-input bug
    // actually takes in practice.
    for i in 0..ACC_OFFSET {
        let at = INSTANCE_START + i * 32;
        if h.calldata[at..at + 32].iter().all(|b| *b == 0) {
            continue;
        }
        let cd = h.with(|cd| cd[at..at + 32].fill(0));
        h.reject_at_pairing(cd, &format!("instance[{i}] := 0"));
    }

    // -- (d) commitment swaps within a category. Both points stay valid G1
    //    elements; only their order changes, so nothing but the transcript can
    //    notice.
    for (name, off, count) in SECTIONS {
        if *count < 2 {
            continue;
        }
        let a = PROOF_START + off;
        let b = a + 0x80;
        let cd = h.with(|cd| {
            for k in 0..0x80 {
                cd.swap(a + k, b + k);
            }
        });
        h.reject_at_pairing(cd, &format!("{name}[0] <-> {name}[1] swapped"));
    }

    // -- (e) a single flipped bit in the low byte of a commitment coordinate
    //    almost certainly leaves the curve, so instead swap two whole
    //    commitments across categories, which keeps both valid.
    let cd = h.with(|cd| {
        let a = PROOF_START + F_COM_OFF;
        let b = PROOF_START + PI_OFF;
        for k in 0..0x80 {
            cd.swap(a + k, b + k);
        }
    });
    h.reject_at_pairing(cd, "f_com <-> pi swapped");

    assert!(
        h.rejected >= EVALS_COUNT + Q_EVALS_COUNT + ACC_OFFSET,
        "binding sweep shrank"
    );
}

// ===========================================================================
// 7. The public IVC accumulator codec. Instances 11..18 are two G1 points
//    published as seven radix-2^56 limbs per coordinate, packed four-then-three
//    into native words. This region is validated BEFORE the transcript, so its
//    guards are the cheapest rejections the verifier has.
// ===========================================================================

/// Absolute calldata offset of accumulator instance word `i` (0-based within
/// the accumulator window).
fn acc_word(i: usize) -> usize {
    INSTANCE_START + (ACC_OFFSET + i) * 32
}

#[test]
fn fixture_verifier_validates_the_public_accumulator_codec() {
    let mut h = Harness::new();

    // The window is exactly two points: lhs(x0,x1,y0,y1), rhs(x0,x1,y0,y1).
    assert_eq!(NUM_INSTANCES - ACC_OFFSET, 8);

    // -- (a) over-packing. Word 0 of a coordinate carries 4 limbs = 224 bits,
    //    word 1 carries 3 limbs = 168 bits. Any bit above those is a second
    //    encoding of the same coordinate.
    for i in 0..8 {
        let used_bits = if i % 2 == 0 { 224 } else { 168 };
        let cur = Big::from_bytes_be(&h.calldata[acc_word(i)..acc_word(i) + 32]);
        let over = &cur + (Big::from(1u32) << used_bits);
        let cd = h.with(|cd| {
            cd[acc_word(i)..acc_word(i) + 32].copy_from_slice(&word_bytes(&over))
        });
        h.reject_early(
            cd,
            ERR_BAD_POINT_ENCODING,
            &format!("acc word {i}: bit {used_bits} set (over-packed)"),
        );
    }

    // -- (b) a coordinate whose *shifted* value is >= p. The codec publishes
    //    `coord - 1`, and `load_acc_coord` bounds that shifted value by p-1
    //    before adding one back, so the vector must pack `p` (and the maximum
    //    the packing allows) directly rather than going through `encode_coord`.
    for point in 0..2 {
        for coord in 0..2 {
            let base = point * 4 + coord * 2;
            for (name, e) in [
                ("p", p()),
                ("2^392-1 (max the packing allows)", (Big::from(1u32) << 392) - Big::from(1u32)),
            ] {
                let (w0, w1) = raw_limbs(&e);
                let cd = h.with(|cd| {
                    cd[acc_word(base)..acc_word(base) + 32].copy_from_slice(&word_bytes(&w0));
                    cd[acc_word(base + 1)..acc_word(base + 1) + 32]
                        .copy_from_slice(&word_bytes(&w1));
                });
                h.reject_early(
                    cd,
                    ERR_BAD_POINT_ENCODING,
                    &format!("acc point {point} coord {coord} shifted value = {name}"),
                );
            }
        }
    }

    // -- (c) a non-canonical infinity. The codec accepts exactly one encoding
    //    of the identity: x = p-1 with the identity flag, y = p-1. Any other
    //    zero-decoding form must be refused, otherwise the accumulator has two
    //    representations of the same point.
    for point in 0..2 {
        let base = point * 4;
        // p-1 in both coordinates but WITHOUT the identity flag on x: this
        // decodes to affine (0,0), which EIP-2537 reserves for infinity.
        let (w0, w1) = encode_coord(&Big::from(0u32));
        let cd = h.with(|cd| {
            for (k, w) in [(0usize, &w0), (1, &w1), (2, &w0), (3, &w1)] {
                cd[acc_word(base + k)..acc_word(base + k) + 32]
                    .copy_from_slice(&word_bytes(w));
            }
        });
        h.reject_early(
            cd,
            ERR_BAD_POINT_ENCODING,
            &format!("acc point {point}: unflagged (0,0) infinity encoding"),
        );
    }

    // -- (c2) x carries the identity flag but y is a real coordinate.
    //
    //    `load_acc_point` reassigns `is_id` from the whole-point sentinel to
    //    `x_is_id`, which is decided by `load_acc_coord`'s flag probe reading
    //    only x's two words. So an x equal to the flagged sentinel with ANY y
    //    enters the `if is_id` branch at Halo2Verifier.sol:1189, and the guard
    //    at line 1201 -- `ok := and(ok, iszero(or(or(x_hi, x_lo), or(y_hi,
    //    y_lo))))` -- is the ONLY thing that rejects it.
    //
    //    The comment above that branch (lines 1194-1200) says it is
    //    "unreachable by construction ... kept as defence in depth ... rather
    //    than as a live branch". That is false: the branch is live and
    //    load-bearing, and deleting it would admit a family of non-canonical
    //    identity encodings (identity-flagged x with arbitrary y). This case
    //    executes it.
    let flagged = {
        // Derive the flagged first word rather than hardcoding it: it is the
        // packed p-1 word plus one radix base.
        let (w0, w1) = encode_coord(&Big::from(0u32));
        let w0_flag = &w0 + (Big::from(1u32) << LIMB_BITS);
        // Tie the derivation to the artifact's own constant.
        let ver = fixture_source("Halo2Verifier.sol");
        let want = format!("0x{}", hex::encode(word_bytes(&w0_flag)));
        assert!(
            ver.contains(&format!("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG = {want}")),
            "derived identity-flagged word {want} does not match the verifier constant"
        );
        (w0_flag, w1)
    };
    for point in 0..2 {
        let base = point * 4;
        let (y0, y1) = encode_coord(&Big::from(2u32));
        let cd = h.with(|cd| {
            for (k, w) in [(0usize, &flagged.0), (1, &flagged.1), (2, &y0), (3, &y1)] {
                cd[acc_word(base + k)..acc_word(base + k) + 32]
                    .copy_from_slice(&word_bytes(w));
            }
        });
        h.reject_early(
            cd,
            ERR_BAD_POINT_ENCODING,
            &format!("acc point {point}: identity-flagged x with y = 2"),
        );
    }

    // -- (d) a valid, in-subgroup, but WRONG accumulator point. Passes every
    //    decode and the G1MSM round-trip; can only fail at the batched pairing.
    let (gx, gy) = generator();
    for point in 0..2 {
        let base = point * 4;
        let (x0, x1) = encode_coord(&gx);
        let (y0, y1) = encode_coord(&gy);
        let cd = h.with(|cd| {
            for (k, w) in [(0usize, &x0), (1, &x1), (2, &y0), (3, &y1)] {
                cd[acc_word(base + k)..acc_word(base + k) + 32]
                    .copy_from_slice(&word_bytes(w));
            }
        });
        h.reject_at_pairing(cd, &format!("acc point {point} := G1 generator"));
    }

    // -- (d2) the p-1 zero sentinel collides with the only curve points whose
    //    x-coordinate is zero, (0, +-2). The codec CAN represent them: encode x
    //    as the sentinel (which decodes to 0) and y as 2. The `decoded_zero`
    //    guard in load_acc_point only fires when BOTH coordinates decode to
    //    zero, so (0, 2) passes every decode check in this contract. It is
    //    rejected only because (0, 2) is h-torsion and EIP-2537 enforces
    //    subgroup membership -- a non-local argument worth executing.
    for point in 0..2 {
        let base = point * 4;
        let two = Big::from(2u32);
        assert!(on_curve(&Big::from(0u32), &two), "(0,2) must be on the curve");
        assert!(
            !in_subgroup(&Pt::Aff(Big::from(0u32), two.clone())),
            "(0,2) must be outside the r-order subgroup, else this case proves nothing"
        );
        let (x0, x1) = encode_coord(&Big::from(0u32));
        let (y0, y1) = encode_coord(&two);
        let cd = h.with(|cd| {
            for (k, w) in [(0usize, &x0), (1, &x1), (2, &y0), (3, &y1)] {
                cd[acc_word(base + k)..acc_word(base + k) + 32]
                    .copy_from_slice(&word_bytes(w));
            }
        });
        h.reject_early(
            cd,
            ERR_PRECOMPILE_FAILED,
            &format!("acc point {point} := (0, 2) via the p-1 sentinel"),
        );
    }

    // -- (e) an on-curve point OUTSIDE the r-order subgroup. The verifier has
    //    no subgroup check; the G1MSM round-trip in validate_public_accumulator
    //    is the only thing that can catch this.
    let (nx, ny) = non_subgroup_point();
    assert!(!in_subgroup(&Pt::Aff(nx.clone(), ny.clone())));
    for point in 0..2 {
        let base = point * 4;
        let (x0, x1) = encode_coord(&nx);
        let (y0, y1) = encode_coord(&ny);
        let cd = h.with(|cd| {
            for (k, w) in [(0usize, &x0), (1, &x1), (2, &y0), (3, &y1)] {
                cd[acc_word(base + k)..acc_word(base + k) + 32]
                    .copy_from_slice(&word_bytes(w));
            }
        });
        let (gas, payload) = h.reject(cd, &format!("acc point {point} := non-subgroup"));
        assert_eq!(payload.len(), 4, "expected a typed error");
        let sel: [u8; 4] = payload[..].try_into().unwrap();
        println!(
            "acc point {point} := non-subgroup -> 0x{} at {gas} gas",
            hex::encode(sel)
        );
        assert!(
            sel == ERR_BAD_POINT_ENCODING || sel == ERR_PRECOMPILE_FAILED,
            "unexpected error 0x{}",
            hex::encode(sel)
        );
    }

    // 8 over-packing (both word widths x 8 words)
    // + 8 out-of-field (2 points x 2 coords x {p, 2^392-1})
    // + 2 identity-flagged x with a real y
    // + 2 unflagged (0,0)
    // + 2 sentinel-encoded (0,2)
    // + 2 generator
    // + 2 non-subgroup.
    assert_eq!(
        h.rejected,
        26,
        "accumulator sweep shrank: a codec case was dropped"
    );
}

// ===========================================================================
// 8. Cross-artifact confusion. A proof for a different circuit, or the other
//    fixture's calldata, must never verify here.
// ===========================================================================

#[test]
fn fixture_verifier_rejects_foreign_calldata() {
    let mut h = Harness::new();

    // The IVC fixture is a different circuit with a different proof length
    // (8,356 bytes against 8,516), so this exercises the ABI shape guard, not
    // circuit binding -- the parser never gets far enough to disagree about the
    // proof itself. Asserting the exact selector is what keeps that honest: if
    // it ever started reverting for a different reason, the case would no
    // longer mean what its name says.
    let ivc = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/ivc/calldata.bin");
    let other = std::fs::read(&ivc)
        .unwrap_or_else(|e| panic!("missing {}: {e}", ivc.display()));
    assert_ne!(other.len(), h.calldata.len(), "fixtures must differ in length");
    h.reject_early(
        other,
        ERR_BAD_CALLDATA_SHAPE,
        "IVC fixture calldata replayed against the wrap verifier",
    );

    // Zeroed proof body with an otherwise perfect envelope: all commitments
    // become the point at infinity and all scalars become zero, which is
    // canonical. Nothing structural is wrong, so this must reach the pairing --
    // and it does, executing more than a full accepted run before failing.
    let cd = h.with(|cd| cd[PROOF_START..PROOF_START + PROOF_LEN].fill(0));
    h.reject_at_pairing(cd, "all-zero proof body");

    // Same proof, all instances zeroed. The accumulator window then decodes to
    // the affine point (1, 1) -- every limb is zero, so the shifted value is 0
    // and the codec adds one back to each coordinate. (1, 1) is not on
    // y^2 = x^3 + 4, and the verifier has no on-curve check of its own, so the
    // rejection comes from the G1MSM round-trip rather than from a decode
    // guard. See `accumulator_offcurve_points_are_reported_as_precompile_failures`.
    let cd = h.with(|cd| cd[INSTANCE_START..].fill(0));
    h.reject_early(cd, ERR_PRECOMPILE_FAILED, "all-zero instances");
}


// ===========================================================================
// 9. Taxonomy defect, pinned.
//
//    `validate_public_accumulator` documents (MF-4, Halo2Verifier.sol:1240-1245)
//    that `precompile_failed` separates "a G1MSM staticcall that could not run
//    (chain/gas fault)" from "a public-input point this verifier decoded and
//    rejected (bad packing, out-of-field coordinate, non-canonical identity
//    encoding, OR A POINT THE PRECOMPILE FOUND OFF-CURVE/OUT-OF-SUBGROUP)",
//    and says "only the second is a BadPointEncoding".
//
//    The code cannot make that distinction. Both cases surface as a reverted
//    STATICCALL, so both set `precompile_failed`, and the call site
//    (Halo2Verifier.sol:1447-1451) reports PrecompileFailed. A malformed
//    accumulator point -- a proof fault, attacker-controlled -- is therefore
//    reported to incident response as a chain fault.
//
//    This is not a soundness break: every such input is still rejected. It is
//    a monitoring/triage defect, and it is pinned here so that a fix (or a
//    correction of the comment) is a deliberate change.
// ===========================================================================

#[test]
fn accumulator_offcurve_points_are_reported_as_precompile_failures() {
    let mut h = Harness::new();

    // (1, 1): legal limb packing, in-field coordinates, not on the curve.
    let (x0, x1) = encode_coord(&Big::from(1u32));
    let (y0, y1) = encode_coord(&Big::from(1u32));
    assert!(!on_curve(&Big::from(1u32), &Big::from(1u32)));
    let cd = h.with(|cd| {
        for (k, w) in [(0usize, &x0), (1, &x1), (2, &y0), (3, &y1)] {
            cd[acc_word(k)..acc_word(k) + 32].copy_from_slice(&word_bytes(w));
        }
    });
    h.reject_early(
        cd,
        ERR_PRECOMPILE_FAILED,
        "off-curve accumulator point reported as PrecompileFailed, not BadPointEncoding",
    );

    // On-curve but outside the r-order subgroup: same outcome.
    let (nx, ny) = non_subgroup_point();
    let (x0, x1) = encode_coord(&nx);
    let (y0, y1) = encode_coord(&ny);
    let cd = h.with(|cd| {
        for (k, w) in [(0usize, &x0), (1, &x1), (2, &y0), (3, &y1)] {
            cd[acc_word(k)..acc_word(k) + 32].copy_from_slice(&word_bytes(w));
        }
    });
    h.reject_early(
        cd,
        ERR_PRECOMPILE_FAILED,
        "non-subgroup accumulator point reported as PrecompileFailed",
    );

    // Contrast: a decode-layer rejection does carry BadPointEncoding, so the
    // taxonomy is only wrong for the precompile-validated cases.
    let cur = Big::from_bytes_be(&h.calldata[acc_word(0)..acc_word(0) + 32]);
    let over = &cur + (Big::from(1u32) << 224u32);
    let cd = h.with(|cd| cd[acc_word(0)..acc_word(0) + 32].copy_from_slice(&word_bytes(&over)));
    h.reject_early(cd, ERR_BAD_POINT_ENCODING, "over-packed word keeps BadPointEncoding");
}

// ===========================================================================
// 10. Deployability. The revm harness lifts EIP-170
//     (`limit_contract_code_size = usize::MAX`, `src/evm.rs`), so every test
//     above would pass even for an artifact that cannot exist on a real chain.
//     Measure the runtime sizes explicitly, and check the VK metadata the
//     verifier pins by constant.
// ===========================================================================

/// EIP-170 maximum contract runtime size.
const EIP_170_LIMIT: usize = 24_576;

#[test]
fn fixture_artifacts_fit_in_a_deployable_contract() {
    let vk_src = fixture_source("Halo2VerifyingKey.sol");
    let ver_src = fixture_source("Halo2Verifier.sol");

    let mut evm = Evm::default();
    let vk = evm.create(compile_solidity_with_runs(&vk_src, SOLC_OPTIMIZE_RUNS));
    let vk_len = evm.code_size(vk);

    // The verifier hard-codes both of these; a mismatch bricks every proof.
    assert!(
        ver_src.contains(&format!("EXPECTED_VK_LENGTH = {vk_len}")),
        "deployed VK runtime is {vk_len} bytes but the verifier pins a different \
         EXPECTED_VK_LENGTH"
    );
    assert!(
        ver_src.contains(&format!(
            "EXPECTED_VK_PAYLOAD_LENGTH = {}",
            vk_len - 1
        )),
        "EXPECTED_VK_PAYLOAD_LENGTH must be EXPECTED_VK_LENGTH - 1 (the INVALID prefix)"
    );
    let want_hash = ver_src
        .lines()
        .find(|l| l.contains("EXPECTED_VK_CODEHASH_WORD"))
        .and_then(|l| l.rsplit_once("0x"))
        .map(|(_, v)| v.trim_end_matches(';').to_string())
        .expect("verifier must pin EXPECTED_VK_CODEHASH_WORD");
    assert_eq!(
        format!("{:064x}", evm.code_hash(vk)),
        want_hash,
        "deployed VK codehash does not match the pinned constant"
    );

    let verifier =
        evm.create_with_address_arg(compile_solidity_with_runs(&ver_src, SOLC_OPTIMIZE_RUNS), vk);
    let ver_len = evm.code_size(verifier);

    println!(
        "runtime sizes at optimize-runs={SOLC_OPTIMIZE_RUNS}: verifier {ver_len} B, \
         verifying key {vk_len} B, EIP-170 limit {EIP_170_LIMIT} B"
    );
    assert!(
        vk_len <= EIP_170_LIMIT,
        "verifying key runtime {vk_len} exceeds EIP-170"
    );
    assert!(
        ver_len <= EIP_170_LIMIT,
        "verifier runtime {ver_len} exceeds EIP-170 ({} bytes over); this artifact \
         cannot be deployed to a chain that enforces the limit",
        ver_len - EIP_170_LIMIT
    );

    // The header of the artifact claims the (version, runs) pair is
    // load-bearing for deployability. Show the headroom so a future codegen
    // change that eats it is visible.
    println!(
        "EIP-170 headroom: verifier {} B, verifying key {} B",
        EIP_170_LIMIT - ver_len,
        EIP_170_LIMIT - vk_len
    );
}

// ===========================================================================
// 11. Exhaustive single-bit sweep. The structured suites above target specific
//     guards; this one makes no assumption about where a mutation lands. Every
//     byte of the 8,516-byte calldata is flipped in turn and the result must
//     never be accepted.
//
//     This is the closest thing to a completeness statement the harness can
//     make: it covers the ABI prologue, every proof byte, and every instance
//     word, including regions no named test reaches (the interior bytes of
//     coordinate low words, the middle of the evaluation block, the padding
//     inside the length words).
// ===========================================================================

/// Run the sweep over `calldata[i]` for every `i` where `i % stride == phase`.
/// Returns the histogram of rejection classes.
fn single_bit_sweep(
    h: &mut Harness,
    stride: usize,
) -> (usize, std::collections::BTreeMap<String, usize>) {
    let len = h.calldata.len();
    let mut classes = std::collections::BTreeMap::<String, usize>::new();
    let mut total = 0usize;
    for byte in (0..len).step_by(stride) {
        for bit in [0u8, 7] {
            let cd = h.with(|cd| cd[byte] ^= 1 << bit);
            total += 1;
            match h.call(cd) {
                CallOutcome::Success { output, .. } => panic!(
                    "byte {byte:#x} bit {bit} flipped: ACCEPTED (output 0x{})",
                    hex::encode(output)
                ),
                CallOutcome::Halt { reason, .. } => {
                    panic!("byte {byte:#x} bit {bit} flipped: halted ({reason})")
                }
                CallOutcome::Revert { output, .. } => {
                    let key = if output.is_empty() {
                        "bare revert (solc ABI decoder)".to_string()
                    } else {
                        format!("0x{}", hex::encode(&output[..output.len().min(4)]))
                    };
                    *classes.entry(key).or_default() += 1;
                }
            }
        }
    }
    (total, classes)
}

fn report_sweep(total: usize, classes: &std::collections::BTreeMap<String, usize>) {
    println!("single-bit sweep: {total} mutations, none accepted");
    for (k, v) in classes {
        let pct = 100.0 * (*v as f64) / (total as f64);
        println!("  {v:>6}  ({pct:5.1}%)  {k}");
    }
}

/// Strided sample, fast enough for CI. Every 13th byte is coprime with the
/// 32-byte word size and the 128-byte point size, so the sample walks every
/// intra-word and intra-point position rather than always landing on the same
/// byte of each element.
#[test]
fn sampled_single_bit_mutations_never_verify() {
    let mut h = Harness::new();
    let (total, classes) = single_bit_sweep(&mut h, 13);
    assert!(total > 1_200, "sample shrank unexpectedly");
    report_sweep(total, &classes);
}

/// The exhaustive version: the low bit and the high bit of every one of the
/// 8,516 calldata bytes. 17,032 EVM runs, roughly seven minutes, so it is
/// opt-in.
///
/// Two bits per byte, not eight: this covers 25% of all single-bit mutations.
/// Bits 0 and 7 are chosen because they exercise opposite ends of every encoded
/// value -- bit 7 of a coordinate's leading pad byte is exactly what the
/// EIP-2537 pad guard catches, and bit 0 of a scalar's last byte is the
/// smallest possible perturbation. The histogram below is therefore data about
/// this sweep, not a property of the contract: a different bit selection would
/// shift the shares between BadPointEncoding and ProofRejected.
///
/// This is the closest thing to a completeness statement the harness can make:
/// it covers the ABI prologue, every proof byte and every instance word,
/// including regions no named test reaches (interior bytes of coordinate low
/// words, the middle of the evaluation block, the padding inside length words).
///
/// Measured distribution of the 17,032 rejections (2026-08-23, this fixture):
///
/// ```text
///    7433  (43.6%)  0xc3b0d8cd  ProofRejected      -- reached the pairing
///    6840  (40.2%)  0x84e81692  PrecompileFailed   -- EIP-2537 rejected a point
///    2376  ( 14.0%)  0xf27905ec  BadPointEncoding   -- decode/packing guard
///     119  ( 0.7%)  0x77530042  NonCanonicalScalar
///       4  ( 0.0%)  0x1b99e37c  BadCalldataShape
///     260  ( 1.5%)  bare revert (solc's ABI decoder, before the taxonomy)
/// ```
///
/// The 40% share of `PrecompileFailed` is the empirical form of the taxonomy
/// defect pinned by
/// `accumulator_offcurve_points_are_reported_as_precompile_failures`: the
/// documented meaning of that selector is a chain fault, but in practice its
/// dominant cause is an attacker-supplied point that is simply not on the
/// curve.
#[test]
#[ignore = "17,032 EVM runs, ~7 minutes; run with --ignored"]
fn no_low_or_high_bit_flip_of_the_fixture_calldata_verifies() {
    let mut h = Harness::new();
    let (total, classes) = single_bit_sweep(&mut h, 1);
    assert_eq!(total, h.calldata.len() * 2, "sweep did not cover every byte");
    report_sweep(total, &classes);
}

// ===========================================================================
// 12. The committed-instance evaluation is enforced only indirectly.
//
//     Point set 0 declares "43 evaluation term(s), 42 commitment term(s)"
//     (Halo2Verifier.sol:3460): one evaluation in the batched claim has no
//     matching term in the final MSM. That evaluation is the committed-instance
//     column, whose commitment is the G1 identity -- absorbed into the
//     transcript as 128 zero bytes and dropped from the MSM because the
//     identity contributes nothing.
//
//     The consequence is that the verifier never checks `eval[0] == 0` with an
//     equality. It is enforced by the algebra: the evaluation stays in the
//     batched claim multiplied by a batching coefficient the prover cannot
//     predict, so a nonzero value breaks the opening -- but with the soundness
//     of a 128-bit truncated coefficient, not of a hard check.
//
//     This test records both halves of that: the honest proof really does send
//     zero there, and perturbing it really is rejected, at the pairing.
// ===========================================================================

#[test]
fn committed_instance_evaluation_is_zero_and_bound_only_by_the_pcs() {
    let mut h = Harness::new();

    let at = PROOF_START + EVALS_OFF;
    assert!(
        h.calldata[at..at + 32].iter().all(|b| *b == 0),
        "eval[0] should be the committed-instance evaluation, which an honest \
         prover sends as zero"
    );
    let zeros = (0..EVALS_COUNT)
        .filter(|i| {
            let o = PROOF_START + EVALS_OFF + i * 32;
            h.calldata[o..o + 32].iter().all(|b| *b == 0)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        zeros,
        vec![0],
        "exactly one evaluation should be structurally zero; if this changed, the \
         committed-instance reasoning above no longer identifies eval[0]"
    );

    // The verifier has no equality check for it, so the rejection must come
    // from the pairing, at full cost.
    for delta in [1u8, 2, 0xff] {
        let cd = h.with(|cd| cd[at + 31] = delta);
        h.reject_at_pairing(cd, &format!("eval[0] := {delta} (committed instance)"));
    }
    // Also at the top of the word, so the mutation is not a small-value fluke.
    let cd = h.with(|cd| cd[at] = 0x01);
    h.reject_at_pairing(cd, "eval[0] high byte set");
}
