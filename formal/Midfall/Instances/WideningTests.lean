/-
  Midfall.Instances.WideningTests  (WID.1: landed verbatim from the evidence file
  `docs/plans/V3-evidence/lean/widening/WideningTests.lean`; only this header and the import line
  changed. The five `#eval` gates below are now KAT gates: `scripts/kat_gate.py` walks the tree.)

  WideningTests - TESTS for the widening (rule W12): witnesses and falsifiers that are computations.
  Nothing here is a proof obligation of the generic theorem. Every `#eval` prints `true`.

  The sixteen instance words are those of the LOCAL, UNTRACKED file
  proofs/solidity-verifier/target/ivc-keccak-solidity-dump/instance.le (a Rust-made public input
  of the IVC decider circuit, written by a bench run of 2026-10-07). They are data for a codec
  test only: that run's proof does not belong to the tracked contracts (memo §7).
-/
import Midfall.LoweringV3.WideningStages

namespace Midfall.LoweringW.Tests

open Midfall Midfall.Halo2

/-- `instance.le`, as sixteen big-endian words: 4 state words, then lhs point (x: 2 words,
    y: 2 words, flag), lhs scalar, rhs point, rhs scalar. -/
def ivcInst : Array Word256 :=
  #[0x1,
    0x1544bddbd052009eccbf6e3ed204c2f7bb29a3d317386e5c87095f03f766f47a,
    0x1,
    0x1544bddbd052009eccbf6e3ed204c2f7bb29a3d317386e5c87095f03f766f47a,
    0xfbbf27a90f3f7f09ae34aee2bc75def9936d6815bfea6fe6c44683cc,
    0x162474d3c8b769ad9b0acb05f830c5b838bc66cd,
    0x312eec1f73079f0daa2f9307f3f325e73420bc3420329a21ad8c59b5,
    0x9c84d2b422e38b326862bfb345b8f8820073a19,
    0x0,
    0x1,
    0x27b3832022cc7b3b9c51634bfd7f2f633100e5a3bc110bb07b416383,
    0x160be22f01f9abfc6af280653f899f2547e7ae84,
    0xc3f092755e337c1df26937419e3bd099289534cb0594f304c733af3e,
    0x242b1ba9a924dec16a51b1fdd654f2559be3e2,
    0x0,
    0x1]

/-- The encoding of the e2e test (`ivc_keccak_solidity.rs:1125`): offset 4, 7 limbs of 56 bits,
    point-and-scalar. -/
def ivcEnc : Midfall.Halo2.AccumulatorEncoding := Midfall.Halo2.AccumulatorEncoding.new 4 7 56

/-- Expected affine coordinates, computed OUTSIDE Lean (python, from the layout read in
    `Halo2Verifier.sol:980-1072`: value = word0 + word1·2^224, coordinate = value + 1 mod p), and
    checked there to satisfy y² = x³ + 4. -/
def lhsX : Nat := 0x162474d3c8b769ad9b0acb05f830c5b838bc66cdfbbf27a90f3f7f09ae34aee2bc75def9936d6815bfea6fe6c44683cd
def lhsY : Nat := 0x9c84d2b422e38b326862bfb345b8f8820073a19312eec1f73079f0daa2f9307f3f325e73420bc3420329a21ad8c59b6
def rhsX : Nat := 0x160be22f01f9abfc6af280653f899f2547e7ae8427b3832022cc7b3b9c51634bfd7f2f633100e5a3bc110bb07b416384
def rhsY : Nat := 0x242b1ba9a924dec16a51b1fdd654f2559be3e2c3f092755e337c1df26937419e3bd099289534cb0594f304c733af3f

/-- The point is on the curve y² = x³ + 4 over the BLS12-381 base field. -/
def onCurve (x y : Nat) : Bool := (y * y) % accFpModulus == (x * x * x + 4) % accFpModulus

/-- WITNESS (scope): the encoding is in the class `AccShape` admits - no fixed-base tail. -/
def noTail_ok : Bool :=
  ivcEnc.fixedScalarCount 16 == some 0 && ivcEnc.fixedPayloadWords == 12

/-- FALSIFIERS (scope), each a shape `AccShape.noTail` excludes or the generator refuses:
    a point-and-scalar encoding with ONE tail scalar; an encoding that does not fit; a limb shape
    other than 7 x 56 (the generator accepts no other, so the class loses nothing by it). -/
def noTail_refuses : Bool :=
  (Midfall.Halo2.AccumulatorEncoding.new 3 7 56).fixedScalarCount 16 == some 1 &&
  (Midfall.Halo2.AccumulatorEncoding.new 5 7 56).fixedScalarCount 16 == none &&
  (Midfall.Halo2.AccumulatorEncoding.new 4 8 48).fixedScalarCount 16 == none &&
  (Midfall.Halo2.AccumulatorEncoding.new 4 6 64).fixedScalarCount 16 == none

/-- The point-pair kind with no tail is admitted by `noTail` too (10 words): it is `accKind`,
    not `noTail`, that leaves it out of the first cut. -/
def pointPair_noTail : Bool :=
  (Midfall.Halo2.AccumulatorEncoding.pointPair 6 7 56).fixedScalarCount 16 == some 0 &&
  (Midfall.Halo2.AccumulatorEncoding.pointPair 5 7 56).fixedScalarCount 16 == none

/-- WITNESS (decoder): the ported limb decoder ACCEPTS the Rust-made accumulator, both points are
    non-identity, the coordinates it rebuilds are the expected ones, both points are on the
    curve, and both carried scalars are 1. -/
def decoder_accepts : Bool :=
  match loadAccPoint ivcEnc ivcInst 4, loadAccPoint ivcEnc ivcInst 10 with
  | some (lb, lid), some (rb, rid) =>
      !lid && !rid &&
      coordOfEip lb 0 == lhsX && coordOfEip lb 1 == lhsY &&
      coordOfEip rb 0 == rhsX && coordOfEip rb 1 == rhsY &&
      onCurve lhsX lhsY && onCurve rhsX rhsY &&
      (ivcInst.getD 9 0).toNat == 1 && (ivcInst.getD 15 0).toNat == 1
  | _, _ => false

/-- FALSIFIERS (decoder), the mutations of the e2e test (`:1463-1475`) and three more:
    flag 2 is rejected; flag 1 decodes to the 128 zero bytes whatever the coordinates; an unused
    high bit in a packed word is rejected; raw zero coordinate words with flag 0 decode to the
    point (1,1), which is NOT on the curve (so the G1MSM call, not the decoder, rejects it);
    the encoded identity coordinates (value p-1, i.e. coordinate 0) with flag 0 are rejected by
    the decoder itself. -/
def decoder_refuses : Bool :=
  let pm1 := accFpModulus - 1
  let idW0 : Word256 := BitVec.ofNat 256 (pm1 % 2 ^ 224)
  let idW1 : Word256 := BitVec.ofNat 256 (pm1 / 2 ^ 224)
  let withIdCoords := (((ivcInst.set! 4 idW0).set! 5 idW1).set! 6 idW0).set! 7 idW1
  let zeroCoords := (((ivcInst.set! 4 0).set! 5 0).set! 6 0).set! 7 0
  (loadAccPoint ivcEnc (ivcInst.set! 8 2) 4).isNone &&
  (match loadAccPoint ivcEnc (ivcInst.set! 8 1) 4 with
   | some (bs, true) => bs == natToBytesBE 0 128
   | _ => false) &&
  (loadAccPoint ivcEnc (ivcInst.set! 4 (BitVec.ofNat 256 (2 ^ 224))) 4).isNone &&
  (match loadAccPoint ivcEnc zeroCoords 4 with
   | some (bs, false) => coordOfEip bs 0 == 1 && coordOfEip bs 1 == 1 && !onCurve 1 1
   | _ => false) &&
  (loadAccPoint ivcEnc withIdCoords 4).isNone

#eval noTail_ok          -- expect true
#eval noTail_refuses     -- expect true
#eval pointPair_noTail   -- expect true
#eval decoder_accepts    -- expect true
#eval decoder_refuses    -- expect true

end Midfall.LoweringW.Tests
