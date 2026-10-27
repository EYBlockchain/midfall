-- |
-- Midfall.Assumptions.Codec
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 3; PLAN
-- P-SE-semantic-equivalence.md section C and index item 3; design1.md
-- 'G1CodecLaws (structure; statable-now; M5)').
--
-- WHAT THIS FILE IS FOR. Every headline semantic-equivalence statement consumes
-- a G1 point codec: the contract absorbs 128-byte EIP-2537 encodings straight out
-- of calldata, and the Lean verifier absorbs the DECODED points re-serialised by
-- the same codec. The two agree only if the codec is canonical in both directions,
-- so the laws are named here once instead of being scattered through the
-- theorems. design1 lists the consumers: decodeAcc_encode, decodeAcc_injective,
-- calldata_roundtrip, calldata_canonical and the provable restatement of
-- Statements.verifyNative_iff_msgs (finding B1).
--
-- WHY A HYPOTHESIS STRUCTURE AND NOT A CLASS. R-34 (docs/REVIEW.md): no Lean
-- instance proves any of these laws, and the only real BLS12-381 codec lives in
-- Midfall/Instances/Bls12_381.lean, which no theorem-bearing file may import
-- (D-P17, enforced by scripts/checks.sh). So each law is a binder, exactly as
-- Midfall/Assumptions/Pairing.lean does for the pairing itself: a hypothesis is a
-- binder, not a proof hole, and the gap policy (plan Section 3) prefers it to a
-- bare sorry.
--
-- WHICH SET OF LAWS. attack.md line 15 records that the three design passes
-- proposed two different bundles in this file (P1 G1Codec.Laws with four fields,
-- P3 G1CodecLaws with six) and line 180 FIX settles it: one structure, P3 fields
-- plus eipWidth, because the headline theorems need toEip_one (the committed point
-- absorbed as 128 zero bytes), eipShape and ofEip_toEip, and P1 set is
-- insufficient. The two round trips are the tree decoder-first properties
-- (Common/Codec.lean:106 and :113); the encoder-first law was deliberately
-- REMOVED from G1Codec (Common/Codec.lean:97-105 records why) and must stay a
-- hypothesis here rather than being restated as a fact.
--
-- KNOWN FALSEHOOD THIS FILE DOES NOT STATE. The frozen
-- Midfall.Statements.verifyNative_iff_msgs is false for a degenerate codec
-- (finding B1: toCompressed := fun _ => Bytes.empty re-serialises a 48-byte
-- stream to nothing, so prepareMsgs faults while verifyNative accepts). Its
-- restatement, verifyNative_iff_msgs_codec, belongs to Obligations.lean (stage 6)
-- because it needs the transcript-log invariant; it is NOT hidden here. attack.md
-- line 107 FIX also drops the p <= 2^256 hypothesis from that restatement as
-- decorative while KEEPING it here, where the encoder-first direction is used.

import Midfall.Common.Codec
import Midfall.Common.Bytes
import Midfall.Assumptions.Pairing

namespace Midfall.Assumptions
open Midfall

/-! ### The G1 codec law bundle -/

/-- The G1 codec laws the accumulator and calldata statements consume (R-34: each
    is a binder, none is proved in-tree). The two round trips are decoder-first
    (Common/Codec.lean:106, :113); ofEip_toEip is the encoder-first law that
    Common/Codec.lean:97-105 deliberately removed from G1Codec, and it is needed
    only where the encoder is OURS (asPublicInputPoint, encodeContractProof).

    eipShape is the EIP-2537 frame shape with in-field, non-(0,0) coordinates:
    AssemblyHelpers.yul:94-104 and AccumulatorHelpers.yul:152-157 reject (0,0)
    under flag 0, so a codec that encoded a nonzero point as all-zero bytes would
    make the contract and the transcript disagree about the identity. toEip_one is
    the other half of the same pin: the committed point is absorbed as 128 zero
    bytes by the contract (TranscriptProofParser.yul:36-46) while Lean absorbs
    toEip 1, and attack.md line 32 (FIX, binding) makes both laws hypotheses of
    every headline field. -/
structure G1CodecLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  /-- decoder-first: whatever ofEip? accepts re-encodes to the same bytes. -/
  eipRoundtrip : c.eipRoundtrip
  /-- decoder-first for the 48-byte transcript form. -/
  compressedRoundtrip : c.compressedRoundtrip
  /-- encoder-first, restricted to real points: needed by decodeAcc_encode and
      calldata_roundtrip. -/
  ofEip_toEip : ∀ Q : G₁, c.ofEip? (c.toEip Q) = some Q
  /-- the 16-48-16-48 EIP-2537 frame, coordinates in field and not both zero. -/
  eipShape : ∀ Q : G₁, Q ≠ 1 → ∃ x y : Nat, x < pBase ∧ y < pBase ∧ ¬ (x = 0 ∧ y = 0) ∧
    c.toEip Q = natToBytesBE 0 16 ++ natToBytesBE x 48 ++ natToBytesBE 0 16 ++ natToBytesBE y 48
  /-- identity is exactly 128 zero bytes (AccumulatorHelpers.yul:137-140). -/
  toEip_one : c.toEip 1 = natToBytesBE 0 128
  /-- the two widths, so a wrong-length repr is a shape error, not a silent none. -/
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  eipWidth : ∀ Q : G₁, (c.toEip Q).size = g1EipWidth

/-! ### Byte lemmas (design1 M5-2)

design1 M5-2 assigns this stage the byte lemmas the VkDigest, Calldata and
Accumulator statements share. They are stated here, in the assumption layer,
because this is the first file that needs them and because their natural home -
Midfall/Common/Bytes.lean - is the P-05 row's file, which stage 2 may not edit
(the standing rule against touching another package's Lean file). Only the half
that lands is here; the reason the other half does not is recorded at
frOfRepr_frToRepr and again at Lowering/VkDigest.lean. -/

/-- The digits natToBytesLowFirst emits, least significant first, as a list. This
    is the shape the emitter's accumulator builds, and naming it is what makes the
    induction go through without reasoning about ByteArray internals. -/
def lowDigits : Nat → Nat → List UInt8
  | _, 0 => []
  | n, k+1 => Nat.toUInt8 (n % 256) :: lowDigits (n / 256) k

/-- The emitter's accumulator step, as a list equation. -/
theorem lowDigits_go : ∀ (len : Nat) (n : Nat) (acc : Bytes),
    (Midfall.natToBytesLowFirst.go n len acc).data.toList =
      acc.data.toList ++ lowDigits n len := by
  intro len
  induction len with
  | zero => intro n acc; simp [Midfall.natToBytesLowFirst.go, lowDigits]
  | succ k ih =>
      intro n acc
      show (Midfall.natToBytesLowFirst.go (n/256) k
            (acc.push (Nat.toUInt8 (n % 256)))).data.toList = _
      rw [ih (n := n/256) (acc := acc.push (Nat.toUInt8 (n % 256)))]
      have hpush : (acc.push (Nat.toUInt8 (n % 256))).data.toList =
          acc.data.toList ++ [Nat.toUInt8 (n % 256)] := by
        cases acc with
        | mk arr => simp [ByteArray.push, Array.toList_push]
      rw [hpush, List.append_assoc]
      rfl

/-- The emitter always produces exactly len bytes - which is the half of
    frOfRepr_frToRepr that is about the SHAPE of a repr rather than its value, and
    the half that makes feToU256's length guard unreachable for frToRepr. -/
theorem natToBytesLowFirst_size (n len : Nat) :
    (natToBytesLowFirst n len).size = len := by
  show (Midfall.natToBytesLowFirst.go n len Bytes.empty).size = len
  have h : ∀ (len : Nat) (n : Nat) (acc : Bytes),
      (Midfall.natToBytesLowFirst.go n len acc).size = acc.size + len := by
    intro len
    induction len with
    | zero => intro n acc; simp [Midfall.natToBytesLowFirst.go]
    | succ k ih =>
        intro n acc
        show (Midfall.natToBytesLowFirst.go (n/256) k
              (acc.push (Nat.toUInt8 (n % 256)))).size = _
        rw [ih (n := n/256) (acc := acc.push (Nat.toUInt8 (n % 256)))]
        rw [ByteArray.size_push]
        omega
  rw [h]
  have h0 : Bytes.empty.size = 0 := rfl
  omega

/-- The same fact for the two public spellings, so a caller never has to know that
    natToBytesLE is natToBytesLowFirst. -/
theorem frToRepr_size {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) :
    (frToRepr x).size = 32 := natToBytesLowFirst_size x.val 32

/-! ### The scalar repr round trip -/

/-- A canonical scalar round-trips through its 32-byte little-endian repr
    (rust: ff::PrimeField::to_repr then from_repr, implementors.rs:322-334). The
    bound p <= 2^256 is load-bearing: frToRepr truncates to 32 bytes
    (Common/Bytes.lean:45-54), so for p > 2^256 a value at or above 2^256 decodes
    to its residue, not to itself. attack.md line 107 FIX keeps hp HERE (the
    encoder-first direction) while dropping it from verifyNative_iff_msgs_codec,
    which is decoder-first and does not need it.

    PROOF OBLIGATION, registered in SORRY.md. design1 M5-2 assigns the two byte
    lemmas it needs to stage 2. The SHAPE half landed above (natToBytesLowFirst_size,
    frToRepr_size): the repr is always 32 bytes, so frOfRepr?'s width test passes.
    The VALUE half - bytesToNatLE (natToBytesLE n len) = n % 256^len - did not, and
    the reason is mechanical: Midfall.bytesToNatBE (Common/Bytes.lean:92) folds with
    Array.foldl, which in Lean 4.35 is the index-loop over the opaque Array
    representation and is not definitionally List.foldl on toList, and core exports
    no Array.foldl_eq_foldl_data. Closing it needs either an Array-index induction
    over loop bounds or a lemma inside Common/Bytes.lean, which is the P-05 row's
    file and outside this package's edit rights. The statement is unchanged and the
    gate frReprKats_ok below computes the round trip at p = 17, so the claim is
    checked where it can be checked. -/
theorem frOfRepr_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≤ 2 ^ 256) (x : Fr p) :
    frOfRepr? (p := p) (frToRepr x) = some x := by
  sorry

/-! ### Non-vacuity -/

/-- The bundle is not the trivial predicate: three of its seven fields are
    refuted by the two degenerate codecs below, so no field can be discharged by
    accident (design1 non-vacuity note; attack.md line 180). Both are written over
    Multiplicative (ZMod 17), a nontrivial group that needs no curve instance and
    so does not drag Midfall/Instances/ into a theorem-bearing file (D-P17). -/
def shortEipCodec : G1Codec (Multiplicative (ZMod 17)) where
  toEip := fun _ => natToBytesBE 0 96
  ofEip? := fun _ => none
  toCompressed := fun _ => Bytes.empty
  ofCompressed? := fun _ => none

/-- The honest 128-zero identity encoding with a decoder that answers nothing:
    the shape is right and the encoder-first law is what fails. -/
def nullDecoderCodec : G1Codec (Multiplicative (ZMod 17)) where
  toEip := fun _ => natToBytesBE 0 128
  ofEip? := fun _ => none
  toCompressed := fun _ => natToBytesBE 0 48
  ofCompressed? := fun _ => none

/-- toEip_one and eipWidth are load-bearing: a codec that drops the two padding
    words satisfies every algebraic law you can write and still disagrees with the
    contract about the committed point. Refuted by byte count, which is the cheap
    way to keep the gate inside the kernel budget (a 128-element decide blows the
    recursion depth). -/
example : G1CodecLaws shortEipCodec → False := by
  intro l
  have h : (shortEipCodec.toEip 1).size = (natToBytesBE 0 128).size := congrArg ByteArray.size l.toEip_one
  exact absurd h (by decide)

example : G1CodecLaws shortEipCodec → False := by
  intro l
  have h : (shortEipCodec.toEip (1 : Multiplicative (ZMod 17))).size = g1EipWidth :=
    l.eipWidth (1 : Multiplicative (ZMod 17))
  exact absurd h (by decide)

/-- ofEip_toEip is load-bearing: a decoder that rejects everything makes the
    encoder-first law false at the identity, which is the one point the contract
    always sees (the committed instance column). -/
example : G1CodecLaws nullDecoderCodec → False := by
  intro l
  have h := l.ofEip_toEip (1 : Multiplicative (ZMod 17))
  simp [nullDecoderCodec] at h

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The scalar repr gate, computed at a small prime so the kernel can reduce it:
    32 bytes out, the round trip frOfRepr_frToRepr states on the value the
    transcript actually reads, and a negative control - a decoder that ignored
    canonicity would answer some for the value 17 as well, which is exactly the
    malleability frOfRepr? exists to reject (Common/Codec.lean:35-39). The last two
    lines pin the byte ORDER: little-endian, so 2 is the first byte and not the
    last - the R-20 defect class. -/
def frReprKats_ok : Bool :=
  (frToRepr (p := 17) (2 : Fr 17)).size == 32 &&
    frOfRepr? (p := 17) (frToRepr (p := 17) (2 : Fr 17)) == some (2 : Fr 17) &&
    frOfRepr? (p := 17) (frToRepr (p := 17) (16 : Fr 17)) == some (16 : Fr 17) &&
    frOfRepr? (p := 17) (natToBytesLE 17 32) == none &&
    (frToRepr (p := 17) (2 : Fr 17)).data[0]? == some 2 &&
    (frToRepr (p := 17) (2 : Fr 17)).data[1]? == some 0

#eval frReprKats_ok   -- expect true

/-- The two widths the law bundle pins, against the encoders they describe, and
    the 16-48-16-48 split of the EIP frame that eipShape asserts. A codec that
    emitted 47 compressed bytes would satisfy every algebraic law and still be
    wrong on the wire. -/
def codecWidthKats_ok : Bool :=
  g1CompressedWidth == 48 && g1EipWidth == 128 &&
    (natToBytesBE 0 16).size == 16 && (natToBytesBE 0 48).size == 48 &&
    (natToBytesBE 0 16).size + (natToBytesBE 0 48).size +
      (natToBytesBE 0 16).size + (natToBytesBE 0 48).size == g1EipWidth &&
    eipPad.size == 16 && (natToBytesBE 0 128).size == g1EipWidth

#eval codecWidthKats_ok   -- expect true

end Midfall.Assumptions