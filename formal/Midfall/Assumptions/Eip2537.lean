-- |
-- Midfall.Assumptions.Eip2537
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 4; PLAN
-- P-SE-semantic-equivalence.md section D and index item 4; design0.md
-- 'Midfall.Assumptions.Eip2537.Holds'; design2.md 'Eip2537.Holds / G2Enc /
-- modexpInv_correct').
--
-- WHAT THIS FILE IS FOR. The deployed verifier does not compute pairings: it
-- staticcalls the EIP-2537 precompiles at 0x0b (G1ADD), 0x0c (G1MSM) and 0x0f
-- (PAIRING_CHECK), and EIP-198 modexp at 0x05. Midfall/Yul/Externals.lean models
-- the BYTE side of those frames and computes everything it can - G1ADD, G1MSM and
-- modexp results are all computed there - but it cannot compute the pairing
-- product, because that needs Fp12 and no Lean library has BLS12-381 at all
-- (docs/ecosystem.md, D-P1). Externals.lean:934-941 names that hole
-- PairingProduct := Bytes -> Bool and leaves it a parameter. This file is where
-- the parameter is pinned to the abstract pairing: Eip2537.Holds is the named
-- hypothesis saying the precompile answers agree with AdmissiblePairing.e, the
-- group law and the scalar action through the codecs. Per the gap policy (plan
-- Section 3) an unproven fact is a binder here, never a proof hole.
--
-- WHICH SHAPE, and why. attack.md line 7 records that the three design passes
-- proposed incompatible Holds signatures (P1: list-general pairing_iff over
-- msmSpecific; P2: a two-pair pairing2 with a bare G2 encoder function), and
-- line 84 FIX settles it: one file, P2 two-pair form - the verifier never pairs
-- more than two pairs (AssemblyHelpers.yul:294 staticcalls PAIRING_GAS_2PAIR on a
-- 0x300-byte frame) - wrapped in P1 G2Enc structure, because a bare G2 -> Bytes
-- field cannot carry the VK-header link the Surface needs. D14 in the stage-1
-- brief restates the same decision. The frame is CALLER-ordered: ec_pairing lays
-- out [lhs_g1 | G2_BASE | rhs_g1 | NEG_S_G2_BASE] (AssemblyHelpers.yul:284-287)
-- but FinalPairing.yul:88 calls ec_pairing(success, PAIRING_RHS_MPTR,
-- PAIRING_LHS_MPTR), so the pairs the precompile actually sees are
-- [(rhs, G2), (lhs, -sG2)]. R-11 is the port finding: the orientation flips at
-- the call site, not in pairingFrame, so Holds is stated over the frame as laid
-- out and finalPairing_spec (stage 4) owns the swap.
--
-- WHAT IS NOT AN ASSUMPTION HERE. Modexp is not a hypothesis: Externals.modexpOutput
-- computes base^exp mod modulus by square-and-multiply, so the correctness of the
-- inversion frame is a THEOREM (modexpInv_correct below), stated as a hole rather
-- than as a field so nobody later mistakes the modelled arithmetic for trusted
-- arithmetic. D14 / design2 disagreement D say exactly this.
--
-- SATISFIABILITY. No in-tree object can discharge Eip2537.Holds today: the only
-- AdmissiblePairing instance is the exponent model in Midfall/Instances/, whose
-- toEip is not a curve point, and D-P17 forbids importing it here. So the
-- structure is a trusted-base entry (plan Section 1), not a deferred proof. That
-- is stated rather than hidden, per design2 hazard for this file.

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Curve
import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Yul.Externals

namespace Midfall.Assumptions
open Midfall Midfall.Halo2 Midfall.Yul

/-! ### The two moduli, tied together -/

/-- The scalar modulus in Midfall/Yul/Externals.lean is the same number as the one
    CompPoly provides, proved by rfl rather than re-typed. This is the R-20 defect
    class (docs/REVIEW.md): Assumptions/Pairing.lean once carried the BLS12-**377
    base modulus in a file that also had the right one, and the two BLS moduli share
    a 50-digit prefix so the slip was invisible to the eye. Externals.lean:57-64
    records that it refused to import pBase for exactly that reason and defined its
    own blsP; this theorem is the check that the two copies agree. -/
theorem blsR_eq_r : blsR = Assumptions.r := rfl

/-- The base-field modulus, same story: Externals.blsP is the EIP-2537 number and
    Assumptions.pBase is the fixed literal (Pairing.lean:55-64 records the bug and
    the gate that now catches it). -/
theorem blsP_eq_pBase : blsP = Assumptions.pBase := rfl

/-- CompPoly proves the scalar modulus prime; transported across blsR_eq_r so the
    precompile arithmetic can use ZMod blsR as a field without restating the
    number. Proved by rewriting, not by decide: a 255-bit primality proof does not
    belong in the kernel here. -/
instance : Fact (Nat.Prime blsR) := ⟨by
  have h : blsR = Assumptions.r := rfl
  exact h ▸ (inferInstance : Fact (Nat.Prime Assumptions.r)).out⟩

/-! ### The G2 encoder -/

/-- An abstract EIP-2537 G2 encoder: 256 bytes per point (Externals.g2Bytes). The
    only G2 encoding in the tree is Generator.VkPointCodecs.g2Repr composed with
    g2ToU256s, which sits behind Generator/Vk.lean import of Midfall/Instances/
    (design2 disagreement D), so the hypothesis layer takes the encoder as a
    wrapped function rather than importing it. The wrapper - rather than a bare
    G2 -> Bytes - is attack.md line 84 FIX: it is the hook where the VK-header
    agreement field hangs in Surface.lean. -/
structure G2Enc (G₂ : Type) where
  /-- The 256-byte padded EIP-2537 encoding. -/
  toEip : G₂ -> Bytes

/-! ### The hypothesis structure -/

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- What EIP-2537 must deliver for the generated verifier, relative to the two
    codecs and the pairing-product oracle (the Fp12 hole, Externals.lean:934-941).

    pairing2 is the two-pair form: the verifier pairs exactly two pairs, and the
    equation is written additively in Gₜ so the identity is 0 (EIP-2537 says the
    product must equal 1 multiplicatively). g1Add and g1Msm1 pin the frames the
    accumulator helper rewrites in place (FinalPairing.yul:36-60), and the MSM
    scalar is the canonical big-endian word frToInputBE s - the same bytes as
    wordToBytesBE (frWord s) in Exec/Accumulator.lean:433, spelled here without
    importing the Exec layer. g1Decodes is the soundness side: a frame the
    precompile validators accept must decode through the codec, which is what
    closes the points_subgroup_checked gap for the no-accumulator path (design0
    note on this declaration). -/
structure Eip2537.Holds (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop where
  /-- Encoded G1 points are what the byte-level validators accept: on-curve,
      canonical, in the r-torsion (Externals.g1PointMsmValid). -/
  g1Valid : ∀ Q : G₁, ∃ pt, g1Of? (c.toEip Q) = some pt ∧ g1PointMsmValid pt = true
  /-- Same for G2, for the encoder above. -/
  g2Valid : ∀ R : G₂, ∃ pt, g2Of? (c₂.toEip R) = some pt ∧ g2PointValid pt = true
  /-- PAIRING_CHECK on two pairs is the additive pairing equation. -/
  pairing2 : ∀ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
    product (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) +
        P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) = 0
  /-- G1ADD on the 0x100-byte frame is the group law (R-21: the frame is two
      padded points, not the 0x80 the work-package brief claimed - see
      Externals.lean divergence 4). -/
  g1Add : ∀ P₁ P₂ : G₁,
    g1AddOutput (g1AddFrame (c.toEip P₁) (c.toEip P₂)) = some (c.toEip (P₁ * P₂))
  /-- One-pair G1MSM on the interleaved 0xa0-byte record is the scalar action
      (gsmul). The scalar is the canonical word: EIP-2537 lets a MSM scalar exceed
      r, and a non-canonical word would alias to a different field element. -/
  g1Msm1 : ∀ (Q : G₁) (s : Fr p),
    g1MsmOutput (g1MsmFrame [(c.toEip Q, frToInputBE s)]) = some (c.toEip (gsmul s Q))
  /-- Soundness side: a frame the precompile accepts decodes through the codec. -/
  g1Decodes : ∀ b : Bytes, (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
    ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-! ### Modexp is arithmetic, not an assumption -/

/-- The generated inversion frame returns x to the power r-2 modulo r, which is
    x inverse in the scalar field for every nonzero x below r (Fermat). Externals
    COMPUTES modexpOutput, so this is a theorem and not a hypothesis - D14 and
    design2 disagreement D are explicit that stating it as an assumption would
    mislabel modelled arithmetic as trusted arithmetic.

    PROOF OBLIGATION, registered in SORRY.md: modPow is a square-and-multiply over
    the bits of the exponent, so the proof is the correctness of that fold plus
    the Fermat identity in ZMod blsR. NOTE: the plan sketch cites
    ZMod.pow_card_sub_two_eq_inv, which does NOT exist in the pinned Mathlib
    (measured: no such constant); the available form is ZMod.pow_card_sub_one_eq_one
    (Mathlib/FieldTheory/Finite/Basic.lean:612), from which the inverse identity
    follows in one line. Reported as a stage-1 finding. -/
theorem modexpInv_correct (x : ℕ) (hx : 0 < x) (hr : x < blsR) :
    modexpOutput (modexpInvFrame x) =
      some (bytesNatBE ((x : ZMod blsR)⁻¹).val wordBytes) := by
  sorry

/-! ### Gates -/

/-- The known answer the plan names: the inverse of 2 is (r+1)/2, checked against
    the COMPUTED modexp output, not against an assumption. This is the gate that
    distinguishes modexpInv_correct from a hypothesis: the frame is parsed, the
    exponentiation runs, and the byte result is compared with the field inverse.
    The second line pins the frame width the contract emits (0xc0 = 6 words), and
    the third pins the two-pair pairing frame at 0x300 bytes, which is what
    pairing2 quantifies over. -/
def modexpInvKats_ok : Bool :=
  (match modexpOutput (modexpInvFrame 2) with
   | some o => bytesToNatBE o == (blsR + 1) / 2
   | none => false) &&
  (match modexpOutput (modexpInvFrame 7) with
   | some o => (bytesToNatBE o * 7) % blsR == 1
   | none => false) &&
  (modexpInvFrame 2).size == modexpFrameBytes && modexpFrameBytes == 0xc0 &&
  (pairingFrame [((bytesZero g1Bytes), (bytesZero g2Bytes)),
    ((bytesZero g1Bytes), (bytesZero g2Bytes))]).size == pairingTwoPairBytes &&
  pairingTwoPairBytes == 0x300 && g1MsmPairBytes == 0xa0 && g1AddInputBytes == 0x100

#eval modexpInvKats_ok   -- expect true

/-- The MSM scalar slot is big-endian: 2 sits in the LAST byte of the word, not
    the first. A little-endian scalar slot would make g1Msm1 disagree with
    AccumulatorHelpers.yul:300-301, and the two BLS byte orders differ only in
    which end the value sits at - the R-20 class again. -/
local instance smallPrime : Fact (Nat.Prime 17) := ⟨by decide⟩

def msmScalarWordKats_ok : Bool :=
  (frToInputBE (p := 17) (2 : Fr 17)).size == 32 &&
    (frToInputBE (p := 17) (2 : Fr 17)).data[31]? == some 2 &&
    (frToInputBE (p := 17) (2 : Fr 17)).data[0]? == some 0 &&
    (g1MsmFrame [((bytesZero g1Bytes), (frToInputBE (p := 17) (2 : Fr 17)))]).size == g1MsmPairBytes

#eval msmScalarWordKats_ok   -- expect true

end Midfall.Assumptions
