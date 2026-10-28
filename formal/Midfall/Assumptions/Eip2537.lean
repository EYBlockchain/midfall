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

/-! ### THE SATISFIABILITY DEFECT: g1Decodes IS UNSATISFIABLE AS WRITTEN

P-CURVE (docs/plans/P-CURVE-real-g1.md) was fired to make Eip2537.Holds satisfiable by
building a real-curve G1 model, on R-61's reading that the only thing between the exponent
model and a Holds exhibit is a curve. Measured here, BEFORE any curve work, that is not the
obstacle: the g1Decodes clause is unsatisfiable for EVERY codec on EVERY prime-order group,
curve included, so the four-way headline bundle is not merely unexhibited - it is PROVABLY
EMPTY, and no amount of curve modelling can change that until the clause is repaired.

THE MECHANISM. g1Decodes quantifies over all b : Bytes that the byte validators accept:

    (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
      ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

and g1Of? is the COORDINATE decoder, not a frame validator: it reads bytes 0..64 and 64..128
through bytesSlice, which clamps to the bytes that exist and never checks the length. So
every extension of a valid 128-byte frame by any number of trailing bytes satisfies the
antecedent - garbageFrame k below is the infinite family, all-zero frames of length 0x80 + k,
every one of which decodes to the point of infinity and passes g1PointMsmValid. The consequent
then demands c.toEip Q = garbageFrame k for each k, i.e. that toEip hit infinitely many
distinct byte strings. But PrimeOrderWith G1 p says Nat.card G1 = p, so toEip has at most p
values. Contradiction, proved below with no computation heavier than a 64-byte decide and no
axiom beyond the standard three.

WHY THE OTHER FIVE CLAUSES DO NOT HAVE THIS PROBLEM, and why this one was invisible. g1Valid
is existential over the ENCODINGS the codec produces, so it constrains the range of toEip and
is happy with a finite one. g1Add, g1Msm1 and pairing2 are equations between precompile
outputs and codec outputs, again only over frames the codec itself emitted. Only g1Decodes
runs the implication the other way - from accepted BYTES to a codec preimage - and it is the
only clause written over raw Bytes rather than over (c.toEip Q). Every frame the precompile
actually accepts is length-pinned elsewhere (0x100 for G1ADD at g1AddValidInput, a whole
number of 0xa0 pairs for G1MSM at g1MsmPairs?, of 0x180 for PAIRING_CHECK at pairingPairs?),
so nothing in the byte model can see the difference; the clause's own docstring says "a frame
the precompile accepts", and the precompile does NOT accept a 0x81-byte point. The defect is
that the clause says g1Of?-accepts where the doc says frame-accepts.

THE REPAIR, stated below as g1DecodesWidth and NOT substituted into the structure. Adding the
frame-width condition to the antecedent - b.size == g1Bytes, which is what the docstring
already means - removes the obstruction: Holds.g1Decodes implies the repaired clause (proved
below, so the repair is a genuine relaxation of an unsatisfiable demand and not a rewording),
and the real-curve frame type in Midfall/Instances/Bls12_381G1.lean satisfies the repaired
clause outright. Swapping it into the structure is a HEADLINE STATEMENT CHANGE and is
deliberately left to the orchestrator: this package's rule is that a hypothesis is repaired by
a decision and a review, not by the agent who is graded on satisfying it. What is NOT closed
by the repair is recorded there: the remaining clauses still need a group law over Fp and a
count of the r-torsion, so repairing g1Decodes unblocks the clause but not the exhibit. -/

/-- A valid 128-byte G1 frame with k extra bytes appended. g1Of? accepts every one of them as
    the point of infinity, because it slices rather than checks the length. -/
def garbageFrame (k : ℕ) : Bytes := bytesZero (g1Bytes + k)

@[simp] theorem garbageFrame_size (k : ℕ) : (garbageFrame k).size = g1Bytes + k := by
  show (bytesReplicate (g1Bytes + k) 0).size = _
  classical
  show (List.replicate (g1Bytes + k) (0 : UInt8)).toArray.size = _
  rw [List.toArray_replicate, Array.size_replicate]

/-- The two slices g1Of? reads out of an all-zero frame, at any length that contains them. -/
theorem bytesSlice_bytesZero (n i j : ℕ) (h : i + j ≤ n) :
    bytesSlice (bytesZero n) i j = bytesZero j := by
  classical
  simp only [bytesSlice, bytesZero, bytesReplicate, List.toArray_replicate, ByteArray.size,
    Array.size_replicate, Nat.min_eq_left (by omega : i <= n),
    Nat.min_eq_left (by omega : i + j <= n), Array.extract_replicate, Nat.add_sub_cancel_left]

/-- The distinctness half of the obstruction: the family is infinite because the SIZES
    differ, so no two of them can share a codec preimage. -/
theorem garbageFrame_injective : Function.Injective garbageFrame := by
  intro k j h
  have := congrArg ByteArray.size h
  rw [garbageFrame_size, garbageFrame_size] at this
  omega

set_option maxRecDepth 1000000 in
private theorem fpCoordOf?_bytesZero64 : fpCoordOf? (bytesZero 64) = some 0 := by decide

/-- EVERY member of the family is accepted by the byte validators: g1Of? decodes it to the
    point of infinity and g1PointMsmValid passes that point. This is the witness half of the
    defect (D-P23): not a claim that the clause is awkward, but an explicit infinite family of
    counterexample inputs. -/
theorem garbageFrame_accepted (k : ℕ) :
    ∃ pt, g1Of? (garbageFrame k) = some pt ∧ g1PointMsmValid pt = true := by
  refine ⟨(0, 0), ?_, by decide⟩
  have e1 : bytesSlice (garbageFrame k) 0 64 = bytesZero 64 :=
    bytesSlice_bytesZero _ _ _ (by unfold g1Bytes; omega)
  have e2 : bytesSlice (garbageFrame k) 64 64 = bytesZero 64 :=
    bytesSlice_bytesZero _ _ _ (by unfold g1Bytes; omega)
  simp [g1Of?, e1, e2, fpCoordOf?_bytesZero64]

/-- THE DEFECT, AS A THEOREM. The g1Decodes clause cannot be discharged by any codec on any
    prime-order group. The proof is the pigeonhole: the clause makes toEip hit every
    garbageFrame k, the family is infinite, and Nat.card G1 = p makes the range finite -
    formally, an injection (Nat → G1) makes G1 infinite, so its Nat.card is 0, not p. -/
theorem g1Decodes_unsatisfiable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] (c : G1Codec G₁) :
    ¬ (∀ b : Bytes, (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
        ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b) := by
  intro h
  have key : ∀ k : ℕ, ∃ Q, c.ofEip? (garbageFrame k) = some Q ∧ c.toEip Q = garbageFrame k :=
    fun k => h _ (garbageFrame_accepted k)
  choose Q hQ using key
  have hinj : Function.Injective Q := by
    intro k j hkj
    exact garbageFrame_injective
      ((hQ k).2.symm.trans ((congrArg c.toEip hkj).trans (hQ j).2))
  haveI : Infinite G₁ := Infinite.of_injective Q hinj
  have hc : Nat.card G₁ = p := (inferInstance : PrimeOrderWith G₁ p).hCard
  rw [Nat.card_eq_zero_of_infinite] at hc
  exact absurd hc.symm (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

/-- THE HEADLINE CONSEQUENCE: Eip2537.Holds has no model at all, at any curve, over any group,
    with any G2 encoder and any pairing product. This is what makes the four-way bundle
    (BlkIsEmitter ∧ SupportedS ∧ EnvAgrees ∧ Eip2537.Holds) empty rather than merely
    unexhibited, and it is the eighth false-as-written finding of the class R-60 S1 named
    and R-62 counted to seven - except that this time the conjunction is REFUTED, not merely
    unpopulated. -/
theorem holds_unsatisfiable (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) :
    ¬ (Eip2537.Holds c c₂ product) :=
  fun h => g1Decodes_unsatisfiable c h.g1Decodes

/-- The non-existence form, which is the shape the bundle gate cares about: there is no triple
    of codec, encoder and oracle making the hypothesis true, so no field of LoweringCorrect
    that takes Eip2537.Holds can ever be discharged by exhibit until the clause is repaired. -/
theorem not_exists_holds :
    ¬ (∃ (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct),
        Eip2537.Holds c c₂ product) := by
  rintro ⟨c, c₂, product, h⟩
  exact holds_unsatisfiable c c₂ product h

/-- THE REPAIR. b.size == g1Bytes is the frame-width condition the clause's docstring already
    states ("a frame the precompile accepts") and that every real frame validator pins: G1ADD
    at 0x100 (g1AddValidInput), G1MSM at a whole number of 0xa0 pairs (g1MsmPairs?),
    PAIRING_CHECK at a whole number of 0x180 pairs (pairingPairs?). It is stated here as a
    named proposition, NOT substituted into Eip2537.Holds, because changing a headline
    hypothesis is a decision for the orchestrator and not for the package that wants to
    satisfy it (D-P23). -/
def g1DecodesWidth (c : G1Codec G₁) : Prop :=
  ∀ b : Bytes, b.size == g1Bytes → (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
    ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-- The repair is a relaxation of the written clause and nothing more: every Holds satisfies
    it. Stated as an implication rather than as a replacement so the direction is on the
    record - the written clause is strictly stronger, and strictly stronger than
    satisfiable. -/
theorem holds_g1DecodesWidth (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct)
    (h : Eip2537.Holds c c₂ product) : g1DecodesWidth c :=
  fun b _hs ⟨pt, hpt, hv⟩ => h.g1Decodes b ⟨pt, hpt, hv⟩

/-- THE FAILURE MODE OF THE DEFECT, as a computation (R-41: a demonstrated failure mode, not a
    narrative). Lines 1-2: the coordinate decoder accepts a 0x81- and a 0xa0-byte frame as the
    point of infinity, which is what makes the antecedent infinite. Line 3: the frames are
    pairwise distinct, so they need pairwise distinct preimages. Lines 4-6: the PRECOMPILE
    itself refuses those lengths, so the tolerance is an artefact of g1Of? being a coordinate
    reader and not a statement about what EIP-2537 accepts - which is why the repair is a
    width condition and not a change to the precompile model. -/
def g1DecodesDefectKats_ok : Bool :=
  (match g1Of? (garbageFrame 1) with
   | some pt => g1PointMsmValid pt && g1Of? (garbageFrame 1) == some ((0, 0) : Nat × Nat)
   | none => false) &&
  (match g1Of? (garbageFrame 32) with
   | some pt => g1PointMsmValid pt
   | none => false) &&
    ! bytesEq (garbageFrame 1) (garbageFrame 2) &&
    ! g1AddValidInput (garbageFrame 32) &&
    g1MsmPairs? (garbageFrame 1) == none &&
    ! pairingValidInput (garbageFrame 32) &&
    g1Bytes == 0x80 && g1AddInputBytes == 2 * g1Bytes

#eval g1DecodesDefectKats_ok   -- expect true

end Midfall.Assumptions
