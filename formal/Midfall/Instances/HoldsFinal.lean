-- |
-- Midfall.Instances.HoldsFinal
--
-- P-HOLDS-FINAL STEPS 2 AND 5: THE LANDMARK. 'Eip2537.Holds' exhibited as ONE unconditional term,
-- at the real-curve G1 codec and the exponent-fold G2 codec, over the pairing D-P36a assumes.
--
-- THE WHOLE DERIVATION IS ONE TERM: 'holds_exhibited' below is 'holds_staged' with its single
-- binder discharged by 'Midfall/Assumptions/CurvePairing.lean'. That is the intended shape and
-- not a shortcut - P-G2B staged the exhibit precisely so that installing D-P36a would be a few
-- lines. What is NOT here: no Fp12, no pairing construction, no claim about a Surface. The
-- assumption is named, documented and gate-enforced in Assumptions/CurvePairing.lean, and
-- 'assumption_dP36a' in Instances/ObligationsGates.lean is its registry record.
--
-- WHY IN Instances/. D-P17: the exhibit cites 'g1CodecZ', 'g2CodecFold' and 'holds_staged', all
-- of which are concrete models, so it cannot live in a theorem-bearing file outside this
-- directory. The confinement gate is what keeps it here rather than in Lowering/.
--
-- WHAT THE EXHIBIT DOES NOT BUY, stated because the gap record used to over-state this in both
-- directions. It does not make any headline field provable, and it does not make the fixture's
-- four-way bundle inhabited: 'realSurface.E.g1' IS the exponent codec, so
-- 'bundle_holds_empty' still refutes that conjunction and stays exactly where it was. The
-- hypothesis the spec theorems bind is 'Holds S.E.g1 (S.encG2) product' - about the SURFACE's
-- own codec - and no Surface in the tree installs 'g1CodecZ'. What the exhibit removes is the
-- claim that the CLAUSE has no model, which is the difference between an unprovable theorem and
-- an unbuilt instance.
--
-- D-P23, BOTH HALVES, AS THEOREMS. Satisfiability: 'holds_exhibit_witness' (the exhibit lives on
-- non-degenerate carriers and its product answers FALSE on a frame whose pairing sum is
-- non-zero) and 'dP36a_class_not_empty' (the class being assumed has a model in the tree at the
-- same scalar field, so the binder is not an empty condition). Falsification:
-- 'holds_refutes_constant_true' and 'holds_refutes_constant_false' (the clause pins the product
-- the exhibit supplies - it is not a free parameter dressed as a hypothesis) and
-- 'dP36a_pairing_not_the_zero_map'. THE LIMIT, stated rather than hidden: no gate in this
-- repository deletes a falsification theorem and reddens the build. That gap has now been
-- measured FOURTEEN times, most recently in this package, and nothing here claims coverage for
-- it. Only the '#print axioms' probe in scripts/check_frozen_axioms.py is a real gate over what
-- this file depends on.

import Midfall.Instances.HoldsStaging
import Midfall.Instances.ExponentModel
import Midfall.Assumptions.CurvePairing

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions

/-! ### THE EXHIBIT -/

/-- **THE LANDMARK: ONE UNCONDITIONAL 'Eip2537.Holds' TERM.** There is a pairing product for
    which 'Eip2537.Holds' holds at 'g1CodecZ' - the codec whose bytes are real points of
    y^2 = x^3 + 4 over Fp, on the r-torsion carrier of the published H1 - and 'g2CodecFold',
    the exponent-fold G2 codec whose encoder is injective. All six clauses: 'g1Valid', 'g1Add',
    'g1Msm1', 'g1Decodes', 'g2Valid', 'pairing2'.

    The hypothesis budget is EXACTLY ONE named assumption, 'Midfall.Assumptions.bls12_381Pairing'
    and the four constants it needs (Assumptions/CurvePairing.lean, D-P36a), and '#print axioms'
    below is what says so: the standard three plus those five and nothing else. -/
theorem holds_exhibited : ∃ product : PairingProduct,
    Eip2537.Holds g1CodecZ g2CodecFold product := holds_staged

/-- **THE PROJECTION CHECK**: the term above is the live 'Holds' structure and not a look-alike,
    because its 'pairing2' field IS the live 'Pairing2' proposition. The pattern of
    'holds_pairing2_is_the_clause' (Assumptions/Eip2537.lean), restated at the exhibit. -/
theorem holds_exhibited_is_the_live_structure
    (h : Eip2537.Holds g1CodecZ g2CodecFold (pairingProductOf g1CodecZ g2foldOfEip?)) :
    Pairing2 g1CodecZ g2CodecFold (pairingProductOf g1CodecZ g2foldOfEip?) := h.pairing2

/-! ### D-P23: THE WITNESS HALVES, PLUS THE TWO FALSIFICATIONS THAT SHOW THE ASSUMPTION CONSTRAINS -/

/-- **THE ASSUMED CLASS IS NOT AN EMPTY CONDITION (D-P23 witness, half 1 for the assumption).** 'expAdmissible'
    inhabits 'AdmissiblePairing' at the same scalar field 'blsR' and at two of the three carriers
    this exhibit uses - 'G2fold' is 'Exp blsR' by definition. It is NOT a model of the assumption
    itself: the assumption is about 'G₁z' as well, and 'G₁z' is a carrier of real curve points
    that the exponent model does not reach. What it rules out is the worse failure mode, a binder
    nobody could ever satisfy. -/
theorem dP36a_class_not_empty : Nonempty (AdmissiblePairing G2fold G2fold G2fold) :=
  ⟨expAdmissible (p := blsR)⟩

/-- **THE ASSUMPTION EXCLUDES A DEGENERATE PAIRING (D-P23 falsification, half 1 for D-P36a).**
    'hNonDeg' is a field of the assumed class, so this is a consequence of the assumption and not a
    proof of it - which is exactly the point: the assumption CONSTRAINS what it assumes, and a
    pairing that is identically zero - the shape a vacuous binder would allow - does not satisfy
    it. -/
theorem dP36a_pairing_not_the_zero_map :
    ∃ (x : Additive G₁z) (y : Additive G2fold), bls12_381Pairing.e x y ≠ 0 :=
  ⟨Additive.ofMul bls12_381Pairing.g₁, Additive.ofMul bls12_381Pairing.g₂,
    bls12_381Pairing.hNonDeg⟩

/-- **THE ASSUMPTION EXCLUDES A SINGLETON TARGET (D-P23 falsification, half 2 for D-P36a).**
    'PrimeOrderWith' pins 'Nat.card blsGT = blsR' and 'blsR' is prime, so the carrier the exhibit
    lands in has more than one element. Without this the quantifiers over 'Gₜ' could be vacuous. -/
theorem dP36a_target_not_a_singleton : Nontrivial blsGT := by
  classical
  by_contra h
  have hcard : Nat.card blsGT = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨not_nontrivial_iff_subsingleton.mp h, ⟨1⟩⟩
  rw [blsGT_primeOrder.hCard] at hcard
  exact Nat.Prime.ne_one (Fact.out (p := Nat.Prime blsR)) hcard

/-- **THE EXHIBIT IS NON-DEGENERATE AND ITS PRODUCT IS PINNED (D-P23 witness, half 2).** The
    carriers are not trivial - the G1 encoder separates the generator from the identity and the
    G2 encoder's generator is not the identity - and the product the exhibit supplies answers
    FALSE on a named frame: the two-pair frame ((g₁, g₂), (1, 1)), whose pairing sum is
    'e g₁ g₂ + 0' and so is non-zero. A constant-true oracle would answer true there, which is
    the failure mode 'pairing2' exists to exclude. -/
theorem holds_exhibit_witness :
    ∃ product : PairingProduct, Eip2537.Holds g1CodecZ g2CodecFold product ∧
      g1zToEip g1zGen ≠ g1zToEip (1 : G₁z) ∧ (g2foldExp 1 : G2fold) ≠ 1 ∧
      product (pairingFrame [(g1CodecZ.toEip bls12_381Pairing.g₁,
          g2CodecFold.toEip bls12_381Pairing.g₂),
          (g1CodecZ.toEip (1 : G₁z), g2CodecFold.toEip (1 : G2fold))]) = false := by
  classical
  obtain ⟨product, h⟩ := holds_exhibited
  refine ⟨product, h, g1zToEip_not_constant, g2foldExp_one_ne_one, ?_⟩
  have hz : bls12_381Pairing.e (Additive.ofMul (1 : G₁z))
      (Additive.ofMul (1 : G2fold)) = 0 := by simp
  have key : bls12_381Pairing.e (Additive.ofMul bls12_381Pairing.g₁)
      (Additive.ofMul bls12_381Pairing.g₂) +
      bls12_381Pairing.e (Additive.ofMul (1 : G₁z)) (Additive.ofMul (1 : G2fold)) ≠ 0 := by
    rw [hz, add_zero]
    exact bls12_381Pairing.hNonDeg
  have hiff := h.pairing2 bls12_381Pairing.g₁ (1 : G₁z) bls12_381Pairing.g₂ (1 : G2fold)
  exact Bool.eq_false_of_ne_true (fun ht => key (hiff.mp ht))

/-! ### D-P23: THE FALSIFICATION HALVES FOR THE EXHIBIT ITSELF -/

/-- **THE CLAUSE BITES, HALF 1 (D-P23 falsification): the always-true oracle does not satisfy
    'Holds' at the exhibited codecs.** Same shape as 'constantTrue_not_pairing2'
    (Instances/PairingProduct.lean) but at the CURVE codecs, and it needs the assumed pairing's
    non-degeneracy to fire - which is the honest reading of what D-P36a buys and what it costs. -/
theorem holds_refutes_constant_true :
    ¬ Eip2537.Holds g1CodecZ g2CodecFold (fun _ => true) := by
  intro h
  have hz : bls12_381Pairing.e (Additive.ofMul (1 : G₁z))
      (Additive.ofMul (1 : G2fold)) = 0 := by simp
  have key : bls12_381Pairing.e (Additive.ofMul bls12_381Pairing.g₁)
      (Additive.ofMul bls12_381Pairing.g₂) +
      bls12_381Pairing.e (Additive.ofMul (1 : G₁z)) (Additive.ofMul (1 : G2fold)) ≠ 0 := by
    rw [hz, add_zero]
    exact bls12_381Pairing.hNonDeg
  have := (h.pairing2 bls12_381Pairing.g₁ (1 : G₁z) bls12_381Pairing.g₂ (1 : G2fold)).mp rfl
  exact key this

/-- **THE CLAUSE BITES, HALF 2 (D-P23 falsification): so does the always-false oracle.** The
    all-identity frame has pairing sum 0, so 'pairing2' demands 'true' there and a product that
    never says true cannot supply it. Together with 'holds_refutes_constant_true' this says the
    free parameter 'product' is genuinely constrained by the exhibit and not left free by it. -/
theorem holds_refutes_constant_false :
    ¬ Eip2537.Holds g1CodecZ g2CodecFold (fun _ => false) := by
  intro h
  have hz : bls12_381Pairing.e (Additive.ofMul (1 : G₁z))
      (Additive.ofMul (1 : G2fold)) +
      bls12_381Pairing.e (Additive.ofMul (1 : G₁z)) (Additive.ofMul (1 : G2fold)) = 0 := by
    simp
  have := (h.pairing2 (1 : G₁z) (1 : G₁z) (1 : G2fold) (1 : G2fold)).mpr hz
  exact absurd this (by simp)

#print axioms holds_exhibited
#print axioms holds_exhibit_witness
#print axioms holds_refutes_constant_true
#print axioms holds_refutes_constant_false
#print axioms dP36a_target_not_a_singleton

end Midfall.Instances
