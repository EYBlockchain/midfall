import Midfall.Common.Curve

/-!
Phase 4a algebra, first entry: the DualMSM pairing-reorder lemma.

The Rust verifier checks   e(left, sG2) * e(right, -G2) = 1
The contract checks        e(right, G2) * e(left, -sG2) = 1

Plan Section 6 lists the equivalence as a required lemma, because
AssemblyHelpers.yul:213-232 lays the pairing input out as [RHS|G2|LHS|NEG_S_G2]
- a reordering AND a move of the negation between the two pairs.

The mathematical content lives entirely in the EXPONENTS: writing left = xL * g1,
right = xR * g1 and sG2 = s * g2, bilinearity turns each product of pairings into
one equation over the scalar field, and the two checks become the two sides below.
So the lemma is stated over a general commutative ring rather than over the
exponent model: it is model-independent, needs no pairing, and lifts to any
AdmissiblePairing by bilinearity. The lifting is the remaining step and is
tracked below.
-/
namespace Midfall.Halo2.Spec.Lemmas

/-- The Rust-side exponent equation. -/
def rustEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xL * s - xR = 0

/-- The contract-side exponent equation. -/
def contractEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xR - s * xL = 0

/-- REORDER LEMMA. The two checks accept exactly the same triples. -/
theorem pairing_reorder {R : Type*} [CommRing R] (xL xR s : R) :
    rustEq xL xR s ↔ contractEq xL xR s := by
  constructor
  · intro h
    rw [rustEq, sub_eq_zero] at h
    rw [contractEq, sub_eq_zero]
    rw [← h]
    ring
  · intro h
    rw [contractEq, sub_eq_zero] at h
    rw [rustEq, sub_eq_zero]
    rw [h]
    ring

/-- Content, so the equivalence above cannot be satisfied by two unsatisfiable
    predicates (the R-30 / R-32 vacuity pattern): each side is equivalent to the
    single relation the DualMSM is meant to enforce. -/
theorem rustEq_iff {R : Type*} [CommRing R] (xL xR s : R) :
    rustEq xL xR s ↔ xR = s * xL := by
  rw [rustEq, sub_eq_zero, eq_comm, mul_comm]

theorem contractEq_iff {R : Type*} [CommRing R] (xL xR s : R) :
    contractEq xL xR s ↔ xR = s * xL := by
  rw [contractEq, sub_eq_zero]

/-- Non-vacuity: the relation holds for some triples and fails for others, so
    neither side is a constant predicate. -/
example : rustEq (R := ZMod 17) 1 1 1 := by unfold rustEq; decide
example : ¬ rustEq (R := ZMod 17) 1 2 1 := by unfold rustEq; decide
example : contractEq (R := ZMod 17) 1 1 1 := by unfold contractEq; decide
example : ¬ contractEq (R := ZMod 17) 1 2 1 := by unfold contractEq; decide

end Midfall.Halo2.Spec.Lemmas
