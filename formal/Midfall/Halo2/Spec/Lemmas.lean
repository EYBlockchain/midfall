import Midfall.Common.Curve

/-!
Phase 4a algebra lemmas: deterministic facts the lowering proofs consume.

Everything here is stated over a general field or commutative ring rather than over
the exponent model or a concrete pairing. The content is in the exponents and the
indices, so the extra generality is free and the lemmas lift to any AdmissiblePairing
by bilinearity.
-/
namespace Midfall.Halo2.Spec.Lemmas

/-! ## The DualMSM pairing-reorder lemma

The Rust verifier checks   e(left, sG2) * e(right, -G2) = 1
The contract checks        e(right, G2) * e(left, -sG2) = 1

Plan Section 6 lists the equivalence as required, because AssemblyHelpers.yul
lays the pairing input out as [RHS|G2|LHS|NEG_S_G2]: a reordering AND a move of
the negation between the two pairs. Writing left = xL*g1, right = xR*g1 and
sG2 = s*g2, bilinearity turns each product of pairings into one scalar equation,
so the content is entirely in those exponents and needs no pairing to prove.
-/

/-- The Rust-side exponent equation. -/
def rustEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xL * s - xR = 0

/-- The contract-side exponent equation. -/
def contractEq {R : Type*} [CommRing R] (xL xR s : R) : Prop := xR - s * xL = 0

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

/-! ## Z_H and rotate_omega

The port's Domain carries omega, omega_inv and extended_omega; these are the
identities the per-partial proofs need from them.
-/

/-- **Z_H vanishes on H.** With Z_H(x) = x^n - 1 and ω an n-th root of unity,
    Z_H(ω^i) = 0 for every i. -/
theorem zH_vanishes {F : Type*} [Field F] (ω : F) (n i : ℕ) (h : ω ^ n = 1) :
    (ω ^ i) ^ n = 1 := by
  calc (ω ^ i) ^ n = ω ^ (i * n) := (pow_mul ω i n).symm
    _ = ω ^ (n * i) := by rw [Nat.mul_comm]
    _ = (ω ^ n) ^ i := pow_mul ω n i
    _ = 1 := by rw [h]; exact one_pow _

/-- **rotate_omega agrees with multiplication by ω^rot.** Rotating a domain index
    is multiplying by the rotation factor; the permutation and lookup telescoping
    proofs invoke this repeatedly.

    NOTE this is the unreduced-index form. The reduced version
    ω^((i+rot) % n) = ω^i * ω^rot needs ω to have order exactly n, not merely
    dividing n, plus the exponent reduction a^(m % n) = a^m. Deferred rather than
    approximated: the port's rotateOmega computes the reduced index, so a
    per-partial proof will want the mod form, and it is tracked as an open item
    rather than papered over with a weaker statement. -/
theorem rotate_omega_eq {F : Type*} [Field F] (ω : F) (i rot : ℕ) :
    ω ^ (i + rot) = ω ^ i * ω ^ rot := pow_add ω i rot

/-- Non-vacuity: the reorder relation holds for some triples and fails for others,
    over a concrete field. Without this the two sides could both be constants. -/
example : rustEq (R := ZMod 17) 1 1 1 := by unfold rustEq; decide
example : ¬ rustEq (R := ZMod 17) 1 2 1 := by unfold rustEq; decide
example : contractEq (R := ZMod 17) 1 1 1 := by unfold contractEq; decide
example : ¬ contractEq (R := ZMod 17) 1 2 1 := by unfold contractEq; decide
example : (2 : ZMod 7) ^ 3 = 1 := by decide
example : ((2 : ZMod 7) ^ 2) ^ 3 = 1 := by decide
example : (2 : ZMod 7) ^ (2 + 2) = (2 : ZMod 7) ^ 2 * (2 : ZMod 7) ^ 2 := by decide

end Midfall.Halo2.Spec.Lemmas
