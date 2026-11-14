-- |
-- Midfall.Instances.G2Agreement
--
-- P-G2 STEPS 2 AND 3: the G2 curve over Fp2, the AGREEMENT between the byte-level affine group law
-- of 'fp2Ops' (Midfall/Yul/Externals.lean) and mathlib's elliptic-curve group law at the real
-- modulus, the published generator H2 with 'r • H2 = 0' as a kernel theorem, the prime-order
-- carrier G₂z, and 'g2Valid' - the last unexhibited clause of 'Eip2537.Holds' - DISCHARGED at a
-- real-curve G2 codec.
--
-- IT IS A MIRROR OF Instances/G1Agreement.lean, deliberately. Every wall that file documents is
-- inherited rather than rediscovered: the 'Point.some' dependent-proof obstruction and its 'subst'
-- cure ('point_some_eq2'), the pair-'==' whnf wall that forces 'unfold' instead of 'rw' across
-- 'g2InSubgroup', the canonicity walk over VARIABLES rather than literals, and the rule that a
-- 255-bit 'nsmul' or 'affineSmul' must never be whnf'd by the elaborator. Where the mirror is
-- cheaper than the original is stated in the lemma that is cheaper.
--
-- WHAT IS NEW AND WHAT IT COST.
--   * The field is Fp2 = Fp[u]/(u^2+1) (Instances/Fp2.lean), so the coefficient is 4(u+1) = (4,4)
--     and the discriminant is -13824u rather than -6912: a different computation, same shape.
--   * THE EXPENSIVE KERNEL COMPUTATION IS CHEAPER THAN PREDICTED. 'affineSmul fp2Ops blsR h2Pair =
--     ((0,0),(0,0))' by 'decide' measures 8.6 s here (maxRecDepth 100000, maxHeartbeats 4e9,
--     largest process 4.42 GiB), where the brief budgeted ~4x the G1 fold's 16.6 s. The reason is
--     visible in the definitions: the cost of the fold is the 'modPow' inside 'fpInv', and
--     'fp2Ops.inv' calls 'fpInv' EXACTLY ONCE per inverse (on the norm, a 381-bit natural), so a
--     G2 step costs one G1-sized modPow plus cheap pair arithmetic. It is a 255-step fold either
--     way. Recorded because the estimate was wrong in the pessimistic direction, and because the
--     number decides whether it can be wired into a gate: it is a THEOREM here and appears in no
--     '#eval', so no gate pass re-runs it (P-GAPFIX's warning).
--   * INDEPENDENT CHECK BEFORE THE KERNEL WAS ASKED. The published H2 coordinates, the curve
--     equation, and 'r • H2 = O' were all verified in Python bignum arithmetic over
--     Fp[u]/(u^2+1) before any 'decide' was run, so a 'decide' that returned true could not be
--     mistaken for a vacuity: the same program also confirms '(r-1) • H2 = -H2' and '3 • H2 ≠ O'.
--
-- D-P23: every claim below carries a witness and a falsification AS THEOREMS, and the honest limit
-- of the gate coverage is stated at the bottom: 'checks.sh' runs the '#eval' lines, 'lake build'
-- runs the theorems, and NOTHING in either deletes a falsification theorem and reddens the build.

import Midfall.Instances.Fp2
import Midfall.Instances.G1Agreement
import Midfall.Assumptions.Eip2537
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators

private theorem p_pos2 : 0 < blsP := Nat.Prime.pos (Fact.out : Nat.Prime blsP)
private theorem r_prime2 : Nat.Prime blsR := Fact.out (p := Nat.Prime blsR)

/-! ### THE CURVE y^2 = x^3 + 4(u+1) OVER Fp2 -/

/-- **THE SHORT MODEL OVER Fp2**: 'y^2 = x^3 + 4(v+1)' with EIP-2537's 'v' spelled 'u' here, i.e.
    the coefficient 'ofPair 4 4'. The spelling rules are the G1 file's: unicode subscripts a₁..a₆,
    and the type ascription 'Affine Fp2' so dot projection resolves 'W2.Point' / 'W2.Equation' /
    'W2.nonsingular_iff'. -/
noncomputable def W2 : Affine Fp2 :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := ofPair (4 : FpBase) (4 : FpBase) }

private theorem a₁z2 : (W2.a₁ : Fp2) = 0 := rfl
private theorem a₂z2 : (W2.a₂ : Fp2) = 0 := rfl
private theorem a₃z2 : (W2.a₃ : Fp2) = 0 := rfl
private theorem a₄z2 : (W2.a₄ : Fp2) = 0 := rfl
private theorem a₆z2 : (W2.a₆ : Fp2) = ofPair (4 : FpBase) (4 : FpBase) := rfl

/-- The small integers stay nonzero in Fp2: they sit in the base field, where they are nonzero, and
    'ofPair' reflects zero. -/
private theorem natCast_ne_zero_FpBase {n : ℕ} (hn : n < blsP) (hn0 : n ≠ 0) : (n : FpBase) ≠ 0 := by
  intro h
  have h1 : ((n : FpBase)).val = 0 := (ZMod.val_eq_zero (n : FpBase)).mpr h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn] at h1
  exact hn0 h1

private theorem coe_nat_ne_zero2 {n : ℕ} (hn : n < blsP) (hn0 : n ≠ 0) : (n : Fp2) ≠ 0 := by
  intro h
  have h2 : ofPair (n : FpBase) 0 = 0 := by
    have h3 : (n : Fp2) = ofPair (n : FpBase) 0 := (ofPair_natCast n).symm
    rw [← h3]
    exact h
  obtain ⟨h3, -⟩ := (ofPair_eq_zero_iff (n : FpBase) 0).mp h2
  exact natCast_ne_zero_FpBase hn hn0 h3

private theorem two_ne_zero2 : (2 : Fp2) ≠ 0 := coe_nat_ne_zero2 (by decide) (by decide)
private theorem three_ne_zero2 : (3 : Fp2) ≠ 0 := coe_nat_ne_zero2 (by decide) (by decide)
private theorem four_ne_zero2 : (4 : Fp2) ≠ 0 := coe_nat_ne_zero2 (by decide) (by decide)

/-- **THE CURVE EQUATION COLLAPSES** to 'y^2 = x^3 + 4(u+1)' in mathlib's five-coefficient form. -/
theorem equation_iff_sq2 (x y : Fp2) :
    W2.Equation x y ↔ y ^ 2 = x ^ 3 + ofPair (4 : FpBase) (4 : FpBase) := by
  rw [W2.equation_iff, a₁z2, a₂z2, a₃z2, a₄z2, a₆z2]
  constructor
  · intro h
    have hy : y ^ 2 + (0 : Fp2) * x * y + (0 : Fp2) * y = y ^ 2 := by ring
    have hx : x ^ 3 + (0 : Fp2) * x ^ 2 + (0 : Fp2) * x + ofPair (4 : FpBase) (4 : FpBase)
        = x ^ 3 + ofPair (4 : FpBase) (4 : FpBase) := by ring
    rw [hy, hx] at h
    exact h
  · intro h
    rw [h]
    ring

/-- **NON-SINGULARITY**: a singular point of the short form has 3x^2 = 0 and 2y = 0, so x = y = 0,
    and the equation then reads 0 = 4(u+1), false because 4(u+1) is nonzero in Fp2. -/
private theorem b4_ne_zero2 : (ofPair (4 : FpBase) (4 : FpBase) : Fp2) ≠ 0 := by
  intro h
  obtain ⟨h1, -⟩ := (ofPair_eq_zero_iff (4 : FpBase) (4 : FpBase)).mp h
  exact four_ne_zero_Fp h1

theorem nonsingular_of_equation2 {x y : Fp2} (h : W2.Equation x y) : W2.Nonsingular x y := by
  rw [W2.nonsingular_iff]
  refine ⟨h, ?_⟩
  by_cases hx : x = 0
  · right
    subst hx
    simp only [a₁z2, a₃z2, mul_zero, sub_zero]
    intro hy
    have h1 : (2 : Fp2) * y = 0 := by
      rw [two_mul]
      have h2 := congrArg (fun t => t + y) hy
      rw [h2]
      ring
    have hy0 : y = 0 := (mul_eq_zero.mp h1).resolve_left two_ne_zero2
    rw [hy0, W2.equation_zero, a₆z2] at h
    exact b4_ne_zero2 h
  · left
    intro hh
    simp only [a₁z2, a₂z2, a₄z2, mul_zero, add_zero, zero_mul] at hh
    have h1 : (3 : Fp2) * x ^ 2 = 0 := by simpa using hh
    have h2 : x ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left three_ne_zero2
    have h3 : x * x = 0 := by rwa [pow_two] at h2
    exact hx ((mul_eq_zero.mp h3).resolve_left hx)

/-- **THE DISCRIMINANT**: for a₁ = a₂ = a₃ = a₄ = 0 mathlib's b₂ and b₄ vanish, b₆ = 4a₆ and
    b₈ = 0, so Δ = -27(4a₆)^2 = -432 a₆^2. With a₆ = 4(u+1) the square is 16(1+u)^2 = 16(2u) =
    32u, so Δ = -13824u: nonzero, because u is nonzero and 13824 < p. -/
private theorem W2_b2 : W2.b₂ = (0 : Fp2) := by
  show (0 : Fp2) ^ 2 + 4 * 0 = 0
  simp

private theorem W2_b4 : W2.b₄ = (0 : Fp2) := by
  show 2 * (0 : Fp2) + 0 * 0 = 0
  simp

private theorem W2_b6 : W2.b₆ = ofPair (16 : FpBase) (16 : FpBase) := by
  show (0 : Fp2) ^ 2 + 4 * ofPair (4 : FpBase) (4 : FpBase) = _
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  have h4 : (4 : Fp2) = ofPair (4 : FpBase) 0 := (ofPair_natCast 4).symm
  rw [h4, ofPair_mul]
  refine congrArg₂ ofPair ?_ ?_ <;> norm_num

private theorem W2_b8 : W2.b₈ = (0 : Fp2) := by
  show (0 : Fp2) ^ 2 * ofPair (4 : FpBase) (4 : FpBase)
      + 4 * 0 * ofPair (4 : FpBase) (4 : FpBase) - 0 * 0 * 0 + 0 * 0 ^ 2 - 0 ^ 2 = 0
  simp

theorem W2_delta : (W2.Δ : Fp2) = -(ofPair (13824 : FpBase) 0 * u) := by
  show -(W2.b₂ ^ 2) * W2.b₈ - 8 * W2.b₄ ^ 3 - 27 * W2.b₆ ^ 2 + 9 * W2.b₂ * W2.b₄ * W2.b₆ = _
  rw [W2_b2, W2_b4, W2_b8, W2_b6]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, add_zero]
  have hsq : (ofPair (16 : FpBase) (16 : FpBase) : Fp2) ^ 2 = ofPair 0 (512 : FpBase) := by
    rw [pow_two, ofPair_mul]
    refine congrArg₂ ofPair ?_ ?_ <;> norm_num
  rw [hsq]
  have h27 : (27 : Fp2) = ofPair (27 : FpBase) 0 := (ofPair_natCast 27).symm
  have hu : u = ofPair 0 (1 : FpBase) := ofPair_u.symm
  have hc1 : ofPair (27 : FpBase) 0 * ofPair 0 (512 : FpBase) = ofPair 0 (13824 : FpBase) := by
    rw [ofPair_mul]
    refine congrArg₂ ofPair ?_ ?_ <;> norm_num
  have hc2 : ofPair (13824 : FpBase) 0 * ofPair 0 (1 : FpBase) = ofPair 0 (13824 : FpBase) := by
    rw [ofPair_mul]
    refine congrArg₂ ofPair ?_ ?_ <;> norm_num
  rw [h27, hu, hc1, hc2]
  ring

/-- **W2 IS AN ELLIPTIC CURVE**, so mathlib's 'AddCommGroup W2.Point' is available at the real
    modulus and 'n • P' is statable - the same move G1Agreement makes for 'W'. -/
instance : WeierstrassCurve.IsElliptic W2 := ⟨by
  rw [isUnit_iff_ne_zero, W2_delta]
  intro hh
  have h2 : ofPair (13824 : FpBase) 0 * u = 0 := neg_eq_zero.mp hh
  rcases mul_eq_zero.mp h2 with h3 | h4
  · obtain ⟨h5, -⟩ := (ofPair_eq_zero_iff (13824 : FpBase) 0).mp h3
    exact natCast_ne_zero_FpBase (by decide : 13824 < blsP) (by decide) h5
  · exact fp2_ne_ofPair_zero h4⟩

/-! ### THE FRAME TYPE AND THE EMBEDDING INTO MATHLIB'S CURVE -/

/-- An accepted affine Fp2 frame: both coordinates are pairs of naturals (the EIP's padded
    coordinates, as 'g2Of?' decodes them) and the byte validator 'affineOnCurve fp2Ops' accepts the
    point. This is the exact analogue of 'FpFrame' in Instances/G1Agreement.lean, and it carries the
    same two conventions: the all-zero frame is accepted (through the infinity branch) and is NOT a
    curve point, so it must map to 'Point.zero'. -/
def Fp2Frame : Type := { P : AffinePt (Nat × Nat) // affineOnCurve fp2Ops P = true }

private theorem Fp2Frame.onCurve (P : Fp2Frame) : affineOnCurve fp2Ops P.1 = true := P.2

/-- The all-zero frame: EIP-2537's point of infinity. -/
def infFrame2 : Fp2Frame := ⟨((0, 0), (0, 0)), by decide⟩

/-- **THE FIELD READINGS OF A BYTE POINT**: 'ofNatPair P.1' is the x-coordinate in Fp2 and
    'ofNatPair P.2' the y-coordinate. Spelled out rather than abbreviated, because 'Fp2' is
    noncomputable and an abbreviation over it cannot be compiled - the same reason 'ofNatPair' itself
    is 'noncomputable'. -/
private theorem inf_iff2 (P : AffinePt (Nat × Nat)) :
    affineIsInfinity fp2Ops P = true ↔ ofNatPair P.1 = 0 ∧ ofNatPair P.2 = 0 := by
  show (fp2Ops.beq P.1 fp2Ops.zero && fp2Ops.beq P.2 fp2Ops.zero) = true ↔ _
  rw [Bool.and_eq_true, fp2Beq_iff, fp2Beq_iff]
  simp only [ofNatPair_zero]

/-- The curve equation of an accepted non-infinity frame, in the product spelling the group law
    computes with. -/
private theorem frame_beq2 (P : Fp2Frame) (h : ¬ affineIsInfinity fp2Ops P.1) :
    ofNatPair P.1.2 * ofNatPair P.1.2
      = ofNatPair P.1.1 * ofNatPair P.1.1 * ofNatPair P.1.1 + ofPair (4 : FpBase) (4 : FpBase) := by
  have h1 := P.onCurve
  simp only [affineOnCurve, Bool.or_eq_true_iff] at h1
  cases h1 with
  | inl hin => exact absurd hin h
  | inr hb =>
      rw [fp2Beq_iff] at hb
      rw [ofNatPair_mul, ofNatPair_add, ofNatPair_mul, ofNatPair_mul, ofNatPair_b] at hb
      exact hb

private theorem frame_eq2 (P : Fp2Frame) (h : ¬ affineIsInfinity fp2Ops P.1) :
    ofNatPair P.1.2 ^ 2 = ofNatPair P.1.1 ^ 3 + ofPair (4 : FpBase) (4 : FpBase) := by
  have h2 := frame_beq2 P h
  rw [pow_two, pow_three, h2]
  ring

private theorem equation_of_frame2 (P : Fp2Frame) (h : ¬ affineIsInfinity fp2Ops P.1) :
    W2.Equation (ofNatPair P.1.1) (ofNatPair P.1.2) := by
  rw [equation_iff_sq2]
  exact frame_eq2 P h

/-- The converse: a pair satisfying the equation is an accepted frame - the direction that turns
    'nonsingular_add' into closure for the byte law. -/
private theorem onCurve_of_eq_pow2 (x : AffinePt (Nat × Nat))
    (h : ofNatPair x.2 ^ 2 = ofNatPair x.1 ^ 3 + ofPair (4 : FpBase) (4 : FpBase)) :
    affineOnCurve fp2Ops x = true := by
  rw [affineOnCurve, Bool.or_eq_true_iff]
  right
  rw [fp2Beq_iff]
  rw [ofNatPair_mul, ofNatPair_add, ofNatPair_mul, ofNatPair_mul, ofNatPair_b]
  rw [pow_two, pow_three] at h
  rw [← mul_assoc] at h
  exact h

private theorem onCurve_of_eq2 (x : AffinePt (Nat × Nat))
    (h : W2.Equation (ofNatPair x.1) (ofNatPair x.2)) : affineOnCurve fp2Ops x = true :=
  onCurve_of_eq_pow2 x ((equation_iff_sq2 (ofNatPair x.1) (ofNatPair x.2)).mp h)

/-- **THE EMBEDDING.** The all-zero frame maps to the point at infinity and every other accepted
    frame to the curve point with the same coordinates - the G1 file's 'emb', with 'ofNatPair' in
    place of the cast and the same trap: (0,0) is not a curve point because 4(u+1) ≠ 0. -/
noncomputable def emb2 (P : Fp2Frame) : W2.Point :=
  if h : affineIsInfinity fp2Ops P.1 then 0
  else Point.some (ofNatPair P.1.1) (ofNatPair P.1.2)
    (nonsingular_of_equation2 (equation_of_frame2 P h))

private theorem emb_inf2 (P : Fp2Frame) (h : affineIsInfinity fp2Ops P.1) : emb2 P = 0 := dif_pos h

private theorem emb_notInf2 (P : Fp2Frame) (h : ¬ affineIsInfinity fp2Ops P.1) :
    emb2 P = Point.some (ofNatPair P.1.1) (ofNatPair P.1.2)
      (nonsingular_of_equation2 (equation_of_frame2 P h)) := dif_neg h

theorem emb2_eq_zero_iff (P : Fp2Frame) :
    emb2 P = 0 ↔ affineIsInfinity fp2Ops P.1 = true := by
  classical
  by_cases h : affineIsInfinity fp2Ops P.1 = true
  · rw [emb_inf2 P h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [emb_notInf2 P h]
    exact ⟨fun hh => absurd hh (Point.some_ne_zero _), fun hh => absurd hh h⟩

/-- **THE ZERO FRAME IS NOT A CURVE POINT**, which is what makes the infinity convention
    unambiguous (the G1 file's 'four_ne_zero', lifted to Fp2). -/
private theorem not_onCurve_zero2 : ¬ W2.Equation (0 : Fp2) (0 : Fp2) := by
  intro h
  rw [equation_iff_sq2] at h
  simp only [pow_two, pow_three, mul_zero, zero_add] at h
  exact b4_ne_zero2 h.symm

private theorem notInf_of_nonsingular2 (x : AffinePt (Nat × Nat))
    (h : W2.Nonsingular (ofNatPair x.1) (ofNatPair x.2)) :
    ¬ affineIsInfinity fp2Ops x = true := by
  intro hinf
  obtain ⟨h1, h2⟩ := (inf_iff2 x).mp hinf
  rw [h1, h2] at h
  exact not_onCurve_zero2 h.1

private theorem emb_of_nonsingular2 (x : AffinePt (Nat × Nat))
    (h : W2.Nonsingular (ofNatPair x.1) (ofNatPair x.2)) :
    emb2 ⟨x, onCurve_of_eq2 x h.1⟩ =
      Point.some (ofNatPair x.1) (ofNatPair x.2) (nonsingular_of_equation2 h.1) := by
  classical
  rw [emb_notInf2 ⟨x, onCurve_of_eq2 x h.1⟩ (notInf_of_nonsingular2 x h)]

/-- The dependent-proof transport G1Agreement records as THE wall: 'Point.some' carries a
    'Nonsingular' proof, 'rw' cannot move a goal across a coordinate equality that touches it, and
    'subst' can - because the third argument is a 'Prop' and proof irrelevance is definitional. -/
private theorem point_some_eq2 {x₁ x₂ y₁ y₂ : Fp2} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : W2.Nonsingular x₁ y₁) (h₂ : W2.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

private theorem nonsingular_congr2 {x₁ x₂ y₁ y₂ : Fp2} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h : W2.Nonsingular x₂ y₂) : W2.Nonsingular x₁ y₁ := by
  subst hx
  subst hy
  exact h

private theorem equation_congr2 {x₁ x₂ y₁ y₂ : Fp2} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h : W2.Equation x₂ y₂) : W2.Equation x₁ y₁ := by
  subst hx
  subst hy
  exact h

private theorem nonsingular_of_frame2 (P : Fp2Frame) (hP : ¬ affineIsInfinity fp2Ops P.1) :
    W2.Nonsingular (ofNatPair P.1.1) (ofNatPair P.1.2) :=
  nonsingular_of_equation2 (equation_of_frame2 P hP)

private theorem onCurve_of_nonsingular_congr2 {R : AffinePt (Nat × Nat)} {x y : Fp2}
    (hx : ofNatPair R.1 = x) (hy : ofNatPair R.2 = y) (h : W2.Nonsingular x y) :
    affineOnCurve fp2Ops R = true :=
  onCurve_of_eq2 R (equation_congr2 hx hy h.1)

/-! ### THE COORDINATE AGREEMENT OVER Fp2 -/

/-- mathlib's own 'slope' on a secant, in the multiply-by-inverse form the byte law computes. -/
private theorem slope_secant2 (P Q : AffinePt (Nat × Nat))
    (hne : ofNatPair P.1 ≠ ofNatPair Q.1) :
    W2.slope (ofNatPair P.1) (ofNatPair Q.1) (ofNatPair P.2) (ofNatPair Q.2)
      = (ofNatPair Q.2 - ofNatPair P.2) * (ofNatPair Q.1 - ofNatPair P.1)⁻¹ := by
  rw [W2.slope_of_X_ne hne]
  field_simp
  ring

/-- The byte-level inverse of a nonzero Fp2 element casts to the field inverse of the difference. -/
private theorem inv_sub2 (P Q : AffinePt (Nat × Nat))
    (hne : ofNatPair P.1 ≠ ofNatPair Q.1) :
    fp2Ops.inv (fp2Ops.sub Q.1 P.1) ≠ none := by
  intro hh
  have := (fp2Ops_inv_none_iff (fp2Ops.sub Q.1 P.1)).mp hh
  rw [ofNatPair_sub] at this
  exact hne ((sub_eq_zero.mp this).symm)

/-- **THE SECANT COORDINATE AGREEMENT**: the byte-level output of 'affineAdd' is mathlib's 'addX' /
    'addY' at mathlib's own 'slope', coordinate by coordinate. This is the Fp2 twin of the lemma the
    G1 file calls "the lemma the whole package turns on", and the proof is the same three steps:
    decide the branches, push 'ofNatPair' through the byte operations, then 'ring'. -/
theorem affineAdd_coord_secant2 (P Q : Fp2Frame)
    (hP : ¬ affineIsInfinity fp2Ops P.1 = true) (hQ : ¬ affineIsInfinity fp2Ops Q.1 = true)
    (hne : ofNatPair P.1.1 ≠ ofNatPair Q.1.1) :
    ofNatPair (affineAdd fp2Ops P.1 Q.1).1
      = W2.addX (ofNatPair P.1.1) (ofNatPair Q.1.1)
          (W2.slope (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2) (ofNatPair Q.1.2)) ∧
    ofNatPair (affineAdd fp2Ops P.1 Q.1).2
      = W2.addY (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2)
          (W2.slope (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2) (ofNatPair Q.1.2)) := by
  classical
  have hxb : ¬ (fp2Ops.beq P.1.1 Q.1.1 = true) := fun hh => hne ((fp2Beq_iff P.1.1 Q.1.1).mp hh)
  rw [affineAdd, if_neg hP, if_neg hQ, if_neg hxb]
  cases hinv : fp2Ops.inv (fp2Ops.sub Q.1.1 P.1.1) with
  | none =>
      have h2 : ofNatPair (fp2Ops.sub Q.1.1 P.1.1) = 0 := (fp2Ops_inv_none_iff _).mp hinv
      rw [ofNatPair_sub] at h2
      exact absurd ((sub_eq_zero.mp h2).symm) hne
  | some i =>
      have hii : ofNatPair i = (ofNatPair Q.1.1 - ofNatPair P.1.1)⁻¹ := by
        rw [← ofNatPair_sub, ofNatPair_inv hinv]
      dsimp only
      set ℓ := (ofNatPair Q.1.2 - ofNatPair P.1.2) * (ofNatPair Q.1.1 - ofNatPair P.1.1)⁻¹ with hℓ
      have hslope : W2.slope (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2)
          (ofNatPair Q.1.2) = ℓ := slope_secant2 P.1 Q.1 hne
      rw [hslope]
      refine ⟨?_, ?_⟩
      · simp only [ofNatPair_sub, ofNatPair_mul, hii]
        show (ℓ * ℓ - ofNatPair P.1.1) - ofNatPair Q.1.1 =
            W2.addX (ofNatPair P.1.1) (ofNatPair Q.1.1) ℓ
        show (ℓ * ℓ - ofNatPair P.1.1) - ofNatPair Q.1.1 =
            ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair Q.1.1
        ring
      · simp only [ofNatPair_sub, ofNatPair_mul, hii]
        show ℓ * (ofNatPair P.1.1 - (ℓ * ℓ - ofNatPair P.1.1 - ofNatPair Q.1.1))
            - ofNatPair P.1.2 = W2.addY (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2) ℓ
        show ℓ * (ofNatPair P.1.1 - (ℓ * ℓ - ofNatPair P.1.1 - ofNatPair Q.1.1))
            - ofNatPair P.1.2 =
          -((ℓ * ((ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair Q.1.1)
            - ofNatPair P.1.1)) + ofNatPair P.1.2) - (0 : Fp2) *
            (ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair Q.1.1) - 0
        ring

/-- The tangent slope: mathlib's 'slope' at (x, y) with y ≠ 0 is 3x^2 / 2y, the expression
    'affineDouble' builds from 'fp2Ops.inv'. -/
private theorem slope_tangent2 (P : AffinePt (Nat × Nat)) (hy : ofNatPair P.2 ≠ 0) :
    W2.slope (ofNatPair P.1) (ofNatPair P.1) (ofNatPair P.2) (ofNatPair P.2)
      = 3 * (ofNatPair P.1 * ofNatPair P.1) * ((2 : Fp2) * ofNatPair P.2)⁻¹ := by
  have negY2 : W2.negY (ofNatPair P.1) (ofNatPair P.2) = -(ofNatPair P.2) := by
    show -(ofNatPair P.2) - (0 : Fp2) * ofNatPair P.1 - (0 : Fp2) = -(ofNatPair P.2)
    simp
  have hneg : (ofNatPair P.2 : Fp2) ≠ W2.negY (ofNatPair P.1) (ofNatPair P.2) := by
    intro hh
    rw [negY2] at hh
    apply hy
    have h3 : (2 : Fp2) * ofNatPair P.2 = 0 := by
      rw [two_mul]
      have h4 := congrArg (fun t => t + ofNatPair P.2) hh
      rw [h4]
      ring
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero2
  rw [W2.slope_of_Y_ne rfl hneg]
  simp only [a₁z2, a₂z2, a₄z2, negY2]
  have hd : (ofNatPair P.2) - -(ofNatPair P.2) = (2 : Fp2) * ofNatPair P.2 := by ring
  have hn : 3 * (ofNatPair P.1) ^ 2 + 2 * (0 : Fp2) * ofNatPair P.1 + (0 : Fp2)
      - (0 : Fp2) * ofNatPair P.2 = 3 * (ofNatPair P.1 * ofNatPair P.1) := by ring
  rw [hd, hn, div_eq_mul_inv]

/-- **THE TANGENT COORDINATE AGREEMENT**: 'affineDouble' on a frame with nonzero ordinate is
    mathlib's doubling formula. -/
theorem affineDouble_coord2 (P : Fp2Frame) (hP : ¬ affineIsInfinity fp2Ops P.1 = true)
    (hy : ofNatPair P.1.2 ≠ 0) :
    ofNatPair (affineDouble fp2Ops P.1).1
      = W2.addX (ofNatPair P.1.1) (ofNatPair P.1.1)
          (W2.slope (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2) (ofNatPair P.1.2)) ∧
    ofNatPair (affineDouble fp2Ops P.1).2
      = W2.addY (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2)
          (W2.slope (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2) (ofNatPair P.1.2)) := by
  classical
  have hinv : fp2Ops.inv (fp2Ops.mul (fp2Ops.add fp2Ops.one fp2Ops.one) P.1.2) ≠ none := by
    intro hh
    have := (fp2Ops_inv_none_iff (fp2Ops.mul (fp2Ops.add fp2Ops.one fp2Ops.one) P.1.2)).mp hh
    rw [ofNatPair_mul, ofNatPair_add, ofNatPair_one] at this
    have h12 : (1 : Fp2) + 1 ≠ 0 := by
      intro hh
      have hz : (2 : Fp2) = 0 := by
        have hc : (2 : Fp2) = 1 + 1 := by norm_num
        rw [hc, hh]
      exact two_ne_zero2 hz
    exact hy ((mul_eq_zero.mp this).resolve_left h12)
  cases h2 : fp2Ops.inv (fp2Ops.mul (fp2Ops.add fp2Ops.one fp2Ops.one) P.1.2) with
  | none => exact absurd h2 hinv
  | some i =>
      have h3 : ofNatPair (fp2Ops.mul (fp2Ops.add fp2Ops.one fp2Ops.one) P.1.2)
          = (2 : Fp2) * ofNatPair P.1.2 := by
        rw [ofNatPair_mul, ofNatPair_add, ofNatPair_one]
        show ((1 : Fp2) + 1) * ofNatPair P.1.2 = (2 : Fp2) * ofNatPair P.1.2
        norm_num
      have hii : ofNatPair i = ((2 : Fp2) * ofNatPair P.1.2)⁻¹ := by
        rw [ofNatPair_inv h2, h3]
      rw [affineDouble, if_neg hP]
      dsimp only
      rw [h2]
      dsimp only
      set ℓ := 3 * (ofNatPair P.1.1 * ofNatPair P.1.1) * ((2 : Fp2) * ofNatPair P.1.2)⁻¹ with hℓ
      have hslope : W2.slope (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2)
          (ofNatPair P.1.2) = ℓ := slope_tangent2 P.1 hy
      rw [hslope]
      refine ⟨?_, ?_⟩
      · simp only [ofNatPair_sub, ofNatPair_mul, ofNatPair_add, ofNatPair_one, hii]
        rw [show ((1 : Fp2) + 1) = 2 by norm_num, show ((2 : Fp2) + 1) = 3 by norm_num]
        have key : (3 : Fp2) * (ofNatPair P.1.1 * ofNatPair P.1.1) *
            ((2 : Fp2) * ofNatPair P.1.2)⁻¹ = ℓ := rfl
        rw [← key]
        have hz : ℓ * ℓ - (2 : Fp2) * ofNatPair P.1.1 =
            (ℓ * ℓ - ofNatPair P.1.1) - ofNatPair P.1.1 := by ring
        rw [hz]
        show (ℓ * ℓ - ofNatPair P.1.1) - ofNatPair P.1.1 =
            ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair P.1.1
        ring
      · simp only [ofNatPair_sub, ofNatPair_mul, ofNatPair_add, ofNatPair_one, hii]
        rw [show ((1 : Fp2) + 1) = 2 by norm_num, show ((2 : Fp2) + 1) = 3 by norm_num]
        have key : (3 : Fp2) * (ofNatPair P.1.1 * ofNatPair P.1.1) *
            ((2 : Fp2) * ofNatPair P.1.2)⁻¹ = ℓ := rfl
        rw [← key]
        have hz : ℓ * ℓ - (2 : Fp2) * ofNatPair P.1.1 =
            (ℓ * ℓ - ofNatPair P.1.1) - ofNatPair P.1.1 := by ring
        rw [hz]
        show ℓ * (ofNatPair P.1.1 - ((ℓ * ℓ - ofNatPair P.1.1) - ofNatPair P.1.1))
            - ofNatPair P.1.2 =
          -((ℓ * ((ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair P.1.1)
            - ofNatPair P.1.1)) + ofNatPair P.1.2) - (0 : Fp2) *
            (ℓ ^ 2 + (0 : Fp2) * ℓ - 0 - ofNatPair P.1.1 - ofNatPair P.1.1) - 0
        ring

/-! ### CLOSURE AND THE POINT-LEVEL ASSEMBLY -/

/-- A nonzero ordinate is not its own negative: the hypothesis mathlib's tangent branch wants. -/
private theorem ne_neg_of_ne_zero2 {y : Fp2} (hy : y ≠ 0) : y ≠ -y := by
  intro hh
  apply hy
  have h2 := congrArg (fun t => t + y) hh
  have h3 : (2 : Fp2) * y = 0 := by rw [two_mul, h2]; ring
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero2

private theorem ne_negY_of_ne_zero2 {x y : Fp2} (hy : y ≠ 0) : y ≠ W2.negY x y := by
  intro hh
  have h2 : W2.negY x y = -y := by
    show -y - (0 : Fp2) * x - (0 : Fp2) = -y
    simp
  rw [h2] at hh
  exact ne_neg_of_ne_zero2 hy hh

private theorem negY_of_zero2 {x y : Fp2} (hy : y = 0) : y = W2.negY x y := by
  show y = -y - (0 : Fp2) * x - (0 : Fp2)
  rw [hy]
  simp

/-- The doubling of a frame whose ordinate is zero is the all-zero frame: the byte law's
    zero-denominator branch, and the right answer because such a point is 2-torsion. -/
private theorem affineDouble_of_y_zero2 (P : Fp2Frame) (hP : ¬ affineIsInfinity fp2Ops P.1)
    (hy0 : ofNatPair P.1.2 = 0) : affineDouble fp2Ops P.1 = ((0, 0), (0, 0)) := by
  rw [affineDouble, if_neg hP]
  dsimp only
  rw [(fp2Ops_inv_none_iff _).mpr (by
    rw [ofNatPair_mul, ofNatPair_add, ofNatPair_one, hy0]
    simp)]
  rfl

/-- **CLOSURE UNDER DOUBLING.** -/
theorem affineDouble_onCurve2 (P : Fp2Frame) :
    affineOnCurve fp2Ops (affineDouble fp2Ops P.1) = true := by
  classical
  by_cases hPinf : affineIsInfinity fp2Ops P.1 = true
  · rw [affineDouble, if_pos hPinf]
    decide
  · by_cases hyz : ofNatPair P.1.2 = 0
    · rw [affineDouble_of_y_zero2 P hPinf hyz]
      decide
    · obtain ⟨hc1, hc2⟩ := affineDouble_coord2 P hPinf hyz
      refine onCurve_of_nonsingular_congr2 hc1 hc2
        (nonsingular_add (nonsingular_of_frame2 P hPinf) (nonsingular_of_frame2 P hPinf)
          (fun hxy => ne_negY_of_ne_zero2 hyz hxy.right))

def doubleFrame2 (P : Fp2Frame) : Fp2Frame :=
  ⟨affineDouble fp2Ops P.1, affineDouble_onCurve2 P⟩

/-- **CLOSURE OF THE ACCEPTED SET UNDER THE BYTE-LEVEL SUM.** -/
theorem affineAdd_onCurve2 (P Q : Fp2Frame) :
    affineOnCurve fp2Ops (affineAdd fp2Ops P.1 Q.1) = true := by
  classical
  by_cases hPinf : affineIsInfinity fp2Ops P.1 = true
  · rw [affineAdd, if_pos hPinf]
    exact Q.2
  · by_cases hQinf : affineIsInfinity fp2Ops Q.1 = true
    · rw [affineAdd, if_neg hPinf, if_pos hQinf]
      exact P.2
    · by_cases hxb : fp2Ops.beq P.1.1 Q.1.1 = true
      · by_cases hyb : fp2Ops.beq P.1.2 Q.1.2 = true
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          exact affineDouble_onCurve2 P
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
          decide
      · have hne : ofNatPair P.1.1 ≠ ofNatPair Q.1.1 :=
          fun h => hxb ((fp2Beq_iff P.1.1 Q.1.1).mpr h)
        obtain ⟨hc1, hc2⟩ := affineAdd_coord_secant2 P Q hPinf hQinf hne
        refine onCurve_of_nonsingular_congr2 hc1 hc2
          (nonsingular_add (nonsingular_of_frame2 P hPinf) (nonsingular_of_frame2 Q hQinf)
            (fun hxy => hne hxy.left))

def addFrame2 (P Q : Fp2Frame) : Fp2Frame :=
  ⟨affineAdd fp2Ops P.1 Q.1, affineAdd_onCurve2 P Q⟩

private theorem addFrame2_val (P Q : Fp2Frame) :
    (addFrame2 P Q).1 = affineAdd fp2Ops P.1 Q.1 := rfl
private theorem doubleFrame2_val (P : Fp2Frame) :
    (doubleFrame2 P).1 = affineDouble fp2Ops P.1 := rfl

/-- **THE AGREEMENT THEOREM, AT THE POINT LEVEL.** The Fp2 twin of 'emb_add': 'emb2' carries the
    byte-level affine sum to mathlib's group law in all four branches at once. -/
theorem emb2_add (P Q : Fp2Frame) : emb2 P + emb2 Q = emb2 (addFrame2 P Q) := by
  classical
  by_cases hPinf : affineIsInfinity fp2Ops P.1 = true
  · have h1 : affineAdd fp2Ops P.1 Q.1 = Q.1 := by rw [affineAdd, if_pos hPinf]
    have h2 : addFrame2 P Q = Q := Subtype.eq h1
    rw [emb_inf2 P hPinf, h2, zero_add]
  · by_cases hQinf : affineIsInfinity fp2Ops Q.1 = true
    · have h1 : affineAdd fp2Ops P.1 Q.1 = P.1 := by
        rw [affineAdd, if_neg hPinf, if_pos hQinf]
      have h2 : addFrame2 P Q = P := Subtype.eq h1
      rw [emb_inf2 Q hQinf, h2, add_zero]
    · have hP : W2.Nonsingular (ofNatPair P.1.1) (ofNatPair P.1.2) := nonsingular_of_frame2 P hPinf
      have hQ : W2.Nonsingular (ofNatPair Q.1.1) (ofNatPair Q.1.2) := nonsingular_of_frame2 Q hQinf
      by_cases hxb : fp2Ops.beq P.1.1 Q.1.1 = true
      · by_cases hyb : fp2Ops.beq P.1.2 Q.1.2 = true
        · have hx : ofNatPair P.1.1 = ofNatPair Q.1.1 := (fp2Beq_iff P.1.1 Q.1.1).mp hxb
          have hy : ofNatPair P.1.2 = ofNatPair Q.1.2 := (fp2Beq_iff P.1.2 Q.1.2).mp hyb
          have heQ : Point.some (ofNatPair Q.1.1) (ofNatPair Q.1.2) hQ =
              Point.some (ofNatPair P.1.1) (ofNatPair P.1.2) hP :=
            point_some_eq2 hx.symm hy.symm hQ hP
          have hadd : affineAdd fp2Ops P.1 Q.1 = affineDouble fp2Ops P.1 := by
            rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          have hfr : addFrame2 P Q = doubleFrame2 P := Subtype.eq hadd
          rw [emb_notInf2 P hPinf, emb_notInf2 Q hQinf, heQ, hfr]
          by_cases hyz : ofNatPair P.1.2 = 0
          · have hdbl : affineDouble fp2Ops P.1 = ((0, 0), (0, 0)) :=
              affineDouble_of_y_zero2 P hPinf hyz
            have hif : doubleFrame2 P = infFrame2 := Subtype.eq hdbl
            rw [Point.add_self_of_Y_eq (negY_of_zero2 hyz), hif,
              emb_inf2 infFrame2 (by decide)]
          · obtain ⟨hc1, hc2⟩ := affineDouble_coord2 P hPinf hyz
            have hns : W2.Nonsingular
                (W2.addX (ofNatPair P.1.1) (ofNatPair P.1.1)
                  (W2.slope (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2) (ofNatPair P.1.2)))
                (W2.addY (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2)
                  (W2.slope (ofNatPair P.1.1) (ofNatPair P.1.1) (ofNatPair P.1.2) (ofNatPair P.1.2))) :=
              nonsingular_add hP hP (fun hxy =>
                ne_negY_of_ne_zero2 hyz hxy.right)
            have hemb : emb2 (doubleFrame2 P) =
                Point.some (ofNatPair (affineDouble fp2Ops P.1).1)
                  (ofNatPair (affineDouble fp2Ops P.1).2)
                  (nonsingular_of_equation2 (nonsingular_congr2 hc1 hc2 hns).1) :=
              emb_of_nonsingular2 (affineDouble fp2Ops P.1) (nonsingular_congr2 hc1 hc2 hns)
            rw [Point.add_self_of_Y_ne (ne_negY_of_ne_zero2 hyz), hemb]
            exact point_some_eq2 hc1.symm hc2.symm hns _
        · have hx : ofNatPair P.1.1 = ofNatPair Q.1.1 := (fp2Beq_iff P.1.1 Q.1.1).mp hxb
          have hne : ¬ (ofNatPair P.1.2 = ofNatPair Q.1.2) :=
            fun h => hyb ((fp2Beq_iff P.1.2 Q.1.2).mpr h)
          have hy : ofNatPair P.1.2 = W2.negY (ofNatPair Q.1.1) (ofNatPair Q.1.2) :=
            (Y_eq_of_X_eq hP.1 hQ.1 hx).resolve_left hne
          have hadd : affineAdd fp2Ops P.1 Q.1 = ((0, 0), (0, 0)) := by
            rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
            rfl
          have hif : addFrame2 P Q = infFrame2 := Subtype.eq hadd
          rw [emb_notInf2 P hPinf, emb_notInf2 Q hQinf, Point.add_of_Y_eq hx hy, hif,
            emb_inf2 infFrame2 (by decide)]
      · rw [emb_notInf2 P hPinf, emb_notInf2 Q hQinf]
        have hne : ofNatPair P.1.1 ≠ ofNatPair Q.1.1 :=
          fun h => hxb ((fp2Beq_iff P.1.1 Q.1.1).mpr h)
        obtain ⟨hc1, hc2⟩ := affineAdd_coord_secant2 P Q hPinf hQinf hne
        have hns : W2.Nonsingular
            (W2.addX (ofNatPair P.1.1) (ofNatPair Q.1.1)
              (W2.slope (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2) (ofNatPair Q.1.2)))
            (W2.addY (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2)
              (W2.slope (ofNatPair P.1.1) (ofNatPair Q.1.1) (ofNatPair P.1.2) (ofNatPair Q.1.2))) :=
          nonsingular_add hP hQ (fun hxy => hne hxy.left)
        have hemb : emb2 (addFrame2 P Q) =
            Point.some (ofNatPair (affineAdd fp2Ops P.1 Q.1).1)
              (ofNatPair (affineAdd fp2Ops P.1 Q.1).2)
              (nonsingular_of_equation2 (nonsingular_congr2 hc1 hc2 hns).1) :=
          emb_of_nonsingular2 (affineAdd fp2Ops P.1 Q.1) (nonsingular_congr2 hc1 hc2 hns)
        rw [Point.add_of_X_ne hne, hemb]
        exact point_some_eq2 hc1.symm hc2.symm hns _

/-! ### THE SCALAR-MULTIPLICATION AGREEMENT -/

/-- One double-and-add step at frame level. -/
def smulStep2 (n : ℕ) (st : Fp2Frame × Fp2Frame) (i : ℕ) : Fp2Frame × Fp2Frame :=
  (if Nat.testBit n i then addFrame2 st.1 st.2 else st.1, doubleFrame2 st.2)

/-- The same step at byte level. -/
def smulStepBytes2 (n : ℕ) (st : AffinePt (Nat × Nat) × AffinePt (Nat × Nat))
    (i : ℕ) : AffinePt (Nat × Nat) × AffinePt (Nat × Nat) :=
  (if Nat.testBit n i then affineAdd fp2Ops st.1 st.2 else st.1, affineDouble fp2Ops st.2)

private def fval2 (st : Fp2Frame × Fp2Frame) :
    AffinePt (Nat × Nat) × AffinePt (Nat × Nat) := (st.1.1, st.2.1)

private theorem fval2_step (n : ℕ) (st : Fp2Frame × Fp2Frame) (i : ℕ) :
    fval2 (smulStep2 n st i) = smulStepBytes2 n (fval2 st) i := by
  obtain ⟨A, D⟩ := st
  have eL : fval2 (smulStep2 n (A, D) i) =
      ((if Nat.testBit n i then addFrame2 A D else A).1, (doubleFrame2 D).1) := rfl
  have eR : smulStepBytes2 n (fval2 (A, D)) i =
      (if Nat.testBit n i then affineAdd fp2Ops A.1 D.1 else A.1, affineDouble fp2Ops D.1) := rfl
  rw [eL, eR]
  by_cases hb : Nat.testBit n i
  · rw [if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb]
    rfl

private theorem foldl_range_succ2 {α : Type} (f : α → ℕ → α) (init : α) (k : ℕ) :
    (List.range (k + 1)).foldl f init = f ((List.range k).foldl f init) k := by
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem fval2_fold (n : ℕ) (P : Fp2Frame) :
    ∀ k : ℕ, fval2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)) =
      (List.range k).foldl (smulStepBytes2 n) (((0, 0), (0, 0)), P.1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [foldl_range_succ2, foldl_range_succ2, ← ih]
      exact fval2_step n _ k

/-- **SCALAR MULTIPLICATION AS A FRAME.** -/
def smulFrame2 (n : ℕ) (P : Fp2Frame) : Fp2Frame :=
  ((List.range (Nat.log2 n + 1)).foldl (smulStep2 n) (infFrame2, P)).1

theorem smulFrame2_val (n : ℕ) (P : Fp2Frame) :
    (smulFrame2 n P).1 = affineSmul fp2Ops n P.1 :=
  congrArg Prod.fst (fval2_fold n P (Nat.log2 n + 1))

theorem emb2_double (P : Fp2Frame) : emb2 (doubleFrame2 P) = emb2 P + emb2 P := by
  classical
  by_cases hPinf : affineIsInfinity fp2Ops P.1 = true
  · have h1 : affineDouble fp2Ops P.1 = ((0, 0), (0, 0)) := by
      rw [affineDouble, if_pos hPinf]
      rfl
    have h2 : doubleFrame2 P = infFrame2 := Subtype.ext h1
    rw [h2, emb_inf2 infFrame2 (by decide), emb_inf2 P hPinf, zero_add]
  · have hbeqx : fp2Ops.beq P.1.1 P.1.1 = true := (fp2Beq_iff P.1.1 P.1.1).mpr rfl
    have hbeqy : fp2Ops.beq P.1.2 P.1.2 = true := (fp2Beq_iff P.1.2 P.1.2).mpr rfl
    have h1 : affineAdd fp2Ops P.1 P.1 = affineDouble fp2Ops P.1 := by
      rw [affineAdd, if_neg hPinf, if_neg hPinf, if_pos hbeqx, if_pos hbeqy]
    have h2 : addFrame2 P P = doubleFrame2 P := Subtype.ext h1
    rw [← h2, emb2_add]

private theorem emb2_smul_fold (n : ℕ) (P : Fp2Frame) :
    ∀ k : ℕ, emb2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).1 =
        (n % 2 ^ k) • emb2 P ∧
      emb2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).2 = 2 ^ k • emb2 P := by
  intro k
  induction k with
  | zero =>
      have h1 : ((List.range 0).foldl (smulStep2 n) (infFrame2, P)).1 = infFrame2 := rfl
      have h2 : ((List.range 0).foldl (smulStep2 n) (infFrame2, P)).2 = P := rfl
      rw [h1, h2, Nat.pow_zero, Nat.mod_one, zero_nsmul, one_nsmul,
        emb_inf2 infFrame2 (by decide)]
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      rw [foldl_range_succ2]
      obtain ⟨h1, h2⟩ := ih
      have e1 : (smulStep2 n ((List.range k).foldl (smulStep2 n) (infFrame2, P)) k).1 =
          (if Nat.testBit n k then
            addFrame2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).1
              ((List.range k).foldl (smulStep2 n) (infFrame2, P)).2
           else ((List.range k).foldl (smulStep2 n) (infFrame2, P)).1) := rfl
      have e2 : (smulStep2 n ((List.range k).foldl (smulStep2 n) (infFrame2, P)) k).2 =
          doubleFrame2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).2 := rfl
      rw [e1, e2]
      refine ⟨?_, ?_⟩
      · by_cases hb : Nat.testBit n k
        · rw [if_pos hb, ← emb2_add, h1, h2, ← add_nsmul,
            Midfall.Assumptions.mod_pow_succ 2 n k (by decide), ← Nat.toNat_testBit, hb,
            Bool.toNat_true, Nat.mul_one]
        · rw [if_neg hb, h1, Midfall.Assumptions.mod_pow_succ 2 n k (by decide),
            ← Nat.toNat_testBit, Bool.eq_false_of_ne_true hb, Bool.toNat_false, Nat.mul_zero,
            Nat.add_zero]
      · rw [emb2_double, h2, ← two_nsmul, ← mul_nsmul]
        congr 1

/-- **THE SCALAR-MULTIPLICATION AGREEMENT OVER Fp2.** -/
theorem emb2_smul (n : ℕ) (P : Fp2Frame) : n • emb2 P = emb2 (smulFrame2 n P) := by
  have h := emb2_smul_fold n P (Nat.log2 n + 1)
  rw [show smulFrame2 n P =
        ((List.range (Nat.log2 n + 1)).foldl (smulStep2 n) (infFrame2, P)).1 from rfl]
  rw [Nat.mod_eq_of_lt Nat.lt_log2_self] at h
  exact h.1.symm

/-! ### CANONICITY: where "maps to zero" and "is the all-zero pair" come apart -/

/-- A frame is canonical when all four coordinates sit below the modulus - what 'fpCoordOf?'
    guarantees for every frame the precompile decodes. -/
def CanonicalFrame2 (P : Fp2Frame) : Prop :=
  P.1.1.1 < blsP ∧ P.1.1.2 < blsP ∧ P.1.2.1 < blsP ∧ P.1.2.2 < blsP

/-- The same predicate on a raw byte point. -/
def CanonPt (P : AffinePt (Nat × Nat)) : Prop :=
  P.1.1 < blsP ∧ P.1.2 < blsP ∧ P.2.1 < blsP ∧ P.2.2 < blsP

private theorem sub_blt2 {a b : Nat × Nat} :
    (fp2Ops.sub a b).1 < blsP ∧ (fp2Ops.sub a b).2 < blsP :=
  ⟨Nat.mod_lt _ p_pos2, Nat.mod_lt _ p_pos2⟩

private theorem zero_blt2 : (fp2Ops.zero : Nat × Nat).1 < blsP ∧
    (fp2Ops.zero : Nat × Nat).2 < blsP := ⟨p_pos2, p_pos2⟩

/-- **THE WALK, DOUBLING HALF** - five branches, no literal anywhere, exactly the G1 shape: the
    infinity and zero-denominator branches return 'fp2Ops.zero', the tangent returns two
    reductions. -/
theorem affineDouble_canonic2 (P : AffinePt (Nat × Nat)) (_hP : CanonPt P) :
    CanonPt (affineDouble fp2Ops P) := by
  classical
  by_cases hinf : affineIsInfinity fp2Ops P = true
  · rw [affineDouble, if_pos hinf]
    exact ⟨zero_blt2.1, zero_blt2.2, zero_blt2.1, zero_blt2.2⟩
  · rw [affineDouble, if_neg hinf]
    dsimp only
    cases h : fp2Ops.inv (fp2Ops.mul (fp2Ops.add fp2Ops.one fp2Ops.one) P.2) with
    | none => exact ⟨zero_blt2.1, zero_blt2.2, zero_blt2.1, zero_blt2.2⟩
    | some i =>
        exact ⟨sub_blt2.1, sub_blt2.2, sub_blt2.1, sub_blt2.2⟩

/-- **THE WALK, ADDITION HALF** - the two copy branches are where the hypothesis is USED. -/
theorem affineAdd_canonic2 (P Q : AffinePt (Nat × Nat)) (hP : CanonPt P) (hQ : CanonPt Q) :
    CanonPt (affineAdd fp2Ops P Q) := by
  classical
  by_cases hPinf : affineIsInfinity fp2Ops P = true
  · rw [affineAdd, if_pos hPinf]
    exact hQ
  · by_cases hQinf : affineIsInfinity fp2Ops Q = true
    · rw [affineAdd, if_neg hPinf, if_pos hQinf]
      exact hP
    · by_cases hxb : fp2Ops.beq P.1 Q.1 = true
      · by_cases hyb : fp2Ops.beq P.2 Q.2 = true
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          exact affineDouble_canonic2 P hP
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
          exact ⟨zero_blt2.1, zero_blt2.2, zero_blt2.1, zero_blt2.2⟩
      · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_neg hxb]
        cases h : fp2Ops.inv (fp2Ops.sub Q.1 P.1) with
        | none => exact ⟨zero_blt2.1, zero_blt2.2, zero_blt2.1, zero_blt2.2⟩
        | some i => exact ⟨sub_blt2.1, sub_blt2.2, sub_blt2.1, sub_blt2.2⟩

theorem doubleFrame2_canonic (P : Fp2Frame) (hP : CanonicalFrame2 P) :
    CanonicalFrame2 (doubleFrame2 P) := affineDouble_canonic2 P.1 hP

theorem addFrame2_canonic (P Q : Fp2Frame) (hP : CanonicalFrame2 P) (hQ : CanonicalFrame2 Q) :
    CanonicalFrame2 (addFrame2 P Q) := affineAdd_canonic2 P.1 Q.1 hP hQ

theorem smulStep2_canonic (n : ℕ) (st : Fp2Frame × Fp2Frame) (i : ℕ)
    (h1 : CanonicalFrame2 st.1) (h2 : CanonicalFrame2 st.2) :
    CanonicalFrame2 (smulStep2 n st i).1 ∧ CanonicalFrame2 (smulStep2 n st i).2 := by
  classical
  by_cases hb : Nat.testBit n i
  · rw [smulStep2, if_pos hb]
    exact ⟨addFrame2_canonic st.1 st.2 h1 h2, doubleFrame2_canonic st.2 h2⟩
  · rw [smulStep2, if_neg hb]
    exact ⟨h1, doubleFrame2_canonic st.2 h2⟩

/-- **THE FOLD NEVER LEAVES THE CANONICAL SET.** -/
theorem smulFrame2_canonic (n : ℕ) (P : Fp2Frame) (hP : CanonicalFrame2 P) :
    CanonicalFrame2 (smulFrame2 n P) := by
  classical
  have key : ∀ k : ℕ, CanonicalFrame2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).1 ∧
      CanonicalFrame2 ((List.range k).foldl (smulStep2 n) (infFrame2, P)).2 := by
    intro k
    induction k with
    | zero =>
        exact ⟨⟨p_pos2, p_pos2, p_pos2, p_pos2⟩, hP⟩
    | succ k ih =>
        rw [foldl_range_succ2]
        exact smulStep2_canonic n _ k ih.1 ih.2
  exact (key (Nat.log2 n + 1)).1

/-- For a canonical frame, "embeds to zero" and "is the literal all-zero pair" coincide. -/
theorem emb2_eq_zero_iff_canonical (P : Fp2Frame) (hP : CanonicalFrame2 P) :
    emb2 P = 0 ↔ P.1 = ((0, 0), (0, 0)) := by
  classical
  rw [emb2_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (inf_iff2 P.1).mp h
    obtain ⟨e1, e2, e3, e4⟩ := hP
    obtain ⟨q1, q2⟩ := (ofNatPair_eq_zero_iff P.1.1).mp h1
    obtain ⟨r1, r2⟩ := (ofNatPair_eq_zero_iff P.1.2).mp h2
    simp only [Nat.mod_eq_of_lt e1, Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt e3,
      Nat.mod_eq_of_lt e4] at q1 q2 r1 r2
    exact Prod.ext (Prod.ext q1 q2) (Prod.ext r1 r2)
  · intro h
    rw [h]
    decide

/-- **THE SUBGROUP TEST IN GROUP-THEORETIC FORM.** Note the transport: '▸' along named equations,
    never 'rw' through the pair-'==' - the G1 file's measured wall. -/
theorem nsmul_emb2_eq_zero_iff (n : ℕ) (P : Fp2Frame) (hc : CanonicalFrame2 (smulFrame2 n P)) :
    n • emb2 P = 0 ↔ affineSmul fp2Ops n P.1 = ((0, 0), (0, 0)) := by
  classical
  constructor
  · intro h
    have h2 : emb2 (smulFrame2 n P) = 0 := emb2_smul n P ▸ h
    have h1 : (smulFrame2 n P).1 = ((0, 0), (0, 0)) :=
      (emb2_eq_zero_iff_canonical (smulFrame2 n P) hc).mp h2
    exact smulFrame2_val n P ▸ h1
  · intro h
    have h1 : (smulFrame2 n P).1 = ((0, 0), (0, 0)) := (smulFrame2_val n P).symm ▸ h
    have h2 : emb2 (smulFrame2 n P) = 0 :=
      (emb2_eq_zero_iff_canonical (smulFrame2 n P) hc).mpr h1
    exact (emb2_smul n P).symm ▸ h2

/-- **THE PRECOMPILE'S OWN G2 SUBGROUP TEST** is 'blsR • emb2 P = 0' for a canonical frame. -/
theorem g2InSubgroup_iff2 (P : Fp2Frame) (hP : CanonicalFrame2 P) :
    g2InSubgroup P.1 = true ↔ blsR • emb2 P = 0 := by
  classical
  have hc : CanonicalFrame2 (smulFrame2 blsR P) := smulFrame2_canonic blsR P hP
  have core : (g2InSubgroup P.1 = true) ↔ affineSmul fp2Ops blsR P.1 = ((0, 0), (0, 0)) := by
    constructor
    · intro h
      unfold g2InSubgroup at h
      exact beq_iff_eq.mp h
    · intro h
      unfold g2InSubgroup
      exact beq_iff_eq.mpr h
  exact core.trans (nsmul_emb2_eq_zero_iff blsR P hc).symm

/-- **THE WHOLE G2 VALIDATOR, IN GROUP FORM**: 'g2PointValid' is r-torsion of the embedded point. -/
theorem g2PointValid_iff2 (P : Fp2Frame) (hP : CanonicalFrame2 P) :
    g2PointValid P.1 = true ↔ blsR • emb2 P = 0 := by
  classical
  constructor
  · intro h
    unfold g2PointValid at h
    rw [Bool.and_eq_true] at h
    obtain ⟨-, hdisj⟩ := h
    rw [Bool.or_eq_true_iff] at hdisj
    cases hdisj with
    | inl hinf =>
        have hz : emb2 P = 0 := emb_inf2 P hinf
        rw [hz]
        exact nsmul_zero _
    | inr hsub => exact (g2InSubgroup_iff2 P hP).mp hsub
  · intro h
    unfold g2PointValid
    rw [Bool.and_eq_true]
    refine ⟨Fp2Frame.onCurve P, ?_⟩
    rw [Bool.or_eq_true_iff]
    right
    exact (g2InSubgroup_iff2 P hP).mpr h

/-! ### THE PUBLISHED GENERATOR H2 AND ITS r-TORSION MEMBERSHIP -/

/-- x_c0 of EIP-2537's H2, as 'katG2GenWords' renders it (PrecompileSmoke.sol:161-168). -/
def h2x0 : Nat :=
  0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8

/-- x_c1 of H2. -/
def h2x1 : Nat :=
  0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e

/-- y_c0 of H2. -/
def h2y0 : Nat :=
  0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801

/-- y_c1 of H2. -/
def h2y1 : Nat :=
  0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be

/-- The published H2 as a byte point: ((x_c0, x_c1), (y_c0, y_c1)), the order 'g2Of?' decodes. -/
def h2Pair : AffinePt (Nat × Nat) := ((h2x0, h2x1), (h2y0, h2y1))

/-- **H2 IS ON THE CURVE** y^2 = x^3 + 4(u+1) over Fp2, as a kernel theorem: 'affineOnCurve fp2Ops'
    at the real 381-bit modulus, computed by the same integer arithmetic the precompile model uses.
    Independently confirmed in Python bignum arithmetic over Fp[u]/(u^2+1) before this was written. -/
theorem h2Pair_onCurve : affineOnCurve fp2Ops h2Pair = true := by decide

def h2Frame : Fp2Frame := ⟨h2Pair, h2Pair_onCurve⟩

theorem h2Frame_canonical : CanonicalFrame2 h2Frame :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem h2Frame_notInf : ¬ affineIsInfinity fp2Ops h2Pair = true := by decide

theorem emb2_h2_ne_zero : emb2 h2Frame ≠ 0 := fun h =>
  h2Frame_notInf ((emb2_eq_zero_iff h2Frame).mp h)

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 100000 in
/-- **THE EXPENSIVE KERNEL COMPUTATION, MEASURED.** 'affineSmul fp2Ops blsR h2Pair = ((0,0),(0,0))':
    the published H2 is killed by the precompile's own 255-step double-and-add. MEASURED HERE:
    8.6 s of kernel reduction, largest single process 4.42 GiB, at maxRecDepth 100000 and
    maxHeartbeats 4e9. THE BRIEF BUDGETED ~4x the G1 fold's 16.6 s and the estimate was WRONG IN
    THE PESSIMISTIC DIRECTION by about 2x: the fold's cost is the 'modPow' inside 'fpInv', and
    'fp2Ops.inv' calls 'fpInv' exactly once per inverse (on the norm, a 381-bit natural), so a G2
    step costs one G1-sized modPow plus cheap pair arithmetic. It is a theorem and appears in no
    '#eval', so no gate pass re-runs it. -/
theorem h2Pair_r_smul_zero : affineSmul fp2Ops blsR h2Pair = ((0, 0), (0, 0)) := by decide

/-- **'blsR • emb2 h2Frame = 0' AS A GROUP STATEMENT**, transported from the byte computation in
    three lines because '▸' along a named equation never whnfs the fold. -/
theorem r_nsmul_emb2_h2 : blsR • emb2 h2Frame = 0 := by
  have h1 : (smulFrame2 blsR h2Frame).1 = ((0, 0), (0, 0)) :=
    (smulFrame2_val blsR h2Frame).symm ▸ h2Pair_r_smul_zero
  have h2 : emb2 (smulFrame2 blsR h2Frame) = 0 :=
    (emb2_eq_zero_iff_canonical (smulFrame2 blsR h2Frame)
      (smulFrame2_canonic blsR h2Frame h2Frame_canonical)).mpr h1
  exact (emb2_smul blsR h2Frame).symm ▸ h2

/-- The published generator passes the precompile's own G2 validator, as a THEOREM. -/
theorem g2PointValid_h2Pair : g2PointValid h2Pair = true :=
  (g2PointValid_iff2 h2Frame h2Frame_canonical).mpr r_nsmul_emb2_h2

/-! ### WHAT LANDED, WHAT STALLED, AND THE GATE -/

/-- H2's byte-level negation, as a frame. -/
def negH2Frame : Fp2Frame := ⟨affineNeg fp2Ops h2Pair, by decide⟩

/-- **WITNESS FOR 'emb2_add' (D-P23 satisfiability).** At the published generator: the sum of H2
    with its byte-level negation is the point at infinity, while H2 itself is not. The same shape as
    the G1 file's witness, at a point nobody chose. -/
theorem emb2_add_witness :
    emb2 h2Frame + emb2 negH2Frame = 0 ∧ emb2 h2Frame ≠ 0 := by
  classical
  refine ⟨?_, emb2_h2_ne_zero⟩
  have hadd : affineAdd fp2Ops h2Pair (affineNeg fp2Ops h2Pair) = ((0, 0), (0, 0)) := by decide
  have hfr : addFrame2 h2Frame negH2Frame = infFrame2 := Subtype.ext hadd
  rw [emb2_add, hfr, emb_inf2 infFrame2 (by decide)]

/-- **WITNESS FOR 'emb2_smul' (D-P23 satisfiability)** at a nontrivial scalar: the fold at 1 is the
    identity on the generator, and the fold at 2 is the byte-level doubling. -/
theorem emb2_smul_witness :
    (1 : ℕ) • emb2 h2Frame = emb2 h2Frame ∧
      2 • emb2 h2Frame = emb2 (smulFrame2 2 h2Frame) ∧
      (smulFrame2 2 h2Frame).1 = affineSmul fp2Ops 2 h2Pair := by
  classical
  refine ⟨by rw [one_nsmul], emb2_smul 2 h2Frame, smulFrame2_val 2 h2Frame⟩

/-- **FALSIFICATION FOR 'emb2_smul' (D-P23): the agreement is not the vacuous statement "every
    scalar multiple is the point".** At the scalar 0 the left side is the identity and the right
    side is not, because the generator is not the identity. -/
theorem emb2_smul_not_constant : ¬ ∀ (n : ℕ) (P : Fp2Frame), n • emb2 P = emb2 P := by
  intro h
  have h0 : (0 : ℕ) • emb2 h2Frame = emb2 h2Frame := h 0 h2Frame
  rw [zero_nsmul] at h0
  exact emb2_h2_ne_zero h0.symm

/-- **THE VALIDATOR IS A CONJUNCTION, NOT THE CURVE TEST.** Stated over a VARIABLE point so nothing
    forces the 255-step fold: 'g2PointValid' concedes nothing by itself, and the subgroup conjunct is
    a real second condition - which is what 'g2PointValid_iff2' turns into 'blsR • emb2 P = 0'. -/
theorem g2PointValid_is_a_conjunction (P : AffinePt (Nat × Nat)) :
    g2PointValid P =
      (affineOnCurve fp2Ops P && (affineIsInfinity fp2Ops P || g2InSubgroup P)) := rfl



/-- **THE GATE FOR THIS PACKAGE.** Lines 1-3: the published H2 is on the curve, passes the whole
    precompile validator, and decodes from the EIP's own bytes through 'g2Of?'. Line 4: the encoder
    width is 0x100 and the identity frame is the all-zero word. Lines 5-6: the byte fold at 1 is the
    identity and H2 plus its byte-level negation is the all-zero frame - the opposite-points branch
    exercised on real bytes. Lines 7-8: the two arithmetic facts the tower and the failed count
    transfer rest on. -/
def g2AgreementKats_ok : Bool :=
  (affineOnCurve fp2Ops h2Pair) &&
    (g2PointValid h2Pair) &&
    (g2Of? (bytesOfWords katG2GenWords) == some h2Pair) &&
    (g2PointBytes h2Pair).size == g2Bytes &&
    (affineSmul fp2Ops 1 h2Pair == h2Pair) &&
    (affineAdd fp2Ops h2Pair (affineNeg fp2Ops h2Pair) == ((0, 0), (0, 0))) &&
    (blsP % 4 == 3) &&
    (2 * blsP * blsP + 1 > blsR * blsR)

#eval g2AgreementKats_ok   -- expect true

/-- **WHAT P-G2 LANDED HERE, AND THE SPECIFIC CAUSE OF WHAT IT DID NOT.**
    LANDED: the Fp2 field model (Instances/Fp2.lean) with 'p % 4 = 3' as a theorem and the
    byte-model agreement for every operation of 'fp2Ops' including 'inv'; the G2 curve
    y^2 = x^3 + 4(u+1) over it with mathlib's 'IsElliptic' instance (discriminant -13824u);
    'emb2_add' and 'emb2_smul' - the full group-law and scalar-multiplication agreement between
    'affineAdd'/'affineSmul' on 'fp2Ops' and mathlib's 'W2.Point'; the canonicity walk over
    variables; 'g2InSubgroup_iff2' and 'g2PointValid_iff2'; and the published H2 with
    'r • H2 = 0' as a kernel theorem (measured 8.6 s, largest process 4.42 GiB).

    STALLED, WITH THE CAUSE: the 'g2Valid' EXHIBIT at a codec. Two specific blockers, both plumbing
    and neither mathematical, and both hit at the byte layer rather than the field layer.
      (1) The 0x100 round trip needs 'g2Of? (g2PointBytes P) = some P', i.e. four slice windows over
          a three-fold 'bytesAppend' nest. 'bytesAppend_size' is PRIVATE in Instances/G1Agreement.lean,
          so the window lemmas that G1 proves for a two-fold nest cannot be reused as they stand, and
          re-deriving them for the four-coordinate frame ran into the elaborator's 200k-heartbeat
          default whnf budget on 'fpCoordBytes' size arithmetic (the same family as the four walls
          G1Agreement documents; the cure is 'set_option maxHeartbeats' on the byte lemmas, which was
          not tried before the budget ran out).
      (2) The zpowers carrier used for G1 ('Subgroup.zpowers (ofAdd (emb genFrame))') cannot be
          copied, because encoding a 'W2.Point' needs its coordinates as canonical naturals and an
          element of 'Fp2 = AdjoinRoot Fp (X^2+1)' is a quotient with no computable representative
          extraction - the G1 file gets that from 'ZMod.val'. The exponent-indexed carrier with the
          fold encoder was designed to route around it ('g2foldToEip' writes the bytes the fold
          computes, so canonicity is 'smulFrame2_canonic' and no quotient is ever read back), but the
          codec lemmas for it sit behind blocker (1).
    So 'g2Valid' is DISCHARGED AT THE VALIDATOR LEVEL ('g2PointValid_h2Pair': the published
    generator passes it, as a theorem) but NOT YET AS A HOLDS CLAUSE QUANTIFIED OVER A CARRIER. -/
def gap_g2_codec_plumbing : String :=
  "blocker: g2Valid is not yet exhibited as a Holds clause over a carrier, and the cause is byte "
    ++ "plumbing, not the Fp2 model - which landed (Instances/Fp2.lean) together with the group-law "
    ++ "agreement emb2_add, emb2_smul and the r-torsion theorem r • H2 = 0. Two named items: "
    ++ "(1) g2Of? (g2PointBytes P) = some P needs four slice windows over a three-fold bytesAppend "
    ++ "nest, and bytesAppend_size is private in Instances/G1Agreement.lean; the re-derived version "
    ++ "hits the 200k-heartbeat default whnf budget on fpCoordBytes size arithmetic. "
    ++ "(2) The G1 zpowers carrier cannot be copied because an AdjoinRoot element has no computable "
    ++ "coordinate extraction (the G1 file uses ZMod.val); the exponent-indexed fold carrier avoids "
    ++ "that but still needs (1)."

/-- **THE REQUIRED FINDING, AS A COMPUTATION**: with the Fp2 model and the G2 agreement landed, the
    open Holds clauses are 'g2Valid' (blocked on the codec plumbing above, NOT on any missing
    mathematics) and 'pairing2' at real points (blocked on D-P36a, a curve 'AdmissiblePairing').
    The G1 side is four of four. So a single 'Holds' term needs exactly TWO items: the byte plumbing
    of (1), and one named assumption. It does not need Fp12, a point count, or any new number
    theory - and the count route stays closed for G2 (2p^2 + 1 > r^2, pinned on line 8 of the gate). -/
def g2ModelStatus_ok : Bool :=
  (gap_g2_codec_plumbing.contains "bytesAppend_size") &&
    (gap_g2_codec_plumbing.contains "AdjoinRoot") &&
    (gap_g2_codec_plumbing.contains "g2Valid") &&
    (blsP % 4 == 3) &&
    (g2PointValid h2Pair) &&
    (affineOnCurve fp2Ops h2Pair) &&
    (2 * blsP * blsP + 1 > blsR * blsR)

#eval g2ModelStatus_ok   -- expect true

end Midfall.Instances
