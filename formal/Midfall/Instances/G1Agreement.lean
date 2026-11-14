-- |
-- Midfall.Instances.G1Agreement
--
-- P-MODEXP step 2: THE AGREEMENT THEOREM between the byte-level affine group law of
-- Midfall/Yul/Externals.lean (`affineAdd` / `affineDouble` / `affineSmul` over integer residues)
-- and mathlib's elliptic-curve group law (`WeierstrassCurve.Affine.Point.add`, proved at
-- AlgebraicGeometry/EllipticCurve/Affine/Point.lean:805) at the REAL base modulus. This is the
-- wall P-HOLDS2 named for `g1Add`, `g1Msm1` and the subgroup half of `g1Valid`.
--
-- WHAT THE BRIEF GOT WRONG, TWICE. (1) The short-form literal is
--   `{ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }` with UNICODE SUBSCRIPT field names; the
--   brief's `a1 := 0` does not elaborate (measured: "a1 is not a field of structure
--   WeierstrassCurve"). (2) `Affine` is an abbreviation of `WeierstrassCurve`, so dot projection
--   only resolves `W.Point` / `W.Equation` / `W.nonsingular_iff` when the def is ascribed to
--   `Affine K`; ascribed to `WeierstrassCurve K` every projection fails. Both are recorded
--   because a reader who trusts the brief's spelling loses an hour.
--
-- WHY IT IS A ZMod ARGUMENT AND NOT A NEW TECHNIQUE. Every fpOps operation is a residue, so each
-- one commutes with the cast into `ZMod blsP` (coe_add / coe_mul / coe_sub / coe_neg / coe_one),
-- `fpOps.beq` is equality in the field (beq_iff), and `fpInv` is the field inverse by Fermat
-- (fpInv_correct plus coe_fpInv, P-MODEXP step 1). With those facts the chord-and-tangent law
-- unfolds to mathlib's own `slope` / `addX` / `addY` definitions: for a₁ = a₂ = a₃ = a₄ = 0
-- mathlib's slope is (y₁ - y₂) / (x₁ - x₂) for the secant and 3x² / 2y for the tangent, `addX` is
-- ℓ² - x₁ - x₂ and `addY` is ℓ(x₁ - addX) - y₁ - the same three lines `affineAdd` writes. Closure of
-- the accepted set is then FREE: `nonsingular_add` proves the formula's output is on the curve,
-- so the byte-level sum of two on-curve frames is on-curve with no separate algebraic argument.
--
-- THE INFINITY TRAP, HANDLED. `affineOnCurve fpOps` accepts the all-zero frame, and the all-zero
-- frame is NOT an affine curve point: it must map to `Point.zero`. Every statement below maps
-- (0,0) to 0 and every other accepted frame to `Point.some`, and the case splits in `affineAdd`
-- (infinity in, opposite point out, zero denominator out) are matched against mathlib's own
-- zero, vertical-chord and doubling branches.
--
-- COST. No kernel computation at 381 bits appears in the theorems here: the field facts are
-- `field_simp` + `ring`, and the primality of pBase is the certificate in
-- Assumptions/BasePrime.lean, not a search.

import Midfall.Assumptions.Codec
import Midfall.Assumptions.Eip2537
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions
open WeierstrassCurve WeierstrassCurve.Affine

/-- The base field of the EIP-2537 curve as mathlib sees it: `ZMod blsP` with the `Field` instance
    that the Lucas/Pratt certificate in Assumptions/BasePrime.lean buys (transported across
    `blsP = pBase` by the instance in Assumptions/Eip2537.lean). -/
abbrev K : Type := ZMod blsP

/-- THE SHORT MODEL y² = x³ + 4 over Fp, in mathlib's general five-coefficient Weierstrass form.
    Two spellings matter: the field names are the unicode subscripts a₁, a₂, a₃, a₄, a₆ (`a1` does
    not elaborate), and the type ascription is `Affine` rather than `WeierstrassCurve` so that dot
    projection resolves `W.Point`, `W.Equation` and `W.nonsingular_iff`. -/
def W : Affine K := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }

private theorem a₁z : (W.a₁ : K) = 0 := rfl
private theorem a₂z : (W.a₂ : K) = 0 := rfl
private theorem a₃z : (W.a₃ : K) = 0 := rfl
private theorem a₄z : (W.a₄ : K) = 0 := rfl
private theorem a₆z : (W.a₆ : K) = 4 := rfl

/-- The small integers the group law divides by are nonzero in Fp: the modulus is a 381-bit prime,
    so 2, 3 and 4 all sit strictly between 0 and p. `four_ne_zero` is what makes the all-zero
    frame NOT a curve point, and so what makes the infinity convention unambiguous. -/
private theorem two_lt_p : 2 < blsP := by decide
private theorem three_lt_p : 3 < blsP := by decide
private theorem four_lt_p : 4 < blsP := by decide

private theorem coe_nat_ne_zero {n : ℕ} (hn : n < blsP) (hn0 : n ≠ 0) : (n : K) ≠ 0 := by
  intro h
  have h1 : (n : K).val = 0 := (ZMod.val_eq_zero (n : K)).mpr h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn] at h1
  exact hn0 h1

private theorem two_ne_zero : (2 : K) ≠ 0 := coe_nat_ne_zero two_lt_p (by decide)
private theorem three_ne_zero : (3 : K) ≠ 0 := coe_nat_ne_zero three_lt_p (by decide)
private theorem four_ne_zero : (4 : K) ≠ 0 := coe_nat_ne_zero four_lt_p (by decide)

/-- `0 < blsP`: needed to turn `x % p = 0` into `x = 0` and to justify the saturating subtraction
    inside `fpOps.sub` / `fpOps.neg`. -/
private theorem p_pos : 0 < blsP := Nat.Prime.pos (Fact.out : Nat.Prime blsP)

/-! ### Every fpOps operation commutes with the cast into the field -/

/-- Reducing a number mod the modulus does not change its image in `ZMod blsP`. Stated through
    `ZMod.natCast_zmod_val` rather than by rewriting `Nat.mod_add_div`, which rewrites the wrong
    occurrence: the `a` inside `a % blsP` is as much a match as the `a` on the right. -/
private lemma coe_mod (a : ℕ) : ((a % blsP : ℕ) : K) = (a : K) := by
  have h : ((a : K).val : K) = (a : K) := ZMod.natCast_zmod_val (a : K)
  rwa [ZMod.val_natCast] at h

private lemma coe_nat_eq_iff (a b : ℕ) : ((a : K) = (b : K)) ↔ a % blsP = b % blsP := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this
  · intro h
    exact ZMod.val_injective blsP (by rw [ZMod.val_natCast, ZMod.val_natCast]; exact h)

private lemma coe_zero : ((fpOps.zero : ℕ) : K) = 0 := rfl

private lemma coe_one : ((fpOps.one : ℕ) : K) = 1 := by
  show (((1 % blsP : ℕ) : K)) = 1
  rw [coe_mod, Nat.cast_one]

private lemma coe_add (a b : ℕ) : ((fpOps.add a b : ℕ) : K) = (a : K) + (b : K) := by
  show (((a + b) % blsP : ℕ) : K) = (a : K) + (b : K)
  rw [coe_mod, Nat.cast_add]

private lemma coe_mul (a b : ℕ) : ((fpOps.mul a b : ℕ) : K) = (a : K) * (b : K) := by
  show (((a * b) % blsP : ℕ) : K) = (a : K) * (b : K)
  rw [coe_mod, Nat.cast_mul]

private lemma coe_sub (a b : ℕ) : ((fpOps.sub a b : ℕ) : K) = (a : K) - (b : K) := by
  have hb : b % blsP ≤ a + blsP := by
    have := Nat.mod_lt b p_pos
    omega
  show (((a + blsP - b % blsP) % blsP : ℕ) : K) = (a : K) - (b : K)
  rw [coe_mod, Nat.cast_sub hb, Nat.cast_add, ZMod.natCast_self, add_zero, ← coe_mod b]

private lemma coe_neg (a : ℕ) : ((fpOps.neg a : ℕ) : K) = -(a : K) := by
  have ha : a % blsP ≤ blsP := Nat.le_of_lt (Nat.mod_lt a p_pos)
  show (((blsP - a % blsP) % blsP : ℕ) : K) = -(a : K)
  rw [coe_mod, Nat.cast_sub ha, ZMod.natCast_self, zero_sub, ← coe_mod a]

private lemma coe_b : ((fpOps.b : ℕ) : K) = 4 := rfl

/-- `fpOps.beq` IS field equality: both sides are reduced mod p first, and two residues agree as
    naturals exactly when their casts agree in the field. -/
private lemma beq_iff (a b : ℕ) : fpOps.beq a b = true ↔ (a : K) = (b : K) := by
  show (a % blsP == b % blsP) = true ↔ (a : K) = (b : K)
  rw [beq_iff_eq, coe_nat_eq_iff]

/-- THE INVERSE FACT IN FIELD FORM: whenever the residue of x is nonzero in the field, the value
    `fpInv` returns casts to `(x : K)⁻¹`. This is P-MODEXP step 1 (modPow as modular inverse) read
    through the cast, and it is the only place the Fermat argument enters the group law. -/
private lemma coe_fpInv {x v : ℕ} (hv : fpInv x = some v) : (v : K) = (x : K)⁻¹ := by
  have hne : ¬ (x % blsP == 0) := by
    intro h
    rw [fpInv, if_pos (by simpa using h)] at hv
    exact absurd hv (by simp)
  rw [fpInv, if_neg hne] at hv
  rw [Option.some.injEq] at hv
  subst hv
  show ((modPow x (blsP - 2) blsP : ℕ) : K) = (x : K)⁻¹
  have hnz : (x : K) ≠ 0 := by
    intro h
    have h2 : x % blsP = 0 := by
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, ZMod.val_zero] at this
    exact hne (by simpa using h2)
  rw [modPow_eq x (blsP - 2) blsP p_pos, coe_mod, Nat.cast_pow,
    pow_card_sub_two_eq_inv_card _ hnz]

/-! ### Accepted frames, and the embedding into mathlib's curve -/

/-- A canonical affine Fp frame: both coordinates below the modulus (which is what `fpCoordOf?`
    guarantees for every frame the precompile decodes) and either the all-zero frame or on the
    curve `y² = x³ + 4`. This is `g1PointAddValid` plus canonicity; canonicity is what makes the
    embedding below injective, and the precompile never sees a non-canonical pair. -/
def FpFrame : Type := { P : Nat × Nat // affineOnCurve fpOps P = true }

private theorem FpFrame.onCurve (P : FpFrame) : affineOnCurve fpOps P.1 = true := P.2

/-- The all-zero frame: the point of infinity in EIP-2537 convention. Accepted because
    `affineOnCurve` short-circuits on `affineIsInfinity`, and `decide` evaluates that test on the
    spot (it is `0 % p == 0`, no big arithmetic). -/
def infFrame : FpFrame := ⟨(0, 0), by decide⟩

/-- `affineIsInfinity` IS "both coordinates vanish in the field". -/
private theorem inf_iff (x y : ℕ) :
    affineIsInfinity fpOps (x, y) = true ↔ (x : K) = 0 ∧ (y : K) = 0 := by
  show (fpOps.beq x fpOps.zero && fpOps.beq y fpOps.zero) = true ↔ _
  rw [Bool.and_eq_true, beq_iff, beq_iff, coe_zero]

/-- The field form of the curve equation for an accepted non-infinity frame, in the product
    spelling the group law computes with. -/
private theorem frame_beq (P : FpFrame) (h : ¬ affineIsInfinity fpOps P.1) :
    (P.1.2 : K) * (P.1.2 : K) = (P.1.1 : K) * (P.1.1 : K) * (P.1.1 : K) + 4 := by
  have h1 := P.onCurve
  simp only [affineOnCurve, Bool.or_eq_true_iff] at h1
  cases h1 with
  | inl hin => exact absurd hin h
  | inr hb =>
      rw [beq_iff] at hb
      simp only [coe_mul, coe_add, coe_b] at hb
      exact hb

private theorem frame_eq (P : FpFrame) (h : ¬ affineIsInfinity fpOps P.1) :
    (P.1.2 : K) ^ 2 = (P.1.1 : K) ^ 3 + 4 := by
  have h2 := frame_beq P h
  rw [pow_two, pow_three, h2]
  ring

/-- An accepted frame that is not the infinity frame satisfies the Weierstrass equation. -/
private theorem equation_of_frame (P : FpFrame) (h : ¬ affineIsInfinity fpOps P.1) :
    W.Equation (P.1.1 : K) (P.1.2 : K) := by
  rw [W.equation_iff]
  rw [a₁z, a₂z, a₃z, a₄z, a₆z]
  have h2 := frame_eq P h
  rw [h2]
  ring

/-- The converse: a pair whose field coordinates satisfy the equation is an accepted frame. This
    is what turns mathlib's `nonsingular_add` into closure for `affineAdd`. -/
private theorem onCurve_of_eq_pow (x y : ℕ) (h : (y : K) ^ 2 = (x : K) ^ 3 + 4) :
    affineOnCurve fpOps (x, y) = true := by
  rw [affineOnCurve, Bool.or_eq_true_iff]
  right
  rw [beq_iff]
  simp only [coe_mul, coe_add, coe_b]
  have h1 : (y : K) * (y : K) = (y : K) ^ 2 := by ring
  have h2 : (x : K) * (x : K) * (x : K) = (x : K) ^ 3 := by ring
  rw [h1, h2, h]

private theorem onCurve_of_eq (x y : ℕ) (h : W.Equation (x : K) (y : K)) :
    affineOnCurve fpOps (x, y) = true := by
  rw [W.equation_iff] at h
  rw [a₁z, a₂z, a₃z, a₄z, a₆z] at h
  have h2 : (y : K) ^ 2 = (x : K) ^ 3 + 4 := by
    rw [show ((y : K) ^ 2 + (0 : K) * x * y + (0 : K) * y = (y : K) ^ 2) by ring,
      show ((x : K) ^ 3 + (0 : K) * x ^ 2 + (0 : K) * x + 4 = (x : K) ^ 3 + 4) by ring] at h
    exact h
  exact onCurve_of_eq_pow x y h2

/-- NONSINGULARITY IS FREE for the short form: a singular point has a₁y = 3x² + 2a₂x + a₄ and
    y = -y - a₁x - a₃ simultaneously, i.e. 3x² = 0 and 2y = 0, i.e. x = y = 0, and then the
    equation reads 0 = 4, false in Fp. This is the argument the brief predicted; it needs only
    that the modulus exceeds 4. -/
theorem nonsingular_of_equation {x y : K} (h : W.Equation x y) : W.Nonsingular x y := by
  rw [W.nonsingular_iff]
  refine ⟨h, ?_⟩
  by_cases hx : x = 0
  · right
    subst hx
    simp only [a₁z, a₃z, mul_zero, sub_zero]
    intro hy
    have h1 : (2 : K) * y = 0 := by
      rw [two_mul]
      have h2 := congrArg (fun t => t + y) hy
      rw [h2]
      ring
    have hy0 : y = 0 := (mul_eq_zero.mp h1).resolve_left two_ne_zero
    rw [hy0, W.equation_zero, a₆z] at h
    exact four_ne_zero h
  · left
    intro hh
    simp only [a₁z, a₂z, a₄z, mul_zero, add_zero, zero_mul] at hh
    have h1 : (3 : K) * x ^ 2 = 0 := by simpa using hh
    have h2 : x ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left three_ne_zero
    have h3 : x * x = 0 := by rwa [pow_two] at h2
    exact hx ((mul_eq_zero.mp h3).resolve_left hx)

/-- THE EMBEDDING. An accepted frame maps to the curve point with the same coordinates, except
    that the all-zero frame maps to the point at infinity: the zero frame is not a curve point
    (`four_ne_zero`), and EIP-2537 says the all-zero encoding "is instead used by convention to
    encode the point of infinity". THE TRAP THE BRIEF NAMED: mapping (0,0) to `Point.some` is
    ill-typed, and mapping a genuine curve point to `0` would make every statement below false. -/
def emb (P : FpFrame) : W.Point :=
  if h : affineIsInfinity fpOps P.1 then 0
  else Point.some (P.1.1 : K) (P.1.2 : K)
    (nonsingular_of_equation (equation_of_frame P h))

private theorem emb_inf (P : FpFrame) (h : affineIsInfinity fpOps P.1) : emb P = 0 := dif_pos h

private theorem emb_notInf (P : FpFrame) (h : ¬ affineIsInfinity fpOps P.1) :
    emb P = Point.some (P.1.1 : K) (P.1.2 : K)
      (nonsingular_of_equation (equation_of_frame P h)) :=
  dif_neg h

/-- THE INFINITY FRAME MAPS TO ZERO, and only infinity frames do. This is the direction the
    `g1PointMsmValid` trap turns on: `affineSmul fpOps blsR P = (0,0)` has to mean
    `blsR • emb P = 0`. -/
theorem emb_eq_zero_iff (P : FpFrame) : emb P = 0 ↔ affineIsInfinity fpOps P.1 = true := by
  by_cases h : affineIsInfinity fpOps P.1
  · rw [emb_inf P h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [emb_notInf P h]
    exact ⟨fun hh => absurd hh (Point.some_ne_zero _), fun hh => absurd hh h⟩

/-! ### THE COORDINATE AGREEMENT -/

/-- The secant denominator `x₂ - x₁` is nonzero in the field exactly when the abscissas differ. -/
private lemma coe_sub_ne_zero (P Q : FpFrame) (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    ((fpOps.sub Q.1.1 P.1.1 : ℕ) : K) ≠ 0 := by
  intro h
  have h2 : (Q.1.1 : K) - (P.1.1 : K) = 0 := by rwa [coe_sub] at h
  exact hne ((sub_eq_zero.mp h2).symm)

/-- When `x % p ≠ 0`, `fpInv x` takes the `some` branch. -/
private lemma fpInv_some (x : ℕ) (hx : ¬ (x % blsP == 0)) :
    fpInv x = some (modPow x (blsP - 2) blsP) := by
  show (if x % blsP == 0 then none else some (modPow x (blsP - 2) blsP)) = _
  rw [if_neg hx]

/-- `fpOps.inv` IS `fpInv`, spelled the way `affineAdd` writes it: the structure field, not the
    definition, is what `rw` has to match. -/
private theorem fpOps_inv : fpOps.inv = fpInv := rfl

/-- The `fpInv` call of the secant branch resolves to the Fermat power. -/
private lemma fpInv_sub (P Q : FpFrame) (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    fpInv (fpOps.sub Q.1.1 P.1.1) =
      some (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP) := by
  classical
  refine fpInv_some _ (by
    intro h
    have h2 : (fpOps.sub Q.1.1 P.1.1) % blsP = 0 % blsP := by
      rw [Nat.zero_mod]
      exact (by simpa using h)
    exact coe_sub_ne_zero P Q hne ((coe_nat_eq_iff (fpOps.sub Q.1.1 P.1.1) 0).mpr h2))

/-- THE FERMAT POWER CASTS TO THE FIELD INVERSE of `x₂ - x₁`: step 1's `modPow_inv`, at the
    subtraction the chord formula actually divides by. -/
private lemma coe_modPow_sub (P Q : FpFrame) (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    ((modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP : ℕ) : K) =
      ((Q.1.1 : K) - (P.1.1 : K))⁻¹ := by
  rw [coe_fpInv (fpInv_sub P Q hne), coe_sub]

/-- mathlib's own `slope` on a secant, in the multiplication-by-inverse form the byte-level law
    uses. -/
private theorem slope_secant (P Q : FpFrame) (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    W.slope (P.1.1) (Q.1.1) (P.1.2) (Q.1.2) =
      ((Q.1.2 : K) - (P.1.2 : K)) * ((Q.1.1 : K) - (P.1.1 : K))⁻¹ := by
  rw [W.slope_of_X_ne hne]
  field_simp
  ring

/-- THE SECANT UNFOLDING: with both frames affine and their abscissas distinct, `affineAdd` is the
    chord formula written out, with no `if`, no `match` and no `let` left in it. -/
private theorem affineAdd_secant (P Q : FpFrame)
    (hP : ¬ affineIsInfinity fpOps P.1) (hQ : ¬ affineIsInfinity fpOps Q.1)
    (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    affineAdd fpOps P.1 Q.1
      = (fpOps.sub (fpOps.sub (fpOps.mul (fpOps.mul (fpOps.sub Q.1.2 P.1.2)
              (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP))
            (fpOps.mul (fpOps.sub Q.1.2 P.1.2)
              (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP))) P.1.1) Q.1.1,
          fpOps.sub
            (fpOps.mul (fpOps.mul (fpOps.sub Q.1.2 P.1.2)
                (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP))
              (fpOps.sub P.1.1
                (fpOps.sub (fpOps.sub (fpOps.mul (fpOps.mul (fpOps.sub Q.1.2 P.1.2)
                      (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP))
                    (fpOps.mul (fpOps.sub Q.1.2 P.1.2)
                      (modPow (fpOps.sub Q.1.1 P.1.1) (blsP - 2) blsP))) P.1.1) Q.1.1)))
            P.1.2) := by
  classical
  have hxbeq : ¬ (fpOps.beq P.1.1 Q.1.1 = true) := by
    intro h
    exact hne ((beq_iff P.1.1 Q.1.1).mp h)
  rw [affineAdd, fpOps_inv, if_neg hP, if_neg hQ, if_neg hxbeq, fpInv_sub P Q hne]

/-- THE SECANT COORDINATE AGREEMENT: the byte-level output is mathlib's `addX` / `addY` at
    mathlib's own `slope`, coordinate by coordinate. This is the lemma the whole package turns on:
    the two laws are the same formula, computed in the residues and in the field respectively. -/
theorem affineAdd_coord_secant (P Q : FpFrame)
    (hP : ¬ affineIsInfinity fpOps P.1) (hQ : ¬ affineIsInfinity fpOps Q.1)
    (hne : (P.1.1 : K) ≠ (Q.1.1 : K)) :
    ((affineAdd fpOps P.1 Q.1).1 : K)
      = W.addX (P.1.1) (Q.1.1) (W.slope (P.1.1) (Q.1.1) (P.1.2) (Q.1.2)) ∧
    ((affineAdd fpOps P.1 Q.1).2 : K)
      = W.addY (P.1.1) (Q.1.1) (P.1.2) (W.slope (P.1.1) (Q.1.1) (P.1.2) (Q.1.2)) := by
  classical
  set ℓ := W.slope (P.1.1 : K) (Q.1.1 : K) (P.1.2 : K) (Q.1.2 : K) with hℓ
  have hadd := affineAdd_secant P Q hP hQ hne
  rw [hadd]
  simp only [coe_sub, coe_mul, coe_modPow_sub P Q hne]
  rw [← slope_secant P Q hne]
  constructor
  · show (ℓ * ℓ - (P.1.1 : K)) - (Q.1.1 : K) = W.addX (P.1.1) (Q.1.1) ℓ
    show (ℓ * ℓ - (P.1.1 : K)) - (Q.1.1 : K) =
        ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (Q.1.1 : K)
    ring
  · show ℓ * ((P.1.1 : K) - ((ℓ * ℓ - (P.1.1 : K)) - (Q.1.1 : K))) - (P.1.2 : K) =
        W.addY (P.1.1) (Q.1.1) (P.1.2) ℓ
    show ℓ * ((P.1.1 : K) - ((ℓ * ℓ - (P.1.1 : K)) - (Q.1.1 : K))) - (P.1.2 : K) =
        -((ℓ * ((ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (Q.1.1 : K)) - (P.1.1 : K))) +
            (P.1.2 : K)) -
          (0 : K) * (ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (Q.1.1 : K)) - 0
    ring


/-! ### The tangent branch -/

/-- `fpInv` answers `none` exactly at the multiples of `blsP`. -/
private lemma fpInv_none (x : ℕ) (h : (x : K) = 0) : fpInv x = none := by
  have h2 : x % blsP = 0 := by
    have := (coe_nat_eq_iff x 0).mp h
    simpa [Nat.zero_mod] using this
  show (if x % blsP == 0 then none else some (modPow x (blsP - 2) blsP)) = none
  rw [if_pos (by simpa using h2)]

/-- `y ≠ 0` is the same as `y ≠ -y` in a field of characteristic not 2: the hypothesis mathlib's
    tangent branch asks for. -/
private lemma ne_neg_of_ne_zero {y : K} (hy : y ≠ 0) : y ≠ -y := by
  intro hh
  apply hy
  have h2 := congrArg (fun t => t + y) hh
  have h3 : (2 : K) * y = 0 := by rw [two_mul, h2]; ring
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

private theorem coe_two : ((fpOps.add fpOps.one fpOps.one : ℕ) : K) = 2 := by
  rw [coe_add, coe_one]
  norm_num

private theorem coe_three :
    ((fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one : ℕ) : K) = 3 := by
  rw [coe_add, coe_two, coe_one]
  norm_num

/-- THE TANGENT SLOPE: mathlib's `slope` at (x, y) with y ≠ 0 is `3x² / 2y`, the expression
    `affineDouble` builds from `fpInv`. -/
private theorem slope_tangent (P : FpFrame) (hy : (P.1.2 : K) ≠ 0) :
    W.slope (P.1.1) (P.1.1) (P.1.2) (P.1.2) =
      3 * (P.1.1 : K) * (P.1.1 : K) * ((2 : K) * (P.1.2 : K))⁻¹ := by
  have hneg : (P.1.2 : K) ≠ W.negY (P.1.1 : K) (P.1.2 : K) := by
    intro hh
    have h2 : W.negY (P.1.1 : K) (P.1.2 : K) = -(P.1.2 : K) := by
      show (-(P.1.2 : K) - (0 : K) * (P.1.1 : K) - (0 : K)) = -(P.1.2 : K)
      simp
    rw [h2] at hh
    exact ne_neg_of_ne_zero hy hh
  rw [W.slope_of_Y_ne rfl hneg]
  show ((3 * (P.1.1 : K) ^ 2 + 2 * (0 : K) * (P.1.1 : K) + (0 : K) - (0 : K) * (P.1.2 : K)) /
      ((P.1.2 : K) - (-(P.1.2 : K) - (0 : K) * (P.1.1 : K) - (0 : K))) = _)
  have hd : ((P.1.2 : K) - (-(P.1.2 : K) - (0 : K) * (P.1.1 : K) - (0 : K))) =
      (2 : K) * (P.1.2 : K) := by ring
  have hn : (3 * (P.1.1 : K) ^ 2 + 2 * (0 : K) * (P.1.1 : K) + (0 : K) - (0 : K) * (P.1.2 : K)) =
      3 * (P.1.1 : K) * (P.1.1 : K) := by ring
  rw [hd, hn, div_eq_mul_inv]

/-- THE TANGENT COORDINATE AGREEMENT: the `x₁ = x₂, y₁ = y₂` branch of `affineAdd`, i.e. doubling,
    agrees with mathlib's `addX` / `addY` at the tangent slope. -/
theorem affineDouble_coord (P : FpFrame) (hP : ¬ affineIsInfinity fpOps P.1)
    (hy : (P.1.2 : K) ≠ 0) :
    ((affineDouble fpOps P.1).1 : K)
      = W.addX (P.1.1) (P.1.1) (W.slope (P.1.1) (P.1.1) (P.1.2) (P.1.2)) ∧
    ((affineDouble fpOps P.1).2 : K)
      = W.addY (P.1.1) (P.1.1) (P.1.2) (W.slope (P.1.1) (P.1.1) (P.1.2) (P.1.2)) := by
  classical
  set ℓ := W.slope (P.1.1 : K) (P.1.1 : K) (P.1.2 : K) (P.1.2 : K) with hℓ
  have hinv : fpInv (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) = some (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP) := by
    refine fpInv_some _ (by
      intro h
      have h2 : ((fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2 : ℕ) : K) = 0 :=
        (coe_nat_eq_iff _ 0).mpr (by simpa [Nat.zero_mod] using h)
      rw [coe_mul, coe_add, coe_one] at h2
      exact hy ((mul_eq_zero.mp h2).resolve_left two_ne_zero))
  have hc : (((modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP) : ℕ) : K) = ((2 : K) * (P.1.2 : K))⁻¹ := by
    rw [coe_fpInv hinv, coe_mul, coe_add, coe_one]
    rw [show ((1 : K) + 1 = (2 : K)) by norm_num]
  have hl : (((fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) : ℕ) : K) = ℓ := by
    rw [coe_mul, coe_mul, coe_three, coe_mul, hc]
    refine Eq.trans ?_ (slope_tangent P hy).symm
    ring
  have hcastX : (((fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP))) (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.1)) : ℕ) : K) = ℓ * ℓ - (2 : K) * (P.1.1 : K) := by
    rw [coe_sub, coe_mul, hl, coe_mul, coe_two]
  have hadd : affineDouble fpOps P.1 = ((fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP))) (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.1)), (fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.sub P.1.1 (fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP))) (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.1)))) P.1.2)) := by
    rw [affineDouble, fpOps_inv, if_neg hP]
    dsimp only
    rw [hinv]
  rw [hadd]
  constructor
  · show (((fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP))) (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.1)) : ℕ) : K) = W.addX (P.1.1) (P.1.1) ℓ
    rw [hcastX]
    show ℓ * ℓ - (2 : K) * (P.1.1 : K) = ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (P.1.1 : K)
    ring
  · show (((fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.sub P.1.1 (fpOps.sub (fpOps.mul (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP)) (fpOps.mul (fpOps.mul (fpOps.add (fpOps.add fpOps.one fpOps.one) fpOps.one) (fpOps.mul P.1.1 P.1.1)) (modPow (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (blsP - 2) blsP))) (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.1)))) P.1.2) : ℕ) : K) = W.addY (P.1.1) (P.1.1) (P.1.2) ℓ
    rw [coe_sub, coe_mul, hl, coe_sub, hcastX]
    show ℓ * ((P.1.1 : K) - (ℓ * ℓ - (2 : K) * (P.1.1 : K))) - (P.1.2 : K) =
        -((ℓ * ((ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (P.1.1 : K)) - (P.1.1 : K))) +
            (P.1.2 : K)) -
          (0 : K) * (ℓ ^ 2 + (0 : K) * ℓ - 0 - (P.1.1 : K) - (P.1.1 : K)) - 0
    ring


/-! ### THE AGREEMENT THEOREM -/

/-- NO FRAME OUTSIDE THE CURVE: the all-zero pair is not a curve point (`four_ne_zero`), which is
    what makes the infinity convention unambiguous. -/
private theorem not_onCurve_zero : ¬ W.Equation (0 : K) (0 : K) := by
  intro h
  have h4 : (4 : K) = 0 := by rw [← a₆z]; exact (W.equation_zero).mp h
  exact four_ne_zero h4

/-- A nonsingular pair is never the all-zero pair, so a frame built from one is not the infinity
    frame. -/
private theorem notInf_of_nonsingular (x y : ℕ) (h : W.Nonsingular (x : K) (y : K)) :
    ¬ affineIsInfinity fpOps (x, y) = true := by
  intro hinf
  obtain ⟨hx, hy⟩ := (inf_iff x y).mp hinf
  rw [hx, hy] at h
  exact not_onCurve_zero h.1

/-- `emb` of a frame built from a nonsingular pair, in `Point.some` form. -/
private theorem emb_of_nonsingular (x y : ℕ) (h : W.Nonsingular (x : K) (y : K)) :
    emb ⟨(x, y), onCurve_of_eq x y h.1⟩ =
      Point.some (x : K) (y : K) (nonsingular_of_equation h.1) := by
  classical
  have hi : ¬ affineIsInfinity fpOps (x, y) = true := notInf_of_nonsingular x y h
  rw [emb_notInf ⟨(x, y), onCurve_of_eq x y h.1⟩ hi]

/-- Unfolding of `affineDouble` when the denominator `2y` vanishes: the byte law returns the
    all-zero frame, which is the right answer because such a point is 2-torsion. -/
private theorem negY_eq_neg {x y : K} : W.negY x y = -y - (0 : K) * x - (0 : K) := rfl

/-- A nonzero ordinate is not its own negative, so the tangent branch of mathlib's law applies. -/
private theorem ne_negY_of_ne_zero {x y : K} (hy : y ≠ 0) : y ≠ W.negY x y := by
  intro hh
  rw [negY_eq_neg] at hh
  simp only [zero_mul, sub_zero] at hh
  exact ne_neg_of_ne_zero hy hh

/-- A zero ordinate IS its own negative: the vertical-chord branch of mathlib's law applies, and
    the byte law answers the all-zero frame. -/
private theorem negY_of_zero {x y : K} (hy : y = 0) : y = W.negY x y := by
  rw [negY_eq_neg, hy]
  simp

private theorem affineDouble_of_y_zero (P : FpFrame) (hP : ¬ affineIsInfinity fpOps P.1)
    (hy0 : (P.1.2 : K) = 0) : affineDouble fpOps P.1 = (0, 0) := by
  rw [affineDouble, fpOps_inv, if_neg hP]
  dsimp only
  rw [fpInv_none (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.1.2) (by
    rw [coe_mul, coe_add, coe_one, hy0]
    simp)]
  rfl

/-! ### THE POINT-LEVEL ASSEMBLY (P-G1AGREE step 1) -/

/-- **THE RECORDED OBSTRUCTION, RE-VERIFIED, AND THE FIX - WHICH IS NOT THE SUGGESTED ONE.**
    P-MODEXP is right that \`rw\` cannot move a \`W.Nonsingular\` goal across a coordinate equality:
    rewriting the goal \`W.Nonsingular ((affineAdd fpOps P.1 Q.1).1 : K) ((affineAdd ...).2 : K)\`
    along \`hc1\` has to abstract the *term* \`((affineAdd fpOps P.1 Q.1).1 : K)\` over a motive that
    re-typechecks the dependent proof argument of \`Point.some\`, and that is exactly where the
    elaborator reports the target is not type-correct at \`implicit\` transparency. What the
    write-up did NOT have right is the prescription: neither suggested fix is needed. \`FpFrame\`
    stays a subtype of a pair, and no \`have\`-carried coordinate is needed either. The move is to
    stop rewriting the GOAL and instead apply a lemma stated over VARIABLES, where \`subst\`
    discharges the dependency for free - \`subst\` on a hypothesis between two local variables
    never builds the motive \`rw\` gets stuck on. It works because \`W.Nonsingular\` is a \`def\` into
    \`And\` (Affine/Basic.lean:211) and \`Point\` is an \`inductive\` whose third argument is a \`Prop\`
    (Affine/Point.lean:477), so two \`Point.some\`s with equal coordinates are equal by proof
    irrelevance, which in Lean 4 is definitional. -/
private theorem point_some_eq {x₁ x₂ y₁ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

/-- \`Nonsingular\` transported along coordinate equalities, in the variable form that \`subst\`
    accepts. This is the lemma the recorded obstruction says cannot be proved at all. -/
private theorem nonsingular_congr {x₁ x₂ y₁ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h : W.Nonsingular x₂ y₂) : W.Nonsingular x₁ y₁ := by
  subst hx
  subst hy
  exact h

private theorem equation_congr {x₁ x₂ y₁ y₂ : K} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h : W.Equation x₂ y₂) : W.Equation x₁ y₁ := by
  subst hx
  subst hy
  exact h

/-- The field form of nonsingularity for an accepted non-infinity frame: the proof \`emb\` builds
    internally, named so the assembly can cite it. -/
private theorem nonsingular_of_frame (P : FpFrame) (hP : ¬ affineIsInfinity fpOps P.1) :
    W.Nonsingular (P.1.1 : K) (P.1.2 : K) :=
  nonsingular_of_equation (equation_of_frame P hP)

/-- **CLOSURE, IN ONE STEP.** A pair whose field coordinates agree with a nonsingular pair is an
    accepted frame. This is where \`nonsingular_add\` becomes "the byte-level sum of two on-curve
    frames is on-curve", and it goes through \`equation_congr\` rather than through any rewrite of a
    dependent goal. -/
private theorem onCurve_of_nonsingular_congr {R : Nat × Nat} {x y : K}
    (hx : (R.1 : K) = x) (hy : (R.2 : K) = y) (h : W.Nonsingular x y) :
    affineOnCurve fpOps R = true :=
  onCurve_of_eq R.1 R.2 (equation_congr hx hy h.1)

/-- \`W\` IS AN ELLIPTIC CURVE: the discriminant of \`y² = x³ + 4\` is \`-27 · 16² = -6912\`
    (b₂ = b₄ = b₈ = 0 and b₆ = 4a₆ = 16 in Weierstrass.lean:100-131), and \`p ∤ 6912\` because \`p\`
    is a 381-bit prime. With this instance mathlib's \`AddCommGroup W.Point\` (Affine/Point.lean:805)
    becomes available, which is what makes \`n • emb P\` statable at all - and therefore what makes
    the \`zpowers\` route to \`PrimeOrderWith\` statable over a real curve point. The discriminant is a
    \`rfl\` computation on the coefficient literals; the only arithmetic is \`6912 % blsP\`. -/
instance : WeierstrassCurve.IsElliptic W := ⟨by
  have h : (W.Δ : K) = -6912 := rfl
  rw [h]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (show (6912 : K) ≠ 0 by decide))⟩

/-- Closure under doubling, both sub-branches: a zero ordinate sends the tangent denominator to
    \`none\` and the byte law answers the all-zero frame, which is accepted as infinity. -/
theorem affineDouble_onCurve (P : FpFrame) :
    affineOnCurve fpOps (affineDouble fpOps P.1) = true := by
  classical
  by_cases hPinf : affineIsInfinity fpOps P.1 = true
  · rw [affineDouble, if_pos hPinf]
    decide
  · by_cases hyz : (P.1.2 : K) = 0
    · rw [affineDouble_of_y_zero P hPinf hyz]
      decide
    · obtain ⟨hc1, hc2⟩ := affineDouble_coord P hPinf hyz
      refine onCurve_of_nonsingular_congr hc1 hc2
        (nonsingular_add (nonsingular_of_frame P hPinf) (nonsingular_of_frame P hPinf)
          (fun hxy => ne_negY_of_ne_zero hyz hxy.right))

/-- The doubling of a frame, as a frame. -/
def doubleFrame (P : FpFrame) : FpFrame :=
  ⟨affineDouble fpOps P.1, affineDouble_onCurve P⟩

/-- **CLOSURE OF THE ACCEPTED SET UNDER THE BYTE-LEVEL SUM** - the statement P-MODEXP listed as
    the second missing ingredient, and it is a corollary of the two coordinate agreements, not a
    separate argument. Five branches, matched one for one against mathlib's own case split. -/
theorem affineAdd_onCurve (P Q : FpFrame) :
    affineOnCurve fpOps (affineAdd fpOps P.1 Q.1) = true := by
  classical
  by_cases hPinf : affineIsInfinity fpOps P.1 = true
  · rw [affineAdd, if_pos hPinf]
    exact Q.2
  · by_cases hQinf : affineIsInfinity fpOps Q.1 = true
    · rw [affineAdd, if_neg hPinf, if_pos hQinf]
      exact P.2
    · by_cases hxb : fpOps.beq P.1.1 Q.1.1 = true
      · by_cases hyb : fpOps.beq P.1.2 Q.1.2 = true
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          exact affineDouble_onCurve P
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
          decide
      · have hne : (P.1.1 : K) ≠ (Q.1.1 : K) := fun h => hxb ((beq_iff P.1.1 Q.1.1).mpr h)
        obtain ⟨hc1, hc2⟩ := affineAdd_coord_secant P Q hPinf hQinf hne
        refine onCurve_of_nonsingular_congr hc1 hc2
          (nonsingular_add (nonsingular_of_frame P hPinf) (nonsingular_of_frame Q hQinf)
            (fun hxy => hne hxy.left))

/-- The sum of two frames, as a frame. -/
def addFrame (P Q : FpFrame) : FpFrame :=
  ⟨affineAdd fpOps P.1 Q.1, affineAdd_onCurve P Q⟩

/-- **THE AGREEMENT THEOREM, AT THE POINT LEVEL.** \`emb\` carries the byte-level affine sum to
    mathlib's group law in all four branches of the byte-level case split at once: infinity in,
    opposite points out (both sides zero), the tangent branch, and the secant branch. Everything
    P-MODEXP left is here; the mathematics was already in the two coordinate agreements and the
    only missing piece was \`point_some_eq\`. -/
theorem emb_add (P Q : FpFrame) : emb P + emb Q = emb (addFrame P Q) := by
  classical
  by_cases hPinf : affineIsInfinity fpOps P.1 = true
  · have h1 : affineAdd fpOps P.1 Q.1 = Q.1 := by rw [affineAdd, if_pos hPinf]
    have h2 : addFrame P Q = Q := Subtype.eq h1
    rw [emb_inf P hPinf, h2, zero_add]
  · by_cases hQinf : affineIsInfinity fpOps Q.1 = true
    · have h1 : affineAdd fpOps P.1 Q.1 = P.1 := by
        rw [affineAdd, if_neg hPinf, if_pos hQinf]
      have h2 : addFrame P Q = P := Subtype.eq h1
      rw [emb_inf Q hQinf, h2, add_zero]
    · have hP : W.Nonsingular (P.1.1 : K) (P.1.2 : K) := nonsingular_of_frame P hPinf
      have hQ : W.Nonsingular (Q.1.1 : K) (Q.1.2 : K) := nonsingular_of_frame Q hQinf
      by_cases hxb : fpOps.beq P.1.1 Q.1.1 = true
      · by_cases hyb : fpOps.beq P.1.2 Q.1.2 = true
        · -- tangent / vertical chord: affineAdd reduces to affineDouble
          have hx : (P.1.1 : K) = (Q.1.1 : K) := (beq_iff P.1.1 Q.1.1).mp hxb
          have hy : (P.1.2 : K) = (Q.1.2 : K) := (beq_iff P.1.2 Q.1.2).mp hyb
          have heQ : Point.some (Q.1.1 : K) (Q.1.2 : K) hQ =
              Point.some (P.1.1 : K) (P.1.2 : K) hP := point_some_eq hx.symm hy.symm hQ hP
          have hadd : affineAdd fpOps P.1 Q.1 = affineDouble fpOps P.1 := by
            rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          have hfr : addFrame P Q = doubleFrame P := Subtype.eq hadd
          rw [emb_notInf P hPinf, emb_notInf Q hQinf, heQ, hfr]
          by_cases hyz : (P.1.2 : K) = 0
          · -- vertical chord: the byte law answers the all-zero frame, mathlib answers zero
            have hdbl : affineDouble fpOps P.1 = (0, 0) := affineDouble_of_y_zero P hPinf hyz
            have hif : doubleFrame P = infFrame := Subtype.eq hdbl
            rw [Point.add_self_of_Y_eq (negY_of_zero hyz), hif, emb_inf infFrame (by decide)]
          · -- tangent
            obtain ⟨hc1, hc2⟩ := affineDouble_coord P hPinf hyz
            have hns : W.Nonsingular
                (W.addX (P.1.1) (P.1.1) (W.slope (P.1.1) (P.1.1) (P.1.2) (P.1.2)))
                (W.addY (P.1.1) (P.1.1) (P.1.2) (W.slope (P.1.1) (P.1.1) (P.1.2) (P.1.2))) :=
              nonsingular_add hP hP (fun hxy => ne_negY_of_ne_zero hyz hxy.right)
            have hemb : emb (doubleFrame P) =
                Point.some ((affineDouble fpOps P.1).1 : K) ((affineDouble fpOps P.1).2 : K)
                  (nonsingular_of_equation (nonsingular_congr hc1 hc2 hns).1) :=
              emb_of_nonsingular (affineDouble fpOps P.1).1 (affineDouble fpOps P.1).2
                (nonsingular_congr hc1 hc2 hns)
            rw [Point.add_self_of_Y_ne (ne_negY_of_ne_zero hyz), hemb]
            exact point_some_eq hc1.symm hc2.symm hns _
        · -- opposite points: the byte law answers the all-zero frame, mathlib answers zero
          have hx : (P.1.1 : K) = (Q.1.1 : K) := (beq_iff P.1.1 Q.1.1).mp hxb
          have hne : ¬ ((P.1.2 : K) = (Q.1.2 : K)) :=
            fun h => hyb ((beq_iff P.1.2 Q.1.2).mpr h)
          have hy : (P.1.2 : K) = W.negY (Q.1.1 : K) (Q.1.2 : K) :=
            (Y_eq_of_X_eq hP.1 hQ.1 hx).resolve_left hne
          have hadd : affineAdd fpOps P.1 Q.1 = (0, 0) := by
            rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
            rfl
          have hif : addFrame P Q = infFrame := Subtype.eq hadd
          rw [emb_notInf P hPinf, emb_notInf Q hQinf, Point.add_of_Y_eq hx hy, hif,
            emb_inf infFrame (by decide)]
      · -- secant
        rw [emb_notInf P hPinf, emb_notInf Q hQinf]
        have hne : (P.1.1 : K) ≠ (Q.1.1 : K) := fun h => hxb ((beq_iff P.1.1 Q.1.1).mpr h)
        obtain ⟨hc1, hc2⟩ := affineAdd_coord_secant P Q hPinf hQinf hne
        have hns : W.Nonsingular
            (W.addX (P.1.1) (Q.1.1) (W.slope (P.1.1) (Q.1.1) (P.1.2) (Q.1.2)))
            (W.addY (P.1.1) (Q.1.1) (P.1.2) (W.slope (P.1.1) (Q.1.1) (P.1.2) (Q.1.2))) :=
          nonsingular_add hP hQ (fun hxy => hne hxy.left)
        have hemb : emb (addFrame P Q) =
            Point.some ((affineAdd fpOps P.1 Q.1).1 : K) ((affineAdd fpOps P.1 Q.1).2 : K)
              (nonsingular_of_equation (nonsingular_congr hc1 hc2 hns).1) :=
          emb_of_nonsingular (affineAdd fpOps P.1 Q.1).1 (affineAdd fpOps P.1 Q.1).2
            (nonsingular_congr hc1 hc2 hns)
        rw [Point.add_of_X_ne hne, hemb]
        exact point_some_eq hc1.symm hc2.symm hns _

/-! ### THE SCALAR-MULTIPLICATION AGREEMENT (P-G1AGREE step 2) -/

/-- One double-and-add step at frame level: the same shape as \`affineSmul\`'s step, lifted to
    frames by \`addFrame\` / \`doubleFrame\`. Named so the fold invariant can be stated about it,
    exactly as \`modPowStep\` is named for the same reason. -/
def smulStep (n : ℕ) (st : FpFrame × FpFrame) (i : ℕ) : FpFrame × FpFrame :=
  (if Nat.testBit n i then addFrame st.1 st.2 else st.1, doubleFrame st.2)

/-- The same step at byte level, spelled the way \`affineSmul\` spells it. -/
def smulStepBytes (n : ℕ) (st : (Nat × Nat) × (Nat × Nat)) (i : ℕ) : (Nat × Nat) × (Nat × Nat) :=
  (if Nat.testBit n i then affineAdd fpOps st.1 st.2 else st.1, affineDouble fpOps st.2)

/-- The underlying pairs of a pair of frames. -/
private def fval (st : FpFrame × FpFrame) : (Nat × Nat) × (Nat × Nat) := (st.1.1, st.2.1)

/-- The frame-level fold projects down to the byte-level fold, step by step. \`Prod.fst\` does not
    distribute over a stuck \`if\`, so the two shapes are not defeq and the bit has to be decided
    first - which is what \`by_cases\` buys here. -/
private theorem fval_step (n : ℕ) (st : FpFrame × FpFrame) (i : ℕ) :
    fval (smulStep n st i) = smulStepBytes n (fval st) i := by
  obtain ⟨A, D⟩ := st
  have eL : fval (smulStep n (A, D) i) =
      ((if Nat.testBit n i then addFrame A D else A).1, (doubleFrame D).1) := rfl
  have eR : smulStepBytes n (fval (A, D)) i =
      (if Nat.testBit n i then affineAdd fpOps A.1 D.1 else A.1, affineDouble fpOps D.1) := rfl
  rw [eL, eR]
  by_cases hb : Nat.testBit n i
  · rw [if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb]
    rfl

/-- \`List.foldl\` over \`List.range (k+1)\` is the fold to \`k\` followed by one step at \`k\`. -/
private theorem foldl_range_succ {α : Type} (f : α → ℕ → α) (init : α) (k : ℕ) :
    (List.range (k + 1)).foldl f init = f ((List.range k).foldl f init) k := by
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The two folds agree, state by state. -/
private theorem fval_fold (n : ℕ) (P : FpFrame) :
    ∀ k : ℕ, fval ((List.range k).foldl (smulStep n) (infFrame, P)) =
      (List.range k).foldl (smulStepBytes n) ((0, 0), P.1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [foldl_range_succ, foldl_range_succ, ← ih]
      exact fval_step n _ k

/-- **SCALAR MULTIPLICATION AS A FRAME.** The double-and-add fold, run in the frame type: the
    accepted set is closed under the step, so the fold never leaves it and no separate closure
    proof is needed at the end. -/
def smulFrame (n : ℕ) (P : FpFrame) : FpFrame :=
  ((List.range (Nat.log2 n + 1)).foldl (smulStep n) (infFrame, P)).1

/-- The frame the fold returns has exactly the coordinates \`affineSmul\` computes. -/
theorem smulFrame_val (n : ℕ) (P : FpFrame) :
    (smulFrame n P).1 = affineSmul fpOps n P.1 :=
  congrArg Prod.fst (fval_fold n P (Nat.log2 n + 1))

/-- **DOUBLING AGREES WITH \`emb P + emb P\`.** Note the infinity case: for a non-canonical
    all-zero-mod-p frame \`affineAdd P P\` returns \`P\` while \`affineDouble P\` returns \`(0,0)\`, so
    the two frames can differ as frames - but their images under \`emb\` are both zero, which is
    all the statement needs. -/
theorem emb_double (P : FpFrame) : emb (doubleFrame P) = emb P + emb P := by
  classical
  by_cases hPinf : affineIsInfinity fpOps P.1 = true
  · have h1 : affineDouble fpOps P.1 = (0, 0) := by
      rw [affineDouble, if_pos hPinf]
      rfl
    have h2 : doubleFrame P = infFrame := Subtype.ext h1
    rw [h2, emb_inf infFrame (by decide), emb_inf P hPinf, zero_add]
  · have hbeqx : fpOps.beq P.1.1 P.1.1 = true := (beq_iff P.1.1 P.1.1).mpr rfl
    have hbeqy : fpOps.beq P.1.2 P.1.2 = true := (beq_iff P.1.2 P.1.2).mpr rfl
    have h1 : affineAdd fpOps P.1 P.1 = affineDouble fpOps P.1 := by
      rw [affineAdd, if_neg hPinf, if_neg hPinf, if_pos hbeqx, if_pos hbeqy]
    have h2 : addFrame P P = doubleFrame P := Subtype.ext h1
    rw [← h2, emb_add]

/-- **THE FOLD INVARIANT.** After the steps for the bit positions \`0, ..., k-1\` the accumulator
    carries \`n % 2^k • emb P\` and the doubling register carries \`2^k • emb P\`. Same shape as
    \`modPow_fold\`, and the same proof: one induction on \`k\`, one \`by_cases\` on the bit, and
    \`add_nsmul\` where \`modPow_fold\` used \`Nat.pow_add\`. -/
private theorem emb_smul_fold (n : ℕ) (P : FpFrame) :
    ∀ k : ℕ, emb ((List.range k).foldl (smulStep n) (infFrame, P)).1 = (n % 2 ^ k) • emb P ∧
      emb ((List.range k).foldl (smulStep n) (infFrame, P)).2 = 2 ^ k • emb P := by
  intro k
  induction k with
  | zero =>
      have h1 : ((List.range 0).foldl (smulStep n) (infFrame, P)).1 = infFrame := rfl
      have h2 : ((List.range 0).foldl (smulStep n) (infFrame, P)).2 = P := rfl
      rw [h1, h2, Nat.pow_zero, Nat.mod_one, zero_nsmul, one_nsmul,
        emb_inf infFrame (by decide)]
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      rw [foldl_range_succ]
      obtain ⟨h1, h2⟩ := ih
      have e1 : (smulStep n ((List.range k).foldl (smulStep n) (infFrame, P)) k).1 =
          (if Nat.testBit n k then
            addFrame ((List.range k).foldl (smulStep n) (infFrame, P)).1
              ((List.range k).foldl (smulStep n) (infFrame, P)).2
           else ((List.range k).foldl (smulStep n) (infFrame, P)).1) := rfl
      have e2 : (smulStep n ((List.range k).foldl (smulStep n) (infFrame, P)) k).2 =
          doubleFrame ((List.range k).foldl (smulStep n) (infFrame, P)).2 := rfl
      rw [e1, e2]
      refine ⟨?_, ?_⟩
      · by_cases hb : Nat.testBit n k
        · rw [if_pos hb, ← emb_add, h1, h2, ← add_nsmul, mod_pow_succ 2 n k (by decide),
            ← Nat.toNat_testBit, hb, Bool.toNat_true, Nat.mul_one]
        · rw [if_neg hb, h1, mod_pow_succ 2 n k (by decide), ← Nat.toNat_testBit,
            Bool.eq_false_of_ne_true hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
      · rw [emb_double, h2, ← two_nsmul, ← mul_nsmul]
        congr 1

/-- **THE SCALAR-MULTIPLICATION AGREEMENT.** \`n • emb P\` is the frame \`affineSmul\` computes: the
    byte-level double-and-add and mathlib's \`nsmul\` agree, for every \`n\` and every accepted
    frame. This is the lemma \`g1Msm1\` needs, and - through \`g1InSubgroup\` - the subgroup half of
    \`g1Valid\` needs. -/
theorem emb_smul (n : ℕ) (P : FpFrame) : n • emb P = emb (smulFrame n P) := by
  have h := emb_smul_fold n P (Nat.log2 n + 1)
  rw [show smulFrame n P =
        ((List.range (Nat.log2 n + 1)).foldl (smulStep n) (infFrame, P)).1 from rfl]
  rw [Nat.mod_eq_of_lt Nat.lt_log2_self] at h
  exact h.1.symm

/-! ### Canonical frames: where "maps to zero" and "is the all-zero pair" come apart -/

/-- A frame is **canonical** when both coordinates sit below the modulus. Every frame the
    precompile actually decodes has this property - \`fpCoordOf?\` rejects a coordinate at or above
    \`blsP\` - and it is what makes "vanishes in the field" and "is literally zero" the same
    statement, which is the gap between \`emb X = 0\` and the \`affineSmul ... = (0,0)\` that
    \`g1InSubgroup\` tests. -/
def CanonicalFrame (P : FpFrame) : Prop := P.1.1 < blsP ∧ P.1.2 < blsP

/-- For a canonical frame the two readings of "is the point at infinity" coincide: the EIP-2537
    convention (both coordinates vanish in the field) and the literal all-zero pair. Without
    canonicity this is FALSE - see \`emb_zero_needs_canonical\` - which is why the hypothesis is
    stated rather than quietly assumed. -/
theorem emb_eq_zero_iff_canonical (P : FpFrame) (hP : CanonicalFrame P) :
    emb P = 0 ↔ P.1 = (0, 0) := by
  classical
  rw [emb_eq_zero_iff, inf_iff, Prod.mk.injEq]
  refine ⟨fun ⟨hx, hy⟩ => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ⟨?_, ?_⟩⟩
  · have h2 : P.1.1 % blsP = 0 % blsP := (coe_nat_eq_iff P.1.1 0).mp hx
    rwa [Nat.mod_eq_of_lt hP.1, Nat.zero_mod] at h2
  · have h2 : P.1.2 % blsP = 0 % blsP := (coe_nat_eq_iff P.1.2 0).mp hy
    rwa [Nat.mod_eq_of_lt hP.2, Nat.zero_mod] at h2
  · rw [h1]
    exact Nat.cast_zero
  · rw [h2]
    exact Nat.cast_zero

/-- **THE CANONICITY HYPOTHESIS BITES** (D-P23 falsification for
    \`emb_eq_zero_iff_canonical\`). The frame \`((blsP, blsP))\` is accepted - it is infinity in the
    field sense - \`emb\` sends it to zero, and it is NOT the all-zero pair the precompile's own
    subgroup test looks for. So "maps to zero" and "is literally (0,0)" come apart without
    canonicity, and the hypothesis is not decoration. The precompile never hands one over
    (\`fpCoordOf?\` rejects a coordinate at or above \`p\`), which is exactly why the lemma carries
    the hypothesis instead of assuming every frame is canonical. -/
def junkPair : Nat × Nat := (blsP, blsP)
theorem junkPair_onCurve : affineOnCurve fpOps junkPair = true := by decide
def junkFrame : FpFrame := ⟨junkPair, junkPair_onCurve⟩

theorem emb_zero_needs_canonical : emb junkFrame = 0 ∧ junkFrame.1 ≠ (0, 0) :=
  ⟨emb_inf junkFrame (by decide), fun hh =>
    absurd (congrArg (fun (t : Nat × Nat) => t.1) hh) (Nat.ne_of_gt p_pos)⟩

theorem junkFrame_not_canonical : ¬ CanonicalFrame junkFrame := fun ⟨h1, _⟩ =>
  Nat.lt_irrefl blsP h1

/-! ### D-P23: witnesses and falsifications for the two agreements -/

/-- The published EIP-2537 G1 generator H1, coordinate by coordinate: the two numbers the EIP
    prints, which are the two coordinates \`katG1GenWords\` renders. Stated as literals rather than
    decoded from the frame so the kernel facts below stay shallow. -/
def genX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

/-- The \`y\` of H1. -/
def genY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- The generator as a pair, and as a frame. \`affineOnCurve\` at the REAL 381-bit modulus is a
    kernel theorem here, not a gate: the curve equation of a point nobody chose. -/
def genPair : Nat × Nat := (genX, genY)

theorem genPair_onCurve : affineOnCurve fpOps genPair = true := by decide

def genFrame : FpFrame := ⟨genPair, genPair_onCurve⟩

theorem genFrame_canonical : CanonicalFrame genFrame := ⟨by decide, by decide⟩
theorem genFrame_notInf : ¬ affineIsInfinity fpOps genPair = true := by decide

/-- `genFrame`'s pair, spelled as the pair: the projection is `rfl`, but the elaborator will not
    always cross the subtype coercion on its own and every `decide` below is priced by whether it
    has to. -/
private theorem genFrame_val : genFrame.1 = genPair := rfl

/-- The generator is not mapped to zero, so every statement below about \`emb genFrame\` is about a
    non-identity point. -/
theorem emb_gen_ne_zero : emb genFrame ≠ 0 := fun h =>
  genFrame_notInf ((emb_eq_zero_iff genFrame).mp h)

/-- The additive inverse of H1 as published (\`p - y\`), and the fact that the byte law sends the
    pair to the all-zero frame: the opposite-points branch is exercised by real bytes. -/
def negGenY : Nat :=
  0x114d1d6855d545a8aa7d76c8cf2e21f267816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca

def negGenPair : Nat × Nat := (genX, negGenY)
theorem negGenPair_onCurve : affineOnCurve fpOps negGenPair = true := by decide
def negGenFrame : FpFrame := ⟨negGenPair, negGenPair_onCurve⟩

theorem add_gen_negGen : affineAdd fpOps genPair negGenPair = (0, 0) := by decide

/-- **WITNESS 1 FOR \`emb_add\` (D-P23 satisfiability).** The assembly is not vacuous and not
    satisfied by a degenerate model: at the published generator it says the sum with the published
    negation is the point at infinity, while the generator itself is not. -/
theorem emb_add_witness : emb genFrame + emb negGenFrame = 0 ∧ emb genFrame ≠ 0 := by
  refine ⟨?_, emb_gen_ne_zero⟩
  have h : addFrame genFrame negGenFrame = infFrame := Subtype.ext add_gen_negGen
  rw [emb_add, h, emb_inf infFrame (by decide)]

/-- **WITNESS 2 FOR `emb_smul` (D-P23 satisfiability).** The fold at `n = 1` really is the
    identity on the generator - the accumulator picks up the point at the first set bit and nothing
    else - so the agreement is instantiated at a nontrivial frame, not only at infinity. -/
theorem smulFrame_one_gen : smulFrame 1 genFrame = genFrame := Subtype.ext rfl

theorem emb_smul_witness_one : (1 : ℕ) • emb genFrame = emb genFrame := by
  rw [emb_smul, smulFrame_one_gen]

/-- **FALSIFICATION 1 FOR \`emb_add\` (D-P23): the case split is load-bearing.** The naive
    point-level statement "the sum is \`Point.some\` of the output coordinates" is not even
    type-correct: the byte law returns the all-zero pair when an input is infinity, and \`(0,0)\` is
    not a nonsingular pair. -/
theorem not_all_outputs_nonsingular :
    ¬ ∀ P Q : FpFrame, W.Nonsingular ((affineAdd fpOps P.1 Q.1).1 : K)
      ((affineAdd fpOps P.1 Q.1).2 : K) := fun h =>
  not_onCurve_zero ((h infFrame infFrame).1)

/-- **FALSIFICATION 2 FOR \`emb_smul\` (D-P23): the agreement really depends on the scalar.** Were
    it the vacuous statement "every scalar multiple is the point", it would say
    \`0 • emb G = emb G\`, which is false at the generator. -/
theorem smul_agreement_not_constant :
    ¬ ∀ (n : ℕ) (P : FpFrame), emb (smulFrame n P) = emb P := by
  intro h
  have h1 : (0 : ℕ) • emb genFrame = emb genFrame := by
    have h2 := h 0 genFrame
    rw [← emb_smul] at h2
    exact h2
  exact emb_gen_ne_zero (h1.symm.trans (zero_nsmul (emb genFrame)))
/-! ### WHAT P-G1AGREE LANDED, AND WHAT IS LEFT

**LANDED.** Step 1: \`emb_add\` - the point-level assembly - plus the closure statements a frame
type needs (\`affineAdd_onCurve\`, \`affineDouble_onCurve\`, \`addFrame\`, \`doubleFrame\`). Step 2:
\`emb_smul\` - the scalar-multiplication agreement - via \`smulFrame\`, plus \`smulFrame_val\` tying
the frame fold back to \`affineSmul\` byte for byte. The \`IsElliptic\` instance for \`W\` is new and
it is what makes \`n • emb P\` statable at all: mathlib's \`AddCommGroup W.Point\`
(Affine/Point.lean:805) is now in scope over the real modulus.

**THE RECORDED OBSTRUCTION WAS RIGHT ABOUT THE SYMPTOM AND WRONG ABOUT THE CURE.** See
\`point_some_eq\`. \`FpFrame\` was NOT converted to a structure with named fields, and no coordinate
is carried as a \`have\`: the fix is to state the transfer lemmas over variables and let \`subst\`
do the work, because \`Point.some\*'s third argument is a \`Prop\` and Lean 4 proof irrelevance is
definitional. Roughly ten lines, as P-MODEXP predicted, but a different ten lines.

**LEFT, AND MEASURED.** Two items, both mechanical, neither mathematical.

1. \`g1InSubgroup\` in field form. \`emb_smul\` gives \`blsR • emb P = emb (smulFrame blsR P)\`, and
   \`emb_eq_zero_iff_canonical\` gives \`emb X = 0 ↔ X.1 = (0,0)\` for a CANONICAL frame, so the
   subgroup half of \`g1Valid\` is one lemma away: it needs
   \`CanonicalFrame (smulFrame blsR P)\`. That in turn needs "every coordinate \`affineAdd\` /
   \`affineDouble\` returns is either copied from an input or reduced mod \`p\`", which is a
   branch walk over the two \`match\`es. It was written and it does not check: the elaborator's
   whnf of \`affineAdd fpOps genPair genPair\` forces the \`fpInv\` (a 381-bit \`modPow\`) while
   type-checking, and the defeq check dies on \`maximum recursion depth\` at every depth tried
   (1024, 100000, 1000000 - the last one flips to "(kernel) deep recursion detected", i.e. a C++
   stack limit, not a budget). \`decide\` proves the same fact happily, because the kernel reduces
   with its own deeper stack. The fix is to keep such facts inside \`decide\` and never let a
   defeq check touch a reduced coordinate - or to add a \`FpFrame\` field for canonicity so the
   walk is over the type, not over the term. Recorded because it cost 20 minutes and it will
   cost the next package 20 more.
2. The same wall blocks the strongest possible witness, \`blsR • emb genFrame = 0\`: the byte-level
   \`affineSmul fpOps blsR genPair = (0,0)\` IS provable by \`decide\` (measured: about 15 s, proved
   in a scratch file during this package), but transporting it across \`smulFrame_val\` requires
   exactly the defeq check that dies above. \`Instances/Bls12_381G1.lean\` already pays the 15 s for
   the same computation in its own frame type.
-/


/-! ### P-CANON: THE CANONICITY WALK

**THE RECORDED WALL IS REAL, AND THE RECORDED DIAGNOSIS IS WRONG ABOUT ITS MECHANISM.** The
closing section of this file blamed \`fpInv\`: "any defeq that forces whnf of affineAdd /
affineDouble at real 381-bit literals must evaluate fpInv, a 381-bit modPow, inside the
elaborator". That is one of two mechanisms, and it is not the one that blocks the walk. Measured
here, at the DEFAULT \`maxRecDepth\` (512), with \`lake env lean -DautoImplicit=false\`:

* \`example : (affineDouble fpOps genPair).1 < blsP\` - \`rfl\` FAILS ("not definitionally equal",
  not a depth error: the check gives up and reports non-defeq) while \`decide\` succeeds. That one
  IS the modPow: the argument is a literal, so \`fpInv\` really runs.
* \`g1InSubgroup P.1 = true -> affineSmul fpOps blsR P.1 = (0, 0)\` for a VARIABLE \`P\` - the proof
  is never reached: \`show\`, \`rw [g1InSubgroup]\`, \`simp only [g1InSubgroup]\` and a bare term-mode
  ascription all die on \`maximum recursion depth\`, and at \`maxRecDepth 100000\` the same check
  dies on the deterministic 200k-heartbeat whnf budget instead. No literal point is involved, so
  no \`fpInv\` can be running.

**THE ACTUAL MECHANISM.** \`g1InSubgroup Q\` is \`affineSmul fpOps blsR Q == (0, 0)\`, and \`whnf\` of a
pair \`==\` does not stop at \`BEq.beq\`: the \`BEq (Nat x Nat)\` instance is a structure projection
that beta-reduces to \`a.1 == b.1 && a.2 == b.2\`, which forces \`whnf\` of \`affineSmul fpOps blsR Q\`,
which unrolls the whole 255-step double-and-add fold into one stuck term. **The cost is the FOLD,
not the INVERSE**, and it is paid whenever a defeq check looks *through* a pair-\`==\` or a
\`smulFrame\` projection. Two corollaries, both used below:

1. **Never force whnf of a term whose head is a pair-\`==\` or a \`smulFrame\` projection at the
   literal scalar.** \`unfold\` and \`delta\` substitute a named constant and do NOT whnf, so they
   cross \`g1InSubgroup\` for free; \`rw\`, \`simp\`, \`show\` and \`change\` all whnf and all die.
   Measured: \`unfold g1InSubgroup at h\` succeeds where \`rw [g1InSubgroup] at h\` dies.
2. **\`▸\` along a NAMED equation does not whnf either**, so the transports the recorded note said
   were impossible - \`smulFrame_val blsR P ▸ h\`, \`(emb_smul blsR P).symm ▸ h\`,
   \`emb_eq_zero_iff_canonical (smulFrame blsR P) hc\` - all check in milliseconds. It was never the
   transport that failed; it was rewriting through the \`==\`.

**AND NEITHER CURE IN THE BRIEF IS THE ONE THAT WORKED.** Cure 1 ("keep such facts inside
\`decide\`") is half right: \`decide\` does prove the byte-level facts (measured: 16.6 s for
\`affineSmul fpOps blsR genPair = (0, 0)\` at \`maxRecDepth 100000\`, peak tree 4.64 GiB, largest
process 3.99 GiB), but the walk never needed \`decide\` - it needed a walk over VARIABLES, which is
cheap because nothing is instantiated at a literal. Cure 2 (a canonicity FIELD on \`FpFrame\`) is
unnecessary and would have been expensive: it changes every constructor in this file
(\`infFrame\`, \`genFrame\`, \`negGenFrame\`, \`junkFrame\`) and every \`Subtype.eq\`, and it does not
remove the branch walk - a frame that carries a canonicity field still has to PROVE that field for
\`addFrame P Q\`, which is the same walk. **The third approach - walk over variables, transport with
\`unfold\` / \`delta\` / \`▸\`, and touch literals only through named equations - is what landed, and
it cost minutes, not the two hours the recorded note priced.** -/

/-- Every \`fpOps\` operation that reduces returns a residue below the modulus, and \`fpOps.zero\` is
    zero. That is the whole arithmetic content of the walk: the byte law is built ONLY from these,
    so every coordinate it produces is either one of these (hence reduced) or copied verbatim from
    an input (hence reduced, if the input was). -/
private theorem sub_blt {a b : ℕ} : fpOps.sub a b < blsP := Nat.mod_lt _ p_pos
private theorem zero_blt : fpOps.zero < blsP := p_pos

/-- **THE WALK, DOUBLING HALF.** Five branches, and no literal anywhere in it: the infinity branch
    and the zero-denominator branch return \`fpOps.zero\`, and the tangent branch returns two
    \`fpOps.sub\`s. \`cases h : fpOps.inv ...\` splits the \`match\` without ever asking what the
    inverse IS, which is what keeps \`fpInv\` - and therefore the 381-bit \`modPow\` - out of the
    elaborator. -/
theorem affineDouble_canonic (P : Nat × Nat) (_hx : P.1 < blsP) (_hy : P.2 < blsP) :
    (affineDouble fpOps P).1 < blsP ∧ (affineDouble fpOps P).2 < blsP := by
  classical
  by_cases hinf : affineIsInfinity fpOps P = true
  · rw [affineDouble, if_pos hinf]
    exact ⟨zero_blt, zero_blt⟩
  · rw [affineDouble, if_neg hinf]
    dsimp only
    cases h : fpOps.inv (fpOps.mul (fpOps.add fpOps.one fpOps.one) P.2) with
    | none => exact ⟨zero_blt, zero_blt⟩
    | some i =>
        dsimp only
        exact ⟨sub_blt, sub_blt⟩

/-- **THE WALK, ADDITION HALF.** Five branches again: two copy an input - which is exactly where
    the hypothesis is USED rather than manufactured - one delegates to doubling, one returns the
    all-zero frame, and the secant returns two reductions. -/
theorem affineAdd_canonic (P Q : Nat × Nat)
    (hP : P.1 < blsP ∧ P.2 < blsP) (hQ : Q.1 < blsP ∧ Q.2 < blsP) :
    (affineAdd fpOps P Q).1 < blsP ∧ (affineAdd fpOps P Q).2 < blsP := by
  classical
  by_cases hPinf : affineIsInfinity fpOps P = true
  · rw [affineAdd, if_pos hPinf]
    exact hQ
  · by_cases hQinf : affineIsInfinity fpOps Q = true
    · rw [affineAdd, if_neg hPinf, if_pos hQinf]
      exact hP
    · by_cases hxb : fpOps.beq P.1 Q.1 = true
      · by_cases hyb : fpOps.beq P.2 Q.2 = true
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_pos hyb]
          exact affineDouble_canonic P hP.1 hP.2
        · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_pos hxb, if_neg hyb]
          exact ⟨zero_blt, zero_blt⟩
      · rw [affineAdd, if_neg hPinf, if_neg hQinf, if_neg hxb]
        cases h : fpOps.inv (fpOps.sub Q.1 P.1) with
        | none => exact ⟨zero_blt, zero_blt⟩
        | some i =>
            dsimp only
            exact ⟨sub_blt, sub_blt⟩

/-- Closure of the frame type under the two laws, canonicity included. -/
theorem doubleFrame_canonic (P : FpFrame) (hP : CanonicalFrame P) :
    CanonicalFrame (doubleFrame P) :=
  affineDouble_canonic P.1 hP.1 hP.2

theorem addFrame_canonic (P Q : FpFrame) (hP : CanonicalFrame P) (hQ : CanonicalFrame Q) :
    CanonicalFrame (addFrame P Q) :=
  affineAdd_canonic P.1 Q.1 hP hQ

/-- The fold step preserves canonicity of both registers, and the infinity frame is canonical, so
    the whole double-and-add never leaves the canonical set. **This is the lemma the recorded
    obstruction said could not be proved.** -/
theorem smulStep_canonic (n : ℕ) (st : FpFrame × FpFrame) (i : ℕ)
    (h1 : CanonicalFrame st.1) (h2 : CanonicalFrame st.2) :
    CanonicalFrame (smulStep n st i).1 ∧ CanonicalFrame (smulStep n st i).2 := by
  classical
  by_cases hb : Nat.testBit n i
  · rw [smulStep, if_pos hb]
    exact ⟨addFrame_canonic st.1 st.2 h1 h2, doubleFrame_canonic st.2 h2⟩
  · rw [smulStep, if_neg hb]
    exact ⟨h1, doubleFrame_canonic st.2 h2⟩

/-- **THE WALK LANDED: THE FOLD NEVER LEAVES THE CANONICAL SET.** Induction on the number of steps,
    the same shape as \`fval_fold\` above and for the same reason - \`foldl_range_succ\` to expose the
    last step, \`smulStep_canonic\` to discharge it. Nothing is instantiated at a literal, which is
    why it checks in milliseconds where the recorded version died. -/
theorem smulFrame_canonic (n : ℕ) (P : FpFrame) (hP : CanonicalFrame P) :
    CanonicalFrame (smulFrame n P) := by
  classical
  have key : ∀ k : ℕ,
      CanonicalFrame ((List.range k).foldl (smulStep n) (infFrame, P)).1 ∧
        CanonicalFrame ((List.range k).foldl (smulStep n) (infFrame, P)).2 := by
    intro k
    induction k with
    | zero => exact ⟨⟨zero_blt, zero_blt⟩, hP⟩
    | succ k ih =>
        rw [foldl_range_succ]
        exact smulStep_canonic n _ k ih.1 ih.2
  exact (key (Nat.log2 n + 1)).1

/-! ### What the walk buys: the subgroup half of \`g1Valid\` -/

/-- **\`n • emb P = 0\` IS THE BYTE SUBGROUP TEST**, for any scalar and any frame whose fold output
    is canonical. Four transports, each along a NAMED equation (\`smulFrame_val\`,
    \`emb_eq_zero_iff_canonical\`, \`emb_smul\`) and each with \`▸\`, which does not whnf. The general
    scalar is deliberate: at \`n = blsR\` the hypothesis is discharged by \`smulFrame_canonic\`, and
    stating it abstractly is what makes the falsification below statable at all. -/
theorem nsmul_emb_eq_zero_iff (n : ℕ) (P : FpFrame) (hc : CanonicalFrame (smulFrame n P)) :
    n • emb P = 0 ↔ affineSmul fpOps n P.1 = (0, 0) := by
  classical
  constructor
  · intro h
    have h2 : emb (smulFrame n P) = 0 := emb_smul n P ▸ h
    have h1 : (smulFrame n P).1 = (0, 0) := (emb_eq_zero_iff_canonical (smulFrame n P) hc).mp h2
    exact smulFrame_val n P ▸ h1
  · intro h
    have h1 : (smulFrame n P).1 = (0, 0) := (smulFrame_val n P).symm ▸ h
    have h2 : emb (smulFrame n P) = 0 :=
      (emb_eq_zero_iff_canonical (smulFrame n P) hc).mpr h1
    exact (emb_smul n P).symm ▸ h2

/-- **THE SUBGROUP HALF OF \`g1Valid\`.** \`g1InSubgroup\` - the test the precompile itself runs - is
    exactly "\`blsR • emb P = 0\`" for a canonical frame. Note how the crossing of \`g1InSubgroup\`
    is done: \`unfold\`, not \`rw\`, because \`rw\` whnfs the pair-\`==\` and wakes the fold. -/
theorem g1InSubgroup_iff (P : FpFrame) (hP : CanonicalFrame P) :
    g1InSubgroup P.1 = true ↔ blsR • emb P = 0 := by
  classical
  have hc : CanonicalFrame (smulFrame blsR P) := smulFrame_canonic blsR P hP
  have core : (g1InSubgroup P.1 = true) ↔ affineSmul fpOps blsR P.1 = (0, 0) := by
    constructor
    · intro h
      unfold g1InSubgroup at h
      exact beq_iff_eq.mp h
    · intro h
      unfold g1InSubgroup
      exact beq_iff_eq.mpr h
  exact core.trans (nsmul_emb_eq_zero_iff blsR P hc).symm

/-- **\`g1PointMsmValid\`, IN GROUP-THEORETIC FORM.** The validator that G1MSM and PAIRING_CHECK run
    is exactly "the embedded point is r-torsion", for a canonical frame. The infinity disjunct
    inside \`g1PointMsmValid\` disappears on its own: an infinity frame embeds to zero and zero is
    r-torsion, which is why no case split survives into the statement. -/
theorem g1PointMsmValid_iff (P : FpFrame) (hP : CanonicalFrame P) :
    g1PointMsmValid P.1 = true ↔ blsR • emb P = 0 := by
  classical
  constructor
  · intro h
    unfold g1PointMsmValid at h
    rw [Bool.and_eq_true] at h
    obtain ⟨-, hdisj⟩ := h
    rw [Bool.or_eq_true_iff] at hdisj
    cases hdisj with
    | inl hinf =>
        have hz : emb P = 0 := emb_inf P hinf
        rw [hz]
        exact nsmul_zero _
    | inr hsub => exact (g1InSubgroup_iff P hP).mp hsub
  · intro h
    unfold g1PointMsmValid
    simp only [Bool.and_eq_true, FpFrame.onCurve P, true_and, Bool.or_eq_true_iff]
    right
    exact (g1InSubgroup_iff P hP).mpr h

/-! ### The strongest witness the recorded note said was unreachable -/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
/-- **THE PUBLISHED GENERATOR IS IN THE r-TORSION, BYTE FOR BYTE**: \`affineSmul fpOps blsR genPair =
    (0, 0)\` at the real 381-bit moduli. MEASURED: 16.6 s of kernel reduction, peak tree 4.64 GiB,
    largest single process 3.99 GiB, at \`maxRecDepth 100000\` - the same computation
    \`Instances/Bls12_381G1.lean\` pays for \`g1GenFrame_valid\` in its own frame type, and the number
    the closing section of this file predicted ("about 15 s"). It is a \`decide\`, and it is the ONLY
    kernel computation in this section: everything else is a walk over variables. -/
theorem genPair_r_smul_zero : affineSmul fpOps blsR genPair = (0, 0) := by decide

/-- **\`blsR • emb genFrame = 0\` - THE FACT THE RECORDED NOTE SAID COULD NOT BE TRANSPORTED.** It
    transports in three lines, because \`▸\` along a named equation never whnfs the fold. This is
    the "strongest possible witness" P-G1AGREE left out for lack of a defeq. -/
theorem r_nsmul_emb_genFrame : blsR • emb genFrame = 0 := by
  have h1 : (smulFrame blsR genFrame).1 = (0, 0) :=
    (smulFrame_val blsR genFrame).symm ▸ genPair_r_smul_zero
  have h2 : emb (smulFrame blsR genFrame) = 0 :=
    (emb_eq_zero_iff_canonical (smulFrame blsR genFrame)
      (smulFrame_canonic blsR genFrame genFrame_canonical)).mpr h1
  exact (emb_smul blsR genFrame).symm ▸ h2

/-- The same fact on the byte side, now free: the published generator passes the precompile's own
    subgroup test, as a THEOREM rather than as a gate. -/
theorem g1InSubgroup_genPair : g1InSubgroup genPair = true :=
  (g1InSubgroup_iff genFrame genFrame_canonical).mpr r_nsmul_emb_genFrame

/-- **AND THE WHOLE VALIDATOR PASSES ON THE PUBLISHED GENERATOR**, as a theorem: this is the
    \`g1PointMsmValid\` fact that \`g1GenFrame_valid\` in \`Instances/Bls12_381G1.lean\` reaches by
    \`decide\` on the byte frame, reached here through the group law instead. -/
theorem g1PointMsmValid_genPair : g1PointMsmValid genPair = true :=
  (g1PointMsmValid_iff genFrame genFrame_canonical).mpr r_nsmul_emb_genFrame

/-! ### D-P23: witnesses and falsifications for the walk -/

/-- **WITNESS FOR THE WALK (D-P23 satisfiability).** The walk is not vacuous: it discharges
    canonicity for the 255-step fold at the PUBLISHED GENERATOR, which is a real 381-bit
    computation and not a two-point model. -/
theorem smulFrame_gen_canonical : CanonicalFrame (smulFrame blsR genFrame) :=
  smulFrame_canonic blsR genFrame genFrame_canonical

/-- **WITNESS AT THE OTHER END**, cheap and independent of the big \`decide\`: the identity frame
    satisfies the new equivalence too, so it is not resting on a single point. -/
theorem g1InSubgroup_infFrame :
    g1InSubgroup infFrame.1 = true ↔ blsR • emb infFrame = 0 :=
  g1InSubgroup_iff infFrame ⟨by decide, by decide⟩

/-- **FALSIFICATION FOR THE WALK (D-P23): the hypothesis is load-bearing.** The all-zero-mod-p junk
    frame is an accepted frame, and the byte sum of it with itself COPIES it, so the output is not
    canonical. Without the hypothesis the conclusion is simply false, and no restructuring of the
    type would have saved it: this is the copy branch of \`affineAdd\`, not an arithmetic branch. -/
theorem affineAdd_canonic_needs_hypothesis : ¬ CanonicalFrame (addFrame junkFrame junkFrame) := by
  intro hc
  obtain ⟨h1, _⟩ := hc
  have e : (addFrame junkFrame junkFrame).1.1 = blsP := rfl
  rw [e] at h1
  exact Nat.lt_irrefl blsP h1

/-- **FALSIFICATION FOR \`nsmul_emb_eq_zero_iff\` (D-P23): the canonicity hypothesis is
    load-bearing, and here is the frame and the scalar that break it.** At \`n = 1\` the fold is a
    copy, so the junk frame's fold output IS the junk pair: \`1 • emb junkFrame = 0\` holds (junk
    embeds to zero) while \`affineSmul fpOps 1 junkPair = (0, 0)\` does not. The equivalence is
    therefore not a tautology about subtype coercion - it fails on a named input. -/
theorem nsmul_emb_eq_zero_iff_needs_canonical :
    (1 : ℕ) • emb junkFrame = 0 ∧ affineSmul fpOps 1 junkPair ≠ (0, 0) := by
  refine ⟨?_, ?_⟩
  · have hz : emb junkFrame = 0 := emb_inf junkFrame (by decide)
    rw [hz]
    exact nsmul_zero _
  · intro hh
    have e : affineSmul fpOps 1 junkPair = junkPair := by decide
    rw [e] at hh
    exact absurd hh (by decide)

set_option maxRecDepth 100000 in
/-- **AND THE MEASURED LIMIT OF THAT FALSIFICATION, recorded rather than hidden.** At the ACTUAL
    scalar \`blsR\` the equivalence happens to survive the junk frame: \`g1InSubgroup junkPair =
    true\`, and the reason is visible - \`blsR\` has more than one set bit, so the second set bit
    re-runs the copy branch and flushes the accumulator to the literal \`(0, 0)\`. So canonicity is
    SUFFICIENT for \`g1InSubgroup_iff\` and NOT necessary at this particular scalar. The honest claim
    is "the hypothesis is used by the proof and is refutable at \`n = 1\`", not "the statement is
    false without it". -/
theorem g1InSubgroup_junkFrame : g1InSubgroup junkPair = true := by decide


/-! ### What the walk makes statable: the first prime-order exhibit at a real curve point -/

/-- **THE CYCLIC SUBGROUP GENERATED BY THE PUBLISHED GENERATOR HAS PRIME ORDER \`r\`.** This is the
    \`PrimeOrderWith\` requirement of \`Eip2537.Holds\` discharged at a REAL curve point, and it is
    \`primeOrderWith_zpowers\` in one line now that \`blsR • emb genFrame = 0\` exists: the two
    hypotheses are \`r • G = 0\` (the \`decide\` above, transported) and \`G ≠ 0\`
    (\`emb_gen_ne_zero\`). Nothing here is a point count - \`Nat.card_zpowers\` and
    \`orderOf_eq_prime\` do the work, exactly as P-HOLDS2 predicted.

    TWO NAMING FINDINGS, measured rather than inherited. (1) The additive cyclic subgroup in this
    mathlib revision is \`AddSubgroup.zmultiples\`, NOT \`AddSubgroup.zsmulSet\` (zero hits for
    \`zsmulSet\` and for \`zsmuls\` across the whole mathlib tree) - the brief's "naming task, not a
    blocker" is right, and this is the name. (2) Even with the right name the carrier has to be
    \`Multiplicative\`-wrapped, because \`PrimeOrderWith\` is stated for a \`Group\` and mathlib has
    NO \`Group (Additive A)\` instance for an additive group \`A\` here (\`#check\` of
    \`Group (Additive (ZMod 5))\` fails to synthesize, while
    \`Group (Multiplicative (AddSubgroup.zmultiples (emb genFrame)))\` synthesizes). So the exhibit
    is a subgroup of \`Multiplicative W.Point\`, not of \`W.Point\`. -/
theorem primeOrderWith_zpowers_emb_genFrame :
    PrimeOrderWith (Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) blsR :=
  primeOrderWith_zpowers (Multiplicative.ofAdd (emb genFrame))
    (by show Multiplicative.ofAdd (blsR • emb genFrame) = Multiplicative.ofAdd 0
        rw [r_nsmul_emb_genFrame])
    (fun h => emb_gen_ne_zero (show emb genFrame = 0 from h))

/-- The cardinality half on its own, since that is the form \`Holds\` consumes: \`Nat.card G₁ = r\`. -/
theorem natCard_zpowers_emb_genFrame :
    Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) = blsR :=
  primeOrderWith_zpowers_emb_genFrame.hCard

/-- **WITNESS FOR THE EXHIBIT (D-P23 satisfiability).** The carrier is not the trivial group: it
    contains the generator, and its cardinality is not 1. Without \`emb_gen_ne_zero\` the whole
    construction collapses to \`zpowers 1\`, which \`zpowers_one_not_prime_order\` in
    \`Assumptions/Eip2537.lean\` already refutes - so the nontriviality is load-bearing here too. -/
theorem zpowers_emb_gen_nontrivial :
    Multiplicative.ofAdd (emb genFrame) ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame)) ∧
      Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) ≠ 1 :=
  ⟨Subgroup.mem_zpowers _, fun hh =>
    Nat.Prime.ne_one (Fact.out : Nat.Prime blsR) (natCard_zpowers_emb_genFrame.symm.trans hh)⟩

/-! ### P-G1CODEC: THE BYTE CODEC ROUND TRIP

**THE CHAIN LANDED, ALL FOUR LINKS.** P-CANON scoped this as "byte plumbing, not the canonicity
wall" and named three matcher obstacles with their causes. RE-VERDICT, each one measured here:

1. `ofLowDigits_append` fires on the wrong occurrence once the RHS is in `bytesToNatBE` form -
   **CONFIRMED, and the cure is to never rewrite the goal at all.** `bytesToNatBE_bytesAppend` is
   proved by converting ALL THREE sides (`A`, `B`, `A ++ B`) into `ofLowDigits` form as named
   `have`s first, rewriting the ofLowDigits-level equation, and converting back with `← hB, ← hA`.
2. `bytesTake_whole` needs `@ByteArray.size_data` to state its hypothesis - **WRONG IN ITS
   SPECIFICS.** `bytesTake b 0 b.size = some b` needs NO hypothesis. What does not work is
   `rw [Array.extract_eq_self_of_le ...]`: that lemma's array AND its bound are both implicit, so
   the matcher sees `Array.extract ?m` with nothing to match on. The cure is to supply it as a
   term: `@Array.extract_eq_self_of_le UInt8 (ByteArray.size b) b.data (Nat.le_refl _)` - the
   ascribe-the-type trick again, in a second guise.
3. The slice side conditions must be stated against `ByteArray.size A` because
   `Array.extract_append` inserts its own `min` - **CONFIRMED.** The window lemmas below take
   `i + n ≤ A.size` and `o = A.size` at the `Bytes` level and enter `.data` exactly once.

ONE NEW WALL, NOT IN P-CANON'S LIST: **`g1PointMsmValid P` for a VARIABLE `P` cannot be whnf'd at
all.** `dsimp` of the match in `g1MsmOutput` forces `List.all [(P, s)] f`, which forces
`g1PointMsmValid P`, which forces `affineSmul fpOps blsR P == (0, 0)` - the 255-step fold, on a
variable. Same pair-`==` wall as P-CANON, reached through a `List.all` instead of a `show`. The
cure is the same shape: **generalise.** `g1MsmOutput_some` takes the decoded list as a VARIABLE
`ps` with `g1MsmPairs? input = some ps` as a hypothesis, so nothing is instantiated at a literal
list and the `all` stays stuck - which is what makes it rewritable. -/

/-- The base modulus fits in `fpBytes` bytes: 381 bits inside 48 (= 384). -/
private theorem blsP_lt_fpBytes_pow : blsP < 256 ^ fpBytes := by decide

private theorem bytesAppend_size (A B : Bytes) :
    (bytesAppend A B).size = A.size + B.size := by
  show (A.data ++ B.data).size = _
  exact Array.size_append

private theorem bytesZero_size (n : Nat) : (bytesZero n).size = n := by
  show ((List.replicate n 0).toArray).size = n
  rw [Array.size_eq_length_toList, List.toList_toArray, List.length_replicate]

/-- Reading a concatenation big-endian: the RIGHT operand sits in the low positions and the LEFT
    one is shifted past it. This is the equation P-CANON could not get `ofLowDigits_append` to
    produce. -/
theorem bytesToNatBE_bytesAppend (A B : Bytes) :
    bytesToNatBE (bytesAppend A B) =
      bytesToNatBE B + 256 ^ B.size * bytesToNatBE A := by
  have hA : bytesToNatBE A = ofLowDigits 256 (A.data.toList.map UInt8.toNat).reverse :=
    bytesToNatBE_eq_ofLowDigits_reverse A
  have hB : bytesToNatBE B = ofLowDigits 256 (B.data.toList.map UInt8.toNat).reverse :=
    bytesToNatBE_eq_ofLowDigits_reverse B
  have hAB : bytesToNatBE (bytesAppend A B)
      = ofLowDigits 256 ((A.data.toList ++ B.data.toList).map UInt8.toNat).reverse := by
    rw [bytesToNatBE_eq_ofLowDigits_reverse]
    show ofLowDigits 256 (((A.data ++ B.data).toList).map UInt8.toNat).reverse = _
    rw [Array.toList_append]
  have hlen : ((B.data.toList.map UInt8.toNat).reverse).length = B.size := by
    rw [List.length_reverse, List.length_map, Array.length_toList, ByteArray.size_data]
  rw [hAB, List.map_append, List.reverse_append, ofLowDigits_append, ← hB, ← hA, hlen]

/-- The EIP-2537 pad reads as zero - which is why canonicity subsumes the padding test. -/
theorem bytesToNatBE_eipPad : bytesToNatBE eipPad = 0 := rfl

/-- A padded coordinate is exactly `fpPadBytes + fpBytes = 64` bytes, whatever the value. -/
theorem fpCoordBytes_size (x : Nat) : (fpCoordBytes x).size = fpPadBytes + fpBytes := by
  show (bytesAppend eipPad (bytesNatBE x fpBytes)).size = _
  rw [bytesAppend_size, bytesNatBE_size]
  have h : eipPad.size = fpPadBytes := rfl
  rw [h]

/-- **THE COORDINATE ROUND TRIP, VALUE HALF.** The pad contributes `256 ^ 48 * 0` and the body is
    `x % 256 ^ 48 = x` because `x < blsP < 256 ^ 48`. -/
theorem bytesToNatBE_fpCoordBytes (x : Nat) (hx : x < blsP) :
    bytesToNatBE (fpCoordBytes x) = x := by
  have h : bytesToNatBE (fpCoordBytes x)
      = bytesToNatBE (bytesNatBE x fpBytes)
          + 256 ^ (bytesNatBE x fpBytes).size * bytesToNatBE eipPad := by
    show bytesToNatBE (bytesAppend eipPad (bytesNatBE x fpBytes)) = _
    rw [bytesToNatBE_bytesAppend]
  have hlt : x < 256 ^ fpBytes := Nat.lt_of_lt_of_le hx (Nat.le_of_lt blsP_lt_fpBytes_pow)
  rw [h, bytesNatBE_size, bytesToNatBE_eipPad, Nat.mul_zero, Nat.add_zero,
    bytesToNatBE_bytesNatBE, Nat.mod_eq_of_lt hlt]

/-- Taking the whole buffer is the identity - with NO hypothesis; see header note 2 for what this
    actually needed. -/
theorem bytesTake_of_size (b : Bytes) : bytesTake b 0 b.size = some b := by
  classical
  unfold bytesTake
  rw [if_pos (by rw [Nat.zero_add])]
  rw [Nat.zero_add]
  have key : b.data.extract 0 (ByteArray.size b) = b.data :=
    @Array.extract_eq_self_of_le UInt8 (ByteArray.size b) b.data (Nat.le_refl _)
  rw [key]

/-- **THE COORDINATE ROUND TRIP, DECODER HALF.** -/
theorem fpCoordOf?_fpCoordBytes (x : Nat) (hx : x < blsP) :
    fpCoordOf? (fpCoordBytes x) = some x := by
  classical
  unfold fpCoordOf?
  have hs : (fpCoordBytes x).size = fpPadBytes + fpBytes := fpCoordBytes_size x
  have htake : bytesTake (fpCoordBytes x) 0 (fpPadBytes + fpBytes) = some (fpCoordBytes x) := by
    rw [← hs]; exact bytesTake_of_size _
  rw [htake]
  dsimp only
  rw [bytesToNatBE_fpCoordBytes x hx, if_pos hx]

/-- **AND ITS CONTRADICTORY:** a coordinate at or above the modulus encodes but never decodes.
    This is the half the round trip's falsification rests on. -/
theorem fpCoordOf?_fpCoordBytes_none_of_too_big (x : Nat) (hx : ¬ (x < blsP))
    (hxb : x < 256 ^ fpBytes) : fpCoordOf? (fpCoordBytes x) = none := by
  classical
  unfold fpCoordOf?
  have hs : (fpCoordBytes x).size = fpPadBytes + fpBytes := fpCoordBytes_size x
  have htake : bytesTake (fpCoordBytes x) 0 (fpPadBytes + fpBytes) = some (fpCoordBytes x) := by
    rw [← hs]; exact bytesTake_of_size _
  rw [htake]
  show (if bytesToNatBE (fpCoordBytes x) < blsP
        then some (bytesToNatBE (fpCoordBytes x)) else none) = none
  have heq : bytesToNatBE (fpCoordBytes x) = x := by
    show bytesToNatBE (bytesAppend eipPad (bytesNatBE x fpBytes)) = _
    rw [bytesToNatBE_bytesAppend, bytesNatBE_size, bytesToNatBE_eipPad, Nat.mul_zero,
      Nat.add_zero, bytesToNatBE_bytesNatBE, Nat.mod_eq_of_lt hxb]
  rw [if_neg (fun hh => hx (heq ▸ hh))]

/-! #### Slice windows over a concatenation -/

theorem bytesSlice_at (bs : Bytes) (i n : Nat) (h : i + n ≤ bs.size) :
    bytesSlice bs i n = ByteArray.mk (bs.data.extract i (i + n)) := by
  classical
  show ByteArray.mk (bs.data.extract (min i bs.size) (min (i + n) bs.size)) = _
  rw [Nat.min_eq_left (by omega : i ≤ bs.size), Nat.min_eq_left (by omega : i + n ≤ bs.size)]

/-- A window that fits has exactly the requested width: the clamp is inert inside the buffer. -/
theorem bytesSlice_size {bs : Bytes} (i n : Nat) (h : i + n ≤ bs.size) :
    (bytesSlice bs i n).size = n := by
  rw [bytesSlice_at _ _ _ h]
  show (bs.data.extract i (i + n)).size = n
  have h2 : i + n ≤ bs.data.size := h
  rw [Array.size_extract, Nat.min_eq_left h2, Nat.add_sub_cancel_left]

theorem bytesSlice_full (A : Bytes) : bytesSlice A 0 A.size = A := by
  classical
  rw [bytesSlice_at _ 0 A.size (by omega), Nat.zero_add]
  show ByteArray.mk (A.data.extract 0 A.data.size) = A
  rw [Array.extract_eq_self_of_le (Nat.le_refl _)]

/-- A window inside the LEFT half of a concatenation is a window of the left half. -/
theorem bytesSlice_window_before {A B : Bytes} (i n : Nat) (h : i + n ≤ A.size) :
    bytesSlice (bytesAppend A B) i n = bytesSlice A i n := by
  classical
  rw [bytesSlice_at _ _ _ (by rw [bytesAppend_size]; omega), bytesSlice_at _ _ _ h]
  show ByteArray.mk ((A.data ++ B.data).extract i (i + n)) = ByteArray.mk (A.data.extract i (i + n))
  rw [Array.extract_append]
  have hz : B.data.extract (i - A.data.size) (i + n - A.data.size) = #[] := by
    refine Array.extract_eq_empty_of_le ?_
    have h1 : i - A.data.size = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_add_right i n) (by exact_mod_cast h))
    have h2 : i + n - A.data.size = 0 := Nat.sub_eq_zero_of_le (by exact_mod_cast h)
    rw [h1, h2]
    exact Nat.min_le_left _ _
  rw [hz, Array.append_empty]

/-- A window that starts where the LEFT half ends is a window of the right half. -/
theorem bytesSlice_window_after {A B : Bytes} (o n : Nat) (ho : o = A.size) (h : n ≤ B.size) :
    bytesSlice (bytesAppend A B) o n = bytesSlice B 0 n := by
  classical
  rw [ho]
  rw [bytesSlice_at _ _ _ (by rw [bytesAppend_size]; omega),
      bytesSlice_at _ _ _ (by rw [Nat.zero_add]; exact h)]
  rw [Nat.zero_add]
  show ByteArray.mk ((bytesAppend A B).data.extract (ByteArray.size A) (ByteArray.size A + n)) =
    ByteArray.mk (B.data.extract 0 n)
  rw [show (bytesAppend A B).data = A.data ++ B.data from rfl,
    show ByteArray.size A = A.data.size from rfl]
  rw [Array.extract_append]
  rw [Array.extract_eq_empty_of_le (Nat.min_le_right _ _), Nat.sub_self,
    Nat.add_sub_cancel_left, Array.empty_append]

theorem bytesTake_window_before {A B : Bytes} (i n : Nat) (h : i + n ≤ A.size) :
    bytesTake (bytesAppend A B) i n = bytesTake A i n := by
  classical
  unfold bytesTake
  rw [if_pos (by rw [bytesAppend_size]; omega), if_pos h]
  show some (ByteArray.mk ((A.data ++ B.data).extract i (i + n))) =
    some (ByteArray.mk (A.data.extract i (i + n)))
  rw [Array.extract_append]
  have hz : B.data.extract (i - A.data.size) (i + n - A.data.size) = #[] := by
    refine Array.extract_eq_empty_of_le ?_
    have h1 : i - A.data.size = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.le_add_right i n) (by exact_mod_cast h))
    have h2 : i + n - A.data.size = 0 := Nat.sub_eq_zero_of_le (by exact_mod_cast h)
    rw [h1, h2]
    exact Nat.min_le_left _ _
  rw [hz, Array.append_empty]

theorem bytesTake_window_after {A B : Bytes} (o n : Nat) (ho : o = A.size) (h : n ≤ B.size) :
    bytesTake (bytesAppend A B) o n = bytesTake B 0 n := by
  classical
  rw [ho]
  unfold bytesTake
  rw [if_pos (by rw [bytesAppend_size]; omega), if_pos (by rw [Nat.zero_add]; exact h)]
  show some (ByteArray.mk ((bytesAppend A B).data.extract (ByteArray.size A)
      (ByteArray.size A + n))) = some (ByteArray.mk (B.data.extract 0 (0 + n)))
  rw [show (bytesAppend A B).data = A.data ++ B.data from rfl,
      show ByteArray.size A = A.data.size from rfl]
  rw [Nat.zero_add, Array.extract_append]
  rw [Array.extract_eq_empty_of_le (Nat.min_le_right _ _), Nat.sub_self,
    Nat.add_sub_cancel_left, Array.empty_append]

/-! #### LINKS 1 AND 2: the two slice equations and the round trip -/

/-- **SLICE EQUATION 1 OF 2**: the first 64 bytes of a 128-byte G1 encoding are the `x`
    coordinate's padded encoding. -/
theorem bytesSlice_g1PointBytes_left (P : Nat × Nat) :
    bytesSlice (g1PointBytes P) 0 64 = fpCoordBytes P.1 := by
  classical
  have hs : (fpCoordBytes P.1).size = 64 := by
    rw [fpCoordBytes_size]; rfl
  rw [show g1PointBytes P = bytesAppend (fpCoordBytes P.1) (fpCoordBytes P.2) from rfl,
      bytesSlice_window_before 0 64 (by rw [hs]), ← hs, bytesSlice_full]

/-- **SLICE EQUATION 2 OF 2**: the second 64 bytes are the `y` coordinate's. -/
theorem bytesSlice_g1PointBytes_right (P : Nat × Nat) :
    bytesSlice (g1PointBytes P) 64 64 = fpCoordBytes P.2 := by
  classical
  have hs : (fpCoordBytes P.1).size = 64 := by rw [fpCoordBytes_size]; rfl
  have ht : (fpCoordBytes P.2).size = 64 := by rw [fpCoordBytes_size]; rfl
  rw [show g1PointBytes P = bytesAppend (fpCoordBytes P.1) (fpCoordBytes P.2) from rfl,
      bytesSlice_window_after 64 64 hs.symm (Nat.le_of_eq ht.symm), ← ht, bytesSlice_full]

/-- **LINK 1, THE ROUND TRIP ITSELF.** The decoder reads back what the encoder wrote, for every
    canonically-encodable point. Four rewrites once the slice equations are on the table. -/
theorem g1Of?_g1PointBytes (P : Nat × Nat) (hx : P.1 < blsP) (hy : P.2 < blsP) :
    g1Of? (g1PointBytes P) = some P := by
  classical
  unfold g1Of?
  rw [bytesSlice_g1PointBytes_left, bytesSlice_g1PointBytes_right,
      fpCoordOf?_fpCoordBytes P.1 hx, fpCoordOf?_fpCoordBytes P.2 hy]

/-- **WITNESS FOR THE ROUND TRIP (D-P23 satisfiability)**, at the PUBLISHED generator: the
    encoder-decoder pair round-trips on a point nobody chose. -/
theorem g1Of?_g1PointBytes_genPair : g1Of? (g1PointBytes genPair) = some genPair :=
  g1Of?_g1PointBytes genPair (by decide) (by decide)

/-- **FALSIFICATION FOR THE ROUND TRIP (D-P23): the canonicity hypothesis is load-bearing.**
    `blsP` is not below `blsP`, so the decoder refuses the encoding of the junk pair even though
    the encoder writes it happily. -/
theorem g1Of?_g1PointBytes_needs_canonical : g1Of? (g1PointBytes junkPair) = none := by
  classical
  show g1Of? (g1PointBytes (blsP, blsP)) = none
  unfold g1Of?
  rw [bytesSlice_g1PointBytes_left, bytesSlice_g1PointBytes_right,
      fpCoordOf?_fpCoordBytes_none_of_too_big blsP (Nat.lt_irrefl blsP)
        blsP_lt_fpBytes_pow]

/-- A G1 encoding is exactly `g1Bytes = 128` bytes, for every point. -/
theorem g1PointBytes_size (P : Nat × Nat) : (g1PointBytes P).size = g1Bytes := by
  show (bytesAppend (fpCoordBytes P.1) (fpCoordBytes P.2)).size = _
  rw [bytesAppend_size, fpCoordBytes_size, fpCoordBytes_size]
  rfl

/-! #### LINK 3: `g1AddValidInput` and `g1AddOutput` unfold -/

private theorem bytesSlice_g1AddFrame_left (P Q : Nat × Nat) :
    bytesSlice (g1AddFrame (g1PointBytes P) (g1PointBytes Q)) 0 g1Bytes = g1PointBytes P := by
  classical
  have hs : (g1PointBytes P).size = g1Bytes := g1PointBytes_size P
  rw [show g1AddFrame (g1PointBytes P) (g1PointBytes Q)
        = bytesAppend (g1PointBytes P) (g1PointBytes Q) from rfl,
      bytesSlice_window_before 0 g1Bytes (by rw [hs]; omega), ← hs, bytesSlice_full]

private theorem bytesSlice_g1AddFrame_right (P Q : Nat × Nat) :
    bytesSlice (g1AddFrame (g1PointBytes P) (g1PointBytes Q)) g1Bytes g1Bytes
      = g1PointBytes Q := by
  classical
  have hs : (g1PointBytes P).size = g1Bytes := g1PointBytes_size P
  have ht : (g1PointBytes Q).size = g1Bytes := g1PointBytes_size Q
  rw [show g1AddFrame (g1PointBytes P) (g1PointBytes Q)
        = bytesAppend (g1PointBytes P) (g1PointBytes Q) from rfl,
      bytesSlice_window_after g1Bytes g1Bytes hs.symm (Nat.le_of_eq ht.symm), ← ht,
      bytesSlice_full]

private theorem g1AddFrame_size_beq (P Q : Nat × Nat) :
    ((g1AddFrame (g1PointBytes P) (g1PointBytes Q)).size == g1AddInputBytes) = true := by
  show ((bytesAppend (g1PointBytes P) (g1PointBytes Q)).size == g1AddInputBytes) = true
  rw [bytesAppend_size, g1PointBytes_size, g1PointBytes_size]
  decide

/-- **`g1AddValidInput`, ON CODEC-EMITTED FRAMES, IS THE VALIDATOR OF THE POINTS.** -/
theorem g1AddValidInput_g1PointBytes (P Q : Nat × Nat)
    (hx : P.1 < blsP) (hy : P.2 < blsP) (hx' : Q.1 < blsP) (hy' : Q.2 < blsP) :
    g1AddValidInput (g1AddFrame (g1PointBytes P) (g1PointBytes Q))
      = (g1PointAddValid P && g1PointAddValid Q) := by
  classical
  unfold g1AddValidInput
  rw [g1AddFrame_size_beq, Bool.true_and, bytesSlice_g1AddFrame_left,
      bytesSlice_g1AddFrame_right, g1Of?_g1PointBytes P hx hy, g1Of?_g1PointBytes Q hx' hy']

/-- **`g1AddOutput` ON CODEC-EMITTED FRAMES IS `g1PointBytes` OF THE BYTE SUM** - the right-hand
    side of the `g1Add` clause, one step short of the group law. -/
theorem g1AddOutput_g1PointBytes (P Q : Nat × Nat)
    (hx : P.1 < blsP) (hy : P.2 < blsP) (hx' : Q.1 < blsP) (hy' : Q.2 < blsP)
    (hP : g1PointAddValid P = true) (hQ : g1PointAddValid Q = true) :
    g1AddOutput (g1AddFrame (g1PointBytes P) (g1PointBytes Q))
      = some (g1PointBytes (affineAdd fpOps P Q)) := by
  classical
  unfold g1AddOutput
  rw [bytesSlice_g1AddFrame_left, bytesSlice_g1AddFrame_right,
      g1Of?_g1PointBytes P hx hy, g1Of?_g1PointBytes Q hx' hy']
  have hv : g1AddValidInput (g1AddFrame (g1PointBytes P) (g1PointBytes Q)) = true := by
    rw [g1AddValidInput_g1PointBytes P Q hx hy hx' hy', hP, hQ]
    rfl
  rw [hv]
  rfl

/-- **FALSIFICATION FOR THE G1ADD UNFOLDING (D-P23): the length conjunct is load-bearing.** The
    full 0x100 frame is accepted; the SAME two points truncated to 255 bytes are refused - and
    `bytesSlice` clamps rather than failing, so a validator that only looked at coordinates would
    accept the short frame too. -/
theorem g1AddValidInput_needs_the_length :
    g1AddValidInput (g1AddFrame (g1PointBytes genPair) (g1PointBytes genPair)) = true ∧
      g1AddValidInput (bytesSlice
        (g1AddFrame (g1PointBytes genPair) (g1PointBytes genPair)) 0 255) = false := by
  refine ⟨?_, ?_⟩
  · rw [g1AddValidInput_g1PointBytes genPair genPair (by decide) (by decide) (by decide)
      (by decide)]
    rfl
  · have h : (bytesSlice (g1AddFrame (g1PointBytes genPair) (g1PointBytes genPair)) 0 255).size
        = 255 := bytesSlice_size 0 255 (by
          show (0 : Nat) + 255 ≤
            ByteArray.size (bytesAppend (g1PointBytes genPair) (g1PointBytes genPair))
          rw [bytesAppend_size, g1PointBytes_size]
          unfold g1Bytes
          omega)
    unfold g1AddValidInput
    rw [h]
    decide

/-! #### LINK 4: the `where`-clause function `g1MsmPairs?.go` -/

set_option maxRecDepth 100000 in
private theorem natToBytesBE_size (n len : Nat) : (natToBytesBE n len).size = len := by
  show ((natToBytesLowFirst n len).data.toList.reverse.toArray).size = len
  simp [List.length_reverse, Midfall.Assumptions.natToBytesLowFirst_size]

private theorem frToInputBE_size (x : Fr blsR) : (frToInputBE x).size = frBytes := by
  show (natToBytesBE x.val 32).size = frBytes
  rw [natToBytesBE_size]
  rfl

/-- The scalar slot reads back as the scalar's canonical value: `frToInputBE` is 32 bytes and
    `r < 2 ^ 256`, so no truncation happens - the fact that makes the `g1Msm1` clause's
    "canonical word" wording load-bearing rather than decorative. -/
theorem bytesToNatBE_frToInputBE (x : Fr blsR) : bytesToNatBE (frToInputBE x) = x.val := by
  show bytesToNatBE (natToBytesBE x.val 32) = x.val
  rw [bytesToNatBE_natToBytesBE, Nat.mod_eq_of_lt]
  have h2 : blsR < 256 ^ (32 : Nat) := by show blsR < 2 ^ 256; decide
  exact Nat.lt_of_lt_of_le (ZMod.val_lt x) (Nat.le_of_lt h2)

private theorem g1MsmFrame_singleton (p sc : Bytes) :
    g1MsmFrame [(p, sc)] = bytesAppend p sc := by
  show bytesAppend Bytes.empty (bytesAppend p sc) = _
  rw [show bytesAppend Bytes.empty (bytesAppend p sc) = bytesAppend p sc from by
    show ByteArray.mk ((#[] : Array UInt8) ++ (bytesAppend p sc).data) = _
    rw [Array.empty_append]]

/-- **LINK 4, THE `where`-CLAUSE FUNCTION.** P-CANON did not attempt this and told the next package
    to budget for it; it needed no budget. The compiler exposes the clauses as
    `g1MsmPairs?.go.eq_1` and `.eq_2`, both `rfl`-level, so the one-pair frame unfolds in a dozen
    lines once the `bytesTake` windows and the round trip are available. The `dsimp only` between
    the rewrites is what fires each `match` - `rw` does not reduce a `match`. -/
theorem g1MsmPairs?_singleton (P : Nat × Nat) (s : Fr blsR)
    (hx : P.1 < blsP) (hy : P.2 < blsP) :
    g1MsmPairs? (g1MsmFrame [(g1PointBytes P, frToInputBE s)]) = some [((P, s.val))] := by
  classical
  rw [g1MsmFrame_singleton]
  have hsz : (bytesAppend (g1PointBytes P) (frToInputBE s)).size = g1MsmPairBytes := by
    rw [bytesAppend_size, g1PointBytes_size, frToInputBE_size]
    rfl
  unfold g1MsmPairs?
  rw [if_neg (by rw [hsz]; decide), hsz]
  have hdiv : g1MsmPairBytes / g1MsmPairBytes = 1 := by decide
  rw [hdiv, g1MsmPairs?.go.eq_2]
  have t1 : bytesTake (bytesAppend (g1PointBytes P) (frToInputBE s)) 0 g1Bytes
      = some (g1PointBytes P) := by
    rw [bytesTake_window_before 0 g1Bytes (by rw [g1PointBytes_size]; omega),
        ← g1PointBytes_size, bytesTake_of_size]
  have t2 : bytesTake (bytesAppend (g1PointBytes P) (frToInputBE s)) (0 + g1Bytes) frBytes
      = some (frToInputBE s) := by
    rw [Nat.zero_add, bytesTake_window_after g1Bytes frBytes
        ((g1PointBytes_size P).symm) (by rw [frToInputBE_size]),
        ← frToInputBE_size, bytesTake_of_size]
  rw [t1, t2]
  dsimp only
  rw [g1Of?_g1PointBytes P hx hy, bytesToNatBE_frToInputBE s]
  dsimp only
  rw [g1MsmPairs?.go.eq_1]
  rfl

/-- **THE `g1MsmOutput` TRANSFER, STATED OVER A VARIABLE LIST.** Forced, not stylistic - see the
    header: a literal list makes the elaborator evaluate `g1PointMsmValid` on a variable point. -/
theorem g1MsmOutput_some {input : Bytes} {ps : List ((Nat × Nat) × Nat)}
    (h : g1MsmPairs? input = some ps)
    (hall : ps.all (fun pr => g1PointMsmValid pr.1) = true) :
    g1MsmOutput input =
      some (g1PointBytes (ps.foldl (fun (acc : Nat × Nat) (pr : (Nat × Nat) × Nat) =>
        affineAdd fpOps acc (affineSmul fpOps pr.2 pr.1)) (0, 0))) := by
  classical
  unfold g1MsmOutput
  rw [h]
  dsimp only
  rw [hall, if_pos rfl]

private theorem addFrame_val (P Q : FpFrame) :
    (addFrame P Q).1 = affineAdd fpOps P.1 Q.1 := rfl

private theorem affineAdd_inf_left (Q : Nat × Nat) : affineAdd fpOps (0, 0) Q = Q := by
  rw [affineAdd, if_pos (by decide)]

/-- **THE ONE-PAIR MSM OUTPUT.** -/
theorem g1MsmOutput_singleton (P : Nat × Nat) (s : Fr blsR) (hx : P.1 < blsP) (hy : P.2 < blsP)
    (hv : g1PointMsmValid P = true) :
    g1MsmOutput (g1MsmFrame [(g1PointBytes P, frToInputBE s)])
      = some (g1PointBytes (affineSmul fpOps s.val P)) := by
  classical
  have hall : ([(P, s.val)] : List ((Nat × Nat) × Nat)).all
      (fun pr => g1PointMsmValid pr.1) = true := by
    rw [List.all_cons, List.all_nil, hv, Bool.and_true]
  rw [g1MsmOutput_some (ps := [(P, s.val)]) (g1MsmPairs?_singleton P s hx hy) hall]
  show some (g1PointBytes (affineAdd fpOps (0, 0) (affineSmul fpOps s.val P))) = _
  rw [affineAdd_inf_left]

/-- **FALSIFICATION FOR THE MSM UNFOLDING (D-P23): the pair-length discipline is real.** The
    160-byte frame parses as one pair; the SAME frame with one trailing byte is refused by the
    `% g1MsmPairBytes` test before `go` ever runs. -/
theorem g1MsmPairs?_needs_whole_pairs :
    (g1MsmPairs? (g1MsmFrame [(g1PointBytes genPair, frToInputBE (1 : Fr blsR))])).isSome ∧
      (g1MsmPairs? (bytesAppend (g1MsmFrame
        [(g1PointBytes genPair, frToInputBE (1 : Fr blsR))]) (bytesZero 1))).isNone := by
  refine ⟨?_, ?_⟩
  · rw [g1MsmPairs?_singleton genPair 1 (by decide) (by decide)]
    decide
  · have hsz : (bytesAppend (g1MsmFrame [(g1PointBytes genPair, frToInputBE (1 : Fr blsR))])
        (bytesZero 1)).size = 161 := by
      rw [bytesAppend_size, g1MsmFrame_singleton, bytesAppend_size, g1PointBytes_size,
        frToInputBE_size]
      rfl
    have hcond : ((161 : Nat) == 0 || 161 % g1MsmPairBytes != 0) = true := by decide
    have hnone : g1MsmPairs? (bytesAppend (g1MsmFrame
        [(g1PointBytes genPair, frToInputBE (1 : Fr blsR))]) (bytesZero 1)) = none := by
      unfold g1MsmPairs?
      rw [hsz, if_pos hcond]
    rw [hnone]
    decide


/-! ### P-G1CODEC: THE G1Codec ON THE `zpowers` CARRIER

**THE SECOND MISSING PIECE, AND WHY THE ROUND TRIP ALONE WAS NOT ENOUGH.** P-CANON named this
explicitly: canonicity + point count does NOT give five of six; it is canonicity (done) + point
count + codec round trip (done above) + **a codec on a carrier that can be plugged into `Holds`**.
The carrier has to be a `Group` with `PrimeOrderWith` and a `Module (ZMod r)` on its additive form,
and the only real-curve object in the tree with all three is the cyclic subgroup generated by the
published H1, whose prime order P-CANON established (`primeOrderWith_zpowers_emb_genFrame`).

THREE SPELLING FINDINGS, measured here rather than inherited:

* `Point.toAffine` **does not exist** in this mathlib revision (zero hits under
  AlgebraicGeometry/EllipticCurve/). The point-to-coordinates map is a two-line `match` on the
  `Point` inductive, and the canonicality the brief wanted from `ZMod.val` is exactly `ZMod.val_lt`:
  a coordinate read out through `val` is BELOW `blsP` by construction, so the round trip applies
  with nothing left to discharge.
* `Module (ZMod blsR) (Additive G₁z)` does NOT synthesize. It is built from
  `AddCommGroup.zmodModule`, whose hypothesis - `∀ x, r • x = 0` - is the exponent fact the carrier
  gets from `r • emb genFrame = 0`. So `g1Msm1` is statable at all only because P-CANON landed
  `r_nsmul_emb_genFrame`.
* **`blsR • X` for a VARIABLE `X : W.Point` cannot be whnf'd** - `nsmul` recurses on the literal
  255-bit scalar, and any `rfl` / `show` / `rw`-motive that forces it dies at the default
  `maxRecDepth`. That is the same shape as the `affineSmul` fold wall, on the mathlib side rather
  than the byte side, and it is why `nsmul_blsR_eq_zero` below goes through the propositional
  `toAdd_pow` instead of the one-line `rfl` that looks correct. -/

/-- **THE CARRIER.** The cyclic subgroup generated by the published H1, multiplicatively wrapped so
    that `Group` synthesizes (P-CANON's naming finding: `Group (Additive A)` does not). -/
abbrev G₁z : Type := Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))

instance primeOrderZ : PrimeOrderWith G₁z blsR := primeOrderWith_zpowers_emb_genFrame

theorem zpow_gen_blsR : (Multiplicative.ofAdd (emb genFrame)) ^ blsR = 1 :=
  show Multiplicative.ofAdd (blsR • emb genFrame) = Multiplicative.ofAdd 0 from
    congrArg Multiplicative.ofAdd r_nsmul_emb_genFrame

/-- **EVERY ELEMENT OF THE CARRIER IS `r`-TORSION, multiplicatively.** `Subgroup.mem_zpowers_iff`
    answers with an INTEGER exponent, so the calculation lives in `zpow`:
    `(g ^ n) ^ r = g ^ (n * r) = g ^ (r * n) = (g ^ r) ^ n = 1`. -/
theorem pow_blsR_eq_one_ambient (x : Multiplicative W.Point)
    (hx : x ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) : x ^ blsR = 1 := by
  classical
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  subst hn
  rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast, zpow_gen_blsR, one_zpow]

theorem pow_blsR_eq_one (x : G₁z) : x ^ blsR = 1 := by
  rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_blsR_eq_one_ambient x x.prop

/-- **THE `ZMod r` MODULE STRUCTURE THE `g1Msm1` CLAUSE NEEDS.** Not an instance mathlib finds on
    its own: `AddCommGroup.zmodModule` is an `abbrev` taking the exponent law as an argument, and
    that argument is `pow_blsR_eq_one`. -/
instance moduleZ : Module (ZMod blsR) (Additive G₁z) :=
  AddCommGroup.zmodModule (fun y : Additive G₁z => by
    apply Additive.ext
    show (y.toMul : G₁z) ^ blsR = 1
    exact pow_blsR_eq_one y.toMul)

/-- **A CURVE POINT AS A CANONICAL COORDINATE PAIR** - the map the brief asked for. `Point.toAffine`
    does not exist in this revision, so this is a `match` on the inductive; the infinity point maps
    to the all-zero frame, matching `emb`'s convention exactly. -/
def ptPair (X : W.Point) : Nat × Nat :=
  match X with
  | 0 => (0, 0)
  | Point.some x y _ => (x.val, y.val)

theorem ptPair_zero : ptPair (0 : W.Point) = (0, 0) := rfl

theorem ptPair_some (x y : K) (h : W.Nonsingular x y) :
    ptPair (Point.some x y h) = (x.val, y.val) := rfl

/-- **THE `ptPair` IMAGE IS AN ACCEPTED FRAME**, in both branches. -/
theorem onCurve_ptPair (X : W.Point) : affineOnCurve fpOps (ptPair X) = true := by
  classical
  cases X with
  | zero => decide
  | some x y h =>
      rw [ptPair_some]
      have heq : W.Equation x y := h.1
      have h1 : (y : K) ^ 2 = (x : K) ^ 3 + 4 := by
        rw [W.equation_iff] at heq
        rw [a₁z, a₂z, a₃z, a₄z, a₆z] at heq
        have hy : (y : K) ^ 2 + (0 : K) * x * y + (0 : K) * y = (y : K) ^ 2 := by ring
        have hx : (x : K) ^ 3 + (0 : K) * x ^ 2 + (0 : K) * x + 4 = (x : K) ^ 3 + 4 := by ring
        rw [hy, hx] at heq
        exact heq
      have hx : ((x.val : ℕ) : K) = x := ZMod.natCast_zmod_val x
      have hy : ((y.val : ℕ) : K) = y := ZMod.natCast_zmod_val y
      refine onCurve_of_eq_pow x.val y.val ?_
      rw [hx, hy]
      exact h1

/-- **THE FRAME OF A CURVE POINT.** -/
def frameOf (X : W.Point) : FpFrame := ⟨ptPair X, onCurve_ptPair X⟩

theorem frameOf_val (X : W.Point) : (frameOf X).1 = ptPair X := rfl

/-- **`emb` AND `ptPair` ARE INVERSE ON THE LEFT.** Note the `have` with an ascribed type instead of
    `rw [emb_notInf _ hi]`: rewriting through `emb`'s dependent `if` builds a motive over the
    `Nonsingular` proof argument and is rejected as not type-correct - the exact obstruction
    P-MODEXP recorded for `Point.some`, arriving again from a different direction. -/
theorem emb_frameOf (X : W.Point) : emb (frameOf X) = X := by
  classical
  cases X with
  | zero => exact emb_inf _ (by decide)
  | some x y h =>
      have hx : ((x.val : ℕ) : K) = x := ZMod.natCast_zmod_val x
      have hy : ((y.val : ℕ) : K) = y := ZMod.natCast_zmod_val y
      have hns : W.Nonsingular ((x.val : ℕ) : K) ((y.val : ℕ) : K) := nonsingular_congr hx hy h
      have hi : ¬ affineIsInfinity fpOps (frameOf (Point.some x y h)).1 = true := by
        rw [frameOf_val, ptPair_some]; exact notInf_of_nonsingular x.val y.val hns
      have key : emb (frameOf (Point.some x y h)) =
          Point.some ((x.val : ℕ) : K) ((y.val : ℕ) : K)
            (nonsingular_of_equation (equation_of_frame (frameOf (Point.some x y h)) hi)) :=
        emb_notInf _ hi
      rw [key]
      exact point_some_eq hx hy _ h

/-- Every `ptPair` frame is canonical - the whole point of going through `ZMod.val`. -/
theorem canonical_frameOf (X : W.Point) : CanonicalFrame (frameOf X) := by
  cases X with
  | zero =>
      show (0 : Nat) < blsP ∧ (0 : Nat) < blsP
      exact ⟨p_pos, p_pos⟩
  | some x y h => exact ⟨ZMod.val_lt x, ZMod.val_lt y⟩

/-- **AND ON THE RIGHT**: reading coordinates back off an embedded CANONICAL frame is the identity.
    Canonicity is what makes this true - a frame whose coordinate is `blsP` embeds to the same
    point as one whose coordinate is `0`. Same canonicity wall P-CANON walked, arriving from the
    byte side. -/
theorem ptPair_emb (P : FpFrame) (hP : CanonicalFrame P) : ptPair (emb P) = P.1 := by
  classical
  obtain ⟨h1, h2⟩ := hP
  by_cases h : affineIsInfinity fpOps P.1 = true
  · have hz : emb P = 0 := emb_inf P h
    rw [hz, ptPair_zero]
    exact ((emb_eq_zero_iff_canonical P ⟨h1, h2⟩).mp hz).symm
  · have key : emb P = Point.some ((P.1.1 : ℕ) : K) ((P.1.2 : ℕ) : K)
        (nonsingular_of_equation (equation_of_frame P h)) := emb_notInf P h
    rw [key]
    have e1 : ((P.1.1 : ℕ) : K).val = P.1.1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h1]
    have e2 : ((P.1.2 : ℕ) : K).val = P.1.2 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h2]
    rw [ptPair_some]
    exact Prod.ext e1 e2

/-- **EVERY ELEMENT OF THE CARRIER IS `r`-TORSION, additively.** The transport is PROPOSITIONAL
    (`toAdd_pow`), not definitional: `rfl` on `toAdd (ofAdd X ^ blsR) = blsR • X` dies because the
    right-hand side whnf's into a 255-bit `nsmul` recursion. See the section header. -/
theorem nsmul_blsR_eq_zero (X : W.Point)
    (hX : Multiplicative.ofAdd X ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) :
    blsR • X = 0 := by
  classical
  have h1 : (Multiplicative.ofAdd X) ^ blsR = 1 := pow_blsR_eq_one_ambient _ hX
  have h2 : ((Multiplicative.ofAdd X) ^ blsR).toAdd = blsR • X := toAdd_pow _ _
  rw [← h2, h1]
  rfl

/-- **THE PRECOMPILE'S OWN VALIDATOR ACCEPTS EVERY `ptPair`** - P-CANON's `g1InSubgroup_iff` route
    applied to EVERY element of the carrier, not just the generator. -/
theorem g1PointMsmValid_ptPair (X : W.Point)
    (hX : Multiplicative.ofAdd X ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame))) :
    g1PointMsmValid (ptPair X) = true := by
  classical
  have hc : CanonicalFrame (frameOf X) := canonical_frameOf X
  have htor : blsR • emb (frameOf X) = 0 := by
    rw [emb_frameOf]; exact nsmul_blsR_eq_zero X hX
  exact (g1PointMsmValid_iff (frameOf X) hc).mpr htor

private theorem g1PointAddValid_ptPair (X : W.Point) : g1PointAddValid (ptPair X) = true :=
  onCurve_ptPair X

/-! #### The codec -/

/-- The underlying curve point of a carrier element. -/
def g1zPoint (Q : G₁z) : W.Point := Multiplicative.toAdd Q.val

private theorem g1zPoint_mem (Q : G₁z) :
    Multiplicative.ofAdd (g1zPoint Q) ∈
      Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame)) :=
  Q.prop

/-- The pair the codec encodes. -/
def g1zPair (Q : G₁z) : Nat × Nat := ptPair (g1zPoint Q)

theorem g1zPair_canonical (Q : G₁z) : (g1zPair Q).1 < blsP ∧ (g1zPair Q).2 < blsP :=
  canonical_frameOf (g1zPoint Q)

theorem g1zPoint_mul (P Q : G₁z) : g1zPoint (P * Q) = g1zPoint P + g1zPoint Q := rfl

/-- The scalar action projects through too: the `ZMod r` smul built by `AddCommGroup.zmodModule`
    is `val`-indexed `nsmul`, which is what the byte fold computes with. -/
theorem g1zPoint_gsmul (Q : G₁z) (s : Fr blsR) :
    g1zPoint (Midfall.Halo2.gsmul s Q) = s.val • g1zPoint Q := by
  classical
  have h : (Midfall.Halo2.gsmul s Q : G₁z) = Q ^ s.val := rfl
  rw [h, g1zPoint, Subgroup.coe_pow, toAdd_pow]
  rfl

/-- **THE ENCODER**: the EIP-2537 padded byte encoding of the point - the `Point` -> canonical-bytes
    map the brief asked for, via the coordinate projection and `ZMod.val`. -/
def g1zToEip (Q : G₁z) : Bytes := g1PointBytes (g1zPair Q)

/-- **THE DECODER, NONCOMPUTABLY.** Making this computable is a DISCRETE LOG: an accepted frame is
    an `r`-torsion point and `ofEip?` has to name an exponent `n` with `ptPair = n • emb genFrame`.
    Not a plumbing item and not this package's item - the same wall as `g1Decodes`, stated precisely
    by `g1CodecZ_g1DecodesWidth_iff`. -/
noncomputable def g1zOfEip? (b : Bytes) : Option G₁z := by
  classical
  exact if h : ∃ Q : G₁z, g1zToEip Q = b then some (Classical.choose h) else none

/-- **THE G1Codec ON THE `zpowers` CARRIER** - the second missing piece P-CANON named. The
    compressed half is a placeholder and says so: no `Holds` clause reads it, and a real
    `ofCompressed?` needs the same discrete log as `ofEip?`. -/
noncomputable def g1CodecZ : G1Codec G₁z where
  toEip := g1zToEip
  ofEip? := g1zOfEip?
  toCompressed := fun Q => bytesNatBE (g1zPair Q).1 fpBytes
  ofCompressed? := fun _ => none

/-- The generator as a carrier element: the carrier is not the trivial group. -/
def g1zGen : G₁z :=
  ⟨Multiplicative.ofAdd (emb genFrame), Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one _⟩⟩

theorem g1zPoint_gen : g1zPoint g1zGen = emb genFrame := rfl
theorem g1zPair_gen : g1zPair g1zGen = genPair := rfl
theorem g1zPair_one : g1zPair (1 : G₁z) = (0, 0) := rfl
theorem g1zToEip_gen : g1zToEip g1zGen = g1PointBytes genPair := rfl
theorem g1zToEip_zero : g1zToEip (1 : G₁z) = g1PointBytes (0, 0) := rfl

/-! #### The three G1-side `Holds` clauses, discharged -/

/-- **`g1Valid`, DISCHARGED AT THE REAL-CURVE CODEC.** The quantifier is over the whole carrier,
    not over a named generator. -/
theorem g1CodecZ_g1Valid :
    ∀ Q : G₁z, ∃ pt, g1Of? (g1CodecZ.toEip Q) = some pt ∧ g1PointMsmValid pt = true := by
  intro Q
  obtain ⟨h1, h2⟩ := g1zPair_canonical Q
  exact ⟨g1zPair Q, g1Of?_g1PointBytes (g1zPair Q) h1 h2,
    g1PointMsmValid_ptPair (g1zPoint Q) (g1zPoint_mem Q)⟩

/-- **`g1Add`, DISCHARGED.** The G1ADD frame built from two codec encodings returns the codec
    encoding of the product. Algebra: `emb_add` (P-G1AGREE). Plumbing: `g1AddOutput_g1PointBytes`
    (this package). Bridge: `ptPair` and `emb` are inverse on canonical frames, and `addFrame`'s
    output is canonical by P-CANON's `affineAdd_canonic` - which is what lets `ptPair_emb` apply. -/
theorem g1CodecZ_g1Add :
    ∀ P Q : G₁z, g1AddOutput (g1AddFrame (g1CodecZ.toEip P) (g1CodecZ.toEip Q)) =
      some (g1CodecZ.toEip (P * Q)) := by
  intro P Q
  obtain ⟨a1, a2⟩ := g1zPair_canonical P
  obtain ⟨b1, b2⟩ := g1zPair_canonical Q
  show g1AddOutput (g1AddFrame (g1PointBytes (g1zPair P)) (g1PointBytes (g1zPair Q))) =
      some (g1PointBytes (g1zPair (P * Q)))
  rw [g1AddOutput_g1PointBytes (g1zPair P) (g1zPair Q) a1 a2 b1 b2
      (g1PointAddValid_ptPair (g1zPoint P)) (g1PointAddValid_ptPair (g1zPoint Q))]
  refine congrArg (fun t => some (g1PointBytes t)) ?_
  show affineAdd fpOps (ptPair (g1zPoint P)) (ptPair (g1zPoint Q)) =
      ptPair (g1zPoint (P * Q))
  refine Eq.symm ?_
  rw [g1zPoint_mul, ← emb_frameOf (g1zPoint P), ← emb_frameOf (g1zPoint Q), emb_add,
      ptPair_emb (addFrame (frameOf (g1zPoint P)) (frameOf (g1zPoint Q)))
        (addFrame_canonic (frameOf (g1zPoint P)) (frameOf (g1zPoint Q))
          (canonical_frameOf _) (canonical_frameOf _)),
      addFrame_val, frameOf_val, frameOf_val, emb_frameOf, emb_frameOf]

/-- **`g1Msm1`, DISCHARGED.** One-pair G1MSM on the interleaved 0xa0 record is the scalar action
    `gsmul`, the scalar carried in the canonical big-endian word. This is where the `where`-clause
    `go` unfolding is consumed, and the `Module (ZMod blsR)` instance is what makes `gsmul` statable
    at a real curve point at all. -/
theorem g1CodecZ_g1Msm1 :
    ∀ (Q : G₁z) (s : Fr blsR),
      g1MsmOutput (g1MsmFrame [(g1CodecZ.toEip Q, frToInputBE s)]) =
        some (g1CodecZ.toEip (Midfall.Halo2.gsmul s Q)) := by
  intro Q s
  obtain ⟨h1, h2⟩ := g1zPair_canonical Q
  show g1MsmOutput (g1MsmFrame [(g1PointBytes (g1zPair Q), frToInputBE s)]) =
      some (g1PointBytes (g1zPair (Midfall.Halo2.gsmul s Q)))
  rw [g1MsmOutput_singleton (g1zPair Q) s h1 h2
      (g1PointMsmValid_ptPair (g1zPoint Q) (g1zPoint_mem Q))]
  refine congrArg (fun t => some (g1PointBytes t)) ?_
  show affineSmul fpOps s.val (ptPair (g1zPoint Q)) =
      ptPair (g1zPoint (Midfall.Halo2.gsmul s Q))
  refine Eq.symm ?_
  rw [g1zPoint_gsmul, ← emb_frameOf (g1zPoint Q), emb_smul,
      ptPair_emb (smulFrame s.val (frameOf (g1zPoint Q)))
        (smulFrame_canonic s.val (frameOf (g1zPoint Q)) (canonical_frameOf _)),
      smulFrame_val, frameOf_val, emb_frameOf]

/-- **THE DECODER-FIRST CANONICALITY LAW `G1Codec.eipRoundtrip` AT THE REAL-CURVE CODEC.** This
    direction needs NO point count and NO discrete log: whatever `ofEip?` accepts re-encodes to the
    bytes it came from. It is the anti-malleability property, and it is the codec law available
    today. -/
theorem g1CodecZ_eipRoundtrip : G1Codec.eipRoundtrip g1CodecZ := by
  classical
  intro b Q h0
  have h : g1zOfEip? b = some Q := h0
  by_cases hex : ∃ R : G₁z, g1zToEip R = b
  · have h2 : g1zOfEip? b = some (Classical.choose hex) := by
      unfold g1zOfEip?
      exact dif_pos hex
    rw [h2] at h
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hex
  · have h2 : g1zOfEip? b = none := by
      unfold g1zOfEip?
      exact dif_neg hex
    rw [h2] at h
    exact absurd h (by simp)

/-- **THE EXACT SHAPE OF WHAT IS LEFT, AS AN EQUIVALENCE.** `g1Decodes` - the fourth G1-side clause
    - is equivalent, over this codec, to "`g1zToEip` is onto the frames the precompile accepts".
    That is not byte plumbing and not a definitional gap: it says every `r`-torsion point of `E(Fp)`
    is a multiple of the published generator, i.e. `|E(Fp)[r]| = r`. THIS is where the point-count
    package lands, and it is the only G1-side clause this package could not close. -/
theorem g1CodecZ_g1DecodesWidth_iff :
    g1DecodesWidth g1CodecZ ↔
      ∀ b : Bytes, b.size == g1Bytes →
        (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
          ∃ Q : G₁z, g1zToEip Q = b := by
  classical
  constructor
  · intro h b hb ⟨pt, hpt, hv⟩
    obtain ⟨Q, _, hQ⟩ := h b hb ⟨pt, hpt, hv⟩
    exact ⟨Q, hQ⟩
  · intro h b hb ⟨pt, hpt, hv⟩
    obtain ⟨Q, hQ⟩ := h b hb ⟨pt, hpt, hv⟩
    have hex : ∃ R : G₁z, g1zToEip R = b := ⟨Q, hQ⟩
    have h1 : g1zOfEip? b = some (Classical.choose hex) := dif_pos hex
    exact ⟨Classical.choose hex, h1, Classical.choose_spec hex⟩

/-! #### D-P23: witnesses and falsifications for the codec -/

/-- **WITNESS FOR `g1Valid` (D-P23 satisfiability), AT THE PUBLISHED GENERATOR**: the decoded pair
    IS the EIP's own H1 coordinates - not a two-point model and not the identity. -/
theorem g1CodecZ_g1Valid_witness :
    ∃ pt, g1Of? (g1CodecZ.toEip g1zGen) = some pt ∧ g1PointMsmValid pt = true ∧ pt = genPair :=
  ⟨genPair, by
      show g1Of? (g1zToEip g1zGen) = some genPair
      rw [g1zToEip_gen]
      exact g1Of?_g1PointBytes_genPair,
    g1PointMsmValid_ptPair (g1zPoint g1zGen) (g1zPoint_mem g1zGen), rfl⟩

/-- **FALSIFICATION FOR THE CODEC (D-P23): `toEip` IS NOT A CONSTANT MAP.** If it were, all three
    clauses above would be vacuous. -/
theorem g1zToEip_not_constant : g1zToEip g1zGen ≠ g1zToEip (1 : G₁z) := by
  intro hh
  have e1 : g1Of? (g1zToEip g1zGen) = some genPair := by
    rw [g1zToEip_gen]
    exact g1Of?_g1PointBytes_genPair
  have e2 : g1Of? (g1zToEip (1 : G₁z)) = some (0, 0) := by
    rw [g1zToEip_zero]
    exact g1Of?_g1PointBytes (0, 0) p_pos p_pos
  rw [hh, e2] at e1
  obtain hq := Option.some.inj e1
  have hx : genX = 0 := (congrArg (fun t : Nat × Nat => t.1) hq).symm
  exact (by decide : genX ≠ 0) hx

/-- **WITNESS FOR `g1Add` (D-P23 satisfiability)**: adding the identity frame to the generator
    frame returns the generator frame - the EIP's own infinity branch, reached through the codec. -/
theorem g1CodecZ_g1Add_witness :
    g1AddOutput (g1AddFrame (g1CodecZ.toEip g1zGen) (g1CodecZ.toEip (1 : G₁z))) =
      some (g1CodecZ.toEip g1zGen) := by
  rw [g1CodecZ_g1Add g1zGen (1 : G₁z), mul_one]

/-- **FALSIFICATION FOR `g1Add` (D-P23): the precompile REFUSES a frame whose point is not
    canonically encoded**, so the clause's left-hand side is not automatically a `some`. -/
theorem g1CodecZ_g1Add_refuses_noncanonical :
    g1AddOutput (g1AddFrame (g1PointBytes junkPair) (g1PointBytes junkPair)) = none := by
  classical
  unfold g1AddOutput
  rw [bytesSlice_g1AddFrame_left, bytesSlice_g1AddFrame_right,
      g1Of?_g1PointBytes_needs_canonical]

/-- **FALSIFICATION FOR `g1Msm1` (D-P23): THE SCALAR IS LOAD-BEARING.** At `s = 0` the clause names
    the identity element and at `s = 1` the generator, and those two carrier elements are DISTINCT.
    The third conjunct is stated at the carrier and not at the bytes: rewriting a hypothesis that
    contains `g1zToEip (gsmul 0 g1zGen)` blows the recursion depth, because the byte encoder has to
    be whnf'd to instantiate the motive. Recorded because it cost a build cycle. -/
theorem g1CodecZ_g1Msm1_scalar_matters :
    Midfall.Halo2.gsmul (0 : Fr blsR) g1zGen = (1 : G₁z) ∧
      Midfall.Halo2.gsmul (1 : Fr blsR) g1zGen = g1zGen ∧ (1 : G₁z) ≠ g1zGen := by
  classical
  have h0 : Midfall.Halo2.gsmul (0 : Fr blsR) g1zGen = (1 : G₁z) := by
    show Additive.toMul ((0 : Fr blsR) • Additive.ofMul g1zGen) = _
    rw [zero_smul]
    rfl
  have h1 : Midfall.Halo2.gsmul (1 : Fr blsR) g1zGen = g1zGen := by
    show Additive.toMul ((1 : Fr blsR) • Additive.ofMul g1zGen) = _
    rw [one_smul]
    rfl
  refine ⟨h0, h1, ?_⟩
  intro hh
  exact g1zToEip_not_constant (congrArg g1zToEip hh).symm

/-- **FALSIFICATION FOR THE DECODER (D-P23): `ofEip?` REFUSES A FRAME OUTSIDE THE IMAGE.** Width is
    the easiest witness: a 129-byte frame encodes nothing, because every `toEip` is exactly
    `g1Bytes` long. So `eipRoundtrip` is not the vacuous truth of a decoder that accepts everything. -/
theorem g1zOfEip?_refuses_outside_the_image : g1zOfEip? (bytesZero (g1Bytes + 1)) = none := by
  classical
  have h : ¬ ∃ Q : G₁z, g1zToEip Q = bytesZero (g1Bytes + 1) := by
    intro hex
    obtain ⟨Q, hQ⟩ := hex
    have hs : (g1zToEip Q).size = g1Bytes := g1PointBytes_size (g1zPair Q)
    rw [hQ, bytesZero_size] at hs
    omega
  have h2 : g1zOfEip? (bytesZero (g1Bytes + 1)) = none := dif_neg h
  exact h2

/-- **WHAT P-G1CODEC TOOK OFF THIS LIST, AND WHAT IS LEFT.** The four links P-CANON named are
ALL closed: `g1Of?_g1PointBytes` (the round trip), `bytesSlice_g1PointBytes_left` / `_right` (the two
slice equations), `g1AddValidInput_g1PointBytes` and `g1AddOutput_g1PointBytes` (the G1ADD
unfolding), and `g1MsmPairs?_singleton` (the `where`-clause `go`, which P-CANON did not attempt and
which needed no special budget - the compiler's `.go.eq_1` / `.eq_2` are `rfl`-level). On top of
them the second missing piece landed too: `g1CodecZ`, a `G1Codec` on the `zpowers` carrier, with
`g1CodecZ_g1Valid`, `g1CodecZ_g1Add` and `g1CodecZ_g1Msm1` discharging three of the six `Holds`
clauses at real curve points, and `g1CodecZ_eipRoundtrip` discharging the codec law of
Common/Codec.lean.

WHAT IS LEFT on the G1 side is ONE clause and it is not plumbing: `g1Decodes`.
`g1CodecZ_g1DecodesWidth_iff` states exactly what it needs - that `g1zToEip` be onto the frames the
precompile accepts, i.e. that every `r`-torsion point of `E(Fp)` be a multiple of the published
generator, which is `|E(Fp)[r]| = r`. That is the point-count package (route (b)), and the same
wall makes `g1zOfEip?` noncomputable: a computable decoder is a discrete log. -/
def gap_g1_codec_roundtrip : String :=
  "closed by P-G1CODEC: the byte round trip, the two slice equations, g1AddValidInput/g1AddOutput, "
    ++ "and g1MsmPairs?.go. Remaining G1-side Holds clause: g1Decodes, which by "
    ++ "g1CodecZ_g1DecodesWidth_iff is exactly surjectivity of g1zToEip onto accepted frames, i.e. "
    ++ "the point count |E(Fp)[r]| = r (and the same wall makes g1zOfEip? noncomputable)."

end Midfall.Instances
