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

import Midfall.Assumptions.Eip2537
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

/-- **THE REMAINING MECHANICAL ITEM, NAMED.** With the agreement theorems (\`emb_add\`, \`emb_smul\`),
    the walk (\`smulFrame_canonic\`) and the exhibit (\`primeOrderWith_zpowers_emb_genFrame\`) all in
    place, \`g1Add\` and \`g1Msm1\` as \`Holds\` FIELDS are blocked by exactly one thing, and it is
    byte plumbing rather than algebra: the codec round trip

        g1Of? (g1PointBytes P) = some P     for P with both coordinates below blsP,

    plus the two slice equations it needs (\`bytesSlice (g1PointBytes P) 0 64\` and
    \`... 64 64\`). HOW FAR THIS PACKAGE GOT, stated exactly: \`fpCoordBytes_size\`
    (\`(bytesAppend eipPad (bytesNatBE x fpBytes)).size = fpPadBytes + fpBytes\`),
    \`eipPad.size = fpPadBytes\`, \`bytesToNatBE eipPad = 0\` and \`blsP < 256 ^ fpBytes\` all
    CHECK, and every core lemma the walk needs was located by \`#check\` - \`Array.length_toList\`,
    \`ByteArray.size_data\`, \`Array.extract_append\`, \`Array.extract_eq_self_of_le\`,
    \`Array.extract_eq_empty_of_le\`, \`ofLowDigits_append\`,
    \`bytesToNatBE_eq_ofLowDigits_reverse\` (with \`bytesToNatBE_bytesNatBE\` and
    \`bytesNatBE_size\` already in \`Assumptions/Eip2537.lean\`).
    NOT YET PROVING, with the reason for each: \`bytesToNatBE_append2\` (the
    \`ofLowDigits_append\` rewrite fires on the wrong occurrence once the right-hand side
    is in \`bytesToNatBE\` form), \`bytesTake_whole\` (it reaches
    \`some { data := b.data.extract 0 (ByteArray.size b) } = some b\` and the last step
    needs \`@ByteArray.size_data\`, whose argument is implicit), and the two slice
    equations (their side conditions must be stated against \`ByteArray.size A\` because
    \`Array.extract_append\` inserts its own \`min\`); hence \`g1Of?_g1PointBytes\` is
    unproved. NOT ATTEMPTED: the \`g1AddValidInput\` / \`g1AddOutput\` unfolding and the
    \`where\`-clause function \`g1MsmPairs?.go\`. NONE of it is the canonicity wall:
    this is plumbing - which is why it is a package and not a lemma. -/
def gap_g1_codec_roundtrip : String :=
  "remaining mechanical item: g1Of? (g1PointBytes P) = some P for canonical P, then "
    ++ "bytesSlice over the 128-byte concatenation, then g1AddValidInput and g1MsmPairs?.go "
    ++ "unfolding. Byte plumbing, not the canonicity wall - that one is closed by "
    ++ "smulFrame_canonic, g1InSubgroup_iff and r_nsmul_emb_genFrame."

end Midfall.Instances
