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

/-! ### WHAT THIS PACKAGE DID NOT FINISH, AND EXACTLY WHERE

The two coordinate agreements above are proved: on the secant branch and on the tangent branch,
the byte-level law and mathlib's `addX` / `addY` compute the same field expressions from the same
slope. What is NOT finished is the `point-level` assembly: turning those coordinate identities into
`emb P + emb Q = emb (affineAdd P Q)` for all four branches at once, plus the closure statement
`affineOnCurve fpOps (affineAdd fpOps P Q) = true` that a frame type needs.

The obstruction is mechanical, not mathematical, and it is one step: given
`hc1 : ((affineAdd fpOps P.1 Q.1).1 : K) = W.addX (P.1.1) (Q.1.1) (W.slope ...)`, the goal
`W.Nonsingular ((affineAdd fpOps P.1 Q.1).1 : K) ((affineAdd fpOps P.1 Q.1).2 : K)` refuses to
rewrite along `hc1` in either direction under `rw`, in every spelling tried (`rw` forward and
backward, `rw ... at h`, `convert ... using 2`, `heq ▸ heq ▸ e`, and `refine ⟨?_, ?_⟩` on the
`Nonsingular` structure). The elaborator's note on each failure is that the target is "not
type-correct under the `implicit` transparency level", which points at the subtype coercion
`(P : FpFrame) ↦ P.1` interacting with the `: K` ascription inside the projection
`((affineAdd ...).1 : K)`. The fix is almost certainly to state the coordinate lemmas with an
explicit `ZMod.val`-free pair projection (e.g. carry `x₃ := (affineAdd fpOps P.1 Q.1).1` as a
separate `have` and rewrite with that), or to make `FpFrame` a structure with named fields
`x y` instead of a subtype of a pair. Either is a few lines; the mathematics is done.

Until that assembly lands, `g1Add` and `g1Msm1` remain out of reach for a second reason as well,
which is independent of this file and is the finding the brief asked for: see the report.
-/

end Midfall.Instances
