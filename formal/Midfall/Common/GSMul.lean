-- |
-- Midfall.Common.GSMul
--
-- The scalar-action transport lemmas. `gsmul` (Halo2/Exec/Kzg/Msm.lean:35) is the
-- port's bridge between the two notations the project is committed to: the groups are
-- written MULTIPLICATIVELY (as the plan and the Rust do) while the scalar action is
-- the `Module (ZMod p) (Additive G)` instance (D-P1), i.e.
-- `gsmul s Q = Additive.toMul (s • Additive.ofMul Q)`. Every statement that folds an
-- MSM has to pay that mismatch somewhere, and this file is the one place it is paid:
-- each lemma here is rfl-level on the `Additive` transport plus one `smul` law.
--
-- WHY A SEPARATE FILE. These seven were written inside Lowering/Accumulator.lean
-- section 8 next to the two MSMKZG.eval holes that needed them, which made them look
-- local to that proof. They are not: they are transport facts about a Midfall
-- definition, and any other file that folds an MSM over `gsmul` needs exactly them.
-- Relocated by P-LIMB step 3.
--
-- WHY THEY ARE NOT SIMPLY CITED FROM MATHLIB. The section comment that used to
-- introduce them claimed "Mathlib's Additive.ofMul_mul / toMul_nsmul family is NOT in
-- this project's built surface". That claim is FALSE and it is the exact error class
-- P-BYTES recorded: the declarations live at ROOT namespace as `ofMul_mul`,
-- `ofMul_one`, `toMul_zero`, `toMul_nsmul` and resolve against `import Midfall` with
-- no new import; it is the `Additive.`-qualified spelling that does not exist. They
-- are still not a substitute for these lemmas, because `gsmul` is a Midfall
-- definition Mathlib has no name for - so what is here was misfiled, not redundant.
-- The proofs below now cite the root-namespace spellings where they apply.

import Midfall.Halo2.Exec.Kzg.Msm

namespace Midfall
open Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)]

section Msm
variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]

/-- Zero acts trivially: 0 • Q = 1. This is what makes the filterMap in
    msmSpecific (dropping zero coefficients, msm.rs:170) a semantic no-op. -/
theorem gsmul_zero (Q : G₁) : gsmul (p := p) (0 : Fr p) Q = 1 := by
  show Additive.toMul ((0 : ZMod p) • Additive.ofMul Q) = 1
  rw [zero_smul]; rfl

/-- One acts as the identity. -/
theorem gsmul_one (Q : G₁) : gsmul (p := p) (1 : Fr p) Q = Q := by
  show Additive.toMul ((1 : ZMod p) • Additive.ofMul Q) = Q
  rw [one_smul]; rfl

/-- Any scalar fixes the identity: c • 1 = 1. -/
theorem gsmul_one_pt (c : Fr p) : gsmul (p := p) c (1 : G₁) = 1 := by
  show Additive.toMul (c • Additive.ofMul (1 : G₁)) = 1
  rw [ofMul_one, smul_zero]; rfl

/-- The action is additive in the point: c • (x * y) = (c • x) * (c • y). -/
theorem gsmul_mul (a : Fr p) (x y : G₁) :
    gsmul (p := p) a (x * y) = gsmul (p := p) a x * gsmul (p := p) a y := by
  show Additive.toMul (a • Additive.ofMul (x * y)) = _
  rw [ofMul_mul x y, smul_add]; rfl

/-- The action is additive in the scalar: (a + b) • Q = (a • Q) * (b • Q). -/
theorem gsmul_add (a b : Fr p) (Q : G₁) :
    gsmul (p := p) (a + b) Q = gsmul (p := p) a Q * gsmul (p := p) b Q := by
  show Additive.toMul ((a + b) • Additive.ofMul Q) = _
  rw [add_smul]; rfl

/-- The action is multiplicative in the scalar: (a * b) • Q = a • (b • Q). -/
theorem gsmul_mul_gsmul (a b : Fr p) (Q : G₁) :
    gsmul (p := p) (a * b) Q = gsmul (p := p) a (gsmul (p := p) b Q) := by
  show Additive.toMul ((a * b) • Additive.ofMul Q) = _
  rw [← smul_smul]; rfl

/-- The scalar action agrees with the multiplicative power at a natural exponent.
    The one place where the two notations have to be reconciled. -/
theorem gsmul_nat (n : ℕ) (Q : G₁) : gsmul (p := p) (n : Fr p) Q = Q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, gsmul_zero, pow_zero]
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, gsmul_add, ih, pow_succ, gsmul_one]

end Msm

end Midfall
