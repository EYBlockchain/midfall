-- |
-- Midfall.Security.Challenges
--
-- The per-round challenge masses and the error-budget shape of plan Section
-- 9.4. These are DEFINED here (no sorry): the inputs are the feature flags, the
-- challenge ROUND, and a bad-outcome count; the degrees themselves are what
-- Spec/Degrees will supply from the paper proof in docs/security.tex.
--
-- Why the constant 3: challenges are squeezed as a 256-bit digest reduced mod r,
-- so a uniform digest lands on any given bad value with probability between
-- 1/r and 2^256 / r^2; ceil(2^256 / r) = 3 for BLS12-381. Design-assessment F2
-- is exactly this factor.
--
-- WHY THE MASS TAKES A ROUND (D-P21 docs/design.md:839, from R-51/F5 and R-23).
-- Truncation is a PER-ROUND property of the Rust, not a global feature, and the
-- two directions it moves in cannot be served by one uniform formula:
--
-- * theta, beta, gamma, trash, y, x - and x1, x2, x4 as VALUES - are squeezed by
--   squeeze_challenge and never truncated: plonk/verifier.rs:150, :167, :172,
--   :194, :215, :304 and poly/kzg/mod.rs:363, :364, :484 have no truncate after
--   the squeeze. Their mass is 3s/2^256 whatever the feature flag says, so the
--   old uniform s/2^128 was SOUND there but about 2^126.42 too big.
-- * x3 is squeezed and THEN truncated: poly/kzg/mod.rs:455-457 (multi open) and
--   :285-287 (single open) do
--     let x3: E::Fr = transcript.squeeze_challenge();
--     let x3 = truncate(x3);
--   and truncate (utils/arithmetic.rs:247-252) keeps the low nb_bytes =
--   NUM_BITS.div_ceil(8).div_ceil(2) = 16 bytes of the canonical representative,
--   i.e. the value mod 2^128. The image is [0, 2^128) but NOT uniform: each
--   truncated value is hit by ceil(r/2^128) field elements, each of which the
--   digest hits at most 3 times out of 2^256, so the per-value mass is
--   3 * ceil(r/2^128) / 2^256 ~ 1.3585 / 2^128. The old s/2^128 is TOO SMALL
--   there, and too small in an error budget is UNSOUND, not conservative.
--   chalMassUniform_lt_x3_mass (witness) and uniform_admits_new_refuses
--   (falsification) exhibit the gap; D-P23 does not accept the claim without them.
--
-- x1 and x4 are a third case this file does NOT settle: their values are
-- untruncated (mass 3s/2^256), but the Rust batches with truncated_powers
-- (poly/kzg/mod.rs:394, :502, :521), so no degree count bounds their bad SET at
-- all. That is R-22 / D-P14 / D-P22 and belongs to the paper, not here.
--
-- The "about 1.5" in D-P21, R-23 and docs/security.tex:157 is an estimate. The
-- exact factor is 3 * ceil(r/2^128) / 2^128 = 1.3585351690..., so the old bound
-- was short by 0.442 bits of budget, not by half a bit. The DIRECTION of the
-- error - the point of the decision - stands; the size is corrected here.

import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Inv
import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Features

namespace Midfall.Security

open Midfall

/-- The verifier's challenge squeezes, in transcript order (plan 9.4 Chal). -/
inductive Chal where
  | theta | beta | gamma | trash | y | x | x1 | x2 | x3 | x4
  deriving BEq

/-- The schedule in transcript order, so the round-by-round behaviour of the mass
    below can be enumerated by a `#eval` gate. -/
def Chal.all : List Chal :=
  [Chal.theta, Chal.beta, Chal.gamma, Chal.trash, Chal.y, Chal.x,
   Chal.x1, Chal.x2, Chal.x3, Chal.x4]

/-- Which rounds the Rust truncates the VALUE of. Exactly one: x3
    (poly/kzg/mod.rs:455-457, :285-287). Every other round's value is a full
    field element even under truncated-challenges; what that feature does to x1
    and x4 is truncate their POWERS, which is a different question (R-22). -/
def Chal.truncatedValue : Chal → Bool
  | .x3 => true
  | .theta | .beta | .gamma | .trash | .y | .x | .x1 | .x2 | .x4 => false

/-- ceil(r / 2^128): how many field elements share one 128-bit truncation, i.e.
    how many preimages one truncated value has. r = H * 2^128 + L with
    H = 0x73eda753299d7d483339d80809a1d805 and L = 0x53bda402fffe5bfeffffffff00000001
    nonzero, so the ceiling is H + 1; truncPreimageCount_ceiling checks it by
    reduction against CompPoly's r rather than trusting the literal. -/
def truncPreimageCount : Nat := 0x73eda753299d7d483339d80809a1d806

theorem truncPreimageCount_ceiling :
    truncPreimageCount = (Midfall.Assumptions.r + 2 ^ 128 - 1) / 2 ^ 128 := by
  decide

/-- The integer factor chalMass applies to a round's bad-point count: the
    ceil(r/2^128) collision factor for the one round whose value is truncated,
    1 elsewhere. Keeping it a Nat OUTSIDE the ENNReal division is what makes the
    factor explicit rather than folded into a constant (D-P21 deliverable 1). -/
def chalFactor (F : Halo2.Features) (c : Chal) : Nat :=
  if F.truncatedChallenges && c.truncatedValue then truncPreimageCount else 1

-- ENNReal division is noncomputable in mathlib, so the error budget is a
-- mathematical object rather than executable code. That is expected: plan rule
-- R10's computability requirement covers the Exec layer, not probability bounds.
/-- Probability mass of hitting a bad value for the challenge of round `c` when
    there are `s` bad values, under the given feature flags (plan 9.4 chalMass,
    made per-round by D-P21). Everything is stated over the common denominator
    2^256: a round whose value is not truncated contributes 3s/2^256 (the
    ceil(2^256/r) = 3 factor of challenge_mass_constant), and the truncated x3
    contributes 3 * ceil(r/2^128) * s / 2^256. -/
noncomputable def chalMass (F : Halo2.Features) (c : Chal) (s : Nat) : ENNReal :=
  3 * ((chalFactor F c * s : Nat) : ENNReal) / (2 : ENNReal) ^ 256

/-- The mass the OLD uniform `chalMass` gave every round under
    truncatedChallenges. Kept so the unsoundness is a statement that can be true
    or false rather than prose in a docstring. -/
noncomputable def chalMassUniform (s : Nat) : ENNReal :=
  (s : ENNReal) / (2 : ENNReal) ^ 128

/-- Restate the uniform mass over the common denominator 2^256, so the two masses
    are compared by comparing the integers inside them. -/
lemma chalMassUniform_eq_scaled (s : Nat) :
    chalMassUniform s = ((s * 2 ^ 128 : Nat) : ENNReal) / (2 : ENNReal) ^ 256 := by
  have hA : (2 : ENNReal) ^ 128 ≠ 0 := by norm_num
  have hAt : (2 : ENNReal) ^ 128 ≠ ⊤ := by norm_num
  have h256 : ((2 : ENNReal) ^ 256)⁻¹ = ((2 : ENNReal) ^ 128)⁻¹ * ((2 : ENNReal) ^ 128)⁻¹ := by
    rw [show (256 : Nat) = 128 + 128 from rfl, pow_add, ENNReal.mul_inv] <;> norm_num
  have hsplit : (2 : ENNReal) ^ 128 * (((2 : ENNReal) ^ 128)⁻¹ * ((2 : ENNReal) ^ 128)⁻¹)
      = ((2 : ENNReal) ^ 128)⁻¹ := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hA hAt, one_mul]
  unfold chalMassUniform
  rw [div_eq_mul_inv, div_eq_mul_inv, h256]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_assoc, hsplit]

/-- Two masses over the common denominator compare as the integers inside them. -/
lemma div256_lt_div256 {a b : Nat} :
    ((a : ENNReal) / (2 : ENNReal) ^ 256 < (b : ENNReal) / (2 : ENNReal) ^ 256) ↔ a < b := by
  rw [ENNReal.div_lt_div_iff_left (c := (2 : ENNReal) ^ 256) (by norm_num) (by norm_num)]
  exact Nat.cast_lt

/-- Fold the leading 3 into the integer numerator. -/
lemma three_mul_coe (n : Nat) :
    (3 : ENNReal) * ((n : Nat) : ENNReal) = ((3 * n : Nat) : ENNReal) :=
  (Nat.cast_mul 3 n).symm

/-- WITNESS (D-P21 deliverable 3, first half; D-P23/R-41). For the round the Rust
    truncates, the per-round mass is strictly LARGER than the mass the old uniform
    definition returned: 3 * ceil(r/2^128) / 2^256 against 1/2^128, a factor of
    1.3585351690. So the uniform number is not an upper bound on the true mass. -/
theorem chalMassUniform_lt_x3_mass :
    chalMassUniform 1 < chalMass Halo2.Features.solidity Chal.x3 1 := by
  rw [chalMassUniform_eq_scaled, chalMass]
  have hfac : chalFactor Halo2.Features.solidity Chal.x3 = truncPreimageCount := rfl
  rw [hfac, three_mul_coe]
  simp only [mul_one, one_mul]
  exact div256_lt_div256.mpr (by decide)

/-- FALSIFICATION (D-P21 deliverable 3, second half). A concrete budget the OLD
    bound admits and the NEW one refuses. Take the x3 bad-point count of
    Spec/Degrees's KAT index, maxSetSize * n = 3 * 16 = 48, and a per-round
    budget of 50 / 2^128 - the budget the old mass clears at 48 bad points,
    rounded up to the next integer count. The uniform mass 48/2^128 fits inside
    it; the true mass 3 * 48 * ceil(r/2^128) / 2^256 = 65.24/2^128 does not. A
    proof that checked the old budget would have accepted a parameter set that is
    not sound. -/
theorem uniform_admits_new_refuses :
    chalMassUniform 48 ≤ chalMassUniform 50
      ∧ ¬ (chalMass Halo2.Features.solidity Chal.x3 48 ≤ chalMassUniform 50) := by
  constructor
  · show (48 : ENNReal) / (2 : ENNReal) ^ 128 ≤ (50 : ENNReal) / (2 : ENNReal) ^ 128
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr (by decide)) _
  · intro h
    have hgt : chalMassUniform 50 < chalMass Halo2.Features.solidity Chal.x3 48 := by
      rw [chalMassUniform_eq_scaled, chalMass]
      have hfac : chalFactor Halo2.Features.solidity Chal.x3 = truncPreimageCount := rfl
      rw [hfac, three_mul_coe]
      exact div256_lt_div256.mpr (by decide)
    exact (not_le_of_gt hgt) h

/-- The other direction, so the fix is not a one-way loosening: for a round whose
    value the Rust does not truncate, the per-round mass is at most the uniform
    one, which reclaims the ~126 bits the old definition threw away. -/
theorem chalMass_untruncated_le_uniform (c : Chal) (h : c.truncatedValue = false) (s : Nat) :
    chalMass Halo2.Features.solidity c s ≤ chalMassUniform s := by
  have hfac : chalFactor Halo2.Features.solidity c = 1 := by simp [chalFactor, h]
  have key : chalMass Halo2.Features.solidity c s
      = ((3 * s : Nat) : ENNReal) / (2 : ENNReal) ^ 256 := by
    rw [chalMass, hfac, three_mul_coe]
    simp only [one_mul]
  rw [key, chalMassUniform_eq_scaled]
  refine ENNReal.div_le_div_right ?_ _
  rw [Nat.cast_le]
  have hle : 3 * s ≤ 2 ^ 128 * s := Nat.mul_le_mul_right s (by decide : (3 : Nat) ≤ 2 ^ 128)
  rw [Nat.mul_comm (2 ^ 128) s] at hle
  exact hle

/-- The constant 3 in `chalMass` really is ceil(2^256 / r) for the BLS12-381
    scalar order r: twice r is below 2^256 and three times r is above it.
    Proved by kernel reduction, not native_decide - the ban on native_decide
    outside Instances/ exists so nothing else leans on compiled code. -/
theorem challenge_mass_constant :
    2 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 < 2 ^ 256 ∧ 2 ^ 256 < 3 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 :=
  by decide

/-- Computable shadow of the mass: the factor function, the ceiling identity and
    the integer inequalities behind the exhibits above, as a Bool gate. ENNReal
    division is noncomputable, so this is all a `#eval` can reach; the theorems
    above are what says it means anything. -/
def chalMass_kats_ok : Bool :=
  truncPreimageCount == (Midfall.Assumptions.r + 2 ^ 128 - 1) / 2 ^ 128 &&
  chalFactor Halo2.Features.solidity Chal.x3 == truncPreimageCount &&
  chalFactor Halo2.Features.solidity Chal.theta == 1 &&
  chalFactor Halo2.Features.solidity Chal.beta == 1 &&
  chalFactor Halo2.Features.solidity Chal.gamma == 1 &&
  chalFactor Halo2.Features.solidity Chal.trash == 1 &&
  chalFactor Halo2.Features.solidity Chal.y == 1 &&
  chalFactor Halo2.Features.solidity Chal.x == 1 &&
  chalFactor Halo2.Features.solidity Chal.x1 == 1 &&
  chalFactor Halo2.Features.solidity Chal.x2 == 1 &&
  chalFactor Halo2.Features.solidity Chal.x4 == 1 &&
  chalFactor { Halo2.Features.solidity with truncatedChallenges := false } Chal.x3 == 1 &&
  (List.map Chal.truncatedValue Chal.all ==
    [false, false, false, false, false, false, false, false, true, false]) &&
  3 * truncPreimageCount > 2 ^ 128 &&
  3 * (truncPreimageCount * 48) > 50 * 2 ^ 128 &&
  48 * 2 ^ 128 ≤ 50 * 2 ^ 128

end Midfall.Security

#eval Midfall.Security.chalMass_kats_ok   -- expect true
