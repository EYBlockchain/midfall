-- |
-- Midfall.Security.Challenges
--
-- The per-round challenge masses and the error-budget shape of plan Section
-- 9.4. These are DEFINED here (no sorry): the inputs are the feature flags and a
-- bad-outcome count, and the degrees themselves are what Spec/Degrees will
-- supply from the paper proof in docs/security.tex.
--
-- Why the constant 3: challenges are squeezed as a 256-bit digest reduced mod r,
-- so a uniform digest lands on any given bad value with probability between
-- 1/r and 2^256 / r^2; ceil(2^256 / r) = 3 for BLS12-381. Design-assessment F2
-- is exactly this factor, and with truncated challenges the squeezed value is
-- cut to 128 bits instead, which is the other branch.

import Mathlib.Data.ENNReal.Basic
import Midfall.Halo2.Exec.Features

namespace Midfall.Security

open Midfall

/-- The verifier's challenge squeezes, in transcript order (plan 9.4 Chal). -/
inductive Chal where
  | theta | beta | gamma | trash | y | x | x1 | x2 | x3 | x4

-- ENNReal division is noncomputable in mathlib, so the error budget is a
-- mathematical object rather than executable code. That is expected: plan rule
-- R10's computability requirement covers the Exec layer, not probability bounds.
/-- Probability mass of hitting a bad value for a challenge with `s` bad
    outcomes, under the given feature flags. -/
noncomputable def chalMass (F : Halo2.Features) (s : Nat) : ENNReal :=
  if F.truncatedChallenges then (s : ENNReal) / (2 : ENNReal) ^ 128
  else 3 * (s : ENNReal) / (2 : ENNReal) ^ 256

/-- The constant 3 in `chalMass` really is ceil(2^256 / r) for the BLS12-381
    scalar order r: twice r is below 2^256 and three times r is above it.
    Proved by kernel reduction, not native_decide - the ban on native_decide
    outside Instances/ exists so nothing else leans on compiled code. -/
theorem challenge_mass_constant :
    2 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 < 2 ^ 256 ∧ 2 ^ 256 < 3 * 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 :=
  by decide

end Midfall.Security
