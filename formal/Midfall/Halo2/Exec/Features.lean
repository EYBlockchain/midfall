-- |
-- Midfall.Halo2.Exec.Features
--
-- The four cargo features the verifier behaviour actually branches on (plan
-- Section 4, rule R8). The values of `Features.solidity` are the production
-- feature set recorded in formal/BASELINE.md.

namespace Midfall.Halo2

structure Features where
  /-- rust: feature "committed-instances" -/
  committedInstances : Bool
  /-- rust: feature "truncated-challenges" -/
  truncatedChallenges : Bool
  /-- rust: feature "outer-fewer-point-sets" -/
  outerFewerPointSets : Bool
  /-- rust: feature "outer-single-h-commitment" -/
  outerSingleHCommitment : Bool

end Midfall.Halo2
