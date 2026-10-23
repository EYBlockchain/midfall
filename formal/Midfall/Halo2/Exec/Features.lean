-- |
-- Midfall.Halo2.Exec.Features
--
-- The four cargo features the verifier behaviour actually branches on (plan
-- Section 4, rule R8). `Features.solidity` is the production feature set
-- recorded in formal/BASELINE.md.

namespace Midfall.Halo2

structure Features where
  /-- rust: feature "committed-instances" (always on: the crate forwards
      midnight-proofs/committed-instances unconditionally). -/
  committedInstances : Bool
  /-- rust: feature "truncated-challenges" -/
  truncatedChallenges : Bool
  /-- rust: feature "outer-fewer-point-sets" -/
  outerFewerPointSets : Bool
  /-- rust: feature "outer-single-h-commitment" -/
  outerSingleHCommitment : Bool

/-- The production profile: the recorded IVC / Moonlight decider runs use
    evm,truncated-challenges,in-circuit-fewer-point-sets (see
    proofs/solidity-verifier/docs/reference/REPRODUCIBLE_BUILDS.md and
    scripts/run_ivc_bench.sh:225-243). in-circuit-fewer-point-sets is not one of
    the four flags - it affects the recursive verifier circuits, not the
    Solidity-facing proof layout - so it does not appear here. The optional
    outer-single-h-commitment profile is a *different* Features value, and the
    per-deployment statement (plan 9.6) names which one it pins.
    TODO(BASELINE): confirm against the frozen baseline's deploy command line. -/
def Features.solidity : Features where
  committedInstances := true
  truncatedChallenges := true
  outerFewerPointSets := false
  outerSingleHCommitment := false

end Midfall.Halo2
