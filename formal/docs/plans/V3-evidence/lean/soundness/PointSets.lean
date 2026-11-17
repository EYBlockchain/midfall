import Midfall.Instances.PoseidonInputs
set_option autoImplicit false
open Midfall Midfall.Generator
-- MEASUREMENT: the static point sets of the deployed plan (rotations per set), and the layout's
-- q_eval count. Settles whether the PCS block has a multi-point set whose scalar_inv reverts at x = 0.
#eval (match Midfall.Generator.intermediateSets Midfall.Instances.PoseidonInputs.poseidonPlanV2.meta_ Midfall.Instances.PoseidonInputs.poseidonPlanV2.data with
  | .ok s => (s.pointSets, s.commitments.length)
  | .error _ => ([], 0))
#eval Midfall.Instances.PoseidonInputs.poseidonPlanV2.proofLayout.qEvals.itemCount
#eval Midfall.Instances.PoseidonInputs.poseidonPlanV2.meta_.numPointSets
#eval Midfall.Instances.PoseidonInputs.poseidonPlanV2.proofLayout.proofLen
