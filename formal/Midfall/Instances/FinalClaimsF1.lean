/-
  Midfall.Instances.FinalClaimsF1

  FINAL ASSEMBLY - **THE F1-REAL CLAIM SURFACE, KEPT SEPARATE FROM THE GENERIC ONE.**

  `Midfall.LoweringV3.FinalClaims` carries the generic claims (`lowering_correct`,
  `generator_correct_V3`, `EndToEndV3` from `ValidV3`). This module carries the F1-real claim and
  nothing else:

    * `f1PointRenderCCN_doneAt` - the `DoneAt` at the resourced-codec F1 render. Its fields wire
      the generic headline (`lowering_correct`), the F1 `ValidV3` (`f1PointRenderCCN_validV3`,
      conditional on the data statement `hpay`), the per-product totality `totalV3_correct`, the
      gate datum, and the D-GATE17 `ArtifactEqV3` datum.

  WHY IT IS A SEPARATE MODULE. `DoneAt`'s cone contains F1 data and native computations
  (`f1ResRun_isOk`, `genFilledRun_isOk`, `vkFilled_isOk`, ...). Those are legitimate at a fixture
  (PLAN-V3 §0: fixtures are tests) and must not appear in a generic claim's cone. checks.sh's
  import-confinement rule enforces the direction mechanically: no theorem-bearing file outside
  `Instances/` may import this module. The generic module names the split in its header and does
  not import it.

  The `#print axioms` below is the measurement, not a gate: it names the F1 data/trust boundary on
  the record so a reader can compare it with the EMPTY native list on the generic claims.
-/
import Midfall.Instances.GeneratorDoneAt

set_option autoImplicit false

namespace Midfall.Instances

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1 Midfall.Instances.ValidV3InhabitationF1Completion
open Midfall.Instances.PayloadPointsF1

noncomputable section

-- **THE F1-REAL CLAIM, EXPOSED FOR THE FINAL SURFACE.** `f1PointRenderCCN_doneAt` is defined
-- in `GeneratorDoneAt.lean`; this `#check` fixes its exact statement on the final surface.
#check @Midfall.Instances.f1PointRenderCCN_doneAt

-- The render-generic `DoneAt` is the same wiring without the resourced-codec choice.
#check @Midfall.Instances.f1PointRenderCN_doneAt

-- A `DoneAt` gives the frozen render-generic `GeneratorDone`.
#check @Midfall.LoweringV3.DoneAt.toGeneratorDone

-- The generic non-vacuity bridge (gate -> `HypothesesInhabitedV3`) is stated in
-- `Instances/GeneratorDone.lean`; it is checked here, on the F1 side of the split, so the generic
-- module can keep its empty `native []` and its no-Instances import.
#check @Midfall.LoweringV3.hypothesesInhabitedV3_of_gateAtV3

#print axioms Midfall.Instances.f1PointRenderCCN_doneAt

end

end Midfall.Instances
