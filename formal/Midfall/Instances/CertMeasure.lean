/-
  Midfall.Instances.CertMeasure  (CERT.0 measurement, rebased)

  Each decidable section-3 conclusion of `Midfall/Generator/Certified.lean`, evaluated at the F1
  fixture. The generator run is `ValidV3InhabitationF1.genFilledOut` (the ported `generateAll` on
  the F1 key with the payload's four reservation fields filled; the payload is the fixed point the
  run returns). This file is a MEASUREMENT, not a gate: the single `#eval` carries no
  `-- expect` annotation, so it does not move the KAT pin.

  D-CERT1 additions: the eight `programOk` conjuncts are measured here too
  (`hasMultiPointSet`, `transcriptRegionOk`, `g1IdentityFloor`, `negLagrangesFloor`,
  `permCommMatchRepaired`, `gasCallOk` at fuel 20000, `gasFree` at fuel 20000, `programFits` via
  its Bool face `programFitB`).
-/
import Midfall.Instances.ValidV3InhabitationF1
import Midfall.Generator.Certified
set_option autoImplicit false

namespace Midfall.Instances.CertMeasure

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Assumptions
open Midfall.LoweringV3 Midfall.Generator.Certified
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid
open Midfall.Instances.ValidV3InhabitationF1
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-- The plan view of the F1 generator-derived render. No `Render` value is constructed: the
    measurement reads only `PlanView`/`Model`, which are computable at F1. -/
def f1Pv : PlanView :=
  planViewOf genFilledOut.plan genFilledOut.model poseidonConfig.accumulator

def f1M : Model := genFilledOut.model

def f1Main : YulBlock := mainAsmRaw f1Pv f1M

/-- The section-3 measurements, one Boolean per decidable conclusion. -/
def report : String :=
  let P2a := f1M.quotientDirect.isNone
  let P2b := Midfall.LoweringV3.constLinesLiteral f1M
  let P2c := Midfall.LoweringV2.constTableOf f1M == Midfall.LoweringV2.expectedConsts f1Pv f1M
  let P2d := decide (((Midfall.LoweringV2.expectedConsts f1Pv f1M).map Prod.fst).Nodup)
  let P2e := ((freeNames (abiGuardBlock f1M ++ f1Main)).filter
      fun x => x != "vk" && x != "quotientEvaluator").all
      fun x => ((Midfall.LoweringV2.expectedConsts f1Pv f1M).map Prod.fst).contains x
  let P3 := Midfall.LoweringV3.callsResolved f1Main
  let P4 := Midfall.LoweringV3.noShadowProg (Midfall.LoweringV2.constTableOf f1M) (abiGuardBlock f1M ++ wrapperLocals f1M 0 0 ++ f1Main)
  let P5 := (Midfall.LoweringV2.freeNames (Inline.inlineContractConstants (Midfall.LoweringV2.constTableOf f1M)
      (abiGuardBlock f1M ++ f1Main))).all (fun x => x == "vk" || x == "quotientEvaluator")
  let P6 := decide (0x80 ≤ f1Pv.memory.transcriptMptr)
  let CS := codegenStruct f1Main f1M
  let CA := codegenAgrees f1Pv f1M
  let NW := noWritersFuel 20000 (asmOf f1Pv f1M 0 0)
  let XD := Midfall.LoweringV3.exitDisciplineFuel 20000 (asmOf f1Pv f1M 0 0)
  let NS := Midfall.LoweringV3.noShadowCore f1Pv f1M
  let MC := mainClosed f1Pv f1M
  let CB := decide (genFilledOut.plan.proofLayout.proofEnd + 32 + 32 * 1 < 2 ^ 256)
  let LY := match ProofCalldataLayout.fromProtocol genFilledOut.plan.meta_.protocol
      abiVerifyProofProofCptr genFilledOut.plan.meta_.numEvals genFilledOut.plan.meta_.numPointSets with
    | .ok l => l.proofLen == genFilledOut.plan.proofLayout.proofLen
    | .error _ => false
  let INV := match genFilledOut.plan.validateGeneratorInvariants with
    | .ok (.ok ()) => true | _ => false
  let LAY := decide genFilledOut.plan.memory.map.WellFormed && genFilledOut.plan.memory.validate.isOk
  let K := f1Pv.k == poseidonVkExec.domain.k
  let HMP := Midfall.LoweringV3.hasMultiPointSet f1Pv
  let TRO := Midfall.LoweringV3.transcriptRegionOk f1Pv poseidonConfig.numInstances
  let G1F := Midfall.LoweringV3.g1IdentityFloor f1Pv
  let NLF := Midfall.LoweringV3.negLagrangesFloor f1Pv
  let PCM := Midfall.LoweringV3.permCommMatchRepaired poseidonVkExec
  let GCO := Midfall.LoweringV3.gasScan 20000 (.b (asmOf f1Pv f1M 0 0))
  let GF := Midfall.LoweringV3.gasFreeScan 20000 (.b (asmOf f1Pv f1M 0 0))
  let PF := Midfall.LoweringV3.programFitB f1Pv f1M
  s!"with today's emitters: codegenStruct={CS} codegenAgrees={CA} P2a={P2a} P2b={P2b} P2c={P2c} P2d={P2d} P2e={P2e} P3={P3} \
P4={P4} P5={P5} P6={P6} noWriters={NW} exitDiscipline={XD} noShadowCore={NS} mainClosed={MC} \
cdBound={CB} layoutV3={LY} invariants={INV} supported.layout={LAY} env_k={K} \
hasMultiPointSet={HMP} transcriptRegionOk={TRO} g1IdentityFloor={G1F} negLagrangesFloor={NLF} \
permCommMatchRepaired={PCM} gasCallOk={GCO} gasFree={GF} programFits={PF}"

#eval report

/-! ## D-GATE11 concrete-count witness (F1)

The D-GATE11 clause is an input computation (`metaCountsBoundB` on the raw meta, the payload
length, and the instance count), so its content at a concrete input is decided by `native_decide`.
There is no `SupportedInput` inhabitant in the tree - `SupportedInput` is a generator-side
predicate and the F1 files witness `SupportedV2`, not it - so this is the honest witness the
clause has: the F1 raw meta, the F1 payload and the F1 proof-end all satisfy the new budget. -/

/-- The F1 raw meta: the same `ConstraintSystemMeta.new` the generator's first bind runs. -/
def f1RawMeta : ConstraintSystemMeta :=
  match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs
      poseidonConfig.numCommittedInstances with
  | .ok m => m
  | .error _ => constraintSystemMetaDefault

/-- D-GATE11 at F1: every count `< 2 ^ 32`, the payload `< 2 ^ 200`, and the proof-end bound. -/
def f1CountsOk : Bool :=
  Midfall.Generator.Certified.metaCountsBoundB f1RawMeta &&
  decide (genFilledOut.plan.vk.len < 2 ^ 200) &&
  decide (genFilledOut.plan.proofLayout.proofEnd + 32 +
    32 * poseidonConfig.numInstances < 2 ^ 256)

theorem f1CountsOk_true : f1CountsOk = true := by native_decide

/-- The clause's content at F1, as a `Prop`: the raw meta passes `MetaCountsBound`. -/
theorem f1MetaCounts_true :
    Midfall.Generator.Certified.metaCountsBoundB f1RawMeta = true := by native_decide

theorem f1MetaCounts : Midfall.Generator.Certified.MetaCountsBound f1RawMeta :=
  Midfall.Generator.Certified.metaCountsBound_of_b f1MetaCounts_true

/-- The generated F1 payload is below the D-GATE11 `2 ^ 200` payload bound. -/
theorem f1PayloadLen_lt : genFilledOut.plan.vk.len < 2 ^ 200 := by native_decide

#print axioms f1CountsOk_true
#print axioms f1MetaCounts
#print axioms f1PayloadLen_lt

#print axioms Midfall.Generator.Certified.generate_spec

end Midfall.Instances.CertMeasure
