import Midfall.Instances.DeployedProfile
import Midfall.LoweringV2.Statements

open Midfall Midfall.Generator Midfall.Instances Midfall.LoweringV2 Midfall.Lowering
open Midfall.Generator.VerifierPartialKats Midfall.Generator.ContractKats
open Midfall.Generator.QuotientFold

/-- tokens of a printed block, without its outer braces -/
def inner (b : YulSemantics.Block YulSemantics.EVM.Op) : List String :=
  ((yulTokens (YulSemantics.EVM.print b)).drop 1).dropLast

def row (name : String) (ast text : List String) : IO Unit :=
  IO.println s!"{name}: ast {ast.length} / codegen {text.length} tokens, equal = {ast == text}"

def probe : IO Unit := do
  let dvk ← readVkDump
  let sol ← readDump
  match vkModelFromArtifact dvk, quotientDeployedCtx sol with
  | some vk, some qctx =>
    let mem := poseidonDerivedMemory vk
    let L := poseidonPlan vk mem quotientDeployedProgram
    match generateVerifierFromPlan (fun _ _ => poseidonBlocks qctx) poseidonInputs poseidonFlags L with
    | .ok m =>
      let pv := planViewOf L m none
      let parts := partsOf m
      row "assemblyHelpers      " (inner (GenAst.emitHelpers pv)) (yulTokens parts.assemblyHelpers)
      row "accumulatorHelpers   " [] (yulTokens parts.accumulatorHelpers)
      row "traceAndGasHelpers   " [] (yulTokens parts.traceAndGasHelpers)
      row "vkLoading            " (inner (GenAst.emitPartial pv .vkLoading)) (yulTokens parts.vkLoading)
      row "transcriptProofParser" (inner (GenAst.emitPartial pv .transcriptParser)) (yulTokens parts.transcriptProofParser)
      row "lagrange             " (inner (GenAst.emitPartial pv .lagrange)) (yulTokens parts.lagrange)
      row "quotientAndLinearize " (inner (GenAst.emitPartial pv .quotientLin)) (yulTokens parts.quotientAndLinearization)
      row "pcs                  " (inner (GenAst.emitPartial pv .pcs)) (yulTokens parts.pcs)
      row "finalPairing         " (inner (GenAst.emitPartial pv .finalPairing)) (yulTokens parts.finalPairing)
      row "traceReturn          " (inner (GenAst.emitPartial pv .traceReturn)) (yulTokens parts.traceReturn)
    | .error _ => IO.println "generateVerifierFromPlan failed"
  | _, _ => IO.println "artifact read failed"

#eval probe
