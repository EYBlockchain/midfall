import Midfall.Instances.DeployedProfile
import Midfall.LoweringV2.Statements

/-! Probe (review scratch, not for the repo): evaluate the V2 codegen-agreement check at the
    deployed poseidon profile, and validate the token offsets the spec assumes. -/

open Midfall Midfall.Generator Midfall.Instances Midfall.LoweringV2
open Midfall.Generator.VerifierPartialKats Midfall.Generator.ContractKats
open Midfall.Generator.QuotientFold

def firstDiff (a b : List String) : Option Nat :=
  (List.range (min a.length b.length)).find? fun i => a.getD i "" != b.getD i ""

def window (l : List String) (i : Nat) : List String := (l.drop (i - 6)).take 14

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
      IO.println s!"abi text head tokens : {(yulTokens (abiGuardText m)).take 7}"
      IO.println s!"abi text last token  : {(yulTokens (abiGuardText m)).getLast?}"
      IO.println s!"main text head tokens: {(yulTokens (mainAssemblyText m)).take 6}"
      let a := yulTokens (YulSemantics.EVM.print (abiGuardBlock m))
      IO.println s!"ABI guard agrees     : {a == abiGuardTokens m}"
      if a != abiGuardTokens m then
        IO.println s!"  ast : {a.take 40}"
        IO.println s!"  text: {(abiGuardTokens m).take 40}"
      let mt := mainAssemblyTokens m
      let astTok := yulTokens (YulSemantics.EVM.print (mainAsmRaw pv))
      IO.println s!"main block agrees    : {astTok == mt}  (AST tokens {astTok.length}, codegen tokens {mt.length})"
      match firstDiff astTok mt with
      | some i =>
        IO.println s!"  first divergence at token {i}"
        IO.println s!"  ast : {window astTok i}"
        IO.println s!"  text: {window mt i}"
      | none => IO.println "  one is a prefix of the other"
      let ct := constTableOf m
      IO.println s!"constTableOf: {ct.length} constants; pinned poseidon table: {Midfall.Lowering.Inline.contractConstants.length}"
      let missing := Midfall.Lowering.Inline.contractConstants.filter fun c => !(ct.contains c)
      IO.println s!"pinned constants not reproduced by constTableOf: {missing.take 10} ({missing.length})"
      IO.println s!"TRANSCRIPT_MPTR = {ct.lookup "TRANSCRIPT_MPTR"}, FR_MODULUS present = {(ct.lookup "FR_MODULUS").isSome}"
    | .error _ => IO.println "generateVerifierFromPlan failed"
  | _, _ => IO.println "artifact read failed"

#eval probe
