import Midfall.Instances.DeployedProfile

open Midfall Midfall.Generator Midfall.Instances
open Midfall.Generator.VerifierPartialKats Midfall.Generator.ContractKats
open Midfall.Generator.QuotientFold

def count (toks : List String) (t : String) : Nat := (toks.filter (· == t)).length

def stats (name : String) (txt : String) : IO Unit := do
  let t := yulTokens txt
  IO.println s!"{name}: tokens {t.length}, lets {count t "let"}, assigns {count t ":="}, if {count t "if"}, switch {count t "switch"}, for {count t "for"}, function-defs {count t "function"}, staticcall {count t "staticcall"}, keccak256 {count t "keccak256"}, mstore {count t "mstore"}, mload {count t "mload"}, calldataload {count t "calldataload"}"

def probe : IO Unit := do
  let sol ← readDump
  match quotientDeployedCtx sol with
  | some b =>
    stats "assemblyHelpers     " (renderAssemblyHelpers b)
    stats "accumulatorHelpers  " (renderAccumulatorHelpers b)
    stats "vkLoading           " (renderVkLoading b)
    stats "transcriptParser    " (renderTranscriptProofParser b)
    stats "lagrange            " (renderLagrange b)
    stats "quotient+lineariz.  " (renderQuotientAndLinearization b (renderQuotientHelpers b) (renderQuotientNumeratorBlock b))
    stats "  quotientHelpers   " (renderQuotientHelpers b)
    stats "  numeratorBlock    " (renderQuotientNumeratorBlock b)
    stats "pcs (artifact)      " (renderPcs b (pcsDeployedComputations sol))
    stats "finalPairing        " (renderFinalPairing b)
    stats "traceReturn         " (renderTraceReturn b)
    IO.println s!"whole artifact .sol: {(yulTokens sol).length} tokens, {sol.length} bytes"
  | none => IO.println "ctx failed"

#eval probe
