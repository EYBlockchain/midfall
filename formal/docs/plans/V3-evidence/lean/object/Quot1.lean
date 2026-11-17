import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs
open Midfall.LoweringV2 Midfall.Lowering YulSemantics YulSemantics.EVM

def b : PartialCtx := partialCtxOfVerifier poseidonM
def tk (ls : List String) : Nat := (yulTokens (String.intercalate "\n" ls)).length
def kw (ls : List String) (k : String) : Nat := ((yulTokens (String.intercalate "\n" ls)).filter (· == k)).length

-- generated-line families of the numerator block: (lines, tokens)
#eval ("inline", b.quotientInlineComputations.map List.length, tk b.quotientInlineComputations.flatten)
#eval ("evalNumer", b.quotientEvalNumerComputations.map List.length, tk b.quotientEvalNumerComputations.flatten)
#eval ("nativePerm", b.quotientNativePermutationComputation.length, tk b.quotientNativePermutationComputation)
#eval ("nativeLookup", b.quotientNativeLookupComputation.length, tk b.quotientNativeLookupComputation)
#eval ("nativeIdentity", b.quotientNativeIdentityComputations.map List.length, tk b.quotientNativeIdentityComputations.flatten)
#eval ("postVm", b.quotientPostVmComputations.map List.length, tk b.quotientPostVmComputations.flatten)
def allGen : List String :=
  b.quotientInlineComputations.flatten ++ b.quotientEvalNumerComputations.flatten ++
  b.quotientNativePermutationComputation ++ b.quotientNativeLookupComputation ++
  b.quotientNativeIdentityComputations.flatten ++ b.quotientPostVmComputations.flatten
#eval ("all generated lines", allGen.length, tk allGen)
#eval ("numerator block total", (yulTokens (renderQuotientNumeratorBlock b)).length)
#eval ("template remainder", (yulTokens (renderQuotientNumeratorBlock b)).length - tk allGen)
-- statement-kind census of the generated lines (what a line parser must handle)
#eval ["let", "if", "for", "switch", "case", "default", "function", "leave", "break", "continue"].map
        (fun k => (k, kw allGen k))
-- user-function calls inside generated lines
#eval (kw allGen "q_pow5", kw allGen "q_program_fail", kw allGen "q_limb7", kw allGen "q_limb7_wide")
-- shapes of line heads in the generated lines
def headOf (l : String) : String :=
  let t := (l.trimAscii).toString
  if t.startsWith "let " then "let"
  else if t.startsWith "mstore(" then "mstore"
  else if t.startsWith "for " then "for"
  else if t.startsWith "if " then "if"
  else if t == "{" then "{"
  else if t == "}" then "}"
  else if (t.splitOn ":=").length == 2 then "assign"
  else "OTHER:" ++ t
#eval (allGen.map headOf).eraseDups
#eval (allGen.map headOf).eraseDups.map fun h => (h, (allGen.filter (fun l => headOf l == h)).length)
-- the template remainder with the model's program flags: which opcode arms render
#eval match b.quotientProgram with
  | some p => s!"len={p.len} ops: pushMemU16={p.opUsage.pushMemU16} add={p.opUsage.add} neg={p.opUsage.neg} foldSel={p.opUsage.foldSelector} mulConstU8={p.opUsage.mulConstU8} addMemU16={p.opUsage.addMemU16} mulMemU16={p.opUsage.mulMemU16} nPerm={p.opUsage.nativePermutation} nLookup={p.opUsage.nativeLookup} nId={p.opUsage.nativeIdentity} foldMain={p.opUsage.foldMain} pow5={p.opUsage.pow5} mul={p.opUsage.mul}"
  | none => "none"
#eval (b.quotientPow5Helper, b.quotientLimb7Helper, b.quotientWideLimb7Helper, b.simpleSelectorCols)
-- AccumulatorHelpers: which ctx fields does the render read? (perturbation probe)
#eval (renderAccumulatorHelpers b == renderAccumulatorHelpers { b with numInstances := 7, k := 9, vkMptr := 1, proofLen := 3 },
       renderAccumulatorHelpers b == renderAccumulatorHelpers { b with expectedHasAccumulator := true },
       (yulTokens (renderAccumulatorHelpers { b with expectedHasAccumulator := true })).length)
