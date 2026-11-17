import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
set_option autoImplicit false

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.Instances.PoseidonInputs
open Midfall.LoweringV2 Midfall.Lowering YulSemantics YulSemantics.EVM

namespace Cov

def b : PartialCtx := partialCtxOfVerifier poseidonM
def parts : VerifierParts := partsOf poseidonM
def rc : RootCtx := rootCtxOfVerifier poseidonM

/-- tokens of a printed AST fragment, without the braces `EVM.print` adds -/
def inner (blk : Block EVM.Op) : List String := ((yulTokens (EVM.print blk)).drop 1).dropLast

/-- first index where two lists differ (or the shorter length if one is a prefix), none if equal -/
def firstDiff (a t : List String) : Option Nat :=
  let rec go (i : Nat) : List String → List String → Option Nat
    | [], [] => none
    | [], _ :: _ => some i
    | _ :: _, [] => some i
    | x :: xs, y :: ys => if x == y then go (i + 1) xs ys else some i
  go 0 a t

/-- the function names defined in a token stream -/
def funNames : List String → List String
  | "function" :: n :: rest => n :: funNames rest
  | _ :: rest => funNames rest
  | [] => []

def linText : String := renderQuotientAndLinearization b "" ""
def qhText : String := renderQuotientHelpers b
def qnbText : String := renderQuotientNumeratorBlock b

/-- (region, text tokens, AST tokens) in the order of `mainAssemblyText` -/
def regions : List (String × List String × List String) :=
  [ ("guard (vhMainAssemblyOpen - 6, incl. opening brace)",
      (yulTokens vhMainAssemblyOpen).drop 6, "{" :: inner mainGuardBlock)
  , ("AssemblyHelpers", yulTokens parts.assemblyHelpers, inner (GenAst.emitHelpers poseidonPv))
  , ("AccumulatorHelpers", yulTokens parts.accumulatorHelpers, [])
  , ("TraceAndGasHelpers", yulTokens parts.traceAndGasHelpers, [])
  , ("verifierDirectSection", yulTokens (verifierDirectSection rc), [])
  , ("mainLocals (vhAfterTraceAndGas)", yulTokens vhAfterTraceAndGas, inner mainLocals)
  , ("VkLoading", yulTokens parts.vkLoading, inner (GenAst.emitPartial poseidonPv .vkLoading))
  , ("TranscriptProofParser", yulTokens parts.transcriptProofParser,
      inner (GenAst.emitPartial poseidonPv .transcriptParser))
  , ("Lagrange", yulTokens parts.lagrange, inner (GenAst.emitPartial poseidonPv .lagrange))
  , ("Q&L / QuotientHelpers", yulTokens qhText, [])
  , ("Q&L / QuotientNumeratorBlock", yulTokens qnbText, [])
  , ("Q&L / linearization scope", yulTokens linText,
      inner (GenAst.emitPartial poseidonPv .quotientLin))
  , ("Pcs", yulTokens parts.pcs, inner (GenAst.emitPartial poseidonPv .pcs))
  , ("FinalPairing", yulTokens parts.finalPairing,
      inner (GenAst.emitPartial poseidonPv .finalPairing))
  , ("TraceReturn", yulTokens parts.traceReturn,
      inner (GenAst.emitPartial poseidonPv .traceReturn))
  , ("closing brace", ["}"], ["}"]) ]

def row (r : String × List String × List String) : String :=
  let (n, t, a) := r
  s!"{n} | text {t.length} | ast {a.length} | agree {t == a} | firstDiffInRegion {firstDiff a t}"

end Cov
open Cov

-- 0. HEAD sanity: totals
#eval (yulTokens (EVM.print (mainAsmRaw poseidonPv))).length
#eval (mainAssemblyTokens poseidonM).length
#eval firstDiff (yulTokens (EVM.print (mainAsmRaw poseidonPv))) (mainAssemblyTokens poseidonM)
#eval codegenAgrees poseidonPv poseidonM
-- guard block (first assembly)
#eval (yulTokens (EVM.print (abiGuardBlock poseidonM)) == abiGuardTokens poseidonM,
       (abiGuardTokens poseidonM).length)

-- 1. the region partition is exact on both sides
#eval (regions.map (fun r => r.2.1)).flatten == mainAssemblyTokens poseidonM
#eval (regions.map (fun r => r.2.2)).flatten == yulTokens (EVM.print (mainAsmRaw poseidonPv))
-- Q&L composite equals the three pieces
#eval yulTokens parts.quotientAndLinearization == yulTokens qhText ++ yulTokens qnbText ++ yulTokens linText

-- 2. the table
#eval IO.println (String.intercalate "\n" (regions.map row))

-- 3. text offsets of each region start (global token index in mainAssemblyTokens)
#eval (regions.foldl (fun (acc : Nat × List (String × Nat)) r => (acc.1 + r.2.1.length, acc.2 ++ [(r.1, acc.1)])) (0, [])).2

-- 4. function definitions
#eval funNames (mainAssemblyTokens poseidonM)
#eval funNames (yulTokens (EVM.print (mainAsmRaw poseidonPv)))
#eval (funNames (mainAssemblyTokens poseidonM)).length
#eval (funNames (yulTokens (EVM.print (mainAsmRaw poseidonPv)))).length
#eval (funNames (mainAssemblyTokens poseidonM)).filter
        (fun n => !(funNames (yulTokens (EVM.print (mainAsmRaw poseidonPv)))).contains n)
-- per-region function names in the text
#eval regions.filterMap (fun r => let f := funNames r.2.1; if f.isEmpty then none else some (r.1, f))

-- 5. PCS detail: non-brace tokens identical?
def nb (l : List String) : List String := l.filter (fun t => t != "{" && t != "}")
#eval let t := yulTokens parts.pcs
      let a := inner (GenAst.emitPartial poseidonPv .pcs)
      (t.length, a.length, (nb t).length, nb t == nb a)

-- 6. slice lengths in statements
#eval Midfall.Lowering.partials.map (fun q => (GenAst.emitPartial poseidonPv q).length)
