-- |
-- Midfall.Instances.YulParseKats
--
-- OBJ.1 (PLAN-V3 V3 row 31, the M2 entry). The instances KAT file for
-- `Midfall.Lowering.YulParse`: the token stream the generator writes, read back as the vendored
-- AST, and compared with the AST the Lean emitters build.
--
-- WHAT IS GATED HERE, AND WHY EACH ONE HAS TEETH.
--
--   * the WHOLE main assembly block (14054 tokens) and the ABI guard block (52 tokens) round-trip:
--     `yulTokens (EVM.print (parseTokens toks)) == toks`. A parser that drops a suffix, or an
--     emitter that prints a token the parser cannot read, reddens this.
--   * every region the Lean emitters produce is compared STRUCTURALLY (`SyntaxEq.stmtsBeq`, the
--     relation D-P13 names) against the parse of the generator text for that region - eight regions,
--     one gate each. Token equality is strictly weaker than this, so this is the stronger clause.
--   * a one-literal mutation of a region's text reddens the region gate (`regionMutationTeeth_ok`).
--     Without it the eight gates above could be satisfied by a parser that ignores its input.
--   * NEGATIVES (W12: a parser with no falsifier is not a gate): an unbalanced-brace stream returns
--     `none`, and so does the real main block with its closing brace dropped, a block whose inner
--     block never closes, and a block that closes and then carries trailing tokens. `parseTokens`
--     requires the whole stream to be consumed, so none of the four can be answered by a partial
--     parse.
--
-- THE TWO UNANNOTATED `#eval` LINES. They are the card's acceptance prints, verbatim, and they print
-- a String containing spaces - which `scripts/kat_gate.py` cannot annotate (an expectation is one
-- token). The same two facts ARE gated, by `mainRtLine_ok` and `guardRtLine_ok`, which pin those
-- exact strings as Bools. The prints are the display; the Bools are the gate.
--
import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Program
import Midfall.Lowering.YulParse

set_option autoImplicit false

namespace Midfall.Instances.YulParseKats

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.Lowering Midfall.Lowering.YulParse YulSemantics YulSemantics.EVM

def ctx : PartialCtx := partialCtxOfVerifier poseidonM

/-- Parse a token stream, print it back, and report the measurement the card asks for. -/
def rt (toks : List String) : String :=
  match parseTokens toks with
  | none => "PARSE FAILED"
  | some blk => s!"parsed stmts={blk.length} roundTrip={yulTokens (EVM.print blk) == toks} tokens={toks.length}"

-- 1. the WHOLE main assembly block of the generator text: parse, print, compare.
#eval rt (mainAssemblyTokens poseidonM)
-- 2. the ABI guard block.
#eval rt (abiGuardTokens poseidonM)

/-- The main block round-trips at the token level, as a gate rather than as a print. -/
def mainRoundTrip_ok : Bool :=
  match parseTokens (mainAssemblyTokens poseidonM) with
  | some blk => yulTokens (EVM.print blk) == mainAssemblyTokens poseidonM
  | none => false
#eval mainRoundTrip_ok -- expect true

/-- The guard block round-trips at the token level. -/
def guardRoundTrip_ok : Bool :=
  match parseTokens (abiGuardTokens poseidonM) with
  | some blk => yulTokens (EVM.print blk) == abiGuardTokens poseidonM
  | none => false
#eval guardRoundTrip_ok -- expect true

/-- The two acceptance lines, pinned as values: 74 statements over 14054 tokens for the main block. -/
def mainRtLine_ok : Bool :=
  rt (mainAssemblyTokens poseidonM) == "parsed stmts=74 roundTrip=true tokens=14054"
#eval mainRtLine_ok -- expect true

/-- ... and 1 statement over 52 tokens for the guard. -/
def guardRtLine_ok : Bool :=
  rt (abiGuardTokens poseidonM) == "parsed stmts=1 roundTrip=true tokens=52"
#eval guardRtLine_ok -- expect true

/-- The parse of a region's generator text, structurally equal to the AST the emitter built. -/
def regOk (text : String) (ast : Block EVM.Op) : Bool :=
  match parseLines [text] with
  | some blk => SyntaxEq.stmtsBeq blk ast
  | none => false

/-- 3. `stmtsBeq` against EACH existing emitter output: the helpers, then the seven partials. -/
def helpersBeq_ok : Bool :=
  regOk (partsOf poseidonM).assemblyHelpers (GenAst.emitHelpers poseidonPv)
#eval helpersBeq_ok -- expect true

def vkLoadingBeq_ok : Bool :=
  regOk (partsOf poseidonM).vkLoading (GenAst.emitPartial poseidonPv .vkLoading)
#eval vkLoadingBeq_ok -- expect true

def transcriptBeq_ok : Bool :=
  regOk (partsOf poseidonM).transcriptProofParser (GenAst.emitPartial poseidonPv .transcriptParser)
#eval transcriptBeq_ok -- expect true

def lagrangeBeq_ok : Bool :=
  regOk (partsOf poseidonM).lagrange (GenAst.emitPartial poseidonPv .lagrange)
#eval lagrangeBeq_ok -- expect true

def quotientLinBeq_ok : Bool :=
  regOk (renderQuotientAndLinearization ctx "" "") (GenAst.emitPartial poseidonPv .quotientLin)
#eval quotientLinBeq_ok -- expect true

def pcsBeq_ok : Bool :=
  regOk (partsOf poseidonM).pcs (GenAst.emitPartial poseidonPv .pcs)
#eval pcsBeq_ok -- expect true

def finalPairingBeq_ok : Bool :=
  regOk (partsOf poseidonM).finalPairing (GenAst.emitPartial poseidonPv .finalPairing)
#eval finalPairingBeq_ok -- expect true

def traceReturnBeq_ok : Bool :=
  regOk (partsOf poseidonM).traceReturn (GenAst.emitPartial poseidonPv .traceReturn)
#eval traceReturnBeq_ok -- expect true

/-- Replace the first occurrence of `needle`. -/
def mutateFirst (needle repl : String) (s : String) : String :=
  match s.splitOn needle with
  | a :: b :: rest => a ++ repl ++ String.intercalate needle (b :: rest)
  | _ => s

/-- THE FALSIFIER FOR THE EIGHT GATES ABOVE: flip one literal in the helpers text and the region gate
    must go false - and the mutation must be a real change of the text, or the falsifier is vacuous. -/
def regionMutationTeeth_ok : Bool :=
  let t := (partsOf poseidonM).assemblyHelpers
  regOk t (GenAst.emitHelpers poseidonPv) &&
    ! regOk (mutateFirst "0x20" "0x21" t) (GenAst.emitHelpers poseidonPv) &&
    t != mutateFirst "0x20" "0x21" t
#eval regionMutationTeeth_ok -- expect true

/-- NEGATIVE KAT. An unbalanced-brace token stream: a block that opens and never closes. -/
def unbalancedToks : List String := ["{", "let", "x", ":=", "1"]

/-- The card's negative: the unbalanced stream returns `none`. Printed as a String so that
    `kat_gate.py` can annotate it - a bare `none` is not a value shape the gate recognises. -/
def negUnbalanced : String :=
  match parseTokens unbalancedToks with
  | none => "none"
  | some _ => "PARSED"
#eval negUnbalanced -- expect "none"

/-- The same failure on the REAL program: the main block with its closing brace dropped is rejected,
    not answered with the statements it managed to read before the stream ran out. -/
def negMainNoClose_ok : Bool :=
  let t := mainAssemblyTokens poseidonM
  (parseTokens (t.take (t.length - 1))).isNone
#eval negMainNoClose_ok -- expect true

/-- An inner block that never closes: `{ { }`. -/
def negInnerUnclosed_ok : Bool := (parseTokens ["{", "{", "}"]).isNone
#eval negInnerUnclosed_ok -- expect true

/-- A block that closes and then carries tokens: `{ } let`. `parseTokens` requires the whole stream
    to be consumed, so trailing junk is a failure and not a successful prefix. -/
def negTrailingJunk_ok : Bool := (parseTokens ["{", "}", "let"]).isNone
#eval negTrailingJunk_ok -- expect true

end Midfall.Instances.YulParseKats
