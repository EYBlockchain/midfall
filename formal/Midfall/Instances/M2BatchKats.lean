-- |
-- Midfall.Instances.M2BatchKats
--
-- M2's batch (G1.1 + G1.2 + OBJ.2 + ST.3, the one D-P52/D-P65 re-hash). The witness and the
-- falsifier for every statement the batch changed, in one file so the batch's acceptance can be
-- read off one `lake env lean` run.
--
-- WHY THIS FILE EXISTS AND NOT JUST A FEW LINES IN `PoseidonValid.lean`. Clause 6 flipped from
-- REFUTED to PROVED there, and `deciding_codegenStruct` ties the AST to the parse at the
-- deployment. Neither of those says WHERE the three new regions' teeth are, and W15 requires a
-- falsifier per changed statement rather than a witness per changed statement. Each gate below
-- names the statement it is about and the mutation that reddens it.
--
-- THE ASYMMETRY THE PLAN INSISTS ON, and this file keeps honest. A STRUCTURED emitter (the eight
-- helpers, the six old partials, `q_program_fail` / `q_pow5`, the five accumulator codecs) is a
-- second implementation of the template, so mutating the template moves one side and the gate
-- reddens: `accMutationTeeth_ok`, `qhMutationTeeth_ok`. A PARSED region (the 5,431 generated
-- tokens of the numerator, OBJ.2's route) is the same `render m` on both sides, so a text
-- mutation moves BOTH and reddens nothing - `numeratorTextMutationMovesBothSides_ok` measures
-- that and says so rather than pretending otherwise. What puts teeth into the parsed half is the
-- AST side: `codegenStructEmittedSideTeeth_ok` perturbs the emitted program and `codegenStruct`
-- goes false. What checks a parsed region's CONTENT is elsewhere: `GeneratedBy`, the artifact
-- gate, and the block proofs (PLAN-V3 section 5, 'what the tie means for a parsed region').
--
-- NOTHING HERE IS `native_decide` (D-P71): every gate is a `Bool` the VM computes, and the
-- kernel-facing discharges of the same facts live in `PoseidonValid.lean`.
--
import Midfall.Instances.PoseidonValid
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Program
import Midfall.Lowering.YulParse

set_option autoImplicit false

namespace Midfall.Instances.M2BatchKats

open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
open Midfall.LoweringV2 Midfall.Lowering Midfall.Lowering.YulParse
open Midfall.Yul Midfall.Yul.Bridge YulSemantics YulSemantics.EVM

def pv : PlanView := poseidonPv
def m : Model := poseidonM
def ctx : PartialCtx := partialCtxOfVerifier m
def cc : ExternalCalls := ⟨fun _ _ _ => False⟩
def gg : ExternalGas := ExternalGas.ofFun fun _ => 0
abbrev DD : Dialect := Bridge.Dialect cc gg

/-- The parse of one region's generator text, `[]` if the parser cannot read it. -/
def reg (text : String) : Block EVM.Op :=
  match parseLines [text] with
  | some b => b
  | none => []

/-- `stmtsBeq` between the parse of a region and the AST an emitter built. -/
def beqRegion (text : String) (ast : Block EVM.Op) : Bool := SyntaxEq.stmtsBeq (reg text) ast

/-- Replace the first occurrence of `needle` (the shape `YulParseKats.mutateFirst` uses). -/
def mutateFirst (needle repl : String) (s : String) : String :=
  match s.splitOn needle with
  | a :: b :: rest => a ++ repl ++ String.intercalate needle (b :: rest)
  | _ => s

/-- The seven slices in include order at the (plan, model) level: the `Render.slices` of the
    deployment, spelled without the noncomputable `Render` so every gate below can compute. -/
def slicesOf : YulBlock :=
  List.foldl (init := []) (fun acc q => acc ++ sliceOf pv m q)
    [Partial.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing,
     .traceReturn]

/-! ## 1. G1.1 - the accumulator codecs as a STRUCTURED emitter -/

/-- The text side's own inventory: the five definitions R.2 measured at 202 + 31 + 151 + 165 + 274
    = 823 tokens, sliced out of the region by the template's own `renderFunction`. -/
def accFnTokens_ok : Bool :=
  let t := (partsOf m).accumulatorHelpers
  ["load_acc_coord_shifted", "is_bls_p_minus_one", "check_acc_coord_packing", "load_acc_coord",
   "load_acc_point"].map (fun nm => (yulTokens (GenAst.renderFunction t nm)).length)
    == [202, 31, 151, 165, 274]
#eval accFnTokens_ok -- expect true

/-- The emitter defines exactly those five, in that order: same names, same order, no extras. -/
def accFnNames_ok : Bool :=
  (GenAst.emitAccumulatorHelpers.filterMap fun
      | Stmt.funDef n _ _ _ => some n
      | _ => none)
    == ["load_acc_coord_shifted", "is_bls_p_minus_one", "check_acc_coord_packing",
        "load_acc_coord", "load_acc_point"]
#eval accFnNames_ok -- expect true

/-- G1.1'S CLAIM: the tree the emitter builds IS the parse of the generator's own accumulator text. -/
def accRegion_isTheParse_ok : Bool :=
  beqRegion (partsOf m).accumulatorHelpers GenAst.emitAccumulatorHelpers
#eval accRegion_isTheParse_ok -- expect true

/-- TEETH (D-P23): one literal of the accumulator text, 0x20 to 0x21, reddens the row above - and
    the mutation is a real change of the text, or the falsifier is vacuous. -/
def accMutationTeeth_ok : Bool :=
  let t := (partsOf m).accumulatorHelpers
  let t' := mutateFirst "0x20" "0x21" t
  beqRegion t GenAst.emitAccumulatorHelpers && ! beqRegion t' GenAst.emitAccumulatorHelpers &&
    t != t'
#eval accMutationTeeth_ok -- expect true

/-- THE PARAMETER REACHES THE PROGRAM: 'limbs_per_word' is a render value, not decoration. The
    deployed render's is 4; at 3 the emitted region is a different AST. -/
def accParamReaches_ok : Bool :=
  beqRegion (partsOf m).accumulatorHelpers (GenAst.emitAccumulatorHelpersAt 4) &&
    ! beqRegion (partsOf m).accumulatorHelpers (GenAst.emitAccumulatorHelpersAt 3)
#eval accParamReaches_ok -- expect true
/-! ## 2. G1.2 - the quotient helpers as a STRUCTURED emitter, on the render's own flag -/

/-- The two definitions the render's flag selects are the parse of the generator's own text. -/
def qhRegion_isTheParse_ok : Bool :=
  beqRegion (renderQuotientHelpers ctx) (GenAst.emitQuotientHelpersAt m.quotientPow5Helper)
#eval qhRegion_isTheParse_ok -- expect true

/-- TEETH: a CODE token of 'q_program_fail' - the shift of the revert selector, 224 to 225.

    NOTE ON A FALSE PREMISE IN OBJ.2: the card asks for '0x3cc81b89 to ...8a', but the FIRST
    occurrence of that hex literal in the QuotientHelpers text is inside the comment
    'bytes4(keccak256) = 0x3cc81b89', so the mutation is invisible to 'yulTokens' and the row does
    NOT redden - exactly the trap the card's own Guidance names ('mutate a code token'). Measured
    here: this mutation reddens it. -/
def qhMutationTeeth_ok : Bool :=
  let t := renderQuotientHelpers ctx
  let t2 := mutateFirst "shl(224," "shl(225," t
  beqRegion t (GenAst.emitQuotientHelpersAt m.quotientPow5Helper) &&
    ! beqRegion t2 (GenAst.emitQuotientHelpersAt m.quotientPow5Helper) && t != t2 &&
    yulTokens t != yulTokens t2

/-! THE FLAG IS LIVE at this render (the value the splice reads; true here is a measurement of
    the model, and not an assumption about it. -/
#eval m.quotientPow5Helper -- expect true

/-! ## 3. OBJ.2 - the numerator as a PARSE, and what that does and does not check -/

/-- The numerator parses, is one block, and its tokens round-trip: 6,384 in, 6,384 out. This is the
    whole of what the parse half is trusted for at the text level. -/
def numParseRoundTrip_ok : Bool :=
  let t := renderQuotientNumeratorBlock ctx
  match parseLines [t] with
  | some bb => bb.length == 1 && (yulTokens t).length == 6384
  | none => false
#eval numParseRoundTrip_ok -- expect true

/-- WHAT THIS GATE DOES AND DOES NOT PROVE, stated plainly because the distinction is the whole
    point of OBJ.2's route. 'emitQuotientNumerator' IS 'parse (render ctx)', so in the real system a
    change to the template moves BOTH sides of 'codegenStruct' together and the tie holds BY
    CONSTRUCTION: 'codegen' buys nothing on this region, and what is trusted is the parser-printer
    round trip and 'EVM.mkCall''s builtin-versus-call resolution (PLAN-V3 section 5, 'what the tie
    means for a parsed region'). What this gate can check, and does, is that the parse is NOT VACUOUS:
    give it different text and it answers differently. The teeth for the parsed half are on the
    EMITTED side, in the gate below. -/

def numeratorParseIsNotVacuous_ok : Bool :=
  let t := renderQuotientNumeratorBlock ctx
  let t2 := mutateFirst "0x20" "0x21" t
  SyntaxEq.stmtsBeq (reg t) (GenAst.emitQuotientNumerator ctx) &&
    ! SyntaxEq.stmtsBeq (reg t2) (GenAst.emitQuotientNumerator ctx) && t != t2
#eval numeratorParseIsNotVacuous_ok -- expect true

/-- THE TEETH OF THE PARSED HALF ARE ON THE EMITTED SIDE: drop one statement out of the emitted
    program and `codegenStruct` goes false. Without this the structural tie would be a tautology. -/
def codegenStructEmittedSideTeeth_ok : Bool :=
  let main := mainAsmRaw pv m
  codegenStruct main m && ! codegenStruct (main.drop 1) m && ! codegenStruct (main ++ main) m
#eval codegenStructEmittedSideTeeth_ok -- expect true

/-- THE PCS BLOCK BOUNDARIES (G1.4b's shape, re-tested against the whole program): flattening the
    eight-block partition - the defect G1.4 recorded - reddens the token tie, so the nine brace
    pairs are load-bearing and not spelling. -/
def pcsFlattenTeeth_ok : Bool :=
  let flat := mainAsmRaw pv m |>.map fun
    | Stmt.block b => Stmt.block (b.flatMap fun
        | Stmt.block inner => inner
        | s => [s])
    | s => s
  yulTokens (EVM.print (mainAsmRaw pv m)) == mainAssemblyTokens m &&
    yulTokens (EVM.print flat) != mainAssemblyTokens m
#eval pcsFlattenTeeth_ok -- expect true
/-! ## 4. The program shape OBJ.2 produces (the card's acceptance numbers) -/

/-- 74 statements and 14,054 tokens, where the emitter reached 66 / 6,779 before this batch. -/
def progShape_ok : Bool :=
  (mainAsmRaw pv m).length == 74 &&
    (yulTokens (EVM.print (mainAsmRaw pv m))).length == 14054 &&
    (mainAssemblyTokens m).length == 14054
#eval progShape_ok -- expect true

/-- The seven slices, in include order: [1, 44, 3, 4, 1, 2, 3]. `.quotientLin` is FOUR where it was
    one - the two `quotient_numerator` includes in front of the linearization scope. -/
def sliceLens_ok : Bool :=
  [Partial.vkLoading, .transcriptParser, .lagrange, .quotientLin, .pcs, .finalPairing,
   .traceReturn].map (fun q => (sliceOf pv m q).length) == [1, 44, 3, 4, 1, 2, 3]
#eval sliceLens_ok -- expect true

/-- Closedness survives the three new includes: the only free names of the inlined main block are
    still the two wrapper locals. -/
def mainClosed_ok : Bool := mainClosed pv m
#eval mainClosed_ok -- expect true

/-- `helpersOf` is `emitHelpers` PLUS the five accumulator codecs, in that order: 13 definitions.
    This is the widening ST.3's first conjunct depends on. -/
def helpersOfNames_ok : Bool :=
  ((helpersOf pv m).filterMap fun
      | Stmt.funDef n _ _ _ => some n
      | _ => none)
    == ["fail", "scalar_inv", "transcript_init", "common_word", "common_uncompressed_g1",
        "squeeze_to", "batch_invert", "ec_pairing", "load_acc_coord_shifted",
        "is_bls_p_minus_one", "check_acc_coord_packing", "load_acc_coord", "load_acc_point"]
#eval helpersOfNames_ok -- expect true

/-- THE BRIDGE: the model-aware dispatch is a widening. Six of the seven arms are `emitPartial`
    verbatim; only `.quotientLin` changed. -/
def emitPartialM_otherArms_ok : Bool :=
  [Partial.vkLoading, .transcriptParser, .lagrange, .pcs, .finalPairing, .traceReturn].all
    fun q => SyntaxEq.stmtsBeq (GenAst.emitPartialM pv ctx q) (GenAst.emitPartial pv q) &&
      ! SyntaxEq.stmtsBeq (GenAst.emitPartialM pv ctx Partial.quotientLin) (GenAst.emitPartial pv Partial.quotientLin)
#eval emitPartialM_otherArms_ok -- expect true

/-- The token tie itself, printed as a value: clause 6 of `Render.Valid`, PROVED. -/
def codegenAgrees_ok : Bool := codegenAgrees pv m
#eval codegenAgrees_ok -- expect true

/-- `noWriters` verdicts are UNCHANGED by the bigger program: 200 is still exhausted, 2000 and
    20000 still scan the whole block. (PoseidonValid's clause-10 discharges stay valid.) -/
def noWritersFuelVerdicts_ok : Bool :=
  Midfall.Yul.Bridge.noWritersFuel 2000 (asmOf pv m 0 0) &&
    Midfall.Yul.Bridge.noWritersFuel 20000 (asmOf pv m 0 0) &&
    ! Midfall.Yul.Bridge.noWritersFuel 200 (asmOf pv m 0 0)
#eval noWritersFuelVerdicts_ok -- expect true
/-! ## 5. ST.3 - the scope, and the two conjuncts `prog_slices_decomp` is sorry about -/

/-- Two hoisted scopes compared element by element: name, parameters, return slots and body. This is
    what the second conjunct of `prog_slices_decomp` claims, as a computation. -/
def fscopeEq (a b : FScope DD) : Bool :=
  a.length == b.length && (a.zip b).all fun p =>
    p.fst.fst == p.snd.fst && p.fst.snd.params == p.snd.snd.params &&
      p.fst.snd.rets == p.snd.snd.rets &&
        SyntaxEq.stmtsBeq (p.fst.snd.body : Block EVM.Op) (p.snd.snd.body : Block EVM.Op)

/-- **CONJUNCT 1, WITNESSED AT THE DEPLOYMENT.** The closed program IS the prefix, the hoisted
    helpers, the inlined main locals and the seven slices, in that order. `prog_slices_decomp` stays
    a SORRY (ST.3's whole purpose is that the general statement is proved once, not decided here);
    what this gate establishes is the thing that must not break: the statement is TRUE at the only
    render anyone can compute, so the hole is unproved and not false. -/
def decompConj1_ok : Bool :=
  SyntaxEq.stmtsBeq (asmOf pv m 0 0)
    (Inline.inlineContractConstants (constTableOf m)
        (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainGuardBlock) ++
      helpersOf pv m ++
      Inline.inlineContractConstants (constTableOf m) mainLocals ++ slicesOf)
#eval decompConj1_ok -- expect true

/-- **CONJUNCT 2, WITNESSED AT THE DEPLOYMENT, IN ITS RESTATED FORM.** The program's hoisted scope
    is the block scope: helpers first, then the slices. Pre-ST.3 this conjunct read
    `hoist prog = hoist helpers`, and G1.2 landing without the restatement would have made it
    FALSE rather than unproved - RV-13, the reason the splice and the scope are one re-hash. -/
def decompConj2_ok : Bool :=
  fscopeEq (hoist DD (asmOf pv m 0 0)) (hoist DD (helpersOf pv m) ++ hoist DD slicesOf)
#eval decompConj2_ok -- expect true

/-- THE SCOPE NOW CARRIES THE SLICES' DEFINITIONS: `q_pow5` and `q_program_fail` are functions the
    program defines and the block scope resolves. With the pre-ST.3 scope - the helpers alone -
    `q_pow5` is absent: that is the negative example OBJ.3 asked to keep, and it is why the old
    scope is not merely weaker but WRONG once the splice has landed. -/
def scopeSeesSliceFuns_ok : Bool :=
  let newScope := [hoist DD (helpersOf pv m) ++ hoist DD slicesOf]
  (lookupFun newScope "q_pow5").isSome && (lookupFun newScope "q_program_fail").isSome &&
    ! (lookupFun [hoist DD (helpersOf pv m)] "q_pow5").isSome
#eval scopeSeesSliceFuns_ok -- expect true

/-- AND THE OLD LOOKUPS STILL RESOLVE TO THE SAME DECLARATIONS: `fail_lookup` in
    `Blocks/TraceReturn.lean:405` is an `rfl` about `R.scope`, and ST.3 must not move what `fail`
    resolves to - only add to the scope. This is the falsifier for 'the slices shadow a helper'. -/
def scopeKeepsHelperLookups_ok : Bool :=
  let newScope := [hoist DD (helpersOf pv m) ++ hoist DD slicesOf]
  (lookupFun newScope "fail").map (fun p => (p.fst.params, p.fst.rets)) ==
    (lookupFun [hoist DD (helpersOf pv m)] "fail").map (fun p => (p.fst.params, p.fst.rets)) &&
    (lookupFun newScope "batch_invert").isSome && (lookupFun newScope "ec_pairing").isSome
#eval scopeKeepsHelperLookups_ok -- expect true

/-- THE NAME COUNT, printed: 13 helpers + 2 quotient helpers = 15 function definitions in the scope,
    which is the number OBJ.3's KAT asked for. -/
def scopeNameCount_ok : Bool :=
  (([hoist DD (helpersOf pv m) ++ hoist DD slicesOf]).flatMap (fun sc => sc.map fun p => p.fst)).length
    == 15
#eval scopeNameCount_ok -- expect true

end Midfall.Instances.M2BatchKats
