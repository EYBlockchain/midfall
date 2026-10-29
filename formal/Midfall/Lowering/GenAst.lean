-- |
-- Midfall.Lowering.GenAst
--
-- P-AST (docs/plans/P-AST.md), D-P25 and D-P26: the generator emits a real Yul AST.
--
-- WHAT THIS FILE IS FOR. Until now no Lean function returned the Yul AST of a verifier
-- partial: P-13 ported the templates as TEXT renders - VerifierPartials.lean's own header
-- says each renderX returns the BYTES Askama returns - and Surface.blk was an abstract
-- field whose only constraint was main_concat. That is the R-62 defect: a Surface with
-- blk .finalPairing := return(0, 0) satisfies every hypothesis of the ten *_spec theorems
-- and refutes their conclusions, because L.main is free too and moves with it. The repair
-- is structural: the generator gets a real AST function, blk is PINNED to it
-- (Lowering/Partials.lean, BlkIsEmitter), and that pin becomes a hypothesis of each spec
-- theorem. This file is the function.
--
-- CONSTRUCTOR HELPERS, NOT QUOTATION (D-P26). 'yul%' cannot splice a Lean value: it
-- elaborates literal numbers, strings and identifiers only, so a computed constant such
-- as pv.memory.finalPairingScratchMptr cannot appear inside a quotation. Every block here
-- is therefore built with the vendored constructors through the small helpers below. The
-- vendored DSL was NOT extended. The helper route did not prove painful for anything in
-- scope - FinalPairing (both arms), its ec_pairing and fail helpers, or the seven-slice
-- concatenation - so there is no DSL-change request in this package. P-AST2 re-ran that
-- finding on the two hardest remaining shapes and it still holds: Lagrange needs five
-- for-loops with their own init/cond/post blocks, a TWO-NAME assignment
-- ('success, lagrange_precompile_failed := batch_invert(..)') and nested scopes, and every
-- one of them is a constructor in Ast.lean (Stmt.forLoop, Stmt.assign with a List of
-- targets, Stmt.block). Two helpers were added - yfor and ysetN - and neither is a DSL
-- change: they are Lean functions returning Stmt, exactly like ylet and yset. So there is
-- still no case for splicing values into yul%.
--
-- WHAT IS EMITTED, and what is a placeholder. Scope is per-deployment first (D-P24). P-AST
-- took ONE partial completely - FinalPairing plus the two AssemblyHelpers definitions it
-- calls (fail, ec_pairing). P-AST2 (docs/plans/P-AST2-lagrange-traceReturn.md) adds two
-- more under D-P30, P-AST3a (docs/plans/P-AST3a-quotientLin.md) a fourth, P-AST3b
-- (docs/plans/P-AST3b-vkLoading.md) a fifth and P-AST4
-- (docs/plans/P-AST4-transcriptParser.md) a sixth. P-PLANVIEW (docs/plans/P-PLANVIEW.md)
-- adds the seventh - pcs - so ALL SEVEN partials are emitted from a real AST and
-- emitPlaceholder is unreachable from the dispatcher: the match in GenAstDispatch.emitPartial
-- is exhaustive over the seven constructors with no wildcard arm, placeholderPartials is
-- proved empty by placeholderPartials_nil, and the def survives only because the
-- falsification plants in Instances/SurfaceFixture.lean compare against it.
--
-- THE CLAIM THIS FILE USED TO MAKE ABOUT pcs, AND WHY IT WAS WRONG. Until P-STR2AST the
-- header said an AST emitter for the generated PCS region CANNOT exist: the reasoning was
-- that Kzg.computations returns List (List String), there is no runtime Yul parser in the
-- vendored tree, and so no AST could be recovered from the text port. Every step of that was
-- sound and the conclusion was still false, because it reasoned from the text port outward
-- instead of from the plan inward: P-STR2AST rebuilt the emitter as computationsAst out of
-- the same plan values the text port interpolates, gated it block for block against the text
-- under both relations, and the parser was never needed. What actually blocked the wiring was
-- one level up - PlanView carried neither a ConstraintSystemMeta nor a Data, the two inputs
-- computationsAst needs - and P-PLANVIEW added them. Recorded at length because a
-- "cannot exist" claim in a header is the most expensive kind of stale comment: three
-- packages repeated it without re-deriving it.
--
-- WHAT REMAINS TRUE OF THE DEPLOYED PROFILE, and it is narrower. The seventh arm is real but
-- at the poseidon plan view it emits NOTHING, because poseidonMeta's protocol field is the
-- default - the circuit is not in the tree - so there is no query schedule, no intermediate
-- point set, and the KZ:943-945 early return fires. The emitter is exercised at a DERIVED
-- circuit instead (Encoding.lean's metaFixture over Protocol.lean's fixtureCs). Both halves
-- are gated: GenAstDispatch.emitPcsDependsOnPlanView_ok and
-- DeployedProfile.pcs_deployedGap_measured_ok.
--
-- P-AST4 is the largest conversion so far by a wide margin - the deployed parser arm is 318
-- template lines / 17,136 bytes against vkLoading's 74 / 4,494 - and it is the first slice
-- whose emitted shape depends on a LIST (the user-phase loop) and not on scalars alone. A
-- spec theorem whose partial is not in emittedPartials used to be pinned to a placeholder;
-- since P-PLANVIEW there is no such partial, and every one of the ten *_spec theorems is
-- pinned to a real emitted program.
--
-- D-P30: THE TEXT PORT IS A REFERENCE, NOT THE DELIVERABLE. Every function in this file
-- builds Block/Stmt/Expr EVM.Op from the vendored package; no raw string expression is
-- emitted anywhere, and the renderX functions of VerifierPartials.lean are kept only as the
-- independent second source each gate compares against. PLAN section 8's equation
-- render g o = (lower g o).map print holds BY CONSTRUCTION for the five slices here, and
-- the checks that say so are the stmtsBeq gates, not the token gates: P-AST measured that
-- spelling every mcopy as a USER call leaves all four token gates green and reddens only
-- stmtsBeq, and P-AST2, P-AST3a and P-AST3b each re-reproduced the blindness on their own
-- slice, so
-- emitLagrange_beq_ok, emitTraceReturn_beq_ok, emitQuotientLin_beq_ok, emitVkLoading_beq_ok
-- and the four emit*_DetectsBuiltinVsCall_ok gates are the records and yulTokens is the
-- tripwire. Gate 34 is the sharpest form of the blindness in the whole file: the mis-spelled
-- constructor is the outermost expression of NINE of the thirteen statements of the emitted
-- scope, so a converter reaching for ycall on the success chain mis-spells nine sites and
-- every token gate in the file stays green.
--
-- NUMERIC SPELLING IS A DOCUMENTED DIVERGENCE, NOT A FAILURE (D-P30 clause 3). The AST
-- stores Literal.number (n : Nat) and EVM.print renders it in DECIMAL; the Rust and the
-- text port render the same constants in HEX through the Askama hex filter - the emitted
-- 'add(mptr, 320)' is the render's 'add(mptr, 0x0140)'. The mapping is pinned by
-- numericSpellingDivergence_ok rather than normalised away, because the two spellings are
-- one of the two reasons "compare modulo comments" reports differences on identical code
-- (the other being line breaks), and a later package that "fixes" the decimal printing
-- would break the token comparator's hex-to-value reduction.
--
-- OUT OF SCOPE, AND STAYING OUT: the SOLIDITY wrapper - Contracts.lean's Constructors.sol,
-- Constants.sol, PrecompileSmoke.sol and the three contract shells - is not Yul, has no
-- AST, and stays text with the line-based normaliser (D-P30, "explicitly out of scope").
-- Nothing in this file emits Solidity, and a later package must not try to convert those
-- four artifacts to AST emission; there is no Block to build.
--
-- PRODUCTION PROFILE ONLY. blk takes (Partial, PlanView) and PlanView carries no
-- diagnostics, so the emitter produces the production arm: no gas_checkpoint calls, and
-- for FinalPairing the reverting arm of the trace if rather than the iszero(iszero(..))
-- one. That is not a silent restriction - every *_spec theorem already hypothesises
-- SupportedS, whose production clause is exactly o.diagnostics.trace = false and
-- o.diagnostics.gasCheckpoints = false. The pin and the theorem's own hypotheses describe
-- the same profile. For TraceReturn the same restriction bites harder: the render's trace
-- arm interpolates numInstances, k, the user-phase challenge loop, numTrashcans and
-- expectedHasAccumulator into 53 template lines. P-AST3b narrowed that gap without closing
-- it, and P-AST4 narrows it further without closing it either: PlanView now carries the phase
-- list and the trashcan count the trace arm needs, but it still has NO trace flag, so the
-- trace arm remains inexpressible in this emitter's signature - see the note on
-- emitTraceReturnBlock. What P-AST4 does close is the parser's own gap: the six values
-- transcriptParser interpolates are now fields, and the four helpers it calls are now
-- emitted.
--
-- HOW THE EMITTED AST IS CHECKED. There is no runtime Yul parser in the vendored tree, so
-- the check is the one D-P25 names: the token comparator yulTokens (YulGolden.lean)
-- applied to EVM.print of the emitted AST against the TEXT PORT's render of the same
-- partial under the same profile. Printed text is NOT compared - R-62 measured that
-- normalise_sol.py reports differences on identical code (Lagrange 73 vs 60 lines,
-- FinalPairing 6 vs 3) purely from line breaks and decimal-vs-hex spelling, and a
-- tripwire that fires on identical input is worse than none. yulTokens drops comments
-- (which D-P13 puts outside the equality) and reduces hex literals to values, so the
-- comparison is about the program. It is the SECONDARY relation: YulGolden's header
-- explains that stmtsBeq is authoritative and strictly finer, because it separates
-- Expr.builtin from Expr.call and the token stream cannot. Both are gated here -
-- emitFinalPairing_tokens_ok against the text port and emitFinalPairing_beq_ok against
-- the yul% quotation that already existed as a fixed snapshot. Gates 12 and 13 add the
-- same quotation-versus-constructor check for ec_pairing and for the accumulator arm, which
-- the token gates alone cannot make: measured in this package, spelling every mcopy as a
-- call to a user function named mcopy leaves all four token gates green and reddens only
-- the stmtsBeq ones.
--
-- NON-VACUITY (D-P23, R-41). Satisfiability: Instances/SurfaceFixture.lean exhibits
-- BlkIsEmitter at realSurface, whose main block is literally emitMain (GenAstDispatch.lean
-- since P-PLANVIEW, because the dispatch has to see the pcs emitter too - see that file's
-- header for the import direction).
-- Falsifiability: the same file plants a blk that keeps main_concat TRUE and still fails
-- the pin, and plants the R-62 counterexample block itself. Within this file,
-- emitDependsOnPlan_ok shows the emitter is a function of its arguments and not a
-- constant, emitDetectsPerturbation_ok shows one changed literal turns both relations
-- red, and emitDetectsBuiltinVsCall_ok shows the wrong constructor choice turns stmtsBeq
-- red while the token gate stays green - the asymmetry, reproduced on this file's AST.

import Midfall.Lowering.Types
import Midfall.Lowering.Checkpoint
import Midfall.Lowering.Inv
import Midfall.Generator.VerifierPartials
import YulSemantics.Syntax
import YulSemantics.PrettyPrint

namespace Midfall.Lowering.GenAst
open YulSemantics YulSemantics.EVM Midfall.Generator

/-! ### Constructor helpers (D-P26)

    The names are the ones a later package reuses: 'yvar' a named local or constant,
    'ylit' a number literal, 'yop' a dialect built-in, 'ycall' a call to a USER function.
    The last two are the distinction the token comparator cannot make and stmtsBeq can
    (YulGolden.lean's header), so every site below chooses between them deliberately:
    mstore / mcopy / staticcall / add / eq / .. are dialect built-ins, and fail and
    ec_pairing are user-defined functions (AssemblyHelpers.yul:4 and :269). -/

/-- A Yul identifier use: a local, or one of the Solidity-level constants the render emits
    bare (PAIRING_RHS_MPTR, ERR_PRECOMPILE_FAILED, r). -/
def yvar (s : String) : Expr Op := .var s

/-- A number literal. Printed in decimal, compared by value. -/
def ylit (n : Nat) : Expr Op := .lit (Literal.number n)

/-- A dialect built-in applied to arguments. -/
def yop (o : Op) (args : List (Expr Op)) : Expr Op := .builtin o args

/-- A call to a user-defined function. -/
def ycall (nm : String) (args : List (Expr Op)) : Expr Op := .call nm args

/-- An expression in statement position. -/
def yexpr (e : Expr Op) : Stmt Op := .exprStmt e

/-- 'v := e'. -/
def yset (v : String) (e : Expr Op) : Stmt Op := Stmt.assign [v] e

/-- 'let v := e'. -/
def ylet (v : String) (e : Expr Op) : Stmt Op := Stmt.letDecl [v] (some e)

/-- 'if c { body }'. Yul has no else. -/
def yif (c : Expr Op) (body : List (Stmt Op)) : Stmt Op := Stmt.cond c body

/-- A nested '{ body }' block, i.e. a new scope. -/
def yblock (body : List (Stmt Op)) : Stmt Op := Stmt.block body

/-- 'for { init } c { post } { body }'. The three sub-blocks are separate statement lists in
    the AST (Ast.lean:90), which is why the Lagrange loops have to name them individually
    rather than quote a header line: the render's multi-line for headers
    ('for { let a := ..\n let b := .. } cond { post }') are a printing artefact, and the
    token comparator sees the same stream either way. -/
def yfor (init : List (Stmt Op)) (c : Expr Op) (post body : List (Stmt Op)) : Stmt Op :=
  Stmt.forLoop init c post body

/-- 'v, w := e' - an assignment to MORE THAN ONE variable, which 'yset' cannot express.
    Lagrange.yul:34 is the only site in the three real slices that has one:
    'success, lagrange_precompile_failed := batch_invert(..)', the MF-4 two-value return. -/
def ysetN (vs : List String) (e : Expr Op) : Stmt Op := Stmt.assign vs e

/-- 'function name(params) -> rets { body }'. An empty rets list prints no '->' arm. -/
def yfun (name : String) (params rets : List String) (body : List (Stmt Op)) : Stmt Op :=
  Stmt.funDef name params rets body

/-- The value of a '0x'-prefixed hex literal string. The domain tag the accumulator arm
    stores is a String in TemplateConstants (the template interpolates it verbatim), so the
    AST path has to parse it. YulGolden.lean's own hex reader is reused rather than a
    second copy being written here - check_duplicate_facts.py exists because copies of one
    fact drift. -/
def hexLiteral (s : String) : Nat := hexVal ((s.drop 2).toString)

/-- Leading and trailing spaces and tabs removed. Lean core has no String.trim at this
    toolchain, and the slicer below needs to recognise an indented line by its content. -/
def trimWs (s : String) : String :=
  let sp (c : Char) : Bool := c == ' ' || c == '\t'
  String.ofList ((s.toList.dropWhile sp).reverse.dropWhile sp |>.reverse)

/-! ### AssemblyHelpers: the two definitions FinalPairing calls -/

/-- 'function fail(sel) { mstore(0x00, shl(224, sel)) revert(0x00, 0x04) }'
    (AssemblyHelpers.yul:4-7).

    NOT parameterised, and that is a measurement rather than an omission: the template's
    fail arm interpolates nothing - 0x00, 224 and 0x04 are literal in the template source,
    which is why the text port's fail arm is a plain string constant too. So the emitted
    AST is a constant function of the plan, and generalising the existing failFunction_ast
    snapshot means generalising nothing here. -/
def emitFail : Block Op :=
  [ yfun "fail" ["sel"] []
    [ yexpr (yop Op.mstore [ylit 0x00, yop Op.shl [ylit 224, yvar "sel"]])
    , yexpr (yop Op.revert [ylit 0x00, ylit 0x04]) ] ]

/-- The EIP-2537 pairing wrapper (AssemblyHelpers.yul:269-302) as an AST, parameterised by
    the four values the template interpolates: the scratch pointer (memory.rs:512
    final_pairing_scratch_mptr), the pairing precompile address (LM:137 PAIRING_ADDRESS),
    the two-pair input length (LM:82 PAIRING_TWO_PAIR_BYTES) and the output word length
    (LM:17 WORD_BYTES).

    The 0x80 and 0x100 copy lengths and the 'ret := 1' tail are literal in the template and
    stay literal here. 'fail' is a user call - it is defined by emitFail, in the same
    hoisted block - and every other call is a dialect built-in. -/
def emitEcPairing (scratch pairingAddr frameBytes outBytes : Nat) : Block Op :=
  [ yfun "ec_pairing" ["success", "lhs_mptr", "rhs_mptr"] ["ret"]
    [ yset "ret" (yvar "success")
      -- 'leave', not a revert: the trace render returns false and TraceReturn decides.
    , yif (yop Op.iszero [yvar "ret"]) [Stmt.leave]
    , ylet "scratch" (ylit scratch)
      -- [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2 (0x100)]
    , yexpr (yop Op.mcopy [yvar "scratch", yvar "lhs_mptr", ylit 0x80])
    , yexpr (yop Op.mcopy [yop Op.add [yvar "scratch", ylit 0x80],
        yvar "G2_BASE_MPTR", ylit 0x100])
    , yexpr (yop Op.mcopy [yop Op.add [yvar "scratch", ylit 0x180],
        yvar "rhs_mptr", ylit 0x80])
    , yexpr (yop Op.mcopy [yop Op.add [yvar "scratch", ylit 0x200],
        yvar "NEG_S_G2_BASE_MPTR", ylit 0x100])
      -- MF-4: a failed precompile is a chain fault, not a rejected proof.
    , yset "ret" (yop Op.staticcall [yvar "PAIRING_GAS_2PAIR", ylit pairingAddr,
        yvar "scratch", ylit frameBytes, yvar "scratch", ylit outBytes])
    , yset "ret" (yop Op.and [yvar "ret",
        yop Op.eq [yop Op.returndatasize [], ylit outBytes]])
    , yif (yop Op.iszero [yvar "ret"])
        [yexpr (ycall "fail" [yvar "ERR_PRECOMPILE_FAILED"])]
      -- Compare against 1 rather than truncating to the low bit.
    , yset "ret" (yop Op.and [yvar "ret",
        yop Op.eq [yop Op.mload [yvar "scratch"], ylit 1]])
    , yif (yop Op.iszero [yvar "ret"])
        [yexpr (ycall "fail" [yvar "ERR_PROOF_REJECTED"])]
    , yset "ret" (ylit 1)
    ] ]

/-- The pairing constants the helpers interpolate, in one place: the Rust reads them from
    the same TemplateConstants::default the text port's ctx carries (poseidonCtx sets
    templateConstants := templateConstantsDefault), so both sides take them from Lean's
    port of that impl and neither side can pick a different number. -/
def pairingScratchOf (pv : PlanView) : Nat := pv.memory.finalPairingScratchMptr

/-- emitEcPairing at the plan's own scratch pointer and the default constants. -/
def emitEcPairingAt (pv : PlanView) : Block Op :=
  emitEcPairing (pairingScratchOf pv) templateConstantsDefault.eip2537.pairingAddress
    templateConstantsDefault.pairingTwoPairBytes templateConstantsDefault.wordBytes

/-! ### AssemblyHelpers: the four definitions transcriptParser calls -/

/-- 'function transcript_init() -> buf_len { buf_len := TRANSCRIPT_MPTR }'
    (AssemblyHelpers.yul:107-110, rendered at D:673-676).

    NOT parameterised, and the measurement is the point: the four transcript helpers
    interpolate NOTHING - TRANSCRIPT_MPTR is a bare Solidity-level constant and the '32',
    '0x20', '0x40', '0x60', '0x80', '128' and the two 128-bit masks are literal template
    bytes. So each of the four is a CONSTANT function of the plan, exactly like emitFail and
    emitTraceReturnBlock, and gate 43 below says so as a computation rather than leaving it
    as an adjective: it perturbs the two template constants a reader might guess were behind
    those literals (g1_bytes, word_bytes) and shows the helper render does not move while
    the PARSER render does. That is the difference between "constant because the template is
    literal" and "constant because the converter typed a number", and only the gate tells
    them apart. -/
def emitTranscriptInit : Block Op :=
  [ yfun "transcript_init" [] ["buf_len"]
    [ yset "buf_len" (yvar "TRANSCRIPT_MPTR") ] ]

/-- 'function common_word(buf_len, word) -> ret { mstore(buf_len, word)
    ret := add(buf_len, 32) }' (AssemblyHelpers.yul:114-117, D:680-683).

    The '32' is DECIMAL in the template - the template writes the literal 32 and not the hex
    filter of word_bytes - so the AST prints the same three characters the render does.
    That makes this the one site in the four helpers where the two spellings coincide, and
    gate 21 pins it beside the sites where they do not. -/
def emitCommonWord : Block Op :=
  [ yfun "common_word" ["buf_len", "word"] ["ret"]
    [ yexpr (yop Op.mstore [yvar "buf_len", yvar "word"])
    , yset "ret" (yop Op.add [yvar "buf_len", ylit 32]) ] ]

/-- One coordinate's canonicality check inside common_uncompressed_g1: accept the 128-bit
    high word only if it is below BLS_P_HI, or equal to it with a low word not above
    BLS_P_MINUS_ONE_LO. The x and y copies differ only in the two variable names, which is
    precisely the shape no length or token-count check can separate - hence the shared
    constructor and the stmtsBeq gate. -/
def g1CoordRangeCheck (hi lo : String) : Stmt Op :=
  yif (yop Op.iszero [yop Op.or
    [ yop Op.lt [yvar hi, yvar "BLS_P_HI"]
    , yop Op.and [yop Op.eq [yvar hi, yvar "BLS_P_HI"],
        yop Op.iszero [yop Op.gt [yvar lo, yvar "BLS_P_MINUS_ONE_LO"]]] ]])
    [yexpr (ycall "fail" [yvar "ERR_BAD_POINT_ENCODING"])]

/-- 'function common_uncompressed_g1(buf_len, cptr) -> ret' (AssemblyHelpers.yul:149-170,
    D:715-736): four calldataloads, two top-16-byte rejections, the two 128-bit masks, two
    coordinate range checks, then the verbatim 128-byte memcpy into the transcript buffer.

    Thirteen statements, and the two range checks are the only place in the whole emitter
    where a block statement is written across lines in the render - which is the shape that
    broke the old renderFunction close test (see its header) and the reason gate 11 now
    pins six slice sizes instead of two. 'fail' is a user call; calldataload, shr, and, or,
    lt, eq, gt, iszero, calldatacopy and add are dialect built-ins (EVMOp.lean:43-65). -/
def emitCommonUncompressedG1 : Block Op :=
  [ yfun "common_uncompressed_g1" ["buf_len", "cptr"] ["ret"]
    [ ylet "x_hi_word" (yop Op.calldataload [yvar "cptr"])
    , ylet "x_lo" (yop Op.calldataload [yop Op.add [yvar "cptr", ylit 0x20]])
    , ylet "y_hi_word" (yop Op.calldataload [yop Op.add [yvar "cptr", ylit 0x40]])
    , ylet "y_lo" (yop Op.calldataload [yop Op.add [yvar "cptr", ylit 0x60]])
    , yif (yop Op.shr [ylit 128, yvar "x_hi_word"])
        [yexpr (ycall "fail" [yvar "ERR_BAD_POINT_ENCODING"])]
    , yif (yop Op.shr [ylit 128, yvar "y_hi_word"])
        [yexpr (ycall "fail" [yvar "ERR_BAD_POINT_ENCODING"])]
    , ylet "x_hi" (yop Op.and [yvar "x_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
    , ylet "y_hi" (yop Op.and [yvar "y_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
    , g1CoordRangeCheck "x_hi" "x_lo"
    , g1CoordRangeCheck "y_hi" "y_lo"
    , yexpr (yop Op.calldatacopy [yvar "buf_len", yvar "cptr", ylit 0x80])
    , yset "ret" (yop Op.add [yvar "buf_len", ylit 0x80]) ] ]

/-- 'function squeeze_to(buf_len, mptr) -> ret' (AssemblyHelpers.yul:175-183, D:741-749):
    one keccak256 over the buffer, reseed the digest at the base, sample the Fq as the
    digest mod r, return the new cursor. 'let r := FR_MODULUS' shadows the outer r inside
    this scope and is the template's own line, not a slip - the mod below reads the local. -/
def emitSqueezeTo : Block Op :=
  [ yfun "squeeze_to" ["buf_len", "mptr"] ["ret"]
    [ ylet "h0" (yop Op.keccak256 [yvar "TRANSCRIPT_MPTR",
        yop Op.sub [yvar "buf_len", yvar "TRANSCRIPT_MPTR"]])
    , yexpr (yop Op.mstore [yvar "TRANSCRIPT_MPTR", yvar "h0"])
    , ylet "r" (yvar "FR_MODULUS")
    , yexpr (yop Op.mstore [yvar "mptr", yop Op.mod [yvar "h0", yvar "r"]])
    , yset "ret" (yop Op.add [yvar "TRANSCRIPT_MPTR", ylit 32]) ] ]

/-- The four transcript helpers, in template order (AssemblyHelpers.yul:107-183). -/
def emitTranscriptHelpers : Block Op :=
  emitTranscriptInit ++ emitCommonWord ++ emitCommonUncompressedG1 ++ emitSqueezeTo

/-- The AssemblyHelpers definitions the emitted slices call: fail and ec_pairing for
    FinalPairing, Lagrange and VkLoading, and the four transcript helpers for
    transcriptParser. This is what the pin puts in the 'helpers' slot of main_concat, and it
    is why the pin has a second conjunct at all: mainScope hoists S.L.main, so a Surface
    whose blk is the emitted slice but whose main carries no fail / ec_pairing /
    transcript_init / common_word / common_uncompressed_g1 / squeeze_to definitions emits a
    program in which the emitted slice cannot run.

    THE HELPER GAP SHRINKS BY FOUR AND DOES NOT CLOSE. batch_invert (AssemblyHelpers.yul:226,
    called by the real Lagrange slice) and validate_public_accumulator
    (AccumulatorHelpers.yul:190, called only by the untaken accumulator arm) are still not
    defined here. P-AST3a and P-AST3b recorded that hole; P-AST4 narrows it without closing
    it, and the deployed profile still never takes the accumulator arm. -/
def emitHelpers (pv : PlanView) : Block Op :=
  emitFail ++ emitTranscriptHelpers ++ emitEcPairingAt pv

/-! ### FinalPairing -/

/-- The MSM-then-ADD pair the accumulator arm runs twice, once per side: batch the point
    with its scalar through G1MSM, fold the result into the pairing slot through G1ADD,
    each guarded on success still holding. -/
def accMsmThenAdd (g1 : Nat) (tc : TemplateConstants) (src dst : String) : Block Op :=
  [ yexpr (yop Op.mcopy [yvar "batch_ptr", yvar src, ylit g1])
  , yexpr (yop Op.mstore [yop Op.add [yvar "batch_ptr", ylit g1], yvar "acc_pair_alpha"])
  , yif (yvar "success")
      [ yset "success" (yop Op.staticcall [yvar "G1MSM_GAS_1PAIR",
          ylit tc.eip2537.g1msmAddress, yvar "batch_ptr", ylit tc.g1MsmPairBytes,
          yvar "batch_ptr", ylit g1])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.returndatasize [], ylit g1]]) ]
  , yexpr (yop Op.mcopy [yop Op.add [yvar "batch_ptr", ylit g1], yvar dst, ylit g1])
  , yif (yvar "success")
      [ yset "success" (yop Op.staticcall [yvar "G1ADD_GAS", ylit tc.eip2537.g1addAddress,
          yvar "batch_ptr", ylit tc.g1addInputBytes, yvar dst, ylit g1])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.returndatasize [], ylit g1]]) ] ]

/-- The batch-and-randomise block of the accumulator arm (FinalPairing.yul:14-62): the
    0x240-byte preimage tag || vk_digest || KZG rhs/lhs || accumulator rhs/lhs, alpha as
    keccak mod r with zero mapped to one, then the two randomised additions. -/
def emitAccBatch (batch : Nat) : Block Op :=
  let tc := templateConstantsDefault
  let acc := tc.accumulator
  let g1 := tc.g1Bytes
  [ yblock
    ([ ylet "batch_ptr" (ylit batch)
     , yexpr (yop Op.mstore [yvar "batch_ptr",
          ylit (hexLiteral acc.pairingBatchDomainTagHex)])
     , yexpr (yop Op.mstore [yop Op.add [yvar "batch_ptr",
          ylit acc.pairingBatchVkDigestOffset], yop Op.mload [yvar "VK_DIGEST_MPTR"]])
     , yexpr (yop Op.mcopy [yop Op.add [yvar "batch_ptr", ylit acc.pairingBatchRhsOffset],
          yvar "PAIRING_RHS_MPTR", ylit g1])
     , yexpr (yop Op.mcopy [yop Op.add [yvar "batch_ptr", ylit acc.pairingBatchLhsOffset],
          yvar "PAIRING_LHS_MPTR", ylit g1])
     , yexpr (yop Op.mcopy [yop Op.add [yvar "batch_ptr",
          ylit acc.pairingBatchAccRhsOffset], yvar "ACC_RHS_MPTR", ylit g1])
     , yexpr (yop Op.mcopy [yop Op.add [yvar "batch_ptr",
          ylit acc.pairingBatchAccLhsOffset], yvar "ACC_LHS_MPTR", ylit g1])
     , ylet "acc_pair_alpha" (yop Op.mod
          [yop Op.keccak256 [yvar "batch_ptr", ylit acc.pairingBatchHashBytes], yvar "r"])
     , yif (yop Op.iszero [yvar "acc_pair_alpha"]) [yset "acc_pair_alpha" (ylit 1)]
     ] ++
      List.flatten [accMsmThenAdd g1 tc "ACC_RHS_MPTR" "PAIRING_RHS_MPTR",
                 accMsmThenAdd g1 tc "ACC_LHS_MPTR" "PAIRING_LHS_MPTR"]) ]

/-- FinalPairing (FinalPairing.yul:1-92) as an AST, parameterised by the plan: the
    accumulator arm is selected by hasAccumulator and its batch pointer comes from the
    memory layout. The ec_pairing scratch pointer belongs to the HELPER, not to this
    slice, so it does not appear here - emitHelpers is where it enters. The tail - the precompile guard and the SWAPPED ec_pairing call -
    is shared by both arms, and the swap is the trap the text port documents at
    VerifierPartials.lean:702-707: the slots are named for the dual-MSM accumulator, not
    for the pairing argument order, so the call passes RHS first. -/
def emitFinalPairingArms (hasAcc : Bool) (batch : Nat) : Block Op :=
  (if hasAcc then emitAccBatch batch else []) ++
    [ yif (yop Op.iszero [yvar "success"])
        [yexpr (ycall "fail" [yvar "ERR_PRECOMPILE_FAILED"])]
    , yset "success" (ycall "ec_pairing" [yvar "success", yvar "PAIRING_RHS_MPTR",
        yvar "PAIRING_LHS_MPTR"]) ]

/-- The FinalPairing slice of one plan. -/
def emitFinalPairing (pv : PlanView) : Block Op :=
  emitFinalPairingArms pv.hasAccumulator pv.memory.accumulatorPairingBatchMptr

/-! ### Lagrange -/

/-- The Lagrange / instance-evaluation block (Lagrange.yul:1-99) as an AST, parameterised by
    the three plan values the template interpolates: the domain exponent k (the render emits
    it in DECIMAL, 'let k := 6', because the template interpolates an integer, not a hex
    filter), the negative-rotation count the l_blind loop walks, and the public instance
    count. The two window sizes are DERIVED here the way the render derives them -
    '(numInstances + numNegLagranges) * 32' for the denominator run, 'numNegLagranges * 32'
    for the negative-rotation tail and the l_0 slot, 'numInstances * 32' for the instance
    loop - so a plan that changes one changes the emitted bytes and the emitted AST by the
    same amount. emitDependsOnPlan_ok makes that a computation.

    Every call in this block is a dialect built-in EXCEPT batch_invert and fail: batch_invert
    is AssemblyHelpers.yul:226 (a user function with a two-value return) and fail is
    AssemblyHelpers.yul:4. mulmod / addmod / sub / lt / mload / mstore / calldataload are
    dialect names (EVMOp.lean:43-53). That split is invisible to the token comparator and is
    what emitLagrangeDetectsBuiltinVsCall_ok reddens.

    The 0x20 stride, the '0x20' / '0x40' offsets of l_blind and l_i_cptr, the '+ 0x20' on
    mptr_end in the batch_invert call and the zero initialiser are literal in the template
    and stay literal here. -/
def emitLagrangeAt (k numInstances numNegLagranges : Nat) : Block Op :=
  let denomWindow := (numInstances + numNegLagranges) * 32
  let negWindow := numNegLagranges * 32
  [ ylet "lagrange_precompile_failed" (ylit 0)
    -- The whole computation runs in its own scope: k, x, mptr and the rest are locals of
    -- this block and are gone by the time quotientLin reads the slots this writes.
  , yblock
    [ ylet "k" (ylit k)
    , ylet "x" (yop Op.mload [yvar "X_MPTR"])
      -- x^n by repeated squaring, n = 2^k.
    , ylet "x_n" (yvar "x")
    , yfor [ylet "idx" (ylit 0)] (yop Op.lt [yvar "idx", yvar "k"])
        [yset "idx" (yop Op.add [yvar "idx", ylit 1])]
        [yset "x_n" (yop Op.mulmod [yvar "x_n", yvar "x_n", yvar "r"])]
    , ylet "omega" (yop Op.mload [yvar "OMEGA_MPTR"])
      -- First pass: denominators (x - omega_i) for every Lagrange value needed, then
      -- x^n - 1 appended at mptr_end, then ONE batch inversion over the whole run.
    , ylet "mptr" (yvar "LAGRANGE_DENOMS_MPTR")
    , ylet "mptr_end" (yop Op.add [yvar "mptr", ylit denomWindow])
    , yfor [ylet "pow_of_omega" (yop Op.mload [yvar "OMEGA_INV_TO_L_MPTR"])]
        (yop Op.lt [yvar "mptr", yvar "mptr_end"])
        [yset "mptr" (yop Op.add [yvar "mptr", ylit 0x20])]
        [ yexpr (yop Op.mstore [yvar "mptr",
            yop Op.addmod [yvar "x", yop Op.sub [yvar "r", yvar "pow_of_omega"], yvar "r"]])
        , yset "pow_of_omega" (yop Op.mulmod [yvar "pow_of_omega", yvar "omega", yvar "r"]) ]
    , ylet "x_n_minus_1" (yop Op.addmod [yvar "x_n", yop Op.sub [yvar "r", ylit 1], yvar "r"])
    , yexpr (yop Op.mstore [yvar "mptr_end", yvar "x_n_minus_1"])
      -- MF-4: the second return value separates a failed precompile (chain fault) from a
      -- rejected denominator (x landed on a domain point). Two assignment targets, which is
      -- why ysetN exists.
    , ysetN ["success", "lagrange_precompile_failed"]
        (ycall "batch_invert" [yvar "success", yvar "LAGRANGE_DENOMS_MPTR",
          yop Op.add [yvar "mptr_end", ylit 0x20], yvar "BATCH_INV_SCRATCH_MPTR", yvar "r"])
      -- Second pass over the same window: turn each inverse into L_i(x).
    , yset "mptr" (yvar "LAGRANGE_DENOMS_MPTR")
    , ylet "l_i_common" (yop Op.mulmod [yvar "x_n_minus_1",
        yop Op.mload [yvar "N_INV_MPTR"], yvar "r"])
    , yfor [ylet "pow_of_omega" (yop Op.mload [yvar "OMEGA_INV_TO_L_MPTR"])]
        (yop Op.lt [yvar "mptr", yvar "mptr_end"])
        [yset "mptr" (yop Op.add [yvar "mptr", ylit 0x20])]
        [ yexpr (yop Op.mstore [yvar "mptr",
            yop Op.mulmod [yvar "l_i_common",
              yop Op.mulmod [yop Op.mload [yvar "mptr"], yvar "pow_of_omega", yvar "r"],
                yvar "r"]])
        , yset "pow_of_omega" (yop Op.mulmod [yvar "pow_of_omega", yvar "omega", yvar "r"]) ]
      -- l_blind: the sum of the negative-rotation terms, which start one word in.
    , ylet "l_blind" (yop Op.mload [yop Op.add [yvar "LAGRANGE_DENOMS_MPTR", ylit 0x20]])
    , ylet "l_i_cptr" (yop Op.add [yvar "LAGRANGE_DENOMS_MPTR", ylit 0x40])
    , yfor [ylet "l_i_cptr_end" (yop Op.add [yvar "LAGRANGE_DENOMS_MPTR", ylit negWindow])]
        (yop Op.lt [yvar "l_i_cptr", yvar "l_i_cptr_end"])
        [yset "l_i_cptr" (yop Op.add [yvar "l_i_cptr", ylit 0x20])]
        [ yset "l_blind" (yop Op.addmod [yvar "l_blind",
            yop Op.mload [yvar "l_i_cptr"], yvar "r"]) ]
      -- Public instance polynomial at x. The cursor pair advances together; the l_i run
      -- continues where the negative-rotation loop left it, which is why the post block has
      -- TWO statements and why the coupling is in the AST and not in a comment.
    , ylet "instance_eval" (ylit 0)
    , yfor [ ylet "instance_cptr" (yvar "INSTANCE_CPTR")
           , ylet "instance_cptr_end" (yop Op.add [yvar "instance_cptr",
               ylit (numInstances * 32)]) ]
        (yop Op.lt [yvar "instance_cptr", yvar "instance_cptr_end"])
        [ yset "instance_cptr" (yop Op.add [yvar "instance_cptr", ylit 0x20])
        , yset "l_i_cptr" (yop Op.add [yvar "l_i_cptr", ylit 0x20]) ]
        [ yset "instance_eval" (yop Op.addmod [yvar "instance_eval",
            yop Op.mulmod [yop Op.mload [yvar "l_i_cptr"],
              yop Op.calldataload [yvar "instance_cptr"], yvar "r"], yvar "r"]) ]
      -- Persist the derived values into the slots quotientLin and PCS read.
    , ylet "x_n_minus_1_inv" (yop Op.mload [yvar "mptr_end"])
    , ylet "l_last" (yop Op.mload [yvar "LAGRANGE_DENOMS_MPTR"])
    , ylet "l_0" (yop Op.mload [yop Op.add [yvar "LAGRANGE_DENOMS_MPTR", ylit negWindow]])
    , yexpr (yop Op.mstore [yvar "X_N_MPTR", yvar "x_n"])
    , yexpr (yop Op.mstore [yvar "X_N_MINUS_1_INV_MPTR", yvar "x_n_minus_1_inv"])
    , yexpr (yop Op.mstore [yvar "L_LAST_MPTR", yvar "l_last"])
    , yexpr (yop Op.mstore [yvar "L_BLIND_MPTR", yvar "l_blind"])
    , yexpr (yop Op.mstore [yvar "L_0_MPTR", yvar "l_0"])
    , yexpr (yop Op.mstore [yvar "INSTANCE_EVAL_MPTR", yvar "instance_eval"]) ]
    -- Section boundary: the two MF-4 incidents, in the template's order.
  , yif (yop Op.iszero [yvar "success"])
      [ yif (yvar "lagrange_precompile_failed")
          [yexpr (ycall "fail" [yvar "ERR_PRECOMPILE_FAILED"])]
      , yexpr (ycall "fail" [yvar "ERR_PROOF_REJECTED"]) ] ]

/-- The Lagrange slice of one plan: the three values the render interpolates are read out of
    the plan view, which is exactly what EnvAgrees.negLagranges and domainN tie to the
    ConstraintSystem, so the emitter and the invariant take them from one place. -/
def emitLagrange (pv : PlanView) : Block Op :=
  emitLagrangeAt pv.k pv.numInstances pv.numNegLagranges

/-! ### TraceReturn -/

/-- The terminal arm of TraceReturn.yul:55-73 in its PRODUCTION shape: guard on success,
    write the ABI true word, return 32 bytes from it. 'fail' is a user call
    (AssemblyHelpers.yul:4); mstore and ret are dialect built-ins, and 'ret' is the dialect
    name for the 'return' opcode (EVMOp.lean:26, :71).

    NOT parameterised, and that is a measurement of the template rather than an omission:
    the production arm interpolates nothing - RETURN_MPTR is a bare Solidity-level constant
    and the '1' and '0x20' are literal - which is why the text port's arm is a plain string
    too, and why the existing traceReturn_ast snapshot is a closed block. The ARM CHOICE is
    plan-dependent in the render (ctx.trace selects the 'return(iszero(iszero(success)))'
    shape), but PlanView carries no diagnostics flag, so the trace arm is not expressible
    in this emitter's signature at all; SupportedS.production is exactly the hypothesis that
    keeps that gap closed. Stated here rather than left to be rediscovered: the four
    placeholders and this constant slice are the two ways a slice can be plan-independent,
    and only one of them is a hole. -/
def emitTraceReturnBlock : Block Op :=
  [ yif (yop Op.iszero [yvar "success"])
      [yexpr (ycall "fail" [yvar "ERR_PROOF_REJECTED"])]
  , yexpr (yop Op.mstore [yvar "RETURN_MPTR", ylit 1])
  , yexpr (yop Op.ret [yvar "RETURN_MPTR", ylit 0x20]) ]

/-- The TraceReturn slice of one plan. Constant in the plan, by the measurement above. -/
def emitTraceReturn (_pv : PlanView) : Block Op := emitTraceReturnBlock

/-! ### QuotientLin -/

/-- The linearization block of QuotientAndLinearization.yul - the deployed arm, artifact
    D:2539-2580, 1,898 bytes / 42 lines by the text port's own note at
    VerifierPartials.lean:617-623 - as an AST, parameterised by the ONE plan value this arm
    interpolates: the domain exponent k. It is interpolated as an INTEGER and not through the
    hex filter, so the render says 'let k := 6' and the AST prints 'let k := 6' - the same
    spelling on both sides, unlike the 0x20 offset below.

    SCOPE, DECIDED ON MEASUREMENT AND NOT ON TASTE. 'blk .quotientLin' is THIS TEMPLATE'S OWN
    BODY - the linearization block - and NOT the artifact's whole quotient region. Three
    numbers, all re-measured in this package against the tracked dump; the first two are pinned
    by gate 29 below and the third by VerifierPartials' own gates 48-51:
      * 'renderQuotientAndLinearization poseidonCtx "" ""' - the empty-parameter render - is
        1,898 bytes / 42 lines and occurs EXACTLY ONCE in the artifact. That is this slice.
      * the same call fed poseidonCtx's OWN includes ('renderQuotientHelpers' 826 B plus
        'renderQuotientNumeratorBlock' 6,682 B) is 9,406 bytes and occurs ZERO times:
        poseidonCtx carries the inert quotient defaults (line 503's note), so its includes are
        not the deployed ones and the composite render matches nothing.
      * with the DEPLOYED includes - 'quotientDeployedCtx sol', which is what gates 48-51 use
        - the two renders are 1,621 B / 31 lines and 55,597 B, 57,218 B / 952 lines combined,
        occurring once, and the whole region including this slice's body is 59,116 B.
    So the text port already treats the two includes as a SEPARATE region with its own byte
    gates, and the region is not this partial's body. Adopting that decomposition here is being
    consistent with the port, not taking a shortcut around it. Converting the two includes is the separate
    Quotient/Evaluator.lean string-machinery job - D-P30 counts 18 sites - and is OUT OF SCOPE
    here. Stated so a later package does not silently redefine the boundary: widening
    'blk .quotientLin' to the whole region means moving BOTH include renders to AST emission in
    the same change, not quietly folding them into this function.

    NOTE, measured in this package rather than inherited: main's helper prefix defines 'fail'
    and 'ec_pairing' ONLY - 'lookupFun' over the hoist of the emitted main finds no
    'batch_invert', which the already-real Lagrange slice calls. That gap is P-AST2's and this
    slice neither widens nor repairs it (quotientLin adds no new callee), but it is the same
    hole transcriptParser would widen fourfold, so it is recorded where a later package reads
    the helper boundary.

    Every call in this block is a dialect built-in - mload, lt, add, mulmod, sub, addmod,
    mstore - and there is NO user call anywhere in it. That is what makes it the cheapest of
    the seven slices: unlike FinalPairing and Lagrange it needs no helper definition in main,
    no 'fail' arm and no 'batch_invert', so 'emitHelpers' does not grow. The nested scope is
    not decoration either: it is the template's own brace, and it is why the emitted slice has
    the SAME top-level length as the placeholder it replaces - one statement each - which is
    exactly why mainConcatKats_ok cannot see this conversion by length and does it structurally
    instead. -/
def emitQuotientLinAt (k : Nat) : Block Op :=
  [ yblock
    [ ylet "x" (yop Op.mload [yvar "X_MPTR"])
    , ylet "k" (ylit k)
      -- x^n and x^(n-1) in ONE squaring walk: x_pow_2i tracks x^(2^i) while
      -- x_pow_2i_minus1 tracks x^(2^i - 1), and the body's first assignment reads the OLD
      -- x_pow_2i, so the two statements are ordered and not interchangeable. Swapping them
      -- leaves the token stream a permutation of itself only at a glance - it does change the
      -- token stream here (the operands differ), and it always changes stmtsBeq.
    , ylet "x_pow_2i" (yvar "x")
    , ylet "x_pow_2i_minus1" (ylit 1)
    , yfor [ylet "idx" (ylit 0)] (yop Op.lt [yvar "idx", yvar "k"])
        [yset "idx" (yop Op.add [yvar "idx", ylit 1])]
        [ yset "x_pow_2i_minus1" (yop Op.mulmod
            [yop Op.mulmod [yvar "x_pow_2i_minus1", yvar "x_pow_2i_minus1", yvar "r"],
              yvar "x", yvar "r"])
        , yset "x_pow_2i" (yop Op.mulmod [yvar "x_pow_2i", yvar "x_pow_2i", yvar "r"]) ]
    , ylet "x_split" (yvar "x_pow_2i_minus1")
    , ylet "one_minus_x_n" (yop Op.addmod [ylit 1, yop Op.sub [yvar "r", yvar "x_pow_2i"],
        yvar "r"])
      -- The 2-word payload PCS block 5 reads: word 0 x_split, word 1 one_minus_x_n. The
      -- 0x20 is the render's hex offset printed decimal here - the divergence gate 21 pins.
    , yexpr (yop Op.mstore [yvar "QUOTIENT_MPTR", yvar "x_split"])
    , yexpr (yop Op.mstore [yop Op.add [yvar "QUOTIENT_MPTR", ylit 0x20],
        yvar "one_minus_x_n"]) ] ]

/-- The QuotientLin slice of one plan: the domain exponent k, the same PlanView field
    emitLagrange reads, so the two slices cannot disagree about the domain size. -/
def emitQuotientLin (pv : PlanView) : Block Op := emitQuotientLinAt pv.k

/-! ### VkLoading -/

/-- The VK-loading block (VkLoading.yul:1-141) as an AST, parameterised by the SEVEN plan
    values the template interpolates: the public instance count (twice - the header
    cross-check and the ABI envelope), the domain exponent k, the four accumulator words,
    and the proof length. The deployed arm is 4,494 bytes / 74 lines occurring EXACTLY
    ONCE in the tracked artifact, and that measurement is a computation and not a
    paragraph: VerifierPartialKats.vkLoading_astAgrees_ok (gate 90 in that file) re-reads
    the size, the single occurrence and the six header words from the dump's own lines,
    and gate 31 below compares this function against that quotation.

    WHY THE FOUR ACCUMULATOR WORDS ARE PARAMETERS AND NOT ZEROS. P-AST3a measured all four
    are 0 in the deployed profile and refused to hard-code them: "hard-coding the four
    zeros would reproduce the deployed bytes and lie for any accumulator plan." This
    package takes that refusal literally. The words arrive through PlanView, where
    Inv.lean's accWordsOfEncoding derives them from the accumulator encoding - none arm
    gives the four zeros the artifact shows, some arm gives 1 / offset / numLimbs /
    numLimbBits - and Surface.plan_accExpectations pins the copy back to cfg.accumulator.
    Gate 33 below is the falsification: changing a word changes the emitted block, so
    the parameter reaches the program and is not decoration.

    SCOPE, measured and not chosen: 'blk .vkLoading' is the TEMPLATE'S OWN BODY, the
    single top-level scope the render emits, and not the surrounding prologue lines
    ('let r := FR_MODULUS', 'let success := true') that the artifact shows above it -
    those belong to the contract shell (Halo2Verifier.sol:217's include order), and no
    partial owns them. The embedded-VK arm (VkLoading.yul:23-53, the mstore loop over
    constants, fixedComms and permutationComms) is NOT emitted: poseidonCtx.embeddedVk is
    none, so the deployed slice takes the external arm, and the embedded arm interpolates
    a whole payload word list that PlanView carries as PV.vk.bytes rather than as words -
    converting it is a separate measurement, not a silent widening here.

    EVERY CALL SITE CHOOSES DELIBERATELY. extcodesize, extcodehash, extcodecopy,
    calldatasize, calldataload, mload, and, eq, iszero and add are dialect built-ins
    (EVMOp.lean:53, :65); 'fail' is the user function AssemblyHelpers.yul:4, and
    'validate_public_accumulator' - accumulator arm only - is the user function
    AccumulatorHelpers.yul:190, i.e. it lives in a DIFFERENT included file from the two
    helpers emitHelpers defines, and renderFunction cannot slice it out of the
    AssemblyHelpers render (measured: it returns the empty string for that name). That
    split is invisible to the token comparator, which is
    why gate 31 (stmtsBeq against the quotation) is the record and gate 30 is only the
    tripwire, and why gate 34 reproduces the blindness on this slice.

    THE HELPER GAP THIS SLICE WIDENS, stated rather than left to be rediscovered: the
    accumulator arm calls validate_public_accumulator, which emitHelpers does NOT define
    (it defines fail and ec_pairing only), and which lives in AccumulatorHelpers.yul:190 -
    a file no emitter touches yet. That is the same hole P-AST2 recorded for batch_invert -
    'main's helper prefix defines fail and ec_pairing ONLY' - and the deployed profile
    never takes the arm, so no emitted program in the tree calls a function main does not
    define. A package that emits an accumulator render has to convert that helper in the
    same change, and it is a 165-line file (gate 31 in VerifierPartials), not two helpers.

    NUMERIC SPELLING, pinned by gate 21: the render writes the proof length and the
    instance window through the hex filter ('eq(0x10e0, calldataload(PROOF_LEN_CPTR))',
    'add(INSTANCE_CPTR, 0x20)') and the copy offset as '0x01', while EVM.print renders
    4320, 32 and 1. The two spellings are one program and no AST relation can tell them
    apart - the standing note, reproduced on a fourth slice. -/
def emitVkLoadingArms (hasAcc : Bool)
    (numInstances k hasWord accOffset numLimbs limbBits proofLen : Nat) : Block Op :=
  [ yblock
      [ yif (yop Op.iszero
          [yop Op.and
            [yop Op.eq [yop Op.extcodesize [yvar "vk"], yvar "EXPECTED_VK_LENGTH"],
             yop Op.eq [yop Op.extcodehash [yvar "vk"],
                        yvar "EXPECTED_VK_CODEHASH_WORD"]]])
          [yexpr (ycall "fail" [yvar "ERR_VK_MISMATCH"])]
        -- Runtime byte 0 is INVALID, so the payload copy starts at byte 1: the 0x01 is
        -- the render's own hex spelling of 1 and prints decimal here.
      , yexpr (yop Op.extcodecopy [yvar "vk", yvar "VK_MPTR", ylit 0x01,
          yvar "EXPECTED_VK_PAYLOAD_LENGTH"])
        -- The six header cross-checks, in the template's order. The last four are the
        -- accumulator words and they come from the plan, not from the artifact.
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "NUM_INSTANCES_MPTR"], ylit numInstances]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "K_MPTR"], ylit k]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "HAS_ACCUMULATOR_MPTR"], ylit hasWord]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "ACC_OFFSET_MPTR"], ylit accOffset]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "NUM_ACC_LIMBS_MPTR"], ylit numLimbs]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.mload [yvar "NUM_ACC_LIMB_BITS_MPTR"], ylit limbBits]])
      , yif (yop Op.iszero [yvar "success"])
          [yexpr (ycall "fail" [yvar "ERR_VK_MISMATCH"])]
        -- The ABI envelope: proof bytes, instance count, and no trailing words. The
        -- window is DERIVED here the way the render derives it - numInstances * 32 - so
        -- a plan with more instances moves the bound and the header check together.
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [ylit proofLen, yop Op.calldataload [yvar "PROOF_LEN_CPTR"]]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [ylit numInstances,
                     yop Op.calldataload [yvar "NUM_INSTANCE_CPTR"]]])
      , yset "success" (yop Op.and [yvar "success",
          yop Op.eq [yop Op.calldatasize [],
            yop Op.add [yvar "INSTANCE_CPTR", ylit (numInstances * 32)]]])
      , yif (yop Op.iszero [yvar "success"])
          [yexpr (ycall "fail" [yvar "ERR_BAD_CALLDATA_SHAPE"])] ] ] ++
    -- The accumulator precheck, OUTSIDE the scope: the template appends it after the
    -- block closes, so the top level grows from one statement to four.
    (if hasAcc then
      [ ylet "acc_precompile_failed" (ylit 0)
      , ysetN ["success", "acc_precompile_failed"]
          (ycall "validate_public_accumulator" [yvar "success", yvar "r"])
      , yif (yop Op.iszero [yvar "success"])
          [ yif (yvar "acc_precompile_failed")
              [yexpr (ycall "fail" [yvar "ERR_PRECOMPILE_FAILED"])]
          , yexpr (ycall "fail" [yvar "ERR_BAD_POINT_ENCODING"]) ] ]
     else [])

/-- The VkLoading slice of one plan. Every value comes from a PlanView field: the two
    counts Inv already read, the four accumulator words P-AST3b added, and the proof
    length read off the calldata geometry rather than copied a fifth time. -/
def emitVkLoading (pv : PlanView) : Block Op :=
  emitVkLoadingArms pv.hasAccumulator pv.numInstances pv.k
    pv.expectedHasAccumulatorWord pv.expectedAccOffset pv.expectedNumAccLimbs
    pv.expectedNumAccLimbBits pv.proofLayout.proofLen

/-- The seven plan values the vkLoading template interpolates, read out of the text port's
    own deployed profile. Every gate that compares against the render or against the
    quotation uses THIS list, so the emitter and the text port are fed the same seven
    numbers and cannot be given different ones by accident. -/
def vkLoadingPoseidonArgs : Bool × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (poseidonCtx.expectedHasAccumulator, poseidonCtx.numInstances, poseidonCtx.k,
    poseidonCtx.expectedHasAccumulatorWord, poseidonCtx.expectedAccOffset,
    poseidonCtx.expectedNumAccLimbs, poseidonCtx.expectedNumAccLimbBits,
    poseidonCtx.proofLen)

/-- The deployed slice, emitted at the poseidon profile - the block gates 21 and 30-35
    compare. -/
def emitVkLoadingDeployed : Block Op :=
  let (h, n, k, w, o, l, b, p) := vkLoadingPoseidonArgs
  emitVkLoadingArms h n k w o l b p

/-! ### transcriptParser -/

/-- The four statements one G1 walk runs: absorb the 128-byte calldata form, copy the same
    bytes into the planned memory slot, advance the slot cursor and the proof cursor. Used
    six times over the six commitment sections, which is why it is a function and not six
    copies - the six differ only in the walk variable and the loop bound, a difference no
    length check can see and stmtsBeq sees exactly. -/
def g1WalkBody (walk : String) : Block Op :=
  let g1 := templateConstantsDefault.g1Bytes
  [ yset "buf_len" (ycall "common_uncompressed_g1" [yvar "buf_len", yvar "proof_cptr"])
  , yexpr (yop Op.calldatacopy [yvar walk, yvar "proof_cptr", ylit g1])
  , yset walk (yop Op.add [yvar walk, ylit g1])
  , yset "proof_cptr" (yop Op.add [yvar "proof_cptr", ylit g1]) ]

/-- The walk loop itself: 'for { let end := add(proof_cptr, N) } lt(proof_cptr, end) {} {
    ... }'. The bound is the section's byte length and the post block is EMPTY - the cursor
    advances inside the body, which is why 'end' is a fresh local per loop and why six loops
    in one scope do not collide. -/
def g1WalkLoop (walk : String) (bytes : Nat) : Stmt Op :=
  yfor [ylet "end" (yop Op.add [yvar "proof_cptr", ylit bytes])]
    (yop Op.lt [yvar "proof_cptr", yvar "end"]) [] (g1WalkBody walk)

/-- The three statements at the two sites that absorb ONE commitment without a walk cursor:
    f_com and pi. Same first two statements as the walk body and NO slot advance, because
    the destination is a fixed MPTR and not a cursor - which is the one place a converter
    reusing g1WalkBody would silently emit a fourth statement ('F_COM_MPTR := add(..)'),
    and the reason the two shapes are separate definitions. Measured in this package: the
    reuse bug printed 46 statements against the quotation's 44. -/
def g1AbsorbCopy (dst : String) : Block Op :=
  let g1 := templateConstantsDefault.g1Bytes
  [ yset "buf_len" (ycall "common_uncompressed_g1" [yvar "buf_len", yvar "proof_cptr"])
  , yexpr (yop Op.calldatacopy [yvar dst, yvar "proof_cptr", ylit g1])
  , yset "proof_cptr" (yop Op.add [yvar "proof_cptr", ylit g1]) ]
/-- The transcript proof parser (TranscriptProofParser.yul:1-424, deployed arm
    D:1178-1495: 17,136 bytes / 318 lines occurring EXACTLY ONCE) as an AST, parameterised
    by the ELEVEN plan values the template interpolates: the public instance count (twice -
    the ABI length word and the instance window), the user-phase list, the four shape
    counts that guard four of the ten proof sections, the truncation flag that guards the
    x3 mask, and the seven proofLayout section byte lengths the loops walk.

    SCOPE, measured and not chosen: 'blk .transcriptParser' is the TEMPLATE'S OWN BODY - the
    44 top-level statements the render emits - and not the surrounding prologue ('let r :=
    FR_MODULUS', 'let success := true'), which belongs to the contract shell exactly as in
    VkLoading. Gate 39 pins the size, the single occurrence and the include boundary against
    the tracked artifact at #eval time.

    WHAT ZERO-RENDERS, and why that is the hazard here. The 12 trace sites and the 8
    gas-checkpoint sites of the template all take their else-arm under
    SupportedS.production, so no gas_checkpoint or trace_point byte appears - the same
    restriction every other slice carries. The four shape guards are TRUE at the deployed
    fixture (numLookups 1, numPermutationZs 3, lookupHPlusAcc 2, numTrashcans 1) and the
    truncation flag is TRUE, so the deployed slice shows every section present. That is the
    opposite of the vkLoading accumulator arm and it cuts both ways: a hard-coded 'always
    emit the section' would reproduce the deployed bytes exactly and pass BOTH relations.
    Gate 38 is the falsification - each of the six counts driven to zero removes statements
    from the emitted block, the flag driven false removes the mask, and each of the seven
    section widths moves a loop bound.

    THE CALL SPLIT. transcript_init, common_word, common_uncompressed_g1, squeeze_to and fail
    are USER calls (AssemblyHelpers.yul, the first four defined by emitTranscriptHelpers in
    the same hoisted main); mstore, mload, calldataload, calldatacopy, add, sub, lt, gt, eq,
    iszero, and, or, shr, mod and keccak256 are dialect built-ins. The parser is the slice
    with the most sites of both kinds, so gate 40 reproduces the token blindness on it, and
    it is the slice where a converter reaching for 'ycall' out of habit mis-spells the most.

    NUMERIC SPELLING, pinned by gate 21: the render writes every section width and stride
    through the hex filter ('add(proof_cptr, 0x0400)', 'add(proof_cptr, 0x20)') and the
    instance count as a DECIMAL integer ('common_word(buf_len, 1)'), while EVM.print renders
    1024 and 32 and 1. One region, both spellings, and no AST relation can tell them apart. -/
def emitTranscriptParserAt (numInstances : Nat) (userPhases : List UserPhase)
    (numLookups numPermutationZs lookupHPlusAcc numTrashcans : Nat)
    (truncatedChallenges : Bool) (L : ProofCalldataLayout) : Block Op :=
  let word := templateConstantsDefault.wordBytes
  -- 'buf_len := squeeze_to(buf_len, SLOT)': the eleven challenge squeezes, identical except
  -- for the slot, which is a bare Solidity-level constant and so a yvar and not a ylit.
  let squeeze (slot : String) : Stmt Op :=
    yset "buf_len" (ycall "squeeze_to" [yvar "buf_len", yvar slot])
  -- one phase's challenge squeeze, at its running offset into CHALLENGE_MPTR. The offset is
  -- a WORD offset scaled by 32, derived here the way ART:168 derives it.
  let squeezeChallenge (off : Nat) : Stmt Op :=
    yset "buf_len" (ycall "squeeze_to" [yvar "buf_len",
      yop Op.add [yvar "CHALLENGE_MPTR", ylit off]])
  let phaseStmts : Block Op := List.flatten (userPhases.map fun ph =>
    ([ g1WalkLoop "advice_walk" ph.adviceBytes ] : Block Op) ++
      ((List.range ph.numChallenges).map fun j =>
        squeezeChallenge ((ph.challengeOffset + j) * 32)))
  let lookupStmts : Block Op := List.flatten (L.lookups.map fun lk =>
    ([ g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen ] : Block Op) ++
      g1WalkBody "lookup_z_walk")
  [ ylet "buf_len" (ycall "transcript_init" [])
  , yset "buf_len" (ycall "common_word" [yvar "buf_len", yop Op.mload [yvar "VK_DIGEST_MPTR"]])
    -- committed_pi: the identity absorbs as 128 zero bytes, four words at the cursor. A raw
    -- transcript absorb and not a memory slot, so it has no MPTR and no plan value.
  , yblock
      [ yexpr (yop Op.mstore [yvar "buf_len", ylit 0])
      , yexpr (yop Op.mstore [yop Op.add [yvar "buf_len", ylit 0x20], ylit 0])
      , yexpr (yop Op.mstore [yop Op.add [yvar "buf_len", ylit 0x40], ylit 0])
      , yexpr (yop Op.mstore [yop Op.add [yvar "buf_len", ylit 0x60], ylit 0])
      , yset "buf_len" (yop Op.add [yvar "buf_len", ylit 0x80]) ]
    -- the instance run: a length word then one word per public input, each range-checked
    -- against r and folded into `success` rather than reverting on the spot.
  , yblock
      [ yset "buf_len" (ycall "common_word" [yvar "buf_len", ylit numInstances])
      , ylet "instance_cptr" (yvar "INSTANCE_CPTR")
      , yfor [ylet "instance_cptr_end" (yop Op.add [yvar "instance_cptr",
            ylit (numInstances * 32)])]
          (yop Op.lt [yvar "instance_cptr", yvar "instance_cptr_end"])
          [yset "instance_cptr" (yop Op.add [yvar "instance_cptr", ylit 0x20])]
          [ ylet "inst_be" (yop Op.calldataload [yvar "instance_cptr"])
          , yset "success" (yop Op.and [yvar "success",
              yop Op.lt [yvar "inst_be", yvar "r"]])
          , yset "buf_len" (ycall "common_word" [yvar "buf_len", yvar "inst_be"]) ]
      , yif (yop Op.iszero [yvar "success"])
          [yexpr (ycall "fail" [yvar "ERR_NON_CANONICAL_SCALAR"])] ]
  , ylet "proof_cptr" (yvar "PROOF_CPTR")
  , ylet "advice_walk" (yvar "ADVICE_COMMS_MPTR_BASE")
  ] ++ phaseStmts ++
    [ squeeze "THETA_MPTR" ] ++
    (if numLookups != 0 then
      [ ylet "lookup_m_walk" (yvar "LOOKUP_M_COMMS_MPTR_BASE")
      , g1WalkLoop "lookup_m_walk" L.lookupMultiplicities.byteLen ] else []) ++
    [ squeeze "BETA_MPTR", squeeze "GAMMA_MPTR" ] ++
    (if numPermutationZs != 0 then
      [ ylet "perm_z_walk" (yvar "PERM_Z_COMMS_MPTR_BASE")
      , g1WalkLoop "perm_z_walk" L.permutationProducts.byteLen ] else []) ++
    (if lookupHPlusAcc != 0 then
      [ ylet "lookup_helper_walk" (yvar "LOOKUP_HELPER_COMMS_MPTR_BASE")
      , ylet "lookup_z_walk" (yvar "LOOKUP_Z_COMMS_MPTR_BASE") ] ++ lookupStmts else []) ++
    [ squeeze "TRASH_CHALLENGE_MPTR" ] ++
    (if numTrashcans != 0 then
      [ ylet "trashcan_walk" (yvar "TRASHCAN_COMMS_MPTR_BASE")
      , g1WalkLoop "trashcan_walk" L.trash.byteLen ] else []) ++
    [ squeeze "Y_MPTR"
    , ylet "quotient_walk" (yvar "QUOTIENT_LIMB_COMMS_MPTR_BASE")
    , g1WalkLoop "quotient_walk" L.quotientLimbs.byteLen
    , squeeze "X_MPTR"
      -- the eval spill block: cursor, canonicality check, store, advance BOTH cursors. The
      -- stride here is word_bytes and not g1_bytes, the one place in the section list where
      -- a copy of the walk shape with the wrong stride would still tokenise to the same
      -- number of tokens.
    , yblock
        [ ylet "eval_buf" (yvar "REVERSED_EVALS_MPTR")
        , yfor [ylet "end" (yop Op.add [yvar "proof_cptr", ylit L.evals.byteLen])]
            (yop Op.lt [yvar "proof_cptr", yvar "end"]) []
            [ ylet "eval" (yop Op.calldataload [yvar "proof_cptr"])
            , yif (yop Op.iszero [yop Op.lt [yvar "eval", yvar "r"]])
                [yexpr (ycall "fail" [yvar "ERR_NON_CANONICAL_SCALAR"])]
            , yexpr (yop Op.mstore [yvar "eval_buf", yvar "eval"])
            , yset "eval_buf" (yop Op.add [yvar "eval_buf", ylit word])
            , yset "buf_len" (ycall "common_word" [yvar "buf_len", yvar "eval"])
            , yset "proof_cptr" (yop Op.add [yvar "proof_cptr", ylit word]) ] ]
    , squeeze "X1_MPTR", squeeze "X2_MPTR"
    ] ++ g1AbsorbCopy "F_COM_MPTR" ++
    [ squeeze "X3_MPTR" ] ++
    -- the truncated-challenges mask: keep the low 128 bits of the squeezed x3 in its slot.
    (if truncatedChallenges then
      [ yexpr (yop Op.mstore [yvar "X3_MPTR",
          yop Op.and [yop Op.mload [yvar "X3_MPTR"],
            ylit 0xffffffffffffffffffffffffffffffff]]) ] else []) ++
    [ yexpr (yop Op.mstore [yvar "Q_EVAL_CPTR_MPTR", yvar "proof_cptr"])
    , yfor [ylet "end" (yop Op.add [yvar "proof_cptr", ylit L.qEvals.byteLen])]
        (yop Op.lt [yvar "proof_cptr", yvar "end"]) []
        [ ylet "eval" (yop Op.calldataload [yvar "proof_cptr"])
        , yif (yop Op.iszero [yop Op.lt [yvar "eval", yvar "r"]])
            [yexpr (ycall "fail" [yvar "ERR_NON_CANONICAL_SCALAR"])]
        , yset "buf_len" (ycall "common_word" [yvar "buf_len", yvar "eval"])
        , yset "proof_cptr" (yop Op.add [yvar "proof_cptr", ylit word]) ]
    , squeeze "X4_MPTR"
    ] ++ g1AbsorbCopy "PI_MPTR" ++
    -- the two tail guards: the cursor identity P-12's gate 22 cites, then the deferred
    -- canonicality failure the instance run folded into success.
    [ yif (yop Op.iszero [yop Op.eq [yvar "proof_cptr", yvar "NUM_INSTANCE_CPTR"]])
        [yexpr (ycall "fail" [yvar "ERR_BAD_CALLDATA_SHAPE"])]
    , yif (yop Op.iszero [yvar "success"])
        [yexpr (ycall "fail" [yvar "ERR_NON_CANONICAL_SCALAR"])] ]
/-- The transcriptParser slice of one plan: the eleven values the template interpolates, all
    read out of PlanView - the one count it already carried, the six P-AST4 fields, and the
    seven proofLayout section accessors. -/
def emitTranscriptParser (pv : PlanView) : Block Op :=
  emitTranscriptParserAt pv.numInstances pv.userPhases pv.numLookups
    pv.numPermutationZs pv.lookupHPlusAcc pv.numTrashcans pv.truncatedChallenges
    pv.proofLayout

/-- The seven plan values the transcriptParser template interpolates beyond the proof
    layout, read out of the text port's own deployed profile - the same device
    vkLoadingPoseidonArgs uses, so the emitter and the text port are fed one set of numbers
    and cannot be given different ones by accident. -/
def transcriptParserPoseidonArgs : Nat × List UserPhase × Nat × Nat × Nat × Nat × Bool :=
  (poseidonCtx.numInstances, poseidonCtx.userPhases, poseidonCtx.numLookups,
    poseidonCtx.numPermutationZs, poseidonCtx.lookupHPlusAcc, poseidonCtx.numTrashcans,
    poseidonCtx.truncatedChallenges)

/-- The deployed slice, emitted at the poseidon profile - the block gates 21 and 37-44
    compare. -/
def emitTranscriptParserDeployed : Block Op :=
  let (n, ph, nl, nz, lh, nt, tc) := transcriptParserPoseidonArgs
  emitTranscriptParserAt n ph nl nz lh nt tc poseidonProofLayout

/-- The three counts the deployed poseidon context carries, re-expressed as the meta
    PlanView now reads them from. SAY WHICH IS WHICH: this is an OBSERVATION and not a
    derivation - poseidonCtx is P-13's transcription of the dump's own lines, so a meta built
    from its counts has exactly the transcription status of the counts themselves. It exists
    so that the parser gates keep driving the deployed numbers THROUGH the PlanView projection
    (which is what they are for) rather than through a tuple, and nothing that claims anything
    about a circuit reads it. The derived meta in this tree is the Kzg fixture's (Encoding.lean
    metaFixture, from ConstraintSystemMeta.new over Protocol.lean's fixtureCs), and that is
    the one the pcs gates run on. -/
def poseidonCountMeta : Midfall.Generator.ConstraintSystemMeta :=
  let m := Midfall.Generator.constraintSystemMetaDefault
  { m with numLookups := poseidonCtx.numLookups, numPermutationZs := poseidonCtx.numPermutationZs, numTrashcans := poseidonCtx.numTrashcans }

/-- The Data that goes with poseidonCountMeta: DERIVED by Data.new over the deployed context's
    own memory, not transcribed. Nothing here reads it for a pcs emission (the pcs gates use
    the Kzg fixture), so its job is to keep the plan view a coherent pair rather than a meta
    with an unrelated Data bolted on. -/
def poseidonCountData : Midfall.Generator.Data :=
  match Midfall.Generator.Data.new poseidonCountMeta Midfall.Lowering.witnessVkPayload
      poseidonCtx.memory with
  | .ok d => d
  | .error _ => Midfall.Lowering.emptyDataAt poseidonCtx.memory

/-- The three parser counts, one of them replaced. Three defs rather than one three-argument
    helper because every gate that uses them perturbs exactly ONE count, and a call site that
    had to re-state the other two could move them by accident - which is the one-field-at-a-
    time discipline gate 38 exists to keep. This is the shape those gates take now that the
    three counts are projections of the meta and no longer fields a with-clause can write. -/
def withNumLookups (n : Nat) (pv : PlanView) : PlanView :=
  let m := pv.meta_
  { pv with meta_ := { m with numLookups := n } }
def withNumPermutationZs (n : Nat) (pv : PlanView) : PlanView :=
  let m := pv.meta_
  { pv with meta_ := { m with numPermutationZs := n } }
def withNumTrashcans (n : Nat) (pv : PlanView) : PlanView :=
  let m := pv.meta_
  { pv with meta_ := { m with numTrashcans := n } }

/-- The deployed plan view the parser gates read through the PlanView fields rather than
    through the profile tuple: the same values, reached by the constructor. Built here and not
    in Instances/ because it is a gate input and not a theorem hypothesis. -/
def transcriptParserPoseidonPlan : PlanView :=
  Midfall.Lowering.planViewWithAccumulator
    (vk := Midfall.Lowering.witnessVkPayload)
    (vkMptr := poseidonCtx.memory.vkMptr)
    (memory := poseidonCtx.memory)
    (proofLayout := poseidonProofLayout)
    (numInstances := poseidonCtx.numInstances) (k := poseidonCtx.k)
    (numNegLagranges := poseidonCtx.numNegLagranges) (acc := none)
    (facts := (poseidonCtx.userPhases, poseidonCtx.lookupHPlusAcc,
      poseidonCtx.truncatedChallenges))
    (meta_ := poseidonCountMeta) (dat := poseidonCountData)
/-- The one-statement dummy for a partial the emitter does not implement. SINCE P-PLANVIEW
    IT IMPLEMENTS ALL SEVEN, so nothing in the emitter can reach this def: the dispatch's
    match is exhaustive and placeholderPartials is proved empty. It stays because the
    falsification plants in Instances/SurfaceFixture.lean need a block to plant - each plant
    puts a real slice back to its own dummy and the pin has to refuse it - and because the
    "placeholder is not the emitter's answer" conjuncts in GenAstDispatch's gate 8 read these
    seven blocks. D-P30 clause 4 asked for the placeholders to end up unreachable rather than
    merely well-documented; that is now the case, and the plants are the evidence that the
    unreachability is load-bearing rather than vacuous. -/
def emitPlaceholder : Partial → Block Op
  | .vkLoading => [yexpr (yop Op.mstore [ylit 0x2000, ylit 1])]
  | .transcriptParser => [yexpr (yop Op.mstore [ylit 0x2100, ylit 2])]
  | .lagrange => [yexpr (yop Op.mstore [ylit 0x2200, ylit 3])]
  | .quotientLin => [yexpr (yop Op.mstore [ylit 0x2300, ylit 4])]
  | .pcs => [yexpr (yop Op.mstore [ylit 0x2400, ylit 5])]
  | .finalPairing => [yexpr (yop Op.mstore [ylit 0x2500, ylit 6])]
  | .traceReturn => [yexpr (yop Op.ret [ylit 0x1000, ylit 0x20])]


/-! ### The text-port comparison machinery -/

/-- Braces introduced minus braces closed on one rendered line, with any '//'-comment
    stripped first. The comment strip is not tidiness: the transcript helpers' own comment
    block sits between the function definitions, and a brace inside prose would move the
    depth and cut a slice in the wrong place. -/
def braceDelta (l : String) : Int :=
  let code := match l.splitOn "//" with
    | first :: _ => first
    | [] => l
  ((code.toList.filter fun c => c == '{').length : Int) -
    (code.toList.filter fun c => c == '}').length

/-- The number of lines from the head of the list through the line that returns the brace
    depth to zero - i.e. the function's OWN closing brace, not the first '}' that happens
    to start a line. -/
def functionCloseAt (ls : List String) : Nat :=
  let rec go (rest : List String) (d : Int) (i : Nat) : Nat :=
    match rest with
    | [] => i
    | l :: more =>
        let d' := d + braceDelta l
        if d' <= 0 then i + 1 else go more d' (i + 1)
  go ls 0 0

/-- The rendered text of one 'function NAME(...)' definition inside a render: its header
    line through its closing brace, comments included (yulTokens drops them). Used to slice
    fail, ec_pairing and the four transcript helpers out of the AssemblyHelpers render,
    which is one string.

    P-AST4 REPAIRED THE CLOSE TEST, and the defect it repaired is the finding. The old rule
    was "the first line whose trimmed text is '}'", which is the function's close only when
    the body contains no block statement written across lines. common_uncompressed_g1 does
    (AssemblyHelpers.yul: its two coordinate range checks each open a '{' and close it on a
    line of its own), so the old slicer returned 13 lines ending at the INNER '}' - a
    truncated, syntactically incomplete fragment that no gate could compare an emitted
    function against. P-AST3b measured "common_uncompressed_g1 13 lines" and reported it as
    the function's size; it is the slicer's truncation point, and 13 is the number of
    STATEMENTS in the real function, not of lines. The depth-aware rule returns 22 lines,
    leaves fail (4), ec_pairing (36), transcript_init (4), common_word (4) and squeeze_to
    (9) exactly where they were - gate 11 below pins all six sizes so a future regression in
    either direction is a red gate - and it is a string helper, not a DSL change. -/
def renderFunction (render name : String) : String :=
  let ls := render.splitOn "\n"
  let header := "function " ++ name ++ "("
  match (ls.zipIdx.find? fun (l, _i) => (trimWs l).startsWith header) with
  | none => ""
  | some (_l, i) =>
    let rest := ls.drop i
    String.intercalate "\n" (rest.take (functionCloseAt rest))

/-! ### Gates -/

/-- GATE 1 (the D-P25 tripwire). The emitted FinalPairing AST prints to the same token
    stream as the text port's render of the same partial in the same profile. This is the
    check the brief asks for, and it is token-level on purpose: printed text differs on
    identical programs (R-62). -/
def emitFinalPairing_tokens_ok : Bool :=
  yulTokens ("{" ++ renderFinalPairing poseidonCtx ++ "}") ==
    yulTokens (EVM.print (emitFinalPairingArms poseidonCtx.expectedHasAccumulator
      poseidonCtx.accumulatorPairingBatchMptr))

/-- GATE 2. The same for the accumulator arm, which the deployed fixture does not take: the
    emitter is a FUNCTION of the plan and the parameterisation is exercised on both arms,
    not only on the one the artifact happens to show. -/
def emitFinalPairingAcc_tokens_ok : Bool :=
  yulTokens ("{" ++ renderFinalPairing
    { poseidonCtx with expectedHasAccumulator := true } ++ "}") ==
    yulTokens (EVM.print (emitFinalPairingArms true
      poseidonCtx.accumulatorPairingBatchMptr))

/-- GATE 3. The fail helper: the emitted AST against the text port's own function, sliced
    out of the AssemblyHelpers render rather than re-typed here. -/
def emitFail_tokens_ok : Bool :=
  yulTokens ("{" ++ renderFunction (renderAssemblyHelpers poseidonCtx) "fail" ++ "}") ==
    yulTokens (EVM.print emitFail)

/-- GATE 4. The ec_pairing helper, same shape as gate 3, against the render of the same
    scratch pointer the emitter is given. -/
def emitEcPairing_tokens_ok : Bool :=
  yulTokens ("{" ++ renderFunction (renderAssemblyHelpers poseidonCtx) "ec_pairing" ++ "}") ==
    yulTokens (EVM.print (emitEcPairing poseidonCtx.finalPairingScratchMptr
      templateConstantsDefault.eip2537.pairingAddress
      templateConstantsDefault.pairingTwoPairBytes templateConstantsDefault.wordBytes))

/-- GATE 5 (authoritative relation, no-acc arm). The emitted AST equals the yul% quotation
    that already existed as a fixed snapshot in VerifierPartials.lean - generalised, not
    replaced - under stmtsBeq, the relation Phase 5's irCheck uses. This is the gate that
    pins the built-in-versus-user-call split, which no token gate can see. -/
def emitFinalPairing_beq_ok : Bool :=
  SyntaxEq.stmtsBeq (emitFinalPairingArms false
    poseidonCtx.accumulatorPairingBatchMptr) VerifierPartialKats.finalPairing_ast

/-- GATE 6. The same for the fail helper against VerifierPartials' failFunction_ast. -/
def emitFail_beq_ok : Bool := SyntaxEq.stmtsBeq emitFail VerifierPartialKats.failFunction_ast

/-- GATE 7 (the emitter is a function of the plan, and the plan matters). Flipping
    hasAccumulator changes the emitted block, and so does moving the scratch pointer or the
    precompile address. Without this an emitter that ignored its arguments would pass every
    gate above, because the poseidon profile is one point of the parameter space. -/
def emitDependsOnPlan_ok : Bool :=
  ! SyntaxEq.stmtsBeq (emitFinalPairingArms true 0x1000)
    (emitFinalPairingArms false 0x1000) &&
    ! SyntaxEq.stmtsBeq (emitEcPairing 0x1240 0x0f 768 32) (emitEcPairing 0x1241 0x0f 768 32) &&
    ! SyntaxEq.stmtsBeq (emitEcPairing 0x1240 0x0f 768 32) (emitEcPairing 0x1240 0x10 768 32) &&
    ! SyntaxEq.stmtsBeq (emitFinalPairingArms true 0x1000)
      (emitFinalPairingArms true 0x1020) &&
    -- and the batch pointer is inert EXACTLY when there is no accumulator arm to use it,
    -- which is the same fact stated the other way round: the parameter reaches the emitted
    -- block through the arm it belongs to, not through a wildcard.
    SyntaxEq.stmtsBeq (emitFinalPairingArms false 0x1000)
      (emitFinalPairingArms false 0x1020) &&
    -- P-AST2: the same for Lagrange, where all three plan values reach the block through a
    -- window size or a loop bound and none of them is decorative.
    ! SyntaxEq.stmtsBeq (emitLagrangeAt 6 1 9) (emitLagrangeAt 7 1 9) &&
    ! SyntaxEq.stmtsBeq (emitLagrangeAt 6 1 9) (emitLagrangeAt 6 2 9) &&
    ! SyntaxEq.stmtsBeq (emitLagrangeAt 6 1 9) (emitLagrangeAt 6 1 8) &&
    -- P-AST3a: and QuotientLin, where the ONE interpolated value is the domain exponent, so
    -- a gate on k alone is a gate on the whole slice. The second conjunct says the same
    -- thing through emitQuotientLin, i.e. through the PlanView field and not only the
    -- Nat parameter, so the dispatch cannot ignore pv.k and stay green.
    ! SyntaxEq.stmtsBeq (emitQuotientLinAt 6) (emitQuotientLinAt 7) &&
    ! SyntaxEq.stmtsBeq (emitQuotientLin Midfall.Lowering.witnessPlanView)
      (emitQuotientLin { Midfall.Lowering.witnessPlanView with k := 3 }) &&
    -- P-AST3b: and VkLoading, where all SEVEN plan values reach the block through the
    -- PlanView fields rather than through the deployed constants. Each field moved by one
    -- changes the emitted AST, so the dispatch cannot ignore any of them - including the
    -- four accumulator words, which is the whole point of deriving them instead of
    -- hard-coding the artifact's four zeros.
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with numInstances := 2 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with k := 3 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with
                       expectedHasAccumulatorWord := 1 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with expectedAccOffset := 1 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with expectedNumAccLimbs := 1 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with
                       expectedNumAccLimbBits := 1 }) &&
    ! SyntaxEq.stmtsBeq (emitVkLoading Midfall.Lowering.witnessPlanView)
      (emitVkLoading { Midfall.Lowering.witnessPlanView with
                       proofLayout := { Midfall.Lowering.witnessPlanView.proofLayout with
                                        proofLen :=
                                          Midfall.Lowering.witnessPlanView.proofLayout.proofLen + 32 } }) &&
    -- and TraceReturn is CONSTANT in the plan, which is the template's own shape and not a
    -- hole: stated as a computation so a later package that parameterises it has to notice
    -- it changed this gate.
    (Midfall.Lowering.partials.all fun _q =>
      SyntaxEq.stmtsBeq (emitTraceReturn Midfall.Lowering.witnessPlanView)
        emitTraceReturnBlock)

/-- GATE 9 (perturbation). One literal of the emitted block changed - the scratch pointer of
    the ec_pairing frame - turns BOTH relations red: the token stream and stmtsBeq. This is
    the falsifiability of gates 1-6 as a computation, in the minimal-perturbation shape
    YulGolden's discriminates_fixture_ok established. -/
def emitDetectsPerturbation_ok : Bool :=
  let good := emitEcPairing 0x1240 0x0f 768 32
  let bad := emitEcPairing 0x1241 0x0f 768 32
  yulTokens (EVM.print good) != yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad

/-- GATE 10 (the relation gap, at the emitter). Spelling the mcopy of the emitted
    ec_pairing as a USER call keeps the token stream and breaks stmtsBeq - the exact
    wrong-implementation class YulGolden.lean names, reproduced on this file's own AST
    rather than on a fixture. -/
def emitDetectsBuiltinVsCall_ok : Bool :=
  let fix (s : Stmt Op) : Stmt Op := match s with
    | Stmt.exprStmt (Expr.builtin Op.mcopy args) => yexpr (ycall "mcopy" args)
    | s => s
  let good := emitEcPairing 0x1240 0x0f 768 32
  let bad : Block Op := good.map fun
    | Stmt.funDef n p r body => Stmt.funDef n p r (body.map fix)
    | s => s
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad

/-- GATE 11 (the slicer is not vacuous, and its close test is now measured on SIX
    definitions and not two). renderFunction finds each helper and finds it as a complete
    function definition, so gates 3, 4 and 37 compare a real slice and not the empty string
    against the empty string; it returns "" for a name the render does not define, so a typo
    in a gate name is a red gate rather than a silent agreement; and the six LINE COUNTS are
    pinned, which is the clause that makes the P-AST4 repair of the close test a gate and not
    a claim. Without the depth-aware close, common_uncompressed_g1 comes back as 13 lines
    ending at an inner brace and this gate goes red - measured, not asserted: the naive rule
    was reverted on a copy of the tree and gate 11 was the first thing to fail. The other five
    sizes are pinned in the same clause so a future over- or under-run of the depth counter is
    caught on whichever helper it hits. -/
def renderFunctionSlices_ok : Bool :=
  (trimWs (renderFunction (renderAssemblyHelpers poseidonCtx) "fail")).startsWith
    "function fail(sel)" &&
    (trimWs (renderFunction (renderAssemblyHelpers poseidonCtx) "ec_pairing")).startsWith
      "function ec_pairing(success, lhs_mptr, rhs_mptr)" &&
    (renderFunction (renderAssemblyHelpers poseidonCtx) "no_such_helper") == "" &&
    let ah := renderAssemblyHelpers poseidonCtx
    VerifierPartialKats.lineCount (renderFunction ah "fail") == 4 &&
    VerifierPartialKats.lineCount (renderFunction ah "ec_pairing") == 36 &&
    VerifierPartialKats.lineCount (renderFunction ah "transcript_init") == 4 &&
    VerifierPartialKats.lineCount (renderFunction ah "common_word") == 4 &&
    VerifierPartialKats.lineCount (renderFunction ah "common_uncompressed_g1") == 22 &&
    VerifierPartialKats.lineCount (renderFunction ah "squeeze_to") == 9 &&
    -- and each slice ENDS at a column-12 closing brace, i.e. at the function's own end and
    -- not at a nested block's - the exact shape that defeated the old rule.
    (["transcript_init", "common_word", "common_uncompressed_g1", "squeeze_to", "ec_pairing"].all
      fun nm => match ((renderFunction ah nm).splitOn "\n").reverse.head? with
        | some last => last == "            }"
        | none => false)

/-! ### Authoritative snapshots: the emitted AST against a quotation

The token comparator cannot see the built-in-versus-user-call split (YulGolden.lean's
header, and emitDetectsBuiltinVsCall_ok here). Gates 1-4 compare against the TEXT PORT and
so inherit that blindness: an emitter that spelled mcopy as a call to a user function named
mcopy would pass all four. These two quotations close the gap for the two blocks the token
gates cover, in the same shape finalPairing_ast and failFunction_ast already establish -
the yul% DSL is a second, independent elaboration path from the constructor helpers, so a
gate between them is not self-fulfilling. -/

/-- The deployed ec_pairing, quoted. Transcribed from the same template region
    AssemblyHelpers.yul:269-302 that the text port renders; the numbers are the poseidon
    profile's, which is why the gate below passes the poseidon scratch pointer to the
    emitter rather than an arbitrary one. -/
def ecPairing_snapshot : Block Op := yul% {
  function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret {
    ret := success
    if iszero(ret) { leave }
    let scratch := 0x1240
    mcopy(scratch, lhs_mptr, 0x80)
    mcopy(add(scratch, 0x80), G2_BASE_MPTR, 0x100)
    mcopy(add(scratch, 0x180), rhs_mptr, 0x80)
    mcopy(add(scratch, 0x200), NEG_S_G2_BASE_MPTR, 0x100)
    ret := staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, scratch, 0x20)
    ret := and(ret, eq(returndatasize(), 0x20))
    if iszero(ret) { fail(ERR_PRECOMPILE_FAILED) }
    ret := and(ret, eq(mload(scratch), 1))
    if iszero(ret) { fail(ERR_PROOF_REJECTED) }
    ret := 1
  }
}

/-- The accumulator arm's batch block, quoted from the render of the same template region
    (FinalPairing.yul:14-62) with the flag flipped. The deployed artifact does not contain
    it, so this is the arm the text port reaches only through poseidonCtx's override - and
    the reason gate 2 above is not the only check on it. -/
def accBatch_snapshot : Block Op := yul% {
  {
    let batch_ptr := 0x1000
    mstore(batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
    mstore(add(batch_ptr, 0x20), mload(VK_DIGEST_MPTR))
    mcopy(add(batch_ptr, 0x40), PAIRING_RHS_MPTR, 0x80)
    mcopy(add(batch_ptr, 0xc0), PAIRING_LHS_MPTR, 0x80)
    mcopy(add(batch_ptr, 0x0140), ACC_RHS_MPTR, 0x80)
    mcopy(add(batch_ptr, 0x01c0), ACC_LHS_MPTR, 0x80)
    let acc_pair_alpha := mod(keccak256(batch_ptr, 0x0240), r)
    if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }
    mcopy(batch_ptr, ACC_RHS_MPTR, 0x80)
    mstore(add(batch_ptr, 0x80), acc_pair_alpha)
    if success {
      success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
      success := and(success, eq(returndatasize(), 0x80))
    }
    mcopy(add(batch_ptr, 0x80), PAIRING_RHS_MPTR, 0x80)
    if success {
      success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_RHS_MPTR, 0x80)
      success := and(success, eq(returndatasize(), 0x80))
    }
    mcopy(batch_ptr, ACC_LHS_MPTR, 0x80)
    mstore(add(batch_ptr, 0x80), acc_pair_alpha)
    if success {
      success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
      success := and(success, eq(returndatasize(), 0x80))
    }
    mcopy(add(batch_ptr, 0x80), PAIRING_LHS_MPTR, 0x80)
    if success {
      success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_LHS_MPTR, 0x80)
      success := and(success, eq(returndatasize(), 0x80))
    }
  }
}

/-- GATE 12 (authoritative, ec_pairing). The emitted helper equals its quotation under
    stmtsBeq. This is the gate that reddens when a dialect built-in is spelled as a user
    call - the class the four token gates above are blind to by construction. -/
def emitEcPairing_beq_ok : Bool :=
  SyntaxEq.stmtsBeq (emitEcPairing poseidonCtx.finalPairingScratchMptr
    templateConstantsDefault.eip2537.pairingAddress
    templateConstantsDefault.pairingTwoPairBytes templateConstantsDefault.wordBytes)
    ecPairing_snapshot

/-- GATE 13 (authoritative, accumulator arm). The emitted batch block equals its quotation
    under stmtsBeq, at the poseidon batch pointer. -/
def emitAccBatch_beq_ok : Bool :=
  SyntaxEq.stmtsBeq (emitFinalPairingArms true poseidonCtx.accumulatorPairingBatchMptr)
    (accBatch_snapshot ++ [
      yif (yop Op.iszero [yvar "success"])
          [yexpr (ycall "fail" [yvar "ERR_PRECOMPILE_FAILED"])],
      yset "success" (ycall "ec_pairing" [yvar "success", yvar "PAIRING_RHS_MPTR",
          yvar "PAIRING_LHS_MPTR"]) ])

/-! ### The P-AST2 gates: lagrange and traceReturn -/

/-- Rewrite the OUTERMOST expression of every statement in a block, recursing through nested
    blocks, function bodies, loop init/condition/post and if bodies. The two
    emit*_DetectsBuiltinVsCall_ok gates use it to mis-spell a dialect built-in as a user call
    at every depth, which is what the P-AST measurement did to the mcopy of ec_pairing: a
    shallow map would miss the statements inside the Lagrange loops and leave the gate green
    for the wrong reason.

    'switch' is returned untouched, and that is a measured limitation rather than a shortcut:
    recursing through its '(Literal x Block)' pairs defeats structural termination here
    ('sizeOf' does not decrease through the pair, reported at elaboration), and none of the
    three real slices contains a switch - the deployed verifier has no switch statement
    anywhere. A later package that emits one has to extend this and delete the note. -/
def mapStmtExprs (f : Expr Op → Expr Op) : Stmt Op → Stmt Op
  | Stmt.block b => Stmt.block (b.map (mapStmtExprs f))
  | Stmt.funDef n p r b => Stmt.funDef n p r (b.map (mapStmtExprs f))
  | Stmt.letDecl v (some e) => Stmt.letDecl v (some (f e))
  | Stmt.letDecl v none => Stmt.letDecl v none
  | Stmt.assign v e => Stmt.assign v (f e)
  | Stmt.cond c b => Stmt.cond (f c) (b.map (mapStmtExprs f))
  | Stmt.switch c cs d => Stmt.switch c cs d
  | Stmt.forLoop i c p b =>
      Stmt.forLoop (i.map (mapStmtExprs f)) (f c) (p.map (mapStmtExprs f))
        (b.map (mapStmtExprs f))
  | Stmt.exprStmt e => Stmt.exprStmt (f e)
  | s => s

/-- GATE 14 (the D-P25 tripwire, Lagrange). The emitted AST prints to the same token stream
    as the TEXT PORT's render of the same partial under the same profile, at the plan values
    the deployed poseidon artifact was generated with. Secondary relation on purpose - see
    gate 15 for the record. -/
def emitLagrange_tokens_ok : Bool :=
  yulTokens ("{" ++ renderLagrange poseidonCtx ++ "}") ==
    yulTokens (EVM.print (emitLagrangeAt poseidonCtx.k poseidonCtx.numInstances
      poseidonCtx.numNegLagranges))

/-- GATE 15 (authoritative, Lagrange). The emitted AST equals the 'yul%' quotation of the
    same render - VerifierPartialKats.lagrange_ast, which already existed in the tree as a
    fixed snapshot - under stmtsBeq. This is the gate the brief calls the record: it separates
    Expr.builtin from Expr.call, it separates a for-loop's three sub-blocks from a flat
    sequence, and it compares the two-name assignment against a one-name one. The quotation
    is an independent elaboration path (a parser, not these constructors), so the gate is not
    self-fulfilling. -/
def emitLagrange_beq_ok : Bool :=
  SyntaxEq.stmtsBeq (emitLagrangeAt poseidonCtx.k poseidonCtx.numInstances
    poseidonCtx.numNegLagranges) VerifierPartialKats.lagrange_ast

/-- GATE 16 (the tripwire, TraceReturn). Same shape as gate 14 against renderTraceReturn. -/
def emitTraceReturn_tokens_ok : Bool :=
  yulTokens ("{" ++ renderTraceReturn poseidonCtx ++ "}") ==
    yulTokens (EVM.print emitTraceReturnBlock)

/-- GATE 17 (authoritative, TraceReturn). The emitted production arm equals the existing
    traceReturn_ast quotation under stmtsBeq - the same block that VerifierPartials' gate 80
    ties to traceReturn_direct, so the constructor path, the quotation and the raw-AST path
    in that file are now one equivalence class rather than three claims. -/
def emitTraceReturn_beq_ok : Bool :=
  SyntaxEq.stmtsBeq emitTraceReturnBlock VerifierPartialKats.traceReturn_ast

/-- GATE 18 (perturbation, Lagrange, D-P23 falsifiability of gates 14-15). Each of the three
    plan values, changed by one, turns BOTH relations red: k moves the loop bound, the
    instance count moves the denominator window AND the instance loop's end, and the
    negative-rotation count moves the window, the l_i_cptr_end and the l_0 slot. A gate that
    only reddened on one of the three would leave two of the parameters decorative. -/
def emitLagrangeDetectsPerturbation_ok : Bool :=
  let good := emitLagrangeAt 6 1 9
  yulTokens (EVM.print good) != yulTokens (EVM.print (emitLagrangeAt 7 1 9)) &&
    ! SyntaxEq.stmtsBeq good (emitLagrangeAt 7 1 9) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (emitLagrangeAt 6 2 9)) &&
    ! SyntaxEq.stmtsBeq good (emitLagrangeAt 6 2 9) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (emitLagrangeAt 6 1 8)) &&
    ! SyntaxEq.stmtsBeq good (emitLagrangeAt 6 1 8)

/-- GATE 19 (the relation gap, at the Lagrange slice). Every mstore of the emitted block
    spelled as a USER call named 'mstore' keeps the token stream and breaks stmtsBeq - the
    exact class P-AST measured on ec_pairing, reproduced on this slice, where the mis-spelling
    is inside nested blocks and for-loop bodies so a shallow rewrite would not reach it. -/
def emitLagrangeDetectsBuiltinVsCall_ok : Bool :=
  let good := emitLagrangeAt poseidonCtx.k poseidonCtx.numInstances
    poseidonCtx.numNegLagranges
  let bad := good.map (mapStmtExprs fun
    | Expr.builtin Op.mstore args => Expr.call "mstore" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad

/-- GATE 20 (the relation gap, at the TraceReturn slice, in the other direction). The
    terminal 'return' spelled as a USER call named 'return' keeps the token stream and breaks
    stmtsBeq. TraceReturn is the slice where the wrong choice is most dangerous: the whole
    post-condition of traceReturn_spec is a '.halt (.ret, abiTrue)' record, and a user call
    named return does not halt. -/
def emitTraceReturnDetectsBuiltinVsCall_ok : Bool :=
  let good := emitTraceReturnBlock
  let bad := good.map (mapStmtExprs fun
    | Expr.builtin Op.ret args => Expr.call "return" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad

/-- GATE 21 (the numeric spelling, pinned as a divergence - D-P30 clause 3). The text port
    writes the denominator window in hex and the AST prints the same value in decimal; the
    token comparator maps the two onto each other, which is exactly why the divergence is
    invisible there and why it needs its own gate. Four things are asserted: the hex form
    occurs in the render, the decimal form occurs in the printed AST, the hex form does NOT
    occur in the printed AST (so nobody has normalised it away), and the hex-to-value map the
    comparator uses sends each pinned literal to the number the emitter put in. -/
def numericSpellingDivergence_ok : Bool :=
  let printed := EVM.print (emitLagrangeAt poseidonCtx.k poseidonCtx.numInstances
    poseidonCtx.numNegLagranges)
  (renderLagrange poseidonCtx).contains ("let mptr_end := add(mptr, "
      ++ hexFilter ((poseidonCtx.numInstances + poseidonCtx.numNegLagranges) * 32) ++ ")") &&
    printed.contains "add(mptr, 320)" &&
    ! printed.contains "0x0140" &&
    yulTokens "add(mptr, 320)" == yulTokens "add(mptr, 0x0140)" &&
    hexLiteral "0x0140" == 320 &&
    hexLiteral "0x0120" == 288 &&
    hexLiteral "0x20" == 32 &&
    -- and the same mapping on the TraceReturn arm: the render's 0x20 is the AST's 32.
    (renderTraceReturn poseidonCtx).contains "return(RETURN_MPTR, 0x20)" &&
    (EVM.print emitTraceReturnBlock).contains "return(RETURN_MPTR, 32)" &&
    -- P-AST3a, and the QuotientLin slice, where BOTH spellings occur in one 42-line region:
    -- the QUOTIENT_MPTR word offset is a hex filter in the render and a decimal 32 in the
    -- printed AST, while the one interpolated value (k) is decimal on both sides because the
    -- template interpolates it as an integer. A slice can mix the two, which is precisely why
    -- no AST relation can be the record for numeric notation.
    (renderQuotientAndLinearization poseidonCtx "" "").contains
      "mstore(add(QUOTIENT_MPTR, 0x20), one_minus_x_n)" &&
    (EVM.print (emitQuotientLinAt poseidonCtx.k)).contains
      "mstore(add(QUOTIENT_MPTR, 32), one_minus_x_n)" &&
    ! (EVM.print (emitQuotientLinAt poseidonCtx.k)).contains "0x" &&
    (renderQuotientAndLinearization poseidonCtx "" "").contains "let k := 6" &&
    (EVM.print (emitQuotientLinAt poseidonCtx.k)).contains "let k := 6" &&
    yulTokens "add(QUOTIENT_MPTR, 32)" == yulTokens "add(QUOTIENT_MPTR, 0x20)" &&
    -- P-AST3b, and the VkLoading slice, where THREE different hex spellings occur in one
    -- 74-line region: the proof length (0x10e0 = 4320), the instance window (0x20 = 32)
    -- and the payload copy offset (0x01 = 1). The last is the sharpest case in the tree - a
    -- one-digit hex literal whose decimal spelling is a different number of characters - so
    -- even a line-length comparison cannot see it and only a string-containment gate can.
    (renderVkLoading poseidonCtx).contains
      "eq(0x10e0, calldataload(PROOF_LEN_CPTR))" &&
    (EVM.print emitVkLoadingDeployed).contains
      "eq(4320, calldataload(PROOF_LEN_CPTR))" &&
    (renderVkLoading poseidonCtx).contains "add(INSTANCE_CPTR, 0x20)" &&
    (EVM.print emitVkLoadingDeployed).contains "add(INSTANCE_CPTR, 32)" &&
    (renderVkLoading poseidonCtx).contains "extcodecopy(vk, VK_MPTR, 0x01," &&
    (EVM.print emitVkLoadingDeployed).contains "extcodecopy(vk, VK_MPTR, 1," &&
    ! (EVM.print emitVkLoadingDeployed).contains "0x" &&
    yulTokens "eq(4320, calldataload(PROOF_LEN_CPTR))" ==
      yulTokens "eq(0x10e0, calldataload(PROOF_LEN_CPTR))" &&
    yulTokens "extcodecopy(vk, VK_MPTR, 1)" == yulTokens "extcodecopy(vk, VK_MPTR, 0x01)" &&
    hexLiteral "0x10e0" == 4320 &&
    -- P-AST4, and the transcriptParser slice - the widest case in the file, because ONE
    -- region mixes all three spellings: the section widths and the strides go through the
    -- hex filter ('add(proof_cptr, 0x0400)', 'add(proof_cptr, 0x20)', 'add(proof_cptr, 0x60)'),
    -- the instance count is interpolated as a DECIMAL integer ('common_word(buf_len, 1)'),
    -- and the x3 mask is a bare 32-nibble hex literal the template writes verbatim. The AST
    -- prints 1024, 32, 96, 1 and the 128-bit modulus of 2 in decimal - 34028236692093846346
    -- 3374607431768211455, a 39-digit number from a 32-character literal. No AST relation can
    -- see any of it: stmtsBeq and yulTokens both map hex to value, so a converter that
    -- normalised the render's notation instead of its numbers would be invisible here and
    -- only a string-containment gate catches it.
    (renderTranscriptProofParser poseidonCtx).contains
      "for { let end := add(proof_cptr, 0x0400) }" &&
    (EVM.print emitTranscriptParserDeployed).contains "add(proof_cptr, 1024)" &&
    (renderTranscriptProofParser poseidonCtx).contains "add(proof_cptr, 0x60) }" &&
    (EVM.print emitTranscriptParserDeployed).contains "add(proof_cptr, 96)" &&
    (renderTranscriptProofParser poseidonCtx).contains "buf_len := common_word(buf_len, 1)" &&
    (EVM.print emitTranscriptParserDeployed).contains "common_word(buf_len, 1)" &&
    (renderTranscriptProofParser poseidonCtx).contains
      "mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))" &&
    (EVM.print emitTranscriptParserDeployed).contains
      "mstore(X3_MPTR, and(mload(X3_MPTR), 340282366920938463463374607431768211455))" &&
    ! (EVM.print emitTranscriptParserDeployed).contains "0x" &&
    yulTokens "add(proof_cptr, 1024)" == yulTokens "add(proof_cptr, 0x0400)" &&
    hexLiteral "0x0400" == 1024 &&
    -- and the four helpers, where the two spellings sit inside ONE function: common_word's
    -- stride is decimal 32 in the template and prints decimal 32 here - the coincidence the
    -- emitCommonWord header claims - while common_uncompressed_g1's copy length is the hex
    -- literal 0x80 and prints 128.
    (renderFunction (renderAssemblyHelpers poseidonCtx) "common_word").contains
      "ret := add(buf_len, 32)" &&
    (EVM.print emitCommonWord).contains "ret := add(buf_len, 32)" &&
    (renderFunction (renderAssemblyHelpers poseidonCtx) "common_uncompressed_g1").contains
      "calldatacopy(buf_len, cptr, 0x80)" &&
    (EVM.print emitCommonUncompressedG1).contains "calldatacopy(buf_len, cptr, 128)" &&
    yulTokens "calldatacopy(buf_len, cptr, 128)" == yulTokens "calldatacopy(buf_len, cptr, 0x80)"

/-- Does a statement begin a 'for' loop? Top level only; gate 22 counts the five Lagrange
    loops, which are all siblings inside one block. -/
def stmtIsFor : Stmt Op → Bool
  | Stmt.forLoop _ _ _ _ => true
  | _ => false

/-- GATE 22 (the slice is a program, not a shape). Structural pattern match on the emitted
    Lagrange: a zero-initialised MF-4 flag, a 28-statement scope containing FIVE for-loops
    and the two-name batch_invert assignment, then the section-boundary guard. This is the
    Lagrange twin of SurfaceFixture's blkPinKats_ok line on finalPairing, and it is what
    makes "real" a computation rather than an adjective: the placeholder is one statement and
    no permutation of a placeholder matches this. -/
def emitLagrangeIsReal_ok : Bool :=
  match emitLagrangeAt poseidonCtx.k poseidonCtx.numInstances
      poseidonCtx.numNegLagranges with
  | Stmt.letDecl ["lagrange_precompile_failed"]
      (some (Expr.lit (Literal.number 0))) :: Stmt.block body :: Stmt.cond _ _ :: [] =>
      body.length == 28 && (body.filter stmtIsFor).length == 5 &&
        (body.any fun s => match s with
          | Stmt.assign ["success", "lagrange_precompile_failed"] (Expr.call "batch_invert" _) =>
              true
          | _ => false)
  | _ => false

/-! ### The P-AST3a gates: quotientLin -/

/-- GATE 24 (the D-P25 tripwire, QuotientLin). The emitted AST prints to the same token
    stream as the TEXT PORT's render of the same partial under the same profile - the
    empty-parameter render, i.e. the template's own body and not the artifact's whole
    quotient region, for the measured reason in the emitQuotientLinAt header and pinned as a
    computation by gate 29. Secondary relation on purpose: see gate 25 for the record. -/
def emitQuotientLin_tokens_ok : Bool :=
  yulTokens ("{" ++ renderQuotientAndLinearization poseidonCtx "" "" ++ "}") ==
    yulTokens (EVM.print (emitQuotientLinAt poseidonCtx.k))

/-- GATE 25 (authoritative, QuotientLin). The emitted AST equals the 'yul%' quotation that
    already existed in VerifierPartials as a fixed snapshot - VerifierPartialKats.
    qalLinearization_ast, gated there against the render by their gate 19 - under stmtsBeq.
    This is the check of record for this slice and the one the brief calls non-negotiable: it
    separates Expr.builtin from Expr.call, it separates the for-loop's three sub-blocks from
    a flat sequence, and it separates the two QUOTIENT_MPTR stores from each other. The
    quotation is an independent elaboration path (a parser, not these constructors), so the
    gate is not self-fulfilling - the same argument P-AST2 made for gates 15 and 17. -/
def emitQuotientLin_beq_ok : Bool :=
  SyntaxEq.stmtsBeq (emitQuotientLinAt poseidonCtx.k) VerifierPartialKats.qalLinearization_ast

/-- GATE 26 (perturbation, QuotientLin; D-P23 falsifiability of gates 24-25). The one
    interpolated plan value, changed by one, turns BOTH relations red. There is only one
    parameter in this slice, so a gate on it is a gate on the whole slice: if k were
    decorative the emitted block could not differ at all, and it differs in the loop bound,
    the loop condition and the printed bytes at once. -/
def emitQuotientLinDetectsPerturbation_ok : Bool :=
  let good := emitQuotientLinAt 6
  yulTokens (EVM.print good) != yulTokens (EVM.print (emitQuotientLinAt 7)) &&
    ! SyntaxEq.stmtsBeq good (emitQuotientLinAt 7) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (emitQuotientLinAt 5)) &&
    ! SyntaxEq.stmtsBeq good (emitQuotientLinAt 5)

/-- GATE 27 (the relation gap, at the QuotientLin slice). Every mstore of the emitted block
    spelled as a USER call named 'mstore' keeps the token stream and breaks stmtsBeq - the
    class P-AST measured on ec_pairing and P-AST2 re-measured on Lagrange and TraceReturn,
    now reproduced on a slice with NO user call in it at all. That makes the blindness
    sharpest here: the whole slice is dialect built-ins, so a converter that reached for
    'ycall' out of habit would be caught by stmtsBeq and by nothing else. The mis-spelling
    goes through mapStmtExprs because both stores sit inside the nested scope, where a
    shallow map would not reach them. -/
def emitQuotientLinDetectsBuiltinVsCall_ok : Bool :=
  let good := emitQuotientLinAt poseidonCtx.k
  let bad := good.map (mapStmtExprs fun
    | Expr.builtin Op.mstore args => Expr.call "mstore" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad

/-- GATE 28 (the slice is a program, not a shape). Structural pattern match on the emitted
    QuotientLin: ONE statement, a scope of NINE statements, containing exactly one for-loop
    and the two QUOTIENT_MPTR stores in the order the template writes them (x_split at the
    base, one_minus_x_n at +32). The placeholder is also one statement, which is exactly why
    this matches on the SHAPE inside it: no permutation of 'mstore(0x2300, 4)' has a scope,
    a loop or two stores. -/
def emitQuotientLinIsReal_ok : Bool :=
  match emitQuotientLinAt poseidonCtx.k with
  | [Stmt.block body] =>
      body.length == 9 && (body.filter stmtIsFor).length == 1 &&
      (match body[7]? with
       | some (Stmt.exprStmt (Expr.builtin Op.mstore
           [Expr.var "QUOTIENT_MPTR", Expr.var "x_split"])) => true
       | _ => false) &&
      (match body[8]? with
       | some (Stmt.exprStmt (Expr.builtin Op.mstore
           [Expr.builtin Op.add [Expr.var "QUOTIENT_MPTR", Expr.lit (Literal.number 32)],
             Expr.var "one_minus_x_n"])) => true
       | _ => false)
  | _ => false

/-- GATE 29 (THE REGION BOUNDARY, pinned as a computation rather than left as a paragraph).
    The scope decision in the emitQuotientLinAt header is a measurement, and this is the
    measurement: the empty-parameter render of QuotientAndLinearization is 1,898 bytes / 42
    lines and occurs EXACTLY ONCE in the tracked artifact; the same call fed poseidonCtx's
    own quotient_numerator includes is 9,406 bytes and occurs ZERO times; the emitted slice
    defines no function, so it is the template body and not the region (the includes are
    what carry the helper definitions); and the emitted slice is the quotation, not the
    region. If a later package widens 'blk .quotientLin' to the whole quotient region it has
    to convert both include renders in the same change and re-number this gate - the gate
    goes red on the boundary being moved, which is the point of writing the boundary down as
    a Bool instead of only as prose. -/
def emitQuotientLinRegionBoundary_ok : IO Bool :=
  VerifierPartialKats.readDump >>= fun sol =>
  let q := renderQuotientAndLinearization poseidonCtx "" ""
  let full := renderQuotientAndLinearization poseidonCtx (renderQuotientHelpers poseidonCtx)
    (renderQuotientNumeratorBlock poseidonCtx)
  let printed := EVM.print (emitQuotientLinAt poseidonCtx.k)
  pure (q.length == 1898 && VerifierPartialKats.lineCount q == 42 &&
    VerifierPartialKats.occ sol q == 1 &&
    full.length == 9406 && VerifierPartialKats.occ sol full == 0 &&
    ! printed.contains "function" &&
    ! printed.contains (renderQuotientHelpers poseidonCtx) &&
    SyntaxEq.stmtsBeq (emitQuotientLinAt poseidonCtx.k)
      VerifierPartialKats.qalLinearization_ast)

/-! ### The P-AST3b gates: vkLoading -/

/-- GATE 30 (the D-P25 tripwire, VkLoading). The emitted AST prints to the same token
    stream as the TEXT PORT's render of the same partial under the same profile. Secondary
    relation on purpose - gate 31 is the record, and gate 34 shows what this one cannot see.
    -/
def emitVkLoading_tokens_ok : Bool :=
  yulTokens ("{" ++ renderVkLoading poseidonCtx ++ "}") ==
    yulTokens (EVM.print emitVkLoadingDeployed)

/-- GATE 31 (authoritative, VkLoading). The emitted AST equals the 'yul%' quotation of the
    deployed slice - VerifierPartialKats.vkLoading_ast, gated there against the render by
    their gate 90 - under stmtsBeq. This is the check of record: it separates Expr.builtin
    from Expr.call, it separates the thirteen statements of the scope from a flat sequence
    of the same statements, and it separates the six header cross-checks from each other
    (four of them differ only in the slot name, which no length or token-count check can
    see). The quotation is an independent elaboration path, so the gate is not
    self-fulfilling - the same argument P-AST2 and P-AST3a made for gates 15, 17 and 25. -/
def emitVkLoading_beq_ok : Bool :=
  SyntaxEq.stmtsBeq emitVkLoadingDeployed VerifierPartialKats.vkLoading_ast

/-- GATE 32 (authoritative, the untaken arm). The accumulator precheck: the emitted block
    with the flag set equals the deployed quotation APPENDED to the arm quotation, and the
    token stream agrees with the render of the same flipped profile. The deployed artifact
    does not contain the arm, so this is the second reason the arm is not decoration: it is
    gated for content against a quotation and not only for existence against a flag. -/
def emitVkLoadingAcc_ok : Bool :=
  SyntaxEq.stmtsBeq
    (emitVkLoadingArms true poseidonCtx.numInstances poseidonCtx.k
      poseidonCtx.expectedHasAccumulatorWord poseidonCtx.expectedAccOffset
      poseidonCtx.expectedNumAccLimbs poseidonCtx.expectedNumAccLimbBits
      poseidonCtx.proofLen)
    (VerifierPartialKats.vkLoading_ast ++ VerifierPartialKats.vkLoadingAccArm_ast) &&
    yulTokens ("{" ++ renderVkLoading { poseidonCtx with
        expectedHasAccumulator := true } ++ "}") ==
      yulTokens (EVM.print (emitVkLoadingArms true poseidonCtx.numInstances poseidonCtx.k
        poseidonCtx.expectedHasAccumulatorWord poseidonCtx.expectedAccOffset
        poseidonCtx.expectedNumAccLimbs poseidonCtx.expectedNumAccLimbBits
        poseidonCtx.proofLen)) &&
    -- and the arm is FOUR top-level statements where the deployed slice is one, so the
    -- flag reaches the shape of the emitted block and not only its bytes.
    (emitVkLoadingArms true 1 6 0 0 0 0 0x10e0).length == 4 &&
    (emitVkLoadingArms false 1 6 0 0 0 0 0x10e0).length == 1

/-- GATE 33 (perturbation, VkLoading; D-P23 falsifiability of gates 30-32). Each of the
    seven interpolated plan values, changed by one, turns BOTH relations red - the token
    stream and stmtsBeq. There is no seventh conjunct for the arm flag because gate 32
    already shows it changes the top-level shape. A gate that reddened on only some of the
    seven would leave the rest decorative, and the four accumulator words are exactly the
    ones a hard-coding converter would leave inert: this is the falsification of the
    refusal P-AST3a recorded in prose. -/
def emitVkLoadingDetectsPerturbation_ok : Bool :=
  let good := emitVkLoadingDeployed
  let bad (n k w o l b p : Nat) : Block Op :=
    emitVkLoadingArms poseidonCtx.expectedHasAccumulator n k w o l b p
  yulTokens (EVM.print good) != yulTokens (EVM.print (bad 2 6 0 0 0 0 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 2 6 0 0 0 0 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 7 0 0 0 0 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 7 0 0 0 0 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 6 1 0 0 0 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 6 1 0 0 0 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 6 0 1 0 0 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 6 0 1 0 0 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 6 0 0 1 0 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 6 0 0 1 0 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 6 0 0 0 1 0x10e0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 6 0 0 0 1 0x10e0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 6 0 0 0 0 0x1100)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 6 0 0 0 0 0x1100)

/-- GATE 34 (the relation gap, at the VkLoading slice). Every 'and' of the success chain
    spelled as a USER call named 'and', and the extcodecopy spelled as a USER call named
    'extcodecopy', keeps the token stream and breaks stmtsBeq - the class P-AST measured on
    ec_pairing and P-AST2, P-AST3a re-measured on their own slices, now reproduced on the
    fourth. The 'and' rewrite is the sharpest form of the blindness here: SEVEN statements
    have it as their outermost expression, so a converter that reached for 'ycall' would
    mis-spell seven sites and no token gate would notice. -/
def emitVkLoadingDetectsBuiltinVsCall_ok : Bool :=
  let good := emitVkLoadingDeployed
  let bad := good.map (mapStmtExprs fun
    | Expr.builtin Op.and args => Expr.call "and" args
    | Expr.builtin Op.extcodecopy args => Expr.call "extcodecopy" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad &&
    -- and the rewrite really fired: NINE of the thirteen statements inside the scope
    -- changed their outer constructor, so this is not a gate that passes because nothing
    -- was rewritten. The nine live inside the scope and not at the top level, which is why
    -- the match is nested - a shallow filter counts zero and would make this a lie.
    (match bad with
     | [Stmt.block body] =>
         (body.filter fun s => match s with
           | Stmt.assign ["success"] (Expr.call "and" _) => true
           | _ => false).length == 9
     | _ => false)

/-- GATE 35 (the slice is a program, not a shape). Structural pattern match on the emitted
    VkLoading: ONE top-level statement, a scope of THIRTEEN, with no loop, the extcodecopy
    at index 1, nine success-fold assignments whose outermost call is the 'and' built-in,
    and exactly three 'if .. { fail(..) }' guards. The placeholder is one statement too -
    'mstore(0x2000, 1)' - which is exactly why this matches on the shape INSIDE the scope:
    no permutation of a single flat mstore has thirteen statements, three user-call guards
    or an extcodecopy. -/
def emitVkLoadingIsReal_ok : Bool :=
  match emitVkLoadingDeployed with
  | [Stmt.block body] =>
      body.length == 13 && (body.filter stmtIsFor).length == 0 &&
      (match body[1]? with
       | some (Stmt.exprStmt (Expr.builtin Op.extcodecopy
           [Expr.var "vk", Expr.var "VK_MPTR", Expr.lit (Literal.number 1),
            Expr.var "EXPECTED_VK_PAYLOAD_LENGTH"])) => true
       | _ => false) &&
      (body.filter fun s => match s with
        | Stmt.assign ["success"] (Expr.builtin Op.and _) => true
        | _ => false).length == 9 &&
      (body.filter fun s => match s with
        | Stmt.cond _ [Stmt.exprStmt (Expr.call "fail" _)] => true
        | _ => false).length == 3
  | _ => false

/-- GATE 36 (THE DERIVATION REACHES THE EMITTED BYTES - the anti-hard-coding gate). A plan
    view built through Inv.lean's planViewWithAccumulator from a REAL accumulator encoding
    carries 1 / 2 / 7 / 56, and those four numbers appear in the AST this emitter returns
    for it - where the deployed artifact carries four zeros. Three things are asserted: the
    derived words are in the emitted text, the emitted block is NOT the deployed quotation
    (a hard-coded zero would be indistinguishable from the artifact and would pass gate 31
    while lying for every accumulator plan), and the TEXT PORT agrees token-for-token at the
    same four values, so the emitter and the port move together when the configuration
    moves. This is the gate that makes "derived from cfg.accumulator, not hard-coded" a
    computation instead of a promise. -/
def emitVkLoadingAccWordsDerived_ok : Bool :=
  let pv := Midfall.Lowering.planViewWithAccumulator
    (vk := Midfall.Lowering.witnessVkPayload)
    (vkMptr := Midfall.Generator.LayoutMemoryKats.referenceLayout.vkMptr)
    (memory := Midfall.Generator.LayoutMemoryKats.referenceLayout)
    (proofLayout := poseidonProofLayout)
    (numInstances := poseidonCtx.numInstances) (k := poseidonCtx.k)
    (numNegLagranges := poseidonCtx.numNegLagranges)
    (acc := some (Midfall.Generator.AccumulatorEncoding.new 2 7 56))
    (facts := Midfall.Lowering.emptyParserFacts)
    (meta_ := Midfall.Generator.constraintSystemMetaDefault) (dat := Midfall.Lowering.witnessPlanData)
  pv.expectedHasAccumulatorWord == 1 && pv.expectedAccOffset == 2 &&
    pv.expectedNumAccLimbs == 7 && pv.expectedNumAccLimbBits == 56 &&
    (EVM.print (emitVkLoading pv)).contains "eq(mload(HAS_ACCUMULATOR_MPTR), 1)" &&
    (EVM.print (emitVkLoading pv)).contains "eq(mload(ACC_OFFSET_MPTR), 2)" &&
    (EVM.print (emitVkLoading pv)).contains "eq(mload(NUM_ACC_LIMBS_MPTR), 7)" &&
    (EVM.print (emitVkLoading pv)).contains "eq(mload(NUM_ACC_LIMB_BITS_MPTR), 56)" &&
    ! SyntaxEq.stmtsBeq (emitVkLoading pv) VerifierPartialKats.vkLoading_ast &&
    yulTokens ("{" ++ renderVkLoading { poseidonCtx with
        expectedHasAccumulator := true, expectedHasAccumulatorWord := 1,
        expectedAccOffset := 2, expectedNumAccLimbs := 7,
        expectedNumAccLimbBits := 56 } ++ "}") ==
      yulTokens (EVM.print (emitVkLoading pv)) &&
    -- and the deployed plan view - the none arm - emits the artifact's four zeros because
    -- the derivation says so, not because a call site typed them in.
    (EVM.print (emitVkLoading Midfall.Lowering.witnessPlanView)).contains
      "eq(mload(ACC_OFFSET_MPTR), 0)"

/-! ### The P-AST4 gates: the four transcript helpers and transcriptParser -/

/-- The four transcript helpers, quoted from the same AssemblyHelpers region the text port
    renders (D:673-749), comments stripped because the AST carries none. Each is an
    independent elaboration of the artifact's own bytes through the vendored 'yul%' parser,
    which is what makes gate 42 a check and not a tautology.

    ONE QUOTATION NOTE, earned in this package and worth the paragraph: the PARSER's loop
    variable is named 'end', which is a Lean keyword, and the vendored elaborator parses
    identifiers with Lean's 'ident' atom (Syntax.lean:52-80), so a quotation writing
    'let end :=' does not elaborate at all - the first attempt at this snapshot failed with
    "unexpected token 'end'; expected identifier" at six sites. Lean's own identifier escape,
    the guillemet form \u00abend\u00bb, parses as the identifier 'end' and prints back as 'end', so
    the snapshot needed no DSL change and no renaming of the program. Recorded because the
    escape is invisible in the printed output and a later package will hit it again. -/
def transcriptInit_snapshot : Block Op := yul% {
  function transcript_init() -> buf_len {
    buf_len := TRANSCRIPT_MPTR
  }
}

def commonWord_snapshot : Block Op := yul% {
  function common_word(buf_len, word) -> ret {
    mstore(buf_len, word)
    ret := add(buf_len, 32)
  }
}

def commonUncompressedG1_snapshot : Block Op := yul% {
  function common_uncompressed_g1(buf_len, cptr) -> ret {
    let x_hi_word := calldataload(cptr)
    let x_lo := calldataload(add(cptr, 0x20))
    let y_hi_word := calldataload(add(cptr, 0x40))
    let y_lo := calldataload(add(cptr, 0x60))
    if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
    if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
    let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)
    let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)
    if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
        fail(ERR_BAD_POINT_ENCODING)
    }
    if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
        fail(ERR_BAD_POINT_ENCODING)
    }
    calldatacopy(buf_len, cptr, 0x80)
    ret := add(buf_len, 0x80)
  }
}

def squeezeTo_snapshot : Block Op := yul% {
  function squeeze_to(buf_len, mptr) -> ret {
    let h0 := keccak256(TRANSCRIPT_MPTR, sub(buf_len, TRANSCRIPT_MPTR))
    mstore(TRANSCRIPT_MPTR, h0)
    let r := FR_MODULUS
    mstore(mptr, mod(h0, r))
    ret := add(TRANSCRIPT_MPTR, 32)
  }
}

/-- GATE 37 (the D-P25 tripwire, the four helpers). Each emitted helper prints to the same
    token stream as the text port's OWN definition, sliced out of the AssemblyHelpers render
    - sliced, not retyped, so the comparison is against the bytes the artifact carries. -/
def emitTranscriptHelpers_tokens_ok : Bool :=
  let ah := renderAssemblyHelpers poseidonCtx
  yulTokens ("{" ++ renderFunction ah "transcript_init" ++ "}") ==
    yulTokens (EVM.print emitTranscriptInit) &&
    yulTokens ("{" ++ renderFunction ah "common_word" ++ "}") ==
      yulTokens (EVM.print emitCommonWord) &&
    yulTokens ("{" ++ renderFunction ah "common_uncompressed_g1" ++ "}") ==
      yulTokens (EVM.print emitCommonUncompressedG1) &&
    yulTokens ("{" ++ renderFunction ah "squeeze_to" ++ "}") ==
      yulTokens (EVM.print emitSqueezeTo)

/-- GATE 42 (authoritative, the four helpers). Each equals its quotation under stmtsBeq - the
    relation that separates the fail USER call from the calldatacopy / shr / and / or / lt /
    gt built-ins around it, which no token gate can see. -/
def emitTranscriptHelpers_beq_ok : Bool :=
  SyntaxEq.stmtsBeq emitTranscriptInit transcriptInit_snapshot &&
    SyntaxEq.stmtsBeq emitCommonWord commonWord_snapshot &&
    SyntaxEq.stmtsBeq emitCommonUncompressedG1 commonUncompressedG1_snapshot &&
    SyntaxEq.stmtsBeq emitSqueezeTo squeezeTo_snapshot

/-- GATE 43 (constant in the plan, and the render says so). The four helpers interpolate
    NOTHING, so two things are asserted: the emitted helpers do not move when the plan
    moves, and the RENDER does not move either - which is the difference between a constant
    the template has and a constant a converter typed. The third line is the control: the
    same perturbation of g1_bytes DOES move the parser render, so the second line is not
    true of the whole file and the helper's 0x80 is not a swallowed parameter. The fourth
    line says the same thing from the AST side: a section width moved by one item moves the
    emitted parser even though no helper changed. -/
def emitTranscriptHelpersPlanConstant_ok : Bool :=
  SyntaxEq.stmtsBeq (emitHelpers Midfall.Lowering.witnessPlanView) (emitHelpers
    (withNumTrashcans 3 (withNumLookups 9 Midfall.Lowering.witnessPlanView))) &&
    renderFunction (renderAssemblyHelpers { poseidonCtx with
      templateConstants := { templateConstantsDefault with
        g1Bytes := 96, wordBytes := 64 } }) "common_uncompressed_g1" ==
      renderFunction (renderAssemblyHelpers poseidonCtx) "common_uncompressed_g1" &&
    renderTranscriptProofParser { poseidonCtx with
      templateConstants := { templateConstantsDefault with g1Bytes := 96 } } !=
      renderTranscriptProofParser poseidonCtx &&
    ! SyntaxEq.stmtsBeq emitTranscriptParserDeployed (emitTranscriptParserAt
      poseidonCtx.numInstances poseidonCtx.userPhases poseidonCtx.numLookups
      poseidonCtx.numPermutationZs poseidonCtx.lookupHPlusAcc poseidonCtx.numTrashcans
      poseidonCtx.truncatedChallenges { poseidonProofLayout with
        trash := ProofSection.new 0x764 2 templateConstantsDefault.g1Bytes })

/-- GATE 39 (THE REGION BOUNDARY, pinned as a computation - the transcriptParser twin of
    gate 29 and gate 90). The deployed render is 17,136 bytes / 318 lines and occurs
    EXACTLY ONCE in the tracked artifact with the include boundary on both sides; the
    emitted AST tokenises to it; the emitted AST is the quotation; and the values the
    quotation pins are RE-READ from the dump's own lines - the six section widths the
    parser interpolates, the phase window, the x3 mask, and the absence of every trace and
    gas-checkpoint byte. Without the last group the snapshot would be the artifact quoted
    back at itself, which is the self-fulfilment D-P30 clause 2 forbids. -/
def emitTranscriptParserRegionBoundary_ok : IO Bool :=
  VerifierPartialKats.readDump >>= fun sol =>
  let r := renderTranscriptProofParser poseidonCtx
  let printed := EVM.print emitTranscriptParserDeployed
  let sect (n : Nat) : String := "for { let end := add(proof_cptr, "
    ++ hexFilter n ++ ") }"
  pure (r.length == 17136 && VerifierPartialKats.lineCount r == 318 &&
    VerifierPartialKats.occ sol r == 1 &&
    VerifierPartialKats.includeBoundary sol r &&
    yulTokens ("{" ++ r ++ "}") == yulTokens printed &&
    SyntaxEq.stmtsBeq emitTranscriptParserDeployed VerifierPartialKats.transcriptParser_ast &&
    sol.contains (sect poseidonProofLayout.lookupMultiplicities.byteLen) &&
    sol.contains (sect poseidonProofLayout.permutationProducts.byteLen) &&
    sol.contains (sect poseidonProofLayout.trash.byteLen) &&
    sol.contains (sect poseidonProofLayout.quotientLimbs.byteLen) &&
    sol.contains (sect poseidonProofLayout.evals.byteLen) &&
    sol.contains (sect poseidonProofLayout.qEvals.byteLen) &&
    sol.contains (sect (poseidonProofLayout.advicePhases.head?.getD
      (ProofSection.new 0 1 1)).byteLen) &&
    sol.contains "mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))" &&
    VerifierPartialKats.occ printed "trace_point" == 0 &&
    VerifierPartialKats.occ printed "trace_u256" == 0 &&
    VerifierPartialKats.occ printed "gas_checkpoint" == 0 &&
    ! printed.contains "function")

/-- GATE 38 (perturbation, transcriptParser; D-P23 falsifiability of gates 36-39, and the
    gate the brief asks for by name). EVERY interpolated plan value, changed, turns BOTH
    relations red: the token stream and stmtsBeq. Six new PlanView fields, seven proofLayout
    section accessors, the instance count and the phase list - and each conjunct pair is the
    answer to a specific accident.

    The four counts and the flag are the sharpest cases, because at the deployed fixture all
    five are non-zero / true: an emitter that ignored them and always emitted the section
    would reproduce the artifact byte for byte and pass gate 39 AND gate 36. Driving a count
    to zero must delete statements, and it does. The seven widths are the second class: each
    appears exactly once, inside one loop bound, so a hard-coded width moves nothing. The
    phase list is the third: it is a LIST, so the gate checks a changed field of the single
    deployed phase AND a SECOND phase - the case no scalar field could express, and the
    reason P-AST4 was told not to flatten it. The last pair kills the inertness
    VerifierPartials' gate 45 records for challenge_offset: at the deployed profile zero
    challenges are squeezed so no RENDER perturbation can see the offset, but a plan with
    one challenge can, and the emitter must move with it. -/
def emitTranscriptParserDetectsPerturbation_ok : Bool :=
  let good := emitTranscriptParserDeployed
  let bad (n : Nat) (ph : List UserPhase) (nl nz lh nt : Nat) (tc : Bool)
      (L : ProofCalldataLayout) : Block Op :=
    emitTranscriptParserAt n ph nl nz lh nt tc L
  let P := poseidonCtx.userPhases
  let p0 := P.head?.getD { adviceBytes := 0, numChallenges := 0, challengeOffset := 0 }
  let L0 := poseidonProofLayout
  let lk0 := L0.lookups.head?.getD { lookup := 0, helpers := ProofSection.new 0x664 1 128, accumulator := ProofSection.new 0x6e4 1 128 }
  let g1 := templateConstantsDefault.g1Bytes
  let w := templateConstantsDefault.wordBytes
  yulTokens (EVM.print good) != yulTokens (EVM.print (bad 2 P 1 3 2 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 2 P 1 3 2 1 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 0 3 2 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 0 3 2 1 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 0 2 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 0 2 1 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 0 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 0 1 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 0 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 0 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 false L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 false L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with lookupMultiplicities := ProofSection.new 0x464 2 g1 })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with lookupMultiplicities := ProofSection.new 0x464 2 g1 }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with permutationProducts := ProofSection.new 0x4e4 2 g1 })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with permutationProducts := ProofSection.new 0x4e4 2 g1 }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with trash := ProofSection.new 0x764 2 g1 })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with trash := ProofSection.new 0x764 2 g1 }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with quotientLimbs := ProofSection.new 0x7e4 3 g1 })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with quotientLimbs := ProofSection.new 0x7e4 3 g1 }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with evals := ProofSection.new 0x9e4 49 w })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with evals := ProofSection.new 0x9e4 49 w }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with qEvals := ProofSection.new 0x1064 4 w })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with qEvals := ProofSection.new 0x1064 4 w }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 P 1 3 2 1 true
      { L0 with lookups := [{ lk0 with helpers := ProofSection.new 0x664 2 g1 }] })) &&
    ! SyntaxEq.stmtsBeq good (bad 1 P 1 3 2 1 true
      { L0 with lookups := [{ lk0 with helpers := ProofSection.new 0x664 2 g1 }] }) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 [{ p0 with
      adviceBytes := 0x420 }] 1 3 2 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 [{ p0 with adviceBytes := 0x420 }] 1 3 2 1 true L0) &&
    yulTokens (EVM.print good) != yulTokens (EVM.print (bad 1 (P ++ [{ adviceBytes := 0x80, numChallenges := 1, challengeOffset := 0 }]) 1 3 2 1 true L0)) &&
    ! SyntaxEq.stmtsBeq good (bad 1 (P ++ [{ adviceBytes := 0x80, numChallenges := 1, challengeOffset := 0 }]) 1 3 2 1 true L0) &&
    yulTokens (EVM.print (bad 1 [{ adviceBytes := 0x400, numChallenges := 1, challengeOffset := 0 }] 1 3 2 1 true L0)) != yulTokens (EVM.print (bad 1 [{ adviceBytes := 0x400, numChallenges := 1, challengeOffset := 4 }] 1 3 2 1 true L0)) &&
    -- and the same eighteen through the PlanView fields, so the dispatch cannot read a
    -- deployed constant and stay green.
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser (withNumLookups 1 Midfall.Lowering.witnessPlanView)) &&
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser (withNumPermutationZs 1 Midfall.Lowering.witnessPlanView)) &&
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser { Midfall.Lowering.witnessPlanView with lookupHPlusAcc := 1 }) &&
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser (withNumTrashcans 1 Midfall.Lowering.witnessPlanView)) &&
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser { Midfall.Lowering.witnessPlanView with
                              truncatedChallenges := true }) &&
    ! SyntaxEq.stmtsBeq (emitTranscriptParser Midfall.Lowering.witnessPlanView)
      (emitTranscriptParser { Midfall.Lowering.witnessPlanView with userPhases :=
                              [{ adviceBytes := 0x400, numChallenges := 0,
                                 challengeOffset := 0 }] })

/-- GATE 40 (the relation gap, at the parser slice). Every calldatacopy spelled as a USER
    call named 'calldatacopy' keeps the token stream and breaks stmtsBeq - the class P-AST
    measured on ec_pairing and P-AST2, P-AST3a and P-AST3b re-measured on their own slices,
    now reproduced on the sixth. Nine sites, and only THREE of them are top-level: the other
    six sit inside for-loop bodies and the lookup accumulator tail, so a shallow rewrite
    would fire three times and the gate would pass for the wrong reason. The counts below
    are the proof that all nine fired on both sides.

    The reverse mis-spelling - common_word as a BUILT-in - is not expressible: the dialect
    has no Op named common_word, so there is no token-preserving way to write it. That is a
    limit of the test and not of the emitter, and it is stated because the parser's five
    common_word calls are exactly the sites a converter would most plausibly get wrong.
    They are pinned for constructor choice by gate 39's stmtsBeq against the quotation
    instead: the quotation parses 'common_word(..)' as a user call because that is what the
    artifact's text says, and an emitter that spelled it as anything else fails there. -/
def emitTranscriptParserDetectsBuiltinVsCall_ok : Bool :=
  let good := emitTranscriptParserDeployed
  let bad := good.map (mapStmtExprs fun
    | Expr.builtin Op.calldatacopy args => Expr.call "calldatacopy" args
    | e => e)
  yulTokens (EVM.print good) == yulTokens (EVM.print bad) &&
    ! SyntaxEq.stmtsBeq good bad &&
    VerifierPartialKats.occ (EVM.print good) "calldatacopy(" == 9 &&
    VerifierPartialKats.occ (EVM.print bad) "calldatacopy(" == 9 &&
    (good.filter fun s => match s with
      | Stmt.exprStmt (Expr.builtin Op.calldatacopy _) => true
      | _ => false).length == 3

/-- GATE 44 (the slice is a program, not a shape). Structural facts about the emitted
    deployed parser, every one measured and not chosen: 44 top-level statements, SEVEN
    top-level for-loops (the phase, multiplicity, perm-Z, lookup-helper, trashcan, quotient
    and q_evals walks) with the eval-spill loop inside a nested scope, ten top-level
    squeeze_to USER calls, three top-level calldatacopies, the cursor-identity guard
    second-to-last and the deferred success guard last. The placeholder is one flat mstore,
    so no permutation of it matches - and the placeholder and the slice differ in length by
    43, which is the only pair in the file where a length check separates them for free.
    That is stated so nobody mistakes the easy case for the pattern. -/
def emitTranscriptParserIsReal_ok : Bool :=
  let b := emitTranscriptParserDeployed
  b.length == 44 && (b.filter stmtIsFor).length == 7 &&
    (b.filter fun s => match s with
      | Stmt.assign ["buf_len"] (Expr.call "squeeze_to" _) => true
      | _ => false).length == 10 &&
    (b.filter fun s => match s with
      | Stmt.exprStmt (Expr.builtin Op.calldatacopy _) => true
      | _ => false).length == 3 &&
    (match b.getLast? with
      | some (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail" _)]) => true
      | _ => false) &&
    (match b[b.length - 2]? with
      | some (Stmt.cond (Expr.builtin Op.iszero
          [Expr.builtin Op.eq [Expr.var "proof_cptr", Expr.var "NUM_INSTANCE_CPTR"]])
          [Stmt.exprStmt (Expr.call "fail" _)]) => true
      | _ => false) &&
    (b.filter fun s => match s with
      | Stmt.block body => (body.filter stmtIsFor).length == 1
      | _ => false).length == 2 &&
    (emitPlaceholder .transcriptParser).length == 1

/-- GATE 41 (THE DERIVATION REACHES THE EMITTED BYTES - the anti-hard-coding gate for the
    six new fields, and the transcriptParser twin of gate 36). A plan view built through
    Inv.lean's planViewWithAccumulator from the deployed profile's own facts emits the
    deployed shape, and each of the six fields, zeroed in the plan view, removes the
    statements it guards - with the TEXT PORT agreeing token-for-token at the same perturbed
    value, so emitter and port move together when the plan moves. The first block also pins
    that the constructor path and the profile-tuple path are the same block, which is what
    makes transcriptParserPoseidonArgs a convenience and not a second source of numbers.

    This is the gate that answers the standing note directly. The deployed values are all
    non-zero, so unlike the four accumulator words a hard-coding converter would have
    reproduced the artifact and passed both relations - and it is also the other direction:
    an emitter that always emitted every section would pass gate 39 too. Only this gate
    distinguishes 'reads the plan' from 'happens to match the dump'. -/
def emitTranscriptParserFactsDerived_ok : Bool :=
  let pv := transcriptParserPoseidonPlan
  let dep := emitTranscriptParser pv
  let printed := EVM.print dep
  (printed.contains "add(proof_cptr, 1024)" &&
    printed.contains "squeeze_to(buf_len, X3_MPTR)" &&
    printed.contains
      "mstore(X3_MPTR, and(mload(X3_MPTR), 340282366920938463463374607431768211455))" &&
    printed.contains "let lookup_m_walk" && printed.contains "let perm_z_walk" &&
    printed.contains "let lookup_helper_walk" && printed.contains "let trashcan_walk") &&
    SyntaxEq.stmtsBeq dep VerifierPartialKats.transcriptParser_ast &&
    SyntaxEq.stmtsBeq dep emitTranscriptParserDeployed &&
    (let z := withNumLookups 0 pv;
      ! SyntaxEq.stmtsBeq (emitTranscriptParser z) VerifierPartialKats.transcriptParser_ast &&
      !(EVM.print (emitTranscriptParser z)).contains "let lookup_m_walk" &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        numLookups := 0 } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z))) &&
    (let z := withNumPermutationZs 0 pv;
      !(EVM.print (emitTranscriptParser z)).contains "let perm_z_walk" &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        numPermutationZs := 0 } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z))) &&
    (let z := { pv with lookupHPlusAcc := 0 };
      !(EVM.print (emitTranscriptParser z)).contains "let lookup_helper_walk" &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        lookupHPlusAcc := 0 } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z))) &&
    (let z := withNumTrashcans 0 pv;
      !(EVM.print (emitTranscriptParser z)).contains "let trashcan_walk" &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        numTrashcans := 0 } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z))) &&
    (let z := { pv with truncatedChallenges := false };
      !(EVM.print (emitTranscriptParser z)).contains "mstore(X3_MPTR" &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        truncatedChallenges := false } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z))) &&
    (let z := { pv with userPhases := [] };
      (emitTranscriptParser z).length == dep.length - 1 &&
      yulTokens ("{" ++ renderTranscriptProofParser { poseidonCtx with
        userPhases := [] } ++ "}") == yulTokens (EVM.print (emitTranscriptParser z)))

#eval Midfall.Lowering.GenAst.emitTranscriptHelpers_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptHelpers_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptHelpersPlanConstant_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptParserRegionBoundary_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptParserDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptParserDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptParserIsReal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTranscriptParserFactsDerived_ok -- expect true

end Midfall.Lowering.GenAst

#eval Midfall.Lowering.GenAst.emitFinalPairing_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFinalPairingAcc_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFail_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitEcPairing_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFinalPairing_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFail_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitDependsOnPlan_ok -- expect true
#eval Midfall.Lowering.GenAst.emitDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.renderFunctionSlices_ok -- expect true
#eval Midfall.Lowering.GenAst.emitEcPairing_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitAccBatch_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitLagrange_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitLagrange_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTraceReturn_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTraceReturn_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitLagrangeDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitLagrangeDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.emitTraceReturnDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.numericSpellingDivergence_ok -- expect true
#eval Midfall.Lowering.GenAst.emitLagrangeIsReal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLin_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLin_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinIsReal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinRegionBoundary_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoading_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoading_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoadingAcc_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoadingDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoadingDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoadingIsReal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitVkLoadingAccWordsDerived_ok -- expect true
