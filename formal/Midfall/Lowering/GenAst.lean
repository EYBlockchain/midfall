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
-- more under D-P30 and P-AST3a (docs/plans/P-AST3a-quotientLin.md) a fourth, so the real
-- emission is now Lagrange, QuotientLin, FinalPairing and TraceReturn; THREE partials still
-- return emitPlaceholder - vkLoading, transcriptParser and pcs - and emittedPartials names
-- the difference as data while
-- emitPlaceholderIsTotal_ok pins it as a computation: four emitted, three placeholders, and
-- no placeholder equal to the real slice it stands for. A
-- spec theorem whose partial is not in emittedPartials is pinned to a placeholder: the pin
-- turns it into a claim about ONE program instead of about every program, which is what
-- removes the false-as-stated quantifier, and its registered hole becomes "the emitter
-- does not implement this partial yet" rather than "blk is free".
--
-- D-P30: THE TEXT PORT IS A REFERENCE, NOT THE DELIVERABLE. Every function in this file
-- builds Block/Stmt/Expr EVM.Op from the vendored package; no raw string expression is
-- emitted anywhere, and the renderX functions of VerifierPartials.lean are kept only as the
-- independent second source each gate compares against. PLAN section 8's equation
-- render g o = (lower g o).map print holds BY CONSTRUCTION for the four slices here, and
-- the checks that say so are the stmtsBeq gates, not the token gates: P-AST measured that
-- spelling every mcopy as a USER call leaves all four token gates green and reddens only
-- stmtsBeq, and P-AST2 and P-AST3a each re-reproduced the blindness on their own slice, so
-- emitLagrange_beq_ok, emitTraceReturn_beq_ok, emitQuotientLin_beq_ok and the three
-- emit*_DetectsBuiltinVsCall_ok gates are the records and yulTokens is the tripwire.
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
-- expectedHasAccumulator into 53 template lines, and PlanView carries NONE of those (no
-- trace flag, no phase list, no trashcan count), so the trace arm is not expressible in
-- this emitter's signature at all - see the note on emitTraceReturnBlock.
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
-- BlkIsEmitter at realSurface, whose main block is literally this file's emitMain.
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

/-- The two AssemblyHelpers definitions FinalPairing needs, in template order. This is what
    the pin puts in the 'helpers' slot of main_concat, and it is why the pin has a second
    conjunct at all: mainScope hoists S.L.main, so a Surface whose blk is the emitted slice
    but whose main carries no fail / ec_pairing definitions emits a program in which the
    emitted slice cannot run. -/
def emitHelpers (pv : PlanView) : Block Op := emitFail ++ emitEcPairingAt pv

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

/-! ### The emitter, total over Partial -/

/-- The partials this file emits for real. Everything else is a placeholder: after P-AST3a
    those are vkLoading, transcriptParser and pcs - the three named by placeholderPartials
    below - and each of the three is blocked for a DIFFERENT measured reason, not the same
    reason: pcs needs Kzg.computations converted from text first (P-AST2's finding: the
    deployed blocks are read back out of the .sol dump), transcriptParser needs four
    AssemblyHelpers definitions the emitter does not have (transcript_init, common_word,
    common_uncompressed_g1, squeeze_to) plus plan values PlanView does not carry, and vkLoading
    needs four accumulator words PlanView does not carry. See the required finding in the
    P-AST3a report; none of the three is blocked on this template. -/
def emittedPartials : List Partial :=
  [.lagrange, .quotientLin, .finalPairing, .traceReturn]

/-- The three partials still emitted as placeholders, as data rather than as a paragraph:
    derived from emittedPartials, so the two lists cannot disagree. -/
def placeholderPartials : List Partial :=
  Midfall.Lowering.partials.filter (fun q => !emittedPartials.contains q)

/-- Is this partial emitted for real, or is it a placeholder? Decidable, so that "one
    partial completely" is a computation in the tree and not a paragraph in a plan. -/
def partialIsEmitted (q : Partial) : Bool := emittedPartials.contains q

/-- The placeholder for a partial the emitter does not implement yet: one statement, with a
    distinct literal per partial so two slices are never interchangeable. These are the
    blocks the fixture carried before P-AST; they moved here so the emitter is the ONLY
    source of blk in the tree, which is what the pin needs in order to mean anything. P-13
    owes the real AST for the three in placeholderPartials - and D-P30 clause 4 is the rule
    that they end up unreachable, not merely well-documented. -/
def emitPlaceholder : Partial → Block Op
  | .vkLoading => [yexpr (yop Op.mstore [ylit 0x2000, ylit 1])]
  | .transcriptParser => [yexpr (yop Op.mstore [ylit 0x2100, ylit 2])]
  | .lagrange => [yexpr (yop Op.mstore [ylit 0x2200, ylit 3])]
  | .quotientLin => [yexpr (yop Op.mstore [ylit 0x2300, ylit 4])]
  | .pcs => [yexpr (yop Op.mstore [ylit 0x2400, ylit 5])]
  | .finalPairing => [yexpr (yop Op.mstore [ylit 0x2500, ylit 6])]
  | .traceReturn => [yexpr (yop Op.ret [ylit 0x1000, ylit 0x20])]

/-- THE GENERATOR FUNCTION the blk pin pins to: the Yul block of one partial under one plan
    view. Total over Partial by construction, so the pin is a plain equation and not a
    conditional that quietly says nothing for six of the seven. -/
def emitPartial (pv : PlanView) (q : Partial) : Block Op :=
  match q with
  | .lagrange => emitLagrange pv
  | .quotientLin => emitQuotientLin pv
  | .finalPairing => emitFinalPairing pv
  | .traceReturn => emitTraceReturn pv
  | q => emitPlaceholder q

/-- The seven slices in include order (Halo2Verifier.sol:217-229), i.e. exactly the tail
    main_concat speaks about. -/
def emitSlices (pv : PlanView) : Block Op :=
  Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++ emitPartial pv q

/-- The whole main block the emitter produces: the helpers, then the seven slices. -/
def emitMain (pv : PlanView) : Block Op := emitHelpers pv ++ emitSlices pv

/-! ### The text-port comparison machinery -/

/-- The rendered text of one 'function NAME(...)' definition inside a render: its header
    line through its closing brace, comments included (yulTokens drops them). Used to slice
    fail and ec_pairing out of the AssemblyHelpers render, which is one string. -/
def renderFunction (render name : String) : String :=
  let ls := render.splitOn "\n"
  let header := "function " ++ name ++ "("
  match (ls.zipIdx.find? fun (l, _i) => (trimWs l).startsWith header) with
  | none => ""
  | some (_l, i) =>
    let rest := ls.drop i
    let close := (rest.zipIdx.find? fun (l, _j) => trimWs l == "}").map fun (_l, j) => j + 1
    String.intercalate "\n" (rest.take (close.getD rest.length))

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
    -- and TraceReturn is CONSTANT in the plan, which is the template's own shape and not a
    -- hole: stated as a computation so a later package that parameterises it has to notice
    -- it changed this gate.
    (Midfall.Lowering.partials.all fun _q =>
      SyntaxEq.stmtsBeq (emitTraceReturn Midfall.Lowering.witnessPlanView)
        emitTraceReturnBlock)

/-- GATE 8 (what is real and what is a placeholder, as a computation). FOUR partials are
    emitted for real after P-AST3a - lagrange, quotientLin, finalPairing, traceReturn - and
    the remaining THREE are one-statement placeholders named by placeholderPartials. The
    last conjuncts are the R-62 clause: for each real slice, the placeholder that used to
    stand for it is NOT what the emitter returns, so the pin cannot be satisfied by a dummy
    for a partial that has a real body. Before P-AST2 the lagrange and traceReturn conjuncts
    were unfalsifiable in exactly this way, and before this package the quotientLin one was -
    the placeholder WAS the emitter's answer - which is what "emitPlaceholder must shrink
    toward unreachable" (D-P30 clause 4) is measuring. The quotientLin conjunct earns its
    place in a way the others do not: placeholder and real slice are BOTH one statement, so
    the two tail conjuncts below are the only way this gate can tell them apart - a length
    check cannot, and it says so rather than pretending otherwise. -/
def emitPlaceholderIsTotal_ok : Bool :=
  emittedPartials.length == 4 && emittedPartials.contains .finalPairing &&
    emittedPartials.contains .lagrange && emittedPartials.contains .traceReturn &&
    emittedPartials.contains .quotientLin &&
    placeholderPartials.length == 3 &&
    placeholderPartials == [.vkLoading, .transcriptParser, .pcs] &&
    (Midfall.Lowering.partials.all fun q =>
      partialIsEmitted q ==
        (q == .finalPairing || q == .lagrange || q == .traceReturn || q == .quotientLin)) &&
    (Midfall.Lowering.partials.all fun q =>
      partialIsEmitted q || (emitPlaceholder q).length == 1) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .finalPairing)
      (emitFinalPairingArms false 0x1000) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .lagrange) (emitLagrangeAt 6 1 9) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .traceReturn) emitTraceReturnBlock &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .quotientLin) (emitQuotientLinAt 6) &&
    -- the shape fact that makes the previous line load-bearing: same top-level length, so
    -- nothing but stmtsBeq separates the dummy from the real scope.
    (emitPlaceholder .quotientLin).length == 1 && (emitQuotientLinAt 6).length == 1 &&
    (match emitQuotientLinAt 6 with
     | [Stmt.block body] => body.length == 9
     | _ => false)

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

/-- GATE 11 (the slicer is not vacuous). renderFunction finds both helpers and finds them as
    function definitions, so gates 3 and 4 compare a real slice and not the empty string
    against the empty string; and it returns "" for a name the render does not define, so a
    typo in a gate name is a red gate rather than a silent agreement. -/
def renderFunctionSlices_ok : Bool :=
  (trimWs (renderFunction (renderAssemblyHelpers poseidonCtx) "fail")).startsWith
    "function fail(sel)" &&
    (trimWs (renderFunction (renderAssemblyHelpers poseidonCtx) "ec_pairing")).startsWith
      "function ec_pairing(success, lhs_mptr, rhs_mptr)" &&
    (renderFunction (renderAssemblyHelpers poseidonCtx) "no_such_helper") == ""

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
    yulTokens "add(QUOTIENT_MPTR, 32)" == yulTokens "add(QUOTIENT_MPTR, 0x20)"

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

/-- GATE 23 (the dispatch, not just the list). emittedPartials CLAIMS four partials are
    real; gates 14-28 check the emitters themselves. Without this gate the file could grow a
    real emitLagrange, list it in emittedPartials, and still have emitPartial fall through to
    emitPlaceholder - the pin would then pin a placeholder while every other gate stayed
    green. That is the R-62 class one level up, so it is checked as a computation: the
    dispatch reaches the real body for all four, and the placeholder is NOT what the
    dispatcher returns for any of them. -/
def emitPartialRoutesRealSlices_ok : Bool :=
  SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .lagrange)
    (emitLagrange Midfall.Lowering.witnessPlanView) &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .traceReturn)
    emitTraceReturnBlock &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLin Midfall.Lowering.witnessPlanView) &&
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .finalPairing)
      (emitFinalPairing Midfall.Lowering.witnessPlanView) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .lagrange)
      (emitPlaceholder .lagrange) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .traceReturn)
      (emitPlaceholder .traceReturn) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitPlaceholder .quotientLin) &&
    -- and the dispatch reads pv.k rather than a hard-coded 6: the fixture plan's k is 2,
    -- so routing to the deployed constant would still satisfy the line above and this one
    -- would catch it.
    SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLinAt Midfall.Lowering.witnessPlanView.k) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .quotientLin)
      (emitQuotientLinAt 6) &&
    ! SyntaxEq.stmtsBeq (emitPartial Midfall.Lowering.witnessPlanView .finalPairing)
      (emitPlaceholder .finalPairing)

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

end Midfall.Lowering.GenAst

#eval Midfall.Lowering.GenAst.emitFinalPairing_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFinalPairingAcc_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFail_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitEcPairing_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFinalPairing_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitFail_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitDependsOnPlan_ok -- expect true
#eval Midfall.Lowering.GenAst.emitPlaceholderIsTotal_ok -- expect true
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
#eval Midfall.Lowering.GenAst.emitPartialRoutesRealSlices_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLin_tokens_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLin_beq_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinDetectsPerturbation_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinDetectsBuiltinVsCall_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinIsReal_ok -- expect true
#eval Midfall.Lowering.GenAst.emitQuotientLinRegionBoundary_ok -- expect true
