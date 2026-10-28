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
-- concatenation - so there is no DSL-change request in this package.
--
-- WHAT IS EMITTED, and what is a placeholder. Scope is per-deployment first (D-P24) and
-- the instruction for this package is ONE partial completely, so the real emission is
-- FinalPairing plus the two AssemblyHelpers definitions it calls (fail, ec_pairing). The
-- other six partials return emitPlaceholder, the same one-statement dummies the fixture
-- carried before this package; emittedPartials names the difference and
-- emitPlaceholderIsTotal_ok pins that the six are placeholders and finalPairing is not. A
-- spec theorem whose partial is not in emittedPartials is pinned to a placeholder: the pin
-- turns it into a claim about ONE program instead of about every program, which is what
-- removes the false-as-stated quantifier, and its registered hole becomes "the emitter
-- does not implement this partial yet" rather than "blk is free".
--
-- PRODUCTION PROFILE ONLY. blk takes (Partial, PlanView) and PlanView carries no
-- diagnostics, so the emitter produces the production arm: no gas_checkpoint calls, and
-- for FinalPairing the reverting arm of the trace if rather than the iszero(iszero(..))
-- one. That is not a silent restriction - every *_spec theorem already hypothesises
-- SupportedS, whose production clause is exactly o.diagnostics.trace = false and
-- o.diagnostics.gasCheckpoints = false. The pin and the theorem's own hypotheses describe
-- the same profile.
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

/-! ### The emitter, total over Partial -/

/-- The partials this file emits for real. Everything else is a placeholder. -/
def emittedPartials : List Partial := [.finalPairing]

/-- Is this partial emitted for real, or is it a placeholder? Decidable, so that "one
    partial completely" is a computation in the tree and not a paragraph in a plan. -/
def partialIsEmitted (q : Partial) : Bool := emittedPartials.contains q

/-- The placeholder for a partial the emitter does not implement yet: one statement, with a
    distinct literal per partial so two slices are never interchangeable. These are the
    blocks the fixture carried before P-AST; they moved here so the emitter is the ONLY
    source of blk in the tree, which is what the pin needs in order to mean anything. P-13
    owes the real AST for the six. -/
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
  | .finalPairing => emitFinalPairing pv
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
      (emitFinalPairingArms false 0x1020)

/-- GATE 8 (what is real and what is a placeholder, as a computation). finalPairing is
    emitted for real; the other six are placeholders; and the placeholder of finalPairing is
    NOT what the emitter returns for it, so the pin cannot be satisfied by a dummy for the
    one partial that has a real body. -/
def emitPlaceholderIsTotal_ok : Bool :=
  emittedPartials.length == 1 && emittedPartials.contains .finalPairing &&
    (Midfall.Lowering.partials.all fun q => partialIsEmitted q == (q == .finalPairing)) &&
    (Midfall.Lowering.partials.all fun q =>
      q == .finalPairing || (emitPlaceholder q).length == 1) &&
    ! SyntaxEq.stmtsBeq (emitPlaceholder .finalPairing)
      (emitFinalPairingArms false 0x1000)

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
