-- |
-- Midfall.Lowering.GenAstQvm
--
-- OBJ.15 (PLAN-V3 V3 row 39): the QVM INTERPRETER TEMPLATE as a structured AST.
--
-- WHAT THIS FILE IS FOR. 'renderQuotientNumeratorBlock' is 6,384 tokens at the deployment, of
-- which 5,431 are the six GENERATED LINE FAMILIES the ported Rust codegen writes and 953 are the
-- interpreter template - the register initialisation, the dispatch loop, the thirty-one opcode
-- arms, the three native callbacks and the epilogue. OBJ.2 landed the region by PARSING all 6,384
-- because a structured emitter was estimated at six times its box; this file is the structured
-- emitter for the template, split the way the card says it has to be: (a) prologue and registers,
-- (b) opcode switch arms, (c) native callbacks, (d) epilogue and selector tail. The generated
-- families are spliced by 'parseLines' and NOT re-implemented - the card's fence excludes AST
-- twins of the block producers, and a second implementation of the generator is the thing the
-- whole package exists to avoid.
--
-- WHY IT MATTERS AND IS NOT HYGIENE. QPROBE measured that the quotient VM does not execute at any
-- fuel by unrolling: the interpreter reads its opcode from SYMBOLIC memory - 'q_op := byte(0,
-- mload(q_pc))' - so 'selectSwitch' cannot reduce, and the stuck leaf was 81,768 chars with ZERO
-- 'False' leaves: stuck on symbolic data, not out of fuel. That fetch is 'qvmLoopPre' here. T3.10
-- 'QInterpRefines' has to reason about it as a tree, which is what makes it worth emitting rather
-- than parsing.
--
-- THE FINGERPRINT DOES NOT MOVE, AND THAT IS A GATE. Nothing here is wired into 'emitPartialM':
-- the deployed program still reaches its numerator through 'GenAst.emitQuotientNumerator', the
-- OBJ.2 parse. 'Midfall.Instances.M2BatchKats.numA_agreesWithParse_ok' is the gate that says the
-- new tree IS the parsed tree at the deployment and at the all-arms context, so rewiring is a free
-- choice for T3.10 and not an artifact change. It was made that way deliberately: the emitter was
-- DERIVED from the parse of the render at a context where every interpolated value is a distinct
-- sentinel number, so each literal here is the field the render reads and not a transcribed fixture
-- value. That is also how two real defects were caught: 'numA_programFieldsReach_ok' reddened on a
-- 'guards.constMax' site that the deployment cannot see, and 'numA_flagsSelect_ok' reddened on
-- eighteen memory-token cases that had been emitted ungated.
--
-- OUT OF SCOPE, NAMED: the legacy/direct arm ('c.quotientProgram = none'), the external and probe
-- arms, and the trace arms - all excluded by the card's fence. The 'none' arm falls back to the
-- parse so this function is total; 'numA_agreesWithParseNoProgram_ok' pins that rather than hiding
-- it behind a comment.
--
-- NO PROOFS LIVE HERE. Every claim is a 'Bool' gate in 'Midfall/Instances/M2BatchKats.lean'
-- (D-P71: 'native_decide' stays in Instances/, and nothing in the headline cone may rest on a
-- concrete model).
--

import Midfall.Lowering.GenAst
import Midfall.Lowering.YulParse
import Midfall.Generator.VerifierPartials

set_option autoImplicit false

namespace Midfall.Lowering.GenAst
open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering.YulParse

/-- THE SIX GENERATED LINE FAMILIES ARE PARSED, NOT RE-IMPLEMENTED. The card's scope fence says
    "does NOT need: AST twins of the block producers", and it is right to: the families are the
    output of the ported Rust codegen, so an AST twin would be a SECOND implementation of the
    generator - the thing this package exists to avoid. What the card asks for is the interpreter
    TEMPLATE as a tree, with the families spliced back in by 'parseLines'. A flat family is a list
    of lines; a nested family is a list of blocks of lines, and the render emits every block's
    lines back to back, so flattening is the splice the text port itself performs. -/
def qGenFlat (ls : List String) : Block Op :=
  match YulParse.parseLines ls with
  | some b => b
  | none => []

/-- A nested generated family. 'quotientNativeIdentityComputations' is the one family whose BLOCK
    PARTITION is rendered (one 'case index0' per block, VerifierPartials.lean:274-280), so it does
    NOT go through here - see 'qvmNativeArms'. -/
def qGenNested (bs : List (List String)) : Block Op := qGenFlat (bs.flatten)

/-! ### (a) Prologue and registers -/

/-- The interpreter prologue: the batching challenge, the two table pointers, the zeroed
    accumulator, the optional trace-id seed, the selector-bucket zeroing loop, the optional
    y-power table, the DIRECT INLINE PREFIX family, and the five VM registers. Every number is a
    'QuotientProgram' field or a 'simpleSelectorCols' length, so nothing here is the fixture's
    value: 'numA_programFieldsReach_ok' perturbs each one and requires the tree to move. -/
def qvmPrologue (c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "y" (yop EVM.Op.mload [(yvar "Y_MPTR")])), (ylet "q_const_mptr" (ylit program.constMptr)), (ylet "q_program_mptr" (ylit program.programMptr)), (yexpr (yop EVM.Op.mstore [(ylit program.evalNumerMptr), (ylit 0)]))] ++
      (if c.simpleSelectorCols.length > 0 then
          [(yfor [(ylet "q_sel_zero_off" (ylit 0))] (yop EVM.Op.lt [(yvar "q_sel_zero_off"), (ylit (c.simpleSelectorCols.length * 0x20))]) [(yset "q_sel_zero_off" (yop EVM.Op.add [(yvar "q_sel_zero_off"), (ylit 32)]))] [(yexpr (yop EVM.Op.mstore [(yop EVM.Op.add [(yvar "SELECTOR_ACC_MPTR"), (yvar "q_sel_zero_off")]), (ylit 0)]))])] ++ (if program.selectorMaxPower > 0 then [(yblock [(ylet "q_y_power" (ylit 1)), (yfor [(ylet "q_y_power_i" (ylit 1))] (yop EVM.Op.lt [(yvar "q_y_power_i"), (ylit (program.selectorMaxPower + 1))]) [(yset "q_y_power_i" (yop EVM.Op.add [(yvar "q_y_power_i"), (ylit 1)]))] [(yset "q_y_power" (yop EVM.Op.mulmod [(yvar "q_y_power"), (yvar "y"), (yvar "r")])), (yexpr (yop EVM.Op.mstore [(yop EVM.Op.add [(ylit program.selectorPowerMptr), (yop EVM.Op.shl [(ylit 5), (yvar "q_y_power_i")])]), (yvar "q_y_power")]))])])] else [])
          else []) ++
      qGenNested c.quotientInlineComputations ++
      [(ylet "q_pc" (yvar "q_program_mptr")), (ylet "q_end" (yop EVM.Op.add [(yvar "q_program_mptr"), (ylit program.len)])), (ylet "q_sp" (ylit program.stackMptr)), (ylet "q_top" (ylit 0)), (ylet "q_has_top" (ylit 0))]

/-! ### (b) Opcode switch arms -/

/-! ### (b0) THE ARM BODIES, LIFTED TO TOP-LEVEL NAMES (QEMIT4)

Every one of the thirty-one switch arms used to be spelled INLINE inside the 'if' chain of
'qvmOpcodeArms' / 'qvmNativeArms' / 'qvmFoldArms'. That made the arm bodies unreachable from any
lemma: 'simp only [qvmOpcodeArms]' with all thirty-one 'opUsage' flags pinned dies at 'whnf'
(200000 heartbeats, ~11 s) because unfolding the definition normalises all thirty-one bodies
before 'List.lookup' or 'List.find?' can act - so an arm lemma could not name the block it was
about, and ROW.Q.3's eight 'QArmFamily' leaves could not be stated at the emitter's own arms.

LIFTING each body to a top-level 'def' makes the body ATOMIC to a lemma that rewrites at the
arm-list name: the list structure reduces and the thirty-one bodies do not. This is the QEMIT3
precedent (GenAstQvmFamilies.lean's 'qMloadRunGoA', 'qEmitLookupRegionA', ...), applied to the
interpreter template.

THE LIFT IS A BINDING CHANGE, NOT A VALUE CHANGE, AND THAT IS GATED. Every 'def' below is the
term the chain used to spell, VERBATIM, with the same return type 'Block Op'; each chain below
calls it at the same three arguments it used to read off its own binders. 'numA_isTheParseFixture_ok
'numA_isTheParseAllArms_ok' and 'numA_agreesWithParse_ok' (Instances/M2BatchKats.lean) are the
gates that say the emitted tree did not move, and the object fingerprint with it.

The signature is UNIFORM - context, program, template constants - so a family lemma can apply
any arm of its family to the same arguments; a binder the body does not read is named with a
leading underscore. The family each arm belongs to is the 'QArmFamily' of
'Midfall/Lowering/QuotientInterp.lean' section 6, named in each doc string. -/

/-- Every 'opUsage' flag ON. A lemma that wants the emitter's WHOLE arm list to reduce needs all
    thirty-one 'if' guards decided, and needs them decided GENERICALLY - a hypothesis about a
    program's own flag record, not a fixture's. 'qvmAllFlags' in 'Instances/M2BatchKats.lean' is
    the same record, but 'Instances/' is below the line D-P71 draws for anything a row cites. -/
def opUsageAllOn : Midfall.Generator.QuotientVmOpcodeUsage :=
  { pushConst := true, pushMemLiteral := true, pushMemToken := true,
    pushMemTokenOffset := true, pushMemU16 := true, add := true, mul := true, neg := true,
    pushConstU8 := true, foldMain := true, foldSelector := true, addConstU8 := true,
    mulConstU8 := true, addConst := true, mulConst := true, addMemU16 := true,
    mulMemU16 := true, addMulMemMemConstU8 := true, addMulConstU8MemU16 := true,
    addMulMemMem := true, runAddMulMemMemConstU8 := true, runAddMulConstU8MemU16 := true,
    affineSum := true, nativePermutation := true, nativeLookup := true,
    nativeIdentity := true, lin7 := true, bilin7Row := true, bilin7Pairwise := true,
    modarith7 := true, pow5 := true }

/-- Every 'memUsage' flag ON: the eighteen memory-token cases the two token arms switch over. -/
def memUsageAllOn : Midfall.Generator.QuotientVmMemUsage :=
  { l0 := true, lLast := true, lBlind := true, beta := true, gamma := true, x := true,
    theta := true, trashChallenge := true, instanceEval := true }

/-- ARM 'pushConst' (family 'push'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushConst (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yif (yop EVM.Op.gt [(yvar "qconst"), (ylit program.guards.constMax)]) [(yexpr (ycall "q_program_fail" []))]), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])])), (yset "q_has_top" (ylit 1)), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)]))]

/-- ARM 'pushMemLiteral' (family 'push'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushMemLiteral (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 224), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.byteU32Bytes)])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yvar "q_ptr")])), (yset "q_has_top" (ylit 1))]

/-- ARM 'pushMemToken' (family 'token'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushMemToken (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_token" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])), (ylet "q_ptr" (ylit 0)), (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yvar "L_0_MPTR"))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yvar "L_LAST_MPTR"))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yvar "L_BLIND_MPTR"))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yvar "BETA_MPTR"))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yvar "GAMMA_MPTR"))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yvar "X_MPTR"))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yvar "THETA_MPTR"))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yvar "TRASH_CHALLENGE_MPTR"))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yvar "INSTANCE_EVAL_MPTR"))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yvar "q_ptr")])), (yset "q_has_top" (ylit 1))]

/-- ARM 'pushMemTokenOffset' (family 'token'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushMemTokenOffset (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_token" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_off" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 216), (yvar "q_word")]), (ylit 4294967295)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (ylet "q_ptr" (ylit 0)), (Stmt.switch (yvar "q_token") ((if program.memUsage.l0 then [(Literal.number tcq.mem.l0, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_0_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lLast then [(Literal.number tcq.mem.lLast, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_LAST_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.lBlind then [(Literal.number tcq.mem.lBlind, [(yset "q_ptr" (yop EVM.Op.add [(yvar "L_BLIND_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.beta then [(Literal.number tcq.mem.beta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "BETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.gamma then [(Literal.number tcq.mem.gamma, [(yset "q_ptr" (yop EVM.Op.add [(yvar "GAMMA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.x then [(Literal.number tcq.mem.x, [(yset "q_ptr" (yop EVM.Op.add [(yvar "X_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.theta then [(Literal.number tcq.mem.theta, [(yset "q_ptr" (yop EVM.Op.add [(yvar "THETA_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.trashChallenge then [(Literal.number tcq.mem.trashChallenge, [(yset "q_ptr" (yop EVM.Op.add [(yvar "TRASH_CHALLENGE_MPTR"), (yvar "q_off")]))])] else []) ++ (if program.memUsage.instanceEval then [(Literal.number tcq.mem.instanceEval, [(yset "q_ptr" (yop EVM.Op.add [(yvar "INSTANCE_EVAL_MPTR"), (yvar "q_off")]))])] else [])) (some [(yexpr (ycall "q_program_fail" []))])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yvar "q_ptr")])), (yset "q_has_top" (ylit 1))]

/-- ARM 'pushMemU16' (family 'push'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushMemU16 (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yvar "q_ptr")])), (yset "q_has_top" (ylit 1))]

/-- ARM 'add' (family 'arith'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAdd (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.eq [(yvar "q_sp"), (ylit program.stackMptr)]) [(yexpr (ycall "q_program_fail" []))]), (yset "q_sp" (yop EVM.Op.sub [(yvar "q_sp"), (ylit 32)])), (yset "q_top" (yop EVM.Op.addmod [(yop EVM.Op.mload [(yvar "q_sp")]), (yvar "q_top"), (yvar "r")]))]

/-- ARM 'mul' (family 'arith'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyMul (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.eq [(yvar "q_sp"), (ylit program.stackMptr)]) [(yexpr (ycall "q_program_fail" []))]), (yset "q_sp" (yop EVM.Op.sub [(yvar "q_sp"), (ylit 32)])), (yset "q_top" (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_sp")]), (yvar "q_top"), (yvar "r")]))]

/-- ARM 'neg' (family 'arith'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyNeg (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yset "q_top" (yop EVM.Op.addmod [(ylit 0), (yop EVM.Op.sub [(yvar "r"), (yvar "q_top")]), (yvar "r")]))]

/-- ARM 'pow5' (family 'arith'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPow5 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q2" (yop EVM.Op.mulmod [(yvar "q_top"), (yvar "q_top"), (yvar "r")])), (yset "q_top" (yop EVM.Op.mulmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yvar "q2"), (yvar "q2"), (yvar "r")]), (yvar "r")]))]

/-- ARM 'pushConstU8' (family 'push'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyPushConstU8 (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yset "q_top" (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])])), (yset "q_has_top" (ylit 1)), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)]))]

/-- ARM 'addConstU8' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddConstU8 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]))]

/-- ARM 'mulConstU8' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyMulConstU8 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])), (yset "q_top" (yop EVM.Op.mulmod [(yvar "q_top"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]))]

/-- ARM 'addConst' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddConst (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yif (yop EVM.Op.gt [(yvar "qconst"), (ylit program.guards.constMax)]) [(yexpr (ycall "q_program_fail" []))]), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]))]

/-- ARM 'mulConst' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyMulConst (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "qconst" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yif (yop EVM.Op.gt [(yvar "qconst"), (ylit program.guards.constMax)]) [(yexpr (ycall "q_program_fail" []))]), (yset "q_top" (yop EVM.Op.mulmod [(yvar "q_top"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]))]

/-- ARM 'addMemU16' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddMemU16 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mload [(yvar "q_ptr")]), (yvar "r")]))]

/-- ARM 'mulMemU16' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyMulMemU16 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yset "q_top" (yop EVM.Op.mulmod [(yvar "q_top"), (yop EVM.Op.mload [(yvar "q_ptr")]), (yvar "r")]))]

/-- ARM 'addMulMemMemConstU8' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddMulMemMemConstU8 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_word")]), (ylit 65535)])), (ylet "qconst" (yop EVM.Op.byte [(ylit 4), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_lhs")]), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))]

/-- ARM 'addMulConstU8MemU16' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddMulConstU8MemU16 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 2), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_ptr")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))]

/-- ARM 'addMulMemMem' (family 'fused'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAddMulMemMem (_c : PartialCtx) (_program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.byteU32Bytes)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_lhs")]), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yvar "r")]))]

/-- ARM 'runAddMulMemMemConstU8' (family 'run'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyRunAddMulMemMemConstU8 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_count" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_run_end" (yop EVM.Op.add [(yvar "q_pc"), (yop EVM.Op.mul [(yvar "q_count"), (ylit 5)])])), (yfor [] (yop EVM.Op.lt [(yvar "q_pc"), (yvar "q_run_end")]) [] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_word")]), (ylit 65535)])), (ylet "qconst" (yop EVM.Op.byte [(ylit 4), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_lhs")]), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])]

/-- ARM 'runAddMulConstU8MemU16' (family 'run'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyRunAddMulConstU8MemU16 (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_count" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_run_end" (yop EVM.Op.add [(yvar "q_pc"), (yop EVM.Op.mul [(yvar "q_count"), (ylit 3)])])), (yfor [] (yop EVM.Op.lt [(yvar "q_pc"), (yvar "q_run_end")]) [] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 2), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_ptr")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])]

/-- ARM 'affineSum' (family 'run'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyAffineSum (_c : PartialCtx) (_program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_lin_count" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_product_count" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_lin_end" (yop EVM.Op.add [(yvar "q_pc"), (yop EVM.Op.mul [(yvar "q_lin_count"), (ylit 3)])])), (yfor [] (yop EVM.Op.lt [(yvar "q_pc"), (yvar "q_lin_end")]) [] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_ptr" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 2), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_ptr")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))]), (ylet "q_product_end" (yop EVM.Op.add [(yvar "q_pc"), (yop EVM.Op.mul [(yvar "q_product_count"), (ylit 5)])])), (yfor [] (yop EVM.Op.lt [(yvar "q_pc"), (yvar "q_product_end")]) [] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_word")]), (ylit 65535)])), (ylet "qconst" (yop EVM.Op.byte [(ylit 4), (yvar "q_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (yset "q_top" (yop EVM.Op.addmod [(yvar "q_top"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_lhs")]), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])]

/-- ARM 'lin7' (family 'limb'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyLin7 (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (ylet "q_acc" (ylit 0)), (yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_ptr" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yop EVM.Op.mload [(yvar "q_ptr")]), (yvar "r")]), (yvar "r")]))]), (yset "q_top" (yvar "q_acc")), (yset "q_has_top" (ylit 1))]

/-- ARM 'bilin7Row' (family 'limb'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyBilin7Row (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_lhs_value" (yop EVM.Op.mload [(yvar "q_lhs")])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (ylet "q_acc" (ylit 0)), (yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yvar "q_lhs_value"), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))]), (yset "q_top" (yvar "q_acc")), (yset "q_has_top" (ylit 1))]

/-- ARM 'bilin7Pairwise' (family 'limb'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyBilin7Pairwise (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs_base" (yop EVM.Op.shr [(ylit 240), (yvar "q_word")])), (ylet "q_rhs_base" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.byteU32Bytes)])), (ylet "q_coeff_pc" (yvar "q_pc")), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.limbPairwiseCoeffs)])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (ylet "q_acc" (ylit 0)), (yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_lhs_value" (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_lhs_base"), (yop EVM.Op.shl [(ylit 5), (yvar "q_i")])])])), (yfor [(ylet "q_j" (ylit 0))] (yop EVM.Op.lt [(yvar "q_j"), (ylit tcq.limbCount)]) [(yset "q_j" (yop EVM.Op.add [(yvar "q_j"), (ylit 1)]))] [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_coeff_pc"), (yop EVM.Op.add [(yvar "q_i"), (yvar "q_j")])])])])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yvar "q_lhs_value"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_rhs_base"), (yop EVM.Op.shl [(ylit 5), (yvar "q_j")])])]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])]), (yset "q_top" (yvar "q_acc")), (yset "q_has_top" (ylit 1))]

/-- ARM 'modarith7' (family 'limb'): the arm body 'qvmOpcodeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyModarith7 (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_flags" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])), (yif (yop EVM.Op.gt [(yvar "q_flags"), (ylit 3)]) [(yexpr (ycall "q_program_fail" []))]), (ylet "q_cond_ptr" (ylit 0)), (yif (yop EVM.Op.and [(yvar "q_flags"), (ylit 1)]) [(yset "q_cond_ptr" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)]))]), (ylet "q_acc" (ylit 0)), (yif (yop EVM.Op.and [(yvar "q_flags"), (ylit 2)]) [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)])), (yset "q_acc" (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]))]), (ylet "q_counts_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lin_count" (yop EVM.Op.byte [(ylit 0), (yvar "q_counts_word")])), (ylet "q_row_count" (yop EVM.Op.byte [(ylit 1), (yvar "q_counts_word")])), (ylet "q_pairwise_count" (yop EVM.Op.byte [(ylit 2), (yvar "q_counts_word")])), (ylet "q_mem_count" (yop EVM.Op.byte [(ylit 3), (yvar "q_counts_word")])), (ylet "q_product_count" (yop EVM.Op.byte [(ylit 4), (yvar "q_counts_word")])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (yif (yvar "q_has_top") [(yif (yop EVM.Op.gt [(yvar "q_sp"), (ylit program.guards.stackLast)]) [(yexpr (ycall "q_program_fail" []))]), (yexpr (yop EVM.Op.mstore [(yvar "q_sp"), (yvar "q_top")])), (yset "q_sp" (yop EVM.Op.add [(yvar "q_sp"), (ylit 32)]))]), (yfor [(ylet "q_lin_block" (ylit 0))] (yop EVM.Op.lt [(yvar "q_lin_block"), (yvar "q_lin_count")]) [(yset "q_lin_block" (yop EVM.Op.add [(yvar "q_lin_block"), (ylit 1)]))] [(yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_ptr" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yop EVM.Op.mload [(yvar "q_ptr")]), (yvar "r")]), (yvar "r")]))])]), (yfor [(ylet "q_row_block" (ylit 0))] (yop EVM.Op.lt [(yvar "q_row_block"), (yvar "q_row_count")]) [(yset "q_row_block" (yop EVM.Op.add [(yvar "q_row_block"), (ylit 1)]))] [(ylet "q_lhs" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (ylet "q_lhs_value" (yop EVM.Op.mload [(yvar "q_lhs")])), (yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yvar "q_lhs_value"), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])]), (yfor [(ylet "q_pair_block" (ylit 0))] (yop EVM.Op.lt [(yvar "q_pair_block"), (yvar "q_pairwise_count")]) [(yset "q_pair_block" (yop EVM.Op.add [(yvar "q_pair_block"), (ylit 1)]))] [(ylet "q_pair_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "q_lhs_base" (yop EVM.Op.shr [(ylit 240), (yvar "q_pair_word")])), (ylet "q_rhs_base" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 224), (yvar "q_pair_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.byteU32Bytes)])), (ylet "q_coeff_pc" (yvar "q_pc")), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit tcq.limbPairwiseCoeffs)])), (yfor [(ylet "q_i" (ylit 0))] (yop EVM.Op.lt [(yvar "q_i"), (ylit tcq.limbCount)]) [(yset "q_i" (yop EVM.Op.add [(yvar "q_i"), (ylit 1)]))] [(ylet "q_lhs_value" (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_lhs_base"), (yop EVM.Op.shl [(ylit 5), (yvar "q_i")])])])), (yfor [(ylet "q_j" (ylit 0))] (yop EVM.Op.lt [(yvar "q_j"), (ylit tcq.limbCount)]) [(yset "q_j" (yop EVM.Op.add [(yvar "q_j"), (ylit 1)]))] [(ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_coeff_pc"), (yop EVM.Op.add [(yvar "q_i"), (yvar "q_j")])])])])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yvar "q_lhs_value"), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_rhs_base"), (yop EVM.Op.shl [(ylit 5), (yvar "q_j")])])]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))])])]), (yfor [(ylet "q_mem_block" (ylit 0))] (yop EVM.Op.lt [(yvar "q_mem_block"), (yvar "q_mem_count")]) [(yset "q_mem_block" (yop EVM.Op.add [(yvar "q_mem_block"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_ptr" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yop EVM.Op.mload [(yvar "q_ptr")]), (yvar "r")]), (yvar "r")]))]), (yfor [(ylet "q_product_block" (ylit 0))] (yop EVM.Op.lt [(yvar "q_product_block"), (yvar "q_product_count")]) [(yset "q_product_block" (yop EVM.Op.add [(yvar "q_product_block"), (ylit 1)]))] [(ylet "q_word" (yop EVM.Op.mload [(yvar "q_pc")])), (ylet "qconst" (yop EVM.Op.byte [(ylit 0), (yvar "q_word")])), (ylet "q_lhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 232), (yvar "q_word")]), (ylit 65535)])), (ylet "q_rhs" (yop EVM.Op.and [(yop EVM.Op.shr [(ylit 216), (yvar "q_word")]), (ylit 65535)])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 5)])), (yset "q_acc" (yop EVM.Op.addmod [(yvar "q_acc"), (yop EVM.Op.mulmod [(yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_lhs")]), (yop EVM.Op.mload [(yvar "q_rhs")]), (yvar "r")]), (yop EVM.Op.mload [(yop EVM.Op.add [(yvar "q_const_mptr"), (yop EVM.Op.shl [(ylit 5), (yvar "qconst")])])]), (yvar "r")]), (yvar "r")]))]), (yif (yop EVM.Op.and [(yvar "q_flags"), (ylit 1)]) [(yset "q_acc" (yop EVM.Op.mulmod [(yop EVM.Op.mload [(yvar "q_cond_ptr")]), (yvar "q_acc"), (yvar "r")]))]), (yset "q_top" (yvar "q_acc")), (yset "q_has_top" (ylit 1))]

/-- ARM 'foldMain' (family 'fold'): the arm body 'qvmFoldArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyFoldMain (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.iszero [(yop EVM.Op.and [(yvar "q_has_top"), (yop EVM.Op.eq [(yvar "q_sp"), (ylit program.stackMptr)])])]) [(yexpr (ycall "q_program_fail" []))]), (ylet "q_eval" (yvar "q_top")), (yset "q_has_top" (ylit 0)), (yexpr (yop EVM.Op.mstore [(ylit program.evalNumerMptr), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(ylit program.evalNumerMptr)]), (yvar "y"), (yvar "r")])])), (yexpr (yop EVM.Op.mstore [(ylit program.evalNumerMptr), (yop EVM.Op.addmod [(yop EVM.Op.mload [(ylit program.evalNumerMptr)]), (yvar "q_eval"), (yvar "r")])]))]

/-- ARM 'foldSelector' (family 'fold'): the arm body 'qvmFoldArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyFoldSelector (_c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_selector_payload" (yop EVM.Op.shr [(ylit 232), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 3)])), (ylet "q_sel_idx" (yop EVM.Op.shr [(ylit 16), (yvar "q_selector_payload")])), (ylet "q_sel_gap" (yop EVM.Op.and [(yvar "q_selector_payload"), (ylit 65535)])), (yif (yop EVM.Op.iszero [(yop EVM.Op.lt [(yvar "q_sel_idx"), (ylit program.guards.numSelectorBuckets)])]) [(yexpr (ycall "q_program_fail" []))]), (yif (yop EVM.Op.gt [(yvar "q_sel_gap"), (ylit program.selectorMaxPower)]) [(yexpr (ycall "q_program_fail" []))]), (yif (yop EVM.Op.iszero [(yop EVM.Op.and [(yvar "q_has_top"), (yop EVM.Op.eq [(yvar "q_sp"), (ylit program.stackMptr)])])]) [(yexpr (ycall "q_program_fail" []))]), (ylet "q_eval" (yvar "q_top")), (yset "q_has_top" (ylit 0)), (yexpr (yop EVM.Op.mstore [(ylit program.evalNumerMptr), (yop EVM.Op.mulmod [(yop EVM.Op.mload [(ylit program.evalNumerMptr)]), (yvar "y"), (yvar "r")])])), (ylet "q_target_ptr" (yop EVM.Op.add [(yvar "SELECTOR_ACC_MPTR"), (yop EVM.Op.shl [(ylit 5), (yvar "q_sel_idx")])])), (ylet "q_sel_acc" (yop EVM.Op.mload [(yvar "q_target_ptr")])), (yif (yvar "q_sel_gap") [(yset "q_sel_acc" (yop EVM.Op.mulmod [(yvar "q_sel_acc"), (yop EVM.Op.mload [(yop EVM.Op.add [(ylit program.selectorPowerMptr), (yop EVM.Op.shl [(ylit 5), (yvar "q_sel_gap")])])]), (yvar "r")]))]), (yexpr (yop EVM.Op.mstore [(yvar "q_target_ptr"), (yop EVM.Op.addmod [(yvar "q_sel_acc"), (yvar "q_eval"), (yvar "r")])]))]

/-- ARM 'nativePermutation' (family 'native'): the arm body 'qvmNativeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyNativePermutation (c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.or [(yvar "q_has_top"), (yop EVM.Op.xor [(yvar "q_sp"), (ylit program.stackMptr)])]) [(yexpr (ycall "q_program_fail" []))])] ++ qGenFlat c.quotientNativePermutationComputation

/-- ARM 'nativeLookup' (family 'native'): the arm body 'qvmNativeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyNativeLookup (c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.or [(yvar "q_has_top"), (yop EVM.Op.xor [(yvar "q_sp"), (ylit program.stackMptr)])]) [(yexpr (ycall "q_program_fail" []))])] ++ qGenFlat c.quotientNativeLookupComputation

/-- ARM 'nativeIdentity' (family 'native'): the arm body 'qvmNativeArms' used to spell inline,
    lifted unchanged so a lemma can name it (QEMIT4). -/
def qArmBodyNativeIdentity (c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(ylet "q_native_idx" (yop EVM.Op.shr [(ylit 240), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 2)])), (yif (yop EVM.Op.or [(yvar "q_has_top"), (yop EVM.Op.xor [(yvar "q_sp"), (ylit program.stackMptr)])]) [(yexpr (ycall "q_program_fail" []))]), (Stmt.switch (yvar "q_native_idx") ((c.quotientNativeIdentityComputations.zipIdx).map fun (blk, i) => (Literal.number i, qGenFlat blk)) (some [(yexpr (ycall "q_program_fail" []))]))]

/-- The non-native opcode arms, in the template's own order, each gated on the 'opUsage' flag the
    render gates its text on. The case LABELS are 'templateConstants.quotientVm.op' values, so a
    plan that re-numbers its opcodes re-numbers the emitted switch - and a plan that does not use
    an opcode does not pay for its arm. 'numA_flagsSelect_ok' is the gate for the first and
    'numA_isTheParseAllArms_ok' for the second. -/
def qvmOpcodeArms (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : List (Literal × Block Op) :=
  (if program.opUsage.pushConst then [(Literal.number tcq.op.pushConst, qArmBodyPushConst _c program tcq)] else [])
      ++ (if program.opUsage.pushMemLiteral then [(Literal.number tcq.op.pushMemLiteral, qArmBodyPushMemLiteral _c program tcq)] else [])
      ++ (if program.opUsage.pushMemToken then [(Literal.number tcq.op.pushMemToken, qArmBodyPushMemToken _c program tcq)] else [])
      ++ (if program.opUsage.pushMemTokenOffset then [(Literal.number tcq.op.pushMemTokenOffset, qArmBodyPushMemTokenOffset _c program tcq)] else [])
      ++ (if program.opUsage.pushMemU16 then [(Literal.number tcq.op.pushMemU16, qArmBodyPushMemU16 _c program tcq)] else [])
      ++ (if program.opUsage.add then [(Literal.number tcq.op.add, qArmBodyAdd _c program tcq)] else [])
      ++ (if program.opUsage.mul then [(Literal.number tcq.op.mul, qArmBodyMul _c program tcq)] else [])
      ++ (if program.opUsage.neg then [(Literal.number tcq.op.neg, qArmBodyNeg _c program tcq)] else [])
      ++ (if program.opUsage.pow5 then [(Literal.number tcq.op.pow5, qArmBodyPow5 _c program tcq)] else [])
      ++ (if program.opUsage.pushConstU8 then [(Literal.number tcq.op.pushConstU8, qArmBodyPushConstU8 _c program tcq)] else [])
      ++ (if program.opUsage.addConstU8 then [(Literal.number tcq.op.addConstU8, qArmBodyAddConstU8 _c program tcq)] else [])
      ++ (if program.opUsage.mulConstU8 then [(Literal.number tcq.op.mulConstU8, qArmBodyMulConstU8 _c program tcq)] else [])
      ++ (if program.opUsage.addConst then [(Literal.number tcq.op.addConst, qArmBodyAddConst _c program tcq)] else [])
      ++ (if program.opUsage.mulConst then [(Literal.number tcq.op.mulConst, qArmBodyMulConst _c program tcq)] else [])
      ++ (if program.opUsage.addMemU16 then [(Literal.number tcq.op.addMemU16, qArmBodyAddMemU16 _c program tcq)] else [])
      ++ (if program.opUsage.mulMemU16 then [(Literal.number tcq.op.mulMemU16, qArmBodyMulMemU16 _c program tcq)] else [])
      ++ (if program.opUsage.addMulMemMemConstU8 then [(Literal.number tcq.op.addMulMemMemConstU8, qArmBodyAddMulMemMemConstU8 _c program tcq)] else [])
      ++ (if program.opUsage.addMulConstU8MemU16 then [(Literal.number tcq.op.addMulConstU8MemU16, qArmBodyAddMulConstU8MemU16 _c program tcq)] else [])
      ++ (if program.opUsage.addMulMemMem then [(Literal.number tcq.op.addMulMemMem, qArmBodyAddMulMemMem _c program tcq)] else [])
      ++ (if program.opUsage.runAddMulMemMemConstU8 then [(Literal.number tcq.op.runAddMulMemMemConstU8, qArmBodyRunAddMulMemMemConstU8 _c program tcq)] else [])
      ++ (if program.opUsage.runAddMulConstU8MemU16 then [(Literal.number tcq.op.runAddMulConstU8MemU16, qArmBodyRunAddMulConstU8MemU16 _c program tcq)] else [])
      ++ (if program.opUsage.affineSum then [(Literal.number tcq.op.affineSum, qArmBodyAffineSum _c program tcq)] else [])
      ++ (if program.opUsage.lin7 then [(Literal.number tcq.op.lin7, qArmBodyLin7 _c program tcq)] else [])
      ++ (if program.opUsage.bilin7Row then [(Literal.number tcq.op.bilin7Row, qArmBodyBilin7Row _c program tcq)] else [])
      ++ (if program.opUsage.bilin7Pairwise then [(Literal.number tcq.op.bilin7Pairwise, qArmBodyBilin7Pairwise _c program tcq)] else [])
      ++ (if program.opUsage.modarith7 then [(Literal.number tcq.op.modarith7, qArmBodyModarith7 _c program tcq)] else [])

/-! ### (b2) The fold arms -/

/-- The two FOLD arms, which the template places AFTER the native callbacks: they are the identity
    boundaries, and the switch order here is the template's order, not a grouping of convenience.
    Kept separate from 'qvmOpcodeArms' for exactly that reason - a split that reorders the switch
    would still be a program and would still fail 'stmtsBeq', which is the gate that caught it. -/
def qvmFoldArms (_c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : List (Literal × Block Op) :=
  (if program.opUsage.foldMain then [(Literal.number tcq.op.foldMain, qArmBodyFoldMain _c program tcq)] else [])
      ++ (if program.opUsage.foldSelector then [(Literal.number tcq.op.foldSelector, qArmBodyFoldSelector _c program tcq)] else [])

/-! ### (c) Native callbacks -/

/-- The three native-callback arms. Each is the identity-boundary guard followed by the family's
    generated lines. 'nativeIdentity' is the one family spliced as a CASE LIST rather than as
    statements, because the render emits one 'case index0' per block. -/
def qvmNativeArms (c : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : List (Literal × Block Op) :=
  (if program.opUsage.nativePermutation && (c.quotientNativePermutationComputation).length > 0 then [(Literal.number tcq.op.nativePermutation, qArmBodyNativePermutation c program tcq)] else [])
      ++ (if program.opUsage.nativeLookup && (c.quotientNativeLookupComputation).length > 0 then [(Literal.number tcq.op.nativeLookup, qArmBodyNativeLookup c program tcq)] else [])
      ++ (if program.opUsage.nativeIdentity && (c.quotientNativeIdentityComputations).length > 0 then [(Literal.number tcq.op.nativeIdentity, qArmBodyNativeIdentity c program tcq)] else [])

/-! ### (d) The dispatch loop, the epilogue and the selector tail -/

/-- The three statements ahead of the switch inside the loop body: the opcode fetch and the
    one-byte cursor advance. The fetch is the reason the quotient VM does not execute at any fuel
    by unrolling - 'q_op' is symbolic, so 'selectSwitch' cannot reduce it - and it is the leaf T3.10
    has to reason about, which is what makes it worth having as a tree rather than as text. -/
def qvmLoopPre : Block Op :=
  [(ylet "q_op" (yop EVM.Op.byte [(ylit 0), (yop EVM.Op.mload [(yvar "q_pc")])])), (yset "q_pc" (yop EVM.Op.add [(yvar "q_pc"), (ylit 1)]))]

/-- The dispatch loop: an empty init and post, the byte-cursor condition, and the switch over the
    arms of (b) and (c) in template order with the fail-closed default. -/
def qvmLoop (c : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    : Stmt Op :=
  Stmt.forLoop [] (yop EVM.Op.lt [(yvar "q_pc"), (yvar "q_end")]) []
    (qvmLoopPre ++
      [Stmt.switch (yvar "q_op")
        (qvmOpcodeArms c program tcq ++ qvmNativeArms c program tcq
          ++ qvmFoldArms c program tcq) (some [(yexpr (ycall "q_program_fail" []))])])

/-- The post-loop epilogue: the three terminal guards (pc exhausted, no live cached top, stack
    balanced), the POST-VM SUFFIX family, the selector y-power tail blocks - one per
    'selectorTailUpdates' entry, gated on there being simple selectors at all - and the negation
    store that makes the artifact's '-nu_y(x)'. -/
def qvmEpilogue (c : PartialCtx) (program : QuotientProgram)
    (_tcq : QuotientVmTemplateConstants) : Block Op :=
  [(yif (yop EVM.Op.iszero [(yop EVM.Op.eq [(yvar "q_pc"), (yvar "q_end")])]) [(yexpr (ycall "q_program_fail" []))]), (yif (yvar "q_has_top") [(yexpr (ycall "q_program_fail" []))]), (yif (yop EVM.Op.iszero [(yop EVM.Op.eq [(yvar "q_sp"), (ylit program.stackMptr)])]) [(yexpr (ycall "q_program_fail" []))])] ++
      qGenNested c.quotientPostVmComputations ++
      (if c.simpleSelectorCols.length > 0 then (program.selectorTailUpdates.map fun tail => (yblock [(ylet "q_sel_ptr" (yop EVM.Op.add [yvar "SELECTOR_ACC_MPTR", (ylit tail.selectorOffset)])), (yexpr (yop EVM.Op.mstore [yvar "q_sel_ptr", (yop EVM.Op.mulmod [(yop EVM.Op.mload [yvar "q_sel_ptr"]), (yop EVM.Op.mload [(yop EVM.Op.add [(ylit program.selectorPowerMptr), (ylit tail.powerOffset)])]), yvar "r"])]))])) else []) ++
      [(ylet "linearization_expected_eval" (yop EVM.Op.addmod [(ylit 0), (yop EVM.Op.sub [(yvar "r"), (yop EVM.Op.mload [(ylit program.evalNumerMptr)])]), (yvar "r")])), (yexpr (yop EVM.Op.mstore [(yvar "QUOTIENT_EVAL_MPTR"), (yvar "linearization_expected_eval")])), (yexpr (yop EVM.Op.pop [(yvar "y")]))]

/-! ### The deliverable -/

/-- THE WHOLE NUMERATOR REGION AS AN AST (OBJ.15). The 953 template tokens of
    'renderQuotientNumeratorBlock' at the deployed render are built here as a tree, as a function
    of the 'QuotientProgram' the render reads and of 'templateConstants.quotientVm'; the six
    generated line families are spliced by 'parseLines', which is exactly the split the card draws.

    THE LEGACY / DIRECT ARM IS OUT OF SCOPE AND IS NAMED, NOT HIDDEN. 'c.quotientProgram = none'
    selects the template's 'when None' arm, which the card's "does NOT need" line excludes ("the
    external, direct, probe and trace arms"). It falls back to the OBJ.2 parse, so this function is
    TOTAL and agrees with 'emitQuotientNumerator' at every context; 'numA_agreesWithParseNoProgram_ok'
    pins that rather than leaving it to a comment.

    THE FINGERPRINT DOES NOT MOVE, AND THAT IS A GATE. Nothing here is wired into 'emitPartialM':
    the deployed program still reads its numerator through 'emitQuotientNumerator', the OBJ.2 parse.
    'numA_agreesWithParse_ok' is the gate that says the two are the SAME TREE at the deployment,
    which is what makes rewiring a free choice for T3.10 instead of an artifact change. -/
def emitQuotientNumeratorA (c : PartialCtx) : Block Op :=
  match c.quotientProgram with
  | none => emitQuotientNumerator c
  | some program =>
      let tcq := c.templateConstants.quotientVm
      [Stmt.block (qvmPrologue c program tcq ++ [qvmLoop c program tcq]
        ++ qvmEpilogue c program tcq)]

end Midfall.Lowering.GenAst