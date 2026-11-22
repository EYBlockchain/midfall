-- |
-- Midfall.Lowering.QuotientInterp
--
-- T3.10 (PLAN-V3 V3 row 39, ROUTE B): THE CONTRACT for the quotient VM's interpreter loop as the
-- OBJ.15 emitter prints it, FOR EVERY PROGRAM, with witness and falsifiers. This is a STATEMENT
-- card: the contract is landed typechecked and the row that proves it is ROW.Q, not this file.
--
-- WHY A CONTRACT AND NOT AN EXECUTION. /tmp/QPROBE-REPORT.md sections 2 and 4 measured that the
-- quotient numerator does not execute under wp at ANY fuel: the interpreter fetches its opcode from
-- SYMBOLIC memory - 'q_op := byte(0, mload(q_pc))', GenAst.qvmLoopPre - so 'selectSwitch' cannot
-- reduce, and the full slice left ONE stuck leaf of 81,768 chars with ZERO 'False' leaves. That is
-- stuck on symbolic data, not out of fuel, so raising fuel cannot help and Route A (execute one
-- circuit's numerator) is excluded by D-P71. The only executable route to ROW.Q is a loop rule
-- stated over the interpreter as a TREE - which is what OBJ.15's 'GenAst.emitQuotientNumeratorA'
-- makes possible, and why this file instantiates the contract at THAT emitter.
--
-- PROVENANCE OF THE STATEMENT, AND EXACTLY WHAT CHANGED. The contract shape is PORTED from
-- 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean:896-908' ('def QInterpRefines'), a
-- sorry-free 'def' in a file that DOES NOT COMPILE at HEAD (15 errors on the numInst/disjoint-residual
-- facts OBJ.4 proved are not table facts), so it cannot be imported - only copied.
-- 'QInterpRefinesShape' below is that copy, VERBATIM down to the binder names, with nothing adapted
-- except the declaration's own name and the qualification 'Midfall.Word256' (a machine diff of the two
-- is 13 lines, 2 differences); it stays in the file so the port is auditable and so the changes the
-- deliverable makes are visible against it instead of smuggled into it. The deliverable
-- 'QInterpRefines' then makes exactly THREE changes, and no others: the two D-P72 orders, plus one
-- correction the port could not have stated because it had no window (see 'QSegment.inWindow').
--
--   (a) THE MEMORY WINDOW. The port passes 'bytes : List Nat' as if it were the whole address space
--       and quantifies 'cursor exprEnd' freely. D-P72: "state the contract over a memory window
--       (base address and length as parameters) ... the agreement relation is over offsets within the
--       window, not plan-view addresses". So the segment becomes 'QSegment' (window base, window
--       length, segment start, segment end) and agreement relates BYTES AT OFFSETS. This is not
--       cosmetic: without 'exprEnd <= len' the contract is FALSE of the correct interpreter, because
--       the loop 'mload's past the window and nothing constrains what is there - which is what
--       'qinterpRefines_falsifier_window_bound' exhibits.
--   (b) THE DIALECT PARAMETER. The port is fixed at 'Bridge.Dialect c g'. D-P72: "not fixed to
--       'Bridge.Dialect c g', so that the same theorem serves the embedded numerator and the external
--       evaluator's body, which runs in the closed dialect on the callee's copy of the frame
--       (WID.17)". So 'D' is a parameter with '[DecidableEq D.Value]', and the two EVM-shaped things
--       the port hard-codes become named parameters: 'reverts' (supplied as 'Midfall.Lowering.Reverted'
--       at the row) and 'word : U256 -> D.Value' (supplied as the identity, since both dialects have
--       'Value = U256'). The quantifier order, the disjunction, the reference call and the two
--       'AtSegment' positions are the port's.
--
-- NO FIXTURE IS IN THE STATEMENT (D-P71). Everything is parametric in the program: the contract takes
-- 'interp', and the row 'qinterpRefines_qvmLoop' is quantified over EVERY 'PartialCtx', EVERY
-- 'QuotientProgram' and EVERY template-constant table; it never names 'poseidonRender'. The F1
-- instance and the Bool teeth gates live in 'Midfall/Instances/QInterpWitnessF1.lean', where
-- 'native_decide' and the fixture are allowed to be (D-P17, D-P71).
--
-- WHAT THIS FILE DOES NOT DO. It does not prove the contract (ROW.Q and its children); it does not
-- touch the emitter (OBJ.14/15 are done); it does not repair 'GeneratorRows.lean'. The one 'sorry'
-- is the row itself, 'qinterpRefines_qvmLoop', registered as ROW.Q's.
--
-- TEETH. W12 is three PROVED generic witnesses (plus two PROVED F1 witnesses in the Instances file)
-- and four PROVED falsifiers, none of them an '#eval'. Each
-- falsifier names the clause it exists to keep honest: the revert disjunct, the end-of-segment
-- position, the window bound, the value clause. Following OBJ.15's precedent, a gate that cannot go
-- red is not a gate.

import Midfall.Lowering.GenAstQvm
import Midfall.Lowering.Partials
import Midfall.Yul.Bridge
import Midfall.Yul.Contracts
import Midfall.Yul.WpTac
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmValidator

set_option autoImplicit false

namespace Midfall.Lowering.QuotientInterp

open YulSemantics YulSemantics.EVM Midfall.Generator Midfall.Lowering Midfall.Lowering.GenAst
open Midfall.Yul Midfall.Yul.Bridge

/-! ### 1. The memory window (D-P72 (a)) -/

/-- ONE PROGRAM WINDOW OF THE INTERPRETER, as the emitter's prologue leaves it: the window occupies
    the byte addresses '[base, base + len)' of Yul memory, and the identity subprogram under
    discussion is the half-open OFFSET interval '[cursor, exprEnd)' inside it. Offsets, not plan-view
    addresses - that is D-P72's instruction, and it is what lets one statement serve the embedded
    numerator (whose 'q_program_mptr' is the plan view's) and the external evaluator's body (whose
    base is the callee's copy of the frame). -/
structure QSegment where
  /-- Byte address of the window's first program byte. -/
  base : Nat
  /-- Number of program bytes in the window. -/
  len : Nat
  /-- Offset at which the segment starts. -/
  cursor : Nat
  /-- Offset at which the segment ends (exclusive). -/
  exprEnd : Nat

/-- THE WINDOW BOUND - and it is stricter than the port's free quantifier, for a reason that is a
    FINDING ABOUT THE PORTED SHAPE. 'exprEnd <= len' is what lets 'Agrees' constrain every byte the
    loop reads. 'cursor < exprEnd' - STRICT, not the port's implicit '≤' - is what keeps the contract
    TRUE of the emitted loop at all: on an EMPTY segment the reference VM errors
    ('evalQuotientIdentity [] consts mem' ends in 'QVMFault.stackLengthMismatch 0': the Rust pops a
    value it never pushed), while the emitted loop does not enter its body and exits NORMALLY. A
    contract that quantifies over empty segments is therefore false of the very program it exists to
    constrain. Every non-empty garbage segment is fine, because every emitted switch is fail-closed on
    an unknown opcode. The port had no window and so no way to say any of this. -/
def QSegment.inWindow (s : QSegment) : Prop :=
  s.cursor < s.exprEnd ∧ s.exprEnd ≤ s.len

/-- The same window positioned at the end of the segment: the post-state's position. -/
def QSegment.atEnd (s : QSegment) : QSegment := { s with cursor := s.exprEnd }

/-- The byte at offset 'i' of a program window, as the interpreter's 'byte(0, mload ..)' sees it. -/
def windowByte (bytes : List Nat) (i : Nat) : UInt8 := UInt8.ofNat (bytes.getD i 0)

/-- Agreement of Yul memory with the PROGRAM window, BY OFFSET. The interpreter reads its opcode and
    its operands as 'byte(0, mload(q_pc))' and 'shr 240 (mload(q_pc))' - big-endian from 'q_pc' - so
    byte-at-offset agreement is exactly what makes the two sides read the same program. -/
def AgreesProgram (st : EvmState) (s : QSegment) (bytes : List Nat) : Prop :=
  ∀ i, i < s.len → st.memory (s.base + i) = windowByte bytes i

/-- Agreement of Yul memory with the CONSTANT window: 'consts' is the reference's 'Vec<U256>' and the
    emitter addresses slot 'k' as 'q_const_mptr + 32*k', so this window is word-indexed. -/
def AgreesConsts (st : EvmState) (constBase : Nat) (consts : List Midfall.Word256) : Prop :=
  ∀ k, k < consts.length → loadWord st.memory (constBase + 32 * k) = consts.getD k 0

/-- Agreement of Yul memory with the FRAME window, through the reference's own derivation: word 'a'
    of the window is the plan-view address 'frameBase + 32*a' and the reference's value there is
    'mem.literal' at that address. This is the windowed form of the frame valuation whose full
    statement (token domains, 'QuotientReadModel''s window list) is ROW.Q.4's card, not this one. -/
def AgreesFrame (st : EvmState) (frameBase frameWords : Nat) (mem : QuotientRefMemory) : Prop :=
  ∀ a, a < frameWords →
    loadWord st.memory (frameBase + 32 * a) = BitVec.ofNat 256 ((mem.literal (frameBase + 32 * a)).1)

/-! ### 2. THE PORTED SHAPE, VERBATIM -/

/-- **VERBATIM PORT - DO NOT EDIT.** Copied from
    'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean:896-908' with NO adaptation: same
    binders, same implicit dialect, same 'Reverted', same 'BitVec.ofNat 256'. It is kept so that the
    two D-P72 changes in section 3 can be diffed against what the evidence file actually said, and so
    nobody has to re-derive the shape from a file that does not compile. The source calls it "THE
    CONTRACT SHAPE OF ROUTE B's ONE-OFF LEMMA". -/
def QInterpRefinesShape {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (interp : Block EVM.Op) (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : EvmState → QuotientRefMemory → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → Nat → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop) : Prop :=
  ∀ (cursor exprEnd : Nat) (mem : QuotientRefMemory),
    StmtsContractAll (D := Bridge.Dialect c g) funs interp
      (fun V st => AtSegment V st cursor ∧ Agrees st mem)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity ((bytes.drop cursor).take (exprEnd - cursor))
            consts mem = .ok (v, mem') ∧
          Top V' st' (BitVec.ofNat 256 v) ∧ AtSegment V' st' exprEnd))

/-! ### 3. THE CONTRACT, IN ITS D-P72 FORM -/

/-- **THE CONTRACT (T3.10 deliverable).** 'interp' refines the reference VM 'evalQuotientIdentity'
    ONCE: started at any window 's' inside which the segment '[cursor, exprEnd)' lies, on a memory
    that 'Agrees' with the reference memory 'mem', every run either reverts or leaves on the
    interpreter's operand stack exactly the word the reference computes for the segment's bytes.

    It is a 'def ... : Prop' and it is sorry-free: the CONTRACT is the deliverable and the ROW is
    'qinterpRefines_qvmLoop' below. The diff against 'QInterpRefinesShape' (section 2) is exactly
    D-P72 (a) and (b) and nothing else:

      * '{D : YulSemantics.Dialect} [DecidableEq D.Value]' replaces the fixed 'Bridge.Dialect c g',
        and the two EVM-shaped things the port hard-codes become named parameters: 'reverts' and
        'word';
      * the free 'cursor exprEnd' pair becomes one 'QSegment', which carries the window base and
        length the port lacked, and the segment is required to lie inside the window ('s.inWindow');
      * 'Agrees' takes the segment, because agreement is now by offset inside a window;
      * 'AtSegment' takes the whole segment rather than a bare position, because the loop's bound is
        'q_end' and the only way to say "this run stops at 'exprEnd'" is to put 'exprEnd' in the
        state the pre establishes. The port's 'AtSegment V st cursor' / 'AtSegment V' st' exprEnd'
        become 'AtSegment V st s' / 'AtSegment V' st' s.atEnd' - same two positions, same role. -/
def QInterpRefines {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (funs : FunEnv D) (interp : Block D.Op)
    (reverts : D.State → Prop) (word : U256 → D.Value)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : D.State → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv D → D.State → QSegment → Prop)
    (Top : VEnv D → D.State → D.Value → Prop) : Prop :=
  ∀ (s : QSegment) (mem : QuotientRefMemory), s.inWindow →
    StmtsContractAll (D := D) funs interp
      (fun V st => AtSegment V st s ∧ Agrees st mem s)
      (fun _ _ V' st' o => (o = .halt ∧ reverts st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity
            ((bytes.drop s.cursor).take (s.exprEnd - s.cursor)) consts mem = .ok (v, mem') ∧
          Top V' st' (word (BitVec.ofNat 256 v)) ∧ AtSegment V' st' s.atEnd))

/-! ### 4. THE THREE PREDICATES, at the open dialect -/

/-- THE INTERPRETER'S STATE IN THE YUL ENVIRONMENT (card step 1). The emitter's prologue
    ('GenAst.qvmPrologue') initialises exactly five registers that the loop reads and that a segment
    boundary pins: the program counter, the loop bound, the program-window base, the constant-window
    base and the operand-stack base. 'q_top'/'q_has_top' are deliberately NOT here: at a segment START
    the cached top is empty and at a segment END it holds the identity's value, so one predicate
    cannot pin both - which is what 'qinterpTop' is for. -/
def AtSegment {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (V : VEnv (Bridge.Dialect c g)) (_st : EvmState) (s : QSegment) : Prop :=
  VEnv.get V "q_pc" = some (BitVec.ofNat 256 (s.base + s.cursor)) ∧
  VEnv.get V "q_end" = some (BitVec.ofNat 256 (s.base + s.exprEnd)) ∧
  VEnv.get V "q_program_mptr" = some (BitVec.ofNat 256 s.base) ∧
  VEnv.get V "q_const_mptr" = some (BitVec.ofNat 256 program.constMptr) ∧
  VEnv.get V "q_sp" = some (BitVec.ofNat 256 program.stackMptr)

/-- THE WORD ON TOP OF THE INTERPRETER'S STACK. The QVM keeps its top in a register with a validity
    bit ('q_top', 'q_has_top') and spills to memory below it, so "the VM stack holds 'w'" is the
    register pair, not a memory read. The stack BELOW the top is the segment-boundary invariant
    ('q_sp = program.stackMptr', in 'AtSegment'): an identity ends with its operands drained. -/
def qinterpTop {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (_st : EvmState) (w : U256) : Prop :=
  VEnv.get V "q_has_top" = some 1 ∧ VEnv.get V "q_top" = some w

/-- THE FRAME VALUATION, windowed: the three agreements the interpreter's reads need. -/
def Agrees (consts : List Midfall.Word256) (constBase frameBase frameWords : Nat)
    (bytes : List Nat) (st : EvmState) (mem : QuotientRefMemory) (s : QSegment) : Prop :=
  AgreesProgram st s bytes ∧ AgreesConsts st constBase consts ∧
    AgreesFrame st frameBase frameWords mem

/-- The register environment 'AtSegment' pins, at a segment, plus the two stack registers the
    contract's 'Top' reads. Used by the witnesses and falsifiers so they name ONE start state. -/
def segmentV {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (s : QSegment) (top : U256) (hasTop : Bool) : VEnv (Bridge.Dialect c g) :=
  [("q_pc", BitVec.ofNat 256 (s.base + s.cursor)),
   ("q_end", BitVec.ofNat 256 (s.base + s.exprEnd)),
   ("q_program_mptr", BitVec.ofNat 256 s.base),
   ("q_const_mptr", BitVec.ofNat 256 program.constMptr),
   ("q_sp", BitVec.ofNat 256 program.stackMptr),
   ("q_top", top), ("q_has_top", if hasTop then 1 else 0)]

/-! ### 5. THE ROW: the contract instantiated at the emitter's loop, for every program -/

/-! **BOXD: THIS ROW IS REFUTED, NOT MERELY OPEN.** The statement below is UNCHANGED - no hypothesis
    was added to it, to 'ValidV3', a bundle or the root (RULES) - but its universal closure is FALSE,
    and 'Midfall.LoweringV3.QuotientRows.qinterpRefines_qvmLoop_is_false_as_stated' PROVES the negation:
    at the window base '2^256 - 1' the loop's two cursor registers wrap, the guard 'q_pc < q_end' is
    false, the loop exits NORMALLY having run no arm, and the reference errors on the segment's bytes,
    so neither disjunct of the post holds. QLOOP's sketched route (a table that agrees with some opcode
    labels and not others, making the loop run the WRONG arm) is a second, independent route to the
    same failure, and 'QuotientRows.lean' section 12 now PROVES that route too: at the DEFAULT table, a
    program whose only emitted arm is 'neg' and the segment '[qOpNeg]', the loop runs the neg arm to a
    NORMAL exit ('q_pc = q_end') while the reference pops an empty stack and errors - the arm's own
    precondition (a live cached top, a non-empty reference stack) is simply not pinned by the pre. So
    the row fails on three independent axes: the window bound, the unpinned operand stack, and the
    disagreeing table. W13 says a sorry whose negation is proved is
    deleted and the row restated - a HUMAN ruling, because it moves the register, the fingerprint pin
    and the 'kat_gate.py' note naming this hole.

**D-QVM2 IS THAT RULING, AND THIS COMMIT EXECUTES IT** ('design.md:2763-2792', APPROVED 2026-11-21).
'qinterpRefines_qvmLoop' is RETIRED: its sorry is deleted here, in the same commit that states the
replacement (section 11, 'QInterpRefinesSegment'), which is what W13 requires - a sorry deleted without
its replacement in the same commit would break the ruling, and a replacement stated without retiring
the refuted row would leave a refuted hole standing. The retired TEXT is kept below as
'qinterpRefines_qvmLoop_retired', a sorry-free 'Prop', so the refutations stay citable against the
statement they refute; and the ROWFALSE refutations ('QuotientRows.lean' sections 11 and 12, including
':1281') STAY IN THE TREE as the W12 falsifiers of the retired text. They are not deleted with the row:
they are the evidence for retiring it. -/

/-- **THE RETIRED ROW'S TEXT, KEPT AS A 'Prop' AND NOT AS A ROW (D-QVM2).** This is VERBATIM the
    statement of the sorried row that stood here - same binders, same instantiation of 'reverts',
    'word', 'AtSegment', 'Top' and 'Agrees', same block '[GenAst.qvmLoop ctx program tcq]', same bytes
    and constants - with 'theorem ... := by sorry' replaced by 'def ... : Prop' and nothing else
    changed. It carries no proof and no sorry, so it is NOT a registered hole; it is the retired text,
    kept so that 'QuotientRows.lean' section 11's falsifiers refute a NAMED declaration instead of a
    copy inlined into a negation, and so the equivalence is itself proved
    ('Midfall.LoweringV3.QuotientRows.qinterpRetired_text_is_the_refuted_row'). The replacement is
    'QInterpRefinesSegment' in section 11. -/
def qinterpRefines_qvmLoop_retired {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (bytes : List Nat) (consts : List Midfall.Word256)
    (frameBase frameWords : Nat) : Prop :=
  QInterpRefines (D := Bridge.Dialect c g)
    (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
    (AtSegment := AtSegment program) (Top := qinterpTop)
    (Agrees := fun st mem s => Agrees consts program.constMptr frameBase frameWords bytes st mem s)
    funs [GenAst.qvmLoop ctx program tcq] bytes consts

/-! ### 6. THE ARM FAMILIES (card step 3) -/

/-- The families the emitted switch divides into, each with ONE shared proof shape: this is the
    decomposition ROW.Q has to induct over. The gate
    'Midfall.Instances.QInterpWitnessF1.qinterpArmFamilies_cover_ok' is the teeth that says the table
    IS the emitter's arm list at both OBJ.15 acceptance contexts, so an arm added to the emitter
    without a family - or a family naming an opcode the emitter no longer prints - reddens it. -/
inductive QArmFamily : Type
  /-- PUSH_CONST, PUSH_CONST_U8, PUSH_MEM_LITERAL, PUSH_MEM_U16: decode an operand, push a word. -/
  | push
  /-- PUSH_MEM_TOKEN, PUSH_MEM_TOKEN_OFFSET: the arm carries a second switch over memory tokens. -/
  | token
  /-- ADD, MUL, NEG, POW5: pop one, combine with the cached top, keep one. -/
  | arith
  /-- ADD_CONST*, MUL_CONST*, *_MEM_U16, ADD_MUL_*: fused one-shot forms. -/
  | fused
  /-- RUN_*, AFFINE_SUM: count-prefixed repeated blocks - a loop inside the arm. -/
  | run
  /-- LIN7, BILIN7_*, MODARITH7: the limb loops over 'tcq.limbCount'. -/
  | limb
  /-- FOLD_MAIN, FOLD_SELECTOR: the identity boundaries - the only arms that END a segment. -/
  | fold
  /-- NATIVE_*: the generated callback bodies, spliced by 'qGenFlat'. -/
  | native
  deriving DecidableEq, Repr

/-- Which family each emitted arm belongs to, keyed by the arm's NAME so the gate can read it off
    'program.opUsage' without knowing the plan's numbering. -/
def qArmFamilyOfName (name : String) : Option QArmFamily :=
  match name with
  | "pushConst" | "pushConstU8" | "pushMemLiteral" | "pushMemU16" => some .push
  | "pushMemToken" | "pushMemTokenOffset" => some .token
  | "add" | "mul" | "neg" | "pow5" => some .arith
  | "addConstU8" | "mulConstU8" | "addConst" | "mulConst" | "addMemU16" | "mulMemU16"
  | "addMulMemMemConstU8" | "addMulConstU8MemU16" | "addMulMemMem" => some .fused
  | "runAddMulMemMemConstU8" | "runAddMulConstU8MemU16" | "affineSum" => some .run
  | "lin7" | "bilin7Row" | "bilin7Pairwise" | "modarith7" => some .limb
  | "foldMain" | "foldSelector" => some .fold
  | "nativePermutation" | "nativeLookup" | "nativeIdentity" => some .native
  | _ => none

/-- The emitter's whole arm list IN THE ORDER 'qvmLoop' PUTS THEM: the 26 opcode arms of
    'qvmOpcodeArms', then the 3 native callbacks of 'qvmNativeArms', then the 2 fold arms of
    'qvmFoldArms' - 31 names, which is what 'numA_isTheParseAllArms_ok' counts as 'armCount' at the
    all-flags context and 10 at the deployment. -/
def qArmNames : List String :=
  ["pushConst", "pushMemLiteral", "pushMemToken", "pushMemTokenOffset", "pushMemU16",
   "add", "mul", "neg", "pow5", "pushConstU8", "addConstU8", "mulConstU8", "addConst",
   "mulConst", "addMemU16", "mulMemU16", "addMulMemMemConstU8", "addMulConstU8MemU16",
   "addMulMemMem", "runAddMulMemMemConstU8", "runAddMulConstU8MemU16", "affineSum",
   "lin7", "bilin7Row", "bilin7Pairwise", "modarith7",
   "nativePermutation", "nativeLookup", "nativeIdentity",
   "foldMain", "foldSelector"]

/-- The table is total over the emitter's arm list: no name in it is family-less. PROVED, not gated. -/
theorem qArmFamilyOfName_total : ∀ n ∈ qArmNames, (qArmFamilyOfName n).isSome := by decide

/-- The exhibits' windows are legal: segment '[0, len)' inside a window of 'len' bytes at 'base'. -/
theorem inWindow_exhibit (base len : Nat) (h : 0 < len) :
    QSegment.inWindow ⟨base, len, 0, len⟩ := ⟨h, Nat.le_refl len⟩

/-! ### 6.5. THE EIGHT ARM FAMILIES AT THE EMITTER'S OWN ARMS (QEMIT4)

ROW.Q.3's decomposition is this table: eight families, thirty-one arms. Q1 landed the DISPATCH
side (qSwitch_arm, qSwitch_failClosed in QuotientFrame.lean) and reported that the arm BODIES
were unreachable from the emitter, so no family leaf could name the block it constrains: rewriting
at qvmOpcodeArms normalises all thirty-one inline bodies before List.find? can act, and that
dies at whnf (200000 heartbeats, ~11 s). QEMIT4 lifts each body to a top-level def named
qArmBody... in GenAstQvm.lean - a binding change, values untouched, every numA_* and qem_* gate
still true and the fingerprint unmoved - and THAT is what makes the eight statements below
expressible at the emitter's own list rather than at a body passed in as a parameter.

WHAT EACH FAMILY LEMMA SAYS, AND WHAT IT DOES NOT. qArmFamily_<family> is the GADGET
IDENTIFICATION: for every arm of the family, the emitter's own arm list carries exactly the named
body at that arm's label. Apart from the flag hypothesis hou : program.opUsage = opUsageAllOn it is
unconditional - and hou is a hypothesis about a program's own flag record, not a fixture (D-P71);
it is needed because a program that does not use an opcode does not emit its arm. What is NOT here,
and is the rest of ROW.Q.3, is the VALUE half - that the body's effect on q_top / q_sp / q_pc /
q_has_top refines the reference step. That half is QuotientFrame.lean section B's qStepValue_*
equations on the reference side plus a StmtsContractAll proof per arm on the emitted side; it is
not manufactured here. No row, bundle, ValidV3 or the root gains a hypothesis (RULES), and nothing
below is a sorry: these are theorems.

THE TACTIC IS A FINDING, AND IT IS THE LIFT THAT BUYS IT. simp only [qvmOpcodeArms, hou,
opUsageAllOn] STILL dies at whnf after the lift - what normalises the term is simp rewriting at the
definition, not the presence of the bodies inline. The recipe that works is the split one:
unfold qvmOpcodeArms (cheap: the bodies are top-level names, so the chain prints with thirty-one
ATOMIC entries), then simp only [hou, opUsageAllOn] to decide the guards, then simp to close the
membership. All eight families together cost ~4 s.

The three count-prefixed arms of QuotientFrame.lean section F (RUN_ADD_MUL_MEM_MEM_CONST_U8,
RUN_ADD_MUL_CONST_U8_MEM_U16, AFFINE_SUM) are the run family below: their IDENTIFICATION lands here
like every other arm. What section F calls the missing loop-induction lemma tying foldRangeIdxM to
the emitted yfor is the VALUE half and is still open, named there. -/

/-- **FAMILY PUSH (4 arms): decode an operand and push a word.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_push (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.pushConst, qArmBodyPushConst ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.pushMemLiteral, qArmBodyPushMemLiteral ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.pushMemU16, qArmBodyPushMemU16 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.pushConstU8, qArmBodyPushConstU8 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY TOKEN (2 arms): carry a second switch over memory tokens.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_token (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.pushMemToken, qArmBodyPushMemToken ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.pushMemTokenOffset, qArmBodyPushMemTokenOffset ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY ARITH (4 arms): pop one, combine with the cached top, keep one.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_arith (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.add, qArmBodyAdd ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.mul, qArmBodyMul ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.neg, qArmBodyNeg ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.pow5, qArmBodyPow5 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY FUSED (9 arms): the fused one-shot forms.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_fused (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.addConstU8, qArmBodyAddConstU8 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.mulConstU8, qArmBodyMulConstU8 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.addConst, qArmBodyAddConst ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.mulConst, qArmBodyMulConst ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.addMemU16, qArmBodyAddMemU16 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.mulMemU16, qArmBodyMulMemU16 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.addMulMemMemConstU8, qArmBodyAddMulMemMemConstU8 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.addMulConstU8MemU16, qArmBodyAddMulConstU8MemU16 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.addMulMemMem, qArmBodyAddMulMemMem ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY RUN (3 arms): count-prefixed repeated blocks - a loop inside the arm.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_run (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.runAddMulMemMemConstU8, qArmBodyRunAddMulMemMemConstU8 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.runAddMulConstU8MemU16, qArmBodyRunAddMulConstU8MemU16 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.affineSum, qArmBodyAffineSum ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY LIMB (4 arms): the limb loops over tcq.limbCount.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_limb (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.lin7, qArmBodyLin7 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.bilin7Row, qArmBodyBilin7Row ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.bilin7Pairwise, qArmBodyBilin7Pairwise ctx program tcq) ∈ qvmOpcodeArms ctx program tcq ∧
    (Literal.number tcq.op.modarith7, qArmBodyModarith7 ctx program tcq) ∈ qvmOpcodeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmOpcodeArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY FOLD (2 arms): the identity boundaries - the only arms that END a segment.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_fold (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (Literal.number tcq.op.foldMain, qArmBodyFoldMain ctx program tcq) ∈ qvmFoldArms ctx program tcq ∧
    (Literal.number tcq.op.foldSelector, qArmBodyFoldSelector ctx program tcq) ∈ qvmFoldArms ctx program tcq
    := by
    refine ⟨?_, ?_⟩
    · unfold qvmFoldArms
      simp only [hou, opUsageAllOn]
      simp
    · unfold qvmFoldArms
      simp only [hou, opUsageAllOn]
      simp

/-- **FAMILY NATIVE (3 arms): the generated callback bodies, spliced by qGenFlat.** Every arm of the family is
    identified at the emitter's own arm list: the pair (label, NAMED BODY) that a family leaf has
    to constrain is an entry of the list the emitter builds - not a block handed to the lemma, and
    not a lookup into a list that will not reduce. -/
theorem qArmFamily_native (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) (hp : (ctx.quotientNativePermutationComputation).length > 0)
    (hl : (ctx.quotientNativeLookupComputation).length > 0)
    (hi : (ctx.quotientNativeIdentityComputations).length > 0) :
    (Literal.number tcq.op.nativePermutation, qArmBodyNativePermutation ctx program tcq) ∈ qvmNativeArms ctx program tcq ∧
    (Literal.number tcq.op.nativeLookup, qArmBodyNativeLookup ctx program tcq) ∈ qvmNativeArms ctx program tcq ∧
    (Literal.number tcq.op.nativeIdentity, qArmBodyNativeIdentity ctx program tcq) ∈ qvmNativeArms ctx program tcq
    := by
    refine ⟨?_, ?_, ?_⟩
    · unfold qvmNativeArms
      simp only [hou, opUsageAllOn, hp, hl, hi]
      simp
    · unfold qvmNativeArms
      simp only [hou, opUsageAllOn, hp, hl, hi]
      simp
    · unfold qvmNativeArms
      simp only [hou, opUsageAllOn, hp, hl, hi]
      simp

/-! THE EIGHT FAMILY LEAVES, PRINTED so the count is checkable rather than asserted: 8 theorems,
    31 arms between them (4 push + 2 token + 4 arith + 9 fused + 3 run + 4 limb + 2 fold + 3
    native), every one naming a top-level arm body of GenAstQvm.lean. -/
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_push
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_token
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_arith
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_fused
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_run
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_limb
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_fold
#print axioms Midfall.Lowering.QuotientInterp.qArmFamily_native

/-! ### 7. WITNESSES (W12) -/

/-- **WITNESS 1 - THE HYPOTHESES HOLD TOGETHER, FOR EVERY PROGRAM.** The contract's pre is
    'AtSegment V st s ∧ Agrees st mem s', and a contract with an unsatisfiable pre is worth nothing.
    This exhibits, at ANY program, ANY reference memory and ANY window base, a LEGAL non-empty window
    together with an environment and a machine state that satisfy the five register clauses and the
    three agreement clauses AT THE SAME TIME: a one-byte program window, an empty constant window and
    an empty frame window. PROVED; no 'native_decide'; no fixture. The non-degenerate F1 instance -
    the deployment's own program window, its real length and pointers - is
    'Midfall.Instances.QInterpWitnessF1.qinterpF1_hypotheses_together', also PROVED. -/
theorem qinterp_hypotheses_together {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (mem : QuotientRefMemory) (base : Nat) :
    ∃ (s : QSegment) (V : VEnv (Bridge.Dialect c g)) (st : EvmState),
      s.inWindow ∧
      AtSegment (c := c) (g := g) (program := program) V st s ∧
      Agrees [] program.constMptr 0 0 [] st mem s := by
  refine ⟨⟨base, 1, 0, 1⟩, segmentV (c := c) (g := g) (program := program) ⟨base, 1, 0, 1⟩ 0 false,
    EvmState.init, ⟨inWindow_exhibit base 1 (by decide), ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩⟩
  · simp only [Agrees]
    refine ⟨?_, ?_, ?_⟩
    · intro _ _
      rfl
    · intro k hk
      exact absurd hk (Nat.not_lt_zero k)
    · intro a ha
      exact absurd ha (Nat.not_lt_zero a)

/-- **WITNESS 2 - THE CONTRACT IS SATISFIED, WITH THE REAL PREDICATES.** A contract nothing can satisfy
    is as useless as one nothing can violate. The fail-closed block - what the emitted switch's default
    arm runs, and what every guard in every arm reaches through 'q_program_fail' - establishes
    'QInterpRefines' at the real 'AtSegment', the real 'qinterpTop' and the real
    'Midfall.Lowering.Reverted', for EVERY window, EVERY legal segment and EVERY reference memory: its
    only runs are reverts, so the post's first disjunct always holds. PROVED by the tree's own symbolic
    executor ('allRuns_of_wp' + 'wp_run' at fuel 4), not by an '#eval'.

    WHY THE REFERENCE VM IS NOT COMPUTED ANYWHERE IN THIS FILE, AND THAT IS A FINDING. The natural
    second witness - a segment on which 'evalQuotientIdentity' returns '.ok' - cannot be PROVED at
    this commit: 'evalQuotientIdentity' is not kernel-reducible even on the EMPTY program
    ('example : evalQuotientIdentity [] [] m = .error (QVMFault.stackLengthMismatch 0) := by rfl'
    FAILS), because 'evalQuotientIdentityLoop' compiles its fuel recursion through a 'where'-clause
    'go' whose eliminator the kernel will not unfold. That is why every gate over the reference VM in
    'VmReference.lean' is a '#eval' gate and why no theorem in the tree names its output; it is the same
    wall QPROBE hit from the other side. It also bounds this card's falsifiers: the strongest one (right
    cursor, right validity bit, WRONG constant slot) cannot be exhibited by computation, only by the
    bridge theorems 'Qvm.lean:1197, :1481, :1864' begin. ROW.Q's job, not a statement card's. -/
theorem qinterp_satisfied_by_the_fail_closed_block {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (bytes : List Nat) (consts : List Midfall.Word256) :
    QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun _ _ _ => True)
      [] [yexpr (yop Op.revert [ylit 0, ylit 0])] bytes consts := by
  intro s mem _ V st hpre V' st' o hrun
  have key : Midfall.Yul.WpTac.AllRuns [] V st
      [yexpr (yop Op.revert [ylit 0, ylit 0])]
      (fun _ st' o => o = .halt ∧ Midfall.Lowering.Reverted st') := by
    refine Midfall.Yul.WpTac.allRuns_of_wp 20 ?_
    wp_run
    all_goals (first | exact ⟨rfl, rfl⟩ | rfl)
  exact Or.inl (key V' st' o hrun)

/-- **WITNESS 3 - THE REGISTERS THE CONTRACT PINS ARE THE REGISTERS THE EMITTER WRITES.** 'AtSegment'
    is only a contract on the emitted loop if it names the emitter's own variables at the values the
    prologue gives them. This checks the five names against the whole-program window at an arbitrary
    program: 'q_pc' at the window start, 'q_end' at 'programMptr + program.len', the two window bases
    and the stack base - the five the prologue's last five statements write, in that order. -/
theorem qinterp_AtSegment_is_the_prologue_registers {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    AtSegment (c := c) (g := g) (program := program)
      (segmentV (c := c) (g := g) (program := program)
        ⟨program.programMptr, program.len, 0, program.len⟩ 0 false)
      EvmState.init ⟨program.programMptr, program.len, 0, program.len⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### 8. FALSIFIERS (W12) -/

/-- The machine state after 'return(0, 0)' from 'EvmState.init': halted with a 'ret' payload. A
    top-level def so the probes below can unfold it. -/
def retState : EvmState := { EvmState.init with halted := some (.ret, []) }

/-- A 'ret' halt is not a revert. PROVED by reduction; FALSIFIER 1 turns on it. -/
theorem retState_not_Reverted : ¬ Midfall.Lowering.Reverted retState := by
  simp [Midfall.Lowering.Reverted, Midfall.Lowering.revertedOf, retState]

/-- **FALSIFIER 1 - THE REVERT DISJUNCT IS NOT "ANY HALT".** The post lets a run end by REVERTING; it
    does not let it end by RETURNING. Weaken 'reverts' to 'fun _ => True' - the degenerate weakening -
    and the block 'return(0, 0)' passes the contract while saying nothing about the program; at the
    real 'Midfall.Lowering.Reverted' it is exhibited false. PROVED, with the run built from the vendored
    'Step' rules and one 'stepOp' computation. -/
theorem qinterpRefines_falsifier_revert_disjunct {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    ¬ QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun _ _ _ => True)
      [] [yexpr (yop Op.ret [ylit 0, ylit 0])] [] [] := by
  intro H
  set V₀ := segmentV (c := c) (g := g) (program := program) ⟨0, 1, 0, 1⟩ 0 false
  have hargs : Step (Bridge.Dialect c g) [] V₀ EvmState.init (.args [ylit 0, ylit 0])
      (.eres (.vals [0, 0] EvmState.init)) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit
  have hbi : (Bridge.Dialect c g).Builtin Op.ret [0, 0] EvmState.init (.halt retState) := by
    show stepOp Op.ret [0, 0] EvmState.init = some _
    rfl
  have hrun : ExecStmts (Bridge.Dialect c g) [] V₀ EvmState.init
      [yexpr (yop Op.ret [ylit 0, ylit 0])] V₀ retState .halt :=
    Step.seqStop (D := Bridge.Dialect c g) (rest := [])
      (Step.exprStmtHalt (D := Bridge.Dialect c g) (e := yop Op.ret [ylit 0, ylit 0]) (st1 := retState)
        (Step.builtinHalt (D := Bridge.Dialect c g) (args := [ylit 0, ylit 0]) (argvals := [0, 0])
          (st1 := EvmState.init) (st2 := retState) hargs hbi))
      (by decide)
  have h := H ⟨0, 1, 0, 1⟩ (quotientRefMemoryNew Midfall.Bytes.empty)
      (inWindow_exhibit 0 1 (by decide) : QSegment.inWindow ⟨0, 1, 0, 1⟩) V₀ EvmState.init
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩ V₀ retState .halt hrun
  cases h with
  | inl h => exact retState_not_Reverted h.2
  | inr h => exact absurd h.1 (by decide : ¬ ((Outcome.halt : Outcome) = Outcome.normal))

/-- **FALSIFIER 2 - THE POST DOES NOT ALLOW A FALL-THROUGH.** The ported shape's second 'AtSegment'
    is the segment END, and it is load-bearing: the empty block - what the loop degenerates to if every
    arm is deleted, or if the switch's fail-closed default becomes a no-op - satisfies the contract with
    'AtSegment V' st' s.atEnd' dropped, and does NOT satisfy it as stated. -/
theorem qinterpRefines_falsifier_no_fallthrough {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    ¬ QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun _ _ _ => True)
      [] [] [qOpPushConstU8, 7] [7, 11, 13, 17, 19, 23, 29, 31] := by
  intro H
  set V₀ := segmentV (c := c) (g := g) (program := program) ⟨0, 2, 0, 2⟩ 0 false
  have hrun : ExecStmts (Bridge.Dialect c g) [] V₀ EvmState.init [] V₀ EvmState.init .normal :=
    Step.seqNil
  have h := H ⟨0, 2, 0, 2⟩ (quotientRefMemoryNew Midfall.Bytes.empty)
      (inWindow_exhibit 0 2 (by decide) : QSegment.inWindow ⟨0, 2, 0, 2⟩) V₀ EvmState.init
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩ V₀ EvmState.init .normal hrun
  cases h with
  | inl h => exact absurd h.1 (by decide)
  | inr h =>
      obtain ⟨_, _, _, _, hpos⟩ := h.2
      obtain ⟨hpc', _, _, _, _⟩ := hpos
      have h0 : VEnv.get V₀ "q_pc" = some (0 : U256) := rfl
      rw [h0] at hpc'
      exact absurd hpc'
        (by decide : ¬ ((some (0 : U256) : Option U256) = some (BitVec.ofNat 256 2)))

/-- **FALSIFIER 3 - THE WINDOW BOUND IS NOT DECORATION (D-P72 (a)).** Drop 's.inWindow' and the
    contract demands the interpreter refine the reference on segments that run PAST the window - bytes
    'Agrees' says nothing about. Exhibited: two machine states that agree with the same window and the
    same reference memory and disagree on the first byte OUTSIDE it. The verbatim port had no window, so
    its 'bytes.getD i 0' silently agreed with a zeroed memory past the end of the program; here that is
    a hole the statement has to close. -/
theorem qinterpRefines_falsifier_window_bound :
    ∃ (st₁ st₂ : EvmState) (s : QSegment) (bytes : List Nat) (mem : QuotientRefMemory),
      AgreesProgram st₁ s bytes ∧ AgreesProgram st₂ s bytes ∧
      st₁.memory (s.base + s.len) ≠ st₂.memory (s.base + s.len) := by
  refine ⟨EvmState.init, { EvmState.init with memory := fun a => if a = 8 then 1 else 0 },
    ⟨8, 0, 0, 0⟩, [], quotientRefMemoryNew Midfall.Bytes.empty,
    (fun i hi => absurd hi (Nat.not_lt_zero i)), (fun i hi => absurd hi (Nat.not_lt_zero i)), ?_⟩
  show (0 : UInt8) ≠ 1
  decide

/-- **FALSIFIER 4 - THE VALUE CLAUSE IS LOAD-BEARING: THE EMITTER'S OPERAND-WIDTH MUTATION.** The
    'pushConstU8' arm decodes ONE operand byte, marks the cached top live and advances the cursor by
    ONE ('GenAstQvm.lean:105'). Widen the operand to two bytes and the arm lands the cursor on the
    segment end while the word it computed is not on the operand stack at all. The block below is that
    arm reduced to the two effects the contract can observe - the cursor and the cached top - run on the
    two-byte window '[PUSH_CONST_U8, 1]' over the table '[7, 31]'. Every other clause of the post
    (outcome, cursor, stack base, both window bases) the mutant satisfies; it is refused for the one
    thing it got wrong. -/
theorem qinterpRefines_falsifier_operand_width {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    ¬ QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun _ _ _ => True)
      [] [yset "q_top" (ylit 7), yset "q_pc" (ylit 2)] [qOpPushConstU8, 1] [7, 31] := by
  intro H
  set V₀ := segmentV (c := c) (g := g) (program := program) ⟨0, 2, 0, 2⟩ 0 false
  set V₁ := VEnv.setMany (VEnv.setMany V₀ ["q_top"] [7]) ["q_pc"] [2]
  have hrun : ExecStmts (Bridge.Dialect c g) [] V₀ EvmState.init
      [yset "q_top" (ylit 7), yset "q_pc" (ylit 2)] V₁ EvmState.init .normal := by
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := VEnv.setMany V₀ ["q_top"] [7])
      (st1 := EvmState.init) ?_
      (Step.seqCons (D := Bridge.Dialect c g) (V1 := V₁) (st1 := EvmState.init) ?_ Step.seqNil)
    · exact Step.assignVal (D := Bridge.Dialect c g) (vals := [7]) Step.lit (by rfl)
    · exact Step.assignVal (D := Bridge.Dialect c g) (vals := [2]) Step.lit (by rfl)
  have h := H ⟨0, 2, 0, 2⟩ (quotientRefMemoryNew Midfall.Bytes.empty)
      (inWindow_exhibit 0 2 (by decide) : QSegment.inWindow ⟨0, 2, 0, 2⟩) V₀ EvmState.init
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, trivial⟩ V₁ EvmState.init .normal hrun
  cases h with
  | inl h => exact absurd h.1 (by decide)
  | inr h =>
      obtain ⟨_, _, _, htop, _⟩ := h.2
      obtain ⟨h1, _⟩ := htop
      have h0 : VEnv.get V₁ "q_has_top" = some (0 : U256) := rfl
      rw [h0] at h1
      exact absurd h1 (by decide : ¬ ((some (0 : U256) : Option U256) = some 1))

/-! ### 9. THE ACCEPTANCE PRINTS -/

/-! THE CONTRACT IS PARAMETRIC IN THE PROGRAM AND THE BLOCK: 'interp' is a binder of the contract, and
    the row quantifies over every 'PartialCtx', every 'QuotientProgram' and every template-constant
    table. No fixture name appears in either type. -/
#check @Midfall.Lowering.QuotientInterp.QInterpRefinesShape
#check @Midfall.Lowering.QuotientInterp.QInterpRefines
#check @Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop_retired
#check @Midfall.Lowering.QuotientInterp.AtSegment
#check @Midfall.Lowering.QuotientInterp.qinterpTop
#check @Midfall.Lowering.QuotientInterp.Agrees

#print axioms Midfall.Lowering.QuotientInterp.qinterp_hypotheses_together
#print axioms Midfall.Lowering.QuotientInterp.qinterp_AtSegment_is_the_prologue_registers
#print axioms Midfall.Lowering.QuotientInterp.qinterp_satisfied_by_the_fail_closed_block
#print axioms Midfall.Lowering.QuotientInterp.qinterpRefines_falsifier_revert_disjunct
#print axioms Midfall.Lowering.QuotientInterp.qinterpRefines_falsifier_no_fallthrough
#print axioms Midfall.Lowering.QuotientInterp.qinterpRefines_falsifier_window_bound
#print axioms Midfall.Lowering.QuotientInterp.qinterpRefines_falsifier_operand_width


/-! ### 10. THE REPAIRED CONTRACT (QFIX): 'QInterpRefines' PLUS ROWFALSE'S THREE GUARDS

**THIS SECTION ADDS A NEW 'Prop' ALONGSIDE THE REFUTED ROW. IT DOES NOT AMEND IT.** The committed
'QInterpRefines' (section 3) and the sorried row 'qinterpRefines_qvmLoop' (section 5) are
UNTOUCHED here: no hypothesis was added to a row, to 'ValidV3', to a bundle or to the root (RULES),
and the refuted row kept its sorry - deleting it is the human ruling W13 reserves, because it moves
SORRY.md, the 375-fragment fingerprint pin and the 'kat_gate.py' note that names this hole. What
follows is the repair ROWFALSE asked for, STATED and TESTED, so the human can rule on each guard
separately instead of on a paragraph.

**UPDATE (D-QVM2, EXECUTED IN A LATER COMMIT): the ruling landed.** The row's sorry and its register
row are gone and the retired text survives as 'qinterpRefines_qvmLoop_retired' (section 5). The
replacement is 'QInterpRefinesSegment' (section 11): it reuses guards 1, 2 and 3a of this section
VERBATIM and replaces guard 3b with D-QVM2's whole-segment stack-safety certificate. Nothing else in
this section was edited beyond this note.

ROWFALSE proved the row's universal closure FALSE ('QuotientRows.lean' sections 11 and 12) and named
three candidate repairs: the window no-wrap, the table agreement, and a stack/cached-top
correspondence in the pre. This section states all three - and splits the third into the two clauses
the material actually needs, because they do different work:

  * **GUARD 1 ('QWindowNoWrap')** - 's.base + s.exprEnd < 2^256'. 'AtSegment' writes 'q_pc' and 'q_end'
    as 256-bit words, so without this the two registers WRAP, the guard 'q_pc < q_end' is false, and
    the loop exits normally having run no arm while the reference errors. This is ROWFALSE's artefact
    1, and it is the R5 'usize'-to-'Nat' root cause one more time.
  * **GUARD 2 ('QTableAgrees')** - every emitted opcode label equals the reference's own 'qOpX'
    constant for that arm. The card asked for agreement "for the arms in play"; the full 31-way form
    is stated because it is decidable, it HOLDS at the default table ('QTableAgrees_default', proved
    by 'decide' over the pairs), and it is the form the human can weaken clause by clause. 'PG_limbCountAgrees'
    (QuotientArms.lean:4425) is the limb-count member of the same family and is left where it is.
  * **GUARD 3a ('QPreCachedTop')** - the pre pins the emitted cached top: 'q_has_top = 0' and 'q_top'
    bound. This is what the ARM LEMMAS need and 'AtSegment' does not give: 'qPrePushConst'
    (QuotientLoopCompose.lean:159) asks for 'q_has_top = some 0' and 'q_top = some x', and 'AtSegment'
    deliberately omits both (its own docstring: 'q_top'/'q_has_top' are not there because one
    predicate cannot pin a segment start and a segment end). Without 3a the head arm's contract cannot
    even be fed.
  * **GUARD 3b ('QHeadNoPop')** - the byte at the segment's start is one of the reference's TEN no-pop
    opcodes (the six pushes and the four limb forms), i.e. the reference's first step is defined on
    the EMPTY stack it starts with. This is the correspondence between the emitted cached top and the
    reference's operand stack, and it is the guard that ROWFALSE's second refutation turns on: at the
    DEFAULT table, with the segment '[qOpNeg]' and 'q_has_top = 0', the emitted neg arm runs on a
    garbage cached top and exits NORMALLY while the reference pops an empty stack and ERRORS. Guards
    1 and 2 both HOLD there - so 3b is not decoration, it is the only thing that closes that witness.

**THE REPAIR IS A RELAXATION, NOT AN EXTENSION.** 'qinterpRepaired_of_committed' proves the committed
contract IMPLIES the repaired one: every guard is a hypothesis on the quantified segment, and the only
clause added to the pre ('QPreCachedTop') strengthens the assumption the proof gets, never the
conclusion. So anything provable of the refuted form is provable of this one, and the four witnesses
that refute the refuted form do not apply here (proved in 'QuotientRows.lean' section 13).

**AND IT IS SATISFIABLE.** 'qinterpRepaired_pre_satisfiable' exhibits a segment at which all four
guards and the whole pre hold together, and
'qinterpRepaired_satisfied_by_the_fail_closed_block' exhibits a block that SATISFIES the repaired
contract - so the guards have not been chosen to make the statement vacuously true of an impossible
pre. Whether they are JOINTLY SUFFICIENT for the emitted loop is a separate question, answered at
'QuotientRows.lean' section 13.4: they are not known to be, and the residue is named there. -/

/-- **GUARD 1 - THE WINDOW DOES NOT WRAP.** 'AtSegment' stores 'q_pc' and 'q_end' as 'BitVec.ofNat 256'
    of 's.base + s.cursor' and 's.base + s.exprEnd'. Yul memory is addressed by an unbounded 'Nat' and
    the registers are not, so unless the true end fits in a word the two disagree and the loop's guard
    'q_pc < q_end' is decided by the WRAPPED pair. 'ROWFALSE' artefact 1 is exactly this: at
    's.base = 2^256 - 1' the guard is false, no arm runs, and the reference errors.

    Stated as a hypothesis on the segment, NOT folded into 'AtSegment' - 'AtSegment' is the committed
    predicate and belongs to the refuted row. -/
def QWindowNoWrap (s : QSegment) : Prop := s.base + s.exprEnd < 2 ^ 256

/-- The emitted table's thirty-one opcode labels paired with the reference's own 'qOpX' constants, in
    'qArmNames' order. A list of pairs rather than thirty-one conjuncts so that agreement is one
    'decide'-able proposition and so a rejected clause is a named pair. -/
def qOpcodeAgreementPairs (tcq : QuotientVmTemplateConstants) : List (Nat × Nat) :=
  [(tcq.op.pushConst, qOpPushConst), (tcq.op.pushMemLiteral, qOpPushMemLiteral),
   (tcq.op.pushMemToken, qOpPushMemToken), (tcq.op.pushMemTokenOffset, qOpPushMemTokenOffset),
   (tcq.op.pushMemU16, qOpPushMemU16), (tcq.op.add, qOpAdd), (tcq.op.mul, qOpMul),
   (tcq.op.neg, qOpNeg), (tcq.op.pushConstU8, qOpPushConstU8), (tcq.op.foldMain, qOpFoldMain),
   (tcq.op.foldSelector, qOpFoldSelector), (tcq.op.addConstU8, qOpAddConstU8),
   (tcq.op.mulConstU8, qOpMulConstU8), (tcq.op.addConst, qOpAddConst),
   (tcq.op.mulConst, qOpMulConst), (tcq.op.addMemU16, qOpAddMemU16),
   (tcq.op.mulMemU16, qOpMulMemU16), (tcq.op.addMulMemMemConstU8, qOpAddMulMemMemConstU8),
   (tcq.op.addMulConstU8MemU16, qOpAddMulConstU8MemU16), (tcq.op.addMulMemMem, qOpAddMulMemMem),
   (tcq.op.runAddMulMemMemConstU8, qOpRunAddMulMemMemConstU8),
   (tcq.op.runAddMulConstU8MemU16, qOpRunAddMulConstU8MemU16),
   (tcq.op.affineSum, qOpAffineSum), (tcq.op.nativePermutation, qOpNativePermutation),
   (tcq.op.nativeLookup, qOpNativeLookup), (tcq.op.nativeIdentity, qOpNativeIdentity),
   (tcq.op.lin7, qOpLin7), (tcq.op.bilin7Row, qOpBilin7Row),
   (tcq.op.bilin7Pairwise, qOpBilin7Pairwise), (tcq.op.modarith7, qOpModarith7),
   (tcq.op.pow5, qOpPow5)]

/-- **GUARD 2 - TABLE AGREEMENT.** Every label the emitter puts in its switch is the byte the reference
   's interpreter tests for that arm. Without it a table can label byte 6 'neg' while the reference
    reads it as 'add', and the loop runs an arm the reference does not have. QLOOP's sketch
    ('QuotientLoopCompose.lean:47-62') and ROWFALSE's third witness are this gap; 'PG_limbCountAgrees'
    is the limb-count member of the same family. -/
def QTableAgrees (tcq : QuotientVmTemplateConstants) : Prop :=
  ∀ x ∈ qOpcodeAgreementPairs tcq, x.1 = x.2

/-- **GUARD 2 IS TRUE OF THE DEFAULT TABLE**, computed by 'decide' over the thirty-one pairs - no
    fixture enters a statement (D-P71: this is a theorem ABOUT the default table, which the row
    quantifies over, and it is the evidence that the guard does not exclude the deployment). -/
theorem QTableAgrees_default : QTableAgrees templateConstantsDefault.quotientVm := by
  unfold QTableAgrees
  decide

/-- The byte the loop's first fetch reads: the segment's head, as the reference's
    'bytes.getD idx 0' reads it. -/
def qHeadByte (bytes : List Nat) (s : QSegment) : Nat := bytes.getD s.cursor 0

/-- The reference's NO-POP opcodes: the six pushes ('VmReference.lean:733-757') and the four limb
    forms (':850-866'), each of which pushes onto the stack it is handed. Every other reference opcode
    either pops ('add', 'mul', 'neg', 'pow5', the fused and run forms) or is refused inside an identity
    (the five stream opcodes, ':867-871'). -/
def qNoPopOpcodes : List Nat :=
  [qOpPushConst, qOpPushConstU8, qOpPushMemLiteral, qOpPushMemU16,
   qOpPushMemToken, qOpPushMemTokenOffset, qOpLin7, qOpBilin7Row, qOpBilin7Pairwise,
   qOpModarith7]

/-- **GUARD 3b - THE HEAD STEP NEEDS NO STACK OPERAND.** 'evalQuotientIdentity' starts every identity
    with an EMPTY stack ('VmReference.lean:905'), so the first byte of a segment the reference accepts
    must be one of the ten no-pop opcodes; if it is a popping one the reference errors at
    'popStack' and no post-state exists for the contract's second disjunct. On the emitted side the
    same fact is what makes the arm enabled: the push arms are the ones whose precondition is the
    EMPTY cached top ('qPrePushConst': 'q_has_top = some 0'), and a popping arm run with
    'q_has_top = 0' computes on a garbage 'q_top' and exits normally - which is precisely ROWFALSE's
    witness 2, at the default table and with guard 1 satisfied. -/
def QHeadNoPop (bytes : List Nat) (s : QSegment) : Prop := qHeadByte bytes s ∈ qNoPopOpcodes

/-- **GUARD 3a - THE PRE PINS THE CACHED TOP.** 'AtSegment' pins five registers and deliberately not
    'q_top'/'q_has_top'. The arm lemmas need them: 'qPrePushConst' asks for 'q_has_top = some 0' and
    'q_top = some x'. So the repaired contract's pre carries the correspondence explicitly - the
    cached top is EMPTY at a segment start, which is the emitted image of the reference's empty stack
    (guard 3b is the other half of the same correspondence, read from the program side). -/
def QPreCachedTop {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) : Prop :=
  VEnv.get V "q_has_top" = some (0 : U256) ∧ ∃ x : U256, VEnv.get V "q_top" = some x

/-- **THE REPAIRED CONTRACT.** The committed 'QInterpRefines' with ROWFALSE's three repairs, each a
    NAMED hypothesis of the quantified segment rather than a clause folded into a predicate, so the
    human can accept or reject them one at a time:

  * 'QWindowNoWrap s' - guard 1, the window does not wrap;
  * 'QTableAgrees tcq' - guard 2, the emitted labels are the reference's constants;
  * 'QHeadNoPop bytes s' - guard 3b, the head byte is a reference no-pop opcode;
  * 'QPreCachedTop V' - guard 3a, in the pre: the cached top is empty and bound.

    The post is the committed post, unchanged - same disjunction, same reference call on the same
    slice, same 'Top' and 'AtSegment' positions. The contract is instantiated at the emitter's loop by
    'qinterpRefinesRepaired_qvmLoop' in 'QuotientRows.lean' section 13, which is a THEOREM about the
    guards holding, not a row: the row itself stays sorried and refuted until the human rules.

    Unlike 'QInterpRefines' this is fixed at 'Bridge.Dialect c g' and at 'word := fun w => w', i.e. at
    the row's own instantiation: guards 3a and 3b speak about 'U256' registers and about the
    reference's opcode bytes, so a dialect-generic form would have to parameterise both and say less. -/
def QInterpRefinesRepaired {c : ExternalCalls} {g : ExternalGas}
    (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (interp : Block EVM.Op)
    (reverts : EvmState → Prop)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : EvmState → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → QSegment → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop) : Prop :=
  ∀ (s : QSegment) (mem : QuotientRefMemory),
    s.inWindow → QWindowNoWrap s → QTableAgrees tcq → QHeadNoPop bytes s →
    StmtsContractAll (D := Bridge.Dialect c g) funs interp
      (fun V st => AtSegment V st s ∧ Agrees st mem s ∧ QPreCachedTop (c := c) (g := g) V)
      (fun _ _ V' st' o => (o = .halt ∧ reverts st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity
            ((bytes.drop s.cursor).take (s.exprEnd - s.cursor)) consts mem = .ok (v, mem') ∧
          Top V' st' (BitVec.ofNat 256 v) ∧ AtSegment V' st' s.atEnd))

/-- **THE REPAIR IS A RELAXATION OF THE REFUTED CLAIM, NOT A STRONGER ONE.** Every guard is a
    hypothesis on the quantified segment, and the one clause added to the pre ('QPreCachedTop') makes
    the assumption stronger, never the conclusion. So the committed contract - the refuted row's
    statement - would still imply the repaired form. That is what makes the exercise meaningful: the
    repaired form is not a new demand on the emitter, it is the old demand restricted to the windows,
    tables and start states where the reference and the registers can disagree about nothing. -/
theorem qinterpRepaired_of_committed {c : ExternalCalls} {g : ExternalGas}
    (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (interp : Block EVM.Op)
    (reverts : EvmState → Prop)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : EvmState → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → QSegment → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop)
    (h : QInterpRefines (D := Bridge.Dialect c g) (reverts := reverts) (word := fun w => w)
        (AtSegment := AtSegment) (Top := Top) (Agrees := Agrees) funs interp bytes consts) :
    QInterpRefinesRepaired tcq funs interp reverts bytes consts Agrees AtSegment Top :=
  fun s mem hw _hwrap _htab _hhead V st hpre =>
    h s mem hw V st ⟨hpre.1, hpre.2.1⟩

/-- **THE FOUR GUARDS HOLD TOGETHER.** A contract whose pre is unsatisfiable is worth nothing, and
    four conjoined guards are exactly the shape that risks it. This exhibits, at ANY program and ANY
    reference memory, a legal three-byte window '[PUSH_CONST, 0, 7]' at base 0 whose segment satisfies
    'inWindow', guard 1, guard 2 (at the default table), guard 3b and guard 3a simultaneously, together
    with the five 'AtSegment' register clauses and the three 'Agrees' clauses. PROVED; no
    'native_decide'; no fixture. -/
theorem qinterpRepaired_pre_satisfiable {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (mem : QuotientRefMemory) :
    ∃ (s : QSegment) (V : VEnv (Bridge.Dialect c g)) (st : EvmState),
      s.inWindow ∧ QWindowNoWrap s ∧ QTableAgrees templateConstantsDefault.quotientVm
        ∧ QHeadNoPop [qOpPushConst, 0, 7] s ∧ QPreCachedTop (c := c) (g := g) V
        ∧ AtSegment (c := c) (g := g) (program := program) V st s
        ∧ Agrees [] program.constMptr 0 0 [qOpPushConst, 0, 7] st mem s := by
  refine ⟨⟨0, 3, 0, 3⟩, segmentV (c := c) (g := g) (program := program) ⟨0, 3, 0, 3⟩ 0 false,
    { EvmState.init with memory := fun a => if a = 0 then 1 else if a = 2 then 7 else 0 },
    ⟨inWindow_exhibit 0 3 (by decide), (by decide : (0 : Nat) + 3 < 2 ^ 256),
      QTableAgrees_default, (by decide : qOpPushConst ∈ qNoPopOpcodes), ⟨rfl, 0, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hlen : ({ base := 0, len := 3, cursor := 0, exprEnd := 3 } : QSegment).len = 3 := rfl
      rw [hlen] at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> rfl
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro a ha; exact absurd ha (Nat.not_lt_zero a)

/-- **THE REPAIRED CONTRACT IS SATISFIED, WITH THE REAL PREDICATES.** Same shape as section 7's
    witness 2 and the same block - the fail-closed default the emitted switch runs on an unknown
    opcode - but now under all four guards and with the strengthened pre. Its only runs revert, so the
    post's first disjunct always holds and no guard has to be discharged by the block at all. This is
    the evidence that the repaired form is not vacuous-by-impossible-pre: it is satisfiable by a block
    the emitter really prints, at every window, table and segment whose guards hold. -/
theorem qinterpRepaired_satisfied_by_the_fail_closed_block {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (bytes : List Nat) (consts : List Midfall.Word256)
    (tcq : QuotientVmTemplateConstants) :
    QInterpRefinesRepaired (c := c) (g := g) tcq [] [yexpr (yop Op.revert [ylit 0, ylit 0])]
      Midfall.Lowering.Reverted bytes consts (fun _ _ _ => True)
      (AtSegment (c := c) (g := g) (program := program)) qinterpTop := by
  intro s mem hw hwrap htab hhead V st hpre V' st' o hrun
  have key : Midfall.Yul.WpTac.AllRuns [] V st
      [yexpr (yop Op.revert [ylit 0, ylit 0])]
      (fun _ st' o => o = .halt ∧ Midfall.Lowering.Reverted st') := by
    refine Midfall.Yul.WpTac.allRuns_of_wp 20 ?_
    wp_run
    all_goals (first | exact ⟨rfl, rfl⟩ | rfl)
  exact Or.inl (key V' st' o hrun)

-- The repaired form's own acceptance prints.
#print axioms Midfall.Lowering.QuotientInterp.QTableAgrees_default
#print axioms Midfall.Lowering.QuotientInterp.qinterpRepaired_of_committed
#print axioms Midfall.Lowering.QuotientInterp.qinterpRepaired_pre_satisfiable
#print axioms Midfall.Lowering.QuotientInterp.qinterpRepaired_satisfied_by_the_fail_closed_block
#check @Midfall.Lowering.QuotientInterp.QInterpRefinesRepaired
#check @Midfall.Lowering.QuotientInterp.QWindowNoWrap
#check @Midfall.Lowering.QuotientInterp.QTableAgrees
#check @Midfall.Lowering.QuotientInterp.QHeadNoPop
#check @Midfall.Lowering.QuotientInterp.QPreCachedTop

/-! ### 11. THE REPLACEMENT (D-QVM2): THE CONTRACT OVER A FIXED, VALIDATED SEGMENT

**D-QVM2 IS A SIGNED HUMAN RULING ('design.md:2763-2792', APPROVED 2026-11-21) AND THIS SECTION IS
ITS EXECUTION.** The decision, verbatim: "'qinterpRefines_qvmLoop' is RETIRED under W13 (its negation
is proved). The replacement is a contract over a fixed 'QSegment' 's', with the caller supplying:
(1) 's.inWindow' and the D-QVM1 fit ('s.base + s.exprEnd < 2^256'); (2) full template-table agreement
('tcq' = the table the reference labels come from); (3) a segment stack-safety certificate, the row
counterpart of 'validateQuotientProgram'/'qvm_validated_noBoundsFault' (the validator rejects '[NEG]'
at depth 0, which is exactly BOXD's second refutation); (4) the start state the prologue establishes
('q_sp = program.stackMptr', 'q_has_top = 0)."  'QInterpRefinesSegment' below is that contract: the
four items are FOUR NAMED HYPOTHESES of the quantified segment - items 1, 2 and 3 as hypotheses of
'∀ s', item 4 as the named clause of the pre - and the row's sorry was deleted in this same commit,
which is the consequence D-QVM2 states: "the old row's sorry and its register row are deleted in the
same commit that adds the replacement (W13); the ROWFALSE refutations stay as the W12 falsifiers of
the retired text."

**ALIGNED TO QFIX, NOT A FIFTH FORMULATION.** The card's instruction was to read section 10 and align
to it rather than invent a fifth shape, and that is what this is: 'QInterpRefinesSegment' is
'QInterpRefinesRepaired' with ONE substitution and no other change. Guard 1 ('QWindowNoWrap'), guard 2
('QTableAgrees') and guard 3a are reused VERBATIM - 3a widened only in the direction D-QVM2's item 4
names, so that the pre's fourth clause states 'q_sp = program.stackMptr' beside 'q_has_top = 0'
('QPrologueStart'; 'qPrologueStart_of_AtSegment_and_preCachedTop' proves it is exactly 'AtSegment' plus
guard 3a and nothing more). The one substitution is guard 3b: ROWFALSE's head-only test ('QHeadNoPop',
the FIRST byte is a no-pop opcode) becomes D-QVM2's item 3, a certificate over the WHOLE segment built
from the validator's OWN decoder and stack-effect table. 'qinterpSegment_of_committed' proves the
committed contract implies the replacement, exactly as 'qinterpRepaired_of_committed' proves it of
QFIX's form: a RELAXATION of the refuted claim, not a stronger demand on the emitter.

**WHY ITEM 3 IS A WALK AND NOT A HEAD TEST.** Three facts fix the shape. (i) The validator's own
finish check requires the walk to end at depth 0 ('quotientProgramFinishCheck', VmValidator.lean:866),
because a whole PROGRAM is a sequence of identities each closed by a fold; an IDENTITY segment ends
with the single value 'evalQuotientIdentity' reads off the stack (VmReference.lean:905-908), so the
segment counterpart of the validator ends at depth 1, not 0. (ii) The reference REFUSES the five
stream opcodes inside an identity ('VmReference.lean:861-865', 'streamOpcodeInIdentity'), so the walk
refuses them too - a segment whose head is 'neg' fails on the depth rule and a segment that folds
fails on the domain rule. (iii) The walk is a computable function of the segment's bytes, so each of
ROWFALSE's four witnesses is EXCLUDED BY 'decide' rather than by argument; the four exclusions are
proved in 'QuotientRows.lean' section 14. Item 3 is a hypothesis of the NEW contract, which D-QVM2
authorises; no hypothesis was added to a row, to 'ValidV3', to a bundle or to the root (RULES).

**WHAT ITEM 3 DOES NOT COVER, NAMED RATHER THAN HUSHED.** It is a STACK-safety certificate: opcode
decodability, the reference's identity opcode domain, and the static depth walk. It does not say the
segment's OPERANDS are in range - constant slots inside 'consts', token bases, read windows - which
is phase 2 of the validator ('validateQuotientProgramOperands'), whose two legs SEGLEG refuted; those
facts live in 'Agrees' and in obligation (O3) of 'QuotientRows' section 13.4. Nor does any hypothesis
about a start state discharge the inductive stack correspondence (O2) or the per-arm reference tie
(O3): the guards are what makes the four refutations impossible, not a proof of the loop. -/

/-- The segment's own bytes: the slice the contract's reference call evaluates and the slice the
    stack-safety certificate walks. The same expression the post has always used, named once so the
    certificate and the reference call cannot drift apart. -/
def qSegmentBytes (bytes : List Nat) (s : QSegment) : List Nat :=
  (bytes.drop s.cursor).take (s.exprEnd - s.cursor)

/-- The five stream-level opcodes: a width to the validator, an ERROR to the identity interpreter
    ('VmReference.lean:861-865'). 'Midfall.Lowering.streamIdentityExcluded' (Qvm.lean:1088) is the
    same five; it is spelled again here because 'Qvm.lean' is not in this file's import graph and this
    card does not own it. -/
def qSegmentStreamOpcodes : List Nat :=
  [qOpFoldMain, qOpFoldSelector, qOpNativePermutation, qOpNativeLookup, qOpNativeIdentity]

/-- ONE STEP OF THE SEGMENT STACK WALK, in the validator's own vocabulary: decode the head with
    'decodeByteQuotientInstruction' (VmValidator.lean:846, which bounds-checks the instruction and
    validates token operands), refuse the five stream opcodes, then apply the validator's static
    stack-effect table 'applyQuotientStackEffect' (VmValidator.lean:723) and advance by the decoded
    width. 'none' means NOT CERTIFIED: an undecodable head, a stream opcode, an underflow or a
    violated boundary. Fuel is the segment's own length, sound for the same reason the validator's is
    (its own R10 note at VmValidator.lean:677, and 'validateQuotientProgram' passes 'bytes.length' at
    :877): an accepted instruction is at least one byte, so the walk cannot still be mid-instruction. -/
def qSegmentDepthGo (bytes : List Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, idx, depth =>
      if idx < bytes.length then
        match Midfall.Generator.QuotientValidator.decodeByteQuotientInstruction bytes idx with
        | .ok (op, len) =>
            if op ∈ qSegmentStreamOpcodes then none
            else
              match Midfall.Generator.QuotientValidator.applyQuotientStackEffect op idx depth 0 with
              | .ok (depth', _) => qSegmentDepthGo bytes fuel (idx + len) depth'
              | .error _ => none
        | .error _ => none
      else some depth

/-- **ITEM 3 - THE SEGMENT STACK-SAFETY CERTIFICATE (D-QVM2).** The walk above, run over the
    segment's bytes from an EMPTY stack, ends with EXACTLY ONE value on it: the value the reference
    returns. 'some 1' is the whole certificate - decodable heads, no stream opcode, no underflow, no
    boundary violation, and the identity's end depth. This is the row counterpart of
    'validateQuotientProgram' that D-QVM2 asks for, and it is what rejects '[NEG]' at depth 0:
    'neg' needs one operand and the segment starts with none. -/
def QSegmentStackSafe (bytes : List Nat) (s : QSegment) : Prop :=
  qSegmentDepthGo (qSegmentBytes bytes s) (qSegmentBytes bytes s).length 0 0 = some 1

/-- **ITEM 4 - THE START STATE THE PROLOGUE ESTABLISHES (D-QVM2).** 'q_sp = program.stackMptr' (the
    operand stack empty at the segment's start, which is also a conjunct of 'AtSegment') and
    'q_has_top = 0' with the cached top bound - QFIX's guard 3a, plus the 'q_sp' clause item 4 names.
    It lives in the PRE because 'StmtsContractAll' quantifies over the start state internally: that is
    where a contract puts a start-state requirement, and it is a hypothesis of the NEW contract, not a
    patch to the old row. -/
def QPrologueStart {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) : Prop :=
  VEnv.get V "q_sp" = some (BitVec.ofNat 256 program.stackMptr) ∧
    VEnv.get V "q_has_top" = some (0 : U256) ∧ ∃ x : U256, VEnv.get V "q_top" = some x

/-- **ITEM 4 IS 'AtSegment' PLUS QFIX'S GUARD 3A AND NOTHING ELSE.** The bridge that shows the
    replacement adds no start-state content beyond what section 10 already required: 'q_sp' comes from
    the fifth conjunct of 'AtSegment', the cached-top clauses are guard 3a verbatim. -/
theorem qPrologueStart_of_AtSegment_and_preCachedTop {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (s : QSegment)
    (hseg : AtSegment (c := c) (g := g) (program := program) V st s)
    (htop : QPreCachedTop (c := c) (g := g) V) :
    QPrologueStart (c := c) (g := g) program V :=
  ⟨hseg.2.2.2.2, htop.1, htop.2⟩

/-- **THE REPLACEMENT CONTRACT (D-QVM2).** Over a FIXED 'QSegment' 's', with the four caller-supplied
    items as named hypotheses:

  * ITEM 1 's.inWindow' and 'QWindowNoWrap s' - the segment lies in the window and the window does not
    wrap the 256-bit cursor word. NOTE, because the card asks for it: at the row's instantiation item
    1's second half is NOT a burden on the caller - 'windowFit_of_programWindow'
    ('QuotientRows.lean' section 3b) derives 'QWindowNoWrap s' from 'programFits', so for a segment at
    the program's own window it is a THEOREM OF 'ValidV3'. It is stated as a hypothesis here because
    the contract is generic in the window, exactly as QFIX's guard 1 is.
  * ITEM 2 'QTableAgrees tcq' - full template-table agreement: 'tcq' is the table the reference's
    opcode labels come from, all thirty-one pairs, proved true of the default table.
  * ITEM 3 'QSegmentStackSafe bytes s' - the segment stack-safety certificate above.
  * ITEM 4 'QPrologueStart program V' - the start state the prologue establishes, in the pre beside
    'AtSegment' and 'Agrees'.

    The post is the committed post: same disjunction, same reference call on the same slice (now named
    'qSegmentBytes'), same 'Top' and 'AtSegment' positions. Like section 10's form it is fixed at the
    row's own instantiation ('Bridge.Dialect c g', 'word := fun w => w'), because items 3 and 4 speak
    about 'U256' registers and reference opcode bytes. -/
def QInterpRefinesSegment {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (interp : Block EVM.Op)
    (reverts : EvmState → Prop)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : EvmState → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → QSegment → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop) : Prop :=
  ∀ (s : QSegment) (mem : QuotientRefMemory),
    s.inWindow → QWindowNoWrap s → QTableAgrees tcq → QSegmentStackSafe bytes s →
    StmtsContractAll (D := Bridge.Dialect c g) funs interp
      (fun V st => AtSegment V st s ∧ Agrees st mem s ∧
        QPrologueStart (c := c) (g := g) program V)
      (fun _ _ V' st' o => (o = .halt ∧ reverts st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity (qSegmentBytes bytes s) consts mem = .ok (v, mem') ∧
          Top V' st' (BitVec.ofNat 256 v) ∧ AtSegment V' st' s.atEnd))

/-- **THE REPLACEMENT IS A RELAXATION OF THE REFUTED CLAIM, NOT A STRONGER ONE.** The committed
    contract - the retired row's statement - still implies it, by the same one-line argument QFIX used:
    items 1, 2 and 3 are hypotheses on the quantified segment and item 4 strengthens what the proof is
    GIVEN, never what the caller must accept. So anything provable of the refuted form is provable of
    the replacement, and the four witnesses that refute the refuted form do not apply here. -/
theorem qinterpSegment_of_committed {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (interp : Block EVM.Op)
    (reverts : EvmState → Prop)
    (bytes : List Nat) (consts : List Midfall.Word256)
    (Agrees : EvmState → QuotientRefMemory → QSegment → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → QSegment → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop)
    (h : QInterpRefines (D := Bridge.Dialect c g) (reverts := reverts) (word := fun w => w)
        (AtSegment := AtSegment) (Top := Top) (Agrees := Agrees) funs interp bytes consts) :
    QInterpRefinesSegment (c := c) (g := g) program tcq funs interp reverts bytes consts
      Agrees AtSegment Top :=
  fun s mem hw _hwrap _htab _hsafe V st hpre =>
    h s mem hw V st ⟨hpre.1, hpre.2.1⟩

/-- **THE OUTPUT PREDICATE THE FOLD ARMS PRODUCE - D-QVM2'S OPEN DESIGN POINT, STATED AND ANSWERED.
    The decision says the retired row's 'Top := qinterpTop' "is not the output of a segment ending in
    'foldMain'/'foldSelector': those arms consume the cached top and write the accumulator at
    'evalNumerMptr', so the replacement must state the output predicate the fold arms actually
    produce", against the reference's 'evalQuotientIdentity' value, and report. THE ANSWER, AND IT IS
    A FINDING ABOUT THE DECISION RATHER THAN A CHOICE OF PREDICATE: there is no such reference value.
    'evalQuotientIdentityStep' REFUSES all five stream opcodes inside an identity
    ('VmReference.lean:861-865', 'streamOpcodeInIdentity'), so 'evalQuotientIdentity' returns '.error'
    on EVERY segment that ends in a fold - 'qdvm2_foldSegment_refused' in 'QuotientRows' section 14
    proves it at the byte level - and the accumulator slot 'evalNumerMptr' does not appear anywhere in
    the read-only reference (QuotientArms.lean:5502-5530 names the reference-side card, QSTREAM, that
    would have to exist first). So the replacement does NOT state a fold output: item 3's certificate
    refuses the fold opcodes, which is exactly the condition under which 'qinterpTop' IS the emitted
    image of the reference's value - the segment ends with one word on the reference stack and one
    live cached top. The fold predicate is stated here for the record, so the design point is closed
    with a named predicate and a named blocker rather than left as prose: after 'qArmBodyFoldMain'
    ('GenAstQvm.lean:292-295') the cached top is CLEARED and the accumulator word at
    'program.evalNumerMptr' holds 'addmod (mulmod acc y) x' for the consumed top 'x'. When QSTREAM
    lands, 'Top' instantiates to this at a stream contract; nothing here pre-empts it. -/
def qinterpFoldTop {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (acc : U256) : Prop :=
  VEnv.get V "q_has_top" = some (0 : U256) ∧ loadWord st.memory program.evalNumerMptr = acc

/-! THE REPLACEMENT'S OWN ACCEPTANCE PRINTS. -/
#check @Midfall.Lowering.QuotientInterp.QInterpRefinesSegment
#check @Midfall.Lowering.QuotientInterp.QSegmentStackSafe
#check @Midfall.Lowering.QuotientInterp.QPrologueStart
#check @Midfall.Lowering.QuotientInterp.qinterpFoldTop
#check @Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop_retired
#print axioms Midfall.Lowering.QuotientInterp.qinterpSegment_of_committed
#print axioms Midfall.Lowering.QuotientInterp.qPrologueStart_of_AtSegment_and_preCachedTop

-- ('#assert_axioms' is not available in this file: it comes from 'Midfall.Tools.Done', which this file
-- does not import and this card will not add. The asserted form of these two prints is in
-- 'QuotientRows.lean' section 14, which does import it.)

