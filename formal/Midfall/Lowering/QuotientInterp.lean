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

/-- **THE CONTRACT AT THE EMITTER'S LOOP, FOR EVERY PROGRAM (card step 2).** 'GenAst.qvmLoop ctx
    program tcq' is the interpreter loop OBJ.15's structured emitter prints - the opcode fetch
    'qvmLoopPre', the switch over 'qvmOpcodeArms ++ qvmNativeArms ++ qvmFoldArms' in template order,
    and the fail-closed default - and this is the one-off lemma route B needs. It is quantified over
    EVERY context, EVERY 'QuotientProgram' and EVERY template-constant table: no fixture appears, and
    the window is the program's own ('base = program.programMptr', 'len = program.len'), which is
    what the prologue writes.

    REGISTERED HOLE: this is ROW.Q's, not T3.10's - the card is a statement card and its deliverable
    is the contract plus W12 evidence. QPROBE is the measurement that says it cannot be discharged by
    unrolling; the arm families of section 6 are the decomposition it will have to follow. -/
theorem qinterpRefines_qvmLoop {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (funs : FunEnv (Bridge.Dialect c g)) (bytes : List Nat) (consts : List Midfall.Word256)
    (frameBase frameWords : Nat) :
    QInterpRefines (D := Bridge.Dialect c g)
      (reverts := Midfall.Lowering.Reverted) (word := fun w => w)
      (AtSegment := AtSegment program) (Top := qinterpTop)
      (Agrees := fun st mem s => Agrees consts program.constMptr frameBase frameWords bytes st mem s)
      funs [GenAst.qvmLoop ctx program tcq] bytes consts := by
  sorry

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
#check @Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop
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
