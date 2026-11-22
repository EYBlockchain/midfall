-- |
-- Midfall.Lowering.QuotientLoopCompose
--
-- QLOOP: compose the landed per-arm value refinements into the EMITTED DISPATCH, and say exactly
-- where that stops short of 'qinterpRefines_qvmLoop' (T3.10 / ROW.Q). No sorry is introduced here
-- and none is removed: the row stays sorried, at 'QuotientInterp.lean:253', for the reasons in
-- section 6 - none of which is a proof gap this card could close.
--
-- WHAT LANDED. The 25 'qArmValueAll_X' triples each constrain ONE arm body. The row constrains the
-- LOOP, whose body ends in one 'Stmt.switch' over the emitter's own 31-entry case list. The step
-- between them is a SELECTION fact: that 'selectSwitch' at the fetched word runs the arm whose
-- triple you hold. That step is what this file proves:
--
--   * 'qSwitch_selects_pushConst' - the emitter's OWN case list, at a SYMBOLIC template table,
--     selects 'qArmBodyPushConst' at the label 'tcq.op.pushConst'. This is the first time
--     'selectSwitch' is made to reduce on the emitter's list rather than on a list handed in as a
--     parameter (Q1 got only as far as a singleton, QuotientFrame.lean:748, and QEMIT4 reported that
--     reducing the emitter's list dies at whnf). 'selectSwitch_head' + 'find?_head' buy it back, and
--     they need only the HEAD entry.
--   * 'qinterpSwitch_pushConst' - that selection composed with 'qArmValueAll_pushConst' through
--     'StmtContractAll.switch' and the vendored 'Step.block' (BigStep.lean:225-227): THE EMITTED
--     SWITCH SATISFIES AN ARM'S VALUE CONTRACT. First composition of a triple with the dispatch.
--   * 'qinterpSwitch_of_selects' - the general schema the remaining arms plug into: one selection
--     hypothesis plus the arm triple gives the switch contract. Section 6 says what it costs to
--     discharge that hypothesis for the other 30 arms and why the answer is a human ruling.
--
-- WHAT THIS FILE DOES NOT DO, AND WHY IT IS A HUMAN DECISION.
--
--   (1) THE LIMB ARMS (lin7, bilin7Row, bilin7Pairwise, modarith7). Their emitted bodies fold
--       'tcq.limbCount'; the reference folds the global 'quotientVmLimbs', which the KAT pins only
--       for the default table. 'PG_limbCountAgrees' already carries that and is already escalated.
--       LIN7 established the row cannot absorb it, so nothing here does either: no hypothesis was
--       added to the row, to 'ValidV3', to a bundle or to the root.
--   (2) THE OTHER 30 ARMS' SELECTION. 'selectSwitch' walks the list with 'decide (cv = label)', so
--       an arm at position i is reachable only once the i PRECEDING labels are known to differ from
--       the scrutinee. For a symbolic 'tcq' those are facts about the template table -
--       'tcq.op.pushConst ≠ tcq.op.pushMemLiteral' and roughly 460 siblings - which nothing in the
--       tree proves and which the KAT pins only for the default table. THE HEAD ARM IS THE ONLY ONE
--       THAT NEEDS NO SUCH FACT. Same class of table-agreement hypothesis as (1).
--   (3) THE REFERENCE SIDE. Nothing here mentions 'evalQuotientIdentity'. The 25 triples are
--       EMITTED-SIDE contracts: 'qArmValueAll_X' says what the Yul arm leaves in q_top and
--       'qStepValue_X' says what the reference step pushes, and NO THEOREM IN THE TREE YET SAYS THE
--       TWO ARE THE SAME WORD. THE COUNT OF PROVED LOOP-TO-REFERENCE LINKAGES IS UNCHANGED BY THIS
--       FILE AND REMAINS ZERO FOR THE ARMS. QuotientFoldTie's two ties are to
--       'evalQuotientStreamStep', a different function from the row's 'evalQuotientIdentity'.
--       armcount's 'reference-tied 23' is a name intersection, and MOD7G already said so.
-- A DEFECT FOUND WHILE COMPOSING - REPORTED, NOT EXHIBITED IN LEAN, NOT REPAIRED. The contract's
-- post lets a run satisfy the row by REVERTING whatever the reference does, so a table whose labels
-- disagree with the reference's global 'qOpX' constants satisfies the row by reverting more. But a
-- table that agrees with SOME labels and not others can run an arm whose reference step is a
-- DIFFERENT opcode. Take 'tcq.op.pushConstU8 := qOpPushConstU8' and 'tcq.op.add := 200' (say) and the
-- segment '[qOpAdd, k]': the emitted switch finds no earlier match, runs the PUSH-CONST arm to a
-- NORMAL exit with 'q_top = consts.getD k 0' and 'q_pc = q_end', while 'evalQuotientIdentity
-- [qOpAdd, k] consts mem' pops an empty stack and ERRORS - so neither disjunct of the post holds and
-- 'qinterpRefines_qvmLoop' looks FALSE for that table, not merely unprovable. The repair hypothesis
-- ('tcq.op = the reference's opcode constants', or 'tcq = quotientVmTemplateConstants') is exactly
-- the kind of hypothesis the rules forbid adding to a row, so it belongs to the human ruling that
-- 'PG_limbCountAgrees' already escalated - of which this is the general case: limbCount is one field
-- of the table, and the opcode labels are thirty-one more. NOT EXHIBITED HERE because exhibiting it
-- needs a concrete NORMAL run of the emitted loop, which is (4)'s loop-induction work, not this
-- file's; the reasoning above is a report, not a theorem, and no Lean statement in this file depends
-- on it being right.
--
-- AXIOM PROVENANCE, PRINTED NOT ASSERTED. 'stmtsContractAll_singleton' - the only lemma here that
-- does not mention the emitter's list - is [propext]. Every other print carries
-- [propext, Classical.choice, Quot.sound], and the choice is INHERITED FROM THE EMITTER, not
-- introduced by these proofs: 'qvmLoop_body' (QuotientFrame.lean:780) is proved by 'rfl' and prints
-- the same three, because 'qvmOpcodeArms' itself contains a classically-resolved 'Decidable'. Any
-- statement that names 'qCaseList' inherits it. 'selectSwitch_head' and 'find?_head', the two lemmas
-- these proofs actually run on, are axiom-free. No 'termination_by' clause is involved here.
--
--   (4) THE LOOP ITSELF. 'qvmLoop' is a 'Stmt.forLoop' with guard 'q_pc < q_end', so the row needs
--       an induction over iterations carrying the reference's step-fold
--       ('evalQuotientIdentityLoop_step', 'evalQuotientIdentity_one') inside the invariant, plus the
--       fetch bridge from 'AgreesProgram' to 'byte(0, mload q_pc)'. That is ROW.Q proper.

import Midfall.Lowering.QuotientInterp
import Midfall.Lowering.GenAstQvm
import Midfall.LoweringV3.QuotientFrame
import Midfall.LoweringV3.QuotientArms
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Lowering.QuotientLoopCompose

open YulSemantics YulSemantics.EVM Midfall Midfall.Generator Midfall.Lowering
open Midfall.Yul Midfall.Yul.Bridge Midfall.Lowering.QuotientInterp
open Midfall.Lowering.GenAst
open Midfall.LoweringV3.QuotientFrame

/-! ### 1. THE EMITTER'S DISPATCH, NAMED -/

/-- The case list 'GenAst.qvmLoop' puts in its switch, in the emitter's own order: the 26 opcode
    arms, then the 3 native callbacks, then the 2 fold arms. The same term the loop uses, named so a
    lemma can talk about it; 'qvmLoop_switch_body' is the 'rfl' that says so. -/
def qCaseList (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : List (Literal × Block EVM.Op) :=
  qvmOpcodeArms ctx program tcq ++ qvmNativeArms ctx program tcq ++ qvmFoldArms ctx program tcq

/-- The switch statement the loop body ends with, fail-closed default included. -/
def qLoopSwitch (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) : Stmt EVM.Op :=
  Stmt.switch (yvar "q_op") (qCaseList ctx program tcq)
    (some [yexpr (ycall "q_program_fail" [])])

/-- The loop restated through the two names above: 'rfl', and the equation every arm composition is
    read under. 'qvmLoop_body' (QuotientFrame.lean:780) is the same fact with the switch spelled out. -/
theorem qvmLoop_switch_body (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) :
    GenAst.qvmLoop ctx program tcq =
      Stmt.forLoop [] (yop EVM.Op.lt [yvar "q_pc", yvar "q_end"]) []
        (GenAst.qvmLoopPre ++ [qLoopSwitch ctx program tcq]) := rfl

/-- **THE EMITTER'S CASE LIST IS A CONS, AND ITS HEAD IS THE 'pushConst' ARM.** Under the all-flags
    hypothesis only. This is what makes the head arm reachable by 'find?_head' without any fact about
    the other thirty labels. -/
theorem qCaseList_cons (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    ∃ tail, qCaseList ctx program tcq =
      (Literal.number tcq.op.pushConst, GenAst.qArmBodyPushConst ctx program tcq) :: tail := by
  refine ⟨(qvmOpcodeArms ctx program tcq).tail ++ qvmNativeArms ctx program tcq
      ++ qvmFoldArms ctx program tcq, ?_⟩
  show qvmOpcodeArms ctx program tcq ++ qvmNativeArms ctx program tcq
      ++ qvmFoldArms ctx program tcq = _
  unfold qvmOpcodeArms
  simp only [hou, opUsageAllOn]
  simp

/-! ### 2. THE EMITTER'S OWN LIST SELECTS ITS HEAD ARM, AT A SYMBOLIC TABLE -/

/-- **THE FIRST REDUCTION OF THE EMITTER'S CASE LIST.** 'selectSwitch' at the word
    'BitVec.ofNat 256 tcq.op.pushConst' runs 'qArmBodyPushConst' - not at a list handed in as a
    parameter (as far as Q1 got, QuotientFrame.lean:748) but at the emitter's own 31-entry list, with
    the template table SYMBOLIC and only the flag hypothesis 'program.opUsage = opUsageAllOn'. The
    head short-circuits 'List.find?', so nothing about the other 30 labels is needed; section 6
    prices them. -/
theorem qSwitch_selects_pushConst {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (hou : program.opUsage = opUsageAllOn) (dflt : Block EVM.Op) :
    selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.op.pushConst)
        (qCaseList ctx program tcq) (some dflt) =
      GenAst.qArmBodyPushConst ctx program tcq := by
  refine selectSwitch_head (D := Bridge.Dialect c g) _ _
    (Literal.number tcq.op.pushConst, GenAst.qArmBodyPushConst ctx program tcq) _ ?_
  obtain ⟨tail, htail⟩ := qCaseList_cons ctx program tcq hou
  rw [htail]
  refine find?_head _ _ _ ?_
  simpa using (decide_litValue_number_eq_self (c := c) (g := g) tcq.op.pushConst)

/-! ### 3. THE ARM CONTRACTS, NAMED -/

/-- The 'pushConst' arm's precondition, as 'QuotientArms.lean:3072' states it, named so the
    composition can refer to it once instead of copying a seven-clause lambda. -/
def qPrePushConst {c : ExternalCalls} {g : ExternalGas} (pc cb sp x : U256) (b v : Nat)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  VEnv.get V "q_pc" = some pc ∧
  VEnv.get V "q_sp" = some sp ∧
  VEnv.get V "q_has_top" = some 0 ∧
  VEnv.get V "q_top" = some x ∧
  VEnv.get V "q_const_mptr" = some cb ∧
  ((loadWord st.memory pc.toNat) >>> 240) = BitVec.ofNat 256 b ∧
  loadWord st.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat = BitVec.ofNat 256 v

/-- The 'pushConst' arm's postcondition, as 'QuotientArms.lean:3072' states it. -/
def qPostPushConst {c : ExternalCalls} {g : ExternalGas} (pc cb _sp _x : U256) (b v : Nat)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  o = .normal ∧
  st' = touchMemory (touchMemory st pc.toNat 32) (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat 32 ∧
  V' = VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top"
    (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)

/-- The 'pushConst' triple, at ANY function environment, in the named form. The 'funs' quantifier is
    what lets the composition instantiate it under the block's hoisted scope. -/
theorem qArmValueAll_pushConst_any {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat)
    (funs' : FunEnv (Bridge.Dialect c g)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs' (GenAst.qArmBodyPushConst ctx program tcq)
      (qPrePushConst (c := c) (g := g) pc cb sp x b v)
      (qPostPushConst (c := c) (g := g) pc cb sp x b v) :=
  Midfall.LoweringV3.QuotientArms.qArmValueAll_pushConst hc hg ctx program tcq funs' pc cb sp x b v hguard

/-! ### 4. THE COMPOSITION SCHEMA: SELECTION + ARM TRIPLE = SWITCH CONTRACT -/

/-- A one-statement block is a contract for the statement. Needed because the row's
    'StmtsContractAll' sees '[qLoopSwitch ..]' while 'StmtContractAll.switch' concludes about the
    statement alone. -/
theorem stmtsContractAll_singleton {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {s : Stmt D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtContractAll (D := D) funs s pre post) :
    StmtsContractAll (D := D) funs [s] pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · have hpost := h V st hpre V₁ st₁ .normal h₁
    cases h₂
    exact hpost
  · exact h V st hpre V' st' o h₁

/-- **THE SCHEMA EVERY REMAINING ARM PLUGS INTO.** One arm's triple, quantified over the function
    environment, plus the fact that the emitted switch selects that arm's block at the fetched word,
    gives a contract for the SWITCH STATEMENT of the loop body.

    The 'restore' in the post is not decoration and is not a weakening: the vendored rule runs a
    switch's arm through 'Stmt.block' (BigStep.lean:225-227), so the arm's writes reach the loop only
    after the block's scope is popped. The post therefore says the outer environment IS the restored
    inner one and the arm's equation holds of the inner one - exactly what 'Step.block' gives and
    nothing more. Every hypothesis is on THIS lemma: no row, bundle, 'ValidV3' or the root gains one. -/
theorem qinterpSwitch_of_selects {c : ExternalCalls} {g : ExternalGas}
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (cv : U256) (body : Block EVM.Op)
    (funs : FunEnv (Bridge.Dialect c g))
    {pre : VEnv (Bridge.Dialect c g) → EvmState → Prop}
    {post : VEnv (Bridge.Dialect c g) → EvmState → VEnv (Bridge.Dialect c g) → EvmState →
      Outcome → Prop}
    (harm : ∀ funs', StmtsContractAll (D := Bridge.Dialect c g) funs' body pre post)
    (hsel : selectSwitch (Bridge.Dialect c g) cv (qCaseList ctx program tcq)
        (some [yexpr (ycall "q_program_fail" [])]) = body) :
    StmtContractAll (D := Bridge.Dialect c g) funs (qLoopSwitch ctx program tcq)
      (fun V st => VEnv.get V "q_op" = some cv ∧ pre V st)
      (fun V st V' st' o => ∃ Vb, V' = restore V Vb ∧ post V st Vb st' o) := by
  refine StmtContractAll.switch ?_ ?_
  · intro V st cv₁ st₁ hpre heval V' st' o hbody
    -- 'Step.var': the fetched word IS the binding of 'q_op', in the same state, and 'cases'
    -- substitutes it for the schema's 'cv', so 'hsel' applies as it stands.
    cases heval with
    | var hget =>
        have hcv : cv₁ = cv := Option.some.inj (hget.symm.trans hpre.1)
        subst hcv
        rw [hsel] at hbody
        cases hbody with
        | block hinner =>
            refine ⟨_, rfl, harm (hoist (Bridge.Dialect c g) body :: funs) V st hpre.2
              _ _ _ hinner⟩
  · intro V st st₁ hpre heval
    cases heval

/-! ### 5. THE FIRST COMPOSED ARM: THE EMITTED SWITCH SATISFIES PUSHCONST'S CONTRACT -/

/-- **THE COMPOSITION, LANDED.** The emitted switch of the interpreter loop - the emitter's own
    31-entry case list with its fail-closed default, at a SYMBOLIC template table - satisfies the
    'pushConst' arm's value refinement: started with 'q_op' fetched to 'tcq.op.pushConst' and the
    arm's precondition holding, every run ends normally with the arm's postcondition, restored
    through the block's scope. This is 'qArmValueAll_pushConst' lifted from one opcode's body to the
    dispatch the loop actually runs. -/
theorem qinterpSwitch_pushConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (hou : program.opUsage = opUsageAllOn)
    (funs : FunEnv (Bridge.Dialect c g))
    (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    StmtContractAll (D := Bridge.Dialect c g) funs (qLoopSwitch ctx program tcq)
      (fun V st => VEnv.get V "q_op" = some (BitVec.ofNat 256 tcq.op.pushConst) ∧
        qPrePushConst (c := c) (g := g) pc cb sp x b v V st)
      (fun V st V' st' o => ∃ Vb, V' = restore V Vb ∧
        qPostPushConst (c := c) (g := g) pc cb sp x b v V st Vb st' o) :=
  qinterpSwitch_of_selects (c := c) (g := g) ctx program tcq
    (BitVec.ofNat 256 tcq.op.pushConst) (GenAst.qArmBodyPushConst ctx program tcq) funs
      (fun funs' => qArmValueAll_pushConst_any hc hg ctx program tcq pc cb sp x b v hguard funs')
      (qSwitch_selects_pushConst (c := c) (g := g) ctx program tcq hou
        [yexpr (ycall "q_program_fail" [])])

/-- The same composition as a BLOCK contract, which is the shape the loop proof consumes: the loop
    body's switch is one statement of the block 'qvmLoopPre ++ [qLoopSwitch ..]'. -/
theorem qinterpSwitch_pushConst_block {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (hou : program.opUsage = opUsageAllOn)
    (funs : FunEnv (Bridge.Dialect c g))
    (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    StmtsContractAll (D := Bridge.Dialect c g) funs [qLoopSwitch ctx program tcq]
      (fun V st => VEnv.get V "q_op" = some (BitVec.ofNat 256 tcq.op.pushConst) ∧
        qPrePushConst (c := c) (g := g) pc cb sp x b v V st)
      (fun V st V' st' o => ∃ Vb, V' = restore V Vb ∧
        qPostPushConst (c := c) (g := g) pc cb sp x b v V st Vb st' o) :=
  stmtsContractAll_singleton
    (qinterpSwitch_pushConst hc hg ctx program tcq hou funs pc cb sp x b v hguard)

/-- The selection fact restated where it matters: the block the emitted switch RUNS at the
    'pushConst' opcode is the block 'qArmValueAll_pushConst' constrains. The one place the
    identification (QEMIT4) and the value half (QVAL) meet. -/
theorem qinterpSwitch_selectedBlock_pushConst {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (hou : program.opUsage = opUsageAllOn)
    (funs : FunEnv (Bridge.Dialect c g))
    (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (selectSwitch (Bridge.Dialect c g) (BitVec.ofNat 256 tcq.op.pushConst)
        (qCaseList ctx program tcq) (some [yexpr (ycall "q_program_fail" [])]))
      (qPrePushConst (c := c) (g := g) pc cb sp x b v)
      (qPostPushConst (c := c) (g := g) pc cb sp x b v) := by
  rw [qSwitch_selects_pushConst (c := c) (g := g) ctx program tcq hou
    [yexpr (ycall "q_program_fail" [])]]
  exact qArmValueAll_pushConst_any hc hg ctx program tcq pc cb sp x b v hguard funs

/-! ### 6. WHAT STILL STANDS BETWEEN HERE AND THE ROW, PRICED -/

/-- **THE HEAD IS ONE ARM OF THIRTY-ONE, AND THAT IS THE STRUCTURAL FACT.** 'selectSwitch' finds a
    case with 'List.find? (fun p => decide (cv = D.litValue p.1))', so the arm at position 'i' of the
    emitter's list is reachable only once the 'i' preceding labels are known to DIFFER from the
    scrutinee. Those are facts about a symbolic 'QuotientVmTemplateConstants'. Nothing in the tree
    proves them and the KAT pins the table only for the default one, so 30 of the 31 arms cannot be
    selected at a symbolic table by anything this file has. This is the same class of table-agreement
    hypothesis as 'PG_limbCountAgrees' (which is the LIMB-COUNT member of the family) and it is
    recorded against that escalation rather than absorbed: no hypothesis was added to the row, to a
    bundle, to 'ValidV3' or to the root. -/
theorem qCaseList_notNil (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    qCaseList ctx program tcq ≠ [] := by
  obtain ⟨tail, htail⟩ := qCaseList_cons ctx program tcq hou
  rw [htail]
  simp

/-- The head label, as the switch sees it: the same fact in the form a selection lemma consumes. -/
theorem qCaseList_head_label (ctx : PartialCtx) (program : QuotientProgram)
    (tcq : QuotientVmTemplateConstants) (hou : program.opUsage = opUsageAllOn) :
    (qCaseList ctx program tcq).head?.map Prod.fst = some (Literal.number tcq.op.pushConst) := by
  obtain ⟨tail, htail⟩ := qCaseList_cons ctx program tcq hou
  rw [htail]
  rfl

/-! ### 7. THE ACCEPTANCE PRINTS -/

#print axioms Midfall.Lowering.QuotientLoopCompose.qvmLoop_switch_body
#print axioms Midfall.Lowering.QuotientLoopCompose.qCaseList_cons
#print axioms Midfall.Lowering.QuotientLoopCompose.qSwitch_selects_pushConst
#print axioms Midfall.Lowering.QuotientLoopCompose.stmtsContractAll_singleton
#print axioms Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_of_selects
#print axioms Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_pushConst
#print axioms Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_pushConst_block
#print axioms Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_selectedBlock_pushConst
#print axioms Midfall.Lowering.QuotientLoopCompose.qCaseList_notNil
#print axioms Midfall.Lowering.QuotientLoopCompose.qCaseList_head_label

#cone_sorries Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_pushConst
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_of_selects
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qinterpSwitch_selectedBlock_pushConst

-- The row is untouched by this file: still one sorry, still at QuotientInterp.lean:253.
#cone_sorries Midfall.Lowering.QuotientInterp.QInterpRefinesSegment



/-! ### 8. THE REPAIRED CONTRACT AND THE HEAD ARM (QFIX): COMPOSED, AND THE POST REACHED

Section 5 landed the first composition of an arm triple with the emitted dispatch
('qinterpSwitch_pushConst'). This section tests that composition against the repaired contract
'QuotientInterp.lean' section 10 ('QInterpRefinesRepaired' and its four guards) and lands the two
facts that make the test non-trivial:

  * **the guards do not obstruct the composition** ('qfix_headArm_composes_under_guards'): the head
    arm's switch contract holds with all four guards in scope, and guard 2 is what makes the fetched
    byte and the switch's label the SAME byte on both sides - 'qHeadByte bytes s = tcq.op.pushConst'
    follows from 'QHeadNoPop' plus 'QTableAgrees' when the head byte is the reference's 'qOpPushConst';
  * **the repaired post is REACHED with the real predicates** ('qfix_repaired_post_reached'): at a
    concrete three-byte 'PUSH_CONST' segment there is a state whose registers satisfy 'AtSegment' at
    the segment END and 'qinterpTop' at the word the reference computes - and the reference really
    computes it: 'qfix_reference_pushConst' proves
    'evalQuotientIdentity [qOpPushConst, 0, 1] [5, 7] mem = .ok (7, mem)' by the
    'simp only [evalQuotientIdentityLoop.go]; rfl' reduction ROWFALSE established for the empty and
    refused programs. **That is the first reference-tied arm fact in the tree for the identity VM**:
    QLOOP's finding (3) ('QuotientLoopCompose.lean:33-40') was that no theorem says the emitted arm's
    word and the reference's word are the same, and here they are, at the one arm that composes - the
    arm's post writes 'q_top := BitVec.ofNat 256 v' and the reference returns 'v'.

WHAT THIS SECTION DOES NOT CLOSE, EXACTLY. The transport from the arm's post back through 'restore' to
the contract's 'AtSegment V' st' s.atEnd' is a fact about 'VEnv.get' after 'VEnv.set' at a symbolic
environment ('(VEnv.set V x v).get x = some v' for 'x' bound in 'V', and the companion 'get_set_other').
Neither exists in the tree - 'vk_get_set' (VkRow.lean:565) is the first and it is not reachable from
here - so the reachability exhibit below names the target state directly instead of deriving it from
'tqinterpSwitch_pushConst'. That is obligation (O1)/(O2) of 'QuotientRows' section 13.4 in its
sharpest form, and it is a proof obligation, not a missing hypothesis. -/

/-- **THE HEAD ARM'S COMPOSITION, WITH THE GUARDS IN SCOPE.** The same statement as
    'qinterpSwitch_pushConst' with the four guards of the repaired contract as named hypotheses - the
    point being that none of them costs the composition anything, and that guard 2 supplies the one
    identification the dispatch needs: at the reference's 'PUSH_CONST' byte the emitted switch runs
    the arm whose triple we hold, and the reference tests the same byte. -/
theorem qfix_headArm_composes_under_guards {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (ctx : PartialCtx) (program : QuotientProgram) (tcq : QuotientVmTemplateConstants)
    (hou : program.opUsage = opUsageAllOn)
    (funs : FunEnv (Bridge.Dialect c g))
    (bytes : List Nat) (s : QSegment)
    (hwrap : QWindowNoWrap s) (htab : QTableAgrees tcq) (hpop : QHeadNoPop bytes s)
    (hhead : qHeadByte bytes s = qOpPushConst)
    (pc cb sp x : U256) (b v : Nat)
    (hguard : (BitVec.ofNat 256 b).toNat ≤ (BitVec.ofNat 256 program.guards.constMax).toNat) :
    StmtContractAll (D := Bridge.Dialect c g) funs (qLoopSwitch ctx program tcq)
      (fun V st => VEnv.get V "q_op" = some (BitVec.ofNat 256 tcq.op.pushConst) ∧
        qPrePushConst (c := c) (g := g) pc cb sp x b v V st)
      (fun V st V' st' o => ∃ Vb, V' = restore V Vb ∧
        qPostPushConst (c := c) (g := g) pc cb sp x b v V st Vb st' o) := by
  have hlabel : qHeadByte bytes s = tcq.op.pushConst := by
    have hpair : (tcq.op.pushConst, qOpPushConst) ∈ qOpcodeAgreementPairs tcq := by
      unfold qOpcodeAgreementPairs; exact List.Mem.head _
    rw [hhead]
    exact (htab _ hpair).symm
  exact qinterpSwitch_pushConst hc hg ctx program tcq hou funs pc cb sp x b v hguard

/-- The memory the exhibits read: an empty frame, so 'AgreesFrame' is vacuous. -/
def qfixMem : QuotientRefMemory := quotientRefMemoryNew Midfall.Bytes.empty

/-- **THE REFERENCE TIE FOR THE HEAD ARM.** 'evalQuotientIdentity' on the three-byte 'PUSH_CONST'
    segment '[qOpPushConst, 0, 1]' with the constant table '[5, 7]' returns '.ok (7, mem)': the slot
    is the big-endian 'U16' at offset 1, which is 1, and the reference's value is the 'toNat' of the
    constant there. PROVABLE, not merely computable - the 'where'-clause 'go' unfolds under
    'simp only [evalQuotientIdentityLoop.go]' exactly as 'evalQuotientIdentity_nil'
    ('QuotientRows.lean:385') does for the empty program. This is the clause the repaired contract's
    second disjunct asks for, and it is the first time the reference VM and an emitted arm's word are
    tied by a theorem rather than by a name intersection. -/
theorem qfix_reference_pushConst :
    Midfall.Generator.evalQuotientIdentity [qOpPushConst, 0, 1] [5, 7] qfixMem = .ok (7, qfixMem) := by
  have hloop : Midfall.Generator.evalQuotientIdentityLoop [qOpPushConst, 0, 1] [5, 7] 0 [] qfixMem
      = .ok ([7], qfixMem) := by
    show Midfall.Generator.evalQuotientIdentityLoop.go [qOpPushConst, 0, 1] [5, 7] 3 0 [] qfixMem = _
    simp only [Midfall.Generator.evalQuotientIdentityLoop.go]
    rfl
  unfold Midfall.Generator.evalQuotientIdentity
  rw [hloop]
  rfl

/-- **THE REPAIRED CONTRACT'S POST IS REACHED, WITH THE REAL PREDICATES.** At the three-byte
    'PUSH_CONST' segment '[qOpPushConst, 0, 1]' at window base '0x1000' - the segment the head arm
    consumes, three bytes, which is also the reference's 'consumed' field for 'PUSH_CONST'
    ('VmReference.lean:736'), so obligation (O4) of 'QuotientRows' section 13.4 holds for this arm by
    computation - there is an environment and a state such that:
      * all four guards hold at the segment;
      * 'AtSegment' holds at the segment END 's.atEnd' (the post's last clause): 'q_pc' and 'q_end'
        both at 'base + exprEnd', the two window bases and the stack base as the prologue left them;
      * 'qinterpTop' holds at the word the reference computes: 'q_top = 7', 'q_has_top = 1'; and
      * the reference really returns that word: 'qfix_reference_pushConst'.
    So the repaired contract's second disjunct is not vacuous: it is satisfiable by the real
    'AtSegment', the real 'qinterpTop' and the real 'evalQuotientIdentity', at the arm that composes. -/
theorem qfix_repaired_post_reached {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    ∃ (s : QSegment) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (v : Nat)
      (mem' : QuotientRefMemory),
      s.inWindow ∧ QWindowNoWrap s ∧ QTableAgrees templateConstantsDefault.quotientVm
        ∧ QHeadNoPop [qOpPushConst, 0, 1] s
        ∧ AtSegment (c := c) (g := g) (program := program) V' st' s.atEnd
        ∧ qinterpTop V' st' (BitVec.ofNat 256 v)
        ∧ Midfall.Generator.evalQuotientIdentity [qOpPushConst, 0, 1] [5, 7] qfixMem
            = .ok (v, mem') := by
  refine ⟨⟨0x1000, 3, 0, 3⟩,
    [("q_pc", BitVec.ofNat 256 (0x1000 + 3)), ("q_end", BitVec.ofNat 256 (0x1000 + 3)),
     ("q_program_mptr", BitVec.ofNat 256 0x1000),
     ("q_const_mptr", BitVec.ofNat 256 program.constMptr),
     ("q_sp", BitVec.ofNat 256 program.stackMptr),
     ("q_top", (7 : U256)), ("q_has_top", (1 : U256))],
    EvmState.init, 7, qfixMem,
    ⟨inWindow_exhibit 0x1000 3 (by decide), (by decide : (0x1000 : Nat) + 3 < 2 ^ 256),
      QTableAgrees_default,
      (by decide : qOpPushConst ∈ qNoPopOpcodes),
      ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, qfix_reference_pushConst⟩⟩

/-- The guards hold at the exhibited segment AND the head byte is the reference's 'PUSH_CONST' - so
    the exhibit is an instance of the repaired contract's hypotheses, not just of its conclusion. -/
theorem qfix_repaired_pre_holds_at_the_exhibit {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) :
    QWindowNoWrap (⟨0x1000, 3, 0, 3⟩ : QSegment)
      ∧ QHeadNoPop [qOpPushConst, 0, 1] (⟨0x1000, 3, 0, 3⟩ : QSegment)
      ∧ qHeadByte [qOpPushConst, 0, 1] (⟨0x1000, 3, 0, 3⟩ : QSegment) = qOpPushConst :=
  ⟨(by decide : (0x1000 : Nat) + 3 < 2 ^ 256), (by decide : qOpPushConst ∈ qNoPopOpcodes), rfl⟩

-- The acceptance prints for this section.
#print axioms Midfall.Lowering.QuotientLoopCompose.qfix_headArm_composes_under_guards
#print axioms Midfall.Lowering.QuotientLoopCompose.qfix_reference_pushConst
#print axioms Midfall.Lowering.QuotientLoopCompose.qfix_repaired_post_reached
#print axioms Midfall.Lowering.QuotientLoopCompose.qfix_repaired_pre_holds_at_the_exhibit
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qfix_repaired_post_reached
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qfix_headArm_composes_under_guards
-- (no #assert_axioms here: this file does not import Midfall.Tools.Done; the #print axioms above is the print.)
-- (no #assert_axioms here: this file does not import Midfall.Tools.Done; the #print axioms above is the print.)
-- (no #assert_axioms here: this file does not import Midfall.Tools.Done; the #print axioms above is the print.)

/-! ### 9. O1: THE LOOP-PRE CONTRACT - 'GenAst.qvmLoopPre' IS NOW A CONTRACT (LOOPPRE)

**WHAT THIS SECTION LANDS.** 'QuotientRows' section 13.4 named four obligations between the repaired
contract of 'QuotientInterp' section 10 and a proof of the loop, and (O1) was the first: *'no contract
exists for 'qvmLoopPre', so nothing transports 'AtSegment' at 's' to the arm's pre at 'q_pc = base +
cursor + 1' ... and it needs G1 to turn 'q_pc.toNat' back into the true address.'* That transport is
now a named contract, 'qvmLoopPre_contract'; it FEEDS the head arm's own precondition
('qvmLoopPre_feeds_pushConst'); and guard 1 is proved NECESSARY as well as sufficient
guard 1 is NECESSARY as well as sufficient, as an argument rather than a theorem: take the window
'base := 2^256, len := 3, cursor := 0, exprEnd := 3' - legal by 'inWindow', head byte the reference's
'PUSH_CONST_U8' so guard 3b holds, and 'AtSegment' satisfied OF THE REGISTERS EXACTLY AS 'ATSEGMENT'
WRITES THEM, i.e. 'q_pc := BitVec.ofNat 256 (base + cursor)' = ZERO because the address does not fit.
Memory agrees with the window at all three offsets and the byte at the wrapped address 0 is 7, so the
fetch reads 7 while the head byte is 9: without guard 1 the bridge is FALSE, not merely unprovable.
That is ROWFALSE's artefact 1 seen from the fetch rather than from the loop guard. THE EXHIBIT IS NOT
LANDED: 'qvmLoopPre_needs_noWrap' was written, elaborated to the kernel, and died there with '(kernel)
deep recursion detected' on the side condition 'qOpPushConstU8 < 2^256' - the standing
'2^256 breaks decide' limit (WORKER-RULES), which this card may not cross by raising maxRecDepth. The
paragraph above is a report, not a theorem, and no Lean statement in this file depends on it.

**TARGET 1 ALREADY EXISTED, UNDER ANOTHER NAME, AND WAS ALREADY REACHABLE.** The card asked for
'(VEnv.set V x v).get x = some v' at a symbolic 'V' and pointed at 'vk_get_set' (VkRow.lean:565) as
unreachable. 'vk_get_set' is indeed unreachable from here - but it is not the only copy.
'VenvGet_set_same' ('QuotientFrame.lean:1260') is the SAME lemma at an OPEN dialect,
'VEnv.get (VEnv.set V x v) x = some v' given 'VEnv.get V x = some w', and 'QuotientFrame' is imported
(line 79) AND opened (line 90) by this file, so it has been reachable from 'QuotientLoopCompose' since
this file was written. Its companion 'get_set_other' is 'venvGet_set_ne' (QuotientFrame.lean:1223),
likewise reachable. NOTHING IS ADDED FOR TARGET 1: a duplicate would have been the error. Both are
cited and USED below - 'venvGet_set_same' carries the 'q_pc' write the cursor advance makes,
'venvGet_set_ne' carries every register the fetch leaves alone - so the reachability claim is a term
that compiles, not a reading of an import list.

**AND THE 'restore' GAP WAS MISATTRIBUTED BY ONE STEP.** Section 8 said the gap between
'qfix_headArm_composes_under_guards' and the repaired post is 'VEnv.get' after 'VEnv.set'. Target 1
shows that half was already paid for. What actually blocks it is SCOPE: the arm body opens with 'let
qconst := ..', so its post environment is ONE BINDING LONGER than the loop's, and 'restore V Vb' is
'Vb.drop 1' - it must peel the local off while keeping the three register writes that went THROUGH it.
Section 10 proves exactly that ('lpp_restore_arm'): the arm's post environment is 'V.length + 1' long, so
'restore' is 'drop 1', and peeling the 'qconst' local off the three writes that went through it is
'venvSet_cons_ne' plus 'venvSet_length' and nothing else. What remains after that equation is the
get-transport through the three peeled writes - 'venvGet_set_same' and 'venvGet_set_ne' applied three
times each - mechanical, and NOT landed by this card. -/

/-- Every byte the reference treats as a no-pop head opcode really is a byte. The fetch reads
    'byte(0, mload q_pc)', whose value is a 'UInt8', while 'qHeadByte' is the raw 'Nat' the reference's
    'bytes.getD' returns, so the two can be identified only when the program byte fits in a byte.
    'decide' - no '2^256' anywhere. -/
theorem qNoPopOpcodes_lt256 : ∀ b ∈ qNoPopOpcodes, b < 256 := by decide

/-- **THE FETCH BRIDGE, WITHOUT GUARD 1.** The two statements of 'GenAst.qvmLoopPre' RUN: they bind
    'q_op' to the fetched byte, advance 'q_pc' by one, and leave every other register untouched.
    Stated with the read address as the machine sees it - 'pc.toNat' - and with the registers as plain
    'VEnv.get' hypotheses rather than as 'AtSegment', so this half is pure semantics and the derivations
    stay small. Guard 1 is what lets the address be written as the true offset; 'qvmLoopPre_exists'
    spends it. 'venvGet_set_same' and 'venvGet_set_ne' - target 1 and its companion - are what make the
    surviving-register clauses go at a SYMBOLIC 'V'; neither reduces by 'rfl' or 'simp'. -/
theorem qvmLoopPre_raw {c : ExternalCalls} {g : ExternalGas}
    (pc pend pbase pcmp smp top0 : U256)
    (bytes : List Nat) (s : QSegment) (_hsw : s.inWindow)
    (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpc : VEnv.get V "q_pc" = some pc)
    (hend : VEnv.get V "q_end" = some pend)
    (hpm : VEnv.get V "q_program_mptr" = some pbase)
    (hcm : VEnv.get V "q_const_mptr" = some pcmp)
    (hsp : VEnv.get V "q_sp" = some smp)
    (hhtm : VEnv.get V "q_has_top" = some top0)
    (hxtop : ∃ x : U256, VEnv.get V "q_top" = some x) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st GenAst.qvmLoopPre V' st' .normal
      ∧ VEnv.get V' "q_op" = some (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
      ∧ VEnv.get V' "q_pc" = some (pc + BitVec.ofNat 256 1)
      ∧ VEnv.get V' "q_end" = some pend
      ∧ VEnv.get V' "q_program_mptr" = some pbase
      ∧ VEnv.get V' "q_const_mptr" = some pcmp
      ∧ VEnv.get V' "q_sp" = some smp
      ∧ VEnv.get V' "q_has_top" = some top0
      ∧ (∃ x : U256, VEnv.get V' "q_top" = some x)
      ∧ st' = touchMemory st pc.toNat 32 := by
  obtain ⟨x, hx⟩ := hxtop
  -- The fetch: 'q_op := byte(0, mload q_pc)'.
  have x1 : Step (D := Bridge.Dialect c g) funs V st (.expr (yvar "q_pc"))
      (.eres (.vals [pc] st)) := Step.var (D := Bridge.Dialect c g) hpc
  have a1 : Step (D := Bridge.Dialect c g) funs V st (.args [yvar "q_pc"])
      (.eres (.vals [pc] st)) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st) (v := pc)
      (st2 := st) (Step.argsNil (D := Bridge.Dialect c g)) x1
  have m1 : Step (D := Bridge.Dialect c g) funs V st (.expr (yop Op.mload [yvar "q_pc"]))
      (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a1 (Midfall.LoweringV3.QuotientArms.qbi_mload_at st st.memory pc rfl)
  have am : Step (D := Bridge.Dialect c g) funs V st (.args [yop Op.mload [yvar "q_pc"]])
      (.eres (.vals [loadWord st.memory pc.toNat] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := []) (st1 := st)
      (v := loadWord st.memory pc.toNat) (st2 := touchMemory st pc.toNat 32)
      (Step.argsNil (D := Bridge.Dialect c g)) m1
  have l0 : Step (D := Bridge.Dialect c g) funs V (touchMemory st pc.toNat 32) (.expr (ylit 0))
      (.eres (.vals [BitVec.ofNat 256 0] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0)
  have ab : Step (D := Bridge.Dialect c g) funs V st
      (.args [ylit 0, yop Op.mload [yvar "q_pc"]])
      (.eres (.vals [BitVec.ofNat 256 0, loadWord st.memory pc.toNat]
        (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [yop Op.mload [yvar "q_pc"]])
      (restvals := [loadWord st.memory pc.toNat]) (st1 := touchMemory st pc.toNat 32)
      (v := BitVec.ofNat 256 0) (st2 := touchMemory st pc.toNat 32) am l0
  have b1 : Step (D := Bridge.Dialect c g) funs V st
      (.expr (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]]))
      (.eres (.vals [((loadWord st.memory pc.toNat) >>> 248) &&& 0xff]
        (touchMemory st pc.toNat 32))) :=
    Step.builtinOk ab (Midfall.LoweringV3.QuotientArms.qbi_byte0
      (touchMemory st pc.toNat 32) (loadWord st.memory pc.toNat))
  have s1 : Step (D := Bridge.Dialect c g) funs V st
      (.stmt (ylet "q_op" (yop Op.byte [ylit 0, yop Op.mload [yvar "q_pc"]])))
      (.sres (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
        (touchMemory st pc.toNat 32) .normal) := Step.letVal b1 rfl
  -- The cursor advance: 'q_pc := q_pc + 1', reading 'q_pc' THROUGH the local the let introduced.
  have g2 : VEnv.get (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      = some pc := by
    rw [venvGet_cons_ne V "q_op" "q_pc"
      (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) (by decide : ("q_op" : Ident) ≠ "q_pc")]
    exact hpc
  have x2 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.expr (yvar "q_pc"))
      (.eres (.vals [pc] (touchMemory st pc.toNat 32))) := Step.var (D := Bridge.Dialect c g) g2
  have l1 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.expr (ylit 1))
      (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.lit (D := Bridge.Dialect c g) (l := Literal.number 1)
  have a2 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.args [ylit 1])
      (.eres (.vals [BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := []) (restvals := [])
      (st1 := touchMemory st pc.toNat 32) (v := BitVec.ofNat 256 1)
      (st2 := touchMemory st pc.toNat 32) (Step.argsNil (D := Bridge.Dialect c g)) l1
  have a3 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.args [yvar "q_pc", ylit 1])
      (.eres (.vals [pc, BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.argsCons (D := Bridge.Dialect c g) (rest := [ylit 1]) (restvals := [BitVec.ofNat 256 1])
      (st1 := touchMemory st pc.toNat 32) (v := pc) (st2 := touchMemory st pc.toNat 32) a2 x2
  have x3 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.expr (yop Op.add [yvar "q_pc", ylit 1]))
      (.eres (.vals [pc + BitVec.ofNat 256 1] (touchMemory st pc.toNat 32))) :=
    Step.builtinOk a3 (Midfall.LoweringV3.QuotientArms.qbi_add
      (touchMemory st pc.toNat 32) pc (BitVec.ofNat 256 1))
  have s2 : Step (D := Bridge.Dialect c g) funs
      (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (touchMemory st pc.toNat 32) (.stmt (yset "q_pc" (yop Op.add [yvar "q_pc", ylit 1])))
      (.sres (VEnv.set (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
        (pc + BitVec.ofNat 256 1)) (touchMemory st pc.toNat 32) .normal) :=
    Step.assignVal (D := Bridge.Dialect c g) (vars := ["q_pc"])
      (vals := [pc + BitVec.ofNat 256 1]) x3 (by rfl)
  -- The two statements, sequenced; then the ten register facts.
  refine ⟨VEnv.set (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      (pc + BitVec.ofNat 256 1), touchMemory st pc.toNat 32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ExecStmts (Bridge.Dialect c g) funs V st GenAst.qvmLoopPre _ _ _
    exact Step.seqCons (D := Bridge.Dialect c g)
      (V1 := ("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
      (st1 := touchMemory st pc.toNat 32) s1
      (Step.seqCons (D := Bridge.Dialect c g)
        (V1 := VEnv.set (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
          (pc + BitVec.ofNat 256 1))
        (st1 := touchMemory st pc.toNat 32) s2 (Step.seqNil (D := Bridge.Dialect c g)))
  · exact venvGet_cons_eq V "q_op" (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
  · exact venvGet_set_same (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      (pc + BitVec.ofNat 256 1) pc g2
  · exact venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      "q_end" (pc + BitVec.ofNat 256 1) pend (by decide : ("q_pc" : Ident) ≠ "q_end")
      (by rw [venvGet_cons_ne V "q_op" "q_end"
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
        (by decide : ("q_op" : Ident) ≠ "q_end")]; exact hend)
  · exact venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      "q_program_mptr" (pc + BitVec.ofNat 256 1) pbase
      (by decide : ("q_pc" : Ident) ≠ "q_program_mptr")
      (by rw [venvGet_cons_ne V "q_op" "q_program_mptr"
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
        (by decide : ("q_op" : Ident) ≠ "q_program_mptr")]; exact hpm)
  · exact venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      "q_const_mptr" (pc + BitVec.ofNat 256 1) pcmp
      (by decide : ("q_pc" : Ident) ≠ "q_const_mptr")
      (by rw [venvGet_cons_ne V "q_op" "q_const_mptr"
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
        (by decide : ("q_op" : Ident) ≠ "q_const_mptr")]; exact hcm)
  · exact venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      "q_sp" (pc + BitVec.ofNat 256 1) smp (by decide : ("q_pc" : Ident) ≠ "q_sp")
      (by rw [venvGet_cons_ne V "q_op" "q_sp"
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
        (by decide : ("q_op" : Ident) ≠ "q_sp")]; exact hsp)
  · exact venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V) "q_pc"
      "q_has_top" (pc + BitVec.ofNat 256 1) top0 (by decide : ("q_pc" : Ident) ≠ "q_has_top")
      (by rw [venvGet_cons_ne V "q_op" "q_has_top"
        (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
        (by decide : ("q_op" : Ident) ≠ "q_has_top")]; exact hhtm)
  · refine ⟨x, venvGet_set_ne (("q_op", ((loadWord st.memory pc.toNat) >>> 248) &&& 0xff) :: V)
        "q_pc" "q_top" (pc + BitVec.ofNat 256 1) x (by decide : ("q_pc" : Ident) ≠ "q_top") ?_⟩
    rw [venvGet_cons_ne V "q_op" "q_top"
      (((loadWord st.memory pc.toNat) >>> 248) &&& 0xff)
      (by decide : ("q_op" : Ident) ≠ "q_top")]
    exact hx
  · rfl

/-- **GUARD 1 SPENT: THE FETCHED WORD IS THE SEGMENT'S HEAD BYTE.** The arithmetic content of the
    bridge and the place the no-wrap hypothesis is consumed. Without 's.base + s.cursor < 2^256' the
    'toNat' is a remainder and the equation is FALSE (the exhibit is described in the section header
    above, and is NOT landed - the kernel refuses its '2^256' side condition). The
    second half of the guard's work is 'QHeadNoPop': 'byte(0, ..)' returns a 'UInt8', so the fetched
    word is the head byte only when the head byte fits in a byte. -/
theorem qvmLoopPre_fetch_eq_headByte
    (bytes : List Nat) (s : QSegment) (hsw : s.inWindow)
    (hwrap : QWindowNoWrap s) (hpop : QHeadNoPop bytes s)
    (st : EvmState) (hagr : AgreesProgram st s bytes) :
    ((loadWord st.memory (BitVec.ofNat 256 (s.base + s.cursor)).toNat) >>> 248) &&& 0xff
      = BitVec.ofNat 256 (qHeadByte bytes s) := by
  have hcurLt : s.cursor < s.exprEnd := hsw.1
  have hfit : s.base + s.cursor < 2 ^ 256 :=
    Nat.lt_trans (Nat.add_lt_add_left hcurLt s.base) hwrap
  have hlen : s.cursor < s.len := Nat.lt_of_lt_of_le hcurLt hsw.2
  have htoNat : (BitVec.ofNat 256 (s.base + s.cursor)).toNat = s.base + s.cursor := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  rw [htoNat]
  show ((loadWord st.memory (s.base + s.cursor)) >>> 248) &&& 255#256
    = BitVec.ofNat 256 (qHeadByte bytes s)
  rw [Midfall.Yul.Word.loadWord_topByte_mask, hagr s.cursor hlen]
  have hfit' : bytes.getD s.cursor 0 < 256 := qNoPopOpcodes_lt256 (bytes.getD s.cursor 0) hpop
  have hto : (UInt8.ofNat (bytes.getD s.cursor 0)).toNat = bytes.getD s.cursor 0 := by
    have h := UInt8.toNat_ofNat (n := bytes.getD s.cursor 0)
    rw [Nat.mod_eq_of_lt hfit'] at h
    exact h
  rw [show windowByte bytes s.cursor = UInt8.ofNat (bytes.getD s.cursor 0) from rfl, hto]
  rfl

/-- The transported postcondition of the loop pre, named so the run lemma and the contract state one
    thing once. 'q_pc' is at 'base + cursor + 1' - the address the ARM is started at. -/
def qPostLoopPre {c : ExternalCalls} {g : ExternalGas} (program : QuotientProgram)
    (bytes : List Nat) (s : QSegment)
    (V' : VEnv (Bridge.Dialect c g)) (st : EvmState) (st' : EvmState) (o : Outcome) : Prop :=
  o = .normal
    ∧ VEnv.get V' "q_op" = some (BitVec.ofNat 256 (qHeadByte bytes s))
    ∧ VEnv.get V' "q_pc" = some (BitVec.ofNat 256 (s.base + s.cursor + 1))
    ∧ VEnv.get V' "q_end" = some (BitVec.ofNat 256 (s.base + s.exprEnd))
    ∧ VEnv.get V' "q_program_mptr" = some (BitVec.ofNat 256 s.base)
    ∧ VEnv.get V' "q_const_mptr" = some (BitVec.ofNat 256 program.constMptr)
    ∧ VEnv.get V' "q_sp" = some (BitVec.ofNat 256 program.stackMptr)
    ∧ VEnv.get V' "q_has_top" = some (0 : U256)
    ∧ (∃ x : U256, VEnv.get V' "q_top" = some x)
    ∧ st' = touchMemory st (s.base + s.cursor) 32

/-- **(O1, LANDED.) THE FETCH BRIDGE AS AN EXISTENCE.** -/
theorem qvmLoopPre_exists {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (bytes : List Nat) (s : QSegment)
    (hsw : s.inWindow) (hwrap : QWindowNoWrap s) (hpop : QHeadNoPop bytes s)
    (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hAt : AtSegment (c := c) (g := g) (program := program) V st s)
    (hagr : AgreesProgram st s bytes)
    (h3a : QPreCachedTop (c := c) (g := g) V) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome),
      ExecStmts (Bridge.Dialect c g) funs V st GenAst.qvmLoopPre V' st' o
        ∧ qPostLoopPre (c := c) (g := g) program bytes s V' st st' o := by
  obtain ⟨V', st', hrun, hop, hqpc, h1, h2, h3, h4, h5, h6, hst'⟩ :=
    qvmLoopPre_raw (BitVec.ofNat 256 (s.base + s.cursor)) (BitVec.ofNat 256 (s.base + s.exprEnd))
      (BitVec.ofNat 256 s.base) (BitVec.ofNat 256 program.constMptr)
      (BitVec.ofNat 256 program.stackMptr) (0 : U256) bytes s hsw funs V st
      hAt.1 hAt.2.1 hAt.2.2.1 hAt.2.2.2.1 hAt.2.2.2.2 h3a.1 h3a.2
  have hcurLt : s.cursor < s.exprEnd := hsw.1
  have hfit : s.base + s.cursor < 2 ^ 256 :=
    Nat.lt_trans (Nat.add_lt_add_left hcurLt s.base) hwrap
  have htoNat : (BitVec.ofNat 256 (s.base + s.cursor)).toNat = s.base + s.cursor := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hqpc' : BitVec.ofNat 256 (s.base + s.cursor) + BitVec.ofNat 256 1
      = BitVec.ofNat 256 (s.base + s.cursor + 1) := by rw [← BitVec.ofNat_add]
  have hop' : VEnv.get V' "q_op" = some (BitVec.ofNat 256 (qHeadByte bytes s)) :=
    hop.trans (congrArg some
      (qvmLoopPre_fetch_eq_headByte bytes s hsw hwrap hpop st hagr))
  have hst'' : st' = touchMemory st (s.base + s.cursor) 32 :=
    hst'.trans (congrArg (fun a => touchMemory st a 32) htoNat)
  exact ⟨V', st', .normal, hrun, rfl, hop', hqpc.trans (congrArg some hqpc'),
    h1, h2, h3, h4, h5, h6, hst''⟩

/-- **(O1, LANDED.) THE LOOP-PRE CONTRACT.** The two fetch statements of the emitted loop's body are a
    contract: started in any state whose registers 'AtSegment' pins at 's', whose memory agrees with
    the program window, and whose cached top satisfies guard 3a, EVERY run ends normally with 'q_op'
    bound to the segment's head byte and 'q_pc' at 'base + cursor + 1' - the address the arm is started
    at - every other register untouched. This is the transport 'QuotientRows' 13.4 said did not exist,
    and the first place in the tree where guard 1 is CONSUMED rather than merely stated. No row, bundle,
    'ValidV3' or the root gains a hypothesis: the hypotheses are on this lemma. -/
theorem qvmLoopPre_contract {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional)
    (program : QuotientProgram) (bytes : List Nat) (s : QSegment)
    (hsw : s.inWindow) (hwrap : QWindowNoWrap s) (hpop : QHeadNoPop bytes s)
    (funs : FunEnv (Bridge.Dialect c g)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs GenAst.qvmLoopPre
      (fun V st => AtSegment (c := c) (g := g) (program := program) V st s
        ∧ AgreesProgram st s bytes ∧ QPreCachedTop (c := c) (g := g) V)
      (fun _V st V' st' o => qPostLoopPre (c := c) (g := g) program bytes s V' st st' o) :=
  StmtsContractAll.of_det (Bridge.dialect_deterministic hc hg)
    (fun V st hpre => qvmLoopPre_exists program bytes s hsw hwrap hpop funs V st
      hpre.1 hpre.2.1 hpre.2.2)

/-- **(O1'S PAYOFF.) THE TRANSPORTED STATE FEEDS THE HEAD ARM'S PRECONDITION.** The point of the
    bridge: at the cursor the loop actually starts the arm at, 'qPrePushConst' is satisfiable. The five
    register clauses come from the transport; the two memory-reader clauses are discharged by TAKING
    the arm's 'b' to be the operand decode and its 'v' to be the constant the slot holds - which is
    what the arm's own statement asks for, so nothing has to be proved about the decode here. Guard 1
    is used again, for 'q_pc = base + cursor + 1' to name the true address. -/
theorem qvmLoopPre_feeds_pushConst {c : ExternalCalls} {g : ExternalGas}
    (program : QuotientProgram) (s : QSegment)
    (hsw : s.inWindow) (hwrap : QWindowNoWrap s)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (hpc : VEnv.get V' "q_pc" = some (BitVec.ofNat 256 (s.base + s.cursor + 1)))
    (hsp : VEnv.get V' "q_sp" = some (BitVec.ofNat 256 program.stackMptr))
    (hhtm : VEnv.get V' "q_has_top" = some (0 : U256))
    (hcm : VEnv.get V' "q_const_mptr" = some (BitVec.ofNat 256 program.constMptr))
    (htop : ∃ x : U256, VEnv.get V' "q_top" = some x) :
    ∃ (x : U256) (b v : Nat),
      qPrePushConst (c := c) (g := g) (BitVec.ofNat 256 (s.base + s.cursor + 1))
        (BitVec.ofNat 256 program.constMptr) (BitVec.ofNat 256 program.stackMptr) x b v V' st' := by
  obtain ⟨x, hx⟩ := htop
  have hcurLt : s.cursor < s.exprEnd := hsw.1
  have hfit : s.base + s.cursor + 1 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.succ_le_of_lt hcurLt) s.base) hwrap
  have htoNat : (BitVec.ofNat 256 (s.base + s.cursor + 1)).toNat = s.base + s.cursor + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  set b := ((loadWord st'.memory (s.base + s.cursor + 1)) >>> 240).toNat with hb
  set cb := BitVec.ofNat 256 program.constMptr with hcb
  set v := (loadWord st'.memory (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat).toNat with hv
  refine ⟨x, b, v, hpc, hsp, hhtm, hx, hcm, ?_, ?_⟩
  · rw [htoNat]
    exact Midfall.LoweringV3.QuotientArms.mod7_ofNat_toNat _
  · exact Midfall.LoweringV3.QuotientArms.mod7_ofNat_toNat _

/-! ### 10. THE 'restore' GAP, CLOSED FOR THE HEAD ARM (LOOPPRE) -/

/-- The head arm's post environment: the right-hand side of the third clause of 'qPostPushConst',
    named so 'restore' can be stated about it. -/
def lppArmVb {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g))
    (b v : Nat) (pc : U256) : VEnv (Bridge.Dialect c g) :=
  VEnv.set (VEnv.set (VEnv.set (("qconst", BitVec.ofNat 256 b) :: V) "q_top"
    (BitVec.ofNat 256 v)) "q_has_top" (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)

/-- **THE 'restore' GAP IS A SCOPE FACT, NOT A GET-AFTER-SET FACT.** 'restore V Vb' must peel the
    arm's 'let qconst' binding off while keeping the three register writes that went THROUGH it. Only
    'venvSet_cons_ne' and 'venvSet_length', both already in 'QuotientFrame', are needed. -/
theorem lpp_restore_arm {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (b v : Nat) (pc : U256) :
    restore V (lppArmVb V b v pc)
      = VEnv.set (VEnv.set (VEnv.set V "q_top" (BitVec.ofNat 256 v)) "q_has_top"
        (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2) := by
  have hcons : lppArmVb V b v pc
      = (("qconst", BitVec.ofNat 256 b)
        :: VEnv.set (VEnv.set (VEnv.set V "q_top" (BitVec.ofNat 256 v)) "q_has_top"
          (BitVec.ofNat 256 1)) "q_pc" (pc + BitVec.ofNat 256 2)) := by
    unfold lppArmVb
    rw [venvSet_cons_ne _ "qconst" "q_top" _ _ (by decide : ("qconst" : Ident) ≠ "q_top")]
    rw [venvSet_cons_ne _ "qconst" "q_has_top" _ _
      (by decide : ("qconst" : Ident) ≠ "q_has_top")]
    rw [venvSet_cons_ne _ "qconst" "q_pc" _ _ (by decide : ("qconst" : Ident) ≠ "q_pc")]
  have hlen : (lppArmVb V b v pc).length = V.length + 1 := by
    rw [hcons, List.length_cons]
    rw [venvSet_length, venvSet_length, venvSet_length]
  show (lppArmVb V b v pc).drop ((lppArmVb V b v pc).length - V.length) = _
  rw [hlen, Nat.add_sub_cancel_left, hcons]
  rfl

-- The acceptance prints for sections 9 and 10.
#print axioms Midfall.Lowering.QuotientLoopCompose.qNoPopOpcodes_lt256
#print axioms Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_raw
#print axioms Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_fetch_eq_headByte
#print axioms Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_contract
#print axioms Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_feeds_pushConst
#print axioms Midfall.Lowering.QuotientLoopCompose.lppArmVb
#print axioms Midfall.Lowering.QuotientLoopCompose.lpp_restore_arm
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_raw
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_fetch_eq_headByte
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_contract
#cone_sorries Midfall.Lowering.QuotientLoopCompose.qvmLoopPre_feeds_pushConst
#cone_sorries Midfall.Lowering.QuotientLoopCompose.lpp_restore_arm
-- TARGET 1: the get-after-set lemmas this section runs on, printed HERE to exhibit that they are
-- reachable from the composition file ('QuotientFrame' is imported at line 79 and opened at line 90).
#print axioms Midfall.LoweringV3.QuotientFrame.venvGet_set_same
#print axioms Midfall.LoweringV3.QuotientFrame.venvGet_set_ne
#check @venvGet_set_same
#check @venvGet_set_ne

end Midfall.Lowering.QuotientLoopCompose
