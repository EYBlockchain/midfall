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
#cone_sorries Midfall.Lowering.QuotientInterp.qinterpRefines_qvmLoop

end Midfall.Lowering.QuotientLoopCompose
