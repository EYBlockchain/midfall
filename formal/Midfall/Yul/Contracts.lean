-- |
-- Midfall.Yul.Contracts
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 2 of the table; PLAN
-- P-SE-semantic-equivalence.md section A and index item 1; design0.md
-- 'YulSemantics.StmtsContractAll / StmtContractAll / ExprContractAll').
--
-- WHAT THIS FILE IS FOR. The vendored relational layer
-- (vendor/yul-semantics/YulSemantics/Contract.lean) only has the EXISTENTIAL
-- contract: StmtsContract funs stmts pre post (Contract.lean:94) says 'there is
-- SOME run of stmts from a pre state that satisfies post'. Every per-partial
-- spec the semantic-equivalence proof needs is the opposite quantifier: under a
-- RELATIONAL calls (an open-world external-call relation admits many responses)
-- EVERY run of the partial must end in a state that satisfies the next
-- checkpoint, because the contract returns only if all of them do. That
-- forall-runs form is what StmtContractAll / StmtsContractAll / ExprContractAll
-- below are, and the composition lemmas are the ones the existential layer
-- cannot state: the vendored StmtsContract.cons (Contract.lean:143) forces the
-- head statement to be .normal, so it cannot express 'the head reverted, so the
-- tail never ran', which is the shape of every fail(..) arm in the verifier
-- partials. attack.md line 94 FIX (binding) is the same complaint about
-- ExecLoopAll.countdown_or_halt being 'True := trivial' in one design: a real
-- halting-loop rule is stated here instead, inverting all seven loop
-- constructors (loopDone, loopCondHalt, loopStep, loopPostHalt, loopBreak,
-- loopLeave, loopBodyHalt, BigStep.lean:299-335).
--
-- DIALECT-GENERIC ON PURPOSE. Everything is parameterised by
-- {D : Dialect} [DecidableEq D.Value] exactly like the vendor file, so it
-- instantiates at Midfall.Yul.Bridge.Dialect calls gas without a second copy.
-- attack.md line 13 FIX (binding) resolves the two-design conflict this way:
-- 'keep P2 generic form and instantiate; one copy'. Midfall/Yul/Bridge.lean
-- therefore does NOT redefine these combinators.
--
-- WHY [DecidableEq D.Value]. Step needs it so switch dispatches through the
-- FUNCTION selectSwitch (BigStep.lean:132) instead of a relation; that is what
-- makes StmtContractAll.switch provable with no side condition. It resolves at
-- the open EVM dialect because Value := U256 reducibly (EVMExec.lean:953-961).
--
-- KNOWN FALSEHOOD THIS FILE AVOIDS. The plan sketch for the halting-loop rule
-- (P-SE section A, ExecLoopAll.countdown_or_halt) concludes only
-- (o = .normal AND Inv 0) OR (o = .halt AND Q) with two hypotheses. That form is
-- not derivable from the loop rules as vendored: a body that executes leave
-- makes Step.loopLeave fire with outcome .leave, and a condition that halts at
-- fuel level 0 makes Step.loopCondHalt fire, neither of which the sketch
-- hypotheses can discharge. The rule below states the extra arms instead of
-- leaving a hole on a statement nobody can prove; nothing is weakened, the
-- hypothesis list only grows. Reported as a stage-1 finding.

import YulSemantics.BigStep
import YulSemantics.Contract
import YulSemantics.Determinism

namespace YulSemantics

variable {D : Dialect} [DecidableEq D.Value]

/-! ### The forall-runs contract layer -/

/-- Partial correctness over EVERY derivation: whenever pre holds, every Step
    derivation of stmts ends in a state and outcome satisfying post. Compare
    StmtsContract (Contract.lean:94), which asks for one run. Cited by PLAN 9.5
    per-partial specs (P-SE index item 1, design0 'Forall-runs contract layer'). -/
def StmtsContractAll (funs : FunEnv D) (stmts : Block D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmts D funs V st stmts V' st' o → post V st V' st' o

/-- Single-statement form of StmtsContractAll. -/
def StmtContractAll (funs : FunEnv D) (s : Stmt D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmt D funs V st s V' st' o → post V st V' st' o

/-- Expression form: every evaluation result - values or a halt - satisfies
    post. Needed because a partial guard expression (calldatasize, an mload of a
    pointer) can itself halt, and the revert arm must be proved for the
    expression, not only for the block it guards. -/
def ExprContractAll (funs : FunEnv D) (e : Expr D.Op)
    (pre : VEnv D → D.State → Prop) (post : VEnv D → D.State → EResult D → Prop) : Prop :=
  ∀ V st, pre V st → ∀ r, EvalExpr D funs V st e r → post V st r

/-- Whole-program form: the shape RunVerifier / RunContractIR (PLAN 9.5)
    consume. Note the argument order matches YulSemantics.Run
    (BigStep.lean:366), which puts the initial state first and the final
    environment second. -/
def RunContractAll (program : Block D.Op) (pre : D.State → Prop)
    (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ st0 V' st' o, pre st0 → Run D program st0 V' st' o → post st0 V' st' o

/-- Non-vacuity gate for the whole layer (design0 'non-vacuity'): the definitions
    really do quantify over derivations, so the empty block cannot establish a
    false postcondition through Step.seqNil. A definition that quantified over no
    derivation would make this example unprovable. -/
example : ¬ StmtsContractAll (D := EVM.evm) [] [] (fun _ _ => True) (fun _ _ _ _ _ => False) :=
  fun h => h [] EVM.EvmState.init trivial [] _ .normal Step.seqNil

/-! ### Step inversion lemmas -/

/-- A sequence derivation is either seqCons (head continues normally) or seqStop
    (head halts the sequence): the only two Step rules for .stmts (s :: rest)
    (BigStep.lean:287-294). Proved by cases because the Code index is syntactic. -/
theorem Step.stmts_cons_inv {funs : FunEnv D} {V st s ss V' st' o}
    (h : ExecStmts D funs V st (s :: ss) V' st' o) :
    (∃ V₁ st₁, ExecStmt D funs V st s V₁ st₁ .normal ∧ ExecStmts D funs V₁ st₁ ss V' st' o) ∨
    (ExecStmt D funs V st s V' st' o ∧ o ≠ .normal) := by
  cases h with
  | seqCons h₁ h₂ => exact Or.inl ⟨_, _, h₁, h₂⟩
  | seqStop h₁ hne => exact Or.inr ⟨h₁, hne⟩

/-- An appended-sequence derivation splits at the boundary: either the first block
    finishes normally and the second block produces the run, or the first block
    already stopped with a non-.normal outcome and the second never ran. Needed
    because each verifier partial is a SLICE of the main block, so composition is
    over ++ and not over ::. -/
theorem Step.stmts_append_inv {funs : FunEnv D} {V st ss₁ ss₂ V' st' o}
    (h : ExecStmts D funs V st (ss₁ ++ ss₂) V' st' o) :
    (∃ V₁ st₁, ExecStmts D funs V st ss₁ V₁ st₁ .normal ∧ ExecStmts D funs V₁ st₁ ss₂ V' st' o) ∨
    (ExecStmts D funs V st ss₁ V' st' o ∧ o ≠ .normal) := by
  induction ss₁ generalizing V st with
  | nil => exact Or.inl ⟨V, st, Step.seqNil, h⟩
  | cons s rest ih =>
      cases h with
      | seqCons h₁ h₂ =>
          rcases ih h₂ with ⟨V₂, st₂, hr, hs⟩ | ⟨hr, hne2⟩
          · exact Or.inl ⟨V₂, st₂, Step.seqCons h₁ hr, hs⟩
          · exact Or.inr ⟨Step.seqCons h₁ hr, hne2⟩
      | seqStop h₁ hne => exact Or.inr ⟨Step.seqStop h₁ hne, hne⟩

/-! ### Composition lemmas -/

/-- Halting-head cons: the head either continues normally into mid or stops with
    the final postcondition already established (the revert arm). This is the
    per-partial shape 'reverted OR Inv next' that PLAN 9.5 writes, and the lemma
    the vendored StmtsContract.cons cannot express. -/
theorem StmtsContractAll.cons_split {funs : FunEnv D} {s : Stmt D.Op} {ss : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (head : StmtContractAll funs s pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (tail : ∀ V st, pre V st →
      StmtsContractAll funs ss mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (s :: ss) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases head V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact tail V st hpre V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne'
  · rcases head V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hpost⟩
    · exact absurd heq hne
    · exact hpost

/-- Sequencing over ++: the head slice either continues normally into mid or stops
    with post already established, and the tail slice continues from mid. design0
    lists this as provable-now with a sketch hole; it follows from
    Step.stmts_append_inv above. -/
theorem StmtsContractAll.append {funs : FunEnv D} {ss₁ ss₂ : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h₁ : StmtsContractAll funs ss₁ pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (h₂ : ∀ V st, pre V st → StmtsContractAll funs ss₂ mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (ss₁ ++ ss₂) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁run, h₂run⟩ | ⟨h₁run, hne⟩
  · rcases h₁ V st hpre V₁ st₁ .normal h₁run with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact h₂ V st hpre V₁ st₁ hmid V' st' o h₂run
    · exact absurd rfl hne'
  · rcases h₁ V st hpre V' st' o h₁run with ⟨heq, _⟩ | ⟨_, hpost⟩
    · exact absurd heq hne
    · exact hpost

/-- A block statement runs its body under the hoisted function scope and restores
    the outer variable environment on the way out (Step.block, BigStep.lean:225-227).
    Mirror of the vendored StmtsContract.block (Contract.lean:158) at the
    forall-runs layer. -/
theorem StmtsContractAll.block {funs : FunEnv D} {body : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtsContractAll (hoist D body :: funs) body pre
      (fun V st V' st' o => post V st (restore V V') st' o)) :
    StmtContractAll funs (.block body) pre post := by
  intro V st hpre V' st' o hrun
  cases hrun with
  | block hbody => exact h V st hpre _ _ _ hbody

/-- if c { body }: the guard is evaluated once, so the contract needs the
    expression-level facts (a zero guard skips the body, a nonzero guard runs it
    as a block, a halting guard halts the statement). D.zero is the dialect
    reading of the literal 0 (BigStep.lean:89). -/
theorem StmtContractAll.cond {funs : FunEnv D} {e : Expr D.Op} {body : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (hcond : ∀ V st cv st₁, pre V st → EvalExpr D funs V st e (.vals [cv] st₁) →
      (cv = D.zero → post V st V st₁ .normal) ∧
      (cv ≠ D.zero → ∀ V' st' o, ExecStmt D funs V st₁ (.block body) V' st' o → post V st V' st' o))
    (hhalt : ∀ V st st₁, pre V st → EvalExpr D funs V st e (.halt st₁) → post V st V st₁ .halt) :
    StmtContractAll funs (.cond e body) pre post := by
  intro V st hpre V' st' o hrun
  cases hrun with
  | ifTrue hc hnz hbody =>
      rename_i _ cv st₁
      exact (hcond V st cv st₁ hpre hc).2 hnz V' st' o hbody
  | ifFalse hc hz =>
      rename_i _ cv
      exact (hcond V st cv st' hpre hc).1 hz
  | ifHalt hc =>
      exact hhalt V st st' hpre hc

/-- switch c cases dflt: the block executed is selectSwitch, a FUNCTION
    (BigStep.lean:132), which is why no determinism hypothesis is needed here -
    the [DecidableEq D.Value] binder does the work. -/
theorem StmtContractAll.switch {funs : FunEnv D} {e : Expr D.Op}
    {cases : List (Literal × Block D.Op)} {dflt : Option (Block D.Op)}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (hsel : ∀ V st cv st₁, pre V st → EvalExpr D funs V st e (.vals [cv] st₁) →
      ∀ V' st' o, ExecStmt D funs V st₁ (.block (selectSwitch D cv cases dflt)) V' st' o →
        post V st V' st' o)
    (hhalt : ∀ V st st₁, pre V st → EvalExpr D funs V st e (.halt st₁) → post V st V st₁ .halt) :
    StmtContractAll funs (.switch e cases dflt) pre post := by
  intro V st hpre V' st' o hrun
  cases hrun with
  | switchExec hc hbody =>
      rename_i _ cv st₁
      exact hsel V st cv st₁ hpre hc V' st' o hbody
  | switchHalt hc =>
      exact hhalt V st st' hpre hc

/-- A user-function call: the argument list, then the body under the definition
    site function environment (Step.callOk / callHalt / callArgsHalt,
    BigStep.lean:185-203). The output variables are read back from the callee
    environment with the same .getD D.zero fallback the rule uses. -/
theorem ExprContractAll.callUser {funs : FunEnv D} {f : Ident} {args : List (Expr D.Op)}
    {decl cenv} (hlook : lookupFun funs f = some (decl, cenv))
    {pre : VEnv D → D.State → Prop} {post : VEnv D → D.State → EResult D → Prop}
    (hargs : ∀ V st vals st₁, pre V st → EvalArgs D funs V st args (.vals vals st₁) →
      vals.length = decl.params.length →
      ∀ V' st' o, ExecStmt D cenv ((decl.params.zip vals) ++ bindZeros D decl.rets) st₁
        (.block decl.body) V' st' o →
        (o = .halt → post V st (.halt st')) ∧
        (o ≠ .halt → post V st (.vals (decl.rets.map fun r => (VEnv.get V' r).getD D.zero) st')))
    (hargsHalt : ∀ V st st₁, pre V st → EvalArgs D funs V st args (.halt st₁) → post V st (.halt st₁)) :
    ExprContractAll funs (.call f args) pre post := by
  intro V st hpre r hr
  cases hr with
  | callOk hstep₁ hlookup hlen hbody hor =>
      rename_i _ argvals st₁ decl₂ cenv₂ V₂ st₂ o₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hlook.symm.trans hlookup))
      have hne : o₂ ≠ .halt := by
        intro h
        cases hor <;> simp_all
      exact (hargs V st argvals st₁ hpre hstep₁ hlen V₂ st₂ o₂ hbody).2 hne
  | callHalt hstep₁ hlookup hlen hbody =>
      rename_i _ argvals st₁ decl₂ cenv₂ V₂ st₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hlook.symm.trans hlookup))
      exact (hargs V st argvals st₁ hpre hstep₁ hlen V₂ st₂ .halt hbody).1 rfl
  | callArgsHalt hstep₁ =>
      rename_i _ st₁
      exact hargsHalt V st st₁ hpre hstep₁

/-- The existential contract plus per-op determinism gives the universal one.
    This is the bridge the honest-call layer uses: StmtsContract is what a
    constructive proof of 'the partial runs' gives, and determinism is what turns
    it into 'every run of the partial behaves'. hdet is discharged at the open
    dialect by Midfall.Yul.Bridge.dialect_deterministic, which needs the call
    relation to be functional - so this lemma is exactly where D-P10
    determinism condition becomes load-bearing. -/
theorem StmtsContractAll.of_det {funs : FunEnv D} {stmts : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (hdet : ∀ op, D.Deterministic op) (h : StmtsContract funs stmts pre post) :
    StmtsContractAll funs stmts pre post := by
  intro V st hpre V' st' o hrun
  obtain ⟨V₂, st₂, o₂, hexec, hp⟩ := h V st hpre
  obtain ⟨hV, hst, ho⟩ := ExecStmts.det hdet hrun hexec
  subst hV; subst hst; subst ho
  exact hp

/-! ### The halting loop -/

/-- Countdown rule for a for loop whose body may halt, leave or break - the rule
    attack.md line 94 FIX (binding) demands, inverting all seven loop
    constructors of Step (BigStep.lean:299-335). The vendored ExecLoop.countdown
    (Contract.lean:176) covers only the .normal arm and builds the run rather
    than constraining every one of them.

    Inv k is the invariant with k iterations of fuel left; zero says that at fuel
    0 the guard cannot be true, which is what makes the induction terminate.
    Exit, Qh and Ql are the three ways a loop derivation can end: normally (break
    included, because loopBreak turns it into .normal), halted, or by leave.

    DEVIATION FROM THE PLAN SKETCH, recorded: P-SE section A states the post as
    (o = .normal AND Inv 0) OR (o = .halt AND Q) with two hypotheses. That form is
    not derivable - Step.loopLeave produces .leave and Step.loopCondHalt produces
    .halt at fuel 0 - so the rule here carries the extra arms as hypotheses and a
    third disjunct. Nothing is weakened: the plan conclusion is recovered by
    instantiating Ql := fun _ _ => True and Exit := fun V' st' => Inv 0 V' st'. -/
theorem ExecLoopAll.countdown_or_halt {funs : FunEnv D} {cond : Expr D.Op}
    {post body : Block D.Op} {Inv : Nat → VEnv D → D.State → Prop}
    {Exit Qh Ql : VEnv D → D.State → Prop}
    (zero : ∀ V st cv st', Inv 0 V st → EvalExpr D funs V st cond (.vals [cv] st') → cv = D.zero)
    (done : ∀ n V st cv st', Inv n V st → EvalExpr D funs V st cond (.vals [cv] st') →
      cv = D.zero → Exit V st')
    (condHalt : ∀ n V st stc, Inv n V st → EvalExpr D funs V st cond (.halt stc) → Qh V stc)
    (bodyHalt : ∀ n V st cv stc Vb stb, Inv n V st →
      EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero →
      ExecStmt D funs V stc (.block body) Vb stb .halt → Qh Vb stb)
    (postHalt : ∀ n V st cv stc Vb stb ob Vp stp, Inv n V st →
      EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero →
      ExecStmt D funs V stc (.block body) Vb stb ob → (ob = .normal ∨ ob = .«continue») →
      ExecStmt D funs Vb stb (.block post) Vp stp .halt → Qh Vp stp)
    (bodyLeave : ∀ n V st cv stc Vb stb, Inv n V st →
      EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero →
      ExecStmt D funs V stc (.block body) Vb stb .leave → Ql Vb stb)
    (bodyBreak : ∀ n V st cv stc Vb stb, Inv n V st →
      EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero →
      ExecStmt D funs V stc (.block body) Vb stb .«break» → Exit Vb stb)
    (progress : ∀ n V st cv stc Vb stb ob, Inv (n + 1) V st →
      EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero →
      ExecStmt D funs V stc (.block body) Vb stb ob → (ob = .normal ∨ ob = .«continue») →
      ∀ Vp stp, ExecStmt D funs Vb stb (.block post) Vp stp .normal → Inv n Vp stp) :
    ∀ n V st, Inv n V st → ∀ V' st' o, ExecLoop D funs V st cond post body V' st' o →
(o = .normal ∧ Exit V' st') ∨ (o = .halt ∧ Qh V' st') ∨ (o = .leave ∧ Ql V' st') := by
  intro n
  induction n with
  | zero =>
      intro V st hInv V' st' o hloop
      cases hloop with
      | loopDone hc hz =>
          rename_i cv
          exact Or.inl ⟨rfl, done 0 V st cv st' hInv hc hz⟩
      | loopCondHalt hc =>
          exact Or.inr (Or.inl ⟨rfl, condHalt 0 V st st' hInv hc⟩)
      | loopStep hc hnz hbody hob hpost hrec =>
          rename_i cv st₁ Vb stb ob Vp stp
          exact absurd (zero V st cv st₁ hInv hc) hnz
      | loopPostHalt hc hnz hbody hob hpost =>
          rename_i cv st₁ Vb stb ob
          exact absurd (zero V st cv st₁ hInv hc) hnz
      | loopBreak hc hnz hbody =>
          rename_i cv st₁
          exact absurd (zero V st cv st₁ hInv hc) hnz
      | loopLeave hc hnz hbody =>
          rename_i cv st₁
          exact absurd (zero V st cv st₁ hInv hc) hnz
      | loopBodyHalt hc hnz hbody =>
          rename_i cv st₁
          exact absurd (zero V st cv st₁ hInv hc) hnz
  | succ n ih =>
      intro V st hInv V' st' o hloop
      cases hloop with
      | loopDone hc hz =>
          rename_i cv
          exact Or.inl ⟨rfl, done (n + 1) V st cv st' hInv hc hz⟩
      | loopCondHalt hc =>
          exact Or.inr (Or.inl ⟨rfl, condHalt (n + 1) V st st' hInv hc⟩)
      | loopStep hc hnz hbody hob hpost hrec =>
          rename_i cv st₁ Vb stb ob Vp stp
          have hInv2 := progress n V st cv st₁ Vb stb ob hInv hc hnz hbody hob Vp stp hpost
          exact ih Vp stp hInv2 V' st' o hrec
      | loopPostHalt hc hnz hbody hob hpost =>
          rename_i cv st₁ Vb stb ob
          exact Or.inr (Or.inl ⟨rfl, postHalt (n + 1) V st cv st₁ Vb stb ob V' st' hInv hc hnz hbody hob hpost⟩)
      | loopBreak hc hnz hbody =>
          rename_i cv st₁
          exact Or.inl ⟨rfl, bodyBreak (n + 1) V st cv st₁ V' st' hInv hc hnz hbody⟩
      | loopLeave hc hnz hbody =>
          rename_i cv st₁
          exact Or.inr (Or.inr ⟨rfl, bodyLeave (n + 1) V st cv st₁ V' st' hInv hc hnz hbody⟩)
      | loopBodyHalt hc hnz hbody =>
          rename_i cv st₁
          exact Or.inr (Or.inl ⟨rfl, bodyHalt (n + 1) V st cv st₁ V' st' hInv hc hnz hbody⟩)
end YulSemantics
