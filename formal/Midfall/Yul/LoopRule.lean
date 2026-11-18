/-
  Midfall.Yul.LoopRule

  THE LOOP RULE FOR A SYMBOLIC BOUND (GEN.3, PLAN-V3): one INVARIANT rule for a Yul `for` loop whose
  bound is a VARIABLE, usable inside a `wp`/`AllRuns` goal, with its W12 witness and its two
  falsifiers. Ported VERBATIM from the proved scratch source
  docs/plans/V3-evidence/lean/prooftech/LoopRule.lean (522 lines, ZERO sorry warnings under
  `bash docs/plans/V3-evidence/check.sh prooftech`); the only changes are (a) the import paths -
  plus `import Mathlib.Tactic.Ring`, which the scratch file picked up TRANSITIVELY (its `WPTac` ->
  `WPBridge` -> `Lits` -> `Midfall.Instances.PoseidonValid` chain pulls Mathlib, while the landed
  `Midfall.Yul.WpTac` deliberately does not) and which `tri_succ` needs - (b) the namespace
  (Midfall.Scratch.ProofTech -> Midfall.Yul.LoopRule) and the opens that move requires, (c)
  `#assert_axioms` added beside the `#print axioms` lines the source already carried, and (d) this
  header. No statement and no proof step was restated.

  WHY IT IS HERE. ROW.TP and ROW.PCS (M6) induct over loops whose trip count is a PLAN COUNT, not a
  numeral: `32 * numInstances`, `0x80 * plan count`, `k` from a VK field. `wpL`
  (Midfall/Yul/Wp.lean:194) unrolls by FUEL, so it cannot run a loop whose count is symbolic.
  `wpIter` is `wpL` for ONE iteration with the recursive call replaced by the invariant, and
  `allRuns_for_cons_wp` cuts a `for` statement into `init` + one symbolic iteration + a SEMANTIC
  continuation. That is the shape every block-row loop proof applies.

  NO VARIANT IS NEEDED, and that is the point: `AllRuns` quantifies over big-step derivations,
  which are finite, so the rule is proved by induction on the DERIVATION, not on a remaining-
  iteration count, and the invariant need not decrease. Termination is not this rule's business
  (that is TOT.1's). Contrast `Midfall.Yul.Contracts.lean:298` `ExecLoopAll.countdown_or_halt`,
  which inducts on the count and therefore needs `Inv 0 -> guard = 0`; this rule needs neither.

  WHAT IS HERE (the section numbers are the source's, preserved):
    §1 IterAll, loop_inv_aux, allRuns_loop     the rule on the big-step judgment (no engine, no fuel)
    §2 wpIter, iterAll_of_wp, allRuns_loop_wp,
       allRuns_for_wp, allRuns_for_cons_wp,
       allRuns_for_cons_wp_count               the same rule as an allRuns_cons_wp-style cut
    §3 sumLoop_all                  the W12 witness: bound `n : Nat`, EVERY n < 2^256
    §4 loopRuleNoPres_false,
       sumLoop_all_needs_bound                 the W12 falsifiers (rule level; side condition)
    §5 the table of the generated verifier's loops that need this rule (F1 line numbers): the
       card's loop table, carried VERBATIM as the section docstring there.

  D-P71: NO `native_decide` anywhere in this file, and none is needed. The witness runs `init`, one
  iteration and the rest as three `wp_run` goals; the two decidable word equations in the falsifiers
  are kernel `decide`, not `native_decide`. This file is inside `lowering_correct`'s cone.

  W12: the witness AND both falsifiers are in the tree, and NOTHING in this file is sorried - there
  is no row for it in SORRY.md.

  AXIOMS (pinned by the `#assert_axioms` lines below, measured in the LANDED tree): the three rules
  rest on `[propext]` ALONE - stronger than the `[propext, Classical.choice, Quot.sound]` the card
  allows - while the witness `sumLoop_all` needs the full triple, because `tri_succ` runs `ring` and
  `norm_num`. The card's parenthetical "(measured: `[propext]` only)" is true of the three rules and
  FALSE of the witness; the pin the card states, `[propext, Classical.choice, Quot.sound] native []`,
  is what the tree now enforces for all four.
-/
import Mathlib.Tactic.Ring
import Midfall.Yul.WpTac
import Midfall.Tools.Done
set_option autoImplicit false

/-!
LoopRule (scratch, prooftech, D-P71 / T3.9 restated): an INVARIANT rule for a Yul `for` loop whose
bound is a variable. `wpL` (`WP.lean:167`) unrolls by fuel, so it cannot run a loop whose trip
count is symbolic; this file replaces the unrolling by an invariant and keeps `wp` for ONE
iteration.

  §1 `IterAll`, `allRuns_loop`        the rule on the big-step judgment (no engine, no fuel)
  §2 `wpIter`, `allRuns_loop_wp`,
     `allRuns_for_wp`,
     `allRuns_for_cons_wp`            the same rule as an `allRuns_cons_wp`-style cut (WP.lean:401)
     `allRuns_for_cons_wp_count`      the invariant indexed by a counter
  §3 W12 witness                      `sumLoop_all`: a loop with bound `n : Nat`, every `n < 2^256`
  §4 W12 falsifiers                   preservation dropped; the bound hypothesis dropped
  §5 the loops of the generated verifier that need the rule (table)

NO VARIANT IS NEEDED. `AllRuns` quantifies over big-step derivations, which are finite, so the rule
is proved by induction on the DERIVATION, not on a remaining-iteration count: the invariant need not
decrease. (`ExecLoopAll.countdown_or_halt`, `Midfall/Yul/Contracts.lean:298`, inducts on the count
and so needs `zero : Inv 0 → guard = 0`; that hypothesis is absent here.) A variant IS needed for the
existence half (a run exists) - that is the vendored `ExecLoop.countdown`
(`vendor/yul-semantics/YulSemantics/Contract.lean:176`), normal arm only.

NO `sorry` IN THIS FILE.
-/
namespace Midfall.Yul.LoopRule
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac
open YulSemantics

/-! ## 1. The rule on the big-step judgment -/
section Semantic
variable {D : Dialect} [DecidableEq D.Value]

/-- What ONE iteration must establish from the loop head `(V, st)`, for EVERY evaluation of the
    condition, EVERY run of the body and EVERY run of the post block. `Q` is the loop's
    postcondition on `(Vend, stend, outcome)`; the outcome of a loop is `normal` (guard false, or
    `break`), `leave`, or `halt`. -/
structure IterAll (funs : FunEnv D) (c : Expr D.Op) (post body : Block D.Op)
    (Inv : VEnv D → D.State → Prop) (Q : VEnv D → D.State → Outcome → Prop)
    (V : VEnv D) (st : D.State) : Prop where
  /-- the condition halts -/
  condHalt : ∀ st1, EvalExpr D funs V st c (.halt st1) → Q V st1 .halt
  /-- the condition is false: the loop exits normally -/
  exit : ∀ cv st1, EvalExpr D funs V st c (.vals [cv] st1) → cv = D.zero → Q V st1 .normal
  /-- the condition is true: the body runs, then the post block, and the invariant holds again -/
  iter : ∀ cv st1, EvalExpr D funs V st c (.vals [cv] st1) → cv ≠ D.zero →
    ∀ Vb stb ob, ExecStmt D funs V st1 (.block body) Vb stb ob →
      match ob with
      | .normal | .«continue» =>
          ∀ Vp stp op, ExecStmt D funs Vb stb (.block post) Vp stp op →
            (op = .normal → Inv Vp stp) ∧ (op = .halt → Q Vp stp .halt)
      | .«break» => Q Vb stb .normal
      | .leave => Q Vb stb .leave
      | .halt => Q Vb stb .halt

/-- Induction on the derivation. Every non-loop constructor is excluded by its `Code` index. -/
theorem loop_inv_aux {funs : FunEnv D} {V : VEnv D} {st : D.State} {code : Code D.Op} {res : Res D}
    (h : Step D funs V st code res) :
    ∀ (c : Expr D.Op) (post body : Block D.Op), code = .loop c post body →
    ∀ (Inv : VEnv D → D.State → Prop) (Q : VEnv D → D.State → Outcome → Prop),
      (∀ V st, Inv V st → IterAll funs c post body Inv Q V st) → Inv V st →
      ∀ V' st' o, res = .sres V' st' o → Q V' st' o := by
  induction h with
  | loopDone hc hz =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      exact (hstep _ _ hInv).exit _ _ hc hz
  | loopCondHalt hc =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      exact (hstep _ _ hInv).condHalt _ hc
  | loopStep hc hnz hbody hob hpost hrec _ _ _ ihrec =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode
      have hb := (hstep _ _ hInv).iter _ _ hc hnz _ _ _ hbody
      refine ihrec _ _ _ rfl Inv Q hstep ?_ V' st' o hres
      rcases hob with rfl | rfl
      · exact (hb _ _ _ hpost).1 rfl
      · exact (hb _ _ _ hpost).1 rfl
  | loopPostHalt hc hnz hbody hob hpost =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      have hb := (hstep _ _ hInv).iter _ _ hc hnz _ _ _ hbody
      rcases hob with rfl | rfl
      · exact (hb _ _ _ hpost).2 rfl
      · exact (hb _ _ _ hpost).2 rfl
  | loopBreak hc hnz hbody =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      exact (hstep _ _ hInv).iter _ _ hc hnz _ _ _ hbody
  | loopLeave hc hnz hbody =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      exact (hstep _ _ hInv).iter _ _ hc hnz _ _ _ hbody
  | loopBodyHalt hc hnz hbody =>
      intro c post body hcode Inv Q hstep hInv V' st' o hres
      cases hcode; cases hres
      exact (hstep _ _ hInv).iter _ _ hc hnz _ _ _ hbody
  | _ => intro c post body hcode; cases hcode

/-- **THE LOOP RULE (semantic form).** If the invariant holds at the head and one iteration
    re-establishes it or ends in `Q`, EVERY run of the loop ends in `Q`. No fuel, no bound. -/
theorem allRuns_loop {funs : FunEnv D} {c : Expr D.Op} {post body : Block D.Op}
    (Inv : VEnv D → D.State → Prop) (Q : VEnv D → D.State → Outcome → Prop)
    (hstep : ∀ V st, Inv V st → IterAll funs c post body Inv Q V st) :
    ∀ V st, Inv V st →
      ∀ V' st' o, ExecLoop D funs V st c post body V' st' o → Q V' st' o :=
  fun _ _ hInv V' st' o h => loop_inv_aux h c post body rfl Inv Q hstep hInv V' st' o rfl

end Semantic

/-! ## 2. The rule as an engine cut -/
section Engine
variable (D : Dialect) [DecidableEq D.Value] (B : BT D) (C : CT D)

/-- `wpL` (`WP.lean:167`) for ONE iteration, with the recursive call replaced by the invariant.
    A `wp` goal: `wp_run` executes the condition, the body and the post block symbolically. -/
def wpIter (n : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (c : Expr D.Op)
    (post body : Block D.Op) (Inv : VEnv D → D.State → Prop)
    (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  wpE D B C n funs V st c fun r =>
    match r with
    | .vals [cv] st1 =>
        (cv = D.zero → Q V st1 .normal) ∧
        (cv ≠ D.zero →
          wpS D B C n funs V st1 (.block body) fun Vb stb ob =>
            match ob with
            | .normal | .«continue» =>
                wpS D B C n funs Vb stb (.block post) fun Vp stp op =>
                  match op with
                  | .normal => Inv Vp stp
                  | .halt => Q Vp stp .halt
                  | _ => False
            | .«break» => Q Vb stb .normal
            | .leave => Q Vb stb .leave
            | .halt => Q Vb stb .halt)
    | .vals _ _ => False
    | .halt st1 => Q V st1 .halt

/-- Expression projection of `wp_sound` (`WP.lean:209`; the file names only the statement ones). -/
theorem wpE_sound (hB : BSound D B) (hC : CSound D C) {n funs V st e Q}
    (h : wpE D B C n funs V st e Q) : ∀ r, EvalExpr D funs V st e r → Q r :=
  (wp_sound D B C hB hC n).1 funs V st e Q h

theorem iterAll_of_wp (hB : BSound D B) (hC : CSound D C) {n : Nat} {funs : FunEnv D}
    {V : VEnv D} {st : D.State} {c : Expr D.Op} {post body : Block D.Op}
    {Inv : VEnv D → D.State → Prop} {Q : VEnv D → D.State → Outcome → Prop}
    (h : wpIter D B C n funs V st c post body Inv Q) : IterAll funs c post body Inv Q V st := by
  refine ⟨?_, ?_, ?_⟩
  · intro st1 hc
    exact wpE_sound D B C hB hC h _ hc
  · intro cv st1 hc hz
    have h1 := wpE_sound D B C hB hC h _ hc
    exact h1.1 hz
  · intro cv st1 hc hnz Vb stb ob hbody
    have h1 := wpE_sound D B C hB hC h _ hc
    have h3 := wpS_sound D B C hB hC (h1.2 hnz) _ _ _ hbody
    cases ob with
    | normal =>
        intro Vp stp op hpost
        have h4 := wpS_sound D B C hB hC h3 _ _ _ hpost
        cases op <;> first
          | exact h4.elim
          | exact ⟨fun _ => h4, fun e => (nomatch e)⟩
          | exact ⟨fun e => (nomatch e), fun _ => h4⟩
    | «continue» =>
        intro Vp stp op hpost
        have h4 := wpS_sound D B C hB hC h3 _ _ _ hpost
        cases op <;> first
          | exact h4.elim
          | exact ⟨fun _ => h4, fun e => (nomatch e)⟩
          | exact ⟨fun e => (nomatch e), fun _ => h4⟩
    | «break» => exact h3
    | «leave» => exact h3
    | halt => exact h3

/-- **THE LOOP RULE (engine form), loop only.** -/
theorem allRuns_loop_wp (hB : BSound D B) (hC : CSound D C) {n : Nat} {funs : FunEnv D}
    {c : Expr D.Op} {post body : Block D.Op}
    (Inv : VEnv D → D.State → Prop) (Q : VEnv D → D.State → Outcome → Prop)
    (hstep : ∀ V st, Inv V st → wpIter D B C n funs V st c post body Inv Q) :
    ∀ V st, Inv V st →
      ∀ V' st' o, ExecLoop D funs V st c post body V' st' o → Q V' st' o :=
  allRuns_loop Inv Q fun V st h => iterAll_of_wp D B C hB hC (hstep V st h)

/-- **THE LOOP RULE, one `for` statement.** `init` is executed by `wp` and must establish the
    invariant; the loop's own scope is `hoist D init :: funs` and its exit environment is
    `restore V Vend` (`Step.forLoop`, `BigStep.lean:269`). -/
theorem allRuns_for_wp (hB : BSound D B) (hC : CSound D C) {n : Nat} {funs : FunEnv D}
    {V : VEnv D} {st : D.State} {init : Block D.Op} {c : Expr D.Op} {post body : Block D.Op}
    (Inv : VEnv D → D.State → Prop) {Q : VEnv D → D.State → Outcome → Prop}
    (hinit : wpSS D B C n (hoist D init :: funs) V st init fun Vi sti oi =>
        match oi with
        | .normal => Inv Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False)
    (hstep : ∀ Vi sti, Inv Vi sti →
        wpIter D B C n (hoist D init :: funs) Vi sti c post body Inv
          fun Vend stend o => Q (restore V Vend) stend o) :
    ∀ V' st' o, ExecStmt D funs V st (.forLoop init c post body) V' st' o → Q V' st' o := by
  intro V' st' o hrun
  cases hrun with
  | forLoop hi hl =>
      have hInv := wpSS_sound D B C hB hC hinit _ _ _ hi
      exact allRuns_loop_wp D B C hB hC Inv _ hstep _ _ hInv _ _ _ hl
  | forInitHalt hi => exact wpSS_sound D B C hB hC hinit _ _ _ hi

/-- **THE LOOP RULE AS A CUT (the form a block-row proof applies).** The shape of
    `allRuns_cons_wp` (`WP.lean:401`) at a `for` statement: `init` and ONE iteration are `wp`
    goals for `wp_run`; the continuation after a normal exit is SEMANTIC - every run of `rest`
    from the restored environment - wrapped in `Hold` so that `wp_run` stops there and the proof
    continues with `allRuns_of_wp`, `allRuns_cons_wp` or this rule again. -/
theorem allRuns_for_cons_wp (hB : BSound D B) (hC : CSound D C) {n : Nat} {funs : FunEnv D}
    {V : VEnv D} {st : D.State} {init : Block D.Op} {c : Expr D.Op} {post body : Block D.Op}
    {rest : Block D.Op} (Inv : VEnv D → D.State → Prop)
    {Q : VEnv D → D.State → Outcome → Prop}
    (hinit : wpSS D B C n (hoist D init :: funs) V st init fun Vi sti oi =>
        match oi with
        | .normal => Inv Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False)
    (hstep : ∀ Vi sti, Inv Vi sti →
        wpIter D B C n (hoist D init :: funs) Vi sti c post body Inv
          fun Vend stend o =>
            match o with
            | .normal => Hold (AllRuns funs (restore V Vend) stend rest Q)
            | _ => Q (restore V Vend) stend o) :
    AllRuns funs V st (.forLoop init c post body :: rest) Q := by
  intro V' st' o hrun
  cases hrun with
  | seqCons h1 h2 =>
      cases h1 with
      | forLoop hi hl =>
          have hInv := wpSS_sound D B C hB hC hinit _ _ _ hi
          have hk : Hold (AllRuns funs _ _ rest Q) :=
            allRuns_loop_wp D B C hB hC Inv _ hstep _ _ hInv _ _ _ hl
          exact hk.elim _ _ _ h2
  | seqStop h1 hne =>
      cases h1 with
      | forLoop hi hl =>
          have hInv := wpSS_sound D B C hB hC hinit _ _ _ hi
          have hk := allRuns_loop_wp D B C hB hC Inv _ hstep _ _ hInv _ _ _ hl
          cases o <;> first | exact absurd rfl hne | exact hk
      | forInitHalt hi => exact wpSS_sound D B C hB hC hinit _ _ _ hi

/-- The same cut with the invariant INDEXED BY A COUNTER (`Inv k`: `k` iterations remain, or any
    other measure). The index is existential at every head, so no relation between consecutive
    indices is imposed - see the file header: a decrease is not needed for `AllRuns`. -/
theorem allRuns_for_cons_wp_count (hB : BSound D B) (hC : CSound D C) {n : Nat} {funs : FunEnv D}
    {V : VEnv D} {st : D.State} {init : Block D.Op} {c : Expr D.Op} {post body : Block D.Op}
    {rest : Block D.Op} (Inv : Nat → VEnv D → D.State → Prop)
    {Q : VEnv D → D.State → Outcome → Prop}
    (hinit : wpSS D B C n (hoist D init :: funs) V st init fun Vi sti oi =>
        match oi with
        | .normal => ∃ k, Inv k Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False)
    (hstep : ∀ k Vi sti, Inv k Vi sti →
        wpIter D B C n (hoist D init :: funs) Vi sti c post body (fun Vp stp => ∃ k', Inv k' Vp stp)
          fun Vend stend o =>
            match o with
            | .normal => Hold (AllRuns funs (restore V Vend) stend rest Q)
            | _ => Q (restore V Vend) stend o) :
    AllRuns funs V st (.forLoop init c post body :: rest) Q :=
  allRuns_for_cons_wp D B C hB hC (fun V st => ∃ k, Inv k V st) hinit
    (fun Vi sti ⟨k, h⟩ => hstep k Vi sti h)

end Engine

#print axioms allRuns_loop
#assert_axioms allRuns_loop [propext]
#print axioms allRuns_for_cons_wp
#assert_axioms allRuns_for_cons_wp [propext]
#print axioms allRuns_for_cons_wp_count
#assert_axioms allRuns_for_cons_wp_count [propext]

/-! ## 3. W12 WITNESS: the rule applied to a loop whose bound is a variable

  `for { let i := 0 } lt(i, n) { i := add(i, 1) } { acc := add(acc, i) }` followed by
  `acc := add(acc, 1)`, for EVERY `n < 2^256`, any call relation, any gas oracle, any scope.
  `init`, one iteration and the rest of the block are each ONE `wp_run`; no `native_decide`. -/
section Witness
open YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

def sumLoop (n : Nat) : Stmt EVM.Op :=
  Stmt.forLoop [Stmt.letDecl ["i"] (some (Expr.lit (.number 0)))]
    (Expr.builtin Op.lt [Expr.var "i", Expr.lit (.number n)])
    [Stmt.assign ["i"] (Expr.builtin Op.add [Expr.var "i", Expr.lit (.number 1)])]
    [Stmt.assign ["acc"] (Expr.builtin Op.add [Expr.var "acc", Expr.var "i"])]

/-- The rest of the block after the loop. -/
def sumRest : Block EVM.Op :=
  [Stmt.assign ["acc"] (Expr.builtin Op.add [Expr.var "acc", Expr.lit (.number 1)])]

theorem tri_succ (i : Nat) : (i + 1) * i / 2 = i * (i - 1) / 2 + i := by
  cases i with
  | zero => simp
  | succ j =>
      have h : (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) := by ring
      rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      simp

/-- `lt` on two in-range literals is `<` on `Nat`. THIS is where the bound is used. -/
theorem ult_ofNat {i n : Nat} (hi : i < 2 ^ 256) (hn : n < 2 ^ 256) :
    (BitVec.ofNat 256 i).ult (BitVec.ofNat 256 n) = decide (i < n) := by
  have h1 : (BitVec.ofNat 256 i).toNat = i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hi
  have h2 : (BitVec.ofNat 256 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  simp only [BitVec.ult, h1, h2]

theorem lt_guard_false {i n : Nat} (hi : i < 2 ^ 256) (hn : n < 2 ^ 256)
    (h : b2w ((BitVec.ofNat 256 i).ult (BitVec.ofNat 256 n)) = (0 : U256)) : n ≤ i := by
  rw [ult_ofNat hi hn] at h
  by_contra hlt
  have hd : decide (i < n) = true := by simpa using Nat.lt_of_not_le hlt
  rw [hd] at h
  exact absurd h (by decide)

theorem lt_guard_true {i n : Nat} (hi : i < 2 ^ 256) (hn : n < 2 ^ 256)
    (h : b2w ((BitVec.ofNat 256 i).ult (BitVec.ofNat 256 n)) ≠ (0 : U256)) : i < n := by
  rw [ult_ofNat hi hn] at h
  by_contra hge
  have hd : decide (i < n) = false := by simpa using hge
  rw [hd] at h
  exact h (by decide)

set_option maxRecDepth 10000 in
set_option wpLets false in
set_option profiler true in
set_option profiler.threshold 50 in
/-- **WITNESS.** Every run of the loop-then-rest block is normal, leaves the state alone and
    ends with `acc = a0 + n(n-1)/2 + 1`, for every bound `n < 2^256`. -/
theorem sumLoop_all (c : ExternalCalls) (g : ExternalGas) (funs : FunEnv (Bridge.Dialect c g))
    (n : Nat) (hn : n < 2 ^ 256) (st : EvmState) (a0 : U256) :
    AllRuns funs [("acc", a0)] st (sumLoop n :: sumRest)
      fun V' st' o => Hold (o = .normal ∧ st' = st ∧
        V' = [("acc", a0 + BitVec.ofNat 256 (n * (n - 1) / 2) + 1)]) := by
  refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _) (Bopen_sound c g)
    (Cnone_sound _) (n := 20)
    (fun V st' => ∃ i, i ≤ n ∧ st' = st ∧
      V = [("i", BitVec.ofNat 256 i), ("acc", a0 + BitVec.ofNat 256 (i * (i - 1) / 2))]) ?_ ?_
  · -- init establishes the invariant at i = 0
    wp_run
    refine ⟨0, Nat.zero_le _, rfl, ?_⟩
    show [("i", (BitVec.ofNat 256 0 : U256)), ("acc", a0)] = _
    simp
  · -- one iteration, from an arbitrary head state satisfying the invariant
    rintro Vi sti ⟨i, hi, rfl, rfl⟩
    wp_run
    · -- the guard is false: i = n, and the rest of the block runs
      rename_i h
      have hin : i = n := Nat.le_antisymm hi (lt_guard_false (Nat.lt_of_le_of_lt hi hn) hn h)
      subst hin
      refine ⟨allRuns_of_wp 20 ?_⟩
      wp_run
      exact ⟨⟨rfl, rfl, rfl⟩⟩
    · -- the guard is true: i < n, body and post run, the invariant holds at i + 1
      rename_i h
      have hlt : i < n := lt_guard_true (Nat.lt_of_le_of_lt hi hn) hn h
      refine ⟨i + 1, hlt, rfl, ?_⟩
      show [("i", (BitVec.ofNat 256 i + BitVec.ofNat 256 1 : U256)),
        ("acc", a0 + BitVec.ofNat 256 (i * (i - 1) / 2) + BitVec.ofNat 256 i)] = _
      simp only [Nat.add_sub_cancel]
      rw [tri_succ, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc]

#print axioms sumLoop_all
#assert_axioms sumLoop_all [propext, Classical.choice, Quot.sound]

/-! ## 4. W12 FALSIFIERS -/

/-- `wpIter` with the PRESERVATION obligation removed: the post block's normal exit owes nothing. -/
def wpIterNoPres (D : Dialect) [DecidableEq D.Value] (B : BT D) (C : CT D) (n : Nat)
    (funs : FunEnv D) (V : VEnv D) (st : D.State) (c : Expr D.Op) (post body : Block D.Op)
    (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  wpE D B C n funs V st c fun r =>
    match r with
    | .vals [cv] st1 =>
        (cv = D.zero → Q V st1 .normal) ∧
        (cv ≠ D.zero →
          wpS D B C n funs V st1 (.block body) fun Vb stb ob =>
            match ob with
            | .normal | .«continue» =>
                wpS D B C n funs Vb stb (.block post) fun Vp stp op =>
                  match op with
                  | .normal => True
                  | .halt => Q Vp stp .halt
                  | _ => False
            | .«break» => Q Vb stb .normal
            | .leave => Q Vb stb .leave
            | .halt => Q Vb stb .halt)
    | .vals _ _ => False
    | .halt st1 => Q V st1 .halt

/-- `allRuns_loop_wp` at the open Bridge dialect, with invariant preservation dropped. -/
def LoopRuleNoPres (c : ExternalCalls) (g : ExternalGas) : Prop :=
  ∀ (n : Nat) (funs : FunEnv (Bridge.Dialect c g)) (cnd : Expr EVM.Op) (post body : Block EVM.Op)
    (Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop)
    (Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop),
    (∀ V st, Inv V st →
      wpIterNoPres (Bridge.Dialect c g) (Bopen c g) (Cnone _) n funs V st cnd post body Q) →
    ∀ V st, Inv V st →
      ∀ V' st' o, ExecLoop (Bridge.Dialect c g) funs V st cnd post body V' st' o → Q V' st' o

/-- **FALSIFIER 1 (rule level).** Without preservation the rule is FALSE, for every call relation
    and gas oracle: `for {} iszero(x) { x := 1 } {}` from `x = 0` satisfies every remaining
    hypothesis for `Inv = Q = (x = 0)`, and its one run ends with `x = 1`. -/
theorem loopRuleNoPres_false (c : ExternalCalls) (g : ExternalGas) : ¬ LoopRuleNoPres c g := by
  intro H
  have hrun : ExecLoop (Bridge.Dialect c g) [] [("x", (0 : U256))] EvmState.init
      (Expr.builtin Op.iszero [Expr.var "x"]) [Stmt.assign ["x"] (Expr.lit (.number 1))] []
      [("x", (1 : U256))] EvmState.init .normal := by
    have hb0 : (Bridge.Dialect c g).Builtin Op.iszero [(0 : U256)] EvmState.init
        (.ok [(1 : U256)] EvmState.init) := by
      show stepOp Op.iszero [(0 : U256)] EvmState.init = some _
      rfl
    have hb1 : (Bridge.Dialect c g).Builtin Op.iszero [(1 : U256)] EvmState.init
        (.ok [(0 : U256)] EvmState.init) := by
      show stepOp Op.iszero [(1 : U256)] EvmState.init = some _
      rfl
    refine Step.loopStep (D := Bridge.Dialect c g) (cv := (1 : U256)) (st1 := EvmState.init) (Vb := [("x", (0 : U256))])
      (stb := EvmState.init) (ob := .normal) (Vp := [("x", (1 : U256))]) (stp := EvmState.init)
      ?_ ?_ ?_ (Or.inl rfl) ?_ ?_
    · exact Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil (Step.var rfl)) hb0
    · show (1 : U256) ≠ 0
      decide
    · refine Step.block (D := Bridge.Dialect c g) (Vb := [("x", (0 : U256))]) ?_
      exact Step.seqNil
    · refine Step.block (D := Bridge.Dialect c g) (Vb := [("x", (1 : U256))]) ?_
      refine Step.seqCons (D := Bridge.Dialect c g) (V1 := [("x", (1 : U256))]) (st1 := EvmState.init) ?_ Step.seqNil
      exact Step.assignVal (D := Bridge.Dialect c g) (vals := [(1 : U256)]) Step.lit rfl
    · refine Step.loopDone (D := Bridge.Dialect c g) (cv := (0 : U256)) ?_ rfl
      exact Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil (Step.var rfl)) hb1
  have h := H 20 [] _ _ _ (fun V _ => V = [("x", (0 : U256))])
    (fun V _ _ => V = [("x", (0 : U256))])
    (by rintro V st rfl; wp_run) _ _ rfl _ _ _ hrun
  have h' : ([("x", (1 : U256))] : List (String × U256)) = [("x", (0 : U256))] := h
  exact absurd h' (by decide)

/-- **FALSIFIER 2 (side condition of the witness).** `sumLoop_all` without `n < 2^256` is FALSE:
    at `n = 2^256` the literal bound is the word 0, the loop runs zero times and `acc` ends at
    `a0 + 1`, not `a0 + 2^255 + 1`. -/
theorem sumLoop_all_needs_bound (c : ExternalCalls) (g : ExternalGas) :
    ¬ (∀ (funs : FunEnv (Bridge.Dialect c g)) (n : Nat) (st : EvmState) (a0 : U256),
        AllRuns funs [("acc", a0)] st (sumLoop n :: sumRest)
          fun V' st' o => Hold (o = .normal ∧ st' = st ∧
            V' = [("acc", a0 + BitVec.ofNat 256 (n * (n - 1) / 2) + 1)])) := by
  intro H
  have hrun : ExecStmts (Bridge.Dialect c g) [] [("acc", (0 : U256))] EvmState.init
      (sumLoop (2 ^ 256) :: sumRest) [("acc", (1 : U256))] EvmState.init .normal := by
    have hlt : (Bridge.Dialect c g).Builtin Op.lt [(0 : U256), (0 : U256)] EvmState.init
        (.ok [(0 : U256)] EvmState.init) := by
      show stepOp Op.lt [(0 : U256), (0 : U256)] EvmState.init = some _
      rfl
    have hadd : (Bridge.Dialect c g).Builtin Op.add [(0 : U256), (1 : U256)] EvmState.init
        (.ok [(1 : U256)] EvmState.init) := by
      show stepOp Op.add [(0 : U256), (1 : U256)] EvmState.init = some _
      rfl
    refine Step.seqCons (D := Bridge.Dialect c g) (V1 := [("acc", (0 : U256))]) (st1 := EvmState.init) ?_ ?_
    · refine Step.forLoop (D := Bridge.Dialect c g) (Vinit := [("i", (0 : U256)), ("acc", (0 : U256))])
        (stinit := EvmState.init) (Vend := [("i", (0 : U256)), ("acc", (0 : U256))]) ?_ ?_
      · refine Step.seqCons (D := Bridge.Dialect c g) (V1 := [("i", (0 : U256)), ("acc", (0 : U256))])
          (st1 := EvmState.init) ?_ Step.seqNil
        exact Step.letVal (D := Bridge.Dialect c g) (vals := [(0 : U256)]) Step.lit rfl
      · refine Step.loopDone (D := Bridge.Dialect c g) (cv := (0 : U256)) ?_ rfl
        refine Step.builtinOk (D := Bridge.Dialect c g) (argvals := [(0 : U256), (0 : U256)]) (st1 := EvmState.init) ?_ hlt
        exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)
    · refine Step.seqCons (D := Bridge.Dialect c g) (V1 := [("acc", (1 : U256))]) (st1 := EvmState.init) ?_ Step.seqNil
      refine Step.assignVal (D := Bridge.Dialect c g) (vals := [(1 : U256)]) ?_ rfl
      refine Step.builtinOk (D := Bridge.Dialect c g) (argvals := [(0 : U256), (1 : U256)]) (st1 := EvmState.init) ?_ hadd
      exact Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var rfl)
  have h := H [] (2 ^ 256) EvmState.init 0 _ _ _ hrun
  have h' : ([("acc", (1 : U256))] : List (String × U256)) =
      [("acc", (0 : U256) + BitVec.ofNat 256 (2 ^ 256 * (2 ^ 256 - 1) / 2) + 1)] := h.elim.2.2
  exact absurd h' (by decide)

#print axioms loopRuleNoPres_false
#print axioms sumLoop_all_needs_bound
end Witness

/-! ## 5. The loops of the generated verifier that need the rule

  READ: `proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol` (F1; line numbers
  are of that file). "Bound at F1" is the numeral in the text. "Bound for every R" is INFERRED from
  where the generator takes the numeral (not checked against the Lean emitter): a PLAN COUNT is a
  `Nat` expression in plan-view fields, so a variable under D-P71; none is read from calldata.

  line(s)             block / helper          shape                                   bound at F1          bound for every R            body calls
  ------------------  ----------------------  --------------------------------------  -------------------  ---------------------------  -------------------------
  1233                transcript: instances   end in init; `cptr += 0x20` in post     0x20                 32 * numInstances (VK)       common_word
  1275 1295 1314      transcript: G1 reads    `let end := add(proof_cptr, N)`;        0x400 0x80 0x180     0x80 * plan count            common_uncompressed_g1
  1332 1357 1380        (advice, lookup-m,      post EMPTY, `proof_cptr += 0x80`      0x80 0x80 0x200        (per commitment family)
                        perm-z, helpers,        in the body
                        trashcan, quotient)
  1405 1460           transcript: eval reads  same, step 0x20                         0x600 0x60           32 * plan count              fail (under `if`), common_word
  1509                lagrange: x^n           `lt(idx, k)`, counter in post           k = 6                k (VK field)                 none
  1521 1535           lagrange: denominators  `lt(mptr, mptr_end)`, init binds        0x140                32 * plan count              none
                                                another variable
  1546                lagrange: l_blind       `lt(l_i_cptr, end)`                     0x120                32 * plan count              none
  1556                lagrange: instance      TWO variables advanced in post          0x20                 32 * numInstances            none
  833 880             helper `batch_invert`   `for {} lt(mptr, sub(end, 0x20)) {}`    arguments            caller's layout constant     none; body 1 has `leave`;
                                                up-walk, then a DOWN-walk                                    + plan count                 a `staticcall` sits between
  1727 1739           quotient prelude        counters                                0x80, 22             plan counts                  none
  1894                quotient interpreter    `for {} lt(q_pc, q_end) {}` + `switch`  bytecode length      DATA: the bytecode in        q_program_fail (14 sites),
                                                                                                             memory (from the key)        q_pow5
  1988-2042           quotient, perm case     counters 5 8 3 3 3 and a nested         plan counts          plan counts                  none
                        (inside 1894)           `q_perm_j` from start to end
  2565                pcs                     `lt(idx, k)`                            k                    k (VK field)                 none
  2626 2674 2702      pcs                     counters                                0x20 0x21 0x5        plan counts (set sizes)      none
  957 998             accumulator helpers     counters on arguments                   not called at F1     outside `SupportedV3`        -
  369 495 504         require_eip2537_…       counters                                0x300 0x1d60         outside the `verifyProof`    -
                                                                                                             body

  WHAT THE TABLE SAYS ABOUT THE RULE.
  * Every shape above is an instance of `allRuns_for_cons_wp`: the rule does not care whether the
    counter moves in the post block or in the body, up or down, or how many variables move.
  * Four families call a helper inside the body (instances, G1 reads, eval reads, the interpreter):
    their iteration `wp` goal needs the helper's SUMMARY in the `C` table (HLP.1), because the
    scope is a variable (`VKP.lean` §2).
  * Only the quotient interpreter has a data-dependent bound; its invariant is over the program
    counter and the decoded prefix, not over a count.
  * Each pointer walk needs a no-wrap side condition of the form `ptr + N < 2^256` (the analogue
    of `n < 2^256` in the witness, shown necessary by `sumLoop_all_needs_bound`). -/

end Midfall.Yul.LoopRule
