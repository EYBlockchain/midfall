/-
  Midfall.Yul.Wp

  THE WP ENGINE (T3.1, PLAN-V3): a fuel-indexed DEMONIC weakest-precondition transformer over the
  vendored AST, generic in the dialect, and its SOUNDNESS against the big-step judgment `Step`.
  Ported VERBATIM from the proved scratch source
  `docs/plans/V3-evidence/lean/prooftech/WP.lean`; the only changes are the namespace
  (`Midfall.Scratch.ProofTech` -> `Midfall.Yul.Wp`) and this header. Nothing is restated: the
  definitions, the mutual block, and every proof step are the ones that compiled in the evidence
  area (`bash docs/plans/V3-evidence/check.sh prooftech` prints `ok prooftech/WP` with
  ZERO sorry warnings).

  WHY IT IS HERE. M5/M6 discharge `rejects_correct` / `complete_correct` / `total_correct` for a
  block row by applying `wp_sound` / `wpSS_sound` to the row's slice, so the engine must be a tree
  module and not a scratch file. `Midfall/Yul/WpBridge.lean` instantiates it at the open Bridge
  dialect; `Midfall/Yul/WpFalsifiers.lean` exhibits the falsifiers that keep the statements
  non-vacuous (W12).

  THE SHAPE OF THE CLAIM, in one line: `wp 0 = False` and every stuck configuration is `False`, so
  `wp n ... Q` says "for every oracle answer the code terminates within fuel n, never gets stuck,
  and ends in Q" - a DEMONIC reading of the dialect relation, which is what makes a proof of it
  about an open (nondeterministic) dialect mean something.

  AXIOMS (pinned by `#assert_axioms` in Midfall/Yul/WpFalsifiers.lean): `wp_sound` rests on
  `[propext]` alone; no `sorryAx`, no `native_decide` (D-P71 - this engine is inside the cone of
  `lowering_correct`).
-/
import YulSemantics
import YulSemantics.Contract
set_option autoImplicit false

/-!
WP (scratch, prooftech): a fuel-indexed DEMONIC weakest-precondition transformer over the vendored
AST, generic in the dialect, and its soundness against the big-step judgment `Step`.

* `B` is the BUILT-IN transformer: `B op args st Q` must imply `Q r` for EVERY result `r` the
  dialect's relation admits. For a local op it is "evaluate stepOp"; for `staticcall` under the
  permissive relation it is "for all permitted responses"; for `gas()` "for all oracle words".
* `C` is the CALL-SUMMARY table: `C funs fn args st = some T` replaces inlining of `fn`'s body by a
  previously proved contract `T` (helper summaries, loop-carrying helpers).
* `wp 0 = False`, and every stuck configuration is `False`: a proof of `wp n ... Q` therefore says
  "for every oracle answer the code terminates within fuel n, never gets stuck, and ends in Q".
-/
namespace Midfall.Yul.Wp
open YulSemantics

/-- A SEQUENCE POINT. Logically the identity; a STRUCTURE so that kernel head reduction stops here
    (after each statement and each loop iteration), which is where the driver normalises the
    symbolic state (literals for concrete values, `let`-names for symbolic ones). -/
structure Stop (P : Prop) : Prop where
  intro ::
  elim : P

section WP
variable (D : Dialect) [DecidableEq D.Value]

/-- Built-in transformer. -/
abbrev BT : Type := D.Op → List D.Value → D.State → (BuiltinResult D.Value D.State → Prop) → Prop
/-- Call-summary table. -/
abbrev CT : Type := FunEnv D → Ident → List D.Value → D.State → Option ((EResult D → Prop) → Prop)

variable (B : BT D) (C : CT D)

mutual
/-- wp of an expression. -/
def wpE (fuel : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (e : Expr D.Op)
    (Q : EResult D → Prop) : Prop :=
  match fuel with
  | 0 => False
  | n + 1 =>
    match e with
    | .lit l => Q (.vals [D.litValue l] st)
    | .var x =>
        match VEnv.get V x with
        | some v => Q (.vals [v] st)
        | none => False
    | .builtin op args =>
        wpA n funs V st args fun r =>
          match r with
          | .vals argvals st1 =>
              B op argvals st1 fun br =>
                match br with
                | .ok rets st2 => Q (.vals rets st2)
                | .halt st2 => Q (.halt st2)
          | .halt st1 => Q (.halt st1)
    | .call fn args =>
        wpA n funs V st args fun r =>
          match r with
          | .vals argvals st1 =>
              match C funs fn argvals st1 with
              | some T => T Q
              | none =>
                  match lookupFun funs fn with
                  | some (decl, cenv) =>
                      argvals.length = decl.params.length ∧
                      wpS n cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
                        (.block decl.body) fun Vend st2 o =>
                          match o with
                          | .normal | .leave =>
                              Q (.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2)
                          | .halt => Q (.halt st2)
                          | _ => False
                  | none => False
          | .halt st1 => Q (.halt st1)

/-- wp of an argument list (right-to-left). -/
def wpA (fuel : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (args : List (Expr D.Op))
    (Q : EResult D → Prop) : Prop :=
  match fuel with
  | 0 => False
  | n + 1 =>
    match args with
    | [] => Q (.vals [] st)
    | e :: rest =>
        wpA n funs V st rest fun r =>
          match r with
          | .vals restvals st1 =>
              wpE n funs V st1 e fun r2 =>
                match r2 with
                | .vals [v] st2 => Q (.vals (v :: restvals) st2)
                | .vals _ _ => False
                | .halt st2 => Q (.halt st2)
          | .halt st1 => Q (.halt st1)

/-- wp of a statement. -/
def wpS (fuel : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (s : Stmt D.Op)
    (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | n + 1 =>
    match s with
    | .funDef .. => Q V st .normal
    | .block body =>
        wpSS n (hoist D body :: funs) V st body fun Vb stb o => Q (restore V Vb) stb o
    | .letDecl vars none => Q (bindZeros D vars ++ V) st .normal
    | .letDecl vars (some e) =>
        wpE n funs V st e fun r =>
          match r with
          | .vals vals st1 => vals.length = vars.length ∧ Q (vars.zip vals ++ V) st1 .normal
          | .halt st1 => Q V st1 .halt
    | .assign vars e =>
        wpE n funs V st e fun r =>
          match r with
          | .vals vals st1 =>
              vals.length = vars.length ∧ Q (VEnv.setMany V vars vals) st1 .normal
          | .halt st1 => Q V st1 .halt
    | .exprStmt e =>
        wpE n funs V st e fun r =>
          match r with
          | .vals [] st1 => Q V st1 .normal
          | .vals _ _ => False
          | .halt st1 => Q V st1 .halt
    | .cond c body =>
        wpE n funs V st c fun r =>
          match r with
          | .vals [cv] st1 =>
              (cv = D.zero → Q V st1 .normal) ∧
              (cv ≠ D.zero → wpS n funs V st1 (.block body) Q)
          | .vals _ _ => False
          | .halt st1 => Q V st1 .halt
    | .switch c cases dflt =>
        wpE n funs V st c fun r =>
          match r with
          | .vals [cv] st1 => wpS n funs V st1 (.block (selectSwitch D cv cases dflt)) Q
          | .vals _ _ => False
          | .halt st1 => Q V st1 .halt
    | .forLoop init c post body =>
        wpSS n (hoist D init :: funs) V st init fun Vinit stinit oinit =>
          match oinit with
          | .normal =>
              wpL n (hoist D init :: funs) Vinit stinit c post body fun Vend stend o =>
                Q (restore V Vend) stend o
          | .halt => Q (restore V Vinit) stinit .halt
          | _ => False
    | .«break» => Q V st .«break»
    | .«continue» => Q V st .«continue»
    | .leave => Q V st .leave

/-- wp of a statement sequence. -/
def wpSS (fuel : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (ss : List (Stmt D.Op))
    (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | n + 1 =>
    match ss with
    | [] => Q V st .normal
    | s :: rest =>
        wpS n funs V st s fun V1 st1 o1 =>
          match o1 with
          | .normal => Stop (wpSS n funs V1 st1 rest Q)
          | _ => Q V1 st1 o1

/-- wp of a loop iteration (after `init`): unrolling. -/
def wpL (fuel : Nat) (funs : FunEnv D) (V : VEnv D) (st : D.State) (c : Expr D.Op)
    (post body : Block D.Op) (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | n + 1 =>
    wpE n funs V st c fun r =>
      match r with
      | .vals [cv] st1 =>
          (cv = D.zero → Q V st1 .normal) ∧
          (cv ≠ D.zero →
            wpS n funs V st1 (.block body) fun Vb stb ob =>
              match ob with
              | .normal | .«continue» =>
                  wpS n funs Vb stb (.block post) fun Vp stp op =>
                    match op with
                    | .normal => Stop (wpL n funs Vp stp c post body Q)
                    | .halt => Q Vp stp .halt
                    | _ => False
              | .«break» => Q Vb stb .normal
              | .leave => Q Vb stb .leave
              | .halt => Q Vb stb .halt)
      | .vals _ _ => False
      | .halt st1 => Q V st1 .halt
end

/-- The built-in transformer is sound for the dialect's relation. -/
def BSound : Prop :=
  ∀ op args st Q, B op args st Q → ∀ r, D.Builtin op args st r → Q r

/-- Every call summary is a valid contract of the function body it replaces. -/
def CSound : Prop :=
  ∀ funs fn argvals st1 T, C funs fn argvals st1 = some T → ∀ Q, T Q →
    ∀ decl cenv, lookupFun funs fn = some (decl, cenv) →
      argvals.length = decl.params.length →
      ∀ Vend st2 o,
        Step D cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 o) →
        ((o = .normal ∨ o = .leave) →
            Q (.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2)) ∧
        (o = .halt → Q (.halt st2))

/-- **SOUNDNESS (all runs).** If `wp` holds then EVERY big-step derivation ends in `Q`. -/
theorem wp_sound (hB : BSound D B) (hC : CSound D C) : ∀ n : Nat,
    (∀ funs V st e Q, wpE D B C n funs V st e Q →
        ∀ r, EvalExpr D funs V st e r → Q r) ∧
    (∀ funs V st es Q, wpA D B C n funs V st es Q →
        ∀ r, EvalArgs D funs V st es r → Q r) ∧
    (∀ funs V st s Q, wpS D B C n funs V st s Q →
        ∀ V' st' o, ExecStmt D funs V st s V' st' o → Q V' st' o) ∧
    (∀ funs V st ss Q, wpSS D B C n funs V st ss Q →
        ∀ V' st' o, ExecStmts D funs V st ss V' st' o → Q V' st' o) ∧
    (∀ funs V st c post body Q, wpL D B C n funs V st c post body Q →
        ∀ V' st' o, ExecLoop D funs V st c post body V' st' o → Q V' st' o) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro funs V st e Q h; simp [wpE] at h
      · intro funs V st es Q h; simp [wpA] at h
      · intro funs V st s Q h; simp [wpS] at h
      · intro funs V st ss Q h; simp [wpSS] at h
      · intro funs V st c post body Q h; simp [wpL] at h
  | succ n ih =>
      obtain ⟨ihE, ihA, ihS, ihSS, ihL⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      /- expressions -/
      · intro funs V st e Q h r hr
        cases e with
        | lit l =>
            simp only [wpE] at h
            cases hr
            exact h
        | var x =>
            simp only [wpE] at h
            cases hr with
            | var hget =>
                simp only [hget] at h
                exact h
        | builtin op args =>
            simp only [wpE] at h
            cases hr with
            | builtinOk hargs hbi => exact hB _ _ _ _ (ihA _ _ _ _ _ h _ hargs) _ hbi
            | builtinHalt hargs hbi => exact hB _ _ _ _ (ihA _ _ _ _ _ h _ hargs) _ hbi
            | builtinArgsHalt hargs => exact ihA _ _ _ _ _ h _ hargs
        | call fn args =>
            simp only [wpE] at h
            cases hr with
            | callOk hargs hlookup hlen hbody hor =>
                rename_i argvals st1 decl cenv Vend st2 o
                have h1 := ihA _ _ _ _ _ h _ hargs
                cases hc : C funs fn argvals st1 with
                | some T =>
                    simp only [hc] at h1
                    exact (hC _ _ _ _ _ hc Q h1 _ _ hlookup hlen _ _ _ hbody).1 hor
                | none =>
                    simp only [hc, hlookup] at h1
                    have h3 := ihS _ _ _ _ _ h1.2 _ _ _ hbody
                    rcases hor with rfl | rfl <;> exact h3
            | callHalt hargs hlookup hlen hbody =>
                rename_i argvals st1 decl cenv Vend st2
                have h1 := ihA _ _ _ _ _ h _ hargs
                cases hc : C funs fn argvals st1 with
                | some T =>
                    simp only [hc] at h1
                    exact (hC _ _ _ _ _ hc Q h1 _ _ hlookup hlen _ _ _ hbody).2 rfl
                | none =>
                    simp only [hc, hlookup] at h1
                    exact ihS _ _ _ _ _ h1.2 _ _ _ hbody
            | callArgsHalt hargs => exact ihA _ _ _ _ _ h _ hargs
      /- argument lists -/
      · intro funs V st es Q h r hr
        cases es with
        | nil =>
            simp only [wpA] at h
            cases hr
            exact h
        | cons e rest =>
            simp only [wpA] at h
            cases hr with
            | argsCons hrest he => exact ihE _ _ _ _ _ (ihA _ _ _ _ _ h _ hrest) _ he
            | argsRestHalt hrest => exact ihA _ _ _ _ _ h _ hrest
            | argsHeadHalt hrest he => exact ihE _ _ _ _ _ (ihA _ _ _ _ _ h _ hrest) _ he
      /- statements -/
      · intro funs V st s Q h V' st' o hrun
        cases s with
        | funDef nm ps rs b =>
            simp only [wpS] at h
            cases hrun
            exact h
        | block body =>
            simp only [wpS] at h
            cases hrun with
            | block hb => exact ihSS _ _ _ _ _ h _ _ _ hb
        | letDecl vars oe =>
            cases oe with
            | none =>
                simp only [wpS] at h
                cases hrun
                exact h
            | some e =>
                simp only [wpS] at h
                cases hrun with
                | letVal he hlen => exact (ihE _ _ _ _ _ h _ he).2
                | letHalt he => exact ihE _ _ _ _ _ h _ he
        | assign vars e =>
            simp only [wpS] at h
            cases hrun with
            | assignVal he hlen => exact (ihE _ _ _ _ _ h _ he).2
            | assignHalt he => exact ihE _ _ _ _ _ h _ he
        | exprStmt e =>
            simp only [wpS] at h
            cases hrun with
            | exprStmt he => exact ihE _ _ _ _ _ h _ he
            | exprStmtHalt he => exact ihE _ _ _ _ _ h _ he
        | cond c body =>
            simp only [wpS] at h
            cases hrun with
            | ifTrue hc hnz hbody => exact ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody
            | ifFalse hc hz => exact (ihE _ _ _ _ _ h _ hc).1 hz
            | ifHalt hc => exact ihE _ _ _ _ _ h _ hc
        | «switch» c cases dflt =>
            simp only [wpS] at h
            cases hrun with
            | switchExec hc hbody => exact ihS _ _ _ _ _ (ihE _ _ _ _ _ h _ hc) _ _ _ hbody
            | switchHalt hc => exact ihE _ _ _ _ _ h _ hc
        | forLoop init c post body =>
            simp only [wpS] at h
            cases hrun with
            | forLoop hinit hloop => exact ihL _ _ _ _ _ _ _ (ihSS _ _ _ _ _ h _ _ _ hinit) _ _ _ hloop
            | forInitHalt hinit => exact ihSS _ _ _ _ _ h _ _ _ hinit
        | «break» =>
            simp only [wpS] at h
            cases hrun
            exact h
        | «continue» =>
            simp only [wpS] at h
            cases hrun
            exact h
        | «leave» =>
            simp only [wpS] at h
            cases hrun
            exact h
      /- sequences -/
      · intro funs V st ss Q h V' st' o hrun
        cases ss with
        | nil =>
            simp only [wpSS] at h
            cases hrun
            exact h
        | cons s rest =>
            simp only [wpSS] at h
            cases hrun with
            | seqCons h1 h2 => exact ihSS _ _ _ _ _ (Stop.elim (ihS _ _ _ _ _ h _ _ _ h1)) _ _ _ h2
            | seqStop h1 hne =>
                have h3 := ihS _ _ _ _ _ h _ _ _ h1
                cases o <;> first | exact absurd rfl hne | exact h3
      /- loops -/
      · intro funs V st c post body Q h V' st' o hrun
        simp only [wpL] at h
        cases hrun with
        | loopDone hc hz => exact (ihE _ _ _ _ _ h _ hc).1 hz
        | loopCondHalt hc => exact ihE _ _ _ _ _ h _ hc
        | loopStep hc hnz hbody hob hpost hrec =>
            have hb := ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody
            rcases hob with rfl | rfl
            · exact ihL _ _ _ _ _ _ _ (Stop.elim (ihS _ _ _ _ _ hb _ _ _ hpost)) _ _ _ hrec
            · exact ihL _ _ _ _ _ _ _ (Stop.elim (ihS _ _ _ _ _ hb _ _ _ hpost)) _ _ _ hrec
        | loopPostHalt hc hnz hbody hob hpost =>
            have hb := ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody
            rcases hob with rfl | rfl
            · exact ihS _ _ _ _ _ hb _ _ _ hpost
            · exact ihS _ _ _ _ _ hb _ _ _ hpost
        | loopBreak hc hnz hbody =>
            exact ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody
        | loopLeave hc hnz hbody =>
            exact ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody
        | loopBodyHalt hc hnz hbody =>
            exact ihS _ _ _ _ _ ((ihE _ _ _ _ _ h _ hc).2 hnz) _ _ _ hbody

/-- Statement-sequence projection of `wp_sound`, in `StmtsContractAll` shape. -/
theorem wpSS_sound (hB : BSound D B) (hC : CSound D C) {n funs V st ss Q}
    (h : wpSS D B C n funs V st ss Q) :
    ∀ V' st' o, ExecStmts D funs V st ss V' st' o → Q V' st' o :=
  (wp_sound D B C hB hC n).2.2.2.1 funs V st ss Q h

/-- Single-statement projection. -/
theorem wpS_sound (hB : BSound D B) (hC : CSound D C) {n funs V st s Q}
    (h : wpS D B C n funs V st s Q) :
    ∀ V' st' o, ExecStmt D funs V st s V' st' o → Q V' st' o :=
  (wp_sound D B C hB hC n).2.2.1 funs V st s Q h

/-- **THE CUT RULE.** Symbolically execute ONE statement; the continuation is SEMANTIC (all runs of
    the rest), so at any leaf the proof may keep stepping or apply a previously proved lemma about
    `rest` (a poisoned-continuation lemma, a block contract, a loop rule). -/
theorem allRuns_cons_wp (hB : BSound D B) (hC : CSound D C) {n funs V st s rest}
    {Q : VEnv D → D.State → Outcome → Prop}
    (h : wpS D B C n funs V st s fun V1 st1 o1 =>
      match o1 with
      | .normal => ∀ V' st' o, ExecStmts D funs V1 st1 rest V' st' o → Q V' st' o
      | _ => Q V1 st1 o1) :
    ∀ V' st' o, ExecStmts D funs V st (s :: rest) V' st' o → Q V' st' o := by
  intro V' st' o hrun
  cases hrun with
  | seqCons h1 h2 => exact wpS_sound D B C hB hC h _ _ _ h1 _ _ _ h2
  | seqStop h1 hne =>
      have h3 := wpS_sound D B C hB hC h _ _ _ h1
      cases o <;> first | exact absurd rfl hne | exact h3

end WP

end Midfall.Yul.Wp
