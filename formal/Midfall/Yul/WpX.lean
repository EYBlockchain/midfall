/-
  Midfall.Yul.WpX

  THE WPX EXISTENCE AND LAYER STATEMENTS (T3.1b, PLAN-V3). Ported VERBATIM from the scratch source
  docs/plans/V3-evidence/lean/prooftech/WPX.lean; the only changes are the import paths, the
  namespace (the scratch ProofTech namespace -> Midfall.Yul.WpX) and the deletion of the four
  declarations BLive, Bfun, Bfun_sound and Bfun_live, which T3.1 had ALREADY landed verbatim in
  Midfall/Yul/WpBridge.lean (that file's header names WPX.lean as their source). Restating them here
  would duplicate a proved declaration, so this file uses Midfall.Yul.WpBridge.BLive instead. No
  statement and no proof step was restated.

  WHAT IS HERE. Three proved bridges, the totality half (T3.2), and the arithmetic layer (T3.8):

    * wp_exists          THE FIVE-CLASS EXISTENCE CONJUNCTION - the mirror image of wp_sound with an
                         EXISTENTIAL conclusion, by one induction on fuel. PROVED here (T3.2). Its
                         summary-liveness binder is what Midfall/Yul/VKP.lean's CLive is definitionally,
                         so the same induction gives wpSS_exists_C there: ONE induction, two
                         projections, no second case split.
    * wpSS_exists        TOTALITY: with a LIVE transformer and an empty summary table, a wpSS proof
                         exhibits a run. PROVED here (T3.2) as a projection of wp_exists. Together
                         with wp_sound this is StmtsTotal (Blocks.lean:50) from ONE evaluation, and
                         it is the non-stuckness guarantee finding C-1 asks for.
    * Bopen_not_live     THE FALSIFIER the card asks for: BLive is not a consequence of BSound - the
                         demonic Bopen is sound for every call relation and is NOT live at
                         ExternalCalls.none, because a staticcall has no response. This is why the
                         existence half runs at Bfun (Bfun_live) and not at Bopen.
    * loadWord_storeWord the memory layer's read-over-write lemma. PROVED here (T3.5) from
                         Midfall/Yul/Word.lean: the equal window reassembles, the disjoint window is
                         invisible, and the overlap is genuinely undetermined (see the lemma).
    * mulmod_toFr        the arithmetic layer's bridge. PROVED here (T3.8): EVM mulmod at the scalar
                         modulus IS field multiplication in Fr r = ZMod r, and addmod is addition.
                         Neither needs a canonicity hypothesis (see the lemma); wSubFr is the third
                         bridge and the only one that does, with its failure gated below it.
    * runs_agree_of_wp   PROVED here: prefix determinism WITHOUT dialect_deterministic (finding C-3),
                         by two applications of WpTac.allRuns_of_wp.

  D-P71: no native_decide in this file, and none is needed - wp_exists and runs_agree_of_wp are
  term-level arguments over the engine and its soundness theorem, loadWord_storeWord is a
  fold-level argument over the vendored byte model (Midfall/Yul/Word.lean), and the T3.8 arithmetic
  bridge is a closed-term argument over the modulus literal: the only decision it makes is `decide` on
  the 256-bit comparison qvmFrModulus < 2^256, measured at well under a millisecond, and no gate here
  searches the field. THIS FILE NOW HAS NO SORRY: mulmod_toFr was the last one and it is PROVED, so
  SORRY.md lost its row (register 64 -> 63). The axiom gate for the
  T3.2 and T3.8 theorems is a #assert_axioms block at the end of Midfall/Yul/VKP.lean, which is the
  file that imports Midfall.Tools.Done.
-/
import Midfall.Yul.WpTac
import Midfall.Yul.Word
import Midfall.Lowering.Qvm
set_option autoImplicit false

namespace Midfall.Yul.WpX
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac

section Exists
variable (D : Dialect) [DecidableEq D.Value] (B : BT D) (C : CT D)

/-- **THE FIVE-CLASS EXISTENCE CONJUNCTION - the mirror image of `wp_sound` (`Wp.lean:236`), with an
    EXISTENTIAL conclusion.** `wp_sound` reads "every run ends in `Q`"; this reads "`SOME` run ends
    in `Q`", and it is the half that makes a block's `StmtsTotal` contract (finding C-1) come out of
    the SAME `wp` evaluation as its `StmtsContractAll`. Induction on fuel, one case per `Step`
    constructor, in the shape of `wp_sound`; the `Stop` wrapper composes because `Stop.elim`
    extracts its field, and the fuel bound is inherited from the hypothesis (no extra bound is needed:
    at fuel 0 every class is `False`, discharged by `simp` as in `wp_sound`'s zero case).

    WHY THE SUMMARY HYPOTHESIS IS SHAPED LIKE THIS. `wp_sound`'s hypothesis `CSound` is a universal
    over runs, so an empty table satisfies it trivially (`Cnone_sound`); liveness is an EXISTENTIAL
    over runs, so the empty table satisfies it only vacuously and a summarised call needs a real
    witness. The binder below is therefore the liveness law of a summary table, stated INLINE rather
    than by name: `Midfall.Yul.VKP.CLive` (`VKP.lean:407`) is DEFINITIONALLY this proposition, so
    ONE induction serves both `wpSS_exists` below (whose `hC : C = none` everywhere refutes the
    `some T` branch on the spot) and `wpSS_exists_C` in `VKP.lean`, which passes its `CLive`
    directly. Neither registered statement is weakened or restated: both keep the text they were
    registered with, and each is a projection of the conjunction below. And the binder is not a second
    definition that could drift: `wpSS_exists_C`'s one-line proof IS the check that this binder and
    `CLive` still mean the same thing - restate either and the projection stops type-checking.

    BOTH HYPOTHESES ARE LOAD-BEARING. `hB : BLive D B` is what turns a built-in obligation into a
    result: the falsifier `Bopen_not_live` below exhibits a transformer that is SOUND
    (`Bopen_sound`) but NOT live, which is why the existence half runs at the FUNCTIONAL transformer
    `Bfun` (`WpBridge.lean:248`, live by `Bfun_live`) and not at `Bopen`. And a call the table
    does not summarise must resolve in `funs`: the `.call` case builds `Step.callOk` /
    `Step.callHalt`, so it needs `lookupFun funs fn = some _`, which the wp hypothesis supplies - a
    `none` there makes the wp `False`, i.e. refuses the program rather than proving it. -/
theorem wp_exists (hB : BLive D B)
    (hC : ∀ funs fn argvals st1 T, C funs fn argvals st1 = some T → ∀ Q, T Q →
      ∃ decl cenv, lookupFun funs fn = some (decl, cenv) ∧
        argvals.length = decl.params.length ∧
        ∃ Vend st2 o,
          Step D cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
            (.stmt (.block decl.body)) (.sres Vend st2 o) ∧
          (((o = .normal ∨ o = .leave) ∧
              Q (.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2)) ∨
            (o = .halt ∧ Q (.halt st2)))) :
    ∀ n : Nat,
      (∀ funs V st e Q, wpE D B C n funs V st e Q → ∃ r, EvalExpr D funs V st e r ∧ Q r) ∧
      (∀ funs V st es Q, wpA D B C n funs V st es Q → ∃ r, EvalArgs D funs V st es r ∧ Q r) ∧
      (∀ funs V st s Q, wpS D B C n funs V st s Q →
          ∃ V' st' o, ExecStmt D funs V st s V' st' o ∧ Q V' st' o) ∧
      (∀ funs V st ss Q, wpSS D B C n funs V st ss Q →
          ∃ V' st' o, ExecStmts D funs V st ss V' st' o ∧ Q V' st' o) ∧
      (∀ funs V st c post body Q, wpL D B C n funs V st c post body Q →
          ∃ V' st' o, ExecLoop D funs V st c post body V' st' o ∧ Q V' st' o) := by
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
      · intro funs V st e Q h
        cases e with
        | lit l =>
            simp only [wpE] at h
            exact ⟨.vals [D.litValue l] st, Step.lit, h⟩
        | var x =>
            simp only [wpE] at h
            cases hget : VEnv.get V x with
            | none => simp only [hget] at h
            | some v =>
                simp only [hget] at h
                exact ⟨.vals [v] st, Step.var hget, h⟩
        | builtin op args =>
            simp only [wpE] at h
            obtain ⟨argr, hargs, h1⟩ := ihA _ _ _ _ _ h
            cases argr with
            | halt st1 => exact ⟨.halt st1, Step.builtinArgsHalt hargs, h1⟩
            | vals argvals st1 =>
                -- THE ONLY USE OF `hB`: the demonic `∀ br` inside `B` is discharged by a LIVE
                -- transformer, which hands back a result AND the fact that it satisfies the
                -- continuation. At `Bopen` the same `∀` is what makes the transformer sound but
                -- unusable here (`Bopen_not_live`).
                obtain ⟨br, hbi, h2⟩ := hB _ _ _ _ h1
                cases br with
                | ok rets st2 => exact ⟨.vals rets st2, Step.builtinOk hargs hbi, h2⟩
                | halt st2 => exact ⟨.halt st2, Step.builtinHalt hargs hbi, h2⟩
        | call fn args =>
            simp only [wpE] at h
            obtain ⟨argr, hargs, h1⟩ := ihA _ _ _ _ _ h
            cases argr with
            | halt st1 => exact ⟨.halt st1, Step.callArgsHalt hargs, h1⟩
            | vals argvals st1 =>
                cases hc : C funs fn argvals st1 with
                | some T =>
                    -- THE SUMMARISED CALL: the one case `wp_sound` has no twin of. `hC` names the
                    -- callee, its arity and a RUN of its body; the run is already in the shape
                    -- `Step.callOk` / `Step.callHalt` want, so no inlining happens here.
                    simp only [hc] at h1
                    obtain ⟨decl, cenv, hlookup, hlen, Vend, st2, o, hstep, hres⟩ :=
                      hC _ _ _ _ _ hc _ h1
                    cases hres with
                    | inl h =>
                        obtain ⟨h1o, hQ⟩ := h
                        rcases h1o with rfl | rfl
                        · exact ⟨.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2,
                            Step.callOk hargs hlookup hlen hstep (Or.inl rfl), hQ⟩
                        · exact ⟨.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2,
                            Step.callOk hargs hlookup hlen hstep (Or.inr rfl), hQ⟩
                    | inr h =>
                        obtain ⟨rfl, hQ⟩ := h
                        exact ⟨.halt st2, Step.callHalt hargs hlookup hlen hstep, hQ⟩
                | none =>
                    simp only [hc] at h1
                    cases hlookup : lookupFun funs fn with
                    | none => simp only [hlookup] at h1
                    | some x =>
                        cases x with
                        | mk decl cenv =>
                            simp only [hlookup] at h1
                            obtain ⟨hlen, hsub⟩ := h1
                            obtain ⟨Vend, st2, o, hstep, hmatch⟩ := ihS _ _ _ _ _ hsub
                            cases o with
                            | normal =>
                                exact ⟨.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2,
                                  Step.callOk hargs hlookup hlen hstep (Or.inl rfl), hmatch⟩
                            | «leave» =>
                                exact ⟨.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2,
                                  Step.callOk hargs hlookup hlen hstep (Or.inr rfl), hmatch⟩
                            | halt =>
                                exact ⟨.halt st2, Step.callHalt hargs hlookup hlen hstep, hmatch⟩
                            -- `break` / `continue` cannot escape a function body: the wp refuses
                            -- them (`| _ => False`), and that refusal closes the branch.
                            | «break» | «continue» => exact False.elim hmatch
      /- argument lists -/
      · intro funs V st es Q h
        cases es with
        | nil =>
            simp only [wpA] at h
            exact ⟨.vals [] st, Step.argsNil, h⟩
        | cons e rest =>
            simp only [wpA] at h
            obtain ⟨rr, hrest, h1⟩ := ihA _ _ _ _ _ h
            cases rr with
            | halt st1 => exact ⟨.halt st1, Step.argsRestHalt hrest, h1⟩
            | vals restvals st1 =>
                obtain ⟨r2, he, h2⟩ := ihE _ _ _ _ _ h1
                cases r2 with
                | halt st2 => exact ⟨.halt st2, Step.argsHeadHalt hrest he, h2⟩
                | vals vs st2 =>
                    cases vs with
                    | nil => exact False.elim h2
                    | cons v vs' =>
                        cases vs' with
                        | cons v' vs'' => exact False.elim h2
                        | nil => exact ⟨.vals (v :: restvals) st2, Step.argsCons hrest he, h2⟩
      /- statements -/
      · intro funs V st s Q h
        cases s with
        | funDef nm ps rs b =>
            simp only [wpS] at h
            exact ⟨V, st, .normal, Step.funDef, h⟩
        | block body =>
            simp only [wpS] at h
            obtain ⟨V', st', o, hrun, hQ⟩ := ihSS _ _ _ _ _ h
            exact ⟨restore V V', st', o, Step.block hrun, hQ⟩
        | letDecl vars oe =>
            cases oe with
            | none =>
                simp only [wpS] at h
                exact ⟨bindZeros D vars ++ V, st, .normal, Step.letZero, h⟩
            | some e =>
                simp only [wpS] at h
                obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
                cases r with
                | halt st1 => exact ⟨V, st1, .halt, Step.letHalt he, hmatch⟩
                | vals vals' st1 =>
                    exact ⟨vars.zip vals' ++ V, st1, .normal, Step.letVal he hmatch.1, hmatch.2⟩
        | assign vars e =>
            simp only [wpS] at h
            obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
            cases r with
            | halt st1 => exact ⟨V, st1, .halt, Step.assignHalt he, hmatch⟩
            | vals vals' st1 =>
                exact ⟨VEnv.setMany V vars vals', st1, .normal,
                  Step.assignVal he hmatch.1, hmatch.2⟩
        | exprStmt e =>
            simp only [wpS] at h
            obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
            cases r with
            | halt st1 => exact ⟨V, st1, .halt, Step.exprStmtHalt he, hmatch⟩
            | vals vs st1 =>
                cases vs with
                | nil => exact ⟨V, st1, .normal, Step.exprStmt he, hmatch⟩
                -- A VALUED expression in statement position is STUCK: falsifier F1 of
                -- `WpFalsifiers` exhibits the refusal at every fuel, and here the same refusal
                -- (`| .vals _ _ => False`) is what makes this branch empty.
                | cons v vs' => exact False.elim hmatch
        | cond c body =>
            simp only [wpS] at h
            obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
            cases r with
            | halt st1 => exact ⟨V, st1, .halt, Step.ifHalt he, hmatch⟩
            | vals vs st1 =>
                cases vs with
                | nil => exact False.elim hmatch
                | cons cv vs' =>
                    cases vs' with
                    | cons v' vs'' => exact False.elim hmatch
                    | nil =>
                        by_cases hz : cv = D.zero
                        · exact ⟨V, st1, .normal, Step.ifFalse he hz, hmatch.1 hz⟩
                        · obtain ⟨V', st', o, hrun, hQ⟩ := ihS _ _ _ _ _ (hmatch.2 hz)
                          exact ⟨V', st', o, Step.ifTrue he hz hrun, hQ⟩
        | «switch» c cases dflt =>
            simp only [wpS] at h
            obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
            cases r with
            | halt st1 => exact ⟨V, st1, .halt, Step.switchHalt he, hmatch⟩
            | vals vs st1 =>
                cases vs with
                | nil => exact False.elim hmatch
                | cons cv vs' =>
                    cases vs' with
                    | cons v' vs'' => exact False.elim hmatch
                    | nil =>
                        obtain ⟨V', st', o, hrun, hQ⟩ := ihS _ _ _ _ _ hmatch
                        exact ⟨V', st', o, Step.switchExec he hrun, hQ⟩
        | forLoop init c post body =>
            simp only [wpS] at h
            obtain ⟨Vinit, stinit, oinit, hinit, hmatch⟩ := ihSS _ _ _ _ _ h
            cases oinit with
            | halt => exact ⟨restore V Vinit, stinit, .halt, Step.forInitHalt hinit, hmatch⟩
            | «break» | «continue» | «leave» => exact False.elim hmatch
            | normal =>
                obtain ⟨Vend, stend, o, hloop, hQ⟩ := ihL _ _ _ _ _ _ _ hmatch
                exact ⟨restore V Vend, stend, o, Step.forLoop hinit hloop, hQ⟩
        | «break» =>
            simp only [wpS] at h
            exact ⟨V, st, .break, Step.«break», h⟩
        | «continue» =>
            simp only [wpS] at h
            exact ⟨V, st, .continue, Step.«continue», h⟩
        | «leave» =>
            simp only [wpS] at h
            exact ⟨V, st, .leave, Step.leave, h⟩
      /- sequences -/
      · intro funs V st ss Q h
        cases ss with
        | nil =>
            simp only [wpSS] at h
            exact ⟨V, st, .normal, Step.seqNil, h⟩
        | cons s rest =>
            simp only [wpSS] at h
            obtain ⟨V1, st1, o1, h1, hmatch⟩ := ihS _ _ _ _ _ h
            cases o1 with
            | normal =>
                -- THE SEQUENCE POINT: the only place the `Stop` wrapper is opened. It composes
                -- because `Stop.elim` is a projection, so the induction hypothesis is reachable.
                obtain ⟨V', st', o, h2, hQ⟩ := ihSS _ _ _ _ _ (Stop.elim hmatch)
                exact ⟨V', st', o, Step.seqCons h1 h2, hQ⟩
            | «break» => exact ⟨V1, st1, .break, Step.seqStop h1 (by decide), hmatch⟩
            | «continue» => exact ⟨V1, st1, .continue, Step.seqStop h1 (by decide), hmatch⟩
            | «leave» => exact ⟨V1, st1, .leave, Step.seqStop h1 (by decide), hmatch⟩
            | halt => exact ⟨V1, st1, .halt, Step.seqStop h1 (by decide), hmatch⟩
      /- loops -/
      · intro funs V st c post body Q h
        simp only [wpL] at h
        obtain ⟨r, he, hmatch⟩ := ihE _ _ _ _ _ h
        cases r with
        | halt st1 => exact ⟨V, st1, .halt, Step.loopCondHalt he, hmatch⟩
        | vals vs st1 =>
            cases vs with
            | nil => exact False.elim hmatch
            | cons cv vs' =>
                cases vs' with
                | cons v' vs'' => exact False.elim hmatch
                | nil =>
                    by_cases hz : cv = D.zero
                    · exact ⟨V, st1, .normal, Step.loopDone he hz, hmatch.1 hz⟩
                    · obtain ⟨Vb, stb, ob, hbody, hmatchb⟩ := ihS _ _ _ _ _ (hmatch.2 hz)
                      cases ob with
                      | «break» => exact ⟨Vb, stb, .normal, Step.loopBreak he hz hbody, hmatchb⟩
                      | «leave» => exact ⟨Vb, stb, .leave, Step.loopLeave he hz hbody, hmatchb⟩
                      | halt => exact ⟨Vb, stb, .halt, Step.loopBodyHalt he hz hbody, hmatchb⟩
                      | normal =>
                          obtain ⟨Vp, stp, op, hpost, hmatchp⟩ := ihS _ _ _ _ _ hmatchb
                          cases op with
                          | halt =>
                              exact ⟨Vp, stp, .halt,
                                Step.loopPostHalt he hz hbody (Or.inl rfl) hpost, hmatchp⟩
                          | «break» | «continue» | «leave» => exact False.elim hmatchp
                          | normal =>
                              obtain ⟨Vend, stend, o, hrec, hQ⟩ :=
                                ihL _ _ _ _ _ _ _ (Stop.elim hmatchp)
                              exact ⟨Vend, stend, o,
                                Step.loopStep he hz hbody (Or.inl rfl) hpost hrec, hQ⟩
                      | «continue» =>
                          obtain ⟨Vp, stp, op, hpost, hmatchp⟩ := ihS _ _ _ _ _ hmatchb
                          cases op with
                          | halt =>
                              exact ⟨Vp, stp, .halt,
                                Step.loopPostHalt he hz hbody (Or.inr rfl) hpost, hmatchp⟩
                          | «break» | «continue» | «leave» => exact False.elim hmatchp
                          | normal =>
                              obtain ⟨Vend, stend, o, hrec, hQ⟩ :=
                                ihL _ _ _ _ _ _ _ (Stop.elim hmatchp)
                              exact ⟨Vend, stend, o,
                                Step.loopStep he hz hbody (Or.inr rfl) hpost hrec, hQ⟩

/-- **TOTALITY (a run exists).** With a live transformer and no summaries, `wp` exhibits a run.
    Together with `wp_sound` this is `StmtsTotal` (Blocks.lean:50) from ONE evaluation, and it is
    the non-stuckness guarantee finding C-1 asks for. PROOF: induction on fuel, building the `Step`
    derivation (the mirror image of `wp_sound`; about the same size). PROVED here as a
    projection of `wp_exists`. -/
theorem wpSS_exists (hB : BLive D B) (hC : ∀ funs fn args st, C funs fn args st = none)
    {n : Nat} {funs : FunEnv D} {V : VEnv D} {st : D.State} {ss : Block D.Op}
    {Q : VEnv D → D.State → Outcome → Prop} (h : wpSS D B C n funs V st ss Q) :
    ∃ V' st' o, ExecStmts D funs V st ss V' st' o ∧ Q V' st' o := by
  have key := wp_exists D B C hB (by
    intro funs fn argvals st1 T hT
    rw [hC] at hT
    cases hT) n
  exact key.2.2.2.1 funs V st ss Q h
end Exists

/-! ## THE FALSIFIER (T3.2, card Accept): liveness is a real hypothesis -/

/-- At the EMPTY call relation the demonic transformer HOLDS VACUOUSLY at a `staticcall`: `Bopen`
    quantifies over every response `c` admits, and `ExternalCalls.none` admits none, so the
    obligation is satisfied even by the post `fun _ => False` that nothing can satisfy. -/
theorem Bopen_staticcall_vacuous (g : ExternalGas) :
    Bopen ExternalCalls.none g Op.staticcall [0, 0, 0, 0, 0, 0] EvmState.init (fun _ => False) :=
  fun _ h => h.elim

/-- AND the same staticcall has NO relational result at all: `Builtin` for a call op is
    `externalCall`, an existential over a response, and there is no response. This is the half the
    exhibit below consumes - it is why the transformer above is sound but not live. -/
theorem not_live_staticcall (g : ExternalGas) :
    ¬ ∃ r, (Bridge.Dialect ExternalCalls.none g).Builtin Op.staticcall
        [0, 0, 0, 0, 0, 0] EvmState.init r := by
  intro h
  obtain ⟨r, hr⟩ := h
  simp only [builtinWithExternal] at hr
  obtain ⟨resp, hcall, _⟩ := hr
  cases hcall

/-- **FALSIFIER.** `BLive` is NOT a consequence of `BSound`: the demonic transformer `Bopen` is
    sound for every call relation (`Bopen_sound`) and is not live at `ExternalCalls.none`, because
    a staticcall has no response to exist. What this refutes is the `Bopen` INSTANTIATION of
    `wpSS_exists` for a call relation with no answer - the induction is fine, the `BLive` hypothesis
    is what fails - so the card's instruction to run the existence half at the honest dialect under
    `Bfun` (live by `Bfun_live` at a functional oracle) is not a stylistic preference. W12: the
    witness that keeps `wpSS_exists` non-vacuous is `Bfun_live` at the honest dialect
    (`Midfall.LoweringV2.HonestExec`, which this file must not import: `Midfall/Yul` does not reach
    up into `LoweringV2`). -/
theorem Bopen_not_live (g : ExternalGas) :
    ¬ BLive (Bridge.Dialect ExternalCalls.none g) (Bopen ExternalCalls.none g) := by
  intro h
  obtain ⟨r, hr, hF⟩ := h Op.staticcall [0, 0, 0, 0, 0, 0] EvmState.init (fun _ => False)
    (Bopen_staticcall_vacuous g)
  exact not_live_staticcall g ⟨r, hr⟩

/-- **PREFIX DETERMINISM without `dialect_deterministic` (finding C-3).** For ANY call relation and
    ANY gas oracle: if `wp` shows every run of a statement list ends at one named endpoint, two runs
    agree. For call-free, gas-free code (the ABI guard, wrapper locals, MF-2 guard, `mainLocals`)
    the `wp` evaluation never consults an oracle, so this applies to
    `permissive (callsOf product)` with an arbitrary `g`. -/
theorem runs_agree_of_wp {c : ExternalCalls} {g : ExternalGas} {n : Nat}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {V₀ : VEnv (Bridge.Dialect c g)} {st₀ : EvmState} {o₀ : Outcome}
    (h : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) n funs V st ss
      fun V' st' o => V' = V₀ ∧ st' = st₀ ∧ o = o₀)
    {V₁ V₂ : VEnv (Bridge.Dialect c g)} {st₁ st₂ : EvmState} {o₁ o₂ : Outcome}
    (h₁ : ExecStmts (Bridge.Dialect c g) funs V st ss V₁ st₁ o₁)
    (h₂ : ExecStmts (Bridge.Dialect c g) funs V st ss V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ := by
  have a := allRuns_of_wp n h V₁ st₁ o₁ h₁
  have b := allRuns_of_wp n h V₂ st₂ o₂ h₂
  exact ⟨a.1.trans b.1.symm, a.2.1.trans b.2.1.symm, a.2.2.trans b.2.2.symm⟩

/-- **Read over write at the word layer (T3.5, PROVED).** A 32-byte load after a 32-byte store:
    at the SAME address the stored word reads back (`Word.loadWord_storeWord_same`, whose engine is
    the big-endian reassembly `Word.reassemble`); at a DISJOINT address the store is invisible
    (`Word.loadWord_storeWord_disjoint`); and in the OVERLAP case nothing is determined - the word
    depends on the stored bytes and on the old memory together - so that branch keeps the term
    itself. The third branch is not a gap in the proof: the card's own falsifier, that
    `loadWord (storeWord mem p v) (p+1) = v`, fails already at `v = 1#256` on the zero memory
    (the shifted read is `256`, and `256 ≠ 1` by `decide`), so no side-condition-free strengthening
    of this statement exists. The layer lives in
    `Midfall/Yul/Word.lean`; the statement is verbatim the memo's 3.3 proposal, unchanged. -/
theorem loadWord_storeWord (mem : Nat → UInt8) (p q : Nat) (v : U256) :
    loadWord (storeWord mem p v) q =
      if q = p then v else if q + 32 ≤ p ∨ p + 32 ≤ q then loadWord mem q
      else loadWord (storeWord mem p v) q := by
  by_cases hpq : q = p
  · subst hpq
    rw [ite_eq_left (rfl : q = q)]
    exact Word.loadWord_storeWord_same mem q v
  · rw [ite_eq_right hpq]
    by_cases hd : q + 32 ≤ p ∨ p + 32 ≤ q
    · rw [ite_eq_left hd]
      exact Word.loadWord_storeWord_disjoint mem p q v hd
    · rw [ite_eq_right hd]

/-! ### The arithmetic layer: EVM `mulmod`/`addmod` at the scalar modulus (T3.8) -/

/-- The scalar modulus as a 256-bit WORD: what the generated Yul binds to `r` and passes as the third
    argument of every `mulmod`/`addmod` (`Midfall/Lowering/GenAstPcs.lean:106` is
    `x_pow_of_omega := mulmod(x_pow_of_omega, w, r)`). `frModulusWord_toNat` says the embedding is
    exact; `frModulusWord_ne` is what makes EVM's `if n = 0 then 0 else ...` guard take its arithmetic
    branch at this modulus. -/
def frModulusWord : U256 := BitVec.ofNat 256 Midfall.Generator.qvmFrModulus

/-- **The modulus literal is canonical at 256 bits**, so the wrap EVM performs loses nothing. This is
    the ONLY fact about the size of the literal the bridge uses, and it is a `decide` on a 256-bit `Nat`
    comparison - a closed-term reduction (measured: well under a millisecond, the same cost class as
    `qvmFrModulus_eq_r` at Qvm.lean:133), not a search over field elements. -/
theorem frModulusWord_toNat : frModulusWord.toNat = Midfall.Generator.qvmFrModulus := by
  have h : Midfall.Generator.qvmFrModulus < 2 ^ 256 := by decide
  show (BitVec.ofNat 256 Midfall.Generator.qvmFrModulus).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The scalar modulus is not the zero word, so the `addmod`/`mulmod` zero-guard never fires here. -/
theorem frModulusWord_ne : frModulusWord ≠ 0 := by
  intro h
  have h2 : frModulusWord.toNat = 0 := by rw [h]; rfl
  rw [frModulusWord_toNat] at h2
  exact absurd h2 (by decide : Midfall.Generator.qvmFrModulus ≠ 0)

/-- EVM `mulmod(a, b, r)` at the scalar modulus: `stepOp`'s `.mulmod` arm (`EVMExec.lean:722`) applied
    to the third argument `frModulusWord` - see `stepOp_mulmod_atFr`. -/
def wMulmod (a b : U256) : U256 :=
  BitVec.ofNat 256 ((a.toNat * b.toNat) % Midfall.Generator.qvmFrModulus)

/-- EVM `addmod(a, b, r)` at the scalar modulus: `stepOp`'s `.addmod` arm (`EVMExec.lean:721`) applied
    to `frModulusWord`. -/
def wAddmod (a b : U256) : U256 :=
  BitVec.ofNat 256 ((a.toNat + b.toNat) % Midfall.Generator.qvmFrModulus)

/-- EVM `sub(r, x)` at the scalar modulus - the `subFrom` helper the generator emits for a field
    subtraction (`GenAstPcs.lean:117` builds `addmod(a, sub(r, b), r)`). Unlike `wMulmod` and `wAddmod`
    this one is a field negation only for a CANONICAL `x`: `subFr_toFr` carries the hypothesis and
    `subFr_needsCanonicity` shows it cannot be dropped. -/
def wSubFr (x : U256) : U256 := frModulusWord - x

/-- **THE NAMING STEP, PROVED (card Do 1).** At the scalar modulus the EVM step IS the named word
    operation: the third argument is nonzero, so the `if` takes the arithmetic branch and the word that
    comes out is `wMulmod a b`. Same for `addmod`. These two are what make the bridge below a bridge
    about EVM `mulmod` rather than about a bare `Nat` identity. -/
theorem stepOp_mulmod_atFr (a b : U256) (st : EvmState) :
    stepOp Op.mulmod [a, b, frModulusWord] st = some (.ok [wMulmod a b] st) := by
  simp only [stepOp, ter, wMulmod, frModulusWord_toNat]
  rw [ite_eq_right frModulusWord_ne]

/-- The `addmod` twin of `stepOp_mulmod_atFr`. -/
theorem stepOp_addmod_atFr (a b : U256) (st : EvmState) :
    stepOp Op.addmod [a, b, frModulusWord] st = some (.ok [wAddmod a b] st) := by
  simp only [stepOp, ter, wAddmod, frModulusWord_toNat]
  rw [ite_eq_right frModulusWord_ne]

/-- **THE ARITHMETIC BRIDGE (T3.8, PROVED - the last hole in this file).** EVM `mulmod` at the scalar
    modulus is field multiplication in `Fr r = ZMod r` (`Midfall/Lowering/Qvm.lean:136,139`). NO
    canonicity hypothesis is needed and none was added, on either side:

      * the left word is `wMulmod a b` by definition, and `(x * y) % qvmFrModulus < qvmFrModulus <
        2^256`, so the 256-bit wrap the opcode performs is the identity here - the only place the
        literal's SIZE is used at all (`frModulusWord_toNat`);
      * the `% qvmFrModulus` the opcode applies is the reduction `ZMod` applies anyway
        (`ZMod.natCast_mod`), which is the same reason `qvmToFr_add`/`qvmToFr_mul` (Qvm.lean:143,148)
        need no hypothesis - only `qvmToFr_neg` does, because `m - a` is not `-a` once `a >= m`;
      * the right side is a product of CASTS, so a non-canonical input word `a >= r` is no obstacle:
        `qvmToFr` maps it to its residue on both sides of the equation.

    The statement is verbatim the registered one; `qvmToFr_mul` is the `QVMFr`-level twin. -/
theorem mulmod_toFr (a b : U256) :
    Midfall.Lowering.qvmToFr
        (BitVec.ofNat 256 ((a.toNat * b.toNat) % Midfall.Generator.qvmFrModulus)).toNat =
      Midfall.Lowering.qvmToFr a.toNat * Midfall.Lowering.qvmToFr b.toNat := by
  show Midfall.Lowering.qvmToFr (wMulmod a b).toNat =
    Midfall.Lowering.qvmToFr a.toNat * Midfall.Lowering.qvmToFr b.toNat
  have hlt : (a.toNat * b.toNat) % Midfall.Generator.qvmFrModulus < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < Midfall.Generator.qvmFrModulus))
      (Nat.le_of_lt (by decide : Midfall.Generator.qvmFrModulus < 2 ^ 256))
  unfold wMulmod
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  unfold Midfall.Lowering.qvmToFr
  rw [Midfall.Lowering.qvmFrModulus_eq_r, ZMod.natCast_mod, ← Nat.cast_mul]

/-- **THE `addmod` TWIN (card Do 2).** EVM `addmod` at the scalar modulus is field addition, for the
    same two reasons: the sum is reduced below `r < 2^256` before the wrap, and the cast absorbs the
    reduction. No canonicity hypothesis, and none is needed. -/
theorem addmod_toFr (a b : U256) :
    Midfall.Lowering.qvmToFr (wAddmod a b).toNat =
      Midfall.Lowering.qvmToFr a.toNat + Midfall.Lowering.qvmToFr b.toNat := by
  have hlt : (a.toNat + b.toNat) % Midfall.Generator.qvmFrModulus < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < Midfall.Generator.qvmFrModulus))
      (Nat.le_of_lt (by decide : Midfall.Generator.qvmFrModulus < 2 ^ 256))
  unfold wAddmod
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  unfold Midfall.Lowering.qvmToFr
  rw [Midfall.Lowering.qvmFrModulus_eq_r, ZMod.natCast_mod, ← Nat.cast_add]

/-- **`sub(r, x)` IS NEGATION FOR A CANONICAL WORD (card Do 2, the third bridge).** This is the one
    arithmetic bridge that needs the hypothesis: `r - x` is the field negation of `x` only while the
    word subtraction does not wrap, i.e. while `x.toNat <= r` - and the canonical window `x.toNat < r`
    is what the verifier's own range checks supply. The word-level form of `qvmToFr_neg`
    (Qvm.lean:156), which carries the same hypothesis for the same reason. -/
theorem subFr_toFr (x : U256) (hx : x.toNat < Midfall.Generator.qvmFrModulus) :
    Midfall.Lowering.qvmToFr (wSubFr x).toNat = - Midfall.Lowering.qvmToFr x.toNat := by
  have hlt : Midfall.Generator.qvmFrModulus < 2 ^ 256 := by decide
  have key : 2 ^ 256 - x.toNat + Midfall.Generator.qvmFrModulus
      = Midfall.Generator.qvmFrModulus - x.toNat + 2 ^ 256 := by omega
  have hb : Midfall.Generator.qvmFrModulus - x.toNat < 2 ^ 256 := by omega
  have hsub : (wSubFr x).toNat = Midfall.Generator.qvmFrModulus - x.toNat := by
    show (frModulusWord - x).toNat = _
    rw [BitVec.toNat_sub, frModulusWord_toNat, key, Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt hb]
  unfold Midfall.Lowering.qvmToFr
  rw [hsub, Nat.cast_sub (Nat.le_of_lt hx), Midfall.Lowering.qvmFrModulus_eq_r,
    ZMod.natCast_self, zero_sub]

/-- **THE HYPOTHESIS IN `subFr_toFr` IS LOAD-BEARING**, on a concrete value: at the non-canonical word
    `r + 1` the word subtraction wraps to `2^256 - 1`, whose residue mod `r` is not `-1`, so the bridge
    fails. Note where the card's own falsifier line is wrong: it says the negation bridge fails at
    `x = r`, but at `x = r` BOTH sides are `0` - the first failure is at `r + 1`. What DOES fail at
    `x = r` is INJECTIVITY, and the tree already gates that as `qvmToFr_needsCanonicity_ok`
    (Qvm.lean:2893): `qvmToFr r = qvmToFr 0` with `r != 0`. -/
theorem subFr_needsCanonicity :
    ¬ (Midfall.Lowering.qvmToFr (wSubFr (BitVec.ofNat 256 (Midfall.Generator.qvmFrModulus + 1))).toNat
      = - Midfall.Lowering.qvmToFr (BitVec.ofNat 256 (Midfall.Generator.qvmFrModulus + 1)).toNat) := by
  intro h
  exact absurd h (by decide)

#print axioms wp_exists
#print axioms wpSS_exists
#print axioms Bopen_not_live
#print axioms runs_agree_of_wp
#print axioms loadWord_storeWord
#print axioms mulmod_toFr
#print axioms addmod_toFr
#print axioms subFr_toFr
#print axioms subFr_needsCanonicity
#print axioms stepOp_mulmod_atFr
#print axioms frModulusWord_toNat
end Midfall.Yul.WpX
