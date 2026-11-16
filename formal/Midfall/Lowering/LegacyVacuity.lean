/-
  Midfall.Lowering.LegacyVacuity

  WHY THE v1 HEADLINE IS RETIRED, AS THEOREMS. Kernel-checked, no `sorry`, no `native_decide`.

  1. `not_LoweringCorrect`: `LoweringCorrect S product` is UNINHABITED for every Surface `S` and
     every pairing oracle, so `Lowering.lowering_equivalence` (whose first hypothesis it is) is
     vacuous everywhere. The mechanism is `ir_refines`: it quantifies over every object passing
     `Surface.irCheck`, which only checks top-level name resolution
     (`IrCheckBlindness.irCheck_accepts_any_top_level_clean_block`). An empty runtime (one run,
     outcome `.normal`) and a stuck one (no run) both pass, so both would have to be `ObsEquiv` to
     the same `RunShell`, hence to each other. No determinism lemma is needed - contrary to the
     P-INLINE report, which believed refuting `ir_refines` requires `dialect_deterministic`.

  2. `ir_refines_field_is_false`: the same field refuted with a `revert(0,0)` object instead of a
     stuck one (both directions of `ObsEquiv` are used).

  3. `stuck_satisfies_every_post`: a forall-runs contract (`StmtsContractAll`) over a block that
     reads an unbound name holds for EVERY postcondition. This is the mechanism by which v1's
     per-partial specs - stated over UN-inlined fragments whose helpers read contract constants
     their own signatures cannot supply (`RunShellInversion.helperOwnFree_count_ok`: six of eight)
     - are vacuous on exactly the paths that call those helpers.

  Items 2 and 3 are the reviewer-supplied `FormalReviewCounterexamples.lean`, re-namespaced.
-/
import Midfall.Lowering.Obligations

namespace Midfall.Lowering.LegacyVacuity

open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Yul Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## Objects that pass `Surface.irCheck` -/

/-- An object whose runtime sub-object is `b`, named the way `S.runtimeName` expects. -/
def objOf (S : Surface p G₁ G₂ Gₜ) (b : YulBlock) : YulObject :=
  Object.mk "x" [] [Object.mk (S.runtimeName "x") b [] []] []

theorem irRuntime_objOf (S : Surface p G₁ G₂ Gₜ) (b : YulBlock) :
    S.irRuntime (objOf S b) = some b := by
  simp [Surface.irRuntime, objOf, Object.subObject, Object.subObjects, Object.name,
    Object.codeBlock]

/-- Runs off the end. -/
def emptyB : YulBlock := []

/-- Reads an unbound variable: no derivation exists. -/
def stuckB : YulBlock := [Stmt.letDecl ["y"] (some (Expr.var "zz"))]

/-- `revert(0, 0)`. -/
def revertB : YulBlock := [Stmt.exprStmt (Expr.builtin Op.revert [wlit 0, wlit 0])]

theorem irCheck_empty (S : Surface p G₁ G₂ Gₜ) : S.irCheck (objOf S emptyB) = true := by
  unfold Surface.irCheck; rw [irRuntime_objOf]; rfl

theorem irCheck_stuck (S : Surface p G₁ G₂ Gₜ) : S.irCheck (objOf S stuckB) = true := by
  unfold Surface.irCheck; rw [irRuntime_objOf]; rfl

theorem irCheck_revert (S : Surface p G₁ G₂ Gₜ) : S.irCheck (objOf S revertB) = true := by
  unfold Surface.irCheck; rw [irRuntime_objOf]; rfl

/-! ## Run facts for the three tiny programs -/

theorem empty_run (c : ExternalCalls) (g : ExternalGas) (st0 : EvmState) :
    RunCommitted c g emptyB st0 (restore ([] : VEnv (Bridge.Dialect c g)) [])
      (committedState st0 st0) .normal :=
  ⟨st0, Step.block Step.seqNil, rfl⟩

theorem empty_run_outcome {c : ExternalCalls} {g : ExternalGas} {st : EvmState}
    {V : VEnv (Bridge.Dialect c g)} {st' : EvmState} {out : Outcome}
    (h : Bridge.Run c g emptyB st V st' out) : out = .normal := by
  cases h with
  | block hbody =>
    cases hbody
    rfl

theorem stuck_no_run {c : ExternalCalls} {g : ExternalGas} {st0 : EvmState}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : Bridge.Run c g stuckB st0 V' st' o) : False := by
  have h' : Step (Bridge.Dialect c g) [] [] st0
      (.stmt (.block [Stmt.letDecl ["y"] (some (Expr.var "zz"))])) (.sres V' st' o) := h
  cases h' with
  | block hb =>
    cases hb with
    | seqCons hs _ =>
      cases hs with
      | letVal he _ =>
        cases he with
        | var hv => simp [VEnv.get] at hv
    | seqStop hs _ =>
      cases hs with
      | letVal he _ =>
        cases he with
        | var hv => simp [VEnv.get] at hv
      | letHalt he => cases he

/-! ## 1. The whole v1 bundle is empty -/

/-- **`LoweringCorrect` is uninhabited at every Surface.** -/
theorem not_LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) :
    ¬ LoweringCorrect S product := by
  intro hc
  have hwl : ExternalCalls.none.WorldLocal := fun _ _ _ _ _ => Iff.rfl
  have h1 := hc.ir_refines (objOf S emptyB) S.shellLayout (irCheck_empty S)
    EvmState.init.env keccak256 ByteArray.empty ExternalCalls.none 0 hwl
  have h2 := hc.ir_refines (objOf S stuckB) S.shellLayout (irCheck_stuck S)
    EvmState.init.env keccak256 ByteArray.empty ExternalCalls.none 0 hwl
  let st0 := callState EvmState.init.env S.shellLayout keccak256 ByteArray.empty
  let o : Obs := ⟨committedState st0 st0, .normal⟩
  have ho : RunContractIR S EvmState.init.env keccak256 (objOf S emptyB) S.shellLayout
      ByteArray.empty ExternalCalls.none (ExternalGas.ofFun fun _ => 0) o :=
    ⟨emptyB, _, irRuntime_objOf S emptyB, empty_run _ _ st0⟩
  obtain ⟨o', ho', hv'⟩ := (h1 o.view).1 ⟨o, ho, rfl⟩
  obtain ⟨o'', ⟨rt, V', hrt, st', hrun, _⟩, _⟩ := (h2 o.view).2 ⟨o', ho', hv'⟩
  rw [irRuntime_objOf] at hrt
  cases hrt
  exact stuck_no_run hrun

/-- So the v1 headline is an implication from `False` at every Surface. -/
theorem v1_headline_hypothesis_is_false (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (hc : LoweringCorrect S product) : False :=
  not_LoweringCorrect S product hc

/-! ## 2. The `ir_refines` field on its own, with a reverting object -/

/-- The field, verbatim. -/
def IrRefinesClaim (S : Surface p G₁ G₂ Gₜ) : Prop :=
  ∀ (ir : YulObject) (irLyt : EVM.Layout), S.irCheck ir = true →
    ∀ (W : ExecEnv) (H : Hash) (cd : Bytes) (c : ExternalCalls) (g₀ : U256),
      c.WorldLocal →
      ObsEquiv (RunContractIR S W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
        (RunShell S W H cd c (ExternalGas.ofFun fun _ => g₀))

theorem ir_refines_field_is_false (S : Surface p G₁ G₂ Gₜ)
    (W : ExecEnv) (H : Hash) (cd : Bytes) :
    ¬ IrRefinesClaim S := by
  intro hc
  let c : ExternalCalls := ExternalCalls.none
  let g : ExternalGas := ExternalGas.ofFun (fun _ => 0)
  let st : EvmState := callState W S.shellLayout H cd
  let reverted : EvmState := { st with halted := some (.revert, []) }
  let obsRevert : Obs := ⟨committedState st reverted, .halt⟩
  have hw : c.WorldLocal := fun _ _ _ _ _ => Iff.rfl
  have hrevert : RunContractIR S W H (objOf S revertB)
      S.shellLayout cd c g obsRevert := by
    refine ⟨revertB, [], irRuntime_objOf S revertB, reverted, ?_, rfl⟩
    show Step (Bridge.Dialect c g) [] [] st (.stmt (.block revertB))
      (.sres [] reverted .halt)
    exact Step.block (D := Bridge.Dialect c g)
      (Step.seqStop (D := Bridge.Dialect c g)
        (Step.exprStmtHalt (D := Bridge.Dialect c g)
          (Step.builtinHalt (D := Bridge.Dialect c g)
            (wlits_eval st [0, 0]) (by rfl))) (by decide))
  have hs := hc (objOf S revertB) S.shellLayout (irCheck_revert S) W H cd c 0 hw
  have hn := hc (objOf S emptyB) S.shellLayout (irCheck_empty S) W H cd c 0 hw
  obtain ⟨obsShell, hShell, hShellView⟩ :=
    (hs obsRevert.view).1 ⟨obsRevert, hrevert, rfl⟩
  obtain ⟨obsEmpty, hEmpty, hEmptyView⟩ :=
    (hn obsShell.view).2 ⟨obsShell, hShell, rfl⟩
  have hhalt : obsEmpty.outcome = .halt :=
    congrArg ObsView.outcome (hEmptyView.trans hShellView)
  obtain ⟨rt, V, hrt, raw, hrun, _hcommit⟩ := hEmpty
  rw [irRuntime_objOf] at hrt
  have heq : rt = emptyB := (Option.some.inj hrt).symm
  subst rt
  have hnormal := empty_run_outcome hrun
  exact Outcome.noConfusion (hnormal.symm.trans hhalt)

/-! ## 3. Forall-runs contracts are vacuous on stuck code -/

theorem variable_statement_is_stuck {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {name : String}
    {V' : VEnv D} {st' : D.State} {out : Outcome}
    (h : ExecStmt D funs V st (.exprStmt (.var name)) V' st' out) : False := by
  cases h with
  | exprStmt he => cases he
  | exprStmtHalt he => cases he

/-- A block that only reads an unbound name satisfies EVERY forall-runs contract, including one
    whose postcondition is `False`. -/
theorem stuck_satisfies_every_post {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (funs : FunEnv D) (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) :
    StmtsContractAll funs [.exprStmt (.var "missing")] pre post := by
  intro V st _hpre V' st' out hrun
  cases hrun with
  | seqCons he _ => exact False.elim (variable_statement_is_stuck he)
  | seqStop he _ => exact False.elim (variable_statement_is_stuck he)

end Midfall.Lowering.LegacyVacuity

#print axioms Midfall.Lowering.LegacyVacuity.not_LoweringCorrect
#print axioms Midfall.Lowering.LegacyVacuity.ir_refines_field_is_false
#print axioms Midfall.Lowering.LegacyVacuity.stuck_satisfies_every_post
