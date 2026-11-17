import WPTac
set_option autoImplicit false

/-! VK (scratch): the vkLoading slice at the DEPLOYMENT, by definitional symbolic execution. -/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2 Midfall.Instances.PoseidonValid
open Midfall.Scratch.ProofTech.Lits

def scopeLit (c : ExternalCalls) (g : ExternalGas) : FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) helpersLit]

theorem one_and_b2w (b : Bool) : (1 : U256) &&& b2w b = b2w b := by cases b <;> decide
theorem b2w_and_b2w (a b : Bool) : b2w a &&& b2w b = b2w (a && b) := by
  cases a <;> cases b <;> decide

open Lean Elab Tactic Meta in
elab "count_goals" : tactic => do
  let gs ← getGoals
  logInfo m!"open leaves: {gs.length}"

set_option maxRecDepth 10000 in
set_option wpLets false in
set_option profiler true in
set_option profiler.threshold 50 in
theorem vk_all (c : ExternalCalls) (g : ExternalGas) (st : EvmState) (rv vk : U256) :
    AllRuns (scopeLit c g) [("success", (1 : U256)), ("r", rv), ("vk", vk)] st vkLoadingLit
      fun V' st' o => Hold (
        (o = .halt ∧ ∃ d, st'.halted = some (.revert, d)) ∨
        (o = .normal ∧ V' = [("success", (1 : U256)), ("r", rv), ("vk", vk)])) := by
  refine allRuns_of_wp 60 ?_
  wp_run
  count_goals
  -- leaf 1: the normal exit. Residue = Boolean-word algebra on the `success` chain.
  · rename_i h1 h2 h3
    refine ⟨Or.inr ⟨rfl, ?_⟩⟩
    simp only [Bridge.Dialect, evmWithExternal, EVM.litValue, YulSemantics.Dialect.zero,
      b2w_eq_zero_iff, one_and_b2w, b2w_and_b2w, decide_eq_false_iff_not, ne_eq,
      b2w_eq_zero_iff, Bool.and_eq_true, decide_eq_true_eq] at h3 ⊢
    clear h1 h2
    trace_state
    sorry
  -- leaves 2-4: the three guards fire; the halt record is literally a revert
  all_goals exact ⟨Or.inl ⟨rfl, _, rfl⟩⟩

#print axioms vk_all
end Midfall.Scratch.ProofTech
