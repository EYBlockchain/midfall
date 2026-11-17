import WPTac
import Midfall.LoweringV2.Blocks.TraceReturn
set_option autoImplicit false

/-! TR (scratch): TraceReturn at the DEPLOYMENT, re-derived with the wp engine. -/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2 Midfall.Instances.PoseidonValid
open Midfall.Scratch.ProofTech.Lits

/-- The deployment's function scope, as a literal. -/
def scopeLit (c : ExternalCalls) (g : ExternalGas) : FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) helpersLit]

set_option profiler true in
set_option profiler.threshold 50 in
theorem tr_all (c : ExternalCalls) (g : ExternalGas) (Vr : VEnv (Bridge.Dialect c g))
    (st : EvmState) (s : U256) :
    AllRuns (scopeLit c g) (("success", s) :: Vr) st traceReturnLit fun _ st' o =>
      Hold (o = .halt ∧ ((s ≠ 0 ∧ st'.halted = some (.ret, abiTrue)) ∨
                   (s = 0 ∧ ∃ d, st'.halted = some (.revert, d)))) := by
  refine allRuns_of_wp 40 ?_
  wp_run
  · rename_i h st1
    have h' : b2w (decide (s = 0)) = (0 : U256) := h
    have hs : s ≠ 0 := by simpa using (b2w_eq_zero_iff _).mp h'
    exact ⟨rfl, Or.inl ⟨hs, congrArg (fun x => some (HaltKind.ret, x))
      (Midfall.LoweringV2.Blocks.TraceReturn.readBytes_storeWord_one _ _)⟩⟩
  · rename_i h st1
    have h' : b2w (decide (s = 0)) ≠ (0 : U256) := h
    have hs : s = 0 := by
      by_contra hne
      exact h' ((b2w_eq_zero_iff _).mpr (by simpa using hne))
    exact ⟨rfl, Or.inr ⟨hs, _, rfl⟩⟩

#print axioms tr_all

end Midfall.Scratch.ProofTech
