import WPTac
set_option autoImplicit false

/-! LAGP (scratch): the lagrange slice's first ten statements at the DEPLOYMENT - two loops
    (6 + 10 iterations) over SYMBOLIC memory, concrete control flow - by definitional symbolic
    execution with sequence-point normalisation. Bounded measurement. -/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2 Midfall.Instances.PoseidonValid
open Midfall.Scratch.ProofTech.Lits

def scopeLit (c : ExternalCalls) (g : ExternalGas) : FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) helpersLit]

def frMod : U256 := 52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- The body of the lagrange slice's inner block. -/
def lagInner : Block EVM.Op :=
  match lagrangeLit with
  | [_, Stmt.block body, _] => body
  | _ => []

/-- Everything before the `batch_invert` call. -/
def lagPrefix : Block EVM.Op := lagInner.take 4

set_option maxRecDepth 10000 in
set_option profiler true in
set_option profiler.threshold 50 in
theorem lagPrefix_runs (c : ExternalCalls) (g : ExternalGas) (st : EvmState) (vk : U256) :
    AllRuns (scopeLit c g)
      [("lagrange_precompile_failed", (0 : U256)), ("success", (1 : U256)), ("r", frMod), ("vk", vk)]
      st lagPrefix fun V' _ o => Hold (o = .normal ∧ V'.length = 7) := by
  refine allRuns_of_wp 40 ?_
  wp_run
  all_goals exact ⟨rfl, rfl⟩

#print axioms lagPrefix_runs
end Midfall.Scratch.ProofTech
