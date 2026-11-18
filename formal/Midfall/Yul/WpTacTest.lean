/-
  Midfall.Yul.WpTacTest

  THE ENGINE'S OWN TEST FOR wp_run (T3.1b, PLAN-V3): one closed wp_run example, with its
  #print axioms.

  WHY A SEPARATE FILE. The driver reads its own options (wpDebug / wpLits / wpLets), and those are
  register_option declarations. Lean cannot evaluate an [init] declaration of the module it is
  elaborating ("cannot evaluate [init] declaration 'Midfall.Yul.WpTac.wpDebug' in the same module",
  MEASURED: lake build exits 134 when the example sits at the bottom of WpTac.lean). So the tactic's
  own test has to be in a CONSUMER module. That is a real constraint on M6, not a preference: every
  file that runs wp_run imports WpTac rather than extending it.

  WHAT THE SLICE EXERCISES. Four statements, and nothing else is needed - no block row, no fixture,
  no generated slice, no Lits.lean:

    let x := add(1, 2)     a sequence point at which a CONCRETE word becomes a BitVec literal
                           (the wpLits path: every free variable of it is an oracle parameter);
    if x { }               the branch shape  cv = zero -> _ :  evaluation refutes 3 = 0, so this
                           leaf is CLOSED inside wp_run by of_decide_eq_false + absurd;
    if iszero(x) { }       the branch shape  cv != zero -> _ :  iszero 3 evaluates to 0, so the
                           hypothesis 0 != 0 is refuted and this leaf is CLOSED inside wp_run too;
    let y := mul(x, 4)     a second sequence point, read back from the normalised literal
                           environment.

  The residue is ONE leaf - a word equation on a normalised environment, not a 3000-node unfolding -
  and it discharges by rfl. Measured on this host: wp_run 13-14 ms, both files under 2 s. No
  native_decide anywhere (D-P71): the two closed leaves are hand-built kernel-evaluation proofs.
-/
import Midfall.Yul.WpTac
set_option autoImplicit false

namespace Midfall.Yul.WpTacTest
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac

/-- The test slice: two concrete lets and both guard shapes, one refuted by an equation and one by a
    disequality. -/
def wpTestSlice : Block EVM.Op :=
  [ .letDecl ["x"] (some (.builtin EVM.Op.add [.lit (Literal.number 1), .lit (Literal.number 2)])),
    .cond (.var "x") [],
    .cond (.builtin EVM.Op.iszero [.var "x"]) [],
    .letDecl ["y"] (some (.builtin EVM.Op.mul [.var "x", .lit (Literal.number 4)])) ]

/-- **The engine's own test.** One wp_run executes wpTestSlice at the open Bridge dialect for ANY
    call relation and ANY gas oracle: the two refuted guard leaves close inside the tactic, and the
    single remaining leaf is the literal environment [y = 12, x = 3] at the last sequence point. -/
theorem wpTestSlice_runs (c : ExternalCalls) (g : ExternalGas) (st : EvmState) :
    AllRuns ([] : FunEnv (Bridge.Dialect c g)) ([] : VEnv (Bridge.Dialect c g)) st wpTestSlice
      fun V' _ o => Hold (o = .normal ∧ V' = [("y", (12 : U256)), ("x", (3 : U256))]) := by
  refine allRuns_of_wp 20 ?_
  wp_run
  exact ⟨⟨rfl, rfl⟩⟩

#print axioms Midfall.Yul.WpTacTest.wpTestSlice_runs

end Midfall.Yul.WpTacTest
