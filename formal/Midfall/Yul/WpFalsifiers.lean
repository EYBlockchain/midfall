/-
  Midfall.Yul.WpFalsifiers

  THE FALSIFIERS (T3.1, PLAN-V3, W12). A soundness theorem that nothing can make false is a
  vacuity trap: four V2 sorries landed in exactly that shape, and `docs/plans/PLAN-V3-cards.md`
  makes an exhibited falsifier part of T3.1's acceptance. Every declaration here is PROVED - there
  is no `sorry` in this file and none is registered in SORRY.md - and every measurement is a
  `#eval ... -- expect` gate that `scripts/kat_gate.py` runs.

  WHAT FIRES, and why each one is a real threat to the engine rather than a tautology:

    F1  `wpS` is FALSE at EVERY fuel on `Stmt.exprStmt` of a valued builtin (`add`). An expression
        statement must produce no values; `add` produces one, so the configuration is stuck and the
        transformer must refuse it. If `wpS` ever accepted this, `wp_sound` would be vacuous: there
        is no run to contradict, so the "theorem" would say nothing about a program that cannot
        execute. The gate pins the premise that makes it fire - `stepOp Op.add` returns a NONEMPTY
        result - which is the half a reader cannot see from the statement.
    F2  `wp` at fuel 0 is `False`, for every expression, statement and sequence. This is what makes
        the fuel index a bound on termination rather than decoration: `wp n ... Q` is a claim that
        every run finishes inside n steps, and at n = 0 nothing finishes. The executable mirror is
        pinned too: `Interp.run` at zero fuel returns `.stuck`.
    KAT `Bopen` at `Bridge.nondetBlock` DOES NOT prove a post that fixes the staticcall response.
        `nondetBlock` is `{ let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }` and the relation
        is the two-response one of `Bridge.twoResponses_nondet`, which admits BOTH success and
        failure. The proof is by the engine's own `wpS_sound`: a wp for the post `memory 31 = 1`
        would make EVERY run end with that byte set, and `Bridge.run_staticcall_mstore` exhibits a
        run of the same program from the same state that ends with it CLEAR. So the demonic
        `∀ resp, c.Call ... → Q resp` inside `Bopen` is load-bearing, not decorative: it is the only
        thing that makes a proof at an OPEN dialect mean "for every oracle answer". The functional
        transformer next to it is gated doing the OPPOSITE (`execBuiltin` fixes the byte), which is
        why T3.2's existence half runs at `Bfun` and not at `Bopen`.

  The `#assert_axioms` block at the bottom is the machine-checked half of the card's acceptance: it
  is a BUILD ERROR, not a printed line, if `sorryAx`, a `native_decide` axiom (D-P71) or any other
  axiom enters one of these cones.
-/
import Midfall.Yul.WpBridge
import Midfall.LoweringV2.HonestExec
import Midfall.Tools.Done
set_option autoImplicit false

namespace Midfall.Yul.WpFalsifiers
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.Wp Midfall.Yul.WpBridge

/-- The gas oracle of conjunct 2 and of every honest run: gas is not modelled, it is a constant. -/
def gh : ExternalGas := ExternalGas.ofFun fun _ => 0

/-- THE TWO-RESPONSE RELATION of `Midfall.Yul.Bridge.twoResponses_nondet` (Bridge.lean:377), repeated
    here as a name so the exhibit below can cite it: the pairing precompile answers with BOTH
    success values, so no post that fixes the answer can be proved demonically. -/
def twoResponses : ExternalCalls :=
  ⟨fun req st r => req.target = 0x0f ∧ r.world = CallWorld.ofState st ∧
    r.returndata = [] ∧ (r.success = true ∨ r.success = false)⟩

/-- The failing answer `twoResponses` admits. -/
def badResp : CallResponse :=
  { success := false, returndata := [], world := CallWorld.ofState EvmState.init }

/-- A pairing product that accepts everything: enough to make `honestExec` a closed
    term the VM can run. Whether the pairing check ACCEPTS is not what is under test here -
    the empty input of `nondetBlock` does not reach the pairing decode at all. -/
def trueProduct : PairingProduct := fun _ => true

/-! ## F1. A valued builtin in statement position is stuck at every fuel -/

/-- `add` on two words is a valued step: one word out, state unchanged. `rfl` - the arithmetic ops
    touch neither memory nor the oracles. -/
theorem stepOp_add (a b : U256) (st : EvmState) :
    stepOp Op.add [a, b] st = some (.ok [a + b] st) := rfl

/-- **FALSIFIER 1.** `Stmt.exprStmt` of a valued builtin is refused by `wpS` AT EVERY FUEL, for
    every call relation, every gas oracle, every state and every post. The fuel split is not
    cosmetic: below 6 the fuel runs out before the builtin is reached, at and above 6 the builtin is
    reached and refuses on its arity. Both halves end in `False`, which is the point - there is no
    fuel at which this statement is provable. -/
theorem exprStmt_add_not_wp {c : ExternalCalls} {g : ExternalGas} (n : Nat) (st : EvmState)
    (Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop) :
    ¬ wpS (Bridge.Dialect c g) (Bopen c g) (Cnone _) n [] [] st
        (.exprStmt (.builtin Op.add [wlit 1, wlit 2])) Q := by
  intro h
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 =>
      simp only [wpS, wpE, wpA, Bopen, wlit, YulSemantics.EVM.litValue, stepOp_add] at h
  | k+6 =>
      simp only [wpS, wpE, wpA, Bopen, wlit, YulSemantics.EVM.litValue, stepOp_add] at h

/-- THE GATE FOR F1: the premise the falsifier turns on, measured. `add` returns exactly one word,
    so `exprStmt` - which demands zero - is stuck. A `Bool` because `kat_gate.py` reads one token. -/
def addIsValued_ok : Bool :=
  match stepOp Op.add [1, 2] EvmState.init with
  | some (.ok rets _) => rets == [3]
  | _ => false
#eval addIsValued_ok -- expect true

/-! ## F2. Zero fuel proves nothing -/

/-- **FALSIFIER 2.** `wp` at fuel 0 is `False` - for expressions, for statements and for
    sequences. `Iff.rfl` is the whole proof, and that is the claim: the definition itself, not any
    lemma about it, is what refuses to prove anything with no fuel. -/
theorem wpE_zero {D : Dialect} [DecidableEq D.Value] (B : BT D) (C : CT D)
    (funs : FunEnv D) (V : VEnv D) (st : D.State) (e : Expr D.Op)
    (Q : EResult D → Prop) : wpE D B C 0 funs V st e Q ↔ False := Iff.rfl

theorem wpS_zero {D : Dialect} [DecidableEq D.Value] (B : BT D) (C : CT D)
    (funs : FunEnv D) (V : VEnv D) (st : D.State) (s : Stmt D.Op)
    (Q : VEnv D → D.State → Outcome → Prop) : wpS D B C 0 funs V st s Q ↔ False := Iff.rfl

theorem wpSS_zero {D : Dialect} [DecidableEq D.Value] (B : BT D) (C : CT D)
    (funs : FunEnv D) (V : VEnv D) (st : D.State) (ss : List (Stmt D.Op))
    (Q : VEnv D → D.State → Outcome → Prop) : wpSS D B C 0 funs V st ss Q ↔ False := Iff.rfl

/-- The zero-fuel claim at the open dialect, as one name, so it can be gated. -/
abbrev wpAtZero : Prop :=
  wpSS (Bridge.Dialect twoResponses ExternalGas.any) (Bopen twoResponses ExternalGas.any)
    (Cnone _) 0 [] [] EvmState.init nondetBlock (fun _ _ _ => True)

/-- THE GATE FOR F2. The `Decidable` instance IS the falsifier (`isFalse`), so the printed
    `false` is checked against the proof above and not against a second implementation: if the
    engine ever became provable at zero fuel, `isFalse` stops elaborating and the build goes red. -/
local instance : Decidable wpAtZero := isFalse fun h => h
#eval wpAtZero -- expect false

/-- The executable mirror of F2, MEASURED: at zero fuel the vendored interpreter reports
    `outOfFuel` on the same block - it does not stall on a stuck rule, it cannot start. Fuel is a
    bound on termination on both sides of `honest_adequacy`, which is what makes the two `False`s
    the same statement. -/
def interpZeroFuel_ok : Bool :=
  match Interp.run (execOf twoResponses gh (fun _ _ => some badResp) (fun _ => 0)) 0
      nondetBlock EvmState.init with
  | .outOfFuel => true
  | .ok _ => false
  | .stuck => false
#eval interpZeroFuel_ok -- expect true

/-! ## KAT. The demonic quantifier is load-bearing at the open dialect -/

/-- **THE KAT.** `Bopen` at `Bridge.nondetBlock` does NOT prove the post that fixes the staticcall
    response, at any fuel. PROOF BY THE ENGINE ITSELF: `wpS_sound` turns a wp into a claim about
    EVERY run, `Bridge.run_staticcall_mstore` exhibits a run of this block whose response is the
    failing one, and that run ends with `memory 31` CLEAR while the post demands it SET. So the
    `∀ resp, c.Call req st resp → Q resp` inside `Bopen` cannot be dropped without making this
    theorem unstatable - which is the W12 condition on `Bopen_sound`. -/
theorem nondetBlock_not_fixed (n : Nat) :
    ¬ wpS (Bridge.Dialect twoResponses gh) (Bopen twoResponses gh) (Cnone _) n [] []
        EvmState.init (.block nondetBlock) (fun _ st _ => st.memory 31 = 1) := by
  intro h
  let req0 : EVM.CallRequest :=
    { kind := .staticcall, gas := 0, target := 0x0f, value := 0,
      input := readBytes EvmState.init.memory 0 0 }
  have hbad : twoResponses.Call req0 EvmState.init badResp := ⟨rfl, rfl, rfl, Or.inr rfl⟩
  obtain ⟨st', run, hmem⟩ := run_staticcall_mstore (c := twoResponses) (resp := badResp) hbad
  have h1 := wpS_sound (Bridge.Dialect twoResponses gh) (Bopen twoResponses gh) (Cnone _)
      (Bopen_sound twoResponses gh) (Cnone_sound _) h [] st' .normal run
  rw [hmem] at h1
  exact absurd h1 (by decide)

/-- The KAT claim at a fuel big enough to reach the call (8), as one name, so it can be gated. -/
abbrev wpNondetFixesResponse : Prop :=
  wpS (Bridge.Dialect twoResponses gh) (Bopen twoResponses gh) (Cnone _) 8 [] [] EvmState.init
    (.block nondetBlock) (fun _ st _ => st.memory 31 = 1)

/-- THE GATE FOR THE KAT: the demonic transformer does not prove it. Same discipline as F2's gate -
    the `Decidable` instance is the theorem, so the print is checked against the proof. -/
local instance : Decidable wpNondetFixesResponse := isFalse (nondetBlock_not_fixed 8)
#eval wpNondetFixesResponse -- expect false

/-- THE CONTRAST, measured: at a FUNCTIONAL oracle the executable step DOES fix the byte - one
    answer, written into memory. This is why the existence half (T3.2 `wpSS_exists`) runs at `Bfun`
    and the soundness half runs at `Bopen`: the same statement is provable at one and refuted at the
    other, so neither transformer is a notational duplicate of the other. -/
def execBuiltinFixesByte_ok : Bool :=
  match execBuiltin (fun _ _ => some badResp) (fun _ => 0) Op.staticcall
      [0, 0x0f, 0, 0, 0, 0] EvmState.init with
  | some (.ok [flag] _) => flag == 0
  | _ => false
#eval execBuiltinFixesByte_ok -- expect true

/-- AND the honest dialect runs: `honestExec` (the lawful executable dialect of
    `Midfall/LoweringV2/HonestExec.lean`) executes `nondetBlock` to a normal outcome at fuel 40 and
    writes the byte the honest relation answers with - measured 0, because the empty input of this
    block is not a pairing proof, so the honest precompile refuses it. This is the executable half
    of `honest_adequacy`: the program the theorem quantifies over is a program that runs. -/
def honestRunByte_ok : Bool :=
  match Interp.run (Midfall.LoweringV2.honestExec trueProduct) 40 nondetBlock EvmState.init with
  | .ok (_, st, .normal) => st.memory 31 == 0
  | _ => false
#eval honestRunByte_ok -- expect true

/-! ## THE AXIOM PINS (the acceptance, as a build error) -/

#assert_axioms Midfall.Yul.Wp.wp_sound [propext]
#assert_axioms Midfall.Yul.Wp.wpSS_sound [propext]
#assert_axioms Midfall.Yul.Wp.wpS_sound [propext]
#assert_axioms Midfall.Yul.Wp.allRuns_cons_wp [propext]
#assert_axioms Midfall.Yul.WpBridge.Bopen_sound [propext, Quot.sound]
#assert_axioms Midfall.Yul.WpBridge.Cnone_sound [propext]
#assert_axioms Midfall.Yul.WpBridge.execOf_lawful [propext, Quot.sound]
#assert_axioms Midfall.Yul.WpBridge.Bfun_sound [propext, Quot.sound]
#assert_axioms Midfall.Yul.WpBridge.Bfun_live [propext, Quot.sound]
#assert_axioms Midfall.LoweringV2.callsOf_graph [propext, Quot.sound]
#assert_axioms Midfall.LoweringV2.honestExec_lawful [propext, Quot.sound]
#assert_axioms Midfall.LoweringV2.honest_adequacy [propext, Quot.sound]
#assert_axioms Midfall.Yul.WpFalsifiers.nondetBlock_not_fixed [propext, Quot.sound]
#assert_axioms Midfall.Yul.WpFalsifiers.exprStmt_add_not_wp [propext, Quot.sound]

end Midfall.Yul.WpFalsifiers
