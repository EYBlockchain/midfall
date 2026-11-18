/-
  Midfall.Yul.WpBridge

  THE BRIDGE INSTANTIATION OF THE WP ENGINE (T3.1, PLAN-V3). Ported VERBATIM from three PROVED
  scratch files in `docs/plans/V3-evidence/lean/prooftech/` - `P1_Exec.lean` (`execBuiltin`,
  `execOf`, `externalCall_iff`, `execOf_lawful`), `WPBridge.lean` (`Bopen`, `Bopen_sound`,
  `Cnone`, `Cnone_sound`) and `WPX.lean` (`BLive`, `Bfun`, `Bfun_sound`, `Bfun_live`: the card
  names these four for THIS file, and `BLive` is the hypothesis `Bfun_live` is stated under). The
  only changes are the namespace (`Midfall.Scratch.ProofTech` -> `Midfall.Yul.WpBridge`), the
  import paths, and making `BLive`'s two section variables explicit binders. No proof was
  restated.

  WHAT IS INSTANTIATED. `Midfall.Yul.Wp` is generic in the dialect; here it runs at the OPEN Bridge
  dialect `Bridge.Dialect c g` for ANY call relation and ANY gas oracle - which is strictly more
  than `run_adequacy` and `dialect_deterministic` give, because those need functional oracles. Two
  built-in transformers:

    * `Bopen c g`  DEMONIC: `staticcall` quantifies over EVERY response `c` admits and `gas()`
                   over every word `g` admits; the other call/create ops are refused (the generated
                   verifier never uses them); a local op is one `stepOp` evaluation and a stuck
                   local op is `False`. Sound for any `c`, `g` (`Bopen_sound`). This is what a
                   block row proves with when the response is not known.
    * `Bfun c g cf gf` FUNCTIONAL: one evaluation of `execBuiltin`. Sound AND live, but only when
                   `cf`/`gf` are graphs of the relations (`hc`/`hg`) - which is exactly what
                   `execOf_lawful` supplies for the honest dialect. This is what the totality card
                   (T3.2, `wpSS_exists`) runs at, because liveness needs a response to exist.

  `execOf c g cf gf` is the executable dialect over `Bridge.Dialect c g`; with it `Interp.adequacy`
  applies to the open dialect whenever the oracles are function graphs - the piece
  `Midfall/Lowering/RunEmitted.lean:33` names as "attempted and not landed". The honest instantiation
  of that (`callsOf_graph`, `honestExec`, `honest_adequacy`) lives in
  `Midfall/LoweringV2/HonestExec.lean`, NOT here: `callsOf` lives in `Midfall/LoweringV2/Statements.lean`
  and `Midfall/Yul` must not reach up into `LoweringV2` (card Do 2, "placement decided by imports").

  AXIOMS: `Bopen_sound` and `execOf_lawful` rest on `[propext, Quot.sound]`; no `sorryAx` and no
  `native_decide` anywhere in this file (D-P71).
-/
import YulSemantics
import YulSemantics.Dialect.EVM
import Midfall.Yul.Bridge
import Midfall.Yul.Wp
set_option autoImplicit false

namespace Midfall.Yul.WpBridge
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.Yul.Wp

/-! ## The lawful executable dialect over the open Bridge dialect (scratch `P1_Exec.lean`) -/

/-- The executable built-in step for the open dialect, given a response FUNCTION and a gas FUNCTION. -/
def execBuiltin (cf : EVM.CallRequest → EvmState → Option CallResponse) (gf : EvmState → U256)
    (op : Op) (args : List U256) (st : EvmState) : Option (BuiltinResult U256 EvmState) :=
  match op with
  | .call => match args with
      | [gas, target, value, io, is, oo, os] =>
          if st.env.static ∧ value ≠ 0 then
            some (.halt { st with halted := some (.staticViolation, []) })
          else
            (cf { kind := .call, gas, target, value,
                  input := readBytes st.memory io.toNat is.toNat } st).map fun resp =>
              .ok [resp.flag] (finishCall .call st resp io.toNat is.toNat oo.toNat os.toNat)
      | _ => none
  | .callcode => match args with
      | [gas, target, value, io, is, oo, os] =>
          (cf { kind := .callcode, gas, target, value,
                input := readBytes st.memory io.toNat is.toNat } st).map fun resp =>
            .ok [resp.flag] (finishCall .callcode st resp io.toNat is.toNat oo.toNat os.toNat)
      | _ => none
  | .delegatecall => match args with
      | [gas, target, io, is, oo, os] =>
          (cf { kind := .delegatecall, gas, target, value := st.env.callvalue,
                input := readBytes st.memory io.toNat is.toNat } st).map fun resp =>
            .ok [resp.flag] (finishCall .delegatecall st resp io.toNat is.toNat oo.toNat os.toNat)
      | _ => none
  | .staticcall => match args with
      | [gas, target, io, is, oo, os] =>
          (cf { kind := .staticcall, gas, target, value := 0,
                input := readBytes st.memory io.toNat is.toNat } st).map fun resp =>
            .ok [resp.flag] (finishCall .staticcall st resp io.toNat is.toNat oo.toNat os.toNat)
      | _ => none
  | .create => match args with
      | [_, _, _] =>
          if st.env.static then some (.halt { st with halted := some (.staticViolation, []) })
          else none
      | _ => none
  | .create2 => match args with
      | [_, _, _, _] =>
          if st.env.static then some (.halt { st with halted := some (.staticViolation, []) })
          else none
      | _ => none
  | .gas => match args with
      | [] => some (.ok [gf st] st)
      | _ => none
  | _ => stepOp op args st

/-- The executable dialect over `Bridge.Dialect c g`. -/
@[reducible] def execOf (c : ExternalCalls) (g : ExternalGas)
    (cf : EVM.CallRequest → EvmState → Option CallResponse) (gf : EvmState → U256) : ExecDialect :=
  { toDialect := Bridge.Dialect c g, builtinFn := execBuiltin cf gf }

theorem externalCall_iff {c : ExternalCalls} {cf : EVM.CallRequest → EvmState → Option CallResponse}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (kind : EVM.CallKind) (gas target value io is oo os : U256) (st : EvmState)
    (r : BuiltinResult U256 EvmState) :
    externalCall c kind gas target value io is oo os st r ↔
      (cf { kind := kind, gas := gas, target := target, value := value,
            input := readBytes st.memory io.toNat is.toNat } st).map (fun resp =>
        BuiltinResult.ok [resp.flag]
          (finishCall kind st resp io.toNat is.toNat oo.toNat os.toNat)) = some r := by
  unfold externalCall
  constructor
  · rintro ⟨resp, hcall, rfl⟩
    rw [(hc _ _ _).mp hcall]; rfl
  · intro h
    cases hcf : cf ⟨kind, gas, target, value, readBytes st.memory io.toNat is.toNat⟩ st with
    | none => rw [hcf] at h; cases h
    | some resp =>
        rw [hcf] at h
        exact ⟨resp, (hc _ _ _).mpr hcf, (Option.some.inj h).symm⟩

/-- **LAWFULNESS.** The executable step is exactly the relational one, when both oracles are
    function graphs. -/
theorem execOf_lawful {c : ExternalCalls} {g : ExternalGas}
    {cf : EVM.CallRequest → EvmState → Option CallResponse} {gf : EvmState → U256}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (hg : ∀ st w, g.Gas st w ↔ w = gf st) : (execOf c g cf gf).Lawful := by
  intro op args st r
  cases op
  all_goals try exact Iff.rfl
  case gas =>
    cases args with
    | cons a as => simp [builtinWithExternal, execBuiltin]
    | nil =>
        simp only [builtinWithExternal, execBuiltin]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [(hg st w).mp hw]
        · intro h
          exact ⟨gf st, (hg st _).mpr rfl, (Option.some.inj h).symm⟩
  case call =>
    rcases args with _|⟨a,_|⟨b,_|⟨v,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x8,xs⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    by_cases hstat : st.env.static = true ∧ v ≠ 0
    · rw [ite_eq_left hstat, ite_eq_left hstat]
      exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    · rw [ite_eq_right hstat, ite_eq_right hstat]
      exact externalCall_iff hc .call a b v io is oo os st r
  case callcode =>
    rcases args with _|⟨a,_|⟨b,_|⟨v,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x8,xs⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    exact externalCall_iff hc .callcode a b v io is oo os st r
  case delegatecall =>
    rcases args with _|⟨a,_|⟨b,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x7,xs⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    exact externalCall_iff hc .delegatecall a b st.env.callvalue io is oo os st r
  case staticcall =>
    rcases args with _|⟨a,_|⟨b,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x7,xs⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    exact externalCall_iff hc .staticcall a b 0 io is oo os st r
  case create =>
    rcases args with _|⟨v,_|⟨off,_|⟨sz,_|⟨x4,xs⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    by_cases hstat : st.env.static = true
    · rw [ite_eq_left hstat, ite_eq_left hstat]
      exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    · rw [ite_eq_right hstat, ite_eq_right hstat]
      exact ⟨fun h => (externalCreate_none_ne h).elim, fun h => by cases h⟩
  case create2 =>
    rcases args with _|⟨v,_|⟨off,_|⟨sz,_|⟨salt,_|⟨x5,xs⟩⟩⟩⟩⟩
    all_goals simp only [builtinWithExternal, execBuiltin]
    all_goals try exact ⟨False.elim, fun h => by cases h⟩
    by_cases hstat : st.env.static = true
    · rw [ite_eq_left hstat, ite_eq_left hstat]
      exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
    · rw [ite_eq_right hstat, ite_eq_right hstat]
      exact ⟨fun h => (externalCreate_none_ne h).elim, fun h => by cases h⟩

/-! ## The demonic transformer at the open Bridge dialect (scratch `WPBridge.lean`) -/

/-- The demonic built-in transformer of the open dialect. `staticcall` quantifies over EVERY
    response the relation admits, `gas()` over every oracle word; the other call/create ops are
    refused (the generated verifier never uses them); a local op is one `stepOp` evaluation, and a
    stuck local op is `False`. -/
def Bopen (c : ExternalCalls) (g : ExternalGas) : BT (Bridge.Dialect c g) := fun op args st Q =>
  match op with
  | .staticcall =>
      match args with
      | [gas, target, io, is, oo, os] =>
          ∀ resp, c.Call ⟨.staticcall, gas, target, 0, readBytes st.memory io.toNat is.toNat⟩ st resp →
            Q (.ok [resp.flag] (finishCall .staticcall st resp io.toNat is.toNat oo.toNat os.toNat))
      | _ => False
  | .gas =>
      match args with
      | [] => ∀ w, g.Gas st w → Q (.ok [w] st)
      | _ => False
  | .call | .callcode | .delegatecall | .create | .create2 => False
  | _ =>
      match stepOp op args st with
      | some r => Q r
      | none => False

theorem Bopen_sound (c : ExternalCalls) (g : ExternalGas) :
    BSound (Bridge.Dialect c g) (Bopen c g) := by
  intro op args st Q h r hr
  cases op
  all_goals try (
    have hr' : stepOp _ args st = some r := hr
    simp only [Bopen, hr'] at h
    exact h)
  case staticcall =>
    rcases args with _|⟨a,_|⟨b,_|⟨io,_|⟨is,_|⟨oo,_|⟨os,_|⟨x7,xs⟩⟩⟩⟩⟩⟩⟩
    all_goals simp only [Bopen] at h
    all_goals try exact h.elim
    simp only [builtinWithExternal] at hr
    obtain ⟨resp, hcall, rfl⟩ := hr
    exact h resp hcall
  case gas =>
    cases args with
    | cons a as => simp only [Bopen] at h
    | nil =>
        simp only [Bopen] at h
        simp only [builtinWithExternal] at hr
        obtain ⟨w, hw, rfl⟩ := hr
        exact h w hw
  all_goals (simp only [Bopen] at h)

/-- No call summaries: every user function is inlined. -/
def Cnone (D : Dialect) : CT D := fun _ _ _ _ => none

theorem Cnone_sound (D : Dialect) [DecidableEq D.Value] : CSound D (Cnone D) := by
  intro funs fn argvals st1 T h
  cases h


/-! ## The functional transformer, and the no-summaries table (scratch `WPX.lean`) -/

/-- The built-in transformer is LIVE: when it holds, a relational result exists and satisfies `Q`. -/
def BLive (D : Dialect) [DecidableEq D.Value] (B : BT D) : Prop :=
  ∀ op args st Q, B op args st Q → ∃ r, D.Builtin op args st r ∧ Q r

/-- The FUNCTIONAL transformer of a function-graph dialect (the honest dialect of conjunct 2):
    one evaluation of the executable step. Sound AND live, by `execOf_lawful`. -/
def Bfun (c : ExternalCalls) (g : ExternalGas)
    (cf : EVM.CallRequest → EvmState → Option CallResponse) (gf : EvmState → U256) :
    BT (Bridge.Dialect c g) := fun op args st Q =>
  match execBuiltin cf gf op args st with
  | some r => Q r
  | none => False

theorem Bfun_sound {c : ExternalCalls} {g : ExternalGas}
    {cf : EVM.CallRequest → EvmState → Option CallResponse} {gf : EvmState → U256}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (hg : ∀ st w, g.Gas st w ↔ w = gf st) :
    BSound (Bridge.Dialect c g) (Bfun c g cf gf) := by
  intro op args st Q h r hr
  have hr' : execBuiltin cf gf op args st = some r := (execOf_lawful hc hg op args st r).mp hr
  simp only [Bfun, hr'] at h
  exact h

theorem Bfun_live {c : ExternalCalls} {g : ExternalGas}
    {cf : EVM.CallRequest → EvmState → Option CallResponse} {gf : EvmState → U256}
    (hc : ∀ req st resp, c.Call req st resp ↔ cf req st = some resp)
    (hg : ∀ st w, g.Gas st w ↔ w = gf st) :
    BLive (Bridge.Dialect c g) (Bfun c g cf gf) := by
  intro op args st Q h
  cases hx : execBuiltin cf gf op args st with
  | none => simp only [Bfun, hx] at h
  | some r =>
      simp only [Bfun, hx] at h
      exact ⟨r, (execOf_lawful hc hg op args st r).mpr hx, h⟩

end Midfall.Yul.WpBridge
