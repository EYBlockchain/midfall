import Midfall.Instances.PoseidonValid
set_option autoImplicit false

/-!
P1 (scratch, prooftech): a LAWFUL executable dialect over the OPEN Bridge dialect, for oracles that
are graphs of (partial) functions. This is the piece RunEmitted.lean:33 names as "attempted and not
landed". With it `Interp.adequacy` applies to `Bridge.Dialect c g` whenever `c` and `g` are
function graphs - in particular to the honest dialect `callsOf product` / `ofFun (fun _ => 0)`.
-/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

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

/-- The honest dialect of conjunct 2 is a function graph. -/
theorem callsOf_graph (product : PairingProduct) (req : EVM.CallRequest) (st : EvmState)
    (resp : CallResponse) :
    (Midfall.LoweringV2.callsOf product).Call req st resp ↔
      honestOf (honestRelations product) req st = some resp := by
  simp [Midfall.LoweringV2.callsOf, honestCalls]

/-- The honest executable dialect: `toDialect` IS the dialect of `BlockProgress` / conjunct 2. -/
@[reducible] def honestExec (product : PairingProduct) : ExecDialect :=
  execOf (Midfall.LoweringV2.callsOf product) (ExternalGas.ofFun fun _ => 0)
    (honestOf (honestRelations product)) (fun _ => 0)

theorem honestExec_lawful (product : PairingProduct) : (honestExec product).Lawful :=
  execOf_lawful (callsOf_graph product) (fun _ _ => Iff.rfl)

/-- Adequacy at the OPEN honest dialect: this is the statement `run_adequacy` could not give. -/
theorem honest_adequacy (product : PairingProduct) {funs V st code res} :
    Step (Bridge.Dialect (Midfall.LoweringV2.callsOf product) (ExternalGas.ofFun fun _ => 0))
        funs V st code res ↔
      ∃ n, Interp.InterpOk (honestExec product) n funs V st code res :=
  Interp.adequacy (honestExec_lawful product)

#print axioms execOf_lawful
#print axioms honest_adequacy

end Midfall.Scratch.ProofTech
