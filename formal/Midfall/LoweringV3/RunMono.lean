-- |
-- Midfall.LoweringV3.RunMono
--
-- TRANSPORT HELPERS FOR `runBody_mono` (ST.13). The `Dialect c g` and `Dialect c' g`
-- differ only in `Builtin`; `FunEnv`/`Res` are indexed by the whole dialect, so the direct
-- `Step` induction needs an explicit transport. This file lands the GREEN transport layer:
-- casts for `FDecl`/`FScope`/`FunEnv`/`EResult`/`Res`, the `lookupFun` commutation, and the
-- `builtinWithExternal` monotonicity in the call relation.
--
-- NOT LANDED HERE: `Step_mono` itself. The remaining obstruction is definitional-instance
-- transport for `VEnv.setMany` and `selectSwitch` (both take `[DecidableEq D.Value]` and a
-- dialect-indexed type), plus the same for the loop/call helper terms. See the report.
import Midfall.Yul.Bridge

namespace Midfall.LoweringV3.RunMono
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
variable {c c' : ExternalCalls} {g : ExternalGas}

def fdeclCast (d : FDecl (Dialect c g)) : FDecl (Dialect c' g) :=
  { params := d.params, rets := d.rets, body := d.body }

def fscopeCast (s : FScope (Dialect c g)) : FScope (Dialect c' g) :=
  s.map (fun p => (p.1, fdeclCast (c := c) (c' := c') p.2))

def funEnvCast : FunEnv (Dialect c g) → FunEnv (Dialect c' g)
  | [] => []
  | s :: ss => fscopeCast (c := c) (c' := c') s :: funEnvCast ss

@[reducible] def eresultCast : EResult (Dialect c g) → EResult (Dialect c' g)
  | .vals vs st => .vals vs st
  | .halt st => .halt st

@[reducible] def resCast : Res (Dialect c g) → Res (Dialect c' g)
  | .eres e => .eres (eresultCast (c := c) (c' := c') e)
  | .sres V st o => .sres V st o

lemma find?_fscopeCast (s : FScope (Dialect c g)) (fn : Ident) :
    (fscopeCast (c := c) (c' := c') s).find? (fun p => p.1 = fn) =
      (s.find? (fun p => p.1 = fn)).map
        (fun p => (p.1, fdeclCast (c := c) (c' := c') p.2)) := by
  unfold fscopeCast
  induction s with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.find?_cons]
      split <;> simp_all

theorem lookupFun_funEnvCast (funs : FunEnv (Dialect c g)) (fn : Ident) :
    lookupFun (funEnvCast (c := c) (c' := c') funs) fn =
      (lookupFun funs fn).map
        (fun p => (fdeclCast (c := c) (c' := c') p.1,
          funEnvCast (c := c) (c' := c') p.2)) := by
  induction funs with
  | nil => rfl
  | cons s ss ih =>
      dsimp [funEnvCast, lookupFun]
      rw [find?_fscopeCast]
      cases hfind : s.find? (fun p => p.1 = fn) with
      | none =>
          simp only [hfind, Option.map_none] at *
          rw [ih]
      | some p =>
          simp only [hfind, Option.map_some]
          rfl

theorem externalCall_mono (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    {kind : CallKind} {gas target value io is oo os : U256} {st : EvmState}
    {res : BuiltinResult U256 EvmState}
    (h : externalCall c kind gas target value io is oo os st res) :
    externalCall c' kind gas target value io is oo os st res := by
  obtain ⟨response, hcall, hr⟩ := h
  exact ⟨response, hcc _ _ _ hcall, hr⟩

theorem builtinWithExternal_mono (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    {op : Op} {args : List U256} {st : EvmState} {res : BuiltinResult U256 EvmState}
    (h : builtinWithExternal c ExternalCreates.none g op args st res) :
    builtinWithExternal c' ExternalCreates.none g op args st res := by
  unfold builtinWithExternal at h ⊢
  repeat' (first | split at h | split)
  all_goals try (exact externalCall_mono hcc (by assumption))
  all_goals simp_all

lemma bindZeros_dialect_eq (xs : List Ident) :
    bindZeros (Dialect c g) xs = bindZeros (Dialect c' g) xs := rfl

lemma fscopeCast_hoist (body : Block (Dialect c g).Op) :
    fscopeCast (c := c) (c' := c') (hoist (Dialect c g) body) =
      hoist (Dialect c' g) body := by
  induction body with
  | nil => rfl
  | cons s ss ih =>
      have ih' := ih
      simp only [fscopeCast, hoist, fdeclCast] at ih'
      cases s <;> simp [hoist, fscopeCast, fdeclCast, ih']

@[simp] lemma resCast_eres (e : EResult (Dialect c g)) :
    resCast (c := c) (c' := c') (Res.eres e) = Res.eres (eresultCast (c := c) (c' := c') e) := rfl

@[simp] lemma resCast_sres (V : VEnv (Dialect c g)) (st : EvmState) (o : Outcome) :
    resCast (c := c) (c' := c') (Res.sres V st o) =
      @Res.sres (Dialect c' g) V st o := rfl



end Midfall.LoweringV3.RunMono
