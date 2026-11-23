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





lemma set_dialect_eq (V : VEnv (Dialect c g)) (x : Ident) (v : U256) :
    VEnv.set V x v = @VEnv.set (Dialect c' g) V x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      simp only [VEnv.set]
      by_cases h : p.1 = x <;> simp [h, ih]

lemma foldl_set_dialect_eq (start : VEnv (Dialect c g)) (zs : List (Ident × U256)) :
    zs.foldl (fun acc p => @VEnv.set (Dialect c g) acc p.1 p.2) start =
      zs.foldl (fun acc p => @VEnv.set (Dialect c' g) acc p.1 p.2) start := by
  induction zs generalizing start with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.foldl_cons]
      have hhead : @VEnv.set (Dialect c g) start p.1 p.2 =
          @VEnv.set (Dialect c' g) start p.1 p.2 := set_dialect_eq start p.1 p.2
      rw [hhead]
      exact ih (@VEnv.set (Dialect c' g) start p.1 p.2)

lemma setMany_dialect_eq (V : VEnv (Dialect c g)) (xs : List Ident) (vs : List U256) :
    @VEnv.setMany (Dialect c g) V xs vs = @VEnv.setMany (Dialect c' g) V xs vs := by
  unfold VEnv.setMany
  exact foldl_set_dialect_eq V (xs.zip vs)

lemma find?_dialect_eq (cv : U256) (cases : List (Literal × Block (Dialect c g).Op)) :
    List.find? (fun p => decide (cv = (Dialect c g).litValue p.1)) cases =
      List.find? (fun p => decide (cv = (Dialect c' g).litValue p.1)) cases := by
  letI : DecidableEq U256 := instDecidableEqBitVec
  induction cases with
  | nil => rfl
  | cons p ps ih => simp only [List.find?_cons]

lemma selectSwitch_dialect_eq (cv : U256) (cases : List (Literal × Block (Dialect c g).Op))
    (dflt : Option (Block (Dialect c g).Op)) :
    selectSwitch (Dialect c g) cv cases dflt = selectSwitch (Dialect c' g) cv cases dflt := by
  letI : DecidableEq U256 := instDecidableEqBitVec
  unfold selectSwitch
  rw [find?_dialect_eq (c := c) (c' := c')]
  split <;> rfl

theorem Step_mono (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    {funs : FunEnv (Dialect c g)} {V : VEnv (Dialect c g)} {st : EvmState}
    {code : Code (Dialect c g).Op} {res : Res (Dialect c g)}
    (h : Step (Dialect c g) funs V st code res) :
    Step (Dialect c' g) (funEnvCast (c := c) (c' := c') funs) V st code
      (resCast (c := c) (c' := c') res) := by
  letI : DecidableEq U256 := instDecidableEqBitVec
  induction h with
  | lit => exact Step.lit
  | var hv => exact Step.var hv
  | builtinOk hargs hb ihargs =>
      exact Step.builtinOk ihargs (builtinWithExternal_mono hcc hb)
  | builtinHalt hargs hb ihargs =>
      exact Step.builtinHalt ihargs (builtinWithExternal_mono hcc hb)
  | builtinArgsHalt hargs ihargs => exact Step.builtinArgsHalt ihargs
  | callOk hargs hlook hlen hbody ho ihargs ihbody =>
      exact Step.callOk ihargs (by rw [lookupFun_funEnvCast, hlook]; rfl) hlen
        (by rw [bindZeros_dialect_eq]; simpa [fdeclCast, resCast] using ihbody) ho
  | callHalt hargs hlook hlen hbody ihargs ihbody =>
      exact Step.callHalt ihargs (by rw [lookupFun_funEnvCast, hlook]; rfl) hlen
        (by rw [bindZeros_dialect_eq]; simpa [fdeclCast, resCast] using ihbody)
  | callArgsHalt hargs ihargs => exact Step.callArgsHalt ihargs
  | argsNil => exact Step.argsNil
  | argsCons hrest hhead ihrest ihhead => exact Step.argsCons ihrest ihhead
  | argsRestHalt hargs ihargs => exact Step.argsRestHalt ihargs
  | argsHeadHalt hrest hhead ihrest ihhead => exact Step.argsHeadHalt ihrest ihhead
  | funDef => exact Step.funDef
  | block hbody ihbody =>
      exact Step.block (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
  | letZero => exact Step.letZero
  | letVal he hlen ihe => simpa [resCast] using Step.letVal ihe hlen
  | letHalt he ihe => simpa [resCast] using Step.letHalt ihe
  | assignVal he hlen ihe =>
      rw [setMany_dialect_eq (c := c) (c' := c')]
      simpa [resCast] using Step.assignVal ihe hlen
  | assignHalt he ihe => simpa [resCast] using Step.assignHalt ihe
  | exprStmt he ihe => simpa [resCast] using Step.exprStmt ihe
  | exprStmtHalt he ihe => simpa [resCast] using Step.exprStmtHalt ihe
  | ifTrue hc hcv hbody ihc ihbody =>
      exact Step.ifTrue ihc hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
  | ifFalse hc hcv ihc => simpa [resCast] using Step.ifFalse ihc hcv
  | ifHalt hc ihc => simpa [resCast] using Step.ifHalt ihc
  | switchExec hc hbody ihc ihbody =>
      rw [selectSwitch_dialect_eq (c := c) (c' := c')] at ihbody
      exact Step.switchExec ihc
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
  | switchHalt hc ihc => simpa [resCast] using Step.switchHalt ihc
  | forLoop hinit hloop ihinit ihloop =>
      exact Step.forLoop
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihinit)
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihloop)
  | forInitHalt hinit ihinit =>
      exact Step.forInitHalt
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihinit)
  | «break» => exact Step.break
  | «continue» => exact Step.continue
  | «leave» => exact Step.leave
  | seqNil => exact Step.seqNil
  | seqCons h1 h2 ih1 ih2 => simpa [resCast] using Step.seqCons ih1 ih2
  | seqStop h1 hne ih1 => simpa [resCast] using Step.seqStop ih1 hne
  | loopDone hcond hcv ihcond => simpa [resCast] using Step.loopDone ihcond hcv
  | loopCondHalt hcond ihcond => simpa [resCast] using Step.loopCondHalt ihcond
  | loopStep hcond hcv hbody hcont hpost hloop ihcond ihbody ihpost ihloop =>
      exact Step.loopStep ihcond hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
        hcont
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihpost)
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihloop)
  | loopPostHalt hcond hcv hbody hcont hpost ihcond ihbody ihpost =>
      exact Step.loopPostHalt ihcond hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody) hcont
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihpost)
  | loopBreak hcond hcv hbody ihcond ihbody =>
      exact Step.loopBreak ihcond hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
  | loopLeave hcond hcv hbody ihcond ihbody =>
      exact Step.loopLeave ihcond hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)
  | loopBodyHalt hcond hcv hbody ihcond ihbody =>
      exact Step.loopBodyHalt ihcond hcv
        (by simpa [funEnvCast, fscopeCast_hoist, resCast, fdeclCast] using ihbody)


theorem Run_mono (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    {prog : Block Op} {st0 st' : EvmState} {o : Outcome}
    {V' : VEnv (Dialect c g)}
    (h : Midfall.Yul.Bridge.Run c g prog st0 V' st' o) :
    ∃ V'' : VEnv (Dialect c' g), Midfall.Yul.Bridge.Run c' g prog st0 V'' st' o := by
  unfold Midfall.Yul.Bridge.Run at h
  have hs := Step_mono (c := c) (c' := c') hcc h
  refine ⟨V', ?_⟩
  simpa [Midfall.Yul.Bridge.Run, YulSemantics.Run, YulSemantics.ExecStmt,
    funEnvCast, resCast] using hs

theorem RunCommitted_mono (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    {prog : Block Op} {st0 stObs : EvmState} {o : Outcome}
    {V' : VEnv (Dialect c g)}
    (h : Midfall.Yul.Bridge.RunCommitted c g prog st0 V' stObs o) :
    ∃ V'' : VEnv (Dialect c' g),
      Midfall.Yul.Bridge.RunCommitted c' g prog st0 V'' stObs o := by
  obtain ⟨st', hrun, hobs⟩ := h
  obtain ⟨V'', hrun'⟩ := Run_mono (c := c) (c' := c') hcc hrun
  exact ⟨V'', st', hrun', hobs⟩


end Midfall.LoweringV3.RunMono
