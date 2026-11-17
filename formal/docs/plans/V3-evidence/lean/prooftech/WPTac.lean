import WPBridge
set_option autoImplicit false

/-!
WPTac (scratch, prooftech): DEFINITIONAL SYMBOLIC EXECUTION.

`wp_run` head-normalises a `wp...` goal with `Meta.whnf` (call-by-need: a continuation is unfolded
only when it is applied to a concrete symbolic result), splits `∧`, introduces `→`/`∀`, and closes
a branch whose fresh hypothesis is refuted by evaluation (`decide`). It stops at `Hold P` leaves and
at stuck heads. The kernel re-checks every step by definitional unfolding of the verified `wp`.
-/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-- A wrapper that stops head reduction at the user's postcondition. A STRUCTURE, not an
    `@[irreducible] def`: the kernel reducer ignores reducibility attributes and would unfold a def. -/
structure Hold (P : Prop) : Prop where
  intro ::
  elim : P

/-- `iszero`-style guards: the word of a Boolean is zero iff the Boolean is false. -/
theorem b2w_eq_zero_iff (b : Bool) : b2w b = (0 : U256) ↔ b = false := by
  cases b <;> decide

/-- Every run of a statement list ends in `Q` (the `StmtsContractAll` shape at one start state). -/
def AllRuns {D : Dialect} [DecidableEq D.Value] (funs : FunEnv D) (V : VEnv D) (st : D.State)
    (ss : Block D.Op) (Q : VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V' st' o, ExecStmts D funs V st ss V' st' o → Q V' st' o

theorem allRuns_of_wp {c : ExternalCalls} {g : ExternalGas} (n : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop}
    (h : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) n funs V st ss Q) :
    AllRuns funs V st ss Q :=
  wpSS_sound _ (Bopen c g) (Cnone _) (Bopen_sound c g) (Cnone_sound _) h

register_option wpDebug : Bool := { defValue := false, descr := "trace wp_run kernel steps" }
register_option wpLits : Bool := { defValue := true, descr := "sequence points: concrete values become literals" }
register_option wpLets : Bool := { defValue := true, descr := "sequence points: symbolic values and states become let-bound locals" }

open Lean Elab Tactic Meta in
/-- Kernel weak-head normal form (the C++ kernel reducer: lazy, cached, ~100x `Meta.whnf` here). -/
def kwhnf (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let t0 ← IO.monoMsNow
  let r ← ofExceptKernelException (Lean.Kernel.whnf (← getEnv) (← getLCtx) e)
  let t1 ← IO.monoMsNow
  if wpDebug.get (← getOptions) then
    IO.eprintln s!"  kwhnf {t1 - t0} ms -> head {r.getAppFn.constName?}"
  return r

open Lean Elab Tactic Meta in
/-- Every free variable of `e` is an oracle parameter (`ExternalCalls` / `ExternalGas`): the term
    is a CONCRETE word (a loop counter, an address), safe to evaluate in the kernel. -/
def isConcrete (e : Expr) : MetaM Bool := do
  for fv in (collectFVars {} e).fvarIds do
    let ty ← fv.getType
    unless ty.isConstOf ``YulSemantics.EVM.ExternalCalls ||
        ty.isConstOf ``YulSemantics.EVM.ExternalGas do
      return false
  return true

open Lean Elab Tactic Meta in
/-- Evaluate the SPINE and NAMES of a variable environment (never the values). A symbolic tail
    (an environment variable) is returned as is. -/
partial def envSpine (V : Expr) : MetaM (Array (Expr × Expr) × Option Expr) := do
  let V' ← kwhnf V
  if V'.isAppOfArity ``List.nil 1 then return (#[], none)
  else if V'.isAppOfArity ``List.cons 3 then
    let hd ← kwhnf (V'.getArg! 1)
    unless hd.isAppOfArity ``Prod.mk 4 do throwError "envSpine: head is not a pair{indentExpr hd}"
    let nm ← kwhnf (hd.getArg! 2)
    let (rest, tl) ← envSpine (V'.getArg! 2)
    return (#[(nm, hd.getArg! 3)] ++ rest, tl)
  else return (#[], some V)

open Lean Elab Tactic Meta in
/-- SEQUENCE-POINT NORMALISATION. At `Stop (wp.. funs V st ..)`: a concrete value becomes a
    literal, a symbolic non-variable value becomes a `let`-bound local (SSA name), and the state
    becomes a `let`-bound local. Terms stay small; the context accumulates a straight-line
    word-level program. Returns the goal for the normalised `wp..` proposition. -/
def normaliseAtStop (g : MVarId) (X : Expr) : MetaM MVarId := g.withContext do
  let f := X.getAppFn
  let args := X.getAppArgs
  unless args.size ≥ 3 do throwError "normaliseAtStop: unexpected shape"
  let w := mkNatLit 256
  let wordTy := mkApp (mkConst ``BitVec) w
  let (pairs, tail?) ← envSpine args[1]!
  let mut g := g
  let mut out : Array (Expr × Expr) := #[]
  for (nm, val) in pairs do
    let val ← instantiateMVars val
    if val.isFVar then
      out := out.push (nm, val)
    else if (wpLits.get (← getOptions)) && (← g.withContext (isConcrete val)) then
      let n ← g.withContext <| kwhnf (mkApp2 (mkConst ``BitVec.toNat) w val)
      match n.rawNatLit? with
      | some k => out := out.push (nm, mkApp2 (mkConst ``BitVec.ofNat) w (mkRawNatLit k))
      | none =>
          if n.isConstOf ``Nat.zero then
            out := out.push (nm, mkApp2 (mkConst ``BitVec.ofNat) w (mkRawNatLit 0))
          else out := out.push (nm, val)
    else if wpLets.get (← getOptions) then
      let g1 ← g.define (← mkFreshUserName `v) wordTy val
      let (fv, g2) ← g1.intro1P
      g := g2
      out := out.push (nm, mkFVar fv)
    else out := out.push (nm, val)
  -- the state
  let st := args[2]!
  let mut stE := st
  unless st.isFVar || !(wpLets.get (← getOptions)) do
    let g1 ← g.define (← mkFreshUserName `st) (mkConst ``YulSemantics.EVM.EvmState) st
    let (fv, g2) ← g1.intro1P
    g := g2
    stE := mkFVar fv
  -- rebuild the environment literal
  let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) wordTy
  let mut V' := tail?.getD (mkApp (mkConst ``List.nil [Level.zero]) pairTy)
  for (nm, val) in out.reverse do
    let pr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) wordTy nm val
    V' := mkApp3 (mkConst ``List.cons [Level.zero]) pairTy pr V'
  let X' := mkAppN f ((args.set! 1 V').set! 2 stE)
  let newGoal ← g.withContext <| mkFreshExprSyntheticOpaqueMVar X'
  g.assign (mkApp2 (mkConst ``Midfall.Scratch.ProofTech.Stop.intro) X' newGoal)
  return newGoal.mvarId!

open Lean Elab Tactic Meta in
/-- Decide a word equation `a = b` (both of type `U256`, up to defeq) by KERNEL evaluation, with a
    hand-built instance (no `synthInstance` on a large symbolic term). `some true` / `some false`
    when the evaluation is conclusive, `none` when it is stuck on a symbolic value. -/
def decideWordEq (a b : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  -- CONCRETENESS GUARD: only evaluate when every free variable is an oracle parameter
  -- (`ExternalCalls` / `ExternalGas`). Evaluating a word that depends on symbolic memory or
  -- calldata makes the kernel unfold `Nat.lor`/`loadWord` on non-literals before it gets stuck.
  unless (← isConcrete a) && (← isConcrete b) do return none
  let w := mkNatLit 256
  let p := mkApp3 (mkConst ``Eq [Level.one]) (mkApp (mkConst ``BitVec) w) a b
  let inst := mkApp3 (mkConst ``instDecidableEqBitVec) w a b
  let d := mkApp2 (mkConst ``Decidable.decide) p inst
  let r ← kwhnf d
  if r.isConstOf ``Bool.true then return some (true, p, inst)
  else if r.isConstOf ``Bool.false then return some (false, p, inst)
  else return none

open Lean Elab Tactic Meta in
/-- Core loop of `wp_run`. Returns the open leaves. -/
partial def wpRunCore (g : MVarId) (acc : Array MVarId) : MetaM (Array MVarId) := g.withContext do
  let t ← kwhnf (← g.getType)
  let g ← g.replaceTargetDefEq t
  g.withContext do
  if t.isAppOfArity ``Midfall.Scratch.ProofTech.Stop 1 then
    let g' ← normaliseAtStop g (t.getArg! 0)
    return ← wpRunCore g' acc
  match t.and? with
  | some (a, b) =>
      let ga ← mkFreshExprSyntheticOpaqueMVar a
      let gb ← mkFreshExprSyntheticOpaqueMVar b
      g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
      let acc ← wpRunCore ga.mvarId! acc
      wpRunCore gb.mvarId! acc
  | none =>
    if t.isConstOf ``True then
      g.assign (mkConst ``True.intro)
      return acc
    else if t.isForall then
      let hty := t.bindingDomain!
      let (h, g') ← g.intro1P
      g'.withContext do
        -- the two branch shapes wp produces: `cv = zero → _` and `cv ≠ zero → _`
        let tgt ← g'.getType
        match hty.eq? with
        | some (_, a, b) =>
            match ← decideWordEq a b with
            | some (false, _, inst) =>
                -- h : a = b, but evaluation says a ≠ b. Built by hand: NO Meta-level defeq check on
                -- the (large) target; the kernel checks the term once, at the end.
                let rflF := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)
                let npf := mkApp3 (mkConst ``of_decide_eq_false) hty inst rflF
                g'.assign (mkApp4 (mkConst ``absurd [Level.zero]) hty tgt (mkFVar h) npf)
                return acc
            | _ => wpRunCore g' acc
        | none =>
          -- `cv ≠ zero` is `Ne cv zero` (or `Not (cv = zero)` after unfolding)
          let ne? : Option (Expr × Expr) :=
            match hty.ne? with
            | some (_, a, b) => some (a, b)
            | none =>
              match hty.not? with
              | some q => (q.eq?).map fun (_, a, b) => (a, b)
              | none => none
          match ne? with
          | some (a, b) =>
              match ← decideWordEq a b with
              | some (true, p, inst) =>
                  -- h : a ≠ b, but evaluation says a = b
                  let rflT := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
                  let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst rflT
                  g'.assign (mkApp2 (mkConst ``False.elim [Level.zero]) tgt (mkApp (mkFVar h) pf))
                  return acc
              | _ => wpRunCore g' acc
          | none => wpRunCore g' acc
    else
      -- an arity check `[v].length = ["sel"].length`: a closed equation on Nat
      match t.eq? with
      | some (ty, a, b) =>
          if ty.isConstOf ``Nat then
            let inst := mkApp2 (mkConst ``instDecidableEqNat) a b
            let d := mkApp2 (mkConst ``Decidable.decide) t inst
            let r ← kwhnf d
            if r.isConstOf ``Bool.true then
              let rflT := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
              g.assign (mkApp3 (mkConst ``of_decide_eq_true) t inst rflT)
              return acc
            else return acc.push g
          else return acc.push g
      | none => return acc.push g

open Lean Elab Tactic Meta in
/-- `wp_run`: definitional symbolic execution of the main goal. -/
elab "wp_run" : tactic => do
  let t0 ← IO.monoMsNow
  let g ← getMainGoal
  let leaves ← wpRunCore g #[]
  let t1 ← IO.monoMsNow
  trace[Elab.debug] "wp_run: {t1 - t0} ms, {leaves.size} leaves"
  replaceMainGoal (leaves.toList ++ (← getGoals).tail)

end Midfall.Scratch.ProofTech
