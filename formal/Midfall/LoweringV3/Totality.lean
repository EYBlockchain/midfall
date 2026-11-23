/-
  Midfall.LoweringV3.Totality

  PL.H0 step 3(c) - **OBLIGATION 4 AS ITS OWN TREE.** `totalV3_of_stages` (RECON.2,
  Composition.lean) is DELETED here: `BodyTotal` asks for a run at EVERY calldata, while
  `ProgRowsV3` assumes `LeanAccepts`, so the sequenced progress rows cannot supply conjunct 4 at a
  REJECTING calldata. Confirmed by unfolding `TotalV3`/`BodyTotal` (Statements.lean:1432, :1318):
  the hypothesis a row needs is not derivable from the hypothesis the obligation quantifies over.
  So totality is ported from the evidence instead - `GeneratorRows.lean` section 10 - as
  `totalV3_correct`, proved from FOUR named leaves and nothing else.

  THE FOUR LEAVES (owners TOT.1, TOT.1.a):
    * `gasFree_of_valid`      - the program executes no `gas()` (decidable scan);
    * `runBody_gas_oblivious` - a gas-free program has the same runs under every gas oracle;
    * `block_live`            - per block, a run exists from a boundary a run can actually be at;
    * `prefix_live`           - the same for the prefix.
  `live_append`, `slices_live`, `stmts_append_stop` and `totalV3_correct` itself are PROVED glue.

  D-P71: every statement here is generic in the render and carries no fixture. The evidence's
  `hR : R.Valid` is read as `ValidV3 R` and its `SimPins R` as `G1CodecHeadlineLaws` - the same
  dissolution RECON.2 applied to the row bundles.
-/
import Midfall.LoweringV3.Statements
import Midfall.LoweringV3.PrefixV3
import Midfall.LoweringV2.Stages
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.LoweringV2.Blocks.FinalPairing
import Midfall.LoweringV3.FpConsts
import Midfall.LoweringV3.VkClean
import Midfall.LoweringV3.FpBody
import Midfall.Lowering.FrameWalk
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. The `gas()` scan: a program that never asks for gas has the same runs under any oracle -/

/-- **NON-VACUITY OF THE SCAN (W12 falsifier for `gasFree_of_valid`).** The scan is not the constant
    `true`: it refuses a `gas()` and accepts a `msize()`, both PROVED by `decide` at fuel 20 with
    no render content. Ported from the evidence (`GeneratorRows.lean:1249`). -/
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.gas []])]) = false := by decide

/-- The accepting arm of the same pair: a builtin that is not `gas()` passes the scan. -/
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.msize []])]) = true := by decide

/-! ### 1b. SCAN CLOSURE AND ORACLE INDEPENDENCE (the proof of TOT.1.a)

`gasFreeScan` is fuel-structural; `GasFreeScan` is its `∃ fuel` face over ALL five
`Scan` classes. The closure lemmas below invert one scan layer at a time, the
`GasFreeEnv` maintained through `Step`'s function environments, and the casts rebuild
the `FDecl`/`FunEnv`/`Res` indices at the target dialect (the `Dialect c g` and
`Dialect c g'` values are NOT definitionally equal - only `Op`, `Value`, `State`,
`litValue` are - so the environment and result indices are rebuilt field for field).
`step_gas_irrel` is then one induction on the derivation: the only constructor whose
premise reads the oracle is `builtinOk`/`builtinHalt` at `Op.gas`, and the scan forbids
that op. -/

def GasFreeScan (sc : Scan) : Prop := ∃ n, gasFreeScan n sc = true

theorem gfs_stmt_of_mem {ss : Block EVM.Op} (h : GasFreeScan (.b ss))
    (s : Stmt EVM.Op) (hs : s ∈ ss) : GasFreeScan (.s s) := by
  induction ss with
  | nil => exact absurd hs (by simp)
  | cons a as ih =>
      obtain ⟨fuel, hfuel⟩ := h
      cases fuel with
      | zero => simp [gasFreeScan] at hfuel
      | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
          rcases List.mem_cons.mp hs with heq | hs
          · subst heq; exact ⟨m, hfuel.1⟩
          · exact ih ⟨m, hfuel.2⟩ hs

theorem gfs_funDef_body_of_block {ss : Block EVM.Op} (h : GasFreeScan (.b ss))
    {n : Ident} {ps rs : List Ident} {fb : Block EVM.Op}
    (hmem : Stmt.funDef n ps rs fb ∈ ss) : GasFreeScan (.b fb) := by
  induction ss with
  | nil => exact absurd hmem (by simp)
  | cons a as ih =>
      obtain ⟨fuel, hfuel⟩ := h
      cases fuel with
      | zero => simp [gasFreeScan] at hfuel
      | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst heq
            cases m with
            | zero => simp [gasFreeScan] at hfuel
            | succ k => exact ⟨k, hfuel.1⟩
          · exact ih ⟨m, hfuel.2⟩ hmem

/-- The function bodies of `hoist body` are gas-free. -/
theorem gfs_hoist {c : ExternalCalls} {g : ExternalGas} {body : Block EVM.Op}
    (h : GasFreeScan (.b body)) :
    ∀ p ∈ hoist (Dialect c g) body, GasFreeScan (.b p.2.body) := by
  intro p hp
  simp only [hoist, List.mem_filterMap] at hp
  obtain ⟨s, hs, hps⟩ := hp
  cases s with
  | funDef n ps rs fb =>
      simp only [Option.some.injEq] at hps
      subst hps
      exact gfs_funDef_body_of_block h hs
  | _ => simp at hps

theorem gfs_builtin_head {sc : Scan} (h : GasFreeScan sc) {op : EVM.Op} {args : List (Expr EVM.Op)}
    (he : sc = .e (.builtin op args)) : op ≠ EVM.Op.gas := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m =>
      simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
      rw [Bool.not_eq_true'] at hfuel
      intro hop
      subst hop
      exact absurd hfuel.1 (by simp)

theorem gfs_args_of_builtin {sc : Scan} (h : GasFreeScan sc) {op : EVM.Op}
    {args : List (Expr EVM.Op)}
    (he : sc = .e (.builtin op args)) : GasFreeScan (.es args) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).2⟩

theorem gfs_args_head {sc : Scan} (h : GasFreeScan sc) {e : Expr EVM.Op} {rest : List (Expr EVM.Op)}
    (he : sc = .es (e :: rest)) : GasFreeScan (.e e) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).1⟩

theorem gfs_args_tail {sc : Scan} (h : GasFreeScan sc) {e : Expr EVM.Op} {rest : List (Expr EVM.Op)}
    (he : sc = .es (e :: rest)) : GasFreeScan (.es rest) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).2⟩

theorem gfs_call_args {sc : Scan} (h : GasFreeScan sc) {f : Ident} {args : List (Expr EVM.Op)}
    (he : sc = .e (.call f args)) : GasFreeScan (.es args) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, hfuel⟩

theorem gfs_block_of_stmt {sc : Scan} (h : GasFreeScan sc) {body : Block EVM.Op}
    (he : sc = .s (.block body)) : GasFreeScan (.b body) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, hfuel⟩

theorem gfs_letVal {sc : Scan} (h : GasFreeScan sc) {vars : List Ident} {e : Expr EVM.Op}
    (he : sc = .s (.letDecl vars (some e))) : GasFreeScan (.e e) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, hfuel⟩

theorem gfs_assign {sc : Scan} (h : GasFreeScan sc) {vars : List Ident} {e : Expr EVM.Op}
    (he : sc = .s (.assign vars e)) : GasFreeScan (.e e) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, hfuel⟩

theorem gfs_cond {sc : Scan} (h : GasFreeScan sc) {c : Expr EVM.Op} {body : Block EVM.Op}
    (he : sc = .s (.cond c body)) :
    GasFreeScan (.e c) ∧ GasFreeScan (.b body) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m =>
      simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
      exact ⟨⟨m, hfuel.1⟩, ⟨m, hfuel.2⟩⟩

theorem gfs_switch {sc : Scan} (h : GasFreeScan sc) {c : Expr EVM.Op}
    {cases : List (Literal × Block EVM.Op)} {dflt : Option (Block EVM.Op)}
    (he : sc = .s (.switch c cases dflt)) :
    GasFreeScan (.e c) ∧ GasFreeScan (.cs cases) ∧
      (∀ d, dflt = some d → GasFreeScan (.b d)) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m =>
      simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
      obtain ⟨⟨hc, hcs⟩, hd⟩ := hfuel
      refine ⟨⟨m, hc⟩, ⟨m, hcs⟩, ?_⟩
      cases dflt with
      | none => intro d hd'; cases hd'
      | some d => intro d' hd'; cases hd'; exact ⟨m, hd⟩

theorem gfs_forLoop {sc : Scan} (h : GasFreeScan sc) {init : Block EVM.Op} {c : Expr EVM.Op}
    {post body : Block EVM.Op} (he : sc = .s (.forLoop init c post body)) :
    GasFreeScan (.b init) ∧ GasFreeScan (.e c) ∧
      GasFreeScan (.b post) ∧ GasFreeScan (.b body) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m =>
      simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
      obtain ⟨⟨⟨hi, hc⟩, hp⟩, hb⟩ := hfuel
      exact ⟨⟨m, hi⟩, ⟨m, hc⟩, ⟨m, hp⟩, ⟨m, hb⟩⟩

theorem gfs_exprStmt {sc : Scan} (h : GasFreeScan sc) {e : Expr EVM.Op}
    (he : sc = .s (.exprStmt e)) : GasFreeScan (.e e) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, hfuel⟩

theorem gfs_stmt_head {sc : Scan} (h : GasFreeScan sc) {s : Stmt EVM.Op} {ss : Block EVM.Op}
    (he : sc = .b (s :: ss)) : GasFreeScan (.s s) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).1⟩

theorem gfs_stmt_tail {sc : Scan} (h : GasFreeScan sc) {s : Stmt EVM.Op} {ss : Block EVM.Op}
    (he : sc = .b (s :: ss)) : GasFreeScan (.b ss) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).2⟩

theorem gfs_case_head {sc : Scan} (h : GasFreeScan sc) {l : Literal} {b : Block EVM.Op}
    {rest : List (Literal × Block EVM.Op)}
    (he : sc = .cs ((l, b) :: rest)) : GasFreeScan (.b b) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).1⟩

theorem gfs_case_tail {sc : Scan} (h : GasFreeScan sc) {l : Literal} {b : Block EVM.Op}
    {rest : List (Literal × Block EVM.Op)}
    (he : sc = .cs ((l, b) :: rest)) : GasFreeScan (.cs rest) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m => exact ⟨m, (Bool.and_eq_true_iff.mp hfuel).2⟩



open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage

theorem gfs_block_stmt {body : Block EVM.Op} (h : GasFreeScan (.b body)) :
    GasFreeScan (.s (.block body)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, hn⟩

theorem gfs_case_of_mem {cases : List (Literal × Block EVM.Op)}
    (h : GasFreeScan (.cs cases)) {l : Literal} {b : Block EVM.Op}
    (hm : (l, b) ∈ cases) : GasFreeScan (.b b) := by
  induction cases with
  | nil => exact absurd hm (by simp)
  | cons p ps ih =>
      obtain ⟨fuel, hfuel⟩ := h
      cases fuel with
      | zero => simp [gasFreeScan] at hfuel
      | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
          rcases List.mem_cons.mp hm with heq | hm
          · cases p with
            | mk l' b' =>
                simp only [Prod.mk.injEq] at heq
                obtain ⟨rfl, rfl⟩ := heq
                exact ⟨m, hfuel.1⟩
          · exact ih ⟨m, hfuel.2⟩ hm

theorem gfs_selectSwitch {c : ExternalCalls} {g : ExternalGas} {cv : U256}
    {cases : List (Literal × Block EVM.Op)} {dflt : Option (Block EVM.Op)}
    (hc : GasFreeScan (.cs cases))
    (hd : ∀ d, dflt = some d → GasFreeScan (.b d)) :
    GasFreeScan (.b (selectSwitch (Dialect c g) cv cases dflt)) := by
  unfold selectSwitch
  cases hf : cases.find? (fun p => decide (cv = (Dialect c g).litValue p.1)) with
  | some p =>
      obtain ⟨l, b⟩ := p
      exact gfs_case_of_mem hc (List.mem_of_find?_eq_some hf)
  | none =>
      cases dflt with
      | none => exact ⟨1, rfl⟩
      | some d => exact hd d rfl

/-- Every function body in the environment is gas-free. -/
def GasFreeEnv {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Dialect c g)) : Prop :=
  ∀ sc ∈ funs, ∀ p ∈ sc, GasFreeScan (.b p.2.body)

theorem gfsEnv_lookupFun {c : ExternalCalls} {g : ExternalGas}
    {funs : FunEnv (Dialect c g)} (henv : GasFreeEnv funs)
    {fn : Ident} {decl : FDecl (Dialect c g)} {cenv : FunEnv (Dialect c g)}
    (hl : lookupFun funs fn = some (decl, cenv)) :
    GasFreeScan (.b decl.body) ∧ GasFreeEnv cenv := by
  induction funs with
  | nil => simp [lookupFun] at hl
  | cons scope rest ih =>
      cases hf : scope.find? (fun p => p.1 = fn) with
      | some p =>
          simp only [lookupFun, hf, Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨hd, hc⟩ := hl
          subst hd; subst hc
          exact ⟨henv scope (by simp) p (List.mem_of_find?_eq_some hf), henv⟩
      | none =>
          simp only [lookupFun, hf] at hl
          have hrest : GasFreeEnv rest := fun sc hsc p hp => henv sc (by simp [hsc]) p hp
          exact ih hrest hl

theorem builtinWithExternal_gas_irrel {c : ExternalCalls} {g g' : ExternalGas}
    {op : EVM.Op} (hop : op ≠ EVM.Op.gas) (args : List U256) (st : EvmState)
    {r : BuiltinResult U256 EvmState} :
    builtinWithExternal c ExternalCreates.none g op args st r ↔
      builtinWithExternal c ExternalCreates.none g' op args st r := by
  cases op <;> first | exact Iff.rfl | exact absurd rfl hop

/-- The scan of a code class. -/
def codeGasFree : Code EVM.Op → Prop
  | .expr e => GasFreeScan (.e e)
  | .args es => GasFreeScan (.es es)
  | .stmt s => GasFreeScan (.s s)
  | .stmts ss => GasFreeScan (.b ss)
  | .loop c post body => GasFreeScan (.s (.forLoop [] c post body))

theorem gfs_loop_of_forLoop {sc : Scan} (h : GasFreeScan sc) {init : Block EVM.Op}
    {c : Expr EVM.Op} {post body : Block EVM.Op}
    (he : sc = .s (.forLoop init c post body)) :
    GasFreeScan (.s (.forLoop [] c post body)) := by
  subst he
  obtain ⟨fuel, hfuel⟩ := h
  cases fuel with
  | zero => simp [gasFreeScan] at hfuel
  | succ m =>
      simp only [gasFreeScan, Bool.and_eq_true_iff] at hfuel
      obtain ⟨⟨⟨hi, hc⟩, hp⟩, hb⟩ := hfuel
      cases m with
      | zero => simp [gasFreeScan] at hi
      | succ k =>
          exact ⟨k + 2, by
            show gasStep (.s (.forLoop [] c post body)) (gasFreeScan (k + 1)) = true
            simp only [gasStep]
            rw [hc, hp, hb]
            rfl⟩

/-- Move a function declaration to the same-oracle-changed dialect: the body is the same AST. -/
def fdeclCast {c : ExternalCalls} {g g' : ExternalGas}
    (d : FDecl (Dialect c g)) : FDecl (Dialect c g') :=
  { params := d.params, rets := d.rets, body := d.body }

def fscopeCast {c : ExternalCalls} {g g' : ExternalGas}
    (sc : FScope (Dialect c g)) : FScope (Dialect c g') :=
  sc.map fun p => (p.1, fdeclCast p.2)

def funEnvCast {c : ExternalCalls} {g g' : ExternalGas}
    (funs : FunEnv (Dialect c g)) : FunEnv (Dialect c g') :=
  funs.map fscopeCast

def eresultCast {c : ExternalCalls} {g g' : ExternalGas} :
    EResult (Dialect c g) → EResult (Dialect c g')
  | .vals vs st => .vals vs st
  | .halt st => .halt st

def resCast {c : ExternalCalls} {g g' : ExternalGas} :
    Res (Dialect c g) → Res (Dialect c g')
  | .eres r => .eres (eresultCast r)
  | .sres V st o => .sres V st o

theorem fscopeCast_hoist {c : ExternalCalls} {g g' : ExternalGas} (body : Block EVM.Op) :
    fscopeCast (c := c) (g := g) (g' := g') (hoist (Dialect c g) body)
      = hoist (Dialect c g') body := by
  induction body with
  | nil => rfl
  | cons s ss ih =>
      cases s with
      | funDef n ps rs fb =>
          have ih' : List.map (fun p => (p.1, fdeclCast (g' := g') p.2))
              (hoist (Dialect c g) ss) = hoist (Dialect c g') ss := by
            simpa [fscopeCast] using ih
          simp only [fscopeCast, List.map_cons, hoist, List.filterMap_cons] at ih' ⊢
          rw [ih']
          rfl
      | block b =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | letDecl vars e =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | assign vars e =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | cond e b =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | «switch» e cs d =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | forLoop i e p b =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | exprStmt e =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | «break» =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | «continue» =>
          simp only [hoist, List.filterMap_cons]
          exact ih
      | «leave» =>
          simp only [hoist, List.filterMap_cons]
          exact ih

theorem cast_hoist_cons {c : ExternalCalls} {g g' : ExternalGas} (body : Block EVM.Op)
    (funs : FunEnv (Dialect c g)) :
    funEnvCast (c := c) (g := g) (g' := g') (hoist (Dialect c g) body :: funs)
      = hoist (Dialect c g') body :: funEnvCast funs := by
  simp only [funEnvCast, List.map_cons, fscopeCast_hoist]

theorem find?_fscopeCast {c : ExternalCalls} {g g' : ExternalGas}
    (scope : FScope (Dialect c g)) (fn : Ident) :
    List.find? (fun p => p.1 = fn) (fscopeCast (g' := g') scope)
      = Option.map (fun p => (p.1, fdeclCast (g' := g') p.2))
          (List.find? (fun p => p.1 = fn) scope) := by
  rw [fscopeCast, List.find?_map]
  rfl

theorem lookupFun_cast {c : ExternalCalls} {g g' : ExternalGas}
    {funs : FunEnv (Dialect c g)} {fn : Ident} {decl : FDecl (Dialect c g)}
    {cenv : FunEnv (Dialect c g)}
    (hl : lookupFun funs fn = some (decl, cenv)) :
    lookupFun (funEnvCast (g' := g') funs) fn
      = some (fdeclCast (g' := g') decl, funEnvCast cenv) := by
  induction funs with
  | nil => simp [lookupFun] at hl
  | cons scope rest ih =>
      cases hf : scope.find? (fun p => p.1 = fn) with
      | some p =>
          simp only [lookupFun, hf, Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          simp only [funEnvCast, List.map_cons, lookupFun, find?_fscopeCast, hf,
            Option.map_some]
      | none =>
          simp only [lookupFun, hf] at hl
          simp only [funEnvCast, List.map_cons, lookupFun, find?_fscopeCast, hf,
            Option.map_none]
          exact ih hl


variable {c : ExternalCalls} {g g' : ExternalGas}

theorem get_gas_irrel (V : VEnv (Dialect c g)) (x : Ident) :
    VEnv.get (D := Dialect c g) V x = VEnv.get (D := Dialect c g') V x := rfl

theorem set_gas_irrel (V : VEnv (Dialect c g)) (x : Ident) (v : U256) :
    (VEnv.set V x v : VEnv (Dialect c g')) = VEnv.set V x v := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, w⟩ := p
      simp only [VEnv.set]
      split
      · rfl
      · rw [ih]

theorem setMany_gas_irrel (V : VEnv (Dialect c g)) (vars : List Ident) (vals : List U256) :
    (VEnv.setMany V vars vals : VEnv (Dialect c g')) = VEnv.setMany V vars vals := by
  induction vars generalizing vals V with
  | nil => cases vals <;> rfl
  | cons x xs ih =>
      cases vals with
      | nil => rfl
      | cons v vs =>
          simp only [VEnv.setMany, List.zip_cons_cons, List.foldl_cons]
          rw [set_gas_irrel]
          exact ih (VEnv.set V x v) vs

theorem bindZeros_gas_irrel (vars : List Ident) :
    (bindZeros (Dialect c g) vars : VEnv (Dialect c g')) = bindZeros (Dialect c g') vars := rfl

theorem getD_gas_irrel (V : VEnv (Dialect c g)) (x : Ident) :
    (VEnv.get V x).getD (Dialect.zero (Dialect c g))
      = (VEnv.get (D := Dialect c g') V x).getD (Dialect.zero (Dialect c g')) := rfl

theorem map_get_gas_irrel (rets : List Ident) (V : VEnv (Dialect c g)) :
    rets.map (fun r => (VEnv.get V r).getD (Dialect.zero (Dialect c g)))
      = rets.map (fun r => (VEnv.get (D := Dialect c g') V r).getD
          (Dialect.zero (Dialect c g'))) := rfl


theorem selectSwitch_irrel {c : ExternalCalls} {g g' : ExternalGas} (cv : U256)
    (cases : List (Literal × Block EVM.Op)) (dflt : Option (Block EVM.Op)) :
    selectSwitch (Dialect c g) cv cases dflt = selectSwitch (Dialect c g') cv cases dflt := by
  unfold selectSwitch
  induction cases with
  | nil => cases dflt <;> rfl
  | cons p rest ih =>
      obtain ⟨l, b⟩ := p
      simp only [List.find?_cons]
      split <;> simp_all

theorem step_gas_irrel {c : ExternalCalls} {g g' : ExternalGas} :
    ∀ {funs : FunEnv (Dialect c g)} {V : VEnv (Dialect c g)} {st : EvmState}
      {code : Code EVM.Op} {res : Res (Dialect c g)},
      Step (Dialect c g) funs V st code res →
      codeGasFree code → GasFreeEnv funs →
      Step (Dialect c g') (funEnvCast (c := c) (g := g) (g' := g') funs) V st code
        (resCast (c := c) (g := g) (g' := g') res) := by
  intro funs V st code res h
  induction h with
  | lit =>
      intro _ _
      exact Step.lit
  | var hget =>
      intro _ _
      exact Step.var hget
  | builtinOk hargs hb ihargs =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.builtinOk (ihargs (gfs_args_of_builtin hno rfl) henv)
        ((builtinWithExternal_gas_irrel (g := g) (g' := g')
          (gfs_builtin_head hno rfl) _ _).mp hb)
  | builtinHalt hargs hb ihargs =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.builtinHalt (ihargs (gfs_args_of_builtin hno rfl) henv)
        ((builtinWithExternal_gas_irrel (g := g) (g' := g')
          (gfs_builtin_head hno rfl) _ _).mp hb)
  | builtinArgsHalt hargs ihargs =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.builtinArgsHalt (ihargs (gfs_args_of_builtin hno rfl) henv)
  | callOk hargs hlookup hlen hbody hout ihargs ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hdecl, hcenv⟩ := gfsEnv_lookupFun henv hlookup
      exact Step.callOk (ihargs (gfs_call_args hno rfl) henv)
        (lookupFun_cast hlookup) hlen
        (ihbody (gfs_block_stmt hdecl) hcenv) hout
  | callHalt hargs hlookup hlen hbody ihargs ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hdecl, hcenv⟩ := gfsEnv_lookupFun henv hlookup
      exact Step.callHalt (ihargs (gfs_call_args hno rfl) henv)
        (lookupFun_cast hlookup) hlen
        (ihbody (gfs_block_stmt hdecl) hcenv)
  | callArgsHalt hargs ihargs =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.callArgsHalt (ihargs (gfs_call_args hno rfl) henv)
  | argsNil =>
      intro _ _
      exact Step.argsNil
  | argsCons hrest hexpr ihrest ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.argsCons (ihrest (gfs_args_tail hno rfl) henv)
        (ihexpr (gfs_args_head hno rfl) henv)
  | argsRestHalt hrest ihrest =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.argsRestHalt (ihrest (gfs_args_tail hno rfl) henv)
  | argsHeadHalt hrest hexpr ihrest ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.argsHeadHalt (ihrest (gfs_args_tail hno rfl) henv)
        (ihexpr (gfs_args_head hno rfl) henv)
  | funDef =>
      intro _ _
      exact Step.funDef
  | block hbody ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      have hb := gfs_block_of_stmt hno rfl
      have hstep := ihbody hb (fun sc hsc p hp => by
        rcases List.mem_cons.mp hsc with rfl | hsc
        · exact gfs_hoist hb p hp
        · exact henv sc hsc p hp)
      rw [cast_hoist_cons] at hstep
      exact Step.block hstep
  | letZero =>
      intro _ _
      exact Step.letZero
  | letVal hexpr hlen ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.letVal (ihexpr (gfs_letVal hno rfl) henv) hlen
  | letHalt hexpr ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.letHalt (ihexpr (gfs_letVal hno rfl) henv)
  | assignVal hexpr hlen ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      rw [← setMany_gas_irrel]
      exact Step.assignVal (ihexpr (gfs_assign hno rfl) henv) hlen
  | assignHalt hexpr ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.assignHalt (ihexpr (gfs_assign hno rfl) henv)
  | exprStmt hexpr ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.exprStmt (ihexpr (gfs_exprStmt hno rfl) henv)
  | exprStmtHalt hexpr ihexpr =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.exprStmtHalt (ihexpr (gfs_exprStmt hno rfl) henv)
  | ifTrue hcond hne hbody ihcond ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hc, hb⟩ := gfs_cond hno rfl
      exact Step.ifTrue (ihcond hc henv) hne (ihbody (gfs_block_stmt hb) henv)
  | ifFalse hcond hne ihcond =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.ifFalse (ihcond (gfs_cond hno rfl).1 henv) hne
  | ifHalt hcond ihcond =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.ifHalt (ihcond (gfs_cond hno rfl).1 henv)
  | switchExec hcond hbody ihcond ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hc, hcs, hd⟩ := gfs_switch hno rfl
      have hbody' := ihbody (gfs_block_stmt (gfs_selectSwitch hcs hd)) henv
      rw [selectSwitch_irrel] at hbody'
      exact Step.switchExec (ihcond hc henv) hbody'
  | switchHalt hcond ihcond =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.switchHalt (ihcond (gfs_switch hno rfl).1 henv)
  | forLoop hinit hloop ihinit ihloop =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hi, hc, hp, hb⟩ := gfs_forLoop hno rfl
      have hloopNo := gfs_loop_of_forLoop hno rfl
      have h1 := ihinit hi (by
        intro sc hsc p hp'
        rcases List.mem_cons.mp hsc with rfl | hsc
        · exact gfs_hoist hi p hp'
        · exact henv sc hsc p hp')
      rw [cast_hoist_cons] at h1
      have h2 := ihloop hloopNo (by
        intro sc hsc p hp'
        rcases List.mem_cons.mp hsc with rfl | hsc
        · exact gfs_hoist hi p hp'
        · exact henv sc hsc p hp')
      rw [cast_hoist_cons] at h2
      exact Step.forLoop h1 h2
  | forInitHalt hinit ihinit =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨hi, _, _, _⟩ := gfs_forLoop hno rfl
      have h1 := ihinit hi (by
        intro sc hsc p hp'
        rcases List.mem_cons.mp hsc with rfl | hsc
        · exact gfs_hoist hi p hp'
        · exact henv sc hsc p hp')
      rw [cast_hoist_cons] at h1
      exact Step.forInitHalt h1
  | «break» =>
      intro _ _
      exact Step.break
  | «continue» =>
      intro _ _
      exact Step.continue
  | «leave» =>
      intro _ _
      exact Step.leave
  | seqNil =>
      intro _ _
      exact Step.seqNil
  | seqCons h1 h2 ih1 ih2 =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.seqCons (ih1 (gfs_stmt_head hno rfl) henv)
        (ih2 (gfs_stmt_tail hno rfl) henv)
  | seqStop h1 hne ih1 =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.seqStop (ih1 (gfs_stmt_head hno rfl) henv) hne
  | loopDone hcond heq ihcond =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.loopDone (ihcond (gfs_forLoop hno rfl).2.1 henv) heq
  | loopCondHalt hcond ihcond =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      exact Step.loopCondHalt (ihcond (gfs_forLoop hno rfl).2.1 henv)
  | loopStep hcond hne hbody hout hpost hloop ihcond ihbody ihpost ihloop =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨_, hc, hp, hb⟩ := gfs_forLoop hno rfl
      have hloopNo := gfs_loop_of_forLoop hno rfl
      exact Step.loopStep (ihcond hc henv) hne
        (ihbody (gfs_block_stmt hb) henv) hout
        (ihpost (gfs_block_stmt hp) henv) (ihloop hloopNo henv)
  | loopPostHalt hcond hne hbody hout hpost ihcond ihbody ihpost =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨_, hc, hp, hb⟩ := gfs_forLoop hno rfl
      exact Step.loopPostHalt (ihcond hc henv) hne
        (ihbody (gfs_block_stmt hb) henv) hout (ihpost (gfs_block_stmt hp) henv)
  | loopBreak hcond hne hbody ihcond ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨_, hc, _, hb⟩ := gfs_forLoop hno rfl
      exact Step.loopBreak (ihcond hc henv) hne
        (ihbody (gfs_block_stmt hb) henv)
  | loopLeave hcond hne hbody ihcond ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨_, hc, _, hb⟩ := gfs_forLoop hno rfl
      exact Step.loopLeave (ihcond hc henv) hne
        (ihbody (gfs_block_stmt hb) henv)
  | loopBodyHalt hcond hne hbody ihcond ihbody =>
      intro hno henv
      simp only [codeGasFree, resCast] at hno ⊢
      obtain ⟨_, hc, _, hb⟩ := gfs_forLoop hno rfl
      exact Step.loopBodyHalt (ihcond hc henv) hne
        (ihbody (gfs_block_stmt hb) henv)


/-- **LEAF (TOT.1): THE PROGRAM OF A VALID RENDER EXECUTES NO `gas()`.** PROVED by D-GATE1:
    `programOk` now carries `GasFree (R.prog 0 0)` as its fourth conjunct (the PG-GAS clause the
    evidence asked for), and `gasFree_prog_addr_indep` transfers it from `0 0` to every `vkAddr`
    through the ST.12 erasure identity. The two `example`s above are the scan's non-vacuity
    falsifier. -/
theorem gasFree_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (vkAddr : U256) :
    GasFree (R.prog vkAddr 0) :=
  gasFree_prog_addr_indep R vkAddr 0 hR.program.2.2.1

/-- **LEAF (TOT.1.a): A GAS-FREE PROGRAM HAS THE SAME RUNS UNDER EVERY GAS ORACLE.** PROVED
    (WP A12). The generic derivation transport is `step_gas_irrel` below: one induction on `Step`
    with the scan's `GasFreeScan` as the code hypothesis and `GasFreeEnv` for the function
    environment. The only oracle-reading constructors are `builtinOk`/`builtinHalt` at
    `Op.gas`, and `gasFreeScan` rejects that op; every other builtin's `builtinWithExternal` arm
    does not mention the oracle (`builtinWithExternal_gas_irrel`). The dialects' `Op`, `Value` and
    `State` agree definitionally, so the derivation is transported, not an equality of dialects:
    `fdeclCast`/`funEnvCast`/`resCast` rebuild the three indices that do depend on the full
    `Dialect` value, and `VEnv.setMany`/`bindZeros`/`VEnv.get` are the payload functions whose
    dialect argument needs the small oracle-independence lemmas. FALSIFIER: the two `decide`
    examples above - the scan refuses `pop(gas())` and accepts `pop(msize())`, so the hypothesis
    is not decorative; `mid_start_not_vacuous` (Stages.lean:672, PROVED) keeps the starting
    boundary non-trivial. CONE: 0, axioms standard three. -/
theorem runBody_gas_oblivious (R : Render p G₁ G₂ Gₜ) (vkAddr : U256)
    (hgas : GasFree (R.prog vkAddr 0)) (c : ExternalCalls) (g g' : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (h : RunBody R vkAddr 0 c g st₀ obs) :
    RunBody R vkAddr 0 c g' st₀ obs := by
  obtain ⟨V', st', hrun, hobs⟩ := h
  have hgasB : GasFreeScan (.b (R.prog vkAddr 0)) := hgas
  have hcode : codeGasFree (Code.stmt (.block (R.prog vkAddr 0))) := gfs_block_stmt hgasB
  have henv : GasFreeEnv ([] : FunEnv (Dialect c g)) := by
    intro sc hsc
    simp at hsc
  have hrun' := step_gas_irrel (g := g) (g' := g') hrun hcode henv
  exact ⟨V', st', by
    show Step (Dialect c g') [] [] st₀ (.stmt (.block (R.prog vkAddr 0)))
      (.sres V' st' obs.outcome)
    simpa [funEnvCast, resCast, eresultCast] using hrun', hobs⟩

/-! ## 2. Liveness: a run EXISTS and either continues at the next boundary or stops -/

section Live

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- A run that stops early is a run of any extension. PROVED (evidence `GeneratorRows.lean:1277`). -/
theorem stmts_append_stop {funs : FunEnv D} {a b : Block D.Op} :
    ∀ {V : VEnv D} {st : D.State} {V' : VEnv D} {st' : D.State} {o : Outcome},
      ExecStmts D funs V st a V' st' o → o ≠ .normal →
        ExecStmts D funs V st (a ++ b) V' st' o := by
  induction a with
  | nil =>
      intro V st V' st' o h hne
      cases h
      exact absurd rfl hne
  | cons s rest ih =>
      intro V st V' st' o h hne
      cases h with
      | seqCons hs hrest => exact Step.seqCons hs (ih hrest hne)
      | seqStop hs hne' => exact Step.seqStop hs hne'

/-- A run exists, and it ends normally at `mid` or stops. -/
def LiveTo (funs : FunEnv D) (b : Block D.Op) (pre mid : VEnv D → D.State → Prop) : Prop :=
  StmtsContract funs b pre (fun _ _ V' st' o => (o = .normal ∧ mid V' st') ∨ o ≠ .normal)

/-- Liveness composes. PROVED (evidence `GeneratorRows.lean:1297`), with the tree's
    `ExecStmts.append` in place of the evidence's `stmts_append_run`. -/
theorem live_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid mid' : VEnv D → D.State → Prop}
    (ha : LiveTo funs a pre mid) (hb : LiveTo funs b mid mid') :
    LiveTo funs (a ++ b) pre mid' := by
  intro V st hpre
  obtain ⟨V₁, st₁, o₁, h₁, hpost⟩ := ha V st hpre
  rcases hpost with ⟨ho, hmid⟩ | hne
  · subst ho
    obtain ⟨V', st', o, h₂, hpost₂⟩ := hb V₁ st₁ hmid
    exact ⟨V', st', o, ExecStmts.append h₁ h₂, hpost₂⟩
  · exact ⟨V₁, st₁, o₁, stmts_append_stop h₁ hne, Or.inr hne⟩

end Live

/-- The boundary a run can be at: clean up to `.quotient`, possibly poisoned from `.pcs` on.
    Ported verbatim (`GeneratorRows.lean:1316`). -/
def LivePre (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  match k with
  | .pcs | .pairing => Mid R H vkAddr cd k V st
  | _ => StageInv R H vkAddr cd k V st

/-- One block is live under the honest precompiles. -/
def BlockLive (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => LivePre R H vkAddr cd q.pre V st)
    (fun V st => LivePre R H vkAddr cd q.pre.next V st)

/-- `ERR_PROOF_REJECTED` is in every render's constant table. -/
theorem consts_errProof_of_validV3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.consts.lookup "ERR_PROOF_REJECTED" = some 0xc3b0d8cd :=
  Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR "ERR_PROOF_REJECTED" 0xc3b0d8cd (by
    cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
      cases h3 : R.model.expectedQuotientCodehash <;>
        cases h4 : R.model.expectedHasAccumulator <;>
          simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup])

/-- The `fail` helper body HAS a run from the callee environment, and it halts. The forward dual of
    `tr_fail_body`; the same construction `pfxRevertBody_exists` uses for the prefix's inline copy. -/
theorem fail_body_run {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (err : U256) (st : EvmState) :
    ∃ st', ExecStmts (Bridge.Dialect c g) funs
      ([("sel", err)] : VEnv (Bridge.Dialect c g)) st
      [Stmt.exprStmt (Expr.builtin Op.mstore
          [Expr.lit (.number 0),
           Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
       Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)])]
      [("sel", err)] st' .halt := by
  let shlE : Expr EVM.Op := Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]
  let stM : EvmState :=
    { touchMemory st 0 32 with memory := storeWord st.memory 0 (err <<< 224) }
  let stR : EvmState :=
    { touchMemory stM 0 4 with halted := some (.revert, readBytes stM.memory 0 4) }
  have hSel : EvalExpr (Bridge.Dialect c g) funs [("sel", err)] st (Expr.var "sel")
      (.vals [err] st) := Step.var rfl
  have hShl : EvalExpr (Bridge.Dialect c g) funs [("sel", err)] st shlE (.vals [err <<< 224] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [Expr.lit (.number 224), Expr.var "sel"])
      (argvals := [(224 : U256), err]) (st1 := st) (rets := [err <<< 224]) (st2 := st) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [Expr.var "sel"]) (restvals := [err])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := []) (Step.argsNil (D := Bridge.Dialect c g)) hSel)
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 224))
    · show (Bridge.Dialect c g).Builtin Op.shl [(224 : U256), err] st (.ok [err <<< 224] st)
      rfl
  have hMstore : Step (Bridge.Dialect c g) funs [("sel", err)] st
      (.expr (Expr.builtin Op.mstore [Expr.lit (.number 0), shlE])) (.eres (.vals [] stM)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [Expr.lit (.number 0), shlE])
      (argvals := [(0 : U256), err <<< 224]) (st1 := st) (rets := []) (st2 := stM) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [shlE]) (restvals := [err <<< 224])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g)) hShl)
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.mstore [(0 : U256), err <<< 224] st (.ok [] stM)
      rfl
  have hMstoreStmt : Step (Bridge.Dialect c g) funs [("sel", err)] st
      (.stmt (.exprStmt (Expr.builtin Op.mstore [Expr.lit (.number 0), shlE])))
      (.sres [("sel", err)] stM .normal) := Step.exprStmt hMstore
  have hRevert : Step (Bridge.Dialect c g) funs [("sel", err)] stM
      (.expr (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)]))
      (.eres (.halt stR)) := by
    refine Step.builtinHalt (D := Bridge.Dialect c g)
      (args := [Expr.lit (.number 0), Expr.lit (.number 4)])
      (argvals := [(0 : U256), (4 : U256)]) (st1 := stM) (st2 := stR) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [Expr.lit (.number 4)])
        (restvals := [(4 : U256)])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g))
          (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 4)))
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.revert [(0 : U256), (4 : U256)] stM (.halt stR)
      rfl
  have hRevertStmt : Step (Bridge.Dialect c g) funs [("sel", err)] stM
      (.stmt (.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)])))
      (.sres [("sel", err)] stR .halt) := Step.exprStmtHalt hRevert
  refine ⟨stR, ?_⟩
  show Step (Bridge.Dialect c g) funs [("sel", err)] st
      (.stmts [Stmt.exprStmt (Expr.builtin Op.mstore
          [Expr.lit (.number 0),
           Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
       Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)])])
      (.sres [("sel", err)] stR .halt)
  simp only [shlE, stM, stR] at hMstoreStmt hRevertStmt ⊢
  exact Step.seqCons hMstoreStmt (Step.seqStop hRevertStmt (by decide))

/-- The TraceReturn slice HAS a run from a poisoned boundary: the `iszero(success)` guard fires and
    the `fail` arm reverts. The existence dual of `tr_poison_walk_noarm`. -/
theorem tr_poison_exists {R : Render p G₁ G₂ Gₜ} (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    {V : VEnv (Blocks.TraceReturn.Dhonest product)} {st : EvmState}
    (hpois : Poisoned R H vkAddr cd V st) :
    ∃ V' st' o, ExecStmts (Blocks.TraceReturn.Dhonest product) (R.scope (callsOf product)
      (ExternalGas.ofFun fun _ => 0)) V st (R.slice Partial.traceReturn) V' st' o ∧ o ≠ .normal := by
  obtain ⟨-, hsucc0⟩ := hpois
  have herr : R.consts.lookup "ERR_PROOF_REJECTED" = some 0xc3b0d8cd :=
    consts_errProof_of_validV3 hR
  have herrE : Blocks.TraceReturn.trErrExpr R.consts = Expr.lit (.number 0xc3b0d8cd) := by
    simp [Blocks.TraceReturn.trErrExpr, herr]
  let body : Block EVM.Op :=
    [Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 0),
         Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
     Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 4)])]
  let decl : FDecl (Blocks.TraceReturn.Dhonest product) :=
    { params := ["sel"], rets := [], body := body }
  have hlookup : lookupFun (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) "fail" =
      some (decl, R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Blocks.TraceReturn.fail_lookup R
  obtain ⟨stR, hbody⟩ := fail_body_run (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
    (hoist (Blocks.TraceReturn.Dhonest product) body ::
      R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (BitVec.ofNat 256 0xc3b0d8cd) st
  have hvar : EvalExpr (Blocks.TraceReturn.Dhonest product) (R.scope _ _) V st
      (Expr.var "success") (.vals [(0 : U256)] st) := Step.var hsucc0
  have hz : EvalExpr (Blocks.TraceReturn.Dhonest product) (R.scope _ _) V st
      (Expr.builtin Op.iszero [Expr.var "success"]) (.vals [1] st) :=
    Step.builtinOk (D := Blocks.TraceReturn.Dhonest product)
      (Step.argsCons (D := Blocks.TraceReturn.Dhonest product) (rest := [])
        (Step.argsNil (D := Blocks.TraceReturn.Dhonest product)) hvar)
      (by simp [builtinWithExternal, stepOp, un, b2w])
  let e : Expr EVM.Op := Expr.lit (.number 0xc3b0d8cd)
  have harg : EvalExpr (Blocks.TraceReturn.Dhonest product)
      (([] : FScope (Blocks.TraceReturn.Dhonest product)) :: R.scope _ _) V st
      e (.vals [BitVec.ofNat 256 0xc3b0d8cd] st) := Step.lit
  have hlookup' : lookupFun (([] : FScope (Blocks.TraceReturn.Dhonest product)) :: R.scope _ _)
      "fail" = some (decl, R.scope _ _) := hlookup
  have hcall : Step (Blocks.TraceReturn.Dhonest product)
      (([] : FScope (Blocks.TraceReturn.Dhonest product)) :: R.scope _ _)
      V st (.expr (.call "fail" [e])) (.eres (.halt stR)) :=
    Step.callHalt (D := Blocks.TraceReturn.Dhonest product) (fn := "fail")
      (args := [e])
      (argvals := [BitVec.ofNat 256 0xc3b0d8cd]) (decl := decl)
      (cenv := R.scope _ _) (Vend := [("sel", BitVec.ofNat 256 0xc3b0d8cd)]) (st1 := st) (st2 := stR)
      (Step.argsCons (D := Blocks.TraceReturn.Dhonest product) (rest := [])
        (Step.argsNil (D := Blocks.TraceReturn.Dhonest product)) harg)
      hlookup' (by rfl)
      (Step.block (D := Blocks.TraceReturn.Dhonest product)
        (funs := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) (body := body) hbody)
  have hstmt : Step (Blocks.TraceReturn.Dhonest product)
      (([] : FScope (Blocks.TraceReturn.Dhonest product)) :: R.scope _ _) V st
      (.stmt (.exprStmt (.call "fail" [e])))
      (.sres V stR .halt) := Step.exprStmtHalt hcall
  have hbodyCond : ExecStmts (Blocks.TraceReturn.Dhonest product)
      (([] : FScope (Blocks.TraceReturn.Dhonest product)) :: R.scope _ _) V st
      [Stmt.exprStmt (.call "fail" [e])] V stR .halt :=
    Step.seqStop hstmt (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)
  have hcond : Step (Blocks.TraceReturn.Dhonest product) (R.scope _ _) V st
      (.stmt (.cond (Expr.builtin Op.iszero [Expr.var "success"])
        [Stmt.exprStmt (.call "fail" [e])]))
      (.sres (restore V V) stR .halt) :=
    Step.ifTrue (D := Blocks.TraceReturn.Dhonest product)
      (body := [Stmt.exprStmt (.call "fail" [e])])
      hz (by show (1 : U256) ≠ 0; decide)
      (Step.block (D := Blocks.TraceReturn.Dhonest product)
        (funs := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (body := [Stmt.exprStmt (.call "fail" [e])]) hbodyCond)
  rw [Blocks.TraceReturn.tr_slice R, herrE]
  refine ⟨restore V V, stR, .halt, ?_, by decide⟩
  exact Step.seqStop hcond (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)

/-- **THE TRACERETURN ARM OF `block_live`.** Existence only: `TraceReturn` halts on every run, so
    the `LiveTo` post is its second disjunct whatever the exhibited run is, and
    `tr_progress_ex` (clean) / `tr_poison_exists` (poisoned) supply the run. -/
theorem block_live_traceReturn (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .traceReturn H vkAddr product cd := by
  intro V st hpre
  have hpre' : Mid R H vkAddr cd Checkpoint.pairing V st := hpre
  rcases hpre' with hclean | hpois
  · obtain ⟨hframe, hsucc, -, hraw, -, hagree⟩ := hclean
    obtain ⟨ms, instW, inst, hdecd⟩ := hraw
    obtain ⟨S, -, hinv⟩ := hagree ms instW inst hdecd
    have hcl : Clean R Checkpoint.pairing S H vkAddr cd V st := ⟨hinv, hframe, hsucc⟩
    obtain ⟨V', st', o, hrun, hexit⟩ :=
      Blocks.TraceReturn.tr_progress_ex R product (returnMptr_of_valid hR) S H vkAddr cd hcl
    refine ⟨V', st', o, hrun, Or.inr ?_⟩
    rw [hexit.1]
    exact (by decide : (Outcome.halt : Outcome) ≠ Outcome.normal)
  · obtain ⟨V', st', o, hrun, hne⟩ := tr_poison_exists (R := R) product hR H vkAddr cd hpois
    exact ⟨V', st', o, hrun, Or.inr hne⟩

/-! ### 2a-bis. THE vkLoading ARM: existence of the thirteen-statement run

`block_live_vkLoading_of_exists` above spends the block's all-runs row; what remains is a run.
The three step lemmas below expose each assign's `success` word SYMBOLICALLY (`vk_step_hdr` /
`vk_step_cdl` / `vk_step_cdsz` are the matching instances), so the walk in `vk_run_exists` below
never has to decide a header word: it decides only the two guard bits it must branch on. -/

section VkLiveSteps

variable {c : ExternalCalls} {g : ExternalGas}

/-- The six VK-header cross-checks as a STEP at an ARBITRARY memory word: the assigned value is
    `succ &&& b2w (loadWord ... = n)`, left symbolic. `vk_step_hdr` is the `= n` instance. -/
theorem vk_hdr_step_any (R : Render p G₁ G₂ Gₜ) (slot : String) (i n : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {succExpr : Expr EVM.Op} {av : U256}
    (hsuccE : EvalExpr (Bridge.Dialect c g) funs V
      (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32) succExpr
      (.vals [av] (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)))
    (hlookup : R.consts.lookup slot =
      some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i)))
    (hfit : Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i) < 2 ^ 256) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.builtin Op.mload [Blocks.VkLoading.vkSite slot R.consts],
          Expr.lit (.number n)]]))
      (VEnv.set V "success" (av &&& b2w (loadWord st.memory
        (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) = BitVec.ofNat 256 n)))
      (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32) .normal := by
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st
      (Blocks.VkLoading.vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))] st) := by
    rw [show Blocks.VkLoading.vkSite slot R.consts =
      Expr.lit (.number (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))) from by
      simp [Blocks.VkLoading.vkSite, hlookup]]
    exact Step.lit
  have hmload : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mload [Blocks.VkLoading.vkSite slot R.consts])
      (.vals [loadWord st.memory
        (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat]
        (touchMemory st
          (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons Step.argsNil hsite)
      (by simp [builtinWithExternal, stepOp])
  have hfit' : (BitVec.ofNat 256
      (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat =
      ptrAddr (Ptr.add R.pv.memory.vkMptr i) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa [Midfall.LoweringV2.cAddr_eq_ptrAddr] using hfit)
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n))
      (.vals [BitVec.ofNat 256 n] st) := Step.lit
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.mload [Blocks.VkLoading.vkSite slot R.consts],
        Expr.lit (.number n)]) (.vals [b2w (loadWord st.memory (ptrAddr
          (Ptr.add R.pv.memory.vkMptr i)) = BitVec.ofNat 256 n)] (touchMemory st (BitVec.ofNat 256
            (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g)
        (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil hlit) hmload) ?_
    simp only [builtinWithExternal, stepOp, bin, hfit']
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.builtin Op.mload [Blocks.VkLoading.vkSite slot R.consts],
          Expr.lit (.number n)]])
      (.vals [av &&& b2w (loadWord st.memory (ptrAddr
          (Ptr.add R.pv.memory.vkMptr i)) = BitVec.ofNat 256 n)] (touchMemory st (BitVec.ofNat 256
            (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil heq)
        hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)

/-- The three calldata checks as a STEP at an arbitrary word: the assigned value is
    `succ &&& b2w (wordFrom ... = m)`, left symbolic. `vk_step_cdl` is the `= m` instance. -/
theorem vk_cdl_step_any (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {succExpr : Expr EVM.Op} {av : U256}
    (hsuccE : EvalExpr (Bridge.Dialect c g) funs V st succExpr (.vals [av] st))
    (hlookup : R.consts.lookup slot = some aVal) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.lit (.number m),
          Expr.builtin Op.calldataload [Blocks.VkLoading.vkSite slot R.consts]]]))
      (VEnv.set V "success" (av &&& b2w (BitVec.ofNat 256 m =
        wordFrom st.env.calldata (BitVec.ofNat 256 aVal).toNat))) st
      .normal := by
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st (Blocks.VkLoading.vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 aVal] st) := by
    rw [show Blocks.VkLoading.vkSite slot R.consts = Expr.lit (.number aVal) from by
      simp [Blocks.VkLoading.vkSite, hlookup]]
    exact Step.lit
  have hcdl : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.calldataload [Blocks.VkLoading.vkSite slot R.consts])
      (.vals [wordFrom st.env.calldata (BitVec.ofNat 256 aVal).toNat] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil hsite)
      (by simp [builtinWithExternal, stepOp, rd1])
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number m))
      (.vals [BitVec.ofNat 256 m] st) := Step.lit
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.lit (.number m),
        Expr.builtin Op.calldataload [Blocks.VkLoading.vkSite slot R.consts]])
      (.vals [b2w (BitVec.ofNat 256 m = wordFrom st.env.calldata
        (BitVec.ofNat 256 aVal).toNat)] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil hcdl)
        hlit) ?_
    simp only [builtinWithExternal, stepOp, bin]
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.lit (.number m),
          Expr.builtin Op.calldataload [Blocks.VkLoading.vkSite slot R.consts]]])
      (.vals [av &&& b2w (BitVec.ofNat 256 m = wordFrom st.env.calldata
        (BitVec.ofNat 256 aVal).toNat)] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil heq)
        hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)

/-- The calldatasize check as a STEP at an arbitrary length: `succ &&& b2w (size = aVal + m)`. -/
theorem vk_cdsz_step_any (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {succExpr : Expr EVM.Op} {av : U256}
    (hsuccE : EvalExpr (Bridge.Dialect c g) funs V st succExpr (.vals [av] st))
    (hlookup : R.consts.lookup slot = some aVal) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
          Expr.builtin Op.add [Blocks.VkLoading.vkSite slot R.consts, Expr.lit (.number m)]]]))
      (VEnv.set V "success" (av &&& b2w (BitVec.ofNat 256 st.env.calldata.length =
        BitVec.ofNat 256 aVal + BitVec.ofNat 256 m))) st .normal := by
  have hsize : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin Op.calldatasize [])
      (.vals [BitVec.ofNat 256 st.env.calldata.length] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) Step.argsNil
      (by simp [builtinWithExternal, stepOp, rd0])
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st (Blocks.VkLoading.vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 aVal] st) := by
    rw [show Blocks.VkLoading.vkSite slot R.consts = Expr.lit (.number aVal) from by
      simp [Blocks.VkLoading.vkSite, hlookup]]
    exact Step.lit
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number m))
      (.vals [BitVec.ofNat 256 m] st) := Step.lit
  have hadd : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [Blocks.VkLoading.vkSite slot R.consts, Expr.lit (.number m)])
      (.vals [BitVec.ofNat 256 aVal + BitVec.ofNat 256 m] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil hlit)
        hsite)
      (by simp [builtinWithExternal, stepOp, bin])
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
        Expr.builtin Op.add [Blocks.VkLoading.vkSite slot R.consts, Expr.lit (.number m)]])
      (.vals [b2w (BitVec.ofNat 256 st.env.calldata.length =
        BitVec.ofNat 256 aVal + BitVec.ofNat 256 m)] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil hadd)
        hsize) ?_
    simp only [builtinWithExternal, stepOp, bin]
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [succExpr,
        Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
          Expr.builtin Op.add [Blocks.VkLoading.vkSite slot R.consts, Expr.lit (.number m)]]])
      (.vals [av &&& b2w (BitVec.ofNat 256 st.env.calldata.length =
        BitVec.ofNat 256 aVal + BitVec.ofNat 256 m)] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil heq)
        hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)

/-- The `success` guard SKIPS at any nonzero value (the `= 1` instance is `vk_step_gate`). -/
theorem vk_gate_skip_any (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {s : U256} (hsucc : VEnv.get V "success" = some s) (hne : s ≠ 0) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Blocks.VkLoading.vkSucc])
        [Stmt.exprStmt (Expr.call "fail" [Blocks.VkLoading.vkSite err R.consts])]) V st .normal := by
  have hvar : EvalExpr (Bridge.Dialect c g) funs V st Blocks.VkLoading.vkSucc (.vals [s] st) :=
    Step.var hsucc
  have hb : b2w (s = 0) = 0 := by
    unfold b2w
    split
    · rename_i h
      exact absurd (of_decide_eq_true h) hne
    · rfl
  have hz : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Blocks.VkLoading.vkSucc]) (.vals [0] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil hvar)
      (by
        simp only [builtinWithExternal, stepOp, un, b2w, decide_eq_false hne]
        rfl)
  exact Step.ifFalse hz rfl

/-- The `success` guard FIRES at zero: the `fail` arm reverts. The existence dual of the guard
    inversion, at an arbitrary selector site. -/
theorem vk_gate_halts_any (R : Render p G₁ G₂ Gₜ) (sel : String) (err : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {cenv : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hsel : R.consts.lookup sel = some err)
    (hlookup : lookupFun funs "fail" = some (Blocks.TraceReturn.failFDecl, cenv))
    (hsucc0 : VEnv.get V "success" = some (0 : U256)) :
    ∃ V' st', ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Blocks.VkLoading.vkSucc])
        [Stmt.exprStmt (Expr.call "fail" [Blocks.VkLoading.vkSite sel R.consts])]) V' st' .halt := by
  let e : Expr EVM.Op := Expr.lit (.number err)
  have hsite : Blocks.VkLoading.vkSite sel R.consts = e := by
    simp [Blocks.VkLoading.vkSite, hsel, e]
  obtain ⟨stR, hbody⟩ := fail_body_run (c := c) (g := g)
    (([] : FScope (Bridge.Dialect c g)) :: cenv) (BitVec.ofNat 256 err) st
  have hvar : EvalExpr (Bridge.Dialect c g) funs V st Blocks.VkLoading.vkSucc (.vals [0] st) :=
    Step.var hsucc0
  have hz : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Blocks.VkLoading.vkSucc]) (.vals [1] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil hvar)
      (by simp [builtinWithExternal, stepOp, un, b2w])
  have harg : EvalExpr (Bridge.Dialect c g)
      (([] : FScope (Bridge.Dialect c g)) :: funs) V st e
      (.vals [BitVec.ofNat 256 err] st) := Step.lit
  have hlookup' : lookupFun (([] : FScope (Bridge.Dialect c g)) :: funs) "fail" =
      some (Blocks.TraceReturn.failFDecl, cenv) := hlookup
  have hbody' : ExecStmts (Bridge.Dialect c g) (([] : FScope (Bridge.Dialect c g)) :: cenv)
      ([("sel", BitVec.ofNat 256 err)] : VEnv (Bridge.Dialect c g)) st
      (Blocks.TraceReturn.failFDecl.body) [("sel", BitVec.ofNat 256 err)] stR .halt := hbody
  have hcall : Step (Bridge.Dialect c g) (([] : FScope (Bridge.Dialect c g)) :: funs) V st
      (.expr (.call "fail" [e])) (.eres (.halt stR)) := by
    refine Step.callHalt (D := Bridge.Dialect c g) (fn := "fail") (args := [e])
      (argvals := [BitVec.ofNat 256 err]) (decl := Blocks.TraceReturn.failFDecl)
      (cenv := cenv) (Vend := [("sel", BitVec.ofNat 256 err)]) (st1 := st) (st2 := stR)
      (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
        (Step.argsNil (D := Bridge.Dialect c g)) harg) hlookup' (by rfl) ?_
    exact Step.block (D := Bridge.Dialect c g) (funs := cenv)
      (body := Blocks.TraceReturn.failFDecl.body) hbody'
  have hstmt : Step (Bridge.Dialect c g) (([] : FScope (Bridge.Dialect c g)) :: funs) V st
      (.stmt (.exprStmt (.call "fail" [e]))) (.sres V stR .halt) :=
    Step.exprStmtHalt hcall
  have hbodyCond : ExecStmts (Bridge.Dialect c g) (([] : FScope (Bridge.Dialect c g)) :: funs) V st
      [Stmt.exprStmt (.call "fail" [e])] V stR .halt :=
    Step.seqStop hstmt (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)
  have hcond : Step (Bridge.Dialect c g) funs V st
      (.stmt (.cond (Expr.builtin Op.iszero [Blocks.VkLoading.vkSucc])
        [Stmt.exprStmt (.call "fail" [e])]))
      (.sres (restore V V) stR .halt) :=
    Step.ifTrue (D := Bridge.Dialect c g) (body := [Stmt.exprStmt (.call "fail" [e])])
      hz (by show (1 : U256) ≠ 0; decide)
      (Step.block (D := Bridge.Dialect c g) (funs := funs)
        (body := [Stmt.exprStmt (.call "fail" [e])]) hbodyCond)
  refine ⟨restore V V, stR, ?_⟩
  rw [← hsite] at hcond
  exact hcond

end VkLiveSteps

/-- **TOT.1.b's EXISTENCE HALF for vkLoading.** A run of the 13-statement slice from ANY
    `StageInv .start` boundary: S1's guard is silent (the frame pins the VK), the six header assigns
    step with symbolic bits, and the two guards (S9/S13) are branched on their ACTUAL bit, so no case
    analysis of the VK header words or the calldata is needed. The revert branches go through the
    `fail` helper (`vk_gate_halts_any` + `fail_body_run`). -/
theorem vk_run_exists (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    {V : VEnv (Blocks.TraceReturn.Dhonest product)} {st : EvmState}
    (hpre : StageInv R H vkAddr cd Checkpoint.start V st) :
    ∃ V' st' o, ExecStmts (Blocks.TraceReturn.Dhonest product)
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (R.slice Partial.vkLoading) V' st' o := by
  obtain ⟨hframe, hsucc, -, hraw, -, -⟩ := hpre
  have hcode : vkCodehashArm R.model :=
    (Midfall.LoweringV3.MemoryPairs.generated_model_facts hR.generated).2 hR.supported.separateVk
  obtain ⟨hVK, hPL, hP1, hP2, hP3⟩ := Midfall.LoweringV3.VkWindow.vkTableV3 hR hcode
  obtain ⟨hSN, hSK, hSA, hSO, hSL, hSB⟩ := Midfall.LoweringV3.VkClean.vkHeaderLookupsV3 hR
  have hEN : R.consts.lookup "ERR_VK_MISMATCH" = some 0xa447d73e :=
    Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR "ERR_VK_MISMATCH" 0xa447d73e (by
      cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
        cases h3 : R.model.expectedQuotientCodehash <;>
          cases h4 : R.model.expectedHasAccumulator <;>
            simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup])
  have hEC : R.consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some 0x1b99e37c :=
    Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR "ERR_BAD_CALLDATA_SHAPE" 0x1b99e37c (by
      cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
        cases h3 : R.model.expectedQuotientCodehash <;>
          cases h4 : R.model.expectedHasAccumulator <;>
            simp [Midfall.LoweringV3.expectedConsts, h1, h2, h3, h4, List.lookup])
  have hfail : lookupFun (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) "fail" =
      some (Blocks.TraceReturn.failFDecl,
        R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Blocks.TraceReturn.fail_lookup R
  let funs : FunEnv (Blocks.TraceReturn.Dhonest product) :=
    hoist (Blocks.TraceReturn.Dhonest product)
        (Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
          R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
          R.pv.proofLayout.proofLen) ::
      R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)
  have hfail' : lookupFun funs "fail" = some (Blocks.TraceReturn.failFDecl,
      R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Midfall.LoweringV3.VkRow.vkBody_fail_lookup R R.pv.numInstances R.pv.k
      R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
      R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen hfail
  let st2 : EvmState :=
    { touchMemory st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len with
      memory := copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
        (st.env.extCodeOf vkAddr) }
  let a3 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numInstances))).toNat
  let st3 : EvmState := touchMemory st2 a3 32
  let v3 : U256 := (1 : U256) &&& b2w (loadWord st2.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numInstances)) =
      BitVec.ofNat 256 R.pv.numInstances)
  let a4 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.k))).toNat
  let st4 : EvmState := touchMemory st3 a4 32
  let v4 : U256 := v3 &&& b2w (loadWord st3.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.k)) =
      BitVec.ofNat 256 R.pv.k)
  let a5 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.hasAccumulator))).toNat
  let st5 : EvmState := touchMemory st4 a5 32
  let v5 : U256 := v4 &&& b2w (loadWord st4.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.hasAccumulator)) =
      BitVec.ofNat 256 R.pv.expectedHasAccumulatorWord)
  let a6 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.accOffset))).toNat
  let st6 : EvmState := touchMemory st5 a6 32
  let v6 : U256 := v5 &&& b2w (loadWord st5.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.accOffset)) =
      BitVec.ofNat 256 R.pv.expectedAccOffset)
  let a7 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbs))).toNat
  let st7 : EvmState := touchMemory st6 a7 32
  let v7 : U256 := v6 &&& b2w (loadWord st6.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbs)) =
      BitVec.ofNat 256 R.pv.expectedNumAccLimbs)
  let a8 : Nat := (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbBits))).toNat
  let st8 : EvmState := touchMemory st7 a8 32
  let v8 : U256 := v7 &&& b2w (loadWord st7.memory
    (ptrAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbBits)) =
      BitVec.ofNat 256 R.pv.expectedNumAccLimbBits)
  let V3 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V "success" v3
  let V4 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V3 "success" v4
  let V5 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V4 "success" v5
  let V6 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V5 "success" v6
  let V7 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V6 "success" v7
  let V8 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V7 "success" v8
  have hs3 : VEnv.get V3 "success" = some v3 :=
    Blocks.VkLoading.vk_get_set_of_some hsucc
  have hs4 : VEnv.get V4 "success" = some v4 :=
    Blocks.VkLoading.vk_get_set_of_some hs3
  have hs5 : VEnv.get V5 "success" = some v5 :=
    Blocks.VkLoading.vk_get_set_of_some hs4
  have hs6 : VEnv.get V6 "success" = some v6 :=
    Blocks.VkLoading.vk_get_set_of_some hs5
  have hs7 : VEnv.get V7 "success" = some v7 :=
    Blocks.VkLoading.vk_get_set_of_some hs6
  have hs8 : VEnv.get V8 "success" = some v8 :=
    Blocks.VkLoading.vk_get_set_of_some hs7
  have h1 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V st
      (Blocks.VkLoading.vkS1 R.consts) V st .normal :=
    Midfall.LoweringV3.VkClean.vk_step_s1 (funs := funs) R hR hcode H vkAddr cd hframe
  have h2 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V st
      (Blocks.VkLoading.vkS2 R.consts) V st2 .normal :=
    Midfall.LoweringV3.VkClean.vk_step_s2 (funs := funs) (st := st) R hR vkAddr hframe.vk hVK hPL
  have h3 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V st2
      (Blocks.VkLoading.vkHdr "NUM_INSTANCES_MPTR" R.pv.numInstances R.consts
        (Blocks.VkLoading.vkSucc0 R.consts)) V3 st3 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V (touchMemory st2 a3 32)
        (Blocks.VkLoading.vkSucc0 R.consts) (.vals [1] (touchMemory st2 a3 32)) := by
      rw [Blocks.VkLoading.vkSucc0_var R]; exact Step.var hsucc
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "NUM_INSTANCES_MPTR" vkHeaderTemplateSlotsDefault.numInstances R.pv.numInstances
      (funs := funs) (V := V) (st := st2) (succExpr := Blocks.VkLoading.vkSucc0 R.consts)
      (av := 1) hsuccE hSN (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have h4 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V3 st3
      (Blocks.VkLoading.vkHdr "K_MPTR" R.pv.k R.consts Blocks.VkLoading.vkSucc)
      V4 st4 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V3 (touchMemory st3 a4 32)
        Blocks.VkLoading.vkSucc (.vals [v3] (touchMemory st3 a4 32)) := Step.var hs3
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "K_MPTR" vkHeaderTemplateSlotsDefault.k R.pv.k
      (funs := funs) (V := V3) (st := st3) (succExpr := Blocks.VkLoading.vkSucc) (av := v3)
      hsuccE hSK (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have h5 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V4 st4
      (Blocks.VkLoading.vkHdr "HAS_ACCUMULATOR_MPTR" R.pv.expectedHasAccumulatorWord R.consts
        Blocks.VkLoading.vkSucc) V5 st5 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V4 (touchMemory st4 a5 32)
        Blocks.VkLoading.vkSucc (.vals [v4] (touchMemory st4 a5 32)) := Step.var hs4
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "HAS_ACCUMULATOR_MPTR" vkHeaderTemplateSlotsDefault.hasAccumulator
      R.pv.expectedHasAccumulatorWord
      (funs := funs) (V := V4) (st := st4) (succExpr := Blocks.VkLoading.vkSucc) (av := v4)
      hsuccE hSA (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have h6 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V5 st5
      (Blocks.VkLoading.vkHdr "ACC_OFFSET_MPTR" R.pv.expectedAccOffset R.consts
        Blocks.VkLoading.vkSucc) V6 st6 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V5 (touchMemory st5 a6 32)
        Blocks.VkLoading.vkSucc (.vals [v5] (touchMemory st5 a6 32)) := Step.var hs5
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "ACC_OFFSET_MPTR" vkHeaderTemplateSlotsDefault.accOffset R.pv.expectedAccOffset
      (funs := funs) (V := V5) (st := st5) (succExpr := Blocks.VkLoading.vkSucc) (av := v5)
      hsuccE hSO (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have h7 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V6 st6
      (Blocks.VkLoading.vkHdr "NUM_ACC_LIMBS_MPTR" R.pv.expectedNumAccLimbs R.consts
        Blocks.VkLoading.vkSucc) V7 st7 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V6 (touchMemory st6 a7 32)
        Blocks.VkLoading.vkSucc (.vals [v6] (touchMemory st6 a7 32)) := Step.var hs6
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "NUM_ACC_LIMBS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbs R.pv.expectedNumAccLimbs
      (funs := funs) (V := V6) (st := st6) (succExpr := Blocks.VkLoading.vkSucc) (av := v6)
      hsuccE hSL (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have h8 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V7 st7
      (Blocks.VkLoading.vkHdr "NUM_ACC_LIMB_BITS_MPTR" R.pv.expectedNumAccLimbBits R.consts
        Blocks.VkLoading.vkSucc) V8 st8 .normal := by
    have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V7 (touchMemory st7 a8 32)
        Blocks.VkLoading.vkSucc (.vals [v7] (touchMemory st7 a8 32)) := Step.var hs7
    exact vk_hdr_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
      "NUM_ACC_LIMB_BITS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbBits
      R.pv.expectedNumAccLimbBits
      (funs := funs) (V := V7) (st := st7) (succExpr := Blocks.VkLoading.vkSucc) (av := v7)
      hsuccE hSB (Midfall.LoweringV3.VkClean.vk_hdr_addr_fit R hR _ (by decide))
  have hpre8 : ExecStmts (Blocks.TraceReturn.Dhonest product) funs V st
      [Blocks.VkLoading.vkS1 R.consts, Blocks.VkLoading.vkS2 R.consts,
       Blocks.VkLoading.vkHdr "NUM_INSTANCES_MPTR" R.pv.numInstances R.consts
         (Blocks.VkLoading.vkSucc0 R.consts),
       Blocks.VkLoading.vkHdr "K_MPTR" R.pv.k R.consts Blocks.VkLoading.vkSucc,
       Blocks.VkLoading.vkHdr "HAS_ACCUMULATOR_MPTR" R.pv.expectedHasAccumulatorWord R.consts
         Blocks.VkLoading.vkSucc,
       Blocks.VkLoading.vkHdr "ACC_OFFSET_MPTR" R.pv.expectedAccOffset R.consts
         Blocks.VkLoading.vkSucc,
       Blocks.VkLoading.vkHdr "NUM_ACC_LIMBS_MPTR" R.pv.expectedNumAccLimbs R.consts
         Blocks.VkLoading.vkSucc,
       Blocks.VkLoading.vkHdr "NUM_ACC_LIMB_BITS_MPTR" R.pv.expectedNumAccLimbBits R.consts
         Blocks.VkLoading.vkSucc] V8 st8 .normal :=
    Step.seqCons h1 (Step.seqCons h2 (Step.seqCons h3 (Step.seqCons h4
      (Step.seqCons h5 (Step.seqCons h6 (Step.seqCons h7 (Step.seqCons h8 Step.seqNil)))))))
  by_cases hz8 : v8 = 0
  · have hsucc0 : VEnv.get V8 "success" = some (0 : U256) := by rw [hs8, hz8]
    obtain ⟨V9, st9, h9⟩ := vk_gate_halts_any (c := callsOf product)
      (g := ExternalGas.ofFun fun _ => 0) R "ERR_VK_MISMATCH" 0xa447d73e
      (funs := funs) (cenv := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
      hEN hfail' hsucc0
    have hbody : ExecStmts (Blocks.TraceReturn.Dhonest product) funs V st
        (Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
          R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
          R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) V9 st9 .halt :=
      ExecStmts.append hpre8
        (Step.seqStop h9 (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide))
    refine ⟨restore V V9, st9, .halt, ?_⟩
    rw [Midfall.LoweringV3.VkRow.vk_sliceV3 R hR]
    exact Step.seqStop (Step.block (D := Blocks.TraceReturn.Dhonest product) (funs := R.scope _ _)
      (body := Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
        R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
        R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) hbody)
      (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)
  · have h9 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V8 st8
        (Blocks.VkLoading.vkS9 R.consts) V8 st8 .normal :=
      vk_gate_skip_any R "ERR_VK_MISMATCH" (funs := funs) hs8 hz8
    let v10 : U256 := v8 &&& b2w (BitVec.ofNat 256 R.pv.proofLayout.proofLen =
      wordFrom st8.env.calldata ((BitVec.ofNat 256 (R.pv.proofLayout.proofCptr - 32)).toNat))
    let V10 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V8 "success" v10
    have hs10 : VEnv.get V10 "success" = some v10 :=
      Blocks.VkLoading.vk_get_set_of_some (x := "success") (v := v8) (w := v10) hs8
    have h10 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V8 st8
        (Blocks.VkLoading.vkS10 R.consts R.pv.proofLayout.proofLen) V10 st8 .normal := by
      have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V8 st8
          Blocks.VkLoading.vkSucc (.vals [v8] st8) := Step.var hs8
      exact vk_cdl_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
        "PROOF_LEN_CPTR" (R.pv.proofLayout.proofCptr - 32) R.pv.proofLayout.proofLen
        (funs := funs) (V := V8) (st := st8)
        (succExpr := Blocks.VkLoading.vkSucc) (av := v8) hsuccE hP1
    let v11 : U256 := v10 &&& b2w (BitVec.ofNat 256 R.pv.numInstances =
      wordFrom st8.env.calldata ((BitVec.ofNat 256 R.pv.proofLayout.proofEnd).toNat))
    let V11 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V10 "success" v11
    have hs11 : VEnv.get V11 "success" = some v11 :=
      Blocks.VkLoading.vk_get_set_of_some (x := "success") (v := v10) (w := v11) hs10
    have h11 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V10 st8
        (Blocks.VkLoading.vkS11 R.consts R.pv.numInstances) V11 st8 .normal := by
      have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V10 st8
          Blocks.VkLoading.vkSucc (.vals [v10] st8) := Step.var hs10
      exact vk_cdl_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
        "NUM_INSTANCE_CPTR" R.pv.proofLayout.proofEnd R.pv.numInstances
        (funs := funs) (V := V10) (st := st8)
        (succExpr := Blocks.VkLoading.vkSucc) (av := v10) hsuccE hP2
    let v12 : U256 := v11 &&& b2w (BitVec.ofNat 256 st8.env.calldata.length =
      BitVec.ofNat 256 (R.pv.proofLayout.proofEnd + 32) + BitVec.ofNat 256 (R.pv.numInstances * 32))
    let V12 : VEnv (Blocks.TraceReturn.Dhonest product) := VEnv.set V11 "success" v12
    have h12 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V11 st8
        (Blocks.VkLoading.vkS12 R.consts R.pv.numInstances) V12 st8 .normal := by
      have hsuccE : EvalExpr (Blocks.TraceReturn.Dhonest product) funs V11 st8
          Blocks.VkLoading.vkSucc (.vals [v11] st8) := Step.var hs11
      exact vk_cdsz_step_any (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0) R
        "INSTANCE_CPTR" (R.pv.proofLayout.proofEnd + 32) (R.pv.numInstances * 32)
        (funs := funs) (V := V11) (st := st8)
        (succExpr := Blocks.VkLoading.vkSucc) (av := v11) hsuccE hP3
    have hs12 : VEnv.get V12 "success" = some v12 :=
      Blocks.VkLoading.vk_get_set_of_some (x := "success") (v := v11) (w := v12) hs11
    by_cases hz12 : v12 = 0
    · have hsucc0 : VEnv.get V12 "success" = some (0 : U256) := by rw [hs12, hz12]
      obtain ⟨V13, st13, h13⟩ := vk_gate_halts_any (c := callsOf product)
        (g := ExternalGas.ofFun fun _ => 0) R "ERR_BAD_CALLDATA_SHAPE" 0x1b99e37c
        (funs := funs) (cenv := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
        hEC hfail' hsucc0
      have hbody : ExecStmts (Blocks.TraceReturn.Dhonest product) funs V st
          (Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
            R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
            R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) V13 st13 .halt :=
        ExecStmts.append hpre8 (Step.seqCons h9 (Step.seqCons h10 (Step.seqCons h11
          (Step.seqCons h12 (Step.seqStop h13
            (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide))))))
      refine ⟨restore V V13, st13, .halt, ?_⟩
      rw [Midfall.LoweringV3.VkRow.vk_sliceV3 R hR]
      exact Step.seqStop (Step.block (D := Blocks.TraceReturn.Dhonest product) (funs := R.scope _ _)
        (body := Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
          R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
          R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) hbody)
        (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)
    · have h13 : ExecStmt (Blocks.TraceReturn.Dhonest product) funs V12 st8
          (Blocks.VkLoading.vkS13 R.consts) V12 st8 .normal :=
        vk_gate_skip_any R "ERR_BAD_CALLDATA_SHAPE" (funs := funs) hs12 hz12
      have hbody : ExecStmts (Blocks.TraceReturn.Dhonest product) funs V st
          (Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
            R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
            R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) V12 st8 .normal :=
        ExecStmts.append hpre8 (Step.seqCons h9 (Step.seqCons h10 (Step.seqCons h11
          (Step.seqCons h12 (Step.seqCons h13 Step.seqNil)))))
      refine ⟨restore V V12, st8, .normal, ?_⟩
      rw [Midfall.LoweringV3.VkRow.vk_sliceV3 R hR]
      exact Step.seqCons (Step.block (D := Blocks.TraceReturn.Dhonest product)
        (funs := R.scope _ _) (body := Blocks.VkLoading.vkBody R.consts R.pv.numInstances R.pv.k
          R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
          R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen) hbody) Step.seqNil


section LoopExists
variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- **THE EXISTENCE FORM OF THE LOOP RULE (GEN.3's other half), for a `for` statement.** A `for`
    statement with a countdown invariant HAS a normal run: `ExecLoop.countdown` builds the loop
    derivation from `done`/`step`, and `Step.forLoop` wraps the init run around it. The all-runs
    form is `LoopRule.allRuns_for_cons_wp` / `ExecLoopAll.countdown_or_halt`; neither exhibits a
    run, which is exactly what a `LiveTo` needs. Each per-loop existence leaf of TOT.1 is an
    instance of this theorem at the loop's own invariant. -/
theorem forLoop_exists_of_countdown {funs : FunEnv D} {V : VEnv D} {st : D.State}
    {init : Block D.Op} {cond : Expr D.Op} {post body : Block D.Op}
    {Inv : Nat → VEnv D → D.State → Prop} {V0 : VEnv D} {st0 : D.State}
    (hinit : ExecStmts D (hoist D init :: funs) V st init V0 st0 .normal)
    (done : ∀ V st, Inv 0 V st → ∃ cv st',
      EvalExpr D (hoist D init :: funs) V st cond (.vals [cv] st') ∧ cv = D.zero ∧ Inv 0 V st')
    (step : ∀ n V st, Inv (n + 1) V st → ∃ cv stc Vb stb ob Vp stp,
      EvalExpr D (hoist D init :: funs) V st cond (.vals [cv] stc) ∧ cv ≠ D.zero ∧
      ExecStmt D (hoist D init :: funs) V stc (.block body) Vb stb ob ∧
      (ob = .normal ∨ ob = .«continue») ∧
      ExecStmt D (hoist D init :: funs) Vb stb (.block post) Vp stp .normal ∧ Inv n Vp stp)
    (n : Nat) (hInv : Inv n V0 st0) :
    ∃ V' st', ExecStmt D funs V st (Stmt.forLoop init cond post body) V' st' .normal := by
  obtain ⟨Vl, stl, hloop, -⟩ :=
    ExecLoop.countdown (D := D) (funs := hoist D init :: funs) done step n V0 st0 hInv
  exact ⟨restore V Vl, stl, Step.forLoop hinit hloop⟩

/-- The one-statement-list face of `forLoop_exists_of_countdown` (the shape a slice segment has). -/
theorem forLoop_stmts_exists_of_countdown {funs : FunEnv D} {V : VEnv D} {st : D.State}
    {init : Block D.Op} {cond : Expr D.Op} {post body : Block D.Op}
    {Inv : Nat → VEnv D → D.State → Prop} {V0 : VEnv D} {st0 : D.State}
    (hinit : ExecStmts D (hoist D init :: funs) V st init V0 st0 .normal)
    (done : ∀ V st, Inv 0 V st → ∃ cv st',
      EvalExpr D (hoist D init :: funs) V st cond (.vals [cv] st') ∧ cv = D.zero ∧ Inv 0 V st')
    (step : ∀ n V st, Inv (n + 1) V st → ∃ cv stc Vb stb ob Vp stp,
      EvalExpr D (hoist D init :: funs) V st cond (.vals [cv] stc) ∧ cv ≠ D.zero ∧
      ExecStmt D (hoist D init :: funs) V stc (.block body) Vb stb ob ∧
      (ob = .normal ∨ ob = .«continue») ∧
      ExecStmt D (hoist D init :: funs) Vb stb (.block post) Vp stp .normal ∧ Inv n Vp stp)
    (n : Nat) (hInv : Inv n V0 st0) :
    ∃ V' st', ExecStmts D funs V st [Stmt.forLoop init cond post body] V' st' .normal := by
  obtain ⟨V', st', h⟩ :=
    forLoop_exists_of_countdown hinit done step n hInv
  exact ⟨V', st', Step.seqCons h Step.seqNil⟩

end LoopExists

/-- **THE TOT.1 DECOMPOSITION, NAMED.** A `LiveTo` is exactly an existence statement plus a
    classification of the exhibited run: the existential is `StmtsContract`'s first field, the
    disjunction is its postcondition. This is the shape every block case takes (the plan's "the
    existence form of the loop rule at each loop, and the block's all-runs row to classify the
    exhibited run"). -/
theorem liveTo_of_exists {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {b : Block D.Op} {pre mid : VEnv D → D.State → Prop}
    (hex : ∀ V st, pre V st → ∃ V' st' o, ExecStmts D funs V st b V' st' o)
    (hcls : ∀ V st, pre V st → ∀ V' st' o, ExecStmts D funs V st b V' st' o →
      (o = .normal ∧ mid V' st') ∨ o ≠ .normal) :
    LiveTo funs b pre mid := by
  intro V st hpre
  obtain ⟨V', st', o, hrun⟩ := hex V st hpre
  exact ⟨V', st', o, hrun, hcls V st hpre V' st' o hrun⟩

/-- **THE vkLoading CASE OF `block_live`, REDUCED TO EXISTENCE.** `VkClean.vk_clean_walkV3` is the
    block's all-runs row at the HONEST dialect and it needs no accepted calldata: every run of the
    slice from `StageInv .start` is a halted revert or a normal exit at `StageInv .vk`. So the
    block's `LiveTo` follows from the existence half alone - TOT.1.b's residual obligation is
    `hex` and nothing else. (The existence proof itself must reproduce the 13-statement walk with
    the nine guards case-split; it is not in this commit.) -/
theorem block_live_vkLoading_of_exists (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hex : ∀ V st, StageInv R H vkAddr cd Checkpoint.start V st →
      ∃ V' st' o, ExecStmts (Blocks.TraceReturn.Dhonest product)
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (R.slice Partial.vkLoading) V' st' o) :
    BlockLive R .vkLoading H vkAddr product cd := by
  refine liveTo_of_exists hex ?_
  intro V st hpre V' st' o hrun
  rcases VkClean.vk_clean_walkV3 R hR H vkAddr cd (ExternalGas.ofFun fun _ => 0)
    V st hpre V' st' o hrun with hrev | hok
  · exact Or.inr (by rw [hrev.1]; decide)
  · exact Or.inl hok

/-- The finalPairing slice at `ValidV3`, below `block_live` in the import order (`Rows.fp_sliceV3`
    is above `Totality`). Same proof as that one; the emitter is no-accumulator at `ValidV3`. -/
theorem fp_slice_at (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.slice Partial.finalPairing =
      [Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail"
            [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])],
        Stmt.assign ["success"] (Expr.call "ec_pairing"
          [Expr.var "success",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"])] := by
  have hacc : R.pv.hasAccumulator = false := by
    classical
    have h : R.cfg.accumulator = none := hR.supported.noAcc
    have h1 : R.pv = planViewOf R.plan R.model none := by
      show planViewOf R.plan R.model R.cfg.accumulator = _
      rw [h]
    rw [h1, planViewOf, planViewWithAccumulator]
    rfl
  show Inline.inlineContractConstants R.consts
    (Midfall.Lowering.GenAst.emitPartial R.pv Partial.finalPairing) = _
  rw [Midfall.Lowering.GenAst.emitPartial, Midfall.Lowering.GenAst.emitFinalPairing, hacc]
  rw [Midfall.LoweringV2.Blocks.FinalPairing.fp_slice_raw]
  simp only [Midfall.LoweringV2.Blocks.FinalPairing.fpVal,
    Midfall.LoweringV2.Blocks.TraceReturn.consts_succ_none]

/-- The finalPairing slice from a POISONED boundary: the `iszero(success)` guard fires, so a run
    exists and halts. Half of TOT.1.g; the clean boundary is the other half. -/
theorem block_live_finalPairing_poison (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    ∀ V st, Poisoned R H vkAddr cd V st →
      ∃ V' st' o, ExecStmts (Blocks.TraceReturn.Dhonest product)
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (R.slice Partial.finalPairing) V' st' o ∧
        ((o = .normal ∧ Mid R H vkAddr cd Checkpoint.pairing V' st') ∨ o ≠ .normal) := by
  intro V st hpois
  obtain ⟨-, hsucc0⟩ := hpois
  have hsel := consts_lookup_ERR_PRECOMPILE_FAILED R hR
  have hfail : lookupFun (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) "fail" =
      some (Blocks.TraceReturn.failFDecl,
        R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Blocks.TraceReturn.fail_lookup (c := callsOf product)
      (g := ExternalGas.ofFun fun _ => 0) R
  obtain ⟨V', st', hguard⟩ := vk_gate_halts_any (c := callsOf product)
    (g := ExternalGas.ofFun fun _ => 0) R "ERR_PRECOMPILE_FAILED" 0x84e81692
    (funs := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (cenv := R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) hsel hfail hsucc0
  refine ⟨V', st', .halt, ?_, Or.inr (by decide)⟩
  rw [fp_slice_at R hR]
  exact Step.seqStop hguard (by show (Outcome.halt : Outcome) ≠ Outcome.normal; decide)

/-- **TOT.1.b CLOSED: vkLoading is live.** The existence half is `vk_run_exists`; the classification
    is `block_live_vkLoading_of_exists`'s `vk_clean_walkV3`. Standard three, cone 0. -/
theorem block_live_vkLoading (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .vkLoading H vkAddr product cd :=
  block_live_vkLoading_of_exists R product hR H vkAddr cd
    (fun V st hpre => vk_run_exists R product hR H vkAddr cd hpre)

theorem memoryLifetimeIntersects_perm_left (l : MemoryLifetime) :
    memoryLifetimeIntersects MemoryLifetime.permanent l = true := by
  cases l <;> rfl

theorem memoryLifetimeIntersects_perm_right (l : MemoryLifetime) :
    memoryLifetimeIntersects l MemoryLifetime.permanent = true := by
  cases l <;> rfl

theorem memoryRegionsPairwiseDisjoint_perm_any
    {regions : List MemoryRegion} {lhs rhs : MemoryRegion}
    (h : memoryRegionsPairwiseDisjoint regions = true)
    (hl : regions.find? (fun r => r.name == lhs.name) = some lhs)
    (hr : regions.find? (fun r => r.name == rhs.name) = some rhs)
    (hne : lhs.name ≠ rhs.name)
    (hpl : lhs.lifetime = MemoryLifetime.permanent) :
    lhs.overlaps rhs = false := by
  induction regions with
  | nil => cases hl
  | cons x rest ih =>
      have h1 := h
      simp only [memoryRegionsPairwiseDisjoint, Bool.and_eq_true] at h1
      obtain ⟨hall, hrest⟩ := h1
      rw [List.all_eq_true] at hall
      cases hx : x.name == lhs.name with
      | true =>
        simp only [List.find?, hx] at hl
        have hlhs : x = lhs := Option.some.inj hl
        cases hx2 : x.name == rhs.name with
        | true =>
          exact (hne ((congrArg MemoryRegion.name hlhs).symm.trans
            ((beq_iff_eq (a := x.name) (b := rhs.name)).mp hx2))).elim
        | false =>
          simp only [List.find?, hx2] at hr
          have hthis := hall rhs (MemoryPairs.mem_find hr)
          rw [hlhs] at hthis
          rw [hpl, memoryLifetimeIntersects_perm_left rhs.lifetime] at hthis
          simpa using hthis
      | false =>
        simp only [List.find?, hx] at hl
        cases hx2 : x.name == rhs.name with
        | true =>
          simp only [List.find?, hx2] at hr
          have hxr : x = rhs := Option.some.inj hr
          have hthis := hall lhs (MemoryPairs.mem_find hl)
          rw [hxr] at hthis
          rw [hpl, memoryLifetimeIntersects_perm_right rhs.lifetime] at hthis
          have hs : rhs.overlaps lhs = false := by simpa using hthis
          rw [MemoryPairs.overlaps_symm lhs rhs]
          exact hs
        | false =>
          simp only [List.find?, hx2] at hr
          exact ih hrest hl hr

theorem wellFormed_pair_disjoint_of_perm {map : MemoryMap} {lhs rhs : MemoryRegion}
    (h : map.WellFormed)
    (hl : map.region lhs.name = some lhs)
    (hr : map.region rhs.name = some rhs)
    (hne : lhs.name ≠ rhs.name)
    (hpl : lhs.lifetime = MemoryLifetime.permanent) :
    lhs.overlaps rhs = false :=
  memoryRegionsPairwiseDisjoint_perm_any (MemoryPairs.wellFormed_regions_disjoint h) hl hr hne hpl

/-- **PG-FPSCRATCH: THE INVARIANT THE FINALPAIRING CLEAN ARM NEEDS.** The `ec_pairing` helper's
    four `mcopy`s write `pairingStaticWorkingWords * wordBytes` bytes (768 of them at the default
    template) at `finalPairingScratchMptr`. `Inv`'s memory clauses read (i) the theta window - the
    root of every theta slot, `g1_identity`, `q_eval_cptr`, the commitment run and the selector
    accumulators, at non-negative word offsets from it - and (ii) the vk payload. This says those
    two windows are separated from the scratch window; a `loadWord`/`bytesAt` transport across the
    write needs exactly this, plus the read-window containment of each clause. -/
def FpScratchSeparated (pv : PlanView) : Prop :=
  (ptrAddr pv.memory.thetaMptr +
        ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes ≤
      pv.memory.finalPairingScratchMptr ∨
    pv.memory.finalPairingScratchMptr +
        Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes ≤
      ptrAddr pv.memory.thetaMptr) ∧
  (pv.vk.len = 0 ∨
    ptrAddr pv.memory.vkMptr + pv.vk.len ≤ pv.memory.finalPairingScratchMptr ∨
    pv.memory.finalPairingScratchMptr +
        Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes ≤
      ptrAddr pv.memory.vkMptr)

/-- **THE THETA HALF OF THE REDUCTION.** `theta_scalar_and_g1_slots` is `permanent` and
    `final_pairing_scratch` is a phase, so a permanent lifetime intersects the other and
    `WellFormed`'s pairwise predicate orders the two windows. This is the content a generator-side
    region lemma has to instantiate. -/
theorem fpScratchThetaSeparated_of_map {map : MemoryMap} {thetaStart fpStart : Nat}
    (hWF : map.WellFormed)
    (hth : map.region "theta_scalar_and_g1_slots" =
      some (memoryRegionNew "theta_scalar_and_g1_slots" thetaStart
        (ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes)
        MemoryLifetime.permanent))
    (hfp : map.region "final_pairing_scratch" =
      some (memoryRegionNew "final_pairing_scratch" fpStart
        (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
        (MemoryLifetime.phase MemoryPhase.finalPairing))) :
    thetaStart + ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes ≤ fpStart ∨
      fpStart + Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes ≤
        thetaStart := by
  have hne : ("theta_scalar_and_g1_slots" : String) ≠ "final_pairing_scratch" := by decide
  have hd := wellFormed_pair_disjoint_of_perm (map := map)
    (lhs := memoryRegionNew "theta_scalar_and_g1_slots" thetaStart
      (ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes)
      MemoryLifetime.permanent)
    (rhs := memoryRegionNew "final_pairing_scratch" fpStart
      (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
      (MemoryLifetime.phase MemoryPhase.finalPairing)) hWF hth hfp hne (by rfl)
  have hthLen : (memoryRegionNew "theta_scalar_and_g1_slots" thetaStart
      (ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes)
      MemoryLifetime.permanent).len ≠ 0 := by
    simp only [memoryRegionNew]
    decide
  have hfpLen : (memoryRegionNew "final_pairing_scratch" fpStart
      (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
      (MemoryLifetime.phase MemoryPhase.finalPairing)).len ≠ 0 := by
    simp only [memoryRegionNew]
    decide
  have hsep := MemoryPairs.not_overlaps_sep hd hthLen hfpLen
  simpa only [memoryRegionNew] using hsep

/-- **THE VK HALF OF THE REDUCTION.** Same mechanism; the empty-payload case is carried explicitly
    because `MemoryRegion.overlaps` exempts zero-length regions, so an empty vk window is trivially
    separated and `not_overlaps_sep` does not apply. -/
theorem fpScratchVkSeparated_of_map {map : MemoryMap} {fpStart vkStart vkLen : Nat}
    (hWF : map.WellFormed)
    (hfp : map.region "final_pairing_scratch" =
      some (memoryRegionNew "final_pairing_scratch" fpStart
        (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
        (MemoryLifetime.phase MemoryPhase.finalPairing)))
    (hvk : map.region "vk_payload" =
      some (memoryRegionNew "vk_payload" vkStart vkLen MemoryLifetime.permanent)) :
    vkLen = 0 ∨ vkStart + vkLen ≤ fpStart ∨
      fpStart + Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes ≤
        vkStart := by
  by_cases hv : vkLen = 0
  · exact Or.inl hv
  · have hne : ("vk_payload" : String) ≠ "final_pairing_scratch" := by decide
    have hd := wellFormed_pair_disjoint_of_perm (map := map)
      (lhs := memoryRegionNew "vk_payload" vkStart vkLen MemoryLifetime.permanent)
      (rhs := memoryRegionNew "final_pairing_scratch" fpStart
        (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
        (MemoryLifetime.phase MemoryPhase.finalPairing)) hWF hvk hfp hne (by rfl)
    have hvLen : (memoryRegionNew "vk_payload" vkStart vkLen
        MemoryLifetime.permanent).len ≠ 0 := by simpa only [memoryRegionNew] using hv
    have hfpLen : (memoryRegionNew "final_pairing_scratch" fpStart
        (Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes)
        (MemoryLifetime.phase MemoryPhase.finalPairing)).len ≠ 0 := by
      simp only [memoryRegionNew]
      decide
    have hsep := MemoryPairs.not_overlaps_sep hd hvLen hfpLen
    refine Or.inr ?_
    simpa only [memoryRegionNew] using hsep

/-- The registered scratch region is at least the 768 bytes the four `mcopy`s write, so separation
    from the region is separation from the write. -/
theorem fpScratch_write_le_region :
    Midfall.Generator.finalPairingScratchStart + 768 ≤
      Midfall.Generator.finalPairingScratchStart +
        Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes := by
  decide

/-! ### 3. THE WITNESSES: WHAT `validate` CATCHES, AND WHAT THE PHASE RULE ACCEPTS -/

/-- A payload with no constants and no commitments: the smallest `vk.len` the type allows. Used by
    the near-miss below; it is not claimed to be a `ValidV3` payload. -/
def emptyVkForScratch : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0, constants := [], fixedComms := [], permutationComms := [],
    quotientConstOffsetWords := none, quotientConstWords := 0,
    quotientProgramOffsetWords := none, quotientProgramWords := 0,
    quotientConstLabels := [], quotientConstHeaders := [] }

/-- **THE NEAR-MISS PLAN.** `vkMptr = 0x1100` makes `scalar_inv_scratch` land exactly on the spill
    floor `0x1000`, and puts the theta block at `0x1100` - inside the finalPairing scratch
    `[0x1240, 0x1560)`. This is the closest a plan can get to the overlap `PG-FPSCRATCH` proposed. -/
def pgFpScratchCandidate : VerifierMemoryLayout :=
  VerifierMemoryLayout.new constraintSystemMetaDefault emptyVkForScratch
    (ptrMemory (valueFromNat 0x1100)) verifierMemoryLayoutConfigDefault

theorem pgFpScratchCandidate_scratch : pgFpScratchCandidate.finalPairingScratchMptr = 0x1240 := rfl

theorem pgFpScratchCandidate_theta : ptrAddr pgFpScratchCandidate.thetaMptr = 0x1100 := rfl

/-- The theta window `[0x1100, 0x1780)` straddles the scratch start `0x1240`. -/
theorem pgFpScratchCandidate_thetaWindow_straddles :
    ptrAddr pgFpScratchCandidate.thetaMptr < 0x1240 ∧
      0x1240 < ptrAddr pgFpScratchCandidate.thetaMptr +
        ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes := by
  decide

/-- **`validate` REFUTES THE INV-READ FALSIFIER, AND THE REFUTATION IS THE PROOF.** The requested
    falsifier (a `validate`-accepted plan whose pairing scratch overlaps an `Inv`-read window)
    CANNOT exist for the theta window: `theta_scalar_and_g1_slots` is `permanent`, so its lifetime
    intersects the scratch's phase and `MemoryMap.validate`'s pairwise loop orders the two windows.
    This candidate is rejected, and the message names the first overlap in registration order. -/
theorem pgFpScratchCandidate_rejected :
    pgFpScratchCandidate.validate =
      .error ("memory region constructor_smoke_scratch [0x1000..0x1300) overlaps "
        ++ "theta_scalar_and_g1_slots [0x1100..0x1780)") := by
  decide

/-- **WHAT THE PHASE RULE DOES ACCEPT** (and why the `PG-FPSCRATCH` premise looked plausible):
    `memoryLifetimeIntersects` compares two phases by equality, so two DIFFERENT phase scratches may
    overlap. In the reference layout the constructor-smoke scratch `[0x1000, 0x1300)` does overlap
    the finalPairing scratch `[0x1240, 0x1560)` in `[0x1240, 0x1300)`, and `validate` accepts the
    layout. This overlap is harmless (the phases never coexist and neither window is `Inv`-read),
    but it is exactly the rule that a `PG-FPSCRATCH` falsifier would have to exploit - and the
    permanent theta/vk windows are what keep that from reaching `Inv`. -/
theorem fpScratch_phaseOverlap_accepted :
    Midfall.Generator.LayoutMemoryKats.referenceLayout.constructorSmokeScratchMptr = 0x1000 ∧
    Midfall.Generator.LayoutMemoryKats.referenceLayout.finalPairingScratchMptr = 0x1240 ∧
    0x1240 < Midfall.Generator.LayoutMemoryKats.referenceLayout.constructorSmokeScratchMptr +
      Midfall.Generator.pairingTwoPairBytes ∧
    Midfall.Generator.LayoutMemoryKats.referenceLayout.validate.isOk = true := by
  refine ⟨rfl, rfl, by decide, by decide⟩

/-- **THE REDUCTION'S HYPOTHESIS IS DISCHARGED FROM `ValidV3`, NOT ADDED TO IT.** `SupportedV2`'s
    `layout` clause already carries `R.plan.memory.map.WellFormed` (and `memory.validate = .ok`), so
    the pairwise facts `fpScratchThetaSeparated_of_map` / `fpScratchVkSeparated_of_map` consume are
    free at every render. What is missing for `FpScratchSeparated` is only the four
    `map.region` equations - a generator-side naming lemma, not a clause. -/
theorem fpScratchWellFormed_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.pv.memory.map.WellFormed :=
  hR.supported.layout.1

theorem fpScratchValidated_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.pv.memory.validate.isOk = true :=
  hR.supported.layout.2

open Midfall.Generator.PlanNew Midfall.Generator.QuotientEvaluator

theorem le_foldl_max : ∀ (xs : List Nat) (a : Nat),
    a ≤ xs.foldl max a ∧ ∀ x ∈ xs, x ≤ xs.foldl max a
  | [], a => ⟨Nat.le_refl a, by simp⟩
  | b :: bs, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max bs (max a b)
    refine ⟨Nat.le_trans (Nat.le_max_left a b) h1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hxb | hx
    · rw [hxb]
      exact Nat.le_trans (Nat.le_max_right a b) h1
    · exact h2 x hx

theorem natMaximum_le_of_mem : ∀ {l : List Nat} {v : Nat}, natMaximum l = some v →
    ∀ x ∈ l, x ≤ v
  | [], v, h => by simp [natMaximum] at h
  | a :: as, v, h => by
    simp only [natMaximum, Option.some.injEq] at h
    subst h
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hx
    · rw [hxa]
      exact (le_foldl_max as a).1
    · exact (le_foldl_max as a).2 x hx

theorem staticWorkingMemorySizeForMeta_floor (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    {v : Nat} (h : staticWorkingMemorySizeForMeta meta_ numInstances = .ok v) :
    0x1560 ≤ v := by
  unfold staticWorkingMemorySizeForMeta at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i tw htw
    cases hv : natMaximum [transcriptBufferStart + tw.words * Midfall.Generator.wordBytes,
        pcsPairingScratchStart + staticWorkingMemorySize * Midfall.Generator.wordBytes,
        accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes,
        finalPairingScratchStart + pairingStaticWorkingWords * Midfall.Generator.wordBytes,
        verifierReturnBufferStart + Midfall.Generator.wordBytes,
        quotientReturnBufferStart + (2 + meta_.numSimpleSelectors) *
          Midfall.Generator.wordBytes] with
    | none => rw [hv] at h; cases h
    | some w =>
      rw [hv] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hmem : finalPairingScratchStart + pairingStaticWorkingWords *
          Midfall.Generator.wordBytes ∈
          [transcriptBufferStart + tw.words * Midfall.Generator.wordBytes,
           pcsPairingScratchStart + staticWorkingMemorySize * Midfall.Generator.wordBytes,
           accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes,
           finalPairingScratchStart + pairingStaticWorkingWords * Midfall.Generator.wordBytes,
           verifierReturnBufferStart + Midfall.Generator.wordBytes,
           quotientReturnBufferStart + (2 + meta_.numSimpleSelectors) *
             Midfall.Generator.wordBytes] := by
        simp
      have hle := natMaximum_le_of_mem hv _ hmem
      have hval : finalPairingScratchStart + pairingStaticWorkingWords *
          Midfall.Generator.wordBytes = 0x1560 := by decide
      omega

theorem new_thetaMptr (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).thetaMptr =
      ptrMemory (valueFromNat
        (alignUp (alignUp (ptrAddr vkMptr + vk.len) Midfall.Generator.wordBytes
            + meta_.challengeIndices.length * Midfall.Generator.wordBytes)
          Midfall.Generator.wordBytes)) := rfl

theorem new_theta_ge_vk (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) :
    ptrAddr vkMptr ≤
      ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).thetaMptr := by
  rw [new_thetaMptr, MemoryPairs.ptrAddr_valueFromNat]
  set A := ptrAddr vkMptr + vk.len
  set B := alignUp A Midfall.Generator.wordBytes
  set C := alignUp (B + meta_.challengeIndices.length * Midfall.Generator.wordBytes)
    Midfall.Generator.wordBytes
  have h1 : A ≤ B := MemoryPairs.alignUp_le A Midfall.Generator.wordBytes MemoryPairs.wordBytes_pos
  have h2 : B ≤ C := Nat.le_trans (Nat.le_add_right B _)
    (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos)
  omega


/-- `Value.asUsize` and `Value.asUsizeNat` agree on the success branch. -/
theorem asUsizeNat_of_asUsize {v : Value} {c : Nat} (h : Value.asUsize v = .ok c) :
    Value.asUsizeNat v = c := by
  cases v with
  | integer i =>
    have h' : (if i >= 0 then i.toNat else (i + (2 : Int) ^ 64).toNat) = c := by
      simpa [Value.asUsize] using Except.ok.inj h
    simpa [Value.asUsizeNat] using h'
  | identifier name off => simp [Value.asUsize] at h

/-- The FLOOR invariant of the settling fold: whenever the result is fixed, its pointer's address
    is the static working memory size computed for that result's meta. The fold settles exactly
    when the planned size equals the current pointer's address, so this is maintained by
    construction - no `WellFormed`, no region list. -/
def MetaSize (numInstances : Nat) (st : MemoryPairs.MetaState) : Prop :=
  ∀ r, st.1 = some r →
    ∃ n, staticWorkingMemorySizeForMeta r.2.1 numInstances = .ok n ∧ ptrAddr r.1 = n

theorem metaStep_metaSize {Plan : Type} (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    (st : MemoryPairs.MetaState) (i : Nat) (st' : MemoryPairs.MetaState)
    (h : (fun st (_ : Nat) => do
      if st.1.isSome then Except.ok st else do
        let vkMptr := st.2
        let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
        let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
        let cur ← Value.asUsize vkMptr.value
        if planned == cur then
          Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
        else
          Except.ok (none, ptrMemory (valueFromNat planned))) st i = .ok st') :
    MetaSize numInstances st → MetaSize numInstances st' := by
  intro hinv r hr
  simp only at h
  by_cases hs : st.1.isSome
  · rw [ite_eq_left hs] at h
    cases h
    exact hinv r hr
  · rw [ite_eq_right hs] at h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i md hmd
      split at h
      · cases h
      · rename_i planned hpl
        split at h
        · cases h
        · rename_i cur hcur
          split at h
          · have hb : st' = (some (st.2, md.1, md.2.1, md.2.2), st.2) :=
              (Except.ok.inj h).symm
            subst hb
            have hcase : planned = cur := eq_of_beq (by assumption)
            have hptr : ptrAddr st.2 = cur := by
              show Value.asUsizeNat st.2.value = cur
              exact asUsizeNat_of_asUsize hcur
            have hrr : r = (st.2, md.1, md.2.1, md.2.2) := (Option.some.inj hr).symm
            subst hrr
            refine ⟨planned, hpl, ?_⟩
            show ptrAddr st.2 = planned
            omega
          · have hb : st' = (none, ptrMemory (valueFromNat planned)) :=
              (Except.ok.inj h).symm
            subst hb
            exact absurd hr (by simp)

/-- The combined invariant: the pointer is `Nat`-built AND its address is the planned size. -/
def MetaOK (numInstances : Nat) (st : MemoryPairs.MetaState) : Prop :=
  MemoryPairs.MetaShape st ∧ MetaSize numInstances st

theorem metaStep_metaOK {Plan : Type} (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    (st : MemoryPairs.MetaState) (i : Nat) (st' : MemoryPairs.MetaState)
    (h : (fun st (_ : Nat) => do
      if st.1.isSome then Except.ok st else do
        let vkMptr := st.2
        let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
        let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
        let cur ← Value.asUsize vkMptr.value
        if planned == cur then
          Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
        else
          Except.ok (none, ptrMemory (valueFromNat planned))) st i = .ok st') :
    MetaOK numInstances st → MetaOK numInstances st' :=
  fun hst =>
    ⟨MemoryPairs.metaStep_metaShape feat env meta_ numInstances vk st i st' h hst.1,
      metaStep_metaSize feat env meta_ numInstances vk st i st' h hst.2⟩

/-- `metaDataForStableStaticLayout` returns a `Nat`-built pointer whose address is the static
    working memory size computed for the meta it returns. -/
theorem metaDataForStableStaticLayout_size {Plan : Type} (feat : Features)
    (env : VkBuildEnv Plan) (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey) (r : Ptr × ConstraintSystemMeta × Midfall.Generator.Data × VerifierMemoryLayout)
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk = .ok r) :
    ∃ n, r.1 = ptrMemory (valueFromNat n) ∧
      staticWorkingMemorySizeForMeta r.2.1 numInstances = .ok n := by
  unfold metaDataForStableStaticLayout at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i start hstart
    split at h
    · cases h
    · rename_i st' hst'
      have hinv := MemoryPairs.foldlM_metaShape (P := MetaOK numInstances)
        (step := (fun (st : MemoryPairs.MetaState) (_ : Nat) => do
          if st.1.isSome then Except.ok st else do
            let vkMptr := st.2
            let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
            let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
            let cur ← Value.asUsize vkMptr.value
            if planned == cur then
              Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
            else
              Except.ok (none, ptrMemory (valueFromNat planned))))
        (fun a i b hab ha => metaStep_metaOK feat env meta_ numInstances vk a i b hab ha)
        (a := (none, ptrMemory (valueFromNat start)))
        ⟨⟨⟨start, rfl⟩, by intro r hr; cases hr⟩, by intro r hr; simp at hr⟩ st' hst'
      cases hres : st'.1 with
      | none => rw [hres] at h; cases h
      | some r0 =>
        rw [hres] at h
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨⟨⟨n, hn⟩, hlink⟩, hfloor⟩ := hinv
        obtain ⟨m, hsize, hptr⟩ := hfloor r0 hres
        have hm : ptrAddr r0.1 = n := by
          rw [hlink r0 hres, hn, MemoryPairs.ptrAddr_valueFromNat]
        have hsame : m = n := by omega
        exact ⟨n, (hlink r0 hres).trans hn, by rw [← hsame]; exact hsize⟩

/-- `newFromVk`'s plan: the memory equation AND the floor on the VK pointer, from one peel. -/
theorem newFromVk_size {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : newFromVk feat field cs rawMeta numInstances accEncoding payload = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig) (vkBase : Nat),
      plan.memory = VerifierMemoryLayout.new meta_ payload vkMptr config ∧
        vkMptr = ptrMemory (valueFromNat vkBase) ∧
        staticWorkingMemorySizeForMeta meta_ numInstances = .ok vkBase := by
  simp only [newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := (MemoryPairs.match_ok_iff _ _).mp h
  obtain ⟨vkBase, hvk, hsize⟩ :=
    metaDataForStableStaticLayout_size feat (envOf field cs) rawMeta numInstances payload q hq
  obtain ⟨proofLayout, _, h2⟩ := (MemoryPairs.match_ok_iff _ _).mp h1
  obtain ⟨qplan, _, h3⟩ := (MemoryPairs.match_ok_iff _ _).mp h2
  obtain ⟨build, _, h4⟩ := (MemoryPairs.match_ok_iff _ _).mp h3
  obtain ⟨nativeWords, _, h5⟩ := (MemoryPairs.match_ok_iff _ _).mp h4
  obtain ⟨pcsReq, _, h6⟩ := (MemoryPairs.match_ok_iff _ _).mp h5
  obtain ⟨accTerms, _, h7⟩ := (MemoryPairs.match_ok_iff _ _).mp h6
  obtain ⟨memory, hmem, h8⟩ := (MemoryPairs.match_ok_iff _ _).mp h7
  obtain ⟨opModel, _, h9⟩ := (MemoryPairs.match_ok_iff _ _).mp h8
  obtain ⟨trip, _, h10⟩ := (MemoryPairs.match_ok_iff _ _).mp h9
  have hex : ∃ (config : VerifierMemoryLayoutConfig),
      memory = VerifierMemoryLayout.new q.2.1 payload q.1 config := by
    simp only [memoryLayoutFor, Bind.bind, Except.bind, envOf] at hmem
    obtain ⟨t, _, hmem2⟩ := (MemoryPairs.match_ok_iff _ _).mp hmem
    exact ⟨_, (Except.ok.inj hmem2).symm⟩
  obtain ⟨config, he⟩ := hex
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨q.2.1, q.1, config, vkBase, he, hvk, hsize⟩)

/-- The render face: from `GeneratedBy` alone, the memory is `new` and the VK pointer's address is
    the static working memory size computed for the layout's own meta. -/
theorem plan_size_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig) (vkBase : Nat),
      R.pv.memory = VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config ∧
        vkMptr = ptrMemory (valueFromNat vkBase) ∧
        staticWorkingMemorySizeForMeta meta_ R.cfg.numInstances = .ok vkBase := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := MemoryPairs.plan_of_generated h
  obtain ⟨meta_, vkMptr, config, vkBase, he, hvk, hsize⟩ :=
    newFromVk_size Features.solidity (frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have hpv : R.pv.memory = R.plan.memory := rfl
  have hpvk : R.pv.vk = R.plan.vk := rfl
  exact ⟨meta_, vkMptr, config, vkBase, by rw [hpv, hp, he, hpvk], hvk, hsize⟩

end Midfall.LoweringV3

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage
open Midfall.Generator.PlanNew Midfall.Generator.QuotientEvaluator

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **THE VK-POINTER FLOOR, FROM `GeneratedBy`.** The settling fold returns the pointer whose
    address is `staticWorkingMemorySizeForMeta` at the converged meta, and that size is the maximum
    of the six low-memory ends - one of which is `finalPairingScratchStart +
    pairingStaticWorkingWords * wordBytes = 0x1560`. So `0x1560 <= ptrAddr vkMptr` for EVERY render,
    with no `WellFormed` and no region list. -/
theorem generated_vkMptr_floor (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    0x1560 ≤ ptrAddr R.pv.memory.vkMptr := by
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, hsize⟩ :=
    plan_size_of_generated hR.generated
  have hmemvk : R.pv.memory.vkMptr = vkMptr := by
    rw [hmem]
    exact MemoryPairs.new_vkMptr meta_ R.pv.vk vkMptr config
  rw [hmemvk, hvk, MemoryPairs.ptrAddr_valueFromNat]
  exact staticWorkingMemorySizeForMeta_floor meta_ R.cfg.numInstances hsize

/-- The theta block starts at or after the VK payload (the `allocAfter` chain), so the same floor
    holds for `thetaMptr`. -/
theorem generated_theta_floor (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    0x1560 ≤ ptrAddr R.pv.memory.thetaMptr := by
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, -, -⟩ := plan_size_of_generated hR.generated
  have hvk := generated_vkMptr_floor R hR
  have htheta : ptrAddr R.pv.memory.vkMptr ≤ ptrAddr R.pv.memory.thetaMptr := by
    rw [hmem, MemoryPairs.new_vkMptr]
    exact new_theta_ge_vk meta_ R.pv.vk vkMptr config
  omega

/-- The finalPairing scratch sits at the fixed low-memory constant. -/
theorem generated_finalPairingScratchMptr (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.pv.memory.finalPairingScratchMptr = finalPairingScratchStart := by
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, -, -⟩ := plan_size_of_generated hR.generated
  rw [hmem]
  rfl

/-- **`FpScratchSeparated` AT EVERY RENDER.** Both windows are above the whole low phase block: the
    vk pointer's floor is `0x1560`, which is exactly `finalPairingScratchStart + pairingStaticWorkingWords *
    wordBytes`, and the theta block starts at or after the vk payload. This is the layout fact the
    finalPairing clean arm needs, proved with no new clause. -/
theorem fpScratchSeparated_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    FpScratchSeparated R.pv := by
  have hfp := generated_finalPairingScratchMptr R hR
  have htheta := generated_theta_floor R hR
  have hvk := generated_vkMptr_floor R hR
  have hlen : Midfall.Generator.pairingStaticWorkingWords * Midfall.Generator.wordBytes =
      0x320 := by decide
  have hstart : finalPairingScratchStart = 0x1240 := by decide
  simp only [FpScratchSeparated, hfp, hlen, hstart]
  constructor
  · right
    omega
  · right
    right
    omega

theorem readBytes_congr_of_outside {m₁ m₂ : Nat → UInt8} {scratch len p n : Nat}
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → m₁ x = m₂ x)
    (hwin : p + n ≤ scratch ∨ scratch + len ≤ p) :
    readBytes m₁ p n = readBytes m₂ p n := by
  rw [readBytes]
  exact Midfall.Lowering.FrameWalk.readBytes_congr m₁ m₂ p n
    (fun i hi => hmem _ (by omega))

theorem bytesAt_congr_of_outside {st st' : EvmState} {scratch len p n : Nat}
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hwin : p + n ≤ scratch ∨ scratch + len ≤ p) :
    bytesAt st' p n = bytesAt st p n := by
  unfold bytesAt
  rw [readBytes_congr_of_outside hmem hwin]

theorem wordAt_congr_of_outside {st st' : EvmState} {scratch len a : Nat}
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hwin : a + 32 ≤ scratch ∨ scratch + len ≤ a) :
    wordAt st' a = wordAt st a := by
  unfold wordAt
  exact Midfall.Yul.Word.loadWord_congr st'.memory st.memory a
    (fun i hi => hmem _ (by omega))

omit [Fact (Nat.Prime p)] in
theorem holdsFr_congr_of_outside {st st' : EvmState} {scratch len a : Nat} (x : Fr p)
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hwin : a + 32 ≤ scratch ∨ scratch + len ≤ a) :
    holdsFr st' a x = holdsFr st a x := by
  unfold holdsFr
  rw [wordAt_congr_of_outside hmem hwin]

theorem holdsG1_congr_of_outside {st st' : EvmState} {scratch len a : Nat}
    (E : VerifierEnv p G₁ G₂ Gₜ) (Q : G₁)
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hwin : a + 128 ≤ scratch ∨ scratch + len ≤ a) :
    holdsG1 E st' a Q = holdsG1 E st a Q := by
  unfold holdsG1
  rw [bytesAt_congr_of_outside hmem (by omega)]

omit [Fact (Nat.Prime p)] in
theorem List_all_congr {α : Type} {p q : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, p a = q a) → l.all p = l.all q
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, h a (by simp),
      List_all_congr as (fun b hb => h b (by simp [hb]))]

theorem holdsG1s_congr_of_outside {st st' : EvmState} {scratch len base : Nat}
    (E : VerifierEnv p G₁ G₂ Gₜ) (Qs : Array G₁)
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hbase : ∀ i, i < Qs.size →
      (base + 128 * i) + 128 ≤ scratch ∨ scratch + len ≤ base + 128 * i) :
    holdsG1s E st' base Qs = holdsG1s E st base Qs := by
  unfold holdsG1s
  apply List_all_congr
  intro a ha
  obtain ⟨-, hget⟩ := (Array.mem_zipIdx_iff_le_and_getElem?_sub).mp
    (Array.mem_toList_iff.mp ha)
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp hget
  exact holdsG1_congr_of_outside E a.1 hmem (hbase a.2 (by simpa using hi))

omit [Fact (Nat.Prime p)] in
theorem venv_get_set_ne_tot {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨x', v'⟩ := p
      by_cases hx : x' = x
      · subst hx
        have hxy : decide (x' = y) = false := by
          rw [decide_eq_false]; exact fun hh => h hh.symm
        simp only [VEnv.set, ite_true, VEnv.get, List.find?, hxy]
      · rw [VEnv.set, ite_eq_right hx]
        by_cases hy : x' = y
        · subst hy
          simp only [VEnv.get, List.find?]
          rfl
        · have hxy : decide (x' = y) = false := by
            rw [decide_eq_false]; exact hy
          simp only [VEnv.get, List.find?, hxy]
          exact ih

omit [Fact (Nat.Prime p)] in
theorem holdsFrs_congr_of_outside {st st' : EvmState} {scratch len base : Nat}
    (xs : Array (Fr p))
    (hmem : ∀ x, x < scratch ∨ scratch + len ≤ x → st'.memory x = st.memory x)
    (hbase : ∀ i, i < xs.size →
      (base + 32 * i) + 32 ≤ scratch ∨ scratch + len ≤ base + 32 * i) :
    holdsFrs st' base xs = holdsFrs st base xs := by
  unfold holdsFrs
  apply List_all_congr
  intro a ha
  obtain ⟨-, hget⟩ := (Array.mem_zipIdx_iff_le_and_getElem?_sub).mp
    (Array.mem_toList_iff.mp ha)
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp hget
  exact holdsFr_congr_of_outside a.1 hmem (hbase a.2 (by simpa using hi))

/-- `Frame` is a function of the environment and the two locals, not of memory, so writing
    `success` leaves it intact. -/
theorem Frame_set_success {R : Render p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {c : ExternalCalls} {g : ExternalGas} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (h : Frame R H vkAddr cd V st) (w : U256) :
    Frame R H vkAddr cd (VEnv.set V "success" w) st := by
  refine ⟨h.calldata, h.keccak, h.vkCode, h.vkHash, h.vkNonEmpty, ?_, ?_, h.cdSize⟩
  · obtain ⟨rv, hlk, hget⟩ := h.r
    refine ⟨rv, hlk, ?_⟩
    rw [venv_get_set_ne_tot (D := Bridge.Dialect c g) (x := "success") (y := "r") (v := w)
      (by decide)]
    exact hget
  · rw [venv_get_set_ne_tot (D := Bridge.Dialect c g) (x := "success") (y := "vk") (v := w)
      (by decide)]
    exact h.vk

theorem alignUp_mono {n n' m : Nat} (h : n ≤ n') : alignUp n m ≤ alignUp n' m := by
  unfold alignUp
  exact Nat.mul_le_mul_right m (Nat.div_le_div_right (by omega))

/-- A word-count `Ptr.add` never lowers a planner pointer: its value is an integer, and `Value.add`
    adds a nonnegative multiple of `wordBytes`. -/
theorem ptrAddr_add_ge_of_integer (q : Ptr)
    (h : ∃ n : ℕ, ptrValue q = Value.integer ↑n) (k : Nat) :
    ptrAddr q ≤ ptrAddr (Ptr.add q k) := by
  rw [Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer q k h]
  exact Nat.le_add_right _ _


/-- **THE SCRATCH-WINDOW `Inv .pcs` TRANSPORT.** If the two states agree outside the finalPairing
    scratch window, on the environment and on the halt record, then every `Inv .pcs` memory clause
    reads the same word in both. The write window sits at `0x1240` and every `Inv .pcs` read is at
    the theta block or above, whose start is at least `0x1560` (`generated_theta_floor`). -/
theorem Inv_pcs_of_mem_outside {calls : ExternalCalls} {gas : ExternalGas}
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    {S : Snapshot p G₁ G₂ Gₜ} {V : VEnv (Bridge.Dialect calls gas)} {st st' : EvmState}
    (h : Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S V st)
    (hmem : ∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
      R.pv.memory.finalPairingScratchMptr + 768 ≤ x → st'.memory x = st.memory x)
    (henv : st'.env = st.env) (hhalt : st'.halted = st.halted) (w : U256) :
    Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S (VEnv.set V "success" w) st' := by
  obtain ⟨meta_, vkMptr, config, vkBase, hlayout, -, -⟩ := plan_size_of_generated hR.generated
  have hfpconst : R.pv.memory.finalPairingScratchMptr = finalPairingScratchStart :=
    generated_finalPairingScratchMptr R hR
  have hthfloor : 0x1560 ≤ ptrAddr R.pv.memory.thetaMptr := generated_theta_floor R hR
  have hmem' : ∀ x, x < finalPairingScratchStart ∨ finalPairingScratchStart + 768 ≤ x →
      st'.memory x = st.memory x := by
    intro x hx
    exact hmem x (by simpa [hfpconst] using hx)
  have h' := h
  unfold Midfall.Lowering.Inv at h' ⊢
  simp only [Midfall.Lowering.InvAt] at h' ⊢
  rw [hlayout] at h' ⊢
  rw [hlayout, new_thetaMptr, MemoryPairs.ptrAddr_valueFromNat] at hthfloor
  -- theta start
  set T := alignUp (alignUp (ptrAddr vkMptr + R.pv.vk.len) Midfall.Generator.wordBytes
    + meta_.challengeIndices.length * Midfall.Generator.wordBytes)
    Midfall.Generator.wordBytes with hT
  have hthT : 0x1560 ≤ T := by rw [hT]; exact hthfloor
  have hfloor : finalPairingScratchStart + 768 ≤ T := by
    have h768 : finalPairingScratchStart + 768 ≤ 0x1560 := by decide
    omega

  have hp_theta : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).thetaMptr := by
    show T ≤ T + 0
    omega
  have hp_beta : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).betaMptr := by
    show T ≤ T + 32
    omega
  have hp_gamma : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).gammaMptr := by
    show T ≤ T + 64
    omega
  have hp_trashChallenge : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).trashChallengeMptr := by
    show T ≤ T + 96
    omega
  have hp_y : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).yMptr := by
    show T ≤ T + 128
    omega
  have hp_x : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xMptr := by
    show T ≤ T + 160
    omega
  have hp_x1 : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x1Mptr := by
    show T ≤ T + 192
    omega
  have hp_x2 : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x2Mptr := by
    show T ≤ T + 224
    omega
  have hp_x3 : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x3Mptr := by
    show T ≤ T + 256
    omega
  have hp_x4 : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x4Mptr := by
    show T ≤ T + 288
    omega
  have hp_fCom : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fComMptr := by
    show T ≤ T + 320
    omega
  have hp_pi : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).piMptr := by
    show T ≤ T + 448
    omega
  have hp_xN : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xNMptr := by
    show T ≤ T + 832
    omega
  have hp_lLast : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lLastMptr := by
    show T ≤ T + 896
    omega
  have hp_lBlind : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lBlindMptr := by
    show T ≤ T + 928
    omega
  have hp_l0 : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).l0Mptr := by
    show T ≤ T + 960
    omega
  have hp_instanceEval : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).instanceEvalMptr := by
    show T ≤ T + 992
    omega
  have hp_quotientEval : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientEvalMptr := by
    show T ≤ T + 1024
    omega
  have hp_quotient : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientMptr := by
    show T ≤ T + 1056
    omega
  have hp_fEval : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fEvalMptr := by
    show T ≤ T + 1216
    omega
  have hp_v : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vMptr := by
    show T ≤ T + 1248
    omega
  have hp_finalCom : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).finalComMptr := by
    show T ≤ T + 1280
    omega
  have hp_pairingLhs : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingLhsMptr := by
    show T ≤ T + 1408
    omega
  have hp_pairingRhs : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingRhsMptr := by
    show T ≤ T + 1536
    omega
  have hp_qEvalCptr : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).qEvalCptrMptr := by
    show T ≤ T + 6432
    omega
  have hp_g1Identity : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).g1IdentityMptr := by
    show T ≤ T + 6688
    omega
  have hcomms_eq : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).commsMptrBase =
      alignUp (T + 220 * Midfall.Generator.wordBytes
        + meta_.numEvals * Midfall.Generator.wordBytes) Midfall.Generator.wordBytes := by
    unfold VerifierMemoryLayout.new
    rw [MemoryPairs.ptrAddr_valueFromNat]
    rfl
  have hp_comms : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).adviceCommsMptrBase := by
    have h : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).adviceCommsMptrBase =
        alignUp (T + 220 * Midfall.Generator.wordBytes
          + meta_.numEvals * Midfall.Generator.wordBytes) Midfall.Generator.wordBytes := by
      unfold VerifierMemoryLayout.new
      rw [MemoryPairs.ptrAddr_valueFromNat]
      rfl
    rw [h]
    exact Nat.le_trans
      (by show T ≤ T + 220 * Midfall.Generator.wordBytes + meta_.numEvals * Midfall.Generator.wordBytes; omega)
      (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos)
  have hp_quotLimb : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientLimbCommsMptrBase := by
    have hA : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).commsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupMCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hB : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupMCommsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).permZCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hC : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).permZCommsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupHelperCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hD : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupHelperCommsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupZCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hE : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lookupZCommsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).trashcanCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hF : ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).trashcanCommsMptrBase ≤
        ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientLimbCommsMptrBase :=
      ptrAddr_add_ge_of_integer _ ⟨_, rfl⟩ _
    have hbase : T ≤ ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).commsMptrBase := by
      rw [hcomms_eq]
      exact Nat.le_trans
        (by show T ≤ T + 220 * Midfall.Generator.wordBytes + meta_.numEvals * Midfall.Generator.wordBytes; omega)
        (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos)
    exact Nat.le_trans hbase (Nat.le_trans hA (Nat.le_trans hB (Nat.le_trans hC
      (Nat.le_trans hD (Nat.le_trans hE hF)))))
  have hp_selector : T ≤ (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).selectorAccMptr := by
    have h : (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).selectorAccMptr =
        alignUp (alignUp (T + 220 * Midfall.Generator.wordBytes
          + meta_.numEvals * Midfall.Generator.wordBytes) Midfall.Generator.wordBytes
          + commitmentG1Count meta_ * Midfall.Generator.g1Bytes) Midfall.Generator.wordBytes := by
      show alignUp (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).commsMptrBase
          + commitmentG1Count meta_ * Midfall.Generator.g1Bytes) Midfall.Generator.wordBytes = _
      rw [hcomms_eq]
    rw [h]
    exact Nat.le_trans
      (Nat.le_trans
        (Nat.le_trans
          (by show T ≤ T + 220 * Midfall.Generator.wordBytes + meta_.numEvals * Midfall.Generator.wordBytes; omega)
          (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos))
        (Nat.le_add_right _ _))
      (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos)
  have hvkfloor : finalPairingScratchStart + 768 ≤
      ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr := by
    have h := generated_vkMptr_floor R hR
    rw [hlayout] at h
    have h768 : finalPairingScratchStart + 768 ≤ 0x1560 := by decide
    omega
  have hc_theta : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).thetaMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).thetaMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_theta; omega))
  have hc_beta : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).betaMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).betaMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_beta; omega))
  have hc_gamma : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).gammaMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).gammaMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_gamma; omega))
  have hc_trashChallenge : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).trashChallengeMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).trashChallengeMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_trashChallenge; omega))
  have hc_y : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).yMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).yMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_y; omega))
  have hc_x : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_x; omega))
  have hc_x1 : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x1Mptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x1Mptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_x1; omega))
  have hc_x2 : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x2Mptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x2Mptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_x2; omega))
  have hc_x3 : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x3Mptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x3Mptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_x3; omega))
  have hc_x4 : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x4Mptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).x4Mptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_x4; omega))
  have hc_fCom : holdsG1 R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fComMptr) (S.b.fCom) =
      holdsG1 R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fComMptr) (S.b.fCom) :=
    holdsG1_congr_of_outside R.E (S.b.fCom) hmem' (Or.inr (by have := hp_fCom; omega))
  have hc_pi : holdsG1 R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).piMptr) (S.c.pi) =
      holdsG1 R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).piMptr) (S.c.pi) :=
    holdsG1_congr_of_outside R.E (S.c.pi) hmem' (Or.inr (by have := hp_pi; omega))
  have hc_xN : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xNMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).xNMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_xN; omega))
  have hc_lLast : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lLastMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lLastMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_lLast; omega))
  have hc_lBlind : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lBlindMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).lBlindMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_lBlind; omega))
  have hc_l0 : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).l0Mptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).l0Mptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_l0; omega))
  have hc_instanceEval : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).instanceEvalMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).instanceEvalMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_instanceEval; omega))
  have hc_quotientEval : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientEvalMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientEvalMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_quotientEval; omega))
  have hc_quotient : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_quotient; omega))
  have hc_fEval : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fEvalMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).fEvalMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_fEval; omega))
  have hc_v : ∀ x : Fr p, holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vMptr) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vMptr) x :=
    fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_v; omega))
  have hc_finalCom : holdsG1 R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).finalComMptr) (S.c.finalCom.eval) =
      holdsG1 R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).finalComMptr) (S.c.finalCom.eval) :=
    holdsG1_congr_of_outside R.E (S.c.finalCom.eval) hmem' (Or.inr (by have := hp_finalCom; omega))
  have hc_pairingLhs : holdsG1 R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingLhsMptr) (S.c.dual.left.eval) =
      holdsG1 R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingLhsMptr) (S.c.dual.left.eval) :=
    holdsG1_congr_of_outside R.E (S.c.dual.left.eval) hmem' (Or.inr (by have := hp_pairingLhs; omega))
  have hc_pairingRhs : holdsG1 R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingRhsMptr) (S.c.dual.right.eval) =
      holdsG1 R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).pairingRhsMptr) (S.c.dual.right.eval) :=
    holdsG1_congr_of_outside R.E (S.c.dual.right.eval) hmem' (Or.inr (by have := hp_pairingRhs; omega))
  have hc_qEvalCptr : wordAt st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).qEvalCptrMptr) =
      wordAt st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).qEvalCptrMptr) :=
    wordAt_congr_of_outside hmem' (Or.inr (by have := hp_qEvalCptr; omega))
  have hc_g1Identity : bytesAt st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).g1IdentityMptr) 128 =
      bytesAt st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).g1IdentityMptr) 128 :=
    bytesAt_congr_of_outside hmem' (Or.inr (by have := hp_g1Identity; omega))
  have hc_quotient32 : ∀ x : Fr p,
      holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientMptr + 32) x =
      holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientMptr + 32) x :=
    fun x => holdsFr_congr_of_outside x hmem'
      (Or.inr (by have := hp_quotient; omega))
  have hc_advice : holdsG1s R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).adviceCommsMptrBase)
      (S.trace.adviceCommitments.getD 0 #[]) =
      holdsG1s R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).adviceCommsMptrBase)
      (S.trace.adviceCommitments.getD 0 #[]) :=
    holdsG1s_congr_of_outside R.E _ hmem' (fun i _ => Or.inr (by have := hp_comms; omega))
  have hc_quotLimb : holdsG1s R.E st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientLimbCommsMptrBase)
      S.alg.quotientLimbComs =
      holdsG1s R.E st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientLimbCommsMptrBase)
      S.alg.quotientLimbComs :=
    holdsG1s_congr_of_outside R.E _ hmem' (fun i _ => Or.inr (by have := hp_quotLimb; omega))
  have hc_vk : bytesAt st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr) R.pv.vk.len =
      bytesAt st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr) R.pv.vk.len :=
    bytesAt_congr_of_outside hmem' (Or.inr hvkfloor)
  -- the checkpoint guards
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  have hpcs : (Checkpoint.pcs == Checkpoint.pairing) = false := by decide
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx, h15, h25, h35, h45, h55,
    ite_true, hpcs, Bool.false_eq_true, ite_false] at h' ⊢
  -- LocalsOk is the same (r is not success)
  have hlock : LocalsOk (p := p) (calls := calls) (gas := gas) (VEnv.set V "success" w) =
      LocalsOk (p := p) (calls := calls) (gas := gas) V := by
    unfold LocalsOk
    rw [venv_get_set_ne_tot (D := Bridge.Dialect calls gas) (x := "success") (y := "r") (v := w)
      (by decide)]
  cases hlin : S.lin with
  | none =>
    simp only [hlin] at h' ⊢
    simpa only [hc_g1Identity, hc_theta, hc_beta, hc_gamma, hc_trashChallenge, hc_y, hc_x,
      hc_x1, hc_x2, hc_x3, hc_x4, hc_advice, hc_quotLimb, hc_fCom, hc_pi, hc_qEvalCptr,
      hc_xN, hc_lLast, hc_lBlind, hc_l0, hc_instanceEval, hc_quotient, hc_quotient32,
      hc_fEval, hc_v, hc_finalCom, hc_pairingLhs, hc_pairingRhs, hc_vk, hlock, hhalt, henv]
      using h'
  | some L =>
    simp only [hlin] at h' ⊢
    have hc_quotientEval : ∀ x : Fr p,
        holdsFr st' (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientEvalMptr) x =
        holdsFr st (ptrAddr (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).quotientEvalMptr) x :=
      fun x => holdsFr_congr_of_outside x hmem' (Or.inr (by have := hp_quotientEval; omega))
    have hc_selector : holdsFrs st' (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).selectorAccMptr
        (linComBuckets L.linCom) =
        holdsFrs st (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).selectorAccMptr
        (linComBuckets L.linCom) :=
      holdsFrs_congr_of_outside _ hmem' (fun i _ => Or.inr (by have := hp_selector; omega))
    simpa only [hc_g1Identity, hc_theta, hc_beta, hc_gamma, hc_trashChallenge, hc_y, hc_x,
      hc_x1, hc_x2, hc_x3, hc_x4, hc_advice, hc_quotLimb, hc_fCom, hc_pi, hc_qEvalCptr,
      hc_xN, hc_lLast, hc_lBlind, hc_l0, hc_instanceEval, hc_quotient, hc_quotient32,
      hc_quotientEval, hc_selector, hc_fEval, hc_v, hc_finalCom, hc_pairingLhs,
      hc_pairingRhs, hc_vk, hlock, hhalt, henv] using h'



/-- The clean `.pcs → .pairing` boundary transport at the STAGED invariant. The frame, the success
    bit, and the `BaseInv`/`LeanRaw`/`Mirror` clauses survive by construction (`BaseInv` and `Mirror`
    are `True` at both checkpoints and `LeanRaw` is the same existential); only `Agree` needs work,
    and that is `leanStage_pairing_of` plus `Inv_pairing_of_pcs`, both proved. The `hdual` premise is
    the pairing answer the helper supplies: at every decode, the snapshot the Lean stage built passes
    `DualMSM.check`. -/
theorem stageInv_pairing_of_pcs {calls : ExternalCalls} {gas : ExternalGas}
    (R : Render p G₁ G₂ Gₜ) {H : Hash} {vkAddr : U256} {cd : Bytes}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : StageInv R H vkAddr cd Checkpoint.pcs V st)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hdual : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
      Decoded R cd ms instW inst →
      ∀ S, leanStage R H inst ms Checkpoint.pcs = .ok S →
        DualMSM.check S.c.dual R.params = true) :
    StageInv R H vkAddr cd Checkpoint.pairing V st := by
  obtain ⟨hframe, -, -, hraw, -, hagree⟩ := h
  refine ⟨hframe, hsucc, trivial, hraw, trivial, ?_⟩
  intro ms instW inst hdec
  obtain ⟨S, hstage, hinv⟩ := hagree ms instW inst hdec
  have hsnap : snapshotOf R.E H R.vk inst ms none = .ok S := by
    simpa only [leanStage] using hstage
  have hck := hdual ms instW inst hdec S hstage
  exact ⟨S, leanStage_pairing_of hsnap hck, Inv_pairing_of_pcs hinv hsucc hck⟩

/-- **THE TWO PAIRING-SLOT PINS AT `.pcs`.** The `holdsG1` clauses of `InvAt` at `Checkpoint.pcs`
    are the two `toEip`-byte equations the finalPairing clean arm needs to identify the helper's
    on-wire frame with `fpFrame R S`. Extracting them from the thirty-clause chain is a split at the
    `.pcs` arm only; no `simp` sweep over the whole invariant (the A11 cost finding). -/
theorem inv_pcs_pairing_pins {calls : ExternalCalls} {gas : ExternalGas}
    {E : VerifierEnv p G₁ G₂ Gₜ} {params : ParamsVerifierKZG G₁ G₂}
    {PV : PlanView} {S : Snapshot p G₁ G₂ Gₜ} {V : VEnv (Bridge.Dialect calls gas)}
    {st : EvmState}
    (h : Midfall.Lowering.Inv E params Checkpoint.pcs PV S V st) :
    bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128 = E.g1.toEip S.c.dual.right.eval ∧
      bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128 = E.g1.toEip S.c.dual.left.eval := by
  have h1 := h
  unfold Midfall.Lowering.Inv at h1
  simp only [InvAt] at h1
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h1
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  have hpcs : (Checkpoint.pcs == Checkpoint.pairing) = false := by decide
  simp only [h15, h25, h35, h45, h55, ite_true, hpcs, Bool.false_eq_true, ite_false] at h1
  cases hlin : S.lin with
  | none =>
      simp only [hlin, Bool.and_eq_true] at h1
      refine ⟨?_, ?_⟩
      · have hh := h1.1.2.2
        change ((bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.right.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
      · have hh := h1.1.2.1.2
        change ((bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.left.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
  | some L =>
      simp only [hlin, Bool.and_eq_true] at h1
      refine ⟨?_, ?_⟩
      · have hh := h1.1.2.2
        change ((bytesAt st (ptrAddr PV.memory.pairingRhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.right.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)
      · have hh := h1.1.2.1.2
        change ((bytesAt st (ptrAddr PV.memory.pairingLhsMptr) 128).data ==
          (E.g1.toEip S.c.dual.left.eval).data) = true at hh
        exact ByteArray.ext (beq_iff_eq.mp hh)

/-- `Frame` reads the state only through `env.calldata`, `env.keccakOf` and `env.extCodeOf`,
    so an environment-preserving transition keeps it. -/
theorem Frame_env_congr {R : Render p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {c : ExternalCalls} {g : ExternalGas} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : Frame R H vkAddr cd V st) (henv : st'.env = st.env) :
    Frame R H vkAddr cd V st' := by
  obtain ⟨hcd, hk, hvk, hvh, hne, hr, hv, hsz⟩ := h
  refine ⟨?_, ?_, ?_, hvh, hne, hr, hv, hsz⟩
  · rw [henv]; exact hcd
  · rw [henv]; exact hk
  · rw [henv]; exact hvk

/-- The wire frame the helper hands PAIRING_CHECK, as the evidence's `ec_pairing_sem` states it:
    the two G1 slots read out of memory and the two G2 slots out of the VK header. -/
def fpWireFrame (R : Render p G₁ G₂ Gₜ) (st : EvmState) : Bytes :=
  pairingFrame
    [(bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128, vkG2Words R.pv vkG2BaseSlot),
     (bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128, vkG2Words R.pv vkNegSG2BaseSlot)]

/-- **THE CLEAN `.finalPairing` ARM, REDUCED TO THE HELPER CALL.** The hypothesis is exactly the
    existence half the `ec_pairing` body owes: on every clean `.pcs` boundary the call either
    returns the word 1, changing memory only inside the finalPairing scratch, leaving the
    environment and halt record alone and answering `true` on the wire frame, or it halts. From
    that alone the slice is live: the guard skips (`success = 1`), the assignment sets `success`
    to 1, `Inv .pcs` is transported across the 768-byte write, the two pairing slots are pinned by
    `inv_pcs_pairing_pins`, `fpG2Slots` turns the header words into the params' encodings, and
    `fp_pairing_algebra` converts the wire answer into `DualMSM.check`, which
    `stageInv_pairing_of_pcs` consumes. -/
theorem block_live_finalPairing_clean_of_call
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    (hcall : ∀ V st, StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H vkAddr cd Checkpoint.pcs V st →
      ∃ st' : EvmState,
        (EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
            (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
            (Expr.call "ec_pairing"
              [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
               Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.vals [1] st') ∧
          (∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
                R.pv.memory.finalPairingScratchMptr + 768 ≤ x → st'.memory x = st.memory x) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          product (fpWireFrame R st) = true)
        ∨ EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
            (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
            (Expr.call "ec_pairing"
              [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
               Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.halt st')) :
    ∀ V st, StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H vkAddr cd Checkpoint.pcs V st →
      ∃ V' st' o, ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (R.slice Partial.finalPairing) V' st' o ∧
        ((o = .normal ∧ Mid (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
            R H vkAddr cd Checkpoint.pairing V' st') ∨ o ≠ .normal) := by
  intro V st hclean
  have hclean' := hclean
  obtain ⟨hframe, hsucc, -, hraw, -, hagree⟩ := hclean
  -- the G2 header words are the params' encodings (the V3 `fpG2Slots`)
  have hslots : vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
      vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹ := by
    refine ⟨?_, ?_⟩
    · rw [hR.env.nG2, inv_inv]
      exact hR.payload.g2Base
    · rw [hR.env.sG2]
      exact hR.payload.negSG2
  -- the guard skips at `success = 1`
  have hguard : ExecStmt (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
        [Stmt.exprStmt (Expr.call "fail" [Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "ERR_PRECOMPILE_FAILED"])]) V st .normal :=
    vk_gate_skip_any R "ERR_PRECOMPILE_FAILED" hsucc (by decide)
  rw [fp_slice_at R hR]
  obtain ⟨st', hcase⟩ := hcall V st hclean'
  rcases hcase with ⟨hev, hmem, henv, hhalt, hprod⟩ | ⟨hev⟩
  · -- the helper answered 1: the slice exits normally, with `success = 1` and `StageInv .pairing`
    have hsucc' : VEnv.get (VEnv.setMany V ["success"] [1]) "success" = some (1 : U256) := by
      show VEnv.get (VEnv.set V "success" (1 : U256)) "success" = some 1
      exact Midfall.LoweringV2.Blocks.EcPairing.venv_get_set_same hsucc
    · -- AGREE at `.pcs` in the post state, using `Inv_pcs_of_mem_outside` per decode
      have hagree' : Agree (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
          R H cd Checkpoint.pcs (VEnv.setMany V ["success"] [1]) st' := by
        intro ms instW inst hdec
        obtain ⟨S, hstage, hinv⟩ := hagree ms instW inst hdec
        refine ⟨S, hstage, ?_⟩
        have hset : VEnv.setMany V ["success"] [1] = VEnv.set V "success" (1 : U256) := rfl
        rw [hset]
        exact Inv_pcs_of_mem_outside R hR hinv hmem henv hhalt 1
      -- the pairing answer is the `DualMSM.check` the `.pairing` boundary needs
      have hdual : ∀ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p)),
          Decoded R cd ms instW inst →
          ∀ S, leanStage R H inst ms Checkpoint.pcs = .ok S →
            DualMSM.check S.c.dual R.params = true := by
        intro ms instW inst hdec S hstage
        obtain ⟨S', hstage', hinv⟩ := hagree ms instW inst hdec
        have hS : S' = S := by
          rw [hstage] at hstage'
          exact (Except.ok.inj hstage').symm
        subst hS
        obtain ⟨hRpin, hLpin⟩ := inv_pcs_pairing_pins (E := R.E) (params := R.params)
          (PV := R.pv) (S := S') hinv
        apply (Midfall.LoweringV2.Blocks.FinalPairing.fp_pairing_algebra R product hpc S').mp
        unfold Midfall.LoweringV2.Blocks.FinalPairing.fpAnsBit
        have hfe : Midfall.LoweringV2.Blocks.FinalPairing.fpFrame R S' = fpWireFrame R st := by
          unfold Midfall.LoweringV2.Blocks.FinalPairing.fpFrame fpWireFrame
          rw [hRpin, hLpin, hslots.1, hslots.2]
        rw [hfe, hprod]
      have hframe' : Frame R H vkAddr cd (VEnv.setMany V ["success"] [1]) st' := by
        rw [show VEnv.setMany V ["success"] [1] = VEnv.set V "success" (1 : U256) from rfl]
        exact Frame_env_congr (Frame_set_success hframe 1) henv
      have hstage' : StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
          R H vkAddr cd Checkpoint.pairing (VEnv.setMany V ["success"] [1]) st' :=
        stageInv_pairing_of_pcs R ⟨hframe', hsucc', trivial, hraw, trivial,
          hagree'⟩ hsucc' hdual
      refine ⟨VEnv.setMany V ["success"] [1], st', .normal, ?_, Or.inl ⟨rfl, Or.inl hstage'⟩⟩
      refine Step.seqCons hguard (Step.seqCons (Step.assignVal hev (by rfl)) Step.seqNil)
  · -- the helper halted: the slice halts before the assignment
    refine ⟨V, st', .halt, ?_, Or.inr (by decide)⟩
    refine Step.seqCons hguard (Step.seqStop (Step.assignHalt hev) (by decide))

/-- The exact `ec_pairing` body-run residual: a `Step` of the 13-statement `ecPairingBodyLit`
    from the helper's own entry environment, ending normally with the return word 1, the 768-byte
    scratch write and nothing else, the environment and halt record preserved, and the wire answer
    -- or halting.  `Step.block` at this is the premise of `Step.callOk`; this is the missing
    existence half A11's `ecPairingBodyLit_product_runs` does not supply. -/
def FpBodyRun (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (st : EvmState) (lhsW rhsW : U256),
      ∃ (Vend : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)))
        (stend : EvmState) (o : Outcome),
        Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
          (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0))
          (["success", "lhs_mptr", "rhs_mptr"].zip
            [(1 : U256), lhsW, rhsW] ++ bindZeros (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)) ["ret"]) st
          (.stmt (.block (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
            (GenAst.pairingScratchOf R.pv)
            (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
            (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
            R.model.templateConstants.gas.pairingTwoPair 0x0f 768 32 0x84e81692 0xc3b0d8cd)))
          (.sres Vend stend o) ∧
        (((o = .normal ∨ o = .leave) ∧ VEnv.get Vend "ret" = some (1 : U256) ∧
            (∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
                  R.pv.memory.finalPairingScratchMptr + 768 ≤ x → stend.memory x = st.memory x) ∧
            stend.env = st.env ∧ stend.halted = st.halted ∧
            product (fpWireFrame R st) = true) ∨ o = .halt)

/-- **THE `ec_pairing` CALL FROM THE 13-STATEMENT BODY RUN.** The one hypothesis is the body's
    `Step` at `(.stmt (.block ecPairingBodyLit …))` from the helper's own entry environment - i.e.
    `Step.block` applied to a run of the 13 statements - with the normal post (the return word 1,
    the 768-byte scratch write and nothing else, the environment and halt record preserved, and the
    wire answer) or a halt. `Step.callOk`/`Step.callHalt` turn it into the `EvalExpr` the slice's
    assignment reads, at the two swapped `PAIRING_*_MPTR` sites. This is the exact interface
    between the clean slice (proved) and the missing body run. -/
theorem ecPairing_call_of_body
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hbody : FpBodyRun R product) :
    ∀ (V : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)))
      (st : EvmState),
      VEnv.get V "success" = some (1 : U256) →
      ∃ st' : EvmState,
        (EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
            (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
            (Expr.call "ec_pairing"
              [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
               Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.vals [1] st') ∧
          (∀ x, x < R.pv.memory.finalPairingScratchMptr ∨
                R.pv.memory.finalPairingScratchMptr + 768 ≤ x → st'.memory x = st.memory x) ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧ product (fpWireFrame R st) = true)
        ∨ EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
            (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
            (Expr.call "ec_pairing"
              [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
               Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.halt st') := by
  intro V st hsucc
  -- the declaration and its literal body
  have hdecl := Midfall.LoweringV3.ecPairingDecl_eq_lit R hR
    (callsOf product) (ExternalGas.ofFun fun _ => 0)
  have hlook : lookupFun (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) "ec_pairing" =
      some (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
        (callsOf product) (ExternalGas.ofFun fun _ => 0),
        R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) :=
    Midfall.LoweringV2.Blocks.EcPairing.ecPairing_lookup R
  -- the three argument evaluations
  have hsuccE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Expr.var "success") (.vals [(1 : U256)] st) :=
    Step.var hsucc
  have hRhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingRhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_RHS_MPTR R hR]
  have hLhs : Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR" =
      Expr.lit (.number (cAddr R.pv.memory.pairingLhsMptr)) := by
    unfold Midfall.LoweringV2.Blocks.FinalPairing.fpVal
    rw [consts_lookup_PAIRING_LHS_MPTR R hR]
  have hRhsE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR")
      (.vals [BitVec.ofNat 256
        (cAddr R.pv.memory.pairingRhsMptr)] st) := by
    rw [hRhs]; exact Step.lit
  have hLhsE : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR")
      (.vals [BitVec.ofNat 256
        (cAddr R.pv.memory.pairingLhsMptr)] st) := by
    rw [hLhs]; exact Step.lit
  have hargs : Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (.args [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
        Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"])
      (.eres (.vals [1, BitVec.ofNat 256
          (cAddr R.pv.memory.pairingRhsMptr),
        BitVec.ofNat 256
          (cAddr R.pv.memory.pairingLhsMptr)] st)) :=
    Step.argsCons
      (Step.argsCons (Step.argsCons Step.argsNil hLhsE) hRhsE) hsuccE
  -- the body run, at the swapped binders
  obtain ⟨Vend, stend, o, hstep, hpost⟩ :=
    hbody st (BitVec.ofNat 256
      (cAddr R.pv.memory.pairingRhsMptr))
      (BitVec.ofNat 256
        (cAddr R.pv.memory.pairingLhsMptr))
  -- the call's parameter/return binders at the literal declaration
  have hparams : (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).params =
      ["success", "lhs_mptr", "rhs_mptr"] := by
    rw [hdecl]
  have hrets : (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).rets = ["ret"] := by
    rw [hdecl]
  rcases hpost with ⟨hoc, hret, hmem, henv, hhalt, hprod⟩ | hoh
  · -- normal/leave: the call evaluates to the word 1
    have hlen : ([1, BitVec.ofNat 256
        (cAddr R.pv.memory.pairingRhsMptr),
      BitVec.ofNat 256
        (cAddr R.pv.memory.pairingLhsMptr)] : List U256).length =
        (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
          (callsOf product) (ExternalGas.ofFun fun _ => 0)).params.length := by
      rw [hparams]; rfl
    have hstep' : Step (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) (["success", "lhs_mptr",
          "rhs_mptr"].zip [1, BitVec.ofNat 256
            (cAddr R.pv.memory.pairingRhsMptr),
          BitVec.ofNat 256
            (cAddr R.pv.memory.pairingLhsMptr)] ++
          bindZeros (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)) ["ret"]) st
        (.stmt (.block (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
          (GenAst.pairingScratchOf R.pv)
          (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base))
          (cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base))
          R.model.templateConstants.gas.pairingTwoPair 0x0f 768 32 0x84e81692 0xc3b0d8cd)))
        (.sres Vend stend o) := hstep
    have hev : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (Expr.call "ec_pairing"
          [Expr.var "success", Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_RHS_MPTR",
           Midfall.LoweringV2.Blocks.FinalPairing.fpVal R.consts "PAIRING_LHS_MPTR"]) (.vals [1] stend) := by
      have hcall := Step.callOk (D := Bridge.Dialect (callsOf product)
          (ExternalGas.ofFun fun _ => 0)) (funs := R.scope (callsOf product)
            (ExternalGas.ofFun fun _ => 0)) (Vend := Vend) (st2 := stend)
            hargs hlook hlen ?_ hoc
      · simpa only [hdecl, List.map_cons, List.map_nil, hret, Option.getD_some] using hcall
      · simpa only [hdecl] using hstep'
    exact ⟨stend, Or.inl ⟨hev, hmem, henv, hhalt, hprod⟩⟩
  · subst hoh
    refine ⟨stend, Or.inr ?_⟩
    have hlen : ([1, BitVec.ofNat 256
        (cAddr R.pv.memory.pairingRhsMptr),
      BitVec.ofNat 256
        (cAddr R.pv.memory.pairingLhsMptr)] : List U256).length =
        (Midfall.LoweringV2.Blocks.EcPairing.ecPairingDecl R
          (callsOf product) (ExternalGas.ofFun fun _ => 0)).params.length := by
      rw [hparams]; rfl
    have hcall := Step.callHalt (D := Bridge.Dialect (callsOf product)
        (ExternalGas.ofFun fun _ => 0)) (funs := R.scope (callsOf product)
          (ExternalGas.ofFun fun _ => 0)) (Vend := Vend) (st2 := stend)
          hargs hlook hlen ?_
    · exact hcall
    · simpa only [hdecl] using hstep


/-- The clean `.finalPairing` arm from the body run, by composing the call constructor with the
    clean slice assembly. -/
theorem block_live_finalPairing_clean_of_body
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    (hbody : FpBodyRun R product) :
    ∀ V st, StageInv (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
        R H vkAddr cd Checkpoint.pcs V st →
      ∃ V' st' o, ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
        (R.slice Partial.finalPairing) V' st' o ∧
        ((o = .normal ∧ Mid (c := callsOf product) (g := ExternalGas.ofFun fun _ => 0)
            R H vkAddr cd Checkpoint.pairing V' st') ∨ o ≠ .normal) :=
  block_live_finalPairing_clean_of_call R product hR hpc H vkAddr cd
    (fun V st hclean =>
      ecPairing_call_of_body R product hR hbody V st hclean.2.1)

/-- **THE finalPairing CASE OF `block_live`, REDUCED TO THE BODY RUN.** The clean boundary is the
    assembled slice, the poisoned boundary is `block_live_finalPairing_poison`; both still carry the
    body-run residual as an arm hypothesis and nothing is added to `block_live`. -/
theorem block_live_finalPairing_of_body
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    (hbody : FpBodyRun R product) :
    BlockLive R .finalPairing H vkAddr product cd := by
  intro V st hpre
  rcases hpre with hclean | hpois
  · exact block_live_finalPairing_clean_of_body R product hR hpc H vkAddr cd hbody V st hclean
  · exact block_live_finalPairing_poison R product hR H vkAddr cd V st hpois

/-- **LEAF (TOT.1): PER-BLOCK EXISTENCE, FOR EVERY RENDER.** Leaves TOT.1.b-h, one per block: the
    existence form of the loop rule (GEN.3) at each loop, of each helper summary, the honest relation
    answering at the four precompile addresses, and the block's all-runs row to classify the
    exhibited run. Owner: TOT.1 (WP A12). WITNESS: `gap_lowering_correct_witness_unexhibited`.
    FALSIFIER: `mid_start_not_vacuous` (Stages.lean:672, PROVED). -/
theorem block_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (q : Partial) : BlockLive R q H vkAddr product cd := by
  sorry

/-! ### 2b. THE REVERT RUNS THE PREFIX LEAVES TOT.1 NEEDS

`pfxFailBody_run` (Stages.lean:1505) classifies a run of the guard body; it does not construct one.
The two constructions below are the missing existence half, built from the same `pfxOk*` step
equations the classification uses. Together with `prefix_prog_core` (the both-guards-silent case,
PROVED) they cover all three cases of the prefix: ABI guard fires, memory guard fires, or both are
silent. -/

/-- The guard body `mstore(0, shl(224, err)); revert(0, 4)` HAS a run: two `Step` constructors and
    the pure builtins. Proved, no `wp_run`, no fuel. -/
theorem pfxRevertBody_exists {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    (err : Nat) (st : EvmState) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st (pfxRevertBody err) V' st' .halt := by
  let shlE : Expr EVM.Op := Expr.builtin Op.shl [lit 224, lit err]
  let stM : EvmState :=
    { touchMemory st 0 32 with memory := storeWord st.memory 0 (BitVec.ofNat 256 err <<< 224) }
  let stR : EvmState :=
    { touchMemory stM 0 4 with halted := some (.revert, readBytes stM.memory 0 4) }
  have hShl : PfxEv funs V st shlE
      (BitVec.ofNat 256 err <<< 224) st := by
    exact pfxEv2 pfxDetShl (pfxEvLit err) (pfxEvLit 224)
      (pfxOkShl (BitVec.ofNat 256 224) (BitVec.ofNat 256 err))
  have hMstore : Step (Bridge.Dialect c g) funs V st
      (.expr (Expr.builtin Op.mstore [lit 0, shlE])) (.eres (.vals [] stM)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [lit 0, shlE])
      (argvals := [(0 : U256), (BitVec.ofNat 256 err <<< 224)]) (st1 := st) (rets := []) (st2 := stM) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [shlE])
        (restvals := [BitVec.ofNat 256 err <<< 224])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g)) hShl.ev)
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.mstore [0, BitVec.ofNat 256 err <<< 224] st (.ok [] stM)
      rfl
  have hMstoreStmt : Step (Bridge.Dialect c g) funs V st
      (.stmt (.exprStmt (Expr.builtin Op.mstore [lit 0, shlE]))) (.sres V stM .normal) :=
    Step.exprStmt hMstore
  have hRevert : Step (Bridge.Dialect c g) funs V stM
      (.expr (Expr.builtin Op.revert [lit 0, lit 4])) (.eres (.halt stR)) := by
    refine Step.builtinHalt (D := Bridge.Dialect c g) (args := [lit 0, lit 4])
      (argvals := [(0 : U256), (4 : U256)]) (st1 := stM) (st2 := stR) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [lit 4]) (restvals := [(4 : U256)])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g))
          (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 4)))
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.revert [0, 4] stM (.halt stR)
      rfl
  have hRevertStmt : Step (Bridge.Dialect c g) funs V stM
      (.stmt (.exprStmt (Expr.builtin Op.revert [lit 0, lit 4]))) (.sres V stR .halt) :=
    Step.exprStmtHalt hRevert
  refine ⟨V, stR, ?_⟩
  show Step (Bridge.Dialect c g) funs V st
      (.stmts (pfxRevertBody err)) (.sres V stR .halt)
  simp only [pfxRevertBody, shlE, stM, stR] at hMstoreStmt hRevertStmt ⊢
  exact Step.seqCons hMstoreStmt (Step.seqStop hRevertStmt (by decide))

theorem pfxHead_eq (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) :
    pfxHead R vkAddr =
      [Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c),
       Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)),
       Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)] := rfl

/-- THE ABI GUARD FIRES: the head has a run that halts at the revert. -/
theorem pfxHead_abi_revert_exists {R : Render p G₁ G₂ Gₜ} {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {vkAddr : U256} {st₀ : EvmState}
    (h : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd ≠ 0) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st₀ (pfxHead R vkAddr) V' st' .halt := by
  obtain ⟨Vb, stR, hbody⟩ := pfxRevertBody_exists (c := c) (g := g)
    (hoist (Bridge.Dialect c g) (pfxRevertBody 0x1b99e37c) :: funs) V 0x1b99e37c st₀
  have hcond : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c)))
      (.sres (restore V Vb) stR .halt) :=
    Step.ifTrue (pfxAbiEv R.pv.proofLayout.proofEnd).ev h
      (Step.block (D := Bridge.Dialect c g) hbody)
  refine ⟨restore V Vb, stR, ?_⟩
  rw [pfxHead_eq]
  exact Step.seqStop hcond (by decide)

/-- THE MEMORY GUARD FIRES: the ABI guard is silent, the `let vk` runs, then the second guard halts. -/
theorem pfxHead_mem_revert_exists {R : Render p G₁ G₂ Gₜ} {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {vkAddr : U256} {st₀ : EvmState}
    (ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0)
    (hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr ≠ 0) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st₀ (pfxHead R vkAddr) V' st' .halt := by
  have h1 : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c)))
      (.sres V st₀ .normal) :=
    Step.ifFalse (pfxAbiEv R.pv.proofLayout.proofEnd).ev ha
  have h2 : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.letDecl ["vk"] (some (lit vkAddr.toNat))))
      (.sres (List.zip ["vk"] [vkAddr] ++ V) st₀ .normal) := by
    have hh := Step.letVal (D := Bridge.Dialect c g) (funs := funs) (V := V) (st := st₀)
      (vars := ["vk"]) (e := lit vkAddr.toNat)
      (vals := [(Bridge.Dialect c g).litValue (Literal.number vkAddr.toNat)])
      (Step.lit (D := Bridge.Dialect c g) (V := V) (st := st₀)) (by simp)
    rw [litValue_number vkAddr] at hh
    exact hh
  obtain ⟨Vb, stR, hbody⟩ :=
    pfxRevertBody_exists (c := c) (g := g)
      (hoist (Bridge.Dialect c g) (pfxRevertBody 0xc9888d23) :: funs)
      (List.zip ["vk"] [vkAddr] ++ V) 0xc9888d23 (touchMemory st₀ 0x40 32)
  have h3 : Step (Bridge.Dialect c g) funs (List.zip ["vk"] [vkAddr] ++ V) st₀
      (.stmt (Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)))
      (.sres (restore (List.zip ["vk"] [vkAddr] ++ V) Vb) stR .halt) :=
    Step.ifTrue (pfxMemEv (funs := funs) (V := List.zip ["vk"] [vkAddr] ++ V)
      R.pv.memory.transcriptMptr).ev hm
      (Step.block (D := Bridge.Dialect c g) hbody)
  refine ⟨restore (List.zip ["vk"] [vkAddr] ++ V) Vb, stR, ?_⟩
  rw [pfxHead_eq]
  exact Step.seqCons h1 (Step.seqCons h2 (Step.seqStop h3 (by decide)))

/-- **LEAF (TOT.1 with SIM.6): PREFIX EXISTENCE.** The ABI guard and the memory guard each revert or
    pass, and both are runs. Owner: TOT.1 (WP A12) with SIM.6 (WP A1). WITNESS:
    `gap_lowering_correct_witness_unexhibited`. FALSIFIER: `stageInv_start_not_vacuous`
    (Stages.lean:663, PROVED). -/
theorem prefix_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrameV3 R W Lyt H cd st₀) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st) := by
  intro V st hpre
  obtain ⟨hV, hst⟩ := hpre
  subst V
  subst st
  have hf := pfxFacts_of_validV3 hR
  by_cases ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0
  · by_cases hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0
    · -- both guards silent: the PROVED progress core supplies the normal run at `.start`
      have htotal := prefix_prog_core (c := callsOf product)
        (g := ExternalGas.ofFun fun _ => 0) hf hdep hentry.toV2 ha hm
      obtain ⟨V', st', o, hrun, hpost⟩ := htotal.1 [] st₀ ⟨rfl, rfl⟩
      exact ⟨V', st', o, hrun, Or.inl ⟨hpost.1, by simpa [LivePre] using hpost.2⟩⟩
    · -- the memory guard fires
      obtain ⟨V', st', hrun⟩ :=
        pfxHead_mem_revert_exists (c := callsOf product)
          (g := ExternalGas.ofFun fun _ => 0) (R.scope _ _) [] (vkAddr := vkAddr) ha hm
      rw [preBlock_of_facts hf vkAddr, List.append_assoc]
      exact ⟨V', st', .halt, stmts_append_stop hrun (by decide), Or.inr (by decide)⟩
  · -- the ABI guard fires
    obtain ⟨V', st', hrun⟩ :=
      pfxHead_abi_revert_exists (c := callsOf product)
        (g := ExternalGas.ofFun fun _ => 0) (R.scope _ _) [] (vkAddr := vkAddr) ha
    rw [preBlock_of_facts hf vkAddr, List.append_assoc]
    exact ⟨V', st', .halt, stmts_append_stop hrun (by decide), Or.inr (by decide)⟩

/-- The seven slices are live. PROVED from `block_live` (evidence `GeneratorRows.lean:1352`). -/
theorem slices_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (h7 : ∀ q : Partial, BlockLive R q H vkAddr product cd) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st)
      (fun V st => LivePre R H vkAddr cd Checkpoint.pairing V st) :=
  live_append (live_append (live_append (live_append (live_append (live_append
    (h7 .vkLoading) (h7 .transcriptParser)) (h7 .lagrange)) (h7 .quotientLin)) (h7 .pcs))
    (h7 .finalPairing)) (h7 .traceReturn)

/-- **OBLIGATION 4, PROVED from the four named leaves** (`gasFree_of_valid`,
    `runBody_gas_oblivious`, `block_live`, `prefix_live`). This replaces `totalV3_of_stages`,
    which the unfolding of `BodyTotal` shows cannot be derived from `ProgRowsV3` at all (header).
    The `GasTotal` hypothesis is carried by the statement and not used by the glue: the gas oracle is
    arbitrary precisely because a gas-free program cannot tell one from another. -/
theorem totalV3_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    TotalV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec g _hg
  have hlive := live_append
    (prefix_live R product hR W Lyt H vkAddr cd st₀ hdep hentry)
    (slices_live R product H vkAddr cd
      (fun q => block_live R product hR hcodec hpc H vkAddr cd q))
  obtain ⟨V', st', o, hrun, _⟩ := hlive [] st₀ ⟨rfl, rfl⟩
  exact ⟨_, runBody_gas_oblivious R vkAddr (gasFree_of_valid R hR vkAddr) _ _ g st₀ _
    (run_joinV3 R (noShadowB_of_valid hR) vkAddr _ _ st₀ V' st' o hrun)⟩

/-! ## 3. Cone lists and axiom prints -/

#cone_sorries Midfall.LoweringV3.totalV3_correct
#cone_sorries Midfall.LoweringV3.prefix_live
#cone_sorries Midfall.LoweringV3.slices_live
#cone_sorries Midfall.LoweringV3.live_append
#print axioms Midfall.LoweringV3.prefix_live
#print axioms Midfall.LoweringV3.pfxRevertBody_exists
#print axioms Midfall.LoweringV3.pfxHead_abi_revert_exists
#print axioms Midfall.LoweringV3.pfxHead_mem_revert_exists
#assert_axioms Midfall.LoweringV3.prefix_live [propext, Classical.choice, Quot.sound] native []

#print axioms Midfall.LoweringV3.totalV3_correct
#print axioms Midfall.LoweringV3.slices_live
#print axioms Midfall.LoweringV3.live_append
#print axioms Midfall.LoweringV3.stmts_append_stop
#print axioms Midfall.LoweringV3.gasFreeScan
#cone_sorries Midfall.LoweringV3.runBody_gas_oblivious
#print axioms Midfall.LoweringV3.runBody_gas_oblivious
#assert_axioms Midfall.LoweringV3.runBody_gas_oblivious [propext, Classical.choice, Quot.sound] native []
#cone_sorries Midfall.LoweringV3.gasFree_of_valid
#print axioms Midfall.LoweringV3.gasFree_of_valid
#assert_axioms Midfall.LoweringV3.gasFree_of_valid [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3
