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

/-- The scan that replaces TOT.1's "decidable scan of the literal program": no `gas()` anywhere,
    function bodies included. Structural in the fuel, like `Bridge.noWritersScan`, so `decide`
    reduces it. Ported verbatim from the evidence (`GeneratorRows.lean:1215`). -/
def gasFreeScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !(op == EVM.Op.gas) && gasFreeScan n (.es args)
    | .e (.call _ args) => gasFreeScan n (.es args)
    | .es [] => true
    | .es (e :: rest) => gasFreeScan n (.e e) && gasFreeScan n (.es rest)
    | .s (.block body) => gasFreeScan n (.b body)
    | .s (.funDef _ _ _ body) => gasFreeScan n (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => gasFreeScan n (.e e)
    | .s (.assign _ e) => gasFreeScan n (.e e)
    | .s (.cond c body) => gasFreeScan n (.e c) && gasFreeScan n (.b body)
    | .s (.switch c cases dflt) =>
        gasFreeScan n (.e c) && gasFreeScan n (.cs cases) &&
          (match dflt with | none => true | some d => gasFreeScan n (.b d))
    | .s (.forLoop init c post body) =>
        gasFreeScan n (.b init) && gasFreeScan n (.e c) &&
          gasFreeScan n (.b post) && gasFreeScan n (.b body)
    | .s (.exprStmt e) => gasFreeScan n (.e e)
    | .s .break => true
    | .s .continue => true
    | .s .leave => true
    | .b [] => true
    | .b (s :: ss) => gasFreeScan n (.s s) && gasFreeScan n (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => gasFreeScan n (.b b) && gasFreeScan n (.cs rest)

/-- A block executes no `gas()`. -/
def GasFree (b : Block EVM.Op) : Prop := ∃ n, gasFreeScan n (.b b) = true

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


/-- **LEAF (TOT.1): THE PROGRAM OF A VALID RENDER EXECUTES NO `gas()`.** PREMISE GAP PG-GAS in the
    evidence: `SupportedV2` excludes the three features that print `gas()`, but no clause says the
    program is free of it. Owner: TOT.1 (WP A12). WITNESS: the named gap
    `gap_lowering_correct_witness_unexhibited` - `ValidV3` has no inhabitant the tree can name until
    WP B4 (D-P75 item 5). FALSIFIER: the two `example`s above. -/
theorem gasFree_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (vkAddr : U256) :
    GasFree (R.prog vkAddr 0) := by
  sorry

/-- **LEAF (TOT.1.a): A GAS-FREE PROGRAM HAS THE SAME RUNS UNDER EVERY GAS ORACLE.** One `Step`
    induction in the shape of `Bridge.Run_worldEq_of_noWriters`; generic in the block. Owner:
    TOT.1.a (WP A12). WITNESS: `gap_lowering_correct_witness_unexhibited`. FALSIFIER:
    `mid_start_not_vacuous` (Stages.lean:672, PROVED) - the boundary the run starts from is not
    `True`, so the runs compared are runs of this program and not of an arbitrary one. -/
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

end Midfall.LoweringV3
