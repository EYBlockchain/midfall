/-
  Midfall.Generator.CertScan  (CERT.5 family (b), PLAN-V3)

  THE SYNTACTIC INVARIANTS OF THE TREE EMITTERS, one lemma per emitter group and one composition
  lemma over `mainAsmRaw` / `abiGuardBlock`.

  WHAT THIS FILE PROVES. The scans CERT.5 names - `noShadowProg` / `noShadowCore` (binders),
  `callsResolved` (call sites against the top-level function table), and the `NoWriters` fuel scan -
  are *compositional in the statement list*. This file lands that composition algebra (§1), the
  per-emitter name and signature tables for every group that is a function of the PLAN VIEW alone
  (§2-§4), and the decomposition of `mainAsmRaw` into those groups plus ONE residual (§5): the
  `quotientLin` prefix `emitQuotientHelpersAt c.quotientPow5Helper ++ emitQuotientNumerator c ++
  emitQuotientLin pv`.

  THE WALL, STATED WHERE IT IS HIT (and why the CERT.5 leaves are not closed by this file).
  `emitQuotientNumerator` is `YulParse.parseLines [renderQuotientNumeratorBlock c]` (GenAst:789) -
  a PARSE of a String built from `PartialCtx` fields, whose `quotientProgram`, `quotientInline-
  Computations` and five sibling line families are MODEL data. `yulTokens` is built out of
  `String.splitOn` / `String.replace` / `String.startsWith`, which are `@[extern]`: the KERNEL
  cannot reduce them, and `native_decide` cannot evaluate a term with the render's free variables.
  So for a *symbolic* model nothing in the tree can say what `parseLines …` returns - not that it
  fails (then `emitQuotientNumerator c = []` and every scan is trivially clean), not that it
  succeeds with a `Stmt.block` (then the top-level binder scan is trivially clean), and certainly
  not that its binders avoid the constant names or that its calls resolve. The generated text is
  scan-safe because the PORTED RUST CODEGEN emits good code, and that is a fact about
  `compactQuotientComputationBlocks` / `renderQuotientNumeratorBlock` that the tree records only as
  concrete-render KATs (`Instances/M2BatchKats.lean`, `Instances/StatementsV3Deploy.lean`).

  The residual is therefore named, not weakened: §5 states the two hypotheses
  (`BinderNamesOK … (emitQuotientNumerator c)`, `CallNamesOK …`) that the numerator block would
  have to satisfy, and every CERT.5 scan theorem follows from them mechanically. When OBJ.15's
  structured numerator is spliced in (or a generic `parseLines`-of-generated-text lemma is landed),
  only those hypotheses remain.

  THE SECOND WALL (shadow scans only): `noShadowCore` / `noShadowProg` compare against
  `constTableOf m`, i.e. `solConstantLine?` over `renderConstants (partialCtxOfVerifier m)`. The
  NAMES of that table are again a `String.splitOn` fact (the values differ by render, the names do
  not), so the shadow scans need CERT.6's `prog_constTable` (or a name-level version of it) to turn
  `(constTableOf m).map Prod.fst` into the fixed `expectedConstsNames` list. §5 states the shadow
  reductions with that list named explicitly.

  NO SORRY, NO `native_decide`, no new axiom: everything here is on the standard three and is
  imported by `Midfall/Generator/Certified.lean` only when a target can cite it.
-/
import Midfall.LoweringV3.Statements
import Midfall.Lowering.GenAstDispatch

set_option autoImplicit false

namespace Midfall.Generator.CertScan

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

/-! ## 1. SCAN ALGEBRA: every scan is a fold over the statement list

  These are the lemmas the composition consumes. They are stated for the exact definitions the
  frozen statements use (`LoweringV2.boundSs`, `LoweringV2.refSs`, `LoweringV3.callSitesSs`,
  `LoweringV3.funSigsOf`, `LoweringV2.topBinders`, `LoweringV3.noShadowProg`), not for copies. -/

theorem boundSs_append (a b : YulBlock) :
    LoweringV2.boundSs (a ++ b) =
      LoweringV2.boundSs a ++ LoweringV2.boundSs b := by
  induction a with
  | nil => rw [List.nil_append, LoweringV2.boundSs.eq_1, List.nil_append]
  | cons s ss ih =>
      rw [List.cons_append, LoweringV2.boundSs.eq_2, LoweringV2.boundSs.eq_2, ih,
        List.append_assoc]

theorem refSs_append (a b : YulBlock) :
    LoweringV2.refSs (a ++ b) = LoweringV2.refSs a ++ LoweringV2.refSs b := by
  induction a with
  | nil => rw [List.nil_append, LoweringV2.refSs.eq_1, List.nil_append]
  | cons s ss ih =>
      rw [List.cons_append, LoweringV2.refSs.eq_2, LoweringV2.refSs.eq_2, ih,
        List.append_assoc]

theorem callSitesSs_append (a b : YulBlock) :
    LoweringV3.callSitesSs (a ++ b) =
      LoweringV3.callSitesSs a ++ LoweringV3.callSitesSs b := by
  induction a with
  | nil => rw [List.nil_append, LoweringV3.callSitesSs.eq_1, List.nil_append]
  | cons s ss ih =>
      rw [List.cons_append, LoweringV3.callSitesSs.eq_2, LoweringV3.callSitesSs.eq_2, ih,
        List.append_assoc]

theorem funSigsOf_append (a b : YulBlock) :
    LoweringV3.funSigsOf (a ++ b) =
      LoweringV3.funSigsOf a ++ LoweringV3.funSigsOf b := by
  simp [LoweringV3.funSigsOf, List.filterMap_append]

theorem topBinders_append (a b : YulBlock) :
    LoweringV2.topBinders (a ++ b) =
      LoweringV2.topBinders a ++ LoweringV2.topBinders b := by
  simp [LoweringV2.topBinders, List.flatMap_append]

/-- `noShadowProg` is an `all` over the concatenated binder list: conjunction splits. -/
theorem noShadowProg_append (consts : List (String × Nat)) (a b : YulBlock) :
    LoweringV3.noShadowProg consts (a ++ b) = true ↔
      LoweringV3.noShadowProg consts a = true ∧
        LoweringV3.noShadowProg consts b = true := by
  unfold LoweringV3.noShadowProg
  rw [boundSs_append, List.all_append, Bool.and_eq_true]

/-- `noShadowCore`'s three pieces, separated. -/
theorem noShadowCore_eq (pv : PlanView) (m : Model) :
    LoweringV3.noShadowCore pv m =
      (LoweringV2.topBinders (abiGuardBlock m) ++
        LoweringV2.topBinders (wrapperLocals m 0 0) ++
        LoweringV2.topBinders (mainAsmRaw pv m)).all
        fun x => !((constTableOf m).map Prod.fst).contains x := by
  unfold LoweringV3.noShadowCore
  rw [topBinders_append, topBinders_append]

/-- The `all`/`contains` form every per-emitter binder lemma produces. -/
theorem noShadowProg_of_forall_not_contains {consts : List (String × Nat)} {prog : YulBlock}
    (h : ∀ x ∈ LoweringV2.boundSs prog,
      ((consts.map Prod.fst).contains x) = false) :
    LoweringV3.noShadowProg consts prog = true := by
  unfold LoweringV3.noShadowProg
  rw [List.all_eq_true]
  intro x hx
  rw [h x hx]
  rfl

/-- `noShadowCore` from the same shape at the three pieces. -/
theorem noShadowCore_of_forall_not_contains {pv : PlanView} {m : Model}
    (h : ∀ x ∈ LoweringV2.topBinders
      (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m),
      ((constTableOf m).map Prod.fst).contains x = false) :
    LoweringV3.noShadowCore pv m = true := by
  unfold LoweringV3.noShadowCore
  rw [List.all_eq_true]
  intro x hx
  rw [h x hx]
  rfl

/-- The `callsResolved` scan is three conjuncts; this is the shape a composition cites. -/
theorem callsResolved_of {main : YulBlock}
    (hcalls : ∀ c ∈ LoweringV3.callSitesSs main,
      (LoweringV3.funSigsOf main).contains c = true)
    (hparse : ∀ s ∈ LoweringV3.funSigsOf main, (EVM.parse s.1).isNone = true)
    (hnodup : ((LoweringV3.funSigsOf main).map Prod.fst).Nodup) :
    LoweringV3.callsResolved main = true := by
  unfold LoweringV3.callsResolved
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hcalls, hparse⟩, hnodup⟩

/-- The same, with the call sites and signatures split at a concatenation point. -/
theorem callsResolved_append_of {a b : YulBlock}
    (hcallsA : ∀ c ∈ LoweringV3.callSitesSs a,
      (LoweringV3.funSigsOf (a ++ b)).contains c = true)
    (hcallsB : ∀ c ∈ LoweringV3.callSitesSs b,
      (LoweringV3.funSigsOf (a ++ b)).contains c = true)
    (hparse : ∀ s ∈ LoweringV3.funSigsOf (a ++ b), (EVM.parse s.1).isNone = true)
    (hnodup : ((LoweringV3.funSigsOf (a ++ b)).map Prod.fst).Nodup) :
    LoweringV3.callsResolved (a ++ b) = true := by
  refine callsResolved_of ?_ hparse hnodup
  intro c hc
  rw [callSitesSs_append, List.mem_append] at hc
  exact hc.elim (hcallsA c ·) (hcallsB c ·)

/-! ### `freeNames` and the closedness scans

  `freeNames b` is `eraseDups` of the references of `b` that no binder of `b` owns. It is
  *antitone* in the binder set, which is why appending a block can only shrink the names the left
  block contributes. That is the one fact `prog_constsDeclared`/`prog_closed` need from this file. -/

theorem mem_freeNames_iff {b : YulBlock} {x : String} :
    x ∈ LoweringV2.freeNames b ↔
      x ∈ LoweringV2.refSs b ∧ x ∉ LoweringV2.boundSs b := by
  simp [LoweringV2.freeNames, List.mem_eraseDups, List.mem_filter]

theorem freeNames_subset_of_append_left (a b : YulBlock) :
    ∀ x ∈ LoweringV2.freeNames (a ++ b),
      x ∈ LoweringV2.freeNames a ∨ x ∈ LoweringV2.freeNames b := by
  intro x hx
  rw [mem_freeNames_iff] at hx
  obtain ⟨href, hbound⟩ := hx
  rw [refSs_append, List.mem_append] at href
  rw [boundSs_append, List.mem_append, not_or] at hbound
  obtain ⟨hba, hbb⟩ := hbound
  rcases href with h | h
  · exact Or.inl (by rw [mem_freeNames_iff]; exact ⟨h, hba⟩)
  · exact Or.inr (by rw [mem_freeNames_iff]; exact ⟨h, hbb⟩)

/-! ### `NoWriters` is compositional

  `noWritersScan` threads ONE fuel through every recursive call, so the fuel a list needs is its
  longest path. The append lemma below records the exact accounting: a clean block `a` at fuel
  `n + |a|` leaves the scan of `b` at fuel `n`. -/

theorem noWritersFuel_append_clean {n : Nat} {a b : YulBlock}
    (ha : noWritersScan (n + a.length) (.b a) = true) :
    noWritersScan (n + a.length) (.b (a ++ b)) = noWritersScan n (.b b) := by
  induction a with
  | nil => simp
  | cons s ss ih =>
      have hfuel : n + (ss.length + 1) = (n + ss.length) + 1 := by omega
      rw [List.length_cons, hfuel] at ha ⊢
      simp only [List.cons_append, noWritersScan, noWritersStep, Bool.and_eq_true] at ha ⊢
      rw [ha.1, ih ha.2, Bool.true_and]

/-- The existential form used by `NoWriters`. -/
theorem NoWriters_append {a b : YulBlock} (ha : NoWriters a) (hb : NoWriters b) :
    NoWriters (a ++ b) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + a.length, ?_⟩
  show noWritersScan (max n m + a.length) (.b (a ++ b)) = true
  rw [noWritersFuel_append_clean (n := max n m)
    (noWritersScan_mono (by omega) hn)]
  exact noWritersScan_mono (Nat.le_max_right n m) hm

/-! ## 2. `topBinders`: the TOP-LEVEL binder table of every emitter group

  `topBinders b = b.flatMap Inline.boundOf` reads only the statements that bind at the block's top
  level: `let`, `:=` and `function` (whose parameters and results are its binders). Nested scopes -
  a `for` loop's init, an `if` body, a bare `{ }` block - do NOT contribute, which is what makes the
  fixed-text groups computable without their bodies.

  These are the lemmas `v3_noShadow` (`noShadowCore`) consumes: its scan is exactly this list for
  the guards, the wrappers and the main block. -/

theorem topBinders_singleton (s : Stmt EVM.Op) :
    LoweringV2.topBinders [s] = Inline.boundOf s := by
  simp [LoweringV2.topBinders]

theorem topBinders_flatten_map {α : Type _} (l : List α) (f : α → YulBlock) :
    LoweringV2.topBinders (List.flatten (l.map f)) =
      l.flatMap (fun a => LoweringV2.topBinders (f a)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, topBinders_append, ih, List.flatMap_cons]

theorem topBinders_map {α : Type _} (l : List α) (g : α → Stmt EVM.Op) :
    LoweringV2.topBinders (l.map g) =
      l.flatMap (fun a => Inline.boundOf (g a)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.flatMap_cons, LoweringV2.topBinders, List.flatMap_cons,
        List.append_assoc]
      rw [show List.flatMap Inline.boundOf (List.map g as) =
        List.flatMap (fun a => Inline.boundOf (g a)) as from ih]

theorem mem_topBinders_map {α : Type _} {l : List α} {g : α → Stmt EVM.Op} {x : String} :
    x ∈ LoweringV2.topBinders (l.map g) ↔
      ∃ a ∈ l, x ∈ Inline.boundOf (g a) := by
  rw [topBinders_map, List.mem_flatMap]

theorem boundOf_funDef (n : String) (ps rs : List String) (body : YulBlock) :
    Inline.boundOf (Stmt.funDef n ps rs body) = ps ++ rs := rfl

theorem boundOf_letDecl_some (xs : List String) (e : Expr EVM.Op) :
    Inline.boundOf (Stmt.letDecl xs (some e)) = xs := rfl

theorem boundOf_letDecl_none (xs : List String) :
    Inline.boundOf (Stmt.letDecl xs none) = xs := rfl

theorem boundOf_assign (xs : List String) (e : Expr EVM.Op) :
    Inline.boundOf (Stmt.assign xs e) = xs := rfl

theorem boundOf_block (b : YulBlock) : Inline.boundOf (Stmt.block b) = [] := rfl

theorem boundOf_cond (c : Expr EVM.Op) (b : YulBlock) :
    Inline.boundOf (Stmt.cond c b) = [] := rfl

theorem boundOf_forLoop (i : YulBlock) (c : Expr EVM.Op) (post body : YulBlock) :
    Inline.boundOf (Stmt.forLoop i c post body) = [] := rfl

theorem boundOf_exprStmt (e : Expr EVM.Op) : Inline.boundOf (Stmt.exprStmt e) = [] := rfl

theorem boundOf_switch (c : Expr EVM.Op) (cs : List (Literal × YulBlock))
    (d : Option YulBlock) : Inline.boundOf (Stmt.switch c cs d) = [] := rfl

theorem boundOf_break : Inline.boundOf (Stmt.break : Stmt EVM.Op) = [] := rfl

theorem mem_topBinders_append {a b : YulBlock} {x : String} :
    x ∈ LoweringV2.topBinders (a ++ b) ↔
      x ∈ LoweringV2.topBinders a ∨ x ∈ LoweringV2.topBinders b := by
  rw [topBinders_append, List.mem_append]

theorem mem_topBinders_flatten_map {α : Type _} {l : List α} {f : α → YulBlock} {x : String} :
    x ∈ LoweringV2.topBinders (List.flatten (l.map f)) ↔
      ∃ a ∈ l, x ∈ LoweringV2.topBinders (f a) := by
  rw [topBinders_flatten_map, List.mem_flatMap]

theorem topBinders_abiGuardBlock (m : Model) :
    LoweringV2.topBinders (abiGuardBlock m) = [] := rfl

theorem topBinders_mainGuardBlock :
    LoweringV2.topBinders mainGuardBlock = [] := rfl

theorem topBinders_mainLocals :
    LoweringV2.topBinders mainLocals = ["r", "success"] := rfl

theorem topBinders_wrapperLocals (m : Model) (vkAddr qAddr : U256) :
    LoweringV2.topBinders (wrapperLocals m vkAddr qAddr) =
      (if m.embeddedVk.isNone then ["vk"] else []) ++
        (if m.quotientExternal.isSome then ["quotientEvaluator"] else []) := by
  cases h1 : m.embeddedVk <;> cases h2 : m.quotientExternal <;>
    simp [wrapperLocals, h1, h2, LoweringV2.topBinders, Inline.boundOf]

/-- The eight AssemblyHelpers definitions, in template order, with their parameter/result names. -/
def helpersTopNames : List String :=
  ["sel"] ++
  ["x", "inv"] ++
  ["buf_len"] ++
  ["buf_len", "word", "ret"] ++
  ["buf_len", "cptr", "ret"] ++
  ["buf_len", "mptr", "ret"] ++
  ["success", "mptr_start", "mptr_end", "scratch_mptr", "r", "ret", "precompile_failed"] ++
  ["success", "lhs_mptr", "rhs_mptr", "ret"]

theorem topBinders_emitHelpers (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitHelpers pv) = helpersTopNames := rfl

/-- The five accumulator-codec definitions of `AccumulatorHelpers.yul`. -/
def accumulatorTopNames : List String :=
  ["src", "bits", "n", "base", "limbs_per_word", "hi", "lo"] ++
  ["hi", "lo", "yes"] ++
  ["src", "bits", "n", "limbs_per_word", "ok"] ++
  ["src", "bits", "n", "base", "limbs_per_word", "ok", "hi", "lo"] ++
  ["dst", "src", "bits", "n", "base", "ok", "is_id"]

theorem topBinders_emitAccumulatorHelpers :
    LoweringV2.topBinders GenAst.emitAccumulatorHelpers = accumulatorTopNames := rfl

/-- The quotient helper definitions: only `q_pow5` binds, and only on its flag. -/
theorem topBinders_emitQuotientHelpersAt (pow5 : Bool) :
    LoweringV2.topBinders (GenAst.emitQuotientHelpersAt pow5) =
      (if pow5 then ["x", "z"] else []) := by
  cases pow5 <;> rfl

theorem topBinders_emitVkLoading (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitVkLoading pv) =
      (if pv.hasAccumulator then
        ["acc_precompile_failed", "success", "acc_precompile_failed"] else []) := by
  cases h : pv.hasAccumulator <;>
    simp [GenAst.emitVkLoading, GenAst.emitVkLoadingArms, h, LoweringV2.topBinders,
      GenAst.yblock, GenAst.yif, GenAst.yset, GenAst.ysetN, GenAst.yexpr, GenAst.ycall,
      GenAst.yvar, GenAst.ylit, GenAst.yop, GenAst.ylet, Inline.boundOf]

theorem topBinders_emitLagrange (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitLagrange pv) = ["lagrange_precompile_failed"] := rfl

theorem topBinders_emitQuotientLin (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitQuotientLin pv) = [] := rfl

theorem topBinders_emitFinalPairing (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitFinalPairing pv) = ["success"] := by
  cases h : pv.hasAccumulator <;>
    simp [GenAst.emitFinalPairing, GenAst.emitFinalPairingArms, h, GenAst.emitAccBatch,
      LoweringV2.topBinders, GenAst.yblock, GenAst.yif, GenAst.yset, GenAst.yexpr,
      GenAst.ycall, GenAst.yvar, GenAst.ylit, GenAst.yop, GenAst.ylet, Inline.boundOf]

theorem topBinders_emitTraceReturn (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitTraceReturn pv) = [] := rfl

/-- The PCS slice is ONE nested block on success and empty on a plan-shape fault; either way it
    binds nothing at the top level. This is why the PCS emitter needs no binder table here. -/
theorem topBinders_emitPcsFromPlan (pv : PlanView) :
    LoweringV2.topBinders (GenAst.emitPcsFromPlan pv) = [] := by
  unfold GenAst.emitPcsFromPlan
  split <;> rfl


theorem callSitesE_lit (l : Literal) :
    Midfall.LoweringV3.callSitesE (Expr.lit l) = [] := rfl

theorem callSitesE_var (x : String) :
    Midfall.LoweringV3.callSitesE (Expr.var x) = [] := rfl

theorem funSigsOf_eq_nil_of_forall {b : YulBlock}
    (h : ∀ s ∈ b, ∀ (n : String) (ps rs : List String) (body : YulBlock),
      s ≠ Stmt.funDef n ps rs body) :
    Midfall.LoweringV3.funSigsOf b = [] := by
  rw [Midfall.LoweringV3.funSigsOf, List.filterMap_eq_nil_iff]
  intro s hs
  cases s with
  | funDef n ps rs body => exact absurd rfl (h _ hs _ _ _ _)
  | _ => rfl

/-! ## 3. `callsResolved`: the call-site and signature tables of the emitter groups

  `funSigsOf` reads only top-level `function` definitions; `callSitesSs` reads every user call at
  any depth. The two tables below are what `callsResolved` compares, one group at a time. Every
  right-hand side is a literal list: no plan value, no model value, no render text enters, which is
  exactly what makes the scan a property of the TREE. -/

theorem callSites_emitTraceReturn (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitTraceReturn pv) =
      [("fail", 1)] := by
  simp only [GenAst.emitTraceReturn, GenAst.emitTraceReturnBlock,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]
theorem callSites_emitLagrange (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitLagrange pv) =
      [("batch_invert", 5), ("fail", 1), ("fail", 1)] := by
  simp only [GenAst.emitLagrange, GenAst.emitLagrangeAt,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]
theorem callSites_emitQuotientLin (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitQuotientLin pv) =
      [] := by
  simp only [GenAst.emitQuotientLin, GenAst.emitQuotientLinAt,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]
theorem callSites_emitHelpers (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitHelpers pv) =
      [("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1),
       ("fail", 1), ("fail", 1)] := by
  simp only [GenAst.emitHelpers, GenAst.emitFail, GenAst.emitScalarInvAt, GenAst.emitTranscriptHelpers, GenAst.emitBatchInvertAt, GenAst.emitEcPairingAt,
    GenAst.emitScalarInv, GenAst.emitTranscriptInit, GenAst.emitCommonWord,
    GenAst.emitCommonUncompressedG1, GenAst.emitSqueezeTo, GenAst.emitBatchInvert,
    GenAst.emitEcPairing, GenAst.pairingScratchOf, GenAst.g1CoordRangeCheck,
    GenAst.modexpFrameStores,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]
theorem callSites_emitAccumulatorHelpers :
    Midfall.LoweringV3.callSitesSs GenAst.emitAccumulatorHelpers =
      [("check_acc_coord_packing", 4), ("load_acc_coord_shifted", 5), ("is_bls_p_minus_one", 2),
       ("load_acc_coord", 5), ("load_acc_coord", 5)] := by
  simp only [GenAst.emitAccumulatorHelpers, GenAst.emitAccumulatorHelpersAt, GenAst.emitLoadAccCoordShifted, GenAst.emitIsBlsPMinusOne, GenAst.emitCheckAccCoordPacking, GenAst.emitLoadAccCoord, GenAst.emitLoadAccPoint,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]

theorem callSites_emitQuotientHelpersAt (pow5 : Bool) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitQuotientHelpersAt pow5) = [] := by
  cases pow5 <;>
    simp only [GenAst.emitQuotientHelpersAt, GenAst.emitQProgramFail, GenAst.emitQPow5,
      GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_emitFinalPairing (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitFinalPairing pv) =
      [("fail", 1), ("ec_pairing", 3)] := by
  cases h : pv.hasAccumulator <;>
    simp only [GenAst.emitFinalPairing, GenAst.emitFinalPairingArms, h, GenAst.emitAccBatch,
      GenAst.accMsmThenAdd,
      GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_emitVkLoading (pv : PlanView) :
    Midfall.LoweringV3.callSitesSs (GenAst.emitVkLoading pv) =
      (if pv.hasAccumulator then
        [("fail", 1), ("fail", 1), ("fail", 1), ("validate_public_accumulator", 2),
         ("fail", 1), ("fail", 1)]
       else [("fail", 1), ("fail", 1), ("fail", 1)]) := by
  cases h : pv.hasAccumulator <;>
    simp only [GenAst.emitVkLoading, GenAst.emitVkLoadingArms, h,
      GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor,
      GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_abiGuardBlock (m : Model) : Midfall.LoweringV3.callSitesSs (abiGuardBlock m) = [] := by
  simp [abiGuardBlock, Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
    Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
    Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_mainGuardBlock : Midfall.LoweringV3.callSitesSs mainGuardBlock = [] := by
  simp [mainGuardBlock, Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
    Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
    Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_mainLocals : Midfall.LoweringV3.callSitesSs mainLocals = [] := by
  simp [mainLocals, Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
    Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
    Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


theorem callSites_wrapperLocals (m : Model) : Midfall.LoweringV3.callSitesSs (wrapperLocals m 0 0) = [] := by
  cases h1 : m.embeddedVk <;> cases h2 : m.quotientExternal <;>
  simp [wrapperLocals, h1, h2, Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
    Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
    Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
    Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var, LoweringV2.lit,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      callSitesSs_append, List.length_cons, List.length_nil, List.length_map,
      List.map_cons, List.map_nil,
      List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.flatten_cons, List.flatten_nil, Nat.zero_add, Nat.reduceAdd, reduceIte,
      Bool.false_eq_true]


/-! ### The function-signature side

  `funSigsOf` is a `filterMap` over the top level. Only the two helper blocks and the quotient
  helper region define functions; every slice is a definition-free block. -/


theorem funSigs_emitHelpers (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitHelpers pv) =
      [("fail", 1), ("scalar_inv", 1), ("transcript_init", 0), ("common_word", 2),
       ("common_uncompressed_g1", 2), ("squeeze_to", 2), ("batch_invert", 5), ("ec_pairing", 3)] := by
  simp [GenAst.emitHelpers, GenAst.emitFail, GenAst.emitScalarInvAt, GenAst.emitTranscriptHelpers,
    GenAst.emitBatchInvertAt, GenAst.emitEcPairingAt, GenAst.emitScalarInv,
    GenAst.emitTranscriptInit, GenAst.emitCommonWord, GenAst.emitCommonUncompressedG1,
    GenAst.emitSqueezeTo, GenAst.emitBatchInvert, GenAst.emitEcPairing, GenAst.pairingScratchOf,
    GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.funSigsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]


theorem funSigs_emitAccumulatorHelpers :
    Midfall.LoweringV3.funSigsOf GenAst.emitAccumulatorHelpers =
      [("load_acc_coord_shifted", 5), ("is_bls_p_minus_one", 2), ("check_acc_coord_packing", 4),
       ("load_acc_coord", 5), ("load_acc_point", 5)] := by
  simp [GenAst.emitAccumulatorHelpers, GenAst.emitAccumulatorHelpersAt,
    GenAst.emitLoadAccCoordShifted, GenAst.emitIsBlsPMinusOne, GenAst.emitCheckAccCoordPacking,
    GenAst.emitLoadAccCoord, GenAst.emitLoadAccPoint, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.funSigsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]


theorem funSigs_emitQuotientHelpersAt (pow5 : Bool) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitQuotientHelpersAt pow5) =
      (if pow5 then [("q_program_fail", 0), ("q_pow5", 1)] else [("q_program_fail", 0)]) := by
  cases pow5 <;>
    simp [GenAst.emitQuotientHelpersAt, GenAst.emitQProgramFail, GenAst.emitQPow5, GenAst.yfun,
      Midfall.LoweringV3.funSigsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]


theorem funSigs_emitFinalPairing (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitFinalPairing pv) = [] := by
  cases h : pv.hasAccumulator <;>
  · apply funSigsOf_eq_nil_of_forall
    intro s hs n ps rs body heq
    subst heq
    simp [GenAst.emitFinalPairing, GenAst.emitFinalPairingArms, GenAst.emitAccBatch,
      GenAst.accMsmThenAdd, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock,
      GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      h] at hs

theorem funSigs_emitTraceReturn (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitTraceReturn pv) = [] := by
  simp [GenAst.emitTraceReturn, GenAst.emitTraceReturnBlock, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

theorem funSigs_emitLagrange (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitLagrange pv) = [] := by
  simp [GenAst.emitLagrange, GenAst.emitLagrangeAt, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

theorem funSigs_emitQuotientLin (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitQuotientLin pv) = [] := by
  simp [GenAst.emitQuotientLin, GenAst.emitQuotientLinAt, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
    Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

theorem funSigs_emitVkLoading (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitVkLoading pv) = [] := by
  cases h : pv.hasAccumulator <;>
    simp [GenAst.emitVkLoading, GenAst.emitVkLoadingArms, h, GenAst.yfun, GenAst.ylet, GenAst.yset, GenAst.ysetN, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

theorem funSigs_emitPcsFromPlan (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitPcsFromPlan pv) = [] := by
  unfold GenAst.emitPcsFromPlan
  split <;> simp [Midfall.LoweringV3.funSigsOf]



theorem topBinders_append_subset {S : List String} {a b : YulBlock}
    (ha : ∀ x ∈ LoweringV2.topBinders a, x ∈ S)
    (hb : ∀ x ∈ LoweringV2.topBinders b, x ∈ S) :
    ∀ x ∈ LoweringV2.topBinders (a ++ b), x ∈ S := by
  intro x hx
  rw [mem_topBinders_append] at hx
  rcases hx with h | h
  · exact ha x h
  · exact hb x h

theorem mem_topBinders_flatten_map_subset {α : Type _} {S : List String} {l : List α}
    {f : α → YulBlock}
    (h : ∀ a ∈ l, ∀ x ∈ LoweringV2.topBinders (f a), x ∈ S) :
    ∀ x ∈ LoweringV2.topBinders (List.flatten (l.map f)), x ∈ S := by
  intro x hx
  rw [mem_topBinders_flatten_map] at hx
  obtain ⟨a, ha, hx⟩ := hx
  exact h a ha x hx

/-! ### The transcript parser's list-mapped binder groups

  `emitTranscriptParserAt` splices two list-mapped families: one per `UserPhase` (a walk loop plus
  one squeeze per challenge) and one per `ProofLookupCommitmentsLayout`. Their binder sets are
  constant per element, which is what the two inductions below record. The final assembly of the
  whole slice over the four shape flags is the remaining child of this group. -/

/-- Every binder name the transcript parser can emit. -/
def parserTopNames : List String :=
  ["buf_len", "proof_cptr", "advice_walk", "lookup_m_walk", "perm_z_walk",
    "lookup_helper_walk", "lookup_z_walk", "trashcan_walk", "quotient_walk"]

theorem parser_phase_binders (ph : UserPhase) :
    ∀ x ∈ LoweringV2.topBinders
      ([GenAst.g1WalkLoop "advice_walk" ph.adviceBytes] ++
        (List.map (fun j => GenAst.yset "buf_len"
          (GenAst.ycall "squeeze_to" [GenAst.yvar "buf_len",
            GenAst.yop Op.add [GenAst.yvar "CHALLENGE_MPTR",
              GenAst.ylit ((ph.challengeOffset + j) * 32)]]))
          (List.range ph.numChallenges))),
      x ∈ parserTopNames := by
  intro x hx
  rw [mem_topBinders_append] at hx
  rcases hx with h1 | h2
  · simp only [LoweringV2.topBinders, GenAst.g1WalkLoop, GenAst.yfor, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, boundOf_forLoop] at h1
    exact absurd h1 (by simp)
  · rw [mem_topBinders_map] at h2
    obtain ⟨j, _, hx⟩ := h2
    simp only [GenAst.yset, boundOf_assign] at hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [parserTopNames]

theorem parser_phases_binders (phases : List UserPhase) :
    ∀ x ∈ LoweringV2.topBinders
      (List.flatten (phases.map (fun ph =>
        [GenAst.g1WalkLoop "advice_walk" ph.adviceBytes] ++
          (List.map (fun j => GenAst.yset "buf_len"
            (GenAst.ycall "squeeze_to" [GenAst.yvar "buf_len",
              GenAst.yop Op.add [GenAst.yvar "CHALLENGE_MPTR",
                GenAst.ylit ((ph.challengeOffset + j) * 32)]]))
            (List.range ph.numChallenges))))),
      x ∈ parserTopNames := by
  apply mem_topBinders_flatten_map_subset
  intro ph _ x hx
  exact parser_phase_binders ph x hx

theorem parser_lookup_binders (lk : ProofLookupCommitmentsLayout) :
    ∀ x ∈ LoweringV2.topBinders
      ([GenAst.g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen] ++
        GenAst.g1WalkBody "lookup_z_walk"),
      x ∈ parserTopNames := by
  intro x hx
  rw [mem_topBinders_append] at hx
  rcases hx with h1 | h2
  · simp only [LoweringV2.topBinders, GenAst.g1WalkLoop, GenAst.yfor, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, boundOf_forLoop] at h1
    exact absurd h1 (by simp)
  · simp [LoweringV2.topBinders, GenAst.g1WalkBody, GenAst.yset, GenAst.yexpr, GenAst.yop,
      GenAst.yvar, GenAst.ylit, GenAst.ycall, Inline.boundOf] at h2
    simp [parserTopNames] at h2 ⊢
    tauto

theorem parser_lookups_binders (lookups : List ProofLookupCommitmentsLayout) :
    ∀ x ∈ LoweringV2.topBinders
      (List.flatten (lookups.map (fun lk =>
        [GenAst.g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen] ++
          GenAst.g1WalkBody "lookup_z_walk"))),
      x ∈ parserTopNames := by
  apply mem_topBinders_flatten_map_subset
  intro lk _ x hx
  exact parser_lookup_binders lk x hx

/-! ## 4. THE COMPOSITION OVER `mainAsmRaw`

  `mainAsmRaw` is the guard, the helper blocks, the two main locals, and the seven slices in
  include order. The lemmas below split each scan at exactly that boundary, so every residual is a
  statement about ONE emitter group. They are the shape the CERT.5 leaves cite: substitute the
  per-group facts of §2-§3 and the numerator's facts, and the composition is a rewrite. -/

/-- The `quotientLin` slice as `mainAsmRaw` splices it: helper definitions, the parsed numerator,
    then the linearization scope. This is the one group whose text is not a tree. -/
def qlinSlice (pv : PlanView) (c : PartialCtx) : YulBlock :=
  GenAst.emitQuotientHelpersAt c.quotientPow5Helper ++ GenAst.emitQuotientNumerator c ++
    GenAst.emitQuotientLin pv

/-- `mainAsmRaw` unfolded to its nine parts. Left-nested like the `foldl` that builds it. -/
theorem mainAsmRaw_decomp (pv : PlanView) (m : Model) :
    mainAsmRaw pv m =
      ((((((mainGuardBlock ++ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers ++ mainLocals)
        ++ GenAst.emitVkLoading pv) ++ GenAst.emitTranscriptParser pv) ++ GenAst.emitLagrange pv)
        ++ qlinSlice pv (partialCtxOfVerifier m)) ++ GenAst.emitPcsFromPlan pv)
        ++ GenAst.emitFinalPairing pv ++ GenAst.emitTraceReturn pv := rfl

/-- The top-level binder scan splits at the same boundaries. -/
theorem topBinders_mainAsmRaw (pv : PlanView) (m : Model) :
    LoweringV2.topBinders (mainAsmRaw pv m) =
      LoweringV2.topBinders (mainGuardBlock ++ GenAst.emitHelpers pv ++
        GenAst.emitAccumulatorHelpers ++ mainLocals) ++
      LoweringV2.topBinders (GenAst.emitVkLoading pv) ++
      LoweringV2.topBinders (GenAst.emitTranscriptParser pv) ++
      LoweringV2.topBinders (GenAst.emitLagrange pv) ++
      LoweringV2.topBinders (qlinSlice pv (partialCtxOfVerifier m)) ++
      LoweringV2.topBinders (GenAst.emitPcsFromPlan pv) ++
      LoweringV2.topBinders (GenAst.emitFinalPairing pv) ++
      LoweringV2.topBinders (GenAst.emitTraceReturn pv) := by
  rw [mainAsmRaw_decomp]
  simp only [topBinders_append, List.append_assoc]

theorem topBinders_qlinSlice (pv : PlanView) (c : PartialCtx) :
    LoweringV2.topBinders (qlinSlice pv c) =
      LoweringV2.topBinders (GenAst.emitQuotientHelpersAt c.quotientPow5Helper) ++
        LoweringV2.topBinders (GenAst.emitQuotientNumerator c) := by
  simp [qlinSlice, topBinders_append, topBinders_emitQuotientLin]

theorem funSigs_mainGuardBlock :
    Midfall.LoweringV3.funSigsOf mainGuardBlock = [] := by
  simp [mainGuardBlock, Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

theorem funSigs_mainLocals :
    Midfall.LoweringV3.funSigsOf mainLocals = [] := by
  simp [mainLocals, Midfall.LoweringV3.funSigsOf, List.filterMap_cons, List.filterMap_nil]

/-- The function-signature table splits the same way; `funSigsOf` of every slice except the
    quotient helpers is empty (`funSigs_*` above), and the numerator's is the residual. -/
theorem funSigsOf_mainAsmRaw (pv : PlanView) (m : Model)
    (hnum : Midfall.LoweringV3.funSigsOf
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)) = [])
    (hparser : Midfall.LoweringV3.funSigsOf (GenAst.emitTranscriptParser pv) = []) :
    Midfall.LoweringV3.funSigsOf (mainAsmRaw pv m) =
      ([("fail", 1), ("scalar_inv", 1), ("transcript_init", 0), ("common_word", 2),
        ("common_uncompressed_g1", 2), ("squeeze_to", 2), ("batch_invert", 5),
        ("ec_pairing", 3)] ++
       [("load_acc_coord_shifted", 5), ("is_bls_p_minus_one", 2),
        ("check_acc_coord_packing", 4), ("load_acc_coord", 5), ("load_acc_point", 5)] ++
       (if (partialCtxOfVerifier m).quotientPow5Helper then
          [("q_program_fail", 0), ("q_pow5", 1)] else [("q_program_fail", 0)])) := by
  rw [mainAsmRaw_decomp]
  simp only [funSigsOf_append, funSigs_emitHelpers, funSigs_emitAccumulatorHelpers,
    funSigs_mainGuardBlock, funSigs_mainLocals,
    funSigs_emitVkLoading, hparser, funSigs_emitLagrange, funSigs_emitPcsFromPlan,
    funSigs_emitFinalPairing, funSigs_emitTraceReturn, funSigs_emitQuotientLin,
    qlinSlice, funSigs_emitQuotientHelpersAt,
    hnum, List.append_nil, List.nil_append]

/-- A list of blocks flattened: `NoWriters` of the concatenation from the parts. -/
theorem NoWriters_flatten (l : List YulBlock) (h : ∀ b ∈ l, NoWriters b) :
    NoWriters l.flatten := by
  induction l with
  | nil => exact ⟨1, rfl⟩
  | cons a as ih =>
      rw [List.flatten_cons]
      exact NoWriters_append (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))

/-- **`NoWriters` COMPOSITION.** One hypothesis per group; the append closure does the rest. -/
theorem noWriters_mainAsmRaw (pv : PlanView) (m : Model)
    (hguard : NoWriters mainGuardBlock)
    (hhelp : NoWriters (GenAst.emitHelpers pv))
    (hacc : NoWriters GenAst.emitAccumulatorHelpers)
    (hloc : NoWriters mainLocals)
    (hvk : NoWriters (GenAst.emitVkLoading pv))
    (hparser : NoWriters (GenAst.emitTranscriptParser pv))
    (hlag : NoWriters (GenAst.emitLagrange pv))
    (hqlin : NoWriters (qlinSlice pv (partialCtxOfVerifier m)))
    (hpcs : NoWriters (GenAst.emitPcsFromPlan pv))
    (hfp : NoWriters (GenAst.emitFinalPairing pv))
    (htr : NoWriters (GenAst.emitTraceReturn pv)) :
    NoWriters (mainAsmRaw pv m) := by
  rw [mainAsmRaw_decomp]
  refine NoWriters_append ?_ htr
  refine NoWriters_append ?_ hfp
  refine NoWriters_append ?_ hpcs
  refine NoWriters_append ?_ hqlin
  refine NoWriters_append ?_ hlag
  refine NoWriters_append ?_ hparser
  refine NoWriters_append ?_ hvk
  refine NoWriters_append ?_ hloc
  refine NoWriters_append ?_ hacc
  exact NoWriters_append hguard hhelp


/-! ### `NoWriters` per emitter group

  The scan inspects constructors only (`Op.isWriter` on the builtin and literal values ignored), so
  every emitter whose statement SHAPE is plan-independent is clean by `rfl`: the fuel is chosen
  above the block's height and the kernel computes the scan to `true`. The two flag-guarded groups
  are split on the flag. -/

theorem noWriters_emitTraceReturn (pv : PlanView) : NoWriters (GenAst.emitTraceReturn pv) :=
  ⟨1000, rfl⟩

theorem noWriters_emitLagrange (pv : PlanView) : NoWriters (GenAst.emitLagrange pv) :=
  ⟨1000, rfl⟩

theorem noWriters_emitQuotientLin (pv : PlanView) : NoWriters (GenAst.emitQuotientLin pv) :=
  ⟨1000, rfl⟩

theorem noWriters_emitHelpers (pv : PlanView) : NoWriters (GenAst.emitHelpers pv) :=
  ⟨4000, rfl⟩

theorem noWriters_emitAccumulatorHelpers : NoWriters GenAst.emitAccumulatorHelpers :=
  ⟨1000, rfl⟩

theorem noWriters_emitQuotientHelpersAt (pow5 : Bool) :
    NoWriters (GenAst.emitQuotientHelpersAt pow5) := by
  cases pow5 <;> exact ⟨1000, rfl⟩

theorem noWriters_mainGuardBlock : NoWriters mainGuardBlock := ⟨100, rfl⟩

theorem noWriters_mainLocals : NoWriters mainLocals := ⟨100, rfl⟩

theorem noWriters_abiGuardBlock (m : Model) : NoWriters (abiGuardBlock m) := ⟨100, rfl⟩

theorem noWriters_wrapperLocals (m : Model) : NoWriters (wrapperLocals m 0 0) := by
  cases h1 : m.embeddedVk <;> cases h2 : m.quotientExternal <;>
    simp [wrapperLocals, h1, h2] <;> exact ⟨100, rfl⟩

theorem noWriters_emitVkLoading (pv : PlanView) : NoWriters (GenAst.emitVkLoading pv) := by
  cases h : pv.hasAccumulator <;>
    first
    | exact ⟨1000, rfl⟩
    | exact ⟨1000, by simp [GenAst.emitVkLoading, GenAst.emitVkLoadingArms, h]; rfl⟩

theorem noWriters_emitFinalPairing (pv : PlanView) : NoWriters (GenAst.emitFinalPairing pv) := by
  cases h : pv.hasAccumulator <;>
    first
    | exact ⟨1000, rfl⟩
    | exact ⟨1000, by
        simp [GenAst.emitFinalPairing, GenAst.emitFinalPairingArms, GenAst.emitAccBatch,
          GenAst.accMsmThenAdd, h]
        rfl⟩

/-- **`NoWriters` OF THE `quotientLin` SLICE**, from the parsed numerator's. -/
theorem noWriters_qlinSlice (pv : PlanView) (c : PartialCtx)
    (hnum : NoWriters (GenAst.emitQuotientNumerator c)) :
    NoWriters (qlinSlice pv c) := by
  rw [qlinSlice]
  exact NoWriters_append (NoWriters_append (noWriters_emitQuotientHelpersAt c.quotientPow5Helper)
    hnum) (noWriters_emitQuotientLin pv)

/-- **`NoWriters` OF `mainAsmRaw`**, with exactly three residual hypotheses: the transcript parser
    (a list-mapped group), the PCS slice (a list-mapped group), and the parsed numerator. -/
theorem noWriters_mainAsmRaw_of (pv : PlanView) (m : Model)
    (hparser : NoWriters (GenAst.emitTranscriptParser pv))
    (hpcs : NoWriters (GenAst.emitPcsFromPlan pv))
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (mainAsmRaw pv m) :=
  noWriters_mainAsmRaw pv m noWriters_mainGuardBlock (noWriters_emitHelpers pv)
    noWriters_emitAccumulatorHelpers noWriters_mainLocals (noWriters_emitVkLoading pv)
    hparser (noWriters_emitLagrange pv) (noWriters_qlinSlice pv _ hnum) hpcs
    (noWriters_emitFinalPairing pv) (noWriters_emitTraceReturn pv)


/-! ## 6. ALL-NAMES ALGEBRA: the scans as Boolean `all`s

  `noShadowProg` is `(boundSs prog).all (not contains)`, `mainClosed` is the same over free names,
  and `callsResolved` starts from `(callSitesSs main).all (sigs.contains ·)`. This section states
  the three name predicates in that `all` form, so that the list-mapped emitters compose by
  `List.all_append` / `List.all_flatMap` and the per-element facts are literal computations. -/

/-- Every top-level binder of `b` is in `S`. -/
def TopNamesOK (S : List String) (b : YulBlock) : Prop :=
  (LoweringV2.topBinders b).all (fun x => S.contains x) = true

/-- Every binder of `b`, at any depth, is in `S`. -/
def BindersOK (S : List String) (b : YulBlock) : Prop :=
  (LoweringV2.boundSs b).all (fun x => S.contains x) = true

/-- Every user call site of `b` is in `S`. -/
def CallsOK (S : List (String × Nat)) (b : YulBlock) : Prop :=
  (Midfall.LoweringV3.callSitesSs b).all (fun c => S.contains c) = true

theorem TopNamesOK_of_forall {S : List String} {b : YulBlock}
    (h : ∀ x ∈ LoweringV2.topBinders b, x ∈ S) : TopNamesOK S b := by
  unfold TopNamesOK
  rw [List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr (h x hx)

theorem BindersOK_of_forall {S : List String} {b : YulBlock}
    (h : ∀ x ∈ LoweringV2.boundSs b, x ∈ S) : BindersOK S b := by
  unfold BindersOK
  rw [List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr (h x hx)

theorem CallsOK_of_forall {S : List (String × Nat)} {b : YulBlock}
    (h : ∀ c ∈ Midfall.LoweringV3.callSitesSs b, c ∈ S) : CallsOK S b := by
  unfold CallsOK
  rw [List.all_eq_true]
  intro c hc
  exact List.contains_iff_mem.mpr (h c hc)

theorem boundSs_map {α : Type _} (l : List α) (g : α → Stmt EVM.Op) :
    LoweringV2.boundSs (l.map g) = l.flatMap (fun a => LoweringV2.boundS (g a)) := by
  induction l with
  | nil => simp [LoweringV2.boundSs]
  | cons a as ih =>
      rw [List.map_cons, LoweringV2.boundSs.eq_2, ih, List.flatMap_cons]

theorem boundSs_flatten_map {α : Type _} (l : List α) (f : α → YulBlock) :
    LoweringV2.boundSs ((l.map f).flatten) =
      l.flatMap (fun a => LoweringV2.boundSs (f a)) := by
  induction l with
  | nil => simp [LoweringV2.boundSs]
  | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, boundSs_append, ih, List.flatMap_cons]

theorem callSitesSs_map {α : Type _} (l : List α) (g : α → Stmt EVM.Op) :
    Midfall.LoweringV3.callSitesSs (l.map g) =
      l.flatMap (fun a => Midfall.LoweringV3.callSitesS (g a)) := by
  induction l with
  | nil => simp [Midfall.LoweringV3.callSitesSs]
  | cons a as ih =>
      rw [List.map_cons, Midfall.LoweringV3.callSitesSs.eq_2, ih, List.flatMap_cons]

theorem callSitesSs_flatten_map {α : Type _} (l : List α) (f : α → YulBlock) :
    Midfall.LoweringV3.callSitesSs ((l.map f).flatten) =
      l.flatMap (fun a => Midfall.LoweringV3.callSitesSs (f a)) := by
  induction l with
  | nil => simp [Midfall.LoweringV3.callSitesSs]
  | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, callSitesSs_append, ih, List.flatMap_cons]

theorem TopNamesOK_append {S : List String} {a b : YulBlock}
    (ha : TopNamesOK S a) (hb : TopNamesOK S b) : TopNamesOK S (a ++ b) := by
  unfold TopNamesOK at *
  rw [topBinders_append, List.all_append, ha, hb]
  rfl

theorem BindersOK_append {S : List String} {a b : YulBlock}
    (ha : BindersOK S a) (hb : BindersOK S b) : BindersOK S (a ++ b) := by
  unfold BindersOK at *
  rw [boundSs_append, List.all_append, ha, hb]
  rfl

theorem CallsOK_append {S : List (String × Nat)} {a b : YulBlock}
    (ha : CallsOK S a) (hb : CallsOK S b) : CallsOK S (a ++ b) := by
  unfold CallsOK at *
  rw [callSitesSs_append, List.all_append, ha, hb]
  rfl

theorem TopNamesOK_flatten_map {α : Type _} {S : List String} {l : List α} {f : α → YulBlock}
    (h : ∀ a ∈ l, TopNamesOK S (f a)) : TopNamesOK S ((l.map f).flatten) := by
  unfold TopNamesOK at *
  rw [topBinders_flatten_map, List.all_flatMap, List.all_eq_true]
  exact h

theorem BindersOK_flatten_map {α : Type _} {S : List String} {l : List α} {f : α → YulBlock}
    (h : ∀ a ∈ l, BindersOK S (f a)) : BindersOK S ((l.map f).flatten) := by
  unfold BindersOK at *
  rw [boundSs_flatten_map, List.all_flatMap, List.all_eq_true]
  exact h

theorem CallsOK_flatten_map {α : Type _} {S : List (String × Nat)} {l : List α}
    {f : α → YulBlock} (h : ∀ a ∈ l, CallsOK S (f a)) :
    CallsOK S ((l.map f).flatten) := by
  unfold CallsOK at *
  rw [callSitesSs_flatten_map, List.all_flatMap, List.all_eq_true]
  exact h

theorem BindersOK_map {α : Type _} {S : List String} {l : List α} {g : α → Stmt EVM.Op}
    (h : ∀ a ∈ l, (LoweringV2.boundS (g a)).all (fun x => S.contains x) = true) :
    BindersOK S (l.map g) := by
  unfold BindersOK
  rw [boundSs_map, List.all_flatMap, List.all_eq_true]
  exact h

theorem CallsOK_map {α : Type _} {S : List (String × Nat)} {l : List α}
    {g : α → Stmt EVM.Op}
    (h : ∀ a ∈ l,
      (Midfall.LoweringV3.callSitesS (g a)).all (fun c => S.contains c) = true) :
    CallsOK S (l.map g) := by
  unfold CallsOK
  rw [callSitesSs_map, List.all_flatMap, List.all_eq_true]
  exact h

theorem NoWriters_map {α : Type _} {l : List α} {g : α → Stmt EVM.Op}
    (h : ∀ a ∈ l, NoWriters [g a]) : NoWriters (l.map g) := by
  induction l with
  | nil => exact ⟨1, rfl⟩
  | cons a as ih =>
      rw [List.map_cons]
      exact NoWriters_append (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))


/-! ## 7. THE TRANSCRIPT-PARSER GROUP, CLOSED

  `emitTranscriptParserAt` is the largest list-mapped group: per `UserPhase` it emits a G1 walk
  loop plus one squeeze per challenge, per `ProofLookupCommitmentsLayout` a helper walk plus the
  z walk, and around them a fixed prologue and four flag-guarded sections. The per-element facts
  are `phase_*`/`lookup_*` below; the assembly splits the five flags and composes through
  `TopNamesOK_append` / `BindersOK_append` / `CallsOK_append` / `NoWriters_append`, with the two
  `flatten (map …)` families handed to their `_flatten_map` lemmas. -/

def parserBinderNames : List String :=
  parserTopNames ++ ["instance_cptr", "instance_cptr_end", "inst_be", "success", "end",
    "eval_buf", "eval"]

def parserCallNames : List (String × Nat) :=
  [("transcript_init", 0), ("common_word", 2), ("common_uncompressed_g1", 2),
   ("squeeze_to", 2), ("fail", 1)]

def phaseBlock (ph : UserPhase) : YulBlock :=
  [GenAst.g1WalkLoop "advice_walk" ph.adviceBytes] ++
    (List.map (fun j => GenAst.yset "buf_len"
      (GenAst.ycall "squeeze_to" [GenAst.yvar "buf_len",
        GenAst.yop Op.add [GenAst.yvar "CHALLENGE_MPTR",
          GenAst.ylit ((ph.challengeOffset + j) * 32)]]))
      (List.range ph.numChallenges))

def lookupBlock (lk : ProofLookupCommitmentsLayout) : YulBlock :=
  [GenAst.g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen] ++ GenAst.g1WalkBody "lookup_z_walk"

/-- A flattened family of blocks: `NoWriters` from the parts. -/
theorem NoWriters_flatten_map {α : Type _} {l : List α} {f : α → YulBlock}
    (h : ∀ a ∈ l, NoWriters (f a)) : NoWriters ((l.map f).flatten) := by
  apply NoWriters_flatten
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact h a ha

theorem phase_top (ph : UserPhase) : TopNamesOK parserTopNames (phaseBlock ph) := by
  apply TopNamesOK_of_forall
  unfold phaseBlock
  intro x hx
  rw [topBinders_append] at hx
  rcases List.mem_append.mp hx with h | h
  · rw [topBinders_singleton] at h
    simp [GenAst.g1WalkLoop, GenAst.yfor, boundOf_forLoop] at h
  · rw [topBinders_map] at h
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    simp [GenAst.yset, boundOf_assign, parserTopNames] at hj
    subst hj
    simp [parserTopNames]

theorem lookup_top (lk : ProofLookupCommitmentsLayout) :
    TopNamesOK parserTopNames (lookupBlock lk) := by
  apply TopNamesOK_of_forall
  unfold lookupBlock
  intro x hx
  rw [topBinders_append] at hx
  rcases List.mem_append.mp hx with h | h
  · rw [topBinders_singleton] at h
    simp [GenAst.g1WalkLoop, GenAst.yfor, boundOf_forLoop] at h
  · simp [LoweringV2.topBinders, GenAst.g1WalkBody, GenAst.yset, GenAst.yexpr, GenAst.yop,
      GenAst.yvar, GenAst.ylit, GenAst.ycall, boundOf_assign, boundOf_exprStmt,
      List.mem_append, List.mem_singleton, parserTopNames] at h
    rcases h with h | h | h <;> subst h <;> simp [parserTopNames]

theorem phase_binders (ph : UserPhase) : BindersOK parserBinderNames (phaseBlock ph) := by
  apply BindersOK_of_forall
  unfold phaseBlock
  intro x hx
  rw [boundSs_append] at hx
  rcases List.mem_append.mp hx with h | h
  · have hl : LoweringV2.boundSs [GenAst.g1WalkLoop "advice_walk" ph.adviceBytes]
        = ["end", "buf_len", "advice_walk", "proof_cptr"] := by
      simp only [LoweringV2.boundSs.eq_2, LoweringV2.boundSs.eq_1, LoweringV2.boundS.eq_1,
        GenAst.g1WalkLoop, GenAst.yfor, GenAst.g1WalkBody, GenAst.ylet,
        LoweringV2.boundS.eq_3, LoweringV2.boundS.eq_5, LoweringV2.boundS.eq_9,
        LoweringV2.boundS.eq_10, LoweringV2.boundE, GenAst.yset, GenAst.yexpr,
        GenAst.ycall, GenAst.yvar, GenAst.yop, GenAst.ylit, List.append_nil,
        List.nil_append, List.cons_append]
    rw [hl] at h
    simp [parserBinderNames, parserTopNames] at h ⊢
    tauto
  · rw [boundSs_map] at h
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    simp [GenAst.yset, Midfall.LoweringV2.boundS, Midfall.LoweringV2.boundE] at hj
    rcases hj with rfl | hj <;> simp_all [parserBinderNames, parserTopNames,
      Midfall.LoweringV2.boundE]

theorem lookup_binders (lk : ProofLookupCommitmentsLayout) :
    BindersOK parserBinderNames (lookupBlock lk) := by
  apply BindersOK_of_forall
  unfold lookupBlock
  intro x hx
  rw [boundSs_append] at hx
  rcases List.mem_append.mp hx with h | h
  · have hl : LoweringV2.boundSs [GenAst.g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen]
        = ["end", "buf_len", "lookup_helper_walk", "proof_cptr"] := by
      simp only [LoweringV2.boundSs.eq_2, LoweringV2.boundSs.eq_1, LoweringV2.boundS.eq_1,
        GenAst.g1WalkLoop, GenAst.yfor, GenAst.g1WalkBody, GenAst.ylet,
        LoweringV2.boundS.eq_3, LoweringV2.boundS.eq_5, LoweringV2.boundS.eq_9,
        LoweringV2.boundS.eq_10, LoweringV2.boundE, GenAst.yset, GenAst.yexpr,
        GenAst.ycall, GenAst.yvar, GenAst.yop, GenAst.ylit, List.append_nil,
        List.nil_append, List.cons_append]
    rw [hl] at h
    simp [parserBinderNames, parserTopNames] at h ⊢
    tauto
  · simp [LoweringV2.boundSs, LoweringV2.boundS, LoweringV2.boundE, GenAst.g1WalkBody,
      GenAst.yset, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
      List.mem_append, List.mem_singleton, parserBinderNames, parserTopNames] at h
    simp [parserBinderNames, parserTopNames] at h ⊢
    tauto

theorem phase_calls (ph : UserPhase) : CallsOK parserCallNames (phaseBlock ph) := by
  apply CallsOK_of_forall
  unfold phaseBlock
  intro c hc
  rw [callSitesSs_append] at hc
  rcases List.mem_append.mp hc with h | h
  · have hl : Midfall.LoweringV3.callSitesSs
        [GenAst.g1WalkLoop "advice_walk" ph.adviceBytes] = [("common_uncompressed_g1", 2)] := by
      simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
        Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_3,
        Midfall.LoweringV3.callSitesS.eq_4, Midfall.LoweringV3.callSitesS.eq_5,
        Midfall.LoweringV3.callSitesS.eq_6, Midfall.LoweringV3.callSitesS.eq_7,
        Midfall.LoweringV3.callSitesS.eq_8, Midfall.LoweringV3.callSitesS.eq_9,
        Midfall.LoweringV3.callSitesS.eq_10, Midfall.LoweringV3.callSitesE.eq_1,
        Midfall.LoweringV3.callSitesE.eq_2, Midfall.LoweringV3.callSitesE.eq_3,
        callSitesE_lit, callSitesE_var, Midfall.LoweringV3.callSitesEs.eq_1,
        Midfall.LoweringV3.callSitesEs.eq_2, GenAst.g1WalkLoop, GenAst.yfor,
        GenAst.g1WalkBody, GenAst.ylet, GenAst.yset, GenAst.yexpr, GenAst.ycall,
        GenAst.yvar, GenAst.yop, GenAst.ylit, List.append_nil, List.nil_append,
        List.cons_append, List.length_cons, List.length_nil, List.length_map,
        List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
    rw [hl] at h
    simp [parserCallNames] at h ⊢
    tauto
  · rw [callSitesSs_map] at h
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    simp [GenAst.yset, GenAst.ycall, GenAst.yvar, GenAst.yop, GenAst.ylit,
      Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
      Midfall.LoweringV3.callSitesEs, parserCallNames] at hj
    subst hj
    simp [parserCallNames]

theorem lookup_calls (lk : ProofLookupCommitmentsLayout) :
    CallsOK parserCallNames (lookupBlock lk) := by
  apply CallsOK_of_forall
  unfold lookupBlock
  intro c hc
  rw [callSitesSs_append] at hc
  rcases List.mem_append.mp hc with h | h
  · have hl : Midfall.LoweringV3.callSitesSs
        [GenAst.g1WalkLoop "lookup_helper_walk" lk.helpers.byteLen]
        = [("common_uncompressed_g1", 2)] := by
      simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
        Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_3,
        Midfall.LoweringV3.callSitesS.eq_4, Midfall.LoweringV3.callSitesS.eq_5,
        Midfall.LoweringV3.callSitesS.eq_6, Midfall.LoweringV3.callSitesS.eq_7,
        Midfall.LoweringV3.callSitesS.eq_8, Midfall.LoweringV3.callSitesS.eq_9,
        Midfall.LoweringV3.callSitesS.eq_10, Midfall.LoweringV3.callSitesE.eq_1,
        Midfall.LoweringV3.callSitesE.eq_2, Midfall.LoweringV3.callSitesE.eq_3,
        callSitesE_lit, callSitesE_var, Midfall.LoweringV3.callSitesEs.eq_1,
        Midfall.LoweringV3.callSitesEs.eq_2, GenAst.g1WalkLoop, GenAst.yfor,
        GenAst.g1WalkBody, GenAst.ylet, GenAst.yset, GenAst.yexpr, GenAst.ycall,
        GenAst.yvar, GenAst.yop, GenAst.ylit, List.append_nil, List.nil_append,
        List.cons_append, List.length_cons, List.length_nil, List.length_map,
        List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
    rw [hl] at h
    simp [parserCallNames] at h ⊢
    tauto
  · simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
      Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
      callSitesE_var, GenAst.g1WalkBody, GenAst.yset, GenAst.yexpr, GenAst.ycall,
      GenAst.yvar, GenAst.yop, GenAst.ylit, List.mem_append, List.mem_singleton,
      parserCallNames] at h
    simp [parserCallNames] at h ⊢
    tauto

theorem phase_noWriters (ph : UserPhase) : NoWriters (phaseBlock ph) := by
  unfold phaseBlock
  apply NoWriters_append
  · exact ⟨100, rfl⟩
  · apply NoWriters_map
    intro j _
    exact ⟨100, rfl⟩

theorem lookup_noWriters (lk : ProofLookupCommitmentsLayout) :
    NoWriters (lookupBlock lk) := by
  unfold lookupBlock
  exact NoWriters_append ⟨100, rfl⟩ ⟨100, rfl⟩

set_option maxHeartbeats 1000000 in
theorem parser_topOK (pv : PlanView) :
    TopNamesOK parserTopNames (GenAst.emitTranscriptParser pv) := by
  unfold GenAst.emitTranscriptParser GenAst.emitTranscriptParserAt
  dsimp only
  by_cases h1 : (pv.numLookups != 0) = true <;>
  by_cases h2 : (pv.numPermutationZs != 0) = true <;>
  by_cases h3 : (pv.lookupHPlusAcc != 0) = true <;>
  by_cases h4 : (pv.numTrashcans != 0) = true <;>
  by_cases h5 : pv.truncatedChallenges = true <;>
  all_goals try simp only [h1, h2, h3, h4, h5, if_true, if_false]
  all_goals
    repeat' first
      | apply TopNamesOK_append
      | apply TopNamesOK_flatten_map
      | (intro a _; exact phase_top a)
      | (intro a _; exact lookup_top a)
      | (unfold TopNamesOK; rfl)


set_option maxHeartbeats 1000000 in
theorem parser_bindersOK (pv : PlanView) :
    BindersOK parserBinderNames (GenAst.emitTranscriptParser pv) := by
  unfold GenAst.emitTranscriptParser GenAst.emitTranscriptParserAt
  dsimp only
  by_cases h1 : (pv.numLookups != 0) = true <;>
  by_cases h2 : (pv.numPermutationZs != 0) = true <;>
  by_cases h3 : (pv.lookupHPlusAcc != 0) = true <;>
  by_cases h4 : (pv.numTrashcans != 0) = true <;>
  by_cases h5 : pv.truncatedChallenges = true <;>
  all_goals try simp only [h1, h2, h3, h4, h5, if_true, if_false]
  all_goals
    repeat' first
      | apply BindersOK_append
      | apply BindersOK_flatten_map
      | (intro a _; exact phase_binders a)
      | (intro a _; exact lookup_binders a)
      | (unfold BindersOK
         simp [LoweringV2.boundSs, LoweringV2.boundS, LoweringV2.boundE, GenAst.ylet,
           GenAst.yset, GenAst.yblock, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
           GenAst.yvar, GenAst.ylit, GenAst.ycall, GenAst.g1WalkLoop, GenAst.g1WalkBody,
           GenAst.g1AbsorbCopy, parserBinderNames, parserTopNames])

set_option maxHeartbeats 1000000 in
theorem parser_callsOK (pv : PlanView) :
    CallsOK parserCallNames (GenAst.emitTranscriptParser pv) := by
  unfold GenAst.emitTranscriptParser GenAst.emitTranscriptParserAt
  dsimp only
  by_cases h1 : (pv.numLookups != 0) = true <;>
  by_cases h2 : (pv.numPermutationZs != 0) = true <;>
  by_cases h3 : (pv.lookupHPlusAcc != 0) = true <;>
  by_cases h4 : (pv.numTrashcans != 0) = true <;>
  by_cases h5 : pv.truncatedChallenges = true <;>
  all_goals try simp only [h1, h2, h3, h4, h5, if_true, if_false]
  all_goals
    repeat' first
      | apply CallsOK_append
      | apply CallsOK_flatten_map
      | (intro a _; exact phase_calls a)
      | (intro a _; exact lookup_calls a)
      | (unfold CallsOK
         simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
           Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
           callSitesE_var, GenAst.ylet, GenAst.yset, GenAst.yblock, GenAst.yfor, GenAst.yif,
           GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
           GenAst.g1WalkLoop, GenAst.g1WalkBody, GenAst.g1AbsorbCopy, parserCallNames])

set_option maxHeartbeats 1000000 in
theorem parser_noWriters (pv : PlanView) :
    NoWriters (GenAst.emitTranscriptParser pv) := by
  unfold GenAst.emitTranscriptParser GenAst.emitTranscriptParserAt
  dsimp only
  by_cases h1 : (pv.numLookups != 0) = true <;>
  by_cases h2 : (pv.numPermutationZs != 0) = true <;>
  by_cases h3 : (pv.lookupHPlusAcc != 0) = true <;>
  by_cases h4 : (pv.numTrashcans != 0) = true <;>
  by_cases h5 : pv.truncatedChallenges = true <;>
  all_goals try simp only [h1, h2, h3, h4, h5, if_true, if_false]
  all_goals
    repeat' first
      | apply NoWriters_append
      | apply NoWriters_flatten_map
      | (intro a _; exact phase_noWriters a)
      | (intro a _; exact lookup_noWriters a)
      | (apply NoWriters_map; intro a _; exact ⟨100, rfl⟩)
      | exact ⟨1000, rfl⟩



/-! ### No function definitions in the parser slice -/

def NoFunDefIn (b : YulBlock) : Prop :=
  ∀ s ∈ b, ∀ (n : String) (ps rs : List String) (body : YulBlock), s ≠ Stmt.funDef n ps rs body

theorem NoFunDefIn_append {a b : YulBlock} (ha : NoFunDefIn a) (hb : NoFunDefIn b) :
    NoFunDefIn (a ++ b) := by
  intro s hs n ps rs body heq
  rw [heq] at hs
  rw [List.mem_append] at hs
  rcases hs with h | h
  · exact ha _ h _ _ _ _ rfl
  · exact hb _ h _ _ _ _ rfl

theorem NoFunDefIn_flatten_map {α : Type _} {l : List α} {f : α → YulBlock}
    (h : ∀ a ∈ l, NoFunDefIn (f a)) : NoFunDefIn ((l.map f).flatten) := by
  intro s hs n ps rs body heq
  rw [heq] at hs
  rw [List.mem_flatten] at hs
  obtain ⟨b, hb, hsb⟩ := hs
  rw [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact h a ha _ hsb _ _ _ _ rfl

theorem phase_noFun (ph : UserPhase) : NoFunDefIn (phaseBlock ph) := by
  intro s hs n ps rs body heq
  rw [heq] at hs
  unfold phaseBlock at hs
  rw [List.mem_append] at hs
  rcases hs with h | h
  · simp [GenAst.g1WalkLoop, GenAst.yfor] at h
  · rw [List.mem_map] at h
    obtain ⟨j, _, h⟩ := h
    simp [GenAst.yset] at h

theorem lookup_noFun (lk : ProofLookupCommitmentsLayout) : NoFunDefIn (lookupBlock lk) := by
  intro s hs n ps rs body heq
  rw [heq] at hs
  unfold lookupBlock at hs
  rw [List.mem_append] at hs
  rcases hs with h | h
  · simp [GenAst.g1WalkLoop, GenAst.yfor] at h
  · simp [GenAst.g1WalkBody, GenAst.yset, GenAst.yexpr, GenAst.ycall, GenAst.yvar,
      GenAst.yop, GenAst.ylit] at h

set_option maxHeartbeats 1000000 in
theorem funSigs_emitTranscriptParser (pv : PlanView) :
    Midfall.LoweringV3.funSigsOf (GenAst.emitTranscriptParser pv) = [] := by
  rw [Midfall.LoweringV3.funSigsOf, List.filterMap_eq_nil_iff]
  have h : NoFunDefIn (GenAst.emitTranscriptParser pv) := by
    unfold GenAst.emitTranscriptParser GenAst.emitTranscriptParserAt
    dsimp only
    by_cases h1 : (pv.numLookups != 0) = true <;>
    by_cases h2 : (pv.numPermutationZs != 0) = true <;>
    by_cases h3 : (pv.lookupHPlusAcc != 0) = true <;>
    by_cases h4 : (pv.numTrashcans != 0) = true <;>
    by_cases h5 : pv.truncatedChallenges = true <;>
    all_goals try simp only [h1, h2, h3, h4, h5, if_true, if_false]
    all_goals
      repeat' first
        | apply NoFunDefIn_append
        | apply NoFunDefIn_flatten_map
        | (intro a _; exact phase_noFun a)
        | (intro a _; exact lookup_noFun a)
        | (intro s hs n ps rs body heq
           rw [heq] at hs
           simp [GenAst.ylet, GenAst.yset, GenAst.yblock, GenAst.yfor, GenAst.yif,
             GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, GenAst.ycall,
             GenAst.g1WalkLoop, GenAst.g1WalkBody, GenAst.g1AbsorbCopy] at hs)
  intro s hs
  cases s with
  | funDef n ps rs body => exact absurd rfl (h _ hs n ps rs body)
  | _ => rfl



/-! ## 8. `callsResolved` OF `mainAsmRaw`, CONDITIONAL ON THE TWO RESIDUALS

  Every group's call sites are now tabulated: the fixed groups exactly, the transcript parser by
  `parser_callsOK`, the numerator and the PCS slice by hypothesis. `mainSigSet` is the function
  table `funSigsOf (mainAsmRaw pv m)` (proved equal in §4 once the numerator defines nothing).
  The hypotheses are the FIRST blocker of §5 (the numerator) and the second list-mapped group
  (PCS, whose call sites are `scalar_inv` only). `callsResolved_of` then closes the scan. -/

theorem CallsOK_nil (S : List (String × Nat)) : CallsOK S [] := by
  unfold CallsOK
  simp [Midfall.LoweringV3.callSitesSs]

theorem CallsOK_mono {S T : List (String × Nat)} {b : YulBlock}
    (h : CallsOK S b) (hsub : ∀ c ∈ S, c ∈ T) : CallsOK T b := by
  unfold CallsOK at *
  rw [List.all_eq_true] at h ⊢
  intro c hc
  exact List.contains_iff_mem.mpr (hsub c (List.contains_iff_mem.mp (h c hc)))

theorem CallsOK_of_callSites_eq {S T : List (String × Nat)} {b : YulBlock}
    (h : Midfall.LoweringV3.callSitesSs b = T) (hT : ∀ c ∈ T, c ∈ S) : CallsOK S b := by
  unfold CallsOK
  rw [h, List.all_eq_true]
  intro c hc
  exact List.contains_iff_mem.mpr (hT c hc)

def mainSigSet (c : PartialCtx) : List (String × Nat) :=
  [("fail", 1), ("scalar_inv", 1), ("transcript_init", 0), ("common_word", 2),
   ("common_uncompressed_g1", 2), ("squeeze_to", 2), ("batch_invert", 5),
   ("ec_pairing", 3)] ++
  [("load_acc_coord_shifted", 5), ("is_bls_p_minus_one", 2), ("check_acc_coord_packing", 4),
   ("load_acc_coord", 5), ("load_acc_point", 5)] ++
  (if c.quotientPow5Helper then [("q_program_fail", 0), ("q_pow5", 1)]
   else [("q_program_fail", 0)])


example (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitTraceReturn pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1)])
  · exact callSites_emitTraceReturn pv
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [mainSigSet]

example (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitLagrange pv) := by
  apply CallsOK_of_callSites_eq (T := [("batch_invert", 5), ("fail", 1), ("fail", 1)])
  · exact callSites_emitLagrange pv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals simp [mainSigSet]

example (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitFinalPairing pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1), ("ec_pairing", 3)])
  · exact callSites_emitFinalPairing pv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    all_goals simp [mainSigSet]

example (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitQuotientLin pv) :=
  CallsOK_of_callSites_eq (callSites_emitQuotientLin pv) (by simp)

example (pv : PlanView) (c : PartialCtx) (hacc : pv.hasAccumulator = false) :
    CallsOK (mainSigSet c) (GenAst.emitVkLoading pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1), ("fail", 1), ("fail", 1)])
  · rw [callSites_emitVkLoading, hacc]; rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals simp [mainSigSet]


theorem callsOK_helpers (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitHelpers pv) := by
  apply CallsOK_of_callSites_eq (T :=
    [("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1),
     ("fail", 1), ("fail", 1), ("fail", 1), ("fail", 1)])
  · exact callSites_emitHelpers pv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [mainSigSet]

theorem callsOK_acc (c : PartialCtx) :
    CallsOK (mainSigSet c) GenAst.emitAccumulatorHelpers := by
  apply CallsOK_of_callSites_eq (T :=
    [("check_acc_coord_packing", 4), ("load_acc_coord_shifted", 5), ("is_bls_p_minus_one", 2),
     ("load_acc_coord", 5), ("load_acc_coord", 5)])
  · exact callSites_emitAccumulatorHelpers
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals simp [mainSigSet]

theorem callsOK_parser (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitTranscriptParser pv) :=
  CallsOK_mono (parser_callsOK pv) (by
    intro x hx
    simp only [parserCallNames, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals simp [mainSigSet])



theorem callsOK_trace (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitTraceReturn pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1)])
  · exact callSites_emitTraceReturn pv
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [mainSigSet]

theorem callsOK_fp (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitFinalPairing pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1), ("ec_pairing", 3)])
  · exact callSites_emitFinalPairing pv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [mainSigSet]

theorem callsOK_lagrange (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitLagrange pv) := by
  apply CallsOK_of_callSites_eq (T := [("batch_invert", 5), ("fail", 1), ("fail", 1)])
  · exact callSites_emitLagrange pv
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [mainSigSet]

theorem callsOK_qlin (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitQuotientLin pv) :=
  CallsOK_of_callSites_eq (callSites_emitQuotientLin pv) (by simp)

theorem callsOK_qhelpers (pv : PlanView) (c : PartialCtx) :
    CallsOK (mainSigSet c) (GenAst.emitQuotientHelpersAt c.quotientPow5Helper) := by
  apply CallsOK_of_callSites_eq (callSites_emitQuotientHelpersAt c.quotientPow5Helper)
  intro x hx; simp at hx

theorem callsOK_vk (pv : PlanView) (c : PartialCtx) (hacc : pv.hasAccumulator = false) :
    CallsOK (mainSigSet c) (GenAst.emitVkLoading pv) := by
  apply CallsOK_of_callSites_eq (T := [("fail", 1), ("fail", 1), ("fail", 1)])
  · rw [callSites_emitVkLoading, hacc]; rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [mainSigSet]

theorem callsOK_mainGuard (c : PartialCtx) :
    CallsOK (mainSigSet c) mainGuardBlock :=
  CallsOK_of_callSites_eq callSites_mainGuardBlock (by simp)

theorem callsOK_mainLocals (c : PartialCtx) :
    CallsOK (mainSigSet c) mainLocals :=
  CallsOK_of_callSites_eq callSites_mainLocals (by simp)

theorem callsOK_mainAsmRaw (pv : PlanView) (m : Model) (hacc : pv.hasAccumulator = false)
    (hnum : CallsOK (mainSigSet (partialCtxOfVerifier m))
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)))
    (hpcs : CallsOK (mainSigSet (partialCtxOfVerifier m)) (GenAst.emitPcsFromPlan pv)) :
    CallsOK (mainSigSet (partialCtxOfVerifier m)) (mainAsmRaw pv m) := by
  have hq : CallsOK (mainSigSet (partialCtxOfVerifier m)) (qlinSlice pv (partialCtxOfVerifier m)) := by
    change CallsOK (mainSigSet (partialCtxOfVerifier m))
      (GenAst.emitQuotientHelpersAt (partialCtxOfVerifier m).quotientPow5Helper ++
        GenAst.emitQuotientNumerator (partialCtxOfVerifier m) ++ GenAst.emitQuotientLin pv)
    exact CallsOK_append (CallsOK_append (callsOK_qhelpers pv _) hnum) (callsOK_qlin pv _)
  rw [mainAsmRaw_decomp]
  exact CallsOK_append
    (CallsOK_append
      (CallsOK_append
        (CallsOK_append
          (CallsOK_append
            (CallsOK_append
              (CallsOK_append
                (CallsOK_append
                  (CallsOK_append (CallsOK_append (callsOK_mainGuard _) (callsOK_helpers pv _))
                    (callsOK_acc _))
                  (callsOK_mainLocals _)) (callsOK_vk pv _ hacc)) (callsOK_parser pv _))
              (callsOK_lagrange pv _)) hq) hpcs) (callsOK_fp pv _))
    (callsOK_trace pv _)


theorem callsResolved_mainAsmRaw_of (pv : PlanView) (m : Model)
    (hacc : pv.hasAccumulator = false)
    (hnumSigs : Midfall.LoweringV3.funSigsOf
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)) = [])
    (hnumCalls : CallsOK (mainSigSet (partialCtxOfVerifier m))
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)))
    (hpcsCalls : CallsOK (mainSigSet (partialCtxOfVerifier m)) (GenAst.emitPcsFromPlan pv)) :
    Midfall.LoweringV3.callsResolved (mainAsmRaw pv m) = true := by
  have hsigs : Midfall.LoweringV3.funSigsOf (mainAsmRaw pv m) =
      mainSigSet (partialCtxOfVerifier m) :=
    funSigsOf_mainAsmRaw pv m hnumSigs (funSigs_emitTranscriptParser pv)
  have hcalls : ∀ c ∈ Midfall.LoweringV3.callSitesSs (mainAsmRaw pv m),
      (Midfall.LoweringV3.funSigsOf (mainAsmRaw pv m)).contains c = true := by
    have h := callsOK_mainAsmRaw pv m hacc hnumCalls hpcsCalls
    unfold CallsOK at h
    rw [List.all_eq_true] at h
    intro c hc
    rw [hsigs]
    exact h c (by simpa [hsigs] using hc)
  refine callsResolved_of hcalls ?_ ?_
  · rw [hsigs]
    intro s hs
    have hall : (mainSigSet (partialCtxOfVerifier m)).all
        (fun s => (EVM.parse s.1).isNone) = true := by
      cases hp : (partialCtxOfVerifier m).quotientPow5Helper <;>
        simp [mainSigSet, hp] <;> decide
    exact List.all_eq_true.mp hall s hs
  · rw [hsigs]
    have hnd : ((mainSigSet (partialCtxOfVerifier m)).map Prod.fst).Nodup := by
      cases hp : (partialCtxOfVerifier m).quotientPow5Helper <;>
        simp [mainSigSet, hp]
    exact hnd



/-! ## 9. `noShadowCore` (v3_noShadow), CONDITIONAL ON THE CONSTANT-NAME AND NUMERATOR RESIDUALS

  `TopAvoids C b` is `noShadowCore`'s per-block predicate: every top-level binder of `b` has a
  name that `C` (a constant table, compared by name) does not contain. The fixed groups are
  discharged from their §2 tables plus ONE hypothesis `hS` on the finite name list
  `fixedTopNames`; the parser is discharged from `parser_topOK`; the PCS slice binds nothing at
  the top level. What remains is exactly the two blockers: the wrapper locals `vk` /
  `quotientEvaluator` (a `constTableOf` fact) and the parsed numerator's top-level binders. -/

def TopAvoids (C : List (String × Nat)) (b : YulBlock) : Prop :=
  (LoweringV2.topBinders b).all (fun x => !((C.map Prod.fst).contains x)) = true

theorem TopAvoids_append {C} {a b} (ha : TopAvoids C a) (hb : TopAvoids C b) :
    TopAvoids C (a ++ b) := by
  unfold TopAvoids at *
  rw [topBinders_append, List.all_append, ha, hb]; rfl

theorem TopAvoids_nil (C : List (String × Nat)) : TopAvoids C [] := by
  unfold TopAvoids; rw [topBinders, List.flatMap_nil]; rfl

theorem TopAvoids_of_TopNamesOK {C S b} (h : TopNamesOK S b)
    (hS : ∀ x ∈ S, ((C.map Prod.fst).contains x) = false) : TopAvoids C b := by
  unfold TopNamesOK at h
  unfold TopAvoids
  rw [List.all_eq_true] at h ⊢
  intro x hx
  have hmem : x ∈ S := List.contains_iff_mem.mp (h x hx)
  rw [hS x hmem]; rfl

theorem TopNamesOK_mono {S T : List String} {b : YulBlock}
    (h : TopNamesOK S b) (hsub : ∀ x ∈ S, x ∈ T) : TopNamesOK T b := by
  unfold TopNamesOK at *
  rw [List.all_eq_true] at h ⊢
  intro x hx
  exact List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp (h x hx)))

theorem TopNamesOK_of_eq {S T : List String} {b : YulBlock}
    (h : LoweringV2.topBinders b = T) (hT : ∀ x ∈ T, x ∈ S) : TopNamesOK S b := by
  unfold TopNamesOK
  rw [h, List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr (hT x hx)

def fixedTopNames : List String :=
  helpersTopNames ++ accumulatorTopNames ++ parserTopNames ++
  ["r", "success", "acc_precompile_failed", "lagrange_precompile_failed", "x", "z"]

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitHelpers pv) := by
  apply TopNamesOK_of_eq (T := helpersTopNames)
  · exact topBinders_emitHelpers pv
  · intro x hx
    rw [fixedTopNames]; simp only [List.mem_append]; tauto

example : TopNamesOK fixedTopNames GenAst.emitAccumulatorHelpers := by
  apply TopNamesOK_of_eq (T := accumulatorTopNames)
  · exact topBinders_emitAccumulatorHelpers
  · intro x hx
    rw [fixedTopNames]; simp only [List.mem_append]; tauto

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitLagrange pv) := by
  apply TopNamesOK_of_eq (T := ["lagrange_precompile_failed"])
  · exact topBinders_emitLagrange pv
  · intro x hx; simp at hx; subst hx; simp [fixedTopNames]

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitTranscriptParser pv) :=
  TopNamesOK_mono (parser_topOK pv) (by
    intro x hx
    rw [fixedTopNames]; simp only [List.mem_append]; tauto)

example (pv : PlanView) (hacc : pv.hasAccumulator = false) :
    TopNamesOK fixedTopNames (GenAst.emitVkLoading pv) := by
  apply TopNamesOK_of_eq (T := [])
  · rw [topBinders_emitVkLoading, hacc]; rfl
  · intro x hx; simp at hx

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitFinalPairing pv) := by
  apply TopNamesOK_of_eq (T := ["success"])
  · exact topBinders_emitFinalPairing pv
  · intro x hx; simp at hx; subst hx; simp [fixedTopNames]

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitTraceReturn pv) := by
  apply TopNamesOK_of_eq (T := [])
  · exact topBinders_emitTraceReturn pv
  · intro x hx; simp at hx

example (pv : PlanView) : TopNamesOK fixedTopNames (GenAst.emitQuotientLin pv) := by
  apply TopNamesOK_of_eq (T := [])
  · exact topBinders_emitQuotientLin pv
  · intro x hx; simp at hx

example (pv : PlanView) (c : PartialCtx) :
    TopNamesOK fixedTopNames (GenAst.emitQuotientHelpersAt c.quotientPow5Helper) := by
  apply TopNamesOK_of_eq (T := (if c.quotientPow5Helper then ["x", "z"] else []))
  · exact topBinders_emitQuotientHelpersAt c.quotientPow5Helper
  · intro x hx
    by_cases hp : c.quotientPow5Helper
    · simp [hp] at hx
      rcases hx with rfl | rfl <;> simp [fixedTopNames] <;> tauto
    · simp [hp] at hx



theorem TopAvoids_mainGuard (C : List (String × Nat)) : TopAvoids C mainGuardBlock :=
  TopAvoids_nil C

theorem TopAvoids_mainLocals (C : List (String × Nat))
    (hS : ∀ x ∈ fixedTopNames, ((C.map Prod.fst).contains x) = false) :
    TopAvoids C mainLocals := by
  unfold TopAvoids
  rw [topBinders_mainLocals, List.all_eq_true]
  intro x hx
  simp at hx
  rcases hx with rfl | rfl
  · rw [hS "r" (by simp [fixedTopNames])]; rfl
  · rw [hS "success" (by simp [fixedTopNames])]; rfl

theorem TopAvoids_emitPcsFromPlan (C : List (String × Nat)) (pv : PlanView) :
    TopAvoids C (GenAst.emitPcsFromPlan pv) := by
  unfold TopAvoids; rw [topBinders_emitPcsFromPlan]; rfl

theorem TopAvoids_emitTraceReturn (C : List (String × Nat)) (pv : PlanView) :
    TopAvoids C (GenAst.emitTraceReturn pv) := by
  unfold TopAvoids; rw [topBinders_emitTraceReturn]; rfl

theorem TopAvoids_abiGuardBlock (C : List (String × Nat)) (m : Model) :
    TopAvoids C (abiGuardBlock m) := by
  unfold TopAvoids; rw [topBinders_abiGuardBlock]; rfl

theorem topAvoids_parser {C} (pv : PlanView)
    (hS : ∀ x ∈ fixedTopNames, ((C.map Prod.fst).contains x) = false) :
    TopAvoids C (GenAst.emitTranscriptParser pv) :=
  TopAvoids_of_TopNamesOK (TopNamesOK_mono (parser_topOK pv) (by
    intro x hx; rw [fixedTopNames]; simp only [List.mem_append]; tauto)) hS

theorem TopAvoids_mainAsmRaw_of (pv : PlanView) (m : Model)
    (hacc : pv.hasAccumulator = false)
    (hS : ∀ x ∈ fixedTopNames, (((constTableOf m).map Prod.fst).contains x) = false)
    (hnum : TopAvoids (constTableOf m) (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    TopAvoids (constTableOf m) (mainAsmRaw pv m) := by
  have hH : TopAvoids (constTableOf m) (GenAst.emitHelpers pv) :=
    TopAvoids_of_TopNamesOK (TopNamesOK_of_eq (topBinders_emitHelpers pv) (by
      intro x hx; rw [fixedTopNames]; simp only [List.mem_append]; tauto)) hS
  have hA : TopAvoids (constTableOf m) GenAst.emitAccumulatorHelpers :=
    TopAvoids_of_TopNamesOK (TopNamesOK_of_eq (topBinders_emitAccumulatorHelpers) (by
      intro x hx; rw [fixedTopNames]; simp only [List.mem_append]; tauto)) hS
  have hV : TopAvoids (constTableOf m) (GenAst.emitVkLoading pv) := by
    apply TopAvoids_of_TopNamesOK (S := fixedTopNames) _
      (by intro x hx; exact hS x hx)
    apply TopNamesOK_of_eq (T := [])
    · rw [topBinders_emitVkLoading, hacc]; rfl
    · intro x hx; simp at hx
  have hL : TopAvoids (constTableOf m) (GenAst.emitLagrange pv) :=
    TopAvoids_of_TopNamesOK (TopNamesOK_of_eq (topBinders_emitLagrange pv) (by
      intro x hx; simp at hx; subst hx; simp [fixedTopNames])) hS
  have hQ : TopAvoids (constTableOf m) (GenAst.emitQuotientHelpersAt
      (partialCtxOfVerifier m).quotientPow5Helper) := by
    apply TopAvoids_of_TopNamesOK (S := fixedTopNames) _
      (by intro x hx; exact hS x hx)
    apply TopNamesOK_of_eq (T := (if (partialCtxOfVerifier m).quotientPow5Helper
      then ["x", "z"] else []))
    · exact topBinders_emitQuotientHelpersAt _
    · intro x hx
      by_cases hp : (partialCtxOfVerifier m).quotientPow5Helper
      · simp [hp] at hx
        rcases hx with rfl | rfl <;> simp [fixedTopNames]
      · simp [hp] at hx
  have hQL : TopAvoids (constTableOf m) (GenAst.emitQuotientLin pv) :=
    TopAvoids_of_TopNamesOK (TopNamesOK_of_eq (topBinders_emitQuotientLin pv) (by
      intro x hx; simp at hx)) hS
  have hP : TopAvoids (constTableOf m) (GenAst.emitPcsFromPlan pv) :=
    TopAvoids_emitPcsFromPlan _ pv
  have hF : TopAvoids (constTableOf m) (GenAst.emitFinalPairing pv) :=
    TopAvoids_of_TopNamesOK (TopNamesOK_of_eq (topBinders_emitFinalPairing pv) (by
      intro x hx; simp at hx; subst hx; simp [fixedTopNames])) hS
  have hT : TopAvoids (constTableOf m) (GenAst.emitTraceReturn pv) :=
    TopAvoids_emitTraceReturn _ pv
  rw [mainAsmRaw_decomp]
  exact TopAvoids_append
    (TopAvoids_append
      (TopAvoids_append
        (TopAvoids_append
          (TopAvoids_append
            (TopAvoids_append
              (TopAvoids_append
                (TopAvoids_append
                  (TopAvoids_append (TopAvoids_append (TopAvoids_mainGuard _) hH) hA)
                  (TopAvoids_mainLocals _ hS)) hV) (topAvoids_parser pv hS))
              hL)
            (by
              change TopAvoids (constTableOf m)
                (GenAst.emitQuotientHelpersAt (partialCtxOfVerifier m).quotientPow5Helper ++
                  GenAst.emitQuotientNumerator (partialCtxOfVerifier m) ++
                  GenAst.emitQuotientLin pv)
              exact TopAvoids_append (TopAvoids_append hQ hnum) hQL))
          hP) hF) hT

theorem noShadowCore_of_residuals (pv : PlanView) (m : Model)
    (hacc : pv.hasAccumulator = false)
    (hS : ∀ x ∈ fixedTopNames, (((constTableOf m).map Prod.fst).contains x) = false)
    (hwrap : TopAvoids (constTableOf m) (wrapperLocals m 0 0))
    (hnum : TopAvoids (constTableOf m) (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    Midfall.LoweringV3.noShadowCore pv m = true := by
  have hm := TopAvoids_mainAsmRaw_of pv m hacc hS hnum
  have hg : TopAvoids (constTableOf m) (abiGuardBlock m) := TopAvoids_abiGuardBlock _ m
  change TopAvoids (constTableOf m) (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m)
  exact TopAvoids_append (TopAvoids_append hg hwrap) hm



/-- Every binder of `b`, at any depth, avoids the constant table `C` by name. This is exactly
    `noShadowProg`'s per-block predicate. -/
def Avoids (C : List (String × Nat)) (b : YulBlock) : Prop :=
  (LoweringV2.boundSs b).all (fun x => !((C.map Prod.fst).contains x)) = true

theorem Avoids_append {C : List (String × Nat)} {a b : YulBlock}
    (ha : Avoids C a) (hb : Avoids C b) : Avoids C (a ++ b) := by
  unfold Avoids at *
  rw [boundSs_append, List.all_append, ha, hb]
  rfl

theorem Avoids_of_BindersOK {C : List (String × Nat)} {S : List String} {b : YulBlock}
    (h : BindersOK S b)
    (hS : ∀ x ∈ S, ((C.map Prod.fst).contains x) = false) : Avoids C b := by
  unfold BindersOK at h
  unfold Avoids
  rw [List.all_eq_true] at h ⊢
  intro x hx
  rw [hS x (List.contains_iff_mem.mp (h x hx))]
  rfl

theorem Avoids_nil (C : List (String × Nat)) : Avoids C [] := by
  unfold Avoids; rw [LoweringV2.boundSs.eq_1]; rfl

theorem noShadowProg_eq_Avoids (C : List (String × Nat)) (b : YulBlock) :
    Midfall.LoweringV3.noShadowProg C b = true ↔ Avoids C b := Iff.rfl

/-- **`noShadowProg` OF THE WHOLE UN-INLINED PROGRAM, CONDITIONAL ON THE RESIDUALS.**
    The ABI guard binds nothing (`boundSs` of a `cond` is its condition's expression binders,
    which are empty); the parser is discharged from `BindersOK` + `hSparser`; everything else is
    one hypothesis per group. The two named blockers are `hwrap`/`hfixed` (the `constTableOf`
    name list) and `hqlin` (which contains the parsed numerator). -/
theorem noShadowProg_of_residuals (pv : PlanView) (m : Model)
    (hwrap : Avoids (constTableOf m) (wrapperLocals m 0 0))
    (hfixed : Avoids (constTableOf m)
      (mainGuardBlock ++ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers ++ mainLocals))
    (hSparser : ∀ x ∈ parserBinderNames,
      (((constTableOf m).map Prod.fst).contains x) = false)
    (hvk : Avoids (constTableOf m) (GenAst.emitVkLoading pv))
    (hlag : Avoids (constTableOf m) (GenAst.emitLagrange pv))
    (hqlin : Avoids (constTableOf m) (qlinSlice pv (partialCtxOfVerifier m)))
    (hpcs : Avoids (constTableOf m) (GenAst.emitPcsFromPlan pv))
    (hfp : Avoids (constTableOf m) (GenAst.emitFinalPairing pv))
    (htr : Avoids (constTableOf m) (GenAst.emitTraceReturn pv)) :
    Midfall.LoweringV3.noShadowProg (constTableOf m)
      (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m) = true := by
  rw [noShadowProg_eq_Avoids]
  have hparser : Avoids (constTableOf m) (GenAst.emitTranscriptParser pv) :=
    Avoids_of_BindersOK (parser_bindersOK pv) hSparser
  have hguard : Avoids (constTableOf m) (abiGuardBlock m) := by
    unfold Avoids
    rw [show LoweringV2.boundSs (abiGuardBlock m) = [] from by
      unfold abiGuardBlock
      simp only [LoweringV2.boundSs.eq_2, LoweringV2.boundSs.eq_1, LoweringV2.boundS.eq_6,
        LoweringV2.boundS.eq_10, LoweringV2.boundE, List.append_nil, List.nil_append,
        List.cons_append]]
    rfl
  have hqlin' : Avoids (constTableOf m) (qlinSlice pv (partialCtxOfVerifier m)) := hqlin
  have hmain : Avoids (constTableOf m) (mainAsmRaw pv m) := by
    rw [mainAsmRaw_decomp]
    exact Avoids_append
      (Avoids_append
        (Avoids_append
          (Avoids_append
            (Avoids_append
              (Avoids_append
                (Avoids_append hfixed hvk) hparser) hlag) hqlin') hpcs) hfp) htr
  exact Avoids_append (Avoids_append hguard hwrap) hmain


/-- **`NoWriters` OF THE UN-INLINED PROGRAM**, conditional on the PCS slice and the parsed
    numerator. The parser is discharged (`parser_noWriters`); `noWriters_mainAsmRaw_of` supplies
    the rest. The remaining step to `prog_noWriters` is the inliner-preservation lemma
    `NoWriters (inlineContractConstants c b) ↔ NoWriters b`, named in §5. -/
theorem noWriters_program_of (pv : PlanView) (m : Model)
    (hpcs : NoWriters (GenAst.emitPcsFromPlan pv))
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m) :=
  NoWriters_append (NoWriters_append (noWriters_abiGuardBlock m)
    (noWriters_wrapperLocals m))
    (noWriters_mainAsmRaw_of pv m (parser_noWriters pv) hpcs hnum)

/-- Names whose references are all declared by `S`. `prog_constsDeclared`'s predicate. -/
def FreeOK (S : List String) (b : YulBlock) : Prop :=
  (LoweringV2.freeNames b).all (fun x => S.contains x) = true

theorem FreeOK_append {S : List String} {a b : YulBlock}
    (ha : FreeOK S a) (hb : FreeOK S b) : FreeOK S (a ++ b) := by
  unfold FreeOK at *
  rw [List.all_eq_true] at ha hb ⊢
  intro x hx
  rcases freeNames_subset_of_append_left a b x hx with h | h
  · exact ha x h
  · exact hb x h

/-- **`prog_constsDeclared`'S SCAN**, split over the groups. The guard and the prefix are
    hypotheses (their free names are the render's constants, a `constTableOf`/`expectedConsts`
    fact); the parser and PCS top-level `boundSs` empty their *free* sets only through the
    bound-name tables, and the numerator's free names are the residual. -/
theorem freeNames_program_of (pv : PlanView) (m : Model) (S : List String)
    (hguard : FreeOK S (abiGuardBlock m))
    (hprefix : FreeOK S
      (mainGuardBlock ++ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers ++ mainLocals))
    (hvk : FreeOK S (GenAst.emitVkLoading pv))
    (hparser : FreeOK S (GenAst.emitTranscriptParser pv))
    (hlag : FreeOK S (GenAst.emitLagrange pv))
    (hqlin : FreeOK S (qlinSlice pv (partialCtxOfVerifier m)))
    (hpcs : FreeOK S (GenAst.emitPcsFromPlan pv))
    (hfp : FreeOK S (GenAst.emitFinalPairing pv))
    (htr : FreeOK S (GenAst.emitTraceReturn pv)) :
    FreeOK S (abiGuardBlock m ++ mainAsmRaw pv m) := by
  have hmain : FreeOK S (mainAsmRaw pv m) := by
    rw [mainAsmRaw_decomp]
    exact FreeOK_append
      (FreeOK_append
        (FreeOK_append
          (FreeOK_append
            (FreeOK_append
              (FreeOK_append
                (FreeOK_append hprefix hvk) hparser) hlag) hqlin) hpcs) hfp) htr
  exact FreeOK_append hguard hmain



/-! ### `filterMap` (the PCS set blocks use it to drop the diagonal term)

  A `filterMap` produces a sublist of the `some` results; all three scans are preserved when every
  produced statement satisfies them. These are the lemmas the PCS set-block inductions consume. -/

theorem CallsOK_filterMap {α : Type _} {S : List (String × Nat)} {l : List α}
    {g : α → Option (Stmt EVM.Op)}
    (h : ∀ a ∈ l, ∀ s, g a = some s → CallsOK S [s]) : CallsOK S (l.filterMap g) := by
  induction l with
  | nil => simp [CallsOK, Midfall.LoweringV3.callSitesSs]
  | cons a as ih =>
      rw [List.filterMap_cons]
      cases hga : g a with
      | none => simpa using ih (fun b hb => h b (by simp [hb]))
      | some s =>
          simpa using CallsOK_append (h a (by simp) s hga)
            (ih (fun b hb => h b (by simp [hb])))

theorem BindersOK_filterMap {α : Type _} {S : List String} {l : List α}
    {g : α → Option (Stmt EVM.Op)}
    (h : ∀ a ∈ l, ∀ s, g a = some s → BindersOK S [s]) : BindersOK S (l.filterMap g) := by
  induction l with
  | nil => simp [BindersOK, LoweringV2.boundSs]
  | cons a as ih =>
      rw [List.filterMap_cons]
      cases hga : g a with
      | none => simpa using ih (fun b hb => h b (by simp [hb]))
      | some s =>
          simpa using BindersOK_append (h a (by simp) s hga)
            (ih (fun b hb => h b (by simp [hb])))

theorem NoWriters_filterMap {α : Type _} {l : List α} {g : α → Option (Stmt EVM.Op)}
    (h : ∀ a ∈ l, ∀ s, g a = some s → NoWriters [s]) : NoWriters (l.filterMap g) := by
  induction l with
  | nil => exact ⟨1, rfl⟩
  | cons a as ih =>
      rw [List.filterMap_cons]
      cases hga : g a with
      | none => simpa using ih (fun b hb => h b (by simp [hb]))
      | some s =>
          simpa using NoWriters_append (h a (by simp) s hga)
            (ih (fun b hb => h b (by simp [hb])))


/-- `planViewOf` at the no-accumulator arm has `hasAccumulator = false`; the
    `SupportedInput.noAcc` hypothesis reaches the callsResolved residual this way. -/
theorem planViewOf_hasAccumulator_none {Program Layout : Type} (L : LoweringPlan Program Layout)
    (m : Model) : (planViewOf L m none).hasAccumulator = false := rfl

/-! ## 5. THE BLOCKERS, AND THE EXACT RESIDUAL OF EACH TARGET

  **BLOCKER 1: the parsed numerator.** `emitQuotientNumerator` is
  `YulParse.parseLines [renderQuotientNumeratorBlock c]` (`GenAst.lean:789`); `parseLines`
  (`YulParse.lean:182`) tokenises with `String.splitOn` / `String.replace` / `String.startsWith`
  (`YulGolden.lean:72-120`), which are `@[extern]`. The kernel cannot reduce them, and
  `native_decide` cannot evaluate a term with the render's free variables, so for a symbolic model
  nothing in the tree can say what the parse returns: not that it fails, not that it is a single
  `Stmt.block`, not its binders, calls, free names or early exits. Measured on the F1 render (an
  `Instances/` probe, `native_decide` territory, recorded as a comment rather than imported here):

    `partialCtxOfVerifier poseidonM` with one extra line in `quotientInlineComputations`
      * `["sstore(0, 1)"]`              -> `noWritersFuel 200000 (mainAsmRaw …) = false`
      * `["undeclared_fn(1)"]`          -> `callsResolved (mainAsmRaw …) = false`
      * `["let FR_MODULUS := 1"]`       -> `noShadowProg (constTableOf …) (… mainAsmRaw …) = false`
    while the unmutated model answers `true` to all three.

  So these scans are functions of the MODEL'S TEXT; `Generates` constrains the model only
  equationally (`generateVerifierFromPlan … = .ok model`). The missing fact is about
  `compactQuotientComputationBlocks` / `renderQuotientNumeratorBlock`, and the text-to-AST bridge is
  `YulParse.parseLines`.

  **BLOCKER 2: the `constTableOf` names.** The shadow scans compare against
  `(constTableOf m).map Prod.fst`, i.e. `solConstantLine?` over `renderConstants
  (partialCtxOfVerifier m)` (`Program.lean:59-61`). The table's NAMES are a `String.splitOn` fact
  too, so they need CERT.6's `prog_constTable` (or a name-level version) before any binder table can
  be compared. This is why the shadow reductions below carry a finite-name hypothesis `hS`.

  **WHAT IS NOW CLOSED / REDUCED, PER TARGET.**

  * `v3_noShadow`: the parser's `topBinders` are proved (`parser_topOK`), the fixed groups are
    discharged from their §2 tables (`fixedTopNames` + `hS`), and `topBinders_emitPcsFromPlan = []`
    is proved. `noShadowCore_of_residuals` leaves exactly: the wrapper locals (`vk` /
    `quotientEvaluator`, a `constTableOf` fact) and the parsed numerator's top-level binders.
  * `prog_noShadow`: `noShadowProg_of_residuals` leaves the wrapper locals, the fixed prefix under
    `constTableOf` (`hfixed`), the parser under `hSparser`, and the vk/lagrange/qlin/pcs/finalPairing/
    traceReturn groups' `Avoids` facts. The parser's every-binder table is proved
    (`parser_bindersOK`); the fixed groups' `boundSs` tables and the PCS binder language are the
    mechanical remainder.
  * `prog_callsResolved`: `callsResolved_mainAsmRaw_of` reduces the scan to `CallsOK` of the parsed
    numerator and of the PCS slice, with `pv.hasAccumulator = false` (which removes
    `validate_public_accumulator` from the sigs). Every other group's call sites are tabulated and
    the parser's are proved (`parser_callsOK`); the function table is `mainSigSet`.
    `CertScanPcs.callsResolved_mainAsmRaw_of_pcs` replaces the PCS slice hypothesis by the
    per-block invariant `∀ blocks, computationsAst … = .ok blocks → ∀ b ∈ blocks, CallsOK … b`.
  * `prog_noWriters`: `noWriters_program_of` leaves the PCS slice and the parsed numerator; the
    parser (`parser_noWriters`) and all fixed groups are proved. The target's `prog` is the INLINED
    program, so one more child remains: `NoWriters` is invariant under
    `Inline.inlineContractConstants` (the inliner changes expressions only, and the writer scan
    reads constructors only). `CertScanPcs.noWriters_mainAsmRaw_of_pcs` replaces the PCS slice by
    the same per-block invariant.
  * `prog_constsDeclared`: `freeNames_program_of` reduces the scan to one `FreeOK` hypothesis per
    emitter group; the guard/prefix facts are `constTableOf`/`expectedConsts` computations, and the
    numerator's free names are Blocker 1.
  * `v3_exitDiscipline`: no reduction landed here. The tail is the fixed `traceReturn` shape; the
    prefix scan is the open child, and its numerator part is Blocker 1.
  * `prog_closed` / `v3_closed`: additionally need the inliner free-name lemma (`freeNames` after
    `inlineContractConstants`); the V3 statement records it as the only side condition.

  **PCS, PRECISELY.** `Midfall/Generator/CertScanPcs.lean` lands `callSitesSs`/`NoWriters` for
  `pcsBlock1Ast`, `pcsBlock2Ast`, `pcsBlock3Ast` (including the rolled `for` body and the
  `wordExpr`/`ptrExpr` codec leaves), `pcsBlock6Ast`, `pcsX4PowersAst`, `pcsVLinesAst`,
  `pcsSetBlockAst` (both arms, including the diagonal `List.filterMap`), and `pcsBlock4Ast` (the
  per-set `yblock` induction); plus the `NoWriters_forLoop` composition and the compositional
  `ScanClean` codec leaves. STILL OPEN there, named: `pcsBlock5Ast`'s scans (the nested monadic
  `foldlM` over `bySet`/commitments and `pcsLinExpansion`'s folds; the block has no user call and
  no writer builtin) and the `computationsAst` assembly that extracts the emitted block list from
  the `Except` chain. `topBinders_emitPcsFromPlan = []` and `funSigs_emitPcsFromPlan = []` are
  proved in §2/§3 here. -/

end Midfall.Generator.CertScan
