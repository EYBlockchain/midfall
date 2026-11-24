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

theorem topBinders_flatten_map {α : Type} (l : List α) (f : α → YulBlock) :
    LoweringV2.topBinders (List.flatten (l.map f)) =
      l.flatMap (fun a => LoweringV2.topBinders (f a)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, topBinders_append, ih, List.flatMap_cons]

theorem topBinders_map {α : Type} (l : List α) (g : α → Stmt EVM.Op) :
    LoweringV2.topBinders (l.map g) =
      l.flatMap (fun a => Inline.boundOf (g a)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.flatMap_cons, LoweringV2.topBinders, List.flatMap_cons,
        List.append_assoc]
      rw [show List.flatMap Inline.boundOf (List.map g as) =
        List.flatMap (fun a => Inline.boundOf (g a)) as from ih]

theorem mem_topBinders_map {α : Type} {l : List α} {g : α → Stmt EVM.Op} {x : String} :
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

theorem mem_topBinders_flatten_map {α : Type} {l : List α} {f : α → YulBlock} {x : String} :
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


end Midfall.Generator.CertScan
