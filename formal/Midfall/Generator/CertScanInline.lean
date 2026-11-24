-- |
-- Midfall.Generator.CertScanInline
--
-- The inliner side of CERT.5's `prog_noWriters`: `NoWriters`/`ScanClean` is
-- preserved by `Inline.inlineContractConstants`.
--
-- The inliner rewrites EXPRESSIONS only: `inExpr` can turn a `var` into a
-- literal (or leave it alone), and maps the arguments of `builtin`/`call`
-- without changing the operator or callee. `inlineStmtStep` preserves every
-- statement constructor and its binders; only nested block bodies descend.
-- Therefore the writer scan, which classifies `Op.isWriter` on builtins and
-- recurses through calls, is unchanged. This file proves that as a
-- compositional `ScanClean` preservation, then lifts it through the fuel walk.
--
-- This is the precise `noWriters_inlineContractConstants` used by
-- `CertScanPcs.noWriters_asmOf_pcs`. `boundSs`/`callSitesSs` are not needed
-- here: `callsResolved` is stated on `mainAsmRaw`, not on the inlined `asmOf`.
import Midfall.Generator.CertScan
import Midfall.Lowering.InlineConstants
set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000
open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM
open Midfall.Yul.Bridge
open Midfall.Lowering.Inline
open Midfall.Generator.CertScan

namespace Midfall.Generator.CertScanInline

/-! ## Expressions -/

/-- `ScanClean` of an expression is preserved by `inExpr`. -/
theorem scanClean_inExpr (fuel : Nat) (e : Expr EVM.Op) (consts : Consts) (sh : List String)
    (h : ScanClean (.e e)) : ScanClean (.e (inExpr fuel e consts sh)) := by
  induction fuel generalizing e with
  | zero => simpa [inExpr] using h
  | succ fuel ih =>
      have hes : ∀ (args : List (Expr EVM.Op)), ScanClean (.es args) →
          ScanClean (.es (args.map fun a => inExpr fuel a consts sh)) := by
        intro args hargs
        induction args with
        | nil => simpa using hargs
        | cons a as ihas =>
            obtain ⟨ha, has⟩ := scanClean_es_cons hargs
            simpa using scanClean_es_cons_rev (ih a ha) (ihas has)
      cases e with
      | lit l => simpa [inExpr] using h
      | var x =>
          simp only [inExpr]
          split
          · simpa using h
          · split
            · exact ⟨1, rfl⟩
            · simpa using h
      | builtin op args =>
          have hb := scanClean_e_builtin h
          rw [inExpr]
          exact scanClean_e_builtin_rev hb.1 (hes args hb.2)
      | call f args =>
          have hc := scanClean_e_call h
          rw [inExpr]
          exact scanClean_e_call_rev (hes args hc)

/-- Argument-list form of `scanClean_inExpr`. -/
theorem scanClean_es_inExpr (fuel : Nat) (args : List (Expr EVM.Op)) (consts : Consts)
    (sh : List String) (h : ScanClean (.es args)) :
    ScanClean (.es (args.map fun a => inExpr fuel a consts sh)) := by
  induction args with
  | nil => simpa using h
  | cons a as ih =>
      obtain ⟨ha, has⟩ := scanClean_es_cons h
      simpa using scanClean_es_cons_rev (scanClean_inExpr fuel a consts sh ha) (ih has)

/-! ## Statements and blocks -/

/-- Case-list form used by `switch`. -/
theorem scanClean_cs_map (cs : List (Literal × Block EVM.Op)) (h : ScanClean (.cs cs))
    (rec : List String -> YulBlock -> SRes)
    (hrec : ∀ sh b, ScanClean (.b b) → ScanClean (.b (rec sh b).blks))
    (sh : List String) :
    ScanClean (.cs (cs.map fun (p, b) => (p, (rec sh b).blks))) := by
  induction cs with
  | nil => simpa using h
  | cons q qs ih =>
      obtain ⟨p, b⟩ := q
      obtain ⟨hb, hqs⟩ := scanClean_cs_cons h
      simpa using scanClean_cs_cons_rev (hrec sh b hb) (ih hqs)

/-- The `switch` case list in `inlineStmtStep` is a `zip` of the original
    labels and the recursively rewritten bodies. -/
theorem scanClean_cs_map_zip (cs : List (Literal × Block EVM.Op)) (h : ScanClean (.cs cs))
    (rec : List String -> YulBlock -> SRes)
    (hrec : ∀ sh b, ScanClean (.b b) → ScanClean (.b (rec sh b).blks))
    (sh : List String) :
    ScanClean (.cs ((cs.map Prod.fst).zip
      (cs.map ((fun r => r.blks) ∘ fun q => rec sh q.2)))) := by
  induction cs with
  | nil => simpa using h
  | cons q qs ih =>
      obtain ⟨p, b⟩ := q
      obtain ⟨hb, hqs⟩ := scanClean_cs_cons h
      simpa using scanClean_cs_cons_rev (hrec sh b hb) (ih hqs)

/-- One statement: `inlineStmtStep` preserves `ScanClean`, given the recursion
    preserves nested block bodies. -/
theorem scanClean_inlineStmtStep (rec : List String -> YulBlock -> SRes)
    (hrec : ∀ sh b, ScanClean (.b b) → ScanClean (.b (rec sh b).blks))
    (consts : Consts) (sh : List String) (s : Stmt EVM.Op)
    (h : ScanClean (.s s)) :
    ScanClean (.s (inlineStmtStep rec consts sh s).1) := by
  cases s with
  | block b =>
      simpa [inlineStmtStep] using
        scanClean_s_block_rev (hrec sh b (scanClean_s_block h))
  | funDef n ps rs body =>
      simpa [inlineStmtStep] using
        scanClean_s_funDef_rev (hrec (sh ++ ps ++ rs) body (scanClean_s_funDef h))
  | letDecl xs e =>
      cases e with
      | none => simpa [inlineStmtStep] using h
      | some e =>
          simpa [inlineStmtStep] using
            scanClean_s_letDecl_some_rev
              (scanClean_inExpr exprFuel e consts sh (scanClean_s_letDecl_some h))
  | assign xs e =>
      simpa [inlineStmtStep] using
        scanClean_s_assign_rev
          (scanClean_inExpr exprFuel e consts sh (scanClean_s_assign h))
  | cond c body =>
      obtain ⟨hc, hb⟩ := scanClean_s_cond h
      simpa [inlineStmtStep] using
        scanClean_s_cond_rev (scanClean_inExpr exprFuel c consts sh hc) (hrec sh body hb)
  | «switch» c cs d =>
      obtain ⟨hc, hcs, hd⟩ := scanClean_s_switch h
      have hcs' := scanClean_cs_map_zip cs hcs rec hrec sh
      cases d with
      | none =>
          simpa [inlineStmtStep] using
            scanClean_s_switch_rev (dflt := none)
              (scanClean_inExpr exprFuel c consts sh hc) hcs' (by trivial)
      | some db =>
          simpa [inlineStmtStep] using
            scanClean_s_switch_rev (dflt := some (rec sh db).blks)
              (scanClean_inExpr exprFuel c consts sh hc) hcs' (hrec sh db hd)
  | forLoop init c post body =>
      obtain ⟨hi, hc, hp, hb⟩ := scanClean_s_forLoop h
      let i := rec sh init
      let sh' := sh ++ (i.blks.flatMap boundOf)
      have hi' : ScanClean (.b i.blks) := hrec sh init hi
      have hp' : ScanClean (.b (rec sh' post).blks) := hrec sh' post hp
      have hb' : ScanClean (.b (rec sh' body).blks) := hrec sh' body hb
      simpa [inlineStmtStep, i, sh'] using
        scanClean_s_forLoop_rev hi'
          (scanClean_inExpr exprFuel c consts sh' hc) hp' hb'
  | exprStmt e =>
      simpa [inlineStmtStep] using
        scanClean_s_exprStmt_rev
          (scanClean_inExpr exprFuel e consts sh (scanClean_s_exprStmt h))
  | «break» => simpa [inlineStmtStep] using h
  | «continue» => simpa [inlineStmtStep] using h
  | «leave» => simpa [inlineStmtStep] using h

/-- The accumulator fold of `inlineStep`: if the accumulated block and the
    remaining input are clean, so is the fold's accumulated block. -/
theorem scanClean_foldl_stepAcc (rec : List String -> YulBlock -> SRes)
    (hrec : ∀ sh b, ScanClean (.b b) → ScanClean (.b (rec sh b).blks))
    (consts : Consts) :
    ∀ (bl : YulBlock) (acc : Acc),
      ScanClean (.b acc.blks) → ScanClean (.b bl) →
      ScanClean (.b (bl.foldl (stepAcc rec consts) acc).blks) := by
  intro bl
  induction bl with
  | nil => intro acc hacc _; simpa [List.foldl] using hacc
  | cons s ss ih =>
      intro acc hacc hbl
      obtain ⟨hs, hss⟩ := scanClean_b_cons hbl
      have hs' : ScanClean (.s (inlineStmtStep rec consts acc.sh s).1) :=
        scanClean_inlineStmtStep rec hrec consts acc.sh s hs
      have hacc' : ScanClean (.b (stepAcc rec consts acc s).blks) := by
        rw [stepAcc_blks]
        exact NoWriters_append hacc (scanClean_b_cons_rev hs' scanClean_nil)
      rw [List.foldl_cons]
      exact ih (stepAcc rec consts acc s) hacc' hss

/-- `inlineStep` preserves `ScanClean` of the block. -/
theorem scanClean_inlineStep (rec : List String -> YulBlock -> SRes)
    (hrec : ∀ sh b, ScanClean (.b b) → ScanClean (.b (rec sh b).blks))
    (consts : Consts) (sh : List String) (bl : YulBlock)
    (h : ScanClean (.b bl)) :
    ScanClean (.b (inlineStep rec consts sh bl).blks) := by
  rw [inlineStep_eq_foldl]
  exact scanClean_foldl_stepAcc rec hrec consts bl (initAcc sh) (by simpa [initAcc] using scanClean_nil) h

/-- `inlineScan` preserves `ScanClean` at every fuel. -/
theorem scanClean_inlineScan (fuel : Nat) (consts : Consts) (sh : List String)
    (bl : YulBlock) (h : ScanClean (.b bl)) :
    ScanClean (.b (inlineScan fuel consts sh bl).blks) := by
  induction fuel generalizing sh bl with
  | zero => simpa [inlineScan] using h
  | succ fuel ih =>
      simp only [inlineScan]
      exact scanClean_inlineStep (inlineScan fuel consts)
        (fun sh b hb => ih sh b hb) consts sh bl h

/-- **THE GATE.** `Inline.inlineContractConstants` preserves `NoWriters`.
    This is the `hinline` side condition of `CertScanPcs.noWriters_asmOf_pcs`. -/
theorem noWriters_inlineContractConstants (consts : Consts) (b : YulBlock)
    (h : NoWriters b) : NoWriters (inlineContractConstants consts b) :=
  scanClean_inlineScan inlineFuel consts [] b h

end Midfall.Generator.CertScanInline
