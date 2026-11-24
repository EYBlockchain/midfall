import Midfall.Generator.CertScan

set_option autoImplicit false
open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Generator.CertScan
open Midfall.Lowering.GenAstPcs

/-!
  Midfall.Generator.CertScanPcs — THE PCS GROUP OF CERT.5(b).

  All PCS block functions whose statement shape is a plain Yul tree are scanned here for user
  calls and world writers: `pcsBlock1Ast`, `pcsBlock2Ast`, `pcsBlock3Ast` (both scans),
  `pcsBlock4Ast`, `pcsBlock6Ast`, `pcsSetBlockAst`, `pcsX4PowersAst`, `pcsVLinesAst`. The set
  block's diagonal skip is the `List.filterMap` case; the list-mapped arms use the
  `CallsOK`/`NoWriters` algebra from `CertScan`. Block 3's `NoWriters` closes its rolled
  `for`-body through `NoWriters_forLoop`, with compositional `ScanClean` leaves for
  `wordExpr`/`ptrExpr`.

  `pcsBlock5Ast`'s two scans are also here: the nested monadic `foldlM` over
  `bySet`/commitments is closed through `foldlM_invariant'`, the inner step's
  identity/linearization/MSM arms carry the accumulator invariant, and
  `pcsLinExpansion`'s pure limb fold and selector fold use the same invariant.
  The `computationsAst` assembly is closed here too: `computationsAst_calls` /
  `computationsAst_noWriters` extract the emitted block list from the `Except`
  chain, and the `*_pcs` reductions below discharge the PCS slice. The numerator
  and inliner-preservation sides remain named hypotheses.
-/

namespace Midfall.Generator.CertScanPcs

def pcsCalls : List (String × Nat) := [("scalar_inv", 1)]

theorem CallsOK_map' {α : Type _} {S : List (String × Nat)} {l : List α}
    {g : α → Stmt EVM.Op} (h : ∀ a ∈ l, CallsOK S [g a]) : CallsOK S (l.map g) := by
  induction l with
  | nil => simp [CallsOK, Midfall.LoweringV3.callSitesSs]
  | cons a as ih =>
      rw [List.map_cons]
      exact CallsOK_append (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem CallsOK_flatMap {α : Type _} {S : List (String × Nat)} {l : List α}
    {f : α → YulBlock} (h : ∀ a ∈ l, CallsOK S (f a)) : CallsOK S (l.flatMap f) := by
  rw [show l.flatMap f = (l.map f).flatten from rfl]
  exact CallsOK_flatten_map h

theorem NoWriters_flatMap {α : Type _} {l : List α} {f : α → YulBlock}
    (h : ∀ a ∈ l, NoWriters (f a)) : NoWriters (l.flatMap f) := by
  rw [show l.flatMap f = (l.map f).flatten from rfl]
  exact NoWriters_flatten_map h

theorem CallsOK_optionToList {S : List (String × Nat)} {o : Option (Stmt EVM.Op)}
    (h : ∀ s, o = some s → CallsOK S [s]) : CallsOK S o.toList := by
  cases o with
  | none => simp [CallsOK, Midfall.LoweringV3.callSitesSs]
  | some s => simpa using h s rfl

theorem NoWriters_optionToList {o : Option (Stmt EVM.Op)}
    (h : ∀ s, o = some s → NoWriters [s]) : NoWriters o.toList := by
  cases o with
  | none => exact ⟨1, rfl⟩
  | some s => simpa using h s rfl

-- single-statement leaves
theorem calls_stmt_none {S : List (String × Nat)} {s : Stmt EVM.Op}
    (h : Midfall.LoweringV3.callSitesS s = []) : CallsOK S [s] := by
  unfold CallsOK
  rw [Midfall.LoweringV3.callSitesSs.eq_2, Midfall.LoweringV3.callSitesSs.eq_1, h]
  rfl

theorem calls_stmt_one {S : List (String × Nat)} {s : Stmt EVM.Op}
    (h : Midfall.LoweringV3.callSitesS s = [("scalar_inv", 1)])
    (hmem : ("scalar_inv", 1) ∈ S) : CallsOK S [s] := by
  unfold CallsOK
  rw [Midfall.LoweringV3.callSitesSs.eq_2, Midfall.LoweringV3.callSitesSs.eq_1, h]
  simp [List.all_eq_true, List.contains_iff_mem, hmem]

theorem calls_none {S : List (String × Nat)} {b : YulBlock}
    (h : Midfall.LoweringV3.callSitesSs b = []) : CallsOK S b := by
  unfold CallsOK; rw [h]; rfl

example : CallsOK pcsCalls [GenAst.yexpr (GenAst.yop Op.mstore [GenAst.yvar "a", GenAst.ylit 1])] := by
  apply calls_stmt_none
  simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
    Midfall.LoweringV3.callSitesEs, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit]

example : CallsOK pcsCalls [GenAst.yset "q" (GenAst.ycall "scalar_inv" [GenAst.yvar "x"])] := by
  apply calls_stmt_one
  · simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
      Midfall.LoweringV3.callSitesEs, GenAst.yset, GenAst.ycall, GenAst.yvar]
  · simp [pcsCalls]



theorem block1_calls (rots : List Int) (maxRot minRot : Int) (trace : Bool)
    (ps : List (List Int)) : CallsOK pcsCalls (pcsBlock1Ast rots maxRot minRot trace ps) := by
  unfold pcsBlock1Ast
  dsimp only
  by_cases ht : trace = true <;> simp only [ht, if_true, if_false, reduceIte]
  by_cases hb : minRot < 0 <;> simp only [hb, if_true, if_false, reduceIte]
  repeat' first
    | apply CallsOK_append
    | apply CallsOK_flatMap
    | apply CallsOK_map'
    | apply CallsOK_optionToList
    | split
    | (intro s hs
       simp only [Option.map_eq_some_iff] at hs
       obtain ⟨idx, _, ha⟩ := hs
       subst ha)
    | (intro a _)
    | (apply calls_none
       simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
         Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
         callSitesE_var, mstoreAdd, walkStep, GenAst.ylet, GenAst.yset, GenAst.yexpr,
         GenAst.yop, GenAst.yvar, GenAst.ylit])



example : NoWriters [mstoreAdd "A" 0 (GenAst.yvar "x")] := ⟨100, rfl⟩
example : NoWriters [walkStep "omega"] := ⟨100, rfl⟩

theorem block1_noWriters (rots : List Int) (maxRot minRot : Int)
    (ps : List (List Int)) : NoWriters (pcsBlock1Ast rots maxRot minRot false ps) := by
  unfold pcsBlock1Ast
  dsimp only
  simp only [Bool.false_eq_true, if_false, reduceIte]
  by_cases hb : minRot < 0 <;> simp only [hb, if_true, if_false, reduceIte]
  repeat' first
    | apply NoWriters_append
    | apply NoWriters_flatMap
    | apply NoWriters_map
    | apply NoWriters_optionToList
    | (intro s hs
       simp only [Option.map_eq_some_iff] at hs
       obtain ⟨idx, _, ha⟩ := hs
       subst ha)
    | (intro a _)
    | (exact ⟨100, rfl⟩)



theorem block2_calls (n : Nat) (tr : Bool) : CallsOK pcsCalls (pcsBlock2Ast n tr) := by
  unfold pcsBlock2Ast
  by_cases h : 1 < n <;> simp only [h, if_true, if_false, reduceIte]
  by_cases ht : tr = true <;> simp only [ht, if_true, if_false, reduceIte]
  repeat' first
    | apply CallsOK_append
    | apply CallsOK_map'
    | (apply calls_none
       simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
         Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
         callSitesE_var, GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr,
         GenAst.yop, GenAst.yvar, GenAst.ylit, truncMaskExpr])

theorem block2_noWriters (n : Nat) (tr : Bool) : NoWriters (pcsBlock2Ast n tr) := by
  unfold pcsBlock2Ast
  by_cases h : 1 < n <;> simp only [h, if_true, if_false, reduceIte]
  by_cases ht : tr = true <;> simp only [ht, if_true, if_false, reduceIte]
  repeat' first
    | apply NoWriters_append
    | apply NoWriters_map
    | (intro a _)
    | (exact ⟨100, rfl⟩)

theorem block6_calls (scratch : Nat) : CallsOK pcsCalls (pcsBlock6Ast scratch) := by
  apply calls_none
  simp [pcsBlock6Ast, Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
    Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
    callSitesE_var, GenAst.ylet, GenAst.yset, GenAst.yif, GenAst.yexpr, GenAst.yop,
    GenAst.yvar, GenAst.ylit, subFrom]

theorem block6_noWriters (scratch : Nat) : NoWriters (pcsBlock6Ast scratch) := ⟨200, rfl⟩

theorem x4_calls (nSets : Nat) (tr : Bool) : CallsOK pcsCalls (pcsX4PowersAst nSets tr) := by
  unfold pcsX4PowersAst
  by_cases h : tr = true <;> (try simp only [h, if_true, if_false, reduceIte]) <;>
  repeat' first
    | apply CallsOK_append
    | apply CallsOK_flatMap
    | (intro a _)
    | (apply calls_none
       simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
         Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
         callSitesE_var, GenAst.ylet, GenAst.yset, GenAst.yif, GenAst.yexpr, GenAst.yop,
         GenAst.yvar, GenAst.ylit, truncMaskExpr])

theorem x4_noWriters (nSets : Nat) (tr : Bool) : NoWriters (pcsX4PowersAst nSets tr) := by
  unfold pcsX4PowersAst
  by_cases h : tr = true <;> (try simp only [h, if_true, if_false, reduceIte]) <;>
  repeat' first
    | apply NoWriters_append
    | apply NoWriters_flatMap
    | (intro a _)
    | (exact ⟨100, rfl⟩)

theorem v_calls (nSets : Nat) : CallsOK pcsCalls (pcsVLinesAst nSets) := by
  unfold pcsVLinesAst
  repeat' first
    | apply CallsOK_append
    | apply CallsOK_map'
    | (intro a _)
    | (apply calls_none
       simp [Midfall.LoweringV3.callSitesSs, Midfall.LoweringV3.callSitesS,
         Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, callSitesE_lit,
         callSitesE_var, GenAst.ylet, GenAst.yset, GenAst.yexpr, GenAst.yop, GenAst.yvar,
         GenAst.ylit])

theorem v_noWriters (nSets : Nat) : NoWriters (pcsVLinesAst nSets) := by
  unfold pcsVLinesAst
  repeat' first
    | apply NoWriters_append
    | apply NoWriters_map
    | (intro a _)
    | (exact ⟨100, rfl⟩)




theorem CallsOK_cons_ne {S : List (String × Nat)} {s t : Stmt EVM.Op} {ss : YulBlock}
    (h1 : CallsOK S [s]) (h2 : CallsOK S (t :: ss)) : CallsOK S (s :: t :: ss) := by
  have := CallsOK_append h1 h2
  simpa using this

theorem CallsOK_cons_append {S : List (String × Nat)} {s : Stmt EVM.Op} {a b : YulBlock}
    (h1 : CallsOK S [s]) (h2 : CallsOK S (a ++ b)) : CallsOK S (s :: (a ++ b)) := by
  have := CallsOK_append h1 h2
  simpa using this

theorem NoWriters_cons_append {s : Stmt EVM.Op} {a b : YulBlock}
    (h1 : NoWriters [s]) (h2 : NoWriters (a ++ b)) : NoWriters (s :: (a ++ b)) := by
  have := NoWriters_append h1 h2
  simpa using this

theorem CallsOK_nil' (S : List (String × Nat)) : CallsOK S [] := by
  unfold CallsOK; simp [Midfall.LoweringV3.callSitesSs]

theorem callSitesE_ite {c : Prop} [Decidable c] {a b : Expr EVM.Op}
    (ha : Midfall.LoweringV3.callSitesE a = []) (hb : Midfall.LoweringV3.callSitesE b = []) :
    Midfall.LoweringV3.callSitesE (if c then a else b) = [] := by
  split <;> assumption

theorem callSitesE_valueExpr (v : MValue) :
    Midfall.LoweringV3.callSitesE (valueExpr v) = [] := by
  unfold valueExpr
  split <;> (try split) <;> simp [Midfall.LoweringV3.callSitesE,
    Midfall.LoweringV3.callSitesEs, GenAst.yop, GenAst.yvar, GenAst.ylit]

theorem callSitesE_ptrExpr (p : MPtr) :
    Midfall.LoweringV3.callSitesE (ptrExpr p) = [] := by
  unfold ptrExpr; exact callSitesE_valueExpr p.value

theorem callSitesE_wordExpr (w : MWord) :
    Midfall.LoweringV3.callSitesE (wordExpr w) = [] := by
  unfold wordExpr
  split <;> simp [callSitesE_valueExpr, Midfall.LoweringV3.callSitesE,
    Midfall.LoweringV3.callSitesEs, GenAst.yop]

theorem callSitesE_x1Pow (i : Nat) :
    Midfall.LoweringV3.callSitesE (x1Pow i) = [] := by
  simp [x1Pow, Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs,
    GenAst.yop, GenAst.yvar, GenAst.ylit]

theorem calls_lbasis_terms (points rots : List Int) (j : Nat) (pointJ : Int) :
    CallsOK pcsCalls ((enumIdx points).filterMap fun (k, pointK) =>
      if k == j then none
      else some (GenAst.yset ("lbasis_" ++ toString j)
        (GenAst.yop Op.mulmod [GenAst.yvar ("lbasis_" ++ toString j),
          subFrom (GenAst.yvar ("rot_pt_" ++ toString ((List.findIdx? (fun r => r == pointJ) rots).getD 0)))
            (GenAst.yvar ("rot_pt_" ++ toString ((List.findIdx? (fun r => r == pointK) rots).getD 0))),
          GenAst.yvar "r"]))) := by
  apply CallsOK_filterMap
  intro a ha s hs
  by_cases h : (a.1 == j) = true
  · simp [h] at hs
  · simp only [h, ite_false, Bool.false_eq_true, reduceIte] at hs
    cases hs
    apply calls_none
    simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
      Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
      Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
      Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
      Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
      Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
      Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
      Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
      Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
      GenAst.yset, GenAst.yop, GenAst.yvar, subFrom]
    rfl

set_option maxHeartbeats 2000000 in
theorem setBlock_calls (setIdx : Nat) (points rots : List Int) (off : Nat) :
    CallsOK pcsCalls (pcsSetBlockAst setIdx points rots off) := by
  unfold pcsSetBlockAst
  dsimp only
  split
  · repeat' first
      | exact CallsOK_nil' _
      | apply CallsOK_cons_ne
      | apply CallsOK_map'
      | (intro a _)
      | (apply calls_none
         simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
           Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
           Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
           Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
           Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
           Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
           Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
           Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
           Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
           GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
           GenAst.yvar, GenAst.ylit, subFrom]
         rfl)
      | (exact calls_stmt_one (by
           simp only [Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesE.eq_1,
             callSitesE_var, GenAst.ylet, GenAst.ycall, GenAst.yvar, List.length_cons,
             List.length_nil, Nat.zero_add, List.append_nil]
           rfl) (by simp [pcsCalls]))
  · repeat' first
      | exact CallsOK_nil' _
      | apply CallsOK_cons_ne
      | apply CallsOK_append
      | apply CallsOK_map'
      | apply CallsOK_flatMap
      | (exact calls_lbasis_terms _ _ _ _)
      | (intro a _)
      | (exact calls_stmt_one (by
           simp only [Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesE.eq_1,
             callSitesE_var, GenAst.ylet, GenAst.ycall, GenAst.yvar, List.length_cons,
             List.length_nil, Nat.zero_add, List.append_nil]
           rfl) (by simp [pcsCalls]))
      | (apply calls_none
         simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
           Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
           Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
           Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
           Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
           Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
           Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
           Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
           Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
           GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
           GenAst.yvar, GenAst.ylit, subFrom]
         rfl)



theorem noWriters_lbasis_terms (points rots : List Int) (j : Nat) (pointJ : Int) :
    NoWriters ((enumIdx points).filterMap fun (k, pointK) =>
      if k == j then none
      else some (GenAst.yset ("lbasis_" ++ toString j)
        (GenAst.yop Op.mulmod [GenAst.yvar ("lbasis_" ++ toString j),
          subFrom (GenAst.yvar ("rot_pt_" ++ toString ((List.findIdx? (fun r => r == pointJ) rots).getD 0)))
            (GenAst.yvar ("rot_pt_" ++ toString ((List.findIdx? (fun r => r == pointK) rots).getD 0))),
          GenAst.yvar "r"]))) := by
  apply NoWriters_filterMap
  intro a ha s hs
  by_cases h : (a.1 == j) = true
  · simp [h] at hs
  · simp only [h, ite_false, Bool.false_eq_true, reduceIte] at hs
    cases hs
    exact ⟨100, rfl⟩

theorem noWriters_mstore_ptr (off : Nat) (p : MPtr) :
    NoWriters [GenAst.yexpr (GenAst.yop Op.mstore [GenAst.ylit off, ptrExpr p])] := by
  refine ⟨100, ?_⟩
  unfold ptrExpr valueExpr
  split <;> (try split) <;> rfl

theorem NoWriters_cons_ne {s t : Stmt EVM.Op} {ss : YulBlock}
    (h1 : NoWriters [s]) (h2 : NoWriters (t :: ss)) : NoWriters (s :: t :: ss) := by
  have := NoWriters_append h1 h2
  simpa using this

set_option maxHeartbeats 2000000 in
theorem setBlock_noWriters (setIdx : Nat) (points rots : List Int) (off : Nat) :
    NoWriters (pcsSetBlockAst setIdx points rots off) := by
  unfold pcsSetBlockAst
  dsimp only
  split
  · repeat' first
      | exact ⟨100, rfl⟩
      | apply NoWriters_cons_ne
      | apply NoWriters_append
      | (intro a _)
  · repeat' first
      | exact ⟨100, rfl⟩
      | apply NoWriters_cons_ne
      | apply NoWriters_append
      | apply NoWriters_flatten_map
      | apply NoWriters_map
      | apply NoWriters_flatMap
      | (exact noWriters_lbasis_terms _ _ _ _)
      | (intro a _)



theorem CallsOK_block {S : List (String × Nat)} {b : YulBlock}
    (h : CallsOK S b) : CallsOK S [Stmt.block b] := by
  unfold CallsOK at *
  rw [Midfall.LoweringV3.callSitesSs.eq_2, Midfall.LoweringV3.callSitesSs.eq_1,
    Midfall.LoweringV3.callSitesS.eq_1, List.append_nil]
  exact h

theorem NoWriters_block {b : YulBlock} (h : NoWriters b) : NoWriters [Stmt.block b] := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 2, ?_⟩
  cases n with
  | zero => simp [noWritersFuel, noWritersScan] at hn
  | succ k => simpa [noWritersFuel, noWritersScan, noWritersStep] using hn

set_option maxHeartbeats 1000000 in
theorem block4_calls (nSets : Nat) (rots : List Int) (ps : List (List Int)) :
    CallsOK pcsCalls (pcsBlock4Ast nSets rots ps) := by
  unfold pcsBlock4Ast
  dsimp only
  repeat' first
    | exact CallsOK_nil' _
    | apply CallsOK_cons_append
    | apply CallsOK_cons_ne
    | apply CallsOK_append
    | apply CallsOK_map'
    | apply CallsOK_flatMap
    | (intro a _)
    | (apply CallsOK_block; exact setBlock_calls _ _ _ _)
    | (apply calls_none
       simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
         Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
         Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
         Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
         Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
         Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
         Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
         Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
         Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
         GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
         GenAst.yvar, GenAst.ylit, subFrom, GenAst.yblock]
       rfl)

set_option maxHeartbeats 1000000 in
theorem block4_noWriters (nSets : Nat) (rots : List Int) (ps : List (List Int)) :
    NoWriters (pcsBlock4Ast nSets rots ps) := by
  unfold pcsBlock4Ast
  dsimp only
  repeat' first
    | exact ⟨100, rfl⟩
    | apply NoWriters_cons_append
    | apply NoWriters_cons_ne
    | apply NoWriters_append
    | apply NoWriters_map
    | apply NoWriters_flatMap
    | (intro a _)
    | (apply NoWriters_block; exact setBlock_noWriters _ _ _ _)



set_option maxHeartbeats 1000000 in
theorem block3_calls (setIdx : Nat) (cis : List CommitmentEntry) (sets : IntermediateSets)
    (mptr : Nat) : CallsOK pcsCalls (pcsBlock3Ast setIdx cis sets mptr) := by
  unfold pcsBlock3Ast
  dsimp only
  by_cases hr : (qEvalStrategy cis == QEvalStrategy.rolled) = true <;>
    simp only [hr, ite_true, ite_false, reduceIte]
  · repeat' first
      | exact CallsOK_nil' _
      | apply CallsOK_cons_ne
      | apply CallsOK_cons_append
      | apply CallsOK_append
      | apply CallsOK_map'
      | apply CallsOK_flatMap
      | (intro a _)
      | (apply calls_none
         simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
           Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
           Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
           Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
           Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
           Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
           Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
           Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
           Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
           GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
           GenAst.yvar, GenAst.ylit, mstoreAdd, callSitesE_ptrExpr, callSitesE_wordExpr,
           callSitesE_x1Pow, callSitesE_valueExpr, callSitesSs_append, callSitesSs_map,
           callSitesSs_flatten_map, List.flatMap_eq_nil_iff, List.nil_append,
           List.append_nil, callSitesE_ite]
         all_goals simp)
  · repeat' first
      | exact CallsOK_nil' _
      | apply CallsOK_cons_ne
      | apply CallsOK_cons_append
      | apply CallsOK_append
      | apply CallsOK_map'
      | apply CallsOK_flatMap
      | (intro a _)
      | (apply calls_none
         simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
           Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
           Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
           Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
           Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
           Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
           Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
           Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
           Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
           GenAst.ylet, GenAst.yset, GenAst.yfor, GenAst.yif, GenAst.yexpr, GenAst.yop,
           GenAst.yvar, GenAst.ylit, mstoreAdd, callSitesE_ptrExpr, callSitesE_wordExpr,
           callSitesE_x1Pow, callSitesE_valueExpr, callSitesSs_append, callSitesSs_map,
           callSitesSs_flatten_map, List.flatMap_eq_nil_iff, List.nil_append,
           List.append_nil, callSitesE_ite]
         all_goals simp)

/-- A `for` loop is clean from its parts: the scan splits into init/condition/post/body, and the
    fuel is the max of the four. Used by the PCS block-3 body. -/
theorem NoWriters_forLoop {init post body : YulBlock} {c : Expr EVM.Op}
    (hi : NoWriters init) (hc : ScanClean (.e c)) (hp : NoWriters post)
    (hb : NoWriters body) : NoWriters [Stmt.forLoop init c post body] := by
  obtain ⟨ni, hi⟩ := hi
  obtain ⟨nc, hc⟩ := hc
  obtain ⟨np, hp⟩ := hp
  obtain ⟨nb, hb⟩ := hb
  refine ⟨max (max ni nc) (max np nb) + 2, ?_⟩
  have hi' : noWritersScan (max (max ni nc) (max np nb)) (.b init) = true :=
    noWritersScan_mono (by omega) hi
  have hc' : noWritersScan (max (max ni nc) (max np nb)) (.e c) = true :=
    noWritersScan_mono (by omega) hc
  have hp' : noWritersScan (max (max ni nc) (max np nb)) (.b post) = true :=
    noWritersScan_mono (by omega) hp
  have hb' : noWritersScan (max (max ni nc) (max np nb)) (.b body) = true :=
    noWritersScan_mono (by omega) hb
  simp only [noWritersFuel, noWritersScan, noWritersStep, hi', hc', hp', hb', Bool.and_true,
    Bool.true_and]

/-! ### `pcsBlock3Ast` NoWriters: the codec leaves and the rolled for body

  The writer scan reaches `wordExpr`/`ptrExpr` through `valueExpr`; both are
  `calldataload`/`mload` trees, not writers. The helpers below build `ScanClean`
  compositionally (no fuel recursion) and convert a clean statement to
  `NoWriters [s]`; the rolled arm's loop is closed by `NoWriters_forLoop`, and
  the straight arm's `wordExpr` fold reuses the same expression leaf. -/

theorem scanClean_e_lit (l : Literal) : ScanClean (.e (.lit l)) := ⟨1, rfl⟩
theorem scanClean_e_var (x : String) : ScanClean (.e (.var x)) := ⟨1, rfl⟩
theorem scanClean_es_nil : ScanClean (.es ([] : List (Expr EVM.Op))) := ⟨1, rfl⟩
theorem scanClean_es_of_forall {es : List (Expr EVM.Op)}
    (h : ∀ e ∈ es, ScanClean (.e e)) : ScanClean (.es es) := by
  induction es with
  | nil => exact scanClean_es_nil
  | cons e es ih =>
      exact scanClean_es_cons_rev (h e (by simp)) (ih (fun x hx => h x (by simp [hx])))
theorem scanClean_e_builtin_of {op : EVM.Op} {args : List (Expr EVM.Op)}
    (hw : Op.isWriter op = false) (h : ∀ e ∈ args, ScanClean (.e e)) :
    ScanClean (.e (.builtin op args)) :=
  scanClean_e_builtin_rev hw (scanClean_es_of_forall h)

theorem scanClean_valueExpr (v : MValue) : ScanClean (.e (valueExpr v)) := by
  unfold valueExpr
  split
  · split
    · exact scanClean_e_lit _
    · apply scanClean_e_builtin_of (op := Op.sub) (by rfl)
      intro e he; simp at he; rcases he with rfl | rfl
      · exact scanClean_e_lit _
      · exact scanClean_e_lit _
  · exact scanClean_e_var _
  · split
    · apply scanClean_e_builtin_of (op := Op.add) (by rfl)
      intro e he; simp at he; rcases he with rfl | rfl
      · exact scanClean_e_var _
      · exact scanClean_e_lit _
    · apply scanClean_e_builtin_of (op := Op.sub) (by rfl)
      intro e he; simp at he; rcases he with rfl | rfl
      · exact scanClean_e_var _
      · exact scanClean_e_lit _

theorem scanClean_ptrExpr (p : MPtr) : ScanClean (.e (ptrExpr p)) := by
  simpa [ptrExpr] using scanClean_valueExpr p.value

theorem scanClean_wordExpr (w : MWord) : ScanClean (.e (wordExpr w)) := by
  unfold wordExpr
  split
  · apply scanClean_e_builtin_of (op := Op.calldataload) (by rfl)
    intro e he; simp at he; subst e; exact scanClean_valueExpr _
  · apply scanClean_e_builtin_of (op := Op.mload) (by rfl)
    intro e he; simp at he; subst e; exact scanClean_valueExpr _

theorem noWriters_of_scanClean_s {s : Stmt EVM.Op} (h : ScanClean (.s s)) : NoWriters [s] :=
  scanClean_b_cons_rev h scanClean_nil

theorem noWriters_wordExpr_let (x : String) (w : MWord) :
    NoWriters [GenAst.ylet x (wordExpr w)] := by
  apply noWriters_of_scanClean_s
  simpa [GenAst.ylet] using scanClean_s_letDecl_some_rev (scanClean_wordExpr w)

theorem scanClean_x1Pow (i : Nat) : ScanClean (.e (x1Pow i)) := by
  unfold x1Pow
  apply scanClean_e_builtin_of (op := Op.mload) (by rfl)
  intro e he; simp at he; subst e
  apply scanClean_e_builtin_of (op := Op.add) (by rfl)
  intro e he; simp at he; rcases he with rfl | rfl
  · exact scanClean_e_var _
  · exact scanClean_e_lit _

theorem noWriters_wordExpr_fold (k i : Nat) (w : MWord) :
    NoWriters [GenAst.yset ("q_eval_set_" ++ toString k)
      (GenAst.yop Op.addmod [GenAst.yvar ("q_eval_set_" ++ toString k),
        GenAst.yop Op.mulmod [wordExpr w, x1Pow i, GenAst.yvar "r"], GenAst.yvar "r"])] := by
  apply noWriters_of_scanClean_s
  apply scanClean_s_assign_rev
  apply scanClean_e_builtin_of (op := Op.addmod) (by rfl)
  intro e he; simp at he; rcases he with rfl | rfl | rfl
  · exact scanClean_e_var _
  · apply scanClean_e_builtin_of (op := Op.mulmod) (by rfl)
    intro e he; simp at he; rcases he with rfl | rfl | rfl
    · exact scanClean_wordExpr _
    · exact scanClean_x1Pow _
    · exact scanClean_e_var _
  · exact scanClean_e_var _

theorem noWriters_rolled_body_item (k : Nat) :
    NoWriters [GenAst.yset ("q_eval_set_" ++ toString k)
      (GenAst.yop Op.addmod [GenAst.yvar ("q_eval_set_" ++ toString k),
        GenAst.yop Op.mulmod [GenAst.yop Op.mload [GenAst.yop Op.mload [
          (if k == 0 then GenAst.yvar "eval_p" else GenAst.yop Op.add [GenAst.yvar "eval_p", GenAst.ylit (k * wordBytes)])]],
          GenAst.yvar "pow", GenAst.yvar "r"], GenAst.yvar "r"])] := by
  apply noWriters_of_scanClean_s
  apply scanClean_s_assign_rev
  apply scanClean_e_builtin_of (op := Op.addmod) (by rfl)
  intro e he; simp at he; rcases he with rfl | rfl | rfl
  · exact scanClean_e_var _
  · apply scanClean_e_builtin_of (op := Op.mulmod) (by rfl)
    intro e he; simp at he; rcases he with rfl | rfl | rfl
    · apply scanClean_e_builtin_of (op := Op.mload) (by rfl)
      intro e he; simp at he; subst e
      apply scanClean_e_builtin_of (op := Op.mload) (by rfl)
      intro e he; simp at he; subst e
      split
      · exact scanClean_e_var _
      · apply scanClean_e_builtin_of (op := Op.add) (by rfl)
        intro e he; simp at he; rcases he with rfl | rfl
        · exact scanClean_e_var _
        · exact scanClean_e_lit _
    · exact scanClean_e_var _
    · exact scanClean_e_var _
  · exact scanClean_e_var _

set_option maxHeartbeats 2000000 in
theorem block3_noWriters (setIdx : Nat) (cis : List CommitmentEntry) (sets : IntermediateSets)
    (mptr : Nat) : NoWriters (pcsBlock3Ast setIdx cis sets mptr) := by
  unfold pcsBlock3Ast
  dsimp only
  split
  · repeat first
      | exact ⟨40, rfl⟩
      | apply NoWriters_cons_ne
      | apply NoWriters_cons_append
      | apply NoWriters_append
      | apply NoWriters_map
      | apply NoWriters_flatMap
      | apply NoWriters_forLoop
      | (exact noWriters_mstore_ptr _ _)
      | (exact noWriters_wordExpr_let _ _)
      | (exact noWriters_rolled_body_item _)
      | (intro a _)
  · repeat first
      | exact ⟨40, rfl⟩
      | apply NoWriters_append
      | apply NoWriters_map
      | apply NoWriters_flatMap
      | (exact noWriters_wordExpr_let _ _)
      | (exact noWriters_wordExpr_fold _ _ _)
      | (intro a _)


/-! ### Block 5: the fused final MSM

  `pcsBlock5Ast` is an `Except` computation: two shape guards, a nested
  `foldlM` over `enumIdx bySet` and each set's commitments, and a final block
  assembled from the fold's accumulator. The scan invariant is `CallsOK`/
  `NoWriters` of the accumulator; each step appends only call-free, non-writing
  pairs, and the linearization expansion contributes its own clean block. -/

theorem foldl_invariant' {α β : Type} {l : List α} {f : β → α → β} {P : β → Prop} {init : β}
    (hinit : P init) (hstep : ∀ a ∈ l, ∀ st, P st → P (f st a)) :
    P (List.foldl f init l) := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih (hinit := hstep a (by simp) init hinit)
        (fun b hb st hp => hstep b (by simp [hb]) st hp)

theorem foldlM_invariant' {α β : Type} {l : List α} {f : β → α → Except Midfall.Halo2.Fault β}
    {P : β → Prop} {init : β}
    (hinit : P init)
    (hstep : ∀ a ∈ l, ∀ st, P st → ∀ st', f st a = .ok st' → P st') :
    ∀ st', List.foldlM f init l = .ok st' → P st' := by
  induction l generalizing init with
  | nil =>
      intro st' h
      cases h
      exact hinit
  | cons a as ih =>
      intro st' h
      rw [List.foldlM_cons] at h
      cases hfa : f init a with
      | error e =>
          rw [hfa] at h
          change Except.bind (Except.error e) (fun st => List.foldlM f st as) = .ok st' at h
          cases h
      | ok st1 =>
          rw [hfa] at h
          change Except.bind (Except.ok st1) (fun st => List.foldlM f st as) = .ok st' at h
          simp only [Except.bind] at h
          exact ih (hinit := hstep a (by simp) init hinit st1 hfa)
            (fun b hb st hp st' h' => hstep b (by simp [hb]) st hp st' h') st' h

def pcsLinLimbStep (scratch numQuotients : Nat) (curVar : String) (linXSplit : Expr EVM.Op)
    (st : Nat × Block EVM.Op) (qIdx : Nat) : Nat × Block EVM.Op :=
  have pairBase := scratch + st.1 * g1MsmPairBytes
  have mut1 := [ GenAst.yexpr (GenAst.yop Op.mcopy [GenAst.ylit pairBase,
        GenAst.yop Op.add [GenAst.yvar "QUOTIENT_LIMB_COMMS_MPTR_BASE", GenAst.ylit (qIdx * g1Bytes)],
        GenAst.ylit g1Bytes])
    , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.ylit (pairBase + g1Bytes), GenAst.yvar curVar]) ]
  if qIdx + 1 != numQuotients then
    (st.1 + 1, st.2 ++ mut1 ++ [GenAst.yset curVar
      (GenAst.yop Op.mulmod [GenAst.yvar curVar, linXSplit, GenAst.yvar "r"])])
  else (st.1 + 1, st.2 ++ mut1)

def pcsLinSelStep (scratch : Nat) (dat : Midfall.Generator.Data) (queryVar : String)
    (panicSite : String) (st : Nat × Block EVM.Op) (x : Nat × Nat) :
    Except Midfall.Halo2.Fault (Nat × Block EVM.Op) := do
  have pairBase := scratch + st.1 * g1MsmPairBytes
  let fixed ← listGetMut dat.fixedComms x.2 panicSite
  have selectorScalar := GenAst.yop Op.mload [GenAst.yop Op.add [GenAst.yvar "SELECTOR_ACC_MPTR",
    GenAst.ylit (x.1 * wordBytes)]]
  pure (st.1 + 1, st.2 ++
    [ GenAst.yexpr (GenAst.yop Op.mcopy
        [GenAst.ylit pairBase, ptrExpr fixed.base, GenAst.ylit g1Bytes])
    , GenAst.yexpr (GenAst.yop Op.mstore
        [ GenAst.ylit (pairBase + g1Bytes)
        , GenAst.yop Op.mulmod [GenAst.yvar queryVar, selectorScalar, GenAst.yvar "r"] ]) ])

theorem pcsLinExpansion_eq (scratch startPair numQuotients : Nat)
    (simpleSelectorCols : List Nat) (dat : Midfall.Generator.Data)
    (queryVar curVar : String) (linXSplit : Expr EVM.Op) (panicSite : String) :
    pcsLinExpansion scratch startPair numQuotients simpleSelectorCols dat queryVar curVar
      linXSplit panicSite =
    (do
      let limb := List.foldl (pcsLinLimbStep scratch numQuotients curVar linXSplit)
        (startPair, []) (List.range numQuotients)
      let selRes ← List.foldlM (pcsLinSelStep scratch dat queryVar panicSite) (limb.1, [])
        (enumIdx simpleSelectorCols)
      pure (selRes.1, limb.2 ++ selRes.2)) := by
  unfold pcsLinExpansion pcsLinLimbStep pcsLinSelStep
  rfl


theorem CallsOK_cons {s : Stmt EVM.Op} {ss : YulBlock}
    (hs : CallsOK pcsCalls [s]) (hss : CallsOK pcsCalls ss) :
    CallsOK pcsCalls (s :: ss) := by
  simpa using CallsOK_append hs hss

theorem calls_pair {a b : Stmt EVM.Op}
    (ha : CallsOK pcsCalls [a]) (hb : CallsOK pcsCalls [b]) :
    CallsOK pcsCalls [a, b] := by
  simpa using CallsOK_append ha hb


theorem calls_mut1 (pairBase qIdx : Nat) (curVar : String) :
    CallsOK pcsCalls
      [ GenAst.yexpr (GenAst.yop Op.mcopy
          [GenAst.ylit pairBase,
            GenAst.yop Op.add [GenAst.yvar "QUOTIENT_LIMB_COMMS_MPTR_BASE", GenAst.ylit (qIdx * g1Bytes)],
            GenAst.ylit g1Bytes])
      , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.ylit (pairBase + g1Bytes), GenAst.yvar curVar]) ] := by
  apply calls_pair <;> apply calls_stmt_none <;>
    simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
      Midfall.LoweringV3.callSitesEs, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit,
      callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
      callSitesE_ite]

theorem calls_lin_limb_step (scratch numQuotients : Nat) (curVar : String) (linXSplit : Expr EVM.Op)
    (hlin : Midfall.LoweringV3.callSitesE linXSplit = [])
    (st : Nat × Block EVM.Op) (qIdx : Nat) (hst : CallsOK pcsCalls st.2) :
    CallsOK pcsCalls (pcsLinLimbStep scratch numQuotients curVar linXSplit st qIdx).2 := by
  unfold pcsLinLimbStep
  split
  · apply CallsOK_append
    · apply CallsOK_append
      · exact hst
      · exact calls_mut1 _ qIdx _
    · apply calls_stmt_none
      simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
        Midfall.LoweringV3.callSitesEs, GenAst.yset, GenAst.yop, GenAst.yvar, GenAst.ylit,
        callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
        callSitesE_ite, hlin]
  · apply CallsOK_append
    · exact hst
    · exact calls_mut1 _ qIdx _

theorem calls_lin_sel_step (scratch : Nat) (dat : Midfall.Generator.Data) (queryVar : String)
    (panicSite : String) (st : Nat × Block EVM.Op) (x : Nat × Nat)
    (hst : CallsOK pcsCalls st.2) :
    ∀ st', pcsLinSelStep scratch dat queryVar panicSite st x = .ok st' →
      CallsOK pcsCalls st'.2 := by
  intro st' h
  unfold pcsLinSelStep at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure] at h
  split at h
  · simp at h
  · cases h
    apply CallsOK_append
    · exact hst
    · apply calls_pair <;> apply calls_stmt_none <;>
        simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
          Midfall.LoweringV3.callSitesEs, GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit,
          callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
          callSitesE_ite]

theorem calls_lin_expansion (scratch startPair numQuotients : Nat)
    (simpleSelectorCols : List Nat) (dat : Midfall.Generator.Data)
    (queryVar curVar : String) (linXSplit : Expr EVM.Op)
    (hlin : Midfall.LoweringV3.callSitesE linXSplit = []) (panicSite : String) :
    ∀ r, pcsLinExpansion scratch startPair numQuotients simpleSelectorCols dat queryVar curVar
      linXSplit panicSite = .ok r → CallsOK pcsCalls r.2 := by
  intro r h
  rw [pcsLinExpansion_eq] at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure] at h
  split at h
  · simp at h
  · rename_i selRes hselEq
    cases h
    have hlimb : CallsOK pcsCalls
        (List.foldl (pcsLinLimbStep scratch numQuotients curVar linXSplit)
          (startPair, []) (List.range numQuotients)).2 := by
      apply foldl_invariant' (β := Nat × Block EVM.Op) (P := fun st => CallsOK pcsCalls st.2)
      · exact CallsOK_nil' _
      · intro qIdx _ st hst
        exact calls_lin_limb_step scratch numQuotients curVar linXSplit hlin st qIdx hst
    have hsel : ∀ st', List.foldlM (pcsLinSelStep scratch dat queryVar panicSite)
        ((List.foldl (pcsLinLimbStep scratch numQuotients curVar linXSplit)
          (startPair, []) (List.range numQuotients)).1, [])
        (enumIdx simpleSelectorCols) = .ok st' → CallsOK pcsCalls st'.2 := by
      apply foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => CallsOK pcsCalls st.2)
      · exact CallsOK_nil' _
      · intro a ha st hst st' hstep
        exact calls_lin_sel_step scratch dat queryVar panicSite st a hst st' hstep
    exact CallsOK_append hlimb (hsel selRes hselEq)


theorem NoWriters_cons {s : Stmt EVM.Op} {ss : YulBlock}
    (hs : NoWriters [s]) (hss : NoWriters ss) : NoWriters (s :: ss) := by
  simpa using NoWriters_append hs hss

theorem noWriters_pair {a b : Stmt EVM.Op}
    (ha : NoWriters [a]) (hb : NoWriters [b]) : NoWriters [a, b] := by
  simpa using NoWriters_append ha hb


theorem noWriters_mut1 (pairBase qIdx : Nat) (curVar : String) :
    NoWriters
      [ GenAst.yexpr (GenAst.yop Op.mcopy
          [GenAst.ylit pairBase,
            GenAst.yop Op.add [GenAst.yvar "QUOTIENT_LIMB_COMMS_MPTR_BASE", GenAst.ylit (qIdx * g1Bytes)],
            GenAst.ylit g1Bytes])
      , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.ylit (pairBase + g1Bytes), GenAst.yvar curVar]) ] := by
  apply noWriters_pair <;> exact ⟨100, rfl⟩

theorem noWriters_mcopy_ptr (pairBase : Nat) (p : MPtr) :
    NoWriters [GenAst.yexpr (GenAst.yop Op.mcopy
      [GenAst.ylit pairBase, ptrExpr p, GenAst.ylit g1Bytes])] := by
  refine ⟨100, ?_⟩
  unfold ptrExpr valueExpr GenAst.yexpr GenAst.yop
  split <;> (try split) <;> rfl

theorem noWriters_assign_mulmod3 (x : String) (a b c : Expr EVM.Op)
    (ha : ScanClean (.e a)) (hb : ScanClean (.e b)) (hc : ScanClean (.e c)) :
    NoWriters [GenAst.yset x (GenAst.yop Op.mulmod [a, b, c])] := by
  apply noWriters_of_scanClean_s
  apply scanClean_s_assign_rev
  apply scanClean_e_builtin_of (op := Op.mulmod) (by rfl)
  intro e he
  simp at he
  rcases he with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem noWriters_lin_limb_step (scratch numQuotients : Nat) (curVar : String)
    (linXSplit : Expr EVM.Op) (hlin : ScanClean (.e linXSplit))
    (st : Nat × Block EVM.Op) (qIdx : Nat) (hst : NoWriters st.2) :
    NoWriters (pcsLinLimbStep scratch numQuotients curVar linXSplit st qIdx).2 := by
  unfold pcsLinLimbStep
  split
  · apply NoWriters_append
    · apply NoWriters_append
      · exact hst
      · exact noWriters_mut1 _ qIdx _
    · exact noWriters_assign_mulmod3 curVar _ linXSplit _ (scanClean_e_var curVar) hlin (scanClean_e_var "r")
  · apply NoWriters_append
    · exact hst
    · exact noWriters_mut1 _ qIdx _

theorem noWriters_lin_sel_step (scratch : Nat) (dat : Midfall.Generator.Data) (queryVar : String)
    (panicSite : String) (st : Nat × Block EVM.Op) (x : Nat × Nat)
    (hst : NoWriters st.2) :
    ∀ st', pcsLinSelStep scratch dat queryVar panicSite st x = .ok st' → NoWriters st'.2 := by
  intro st' h
  unfold pcsLinSelStep at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure] at h
  split at h
  · simp at h
  · cases h
    apply NoWriters_append
    · exact hst
    · apply noWriters_pair
      · exact noWriters_mcopy_ptr _ _
      · exact ⟨100, rfl⟩

theorem noWriters_lin_expansion (scratch startPair numQuotients : Nat)
    (simpleSelectorCols : List Nat) (dat : Midfall.Generator.Data)
    (queryVar curVar : String) (linXSplit : Expr EVM.Op) (hlin : ScanClean (.e linXSplit))
    (panicSite : String) :
    ∀ r, pcsLinExpansion scratch startPair numQuotients simpleSelectorCols dat queryVar curVar
      linXSplit panicSite = .ok r → NoWriters r.2 := by
  intro r h
  rw [pcsLinExpansion_eq] at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure] at h
  split at h
  · simp at h
  · rename_i selRes hselEq
    cases h
    have hlimb : NoWriters
        (List.foldl (pcsLinLimbStep scratch numQuotients curVar linXSplit)
          (startPair, []) (List.range numQuotients)).2 := by
      apply foldl_invariant' (β := Nat × Block EVM.Op) (P := fun st => NoWriters st.2)
      · exact ⟨1, rfl⟩
      · intro qIdx _ st hst
        exact noWriters_lin_limb_step scratch numQuotients curVar linXSplit hlin st qIdx hst
    have hsel : ∀ st', List.foldlM (pcsLinSelStep scratch dat queryVar panicSite)
        ((List.foldl (pcsLinLimbStep scratch numQuotients curVar linXSplit)
          (startPair, []) (List.range numQuotients)).1, [])
        (enumIdx simpleSelectorCols) = .ok st' → NoWriters st'.2 := by
      apply foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => NoWriters st.2)
      · exact ⟨1, rfl⟩
      · intro a ha st hst st' hstep
        exact noWriters_lin_sel_step scratch dat queryVar panicSite st a hst st' hstep
    exact NoWriters_append hlimb (hsel selRes hselEq)


def pcsBlock5InnerStep (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch : Nat) (setIdx : Nat) (linComm : Midfall.Generator.EcPoint)
    (st : Nat × Block EVM.Op) (x : Nat × CommitmentEntry) :
    Except Midfall.Halo2.Fault (Nat × Block EVM.Op) :=
  match x with
  | (commitmentIdx, c) =>
    if ecPointBeq c.comm g1Identity = true then pure st
    else
      match st with
      | (pairIdx, acc) =>
        have scalar := pcsFinalMsmScalar setIdx commitmentIdx
        if ecPointBeq c.comm linComm = true then do
          let queryVar := "lin_query_scalar_" ++ toString pairIdx
          let curVar := "lin_cur_scalar_" ++ toString pairIdx
          let (n, ls) ← pcsLinExpansion finalMsmScratch pairIdx meta_.numQuotients
            meta_.simpleSelectorCols dat queryVar curVar (GenAst.yvar "lin_x_split")
            "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1788"
          pure (n, acc ++ [ GenAst.ylet queryVar scalar
            , GenAst.ylet curVar (GenAst.yop Op.mulmod
                [GenAst.yvar queryVar, GenAst.yvar "lin_one_minus_x_n", GenAst.yvar "r"]) ] ++ ls)
        else pure (pairIdx + 1, acc ++ pcsMsmPair
          (finalMsmScratch + pairIdx * g1MsmPairBytes) (commExpr c.comm) scalar)

def pcsBlock5OuterStep (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch : Nat) (linComm : Midfall.Generator.EcPoint)
    (outer : Nat × Block EVM.Op) (x : Nat × List CommitmentEntry) :
    Except Midfall.Halo2.Fault (Nat × Block EVM.Op) :=
  match x with
  | (setIdx, commitmentsInSet) =>
    List.foldlM (pcsBlock5InnerStep meta_ dat finalMsmScratch setIdx linComm)
      outer (enumIdx commitmentsInSet)

theorem pcsBlock5Ast_eq (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) (nSets finalMsmScratch : Nat) (truncatedChallenges : Bool) :
    pcsBlock5Ast meta_ dat bySet nSets finalMsmScratch truncatedChallenges =
    (do
      let linComm := linearizationComm dat
      let shape := finalMsmShape meta_ dat bySet
      let finalMsmTerms := shape.terms
      let finalMsmLen := shape.inputBytes
      unless finalMsmTerms * g1MsmPairBytes == finalMsmLen do
        throw (Midfall.Halo2.Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1677")
      let head := [ GenAst.ylet "x4" (GenAst.yop Op.mload [GenAst.yvar "X4_MPTR"])
                  , GenAst.ylet "lin_x_split" (GenAst.yop Op.mload [GenAst.yvar "QUOTIENT_MPTR"])
                  , GenAst.ylet "lin_one_minus_x_n" (GenAst.yop Op.mload [GenAst.yop Op.add
                      [GenAst.yvar "QUOTIENT_MPTR", GenAst.ylit wordBytes]])
                  , GenAst.ylet "Q_EVAL_CPTR" (GenAst.yop Op.mload [GenAst.yvar "Q_EVAL_CPTR_MPTR"]) ]
      let (pairIdxEnd, msmLines) ← List.foldlM
        (pcsBlock5OuterStep meta_ dat finalMsmScratch linComm) (0, []) (enumIdx bySet)
      unless pairIdxEnd + 1 == finalMsmTerms do
        throw (Midfall.Halo2.Fault.panic "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1816")
      let fComBase := finalMsmScratch + pairIdxEnd * g1MsmPairBytes
      pure (head ++ pcsX4PowersAst nSets truncatedChallenges ++ pcsVLinesAst nSets ++ msmLines ++
        [ GenAst.yexpr (GenAst.yop Op.mcopy
            [GenAst.ylit fComBase, GenAst.yvar "F_COM_MPTR", GenAst.ylit g1Bytes])
        , GenAst.yexpr (GenAst.yop Op.mstore
            [GenAst.ylit (fComBase + g1Bytes), GenAst.yvar ("x4_pow_" ++ toString nSets)])
        , GenAst.yif (GenAst.yvar "success")
            [ GenAst.yset "success" (GenAst.yop Op.staticcall
                [GenAst.ylit (Midfall.Yul.g1MsmGasPairs finalMsmTerms), GenAst.ylit 0x0c,
                  GenAst.ylit finalMsmScratch, GenAst.ylit finalMsmLen,
                  GenAst.yvar "FINAL_COM_MPTR", GenAst.ylit g1Bytes])
            , GenAst.yset "success" (GenAst.yop Op.and
                [GenAst.yvar "success", GenAst.yop Op.eq
                  [GenAst.yop Op.returndatasize [], GenAst.ylit g1Bytes]]) ]
        , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.yvar "V_MPTR", GenAst.yvar "v"]) ])) := by
  rfl


theorem callSitesE_pcsFinalMsmScalar (setIdx commitmentIdx : Nat) :
    Midfall.LoweringV3.callSitesE (pcsFinalMsmScalar setIdx commitmentIdx) = [] := by
  unfold pcsFinalMsmScalar
  split <;> (try split) <;>
    simp [callSitesE_lit, callSitesE_var, callSitesE_x1Pow,
      Midfall.LoweringV3.callSitesE, Midfall.LoweringV3.callSitesEs, GenAst.yop,
      GenAst.yvar, GenAst.ylit]


theorem calls_head (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) :
    CallsOK pcsCalls
      [ GenAst.ylet "x4" (GenAst.yop Op.mload [GenAst.yvar "X4_MPTR"])
      , GenAst.ylet "lin_x_split" (GenAst.yop Op.mload [GenAst.yvar "QUOTIENT_MPTR"])
      , GenAst.ylet "lin_one_minus_x_n" (GenAst.yop Op.mload [GenAst.yop Op.add
          [GenAst.yvar "QUOTIENT_MPTR", GenAst.ylit wordBytes]])
      , GenAst.ylet "Q_EVAL_CPTR" (GenAst.yop Op.mload [GenAst.yvar "Q_EVAL_CPTR_MPTR"]) ] := by
  repeat' first
    | apply CallsOK_cons_ne
    | apply calls_stmt_none
    | simp [Midfall.LoweringV3.callSitesS, Midfall.LoweringV3.callSitesE,
        Midfall.LoweringV3.callSitesEs, GenAst.ylet, GenAst.yop, GenAst.yvar, GenAst.ylit,
        callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
        callSitesE_ite]

theorem calls_final (finalMsmTerms finalMsmScratch finalMsmLen pairIdxEnd nSets : Nat) :
    CallsOK pcsCalls
      [ GenAst.yexpr (GenAst.yop Op.mcopy
          [GenAst.ylit (finalMsmScratch + pairIdxEnd * g1MsmPairBytes), GenAst.yvar "F_COM_MPTR", GenAst.ylit g1Bytes])
      , GenAst.yexpr (GenAst.yop Op.mstore
          [GenAst.ylit (finalMsmScratch + pairIdxEnd * g1MsmPairBytes + g1Bytes),
            GenAst.yvar ("x4_pow_" ++ toString nSets)])
      , GenAst.yif (GenAst.yvar "success")
          [ GenAst.yset "success" (GenAst.yop Op.staticcall
              [GenAst.ylit (Midfall.Yul.g1MsmGasPairs finalMsmTerms), GenAst.ylit 0x0c,
                GenAst.ylit finalMsmScratch, GenAst.ylit finalMsmLen,
                GenAst.yvar "FINAL_COM_MPTR", GenAst.ylit g1Bytes])
          , GenAst.yset "success" (GenAst.yop Op.and
              [GenAst.yvar "success", GenAst.yop Op.eq
                [GenAst.yop Op.returndatasize [], GenAst.ylit g1Bytes]]) ]
      , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.yvar "V_MPTR", GenAst.yvar "v"]) ] := by
  repeat' first
    | apply CallsOK_cons_ne
    | apply calls_stmt_none
    | simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
        Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
        Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
        Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
        Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
        Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
        Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
        Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
        Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
        GenAst.yexpr, GenAst.yset, GenAst.yif, GenAst.yop, GenAst.yvar, GenAst.ylit,
        callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
        callSitesE_ite]
      rfl


theorem calls_inner_step (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch setIdx : Nat) (linComm : Midfall.Generator.EcPoint)
    (st : Nat × Block EVM.Op) (x : Nat × CommitmentEntry) (hst : CallsOK pcsCalls st.2) :
    ∀ st', pcsBlock5InnerStep meta_ dat finalMsmScratch setIdx linComm st x = .ok st' →
      CallsOK pcsCalls st'.2 := by
  intro st' h
  rcases x with ⟨commitmentIdx, c⟩
  rcases st with ⟨pairIdx, acc⟩
  unfold pcsBlock5InnerStep at h
  dsimp only at h
  by_cases hid : ecPointBeq c.comm g1Identity = true
  · simp [hid] at h
    cases h
    exact hst
  · simp [hid] at h
    by_cases hlin : ecPointBeq c.comm linComm = true
    · simp [hlin] at h
      cases hres : pcsLinExpansion finalMsmScratch pairIdx meta_.numQuotients
          meta_.simpleSelectorCols dat ("lin_query_scalar_" ++ pairIdx.repr)
          ("lin_cur_scalar_" ++ pairIdx.repr) (GenAst.yvar "lin_x_split")
          "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1788" with
      | error e => simp [hres] at h
      | ok res =>
          rcases res with ⟨n, ls⟩
          simp [hres] at h
          cases h
          apply CallsOK_append
          · exact hst
          · apply CallsOK_cons_ne
            · apply calls_stmt_none
              simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
                Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
                Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
                Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
                Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
                Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
                Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
                Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
                Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
                GenAst.ylet, GenAst.yop, GenAst.yvar, GenAst.ylit]
              exact callSitesE_pcsFinalMsmScalar _ _
            · apply CallsOK_cons
              · apply calls_stmt_none
                simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
                  Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
                  Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
                  Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
                  Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
                  Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
                  Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
                  Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
                  Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
                  GenAst.ylet, GenAst.yop, GenAst.yvar, GenAst.ylit]
                rfl
              · exact calls_lin_expansion finalMsmScratch pairIdx meta_.numQuotients
                  meta_.simpleSelectorCols dat _ _ (GenAst.yvar "lin_x_split")
                  (by simp [GenAst.yvar, callSitesE_var]) _ (n, ls) hres
    · rw [if_neg hlin] at h
      cases h
      apply CallsOK_append
      · exact hst
      · apply calls_pair
        · apply calls_stmt_none
          simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
            Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
            Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
            Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
            Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
            Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
            Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
            Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
            Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
            GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit, commExpr,
            callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
            callSitesE_ite, callSitesE_pcsFinalMsmScalar]
          rfl
        · apply calls_stmt_none
          simp only [Midfall.LoweringV3.callSitesSs.eq_1, Midfall.LoweringV3.callSitesSs.eq_2,
            Midfall.LoweringV3.callSitesS.eq_1, Midfall.LoweringV3.callSitesS.eq_2,
            Midfall.LoweringV3.callSitesS.eq_3, Midfall.LoweringV3.callSitesS.eq_4,
            Midfall.LoweringV3.callSitesS.eq_5, Midfall.LoweringV3.callSitesS.eq_6,
            Midfall.LoweringV3.callSitesS.eq_7, Midfall.LoweringV3.callSitesS.eq_8,
            Midfall.LoweringV3.callSitesS.eq_9, Midfall.LoweringV3.callSitesS.eq_10,
            Midfall.LoweringV3.callSitesE.eq_1, Midfall.LoweringV3.callSitesE.eq_2,
            Midfall.LoweringV3.callSitesE.eq_3, callSitesE_lit, callSitesE_var,
            Midfall.LoweringV3.callSitesEs.eq_1, Midfall.LoweringV3.callSitesEs.eq_2,
            GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit,
            callSitesE_ptrExpr, callSitesE_wordExpr, callSitesE_x1Pow, callSitesE_valueExpr,
            callSitesE_ite, callSitesE_pcsFinalMsmScalar]
          rfl

theorem calls_outer_step (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch : Nat) (linComm : Midfall.Generator.EcPoint)
    (outer : Nat × Block EVM.Op) (x : Nat × List CommitmentEntry)
    (h : CallsOK pcsCalls outer.2) :
    ∀ st', pcsBlock5OuterStep meta_ dat finalMsmScratch linComm outer x = .ok st' →
      CallsOK pcsCalls st'.2 := by
  intro st' hstep
  unfold pcsBlock5OuterStep at hstep
  exact foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => CallsOK pcsCalls st.2)
    (hinit := h)
    (hstep := fun a ha st hst st' hs =>
      calls_inner_step meta_ dat finalMsmScratch x.1 linComm st a hst st' hs)
    st' hstep


theorem calls_outer_fold (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) (finalMsmScratch : Nat) :
    ∀ st', List.foldlM (pcsBlock5OuterStep meta_ dat finalMsmScratch
      (linearizationComm dat)) (0, []) (enumIdx bySet) = .ok st' →
      CallsOK pcsCalls st'.2 := by
  intro st' h
  exact foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => CallsOK pcsCalls st.2)
    (hinit := CallsOK_nil' _)
    (hstep := fun a ha st hst st' hs =>
      calls_outer_step meta_ dat finalMsmScratch (linearizationComm dat) st a hst st' hs)
    st' h


theorem block5_calls (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) (nSets finalMsmScratch : Nat)
    (truncatedChallenges : Bool) :
    ∀ blocks, pcsBlock5Ast meta_ dat bySet nSets finalMsmScratch truncatedChallenges = .ok blocks →
      CallsOK pcsCalls blocks := by
  intro blocks h
  rw [pcsBlock5Ast_eq] at h
  dsimp only at h
  split at h
  · cases hfold : List.foldlM (pcsBlock5OuterStep meta_ dat finalMsmScratch
        (linearizationComm dat)) (0, []) (enumIdx bySet) with
    | error e =>
        simp only [Bind.bind, Except.bind, Pure.pure] at h
        simp [hfold] at h
    | ok st =>
        simp [hfold] at h
        simp only [Bind.bind, Except.bind, Pure.pure] at h
        split at h
        · cases h
          have hfoldOK : CallsOK pcsCalls st.2 :=
            calls_outer_fold meta_ dat bySet finalMsmScratch st hfold
          have htail : CallsOK pcsCalls
              (pcsX4PowersAst nSets truncatedChallenges ++
                (pcsVLinesAst nSets ++
                  (st.2 ++
                    [ GenAst.yexpr (GenAst.yop Op.mcopy
                        [GenAst.ylit (finalMsmScratch + st.1 * g1MsmPairBytes),
                          GenAst.yvar "F_COM_MPTR", GenAst.ylit g1Bytes])
                    , GenAst.yexpr (GenAst.yop Op.mstore
                        [GenAst.ylit (finalMsmScratch + st.1 * g1MsmPairBytes + g1Bytes),
                          GenAst.yvar ("x4_pow_" ++ toString nSets)])
                    , GenAst.yif (GenAst.yvar "success")
                        [ GenAst.yset "success" (GenAst.yop Op.staticcall
                            [GenAst.ylit (Midfall.Yul.g1MsmGasPairs
                                (finalMsmShape meta_ dat bySet).terms), GenAst.ylit 0x0c,
                              GenAst.ylit finalMsmScratch,
                              GenAst.ylit (finalMsmShape meta_ dat bySet).inputBytes,
                              GenAst.yvar "FINAL_COM_MPTR", GenAst.ylit g1Bytes])
                        , GenAst.yset "success" (GenAst.yop Op.and
                            [GenAst.yvar "success", GenAst.yop Op.eq
                              [GenAst.yop Op.returndatasize [], GenAst.ylit g1Bytes]]) ]
                    , GenAst.yexpr (GenAst.yop Op.mstore
                        [GenAst.yvar "V_MPTR", GenAst.yvar "v"]) ]))) := by
            apply CallsOK_append
            · exact x4_calls nSets truncatedChallenges
            · apply CallsOK_append
              · exact v_calls nSets
              · apply CallsOK_append
                · exact hfoldOK
                · exact calls_final (finalMsmShape meta_ dat bySet).terms
                    finalMsmScratch (finalMsmShape meta_ dat bySet).inputBytes st.1 nSets
          simpa [List.append_assoc] using CallsOK_append (calls_head meta_ dat bySet) htail
        · cases h
  · cases h


theorem scanClean_pcsFinalMsmScalar (setIdx commitmentIdx : Nat) :
    ScanClean (.e (pcsFinalMsmScalar setIdx commitmentIdx)) := by
  unfold pcsFinalMsmScalar
  split <;> (try split)
  · exact scanClean_e_lit _
  · exact scanClean_e_var _
  · exact scanClean_x1Pow _
  · apply scanClean_e_builtin_of (op := Op.mulmod) (by rfl)
    intro e he
    simp at he
    rcases he with rfl | rfl | rfl
    · exact scanClean_x1Pow _
    · exact scanClean_e_var _
    · exact scanClean_e_var _

theorem noWriters_head (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) :
    NoWriters
      [ GenAst.ylet "x4" (GenAst.yop Op.mload [GenAst.yvar "X4_MPTR"])
      , GenAst.ylet "lin_x_split" (GenAst.yop Op.mload [GenAst.yvar "QUOTIENT_MPTR"])
      , GenAst.ylet "lin_one_minus_x_n" (GenAst.yop Op.mload [GenAst.yop Op.add
          [GenAst.yvar "QUOTIENT_MPTR", GenAst.ylit wordBytes]])
      , GenAst.ylet "Q_EVAL_CPTR" (GenAst.yop Op.mload [GenAst.yvar "Q_EVAL_CPTR_MPTR"]) ] := by
  repeat' first
    | exact ⟨100, rfl⟩
    | apply NoWriters_cons_ne

theorem noWriters_final (finalMsmTerms finalMsmScratch finalMsmLen pairIdxEnd nSets : Nat) :
    NoWriters
      [ GenAst.yexpr (GenAst.yop Op.mcopy
          [GenAst.ylit (finalMsmScratch + pairIdxEnd * g1MsmPairBytes),
            GenAst.yvar "F_COM_MPTR", GenAst.ylit g1Bytes])
      , GenAst.yexpr (GenAst.yop Op.mstore
          [GenAst.ylit (finalMsmScratch + pairIdxEnd * g1MsmPairBytes + g1Bytes),
            GenAst.yvar ("x4_pow_" ++ toString nSets)])
      , GenAst.yif (GenAst.yvar "success")
          [ GenAst.yset "success" (GenAst.yop Op.staticcall
              [GenAst.ylit (Midfall.Yul.g1MsmGasPairs finalMsmTerms), GenAst.ylit 0x0c,
                GenAst.ylit finalMsmScratch, GenAst.ylit finalMsmLen,
                GenAst.yvar "FINAL_COM_MPTR", GenAst.ylit g1Bytes])
          , GenAst.yset "success" (GenAst.yop Op.and
              [GenAst.yvar "success", GenAst.yop Op.eq
                [GenAst.yop Op.returndatasize [], GenAst.ylit g1Bytes]]) ]
      , GenAst.yexpr (GenAst.yop Op.mstore [GenAst.yvar "V_MPTR", GenAst.yvar "v"]) ] := by
  repeat' first
    | exact ⟨100, rfl⟩
    | apply NoWriters_cons_ne

theorem noWriters_let_scalar (queryVar : String) (setIdx commitmentIdx : Nat) :
    NoWriters [GenAst.ylet queryVar (pcsFinalMsmScalar setIdx commitmentIdx)] := by
  apply noWriters_of_scanClean_s
  simpa [GenAst.ylet] using
    scanClean_s_letDecl_some_rev (scanClean_pcsFinalMsmScalar setIdx commitmentIdx)

theorem noWriters_let_cur (queryVar curVar : String) :
    NoWriters [GenAst.ylet curVar (GenAst.yop Op.mulmod
      [GenAst.yvar queryVar, GenAst.yvar "lin_one_minus_x_n", GenAst.yvar "r"])] := by
  apply noWriters_of_scanClean_s
  apply scanClean_s_letDecl_some_rev
  apply scanClean_e_builtin_of (op := Op.mulmod) (by rfl)
  intro e he
  simp at he
  rcases he with rfl | rfl | rfl
  · exact scanClean_e_var _
  · exact scanClean_e_var _
  · exact scanClean_e_var _

theorem noWriters_inner_step (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch setIdx : Nat) (linComm : Midfall.Generator.EcPoint)
    (st : Nat × Block EVM.Op) (x : Nat × CommitmentEntry) (hst : NoWriters st.2) :
    ∀ st', pcsBlock5InnerStep meta_ dat finalMsmScratch setIdx linComm st x = .ok st' →
      NoWriters st'.2 := by
  intro st' h
  rcases x with ⟨commitmentIdx, c⟩
  rcases st with ⟨pairIdx, acc⟩
  unfold pcsBlock5InnerStep at h
  dsimp only at h
  by_cases hid : ecPointBeq c.comm g1Identity = true
  · simp [hid] at h
    cases h
    exact hst
  · simp [hid] at h
    by_cases hlin : ecPointBeq c.comm linComm = true
    · simp [hlin] at h
      cases hres : pcsLinExpansion finalMsmScratch pairIdx meta_.numQuotients
          meta_.simpleSelectorCols dat ("lin_query_scalar_" ++ pairIdx.repr)
          ("lin_cur_scalar_" ++ pairIdx.repr) (GenAst.yvar "lin_x_split")
          "proofs/solidity-verifier/src/lowering/kzg/mod.rs:1788" with
      | error e => simp [hres] at h
      | ok res =>
          rcases res with ⟨n, ls⟩
          simp [hres] at h
          cases h
          apply NoWriters_append
          · exact hst
          · apply NoWriters_cons
            · exact noWriters_let_scalar _ _ _
            · apply NoWriters_cons
              · exact noWriters_let_cur _ _
              · exact noWriters_lin_expansion finalMsmScratch pairIdx meta_.numQuotients
                  meta_.simpleSelectorCols dat _ _ (GenAst.yvar "lin_x_split")
                  (scanClean_e_var _) _ (n, ls) hres
    · rw [if_neg hlin] at h
      cases h
      apply NoWriters_append
      · exact hst
      · apply noWriters_pair
        · apply noWriters_mcopy_ptr
        · apply noWriters_of_scanClean_s
          apply scanClean_s_exprStmt_rev
          apply scanClean_e_builtin_of (op := Op.mstore) (by rfl)
          intro e he
          simp at he
          rcases he with rfl | rfl
          · exact scanClean_e_lit _
          · exact scanClean_pcsFinalMsmScalar _ _

theorem noWriters_outer_step (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (finalMsmScratch : Nat) (linComm : Midfall.Generator.EcPoint)
    (outer : Nat × Block EVM.Op) (x : Nat × List CommitmentEntry)
    (h : NoWriters outer.2) :
    ∀ st', pcsBlock5OuterStep meta_ dat finalMsmScratch linComm outer x = .ok st' →
      NoWriters st'.2 := by
  intro st' hstep
  unfold pcsBlock5OuterStep at hstep
  exact foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => NoWriters st.2)
    (hinit := h)
    (hstep := fun a ha st hst st' hs =>
      noWriters_inner_step meta_ dat finalMsmScratch x.1 linComm st a hst st' hs)
    st' hstep

theorem noWriters_outer_fold (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) (finalMsmScratch : Nat) :
    ∀ st', List.foldlM (pcsBlock5OuterStep meta_ dat finalMsmScratch
      (linearizationComm dat)) (0, []) (enumIdx bySet) = .ok st' → NoWriters st'.2 := by
  intro st' h
  exact foldlM_invariant' (β := Nat × Block EVM.Op) (P := fun st => NoWriters st.2)
    (hinit := ⟨1, rfl⟩)
    (hstep := fun a ha st hst st' hs =>
      noWriters_outer_step meta_ dat finalMsmScratch (linearizationComm dat) st a hst st' hs)
    st' h


theorem block5_noWriters (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (bySet : List (List CommitmentEntry)) (nSets finalMsmScratch : Nat)
    (truncatedChallenges : Bool) :
    ∀ blocks, pcsBlock5Ast meta_ dat bySet nSets finalMsmScratch truncatedChallenges = .ok blocks →
      NoWriters blocks := by
  intro blocks h
  rw [pcsBlock5Ast_eq] at h
  dsimp only at h
  split at h
  · cases hfold : List.foldlM (pcsBlock5OuterStep meta_ dat finalMsmScratch
        (linearizationComm dat)) (0, []) (enumIdx bySet) with
    | error e =>
        simp only [Bind.bind, Except.bind, Pure.pure] at h
        simp [hfold] at h
    | ok st =>
        simp [hfold] at h
        simp only [Bind.bind, Except.bind, Pure.pure] at h
        split at h
        · cases h
          have hfoldOK : NoWriters st.2 :=
            noWriters_outer_fold meta_ dat bySet finalMsmScratch st hfold
          have htail : NoWriters
              (pcsX4PowersAst nSets truncatedChallenges ++
                (pcsVLinesAst nSets ++
                  (st.2 ++
                    [ GenAst.yexpr (GenAst.yop Op.mcopy
                        [GenAst.ylit (finalMsmScratch + st.1 * g1MsmPairBytes),
                          GenAst.yvar "F_COM_MPTR", GenAst.ylit g1Bytes])
                    , GenAst.yexpr (GenAst.yop Op.mstore
                        [GenAst.ylit (finalMsmScratch + st.1 * g1MsmPairBytes + g1Bytes),
                          GenAst.yvar ("x4_pow_" ++ toString nSets)])
                    , GenAst.yif (GenAst.yvar "success")
                        [ GenAst.yset "success" (GenAst.yop Op.staticcall
                            [GenAst.ylit (Midfall.Yul.g1MsmGasPairs
                                (finalMsmShape meta_ dat bySet).terms), GenAst.ylit 0x0c,
                              GenAst.ylit finalMsmScratch,
                              GenAst.ylit (finalMsmShape meta_ dat bySet).inputBytes,
                              GenAst.yvar "FINAL_COM_MPTR", GenAst.ylit g1Bytes])
                        , GenAst.yset "success" (GenAst.yop Op.and
                            [GenAst.yvar "success", GenAst.yop Op.eq
                              [GenAst.yop Op.returndatasize [], GenAst.ylit g1Bytes]]) ]
                    , GenAst.yexpr (GenAst.yop Op.mstore
                        [GenAst.yvar "V_MPTR", GenAst.yvar "v"]) ]))) := by
            apply NoWriters_append
            · exact x4_noWriters nSets truncatedChallenges
            · apply NoWriters_append
              · exact v_noWriters nSets
              · apply NoWriters_append
                · exact hfoldOK
                · exact noWriters_final (finalMsmShape meta_ dat bySet).terms
                    finalMsmScratch (finalMsmShape meta_ dat bySet).inputBytes st.1 nSets
          simpa [List.append_assoc] using NoWriters_append (noWriters_head meta_ dat bySet) htail
        · cases h
  · cases h


theorem mapM_block3_calls (sets : IntermediateSets) (b3 : List (List CommitmentEntry))
    (mptr : Nat) :
    ∀ blocks, List.mapM (fun x => (pure (pcsBlock3Ast x.1 x.2 sets mptr) :
      Except Midfall.Halo2.Fault (Block EVM.Op))) (enumIdx b3) = .ok blocks →
      ∀ b ∈ blocks, CallsOK pcsCalls b := by
  intro blocks h b hb
  rw [List.mapM_pure] at h
  cases h
  simp only [List.mem_map] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact block3_calls x.1 x.2 sets mptr

theorem mapM_block3_noWriters (sets : IntermediateSets) (b3 : List (List CommitmentEntry))
    (mptr : Nat) :
    ∀ blocks, List.mapM (fun x => (pure (pcsBlock3Ast x.1 x.2 sets mptr) :
      Except Midfall.Halo2.Fault (Block EVM.Op))) (enumIdx b3) = .ok blocks →
      ∀ b ∈ blocks, NoWriters b := by
  intro blocks h b hb
  rw [List.mapM_pure] at h
  cases h
  simp only [List.mem_map] at hb
  obtain ⟨x, _, rfl⟩ := hb
  exact block3_noWriters x.1 x.2 sets mptr

theorem callsOK_of_mem_pcsBlocks_no2 {S : List (String × Nat)}
    {block1 block4 block5 block6 : Block EVM.Op} {block3 : List (Block EVM.Op)}
    (h1 : CallsOK S block1) (h3 : ∀ b ∈ block3, CallsOK S b)
    (h4 : CallsOK S block4) (h5 : CallsOK S block5) (h6 : CallsOK S block6)
    {b : Block EVM.Op}
    (hb : b ∈ block1 :: (block3 ++ [block4, block5, block6])) : CallsOK S b := by
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_nil_iff,
    or_false, false_or] at hb
  rcases hb with rfl | hb | rfl | rfl | rfl
  · exact h1
  · exact h3 _ hb
  · exact h4
  · exact h5
  · exact h6

theorem callsOK_of_mem_pcsBlocks_2 {S : List (String × Nat)}
    {block1 block2 block4 block5 block6 : Block EVM.Op} {block3 : List (Block EVM.Op)}
    (h1 : CallsOK S block1) (h2 : CallsOK S block2)
    (h3 : ∀ b ∈ block3, CallsOK S b)
    (h4 : CallsOK S block4) (h5 : CallsOK S block5) (h6 : CallsOK S block6)
    {b : Block EVM.Op}
    (hb : b ∈ block1 :: block2 :: (block3 ++ [block4, block5, block6])) : CallsOK S b := by
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_nil_iff,
    or_false, false_or] at hb
  rcases hb with rfl | rfl | hb | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3 _ hb
  · exact h4
  · exact h5
  · exact h6

theorem computationsAst_calls (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (memory : VerifierMemoryLayout) (trunc : Bool) :
    ∀ blocks, computationsAst meta_ dat memory trunc false = .ok blocks →
      ∀ b ∈ blocks, CallsOK pcsCalls b := by
  intro blocks h
  unfold computationsAst at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.map, List.mapM_pure] at h
  repeat' first
    | split at h
    | simp at h
    | cases h
  case h_2.isTrue.refl => simp_all
  case h_2.isTrue.isTrue.refl => simp_all
  case h_2.isFalse.isTrue.refl => simp_all
  case h_2.isTrue.isFalse.refl =>
    intro b hb
    refine callsOK_of_mem_pcsBlocks_2 ?_ ?_ ?_ ?_ ?_ ?_ hb
    · apply block1_calls
    · apply block2_calls
    · apply mapM_block3_calls
      assumption
    · apply block4_calls
    · apply block5_calls
      assumption
    · apply block6_calls
  case h_2.isFalse.isFalse.refl =>
    intro b hb
    refine callsOK_of_mem_pcsBlocks_no2 ?_ ?_ ?_ ?_ ?_ hb
    · apply block1_calls
    · apply mapM_block3_calls
      assumption
    · apply block4_calls
    · apply block5_calls
      assumption
    · apply block6_calls


theorem noWriters_of_mem_pcsBlocks_no2
    {block1 block4 block5 block6 : Block EVM.Op} {block3 : List (Block EVM.Op)}
    (h1 : NoWriters block1) (h3 : ∀ b ∈ block3, NoWriters b)
    (h4 : NoWriters block4) (h5 : NoWriters block5) (h6 : NoWriters block6)
    {b : Block EVM.Op}
    (hb : b ∈ block1 :: (block3 ++ [block4, block5, block6])) : NoWriters b := by
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_nil_iff,
    or_false, false_or] at hb
  rcases hb with rfl | hb | rfl | rfl | rfl
  · exact h1
  · exact h3 _ hb
  · exact h4
  · exact h5
  · exact h6

theorem noWriters_of_mem_pcsBlocks_2
    {block1 block2 block4 block5 block6 : Block EVM.Op} {block3 : List (Block EVM.Op)}
    (h1 : NoWriters block1) (h2 : NoWriters block2)
    (h3 : ∀ b ∈ block3, NoWriters b)
    (h4 : NoWriters block4) (h5 : NoWriters block5) (h6 : NoWriters block6)
    {b : Block EVM.Op}
    (hb : b ∈ block1 :: block2 :: (block3 ++ [block4, block5, block6])) : NoWriters b := by
  simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.mem_nil_iff,
    or_false, false_or] at hb
  rcases hb with rfl | rfl | hb | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3 _ hb
  · exact h4
  · exact h5
  · exact h6

theorem computationsAst_noWriters (meta_ : ConstraintSystemMeta) (dat : Midfall.Generator.Data)
    (memory : VerifierMemoryLayout) (trunc : Bool) :
    ∀ blocks, computationsAst meta_ dat memory trunc false = .ok blocks →
      ∀ b ∈ blocks, NoWriters b := by
  intro blocks h
  unfold computationsAst at h
  dsimp only at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.map, List.mapM_pure] at h
  repeat' first
    | split at h
    | simp at h
    | cases h
  case h_2.isTrue.refl => simp_all
  case h_2.isTrue.isTrue.refl => simp_all
  case h_2.isFalse.isTrue.refl => simp_all
  case h_2.isTrue.isFalse.refl =>
    intro b hb
    refine noWriters_of_mem_pcsBlocks_2 ?_ ?_ ?_ ?_ ?_ ?_ hb
    · apply block1_noWriters
    · apply block2_noWriters
    · apply mapM_block3_noWriters
      assumption
    · apply block4_noWriters
    · apply block5_noWriters
      assumption
    · apply block6_noWriters
  case h_2.isFalse.isFalse.refl =>
    intro b hb
    refine noWriters_of_mem_pcsBlocks_no2 ?_ ?_ ?_ ?_ ?_ hb
    · apply block1_noWriters
    · apply mapM_block3_noWriters
      assumption
    · apply block4_noWriters
    · apply block5_noWriters
      assumption
    · apply block6_noWriters


/-! ### From per-block facts to the PCS slice

  `emitPcsFromPlan` is `[]` on a fault / empty plan and `[Stmt.block (blocks.map Stmt.block)]`
  otherwise, so the slice inherits each emitted block's scan. These two lemmas turn a per-block
  hypothesis (the shape the block facts above have) into the slice's scan. -/

theorem CallsOK_blocks_map {S : List (String × Nat)} (blocks : List YulBlock)
    (h : ∀ b ∈ blocks, CallsOK S b) : CallsOK S (blocks.map Stmt.block) := by
  apply CallsOK_map'
  intro b hb
  exact CallsOK_block (h b hb)

theorem NoWriters_blocks_map (blocks : List YulBlock)
    (h : ∀ b ∈ blocks, NoWriters b) : NoWriters (blocks.map Stmt.block) := by
  apply NoWriters_map
  intro b hb
  exact NoWriters_block (h b hb)

theorem CallsOK_emitPcsFromPlan_of (pv : PlanView) {S : List (String × Nat)}
    (h : ∀ blocks, Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false = .ok blocks → ∀ b ∈ blocks, CallsOK S b) :
    CallsOK S (GenAst.emitPcsFromPlan pv) := by
  unfold GenAst.emitPcsFromPlan
  cases hc : Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
    pv.truncatedChallenges false with
  | error e => simp [hc]; exact CallsOK_nil' _
  | ok blocks =>
      cases blocks with
      | nil => simp [hc]; exact CallsOK_nil' _
      | cons b bs =>
          simp only [hc]
          exact CallsOK_block (CallsOK_blocks_map (S := S) (b :: bs) (h (b :: bs) hc))

theorem NoWriters_emitPcsFromPlan_of (pv : PlanView)
    (h : ∀ blocks, Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false = .ok blocks → ∀ b ∈ blocks, NoWriters b) :
    NoWriters (GenAst.emitPcsFromPlan pv) := by
  unfold GenAst.emitPcsFromPlan
  cases hc : Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
    pv.truncatedChallenges false with
  | error e => simp [hc]; exact ⟨1, rfl⟩
  | ok blocks =>
      cases blocks with
      | nil => simp [hc]; exact ⟨1, rfl⟩
      | cons b bs =>
          simp only [hc]
          exact NoWriters_block (NoWriters_blocks_map (b :: bs) (h (b :: bs) hc))

/-- `callsResolved` of `mainAsmRaw` with the PCS residual replaced by the per-block hypothesis. -/
theorem callsResolved_mainAsmRaw_of_pcs (pv : PlanView) (m : Model)
    (hacc : pv.hasAccumulator = false)
    (hnumSigs : Midfall.LoweringV3.funSigsOf
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)) = [])
    (hnumCalls : CallsOK (mainSigSet (partialCtxOfVerifier m))
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)))
    (hpcs : ∀ blocks, Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false = .ok blocks → ∀ b ∈ blocks,
        CallsOK (mainSigSet (partialCtxOfVerifier m)) b) :
    Midfall.LoweringV3.callsResolved (mainAsmRaw pv m) = true :=
  callsResolved_mainAsmRaw_of pv m hacc hnumSigs hnumCalls
    (CallsOK_emitPcsFromPlan_of pv hpcs)

/-- `NoWriters` of `mainAsmRaw` with the PCS residual replaced by the per-block hypothesis. -/
theorem noWriters_mainAsmRaw_of_pcs (pv : PlanView) (m : Model)
    (hpcs : ∀ blocks, Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory
      pv.truncatedChallenges false = .ok blocks → ∀ b ∈ blocks, NoWriters b)
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (mainAsmRaw pv m) :=
  noWriters_mainAsmRaw_of pv m (parser_noWriters pv) (NoWriters_emitPcsFromPlan_of pv hpcs) hnum


/-- The PCS call table is a subset of `mainSigSet`: `scalar_inv` is the only
    user call in the whole PCS slice. -/
theorem pcsCalls_subset_mainSigSet (m : Model) :
    ∀ c ∈ pcsCalls, c ∈ mainSigSet (partialCtxOfVerifier m) := by
  intro c hc
  simp only [pcsCalls, List.mem_singleton] at hc
  subst hc
  simp [mainSigSet]

/-- `callsResolved` of `mainAsmRaw` with the PCS residual DISCHARGED. Only the
    numerator's signatures/calls remain as hypotheses. -/
theorem callsResolved_mainAsmRaw_pcs (pv : PlanView) (m : Model)
    (hacc : pv.hasAccumulator = false)
    (hnumSigs : Midfall.LoweringV3.funSigsOf
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m)) = [])
    (hnumCalls : CallsOK (mainSigSet (partialCtxOfVerifier m))
      (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    Midfall.LoweringV3.callsResolved (mainAsmRaw pv m) = true :=
  callsResolved_mainAsmRaw_of_pcs pv m hacc hnumSigs hnumCalls
    (fun blocks hc b hb =>
      CallsOK_mono (computationsAst_calls pv.meta_ pv.dat pv.memory pv.truncatedChallenges
        blocks hc b hb) (pcsCalls_subset_mainSigSet m))

/-- `NoWriters` of `mainAsmRaw` with the PCS residual DISCHARGED. The numerator
    remains the only scan hypothesis. -/
theorem noWriters_mainAsmRaw_pcs (pv : PlanView) (m : Model)
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (mainAsmRaw pv m) :=
  noWriters_mainAsmRaw_of_pcs pv m
    (fun blocks hc b hb =>
      computationsAst_noWriters pv.meta_ pv.dat pv.memory pv.truncatedChallenges
        blocks hc b hb)
    hnum

/-- The guard/wrapper/main block with the PCS slice discharged. -/
theorem noWriters_program_pcs (pv : PlanView) (m : Model)
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m) :=
  noWriters_program_of pv m
    (NoWriters_emitPcsFromPlan_of pv
      (fun blocks hc b hb =>
        computationsAst_noWriters pv.meta_ pv.dat pv.memory pv.truncatedChallenges
          blocks hc b hb))
    hnum

/-- The target's INLINED program with the PCS residual discharged. The remaining
    named side condition is the inliner's `NoWriters` preservation; the numerator
    scan is `hnum`. -/
theorem noWriters_asmOf_pcs (pv : PlanView) (m : Model)
    (hinline : NoWriters (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m) →
      NoWriters (Midfall.Lowering.Inline.inlineContractConstants
        (Midfall.LoweringV2.constTableOf m)
        (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m)))
    (hnum : NoWriters (GenAst.emitQuotientNumerator (partialCtxOfVerifier m))) :
    NoWriters (Midfall.LoweringV2.asmOf pv m 0 0) :=
  hinline (noWriters_program_pcs pv m hnum)

end Midfall.Generator.CertScanPcs
