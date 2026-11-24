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

  STILL OPEN, NAMED: `pcsBlock5Ast` (the nested monadic `foldlM` over `bySet`/commitments and
  `pcsLinExpansion`'s folds — no user call, no writer builtin, but the fold invariant is not
  landed) and the `computationsAst` assembly that turns the emitted `Except` blocks into the
  slice's scans.
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

end Midfall.Generator.CertScanPcs
