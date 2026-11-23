import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Generator.Kzg
import Mathlib.Data.List.Sort

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

/-! ## Generic list helpers -/

theorem findIdx?_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = q a) : l.findIdx? p = l.findIdx? q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.findIdx?_cons, List.findIdx?_cons, h a (by simp)]
      split
      · rfl
      · rw [ih (fun b hb => h b (by simp [hb]))]

theorem listAt_eq_getElem {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    listAt l i = some l[i] := by
  unfold listAt
  rw [List.drop_eq_getElem_cons h]
  rfl

theorem listReplaceAt_eq_take_append_drop {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α), i < l.length →
      listReplaceAt l i v = l.take i ++ [v] ++ l.drop (i + 1) := by
  intro l
  induction l with
  | nil =>
      intro i v h
      simp at h
  | cons a as ih =>
      intro i v h
      cases i with
      | zero => rfl
      | succ i =>
          simp only [listReplaceAt, listReplaceAt.go.eq_3, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append, List.nil_append]
          rw [show listReplaceAt.go as i v = listReplaceAt as i v from rfl,
            ih i v (by simpa using h)]

theorem listSetMut_eq_ok {α : Type} (l : List α) (i : Nat) (v : α) (site : String)
    (h : i < l.length) :
    listSetMut l i v site = .ok (l.take i ++ [v] ++ l.drop (i + 1)) := by
  unfold listSetMut
  rw [if_pos h]

theorem listGetMut_eq_ok {α : Type} (l : List α) (i : Nat) (site : String)
    (h : i < l.length) :
    listGetMut l i site = .ok l[i] := by
  unfold listGetMut
  rw [List.drop_eq_getElem_cons h]
  rfl

/-! ## `natCmp` as an order -/

theorem natCmp_eq_iff (a b : Nat) : natCmp a b = .eq ↔ a = b := by
  unfold natCmp
  split
  · rename_i h; simp [Nat.ne_of_lt h]
  · split
    · rename_i h; simp_all [beq_iff_eq]
    · rename_i h1 h2; simp_all [beq_iff_eq]

theorem natCmp_lt_iff (a b : Nat) : natCmp a b = .lt ↔ a < b := by
  unfold natCmp
  split
  · rename_i h; simp [h]
  · split <;> simp_all [beq_iff_eq]

theorem natCmp_gt_iff (a b : Nat) : natCmp a b = .gt ↔ b < a := by
  unfold natCmp
  split
  · rename_i h; simp [Nat.not_lt.mpr (Nat.le_of_lt h)]
  · split <;> simp_all [beq_iff_eq] <;> omega

/-! ## `natSort` and `btreeSetFromList` -/

theorem natSort_insert_mem (x y : Nat) (ys : List Nat) :
    x ∈ natSort.insert y ys ↔ x = y ∨ x ∈ ys := by
  induction ys with
  | nil => simp [natSort.insert]
  | cons z zs ih =>
      rw [natSort.insert.eq_2]
      split <;> simp_all <;> tauto

theorem natSort_mem (x : Nat) : ∀ l : List Nat, x ∈ natSort l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [natSort]
  | cons y ys ih =>
      rw [natSort.eq_2, natSort_insert_mem, ih]
      simp

theorem natSort_insert_pairwise_lt (x : Nat) :
    ∀ (l : List Nat), l.Pairwise (· < ·) → (∀ y ∈ l, x ≠ y) →
      (natSort.insert x l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _ _; simp [natSort.insert]
  | cons y ys ih =>
      intro hpair hne
      have hy : x ≠ y := hne y (by simp)
      have hpair' : ys.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
      have hyle : ∀ z ∈ ys, y < z := (List.pairwise_cons.mp hpair).1
      rw [natSort.insert.eq_2]
      by_cases hlt : x < y
      · rw [if_pos (Nat.le_of_lt hlt)]
        refine List.Pairwise.cons ?_ hpair
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzys
        · exact hlt
        · exact Nat.lt_trans hlt (hyle z hzys)
      · have hyx : y < x := by omega
        rw [if_neg (by omega : ¬ x ≤ y)]
        refine List.Pairwise.cons ?_ (ih hpair' (fun z hz => hne z (by simp [hz])))
        intro z hz
        rw [natSort_insert_mem] at hz
        rcases hz with rfl | hzys
        · exact hyx
        · exact hyle z hzys

theorem natSort_pairwise_lt_of_nodup : ∀ l : List Nat, l.Nodup →
    (natSort l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => simp [natSort]
  | cons x xs ih =>
      intro hnd
      rw [natSort.eq_2]
      exact natSort_insert_pairwise_lt x (natSort xs) (ih (List.nodup_cons.mp hnd).2)
        (fun y hy => fun h => (List.nodup_cons.mp hnd).1
          (h ▸ (natSort_mem y xs).mp hy))

theorem natSort_insert_nodup (x : Nat) :
    ∀ (l : List Nat), l.Nodup → l.Pairwise (· < ·) → x ∉ l →
      (natSort.insert x l).Nodup := by
  intro l
  induction l with
  | nil => intro _ _ _; simp [natSort.insert]
  | cons y ys ih =>
      intro hnd hpair hx
      have hnd' : ys.Nodup := (List.nodup_cons.mp hnd).2
      have hpair' : ys.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
      have hy : x ≠ y := fun h => hx (by simp [h])
      have hxys : x ∉ ys := fun h => hx (by simp [h])
      have hylt : ∀ z ∈ ys, y < z := (List.pairwise_cons.mp hpair).1
      have hyys : y ∉ ys := (List.nodup_cons.mp hnd).1
      rw [natSort.insert.eq_2]
      by_cases hlt : x < y
      · rw [if_pos (Nat.le_of_lt hlt)]
        refine List.Nodup.cons ?_ (List.Nodup.cons hyys hnd')
        intro hmem
        rcases List.mem_cons.mp hmem with hxy | hxys'
        · exact hy hxy
        · exact hxys hxys'
      · have hyx : y < x := by omega
        rw [if_neg (by omega : ¬ x ≤ y)]
        refine List.Nodup.cons ?_ (ih hnd' hpair' hxys)
        intro hmem
        have hmem' := (natSort_insert_mem y x ys).mp hmem
        rcases hmem' with h | h
        · omega
        · exact hyys h

theorem natSort_nodup_of_nodup : ∀ l : List Nat, l.Nodup → (natSort l).Nodup := by
  intro l
  induction l with
  | nil => simp [natSort]
  | cons x xs ih =>
      intro hnd
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hpair : (natSort xs).Pairwise (· < ·) :=
        natSort_pairwise_lt_of_nodup xs hnd'
      rw [natSort.eq_2]
      exact natSort_insert_nodup x (natSort xs) (ih hnd') hpair
        (fun h => (List.nodup_cons.mp hnd).1 ((natSort_mem x xs).mp h))

theorem btreeSetInsert_mem (x y : Nat) : ∀ ys : List Nat,
    x ∈ btreeSetInsert natCmp y ys ↔ x = y ∨ x ∈ ys := by
  intro ys
  induction ys with
  | nil => simp [btreeSetInsert]
  | cons z zs ih =>
      rw [btreeSetInsert.eq_2]
      cases h : natCmp y z with
      | lt => simp [h]
      | eq =>
          have hyz : y = z := natCmp_eq_iff y z |>.mp h
          simp [h, hyz]
      | gt =>
          dsimp only
          simp only [List.mem_cons]
          rw [ih]
          tauto

theorem btreeSetFromList_mem_aux (x : Nat) :
    ∀ (acc l : List Nat),
      x ∈ l.foldl (fun acc y => btreeSetInsert natCmp y acc) acc ↔ x ∈ acc ∨ x ∈ l := by
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons z zs ih =>
      rw [List.foldl_cons, ih (btreeSetInsert natCmp z acc), btreeSetInsert_mem]
      simp only [List.mem_cons]
      tauto

theorem btreeSetFromList_mem (x : Nat) (l : List Nat) :
    x ∈ btreeSetFromList natCmp l ↔ x ∈ l := by
  unfold btreeSetFromList
  simpa using btreeSetFromList_mem_aux x [] l

theorem btreeSetInsert_nodup (x : Nat) :
    ∀ (l : List Nat), l.Nodup → l.Pairwise (· < ·) →
      (btreeSetInsert natCmp x l).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp [btreeSetInsert]
  | cons y ys ih =>
      intro hnd hpair
      have hnd' : ys.Nodup := (List.nodup_cons.mp hnd).2
      have hpair' : ys.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
      have hyle : ∀ z ∈ ys, y < z := (List.pairwise_cons.mp hpair).1
      have hyys : y ∉ ys := (List.nodup_cons.mp hnd).1
      rw [btreeSetInsert.eq_2]
      cases h : natCmp x y with
      | lt =>
          have hlt : x < y := natCmp_lt_iff x y |>.mp h
          dsimp only
          rw [List.nodup_cons]
          refine ⟨?_, ?_⟩
          · intro hmem
            rcases List.mem_cons.mp hmem with hxy | hxys
            · omega
            · have := hyle x hxys; omega
          · rw [List.nodup_cons]
            exact ⟨hyys, hnd'⟩
      | eq =>
          have hxy : x = y := natCmp_eq_iff x y |>.mp h
          subst hxy
          dsimp only
          exact hnd
      | gt =>
          have hgt : y < x := natCmp_gt_iff x y |>.mp h
          dsimp only
          rw [List.nodup_cons]
          refine ⟨?_, ih hnd' hpair'⟩
          intro hmem
          have hmem' := (btreeSetInsert_mem y x ys).mp hmem
          rcases hmem' with h' | h'
          · omega
          · exact hyys h'

theorem btreeSetInsert_pairwise_lt (x : Nat) :
    ∀ l : List Nat, l.Pairwise (· < ·) → (∀ y ∈ l, x ≠ y) →
      (btreeSetInsert natCmp x l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _ _; simp [btreeSetInsert]
  | cons y ys ih =>
      intro hpair hne
      have hpair' : ys.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
      have hyle : ∀ z ∈ ys, y < z := (List.pairwise_cons.mp hpair).1
      rw [btreeSetInsert.eq_2]
      cases h : natCmp x y with
      | lt =>
          have hlt : x < y := natCmp_lt_iff x y |>.mp h
          dsimp only
          rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hzys
            · exact hlt
            · exact Nat.lt_trans hlt (hyle z hzys)
          · rw [List.pairwise_cons]
            exact ⟨(List.pairwise_cons.mp hpair).1, hpair'⟩
      | eq =>
          have hxy : x = y := natCmp_eq_iff x y |>.mp h
          subst hxy
          dsimp only
          exact hpair
      | gt =>
          have hyx : y < x := natCmp_gt_iff x y |>.mp h
          dsimp only
          rw [List.pairwise_cons]
          refine ⟨?_, ih hpair' (fun z hz => hne z (by simp [hz]))⟩
          intro z hz
          rw [btreeSetInsert_mem] at hz
          rcases hz with rfl | hzys
          · exact hyx
          · exact hyle z hzys

theorem btreeSetFromList_pairwise_lt_aux :
    ∀ (l acc : List Nat), acc.Pairwise (· < ·) → l.Nodup →
      (∀ x ∈ l, ∀ y ∈ acc, x ≠ y) →
      (l.foldl (fun acc x => btreeSetInsert natCmp x acc) acc).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro acc hacc _ _; exact hacc
  | cons x xs ih =>
      intro acc hacc hnd hdisj
      rw [List.foldl_cons]
      have hxacc : ∀ y ∈ acc, x ≠ y := hdisj x (by simp)
      have hacc' : (btreeSetInsert natCmp x acc).Pairwise (· < ·) :=
        btreeSetInsert_pairwise_lt x acc hacc hxacc
      apply ih (btreeSetInsert natCmp x acc) hacc'
        (List.nodup_cons.mp hnd).2
      intro z hz y hy
      rw [btreeSetInsert_mem] at hy
      rcases hy with rfl | hyacc
      · intro hzx
        subst hzx
        exact (List.nodup_cons.mp hnd).1 hz
      · exact hdisj z (by simp [hz]) y hyacc

theorem btreeSetFromList_pairwise_lt_of_nodup (l : List Nat) (hnd : l.Nodup) :
    (btreeSetFromList natCmp l).Pairwise (· < ·) := by
  unfold btreeSetFromList
  exact btreeSetFromList_pairwise_lt_aux l [] (by simp) hnd (by simp)

/-- The exact equality of the two canonical sorted forms on duplicate-free
    index lists. `natSort` is the verifier's insertion sort; the generator's
    `btreeSetFromList` is its BTreeSet insertion fold. -/
theorem natSort_eq_btreeSetFromList_of_nodup (l : List Nat) (hnd : l.Nodup) :
    natSort l = btreeSetFromList natCmp l := by
  have h1 : (natSort l).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (natSort_pairwise_lt_of_nodup l hnd)
  have h2 : (btreeSetFromList natCmp l).SortedLT :=
    List.sortedLT_iff_pairwise.mpr (btreeSetFromList_pairwise_lt_of_nodup l hnd)
  refine h1.eq_of_mem_iff h2 ?_
  intro x
  rw [natSort_mem, btreeSetFromList_mem]


/-! ## The verifier/generator step-1 simulation -/

/-- The `ok`-projection of an `Except` bind. -/
theorem except_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e =>
      change (Except.error e : Except ε β) = .ok b at h
      cases h
  | ok a =>
      refine ⟨a, rfl, ?_⟩
      change f a = .ok b at h
      exact h

theorem contains_eq_false_iff_findIdx?_eq_none {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (a : α) :
    (l.contains a = false) ↔ l.findIdx? (fun x => x == a) = none := by
  rw [List.findIdx?_eq_none_iff]
  constructor
  · intro h x hx
    have : ¬ (x == a) = true := by
      intro hb
      have hmem : a ∈ l := by
        have hxa : x = a := beq_iff_eq.mp hb
        exact hxa ▸ hx
      have hc : l.contains a = true := (List.contains_iff_mem).mpr hmem
      rw [hc] at h
      cases h
    simpa using this
  · intro h
    by_contra hc
    have hmem : a ∈ l := (List.contains_iff_mem).mp (by simpa using hc)
    rcases (List.mem_iff_getElem).mp hmem with ⟨i, hi, hget⟩
    have := h l[i] (List.getElem_mem hi)
    rw [hget] at this
    simp at this

/-- The generator's `step1Pass` as a plain recursive fold. -/
def step1Fold (qs : List Query)
    (st : List (EcPoint × List Nat × List Word) × List Int) :
    Except Fault (List (EcPoint × List Nat × List Word) × List Int) :=
  match qs with
  | [] => .ok st
  | q :: qs => constructIntermediateSetsImpl.step1Pass st q >>= step1Fold qs

theorem foldlM_step1Fold (qs : List Query)
    (st : List (EcPoint × List Nat × List Word) × List Int) :
    qs.foldlM constructIntermediateSetsImpl.step1Pass st = step1Fold qs st := by
  induction qs generalizing st with
  | nil =>
      simp only [step1Fold, List.foldlM_nil]
      rfl
  | cons q qs ih =>
      rw [List.foldlM_cons, step1Fold]
      congr 1
      funext st'
      exact ih st'

def cmsComm {F C K : Type} (ck : CommitmentReference F C → K) (cms : List (CD F C)) : List K :=
  cms.map (fun cd => ck cd.commitment)

def cmsIdx {F C : Type} (cms : List (CD F C)) : List (List Nat) :=
  cms.map (fun cd => cd.pointIndices.toList)

def gsComm {K : Type} (gk : EcPoint → K)
    (gs : List (EcPoint × List Nat × List Word)) : List K :=
  gs.map (fun e => gk e.1)

def gsIdx (gs : List (EcPoint × List Nat × List Word)) : List (List Nat) :=
  gs.map (fun e => e.2.1)


theorem listReplaceAt_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat) (v : α),
      (listReplaceAt xs i v).map f = listReplaceAt (xs.map f) i (f v) := by
  intro xs
  induction xs with
  | nil => intro i v; cases i <;> rfl
  | cons a as ih =>
      intro i v
      cases i with
      | zero => rfl
      | succ i =>
          simp only [listReplaceAt, listReplaceAt.go.eq_3, List.map_cons]
          rw [show listReplaceAt.go as i v = listReplaceAt as i v from rfl, ih]
          rfl

theorem map_take_append_drop {α β : Type} (f : α → β) (xs : List α) (i : Nat) (v : α) :
    (xs.take i ++ [v] ++ xs.drop (i + 1)).map f =
      (xs.map f).take i ++ [f v] ++ (xs.map f).drop (i + 1) := by
  simp [List.map_take, List.map_drop]


theorem span_loop_append {α : Type} (p : α → Bool) :
    ∀ (l : List α) (acc : List α),
      (List.span.loop p l acc).1 ++ (List.span.loop p l acc).2 = acc.reverse ++ l := by
  intro l
  induction l with
  | nil =>
      intro acc
      rw [List.span.loop.eq_1]
  | cons a as ih =>
      intro acc
      rw [List.span.loop.eq_2]
      split
      · rw [ih (a :: acc)]
        simp
      · simp

theorem span_fst_append_snd {α : Type} (p : α → Bool) (l : List α) :
    (List.span p l).1 ++ (List.span p l).2 = l := by
  rw [List.span.eq_1]
  simpa using span_loop_append p l []

theorem btreeMapEntryOrInsert_length_of_not_mem (m : List (List Nat × Nat)) (k : List Nat)
    (h : m.any (fun e => e.1 == k) = false) :
    (btreeMapEntryOrInsert m k).length = m.length + 1 := by
  unfold btreeMapEntryOrInsert
  change (if (m.any (fun e => e.1 == k)) = true then m else
    let entry := (k, m.length)
    let (pre, post) := List.span (fun x => natListCmp x.1 k == .lt) m
    pre ++ entry :: post).length = m.length + 1
  rw [h]
  simp only [Bool.false_eq_true, ite_false]
  rw [List.length_append, List.length_cons]
  have hsplit := span_fst_append_snd (fun x => natListCmp x.1 k == .lt) m
  have hlen : (List.span (fun x => natListCmp x.1 k == .lt) m).1.length +
      (List.span (fun x => natListCmp x.1 k == .lt) m).2.length = m.length := by
    rw [← List.length_append, hsplit]
  omega

theorem btreeMapEntryOrInsert_of_mem (m : List (List Nat × Nat)) (k : List Nat)
    (h : m.any (fun e => e.1 == k) = true) :
    btreeMapEntryOrInsert m k = m := by
  unfold btreeMapEntryOrInsert
  change (if (m.any (fun e => e.1 == k)) = true then m else _) = m
  rw [h]
  simp

theorem btreeMapEntryOrInsert_any_of_not_mem (m : List (List Nat × Nat)) (k : List Nat)
    (h : m.any (fun e => e.1 == k) = false) (p : List Nat × Nat → Bool) :
    (btreeMapEntryOrInsert m k).any p = (m.any p || p (k, m.length)) := by
  unfold btreeMapEntryOrInsert
  change (if (m.any (fun e => e.1 == k)) = true then m else
    let entry := (k, m.length)
    let (pre, post) := List.span (fun x => natListCmp x.1 k == .lt) m
    pre ++ entry :: post).any p = (m.any p || p (k, m.length))
  rw [h]
  simp only [Bool.false_eq_true, ite_false]
  set pre := (List.span (fun x => natListCmp x.1 k == .lt) m).1
  set post := (List.span (fun x => natListCmp x.1 k == .lt) m).2
  have hsplit : pre ++ post = m := by
    subst pre; subst post
    exact span_fst_append_snd (fun x => natListCmp x.1 k == .lt) m
  have hany : (List.any pre p || List.any post p) = List.any m p := by
    have h1 : List.any (pre ++ post) p = (List.any pre p || List.any post p) :=
      List.any_append
    have h2 : List.any (pre ++ post) p = List.any m p := by rw [hsplit]
    exact h1.symm.trans h2
  simp only [List.any_append, List.any_cons, List.any_nil]
  rw [← hany]
  simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

def addKeyFind (acc : List (List Nat × Nat)) (k : List Nat) : List (List Nat × Nat) :=
  match acc.findIdx? (fun e => e.1 == k) with
  | some _ => acc
  | none => acc ++ [(k, acc.length)]

theorem addKeyFind_of_any_true (acc : List (List Nat × Nat)) (k : List Nat)
    (h : acc.any (fun e => e.1 == k) = true) : addKeyFind acc k = acc := by
  unfold addKeyFind
  have hs : (acc.findIdx? (fun e => e.1 == k)).isSome = true := by
    rw [List.findIdx?_isSome]; exact h
  cases hf : acc.findIdx? (fun e => e.1 == k) with
  | none => rw [hf] at hs; cases hs
  | some i => dsimp only

theorem addKeyFind_of_any_false (acc : List (List Nat × Nat)) (k : List Nat)
    (h : acc.any (fun e => e.1 == k) = false) :
    addKeyFind acc k = acc ++ [(k, acc.length)] := by
  unfold addKeyFind
  have hs : (acc.findIdx? (fun e => e.1 == k)).isSome = false := by
    rw [List.findIdx?_isSome]; exact h
  cases hf : acc.findIdx? (fun e => e.1 == k) with
  | some i => rw [hf] at hs; cases hs
  | none => dsimp only

theorem pass2_setsNext_eq (sets : List (List Nat × Nat)) (key : List Nat) :
    (match sets.findIdx? (fun s => s.1 == key) with
      | some _ => sets
      | none => sets ++ [(key, match sets.findIdx? (fun s => s.1 == key) with
          | some i => i
          | none => sets.length)]) = addKeyFind sets key := by
  unfold addKeyFind
  split <;> rfl

theorem pass2_snd_fold {F C : Type} (cms : List (CD F C))
    (sets : List (List Nat × Nat))
    (csm : List (CommitmentReference F C × List Nat)) :
    (constructIntermediateSets.pass2 cms sets csm).2 =
      cms.foldl (fun acc cd => addKeyFind acc (natSort cd.pointIndices.toList)) sets := by
  induction cms generalizing sets csm with
  | nil => rfl
  | cons cd rest ih =>
      rw [constructIntermediateSets.pass2.eq_2, List.foldl_cons]
      cases hf : sets.findIdx? (fun s => s.1 == natSort cd.pointIndices.toList) with
      | some i =>
          dsimp only
          unfold addKeyFind
          rw [hf]
          exact ih sets ((cd.commitment, natSort cd.pointIndices.toList) :: csm)
      | none =>
          dsimp only
          unfold addKeyFind
          rw [hf]
          exact ih _ _

theorem foldl_addKeyFind_length_eq_btreeMap (keys : List (List Nat)) :
    (keys.foldl addKeyFind []).length =
      (keys.foldl btreeMapEntryOrInsert []).length := by
  suffices h : ∀ (keys : List (List Nat))
      (accV accG : List (List Nat × Nat)),
      accV.length = accG.length →
      (∀ k, accV.any (fun e => e.1 == k) = accG.any (fun e => e.1 == k)) →
      (keys.foldl addKeyFind accV).length =
      (keys.foldl btreeMapEntryOrInsert accG).length by
    simpa using h keys [] [] rfl (by simp)
  intro keys
  induction keys with
  | nil => intro accV accG hlen _; exact hlen
  | cons k ks ih =>
      intro accV accG hlen hmem
      have hseen := hmem k
      cases hb : accV.any (fun e => e.1 == k) with
      | false =>
          have hbG : accG.any (fun e => e.1 == k) = false := by
            rw [← hseen, hb]
          rw [List.foldl_cons, List.foldl_cons,
            addKeyFind_of_any_false accV k hb]
          have hlen' : (accV ++ [(k, accV.length)]).length =
              (btreeMapEntryOrInsert accG k).length := by
            rw [btreeMapEntryOrInsert_length_of_not_mem accG k hbG]
            simp [hlen]
          apply ih (accV ++ [(k, accV.length)]) (btreeMapEntryOrInsert accG k) hlen'
          intro k'
          rw [List.any_append, List.any_cons, List.any_nil,
            btreeMapEntryOrInsert_any_of_not_mem accG k hbG]
          rw [hmem k']
          simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
      | true =>
          have hbG : accG.any (fun e => e.1 == k) = true := by
            rw [← hseen, hb]
          rw [List.foldl_cons, List.foldl_cons,
            addKeyFind_of_any_true accV k hb,
            btreeMapEntryOrInsert_of_mem accG k hbG]
          exact ih accV accG hlen hmem

theorem forall_mem_listReplaceAt {α : Type} (P : α → Prop) :
    ∀ (l : List α) (i : Nat) (v : α), (∀ a ∈ l, P a) → P v →
      ∀ a ∈ listReplaceAt l i v, P a := by
  intro l
  induction l with
  | nil =>
      intro i v _ _ a ha
      simp [listReplaceAt, listReplaceAt.go] at ha
  | cons x xs ih =>
      intro i v hl hv a ha
      cases i with
      | zero =>
          simp only [listReplaceAt, listReplaceAt.go.eq_2, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hv
          · exact hl a (by simp [ha])
      | succ i =>
          simp only [listReplaceAt, listReplaceAt.go.eq_3, List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hl a (by simp)
          · exact ih i v (fun b hb => hl b (by simp [hb])) hv a ha

theorem forall_mem_append_singleton {α : Type} (P : α → Prop) (l : List α) (v : α)
    (hl : ∀ a ∈ l, P a) (hv : P v) : ∀ a ∈ l ++ [v], P a := by
  intro a ha
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · exact hl a ha
  · rw [List.mem_singleton] at ha
    subst ha
    exact hv

theorem forall_mem_take_append_drop {α : Type} (P : α → Prop) (l : List α) (i : Nat) (v : α)
    (hl : ∀ a ∈ l, P a) (hv : P v) :
    ∀ a ∈ l.take i ++ [v] ++ l.drop (i + 1), P a := by
  intro a ha
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | rfl) | ha
  · exact hl a (List.mem_of_mem_take ha)
  · exact hv
  · exact hl a (List.mem_of_mem_drop ha)

theorem filterMap_length_of_forall_some {α β : Type} (l : List α) (g : α → Option β)
    (h : ∀ a ∈ l, ∃ b, g a = some b) : (l.filterMap g).length = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      obtain ⟨b, hb⟩ := h a (by simp)
      have has : ∀ x ∈ as, ∃ y, g x = some y := fun x hx => h x (by simp [hx])
      simp [hb, ih has]

theorem pointSets_size {F : Type} (points : List F) (sets : List (List Nat × Nat)) :
    ((sets.map (fun (set, _) =>
      (set.filterMap (fun i => listAt points i)).toArray)).toArray).size = sets.length := by
  rw [List.size_toArray, List.length_map]

theorem pass2_sets_valid {F C : Type} (cms : List (CD F C))
    (initial : List (List Nat × Nat))
    (csm : List (CommitmentReference F C × List Nat)) (n : Nat)
    (hinit : ∀ set ∈ initial.map (·.1), ∀ i ∈ set, i < n)
    (hcm : ∀ cd ∈ cms, ∀ i ∈ cd.pointIndices.toList, i < n) :
    ∀ set ∈ (constructIntermediateSets.pass2 cms initial csm).2.map (·.1),
      ∀ i ∈ set, i < n := by
  induction cms generalizing initial csm with
  | nil =>
      rw [constructIntermediateSets.pass2.eq_1]
      exact hinit
  | cons cd rest ih =>
      rw [constructIntermediateSets.pass2.eq_2]
      cases hf : initial.findIdx? (fun s => s.1 == natSort cd.pointIndices.toList) with
      | some i =>
          dsimp only
          apply ih initial ((cd.commitment, natSort cd.pointIndices.toList) :: csm)
          · exact hinit
          · intro cd' hcd'
            exact hcm cd' (by simp [hcd'])
      | none =>
          dsimp only
          apply ih (initial ++ [(natSort cd.pointIndices.toList, initial.length)])
            ((cd.commitment, natSort cd.pointIndices.toList) :: csm)
          · intro set hset i hi
            rw [List.map_append, List.mem_append] at hset
            rcases hset with hset | hset
            · exact hinit set hset i hi
            · rw [List.map_cons, List.map_nil, List.mem_singleton] at hset
              subst hset
              exact hcm cd (by simp) i ((natSort_mem i _).mp hi)
          · intro cd' hcd'
            exact hcm cd' (by simp [hcd'])

theorem listSetMut_length {α : Type} (xs : List α) (i : Nat) (v : α) (site : String)
    (xs' : List α) (h : listSetMut xs i v site = .ok xs') : xs'.length = xs.length := by
  unfold listSetMut at h
  split at h
  · cases h
    simp only [List.length_append, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]
    omega
  · cases h

theorem foldlM_pointSets_length (pointIndexOf : List Int)
    (l : List (List Nat × Nat)) (init : List (List Int)) (site1 site2 : String) :
    ∀ out, l.foldlM (fun ps (idxSet, setIdx) => do
        let rotations ← idxSet.mapM (fun i => listGetMut pointIndexOf i site1)
        listSetMut ps setIdx rotations site2) init = .ok out →
      out.length = init.length := by
  intro out
  induction l generalizing init with
  | nil =>
      intro h
      simp only [List.foldlM_nil] at h
      cases h
      rfl
  | cons e rest ih =>
      intro h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, hstep, hrest⟩ := except_bind_ok h
      have hlen : st1.length = init.length := by
        obtain ⟨rots, _hmap, hset⟩ := except_bind_ok hstep
        exact listSetMut_length init e.2 rots site2 st1 hset
      exact (ih st1 hrest).trans hlen

theorem constructIntermediateSets_parts {F C : Type} [Field F] [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (queries : Array (VerifierQuery F C))
    (cm : Array (CD F C)) (pointSets : Array (Array F))
    (h : constructIntermediateSets eqC queries = .ok (cm, pointSets)) :
    ∃ (points : List F) (cm0 : List (CD F C)) (sets : List (List Nat × Nat)),
      constructIntermediateSets.pass1 eqC queries.toList [] [] = .ok (points, cm0) ∧
      (constructIntermediateSets.pass2 cm0 [] []).2 = sets ∧
      pointSets.size = sets.length := by
  unfold constructIntermediateSets at h
  obtain ⟨p1, hpass1, hrest⟩ := except_bind_ok h
  obtain ⟨points, cm0⟩ := p1
  dsimp only at hrest
  cases hpass2 : constructIntermediateSets.pass2 cm0 [] [] with
  | mk commitSets sets =>
      rw [hpass2] at hrest
      dsimp only at hrest
      obtain ⟨cmap2, _hpass3, hfinal⟩ := except_bind_ok hrest
      cases hfinal
      have hsets : (constructIntermediateSets.pass2 cm0 [] []).2 = sets := by
        rw [hpass2]
      exact ⟨points, cm0, sets, hpass1, hsets, pointSets_size points sets⟩

theorem constructIntermediateSetsImpl_pointSets_length
    (queries : List Query) (sets : IntermediateSets)
    (step1 : List (EcPoint × List Nat × List Word) × List Int)
    (hstep : queries.foldlM constructIntermediateSetsImpl.step1Pass ([], []) = .ok step1)
    (h : constructIntermediateSetsImpl queries = .ok sets) :
    sets.pointSets.length =
      (step1.1.foldl (fun m (e : EcPoint × List Nat × List Word) =>
        btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) []).length := by
  unfold constructIntermediateSetsImpl at h
  rw [hstep] at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨commitments, _hcomm, hrest⟩ := except_bind_ok h
  obtain ⟨pointSets, hpoint, hfinal⟩ := except_bind_ok hrest
  have hp := foldlM_pointSets_length step1.2
    (step1.1.foldl (fun m (e : EcPoint × List Nat × List Word) =>
      btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) [])
    (List.replicate (step1.1.foldl (fun m (e : EcPoint × List Nat × List Word) =>
      btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) []).length [])
    "proofs/solidity-verifier/src/lowering/kzg/mod.rs:502"
    "proofs/solidity-verifier/src/lowering/kzg/mod.rs:503"
    pointSets hpoint
  cases hfinal
  rw [hp, List.length_replicate]

theorem pass1_indices_lt {F C : Type} [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool) :
    ∀ (qs : List (VerifierQuery F C)) (pts : List F) (cms : List (CD F C))
      (pts' : List F) (cms' : List (CD F C)),
      (∀ cd ∈ cms, ∀ i ∈ cd.pointIndices.toList, i < pts.length) →
      constructIntermediateSets.pass1 eqC qs pts cms = .ok (pts', cms') →
      (∀ cd ∈ cms', ∀ i ∈ cd.pointIndices.toList, i < pts'.length) := by
  intro qs
  induction qs with
  | nil =>
      intro pts cms pts' cms' hinit h
      rw [constructIntermediateSets.pass1.eq_1] at h
      cases h
      exact hinit
  | cons q rest ih =>
      intro pts cms pts' cms' hinit h
      rw [constructIntermediateSets.pass1.eq_2] at h
      cases hpt : pts.findIdx? (fun x => x == q.point) with
      | none =>
          rw [hpt] at h
          dsimp only at h
          have hpidx : pts.length < (pts ++ [q.point]).length := by simp
          cases hcm : cms.findIdx? (fun cd => eqC cd.commitment q.commitment) with
          | none =>
              rw [hcm] at h
              dsimp only at h
              apply ih (pts ++ [q.point]) _ _ _ ?_ h
              intro cd hcd
              rw [List.mem_append] at hcd
              rcases hcd with hcd | hcd
              · intro i hi
                have := hinit cd hcd i hi
                simp; omega
              · rw [List.mem_singleton] at hcd
                subst hcd
                intro i hi
                rw [Array.mem_toList_iff] at hi
                have hiEq : i = pts.length := by
                  simpa [Array.toList_push] using hi
                subst hiEq
                simpa using hpidx
          | some pos =>
              rw [hcm] at h
              dsimp only at h
              have hpos : pos < cms.length :=
                (List.findIdx?_eq_some_iff_getElem.mp hcm).1
              rw [listAt_eq_getElem cms pos hpos] at h
              dsimp only at h
              by_cases hc : (cms[pos]).pointIndices.toList.contains pts.length = true
              · rw [if_pos hc] at h
                cases h
              · rw [if_neg (by simpa using hc)] at h
                apply ih (pts ++ [q.point]) _ _ _ ?_ h
                let cdNew : CD F C :=
                  { cms[pos] with pointIndices := (cms[pos]).pointIndices.push pts.length }
                intro cd hcd
                -- membership in listReplaceAt
                have hcd' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                    ∀ i ∈ cd.pointIndices.toList, i < (pts ++ [q.point]).length := by
                  apply forall_mem_listReplaceAt
                    (fun cd => ∀ i ∈ cd.pointIndices.toList, i < (pts ++ [q.point]).length)
                    cms pos cdNew
                  · intro cd' hcd' i hi
                    have := hinit cd' hcd' i hi
                    simp; omega
                  · intro i hi
                    have hi' : i ∈ (cms[pos]).pointIndices.toList ∨ i = pts.length := by
                      simpa [cdNew, Array.toList_push] using hi
                    rcases hi' with hi' | rfl
                    · have := hinit (cms[pos]) (List.getElem_mem hpos) i hi'
                      simp; omega
                    · simp
                exact hcd' cd hcd
      | some pidx =>
          rw [hpt] at h
          dsimp only at h
          have hpidx : pidx < pts.length :=
            (List.findIdx?_eq_some_iff_getElem.mp hpt).1
          cases hcm : cms.findIdx? (fun cd => eqC cd.commitment q.commitment) with
          | none =>
              rw [hcm] at h
              dsimp only at h
              apply ih pts _ _ _ ?_ h
              intro cd hcd
              rw [List.mem_append] at hcd
              rcases hcd with hcd | hcd
              · exact hinit cd hcd
              · rw [List.mem_singleton] at hcd
                subst hcd
                intro i hi
                have hiEq : i = pidx := by
                  simpa [Array.toList_push] using hi
                subst hiEq
                exact hpidx
          | some pos =>
              rw [hcm] at h
              dsimp only at h
              have hpos : pos < cms.length :=
                (List.findIdx?_eq_some_iff_getElem.mp hcm).1
              rw [listAt_eq_getElem cms pos hpos] at h
              dsimp only at h
              by_cases hc : (cms[pos]).pointIndices.toList.contains pidx = true
              · rw [if_pos hc] at h
                cases h
              · rw [if_neg (by simpa using hc)] at h
                apply ih pts _ _ _ ?_ h
                let cdNew : CD F C :=
                  { cms[pos] with pointIndices := (cms[pos]).pointIndices.push pidx }
                intro cd hcd
                have hcd' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                    ∀ i ∈ cd.pointIndices.toList, i < pts.length := by
                  apply forall_mem_listReplaceAt
                    (fun cd => ∀ i ∈ cd.pointIndices.toList, i < pts.length)
                    cms pos cdNew
                  · exact hinit
                  · intro i hi
                    have hi' : i ∈ (cms[pos]).pointIndices.toList ∨ i = pidx := by
                      simpa [cdNew, Array.toList_push] using hi
                    rcases hi' with hi' | rfl
                    · exact hinit (cms[pos]) (List.getElem_mem hpos) i hi'
                    · exact hpidx
                exact hcd' cd hcd

theorem pass1_step1_sim
    {F C K : Type} [BEq F] [BEq K]
    [LawfulBEq F] [LawfulBEq K]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (fk : F → Int) (ck : CommitmentReference F C → K) (gk : EcPoint → K)
    (L : List (VerifierQuery F C × Query))
    (hCommEq : ∀ p ∈ L, ∀ p' ∈ L,
      eqC p.1.commitment p'.1.commitment = (ck p.1.commitment == ck p'.1.commitment))
    (hGCommEq : ∀ p ∈ L, ∀ p' ∈ L,
      ecPointBeq p.2.comm p'.2.comm = (gk p.2.comm == gk p'.2.comm))
    (hPointEq : ∀ p ∈ L, ∀ p' ∈ L,
      (p.1.point == p'.1.point) = (fk p.1.point == fk p'.1.point))
    (pre suffix : List (VerifierQuery F C × Query))
    (hL : L = pre ++ suffix)
    (pts : List F) (rots : List Int) (cms : List (CD F C))
    (gs : List (EcPoint × List Nat × List Word))
    (pts' : List F) (rots' : List Int) (cms' : List (CD F C))
    (gs' : List (EcPoint × List Nat × List Word))
    (hrots : rots = pts.map fk)
    (hcomm : cmsComm ck cms = gsComm gk gs)
    (hidx : cmsIdx cms = gsIdx gs)
    (hndC : ∀ cd ∈ cms, cd.pointIndices.toList.Nodup)
    (hndG : ∀ e ∈ gs, e.2.1.Nodup)
    (hcmMem : ∀ cd ∈ cms, ∃ p ∈ L, cd.commitment = p.1.commitment)
    (hgsMem : ∀ e ∈ gs, ∃ p ∈ L, e.1 = p.2.comm)
    (hptMem : ∀ x ∈ pts, ∃ p ∈ L, x = p.1.point)
    (hpairP : ∀ p ∈ L, fk p.1.point = p.2.rotation)
    (hpairC : ∀ p ∈ L, ck p.1.commitment = gk p.2.comm)
    (hV : constructIntermediateSets.pass1 eqC (suffix.map Prod.fst) pts cms = .ok (pts', cms'))
    (hG : step1Fold (suffix.map Prod.snd) (gs, rots) = .ok (gs', rots')) :
    rots' = pts'.map fk ∧ cmsComm ck cms' = gsComm gk gs' ∧
      cmsIdx cms' = gsIdx gs' ∧
      (∀ cd ∈ cms', cd.pointIndices.toList.Nodup) ∧
      (∀ e ∈ gs', e.2.1.Nodup) := by
  induction suffix generalizing pre pts rots cms gs with
  | nil =>
      simp only [List.map_nil, constructIntermediateSets.pass1.eq_1,
        step1Fold] at hV hG
      cases hV
      cases hG
      exact ⟨hrots, hcomm, hidx, hndC, hndG⟩
  | cons q rest ih =>
      obtain ⟨qV, qG⟩ := q
      have hqL : (qV, qG) ∈ L := by
        rw [hL]
        simp
      have hL' : L = (pre ++ [(qV, qG)]) ++ rest := by
        rw [hL]
        simp [List.append_assoc]
      have hpq : fk qV.point = qG.rotation := hpairP (qV, qG) hqL
      have hcq : ck qV.commitment = gk qG.comm := hpairC (qV, qG) hqL
      have hfindPts : rots.findIdx? (fun r => r == qG.rotation)
          = pts.findIdx? (fun x => x == qV.point) := by
        have h1 : rots.findIdx? (fun r => r == qG.rotation)
            = (pts.map fk).findIdx? (fun r => r == qG.rotation) := by rw [hrots]
        have h2 : (pts.map fk).findIdx? (fun r => r == qG.rotation)
            = pts.findIdx? (fun x => fk x == qG.rotation) :=
          List.findIdx?_map (f := fk) (l := pts) (p := fun r => r == qG.rotation)
        have h3 : pts.findIdx? (fun x => fk x == qG.rotation)
            = pts.findIdx? (fun x => x == qV.point) := by
          rw [← hpq]
          exact findIdx?_congr pts _ _ (fun x hx => by
            obtain ⟨p, hpL, rfl⟩ := hptMem x hx
            exact (hPointEq p hpL (qV, qG) hqL).symm)
        exact (h1.trans h2).trans h3
      have hfindCms : gs.findIdx? (fun e => ecPointBeq e.1 qG.comm)
          = cms.findIdx? (fun cd => eqC cd.commitment qV.commitment) := by
        have h2 : gs.findIdx? (fun e => ecPointBeq e.1 qG.comm)
            = gs.findIdx? (fun e => gk e.1 == gk qG.comm) :=
          findIdx?_congr gs _ _ (fun e he => by
            obtain ⟨p, hpL, heq⟩ := hgsMem e he
            rw [heq]
            exact hGCommEq p hpL (qV, qG) hqL)
        have h3 : gs.findIdx? (fun e => gk e.1 == gk qG.comm)
            = (gs.map (fun e => gk e.1)).findIdx? (fun k => k == gk qG.comm) := by
          change List.findIdx? (fun e => gk e.1 == gk qG.comm) gs =
            List.findIdx? (fun k => k == gk qG.comm) (gs.map (fun e => gk e.1))
          exact (List.findIdx?_map (f := fun e => gk e.1) (l := gs)
            (p := fun k => k == gk qG.comm)).symm
        have hcomm' : cms.map (fun cd => ck cd.commitment) = gs.map (fun e => gk e.1) := by
          simpa only [cmsComm, gsComm] using hcomm
        have h4 : (gs.map (fun e => gk e.1)).findIdx? (fun k => k == gk qG.comm)
            = (cms.map (fun cd => ck cd.commitment)).findIdx? (fun k => k == gk qG.comm) := by
          rw [hcomm']
        have h5 : (cms.map (fun cd => ck cd.commitment)).findIdx? (fun k => k == gk qG.comm)
            = cms.findIdx? (fun cd => ck cd.commitment == gk qG.comm) :=
          List.findIdx?_map (f := fun cd => ck cd.commitment) (l := cms)
            (p := fun k => k == gk qG.comm)
        have h1 : cms.findIdx? (fun cd => eqC cd.commitment qV.commitment)
            = cms.findIdx? (fun cd => ck cd.commitment == ck qV.commitment) :=
          findIdx?_congr cms _ _ (fun cd hcd => by
            obtain ⟨p, hpL, heq⟩ := hcmMem cd hcd
            rw [heq]
            exact hCommEq p hpL (qV, qG) hqL)
        have h1b : cms.findIdx? (fun cd => ck cd.commitment == ck qV.commitment)
            = cms.findIdx? (fun cd => ck cd.commitment == gk qG.comm) := by
          rw [hcq]
        exact ((h2.trans h3).trans (h4.trans h5)).trans (h1.trans h1b).symm
      simp only [List.map_cons, Prod.snd] at hG
      rw [step1Fold.eq_def] at hG
      obtain ⟨st1, hstep, hrest⟩ := except_bind_ok hG
      obtain ⟨gs1, rots1⟩ := st1
      rw [constructIntermediateSetsImpl.step1Pass.eq_1] at hstep
      rw [hfindPts, hfindCms] at hstep
      simp only [List.map_cons, Prod.fst] at hV
      rw [constructIntermediateSets.pass1.eq_2] at hV
      cases hpt : pts.findIdx? (fun x => x == qV.point) with
      | none =>
          rw [hpt] at hstep hV
          dsimp only at hstep hV
          cases hcm : cms.findIdx? (fun cd => eqC cd.commitment qV.commitment) with
          | none =>
              rw [hcm] at hstep hV
              dsimp only at hstep hV
              cases hstep
              let cdNew : CD F C :=
                { CommitmentData.new qV.commitment qV.commitmentLabel with
                  pointIndices := #[pts.length] }
              have hlen : rots.length = pts.length := by
                rw [hrots, List.length_map]
              have hrots' : rots ++ [qG.rotation] = (pts ++ [qV.point]).map fk := by
                rw [hrots, List.map_append]
                simp [hpq]
              have hcomm' : cmsComm ck (cms ++ [cdNew])
                  = gsComm gk (gs ++ [(qG.comm, [rots.length], [qG.eval])]) := by
                have h0 : List.map (fun cd => ck cd.commitment) cms
                    = List.map (fun e => gk e.1) gs := by
                  simpa only [cmsComm, gsComm] using hcomm
                simp only [cmsComm, gsComm, List.map_append, List.map_cons, List.map_nil]
                rw [h0]
                simp [cdNew, CommitmentData.new, hcq]
              have hidx' : cmsIdx (cms ++ [cdNew])
                  = gsIdx (gs ++ [(qG.comm, [rots.length], [qG.eval])]) := by
                have h0 : List.map (fun cd => cd.pointIndices.toList) cms
                    = List.map (fun e => e.2.1) gs := by
                  simpa only [cmsIdx, gsIdx] using hidx
                simp only [cmsIdx, gsIdx, List.map_append, List.map_cons, List.map_nil]
                rw [h0]
                simp [cdNew, CommitmentData.new, hlen]
              have hndC' : ∀ cd ∈ cms ++ [cdNew], cd.pointIndices.toList.Nodup := by
                intro cd hcd
                rw [List.mem_append] at hcd
                rcases hcd with hcd | hcd
                · exact hndC cd hcd
                · rw [List.mem_singleton] at hcd
                  subst hcd
                  simp [cdNew, CommitmentData.new]
              have hndG' : ∀ e ∈ gs ++ [(qG.comm, [rots.length], [qG.eval])],
                  e.2.1.Nodup := by
                intro e he
                rw [List.mem_append] at he
                rcases he with he | he
                · exact hndG e he
                · rw [List.mem_singleton] at he
                  subst he
                  simp
              have hptMem' : ∀ x ∈ pts ++ [qV.point], ∃ p ∈ L, x = p.1.point :=
                forall_mem_append_singleton _ pts qV.point hptMem
                  ⟨(qV, qG), hqL, rfl⟩
              have hcmMem' : ∀ cd ∈ cms ++ [cdNew],
                  ∃ p ∈ L, cd.commitment = p.1.commitment :=
                forall_mem_append_singleton _ cms cdNew hcmMem
                  ⟨(qV, qG), hqL, by simp [cdNew, CommitmentData.new]⟩
              have hgsMem' : ∀ e ∈ gs ++ [(qG.comm, [rots.length], [qG.eval])],
                  ∃ p ∈ L, e.1 = p.2.comm :=
                forall_mem_append_singleton _ gs _ hgsMem
                  ⟨(qV, qG), hqL, rfl⟩
              exact ih (pre ++ [(qV, qG)]) hL' (pts ++ [qV.point]) (rots ++ [qG.rotation])
                (cms ++ [cdNew])
                (gs ++ [(qG.comm, [rots.length], [qG.eval])])
                hrots' hcomm' hidx' hndC' hndG'
                hcmMem' hgsMem' hptMem'
                hV hrest
          | some pos =>
              rw [hcm] at hstep hV
              dsimp only at hstep hV
              have hpos : pos < cms.length :=
                (List.findIdx?_eq_some_iff_getElem.mp hcm).1
              have hlenCG : cms.length = gs.length := by
                have h := congrArg List.length hcomm
                simpa only [cmsComm, gsComm, List.length_map] using h
              have hposG : pos < gs.length := by omega
              rw [listAt_eq_getElem cms pos hpos] at hV
              dsimp only at hV
              rw [listGetMut_eq_ok gs pos _ hposG] at hstep
              simp only [Bind.bind, Except.bind] at hstep
              cases hgse : gs[pos] with
              | mk comm restPair =>
                obtain ⟨pis, evals⟩ := restPair
                rw [hgse] at hstep
                have hcommpos : ck (cms[pos]).commitment = gk comm := by
                  have h := congrArg (fun l => l[pos]?) hcomm
                  simp only [cmsComm, gsComm, List.getElem?_map,
                    List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hposG,
                    hgse, Option.map_some] at h
                  exact Option.some.inj h
                have hidxpos : (cms[pos]).pointIndices.toList = pis := by
                  have h := congrArg (fun l => l[pos]?) hidx
                  simp only [cmsIdx, gsIdx, List.getElem?_map,
                    List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hposG,
                    hgse, Option.map_some] at h
                  exact Option.some.inj h
                by_cases hc : (cms[pos]).pointIndices.toList.contains pts.length = true
                · rw [if_pos hc] at hV
                  cases hV
                · have hcFalse : (cms[pos]).pointIndices.toList.contains pts.length = false := by
                    simpa using hc
                  have hfindNone : (cms[pos]).pointIndices.toList.findIdx?
                      (fun x => x == pts.length) = none :=
                    (contains_eq_false_iff_findIdx?_eq_none _ _).mp hcFalse
                  have hlen : rots.length = pts.length := by
                    rw [hrots, List.length_map]
                  have hfindPis : pis.findIdx? (fun x => x == rots.length) = none := by
                    rw [hlen]
                    rw [← hidxpos]
                    exact hfindNone
                  rw [if_neg (by simpa using hc)] at hV
                  rw [hfindPis] at hstep
                  rw [listSetMut_eq_ok gs pos _ _ hposG] at hstep
                  simp only [Bind.bind, Except.bind] at hstep
                  cases hstep
                  let cdNew : CD F C :=
                    { cms[pos] with pointIndices := (cms[pos]).pointIndices.push pts.length }
                  have hrots' : rots ++ [qG.rotation] = (pts ++ [qV.point]).map fk := by
                    rw [hrots, List.map_append]
                    simp [hpq]
                  have hcomm' : cmsComm ck (listReplaceAt cms pos cdNew)
                      = gsComm gk (gs.take pos ++
                          [(comm, pis ++ [rots.length], evals ++ [qG.eval])] ++ gs.drop (pos + 1)) := by
                    have h0 : List.map (fun cd => ck cd.commitment) cms
                        = List.map (fun e => gk e.1) gs := by
                      simpa only [cmsComm, gsComm] using hcomm
                    simp only [cmsComm, gsComm]
                    rw [listReplaceAt_map, map_take_append_drop, h0]
                    rw [listReplaceAt_eq_take_append_drop (List.map (fun e => gk e.1) gs)
                      pos (ck cdNew.commitment) (by simpa using hposG)]
                    simp [cdNew, hcommpos]
                  have hidx' : cmsIdx (listReplaceAt cms pos cdNew)
                      = gsIdx (gs.take pos ++
                          [(comm, pis ++ [rots.length], evals ++ [qG.eval])] ++ gs.drop (pos + 1)) := by
                    have h0 : List.map (fun cd => cd.pointIndices.toList) cms
                        = List.map (fun e => e.2.1) gs := by
                      simpa only [cmsIdx, gsIdx] using hidx
                    simp only [cmsIdx, gsIdx]
                    rw [listReplaceAt_map, map_take_append_drop, h0]
                    rw [listReplaceAt_eq_take_append_drop (List.map (fun e => e.2.1) gs)
                      pos cdNew.pointIndices.toList (by simpa using hposG)]
                    simp [cdNew, Array.toList_push, hidxpos, hlen]
                  have hndC' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                      cd.pointIndices.toList.Nodup := by
                    have hcdNew : cdNew.pointIndices.toList.Nodup := by
                      have hold : (cms[pos]).pointIndices.toList.Nodup :=
                        hndC _ (List.getElem_mem hpos)
                      have hnot : pts.length ∉ (cms[pos]).pointIndices.toList := by
                        intro hmem
                        have hcont : (cms[pos]).pointIndices.toList.contains pts.length = true :=
                          (List.contains_iff_mem).mpr hmem
                        rw [hcFalse] at hcont
                        cases hcont
                      show ((cms[pos]).pointIndices.push pts.length).toList.Nodup
                      rw [Array.toList_push, List.nodup_append]
                      refine ⟨hold, by simp, ?_⟩
                      intro a ha b hb
                      rw [List.mem_singleton] at hb
                      subst hb
                      exact fun h => hnot (h ▸ ha)
                    exact forall_mem_listReplaceAt (fun cd => cd.pointIndices.toList.Nodup)
                      cms pos cdNew (fun b hb => hndC b hb) hcdNew
                  have hndG' : ∀ e ∈ gs.take pos ++
                      [(comm, pis ++ [rots.length], evals ++ [qG.eval])] ++ gs.drop (pos + 1),
                      e.2.1.Nodup := by
                    have hnew : (pis ++ [rots.length]).Nodup := by
                      have hold : pis.Nodup := by
                        simpa [hgse] using hndG (gs[pos]) (List.getElem_mem hposG)
                      have hnot : rots.length ∉ pis := by
                        intro hmem
                        have h := (List.findIdx?_eq_none_iff.mp hfindPis) rots.length hmem
                        simp at h
                      rw [List.nodup_append]
                      refine ⟨hold, by simp, ?_⟩
                      intro a ha b hb
                      rw [List.mem_singleton] at hb
                      subst hb
                      exact fun h => hnot (h ▸ ha)
                    exact forall_mem_take_append_drop (fun e => e.2.1.Nodup) gs pos
                      (comm, pis ++ [rots.length], evals ++ [qG.eval])
                      (fun b hb => hndG b hb) hnew
                  have hptMem' : ∀ x ∈ pts ++ [qV.point], ∃ p ∈ L, x = p.1.point :=
                    forall_mem_append_singleton _ pts qV.point hptMem
                      ⟨(qV, qG), hqL, rfl⟩
                  have hcmMem' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                      ∃ p ∈ L, cd.commitment = p.1.commitment :=
                    forall_mem_listReplaceAt _ cms pos cdNew hcmMem
                      (by simpa [cdNew] using hcmMem (cms[pos]) (List.getElem_mem hpos))
                  have hcommMem : ∃ p ∈ L, comm = p.2.comm := by
                    obtain ⟨p, hpL, heq⟩ := hgsMem (gs[pos]) (List.getElem_mem hposG)
                    rw [hgse] at heq
                    exact ⟨p, hpL, heq⟩
                  have hgsMem' : ∀ e ∈ gs.take pos ++
                      [(comm, pis ++ [rots.length], evals ++ [qG.eval])] ++ gs.drop (pos + 1),
                      ∃ p ∈ L, e.1 = p.2.comm :=
                    forall_mem_take_append_drop _ gs pos _
                      hgsMem hcommMem
                  exact ih (pre ++ [(qV, qG)]) hL' (pts ++ [qV.point]) (rots ++ [qG.rotation])
                    (listReplaceAt cms pos cdNew)
                    (gs.take pos ++ [(comm, pis ++ [rots.length], evals ++ [qG.eval])] ++ gs.drop (pos + 1))
                    hrots' hcomm' hidx' hndC' hndG'
                    hcmMem' hgsMem' hptMem'
                    hV hrest
      | some pidx =>
          rw [hpt] at hstep hV
          dsimp only at hstep hV
          cases hcm : cms.findIdx? (fun cd => eqC cd.commitment qV.commitment) with
          | none =>
              rw [hcm] at hstep hV
              dsimp only at hstep hV
              cases hstep
              let cdNew : CD F C :=
                { CommitmentData.new qV.commitment qV.commitmentLabel with
                  pointIndices := #[pidx] }
              have hcomm' : cmsComm ck (cms ++ [cdNew])
                  = gsComm gk (gs ++ [(qG.comm, [pidx], [qG.eval])]) := by
                have h0 : List.map (fun cd => ck cd.commitment) cms
                    = List.map (fun e => gk e.1) gs := by
                  simpa only [cmsComm, gsComm] using hcomm
                simp only [cmsComm, gsComm, List.map_append, List.map_cons, List.map_nil]
                rw [h0]
                simp [cdNew, CommitmentData.new, hcq]
              have hidx' : cmsIdx (cms ++ [cdNew])
                  = gsIdx (gs ++ [(qG.comm, [pidx], [qG.eval])]) := by
                have h0 : List.map (fun cd => cd.pointIndices.toList) cms
                    = List.map (fun e => e.2.1) gs := by
                  simpa only [cmsIdx, gsIdx] using hidx
                simp only [cmsIdx, gsIdx, List.map_append, List.map_cons, List.map_nil]
                rw [h0]
              have hndC' : ∀ cd ∈ cms ++ [cdNew], cd.pointIndices.toList.Nodup := by
                intro cd hcd
                rw [List.mem_append] at hcd
                rcases hcd with hcd | hcd
                · exact hndC cd hcd
                · rw [List.mem_singleton] at hcd
                  subst hcd
                  simp [cdNew, CommitmentData.new]
              have hndG' : ∀ e ∈ gs ++ [(qG.comm, [pidx], [qG.eval])], e.2.1.Nodup := by
                intro e he
                rw [List.mem_append] at he
                rcases he with he | he
                · exact hndG e he
                · rw [List.mem_singleton] at he
                  subst he
                  simp
              have hcmMem' : ∀ cd ∈ cms ++ [cdNew],
                  ∃ p ∈ L, cd.commitment = p.1.commitment :=
                forall_mem_append_singleton _ cms cdNew hcmMem
                  ⟨(qV, qG), hqL, by simp [cdNew, CommitmentData.new]⟩
              have hgsMem' : ∀ e ∈ gs ++ [(qG.comm, [pidx], [qG.eval])],
                  ∃ p ∈ L, e.1 = p.2.comm :=
                forall_mem_append_singleton _ gs _ hgsMem
                  ⟨(qV, qG), hqL, rfl⟩
              exact ih (pre ++ [(qV, qG)]) hL' pts rots (cms ++ [cdNew])
                (gs ++ [(qG.comm, [pidx], [qG.eval])])
                hrots hcomm' hidx' hndC' hndG'
                hcmMem' hgsMem' hptMem
                hV hrest
          | some pos =>
              rw [hcm] at hstep hV
              dsimp only at hstep hV
              have hpos : pos < cms.length :=
                (List.findIdx?_eq_some_iff_getElem.mp hcm).1
              have hlenCG : cms.length = gs.length := by
                have h := congrArg List.length hcomm
                simpa only [cmsComm, gsComm, List.length_map] using h
              have hposG : pos < gs.length := by omega
              rw [listAt_eq_getElem cms pos hpos] at hV
              dsimp only at hV
              rw [listGetMut_eq_ok gs pos _ hposG] at hstep
              simp only [Bind.bind, Except.bind] at hstep
              cases hgse : gs[pos] with
              | mk comm restPair =>
                obtain ⟨pis, evals⟩ := restPair
                rw [hgse] at hstep
                have hcommpos : ck (cms[pos]).commitment = gk comm := by
                  have h := congrArg (fun l => l[pos]?) hcomm
                  simp only [cmsComm, gsComm, List.getElem?_map,
                    List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hposG,
                    hgse, Option.map_some] at h
                  exact Option.some.inj h
                have hidxpos : (cms[pos]).pointIndices.toList = pis := by
                  have h := congrArg (fun l => l[pos]?) hidx
                  simp only [cmsIdx, gsIdx, List.getElem?_map,
                    List.getElem?_eq_getElem hpos, List.getElem?_eq_getElem hposG,
                    hgse, Option.map_some] at h
                  exact Option.some.inj h
                by_cases hc : (cms[pos]).pointIndices.toList.contains pidx = true
                · rw [if_pos hc] at hV
                  cases hV
                · have hcFalse : (cms[pos]).pointIndices.toList.contains pidx = false := by
                    simpa using hc
                  have hfindNone : (cms[pos]).pointIndices.toList.findIdx?
                      (fun x => x == pidx) = none :=
                    (contains_eq_false_iff_findIdx?_eq_none _ _).mp hcFalse
                  have hfindPis : pis.findIdx? (fun x => x == pidx) = none := by
                    rw [← hidxpos]
                    exact hfindNone
                  rw [if_neg (by simpa using hc)] at hV
                  rw [hfindPis] at hstep
                  rw [listSetMut_eq_ok gs pos _ _ hposG] at hstep
                  simp only [Bind.bind, Except.bind] at hstep
                  cases hstep
                  let cdNew : CD F C :=
                    { cms[pos] with pointIndices := (cms[pos]).pointIndices.push pidx }
                  have hcomm' : cmsComm ck (listReplaceAt cms pos cdNew)
                      = gsComm gk (gs.take pos ++
                          [(comm, pis ++ [pidx], evals ++ [qG.eval])] ++ gs.drop (pos + 1)) := by
                    have h0 : List.map (fun cd => ck cd.commitment) cms
                        = List.map (fun e => gk e.1) gs := by
                      simpa only [cmsComm, gsComm] using hcomm
                    simp only [cmsComm, gsComm]
                    rw [listReplaceAt_map, map_take_append_drop, h0]
                    rw [listReplaceAt_eq_take_append_drop (List.map (fun e => gk e.1) gs)
                      pos (ck cdNew.commitment) (by simpa using hposG)]
                    simp [cdNew, hcommpos]
                  have hidx' : cmsIdx (listReplaceAt cms pos cdNew)
                      = gsIdx (gs.take pos ++
                          [(comm, pis ++ [pidx], evals ++ [qG.eval])] ++ gs.drop (pos + 1)) := by
                    have h0 : List.map (fun cd => cd.pointIndices.toList) cms
                        = List.map (fun e => e.2.1) gs := by
                      simpa only [cmsIdx, gsIdx] using hidx
                    simp only [cmsIdx, gsIdx]
                    rw [listReplaceAt_map, map_take_append_drop, h0]
                    rw [listReplaceAt_eq_take_append_drop (List.map (fun e => e.2.1) gs)
                      pos cdNew.pointIndices.toList (by simpa using hposG)]
                    simp [cdNew, Array.toList_push, hidxpos]
                  have hndC' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                      cd.pointIndices.toList.Nodup := by
                    have hcdNew : cdNew.pointIndices.toList.Nodup := by
                      have hold : (cms[pos]).pointIndices.toList.Nodup :=
                        hndC _ (List.getElem_mem hpos)
                      have hnot : pidx ∉ (cms[pos]).pointIndices.toList := by
                        intro hmem
                        have hcont : (cms[pos]).pointIndices.toList.contains pidx = true :=
                          (List.contains_iff_mem).mpr hmem
                        rw [hcFalse] at hcont
                        cases hcont
                      show ((cms[pos]).pointIndices.push pidx).toList.Nodup
                      rw [Array.toList_push, List.nodup_append]
                      refine ⟨hold, by simp, ?_⟩
                      intro a ha b hb
                      rw [List.mem_singleton] at hb
                      subst hb
                      exact fun h => hnot (h ▸ ha)
                    exact forall_mem_listReplaceAt (fun cd => cd.pointIndices.toList.Nodup)
                      cms pos cdNew (fun b hb => hndC b hb) hcdNew
                  have hndG' : ∀ e ∈ gs.take pos ++
                      [(comm, pis ++ [pidx], evals ++ [qG.eval])] ++ gs.drop (pos + 1),
                      e.2.1.Nodup := by
                    have hnew : (pis ++ [pidx]).Nodup := by
                      have hold : pis.Nodup := by
                        simpa [hgse] using hndG (gs[pos]) (List.getElem_mem hposG)
                      have hnot : pidx ∉ pis := by
                        intro hmem
                        have h := (List.findIdx?_eq_none_iff.mp hfindPis) pidx hmem
                        simp at h
                      rw [List.nodup_append]
                      refine ⟨hold, by simp, ?_⟩
                      intro a ha b hb
                      rw [List.mem_singleton] at hb
                      subst hb
                      exact fun h => hnot (h ▸ ha)
                    exact forall_mem_take_append_drop (fun e => e.2.1.Nodup) gs pos
                      (comm, pis ++ [pidx], evals ++ [qG.eval])
                      (fun b hb => hndG b hb) hnew
                  have hcmMem' : ∀ cd ∈ listReplaceAt cms pos cdNew,
                      ∃ p ∈ L, cd.commitment = p.1.commitment :=
                    forall_mem_listReplaceAt _ cms pos cdNew hcmMem
                      (by simpa [cdNew] using hcmMem (cms[pos]) (List.getElem_mem hpos))
                  have hcommMem : ∃ p ∈ L, comm = p.2.comm := by
                    obtain ⟨p, hpL, heq⟩ := hgsMem (gs[pos]) (List.getElem_mem hposG)
                    rw [hgse] at heq
                    exact ⟨p, hpL, heq⟩
                  have hgsMem' : ∀ e ∈ gs.take pos ++
                      [(comm, pis ++ [pidx], evals ++ [qG.eval])] ++ gs.drop (pos + 1),
                      ∃ p ∈ L, e.1 = p.2.comm :=
                    forall_mem_take_append_drop _ gs pos _
                      hgsMem hcommMem
                  exact ih (pre ++ [(qV, qG)]) hL' pts rots (listReplaceAt cms pos cdNew)
                    (gs.take pos ++ [(comm, pis ++ [pidx], evals ++ [qG.eval])] ++ gs.drop (pos + 1))
                    hrots hcomm' hidx' hndC' hndG'
                    hcmMem' hgsMem' hptMem
                    hV hrest




theorem list_mapM_length {α β ε : Type} {f : α → Except ε β} :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' → l'.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases h
      rfl
  | cons a as ih =>
      intro l' h
      rw [List.mapM_cons] at h
      obtain ⟨b, hb, h1⟩ := except_bind_ok h
      obtain ⟨bs, hbs, h2⟩ := except_bind_ok h1
      cases h2
      simp only [List.length_cons]
      rw [ih bs hbs]

theorem insertionSortBy_length {α : Type} (lt : α → α → Bool) :
    ∀ l : List α, (insertionSortBy lt l).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [insertionSortBy, List.length_cons]
      -- insert preserves length
      have hins : ∀ (x : α) (l : List α), (insertionSortBy.insert lt x l).length = l.length + 1 := by
        intro x l
        induction l with
        | nil => simp [insertionSortBy.insert]
        | cons y ys ihins =>
            rw [insertionSortBy.insert]
            split
            · simp only [List.length_cons, ihins]
            · simp only [List.length_cons]
      rw [hins, ih]

theorem sortSets_pointSets_length (input : IntermediateSets) (out : IntermediateSets)
    (h : sortSets input = .ok out) : out.pointSets.length = input.pointSets.length := by
  unfold sortSets at h
  obtain ⟨remap, _hremap, h1⟩ := except_bind_ok h
  obtain ⟨pointSets, hps, h2⟩ := except_bind_ok h1
  obtain ⟨commitments, _hcomm, h3⟩ := except_bind_ok h2
  cases h3
  have hlen : pointSets.length = input.pointSets.length := by
    -- the mapM is over `order`, a permutation of range n
    have hmap := list_mapM_length
      (l := insertionSortBy (lenIndexLt (input.pointSets.map List.length)) (List.range input.pointSets.length))
      (f := fun i => listGetMut input.pointSets i "proofs/solidity-verifier/src/lowering/kzg/mod.rs:528")
      (l' := pointSets) hps
    rw [hmap, insertionSortBy_length, List.length_range]
  exact hlen

theorem numPointSets_setNumPointSets (m : ConstraintSystemMeta) (data : Data) (n : Nat) :
    numPointSets (m.setNumPointSets n) data = numPointSets m data := by
  cases m
  rfl

theorem queries_setNumPointSets (m : ConstraintSystemMeta) (data : Data) (n : Nat) :
    queries (m.setNumPointSets n) data = queries m data := by
  cases m
  rfl

theorem numPointSets_parts (meta_ : ConstraintSystemMeta) (data : Data) (n : Nat)
    (h : numPointSets meta_ data = .ok n) :
    ∃ out : IntermediateSets,
      intermediateSets meta_ data = .ok out ∧ out.pointSets.length = n := by
  unfold numPointSets at h
  obtain ⟨out, hout, hlen⟩ := except_bind_ok h
  cases hlen
  exact ⟨out, hout, rfl⟩

theorem intermediateSets_parts (meta_ : ConstraintSystemMeta) (data : Data)
    (out : IntermediateSets) (hdummy : data.dummyEvalWords = [])
    (h : intermediateSets meta_ data = .ok out) :
    ∃ (qs : List Query) (sets : IntermediateSets),
      queries meta_ data = .ok qs ∧
      constructIntermediateSetsImpl qs = .ok sets ∧
      sortSets sets = .ok out := by
  unfold intermediateSets at h
  rw [hdummy] at h
  simp only [List.isEmpty_nil, if_true] at h
  obtain ⟨qs, hq, hrest⟩ := except_bind_ok h
  rw [show (pure qs : Except Fault (List Query)) = .ok qs from rfl] at hrest
  simp only [Bind.bind, Except.bind] at hrest
  cases hci : constructIntermediateSetsImpl qs with
  | error e =>
      rw [hci] at hrest
      simp at hrest
  | ok sets =>
      rw [hci] at hrest
      simp only [Bind.bind, Except.bind] at hrest
      exact ⟨qs, sets, hq, hci, hrest⟩

theorem Data.new_dummyEvalWords (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (mem : VerifierMemoryLayout) (d : Data) (h : Data.new meta_ vk mem = .ok d) :
    d.dummyEvalWords = [] := by
  unfold Data.new at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · obtain ⟨slots, _hslots, h1⟩ := except_bind_ok h
    obtain ⟨permZEvals, _hp, h2⟩ := except_bind_ok h1
    obtain ⟨lookupEvals, _hl, h3⟩ := except_bind_ok h2
    obtain ⟨trashEvals, _ht, h4⟩ := except_bind_ok h3
    cases h4
    rfl

theorem numPointSets_eq_of_queries
    (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (sets out : IntermediateSets)
    (hdummy : data.dummyEvalWords = [])
    (hq : queries meta_ data = .ok qs)
    (hci : constructIntermediateSetsImpl qs = .ok sets)
    (hs : sortSets sets = .ok out) :
    numPointSets meta_ data = .ok out.pointSets.length := by
  unfold numPointSets intermediateSets
  simp only [hdummy, List.isEmpty_nil, if_true, Bind.bind, Except.bind, hq]
  rw [show (pure qs : Except Fault (List Query)) = .ok qs from rfl]
  dsimp only
  rw [hci]
  dsimp only
  rw [hs]
  rfl

theorem numPointSets_eq_of_queries_pointSets_length
    (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (sets out : IntermediateSets)
    (hdummy : data.dummyEvalWords = [])
    (hq : queries meta_ data = .ok qs)
    (hci : constructIntermediateSetsImpl qs = .ok sets)
    (hs : sortSets sets = .ok out) :
    numPointSets meta_ data = .ok sets.pointSets.length := by
  rw [numPointSets_eq_of_queries meta_ data qs sets out hdummy hq hci hs,
    sortSets_pointSets_length sets out hs]

theorem foldl_addKeyFind_map {α : Type} (l : List α) (f : α → List Nat)
    (init : List (List Nat × Nat)) :
    l.foldl (fun acc a => addKeyFind acc (f a)) init =
      (l.map f).foldl addKeyFind init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons]
      exact ih (addKeyFind init (f a))

theorem foldl_btreeMap_map (l : List (EcPoint × List Nat × List Word))
    (init : List (List Nat × Nat)) :
    l.foldl (fun m (e : EcPoint × List Nat × List Word) =>
      btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) init =
    (l.map (fun e => btreeSetFromList natCmp e.2.1)).foldl btreeMapEntryOrInsert init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons]
      exact ih (btreeMapEntryOrInsert init (btreeSetFromList natCmp a.2.1))

/-- The per-index correspondence between a verifier query vector and a generator
    query list, stated at the level the counts need: a common commitment key `K`,
    a point-to-rotation map `fk`, and the equality-reflection hypotheses that make
    the two grouping relations compute the same partition. -/
structure KzgQueryMapData {F C : Type} [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (queriesV : Array (VerifierQuery F C)) (queriesG : List Query) where
  K : Type
  beqK : BEq K
  lawfulK : LawfulBEq K
  fk : F → Int
  ck : CommitmentReference F C → K
  gk : EcPoint → K
  L : List (VerifierQuery F C × Query)
  hVlist : queriesV.toList = L.map Prod.fst
  hGlist : queriesG = L.map Prod.snd
  hpairP : ∀ x ∈ L, fk x.1.point = x.2.rotation
  hpairC : ∀ x ∈ L, ck x.1.commitment = gk x.2.comm
  hCommEq : ∀ p ∈ L, ∀ p' ∈ L,
    eqC p.1.commitment p'.1.commitment = (ck p.1.commitment == ck p'.1.commitment)
  hGCommEq : ∀ p ∈ L, ∀ p' ∈ L,
    ecPointBeq p.2.comm p'.2.comm = (gk p.2.comm == gk p'.2.comm)
  hPointEq : ∀ p ∈ L, ∀ p' ∈ L,
    (p.1.point == p'.1.point) = (fk p.1.point == fk p'.1.point)

theorem findIdx?_eq_of_equiv {α : Type} (l : List α) (r : α → α → Bool)
    (hrefl : ∀ a ∈ l, r a a = true)
    (hsymm : ∀ a ∈ l, ∀ b ∈ l, r a b = r b a)
    (htrans : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l,
      r a b = true → r b c = true → r a c = true)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) :
    r a b = (l.findIdx? (r a) == l.findIdx? (r b)) := by
  have hsomeA : (l.findIdx? (r a)).isSome = true := by
    rw [List.findIdx?_isSome]
    exact List.any_eq_true.mpr ⟨a, ha, hrefl a ha⟩
  have hsomeB : (l.findIdx? (r b)).isSome = true := by
    rw [List.findIdx?_isSome]
    exact List.any_eq_true.mpr ⟨b, hb, hrefl b hb⟩
  cases hia : l.findIdx? (r a) with
  | none => rw [hia] at hsomeA; cases hsomeA
  | some i0 =>
  cases hib : l.findIdx? (r b) with
  | none => rw [hib] at hsomeB; cases hsomeB
  | some j0 =>
  obtain ⟨hi0, hpredA, hminA⟩ := List.findIdx?_eq_some_iff_getElem.mp hia
  obtain ⟨hj0, hpredB, hminB⟩ := List.findIdx?_eq_some_iff_getElem.mp hib
  have hleA : ∀ (j : Nat) (hj : j < l.length), r a l[j] = true → i0 ≤ j := by
    intro j hj hpred
    by_contra hlt
    exact hminA j (by omega) hpred
  have hleB : ∀ (j : Nat) (hj : j < l.length), r b l[j] = true → j0 ≤ j := by
    intro j hj hpred
    by_contra hlt
    exact hminB j (by omega) hpred
  by_cases hab : r a b = true
  · have hba : r b a = true := by
      rw [← hsymm a ha b hb]
      exact hab
    have hbi0 : r b l[i0] = true :=
      htrans b hb a ha l[i0] (List.getElem_mem hi0) hba hpredA
    have hle1 : j0 ≤ i0 := hleB i0 hi0 hbi0
    have haj0 : r a l[j0] = true :=
      htrans a ha b hb l[j0] (List.getElem_mem hj0) hab hpredB
    have hle2 : i0 ≤ j0 := hleA j0 hj0 haj0
    have heq : i0 = j0 := by omega
    subst heq
    simp [hab]
  · have habf : r a b = false := by simpa using hab
    have hbf : r b a = false := by
      rw [← hsymm a ha b hb]
      exact habf
    have hne : i0 ≠ j0 := by
      intro heq
      subst heq
      have haj : r a l[i0] = true := hpredA
      have hbj : r b l[i0] = true := hpredB
      have hcontra : r a b = true :=
        htrans a ha l[i0] (List.getElem_mem hi0) b hb haj (by
          rw [hsymm l[i0] (List.getElem_mem hi0) b hb]
          exact hbj)
      rw [habf] at hcontra
      cases hcontra
    have hbeq : (some i0 == some j0) = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hne (Option.some.inj (beq_iff_eq.mp h))
    rw [hbeq]
    exact habf

noncomputable def ckOf {F C : Type} (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (L : List (VerifierQuery F C × Query)) (a : CommitmentReference F C) : Option Nat :=
  L.findIdx? (fun p => eqC a p.1.commitment)

noncomputable def gkOf {F C : Type} (L : List (VerifierQuery F C × Query)) (c : EcPoint) : Option Nat :=
  L.findIdx? (fun p => ecPointBeq c p.2.comm)

/-- The paired list used by the concrete datum: the two query lists zipped in
    order. The projections are the actual lists whenever the lengths agree. -/
def pairQueries {F C : Type} (queriesV : Array (VerifierQuery F C)) (queriesG : List Query) :
    List (VerifierQuery F C × Query) :=
  queriesV.toList.zip queriesG

theorem pairQueries_fst {F C : Type} (queriesV : Array (VerifierQuery F C))
    (queriesG : List Query) (h : queriesV.size = queriesG.length) :
    (pairQueries queriesV queriesG).map Prod.fst = queriesV.toList := by
  unfold pairQueries
  exact List.map_fst_zip (by simpa [Array.length_toList] using Nat.le_of_eq h)

theorem pairQueries_snd {F C : Type} (queriesV : Array (VerifierQuery F C))
    (queriesG : List Query) (h : queriesV.size = queriesG.length) :
    (pairQueries queriesV queriesG).map Prod.snd = queriesG := by
  unfold pairQueries
  exact List.map_snd_zip (by simpa [Array.length_toList] using Nat.le_of_eq h.symm)

noncomputable def KzgQueryMapData.ofList {F C : Type} [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (queriesV : Array (VerifierQuery F C)) (queriesG : List Query)
    (L : List (VerifierQuery F C × Query))
    (hVlist : queriesV.toList = L.map Prod.fst)
    (hGlist : queriesG = L.map Prod.snd)
    (fk : F → Int) (hPointEq : ∀ a b, (a == b) = (fk a == fk b))
    (hpairP : ∀ p ∈ L, fk p.1.point = p.2.rotation)
    (hclass : ∀ p ∈ L, ∀ p' ∈ L,
      eqC p.1.commitment p'.1.commitment = ecPointBeq p.2.comm p'.2.comm)
    (hCommRefl : ∀ p ∈ L, eqC p.1.commitment p.1.commitment = true)
    (hCommSymm : ∀ p ∈ L, ∀ p' ∈ L,
      eqC p.1.commitment p'.1.commitment = eqC p'.1.commitment p.1.commitment)
    (hCommTrans : ∀ p ∈ L, ∀ p' ∈ L, ∀ p'' ∈ L,
      eqC p.1.commitment p'.1.commitment = true →
      eqC p'.1.commitment p''.1.commitment = true →
      eqC p.1.commitment p''.1.commitment = true)
    (hGRefl : ∀ p ∈ L, ecPointBeq p.2.comm p.2.comm = true)
    (hGSymm : ∀ p ∈ L, ∀ p' ∈ L,
      ecPointBeq p.2.comm p'.2.comm = ecPointBeq p'.2.comm p.2.comm)
    (hGTrans : ∀ p ∈ L, ∀ p' ∈ L, ∀ p'' ∈ L,
      ecPointBeq p.2.comm p'.2.comm = true →
      ecPointBeq p'.2.comm p''.2.comm = true →
      ecPointBeq p.2.comm p''.2.comm = true) :
    KzgQueryMapData eqC queriesV queriesG := by
  refine
    { K := Option Nat
      beqK := inferInstance
      lawfulK := inferInstance
      fk := fk
      ck := ckOf eqC L
      gk := gkOf L
      L := L
      hVlist := hVlist
      hGlist := hGlist
      hpairP := hpairP
      hpairC := ?_
      hCommEq := ?_
      hGCommEq := ?_
      hPointEq := ?_ }
  · intro p hp
    have hidx : L.findIdx? (fun p' => eqC p.1.commitment p'.1.commitment) =
        L.findIdx? (fun p' => ecPointBeq p.2.comm p'.2.comm) :=
      findIdx?_congr L _ _ (fun p' hp' => hclass p hp p' hp')
    simpa [ckOf, gkOf] using hidx
  · intro p hp p' hp'
    have h := findIdx?_eq_of_equiv L
      (fun p p' => eqC p.1.commitment p'.1.commitment)
      hCommRefl hCommSymm hCommTrans hp hp'
    simpa [ckOf] using h
  · intro p hp p' hp'
    have h := findIdx?_eq_of_equiv L
      (fun p p' => ecPointBeq p.2.comm p'.2.comm)
      hGRefl hGSymm hGTrans hp hp'
    simpa [gkOf] using h
  · intro p hp p' hp'
    exact hPointEq p.1.point p'.1.point


/-- **THE PAIRED-LIST DATUM CONSTRUCTOR.** The concrete `L` is
    `pairQueries queriesV queriesG`; `pairQueries_fst`/`_snd` supply the two
    list projections whenever the lengths agree.  The remaining arguments are
    the per-pair point/commitment facts and the reflection hypotheses, exactly
    as in `KzgQueryMapData.ofList`. -/
noncomputable def KzgQueryMapData.ofPairQueries {F C : Type} [BEq F]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (queriesV : Array (VerifierQuery F C)) (queriesG : List Query)
    (hLen : queriesV.size = queriesG.length)
    (fk : F → Int) (hPointEq : ∀ a b, (a == b) = (fk a == fk b))
    (hpairP : ∀ p ∈ pairQueries queriesV queriesG, fk p.1.point = p.2.rotation)
    (hclass : ∀ p ∈ pairQueries queriesV queriesG, ∀ p' ∈ pairQueries queriesV queriesG,
      eqC p.1.commitment p'.1.commitment = ecPointBeq p.2.comm p'.2.comm)
    (hCommRefl : ∀ p ∈ pairQueries queriesV queriesG,
      eqC p.1.commitment p.1.commitment = true)
    (hCommSymm : ∀ p ∈ pairQueries queriesV queriesG,
      ∀ p' ∈ pairQueries queriesV queriesG,
      eqC p.1.commitment p'.1.commitment = eqC p'.1.commitment p.1.commitment)
    (hCommTrans : ∀ p ∈ pairQueries queriesV queriesG,
      ∀ p' ∈ pairQueries queriesV queriesG, ∀ p'' ∈ pairQueries queriesV queriesG,
      eqC p.1.commitment p'.1.commitment = true →
      eqC p'.1.commitment p''.1.commitment = true →
      eqC p.1.commitment p''.1.commitment = true)
    (hGRefl : ∀ p ∈ pairQueries queriesV queriesG,
      ecPointBeq p.2.comm p.2.comm = true)
    (hGSymm : ∀ p ∈ pairQueries queriesV queriesG,
      ∀ p' ∈ pairQueries queriesV queriesG,
      ecPointBeq p.2.comm p'.2.comm = ecPointBeq p'.2.comm p.2.comm)
    (hGTrans : ∀ p ∈ pairQueries queriesV queriesG,
      ∀ p' ∈ pairQueries queriesV queriesG, ∀ p'' ∈ pairQueries queriesV queriesG,
      ecPointBeq p.2.comm p'.2.comm = true →
      ecPointBeq p'.2.comm p''.2.comm = true →
      ecPointBeq p.2.comm p''.2.comm = true) :
    KzgQueryMapData eqC queriesV queriesG :=
  KzgQueryMapData.ofList eqC queriesV queriesG (pairQueries queriesV queriesG)
    (pairQueries_fst queriesV queriesG hLen).symm
    (pairQueries_snd queriesV queriesG hLen).symm
    fk hPointEq hpairP hclass hCommRefl hCommSymm hCommTrans hGRefl hGSymm hGTrans

theorem constructIntermediateSets_pointSets_size_eq_of_queryMap
    {F C K : Type} [Field F] [BEq F] [BEq K]
    [LawfulBEq F] [LawfulBEq K]
    (eqC : CommitmentReference F C → CommitmentReference F C → Bool)
    (fk : F → Int) (ck : CommitmentReference F C → K) (gk : EcPoint → K)
    (L : List (VerifierQuery F C × Query))
    (hCommEq : ∀ p ∈ L, ∀ p' ∈ L,
      eqC p.1.commitment p'.1.commitment = (ck p.1.commitment == ck p'.1.commitment))
    (hGCommEq : ∀ p ∈ L, ∀ p' ∈ L,
      ecPointBeq p.2.comm p'.2.comm = (gk p.2.comm == gk p'.2.comm))
    (hPointEq : ∀ p ∈ L, ∀ p' ∈ L,
      (p.1.point == p'.1.point) = (fk p.1.point == fk p'.1.point))
    (queriesV : Array (VerifierQuery F C)) (queriesG : List Query)
    (hVlist : queriesV.toList = L.map Prod.fst)
    (hGlist : queriesG = L.map Prod.snd)
    (hpairP : ∀ p ∈ L, fk p.1.point = p.2.rotation)
    (hpairC : ∀ p ∈ L, ck p.1.commitment = gk p.2.comm)
    (cm : Array (CD F C)) (pointSets : Array (Array F)) (setsG : IntermediateSets)
    (hV : constructIntermediateSets eqC queriesV = .ok (cm, pointSets))
    (hG : constructIntermediateSetsImpl queriesG = .ok setsG) :
    pointSets.size = setsG.pointSets.length := by
  obtain ⟨points, cm0, setsV, hpass1, hsets, hsize⟩ :=
    constructIntermediateSets_parts eqC queriesV cm pointSets hV
  -- generator step 1
  unfold constructIntermediateSetsImpl at hG
  cases hstep1 : queriesG.foldlM constructIntermediateSetsImpl.step1Pass ([], []) with
  | error e =>
      rw [hstep1] at hG
      cases hG
  | ok step1 =>
  have hstepFold : step1Fold queriesG ([], []) = .ok step1 := by
    rw [← foldlM_step1Fold queriesG ([], [])]
    exact hstep1
  -- simulation
  have hV1 : constructIntermediateSets.pass1 eqC (L.map Prod.fst) [] [] = .ok (points, cm0) := by
    rw [← hVlist]
    exact hpass1
  have hG1 : step1Fold (L.map Prod.snd) ([], []) = .ok step1 := by
    rw [← hGlist]
    exact hstepFold
  have hsim := pass1_step1_sim (eqC := eqC) (fk := fk) (ck := ck) (gk := gk)
    L hCommEq hGCommEq hPointEq [] L rfl [] [] [] [] points step1.2 cm0 step1.1
    rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)
    hpairP hpairC hV1 hG1
  obtain ⟨_hrots, _hcomm, hidx, hndC, _hndG⟩ := hsim
  -- verifier count
  have hsetsFold : setsV = cm0.foldl (fun acc cd => addKeyFind acc (natSort cd.pointIndices.toList)) [] := by
    rw [← hsets]
    exact pass2_snd_fold cm0 [] []
  -- generator count
  have hgen : setsG.pointSets.length =
      (step1.1.foldl (fun m (e : EcPoint × List Nat × List Word) =>
        btreeMapEntryOrInsert m (btreeSetFromList natCmp e.2.1)) []).length :=
    constructIntermediateSetsImpl_pointSets_length queriesG setsG step1 hstep1 hG
  -- key list equality
  have hidx' : List.map (fun cd => cd.pointIndices.toList) cm0 =
      List.map (fun e => e.2.1) step1.1 := by
    simpa only [cmsIdx, gsIdx] using hidx
  have hkeys : cm0.map (fun cd => natSort cd.pointIndices.toList) =
      step1.1.map (fun e => btreeSetFromList natCmp e.2.1) := by
    calc
      cm0.map (fun cd => natSort cd.pointIndices.toList)
          = cm0.map (fun cd => btreeSetFromList natCmp cd.pointIndices.toList) := by
            apply List.map_congr_left
            intro cd hcd
            exact natSort_eq_btreeSetFromList_of_nodup _ (hndC cd hcd)
      _ = (cm0.map (fun cd => cd.pointIndices.toList)).map
            (fun pis => btreeSetFromList natCmp pis) := by
            rw [List.map_map]
            rfl
      _ = (step1.1.map (fun e => e.2.1)).map
            (fun pis => btreeSetFromList natCmp pis) := by
            rw [hidx']
      _ = step1.1.map (fun e => btreeSetFromList natCmp e.2.1) := by
            rw [List.map_map]
            rfl
  rw [hsize, hsetsFold, hgen]
  rw [foldl_addKeyFind_map _ _ [], foldl_btreeMap_map _ [], hkeys]
  exact foldl_addKeyFind_length_eq_btreeMap _

end Midfall.LoweringV3

