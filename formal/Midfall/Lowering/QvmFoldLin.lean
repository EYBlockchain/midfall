-- |
-- Midfall.Lowering.QvmFoldLin
--
-- QFOLD, link 2 of the QVM chain: the GENERIC arithmetic that ties the emitted y-batch fold
-- over the QuotientExpr trees to Midfall.Halo2.computeLinearizationCommitment, the verifier's
-- own linearization. Nothing here mentions a plan, a program or a fixture (D-P71): the
-- statements are over an abstract list of (bucket key, gap, value) triples and an abstract
-- field, so the instantiation in QvmFold.lean is a wiring job and not a re-derivation.
--
-- FOUR PIECES.
--   * linValAt / groupedAdd / KeySorted / keySorted_eq: the linearization's grouped walk
--     (Linearization.lean:88) is insert-or-add into a list kept in the BTreeMap key order, so
--     it is characterised by the per-key total it records; keySorted_eq says a key-sorted
--     list with those totals is unique. That is what makes the MSM's scalar ORDER derivable
--     rather than assumed - the one thing that is easy to get silently wrong.
--   * gfoldGo / gweight / linBucket: the identity at position i of a stream of length m
--     carries y^(m-1-i), because verifier.rs:75 walks the identities in reverse.
--   * bfold / gapSum / endIdx / SpacedAfter / WellSpaced / bfoldTarget_naive: one bucket's
--     sparse fold acc := acc*y^gap + v, and the telescoping that turns it into the naive
--     global-power sum once each gap is the distance between consecutive indices. The head's
--     gap is unconstrained because it multiplies the bucket's initial value, which is 0.
--   * FFold / fstep / ffold_qn / ffold_buckets: the whole-stream fold read in the field,
--     with the main accumulator and each bucket given in closed form.
--
-- NOT YET WIRED: QvmFold.lean's two builder rows still hold their sorries. What is left is
-- instantiation, not ideas: (a) the abstract stream at a plan, with the bucket key and value
-- taken from the verifier's own tagged array so IdentityCorrespondence supplies the bridge;
-- (b) the per-step transport from foldStep to fstep, which needs only qvmToFr_add,
-- qvmToFr_mul, qvmToFr_pow and qvmToFr_val; (c) WellSpaced for a bucket's sub-stream, which
-- is SelectorFoldConsistent's third conjunct read at consecutive bucket positions; and (d) a
-- reading of computeLinearizationCommitment's success that names the grouped list, the
-- appended scalars and the subtracted None bucket.
--
-- NO Midfall/Instances/ import (D-P17). No native_decide. No new axiom: every lemma here is
-- on [propext, Classical.choice, Quot.sound] or less.

import Midfall.Halo2.Exec.Linearization

set_option linter.unusedSectionVars false

namespace Midfall.Lowering
open Midfall.Halo2

variable {F : Type} [Field F]

theorem obEq {a b : Option Nat} : (a == b) = true ↔ a = b := beq_iff_eq

theorem map_eq_map_of_mem {α β : Type} (f g : α → β) (l : List α)
    (h : ∀ a ∈ l, f a = g a) : List.map f l = List.map g l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.map_cons, List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
          ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem ga_nil (key : Option Nat) (v : F) :
    groupedAdd ([] : List (Option Nat × F)) key v = [(key, v)] := rfl

theorem ga_cons (k : Option Nat) (e : F) (as : List (Option Nat × F))
    (key : Option Nat) (v : F) :
    groupedAdd ((k, e) :: as) key v =
      if k == key then (k, e + v) :: as
      else if optionNatLt key k then (key, v) :: (k, e) :: as
           else (k, e) :: groupedAdd as key v := rfl

/-- The total the linearization's grouped walk has recorded for one key. -/
def linValAt (q : Option Nat) : List (Option Nat × F) → F
  | [] => 0
  | (k, v) :: acc => (if k == q then v else 0) + linValAt q acc

theorem linValAt_nil (q : Option Nat) :
    linValAt q ([] : List (Option Nat × F)) = 0 := rfl

theorem linValAt_cons (q k : Option Nat) (v : F) (acc : List (Option Nat × F)) :
    linValAt q ((k, v) :: acc) = (if k == q then v else 0) + linValAt q acc := rfl

theorem linValAt_append (q : Option Nat) (as bs : List (Option Nat × F)) :
    linValAt q (as ++ bs) = linValAt q as + linValAt q bs := by
  induction as with
  | nil => exact (zero_add _).symm
  | cons a rest ih =>
      cases a with
      | mk k v =>
      show (if k == q then v else 0) + linValAt q (rest ++ bs) =
          ((if k == q then v else 0) + linValAt q rest) + linValAt q bs
      rw [ih, add_assoc]

theorem linValAt_notMem (q : Option Nat) (acc : List (Option Nat × F))
    (h : q ∉ acc.map Prod.fst) : linValAt q acc = 0 := by
  induction acc with
  | nil => exact linValAt_nil q
  | cons a rest ih =>
      cases a with
      | mk k v =>
      have hne : ¬ (k == q) = true := by
        intro hh
        apply h
        rw [List.mem_map]
        exact ⟨(k, v), List.mem_cons.mpr (Or.inl rfl), by simpa using hh⟩
      rw [linValAt_cons, if_neg hne]
      rw [ih (fun hm => h (List.mem_cons_of_mem k hm)), add_zero]

theorem linValAt_groupedAdd (acc : List (Option Nat × F)) (key : Option Nat) (v : F)
    (q : Option Nat) :
    linValAt q (groupedAdd acc key v) = linValAt q acc + (if key == q then v else 0) := by
  induction acc with
  | nil =>
      show (if key == q then v else 0) + 0 = 0 + (if key == q then v else 0)
      rw [add_zero, zero_add]
  | cons a rest ih =>
      cases a with
      | mk k e =>
      rw [ga_cons]
      by_cases h1 : (k == key) = true
      · have hke : k = key := Iff.mp obEq h1
        rw [if_pos h1, ← hke]
        simp only [linValAt_cons]
        by_cases hq : (k == q) = true
        · simp only [if_pos hq]
          abel
        · simp only [if_neg hq]
          abel
      · rw [if_neg h1]
        by_cases h2 : optionNatLt key k
        · rw [if_pos h2]
          simp only [linValAt_cons]
          abel
        · rw [if_neg h2]
          simp only [linValAt_cons, ih]
          abel



theorem optionNatLt_trichotomy (a b : Option Nat) :
    optionNatLt a b ∨ a = b ∨ optionNatLt b a := by
  cases a with
  | none =>
      cases b with
      | none => exact Or.inr (Or.inl rfl)
      | some b => exact Or.inl (by simp [optionNatLt])
  | some x =>
      cases b with
      | none => exact Or.inr (Or.inr (by simp [optionNatLt]))
      | some y =>
          cases Nat.lt_trichotomy x y with
          | inl h => exact Or.inl (by simp [optionNatLt]; exact h)
          | inr h =>
              cases h with
              | inl h => exact Or.inr (Or.inl (congrArg some h))
              | inr h => exact Or.inr (Or.inr (by simp [optionNatLt]; exact h))

theorem optionNatLt_asym (a b : Option Nat) (h : optionNatLt a b) : ¬ optionNatLt b a := by
  cases a with
  | none =>
      cases b with
      | none => exact absurd h (by simp [optionNatLt])
      | some b => exact by simp [optionNatLt]
  | some x =>
      cases b with
      | none => exact absurd h (by simp [optionNatLt])
      | some y =>
          intro h2
          simp [optionNatLt] at h h2
          omega

theorem optionNatLt_trans (a b c : Option Nat)
    (h1 : optionNatLt a b) (h2 : optionNatLt b c) : optionNatLt a c := by
  cases a with
  | none =>
      cases b with
      | none => exact absurd h1 (by simp [optionNatLt])
      | some b =>
          cases c with
          | none => exact absurd h2 (by simp [optionNatLt])
          | some c => exact by simp [optionNatLt]
  | some x =>
      cases b with
      | none => exact absurd h1 (by simp [optionNatLt])
      | some y =>
          cases c with
          | none => exact absurd h2 (by simp [optionNatLt])
          | some z =>
              simp [optionNatLt] at h1 h2 ⊢
              omega

/-- The grouped walk's key invariant: the association list is in the BTreeMap key order
    (None before Some, Some ascending), written locally rather than with List.Pairwise.
    Strictness gives duplicate-freeness for free. -/
def KeySorted : List (Option Nat × F) → Prop
  | [] => True
  | (k, _) :: rest => (∀ y ∈ rest.map Prod.fst, optionNatLt k y) ∧ KeySorted rest

theorem keySorted_nil : KeySorted ([] : List (Option Nat × F)) := trivial

theorem keySorted_cons (k : Option Nat) (v : F) (acc : List (Option Nat × F))
    (h1 : ∀ y ∈ acc.map Prod.fst, optionNatLt k y) (h2 : KeySorted acc) :
    KeySorted ((k, v) :: acc) := ⟨h1, h2⟩

theorem mem_keys_groupedAdd (acc : List (Option Nat × F)) (key : Option Nat) (v : F)
    (q : Option Nat) :
    q ∈ (groupedAdd acc key v).map Prod.fst ↔ q = key ∨ q ∈ acc.map Prod.fst := by
  induction acc with
  | nil =>
      rw [ga_nil]
      constructor
      · intro h
        exact Or.inl (List.mem_singleton.mp h)
      · intro h
        rcases h with rfl | h
        · exact List.mem_singleton.mpr rfl
        · exact absurd h (by simp)
  | cons a rest ih =>
      cases a with
      | mk k e =>
      rw [ga_cons]
      by_cases h1 : (k == key) = true
      · have hke : k = key := Iff.mp obEq h1
        rw [if_pos h1, ← hke]
        show (q ∈ k :: rest.map Prod.fst) ↔ q = k ∨ q ∈ k :: rest.map Prod.fst
        simp only [List.mem_cons]
        tauto
      · rw [if_neg h1]
        by_cases h2 : optionNatLt key k
        · rw [if_pos h2]
          show (q ∈ key :: k :: rest.map Prod.fst) ↔ q = key ∨ q ∈ k :: rest.map Prod.fst
          simp only [List.mem_cons]
        · rw [if_neg h2]
          show (q ∈ k :: (groupedAdd rest key v).map Prod.fst) ↔
            q = key ∨ q ∈ k :: rest.map Prod.fst
          simp only [List.mem_cons, ih]
          tauto

theorem keySorted_groupedAdd (acc : List (Option Nat × F)) (key : Option Nat) (v : F)
    (h : KeySorted acc) : KeySorted (groupedAdd acc key v) := by
  induction acc with
  | nil => exact keySorted_cons key v [] (by simp) keySorted_nil
  | cons a rest ih =>
      cases a with
      | mk k e =>
      have hrest : ∀ y ∈ rest.map Prod.fst, optionNatLt k y := h.1
      have htail : KeySorted rest := h.2
      rw [ga_cons]
      by_cases h1 : (k == key) = true
      · have hke : k = key := Iff.mp obEq h1
        rw [if_pos h1]
        exact keySorted_cons k (e + v) rest hrest htail
      · rw [if_neg h1]
        by_cases h2 : optionNatLt key k
        · rw [if_pos h2]
          refine keySorted_cons key v ((k, e) :: rest) ?_ h
          intro y hy
          rcases List.mem_cons.mp hy with hy | hy
          · rw [hy]
            exact h2
          · exact optionNatLt_trans key k y h2 (hrest y hy)
        · rw [if_neg h2]
          refine keySorted_cons k e (groupedAdd rest key v) ?_ (ih htail)
          intro y hy
          rcases (mem_keys_groupedAdd rest key v y).mp hy with hy | hy
          · rw [hy]
            cases optionNatLt_trichotomy k key with
            | inl hk => exact hk
            | inr hh =>
                cases hh with
                | inl he => exact absurd he (by intro q; exact h1 (by rw [obEq]; exact q))
                | inr hk => exact absurd hk h2
          · exact hrest y hy

/-- A key-sorted association list is determined by its key list and its per-key totals. -/
theorem keySorted_tabulate (acc : List (Option Nat × F)) (h : KeySorted acc) :
    acc = (acc.map Prod.fst).map (fun q => (q, linValAt q acc)) := by
  induction acc with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | mk k v =>
      have hrest : KeySorted rest := h.2
      have hnodup : k ∉ rest.map Prod.fst := by
        intro hk
        exact optionNatLt_asym k k (h.1 k hk) (h.1 k hk)
      have hzero : linValAt k rest = 0 := linValAt_notMem k rest hnodup
      have hhead : linValAt k ((k, v) :: rest) = v := by
        rw [linValAt_cons, hzero, if_pos (by rw [obEq]), add_zero]
      have hmap : ∀ q, q ∈ rest.map Prod.fst →
          linValAt q ((k, v) :: rest) = linValAt q rest := by
        intro q hq
        rw [linValAt_cons]
        have hne : ¬ (k == q) = true := by
          intro hh
          exact hnodup ((Iff.mp obEq hh).symm ▸ hq)
        rw [if_neg hne, zero_add]
      have htail : (rest.map Prod.fst).map (fun q => (q, linValAt q ((k, v) :: rest)))
          = (rest.map Prod.fst).map (fun q => (q, linValAt q rest)) := by
        refine map_eq_map_of_mem _ _ _ ?_
        intro q hq
        exact Prod.ext rfl (hmap q hq)
      show (k, v) :: rest =
          (k :: rest.map Prod.fst).map (fun q => (q, linValAt q ((k, v) :: rest)))
      rw [List.map_cons, hhead, htail, ← ih hrest]

/-- The key list of a key-sorted association list, on its own. -/
def KeyAsc : List (Option Nat) → Prop
  | [] => True
  | x :: rest => (∀ y ∈ rest, optionNatLt x y) ∧ KeyAsc rest

theorem keySorted_keyAsc (acc : List (Option Nat × F)) (h : KeySorted acc) :
    KeyAsc (acc.map Prod.fst) := by
  induction acc with
  | nil => exact trivial
  | cons a rest ih =>
      cases a with
      | mk k v => exact ⟨h.1, ih h.2⟩

theorem keyAsc_nodup {xs : List (Option Nat)} (h : KeyAsc xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
      refine List.Nodup.cons ?_ (ih h.2)
      intro hk
      exact optionNatLt_asym x x (h.1 x hk) (h.1 x hk)

/-- Two ascending duplicate-free key lists with the same members are equal. -/
theorem keys_eq_of_sorted {xs ys : List (Option Nat)}
    (hx : KeyAsc xs) (hy : KeyAsc ys) (h : ∀ q, q ∈ xs ↔ q ∈ ys) : xs = ys := by
  induction xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y rest =>
          have hbad : y ∈ ([] : List (Option Nat)) :=
            (h y).mpr (List.mem_cons.mpr (Or.inl rfl))
          exact absurd hbad (by simp)
  | cons x xs' ih =>
      cases ys with
      | nil =>
          have hbad : x ∈ ([] : List (Option Nat)) :=
            (h x).mp (List.mem_cons.mpr (Or.inl rfl))
          exact absurd hbad (by simp)
      | cons y ys' =>
          have hnx : x ∉ xs' := by
            intro hk
            exact optionNatLt_asym x x (hx.1 x hk) (hx.1 x hk)
          have hny : y ∉ ys' := by
            intro hk
            exact optionNatLt_asym y y (hy.1 y hk) (hy.1 y hk)
          have hxy : x = y := by
            by_cases hne : x = y
            · exact hne
            · exfalso
              have hyin : y ∈ xs' := by
                have h1 := (h y).mpr (List.mem_cons.mpr (Or.inl rfl))
                rw [List.mem_cons] at h1
                rcases h1 with hy | hy
                · exact absurd hy.symm hne
                · exact hy
              have hxin : x ∈ ys' := by
                have h1 := (h x).mp (List.mem_cons.mpr (Or.inl rfl))
                rw [List.mem_cons] at h1
                rcases h1 with hx | hx
                · exact absurd hx hne
                · exact hx
              exact optionNatLt_asym x y (hx.1 y hyin) (hy.1 x hxin)
          subst hxy
          suffices hh : xs' = ys' by rw [hh]
          refine keys_eq_of_sorted hx.2 hy.2 (fun q => ?_)
          have hq := h q
          rw [List.mem_cons, List.mem_cons] at hq
          by_cases hqx : q = x
          · subst hqx
            exact ⟨fun h => absurd h hnx, fun h => absurd h hny⟩
          · tauto

/-- Two key-sorted association lists with the same keys and the same per-key totals are
    equal. This is the only place the BTreeMap key order is used essentially. -/
theorem keySorted_eq (as bs : List (Option Nat × F)) (ha : KeySorted as) (hb : KeySorted bs)
    (hmem : ∀ q, q ∈ as.map Prod.fst ↔ q ∈ bs.map Prod.fst)
    (hval : ∀ q, linValAt q as = linValAt q bs) : as = bs := by
  have hk : as.map Prod.fst = bs.map Prod.fst :=
    keys_eq_of_sorted (keySorted_keyAsc as ha) (keySorted_keyAsc bs hb) hmem
  rw [keySorted_tabulate as ha, keySorted_tabulate bs hb, hk]
  refine map_eq_map_of_mem _ _ _ (fun q _ => Prod.ext rfl (hval q))

/-- The grouped walk with an explicit starting power and accumulator: gfoldGo y xs p acc is
    what Linearization.lean's grouped foldl computes after the elements of xs have been
    consumed, where the next element is weighted by p. -/
def gfoldGo (y : F) : List (Option Nat × F) → F → List (Option Nat × F) → List (Option Nat × F)
  | [], _, acc => acc
  | (k, v) :: xs, p, acc => gfoldGo y xs (p * y) (groupedAdd acc k (p * v))

/-- The weighted total a list of tagged values contributes to one key, where the element at
    position j carries y^j. -/
def gweight (y : F) : List (Option Nat × F) → F → Option Nat → F
  | [], _, _ => 0
  | (k, v) :: xs, p, q => (if k == q then p * v else 0) + gweight y xs (p * y) q

theorem gfoldGo_linValAt (y : F) (xs : List (Option Nat × F)) : ∀ (p : F)
    (acc : List (Option Nat × F)) (q : Option Nat),
    linValAt q (gfoldGo y xs p acc) = linValAt q acc + gweight y xs p q := by
  induction xs with
  | nil => intro p acc q; rw [gfoldGo, gweight, add_zero]
  | cons a as ih =>
      cases a with
      | mk k v =>
      intro p acc q
      show linValAt q (gfoldGo y as (p * y) (groupedAdd acc k (p * v))) = _
      rw [ih (p * y) (groupedAdd acc k (p * v)) q, linValAt_groupedAdd, gweight, add_assoc]

theorem gfoldGo_keySorted (y : F) (xs : List (Option Nat × F)) : ∀ (p : F)
    (acc : List (Option Nat × F)), KeySorted acc → KeySorted (gfoldGo y xs p acc) := by
  induction xs with
  | nil => intro p acc h; exact h
  | cons a as ih =>
      cases a with
      | mk k v =>
      intro p acc h
      show KeySorted (gfoldGo y as (p * y) (groupedAdd acc k (p * v)))
      exact ih (p * y) (groupedAdd acc k (p * v)) (keySorted_groupedAdd acc k (p * v) h)

theorem gweight_append (y : F) (xs : List (Option Nat × F)) :
    ∀ (ys : List (Option Nat × F)) (p : F) (q : Option Nat),
      gweight y (xs ++ ys) p q = gweight y xs p q + gweight y ys (p * y ^ xs.length) q := by
  induction xs with
  | nil =>
      intro ys p q
      show gweight y ys p q = gweight y [] p q + gweight y ys (p * y ^ [].length) q
      rw [gweight, List.length_nil, pow_zero, mul_one, zero_add]
  | cons a as ih =>
      cases a with
      | mk k v =>
      intro ys p q
      show (if k == q then p * v else 0) + gweight y (as ++ ys) (p * y) q = _
      rw [ih ys (p * y) q]
      have hpow : p * y ^ (as.length + 1) = (p * y) * y ^ as.length := by
        rw [pow_succ]
        ring
      simp only [List.length_cons, List.length_nil, Nat.zero_add, hpow, gweight]
      abel

/-- The linearization's weighted bucket sum read forward: the element at position i of a
    list of length m carries y^(m-1-i) (verifier.rs:75 walks the identities in reverse). -/
def linBucket (y : F) (m : Nat) : List (Option Nat × F) → Option Nat → F
  | [], _ => 0
  | (k, v) :: xs, q => (if k == q then y ^ (m - 1) * v else 0) + linBucket y (m - 1) xs q

theorem gweight_reverse (y : F) (xs : List (Option Nat × F)) : ∀ (q : Option Nat),
    gweight y xs.reverse 1 q = linBucket y xs.length xs q := by
  induction xs with
  | nil => intro q; rfl
  | cons a as ih =>
      cases a with
      | mk k v =>
      intro q
      rw [List.reverse_cons, gweight_append, ih]
      simp only [gweight, pow_zero, mul_one, add_zero, List.length_reverse, one_mul]
      have hRHS : linBucket y ((k, v) :: as).length ((k, v) :: as) q
          = (if k == q then y ^ as.length * v else 0) + linBucket y as.length as q := by
        show linBucket y (as.length + 1) ((k, v) :: as) q = _
        rw [linBucket, show (as.length + 1) - 1 = as.length by omega]
      rw [hRHS]
      rw [add_comm (linBucket y as.length as q)]


/-- One entry of a bucket's own sub-stream: its position in the whole stream, the gap the
    fold multiplies by, and the value it adds. -/
structure BEntry (F : Type) where
  idx : Nat
  gap : Nat
  val : F

/-- A bucket's sparse fold in the field: acc := acc * y^gap + val at each entry. -/
def bfold (y : F) : List (BEntry F) → F → F
  | [], acc => acc
  | e :: ps, acc => bfold y ps (acc * y ^ e.gap + e.val)

/-- The sum of a bucket's gaps. -/
def gapSum : List (BEntry F) → Nat
  | [] => 0
  | e :: ps => e.gap + gapSum ps

/-- The index a bucket's entry list ends at: the last entry's index, 0 for the empty list. -/
def endIdx : List (BEntry F) → Nat
  | [] => 0
  | [e] => e.idx
  | _ :: ps => endIdx ps

theorem bfold_eq (y : F) (ps : List (BEntry F)) : ∀ (acc : F),
    bfold y ps acc = bfold y ps 0 + acc * y ^ gapSum ps := by
  induction ps with
  | nil => intro acc; rw [bfold, bfold, gapSum, pow_zero, mul_one, zero_add]
  | cons e ps ih =>
      intro acc
      have hA : bfold y (e :: ps) acc = bfold y ps (acc * y ^ e.gap + e.val) := rfl
      have hB : bfold y (e :: ps) 0 = bfold y ps (0 * y ^ e.gap + e.val) := rfl
      have hC : bfold y ps (0 * y ^ e.gap + e.val)
          = bfold y ps 0 + (0 * y ^ e.gap + e.val) * y ^ gapSum ps := ih _
      rw [hA, ih (acc * y ^ e.gap + e.val), hB, hC, gapSum]
      ring

/-- The closed form of a bucket's sparse fold started from zero. -/
def bfoldTarget (y : F) : List (BEntry F) → F
  | [] => 0
  | e :: ps => bfoldTarget y ps + e.val * y ^ gapSum ps

theorem bfold_zero (y : F) (ps : List (BEntry F)) : bfold y ps 0 = bfoldTarget y ps := by
  induction ps with
  | nil => rfl
  | cons e ps ih =>
      show bfold y ps (0 * y ^ e.gap + e.val) = bfoldTarget y ps + e.val * y ^ gapSum ps
      rw [bfold_eq, ih]
      ring


/-- A bucket's entry list is spaced after index p when its indices are strictly ascending
    and each gap is the distance to the previous index, the head's predecessor being p. The
    head's own gap is unconstrained in what follows because it multiplies the bucket's
    initial value, which is 0. -/
inductive SpacedAfter {F : Type} : Nat → List (BEntry F) → Prop
  | nil : ∀ (p : Nat), SpacedAfter p []
  | cons : ∀ (p : Nat) (e : BEntry F) (rest : List (BEntry F)),
      p < e.idx → e.gap = e.idx - p → SpacedAfter e.idx rest →
      SpacedAfter p (e :: rest)

theorem spacedAfter_tail {F : Type} : ∀ (p : Nat) (e : BEntry F) (rest : List (BEntry F)),
    SpacedAfter p (e :: rest) → SpacedAfter e.idx rest
  | p, e, rest, h => by cases h with | cons _ _ _ _ _ hrest => exact hrest

theorem spacedAfter_head {F : Type} : ∀ (p : Nat) (e : BEntry F) (rest : List (BEntry F)),
    SpacedAfter p (e :: rest) → p < e.idx ∧ e.gap = e.idx - p
  | p, e, rest, h => by cases h with | cons _ _ _ hlt hgap _ => exact ⟨hlt, hgap⟩


/-- A bucket's entry list is well-spaced when its indices are strictly ascending and every
    gap after the first is the distance to the previous index. The head's own gap is
    unconstrained because it multiplies the bucket's initial value, which is 0. -/
def WellSpaced {F : Type} : List (BEntry F) → Prop
  | [] => True
  | e :: rest => SpacedAfter e.idx rest

theorem wellSpaced_nil {F : Type} : WellSpaced (@List.nil (BEntry F)) := trivial

theorem wellSpaced_cons_of {F : Type} (e : BEntry F) (rest : List (BEntry F))
    (h : SpacedAfter e.idx rest) : WellSpaced (e :: rest) := h

theorem spacedAfter_ge {F : Type} (p : Nat) (ps : List (BEntry F)) (h : SpacedAfter p ps) :
    ∀ e ∈ ps, p ≤ e.idx := by
  induction h with
  | nil p => intro e he; exact absurd he (by simp)
  | cons p e rest hlt hgap hrest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact Nat.le_of_lt (hx ▸ hlt)
      · exact Nat.le_trans (Nat.le_of_lt hlt) (ih x hx)

theorem spacedAfter_endIdx {F : Type} (p : Nat) (ps : List (BEntry F)) (h : SpacedAfter p ps)
    (hne : ps ≠ []) : p ≤ endIdx ps := by
  cases h with
  | nil p => exact absurd hne (by simp)
  | cons p e rest hlt hgap hrest =>
      cases rest with
      | nil => show p ≤ endIdx [e]; rw [endIdx]; exact Nat.le_of_lt hlt
      | cons g rest' =>
          show p ≤ endIdx (e :: g :: rest')
          have h1 : endIdx (e :: g :: rest') = endIdx (g :: rest') := rfl
          rw [h1]
          exact Nat.le_trans (Nat.le_of_lt hlt)
            (spacedAfter_endIdx e.idx (g :: rest') hrest (by simp))

theorem gapSum_after (ps : List (BEntry F)) : ∀ (p : Nat), SpacedAfter p ps →
    gapSum ps = endIdx ps - p := by
  induction ps with
  | nil => intro p _; rw [gapSum, endIdx]; omega
  | cons f rest ih =>
      intro p h
      have hge : p ≤ f.idx := Nat.le_of_lt (spacedAfter_head p f rest h).1
      have hgap : f.gap = f.idx - p := (spacedAfter_head p f rest h).2
      have htail : SpacedAfter f.idx rest := spacedAfter_tail p f rest h
      cases rest with
      | nil =>
          have h1 : gapSum ([] : List (BEntry F)) = endIdx [] - f.idx := ih f.idx htail
          simp only [gapSum, hgap, endIdx, h1, Nat.sub_self, Nat.sub_zero, add_zero]
      | cons g rest' =>
          have hle : f.idx ≤ endIdx (g :: rest') :=
            spacedAfter_endIdx f.idx (g :: rest') htail (by simp)
          have h1 : gapSum (g :: rest') = endIdx (g :: rest') - f.idx := ih f.idx htail
          rw [gapSum, hgap, h1]
          show (f.idx - p) + (endIdx (g :: rest') - f.idx) = endIdx (f :: g :: rest') - p
          rw [show endIdx (f :: g :: rest') = endIdx (g :: rest') from rfl]
          omega

theorem bfoldTarget_naive (y : F) (ps : List (BEntry F)) : WellSpaced ps →
    bfoldTarget y ps = ((ps.map fun e => e.val * y ^ (endIdx ps - e.idx))).sum := by
  induction ps with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro h
      cases rest with
      | nil =>
          show bfoldTarget y [] + e.val * y ^ gapSum [] =
            (([e.val * y ^ (endIdx [e] - e.idx)] : List F)).sum
          rw [bfoldTarget, gapSum, endIdx, List.sum_cons, List.sum_nil, Nat.sub_self, pow_zero,
            mul_one, add_zero, zero_add]
      | cons f rest' =>
          have hwell : WellSpaced (f :: rest') := spacedAfter_tail e.idx f rest' h
          have h1 : gapSum (f :: rest') = endIdx (f :: rest') - e.idx :=
            gapSum_after (f :: rest') e.idx h
          have h2 : endIdx (e :: f :: rest') = endIdx (f :: rest') := rfl
          have h3 : ((e :: f :: rest').map fun z => z.val * y ^ (endIdx (f :: rest') - z.idx))
              = (e.val * y ^ (endIdx (f :: rest') - e.idx))
                :: ((f :: rest').map fun z => z.val * y ^ (endIdx (f :: rest') - z.idx)) := by
              simp only [List.map_cons]
          rw [bfoldTarget, ih hwell, h1, h2, h3, List.sum_cons, add_comm _ _]

/-- The field-level fold state: the main accumulator and one bucket per simple selector. -/
structure FFold (F : Type) where
  qn : F
  buckets : List F

/-- One step of the field-level fold, mirroring foldStep: the main accumulator advances by y
    on both arms, and the bucket named by the key takes the value after its own gap. -/
def fstep (y : F) (st : FFold F) (e : Option Nat × BEntry F) : FFold F :=
  match e.1 with
  | none => { st with qn := st.qn * y + e.2.val }
  | some s => { qn := st.qn * y,
                buckets := st.buckets.modify s (fun x => x * y ^ e.2.gap + e.2.val) }

/-- The entries of the abstract stream that belong to bucket s, in order. -/
def proj (s : Nat) : List (Option Nat × BEntry F) → List (BEntry F)
  | [] => []
  | (none, _) :: xs => proj s xs
  | (some k, b) :: xs => if k == s then b :: proj s xs else proj s xs

/-- The main accumulator's own entry list: every position advances it by exactly one y, and
    only the main arm contributes a value. -/
def mainEntries (xs : List (Option Nat × BEntry F)) : List (BEntry F) :=
  xs.map fun e => ⟨e.2.idx, 1, if e.1 == none then e.2.val else 0⟩



theorem length_fstep (y : F) (st : FFold F) (e : Option Nat × BEntry F) :
    (fstep y st e).buckets.length = st.buckets.length := by
  cases e with
  | mk k b =>
      cases k with
      | none => rfl
      | some s => exact List.length_modify _ _ _

theorem getD_modify (bs : List F) (f : F → F) : ∀ (s : Nat), s < bs.length →
    (bs.modify s f).getD s 0 = f (bs.getD s 0) := by
  induction bs with
  | nil => intro s h; exact absurd h (by simp)
  | cons a rest ih =>
      intro s h
      cases s with
      | zero => rfl
      | succ s => exact ih s (by simpa using h)

theorem getD_modify_ne (bs : List F) (f : F → F) : ∀ (s s' : Nat), s ≠ s' →
    (bs.modify s' f).getD s 0 = bs.getD s 0 := by
  induction bs with
  | nil => intro s s' _; simp [List.modify]
  | cons a rest ih =>
      intro s s' hne
      cases s with
      | zero =>
          cases s' with
          | zero => exact absurd rfl hne
          | succ s' => rfl
      | succ s =>
          cases s' with
          | zero => rfl
          | succ s' => exact ih s s' (fun he => hne (congrArg Nat.succ he))

theorem mainEntries_none (b : BEntry F) (xs : List (Option Nat × BEntry F)) :
    mainEntries ((none, b) :: xs) = ⟨b.idx, 1, b.val⟩ :: mainEntries xs := rfl

theorem mainEntries_some (s : Nat) (b : BEntry F) (xs : List (Option Nat × BEntry F)) :
    mainEntries ((some s, b) :: xs) = ⟨b.idx, 1, 0⟩ :: mainEntries xs := rfl

theorem proj_none (s : Nat) (b : BEntry F) (xs : List (Option Nat × BEntry F)) :
    proj s ((none, b) :: xs) = proj s xs := rfl

theorem proj_same (s : Nat) (b : BEntry F) (xs : List (Option Nat × BEntry F)) :
    proj s ((some s, b) :: xs) = b :: proj s xs := by
  show (if s == s then b :: proj s xs else proj s xs) = b :: proj s xs
  rw [if_pos (by rw [beq_iff_eq])]

theorem proj_ne (s k : Nat) (b : BEntry F) (xs : List (Option Nat × BEntry F))
    (h : ¬ (k == s) = true) : proj s ((some k, b) :: xs) = proj s xs := by
  show (if k == s then b :: proj s xs else proj s xs) = proj s xs
  rw [if_neg h]

theorem fstep_none (y : F) (st : FFold F) (b : BEntry F) :
    fstep y st (none, b) = ⟨st.qn * y + b.val, st.buckets⟩ := rfl

theorem fstep_some (y : F) (st : FFold F) (s : Nat) (b : BEntry F) :
    fstep y st (some s, b) = ⟨st.qn * y,
      st.buckets.modify s (fun x => x * y ^ b.gap + b.val)⟩ := rfl

theorem ffold_qn (y : F) (xs : List (Option Nat × BEntry F)) :
    ∀ (st : FFold F), (List.foldl (fstep y) st xs).qn = bfold y (mainEntries xs) st.qn := by
  induction xs with
  | nil => intro st; rfl
  | cons e xs ih =>
      intro st
      show (List.foldl (fstep y) (fstep y st e) xs).qn = _
      rw [ih (fstep y st e)]
      cases e with
      | mk k b =>
          cases k with
          | none => rw [fstep_none, mainEntries_none, bfold, pow_one]
          | some s => rw [fstep_some, mainEntries_some, bfold, pow_one, add_zero]

theorem ffold_buckets (y : F) (xs : List (Option Nat × BEntry F)) (s : Nat) :
    ∀ (st : FFold F), s < st.buckets.length →
      ((List.foldl (fstep y) st xs).buckets).getD s 0
        = bfold y (proj s xs) (st.buckets.getD s 0) := by
  induction xs with
  | nil => intro st _; rfl
  | cons e xs ih =>
      intro st hlen
      show ((List.foldl (fstep y) (fstep y st e) xs).buckets).getD s 0 = _
      rw [ih (fstep y st e) (length_fstep y st e ▸ hlen)]
      cases e with
      | mk k b =>
          cases k with
          | none => rw [fstep_none, proj_none]
          | some s' =>
              by_cases hss : s = s'
              · subst hss
                rw [fstep_some, proj_same, getD_modify _ _ s hlen, bfold]
              · have hne : ¬ (s' == s) = true := by
                  intro hh
                  have he : s' = s := by simpa using hh
                  exact hss he.symm
                rw [fstep_some, proj_ne s s' b xs hne,
                  getD_modify_ne _ _ s s' (fun he => hss he)]


/-! ## Instantiation support (QLIN)

    Everything below is still generic (D-P71): it speaks about an abstract list of
    (key, gap, index, value) entries and about the verifier's own grouped walk, never about a
    plan or a fixture. What it supplies is the last mile QFOLD's header named as remaining:
    the reverse-walk sum read off an indexed list (`linBucket_range`), the filtered
    sub-list / sum-with-an-if bridge (`proj_map_sum_eq`), `WellSpaced` for a
    bucket's sub-stream (`wellSpaced_proj`), the foldl that produces the verifier's
    grouped list written as `gfoldGo` (`gfoldGo_foldl`), and a reading of
    `computeLinearizationCommitment`'s emit step that names the appended scalars and the
    subtracted None bucket (`foldlM_linStep_ok`). -/

theorem range'_succ (o n : Nat) : List.range' o (n + 1) = o :: List.range' (o + 1) n := rfl

/-- The sum over a bucket's sub-list is the sum over the whole stream with a zero for every
    entry that is not in the bucket. No index hypothesis is needed: the entries are carried
    through unchanged by `proj`. -/
theorem proj_map_sum_eq (f : BEntry F → F) (s : Nat)
    (xs : List (Option Nat × BEntry F)) :
    ((proj s xs).map f).sum = (xs.map fun p => if p.1 == some s then f p.2 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      cases a with
      | mk k b =>
      rw [List.map_cons, List.sum_cons]
      by_cases hk : (k == some s) = true
      · have hke : k = some s := Iff.mp beq_iff_eq hk
        subst hke
        rw [proj_same, List.map_cons, List.sum_cons, ih]
        rw [if_pos (by rw [beq_iff_eq])]
      · rw [if_neg hk]
        cases k with
        | none => rw [proj_none, zero_add]; exact ih
        | some k' =>
            have hne : ¬ (k' == s) = true := by
              intro h
              apply hk
              rw [beq_iff_eq]
              exact congrArg some (Iff.mp beq_iff_eq h)
            rw [proj_ne s k' b as hne, zero_add]
            exact ih

/-- `linBucket` read as an indexed sum: the entry at position i of a list whose indices
    start at o carries y to the power (o + length - 1 - i), i.e. its distance from the END of
    the stream. This is the reverse walk of verifier.rs:75 made available termwise, which is
    what lets a bucket's sparse fold be matched against it. -/
theorem linBucket_range_aux (y : F) (q : Option Nat) :
    ∀ (xs : List (Option Nat × F)) (o : Nat),
      linBucket y xs.length xs q
        = ((xs.zip (List.range' o xs.length)).map fun p =>
            if p.1.1 == q then y ^ (xs.length + o - 1 - p.2) * p.1.2 else 0).sum := by
  intro xs
  induction xs with
  | nil => intro o; rfl
  | cons a as ih =>
      intro o
      cases a with
      | mk k v =>
      show (if k == q then y ^ as.length * v else 0) + linBucket y as.length as q = _
      rw [ih (o + 1)]
      simp only [List.length_cons, range'_succ]
      have hzip : ((k, v) :: as).zip (o :: List.range' (o + 1) as.length)
          = ((k, v), o) :: as.zip (List.range' (o + 1) as.length) := rfl
      have hfun : (fun p : (Option Nat × F) × Nat =>
            if p.1.1 == q then y ^ (as.length + 1 + o - 1 - p.2) * p.1.2 else 0)
          = (fun p : (Option Nat × F) × Nat =>
            if p.1.1 == q then y ^ (as.length + (o + 1) - 1 - p.2) * p.1.2 else 0) := by
        funext p
        cases p with
        | mk e i =>
        show (if e.1 == q then y ^ (as.length + 1 + o - 1 - i) * e.2 else 0) = _
        rw [show as.length + 1 + o - 1 - i = as.length + (o + 1) - 1 - i from by omega]
      rw [hzip, hfun]
      simp only [List.map_cons, List.sum_cons]
      have hexp : as.length + (o + 1) - 1 - o = as.length := by omega
      rw [hexp]

theorem linBucket_range (y : F) (xs : List (Option Nat × F)) (q : Option Nat) :
    linBucket y xs.length xs q
      = ((xs.zip (List.range' 0 xs.length)).map fun p =>
          if p.1.1 == q then y ^ (xs.length - 1 - p.2) * p.1.2 else 0).sum := by
  simpa using linBucket_range_aux y q xs 0

/-- A stream whose entries carry their own position as `idx` and a gap of 1 is spaced
    after `o - 1`: consecutive indices, consecutive gaps. The main accumulator's stream
    is of exactly this shape. -/
theorem spacedAfter_consecutive : ∀ (ps : List (BEntry F)) (o : Nat), 1 ≤ o →
    (∀ i < ps.length, (ps.getD i ⟨0, 0, 0⟩).idx = o + i) →
    (∀ i < ps.length, (ps.getD i ⟨0, 0, 0⟩).gap = 1) →
    SpacedAfter (o - 1) ps := by
  intro ps
  induction ps with
  | nil => intro o _ _ _; exact SpacedAfter.nil (o - 1)
  | cons e ps ih =>
      intro o ho hidx hgap
      have he : e.idx = o := hidx 0 (by simp)
      have hrest : ∀ i < ps.length, (ps.getD i ⟨0, 0, 0⟩).idx = (o + 1) + i := by
        intro i hi
        have h : (e :: ps).getD (i + 1) ⟨0, 0, 0⟩ = ps.getD i ⟨0, 0, 0⟩ := rfl
        rw [← h]
        have := hidx (i + 1) (by simp [hi])
        omega
      have hgaprest : ∀ i < ps.length, (ps.getD i ⟨0, 0, 0⟩).gap = 1 := by
        intro i hi
        have h : (e :: ps).getD (i + 1) ⟨0, 0, 0⟩ = ps.getD i ⟨0, 0, 0⟩ := rfl
        rw [← h]
        exact hgap (i + 1) (by simp [hi])
      have htail : SpacedAfter e.idx ps := by
        rw [he]
        exact ih (o + 1) (by omega) hrest hgaprest
      refine SpacedAfter.cons (o - 1) e ps (by omega) ?_ htail
      have h1 : e.gap = 1 := hgap 0 (by simp)
      rw [he]
      omega

/-- The verifier's grouped walk is `gfoldGo` with starting power 1 and an empty
    accumulator: `foldl` over the reversed expression list, exactly as
    `computeLinearizationCommitment` writes it. -/
theorem gfoldGo_foldl (y : F) : ∀ (xs : List (Option Nat × F)) (acc : List (Option Nat × F))
    (p : F),
    (xs.foldl (init := (acc, p))
        (fun st e => (groupedAdd st.1 e.1 (st.2 * e.2), st.2 * y)))
        = (gfoldGo y xs p acc, p * y ^ xs.length) := by
  intro xs
  induction xs with
  | nil => intro acc p; simp [gfoldGo]
  | cons a as ih =>
      intro acc p
      cases a with
      | mk k v =>
      show (as.foldl (init := (groupedAdd acc k (p * v), p * y))
            (fun st e => (groupedAdd st.1 e.1 (st.2 * e.2), st.2 * y))) = _
      rw [ih (groupedAdd acc k (p * v)) (p * y)]
      show (gfoldGo y as (p * y) (groupedAdd acc k (p * v)),
            p * y * y ^ as.length) = (gfoldGo y as (p * y) (groupedAdd acc k (p * v)), _)
      have hpow : p * y * y ^ as.length = p * y ^ (as.length + 1) := by
        rw [pow_succ]
        ring
      rw [hpow, List.length_cons]

/-- The values the linearization's MSM gets from the grouped list: the `some` entries,
    in list order. -/
def someSnds : List (Option Nat × F) → List F
  | [] => []
  | (some _, v) :: xs => v :: someSnds xs
  | (none, _) :: xs => someSnds xs

/-- The values folded into the expected evaluation instead of a point: the `none`
    entries. -/
def noneSnds : List (Option Nat × F) → List F
  | [] => []
  | (some _, v) :: xs => noneSnds xs
  | (none, v) :: xs => v :: noneSnds xs

theorem someSnds_map_tabulate (ks : List (Option Nat)) (f : Option Nat → F) :
    someSnds (ks.map fun q => (q, f q))
      = (ks.filter fun q => match q with | some _ => true | none => false).map f := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      rw [List.map_cons, List.filter_cons]
      cases k with
      | none =>
          show someSnds (ks.map fun q => (q, f q))
            = (ks.filter fun q => match q with | some _ => true | none => false).map f
          exact ih
      | some c =>
          show f (some c) :: someSnds (ks.map fun q => (q, f q))
            = f (some c)
              :: (ks.filter fun q => match q with | some _ => true | none => false).map f
          exact congrArg (List.cons (f (some c))) ih

/-- The `none` bucket's total is exactly what `linValAt none` reads back: the sum of the
    `none` entries. This is the identity that turns the emit fold's subtraction into the
    verifier's `expected_eval -= eval`. -/
theorem linValAt_none (acc : List (Option Nat × F)) :
    linValAt none acc = (noneSnds acc).sum := by
  induction acc with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | mk k v =>
      rw [linValAt_cons, ih]
      cases k with
      | none => rw [noneSnds, if_pos (by rw [beq_iff_eq]), List.sum_cons]
      | some c =>
          rw [noneSnds]
          rw [if_neg (by intro h; exact absurd (Iff.mp beq_iff_eq h) (by simp)), zero_add]

/-- A successful monadic bind has a successful left action and a successful continuation on
    its result. The same shape as `Midfall.Lowering.peel_bind` (Qvm.lean:792), restated
    here because this file does not import Qvm.lean and must not: the linearization leaf is
    below the QVM in the dependency order. -/
theorem peel_bind_ok {α β ε : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : (x >>= k) = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- The emit step of `computeLinearizationCommitment` (verifier.rs:80-94), named so it
    can be reasoned about: the local lambda inside the port is defeq to this. -/
def linStep {G₁ : Type} (vk : VerifyingKey F G₁)
    (st : List G₁ × List F × List CommitmentLabel × F) (entry : Option Nat × F) :
    Except Fault (List G₁ × List F × List CommitmentLabel × F) :=
  match entry with
  | (some colIdx, eval) =>
      match vk.fixedCommitments[colIdx]? with
      | none => .error (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84")
      | some com =>
        .ok (st.1 ++ [com], st.2.1 ++ [eval], st.2.2.1 ++ [CommitmentLabel.fixed colIdx],
          st.2.2.2)
  | (none, eval) => .ok (st.1, st.2.1, st.2.2.1, st.2.2.2 - eval)

/-- What a successful emit fold records: the appended scalars are exactly the `some`
    entries' values in list order, and the expected evaluation is the starting value minus the
    `none` entries' sum. No sortedness is needed here - that is what `keySorted_tabulate`
    is for. -/
theorem foldlM_linStep_ok {G₁ : Type} (vk : VerifyingKey F G₁) :
    ∀ (grouped : List (Option Nat × F))
      (st : List G₁ × List F × List CommitmentLabel × F)
      (pts : List G₁) (scals : List F) (labs : List CommitmentLabel) (ee : F),
      grouped.foldlM (linStep vk) st = .ok (pts, scals, labs, ee) →
      scals = st.2.1 ++ someSnds grouped ∧ ee = st.2.2.2 - (noneSnds grouped).sum := by
  intro grouped
  induction grouped with
  | nil =>
      intro st pts scals labs ee h
      cases st with
      | mk p sc =>
        cases sc with
        | mk s2 l2 =>
        rw [List.foldlM_nil] at h
        have h2 : Except.ok (p, s2, l2) = Except.ok (pts, scals, labs, ee) := h
        cases h2
        exact ⟨by simp [someSnds], by simp [noneSnds, sub_zero]⟩
  | cons a rest ih =>
      intro st pts scals labs ee h
      cases a with
      | mk k v =>
      rw [List.foldlM_cons] at h
      cases k with
      | none =>
          rw [linStep] at h
          have h2 : List.foldlM (linStep vk) (st.1, st.2.1, st.2.2.1, st.2.2.2 - v) rest
              = Except.ok (pts, scals, labs, ee) := h
          have hI := ih _ pts scals labs ee h2
          refine ⟨by rw [hI.1, someSnds], by rw [hI.2, noneSnds, List.sum_cons, sub_sub]⟩
      | some c =>
          cases hcm : vk.fixedCommitments[c]? with
          | none =>
              have hbad : linStep vk st (some c, v)
                  = .error (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84") := by
                rw [linStep, hcm]
              rw [hbad] at h
              have h' : Except.error (Fault.panic "proofs/src/plonk/linearization/verifier.rs:84")
                  = Except.ok (pts, scals, labs, ee) := h
              cases h'
          | some com =>
              rw [linStep] at h
              simp only [hcm] at h
              have h2 : List.foldlM (linStep vk)
                    (st.1 ++ [com], st.2.1 ++ [v], st.2.2.1 ++ [CommitmentLabel.fixed c],
                      st.2.2.2) rest = Except.ok (pts, scals, labs, ee) := h
              have hI := ih _ pts scals labs ee h2
              have hc1 : scals = st.2.1 ++ someSnds ((some c, v) :: rest) := by
                rw [hI.1]
                simp [someSnds]
              refine ⟨hc1, by rw [hI.2, noneSnds]⟩


end Midfall.Lowering
