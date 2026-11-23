/-
  Midfall.LoweringV3.EndToEndAlgebra

  The two per-function halves of the `PrepareLogSlots` bridge (D1):

    * `PresWidthSeq` for `Verifier.readAlgebra`  : quotient commitments, then
      exactly the scalar evaluations the function reads, counting the
      committed-instance filter, advice blocks, fixed evals (after the
      simple-selector subtraction), permutation-common evals, `3k - 1` per
      permutation product set, `nbChunks + 3` per lookup, `1` per trashcan.
    * `PresWidthSeq` for `multiPrepare`          : `[g1]`, one scalar per
      q-eval set (`qEvalSets.size`, linked to the `constructIntermediateSets`
      point-set count), then `[g1]`.

  Everything here is in terms of the functions' REAL width expressions, measured
  from `Exec/Verifier.lean`, `Exec/Permutation.lean`, `Exec/Logup.lean`,
  `Exec/Trash.lean` and `Exec/Kzg/MultiOpen.lean`; nothing is weakened and no
  hypothesis is added to a row, bundle, root or `PrepareLogSlots`.

  NOTE for the D1 integrator. `readAlgebra` has no `Protocol`/`Proof` parameter;
  the count below is the exact per-argument count that the protocol-side
  instantiation (`evalReadCount = protocol.proof.evals.length`) still has to
  identify. The permutation count is `3k - 1`, not the `3k - 2` in the doc
  comment of `Permutation.Committed.evaluate`: the loop reads two evals per set
  plus a third for every set but the last, and `ProtocolPlan.validate`'s
  `expectedPermZEvals := 3 * numPermutationZs - 1` agrees.
-/
import Midfall.LoweringV3.EndToEnd
import Midfall.Halo2.Exec.Kzg.MultiOpen
import Midfall.Halo2.Exec.Verifier

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## 1. Arithmetic of width lists

    `PresWidthSeq` states the appended list exactly, so every loop closure needs
    the flatten of per-item `replicate` blocks as one `replicate` of the summed
    count. -/

namespace AlgebraWidths

/-- A list of `replicate (f x) w` blocks flattens to one block of the sum. -/
theorem flatten_map_replicate {α : Type} (l : List α) (f : α → Nat) (w : Nat) :
    (l.map (fun x => List.replicate (f x) w)).flatten = List.replicate ((l.map f).sum) w := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.flatten_cons, List.sum_cons, ih,
        List.replicate_append_replicate]

/-- `(l.map (fun _ => n)).sum = l.length * n`. -/
theorem sum_map_const {α : Type} (l : List α) (n : Nat) :
    (l.map (fun _ => n)).sum = l.length * n := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      rw [Nat.succ_mul]
      omega

/-- The constant-block version. -/
theorem flatten_map_replicate_const {α : Type} (l : List α) (n w : Nat) :
    (l.map (fun _ => List.replicate n w)).flatten = List.replicate (l.length * n) w := by
  have h := flatten_map_replicate l (fun _ => n) w
  rw [sum_map_const] at h
  exact h

/-- An `if`-filtered single-width block: `[w]` on the predicate, `[]` off it. -/
theorem flatten_map_ite {α : Type} (l : List α) (pred : α → Prop) [DecidablePred pred]
    (w : Nat) :
    (l.map (fun x => if pred x then [w] else [])).flatten
      = List.replicate (l.filter pred).length w := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : pred a
      · simp [h, ih, List.replicate_succ]
      · simp [h, ih]

/-- `filterMap` over a list on which the function is always defined keeps the
    length. (Used for the `sortById`-order filter of `buildQ`.) -/
theorem filterMap_length_of_forall_some {α β : Type} (l : List α) (g : α → Option β)
    (h : ∀ a ∈ l, ∃ b, g a = some b) : (l.filterMap g).length = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      obtain ⟨b, hb⟩ := h a (by simp)
      have has : ∀ x ∈ as, ∃ y, g x = some y := fun x hx => h x (by simp [hx])
      simp [hb, ih has]

/-- An always-empty flatten block. -/
theorem flatten_map_nil {α : Type} (l : List α) :
    (l.map (fun _ => ([] : List Nat))).flatten = [] := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

/-- A list of singleton blocks flattens to one `replicate`. -/
theorem flatten_map_single {α : Type} (l : List α) (w : Nat) :
    (l.map (fun _ => [w])).flatten = List.replicate l.length w := by
  have h := flatten_map_replicate_const l 1 w
  simpa using h

/-- The seven value-evaluation blocks of `readAlgebra`, in source order, folded
    into one `replicate`. The trailing `[]` is the `pure` record constructor. -/
theorem combine_widths (w₁ w₂ : Nat) (q a b c d e f g : Nat) :
    List.replicate q w₁ ++ List.replicate (a + b + c + d + e + f + g) w₂ =
      List.replicate q w₁ ++ (List.replicate a w₂ ++ (List.replicate b w₂ ++
        (List.replicate c w₂ ++ (List.replicate d w₂ ++ (List.replicate e w₂ ++
          (List.replicate f w₂ ++ (List.replicate g w₂ ++ []))))))) := by
  have hinner : List.replicate (a + b + c + d + e + f + g) w₂ =
      List.replicate a w₂ ++ (List.replicate b w₂ ++
        (List.replicate c w₂ ++ (List.replicate d w₂ ++ (List.replicate e w₂ ++
          (List.replicate f w₂ ++ (List.replicate g w₂ ++ [])))))) := by
    repeat rw [← List.append_assoc]
    repeat rw [List.replicate_append_replicate]
    rw [List.append_nil]
  rw [hinner]

/-- The per-set width schedule of `Permutation.Committed.evaluate`, closed form:
    every set but the last reads three scalars, the last reads two, so `3k - 1`
    for `k >= 1` and `0` for `k = 0`. -/
theorem range_width_map (w : Nat) : ∀ k : Nat,
    ((List.range k).map (fun i => if i < k - 1 then [w, w, w] else [w, w])).flatten
      = List.replicate (3 * k - 1) w
  | 0 => by simp
  | k + 1 => by
      rw [List.range_succ]
      have hmap : (List.range k).map
          (fun i => if i < (k + 1) - 1 then [w, w, w] else [w, w])
            = (List.range k).map (fun _ => [w, w, w]) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [if_pos (by omega : i < (k + 1) - 1)]
      have hk : (if k < (k + 1) - 1 then ([w, w, w] : List Nat) else [w, w]) = [w, w] := by
        rw [if_neg (by omega : ¬ k < (k + 1) - 1)]
      simp only [List.map_append, List.map_cons, List.map_nil, hmap, hk,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      change (List.map (fun _ => List.replicate 3 w) (List.range k)).flatten ++ [w, w]
        = List.replicate (3 * (k + 1) - 1) w
      rw [flatten_map_replicate_const, List.length_range]
      change List.replicate (k * 3) w ++ List.replicate 2 w
        = List.replicate (3 * (k + 1) - 1) w
      rw [List.replicate_append_replicate]
      congr 1
      omega

end AlgebraWidths

namespace AlgebraWidths

/-! ## 4. The `buildQ` size link

    `buildQ` builds `qEvalSets` from `pointSets` by `arrayReplicate pointSets.size`,
    a size-preserving `arraySetD` fold, a length-preserving `mapM` and the
    `sortById` permutation; hence the first q-eval-set array has exactly
    `pointSets.size` entries. This is the link the `multiPrepare` width needs to
    name `a.qEvalSets.size` from `constructIntermediateSets`. -/

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

/-- `throw` is never `ok`. -/
theorem throw_ok_false {ε β : Type} (e : ε) {b : β}
    (h : (MonadExcept.throw e : Except ε β) = .ok b) : False := by
  change (Except.error e : Except ε β) = .ok b at h
  cases h

/-- `arraySetD` preserves the size. -/
theorem arraySetD_size {α : Type} (a : Array α) (i : Nat) (v : α) :
    (arraySetD a i v).size = a.size := by
  unfold arraySetD
  split
  · rename_i h
    rw [Array.size_set h]
  · rfl

/-- `arrayReplicate` has the requested size. -/
theorem arrayReplicate_size {α : Type} (n : Nat) (v : α) :
    (arrayReplicate n v).size = n := by
  unfold arrayReplicate
  rw [List.size_toArray, List.length_replicate]

/-- A `foldlM` whose steps preserve the second component's size. -/
theorem foldlM_pair_snd_size {α β γ : Type} {l : List α}
    {f : β × Array γ → α → Except Fault (β × Array γ)}
    (hf : ∀ st a st', f st a = .ok st' → st'.2.size = st.2.size) :
    ∀ {init : β × Array γ} {st' : β × Array γ},
      l.foldlM f init = .ok st' → st'.2.size = init.2.size := by
  induction l with
  | nil =>
      intro init st' h
      cases h
      rfl
  | cons a as ih =>
      intro init st' h
      rw [List.foldlM_cons] at h
      obtain ⟨st1, hstep, hrest⟩ := except_bind_ok h
      rw [ih hrest, hf init a st1 hstep]

/-- `List.mapM` over `Except` preserves the length. -/
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

/-- `sortById.insert` is a permutation of the cons. -/
theorem sortById_insert_perm (key : Nat → Nat × Nat) (i : Nat) :
    ∀ l : List Nat, (MultiPrepare.sortById.insert key i l).Perm (i :: l) := by
  intro l
  induction l with
  | nil =>
      rw [MultiPrepare.sortById.insert.eq_1]
  | cons j js ih =>
      rw [MultiPrepare.sortById.insert.eq_2]
      split
      · exact List.Perm.refl _
      · exact (ih.cons j).trans (List.Perm.swap i j js)

/-- `sortById` is a permutation of its input. -/
theorem sortById_perm (key : Nat → Nat × Nat) :
    ∀ l : List Nat, (MultiPrepare.sortById key l).Perm l
  | [] => List.Perm.nil
  | i :: rest =>
      (sortById_insert_perm key i (MultiPrepare.sortById key rest)).trans
        ((sortById_perm key rest).cons i)

/-- A valid index filter through an array keeps the list's length. -/
theorem filterMap_getElem?_length {α : Type} (order : List Nat) (xs : Array α)
    (h : ∀ i ∈ order, i < xs.size) :
    ((order.filterMap (fun i => xs[i]?)).toArray).size = order.length := by
  rw [List.size_toArray]
  exact filterMap_length_of_forall_some order _ (fun i hi => by
    exact ⟨_, Array.getElem?_eq_getElem (h i hi)⟩)

end AlgebraWidths

namespace PresWidthSeq

section MultiPrepareWidths

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **The `constructIntermediateSets` size link.** `buildQ` builds its
    q-eval-set array at exactly the input `pointSets` length: the initial value
    is `arrayReplicate pointSets.size`, the `arraySetD` fold preserves the size,
    the `mapM` over `evalsInnerProduct` preserves the length, and the
    `sortById` order is a permutation of `List.range pointSets.size`. -/
theorem buildQ_qEvalSets_size (feat : Features) (fc : FieldConsts (Fr p)) (x1 : Fr p)
    (commitmentMap : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p)))
    (r : Array (MSMKZG (Fr p) G₁) × Array (Array (Fr p)) × Array (Array (Fr p)))
    (h : MultiPrepare.buildQ (G₂ := G₂) (Gₜ := Gₜ) feat fc x1 commitmentMap pointSets
      = .ok r) :
    r.2.1.size = pointSets.size := by
  unfold MultiPrepare.buildQ at h
  dsimp only at h
  obtain ⟨st, hfold, h1⟩ := AlgebraWidths.except_bind_ok h
  split at h1
  · obtain ⟨qes', hmap, h3⟩ := AlgebraWidths.except_bind_ok h1
    cases h3
    have hst : st.2.size = pointSets.size := by
      have hsize := AlgebraWidths.foldlM_pair_snd_size
        (l := commitmentMap.toList)
        (f := fun st0 cd => do
          let terms ← cd.commitment.asTerms
          let termLabels := match cd.commitment with
            | .linear _ _ labels => labels
            | _ => arrayReplicate terms.size cd.commitmentLabel
          let msm := (List.zip terms.toList termLabels.toList).foldl
            (init := MSMKZG.init) fun m (t, l) => MSMKZG.appendTerm m t.1 t.2 l
          let qComs := arraySetD st0.1 cd.setIndex ((st0.1.getD cd.setIndex #[]).push msm)
          let qEvalSets := arraySetD st0.2 cd.setIndex ((st0.2.getD cd.setIndex #[]).push cd.evals)
          Pure.pure (qComs, qEvalSets))
        (init := (arrayReplicate pointSets.size (#[] : Array (MSMKZG (Fr p) G₁)),
                   arrayReplicate pointSets.size (#[] : Array (Array (Fr p)))))
        (hf := by
          intro st0 cd st0' hstep
          dsimp only at hstep
          obtain ⟨terms, _, hstep2⟩ := AlgebraWidths.except_bind_ok
            (m := cd.commitment.asTerms) hstep
          cases hstep2
          simp only [AlgebraWidths.arraySetD_size])
        hfold
      simpa [AlgebraWidths.arrayReplicate_size] using hsize
    have hqes : qes'.length = pointSets.size := by
      have hlen : qes'.length = st.2.toList.length :=
        AlgebraWidths.list_mapM_length (l := st.2.toList) (l' := qes') hmap
      have hlen2 : st.2.toList.length = st.2.size := Array.length_toList
      rw [hlen, hlen2, hst]
    have horder_len : (MultiPrepare.sortById
        (fun i => ((pointSets.getD i #[]).size, i))
        (List.range pointSets.size)).length = pointSets.size := by
      have hp := AlgebraWidths.sortById_perm
        (fun i => ((pointSets.getD i #[]).size, i)) (List.range pointSets.size)
      rw [hp.length_eq, List.length_range]
    have hidx : ∀ i ∈ MultiPrepare.sortById
        (fun i => ((pointSets.getD i #[]).size, i))
        (List.range pointSets.size), i < qes'.toArray.size := by
      intro i hi
      have hp := AlgebraWidths.sortById_perm
        (fun i => ((pointSets.getD i #[]).size, i)) (List.range pointSets.size)
      have hmem : i ∈ List.range pointSets.size := hp.mem_iff.mp hi
      rw [List.mem_range] at hmem
      rw [List.size_toArray]
      omega
    rw [AlgebraWidths.filterMap_getElem?_length
      (order := MultiPrepare.sortById (fun i => ((pointSets.getD i #[]).size, i))
        (List.range pointSets.size)) (xs := qes'.toArray) hidx]
    exact horder_len
  · obtain ⟨_, hthrow, _⟩ := AlgebraWidths.except_bind_ok h1
    exact (AlgebraWidths.throw_ok_false _ hthrow).elim

end MultiPrepareWidths

open AlgebraWidths

/-! ## 2. `for`-loop closure for `PresWidthSeq`

    `PresWidths.listForIn` (TranscriptLog.lean) carries only the width-class
    invariant; the exact sequence needs the control-flow fact that the loop body
    never returns `.done`. The cons equation of `List.forIn` is definitional, so
    a `.yield`-only step lets the appended list be exactly the flatten of the
    per-iteration widths. -/

/-- A bind whose continuation always returns `.yield` when it returns at all. -/
theorem forIn_step_yield {α β : Type} {m : TranscriptM α}
    {g : α → TranscriptM (ForInStep β)}
    (hg : ∀ a t r t', g a t = .ok (r, t') → ∃ b, r = .yield b) :
    ∀ t r t', (m >>= g) t = .ok (r, t') → ∃ b, r = .yield b := by
  intro t r t' h
  have h2 : m t >>= (fun xr : α × Transcript => g xr.1 xr.2) = .ok (r, t') := h
  cases hm : m t with
  | error e =>
      rw [hm] at h2
      cases h2
  | ok xr =>
      obtain ⟨a, t1⟩ := xr
      rw [hm] at h2
      change g a t1 = .ok (r, t') at h2
      exact hg a t1 r t' h2

/-- The terminal `pure (.yield b)` step. -/
theorem forIn_pure_yield {β : Type} (b : β) :
    ∀ t r t',
      ((StateT.pure (ForInStep.yield b) : TranscriptM (ForInStep β)) t = .ok (r, t')) →
        ∃ b', r = .yield b' := by
  intro t r t' h
  change (.ok (ForInStep.yield b, t) : Except Fault (ForInStep β × Transcript)) =
      .ok (r, t') at h
  cases h
  exact ⟨b, rfl⟩

/-- A `throw` appends nothing (it has no successful run). -/
theorem throwFault {α : Type} (f : Fault) :
    PresWidthSeq [] (MonadExcept.throw f : TranscriptM α) :=
  PresWidthSeq.lift (Except.error f)

/-- The exact width sequence of a `for`-loop whose body always yields. -/
theorem listForIn {α β : Type} (l : List α) (init : β)
    {f : α → β → TranscriptM (ForInStep β)} (wf : α → List Nat)
    (hf : ∀ x b, PresWidthSeq (wf x) (f x b))
    (hy : ∀ x b t r t', f x b t = .ok (r, t') → ∃ b', r = .yield b') :
    PresWidthSeq ((l.map wf).flatten) (forIn l init f) := by
  induction l generalizing init with
  | nil => exact PresWidthSeq.pure _
  | cons a as ih =>
      intro t t' r hrun
      rw [List.forIn_cons] at hrun
      change (f a init t >>= (fun p : ForInStep β × Transcript =>
          (match p.1 with
            | .done b => (StateT.pure b : TranscriptM β)
            | .yield b => forIn as b f) p.2)) = .ok (r, t') at hrun
      cases hstep : f a init t with
      | error e =>
          simp only [hstep] at hrun
          cases hrun
      | ok p =>
          obtain ⟨s, t1⟩ := p
          simp only [hstep] at hrun
          cases s with
          | done b =>
              obtain ⟨b', hb⟩ := hy a init t (.done b) t1 hstep
              cases hb
          | yield b =>
              change (forIn as b f) t1 = .ok (r, t') at hrun
              have hw1 := hf a init t t1 (.yield b) hstep
              have hw2 := ih b t1 t' r hrun
              rw [hw2, hw1, List.append_assoc]
              simp only [List.map_cons, List.flatten_cons]

/-- `replicate (n + 3)` in the block order the logup evaluator reads. -/
theorem replicate_add_three (n w : Nat) :
    List.replicate (n + 3) w = [w] ++ (List.replicate n w ++ ([w] ++ [w])) := by
  change List.replicate (n + 3) w =
    List.replicate 1 w ++ (List.replicate n w ++ (List.replicate 1 w ++ List.replicate 1 w))
  rw [← List.append_assoc]
  rw [List.replicate_append_replicate]
  rw [List.replicate_append_replicate]
  rw [List.replicate_append_replicate]
  congr 1
  omega

/-- `Permutation.VerifyingKey.evaluate` reads one `fr` per VK commitment. -/
theorem permVKevaluate {G₁ : Type} (vk : Permutation.VerifyingKey G₁) :
    PresWidthSeq (List.replicate vk.commitments.size (hashableFr (p := p)).width)
      (Permutation.VerifyingKey.evaluate (p := p) vk) := by
  have hmain : PresWidthSeq
      (List.replicate vk.commitments.size (hashableFr (p := p)).width ++ [])
      (Permutation.VerifyingKey.evaluate (p := p) vk) := by
    unfold Permutation.VerifyingKey.evaluate
    refine PresWidthSeq.bind
      (ws1 := List.replicate vk.commitments.size (hashableFr (p := p)).width)
      (PresWidthSeq.readN (hashableFr (p := p)) vk.commitments.size) (fun _ => ?_)
    exact PresWidthSeq.pure _
  simpa using hmain

/-- `Logup.Committed.evaluate` reads `m`, the `nbChunks` helpers, `Z(x)` and
    `Z(ωx)`: exactly `nbChunks + 3` scalars. -/
theorem logupEvaluate {G₁ : Type} (coms : Logup.Committed G₁) :
    PresWidthSeq (List.replicate (coms.helperPolys.size + 3) (hashableFr (p := p)).width)
      (Logup.Committed.evaluate (p := p) coms) := by
  rw [replicate_add_three]
  unfold Logup.Committed.evaluate
  refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
    (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
  refine PresWidthSeq.bind (ws1 := List.replicate coms.helperPolys.size
    (hashableFr (p := p)).width)
    (PresWidthSeq.readN (hashableFr (p := p)) coms.helperPolys.size) (fun _ => ?_)
  refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
    (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
  refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
    (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
  exact PresWidthSeq.pure _

/-- `Trash.Committed.evaluate` reads exactly one scalar. -/
theorem trashEvaluate {G₁ : Type} (coms : Trash.Committed G₁) :
    PresWidthSeq (List.replicate 1 (hashableFr (p := p)).width)
      (Trash.Committed.evaluate (p := p) coms) := by
  unfold Trash.Committed.evaluate
  refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
    (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
  exact PresWidthSeq.pure _

/-- `Permutation.Committed.evaluate` reads two evals per product set plus a third
    for every set but the last: `3k - 1` scalars (`0` when `k = 0`, which Nat's
    truncated subtraction gives for free). -/
theorem permCommittedEvaluate {G₁ : Type} (coms : Permutation.Committed G₁) :
    PresWidthSeq
      (List.replicate (3 * coms.permutationProductCommitments.size - 1)
        (hashableFr (p := p)).width)
      (Permutation.Committed.evaluate (p := p) coms) := by
  have hmain : PresWidthSeq
      (List.replicate (3 * coms.permutationProductCommitments.size - 1)
        (hashableFr (p := p)).width ++ [])
      (Permutation.Committed.evaluate (p := p) coms) := by
    unfold Permutation.Committed.evaluate
    dsimp only
    rw [← range_width_map (w := (hashableFr (p := p)).width)
      (k := coms.permutationProductCommitments.size)]
    refine PresWidthSeq.bind
      (ws1 := ((List.range coms.permutationProductCommitments.size).map
        (fun i => if i < coms.permutationProductCommitments.size - 1
          then [(hashableFr (p := p)).width, (hashableFr (p := p)).width,
            (hashableFr (p := p)).width]
          else [(hashableFr (p := p)).width, (hashableFr (p := p)).width])).flatten)
      ?_ (fun _ => ?_)
    · refine PresWidthSeq.listForIn (List.range coms.permutationProductCommitments.size)
        (#[] : Array (Permutation.SetEvaluated (Fr p)))
        (fun i => if i < coms.permutationProductCommitments.size - 1
          then [(hashableFr (p := p)).width, (hashableFr (p := p)).width,
            (hashableFr (p := p)).width]
          else [(hashableFr (p := p)).width, (hashableFr (p := p)).width]) ?_ ?_
      · intro i s
        by_cases hi : i < coms.permutationProductCommitments.size - 1
        · rw [if_pos hi]
          refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
            (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
          refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
            (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
          rw [if_pos hi]
          refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
            (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
          refine PresWidthSeq.bind (ws1 := [])
            (PresWidthSeq.pure (some _)) (fun _ => ?_)
          exact PresWidthSeq.pure _
        · rw [if_neg hi]
          refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
            (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
          refine PresWidthSeq.bind (ws1 := [(hashableFr (p := p)).width])
            (PresWidthSeq.read (hashableFr (p := p))) (fun _ => ?_)
          rw [if_neg hi]
          refine PresWidthSeq.bind (ws1 := [])
            (PresWidthSeq.pure (none : Option (Fr p))) (fun _ => ?_)
          exact PresWidthSeq.pure _
      · intro i s t r t' h
        refine PresWidthSeq.forIn_step_yield
          (m := tmRead (hashableFr (p := p))) ?_ t r t' h
        intro a t1 r1 t1' h1
        refine PresWidthSeq.forIn_step_yield
          (m := tmRead (hashableFr (p := p))) ?_ t1 r1 t1' h1
        intro b t2 r2 t2' h2
        by_cases hi : i < coms.permutationProductCommitments.size - 1
        · rw [if_pos hi] at h2
          refine PresWidthSeq.forIn_step_yield
            (m := tmRead (hashableFr (p := p))) ?_ t2 r2 t2' h2
          intro e t3 r3 t3' h3
          refine PresWidthSeq.forIn_step_yield
            (m := (StateT.pure (some e) : TranscriptM (Option (Fr p)))) ?_ t3 r3 t3' h3
          intro last t4 r4 t4' h4
          exact PresWidthSeq.forIn_pure_yield _ t4 r4 t4' h4
        · rw [if_neg hi] at h2
          refine PresWidthSeq.forIn_step_yield
            (m := (StateT.pure none : TranscriptM (Option (Fr p)))) ?_ t2 r2 t2' h2
          intro last t3 r3 t3' h3
          exact PresWidthSeq.forIn_pure_yield _ t3 r3 t3' h3
    · exact PresWidthSeq.pure _
  simpa using hmain

/-- `Verifier.readFixedEvals` reads `numFixedColumns - numSimpleSelectors`
    scalars on its success path; the R-14 insert back-fill is `StateT.lift`, and
    the oversized-selector guard throws before any read. -/
theorem readFixedEvals (cs : ConstraintSystem (Fr p)) :
    PresWidthSeq
      (List.replicate (cs.numFixedColumns - cs.numSimpleSelectors)
        (hashableFr (p := p)).width)
      (Verifier.readFixedEvals (p := p) cs) := by
  have hmain : PresWidthSeq
      (List.replicate (cs.numFixedColumns - cs.numSimpleSelectors)
        (hashableFr (p := p)).width ++ [])
      (Verifier.readFixedEvals (p := p) cs) := by
    unfold Verifier.readFixedEvals
    dsimp only
    split
    · intro t t' a hrun
      change (Except.error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) :
        Except Fault (Array (Fr p) × Transcript)) = .ok (a, t') at hrun
      cases hrun
    · refine PresWidthSeq.bind
        (ws1 := List.replicate (cs.numFixedColumns - cs.numSimpleSelectors)
          (hashableFr (p := p)).width)
        (PresWidthSeq.readN (hashableFr (p := p))
          (cs.numFixedColumns - cs.numSimpleSelectors)) (fun read => ?_)
      refine PresWidthSeq.bind (ws1 := []) ?_ (fun out => ?_)
      · have hfold := PresWidthSeq.listFoldlM
          (f := fun acc step => if cs.hasSimpleSelectorCol step.2.1.index then
            StateT.lift (Verifier.listInsertAt acc step.1 1
              "proofs/src/plonk/verifier.rs:410")
            else Pure.pure acc)
          (wf := fun _ => [])
          (fun acc step => by
            split
            · exact PresWidthSeq.lift _
            · exact PresWidthSeq.pure _)
          (List.zip (List.range cs.fixedQueries.size) cs.fixedQueries.toList)
          (read.toList : List (Fr p))
        simpa [AlgebraWidths.flatten_map_nil] using hfold
      · exact PresWidthSeq.pure _
  simpa using hmain

/-- **`readAlgebra` width sequence.** The quotient commitments (`1` under the
    outer single-h-commitment feature, `getQuotientPolyDegree` otherwise) are
    `g1`s; the scalar evaluations are exactly:

    * one `fr` per (instance row, instance query) pair whose query is committed
      (`q.1.index < nbCommitted`), the rest being inner products;
    * `adviceQueries.size` per proof;
    * `numFixedColumns - numSimpleSelectors` fixed evals;
    * `commitments.size` permutation-common evals;
    * `3k - 1` per permutation product set of size `k`;
    * `helperPolys.size + 3` per lookup;
    * one per trashcan. -/
theorem readAlgebra {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    PresWidthSeq
      (List.replicate
          (if feat.outerSingleHCommitment then 1 else vk.domain.getQuotientPolyDegree)
          (hashableG1 g1).width
        ++ List.replicate
            (instances.size *
                (vk.cs.instanceQueries.toList.filter
                  (fun q => q.1.index < nbCommitted)).length
              + numProofs * vk.cs.adviceQueries.size
              + (vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
              + vk.permutation.commitments.size
              + (permutations.toList.map
                  (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum
              + (lookups.toList.map
                  (fun row => (row.toList.map
                    (fun l => l.helperPolys.size + 3)).sum)).sum
              + (trashcans.toList.map (fun row => row.size)).sum)
            (hashableFr (p := p)).width)
      (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
        nbCommitted numProofs instances) := by
  rw [AlgebraWidths.combine_widths]
  unfold Verifier.readAlgebra
  refine PresWidthSeq.bind (PresWidthSeq.readN (hashableG1 g1) _) (fun _ => ?_)
  refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.squeezeChallenge (p := p))
    (fun _ => ?_)
  refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift (Verifier.i32Abs _ _))
    (fun _ => ?_)
  -- instances
  refine PresWidthSeq.bind ?_ (fun _ => ?_)
  · rw [show List.replicate
        (instances.size *
          (vk.cs.instanceQueries.toList.filter
            (fun q => q.1.index < nbCommitted)).length)
        (hashableFr (p := p)).width
        = (instances.toList.map (fun _ => List.replicate
            (vk.cs.instanceQueries.toList.filter
              (fun q => q.1.index < nbCommitted)).length
            (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate_const, ← Array.length_toList]]
    refine PresWidthSeq.listMapM instances.toList (wf := fun _ => List.replicate
      (vk.cs.instanceQueries.toList.filter
        (fun q => q.1.index < nbCommitted)).length
      (hashableFr (p := p)).width) ?_
    intro row
    rw [show List.replicate
        (vk.cs.instanceQueries.toList.filter
          (fun q => q.1.index < nbCommitted)).length
        (hashableFr (p := p)).width
        = (vk.cs.instanceQueries.toList.map
            (fun q => if q.1.index < nbCommitted
              then [(hashableFr (p := p)).width] else [])).flatten by
      rw [AlgebraWidths.flatten_map_ite]]
    refine PresWidthSeq.listMapM vk.cs.instanceQueries.toList
      (wf := fun q => if q.1.index < nbCommitted
        then [(hashableFr (p := p)).width] else []) ?_
    intro q
    dsimp only
    by_cases hq : q.1.index < nbCommitted
    · simp only [if_pos hq]
      exact PresWidthSeq.read (hashableFr (p := p))
    · simp only [if_neg hq]
      cases hcol : row[q.1.index - nbCommitted]? with
      | none => exact PresWidthSeq.throwFault _
      | some col =>
          dsimp only
          refine PresWidthSeq.ite ?_ ?_
          all_goals first
            | exact PresWidthSeq.lift _
            | refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.throwFault _)
                (fun _ => PresWidthSeq.lift _)
  -- advice
  refine PresWidthSeq.bind ?_ (fun _ => ?_)
  · rw [show List.replicate (numProofs * vk.cs.adviceQueries.size)
        (hashableFr (p := p)).width
        = ((List.range numProofs).map (fun _ => List.replicate
            vk.cs.adviceQueries.size (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate_const, List.length_range]]
    refine PresWidthSeq.listMapM (List.range numProofs)
      (wf := fun _ => List.replicate vk.cs.adviceQueries.size
        (hashableFr (p := p)).width) ?_
    intro _
    exact PresWidthSeq.readN (hashableFr (p := p)) vk.cs.adviceQueries.size
  -- fixed evals
  refine PresWidthSeq.bind (PresWidthSeq.readFixedEvals vk.cs) (fun _ => ?_)
  -- permutation common
  refine PresWidthSeq.bind (PresWidthSeq.permVKevaluate vk.permutation) (fun _ => ?_)
  -- permutation products
  refine PresWidthSeq.bind ?_ (fun _ => ?_)
  · rw [show List.replicate
        ((permutations.toList.map
          (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum)
        (hashableFr (p := p)).width
        = (permutations.toList.map (fun pc => List.replicate
            (3 * pc.permutationProductCommitments.size - 1)
            (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate]]
    refine PresWidthSeq.listMapM permutations.toList
      (wf := fun pc => List.replicate
        (3 * pc.permutationProductCommitments.size - 1)
        (hashableFr (p := p)).width) ?_
    intro pc
    exact PresWidthSeq.permCommittedEvaluate pc
  -- lookups
  refine PresWidthSeq.bind ?_ (fun _ => ?_)
  · rw [show List.replicate
        ((lookups.toList.map
          (fun row => (row.toList.map
            (fun l => l.helperPolys.size + 3)).sum)).sum)
        (hashableFr (p := p)).width
        = (lookups.toList.map (fun row => List.replicate
            ((row.toList.map (fun l => l.helperPolys.size + 3)).sum)
            (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate]]
    refine PresWidthSeq.listMapM lookups.toList
      (wf := fun row => List.replicate
        ((row.toList.map (fun l => l.helperPolys.size + 3)).sum)
        (hashableFr (p := p)).width) ?_
    intro row
    rw [show List.replicate
        ((row.toList.map (fun l => l.helperPolys.size + 3)).sum)
        (hashableFr (p := p)).width
        = (row.toList.map (fun l => List.replicate
            (l.helperPolys.size + 3) (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate]]
    refine PresWidthSeq.listMapM row.toList
      (wf := fun l => List.replicate (l.helperPolys.size + 3)
        (hashableFr (p := p)).width) ?_
    intro l
    exact PresWidthSeq.logupEvaluate l
  -- trashcans
  refine PresWidthSeq.bind ?_ (fun _ => ?_)
  · rw [show List.replicate
        ((trashcans.toList.map (fun row => row.size)).sum)
        (hashableFr (p := p)).width
        = (trashcans.toList.map (fun row => List.replicate row.size
            (hashableFr (p := p)).width)).flatten by
      rw [AlgebraWidths.flatten_map_replicate]]
    refine PresWidthSeq.listMapM trashcans.toList
      (wf := fun row => List.replicate row.size (hashableFr (p := p)).width) ?_
    intro row
    rw [show List.replicate row.size (hashableFr (p := p)).width
        = (row.toList.map (fun _ => [(hashableFr (p := p)).width])).flatten by
      rw [AlgebraWidths.flatten_map_single, Array.length_toList]]
    refine PresWidthSeq.listMapM row.toList
      (wf := fun _ => [(hashableFr (p := p)).width]) ?_
    intro t
    exact PresWidthSeq.trashEvaluate t
  -- the `AlgebraRead` record
  exact PresWidthSeq.pure _

end PresWidthSeq

namespace PresWidthSeq

/-! ## 3. `multiPrepare`: the three `kzg/mod.rs` phases

    `phaseA` (dummy queries + two challenges + the intermediate-set build)
    reads nothing when the fewer-point-sets branch is off; `phaseB` reads one
    `g1` and one `fr` per q-eval set; `phaseC` reads one `g1`. The q-eval-set
    count is `a.qEvalSets.size`, linked below to `constructIntermediateSets`'
    point-set count. -/

section MultiPrepareWidths

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- `phaseA` reads nothing when the dummy-query feature is off. -/
theorem phaseA_noDummies (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁))
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime)) :
    PresWidthSeq [] (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
      fewerPointSetsRuntime queries) := by
  unfold phaseA
  dsimp only
  split
  · rename_i hd
    exact absurd hd hNoDummies
  · refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.pure queries) (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.squeezeChallenge (p := p))
      (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.squeezeChallenge (p := p))
      (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun _ => ?_)
    exact PresWidthSeq.pure _

/-- `phaseB` reads the `f_com` point, then one scalar per q-eval set. -/
theorem phaseB_width (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) :
    PresWidthSeq ([(hashableG1 g1).width] ++
      List.replicate a.qEvalSets.size (hashableFr (p := p)).width)
      (phaseB g1 fc feat a) := by
  have hmain : PresWidthSeq
      ([(hashableG1 g1).width] ++
        (List.replicate a.qEvalSets.size (hashableFr (p := p)).width ++ []))
      (phaseB g1 fc feat a) := by
    unfold phaseB
    dsimp only
    refine PresWidthSeq.bind (ws1 := [(hashableG1 g1).width])
      (PresWidthSeq.read (hashableG1 g1)) (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.squeezeChallenge (p := p))
      (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := List.replicate a.qEvalSets.size
      (hashableFr (p := p)).width) ?_ (fun _ => ?_)
    · rw [show List.replicate a.qEvalSets.size (hashableFr (p := p)).width
          = ((List.range a.qEvalSets.size).map (fun _ => List.replicate 1
              (hashableFr (p := p)).width)).flatten by
        rw [AlgebraWidths.flatten_map_replicate_const, List.length_range, Nat.mul_one]]
      refine PresWidthSeq.listMapM (List.range a.qEvalSets.size)
        (wf := fun _ => [(hashableFr (p := p)).width]) ?_
      intro _
      exact PresWidthSeq.read (hashableFr (p := p))
    · refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun _ => ?_)
      exact PresWidthSeq.pure _
  simpa [List.append_nil] using hmain

/-- `phaseC` reads the `π` point and nothing else. -/
theorem phaseC_width (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (a : MultiPrepare.PhaseA (Fr p) G₁) (b : MultiPrepare.PhaseB (Fr p) G₁) :
    PresWidthSeq ([(hashableG1 g1).width])
      (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
  have hmain : PresWidthSeq ([(hashableG1 g1).width] ++ [])
      (phaseC (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat a b) := by
    unfold phaseC
    dsimp only
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.squeezeChallenge (p := p))
      (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun _ => ?_)
    refine PresWidthSeq.bind (ws1 := [(hashableG1 g1).width])
      (PresWidthSeq.read (hashableG1 g1)) (fun _ => ?_)
    exact PresWidthSeq.pure _
  simpa using hmain

/-- The `ok`-projection of a `TranscriptM` bind. -/
theorem run_bind_ok {α β : Type} {m : TranscriptM α} {f : α → TranscriptM β}
    {t : Transcript} {b : β} {t' : Transcript}
    (h : (m >>= f).run t = .ok (b, t')) :
    ∃ a t1, m.run t = .ok (a, t1) ∧ f a t1 = .ok (b, t') := by
  have h2 : m.run t >>= (fun p : α × Transcript => (f p.1).run p.2) = .ok (b, t') := h
  cases hm : m.run t with
  | error e =>
      simp only [hm] at h2
      cases h2
  | ok p =>
      obtain ⟨a, t1⟩ := p
      refine ⟨a, t1, rfl, ?_⟩
      simp only [hm] at h2
      change (f a).run t1 = .ok (b, t') at h2
      exact h2

/-- `a.qEvalSets.size` is the `constructIntermediateSets` point-set count. -/
theorem phaseA_qEvalSets_size (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁))
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p)))
    (hCI : constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries = .ok (cm, pointSets))
    {t : Transcript} {a : MultiPrepare.PhaseA (Fr p) G₁} {t' : Transcript}
    (hA : (phaseA (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries).run t
      = .ok (a, t')) :
    a.qEvalSets.size = pointSets.size := by
  unfold phaseA at hA
  dsimp only at hA
  rw [if_neg hNoDummies] at hA
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_lift] at hA
  obtain ⟨p1, hp1, h1⟩ := AlgebraWidths.except_bind_ok hA
  cases hp1
  dsimp only at h1
  obtain ⟨p2, _, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨p3, _, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨p4, hp4, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨p5, hp5, h5⟩ := AlgebraWidths.except_bind_ok h4
  cases h5
  obtain ⟨cp, hcp, hp4'⟩ := AlgebraWidths.except_bind_ok hp4
  cases hp4'
  obtain ⟨pq, hBQ, hp5'⟩ := AlgebraWidths.except_bind_ok hp5
  cases hp5'
  have hcpEq : cp = (cm, pointSets) := by
    rw [hCI] at hcp
    cases hcp
    rfl
  rw [hcpEq] at hBQ
  have := PresWidthSeq.buildQ_qEvalSets_size (G₂ := G₂) (Gₜ := Gₜ) feat fc _ cm pointSets pq hBQ
  simpa using this

/-- **`multiPrepare` width sequence.** With the fewer-point-sets branch off,
    `multiPrepare` appends `[g1]`, one scalar per q-eval set, then `[g1]`. The
    q-eval-set count is `pointSets.size` from `constructIntermediateSets`, by
    `phaseA_qEvalSets_size` + `buildQ_qEvalSets_size`. -/
theorem multiPrepare_width (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁))
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p)))
    (hCI : constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries = .ok (cm, pointSets)) :
    PresWidthSeq ([(hashableG1 g1).width] ++
      List.replicate pointSets.size (hashableFr (p := p)).width ++
      [(hashableG1 g1).width])
      (multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime queries) := by
  intro t c t' hrun
  unfold multiPrepare at hrun
  obtain ⟨a, ta, hA, h1⟩ := PresWidthSeq.run_bind_ok hrun
  have hAw : ta.log.toList.map (fun r => r.1) =
      t.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.phaseA_noDummies g1 fc feat fewerPointSetsRuntime queries hNoDummies t ta a hA
  obtain ⟨b, tb, hB, h2⟩ := PresWidthSeq.run_bind_ok h1
  have hBw : tb.log.toList.map (fun r => r.1) =
      ta.log.toList.map (fun r => r.1) ++ ([(hashableG1 g1).width] ++
        List.replicate a.qEvalSets.size (hashableFr (p := p)).width) :=
    PresWidthSeq.phaseB_width g1 fc feat a ta tb b hB
  obtain ⟨c', tc, hC, h3⟩ := PresWidthSeq.run_bind_ok h2
  have hCw : tc.log.toList.map (fun r => r.1) =
      tb.log.toList.map (fun r => r.1) ++ [(hashableG1 g1).width] :=
    PresWidthSeq.phaseC_width g1 fc feat a b tb tc c' hC
  cases h3
  have hsize : a.qEvalSets.size = pointSets.size :=
    PresWidthSeq.phaseA_qEvalSets_size g1 fc feat fewerPointSetsRuntime queries hNoDummies
      cm pointSets hCI hA
  rw [hsize] at hBw
  rw [hCw, hBw, hAw]
  simp only [List.append_nil]
  rw [List.append_assoc]

end MultiPrepareWidths

end PresWidthSeq



/-! ## 5. The `PrepareLogSlots` composition

    The three read blocks of `prepare` are:

      parseTrace        : the commitment prefix (A6's phase schedule / counts)
      readAlgebra       : quotient commitments, then the scalar evals  (PROVED)
      multiPrepare      : `[g1]`, the point-set scalars, `[g1]`        (PROVED,
                          with the point-set count as the KZG residual)

    `readAlgebraWidths` names the first block's exact list; the composition
    below shows the readAlgebra and multiPrepare blocks add without loss. The
    `parseTrace` slot and the KZG point-set-count identification
    (`qEvalSetCount = plan.numPointSets`, which needs the challenge-nonzero pin
    that `kzgPartitionBridge_false_at_x0` shows is missing) are the exact
    residuals left as named props. -/

/-- The exact width list `readAlgebra` appends, as a reusable function. -/
def readAlgebraWidths {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) : List Nat :=
  List.replicate
      (if feat.outerSingleHCommitment then 1 else vk.domain.getQuotientPolyDegree)
      (hashableG1 g1).width
    ++ List.replicate
        (instances.size *
            (vk.cs.instanceQueries.toList.filter
              (fun q => q.1.index < nbCommitted)).length
          + numProofs * vk.cs.adviceQueries.size
          + (vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
          + vk.permutation.commitments.size
          + (permutations.toList.map
              (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum
          + (lookups.toList.map
              (fun row => (row.toList.map
                (fun l => l.helperPolys.size + 3)).sum)).sum
          + (trashcans.toList.map (fun row => row.size)).sum)
        (hashableFr (p := p)).width

theorem PresWidthSeq.readAlgebra_widths {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    PresWidthSeq
      (readAlgebraWidths g1 feat vk permutations lookups trashcans
        nbCommitted numProofs instances)
      (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
        nbCommitted numProofs instances) := by
  unfold readAlgebraWidths
  exact PresWidthSeq.readAlgebra g1 feat vk permutations lookups trashcans
    nbCommitted numProofs instances

/-- **The exact KZG residual.** Every `multiPrepare` call appends `[g1]`, `n`
    scalars, `[g1]`. `n` is the protocol's `numPointSets`; the point-set count
    is data-dependent (it collapses at x = 0, see
    `LoweringV3.kzgPartitionBridge_false_at_x0`), so this is the KZG
    partition-bridge / challenge-pin obligation, not a width fact of the code. -/
def MultiPrepareBlockWidth {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat) : Prop :=
  ∀ (queries : Array (VerifierQuery (Fr p) G₁)),
    PresWidthSeq
      ([(hashableG1 g1).width] ++ List.replicate n (hashableFr (p := p)).width ++
        [(hashableG1 g1).width])
      (pcs.multiPrepare queries)

/-- **The residual for A6's `parseTrace` schedule.** `parseTrace` appends one
    `g1` per non-quotient commitment, in the phase-interleaved order of
    `parse_trace`; this is the exact statement the A6 lane owes. It is not a
    hypothesis of any row, bundle or root. -/
def ParseTraceWidths {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed : Array (Array G₁)) (inst : Array (Array (Array (Fr p))))
    (nCommit : Nat) : Prop :=
  PresWidthSeq (List.replicate nCommit (hashableG1 E.g1).width)
    (parseTrace E.g1 F vk committed inst)

/-- **The KZG point-set-count identification.** The verifier's q-eval-set count
    (the `constructIntermediateSets` point-set count on the queries
    `linearize` produced) is the protocol's `numPointSets`. Stated here as a
    run-level counter equality; the oracle falsifier at x = 0 shows an
    unconditional version is false. -/
def QEvalSetCountMatches {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat) : Prop :=
  MultiPrepareBlockWidth g1 pcs n

/-- `StateT.get`'s run. -/
theorem StateT_get_run (s : Transcript) :
    (StateT.get : TranscriptM Transcript).run s = .ok (s, s) := rfl

/-- `run` distributes over a propositional `if`. -/
theorem run_ite {α : Type} (c : Prop) [Decidable c] (a b : TranscriptM α) (s : Transcript) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  by_cases h : c <;> simp [h]

/-- `PresWidthSeq` is invariant under equality of the width list. -/
theorem PresWidthSeq.congr_width {α : Type} {m : TranscriptM α} {ws ws' : List Nat}
    (h : PresWidthSeq ws m) (hw : ws = ws') : PresWidthSeq ws' m := by
  rw [← hw]
  exact h

/-- `PresWidthSeq` of the exact `StateT.get` / `match m.run` / `StateT.set`
    dance of `verifyAlgebraicConstraints` is `m`'s width: the ok arm sets the
    state and returns, the error arms throw. -/
theorem rerun {α : Type} {m : TranscriptM α} {ws : List Nat} (hm : PresWidthSeq ws m) :
    PresWidthSeq ws
      (StateT.get >>= fun (t : Transcript) =>
        match m.run t with
        | .ok (a, t2) => (do StateT.set t2; (pure a : TranscriptM α))
        | .error (Fault.panic site) => throw (Fault.panic site)
        | .error (Fault.error e) => throw (Fault.error Error.opening)) := by
  intro s s' b h
  rw [StateT.run_bind, StateT_get_run] at h
  change StateT.run (match m.run s with
      | .ok (a, t2) => (do StateT.set t2; (pure a : TranscriptM α))
      | .error (Fault.panic site) => throw (Fault.panic site)
      | .error (Fault.error e) => throw (Fault.error Error.opening)) s = .ok (b, s') at h
  cases hmr : m.run s with
  | error e =>
      cases e with
      | panic site =>
          simp only [hmr] at h
          change (Except.error (Fault.panic site) : Except Fault (α × Transcript)) =
            .ok (b, s') at h
          cases h
      | error e2 =>
          simp only [hmr] at h
          change (Except.error (Fault.error Error.opening) : Except Fault (α × Transcript)) =
            .ok (b, s') at h
          cases h
  | ok p =>
      obtain ⟨a0, t2⟩ := p
      simp only [hmr] at h
      have hh : (a0, t2) = (b, s') := Except.ok.inj h
      have hw := hm s t2 a0 hmr
      cases hh
      exact hw

section Composition

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **The two proved halves compose.** `readAlgebra`'s exact widths plus the
    `linearize` lift (no reads) plus the multiPrepare block (`[g1]`, `n`
    scalars, `[g1]`). This is the algebraic half of `prepare` with the KZG
    point-set count supplied by the residual `MultiPrepareBlockWidth`. -/
theorem readAlgebra_multiPrepare_widths (g1 : G1Codec G₁) (feat : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p))))
    (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat)
    (hMulti : MultiPrepareBlockWidth g1 pcs n)
    (lin : Verifier.AlgebraRead (Fr p) G₁ → Except Fault (Array (VerifierQuery (Fr p) G₁))) :
    PresWidthSeq
      (readAlgebraWidths g1 feat vk permutations lookups trashcans
        nbCommitted numProofs instances
        ++ ([(hashableG1 g1).width] ++
          List.replicate n (hashableFr (p := p)).width ++
          [(hashableG1 g1).width]))
      (Verifier.readAlgebra (p := p) g1 feat vk permutations lookups trashcans
        nbCommitted numProofs instances >>= fun alg =>
        StateT.lift (lin alg) >>= fun queries => pcs.multiPrepare queries) := by
  refine PresWidthSeq.bind (ws1 := readAlgebraWidths g1 feat vk permutations lookups
    trashcans nbCommitted numProofs instances)
    (PresWidthSeq.readAlgebra_widths g1 feat vk permutations lookups trashcans
      nbCommitted numProofs instances) (fun alg => ?_)
  refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift (lin alg))
    (fun queries => ?_)
  exact hMulti queries

/-- **The `verifyAlgebraicConstraints` run glue.** `readAlgebra`'s exact
    widths, the width-free `linearize` lift, and the `multiPrepare` block (via
    `MultiPrepareBlockWidth`), with the `committed.isEmpty` guard and the
    `StateT.get`/`match`/`StateT.set` re-run dance discharged. -/
theorem verifyAlgebraicConstraints_width (g1 : G1Codec G₁) (delta : Fr p)
    (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁)) (instances : Array (Array (Array (Fr p))))
    (n : Nat) (hMulti : MultiPrepareBlockWidth g1 pcs n)
    (hCommit : feat.committedInstances = true) :
    PresWidthSeq
      (readAlgebraWidths g1 feat vk trace.permutations trace.lookups trace.trashcans
          ((Option.map (fun r => r.size)
            (if feat.committedInstances then committedInstances
             else arrayReplicate instances.size (#[] : Array G₁))[0]?).getD 0)
          instances.size instances
        ++ ([(hashableG1 g1).width] ++
          List.replicate n (hashableFr (p := p)).width ++
          [(hashableG1 g1).width]))
      (Verifier.verifyAlgebraicConstraints (p := p) g1 delta feat pcs vk trace
        committedInstances instances) := by
  unfold Verifier.verifyAlgebraicConstraints
  dsimp only
  simp only [hCommit]
  refine PresWidthSeq.ite ?_ ?_
  · refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.throwFault _) (fun _ => ?_)
    refine PresWidthSeq.bind
      (ws1 := readAlgebraWidths g1 feat vk trace.permutations trace.lookups trace.trashcans
        _ instances.size instances)
      (PresWidthSeq.readAlgebra_widths g1 feat vk trace.permutations trace.lookups
        trace.trashcans _ instances.size instances) (fun alg => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun queries => ?_)
    intro t2 t' d hd
    rw [StateT.run_bind, StateT_get_run] at hd
    change StateT.run (match (pcs.multiPrepare queries).run t2 with
        | .ok (guard, t3) => (do StateT.set t3; (pure guard : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)))
        | .error (Fault.panic site) => throw (Fault.panic site)
        | .error (Fault.error e) => throw (Fault.error Error.opening)) t2 = .ok (d, t') at hd
    cases hmr : (pcs.multiPrepare queries).run t2 with
    | error e =>
        cases e with
        | panic site =>
            simp only [hmr] at hd
            change (Except.error (Fault.panic site) :
              Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) = .ok (d, t') at hd
            cases hd
        | error e2 =>
            simp only [hmr] at hd
            change (Except.error (Fault.error Error.opening) :
              Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) = .ok (d, t') at hd
            cases hd
    | ok p =>
        obtain ⟨a0, t3⟩ := p
        simp only [hmr] at hd
        have hh : (a0, t3) = (d, t') := Except.ok.inj hd
        have hw := hMulti queries t2 t3 a0 hmr
        cases hh
        simpa using hw
  · refine PresWidthSeq.bind
      (ws1 := readAlgebraWidths g1 feat vk trace.permutations trace.lookups trace.trashcans
        _ instances.size instances)
      (PresWidthSeq.readAlgebra_widths g1 feat vk trace.permutations trace.lookups
        trace.trashcans _ instances.size instances) (fun alg => ?_)
    refine PresWidthSeq.bind (ws1 := []) (PresWidthSeq.lift _) (fun queries => ?_)
    intro t2 t' d hd
    rw [StateT.run_bind, StateT_get_run] at hd
    change StateT.run (match (pcs.multiPrepare queries).run t2 with
        | .ok (guard, t3) => (do StateT.set t3; (pure guard : TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ)))
        | .error (Fault.panic site) => throw (Fault.panic site)
        | .error (Fault.error e) => throw (Fault.error Error.opening)) t2 = .ok (d, t') at hd
    cases hmr : (pcs.multiPrepare queries).run t2 with
    | error e =>
        cases e with
        | panic site =>
            simp only [hmr] at hd
            change (Except.error (Fault.panic site) :
              Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) = .ok (d, t') at hd
            cases hd
        | error e2 =>
            simp only [hmr] at hd
            change (Except.error (Fault.error Error.opening) :
              Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) = .ok (d, t') at hd
            cases hd
    | ok p =>
        obtain ⟨a0, t3⟩ := p
        simp only [hmr] at hd
        have hh : (a0, t3) = (d, t') := Except.ok.inj hd
        have hw := hMulti queries t2 t3 a0 hmr
        cases hh
        simpa using hw

/-- The plan-slot identity: once the three protocol counts match the three block
    counts (`prefixG1Count = nonQuotient + nbQuotient`, `numEvals = evalCount`,
    `numPointSets = n`), the concatenated block widths are exactly `slots`. -/
theorem slots_eq_blocks (plan : Midfall.Generator.RepackedProofLayoutPlan)
    (nNonQuot nbQuot nEval nPS : Nat)
    (h1 : plan.prefixG1Count = nNonQuot + nbQuot)
    (h2 : plan.numEvals = nEval) (h3 : plan.numPointSets = nPS) :
    List.replicate nNonQuot Midfall.Lowering.WireSlot.g1 ++
      List.replicate nbQuot Midfall.Lowering.WireSlot.g1 ++
      List.replicate nEval Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1] ++
      List.replicate nPS Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1]
      = plan.slots := by
  unfold Midfall.Generator.RepackedProofLayoutPlan.slots
  rw [h1, h2, h3, ← List.replicate_append_replicate]

/-- Mapping a width list block to `WireSlot`s: `g1` widths become
    `WireSlot.g1`, `fr` widths become `WireSlot.fr`. -/
theorem map_width_slots (g1 : G1Codec G₁) (nNonQuot nbQuot nEval nPS : Nat) :
    (List.replicate nNonQuot (hashableG1 g1).width ++
      List.replicate nbQuot (hashableG1 g1).width ++
      List.replicate nEval (hashableFr (p := p)).width ++
      [(hashableG1 g1).width] ++
      List.replicate nPS (hashableFr (p := p)).width ++
      [(hashableG1 g1).width]).map
        (fun w => if w = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                  else Midfall.Lowering.WireSlot.fr)
      = List.replicate nNonQuot Midfall.Lowering.WireSlot.g1 ++
        List.replicate nbQuot Midfall.Lowering.WireSlot.g1 ++
        List.replicate nEval Midfall.Lowering.WireSlot.fr ++
        [Midfall.Lowering.WireSlot.g1] ++
        List.replicate nPS Midfall.Lowering.WireSlot.fr ++
        [Midfall.Lowering.WireSlot.g1] := by
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    hashableG1_width, hashableFr_width, Midfall.g1CompressedWidth]
  simp [Midfall.g1CompressedWidth]

/-- The `Native.prepareWith` = `Verifier.prepare` definitional bridge: the
    native wrapper is the KZG-instantiated verifier on the array-converted
    committed/instance arguments. -/
theorem prepareWith_eq_verifierPrepare (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (committed : List (List G₁)) (inst : List (List (List (Fr p)))) :
    Midfall.Halo2.prepareWith (Gₜ := Gₜ) E F vk committed inst =
      Verifier.prepare (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.delta F
        (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field F E.fewerPointSetsRuntime) vk
        (committed.map (fun r => r.toArray)).toArray
        (inst.map (fun row => (row.map (fun col => col.toArray)).toArray)).toArray := rfl

/-- The quotient-commitment count `readAlgebra` reads: `1` under
    outer-single-h-commitment, `getQuotientPolyDegree` otherwise. -/
def readAlgebraQuotientCount {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (feat : Features) (vk : VerifyingKey (Fr p) G₁) : Nat :=
  if feat.outerSingleHCommitment then 1 else vk.domain.getQuotientPolyDegree

/-- The scalar-evaluation count `readAlgebra` reads, as a reusable function:
    committed-instance queries (per row), advice (per proof), fixed evals,
    permutation-common evals, `3k-1` per permutation set, `chunks+3` per lookup,
    `1` per trashcan. -/
def readAlgebraEvalCount {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) : Nat :=
  instances.size *
      (vk.cs.instanceQueries.toList.filter (fun q => q.1.index < nbCommitted)).length
    + numProofs * vk.cs.adviceQueries.size
    + (vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
    + vk.permutation.commitments.size
    + (permutations.toList.map
        (fun pc => 3 * pc.permutationProductCommitments.size - 1)).sum
    + (lookups.toList.map
        (fun row => (row.toList.map (fun l => l.helperPolys.size + 3)).sum)).sum
    + (trashcans.toList.map (fun row => row.size)).sum

/-- `readAlgebraWidths` is one `g1` block and one `fr` block. -/
theorem readAlgebraWidths_eq {G₁ : Type} (g1 : G1Codec G₁) (feat : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p)))) :
    readAlgebraWidths g1 feat vk permutations lookups trashcans nbCommitted numProofs instances
      = List.replicate (readAlgebraQuotientCount feat vk) (hashableG1 g1).width
        ++ List.replicate
            (readAlgebraEvalCount vk permutations lookups trashcans nbCommitted numProofs
              instances) (hashableFr (p := p)).width := rfl

/-- The three-block mapping: one `g1` block, one `fr` block, the `[g1]`
    separator, one `fr` block, `[g1]`. -/
theorem map_width_slots2 (g1 : G1Codec G₁) (nNonQuot nEval nPS : Nat) :
    (List.replicate nNonQuot (hashableG1 g1).width ++
      List.replicate nEval (hashableFr (p := p)).width ++
      [(hashableG1 g1).width] ++
      List.replicate nPS (hashableFr (p := p)).width ++
      [(hashableG1 g1).width]).map
        (fun w => if w = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                  else Midfall.Lowering.WireSlot.fr)
      = List.replicate nNonQuot Midfall.Lowering.WireSlot.g1 ++
        List.replicate nEval Midfall.Lowering.WireSlot.fr ++
        [Midfall.Lowering.WireSlot.g1] ++
        List.replicate nPS Midfall.Lowering.WireSlot.fr ++
        [Midfall.Lowering.WireSlot.g1] := by
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    hashableG1_width, hashableFr_width]
  simp [Midfall.g1CompressedWidth]

/-- The three-block plan-slot identity. -/
theorem slots_eq_blocks2 (plan : Midfall.Generator.RepackedProofLayoutPlan)
    (nNonQuot nEval nPS : Nat)
    (h1 : plan.prefixG1Count = nNonQuot)
    (h2 : plan.numEvals = nEval) (h3 : plan.numPointSets = nPS) :
    List.replicate nNonQuot Midfall.Lowering.WireSlot.g1 ++
      List.replicate nEval Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1] ++
      List.replicate nPS Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1]
      = plan.slots := by
  unfold Midfall.Generator.RepackedProofLayoutPlan.slots
  rw [← h1, ← h2, ← h3]

/-- **The `hSlots` count identity, proved from the per-trace counts.** The
    concrete `readAlgebraWidths` of the trace is `readAlgebraQuotientCount`
    `g1`s plus `readAlgebraEvalCount` `fr`s; the three count equalities turn
    the composed block list into the plan's `slots`. This is independent of
    A6's `parseTrace` widths and of the KZG partition bridge. -/
theorem prepareSlots_of_counts (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
    (nParse n : Nat)
    (h1 : nParse + readAlgebraQuotientCount Features.solidity R.vk
      = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).prefixG1Count)
    (h2 : readAlgebraEvalCount R.vk trace.permutations trace.lookups trace.trashcans
        1 1 #[#[inst.toList.toArray]]
      = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numEvals)
    (h3 : n = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    (List.replicate nParse (hashableG1 R.E.g1).width
      ++ (readAlgebraWidths R.E.g1 Features.solidity R.vk trace.permutations
            trace.lookups trace.trashcans 1 1 #[#[inst.toList.toArray]]
          ++ ([(hashableG1 R.E.g1).width]
              ++ List.replicate n (hashableFr (p := p)).width
              ++ [(hashableG1 R.E.g1).width]))).map
        (fun w => if w = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                  else Midfall.Lowering.WireSlot.fr)
      = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).slots := by
  have hwidth :
      (List.replicate nParse (hashableG1 R.E.g1).width
        ++ (readAlgebraWidths R.E.g1 Features.solidity R.vk trace.permutations
              trace.lookups trace.trashcans 1 1 #[#[inst.toList.toArray]]
            ++ ([(hashableG1 R.E.g1).width]
                ++ List.replicate n (hashableFr (p := p)).width
                ++ [(hashableG1 R.E.g1).width])))
      = (List.replicate (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).prefixG1Count (hashableG1 R.E.g1).width
          ++ List.replicate (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
              R.plan.proofLayout).numEvals (hashableFr (p := p)).width
          ++ [(hashableG1 R.E.g1).width]
          ++ List.replicate (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
              R.plan.proofLayout).numPointSets (hashableFr (p := p)).width
          ++ [(hashableG1 R.E.g1).width]) := by
    rw [readAlgebraWidths_eq]
    simp only [← List.append_assoc, List.replicate_append_replicate]
    rw [h1, h2, h3]
  rw [hwidth]
  rw [map_width_slots2]
  exact slots_eq_blocks2 (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
    R.plan.proofLayout) _ _ _ rfl rfl rfl

/-- **`PrepareLogSlots` from the exact parts.** `hParse` is A6's `parseTrace`
    schedule (the commitment prefix), `hMulti` is the KZG point-set count
    residual, and `hSlots` is the plan-slot identity with the protocol counts
    (`prefixG1Count = nonQuotient + nbQuotient`, `numEvals`, `numPointSets`).
    The `readAlgebra` block is discharged here, not assumed. -/
theorem PrepareLogSlots_of_parts (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (nParse n : Nat)
    (hParse : ∀ (inst : Array (Fr p)),
      ParseTraceWidths R.E Features.solidity R.vk #[#[(1 : G₁)]] #[#[inst.toList.toArray]] nParse)
    (hMulti : MultiPrepareBlockWidth R.E.g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime) n)
    (hSlots : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      (List.replicate nParse (hashableG1 R.E.g1).width
        ++ (readAlgebraWidths R.E.g1 Features.solidity R.vk trace.permutations
              trace.lookups trace.trashcans 1 1 #[#[inst.toList.toArray]]
            ++ ([(hashableG1 R.E.g1).width]
                ++ List.replicate n (hashableFr (p := p)).width
                ++ [(hashableG1 R.E.g1).width]))).map
          (fun w => if w = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                    else Midfall.Lowering.WireSlot.fr)
        = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots) :
    PrepareLogSlots R := by
  intro inst π d t hrun
  unfold Midfall.Halo2.prepare at hrun
  unfold Midfall.Halo2.prepareWith at hrun
  unfold Verifier.prepare at hrun
  obtain ⟨trace, t1, hparse, hver⟩ := PresWidthSeq.run_bind_ok hrun
  have hparseW : t1.log.toList.map (fun r => r.1) =
      (Transcript.initFromBytes π).log.toList.map (fun r => r.1)
        ++ List.replicate nParse (hashableG1 R.E.g1).width :=
    hParse inst (Transcript.initFromBytes π) t1 trace hparse
  have hverW : t.log.toList.map (fun r => r.1) = t1.log.toList.map (fun r => r.1) ++
      (readAlgebraWidths R.E.g1 Features.solidity R.vk trace.permutations
          trace.lookups trace.trashcans 1 1 #[#[inst.toList.toArray]]
        ++ ([(hashableG1 R.E.g1).width]
            ++ List.replicate n (hashableFr (p := p)).width
            ++ [(hashableG1 R.E.g1).width])) :=
    verifyAlgebraicConstraints_width R.E.g1 R.E.delta Features.solidity
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime) R.vk trace #[#[(1 : G₁)]] #[#[inst.toList.toArray]] n hMulti
      rfl t1 t d hver
  have hcompose : ∀ (l : List (Nat × Bytes)),
      l.map (fun r => if r.1 = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                      else Midfall.Lowering.WireSlot.fr)
        = (l.map (fun r => r.1)).map
            (fun w => if w = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
                      else Midfall.Lowering.WireSlot.fr) := by
    intro l
    rw [List.map_map]
    rfl
  rw [hcompose, hverW, hparseW]
  have hinit : (Transcript.initFromBytes π).log.toList.map (fun r => r.1) = [] := rfl
  rw [hinit]
  simp only [List.nil_append]
  exact hSlots inst trace

/-- **`PrepareLogSlots` from the exact parts and the per-trace counts.** This is
    `PrepareLogSlots_of_parts` with its `hSlots` premise decomposed into the
    three protocol counts, each a separate residual: A6's `parseTrace` g1 count
    (`hParse`, `h1`), the plan's `numEvals` (`h2`), and the KZG point-set count
    (`hMulti`, `h3`). -/
theorem PrepareLogSlots_of_counts (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (nParse n : Nat)
    (hParse : ∀ (inst : Array (Fr p)),
      ParseTraceWidths R.E Features.solidity R.vk #[#[(1 : G₁)]] #[#[inst.toList.toArray]] nParse)
    (hMulti : MultiPrepareBlockWidth R.E.g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime) n)
    (hCounts : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      nParse + readAlgebraQuotientCount Features.solidity R.vk
        = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).prefixG1Count
      ∧ readAlgebraEvalCount R.vk trace.permutations trace.lookups trace.trashcans
          1 1 #[#[inst.toList.toArray]]
        = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).numEvals
      ∧ n = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).numPointSets) :
    PrepareLogSlots R := by
  refine PrepareLogSlots_of_parts R nParse n hParse hMulti ?_
  intro inst trace
  exact prepareSlots_of_counts R inst trace nParse n
    (hCounts inst trace).1 (hCounts inst trace).2.1 (hCounts inst trace).2.2

/-- `fromProtocol`'s `evals` section has the item count it was handed. -/
theorem fromProtocol_evals_itemCount (protocol : Midfall.Generator.ProtocolPlan) (numEvals numPointSets : Nat)
    (L : Midfall.Generator.ProofCalldataLayout)
    (h : Midfall.Generator.ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets
        = .ok L) :
    L.evals.itemCount = numEvals := by
  rw [Midfall.Generator.ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, _, h1⟩ := AlgebraWidths.except_bind_ok h
  obtain ⟨x2, _, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨x3, _, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨x4, _, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨x5, _, h5⟩ := AlgebraWidths.except_bind_ok h4
  obtain ⟨x6, _, h6⟩ := AlgebraWidths.except_bind_ok h5
  by_cases hc : (x6.2.1 != protocol.proof.commitments.length) = true
  · rw [ite_eq_left hc] at h6
    obtain ⟨r, hr, _⟩ := AlgebraWidths.except_bind_ok h6
    cases hr
  · rw [ite_eq_right (by simpa using hc)] at h6
    cases h6
    rfl

/-- `fromProtocol`'s `qEvals` section has the point-set count it was handed. -/
theorem fromProtocol_qEvals_itemCount (protocol : Midfall.Generator.ProtocolPlan) (numEvals numPointSets : Nat)
    (L : Midfall.Generator.ProofCalldataLayout)
    (h : Midfall.Generator.ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets
        = .ok L) :
    L.qEvals.itemCount = numPointSets := by
  rw [Midfall.Generator.ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, _, h1⟩ := AlgebraWidths.except_bind_ok h
  obtain ⟨x2, _, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨x3, _, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨x4, _, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨x5, _, h5⟩ := AlgebraWidths.except_bind_ok h4
  obtain ⟨x6, _, h6⟩ := AlgebraWidths.except_bind_ok h5
  by_cases hc : (x6.2.1 != protocol.proof.commitments.length) = true
  · rw [ite_eq_left hc] at h6
    obtain ⟨r, hr, _⟩ := AlgebraWidths.except_bind_ok h6
    cases hr
  · rw [ite_eq_right (by simpa using hc)] at h6
    cases h6
    rfl

/-- `newFromVk`'s first bind: the plan carries the meta and proof layout its own
    second bind produced (meta equality included). -/
theorem newFromVk_meta_layout {F : Type} [BEq F] (feat : Features)
    (field : Midfall.Generator.QuotientEvaluator.FieldCtx F) (cs : ConstraintSystem F)
    (rawMeta : Midfall.Generator.ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Midfall.Generator.Halo2VerifyingKey)
    (plan : Midfall.Generator.LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding payload
        = .ok plan) :
    ∃ (meta_ : Midfall.Generator.ConstraintSystemMeta) (L : Midfall.Generator.ProofCalldataLayout),
      plan.meta_ = meta_ ∧ plan.proofLayout = L ∧
      Midfall.Generator.ProofCalldataLayout.fromProtocol meta_.protocol Midfall.Generator.abiVerifyProofProofCptr meta_.numEvals
        meta_.numPointSets = .ok L := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, _, h1⟩ := AlgebraWidths.except_bind_ok h
  obtain ⟨proofLayout, hpl, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := AlgebraWidths.except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := AlgebraWidths.except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := AlgebraWidths.except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := AlgebraWidths.except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := AlgebraWidths.except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := AlgebraWidths.except_bind_ok h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨q.2.1, proofLayout, rfl, rfl, hpl⟩)

theorem metaDataForVk_meta_preserved {Plan : Type} (feat : Features) (env : VkBuildEnv Plan)
    (m : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (hfew : feat.outerFewerPointSets = false)
    {meta' : ConstraintSystemMeta} {dat : Data} {mem : VerifierMemoryLayout}
    (h : metaDataForVk feat env m numInstances vk vkMptr = .ok (meta', dat, mem)) :
    meta'.numEvals = m.numEvals ∧ meta'.protocol = m.protocol := by
  unfold metaDataForVk at h
  simp only [Bind.bind, hfew, if_false] at h
  obtain ⟨x1, _, h1⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h
  obtain ⟨x2, _, h2⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h1
  obtain ⟨x3, hx3, h3⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h2
  obtain ⟨x4, _, h4⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h3
  obtain ⟨x5, _, h5⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h4
  obtain ⟨x6, _, h6⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h5
  obtain ⟨x7, _, h7⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h6
  cases hx3
  cases h7
  exact ⟨rfl, rfl⟩

theorem metaDataForStableStaticLayout_meta_preserved {Plan : Type} (feat : Features)
    (hfew : feat.outerFewerPointSets = false) (env : VkBuildEnv Plan)
    (m : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    {vkMptr : Ptr} {meta' : ConstraintSystemMeta} {dat : Data} {mem : VerifierMemoryLayout}
    (h : metaDataForStableStaticLayout feat env m numInstances vk
      = .ok (vkMptr, meta', dat, mem)) :
    meta'.numEvals = m.numEvals ∧ meta'.protocol = m.protocol := by
  unfold metaDataForStableStaticLayout at h
  simp only [Bind.bind] at h
  obtain ⟨start, _, h1⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h
  obtain ⟨res, hres, hout⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h1
  have key : ∀ (l : List Nat)
      (st : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr),
      (∀ r, st.1 = some r → r.2.1.numEvals = m.numEvals ∧ r.2.1.protocol = m.protocol) →
      ∀ (res' : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr),
        l.foldlM (fun (st : Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr)
            (_ : Nat) => do
          if st.1.isSome then Except.ok st else do
            let vkMptr := st.2
            let (metaOut, dat, memory) ← metaDataForVk feat env m numInstances vk vkMptr
            let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
            let cur ← Value.asUsize vkMptr.value
            if planned == cur then
              Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
            else
              Except.ok (none, ptrMemory (valueFromNat planned))) st = .ok res' →
        (∀ r, res'.1 = some r → r.2.1.numEvals = m.numEvals ∧ r.2.1.protocol = m.protocol) := by
    intro l
    induction l with
    | nil =>
        intro st hinv res' hf
        cases hf
        exact hinv
    | cons a as ih =>
        intro st hinv res' hf
        rw [List.foldlM_cons] at hf
        obtain ⟨st1, hstep, hrest⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok hf
        apply ih _ ?_ res' hrest
        intro r hr
        split at hstep
        · rename_i hsome
          cases hstep
          exact hinv r hr
        · rename_i hnone
          obtain ⟨q, hq, hstep2⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok hstep
          obtain ⟨q2, hq2, hstep3⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok hstep2
          obtain ⟨q3, hq3, hstep4⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok hstep3
          split at hstep4
          · cases hstep4
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
            exact metaDataForVk_meta_preserved feat env m numInstances vk st.2 hfew hq
          · cases hstep4
            cases hr
  obtain ⟨resO, resPtr⟩ := res
  cases resO with
  | none => cases hout
  | some r =>
      have hkey := key (List.range 3) (none, ptrMemory (valueFromNat start))
        (by intro r hr; cases hr) (some r, resPtr) hres
      have hval : r = (vkMptr, meta', dat, mem) := Except.ok.inj hout
      have hfin := hkey r rfl
      rw [hval] at hfin
      exact hfin

theorem newFromVk_meta_numEvals {F : Type} [BEq F]
    (field : Midfall.Generator.QuotientEvaluator.FieldCtx F) (cs : ConstraintSystem F)
    (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk Features.solidity field cs rawMeta numInstances
        accEncoding payload = .ok plan) :
    plan.meta_.numEvals = rawMeta.numEvals ∧ plan.meta_.protocol = rawMeta.protocol := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h
  obtain ⟨proofLayout, _hpl, h2⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h1
  obtain ⟨_qplan, _, h3⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h2
  obtain ⟨_build, _, h4⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h3
  obtain ⟨_nw, _, h5⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h4
  obtain ⟨_pcs, _, h6⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h5
  obtain ⟨_acc, _, h7⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h6
  obtain ⟨_memory, _, h8⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h7
  obtain ⟨_op, _, h9⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h8
  obtain ⟨_trip, _, h10⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals exact metaDataForStableStaticLayout_meta_preserved Features.solidity rfl _ rawMeta numInstances payload hq

theorem ConstraintSystemMeta.new_numEvals {F : Type} (feat : Features) (cs : ConstraintSystem F)
    (nbCommittedInstances : Nat) {m : ConstraintSystemMeta}
    (h : ConstraintSystemMeta.new feat cs nbCommittedInstances = .ok m) :
    m.numEvals = m.protocol.numMainEvals := by
  unfold ConstraintSystemMeta.new at h
  simp only [Bind.bind] at h
  obtain ⟨protocol, _hproto, hok⟩ := Midfall.LoweringV3.AlgebraWidths.except_bind_ok h
  cases hok
  rfl

/-- **The plan-side eval-count identification.** For a generated plan (the
    deployed `Features.solidity` profile), the layout's `numEvals` is the
    protocol's main-eval count `meta_.protocol.numMainEvals =
    meta_.protocol.proof.evals.length`: the meta starts from
    `ConstraintSystemMeta.new` (`numEvals := protocol.numMainEvals`), the
    dummy-eval write is `0` with outer-fewer-point-sets off, and
    `fromProtocol` stores `meta_.numEvals` verbatim in `evals.itemCount`. -/
theorem plan_numEvals_eq_protocol (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
      = R.plan.meta_.protocol.numMainEvals := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := Midfall.LoweringV2.pfx_plan_of_generated hR.generated
  obtain ⟨meta_, L, hmeta, hplL, hL⟩ := newFromVk_meta_layout Features.solidity
    (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta R.cfg.numInstances
    R.cfg.accumulator R.plan.vk plan hpl
  rw [← hp] at hmeta hplL
  have h1 : (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
      R.plan.proofLayout).numEvals = R.plan.meta_.numEvals := by
    rw [hplL, hmeta]
    show L.evals.itemCount = meta_.numEvals
    exact fromProtocol_evals_itemCount meta_.protocol meta_.numEvals meta_.numPointSets L hL
  rw [h1]
  have hq := newFromVk_meta_numEvals (Midfall.Generator.PlanNew.frFieldCtx R.E.delta)
    R.vk.cs rawMeta R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  rw [← hp] at hq
  have hrawE := ConstraintSystemMeta.new_numEvals Features.solidity R.vk.cs
    R.cfg.numCommittedInstances hraw
  obtain ⟨hqE, hqP⟩ := hq
  rw [hqE, hqP, hrawE]

/-- The same count as the protocol's eval-read list length. -/
theorem plan_numEvals_eq_proofEvalsLength (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
      = R.plan.meta_.protocol.proof.evals.length := by
  rw [plan_numEvals_eq_protocol R hR]
  rfl

/-- **`PrepareLogSlots` with the plan-side eval count discharged.** The
    `numEvals` premise of `PrepareLogSlots_of_counts` is replaced by the
    trace/protocol count equality: `plan.numEvals = protocol.numMainEvals` is
    now proved (`plan_numEvals_eq_protocol`), so the only remaining eval-count
    premise is the verifier's own count against the protocol's eval-read list
    (the parseTrace shape half). -/
theorem PrepareLogSlots_of_counts' (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (nParse n : Nat)
    (hParse : ∀ (inst : Array (Fr p)),
      ParseTraceWidths R.E Features.solidity R.vk #[#[(1 : G₁)]] #[#[inst.toList.toArray]] nParse)
    (hMulti : MultiPrepareBlockWidth R.E.g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime) n)
    (hCounts : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      nParse + readAlgebraQuotientCount Features.solidity R.vk
        = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).prefixG1Count
      ∧ readAlgebraEvalCount R.vk trace.permutations trace.lookups trace.trashcans
          1 1 #[#[inst.toList.toArray]]
        = R.plan.meta_.protocol.numMainEvals
      ∧ n = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
            R.plan.proofLayout).numPointSets) :
    PrepareLogSlots R := by
  refine PrepareLogSlots_of_counts R nParse n hParse hMulti ?_
  intro inst trace
  refine ⟨(hCounts inst trace).1, ?_, (hCounts inst trace).2.2⟩
  exact (hCounts inst trace).2.1.trans (plan_numEvals_eq_protocol R hR).symm

/-- Filtering a mapped list by a property of the mapped index equals filtering
    first and mapping: the committed-instance filter commutes with the
    `(Column, Rotation) → QueryKey` map of `ProtocolPlan.fromConstraintSystem`. -/
theorem filter_map_index_length (l : List (Column × Rotation)) (nb : Nat) :
    ((l.map (fun q => QueryKey.new q.1.index q.2.int)).filter
        (fun q => q.column < nb)).length
      = (l.filter (fun q => q.1.index < nb)).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      have hcol : (QueryKey.new a.1.index a.2.int).column = a.1.index := rfl
      by_cases h : a.1.index < nb <;> simp [h, hcol, ih]

/-- **The committed-instance filter identity.** The verifier's committed-instance
    query count (`q.1.index < nbCommitted`) is the protocol plan's
    `committedInstanceQueries` count, given the plan's `instanceQueries` field is
    the `QueryKey` image of the constraint system's query vector and the two
    committed-instance counts agree (both are `hR`/`ConstraintsSystemMeta` plan
    fields). -/
theorem committedInstanceFilter_eq_protocol (cs : ConstraintSystem (Fr p))
    (protocol : ProtocolPlan) (nbCommitted : Nat)
    (hq : protocol.instanceQueries = cs.instanceQueries.toList.map
      (fun q => QueryKey.new q.1.index q.2.int))
    (hnb : protocol.numCommittedInstances = nbCommitted) :
    (cs.instanceQueries.toList.filter (fun q => q.1.index < nbCommitted)).length
      = (protocol.instanceQueries.filter
          (fun q => q.column < protocol.numCommittedInstances)).length := by
  rw [hq, hnb]
  exact (filter_map_index_length cs.instanceQueries.toList nbCommitted).symm

end Composition

end Midfall.LoweringV3

