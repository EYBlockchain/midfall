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
import Midfall.LoweringV3.KzgQueryMap
import Midfall.LoweringV3.RotationInjectivity
import Midfall.LoweringV3.LinearizeEntry
import Midfall.LoweringV3.QueryTail
import Midfall.LoweringV3.QueryBlockShape
import Midfall.LoweringV3.PcsOrder
import Midfall.LoweringV3.UpstreamSets
import Midfall.LoweringV3.QuotientFresh
import Midfall.LoweringV3.RenderFresh
import Midfall.LoweringV3.TranscriptRows
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

/-- The width block of ONE `multiPrepare` call, at a fixed query vector. This is
    the true KZG obligation (the `∀ queries` form is refuted at `#[]`; see
    `MultiPrepareBlockWidth.eq_zero_of_empty_run`). -/
def MultiPrepareBlockWidthAt {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat)
    (queries : Array (VerifierQuery (Fr p) G₁)) : Prop :=
  PresWidthSeq
    ([(hashableG1 g1).width] ++ List.replicate n (hashableFr (p := p)).width ++
      [(hashableG1 g1).width])
    (pcs.multiPrepare queries)

/-- The repaired KZG residual: the width block at the query vectors
    `Verifier.linearize` actually produces. Quantified over the algebra-read state
    and the linearize equation, so the empty query vector cannot refute it. -/
def MultiPrepareWidthsLinearize {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat)
    (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (feat : Features)
    (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁))
    (instances : Array (Array (Array (Fr p)))) : Prop :=
  ∀ (alg : Verifier.AlgebraRead (Fr p) G₁)
    (queries : Array (VerifierQuery (Fr p) G₁)),
    Verifier.linearize (p := p) (delta := delta) vk
      (adviceCommitments := trace.adviceCommitments)
      (committedInstances := if feat.committedInstances then committedInstances
        else arrayReplicate instances.size (#[] : Array G₁))
      (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
      (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
      = .ok queries →
    MultiPrepareBlockWidthAt g1 pcs n queries

/-- The per-query width obligation, discharged from the point-set count (an
    unconditional consequence of `PresWidthSeq.multiPrepare_width`). -/
theorem MultiPrepareBlockWidthAt_of_pointSets {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (n : Nat)
    (queries : Array (VerifierQuery (Fr p) G₁))
    (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p)))
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    (hCI : constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
      = .ok (cm, pointSets))
    (hPoint : pointSets.size = n) :
    MultiPrepareBlockWidthAt g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime) n queries := by
  have hw := PresWidthSeq.multiPrepare_width (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
    fewerPointSetsRuntime queries hNoDummies cm pointSets hCI
  rw [hPoint] at hw
  exact hw

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

section KzgPointSetCount

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ### The point-set count: the exact gap in `KzgMultiPrepareWidths`

    `PresWidthSeq.multiPrepare_width` (above) already gives the exact width list
    `[g1] ++ replicate pointSets.size fr ++ [g1]` for every `multiPrepare` run, where
    `pointSets` is the `constructIntermediateSets` result. The only remaining input of
    `KzgMultiPrepareWidths` is therefore the COUNT equality `pointSets.size = n`.
    The theorems here state that reduction exactly and consume the already-named
    `KzgPartitionBridge` (`LoweringV3.EndToEnd`) on the generator side.

    W12 BLOCKER, in the tree: the count is NOT queries-independent. `#[]` gives
    `pointSets.size = 0`, while a deployed plan has `numPointSets > 0`, so the
    `∀ queries` form of `MultiPrepareWidths` is FALSE at the empty query vector
    (for any transcript on which the empty run succeeds). `pointSetsCount_forces_zero`
    is that obstruction, not a weakening: the true residual has to be stated at the
    LINEARIZED query vector (`Verifier.linearize`'s output), whose point-set count is
    fixed by the VK under `ChallengesGood.xNonzero` + rotation distinctness. -/

/-- `multiPrepare` succeeds only if `constructIntermediateSets` did: the
    inversion of the phaseA `StateT.lift` (the `buildQ` lift is irrelevant here). -/
theorem multiPrepare_constructIntermediateSets_ok
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (queries : Array (VerifierQuery (Fr p) G₁))
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    {t : Transcript} {a : DualMSM (Fr p) G₁ G₂ Gₜ} {t' : Transcript}
    (hrun : (Midfall.Halo2.multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
      fewerPointSetsRuntime queries).run t = .ok (a, t')) :
    ∃ cm pointSets,
      constructIntermediateSets (F := Fr p) (C := G₁)
        (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
        = .ok (cm, pointSets) := by
  unfold Midfall.Halo2.multiPrepare at hrun
  obtain ⟨aA, tA, hA, _⟩ := PresWidthSeq.run_bind_ok hrun
  unfold Midfall.Halo2.phaseA at hA
  dsimp only at hA
  rw [if_neg hNoDummies] at hA
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_lift] at hA
  obtain ⟨p1, hp1, h1⟩ := AlgebraWidths.except_bind_ok hA
  cases hp1
  obtain ⟨p2, _, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨p3, _, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨p4, hp4, _⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨cp, hcp, _⟩ := AlgebraWidths.except_bind_ok hp4
  exact ⟨cp.1, cp.2, hcp⟩

/-- The empty query vector has no point sets (the `where` folds reduce on `[]`). -/
theorem constructIntermediateSets_empty :
    constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))
      (#[] : Array (VerifierQuery (Fr p) G₁)) = .ok (#[], #[]) := by
  rfl

/-- **THE `∀ queries` COUNT IS ZERO.** Any uniform point-set count must be `0`, by
    the empty query vector. So `MultiPrepareBlockWidth … n` with `n ≠ 0` cannot be
    established (and is false whenever the empty query run succeeds; see
    `MultiPrepareBlockWidth.eq_zero_of_empty_run`). -/
theorem pointSetsCount_forces_zero
    (n : Nat)
    (hPoint : ∀ (queries : Array (VerifierQuery (Fr p) G₁))
      (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p))),
      constructIntermediateSets (F := Fr p) (C := G₁)
        (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
        = .ok (cm, pointSets) → pointSets.size = n) :
    n = 0 := by
  have h := hPoint #[] #[] #[] (constructIntermediateSets_empty (p := p) (G₁ := G₁)
    (G₂ := G₂) (Gₜ := Gₜ))
  simpa using h.symm

/-- **THE COUNT REDUCTION.** `MultiPrepareBlockWidth` for the KZG instance follows
    from the point-set count equality at every query vector. This is exactly the
    missing count; the width sequence itself is `PresWidthSeq.multiPrepare_width`. -/
theorem MultiPrepareBlockWidth_of_pointSets
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (n : Nat)
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    (hPoint : ∀ (queries : Array (VerifierQuery (Fr p) G₁))
      (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p))),
      constructIntermediateSets (F := Fr p) (C := G₁)
        (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
        = .ok (cm, pointSets) → pointSets.size = n) :
    MultiPrepareBlockWidth g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime) n := by
  intro queries t t' a hrun
  obtain ⟨cm, pointSets, hCI⟩ :=
    multiPrepare_constructIntermediateSets_ok g1 fc feat fewerPointSetsRuntime queries
      hNoDummies hrun
  have hw := PresWidthSeq.multiPrepare_width (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
    fewerPointSetsRuntime queries hNoDummies cm pointSets hCI
  have hp := hPoint queries cm pointSets hCI
  rw [hp] at hw
  exact hw t t' a hrun

/-- **THE TRUE RESIDUAL'S SHAPE, PER QUERY VECTOR.** For the linearized query
    vector, the width block is exact as soon as `constructIntermediateSets` gives
    the plan's point-set count. This is the statement the D-GATE6 query-map bridge
    must discharge at `Verifier.linearize`'s output; it is NOT the `∀ queries`
    form (which is false at `#[]`). -/
theorem multiPrepare_width_at (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (queries : Array (VerifierQuery (Fr p) G₁))
    (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p)))
    (hCI : constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
      = .ok (cm, pointSets))
    (hPoint : pointSets.size = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
      R.plan.proofLayout).numPointSets) :
    PresWidthSeq ([(hashableG1 R.E.g1).width] ++
        List.replicate (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets (hashableFr (p := p)).width ++
        [(hashableG1 R.E.g1).width])
      ((Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime).multiPrepare queries) := by
  have hNoDummies : ¬ (Features.solidity.outerFewerPointSets && R.E.fewerPointSetsRuntime) := by
    simp [Features.solidity]
  have hw := PresWidthSeq.multiPrepare_width (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field
    Features.solidity R.E.fewerPointSetsRuntime queries hNoDummies cm pointSets hCI
  rw [hPoint] at hw
  exact hw

/-- The empty-query width block of `multiPrepare`: two `g1` reads, no scalars. -/
theorem multiPrepare_width_empty
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool)
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime)) :
    PresWidthSeq ([(hashableG1 g1).width] ++ [(hashableG1 g1).width])
      (Midfall.Halo2.multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
        fewerPointSetsRuntime #[]) := by
  have hCI := constructIntermediateSets_empty (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
  have hw := PresWidthSeq.multiPrepare_width (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
    fewerPointSetsRuntime #[] hNoDummies #[] #[] hCI
  simpa using hw

/-- **W12: THE `∀ queries` FORM IS REFUTED BY THE EMPTY QUERY VECTOR.** If the empty
    query run succeeds, any uniform `MultiPrepareBlockWidth … n` forces `n = 0`; a
    deployed plan has `numPointSets > 0`, so `KzgMultiPrepareWidths R` cannot be
    closed in its `∀ queries` form. The true residual is the linearized-query form. -/
theorem MultiPrepareBlockWidth.eq_zero_of_empty_run
    (g1 : G1Codec G₁) (fc : FieldConsts (Fr p)) (feat : Features)
    (fewerPointSetsRuntime : Bool) (n : Nat)
    (hNoDummies : ¬ (feat.outerFewerPointSets && fewerPointSetsRuntime))
    (h : MultiPrepareBlockWidth g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat fewerPointSetsRuntime) n)
    {t : Transcript} {a : DualMSM (Fr p) G₁ G₂ Gₜ} {t' : Transcript}
    (hrun : (Midfall.Halo2.multiPrepare (G₂ := G₂) (Gₜ := Gₜ) g1 fc feat
      fewerPointSetsRuntime #[]).run t = .ok (a, t')) :
    n = 0 := by
  have h1 := h #[] t t' a hrun
  have h2 := multiPrepare_width_empty g1 fc feat fewerPointSetsRuntime hNoDummies
    t t' a hrun
  have hws : ([(hashableG1 g1).width] ++ List.replicate n (hashableFr (p := p)).width ++
        [(hashableG1 g1).width])
      = ([(hashableG1 g1).width] ++ [(hashableG1 g1).width]) :=
    List.append_cancel_left (h1.symm.trans h2)
  have hlen := congrArg List.length hws
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
  omega

end KzgPointSetCount

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
    point-set count supplied at each `linearize` output (`MultiPrepareBlockWidthAt`),
    the D-GATE10 repaired form. -/
theorem readAlgebra_multiPrepare_widths (g1 : G1Codec G₁) (feat : Features)
    (vk : VerifyingKey (Fr p) G₁)
    (permutations : Array (Permutation.Committed G₁))
    (lookups : Array (Array (Logup.Committed G₁)))
    (trashcans : Array (Array (Trash.Committed G₁)))
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p))))
    (pcs : Pcs p G₁ G₂ Gₜ) (n : Nat)
    (lin : Verifier.AlgebraRead (Fr p) G₁ → Except Fault (Array (VerifierQuery (Fr p) G₁)))
    (hMulti : ∀ (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      lin alg = .ok queries → MultiPrepareBlockWidthAt g1 pcs n queries) :
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
  intro t2 t' d hd
  change (StateT.lift (lin alg) >>= fun queries => pcs.multiPrepare queries).run t2
    = .ok (d, t') at hd
  rw [StateT.run_bind] at hd
  cases hlin : lin alg with
  | error e =>
      rw [hlin] at hd
      cases hd
  | ok queries =>
      rw [hlin] at hd
      simp only [StateT.run_lift] at hd
      exact hMulti alg queries hlin t2 t' d hd

/-- **The `verifyAlgebraicConstraints` run glue.** `readAlgebra`'s exact
    widths, the width-free `linearize` lift, and the `multiPrepare` block at the
    query vector `linearize` produced (via `MultiPrepareWidthsLinearize`, the
    D-GATE10 repaired form), with the `committed.isEmpty` guard and the
    `StateT.get`/`match`/`StateT.set` re-run dance discharged. -/
theorem verifyAlgebraicConstraints_width (g1 : G1Codec G₁) (delta : Fr p)
    (feat : Features) (pcs : Pcs p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (trace : VerifierTrace (Fr p) G₁)
    (committedInstances : Array (Array G₁)) (instances : Array (Array (Array (Fr p))))
    (n : Nat)
    (hMulti : MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
      g1 pcs n delta vk feat trace committedInstances instances)
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
  have hif : (if feat.committedInstances then committedInstances
        else arrayReplicate instances.size (#[] : Array G₁))
      = (if True then committedInstances
        else arrayReplicate instances.size (#[] : Array G₁)) := by
    simp [hCommit]
  unfold Verifier.verifyAlgebraicConstraints
  dsimp only
  simp only [hCommit]
  refine PresWidthSeq.ite ?_ ?_
  · -- the empty-committed-instances check throws: any width list is vacuous
    intro t t' a h
    change (Except.error (Fault.error Error.invalidInstances) :
      Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ × Transcript)) = .ok (a, t') at h
    cases h
  · refine PresWidthSeq.bind
      (ws1 := readAlgebraWidths g1 feat vk trace.permutations trace.lookups trace.trashcans
        _ instances.size instances)
      (PresWidthSeq.readAlgebra_widths g1 feat vk trace.permutations trace.lookups
        trace.trashcans _ instances.size instances) (fun alg => ?_)
    intro t2 t' d hd
    simp only [StateT.run_bind, StateT.run_lift] at hd
    cases hlin : Verifier.linearize (p := p) (delta := delta) vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if True then committedInstances
          else arrayReplicate instances.size (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg with
    | error e =>
        rw [hlin] at hd
        cases hd
    | ok queries =>
        rw [hlin] at hd
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT_get_run] at hd
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
            have hlin' : Verifier.linearize (p := p) (delta := delta) vk
                (adviceCommitments := trace.adviceCommitments)
                (committedInstances := if feat.committedInstances then committedInstances
                  else arrayReplicate instances.size (#[] : Array G₁))
                (y := trace.y) (beta := trace.beta) (gamma := trace.gamma)
                (theta := trace.theta) (trashChallenge := trace.trashChallenge)
                (challenges := trace.challenges) alg = .ok queries := by
              rwa [← hif] at hlin
            have hw := hMulti alg queries hlin' t2 t3 a0 hmr
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
    (hMulti : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        R.E.g1 (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
          R.E.fewerPointSetsRuntime) n R.E.delta R.vk Features.solidity trace
        #[#[(1 : G₁)]] #[#[inst.toList.toArray]])
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
        R.E.fewerPointSetsRuntime) R.vk trace #[#[(1 : G₁)]] #[#[inst.toList.toArray]] n
      (hMulti inst trace) rfl t1 t d hver
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
    (hMulti : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        R.E.g1 (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
          R.E.fewerPointSetsRuntime) n R.E.delta R.vk Features.solidity trace
        #[#[(1 : G₁)]] #[#[inst.toList.toArray]])
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

/-- **THE PARSER-SIDE ADVICE ITEM COUNT.** `fromProtocol` reserves one advice
    section per entry of `protocol.numUserAdvices`, in phase order, so the i-th
    section carries the i-th user-advice count. This is the advice half of the
    `TpLayoutFacts` peel (`TranscriptRows.tp_fromProtocol` only records the
    section-shape facts); the schedule walk needs the per-index count to identify
    the parser's per-phase `tmReadN` widths with the plan's advice read groups. -/
theorem fromProtocol_advice_itemCount
    (protocol : Midfall.Generator.ProtocolPlan) (numEvals numPointSets : Nat)
    (L : Midfall.Generator.ProofCalldataLayout)
    (h : Midfall.Generator.ProofCalldataLayout.fromProtocol protocol
        Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets = .ok L)
    (i : Nat) (s : Midfall.Generator.ProofSection)
    (hs : L.advicePhases[i]? = some s) :
    ∃ c, protocol.numUserAdvices[i]? = some c ∧ s.itemCount = c := by
  rw [Midfall.Generator.ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, hadv, h1⟩ := AlgebraWidths.except_bind_ok h
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
    exact Midfall.LoweringV3.TranscriptRows.foldlM_take_nth protocol
      Midfall.Generator.CommitmentRead.advice "advice phase" protocol.numUserAdvices
      (([] : List Midfall.Generator.ProofSection), 0, Midfall.Generator.abiVerifyProofProofCptr)
      x1 i s hadv (by simp) (by simpa using hs)

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

/-- **The plan-side point-set-count identification.** For a generated plan, the
    repacked layout's `numPointSets` (`proofLayout.qEvals.itemCount`) is the plan
    meta's `numPointSets`, exactly as `plan_numEvals_eq_protocol` does for
    `numEvals`. Proved from `newFromVk_meta_layout` and
    `fromProtocol_qEvals_itemCount`; no count hypothesis is assumed. -/
theorem plan_numPointSets_eq_meta (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets
      = R.plan.meta_.numPointSets := by
  obtain ⟨rawMeta, plan, _hraw, hpl, hp⟩ :=
    Midfall.LoweringV2.pfx_plan_of_generated hR.generated
  obtain ⟨meta_, L, hmeta, hplL, hL⟩ := newFromVk_meta_layout Features.solidity
    (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta R.cfg.numInstances
    R.cfg.accumulator R.plan.vk plan hpl
  rw [← hp] at hmeta hplL
  rw [hplL, hmeta]
  show L.qEvals.itemCount = meta_.numPointSets
  exact fromProtocol_qEvals_itemCount meta_.protocol meta_.numEvals meta_.numPointSets L hL

/-- **THE PLAN META'S POINT-SET COUNT IS THE GENERATOR'S COUNT.** `PlanMeta`
    pins `R.plan.meta_` to `(m0.setNumDummyEvals 0).setNumPointSets n` with
    `numPointSets (m0.setNumDummyEvals 0) R.plan.data = .ok n`. Since
    `numPointSets`/`queries` read only the protocol (not the `numPointSets`
    field), the successful computation is available at `R.plan.meta_` itself,
    and its `sortSets` result has exactly `n = R.plan.meta_.numPointSets`
    point sets. The empty dummy-eval buffer is derived from `PlanMeta`'s
    `Data.new` equation by `Data.new_dummyEvalWords`. -/
theorem planMeta_numPointSets_generator (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hM : PlanMeta R) :
    ∃ (qs : List Midfall.Generator.Query) (sets out : Midfall.Generator.IntermediateSets),
      Midfall.Generator.queries R.plan.meta_ R.plan.data = .ok qs ∧
      Midfall.Generator.constructIntermediateSetsImpl qs = .ok sets ∧
      Midfall.Generator.sortSets sets = .ok out ∧
      R.plan.meta_.numPointSets = out.pointSets.length := by
  obtain ⟨m0, n, _hnew, hdata, hn, hmeta⟩ := hM
  have hdummy : R.plan.data.dummyEvalWords = [] :=
    Data.new_dummyEvalWords (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory R.plan.data hdata
  have hcount : Midfall.Generator.numPointSets (R.plan.meta_.setNumPointSets 0)
      R.plan.data = .ok n := by
    rw [hmeta]
    rw [show ((m0.setNumDummyEvals 0).setNumPointSets n).setNumPointSets 0 =
      (m0.setNumDummyEvals 0).setNumPointSets 0 by
        simp [Midfall.Generator.ConstraintSystemMeta.setNumPointSets]]
    rw [numPointSets_setNumPointSets]
    exact hn
  obtain ⟨out, hout, hlen⟩ :=
    numPointSets_parts (R.plan.meta_.setNumPointSets 0) R.plan.data n hcount
  obtain ⟨qs, sets, hq0, hci, hsort⟩ :=
    intermediateSets_parts (R.plan.meta_.setNumPointSets 0) R.plan.data
      out hdummy hout
  have hq : Midfall.Generator.queries R.plan.meta_ R.plan.data = .ok qs := by
    rw [← queries_setNumPointSets]
    exact hq0
  refine ⟨qs, sets, out, hq, hci, hsort, ?_⟩
  rw [hmeta]
  exact hlen.symm

/-- **THE KZG `PlanMeta` RESIDUAL, DISCHARGED FOR GENERATED RENDERS.** `PlanMeta` was the one
    hypothesis `planMeta_numPointSets_generator` could not derive, because it is a property of
    the plan the generator builds. `MemoryPairs.planMeta_of_generated` proves it from the
    `generated` clause alone (the intermediate-vs-final layout stability is
    `Generator.new_dataBases_setNumPointSets`), so the point-set count now follows from
    generation with no extra premise. PROVED. -/
theorem planMeta_numPointSets_of_generated (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (h : GeneratedBy R) :
    ∃ (qs : List Midfall.Generator.Query) (sets out : Midfall.Generator.IntermediateSets),
      Midfall.Generator.queries R.plan.meta_ R.plan.data = .ok qs ∧
      Midfall.Generator.constructIntermediateSetsImpl qs = .ok sets ∧
      Midfall.Generator.sortSets sets = .ok out ∧
      R.plan.meta_.numPointSets = out.pointSets.length :=
  planMeta_numPointSets_generator R (Midfall.LoweringV3.MemoryPairs.planMeta_of_generated h)

/-- The same at the statement surface: `ValidV3`'s `generated` conjunct supplies the premise. -/
theorem planMeta_numPointSets_of_validV3 (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    ∃ (qs : List Midfall.Generator.Query) (sets out : Midfall.Generator.IntermediateSets),
      Midfall.Generator.queries R.plan.meta_ R.plan.data = .ok qs ∧
      Midfall.Generator.constructIntermediateSetsImpl qs = .ok sets ∧
      Midfall.Generator.sortSets sets = .ok out ∧
      R.plan.meta_.numPointSets = out.pointSets.length :=
  planMeta_numPointSets_of_generated R hR.generated

theorem planMeta_numPointSets_generator_of_validV3
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    ∃ (qs : List Midfall.Generator.Query) (sets out : Midfall.Generator.IntermediateSets),
      Midfall.Generator.queries R.plan.meta_ R.plan.data = .ok qs ∧
      Midfall.Generator.constructIntermediateSetsImpl qs = .ok sets ∧
      Midfall.Generator.sortSets sets = .ok out ∧
      R.plan.meta_.numPointSets = out.pointSets.length :=
  planMeta_numPointSets_generator R
    (Midfall.LoweringV3.MemoryPairs.planMeta_of_generated hR.generated)

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
    (hMulti : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        R.E.g1 (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
          R.E.fewerPointSetsRuntime) n R.E.delta R.vk Features.solidity trace
        #[#[(1 : G₁)]] #[#[inst.toList.toArray]])
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

theorem readN_go_size {T : Type} (h : Midfall.Halo2.Hashable T) :
    ∀ (n : Nat) (t : Transcript) (acc : Array T) (acc' : Array T) (t' : Transcript),
      Transcript.readN.go h t acc n = .ok (acc', t') → acc'.size = acc.size + n := by
  intro n
  induction n with
  | zero =>
      intro t acc acc' t' hr
      rw [Transcript.readN.go.eq_1] at hr
      cases hr
      simp
  | succ m ih =>
      intro t acc acc' t' hr
      rw [Transcript.readN.go.eq_2] at hr
      simp only [Bind.bind, Except.bind] at hr
      split at hr
      · cases hr
      · rename_i x hx
        obtain ⟨v, t2⟩ := x
        have := ih t2 (acc.push v) acc' t' hr
        simp only [Array.size_push] at this
        omega

theorem readN_size {T : Type} (h : Midfall.Halo2.Hashable T) (t : Transcript) (n : Nat)
    {acc : Array T} {t' : Transcript} (hr : t.readN h n = .ok (acc, t')) :
    acc.size = n := by
  unfold Transcript.readN at hr
  have := readN_go_size h n t #[] acc t' hr
  simpa using this

theorem tmReadN_size {T : Type} (h : Midfall.Halo2.Hashable T) (n : Nat)
    {s : Transcript} {acc : Array T} {t' : Transcript}
    (hr : (tmReadN h n).run s = .ok (acc, t')) : acc.size = n := by
  cases s with
  | mk st buf pos hash log =>
      rw [tmReadN_run_fields h st buf pos hash log n] at hr
      exact readN_size h _ n hr

theorem permReadProductCommitments_size {G₁ : Type} (perm : PermutationArgument)
    (csDegree : Nat) (h : Midfall.Halo2.Hashable G₁)
    {t : Transcript} {c : Permutation.Committed G₁} {t' : Transcript}
    (hr : (Permutation.readProductCommitments perm csDegree h).run t = .ok (c, t')) :
    c.permutationProductCommitments.size =
      Permutation.numChunksOf perm.columns.size (csDegree - 2) := by
  unfold Permutation.readProductCommitments at hr
  dsimp only at hr
  rw [Midfall.LoweringV3.run_ite] at hr
  by_cases hlen : csDegree - 2 > 0
  · rw [if_pos hlen] at hr
    obtain ⟨read, t2, hread, h2⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hr
    have hsz : read.size = Permutation.numChunksOf perm.columns.size (csDegree - 2) :=
      tmReadN_size h _ hread
    change (Except.ok (Permutation.Committed.mk read,
      t2) : Except Fault (Permutation.Committed G₁ × Transcript)) = .ok (c, t') at h2
    cases h2
    exact hsz
  · rw [if_neg hlen] at hr
    obtain ⟨u, t1, hu, _⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hr
    cases hu

theorem readCommitment_helperPolys_size {G₁ : Type} (cm : Logup.CommittedMultiplicities G₁)
    (nbChunks : Nat) (h : Midfall.Halo2.Hashable G₁)
    {t : Transcript} {c : Logup.Committed G₁} {t' : Transcript}
    (hr : (Logup.CommittedMultiplicities.readCommitment cm nbChunks h).run t = .ok (c, t')) :
    c.helperPolys.size = nbChunks := by
  unfold Logup.CommittedMultiplicities.readCommitment at hr
  obtain ⟨helpers, t1, hh, h1⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hr
  obtain ⟨acc, t2, ha, h2⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok h1
  have hsz : helpers.size = nbChunks := tmReadN_size h _ hh
  change (Except.ok (Logup.Committed.mk cm.multiplicities helpers acc,
      t2) : Except Fault (Logup.Committed G₁ × Transcript)) = .ok (c, t') at h2
  cases h2
  exact hsz

theorem foldlM_push_size {α β : Type} (l : List α) (f : α → TranscriptM β) :
    ∀ (seed : Array β) (out : Array β) (t t' : Transcript),
      (l.foldlM (fun (acc : Array β) x => do let y ← f x; pure (acc.push y)) seed).run t = .ok (out, t') →
      out.size = seed.size + l.length := by
  induction l with
  | nil =>
      intro seed out t t' h
      rw [List.foldlM_nil] at h
      cases h
      simp
  | cons a as ih =>
      intro seed out t t' h
      rw [List.foldlM_cons] at h
      obtain ⟨p, t1, hf, h1⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok h
      obtain ⟨y, t2, hfy, h2⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hf
      change (Except.ok (seed.push y, t2) :
        Except Fault (Array β × Transcript)) = .ok (p, t1) at h2
      have hp : p = seed.push y := (Prod.mk.inj (Except.ok.inj h2)).1.symm
      have ht : t1 = t2 := (Prod.mk.inj (Except.ok.inj h2)).2.symm
      subst p
      subst t1
      have hrest := ih (seed.push y) out t2 t' h1
      simp only [Array.size_push, List.length_cons] at hrest ⊢
      omega

theorem foldlM_push_prop {α β : Type} (l : List α) (f : α → TranscriptM β) (P : β → Prop)
    (hf : ∀ x t y t', (f x).run t = .ok (y, t') → P y) :
    ∀ (seed : Array β), (∀ y ∈ seed.toList, P y) →
      ∀ (out : Array β) (t t' : Transcript),
        (l.foldlM (fun (acc : Array β) x => do let y ← f x; pure (acc.push y)) seed).run t = .ok (out, t') →
        ∀ y ∈ out.toList, P y := by
  induction l with
  | nil =>
      intro seed hseed out t t' h
      rw [List.foldlM_nil] at h
      cases h
      exact hseed
  | cons a as ih =>
      intro seed hseed out t t' h
      rw [List.foldlM_cons] at h
      obtain ⟨p, t1, hstep, h1⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok h
      obtain ⟨y, t2, hfy, h2⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hstep
      change (Except.ok (seed.push y, t2) :
        Except Fault (Array β × Transcript)) = .ok (p, t1) at h2
      have hp : p = seed.push y := (Prod.mk.inj (Except.ok.inj h2)).1.symm
      have ht : t1 = t2 := (Prod.mk.inj (Except.ok.inj h2)).2.symm
      have hy : P y := hf a t y t2 hfy
      subst p
      subst t1
      apply ih (seed.push y) _ out t2 t' h1
      intro z hz
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hseed z hz
      · exact hy

theorem foldlM_push_map {α β γ : Type} (l : List α) (f : α → TranscriptM β)
    (g : α → γ) (h : β → γ)
    (hf : ∀ x t y t', (f x).run t = .ok (y, t') → h y = g x) :
    ∀ (seed : Array β) (out : Array β) (t t' : Transcript),
      (l.foldlM (fun (acc : Array β) x => do let y ← f x; pure (acc.push y)) seed).run t
        = .ok (out, t') →
      out.toList.map h = seed.toList.map h ++ l.map g := by
  induction l with
  | nil =>
      intro seed out t t' hr
      rw [List.foldlM_nil] at hr
      cases hr
      simp
  | cons a as ih =>
      intro seed out t t' hr
      rw [List.foldlM_cons] at hr
      obtain ⟨p, t1, hstep, h1⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hr
      obtain ⟨y, t2, hfy, h2⟩ := Midfall.LoweringV3.PresWidthSeq.run_bind_ok hstep
      change (Except.ok (seed.push y, t2) :
        Except Fault (Array β × Transcript)) = .ok (p, t1) at h2
      have hp : p = seed.push y := (Prod.mk.inj (Except.ok.inj h2)).1.symm
      have ht : t1 = t2 := (Prod.mk.inj (Except.ok.inj h2)).2.symm
      have hy : h y = g a := hf a t y t2 hfy
      subst p
      subst t1
      have hrest := ih (seed.push y) out t2 t' h1
      rw [hrest, Array.toList_push, List.map_append, List.map_cons, List.map_nil, hy]
      simp

theorem lift_run_ok_iff {α : Type} {e : Except Fault α} {t t' : Transcript} {a : α} :
    (StateT.lift e : TranscriptM α).run t = .ok (a, t') ↔ e = .ok a ∧ t' = t := by
  cases e with
  | error err =>
      constructor
      · intro h
        change (Except.error err : Except Fault (α × Transcript)) = .ok (a, t') at h
        cases h
      · intro h
        cases h.1
  | ok x =>
      constructor
      · intro h
        change (Except.ok (x, t) : Except Fault (α × Transcript)) = .ok (a, t') at h
        cases h
        exact ⟨rfl, rfl⟩
      · intro h
        obtain ⟨hx, ht⟩ := h
        cases hx
        cases ht
        rfl

theorem StateT_run_let {α σ : Type} {m : Type → Type} [Monad m] {β : Type}
    (x : β) (f : β → StateT σ m α) (s : σ) :
    StateT.run (let y := x; f y) s = StateT.run (f x) s := rfl

/-- The chunking of a lookup list, as an `Option` so a failure is `none`. -/
def chunkedOf {F : Type} (deg : Nat) (l : List (LogupBatchedArgument F)) :
    Option (List (LogupChunkedArgument F)) :=
  l.mapM (fun x => (x.chunkByDegree deg).toOption)

/-- A fold that reads a chunked lookup and its multiplicity and pushes the pair
    returns exactly the successive chunkings, in order. -/
theorem foldlM_chunked {F G : Type} (l : List (LogupBatchedArgument F)) (deg : Nat)
    (hg : Midfall.Halo2.Hashable G) :
    ∀ (seed : Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F))
      (seedCl : List (LogupChunkedArgument F)),
      seed.toList.map (fun p => p.2.numChunks) =
        seedCl.map LogupChunkedArgument.numChunks →
      ∀ (out : Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F))
        (t t' : Transcript),
        (l.foldlM (fun (acc : Array (Logup.CommittedMultiplicities G ×
              LogupChunkedArgument F)) (x : LogupBatchedArgument F) => do
          let chunked ← StateT.lift (x.chunkByDegree deg)
          let m ← Logup.readMultiplicities chunked hg
          pure (acc.push (m, chunked))) seed).run t = .ok (out, t') →
        ∃ cl, chunkedOf deg l = some cl ∧
          out.toList.map (fun p => p.2.numChunks) =
            (seedCl ++ cl).map LogupChunkedArgument.numChunks := by
  induction l with
  | nil =>
      intro seed seedCl hseed out t t' hr
      rw [List.foldlM_nil] at hr
      cases hr
      refine ⟨[], ?_, ?_⟩
      · simp [chunkedOf]
      · simpa using hseed
  | cons a as ih =>
      intro seed seedCl hseed out t t' hr
      rw [List.foldlM_cons] at hr
      obtain ⟨p1, t1, hstep, h1⟩ := PresWidthSeq.run_bind_ok hr
      obtain ⟨chunked, t2, hlift, h2⟩ := PresWidthSeq.run_bind_ok hstep
      obtain ⟨hchunk, ht2⟩ := lift_run_ok_iff.mp hlift
      subst ht2
      obtain ⟨m, t3, hread, h3⟩ := PresWidthSeq.run_bind_ok h2
      change (Except.ok (seed.push (m, chunked), t3) :
        Except Fault (Array (Logup.CommittedMultiplicities G ×
          LogupChunkedArgument F) × Transcript)) = .ok (p1, t1) at h3
      have hp : p1 = seed.push (m, chunked) := (Prod.mk.inj (Except.ok.inj h3)).1.symm
      have ht1 : t1 = t3 := (Prod.mk.inj (Except.ok.inj h3)).2.symm
      subst hp
      subst ht1
      have hseed' : (seed.push (m, chunked)).toList.map (fun p => p.2.numChunks)
          = (seedCl ++ [chunked]).map LogupChunkedArgument.numChunks := by
        rw [Array.toList_push, List.map_append, List.map_singleton, hseed]
        simp
      obtain ⟨cl, hmap, hout⟩ := ih (seed.push (m, chunked)) (seedCl ++ [chunked]) hseed' out t1 t' h1
      have hmap' : List.mapM (fun x => (x.chunkByDegree deg).toOption) as = some cl := by
        simpa [chunkedOf] using hmap
      refine ⟨chunked :: cl, ?_, ?_⟩
      · unfold chunkedOf
        rw [List.mapM_cons, hchunk, hmap']
        rfl
      · rw [hout]
        simp [List.append_assoc]

/-- The per-proof lookup-multiplicity rows each expose the chunk list. -/
theorem lookupMultiplicities_shape {F G : Type} (lookups : List (LogupBatchedArgument F))
    (deg n : Nat) (hg : Midfall.Halo2.Hashable G) :
    ∀ (out : Array (Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F)))
      (t t' : Transcript),
      ((List.range n).foldlM (fun (acc : Array (Array (Logup.CommittedMultiplicities G ×
            LogupChunkedArgument F))) (_ : Nat) => do
          let row ← lookups.foldlM (fun (acc' : Array (Logup.CommittedMultiplicities G ×
                LogupChunkedArgument F)) (x : LogupBatchedArgument F) => do
            let chunked ← StateT.lift (x.chunkByDegree deg)
            let m ← Logup.readMultiplicities chunked hg
            pure (acc'.push (m, chunked))) #[]
          pure (acc.push row)) #[]).run t = .ok (out, t') →
      ∀ row ∈ out.toList, ∃ cl, chunkedOf deg lookups = some cl ∧
        row.toList.map (fun p => p.2.numChunks) = cl.map LogupChunkedArgument.numChunks := by
  induction n with
  | zero =>
      intro out t t' hr row hrow
      rw [List.range_zero, List.foldlM_nil] at hr
      cases hr
      simp at hrow
  | succ n ih =>
      intro out t t' hr row hrow
      rw [List.range_succ, List.foldlM_append] at hr
      obtain ⟨mid, tmid, hfirst, hlast⟩ := PresWidthSeq.run_bind_ok hr
      rw [List.foldlM_cons] at hlast
      simp only [List.foldlM_nil] at hlast
      obtain ⟨p1, t1, hstep, hfin⟩ := PresWidthSeq.run_bind_ok hlast
      cases hfin
      obtain ⟨row', t2, hinner, hpush⟩ := PresWidthSeq.run_bind_ok hstep
      have hout : out = mid.push row' := (Prod.mk.inj (Except.ok.inj hpush)).1.symm
      have ht' : t' = t2 := (Prod.mk.inj (Except.ok.inj hpush)).2.symm
      subst out
      subst t'
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hrow
      rcases hrow with hrow | rfl
      · exact ih mid t tmid hfirst row hrow
      · exact foldlM_chunked lookups deg hg #[] [] (by simp) row tmid t2 hinner

/-- The commitment pass over one multiplicity row has exactly the helper-poly
    count of the chunked lookups, in order. -/
theorem lookupRow_commit_map {F G : Type} (h : Midfall.Halo2.Hashable G)
    (row : Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F)) :
    ∀ (out : Array (Logup.Committed G)) (t t' : Transcript),
      (row.toList.foldlM (fun (acc : Array (Logup.Committed G))
          (x : Logup.CommittedMultiplicities G × LogupChunkedArgument F) => do
        let c ← x.1.readCommitment x.2.numChunks h
        pure (acc.push c)) #[]).run t = .ok (out, t') →
      out.toList.map (fun c => c.helperPolys.size) = row.toList.map (fun x => x.2.numChunks) := by
  intro out t t' hr
  have := foldlM_push_map row.toList
    (fun x => x.1.readCommitment x.2.numChunks h)
    (fun x => x.2.numChunks) (fun c => c.helperPolys.size)
    (fun x t y t' hy => readCommitment_helperPolys_size x.1 x.2.numChunks h hy)
    #[] out t t' hr
  simpa using this

/-- The commitment pass over all rows maps each row's helper sizes to its chunk
    count list. -/
theorem commitRows_map {F G : Type} (h : Midfall.Halo2.Hashable G)
    (rows : List (Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F))) :
    ∀ (out : Array (Array (Logup.Committed G))) (t t' : Transcript),
      (rows.foldlM (fun (acc : Array (Array (Logup.Committed G)))
          (row : Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F)) => do
        let o ← row.toList.foldlM (fun (acc' : Array (Logup.Committed G))
            (x : Logup.CommittedMultiplicities G × LogupChunkedArgument F) => do
          let c ← x.1.readCommitment x.2.numChunks h
          pure (acc'.push c)) #[]
        pure (acc.push o)) #[]).run t = .ok (out, t') →
      out.toList.map (fun row => row.toList.map (fun c => c.helperPolys.size))
        = rows.map (fun row => row.toList.map (fun x => x.2.numChunks)) := by
  intro out t t' hr
  have := foldlM_push_map rows
    (fun row => row.toList.foldlM (fun (acc' : Array (Logup.Committed G))
        (x : Logup.CommittedMultiplicities G × LogupChunkedArgument F) => do
      let c ← x.1.readCommitment x.2.numChunks h
      pure (acc'.push c)) #[])
    (fun row => row.toList.map (fun x => x.2.numChunks))
    (fun row => row.toList.map (fun c => c.helperPolys.size))
    (fun row t o t' hy => lookupRow_commit_map h row o t t' hy)
    #[] out t t' hr
  simpa using this

theorem commitRows_shape {F G : Type} (deg : Nat) (lookups : List (LogupBatchedArgument F))
    (hg : Midfall.Halo2.Hashable G)
    (rows : List (Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F))) :
    (∀ row ∈ rows, ∃ cl, chunkedOf deg lookups = some cl ∧
      row.toList.map (fun x => x.2.numChunks) = cl.map LogupChunkedArgument.numChunks) →
    ∀ (seed : Array (Array (Logup.Committed G))),
      (∀ o ∈ seed.toList, ∃ cl, chunkedOf deg lookups = some cl ∧
        o.toList.map (fun c => c.helperPolys.size) = cl.map LogupChunkedArgument.numChunks) →
      ∀ (out : Array (Array (Logup.Committed G))) (t t' : Transcript),
        (rows.foldlM (fun (acc : Array (Array (Logup.Committed G)))
            (row : Array (Logup.CommittedMultiplicities G × LogupChunkedArgument F)) => do
          let o ← row.toList.foldlM (fun (acc' : Array (Logup.Committed G))
              (x : Logup.CommittedMultiplicities G × LogupChunkedArgument F) => do
            let c ← x.1.readCommitment x.2.numChunks hg
            pure (acc'.push c)) #[]
          pure (acc.push o)) seed).run t = .ok (out, t') →
        ∀ o ∈ out.toList, ∃ cl, chunkedOf deg lookups = some cl ∧
          o.toList.map (fun c => c.helperPolys.size) = cl.map LogupChunkedArgument.numChunks := by
  induction rows with
  | nil =>
      intro hrows seed hseed out t t' hr o ho
      rw [List.foldlM_nil] at hr
      cases hr
      exact hseed o ho
  | cons a as ih =>
      intro hrows seed hseed out t t' hr o ho
      rw [List.foldlM_cons] at hr
      obtain ⟨seed1, t1, hstep, h1⟩ := PresWidthSeq.run_bind_ok hr
      obtain ⟨out0, t2, hinner, hpush⟩ := PresWidthSeq.run_bind_ok hstep
      have hs1 : seed1 = seed.push out0 := (Prod.mk.inj (Except.ok.inj hpush)).1.symm
      have ht1 : t1 = t2 := (Prod.mk.inj (Except.ok.inj hpush)).2.symm
      subst seed1
      subst t1
      have hseed' : ∀ o' ∈ (seed.push out0).toList, ∃ cl,
          chunkedOf deg lookups = some cl ∧
          o'.toList.map (fun c => c.helperPolys.size) = cl.map LogupChunkedArgument.numChunks := by
        intro o' ho'
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho'
        rcases ho' with ho' | heq
        · exact hseed o' ho'
        · have ho' : o' = out0 := heq
          subst o'
          obtain ⟨cl, hcl, hrow⟩ := hrows a (by simp)
          exact ⟨cl, hcl, (lookupRow_commit_map hg a out0 _ t2 hinner).trans hrow⟩
      apply ih (fun row hrow => hrows row (by simp [hrow])) (seed.push out0) hseed'
        out t2 t' h1 o ho

theorem parseTrace_shapes {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (committed₀ : Array (Array G₁)) (inst : Array (Array (Array (Fr p))))
    {t : Transcript} {tr : VerifierTrace (Fr p) G₁} {t' : Transcript}
    (h : (parseTrace g1 feat vk committed₀ inst).run t = .ok (tr, t')) :
    tr.permutations.size = inst.size ∧
    (∀ pc ∈ tr.permutations.toList, pc.permutationProductCommitments.size =
      Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2)) ∧
    tr.lookups.size = inst.size ∧
    (∀ row ∈ tr.lookups.toList, ∃ cl : List (LogupChunkedArgument (Fr p)),
      chunkedOf vk.csDegree vk.cs.lookups.toList = some cl ∧
      row.toList.map (fun c => c.helperPolys.size) =
        cl.map LogupChunkedArgument.numChunks) ∧
    tr.trashcans.size = inst.size ∧
    (∀ row ∈ tr.trashcans.toList, row.size = vk.cs.trashcans.size) := by
  unfold parseTrace at h
  rw [StateT_run_let] at h
  set comm := (if feat.committedInstances = true then committed₀
    else Array.map (fun _ => #[]) (List.range inst.size).toArray) with hcomm
  rw [Midfall.LoweringV3.run_ite] at h
  by_cases hc1 : comm.isEmpty = true
  · simp only [hc1, if_true] at h
    obtain ⟨u1', a1', ht1, _⟩ := PresWidthSeq.run_bind_ok h
    change (Except.error (Fault.error Error.invalidInstances) :
      Except Fault (Unit × Transcript)) = .ok (u1', a1') at ht1
    cases ht1
  · simp only [hc1, if_false] at h
    rw [StateT_run_let] at h
    rw [Midfall.LoweringV3.run_ite] at h
    by_cases hc2 : comm.toList.any (fun r => r.size ≠
        (Option.map (fun r => r.size) comm[0]?).getD 0) = true
    · simp only [hc2, if_true] at h
      obtain ⟨u2', a2', ht2, _⟩ := PresWidthSeq.run_bind_ok h
      change (Except.error (Fault.error Error.invalidInstances) :
        Except Fault (Unit × Transcript)) = .ok (u2', a2') at ht2
      cases ht2
    · simp only [hc2, if_false] at h
      rw [Midfall.LoweringV3.run_ite] at h
      by_cases hc3 : ((List.zip comm.toList inst.toList).any
          fun (c, i) => c.size + i.size ≠ vk.cs.numInstanceColumns) = true
      · simp only [hc3, if_true] at h
        obtain ⟨u3', a3', ht3, _⟩ := PresWidthSeq.run_bind_ok h
        change (Except.error (Fault.error Error.invalidInstances) :
          Except Fault (Unit × Transcript)) = .ok (u3', a3') at ht3
        cases ht3
      · simp only [hc3, if_false] at h
        rw [StateT_run_let] at h
        obtain ⟨_, _, _, h1⟩ := PresWidthSeq.run_bind_ok h
        obtain ⟨_, _, _, h2⟩ := PresWidthSeq.run_bind_ok h1
        obtain ⟨_, _, _, h3⟩ := PresWidthSeq.run_bind_ok h2
        obtain ⟨_, _, _, h4⟩ := PresWidthSeq.run_bind_ok h3
        obtain ⟨_, _, _, h5⟩ := PresWidthSeq.run_bind_ok h4
        obtain ⟨_, _, _, h6⟩ := PresWidthSeq.run_bind_ok h5
        obtain ⟨_, _, _, h7⟩ := PresWidthSeq.run_bind_ok h6
        obtain ⟨lm, t8, hlm, h8⟩ := PresWidthSeq.run_bind_ok h7
        obtain ⟨_, _, _, h9⟩ := PresWidthSeq.run_bind_ok h8
        obtain ⟨_, _, _, h10⟩ := PresWidthSeq.run_bind_ok h9
        obtain ⟨perms, tp, hperm, h11⟩ := PresWidthSeq.run_bind_ok h10
        obtain ⟨lks, tl, hlks, h12⟩ := PresWidthSeq.run_bind_ok h11
        obtain ⟨_, _, _, h13⟩ := PresWidthSeq.run_bind_ok h12
        obtain ⟨trs, tt, htrs, h14⟩ := PresWidthSeq.run_bind_ok h13
        obtain ⟨_, _, _, h15⟩ := PresWidthSeq.run_bind_ok h14
        cases h15
        -- permutation row count and per-row product count
        have hpermSz := foldlM_push_size (List.range inst.size)
          (fun _ => Permutation.readProductCommitments vk.cs.permutation vk.csDegree
            (hashableG1 g1)) #[] perms _ tp hperm
        simp only [List.length_range] at hpermSz
        have hpermProp := foldlM_push_prop (List.range inst.size)
          (fun _ => Permutation.readProductCommitments vk.cs.permutation vk.csDegree
            (hashableG1 g1))
          (fun pc => pc.permutationProductCommitments.size =
            Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2))
          (fun _ _ _ _ hfy => permReadProductCommitments_size _ _ _ hfy)
          #[] (by intro y hy; simp at hy) perms _ tp hperm
        -- lookup multiplicity rows: count and chunk shape
        have hlmSz := foldlM_push_size (List.range inst.size)
          (fun _ => vk.cs.lookups.toList.foldlM
            (fun (acc' : Array (Logup.CommittedMultiplicities G₁ ×
                LogupChunkedArgument (Fr p)))
                (x : LogupBatchedArgument (Fr p)) => do
              let chunked ← StateT.lift (x.chunkByDegree vk.csDegree)
              let m ← Logup.readMultiplicities chunked (hashableG1 g1)
              pure (acc'.push (m, chunked))) #[]) #[] lm _ t8 hlm
        simp only [List.length_range] at hlmSz
        have hlmShape := lookupMultiplicities_shape vk.cs.lookups.toList vk.csDegree
          inst.size (hashableG1 g1) lm _ t8 hlm
        -- lookup commitment rows
        have hlksSz := foldlM_push_size lm.toList
          (fun row => row.toList.foldlM
            (fun (acc' : Array (Logup.Committed G₁))
                (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
              let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
              pure (acc'.push c)) #[]) #[] lks _ tl hlks
        have hlmLen : lm.toList.length = inst.size := by
          have h : lm.size = inst.size := by simpa using hlmSz
          rw [Array.length_toList]
          exact h
        have hlksSize : lks.size = inst.size := by
          have h : lks.size = lm.toList.length := by simpa using hlksSz
          rw [h]
          exact hlmLen
        have hlksShape := commitRows_shape vk.csDegree vk.cs.lookups.toList (hashableG1 g1)
          lm.toList hlmShape #[] (by intro o ho; simp at ho) lks _ tl hlks
        -- trashcan rows
        have htrsSz := foldlM_push_size (List.range inst.size)
          (fun _ => vk.cs.trashcans.toList.foldlM
            (fun (acc' : Array (Trash.Committed G₁)) (x : TrashArgument (Fr p)) => do
              let c ← Trash.readCommitted x (hashableG1 g1)
              pure (acc'.push c)) #[]) #[] trs _ tt htrs
        simp only [List.length_range] at htrsSz
        have htrsMap : ∀ row ∈ trs.toList, row.size = vk.cs.trashcans.size := by
          intro row hrow
          have hmap := foldlM_push_map (List.range inst.size)
            (fun _ => vk.cs.trashcans.toList.foldlM
              (fun (acc' : Array (Trash.Committed G₁)) (x : TrashArgument (Fr p)) => do
                let c ← Trash.readCommitted x (hashableG1 g1)
                pure (acc'.push c)) #[])
            (fun _ => vk.cs.trashcans.toList.length) (fun row => row.size)
            (fun _ t0 o t0' hy => by
              have := foldlM_push_size vk.cs.trashcans.toList
                (fun x => Trash.readCommitted x (hashableG1 g1)) #[] o _ t0' hy
              simpa using this)
            #[] trs _ tt htrs
          have hmem : row.size ∈ trs.toList.map (fun r => r.size) :=
            List.mem_map_of_mem hrow
          rw [hmap] at hmem
          simp only [List.map_nil, List.nil_append, List.map_const', List.length_range,
            Array.length_toList, List.mem_replicate] at hmem
          exact hmem.2
        exact ⟨by simpa using hpermSz, hpermProp, hlksSize, hlksShape,
          by simpa using htrsSz, htrsMap⟩

set_option maxHeartbeats 2000000

/-! ### A6 - the `parseTrace` READ schedule (the width half of `ParseTraceSchedule`)

    The parser's transcript log is exactly its reads: `vk.hashInto`, the committed
    and instance absorbs, the four challenges and the trailing `y` all go through
    `Transcript.common` / `squeeze`, neither of which touches `log`. What appends
    widths is only

      * the phase loop - one `g1` read per (phase, proof, advice column of that phase);
      * the multiplicity pass - one `g1` per (proof, lookup);
      * `Permutation.readProductCommitments` - `numChunksOf columns (csDegree - 2)` per proof;
      * the lookup-commitment pass - `numChunks + 1` per (proof, lookup);
      * the trashcan pass - one `g1` per (proof, trashcan).

    The lemmas below walk the loops one at a time; `parseTrace_widths` composes them
    on an actual run (the same bind-peeling `parseTrace_shapes` uses) and yields the
    exact count as one `replicate`. No count is assumed. -/

/-- The advice columns the parser reads while processing phase `ph`: the columns
    `i < numAdviceColumns` whose recorded phase is `ph`, in index order. -/
def advicePhaseCols {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p))
    (ph : Nat) : List Nat :=
  (List.range cs.numAdviceColumns).filterMap fun i =>
    if (cs.adviceColumnPhase[i]?.map (fun q => q.val)) == some ph then some i else none

/-- The G1 reads the phase loop performs: one per advice column, per proof. -/
def adviceReadCount {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p))
    (n : Nat) : Nat :=
  ((cs.phases.map fun ph => n * (advicePhaseCols cs ph.val).length)).sum

/-- The G1 reads the lookup-commitment pass performs: `numChunks + 1` per lookup. -/
def lookupCommitReadCount {F : Type} (deg : Nat)
    (lookups : List (LogupBatchedArgument F)) : Nat :=
  (((chunkedOf deg lookups).getD []).map (fun c => c.numChunks + 1)).sum

/-- The exact number of G1 reads `parseTrace` performs at the deployed profile
    (one proof, one committed instance). -/
def parseTraceReadCount {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) : Nat :=
  adviceReadCount vk.cs 1
    + vk.cs.lookups.size
    + Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2)
    + lookupCommitReadCount vk.csDegree vk.cs.lookups.toList
    + vk.cs.trashcans.size

/-- Dropping the trailing `[]` of a composed width. -/
theorem PresWidthSeq.nil_right {α : Type} {m : TranscriptM α} {ws : List Nat}
    (h : PresWidthSeq (ws ++ []) m) : PresWidthSeq ws m := by
  simpa using h

/-- A single read/bind followed by `pure` of a function of its value. -/
theorem PresWidthSeq.bind_pure {α β : Type} {ws : List Nat} {m : TranscriptM α}
    (hm : PresWidthSeq ws m) (f : α → β) :
    PresWidthSeq ws (m >>= fun x => StateT.pure (f x)) :=
  PresWidthSeq.nil_right (PresWidthSeq.bind (ws2 := []) hm
    (fun x => PresWidthSeq.pure (f x)))

/-- `Permutation.readProductCommitments` reads `numChunksOf columns (csDegree - 2)`
    G1 points (and throws before reading when the chunk length is zero, in which
    case no run succeeds and the width is vacuous). -/
theorem readProductCommitments_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (perm : PermutationArgument) (csDegree : Nat) :
    PresWidthSeq
      (List.replicate (Permutation.numChunksOf perm.columns.size (csDegree - 2))
        (hashableG1 g1).width)
      (Permutation.readProductCommitments perm csDegree (hashableG1 g1)) := by
  unfold Permutation.readProductCommitments
  by_cases hc : csDegree - 2 > 0
  · simp only [hc, if_true]
    exact PresWidthSeq.bind_pure (PresWidthSeq.readN (hashableG1 g1) _) _
  · simp only [hc, if_false]
    exact PresWidthSeq.bind (ws2 := List.replicate
        (Permutation.numChunksOf perm.columns.size (csDegree - 2)) (hashableG1 g1).width)
      (PresWidthSeq.throwFault (Fault.panic "proofs/src/plonk/permutation/verifier.rs:45"))
      (fun _ => PresWidthSeq.bind_pure (PresWidthSeq.readN (hashableG1 g1) _) _)

/-- `Trash.readCommitted` reads exactly one G1 point. -/
theorem trashReadCommitted_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (x : TrashArgument (Fr p)) :
    PresWidthSeq [(hashableG1 g1).width] (Trash.readCommitted x (hashableG1 g1)) := by
  unfold Trash.readCommitted
  exact PresWidthSeq.bind_pure (PresWidthSeq.read (hashableG1 g1)) _

/-- `Logup.CommittedMultiplicities.readCommitment` reads `numChunks + 1` G1 points. -/
theorem readCommitment_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (cm : Logup.CommittedMultiplicities G₁) (n : Nat) :
    PresWidthSeq (List.replicate (n + 1) (hashableG1 g1).width)
      (cm.readCommitment n (hashableG1 g1)) := by
  rw [List.replicate_succ']
  unfold Logup.CommittedMultiplicities.readCommitment
  refine PresWidthSeq.bind (ws2 := [(hashableG1 g1).width])
    (PresWidthSeq.readN (hashableG1 g1) n) (fun helperPolys => ?_)
  exact PresWidthSeq.bind_pure (PresWidthSeq.read (hashableG1 g1)) _

/-- `Logup.readMultiplicities` reads exactly one G1 point. -/
theorem readMultiplicities_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (chunked : LogupChunkedArgument (Fr p)) :
    PresWidthSeq [(hashableG1 g1).width]
      (Logup.readMultiplicities chunked (hashableG1 g1)) := by
  unfold Logup.readMultiplicities
  exact PresWidthSeq.bind_pure (PresWidthSeq.read (hashableG1 g1)) _

/-- One multiplicity row's commitment pass: exactly the sum of `numChunks + 1`. -/
theorem commitRow_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁)
    (row : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
    (c : Nat) (hc : (row.toList.map (fun x => x.2.numChunks + 1)).sum = c) :
    PresWidthSeq (List.replicate c (hashableG1 g1).width)
      (row.toList.foldlM (fun (acc' : Array (Logup.Committed G₁))
        (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
        let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
        pure (acc'.push c)) #[]) := by
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc' : Array (Logup.Committed G₁))
      (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
      let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
      pure (acc'.push c))
    (wf := fun x => List.replicate (x.2.numChunks + 1) (hashableG1 g1).width)
    (fun acc' x => PresWidthSeq.bind_pure
      (readCommitment_width (p := p) (G₁ := G₁) g1 x.1 x.2.numChunks) _)
    row.toList #[]
  rw [AlgebraWidths.flatten_map_replicate] at h
  simpa [hc] using h

/-- The whole lookup-commitment pass over the multiplicity rows. -/
theorem commitRows_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁)
    (rows : List (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :
    PresWidthSeq
      ((rows.map (fun row => List.replicate
        (row.toList.map (fun x => x.2.numChunks + 1)).sum (hashableG1 g1).width)).flatten)
      (rows.foldlM (init := #[]) (fun (acc : Array (Array (Logup.Committed G₁)))
        (row : Array (Logup.CommittedMultiplicities G₁ ×
          LogupChunkedArgument (Fr p))) => do
        let out ← row.toList.foldlM (fun (acc' : Array (Logup.Committed G₁))
          (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
          let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
          pure (acc'.push c)) #[]
        pure (acc.push out))) := by
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : Array (Array (Logup.Committed G₁)))
      (row : Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p))) => do
      let out ← row.toList.foldlM (fun (acc' : Array (Logup.Committed G₁))
        (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
        let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
        pure (acc'.push c)) #[]
      pure (acc.push out))
    (wf := fun row => List.replicate
      (row.toList.map (fun x => x.2.numChunks + 1)).sum (hashableG1 g1).width)
    (fun acc row => PresWidthSeq.bind_pure (commitRow_width g1 row _ rfl) _) rows #[]
  exact h

/-- The same pass with a single row width `c`: `rows.length * c` G1 reads. -/
theorem commitRows_width_const {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁)
    (rows : List (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) (c : Nat)
    (hc : ∀ row ∈ rows, (row.toList.map (fun x => x.2.numChunks + 1)).sum = c) :
    PresWidthSeq (List.replicate (rows.length * c) (hashableG1 g1).width)
      (rows.foldlM (init := #[]) (fun (acc : Array (Array (Logup.Committed G₁)))
        (row : Array (Logup.CommittedMultiplicities G₁ ×
          LogupChunkedArgument (Fr p))) => do
        let out ← row.toList.foldlM (fun (acc' : Array (Logup.Committed G₁))
          (x : Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)) => do
          let c ← x.1.readCommitment x.2.numChunks (hashableG1 g1)
          pure (acc'.push c)) #[]
        pure (acc.push out))) := by
  have h := commitRows_width g1 rows
  have hsum : (rows.map (fun row => (row.toList.map (fun x => x.2.numChunks + 1)).sum)).sum
      = rows.length * c := by
    clear h
    induction rows with
    | nil => simp
    | cons a as ih =>
        rw [List.map_cons, List.sum_cons, List.length_cons, hc a (by simp),
          ih (fun row hrow => hc row (by simp [hrow]))]
        ring
  have hflat :
      ((rows.map (fun row => List.replicate
        (row.toList.map (fun x => x.2.numChunks + 1)).sum (hashableG1 g1).width)).flatten)
      = List.replicate
          ((rows.map (fun row => (row.toList.map (fun x => x.2.numChunks + 1)).sum)).sum)
          (hashableG1 g1).width :=
    AlgebraWidths.flatten_map_replicate _ _ _
  rw [hflat, hsum] at h
  exact h

/-- A `for`-loop whose body reads nothing and always yields appends nothing. -/
theorem forIn_yield_width {α : Type} {g : α → PUnit → TranscriptM (ForInStep PUnit)}
    (hg : ∀ a b, PresWidthSeq [] (g a b))
    (hy : ∀ a b t r t', g a b t = .ok (r, t') → ∃ b', r = .yield b') :
    ∀ (xs : List α) (b : PUnit), PresWidthSeq [] (forIn xs b g) := by
  intro xs b
  have h := PresWidthSeq.listForIn xs b (f := g) (wf := fun _ => []) hg hy
  simpa [AlgebraWidths.flatten_map_nil] using h

/-- Array version of `forIn_yield_width`. -/
theorem arrayForIn_yield_width {α : Type} {g : α → PUnit → TranscriptM (ForInStep PUnit)}
    (hg : ∀ a b, PresWidthSeq [] (g a b))
    (hy : ∀ a b t r t', g a b t = .ok (r, t') → ∃ b', r = .yield b') :
    ∀ (xs : Array α) (b : PUnit), PresWidthSeq [] (forIn xs b g) := by
  intro xs b
  rw [← Array.forIn_toList]
  exact forIn_yield_width hg hy xs.toList b

/-- `do m; pure (.yield b)` always yields. -/
theorem yieldSeq {α : Type} (m : TranscriptM α) (b : PUnit) :
    ∀ t r t', ((m >>= fun _ => pure (ForInStep.yield b)) t = .ok (r, t')) →
      ∃ b', r = .yield b' := by
  intro t r t' hr
  exact PresWidthSeq.forIn_step_yield
    (m := m) (g := fun _ => pure (ForInStep.yield b))
    (fun a t1 r1 t1' h1 => PresWidthSeq.forIn_pure_yield _ t1 r1 t1' h1) t r t' hr

/-- A single `tmCommon` followed by `pure (.yield b)` reads nothing. -/
theorem commonYield_width {T : Type} (h : Midfall.Halo2.Hashable T) (x : T) :
    PresWidthSeq [] (do tmCommon h x; pure (ForInStep.yield PUnit.unit)) :=
  PresWidthSeq.bind_pure (PresWidthSeq.common h x) _

theorem commonYield {T : Type} (h : Midfall.Halo2.Hashable T) (x : T) :
    ∀ t r t', ((do tmCommon h x; pure (ForInStep.yield PUnit.unit)) t = .ok (r, t')) →
      ∃ b, r = .yield b := by
  intro t r t' hr
  exact yieldSeq (tmCommon h x) PUnit.unit t r t' hr

/-- The per-row body of the committed-instance absorb loop. -/
def absorbCommittedBody {T : Type} (h : Midfall.Halo2.Hashable T) (row : Array T) :
    TranscriptM (ForInStep PUnit) := do
  forIn row PUnit.unit fun x _ => do tmCommon h x; pure (ForInStep.yield PUnit.unit)
  pure (ForInStep.yield PUnit.unit)

/-- The committed-instance absorb loop (the parser's first `for`). -/
def absorbCommitted {T : Type} (h : Midfall.Halo2.Hashable T) (rows : List (Array T)) :
    TranscriptM Unit :=
  forIn rows PUnit.unit fun row _ => absorbCommittedBody h row

/-- The scalar value loop of one instance column. -/
def absorbInstColBody {p : ℕ} [Fact (Nat.Prime p)] (col : Array (Fr p)) :
    TranscriptM Unit :=
  forIn col PUnit.unit fun v _ => do
    tmCommon (hashableFr (p := p)) v; pure (ForInStep.yield PUnit.unit)

/-- One instance column: its length, then its values. -/
def absorbInstCol {p : ℕ} [Fact (Nat.Prime p)] (col : Array (Fr p)) :
    TranscriptM (ForInStep PUnit) := do
  tmCommon (hashableFr (p := p)) (Nat.cast col.size)
  absorbInstColBody col
  pure (ForInStep.yield PUnit.unit)

/-- One instance row. -/
def absorbInstRow {p : ℕ} [Fact (Nat.Prime p)] (row : Array (Array (Fr p))) :
    TranscriptM (ForInStep PUnit) := do
  forIn row PUnit.unit fun col _ => absorbInstCol col
  pure (ForInStep.yield PUnit.unit)

/-- The instance-column absorb loop (the parser's second `for`). -/
def absorbInst {p : ℕ} [Fact (Nat.Prime p)] (rows : List (Array (Array (Fr p)))) :
    TranscriptM Unit :=
  forIn rows PUnit.unit fun row _ => absorbInstRow row

theorem absorbCommittedBody_width {T : Type} (h : Midfall.Halo2.Hashable T)
    (row : Array T) : PresWidthSeq [] (absorbCommittedBody h row) := by
  unfold absorbCommittedBody
  exact PresWidthSeq.bind_pure
    (arrayForIn_yield_width (g := fun x _ => do
        tmCommon h x; pure (ForInStep.yield PUnit.unit))
      (fun x b => commonYield_width h x)
      (fun x b t r t' hr => commonYield h x t r t' hr) row PUnit.unit) _

theorem absorbCommitted_width {T : Type} (h : Midfall.Halo2.Hashable T)
    (rows : List (Array T)) : PresWidthSeq [] (absorbCommitted h rows) := by
  unfold absorbCommitted
  exact forIn_yield_width (g := fun row _ => absorbCommittedBody h row)
    (fun row b => absorbCommittedBody_width h row)
    (fun row b t r t' hr => by
      unfold absorbCommittedBody at hr
      exact yieldSeq _ _ t r t' hr) rows PUnit.unit

theorem absorbInstColBody_width {p : ℕ} [Fact (Nat.Prime p)] (col : Array (Fr p)) :
    PresWidthSeq [] (absorbInstColBody col) := by
  unfold absorbInstColBody
  rw [← Array.forIn_toList]
  exact forIn_yield_width (g := fun v _ => do
      tmCommon (hashableFr (p := p)) v; pure (ForInStep.yield PUnit.unit))
    (fun v b => commonYield_width _ v)
    (fun v b t r t' hr => commonYield _ v t r t' hr) col.toList PUnit.unit

theorem absorbInstCol_width {p : ℕ} [Fact (Nat.Prime p)] (col : Array (Fr p)) :
    PresWidthSeq [] (absorbInstCol col) := by
  unfold absorbInstCol
  exact PresWidthSeq.bind (ws2 := []) (PresWidthSeq.common _ (Nat.cast col.size))
    (fun _ => PresWidthSeq.bind_pure (absorbInstColBody_width col) _)

theorem absorbInstCol_yield {p : ℕ} [Fact (Nat.Prime p)] (col : Array (Fr p)) :
    ∀ t r t', absorbInstCol col t = .ok (r, t') → ∃ b, r = .yield b := by
  unfold absorbInstCol
  exact yieldSeq _ _

theorem absorbInstRow_width {p : ℕ} [Fact (Nat.Prime p)] (row : Array (Array (Fr p))) :
    PresWidthSeq [] (absorbInstRow row) := by
  unfold absorbInstRow
  exact PresWidthSeq.bind_pure
    (arrayForIn_yield_width (g := fun col _ => absorbInstCol col)
      (fun col b => absorbInstCol_width col)
      (fun col b t r t' hr => absorbInstCol_yield col t r t' hr) row PUnit.unit) _

theorem absorbInst_width {p : ℕ} [Fact (Nat.Prime p)]
    (rows : List (Array (Array (Fr p)))) : PresWidthSeq [] (absorbInst rows) := by
  unfold absorbInst
  exact forIn_yield_width (g := fun row _ => absorbInstRow row)
    (fun row b => absorbInstRow_width row)
    (fun row b t r t' hr => by
      unfold absorbInstRow at hr
      exact yieldSeq _ _ t r t' hr) rows PUnit.unit

/-- The per-proof advice-read fold of one phase. -/
def adviceProofFold {G₁ : Type} [Group G₁] (g1 : G1Codec G₁) (n : Nat) (cols : List Nat)
    (init : List (List (Nat × G₁))) : TranscriptM (List (List (Nat × G₁))) :=
  (List.range n).foldlM (init := init) fun acc k => do
    let reads ← tmReadN (hashableG1 g1) cols.length
    pure ((acc.take k) ++ [((acc[k]?.getD []) ++ (List.zip cols reads.toList))] ++
      (acc.drop (k + 1)))

/-- The challenge squeezes of one phase. -/
def phaseChalFold {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (ph : Nat) (init : List (Nat × Fr p)) :
    TranscriptM (List (Nat × Fr p)) :=
  (List.zip (List.range vk.cs.numChallenges) vk.cs.challengePhase.toList).foldlM
    (init := init) fun acc (e : Nat × Phase) =>
      if e.2.val == ph then do
        let c ← tmSqueezeChallenge
        pure (acc ++ [(e.1, c)])
      else pure acc

/-- One iteration of the parser's phase loop. -/
def phaseStep {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat) (ph : Phase)
    (st : List (List (Nat × G₁)) × List (Nat × Fr p)) :
    TranscriptM (List (List (Nat × G₁)) × List (Nat × Fr p)) := do
  let cols := advicePhaseCols vk.cs ph.val
  let adv ← adviceProofFold g1 n cols st.1
  let chals ← phaseChalFold vk ph.val st.2
  pure (adv, chals)

/-- The parser's phase loop. -/
def phaseFold {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : List (List (Nat × G₁)) × List (Nat × Fr p)) :
    TranscriptM (List (List (Nat × G₁)) × List (Nat × Fr p)) :=
  vk.cs.phases.foldlM (init := init) fun st ph => phaseStep g1 vk n ph st

/-- The lookup-multiplicity row of one proof. -/
def multRow {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) :
    TranscriptM (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p))) :=
  vk.cs.lookups.toList.foldlM
    (fun (acc' : Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p))) (x : LogupBatchedArgument (Fr p)) => do
      let chunked ← StateT.lift (x.chunkByDegree vk.csDegree)
      let m ← Logup.readMultiplicities chunked (hashableG1 g1)
      pure (acc'.push (m, chunked))) #[]

/-- The multiplicity pass over the proofs. -/
def multFold {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :
    TranscriptM (Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :=
  (List.range n).foldlM (init := init) fun acc _ => do
    let row ← multRow g1 vk
    pure (acc.push row)

/-- The permutation-product pass over the proofs. -/
def permFold {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Permutation.Committed G₁)) : TranscriptM (Array (Permutation.Committed G₁)) :=
  (List.range n).foldlM (init := init) fun acc _ => do
    let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
      (hashableG1 g1)
    pure (acc.push pc)

/-- The trashcan row of one proof. -/
def trashRow {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) :
    TranscriptM (Array (Trash.Committed G₁)) :=
  vk.cs.trashcans.toList.foldlM
    (fun (acc' : Array (Trash.Committed G₁)) (x : TrashArgument (Fr p)) => do
      let c ← Trash.readCommitted x (hashableG1 g1)
      pure (acc'.push c)) #[]

/-- The trashcan pass over the proofs. -/
def trashFold {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Array (Trash.Committed G₁))) : TranscriptM (Array (Array (Trash.Committed G₁))) :=
  (List.range n).foldlM (init := init) fun acc _ => do
    let row ← trashRow g1 vk
    pure (acc.push row)

theorem adviceProofFold_width {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (n : Nat) (cols : List Nat) (init : List (List (Nat × G₁))) :
    PresWidthSeq (List.replicate (n * cols.length) (hashableG1 g1).width)
      (adviceProofFold g1 n cols init) := by
  unfold adviceProofFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : List (List (Nat × G₁))) (k : Nat) => do
      let reads ← tmReadN (hashableG1 g1) cols.length
      pure ((acc.take k) ++ [((acc[k]?.getD []) ++ (List.zip cols reads.toList))] ++
        (acc.drop (k + 1))))
    (wf := fun _ => List.replicate cols.length (hashableG1 g1).width)
    (fun acc k => PresWidthSeq.bind_pure
      (PresWidthSeq.readN (hashableG1 g1) cols.length) _) (List.range n) init
  rw [AlgebraWidths.flatten_map_replicate_const, List.length_range] at h
  exact h

theorem phaseChalFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (ph : Nat) (init : List (Nat × Fr p)) :
    PresWidthSeq [] (phaseChalFold vk ph init) := by
  unfold phaseChalFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : List (Nat × Fr p)) (e : Nat × Phase) =>
      if e.2.val == ph then do
        let c ← tmSqueezeChallenge
        pure (acc ++ [(e.1, c)])
      else pure acc)
    (wf := fun _ => [])
    (fun acc e => by
      split
      · exact PresWidthSeq.bind_pure (PresWidthSeq.squeezeChallenge (p := p)) _
      · exact PresWidthSeq.pure _)
    (List.zip (List.range vk.cs.numChallenges) vk.cs.challengePhase.toList) init
  simpa [AlgebraWidths.flatten_map_nil] using h

theorem phaseStep_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat) (ph : Phase)
    (st : List (List (Nat × G₁)) × List (Nat × Fr p)) :
    PresWidthSeq (List.replicate (n * (advicePhaseCols vk.cs ph.val).length)
        (hashableG1 g1).width) (phaseStep g1 vk n ph st) := by
  unfold phaseStep
  exact PresWidthSeq.nil_right (PresWidthSeq.bind (ws2 := [])
    (adviceProofFold_width g1 n _ st.1)
    (fun adv => PresWidthSeq.bind_pure (phaseChalFold_width vk ph.val st.2) _))

theorem phaseFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : List (List (Nat × G₁)) × List (Nat × Fr p)) :
    PresWidthSeq (List.replicate (adviceReadCount vk.cs n) (hashableG1 g1).width)
      (phaseFold g1 vk n init) := by
  unfold phaseFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (st : List (List (Nat × G₁)) × List (Nat × Fr p)) (ph : Phase) =>
      phaseStep g1 vk n ph st)
    (wf := fun ph => List.replicate (n * (advicePhaseCols vk.cs ph.val).length)
      (hashableG1 g1).width)
    (fun st ph => phaseStep_width g1 vk n ph st) vk.cs.phases init
  rw [AlgebraWidths.flatten_map_replicate] at h
  exact h

theorem multRow_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) :
    PresWidthSeq (List.replicate vk.cs.lookups.toList.length (hashableG1 g1).width)
      (multRow g1 vk) := by
  unfold multRow
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc' : Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p))) (x : LogupBatchedArgument (Fr p)) => do
      let chunked ← StateT.lift (x.chunkByDegree vk.csDegree)
      let m ← Logup.readMultiplicities chunked (hashableG1 g1)
      pure (acc'.push (m, chunked)))
    (wf := fun _ => [(hashableG1 g1).width])
    (fun acc' x => PresWidthSeq.bind (ws2 := [(hashableG1 g1).width])
      (PresWidthSeq.lift (x.chunkByDegree vk.csDegree))
      (fun chunked => PresWidthSeq.bind_pure (readMultiplicities_width g1 chunked) _))
    vk.cs.lookups.toList #[]
  simpa [AlgebraWidths.flatten_map_single] using h

theorem multFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Array (Logup.CommittedMultiplicities G₁ ×
      LogupChunkedArgument (Fr p)))) :
    PresWidthSeq (List.replicate (n * vk.cs.lookups.toList.length) (hashableG1 g1).width)
      (multFold g1 vk n init) := by
  unfold multFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : Array (Array (Logup.CommittedMultiplicities G₁ ×
        LogupChunkedArgument (Fr p)))) (_ : Nat) => do
      let row ← multRow g1 vk
      pure (acc.push row))
    (wf := fun _ => List.replicate vk.cs.lookups.toList.length (hashableG1 g1).width)
    (fun acc _ => PresWidthSeq.bind_pure (multRow_width g1 vk) _) (List.range n) init
  rw [AlgebraWidths.flatten_map_replicate_const, List.length_range] at h
  exact h

theorem permFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Permutation.Committed G₁)) :
    PresWidthSeq
      (List.replicate (n * Permutation.numChunksOf vk.cs.permutation.columns.size
        (vk.csDegree - 2)) (hashableG1 g1).width)
      (permFold g1 vk n init) := by
  unfold permFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : Array (Permutation.Committed G₁)) (_ : Nat) => do
      let pc ← Permutation.readProductCommitments vk.cs.permutation vk.csDegree
        (hashableG1 g1)
      pure (acc.push pc))
    (wf := fun _ => List.replicate (Permutation.numChunksOf vk.cs.permutation.columns.size
      (vk.csDegree - 2)) (hashableG1 g1).width)
    (fun acc _ => PresWidthSeq.bind_pure
      (readProductCommitments_width (p := p) (G₁ := G₁) g1 vk.cs.permutation vk.csDegree) _)
    (List.range n) init
  rw [AlgebraWidths.flatten_map_replicate_const, List.length_range] at h
  exact h

theorem trashRow_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) :
    PresWidthSeq (List.replicate vk.cs.trashcans.toList.length (hashableG1 g1).width)
      (trashRow g1 vk) := by
  unfold trashRow
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc' : Array (Trash.Committed G₁)) (x : TrashArgument (Fr p)) => do
      let c ← Trash.readCommitted x (hashableG1 g1)
      pure (acc'.push c))
    (wf := fun _ => [(hashableG1 g1).width])
    (fun acc' x => PresWidthSeq.bind_pure (trashReadCommitted_width g1 x) _)
    vk.cs.trashcans.toList #[]
  simpa [AlgebraWidths.flatten_map_single] using h

theorem trashFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (n : Nat)
    (init : Array (Array (Trash.Committed G₁))) :
    PresWidthSeq (List.replicate (n * vk.cs.trashcans.size) (hashableG1 g1).width)
      (trashFold g1 vk n init) := by
  unfold trashFold
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : Array (Array (Trash.Committed G₁))) (_ : Nat) => do
      let row ← trashRow g1 vk
      pure (acc.push row))
    (wf := fun _ => List.replicate vk.cs.trashcans.toList.length (hashableG1 g1).width)
    (fun acc _ => PresWidthSeq.bind_pure (trashRow_width g1 vk) _) (List.range n) init
  rw [AlgebraWidths.flatten_map_replicate_const, List.length_range] at h
  exact h

/-- A row's commitment-pass width from the chunking data. -/
theorem commitRowSum_eq {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (row : Array (Logup.CommittedMultiplicities G₁ × LogupChunkedArgument (Fr p)))
    (cl : List (LogupChunkedArgument (Fr p)))
    (h : row.toList.map (fun x => x.2.numChunks) = cl.map LogupChunkedArgument.numChunks) :
    (row.toList.map (fun x => x.2.numChunks + 1)).sum
      = (cl.map (fun c => c.numChunks + 1)).sum := by
  have := congrArg (fun l => (l.map (fun n => n + 1)).sum) h
  simpa [List.map_map, Function.comp_def] using this

/-- The advice-commitment scatter fold reads nothing. -/
theorem advPairsFold_width {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (pairs : List (List (Nat × G₁))) :
    PresWidthSeq [] (pairs.foldlM (init := #[]) fun (acc : Array (Array G₁))
      (row : List (Nat × G₁)) => do
        let placed ← StateT.lift (scatterIndexed vk.cs.numAdviceColumns row
          "proofs/src/plonk/verifier.rs:118")
        pure (acc.push placed)) := by
  have h := PresWidthSeq.listFoldlM
    (f := fun (acc : Array (Array G₁)) (row : List (Nat × G₁)) => do
      let placed ← StateT.lift (scatterIndexed vk.cs.numAdviceColumns row
        "proofs/src/plonk/verifier.rs:118")
      pure (acc.push placed))
    (wf := fun _ => [])
    (fun acc row => PresWidthSeq.bind_pure (PresWidthSeq.lift _) _) pairs #[]
  simpa [AlgebraWidths.flatten_map_nil] using h

/-- A `throw` has no successful run. -/
theorem throw_run_ne {α : Type} (f : Fault) (t : Transcript) (b : α × Transcript) :
    (MonadExcept.throw f : TranscriptM α).run t ≠ .ok b := by
  intro h
  change (Except.error f : Except Fault (α × Transcript)) = .ok b at h
  cases h

/-- A throwing program has any width sequence (it has no successful run). -/
theorem PresWidthSeq.throwFault' {α : Type} (ws : List Nat) (f : Fault) :
    PresWidthSeq ws (MonadExcept.throw f : TranscriptM α) := by
  intro t t' a h
  change (Except.error f : Except Fault (α × Transcript)) = .ok (a, t') at h
  cases h

/-- **THE `parseTrace` WIDTH WALK.** At the deployed profile (one committed
    instance, one proof row) every read `parseTrace` performs appends one `g1`
    width, and the whole run appends `parseTraceReadCount` of them, in order:
    advice columns, multiplicities, permutation products, lookup commitments,
    trashcans. Absorbs (`tmCommon`) and squeezes do not log. This is the proved
    width half of `ParseTraceSchedule`; the count identification against
    `prefixG1Count` is `parseTraceSchedule_of_prefixG1Count`. -/
theorem parseTrace_widths {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (g1 : G1Codec G₁) (vk : VerifyingKey (Fr p) G₁) (x : G₁) (row : Array (Fr p))
    {tr : VerifierTrace (Fr p) G₁} {t t' : Transcript}
    (h : (parseTrace g1 Features.solidity vk #[#[x]] #[#[row]]).run t = .ok (tr, t')) :
    t'.log.toList.map (fun r => r.1) = t.log.toList.map (fun r => r.1) ++
      List.replicate (parseTraceReadCount vk) (hashableG1 g1).width := by
  unfold parseTrace at h
  rw [StateT_run_let] at h
  simp only [Features.solidity, if_true] at h
  by_cases hc1 : ((#[#[x]] : Array (Array G₁)).isEmpty = true)
  · simp at hc1
  rw [if_neg hc1] at h
  by_cases hc2 : (((#[#[x]] : Array (Array G₁)).toList.any
    fun r => r.size ≠ (Option.map (fun r => r.size)
      ((#[#[x]] : Array (Array G₁))[0]?)).getD 0) = true)
  · simp at hc2
  rw [if_neg hc2] at h
  by_cases hc3 : ((((#[#[x]] : Array (Array G₁)).toList.zip
    ([#[row]] : List (Array (Array (Fr p))))).any
      fun q => q.1.size + q.2.size ≠ vk.cs.numInstanceColumns) = true)
  · rw [if_pos hc3] at h
    obtain ⟨a1, t1, hbad, _⟩ := PresWidthSeq.run_bind_ok h
    exact absurd hbad (throw_run_ne _ _ _)
  rw [if_neg hc3] at h
  have hsize : (#[#[row]] : Array (Array (Array (Fr p)))).size = 1 := rfl
  -- peel the fifteen binds
  obtain ⟨_, t1, h1, h2⟩ := PresWidthSeq.run_bind_ok h
  obtain ⟨_, t2, hAbs1, h3⟩ := PresWidthSeq.run_bind_ok h2
  obtain ⟨_, t3, hAbs2, h4⟩ := PresWidthSeq.run_bind_ok h3
  obtain ⟨advPairs, t4, hPhase, h5⟩ := PresWidthSeq.run_bind_ok h4
  obtain ⟨_, t5, hAdv, h6⟩ := PresWidthSeq.run_bind_ok h5
  obtain ⟨_, t6, hChal, h7⟩ := PresWidthSeq.run_bind_ok h6
  obtain ⟨_, t7, hTheta, h8⟩ := PresWidthSeq.run_bind_ok h7
  obtain ⟨lm, t8, hMul, h9⟩ := PresWidthSeq.run_bind_ok h8
  obtain ⟨_, t9, hBeta, h10⟩ := PresWidthSeq.run_bind_ok h9
  obtain ⟨_, t10, hGamma, h11⟩ := PresWidthSeq.run_bind_ok h10
  obtain ⟨_, t11, hPerm, h12⟩ := PresWidthSeq.run_bind_ok h11
  obtain ⟨lks, t12, hLks, h13⟩ := PresWidthSeq.run_bind_ok h12
  obtain ⟨_, t13, hTrChal, h14⟩ := PresWidthSeq.run_bind_ok h13
  obtain ⟨_, t14, hTrash, h15⟩ := PresWidthSeq.run_bind_ok h14
  obtain ⟨_, t15, hY, h16⟩ := PresWidthSeq.run_bind_ok h15
  have ht' : t15 = t' := (Prod.mk.inj (Except.ok.inj h16)).2
  -- the per-step log equations
  have e1 : t1.log.toList.map (fun r => r.1)
      = t.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.common _ _ t t1 _ h1
  have e2 : t2.log.toList.map (fun r => r.1)
      = t1.log.toList.map (fun r => r.1) ++ [] :=
    absorbCommitted_width _ _ t1 t2 _ hAbs1
  have e3 : t3.log.toList.map (fun r => r.1)
      = t2.log.toList.map (fun r => r.1) ++ [] :=
    absorbInst_width _ t2 t3 _ hAbs2
  have e4 : t4.log.toList.map (fun r => r.1)
      = t3.log.toList.map (fun r => r.1) ++
        List.replicate (adviceReadCount vk.cs 1) (hashableG1 g1).width :=
    phaseFold_width g1 vk 1 _ t3 t4 _ hPhase
  have e5 : t5.log.toList.map (fun r => r.1)
      = t4.log.toList.map (fun r => r.1) ++ [] :=
    advPairsFold_width vk advPairs.1 t4 t5 _ hAdv
  have e6 : t6.log.toList.map (fun r => r.1)
      = t5.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.lift _ t5 t6 _ hChal
  have e7 : t7.log.toList.map (fun r => r.1)
      = t6.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.squeezeChallenge (p := p) t6 t7 _ hTheta
  have e8 : t8.log.toList.map (fun r => r.1)
      = t7.log.toList.map (fun r => r.1) ++
        List.replicate vk.cs.lookups.toList.length (hashableG1 g1).width := by
    simpa using multFold_width g1 vk 1 _ t7 t8 _ hMul
  have e9 : t9.log.toList.map (fun r => r.1)
      = t8.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.squeezeChallenge (p := p) t8 t9 _ hBeta
  have e10 : t10.log.toList.map (fun r => r.1)
      = t9.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.squeezeChallenge (p := p) t9 t10 _ hGamma
  have e11 : t11.log.toList.map (fun r => r.1)
      = t10.log.toList.map (fun r => r.1) ++
        List.replicate (Permutation.numChunksOf vk.cs.permutation.columns.size
          (vk.csDegree - 2)) (hashableG1 g1).width := by
    simpa using permFold_width g1 vk 1 _ t10 t11 _ hPerm
  -- the multiplicity rows: one row, chunking fixed by `lookupMultiplicities_shape`
  have hlmSize : lm.toList.length = 1 := by
    have := foldlM_push_size (List.range 1) (fun (_ : Nat) => multRow g1 vk)
      #[] lm t7 t8 (by simpa [multFold, multRow, hsize] using hMul)
    simpa using this
  have hshape := lookupMultiplicities_shape vk.cs.lookups.toList vk.csDegree 1
    (hashableG1 g1) lm t7 t8 (by simpa [multFold, multRow, hsize] using hMul)
  have hc : ∀ row ∈ lm.toList,
      (row.toList.map (fun x => x.2.numChunks + 1)).sum
        = lookupCommitReadCount vk.csDegree vk.cs.lookups.toList := by
    intro row hrow
    obtain ⟨cl, hcl, hrowcl⟩ := hshape row hrow
    rw [lookupCommitReadCount]
    simp only [hcl, Option.getD_some]
    exact commitRowSum_eq row cl hrowcl
  have e12 : t12.log.toList.map (fun r => r.1)
      = t11.log.toList.map (fun r => r.1) ++
        List.replicate (lm.toList.length *
          lookupCommitReadCount vk.csDegree vk.cs.lookups.toList)
          (hashableG1 g1).width :=
    commitRows_width_const g1 lm.toList _ hc t11 t12 _ hLks
  have e13 : t13.log.toList.map (fun r => r.1)
      = t12.log.toList.map (fun r => r.1) ++ [] :=
    PresWidthSeq.squeezeChallenge (p := p) t12 t13 _ hTrChal
  have e14 : t14.log.toList.map (fun r => r.1)
      = t13.log.toList.map (fun r => r.1) ++
        List.replicate vk.cs.trashcans.size (hashableG1 g1).width := by
    simpa using trashFold_width g1 vk 1 _ t13 t14 _ hTrash
  have e15 : t'.log.toList.map (fun r => r.1)
      = t14.log.toList.map (fun r => r.1) ++ [] := by
    rw [← ht']
    exact PresWidthSeq.squeezeChallenge (p := p) t14 t15 _ hY
  rw [hlmSize, Nat.one_mul] at e12
  rw [e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]
  -- collapse the concatenation of `replicate`s into the single total count
  unfold parseTraceReadCount
  simp only [List.nil_append, List.append_nil, List.append_assoc,
    List.replicate_append_replicate, Array.length_toList]

theorem option_mapM_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → l'.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases h
      rfl
  | cons a as ih =>
      intro l' h
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => rw [ha] at h; cases h
      | some b =>
          rw [ha] at h
          cases hrest : as.mapM f with
          | none => rw [hrest] at h; cases h
          | some l0 =>
              rw [hrest] at h
              injection h with h
              subst h
              simp only [List.length_cons]
              rw [ih l0 hrest]

theorem chunkedOf_length {F : Type} (deg : Nat) (l : List (LogupBatchedArgument F))
    {cl : List (LogupChunkedArgument F)} (h : chunkedOf deg l = some cl) :
    cl.length = l.length := by
  unfold chunkedOf at h
  exact option_mapM_length _ l cl h

theorem sumNat_eq_sum (l : List Nat) : Midfall.Lowering.sumNat l = l.sum := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [Midfall.Lowering.sumNat_cons, List.sum_cons, ih]

theorem map_add_three_map {α : Type} (l : List α) (f : α → Nat) :
    (l.map f).map (fun x => x + 3) = l.map (fun x => f x + 3) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- The lookup eval count implied by the chunking: `nbChunks + 3` per lookup. -/
def lookupEvalCount {F : Type} (deg : Nat) (lookups : List (LogupBatchedArgument F)) : Nat :=
  (((chunkedOf deg lookups).getD []).map (fun c => c.numChunks + 3)).sum

theorem lookupEvalCount_eq {F : Type} (deg : Nat) (lookups : List (LogupBatchedArgument F))
    (cl : List (LogupChunkedArgument F)) (h : chunkedOf deg lookups = some cl) :
    lookupEvalCount deg lookups = (cl.map (fun c => c.numChunks + 3)).sum := by
  simp [lookupEvalCount, h]

/-- **The per-argument eval count of a parsed trace.** For the deployed profile
    (committed instances on, one proof, one committed instance row), the
    verifier's eval count is the seven-group sum: committed-instance queries,
    advice queries, the fixed (non-simple-selector) queries, permutation-common
    evals, `3 k - 1` for the product sets, `nbChunks + 3` per lookup, and one
    trash eval per trashcan. -/
theorem readAlgebraEvalCount_parseTrace {G₁ : Type} (g1 : G1Codec G₁)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (xc : G₁) (inst : Array (Fr p))
    {t : Transcript} {tr : VerifierTrace (Fr p) G₁} {t' : Transcript}
    (h : (parseTrace g1 Features.solidity vk #[#[xc]] #[#[inst.toList.toArray]]).run t
      = .ok (tr, t')) :
    readAlgebraEvalCount vk tr.permutations tr.lookups tr.trashcans 1 1
        #[#[inst.toList.toArray]]
      = (vk.cs.instanceQueries.toList.filter (fun q => q.1.index < 1)).length
        + vk.cs.adviceQueries.size
        + (vk.cs.numFixedColumns - vk.cs.numSimpleSelectors)
        + vk.permutation.commitments.size
        + (3 * Permutation.numChunksOf vk.cs.permutation.columns.size
            (vk.csDegree - 2) - 1)
        + lookupEvalCount vk.csDegree vk.cs.lookups.toList
        + vk.cs.trashcans.size := by
  obtain ⟨hpermN, hpermP, hlksN, hlksShape, htrsN, htrsMap⟩ :=
    parseTrace_shapes g1 Features.solidity vk #[#[xc]] #[#[inst.toList.toArray]] h
  have hpermN' : tr.permutations.size = 1 := by simpa using hpermN
  have hlksN' : tr.lookups.size = 1 := by simpa using hlksN
  have htrsN' : tr.trashcans.size = 1 := by simpa using htrsN
  have hone : (#[#[inst.toList.toArray]] : Array (Array (Array (Fr p)))).size = 1 := rfl
  unfold readAlgebraEvalCount
  rw [hone]
  simp only [Nat.one_mul, List.length_singleton]
  -- permutations: one product set
  obtain ⟨pc, hpc⟩ := Array.size_eq_one_iff.mp hpermN'
  rw [hpc] at hpermP ⊢
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hpermP pc (by simp)]
  -- lookups: one row
  obtain ⟨row, hrow⟩ := Array.size_eq_one_iff.mp hlksN'
  rw [hrow] at hlksShape ⊢
  obtain ⟨cl, hcl, hclmap⟩ := hlksShape row (by simp)
  have hrowmap : row.toList.map (fun l => l.helperPolys.size + 3)
      = cl.map (fun c => c.numChunks + 3) := by
    conv_rhs => rw [← map_add_three_map]
    rw [← hclmap]
    rw [map_add_three_map]
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrowmap]
  rw [lookupEvalCount_eq vk.csDegree vk.cs.lookups.toList cl hcl]
  -- trashcans: one row
  obtain ⟨rowT, hrowT⟩ := Array.size_eq_one_iff.mp htrsN'
  rw [hrowT] at htrsMap ⊢
  rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [htrsMap rowT (by simp)]
  omega

theorem zip_range_snd_map {α : Type} (l : List α) (f : α → Nat) :
    ((List.range l.length).zip l).map (fun p => f p.2) = l.map f := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons]
      rw [List.zip_map_left, List.map_map]
      simp only [Function.comp_def, Prod.map, id_eq]
      rw [ih]
      rfl

theorem lookup_evals_length (chunks : List Nat) :
    (((List.range chunks.length).zip chunks).map (fun p => 1 + p.2 + 2)).sum
      = (chunks.map (fun c => c + 3)).sum := by
  rw [zip_range_snd_map chunks (fun c => 1 + c + 2)]
  congr 1
  apply List.map_congr_left
  intro c _
  omega

theorem sum_range_three (n : Nat) :
    ((List.range n).map (fun s => if s + 1 != n then 3 else 2)).sum = 3 * n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton]
      simp only [List.sum_cons, List.sum_nil]
      have hmap : (List.range m).map (fun s => if s + 1 != m + 1 then 3 else 2)
          = List.replicate m 3 := by
        have hlen : List.replicate m 3 = List.replicate (List.range m).length 3 := by
          rw [List.length_range]
        rw [hlen, List.map_eq_replicate_iff]
        intro s hs
        have hlt : s < m := List.mem_range.mp hs
        have hne : s ≠ m := by omega
        simp [hne]
      rw [hmap, List.sum_replicate_nat]
      simp
      omega

theorem permZ_evals_length {γ : Type} (n : Nat) (f g h : Nat → γ) :
    ((((List.range n).map (fun s => ([f s, g s] : List γ) ++
        (if s + 1 != n then [h s] else [])))).flatten).length = 3 * n - 1 := by
  rw [List.length_flatten, List.map_map]
  have hmap : ((List.range n).map ((fun l : List γ => l.length) ∘
      (fun s => ([f s, g s] : List γ) ++ (if s + 1 != n then [h s] else []))))
      = (List.range n).map (fun s => if s + 1 != n then 3 else 2) := by
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_def, List.length_append, List.length_cons, List.length_nil]
    split <;> simp
  rw [hmap, sum_range_three]


/-- **The protocol eval-list decomposition (seven groups).** The proof reads:
    the eval reads of a successfully validated plan are exactly
    `committedInstance ++ advice ++ fixed ++ permutationCommon ++
    permutationZ ++ lookup ++ trash`, with lengths

    * committed-instance queries: the filtered `instanceQueries`;
    * advice queries: `adviceQueries.length`;
    * fixed queries: `numFixeds - simpleSelectorCols.length`, which is the I-6
      assert inside `fromConstraintSystem` (`PM:461-475`) -- the same count
      `validate` leaves in the read list, since its own check only excludes
      simple-selector columns from `.fixed` reads;
    * permutation-common: one per permutation column;
    * permutation sets: `3 k - 1` per product set (`Nat` subtraction makes the
      `k = 0` case `0`, which is the constructed list's length);
    * lookups: `nbChunks + 3` per lookup argument (multiplicity, helpers,
      two accumulators);
    * trash: one per trashcan.

    Nothing is assumed about `cs`: the plan is the constructor's output, so its
    fields are read off the same `let`s the constructor bound. -/
theorem fromConstraintSystem_evals_length {F : Type} (feat : Features) (cs : ConstraintSystem F)
    (nb : Nat) {plan : ProtocolPlan}
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok plan) :
    plan.proof.evals.length =
      (plan.instanceQueries.filter (fun q => q.column < plan.numCommittedInstances)).length
      + plan.adviceQueries.length
      + (plan.numFixeds - plan.simpleSelectorCols.length)
      + plan.permutationColumns.length
      + (3 * plan.numPermutationZs - 1)
      + (plan.lookupChunks.map (fun c => c + 3)).sum
      + plan.numTrashcans := by
  unfold ProtocolPlan.fromConstraintSystem at h
  simp only [Bind.bind] at h
  obtain ⟨csDegree, _hdeg, h1⟩ := AlgebraWidths.except_bind_ok h
  obtain ⟨lookupChunks, _hlu, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨_x1, _hr1, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨_x2, _hr2, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨_bl, _hbl, h5⟩ := AlgebraWidths.except_bind_ok h4
  split at h5
  · rename_i hfix
    split at h5
    · cases h5
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_flatten, List.length_replicate]
      -- the fixed-eval guard
      have hfixEq : (List.filter
          (fun q => !decide (q.column ∈
            List.filter (fun idx => cs.hasSimpleSelectorCol idx) (List.range cs.numFixedColumns)))
          (List.map (fun x => QueryKey.new x.1.index x.2.int) cs.fixedQueries.toList)).length
          = cs.numFixedColumns -
            (List.filter (fun idx => cs.hasSimpleSelectorCol idx)
              (List.range cs.numFixedColumns)).length := by
        simpa using hfix
      -- permutation-z group lengths
      have hpermZ : (List.map List.length
          (List.map (fun set =>
            [EvalRead.permutationZ set PermutationZEval.cur,
              EvalRead.permutationZ set PermutationZEval.next] ++
              if (set + 1 != if cs.permutation.getColumns.toList.isEmpty = true then 0
                  else divCeil cs.permutation.getColumns.toList.length (csDegree - 2)) = true
              then [EvalRead.permutationZ set PermutationZEval.last] else [])
            (List.range (if cs.permutation.getColumns.toList.isEmpty = true then 0
              else divCeil cs.permutation.getColumns.toList.length (csDegree - 2))))).sum
          = 3 * (if cs.permutation.getColumns.toList.isEmpty = true then 0
              else divCeil cs.permutation.getColumns.toList.length (csDegree - 2)) - 1 := by
        rw [← List.length_flatten]
        exact permZ_evals_length _ _ _ _
      -- lookup group lengths
      have hlook : (List.map List.length
          (List.map (fun x =>
            [EvalRead.lookupMultiplicity x.1] ++
              List.map (fun chunk => EvalRead.lookupHelper x.1 chunk) (List.range x.2) ++
              [EvalRead.lookupAccumulator x.1 0, EvalRead.lookupAccumulator x.1 1])
            ((List.range lookupChunks.toList.length).zip lookupChunks.toList))).sum
          = (lookupChunks.toList.map (fun c => c + 3)).sum := by
        rw [List.map_map]
        have hstep : (List.map ((fun l : List EvalRead => l.length) ∘
            (fun x => [EvalRead.lookupMultiplicity x.1] ++
              List.map (fun chunk => EvalRead.lookupHelper x.1 chunk) (List.range x.2) ++
              [EvalRead.lookupAccumulator x.1 0, EvalRead.lookupAccumulator x.1 1]))
            ((List.range lookupChunks.toList.length).zip lookupChunks.toList))
            = (List.map (fun p => 1 + p.2 + 2)
              ((List.range lookupChunks.toList.length).zip lookupChunks.toList)) := by
          apply List.map_congr_left
          intro p _
          simp only [Function.comp_def, List.length_append, List.length_map, List.length_range,
            List.length_cons, List.length_nil]
        rw [hstep, lookup_evals_length]
      rw [hfixEq, hpermZ, hlook, List.length_range]
    · cases h5
  · cases h5

theorem mapM_map_opt {α β γ : Type} (f : α → Option β) (g : β → γ) (l : List α) :
    l.mapM (fun x => (f x).map g) = (l.mapM f).map (List.map g) := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.mapM_cons, ih, List.mapM_cons]
      cases h : f a with
      | none => simp [h]
      | some b =>
          cases h2 : as.mapM f with
          | none => simp [h, h2]
          | some l0 => simp [h, h2]

theorem except_toOption_map {ε α β : Type} (e : Except ε α) (g : α → β) :
    (e.map g).toOption = (e.toOption).map g := by
  cases e <;> rfl

theorem mapM_map_some {α β γ : Type} (f : α → Except Fault β) (g : β → γ) :
    ∀ (l : List α) (l' : List γ),
      l.mapM (fun x => ((f x).map g).toOption) = some l' →
      ∃ l0, l.mapM (fun x => (f x).toOption) = some l0 ∧ l' = l0.map g := by
  intro l l' h
  have h' : l.mapM (fun x => ((f x).toOption).map g) = some l' := by
    simpa only [except_toOption_map] using h
  rw [mapM_map_opt (fun x => (f x).toOption) g l] at h'
  cases hm : l.mapM (fun x => (f x).toOption) with
  | none => rw [hm] at h'; cases h'
  | some l0 => rw [hm] at h'; simp only [Option.map_some, Option.some.injEq] at h'
               exact ⟨l0, rfl, h'.symm⟩

theorem mapExceptArray_go_chunkN {F : Type} (deg : Nat) :
    ∀ (xs : List (LogupBatchedArgument F)) (acc out : Array Nat),
      mapExceptArray.go (fun x => (x.chunkByDegree deg).map LogupChunkedArgument.numChunks)
          xs acc = .ok out →
      ∃ l, xs.mapM (fun x => ((x.chunkByDegree deg).map LogupChunkedArgument.numChunks).toOption)
          = some l ∧ out.toList = acc.toList ++ l := by
  intro xs
  induction xs with
  | nil =>
      intro acc out h
      cases h
      exact ⟨[], by simp, by simp⟩
  | cons x rest ih =>
      intro acc out h
      simp only [mapExceptArray.go] at h
      obtain ⟨y, hf, hgo⟩ := AlgebraWidths.except_bind_ok h
      obtain ⟨l, hmap, hout⟩ := ih (acc.push y) out hgo
      refine ⟨y :: l, ?_, ?_⟩
      · rw [List.mapM_cons, hf, hmap]
        rfl
      · rw [hout, Array.toList_push]
        simp [List.append_assoc]

theorem mapExceptArray_chunk {F : Type} (deg : Nat) (xs : Array (LogupBatchedArgument F))
    {out : Array Nat}
    (h : mapExceptArray (fun x => (x.chunkByDegree deg).map LogupChunkedArgument.numChunks)
      xs = .ok out) :
    ∃ cl, chunkedOf deg xs.toList = some cl ∧
      out.toList = cl.map LogupChunkedArgument.numChunks := by
  have hgo := h
  unfold mapExceptArray at hgo
  obtain ⟨l, hmap, hout⟩ := mapExceptArray_go_chunkN deg xs.toList #[] out hgo
  obtain ⟨cl, hcl, hl⟩ := mapM_map_some (fun x => x.chunkByDegree deg)
    LogupChunkedArgument.numChunks xs.toList l hmap
  exact ⟨cl, hcl, by rw [hout]; simpa using hl⟩


theorem divCeil_zero (k : Nat) : divCeil 0 k = 0 := by
  unfold divCeil
  cases k <;> simp

theorem if_list_isEmpty_divCeil {α : Type} (l : List α) (k : Nat) :
    (if l.isEmpty = true then 0 else divCeil l.length k) = divCeil l.length k := by
  by_cases h : l.isEmpty = true
  · rw [if_pos h]
    have hnil : l = [] := by
      cases l with
      | nil => rfl
      | cons a as => simp at h
    rw [hnil]
    simp [divCeil_zero]
  · rw [if_neg h]

set_option maxHeartbeats 8000000 in
theorem validate_numSimpleSelectors {plan : ProtocolPlan} {u : Unit}
    (h : plan.validate = .ok u) : plan.numSimpleSelectors = plan.simpleSelectorCols.length := by
  by_contra hne
  have hb : (plan.numSimpleSelectors != plan.simpleSelectorCols.length) = true := by
    rw [bne_iff_ne]; exact hne
  unfold ProtocolPlan.validate at h
  dsimp only at h
  rw [hb] at h
  simp only [if_true] at h
  cases h


set_option maxHeartbeats 8000000 in
theorem readAlgebraEvalCount_parseTrace_eq_numMainEvals {G₁ : Type} (g1 : G1Codec G₁)
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity)
    (xc : G₁) (inst : Array (Fr p)) {plan : ProtocolPlan}
    (hplan : ProtocolPlan.fromConstraintSystem Features.solidity vk.cs 1 = .ok plan)
    {t : Transcript} {tr : VerifierTrace (Fr p) G₁} {t' : Transcript}
    (h : (parseTrace g1 Features.solidity vk #[#[xc]] #[#[inst.toList.toArray]]).run t
      = .ok (tr, t')) :
    readAlgebraEvalCount vk tr.permutations tr.lookups tr.trashcans 1 1
        #[#[inst.toList.toArray]]
      = plan.numMainEvals := by
  rw [readAlgebraEvalCount_parseTrace g1 vk hf xc inst h]
  change _ = plan.proof.evals.length
  rw [fromConstraintSystem_evals_length Features.solidity vk.cs 1 hplan]
  unfold ProtocolPlan.fromConstraintSystem at hplan
  simp only [Bind.bind] at hplan
  obtain ⟨csDegree, hdeg, hp1⟩ := AlgebraWidths.except_bind_ok hplan
  obtain ⟨lookupChunks, hlu, hp2⟩ := AlgebraWidths.except_bind_ok hp1
  obtain ⟨_x1, _hr1, hp3⟩ := AlgebraWidths.except_bind_ok hp2
  obtain ⟨_x2, _hr2, hp4⟩ := AlgebraWidths.except_bind_ok hp3
  obtain ⟨_bl, _hbl, hp5⟩ := AlgebraWidths.except_bind_ok hp4
  split at hp5
  · rename_i hfix
    split at hp5
    · rename_i hval
      cases hp5
      dsimp only
      have hns : vk.cs.numSimpleSelectors =
          (List.filter (fun idx => vk.cs.hasSimpleSelectorCol idx)
            (List.range vk.cs.numFixedColumns)).length :=
        validate_numSimpleSelectors hval
      have hdegEq : csDegree = vk.csDegree := by
        simp only [hf.csDegreeMatches] at hdeg
        exact (Except.ok.inj hdeg).symm
      obtain ⟨cl, hcl, hchunks⟩ := mapExceptArray_chunk csDegree vk.cs.lookups hlu
      rw [hdegEq] at hcl
      rw [hns]
      rw [hf.permutationCommitmentsMatch]
      rw [hdegEq]
      rw [if_list_isEmpty_divCeil (vk.cs.permutation.getColumns.toList) (vk.csDegree - 2)]
      rw [Array.length_toList]
      rw [lookupEvalCount_eq vk.csDegree vk.cs.lookups.toList cl hcl]
      rw [hchunks]
      rw [map_add_three_map]
      rw [filter_map_index_length]
      simp [Array.length_toList, Permutation.numChunksOf, PermutationArgument.getColumns]
    · cases hp5
  · cases hp5

set_option maxHeartbeats 4000000 in
/-- The generated plan's protocol is `fromConstraintSystem` applied to the same
    constraint system and the deployed committed-instance count (`1`, from
    `SupportedV2.instShape`). -/
theorem plan_protocol_fromConstraintSystem {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    ProtocolPlan.fromConstraintSystem Features.solidity R.vk.cs 1
      = .ok R.plan.meta_.protocol := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := Midfall.LoweringV2.pfx_plan_of_generated hR.generated
  unfold ConstraintSystemMeta.new at hraw
  simp only [Bind.bind] at hraw
  obtain ⟨protocol, hproto, hok⟩ := AlgebraWidths.except_bind_ok hraw
  have hrawMeta : rawMeta.protocol = protocol := by
    have h := Except.ok.inj hok
    rw [← h]
  have hmetaprot : plan.meta_.protocol = protocol := by
    have h2 := (newFromVk_meta_numEvals (Midfall.Generator.PlanNew.frFieldCtx R.E.delta)
      R.vk.cs rawMeta R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl).2
    rw [h2, hrawMeta]
  rw [hp, hmetaprot]
  rw [hR.supported.instShape.2] at hproto
  exact hproto

/-- **`PrepareLogSlots` from A6, the KZG point-set bridge, and the two count
    identities that remain outside this lane.** The readAlgebra eval count is no
    longer assumed for an arbitrary trace: it is derived for the trace the
    `prepare` run actually parses, from `readAlgebraEvalCount_parseTrace` and the
    protocol's seven-group decomposition. -/
theorem PrepareLogSlots_of_parsed {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (nParse n : Nat)
    (hParse : ∀ (inst : Array (Fr p)),
      ParseTraceWidths R.E Features.solidity R.vk #[#[(1 : G₁)]] #[#[inst.toList.toArray]] nParse)
    (hMulti : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
      MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        R.E.g1 (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
          R.E.fewerPointSetsRuntime) n R.E.delta R.vk Features.solidity trace
        #[#[(1 : G₁)]] #[#[inst.toList.toArray]])
    (hQuot : nParse + readAlgebraQuotientCount Features.solidity R.vk
      = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).prefixG1Count)
    (hPoint : n = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    PrepareLogSlots R := by
  intro inst π d t hrun
  unfold Midfall.Halo2.prepare at hrun
  unfold Midfall.Halo2.prepareWith at hrun
  unfold Verifier.prepare at hrun
  obtain ⟨trace, t1, hparse, hver⟩ := PresWidthSeq.run_bind_ok hrun
  have heval := readAlgebraEvalCount_parseTrace_eq_numMainEvals R.E.g1 R.vk
    hR.supported.wf (1 : G₁) inst (plan_protocol_fromConstraintSystem R hR) hparse
  have h2 : readAlgebraEvalCount R.vk trace.permutations trace.lookups trace.trashcans
      1 1 #[#[inst.toList.toArray]]
      = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numEvals :=
    heval.trans (plan_numEvals_eq_protocol R hR).symm
  have hslots := prepareSlots_of_counts R inst trace nParse n hQuot h2 hPoint
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
        R.E.fewerPointSetsRuntime) R.vk trace #[#[(1 : G₁)]] #[#[inst.toList.toArray]] n
      (hMulti inst trace) rfl t1 t d hver
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
  exact hslots

/-- **THE A6 RESIDUAL, NAMED (parseTrace's G1 width block).** `Verifier.parseTrace`
    appends exactly one `g1` width per non-quotient commitment, and that block
    together with the quotient limbs `readAlgebra` reads is the plan's
    `prefixG1Count`. This is the parseTrace half of the shared schedule walk; A6
    proves the EMITTED parser's static schedule (`tp_events_slots`) but not this
    Lean-side run, so the two are kept as separate named residuals. -/
def ParseTraceSchedule (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) : Prop :=
  ∃ nParse : Nat,
    (∀ (inst : Array (Fr p)),
      ParseTraceWidths R.E Features.solidity R.vk #[#[(1 : G₁)]] #[#[inst.toList.toArray]] nParse) ∧
    nParse + readAlgebraQuotientCount Features.solidity R.vk =
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).prefixG1Count

set_option maxHeartbeats 4000000 in
/-- **THE PROTOCOL'S PARSER COUNTS**, read off the successful
    `fromConstraintSystem`: the lookup count and chunk list, the permutation-product
    count, the trashcan count, the quotient-limb count and the advice-phase vector's
    total. -/
theorem protocol_parseCounts {G₁ : Type} (vk : VerifyingKey (Fr p) G₁)
    (hf : vk.WellFormed Features.solidity) {plan : ProtocolPlan}
    (hplan : ProtocolPlan.fromConstraintSystem Features.solidity vk.cs 1 = .ok plan) :
    plan.numLookups = vk.cs.lookups.size ∧
    (∃ cl, chunkedOf vk.csDegree vk.cs.lookups.toList = some cl ∧
      plan.lookupChunks = cl.map LogupChunkedArgument.numChunks) ∧
    plan.numPermutationZs =
      Permutation.numChunksOf vk.cs.permutation.columns.size (vk.csDegree - 2) ∧
    plan.numTrashcans = vk.cs.trashcans.size ∧
    plan.numQuotients = readAlgebraQuotientCount Features.solidity vk ∧
    Midfall.Lowering.sumNat plan.numUserAdvices = vk.cs.adviceColumnPhase.size := by
  unfold ProtocolPlan.fromConstraintSystem at hplan
  simp only [Bind.bind] at hplan
  obtain ⟨csDegree, hdeg, hp1⟩ := AlgebraWidths.except_bind_ok hplan
  obtain ⟨lookupChunks, hlu, hp2⟩ := AlgebraWidths.except_bind_ok hp1
  obtain ⟨⟨adv, advIdx⟩, hAdv, hp3⟩ := AlgebraWidths.except_bind_ok hp2
  obtain ⟨⟨ch, chIdx⟩, hCh, hp4⟩ := AlgebraWidths.except_bind_ok hp3
  obtain ⟨bl, hbl, hp5⟩ := AlgebraWidths.except_bind_ok hp4
  split at hp5
  · rename_i hfix
    split at hp5
    · rename_i hval
      cases hp5
      have hdegEq : csDegree = vk.csDegree := by
        simp only [hf.csDegreeMatches] at hdeg
        exact (Except.ok.inj hdeg).symm
      obtain ⟨cl, hcl, hchunks⟩ := mapExceptArray_chunk csDegree vk.cs.lookups hlu
      have hclLen : cl.length = vk.cs.lookups.size := by
        rw [chunkedOf_length csDegree _ hcl, Array.length_toList]
      have hquot : (if Features.solidity.outerSingleHCommitment then 1
          else csDegree - 1) = readAlgebraQuotientCount Features.solidity vk := by
        rw [readAlgebraQuotientCount, hdegEq,
          show vk.domain.getQuotientPolyDegree = vk.csDegree - 1 from hf.domainConsistent.2]
      refine ⟨?_, ⟨cl, ?_, ?_⟩, ?_, rfl, hquot, ?_⟩
      · rw [hchunks, List.length_map, hclLen]
      · rw [← hdegEq]; exact hcl
      · exact hchunks
      · rw [if_list_isEmpty_divCeil, hdegEq]
        unfold Permutation.numChunksOf
        rw [show vk.cs.permutation.getColumns.toList.length =
            vk.cs.permutation.columns.size from by
          rw [PermutationArgument.getColumns, Array.length_toList]]
      · rw [TranscriptRows.remapping_nums_sum _ _ hAdv]
        simp [ConstraintSystem.adviceColumnPhaseNats, Array.length_toList]
    · cases hp5
  · cases hp5

/-! ### D-GATE7: the advice read count is the advice-column count

    `parseTrace`'s phase loop reads one `g1` per (phase, proof, column of that
    phase). The phase list enumerates `0 .. maxPhase`, and every recorded column
    phase is at most `maxPhase`, so each advice column contributes exactly once.
    `WellFormed.advicePhaseTotal` then identifies `numAdviceColumns` with the
    phase vector's length. -/

/-- `filterMap (if p i then some i else none)` counts the indices satisfying `p`. -/
theorem length_filterMap_ite (l : List Nat) (p : Nat → Bool) :
    (l.filterMap (fun i => if p i then some i else none)).length = l.countP p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.countP_cons]
      by_cases h : p a <;> simp [h, ih]

/-- Counting a value over the index range of a list counts its occurrences. -/
theorem countP_getElem? (l : List Nat) (a : Nat) :
    (List.range l.length).countP (fun i => l[i]? == some a) = l.count a := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
        Function.comp_def]
      simp only [Nat.succ_eq_add_one, List.getElem?_cons_zero, List.getElem?_cons_succ]
      rw [ih, List.count_cons]
      simp only [Option.some.injEq, beq_iff_eq]

/-- The indicator sum of a boolean predicate is its count. -/
theorem sum_map_ite_one {α : Type} (l : List α) (p : α → Bool) :
    (l.map (fun x => if p x then 1 else 0)).sum = l.countP p := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [List.map_cons, List.sum_cons, List.countP_cons, ih]; omega

/-- `Σ_{ph < m} count ph l = l.length` when every entry of `l` is below `m`. -/
theorem sum_range_count_eq_length (l : List Nat) (m : Nat) (h : ∀ x ∈ l, x < m) :
    ((List.range m).map (fun ph => l.count ph)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a < m := h a (by simp)
      have has : ∀ x ∈ as, x < m := fun x hx => h x (by simp [hx])
      have hstep : (List.map (fun ph => (a :: as).count ph) (List.range m)).sum
          = (List.map (fun ph => as.count ph) (List.range m)).sum
            + (List.map (fun ph => if (a == ph) then 1 else 0) (List.range m)).sum := by
        rw [← List.sum_map_add]
        apply congrArg List.sum
        apply List.map_congr_left
        intro ph _
        rw [List.count_cons]
      rw [hstep, ih has]
      have hind : (List.map (fun ph => if (a == ph) then 1 else 0)
          (List.range m)).sum = 1 := by
        rw [sum_map_ite_one]
        have hc : (List.range m).count a = 1 := by
          rw [List.count_range]; simp [ha]
        rw [← hc, List.count_eq_countP]
        apply List.countP_congr
        intro x _
        rw [beq_iff_eq, beq_iff_eq, eq_comm]
      rw [hind]
      simp

/-- The phase fold never decreases its accumulator. -/
theorem le_foldl_max_acc (acc : Nat) (ps : List Phase) :
    acc ≤ ps.foldl (fun acc p => max acc p.val) acc := by
  induction ps generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons q rest ih =>
      rw [List.foldl_cons]
      exact Nat.le_trans (le_max_left acc q.val) (ih (max acc q.val))

/-- Every recorded column phase is at most the fold-max of the phase vector. -/
theorem le_foldl_max_val (b : Nat) (ps : List Phase) :
    ∀ x ∈ ps, x.val ≤ ps.foldl (fun acc p => max acc p.val) b := by
  induction ps generalizing b with
  | nil => intro x hx; simp at hx
  | cons q rest ih =>
      intro x hx
      rw [List.foldl_cons]
      rw [List.mem_cons] at hx
      rcases hx with hx | hx
      · have hq' : x.val = q.val := by rw [hx]
        rw [hq']
        exact Nat.le_trans (le_max_right b q.val) (le_foldl_max_acc (max b q.val) rest)
      · exact ih (max b q.val) x hx

/-- The parser's per-phase advice column list counts occurrences of the phase. -/
theorem advicePhaseCols_length_eq_count {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) (ph : Nat)
    (h : cs.adviceColumnPhase.size = cs.numAdviceColumns) :
    (advicePhaseCols cs ph).length = (cs.adviceColumnPhaseNats.toList).count ph := by
  have hlen : (cs.adviceColumnPhaseNats.toList).length = cs.numAdviceColumns := by
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.length_toList, Array.size_map, h]
  rw [advicePhaseCols, ← hlen, length_filterMap_ite]
  have hp : (fun (i : Nat) => (Option.map (fun (q : Phase) => q.val) cs.adviceColumnPhase[i]? == some ph))
      = (fun (i : Nat) => (cs.adviceColumnPhaseNats.toList)[i]? == some ph) := by
    funext (i : Nat)
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.toList_map, List.getElem?_map, ← Array.getElem?_toList]
  rw [hp]
  exact countP_getElem? _ _

/-- **THE ADVICE READ COUNT IS THE ADVICE-COLUMN COUNT.** `adviceReadCount cs 1`
    sums, over the enumerated phases, the number of advice columns recorded at
    that phase; every column is counted exactly once, so the total is the phase
    vector's length — and `advicePhaseTotal` makes that `numAdviceColumns`. -/
theorem adviceReadCount_eq_phaseSize {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁)
    (h : vk.cs.adviceColumnPhase.size = vk.cs.numAdviceColumns) :
    adviceReadCount vk.cs 1 = vk.cs.adviceColumnPhase.size := by
  have hbound : ∀ x ∈ vk.cs.adviceColumnPhaseNats.toList,
      x < vk.cs.adviceColumnPhase.foldl (fun acc p => max acc p.val) 0 + 1 := by
    intro x hx
    unfold ConstraintSystem.adviceColumnPhaseNats at hx
    rw [Array.toList_map] at hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp
      (show x ∈ List.map (fun q : Phase => q.val) vk.cs.adviceColumnPhase.toList from hx)
    subst hqx
    rw [← Array.foldl_toList]
    have := le_foldl_max_val 0 vk.cs.adviceColumnPhase.toList q hq
    omega
  unfold adviceReadCount ConstraintSystem.phases
  simp only [Nat.one_mul]
  rw [List.map_map]
  dsimp only [Function.comp_def]
  have hfun : (fun i => (advicePhaseCols vk.cs i).length)
      = (fun i => (vk.cs.adviceColumnPhaseNats.toList).count i) := by
    funext i
    exact advicePhaseCols_length_eq_count vk.cs i h
  rw [hfun, sum_range_count_eq_length _ _ hbound]
  have hlen : (vk.cs.adviceColumnPhaseNats.toList).length = vk.cs.numAdviceColumns := by
    unfold ConstraintSystem.adviceColumnPhaseNats
    rw [Array.length_toList, Array.size_map, h]
  rw [hlen, h]

/-- **THE ADVICE COUNT IDENTITY, NAMED.** The parser's phase loop reads one `g1`
    per advice column of every phase, so its total is the advice-phase vector's
    length. D-GATE7's `WellFormed.advicePhaseTotal`
    (`adviceColumnPhase.size = numAdviceColumns`) supplies that length, and
    `adviceReadCount_eq_phaseSize` proves the identity from it
    (`advicePhaseCountFit_of_wellFormed`); the name is kept because the counting
    argument factors through it. -/
def AdvicePhaseCountFit {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) : Prop :=
  adviceReadCount vk.cs 1 = vk.cs.adviceColumnPhase.size

/-- **D-GATE7 DISCHARGES THE PIN.** `WellFormed.advicePhaseTotal` is exactly the
    phase-vector length the count needs, so `AdvicePhaseCountFit` is a theorem of
    every well-formed key. -/
theorem advicePhaseCountFit_of_wellFormed {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (hf : vk.WellFormed Features.solidity) :
    AdvicePhaseCountFit vk :=
  adviceReadCount_eq_phaseSize vk hf.advicePhaseTotal

set_option maxHeartbeats 4000000 in
/-- **`ParseTraceSchedule` FROM THE ADVICE COUNT IDENTITY.** The width walk
    (`parseTrace_widths`), the protocol counts (`protocol_parseCounts`), the layout
    peel (`tp_fromProtocol`) and the group-sum identity
    (`sum_commitmentReadGroups`) assemble into the schedule outright: every
    committed group contributes exactly its parser reads. The one input beyond
    `ValidV3` is `AdvicePhaseCountFit`, itself a theorem of `WellFormed`
    (`advicePhaseCountFit_of_wellFormed`), so `parseTraceSchedule` is
    unconditional. -/
theorem parseTraceSchedule_of_advicePhase {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hpin : AdvicePhaseCountFit R.vk) :
    ParseTraceSchedule R := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hL, _hc1, _hc2, _hc3,
    _hc4, _hc5, _hc6, _hc7, _hc8, _hup, _huser, _hnInst, _htrunc, _hnLook, _hnPerm,
    _hnTrash, _hLH⟩ := TranscriptRows.tp_planFacts (G₁ := G₁) hR
  have facts := TranscriptRows.tp_fromProtocol hL
  have hcounts := protocol_parseCounts (p := p) R.vk hR.supported.wf
    (plan_protocol_fromConstraintSystem R hR)
  rw [hmeta] at hcounts
  obtain ⟨hLook, ⟨cl, hcl, hChunks⟩, hPerm, hTrash, hQuot, hAdvSum⟩ := hcounts
  -- the five group identifications
  have eA : adviceReadCount R.vk.cs 1
      = Midfall.Lowering.sumNat (L.advicePhases.map (fun s => s.itemCount)) := by
    rw [hpin, ← hAdvSum, ← facts.adviceSum]
  have eM : R.vk.cs.lookups.size = L.lookupMultiplicities.itemCount := by
    rw [facts.lookupM, hLook]
  have eP : Permutation.numChunksOf R.vk.cs.permutation.columns.size
        (R.vk.csDegree - 2) = L.permutationProducts.itemCount := by
    rw [facts.permZ, hPerm]
  have eT : R.vk.cs.trashcans.size = L.trash.itemCount := by
    rw [facts.trash, hTrash]
  have eQ : readAlgebraQuotientCount Features.solidity R.vk
      = L.quotientLimbs.itemCount := by
    rw [facts.quotient, hQuot]
  have eS : lookupCommitReadCount R.vk.csDegree R.vk.cs.lookups.toList
      = Midfall.Lowering.sumNat (L.lookups.map (fun lk =>
          lk.helpers.itemCount + lk.accumulator.itemCount)) := by
    rw [facts.lookupSum, hChunks]
    have hmap := zip_range_snd_map (cl.map LogupChunkedArgument.numChunks)
      (fun c => c + 1)
    rw [hmap, List.map_map]
    unfold lookupCommitReadCount
    rw [hcl]
    simp only [Option.getD_some]
    exact (sumNat_eq_sum _).symm
  refine ⟨parseTraceReadCount R.vk, ?_, ?_⟩
  · intro inst t t' tr h
    exact parseTrace_widths R.E.g1 R.vk 1 inst.toList.toArray h
  · have hprefix : (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).prefixG1Count = L.commitmentG1Count := by
      rw [hlay]
      show (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).g1Groups.foldl
        (fun acc n => acc + n) 0 = L.commitmentG1Count
      rw [show (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).g1Groups
        = L.commitmentReadGroups from rfl]
      exact Midfall.Lowering.sum_commitmentReadGroups L
    rw [hprefix]
    unfold ProofCalldataLayout.commitmentG1Count ProofCalldataLayout.nonQuotientG1Count
    dsimp only
    unfold parseTraceReadCount
    rw [eA, eM, eP, eS, eT, eQ]
    unfold Midfall.Lowering.sumNat
    dsimp only

/-- **`ParseTraceSchedule`, UNCONDITIONAL.** The width walk
    (`parseTrace_widths`), the protocol counts (`protocol_parseCounts`) and
    D-GATE7's `WellFormed.advicePhaseTotal` close the parse side: no residual. -/
theorem parseTraceSchedule {G₁ G₂ Gₜ : Type}
    [inst₁ : Group G₁] [inst₂ : Group G₂] [inst₃ : Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    ParseTraceSchedule R :=
  parseTraceSchedule_of_advicePhase R hR (advicePhaseCountFit_of_wellFormed R.vk hR.supported.wf)

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage

variable {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem lookupChunkNum_sum_eq_of_chunkedOf (deg k : Nat) :
    ∀ (l : List (LogupBatchedArgument (Fr p))) (cl : List (LogupChunkedArgument (Fr p))),
      chunkedOf deg l = some cl →
      (l.map (fun x => TranscriptRows.lookupChunkNum deg x + k)).sum
        = (cl.map (fun c => c.numChunks + k)).sum := by
  intro l
  induction l with
  | nil =>
      intro cl h
      simp [chunkedOf] at h
      cases h
      rfl
  | cons a as ih =>
      intro cl h
      unfold chunkedOf at h
      simp only [List.mapM_cons] at h
      cases ha : (a.chunkByDegree deg).toOption with
      | none => simp [ha] at h
      | some c =>
          simp only [ha, Option.bind_some] at h
          cases hrest : List.mapM (fun x => (x.chunkByDegree deg).toOption) as with
          | none => simp [hrest] at h
          | some cl0 =>
              rw [hrest] at h
              simp only [Option.pure_def, Option.bind_some] at h
              injection h with h
              subst h
              simp only [List.map_cons, List.sum_cons]
              have hok : a.chunkByDegree deg = .ok c := by
                cases h : a.chunkByDegree deg with
                | ok c' =>
                    rw [h] at ha
                    simp only [Except.toOption, Option.some.injEq] at ha
                    subst ha
                    rfl
                | error e =>
                    rw [h] at ha
                    change none = some c at ha
                    cases ha
              have hc : c.numChunks = TranscriptRows.lookupChunkNum deg a :=
                TranscriptRows.chunkNum_eq deg a c hok
              rw [hc, ih cl0 hrest]




theorem protocol_evalPlanFields {F : Type} (feat : Features) (cs : ConstraintSystem F)
    (nb : Nat) {plan : ProtocolPlan}
    (h : ProtocolPlan.fromConstraintSystem feat cs nb = .ok plan) :
    plan.instanceQueries = cs.instanceQueries.toList.map
        (fun q => QueryKey.new q.1.index q.2.int) ∧
    plan.numCommittedInstances = nb ∧
    plan.adviceQueries = cs.adviceQueries.toList.map
        (fun q => QueryKey.new q.1.index q.2.int) ∧
    plan.numFixeds = cs.numFixedColumns ∧
    plan.simpleSelectorCols = (List.range cs.numFixedColumns).filter
        (fun idx => cs.hasSimpleSelectorCol idx) ∧
    plan.numSimpleSelectors = cs.numSimpleSelectors ∧
    plan.permutationColumns = cs.permutation.getColumns.toList ∧
    plan.validate = .ok () := by
  unfold ProtocolPlan.fromConstraintSystem at h
  simp only [Bind.bind] at h
  obtain ⟨csDegree, _hdeg, h1⟩ := AlgebraWidths.except_bind_ok h
  obtain ⟨lookupChunks, _hlu, h2⟩ := AlgebraWidths.except_bind_ok h1
  obtain ⟨_x1, _hr1, h3⟩ := AlgebraWidths.except_bind_ok h2
  obtain ⟨_x2, _hr2, h4⟩ := AlgebraWidths.except_bind_ok h3
  obtain ⟨_bl, _hbl, h5⟩ := AlgebraWidths.except_bind_ok h4
  split at h5
  · rename_i hfix
    split at h5
    · rename_i hval
      cases h5
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simpa using hval
    · cases h5
  · cases h5




set_option maxHeartbeats 4000000 in
theorem planPrefixG1_eq (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count
      = TranscriptRows.planPrefixG1Count R := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hL, _hc1, _hc2, _hc3,
    _hc4, _hc5, _hc6, _hc7, _hc8, _hup, _huser, _hnInst, _htrunc, _hnLook, _hnPerm,
    _hnTrash, _hLH⟩ := TranscriptRows.tp_planFacts (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) hR
  have facts := TranscriptRows.tp_fromProtocol hL
  have hcounts := protocol_parseCounts (p := p) R.vk hR.supported.wf
    (plan_protocol_fromConstraintSystem R hR)
  rw [hmeta] at hcounts
  obtain ⟨hLook, ⟨cl, hcl, hChunks⟩, hPerm, hTrash, hQuot, hAdvSum⟩ := hcounts
  have eA : adviceReadCount R.vk.cs 1
      = Midfall.Lowering.sumNat (L.advicePhases.map (fun s => s.itemCount)) := by
    rw [advicePhaseCountFit_of_wellFormed R.vk hR.supported.wf, ← hAdvSum, ← facts.adviceSum]
  have eM : R.vk.cs.lookups.size = L.lookupMultiplicities.itemCount := by
    rw [facts.lookupM, hLook]
  have eP : Permutation.numChunksOf R.vk.cs.permutation.columns.size
        (R.vk.csDegree - 2) = L.permutationProducts.itemCount := by
    rw [facts.permZ, hPerm]
  have eT : R.vk.cs.trashcans.size = L.trash.itemCount := by
    rw [facts.trash, hTrash]
  have eQ : readAlgebraQuotientCount Features.solidity R.vk
      = L.quotientLimbs.itemCount := by
    rw [facts.quotient, hQuot]
  have eS : lookupCommitReadCount R.vk.csDegree R.vk.cs.lookups.toList
      = Midfall.Lowering.sumNat (L.lookups.map (fun lk =>
          lk.helpers.itemCount + lk.accumulator.itemCount)) := by
    rw [facts.lookupSum, hChunks]
    have hmap := zip_range_snd_map (cl.map LogupChunkedArgument.numChunks)
      (fun c => c + 1)
    rw [hmap, List.map_map]
    unfold lookupCommitReadCount
    rw [hcl]
    simp only [Option.getD_some]
    exact (sumNat_eq_sum _).symm
  have eA' : adviceReadCount R.vk.cs 1
      = (R.vk.cs.phases.map (fun ph =>
          (TranscriptRows.phaseCols R.vk.cs ph).length)).sum := by
    simp [adviceReadCount, TranscriptRows.phaseCols, advicePhaseCols]
  have eS' : lookupCommitReadCount R.vk.csDegree R.vk.cs.lookups.toList
      = (R.vk.cs.lookups.toList.map (fun l =>
          TranscriptRows.lookupChunkNum R.vk.csDegree l + 1)).sum := by
    unfold lookupCommitReadCount
    rw [hcl]
    simp only [Option.getD_some]
    exact (lookupChunkNum_sum_eq_of_chunkedOf (p := p) R.vk.csDegree 1
      R.vk.cs.lookups.toList cl hcl).symm
  have hprefix : (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).prefixG1Count = L.commitmentG1Count := by
    rw [hlay]
    show (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).g1Groups.foldl
      (fun acc n => acc + n) 0 = L.commitmentG1Count
    rw [show (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout L).g1Groups
      = L.commitmentReadGroups from rfl]
    exact Midfall.Lowering.sum_commitmentReadGroups L
  rw [hprefix]
  unfold ProofCalldataLayout.commitmentG1Count ProofCalldataLayout.nonQuotientG1Count
  dsimp only
  unfold TranscriptRows.planPrefixG1Count
  change Midfall.Lowering.sumNat (L.advicePhases.map (fun s => s.itemCount))
      + L.lookupMultiplicities.itemCount + L.permutationProducts.itemCount
      + Midfall.Lowering.sumNat (L.lookups.map (fun lk =>
          lk.helpers.itemCount + lk.accumulator.itemCount))
      + L.trash.itemCount + L.quotientLimbs.itemCount =
    (List.map (fun ph => (TranscriptRows.phaseCols R.vk.cs ph).length) R.vk.cs.phases).sum
      + R.vk.cs.lookups.size
      + Permutation.numChunksOf R.vk.cs.permutation.columns.size (R.vk.csDegree - 2)
      + (List.map (fun l => TranscriptRows.lookupChunkNum R.vk.csDegree l + 1)
          R.vk.cs.lookups.toList).sum
      + R.vk.cs.trashcans.size
      + (if Features.solidity.outerSingleHCommitment = true then 1
          else R.vk.domain.getQuotientPolyDegree)
  rw [← eA, ← eM, ← eP, ← eS, ← eT, ← eQ, eA', eS']
  rfl




set_option maxHeartbeats 4000000 in
theorem planNumEvals_eq (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (inst : Array (Fr p)) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
      = TranscriptRows.planNumEvals R inst := by
  rw [plan_numEvals_eq_protocol R hR]
  change R.plan.meta_.protocol.proof.evals.length = TranscriptRows.planNumEvals R inst
  have hplan := plan_protocol_fromConstraintSystem R hR
  rw [fromConstraintSystem_evals_length Features.solidity R.vk.cs 1 hplan]
  obtain ⟨hInstQ, hNCI, hAdvQ, hNumFix, hSimpleCols, hNumSimple, hPermCols, hValid⟩ :=
    protocol_evalPlanFields Features.solidity R.vk.cs 1 hplan
  obtain ⟨hLook, ⟨cl, hcl, hChunks⟩, hPerm, hTrash, hQuot, hAdvSum⟩ :=
    protocol_parseCounts (p := p) R.vk hR.supported.wf hplan
  have hSimpleLen : R.plan.meta_.protocol.simpleSelectorCols.length
      = R.vk.cs.numSimpleSelectors := by
    rw [← validate_numSimpleSelectors hValid, hNumSimple]
  rw [hInstQ, hNCI, hAdvQ, hNumFix, hSimpleLen, hPermCols, hPerm, hChunks, hTrash]
  unfold TranscriptRows.planNumEvals
  simp only [List.map_map, Function.comp_def]
  rw [filter_map_index_length]
  rw [← lookupChunkNum_sum_eq_of_chunkedOf (p := p) R.vk.csDegree 3
    R.vk.cs.lookups.toList cl hcl]
  simp only [Midfall.Halo2.PermutationArgument.getColumns, Array.length_toList]
  rw [← hR.supported.wf.permutationCommitmentsMatch]
  simp [instanceShape]

/-- **`PlanReadCounts` FOR THE GENERATED PLAN.** The parse half is
    `planPrefixG1_eq` (the `protocol_parseCounts` group identifications plus the
    `fromProtocol` layout peel); the eval half is `planNumEvals_eq`
    (`fromConstraintSystem_evals_length` plus the same peel). No count premise is
    assumed. -/
theorem planReadCounts_of_valid (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) : TranscriptRows.PlanReadCounts R :=
  ⟨planPrefixG1_eq R hR, fun inst => planNumEvals_eq R hR inst⟩

/-- **`XcriptAlgebraRun` FROM `ValidV3`.** The schedule is `planReadCounts_of_valid`;
    the only remaining runtime input is `hnum`. -/
theorem xcriptAlgebraRun_of_valid (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (cd : Bytes)
    (hnum : R.cfg.numInstances < 2 ^ 31) :
    TranscriptRows.XcriptAlgebraRun R H cd :=
  TranscriptRows.xcriptAlgebraRun_of_planReadCounts R hR hcodec H cd
    (planReadCounts_of_valid R hR) hnum

/-- **THE FIXED `tp_agrees` ROW, WITH ITS TWO REMAINING NAMED INPUTS.** This is the
    fixed row's conclusion from `ValidV3`, the schedule (now proved), the calldata
    bound `hnum` and Calldata's `XcriptG1`. The fixed `tp_agrees` itself keeps its
    original statement (no `hnum`/`XcriptG1` parameters) and is not weakened; this is
    its schedule-carrying consumer. -/
theorem tp_agrees_of_valid (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (hpost : TranscriptRows.TpPost R H vkAddr cd V st)
    (hnum : R.cfg.numInstances < 2 ^ 31)
    (hG1 : TranscriptRows.XcriptG1 R H cd st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st :=
  TranscriptRows.tp_agrees_of_planReadCounts R hR hcodec H vkAddr cd V st hpost
    (planReadCounts_of_valid R hR) hnum hG1


/-- **THE KZG RESIDUAL, REPAIRED (D-GATE10), AT `linearize`'S QUERY VECTOR.**
    `multiPrepare` appends `[g1]`, one scalar per quotient-opening point set, `[g1]`;
    the count is the plan's `numPointSets`. The OLD `∀ queries` form is FALSE at
    `#[]` (`MultiPrepareBlockWidth.eq_zero_of_empty_run`), so the residual is stated
    at the query vectors `Verifier.linearize` actually produces (which always include
    the linearization query and whose point-set count is fixed by the VK under
    D-GATE5 `x ≠ 0` + D-GATE6 rotation distinctness). This is the form the consumers
    use; `KzgMultiPrepareWidths_of_pointSets` and
    `KzgMultiPrepareWidths_of_kzgPartitionBridge` reduce it to the count and to the
    already-named `KzgPartitionBridge` respectively. -/
def KzgMultiPrepareWidths (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁),
    MultiPrepareWidthsLinearize (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
      R.E.g1
      (Pcs.kzg (G₂ := G₂) (Gₜ := Gₜ) R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime)
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).numPointSets
      R.E.delta R.vk Features.solidity trace #[#[(1 : G₁)]] #[#[inst.toList.toArray]]

/-- **`KzgMultiPrepareWidths` FROM THE POINT-SET COUNT AT `linearize`.** This is the
    exact remaining count obligation: for each query vector `linearize` produces, the
    `constructIntermediateSets` point-set count is the plan's `numPointSets`. -/
theorem KzgMultiPrepareWidths_of_pointSets (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hPoint : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∀ (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p))),
        constructIntermediateSets (F := Fr p) (C := G₁)
          (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
          = .ok (cm, pointSets) →
        pointSets.size = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    KzgMultiPrepareWidths R := by
  intro inst trace alg queries hlin
  have hNoDummies : ¬ (Features.solidity.outerFewerPointSets && R.E.fewerPointSetsRuntime) := by
    simp [Features.solidity]
  by_cases hok : ∃ (cm : Array (CD (Fr p) G₁)) (pointSets : Array (Array (Fr p))),
      constructIntermediateSets (F := Fr p) (C := G₁)
        (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries
        = .ok (cm, pointSets)
  · obtain ⟨cm, pointSets, hCI⟩ := hok
    exact MultiPrepareBlockWidthAt_of_pointSets R.E.g1 R.E.field Features.solidity
      R.E.fewerPointSetsRuntime _ queries cm pointSets hNoDummies hCI
      (hPoint inst trace alg queries hlin cm pointSets hCI)
  · intro t t' a hrun
    obtain ⟨cm, pointSets, hCI⟩ :=
      multiPrepare_constructIntermediateSets_ok R.E.g1 R.E.field Features.solidity
        R.E.fewerPointSetsRuntime queries hNoDummies hrun
    exact absurd ⟨cm, pointSets, hCI⟩ hok

/-- **`KzgMultiPrepareWidths` FROM THE PORT-AUDIT PARTITION BRIDGE**, at the
    linearized query vectors. Consumes the already-named `KzgPartitionBridge` plus
    the generator's `pointSets.length = plan.numPointSets`; the remaining input is
    the query-map correspondence `linearize's queries ↔ Generator.Query`. -/
theorem KzgMultiPrepareWidths_of_kzgPartitionBridge
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hG : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∃ (queriesG : List Midfall.Generator.Query)
        (setsG : Midfall.Generator.IntermediateSets),
        Midfall.Generator.constructIntermediateSetsImpl queriesG = .ok setsG ∧
        KzgPartitionBridge (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) queries queriesG ∧
        setsG.pointSets.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    KzgMultiPrepareWidths R := by
  refine KzgMultiPrepareWidths_of_pointSets R ?_
  intro inst trace alg queries hlin cm pointSets hCI
  obtain ⟨queriesG, setsG, hGok, hBridge, hLen⟩ := hG inst trace alg queries hlin
  exact (hBridge (cm, pointSets) setsG hCI hGok).trans hLen

/-- **THE ROTATION-KEY DATUM CONSTRUCTOR.** This instantiates
    `KzgQueryMapData.ofList` with the global rotation key from
    `exists_pointKey`: `hpairPoint` gives the actual verifier-point/generator-
    rotation relation, and `hrot` puts each generator rotation in the key's
    rotation list. The remaining arguments are the tail-local commitment
    alignment and equivalence facts (the no-aliasing/value-injectivity data).
    This is the concrete datum shape for one `linearize` output. -/
noncomputable def KzgQueryMapData.ofRotations
    (queriesV : Array (VerifierQuery (Fr p) G₁))
    (queriesG : List Midfall.Generator.Query)
    (L : List (VerifierQuery (Fr p) G₁ × Midfall.Generator.Query))
    (hVlist : queriesV.toList = L.map Prod.fst)
    (hGlist : queriesG = L.map Prod.snd)
    (d : EvaluationDomain (Fr p)) (x : Fr p) (rots : List Int)
    (hx : x ≠ 0) (hwi : d.omegaInv * d.omega = 1)
    (hord : Midfall.Assumptions.orderExactly d.omega d.n)
    (hdistinct : ∀ r s : Int, r ≡ s [ZMOD (d.n : Int)] → r = s)
    (hpairPoint : ∀ p ∈ L,
      p.1.point = d.rotateOmega x (Rotation.value p.2.rotation))
    (hrot : ∀ p ∈ L, p.2.rotation ∈ rots)
    (hclass : ∀ p ∈ L, ∀ p' ∈ L,
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p.1.commitment p'.1.commitment = Midfall.Generator.ecPointBeq p.2.comm p'.2.comm)
    (hCommRefl : ∀ p ∈ L,
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p.1.commitment p.1.commitment = true)
    (hCommSymm : ∀ p ∈ L, ∀ p' ∈ L,
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p.1.commitment p'.1.commitment =
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p'.1.commitment p.1.commitment)
    (hCommTrans : ∀ p ∈ L, ∀ p' ∈ L, ∀ p'' ∈ L,
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p.1.commitment p'.1.commitment = true →
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p'.1.commitment p''.1.commitment = true →
      kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
        p.1.commitment p''.1.commitment = true)
    (hGRefl : ∀ p ∈ L, Midfall.Generator.ecPointBeq p.2.comm p.2.comm = true)
    (hGSymm : ∀ p ∈ L, ∀ p' ∈ L,
      Midfall.Generator.ecPointBeq p.2.comm p'.2.comm =
      Midfall.Generator.ecPointBeq p'.2.comm p.2.comm)
    (hGTrans : ∀ p ∈ L, ∀ p' ∈ L, ∀ p'' ∈ L,
      Midfall.Generator.ecPointBeq p.2.comm p'.2.comm = true →
      Midfall.Generator.ecPointBeq p'.2.comm p''.2.comm = true →
      Midfall.Generator.ecPointBeq p.2.comm p''.2.comm = true) :
    KzgQueryMapData (eqC := kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))
      queriesV queriesG := by
  haveI : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).pos.ne'⟩
  let fk : Fr p → Int := Classical.choose (exists_pointKey d x rots hx hwi hord hdistinct)
  have hspec := Classical.choose_spec (exists_pointKey d x rots hx hwi hord hdistinct)
  have hfk : ∀ a b, (a == b) = (fk a == fk b) := hspec.1
  have hfkRot : ∀ r ∈ rots, fk (d.rotateOmega x (Rotation.value r)) = r := hspec.2
  exact KzgQueryMapData.ofList
    (kzgCommitBeq (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))
    queriesV queriesG L hVlist hGlist fk hfk
    (fun p hp => by
      rw [hpairPoint p hp]
      exact hfkRot p.2.rotation (hrot p hp))
    hclass hCommRefl hCommSymm hCommTrans hGRefl hGSymm hGTrans

/-- **THE QUERY-MAP FORM OF THE PARTITION BRIDGE.** This is
    `KzgPartitionBridge` discharged from the per-index verifier↔generator query
    map proved in `Midfall.LoweringV3.KzgQueryMap`: the two
    `constructIntermediateSets` implementations are run in lockstep, their
    first-occurrence point indices agree, and the two canonical sorted forms
    (`natSort`, `btreeSetFromList`) agree on the duplicate-free lists, so the
    point-set counts are equal. -/
theorem KzgPartitionBridge_of_queryMap
    (queriesV : Array (VerifierQuery (Fr p) G₁))
    (queriesG : List Midfall.Generator.Query)
    (qm : @KzgQueryMapData (Fr p) G₁ _
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queriesV queriesG) :
    KzgPartitionBridge (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) queriesV queriesG := by
  intro setsV setsG hV hG
  letI : BEq qm.K := qm.beqK
  letI : LawfulBEq qm.K := qm.lawfulK
  exact constructIntermediateSets_pointSets_size_eq_of_queryMap
    (eqC := kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))
    (fk := qm.fk) (ck := qm.ck) (gk := qm.gk)
    qm.L qm.hCommEq qm.hGCommEq qm.hPointEq
    queriesV queriesG qm.hVlist qm.hGlist
    qm.hpairP qm.hpairC (cm := setsV.1) (pointSets := setsV.2) setsG hV hG

/-- **`KzgMultiPrepareWidths` FROM THE PER-LINEARIZE QUERY MAP.** This is the
    final reduction: for each query vector `linearize` produces, a query-map
    datum plus the generator's point-set count gives the `multiPrepare` width
    block. The concrete construction of the datum (the `linearize` ↔
    `Generator.Query` slot/rotation correspondence, with D-GATE5 `x ≠ 0` and
    D-GATE6 rotation-distinctness supplying the injectivity) is the remaining
    input. -/
theorem KzgMultiPrepareWidths_of_queryMap
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hMap : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∃ (queriesG : List Midfall.Generator.Query)
        (setsG : Midfall.Generator.IntermediateSets)
        (qm : @KzgQueryMapData (Fr p) G₁ _
          (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries queriesG),
        Midfall.Generator.constructIntermediateSetsImpl queriesG = .ok setsG ∧
        setsG.pointSets.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    KzgMultiPrepareWidths R := by
  refine KzgMultiPrepareWidths_of_kzgPartitionBridge R ?_
  intro inst trace alg queries hlin
  obtain ⟨queriesG, setsG, qm, hGok, hLen⟩ := hMap inst trace alg queries hlin
  exact ⟨queriesG, setsG, hGok, KzgPartitionBridge_of_queryMap queries queriesG qm, hLen⟩

/-- **THE D1-SPECIFIC FACT, NAMED EXACTLY: THE LINEARIZE QUERY MAP.** For every
    query vector `Verifier.linearize` emits, the generator's own
    `constructIntermediateSetsImpl` runs on a query list paired index-by-index with
    it, the two grouping relations compute the same partition (`KzgQueryMapData`),
    and the generator's point-set count is the plan's `numPointSets`.

    This is the only fact `PrepareLogSlots` needs beyond `ValidV3` and the parsed
    trace. It is NOT a row, bundle, root or `ValidV3` hypothesis: it is the
    verifier-vs-generator query correspondence (D-GATE10's repaired KZG residual),
    and `KzgMultiPrepareWidths_of_queryMap` consumes exactly this shape. No theorem
    in the tree constructs it from `GeneratedBy`: that clause pins the plan/model to
    `generateAll` for the render's inputs, while the `linearize` query vector comes
    from the per-proof commitments and evaluations in the parsed trace, so the
    index-by-index correspondence is the missing refinement, not a re-reading of a
    definition. -/
def LinearizeQueryMap (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
    (alg : Verifier.AlgebraRead (Fr p) G₁)
    (queries : Array (VerifierQuery (Fr p) G₁)),
    Verifier.linearize (p := p) (delta := R.E.delta) R.vk
      (adviceCommitments := trace.adviceCommitments)
      (committedInstances := if Features.solidity.committedInstances then
        #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
          (#[] : Array G₁))
      (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
      (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
      = .ok queries →
    ∃ (queriesG : List Midfall.Generator.Query)
      (setsG : Midfall.Generator.IntermediateSets)
      (qm : @KzgQueryMapData (Fr p) G₁ _
        (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries queriesG),
      Midfall.Generator.constructIntermediateSetsImpl queriesG = .ok setsG ∧
      setsG.pointSets.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).numPointSets

/-- The named query-map fact gives the KZG width residual. -/
theorem KzgMultiPrepareWidths_of_linearizeQueryMap
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (h : LinearizeQueryMap R) :
    KzgMultiPrepareWidths R :=
  KzgMultiPrepareWidths_of_queryMap R h


/-- **THE SCHEDULE FROM `ValidV3` AND THE PARSED TRACE, WITH THE ONE NAMED FACT.**
    The width walk itself is proved (`PrepareLogSlots_of_parseTrace`); the only
    premise is `LinearizeQueryMap`, the verifier-vs-generator query correspondence. -/
theorem PrepareLogSlots_of_validV3 (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (h : LinearizeQueryMap R) :
    Midfall.LoweringV3.PrepareLogSlots R := by
  obtain ⟨nParse, hParse, hQuot⟩ := parseTraceSchedule R hR
  exact PrepareLogSlots_of_parsed R hR nParse
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
      R.plan.proofLayout).numPointSets hParse
    (KzgMultiPrepareWidths_of_linearizeQueryMap R h) hQuot rfl

/-- **THE ADVERTISED `readScheduleAgrees_of_validV3`.** `decodeRust`'s transcript-log
    slot list is the plan's slot list, for every `ValidV3` render, every instance
    vector and every proof stream, modulo the one named `LinearizeQueryMap` fact. -/
theorem readScheduleAgrees_of_validV3 (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (h : LinearizeQueryMap R) :
    ∀ (inst : Array (Fr p)) (π : Bytes) (ms : List (Msg (Fr p) G₁)),
      decodeRust (Gₜ := Gₜ) R.E Features.solidity R.vk inst π = some ms →
        ms.map Midfall.Lowering.Msg.slot =
          (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots :=
  readScheduleAgrees_of_prepareLogSlots R (PrepareLogSlots_of_validV3 R hR h)

/-- **`KzgMultiPrepareWidths` FROM AN UPSTREAM QUERY DATUM.** The final
    assembly point: for each `linearize` output, the generator supplies the
    upstream repo nstruction `upstreamQueries`, the intermediate sets, and a
    `KzgQueryMapData` between the verifier queries and that upstream list.  The
    per-block `hpairP`/`hpairC`/`hclass` facts live inside the datum. -/
theorem KzgMultiPrepareWidths_of_upstreamDatum
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hUp : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∃ (upstreamSources : List PcsQuerySource)
        (upstreamQueries : List Midfall.Generator.Query)
        (setsG : Midfall.Generator.IntermediateSets)
        (qm : @KzgQueryMapData (Fr p) G₁ _
          (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries upstreamQueries),
        upstreamSources.mapM (fun source =>
          Midfall.Generator.queryFromPlan source R.plan.meta_ R.plan.data) =
            .ok upstreamQueries ∧
        Midfall.Generator.constructIntermediateSetsImpl upstreamQueries = .ok setsG ∧
        setsG.pointSets.length = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
          R.plan.proofLayout).numPointSets) :
    KzgMultiPrepareWidths R := by
  refine KzgMultiPrepareWidths_of_queryMap R ?_
  intro inst trace alg queries hlin
  obtain ⟨upstreamSources, upstreamQueries, setsG, qm, _hsrc, hGok, hLen⟩ :=
    hUp inst trace alg queries hlin
  exact ⟨upstreamQueries, setsG, qm, hGok, hLen⟩

/-- **ITEM 1: THE PLAN COUNT FROM THE QUERY MAP.** The Halo2 point-set count at
    `linearize`'s query vector equals the generator's upstream count
    (`constructIntermediateSets_pointSets_size_eq_of_queryMap`), and the generator's
    count is the plan's `numPointSets` (`planMeta_numPointSets_generator_of_validV3`
    plus `fromProtocol_qEvals_itemCount` through `plan_numPointSets_eq_meta`). The
    `KzgQueryMapData` is used for the Halo2-to-generator transfer. -/
theorem pointSets_length_eq_plan_of_queryMap
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    {queries : Array (VerifierQuery (Fr p) G₁)}
    {cm : Array (CD (Fr p) G₁)} {pointSets : Array (Array (Fr p))}
    {queriesG : List Generator.Query} {setsG : Generator.IntermediateSets}
    {generatorOrder : List Generator.Query} {generatorSets : Generator.IntermediateSets}
    (qm : @KzgQueryMapData (Fr p) G₁ _
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries queriesG)
    (hV : constructIntermediateSets (F := Fr p) (C := G₁)
      (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries = .ok (cm, pointSets))
    (hG : Generator.constructIntermediateSetsImpl queriesG = .ok setsG)
    (hgen : Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder)
    (hgenSets : Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets)
    (hpoint : generatorSets.pointSets = setsG.pointSets) :
    setsG.pointSets.length =
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets := by
  have hsize : pointSets.size = setsG.pointSets.length :=
    (KzgPartitionBridge_of_queryMap queries queriesG qm) (cm, pointSets) setsG hV hG
  obtain ⟨qs, sets, out, hq, hci, hsort, hlen⟩ :=
    planMeta_numPointSets_generator_of_validV3 R hR
  have hqs : qs = generatorOrder := by
    rw [hgen] at hq
    exact (Except.ok.inj hq).symm
  have hsets : sets = generatorSets := by
    rw [hqs] at hci
    exact Except.ok.inj (hci.symm.trans hgenSets)
  have hsort' : Generator.sortSets generatorSets = .ok out := by
    rw [← hsets]
    exact hsort
  have hout : out.pointSets.length = setsG.pointSets.length := by
    rw [sortSets_pointSets_length generatorSets out hsort', hpoint]
  have hpointSize : pointSets.size =
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets :=
    hsize.trans (hout.symm.trans (hlen.symm.trans (plan_numPointSets_eq_meta R hR).symm))
  exact hsize.symm.trans hpointSize

/-- The generator-side count, without the Halo2 success premise. This is the form
    the `LinearizeQueryMap` assembly consumes. -/
theorem setsG_pointSets_length_eq_plan_of_generator
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    {upstreamQueries : List Generator.Query} {setsG : Generator.IntermediateSets}
    {generatorOrder : List Generator.Query} {generatorSets : Generator.IntermediateSets}
    (hgen : Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder)
    (hgenSets : Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets)
    (hG : Generator.constructIntermediateSetsImpl upstreamQueries = .ok setsG)
    (hpoint : generatorSets.pointSets = setsG.pointSets) :
    setsG.pointSets.length =
      (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets := by
  obtain ⟨qs, sets, out, hq, hci, hsort, hlen⟩ :=
    planMeta_numPointSets_generator_of_validV3 R hR
  have hqs : qs = generatorOrder := by
    rw [hgen] at hq
    exact (Except.ok.inj hq).symm
  have hsets : sets = generatorSets := by
    rw [hqs] at hci
    exact Except.ok.inj (hci.symm.trans hgenSets)
  have hsort' : Generator.sortSets generatorSets = .ok out := by
    rw [← hsets]
    exact hsort
  have hout : out.pointSets.length = setsG.pointSets.length := by
    rw [sortSets_pointSets_length generatorSets out hsort', hpoint]
  exact hout.symm.trans (hlen.symm.trans (plan_numPointSets_eq_meta R hR).symm)

/-- `ValidV3`'s `generated`/`supported` clauses pin the plan's protocol to
    `fromConstraintSystem`, and `fromConstraintSystem` writes the literal
    `pcsBlockList`. This is the `dg`/`lc` decomposition item 2 consumes. -/
theorem plan_meta_pcsBlockList (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    ∃ (dg : Nat) (lc : List Nat),
      R.vk.cs.degree = .ok dg ∧
      R.plan.meta_.protocol.pcsQueries = pcsBlockList R.vk.cs 1 dg lc := by
  obtain ⟨dg, lc, hdeg, hpcs⟩ :=
    fromConstraintSystem_pcsQueries Features.solidity R.vk.cs 1 R.plan.meta_.protocol
      (plan_protocol_fromConstraintSystem R hR)
  exact ⟨dg, lc.toList, hdeg, hpcs⟩

/-- **ITEM 2: THE `queryFromPlan` MAPM HALF.** On a `ValidV3` render, the upstream
    source block A5 identifies (the literal `pcsBlockList` with the permutation-Z
    slice in upstream order) maps through `queryFromPlan` to an upstream query list,
    because `Generator.queries` succeeded and therefore ran the I-6 upstream-order
    check (`queries_assert_ok`). The z-position list is supplied explicitly, as in
    A5's `upstreamSources_filter_pcsBlockList`; nonemptiness is the datum's
    permutation-set condition, not a new `ValidV3` clause. -/
theorem upstreamDatum_of_validV3_ofZDatum
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (dg : Nat) (lc : List Nat)
    (hPcs : R.plan.meta_.protocol.pcsQueries = pcsBlockList R.vk.cs 1 dg lc)
    (zPositions : List Nat)
    (hzdef : zPositions = List.filterMap
      (fun x => if Generator.isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range R.plan.meta_.protocol.pcsQueries.length).zip
        R.plan.meta_.protocol.pcsQueries))
    (hzNonempty : zPositions ≠ []) :
    ∃ (upstreamSources : List PcsQuerySource)
      (upstreamQueries generatorOrder : List Generator.Query)
      (generatorSets upstreamSets : Generator.IntermediateSets),
      upstreamSources = (pcsAdviceBlock R.vk.cs ++
          pcsCommittedInstanceBlock R.vk.cs 1) ++
        permZUpstream (pcsNumPermutationZs R.vk.cs dg) ++
        (pcsLookupBlock R.vk.cs dg lc ++ pcsTrashBlock R.vk.cs ++
          pcsFixedBlock R.vk.cs ++ pcsPermutationCommonBlock R.vk.cs ++
          [PcsQuerySource.linearization]) ∧
      upstreamSources.mapM (fun source =>
        Generator.queryFromPlan source R.plan.meta_ R.plan.data) = .ok upstreamQueries ∧
      Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder ∧
      Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
      Generator.constructIntermediateSetsImpl upstreamQueries = .ok upstreamSets ∧
      generatorSets.pointSets = upstreamSets.pointSets := by
  obtain ⟨qs, _sets, _out, hq, _hci, _hsort, _hlen⟩ :=
    planMeta_numPointSets_generator_of_validV3 R hR
  have hassert := queries_assert_ok R.plan.meta_ R.plan.data qs hq
  obtain ⟨upstreamSources, upstreamQueries, generatorSets, upstreamSets,
    hsrc, _hzfilter, hmap, hgenSets, hupSets, hpoint⟩ :=
    upstreamSources_filter_pcsBlockList R.plan.meta_ R.plan.data qs R.vk.cs 1 dg lc
      zPositions hzdef hzNonempty hPcs hassert
  exact ⟨upstreamSources, upstreamQueries, qs, generatorSets, upstreamSets,
    hsrc, hmap, hq, hgenSets, hupSets, hpoint⟩

/-- The mapM half alone, in the exact `upstreamSources.mapM (queryFromPlan · meta
    data) = .ok upstreamQueries` shape `KzgMultiPrepareWidths_of_upstreamDatum`
    consumes. -/
theorem upstreamSources_mapM_of_validV3_ofZDatum
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (dg : Nat) (lc : List Nat)
    (hPcs : R.plan.meta_.protocol.pcsQueries = pcsBlockList R.vk.cs 1 dg lc)
    (zPositions : List Nat)
    (hzdef : zPositions = List.filterMap
      (fun x => if Generator.isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range R.plan.meta_.protocol.pcsQueries.length).zip
        R.plan.meta_.protocol.pcsQueries))
    (hzNonempty : zPositions ≠ []) :
    ∃ (upstreamSources : List PcsQuerySource) (upstreamQueries : List Generator.Query),
      upstreamSources = (pcsAdviceBlock R.vk.cs ++
          pcsCommittedInstanceBlock R.vk.cs 1) ++
        permZUpstream (pcsNumPermutationZs R.vk.cs dg) ++
        (pcsLookupBlock R.vk.cs dg lc ++ pcsTrashBlock R.vk.cs ++
          pcsFixedBlock R.vk.cs ++ pcsPermutationCommonBlock R.vk.cs ++
          [PcsQuerySource.linearization]) ∧
      upstreamSources.mapM (fun source =>
        Generator.queryFromPlan source R.plan.meta_ R.plan.data) = .ok upstreamQueries := by
  obtain ⟨upstreamSources, upstreamQueries, _generatorOrder, _generatorSets, _upstreamSets,
    hsrc, hmap, _hgen, _hgenSets, _hupSets, _hpoint⟩ :=
    upstreamDatum_of_validV3_ofZDatum R hR dg lc hPcs zPositions hzdef hzNonempty
  exact ⟨upstreamSources, upstreamQueries, hsrc, hmap⟩

/-- `ValidV3`/`SupportedV2` do not force the permutation argument to have a column:
    `permutationCommitmentsMatch` only equates the two sizes, so the empty permutation
    argument satisfies every frozen clause. The minimal key-side clause the upstream
    datum needs is therefore that the key's permutation argument is nonempty. The
    deployed poseidon profile observes eight columns (see `PoseidonCoherence`/
    `PoseidonEnv`), so this is not an extra statement about the deployment, only the
    generic interface clause. -/
def PermutationColumnsNonempty (vk : VerifyingKey (Fr p) G₁) : Prop :=
  vk.cs.permutation.getColumns.toList ≠ []

/-- Nonempty permutation columns plus `WellFormed`'s `3 ≤ csDegree` make the literal
    `pcsBlockList`'s permutationZ set count positive. -/
theorem pcsNumPermutationZs_pos_of_columns
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (dg : Nat) (hdeg : R.vk.cs.degree = .ok dg)
    (hcols : PermutationColumnsNonempty R.vk) :
    0 < pcsNumPermutationZs R.vk.cs dg := by
  have hdg : dg = R.vk.csDegree := by
    have h1 := hR.supported.wf.csDegreeMatches
    rw [hdeg] at h1
    exact Except.ok.inj h1
  have hchunk : 3 ≤ dg := by rw [hdg]; exact hR.supported.wf.chunkLenPositive
  unfold pcsNumPermutationZs
  rw [ite_eq_right ?h]
  · unfold Midfall.Halo2.divCeil
    have hlen : 0 < R.vk.cs.permutation.getColumns.toList.length :=
      List.length_pos_of_ne_nil hcols
    exact Nat.div_pos (by omega) (by omega)
  · intro h
    exact hcols (List.isEmpty_iff.mp h)

/-- **ITEM 2, NOW WITH ONLY THE KEY-SIDE CLAUSE.** The z-position list, its
    nonemptiness and the `dg`/`lc` decomposition are all derived: `dg`/`lc` from
    `plan_meta_pcsBlockList`, the z list as `pcsZPositions` at that literal block,
    and nonemptiness from `PermutationColumnsNonempty` via
    `pcsNumPermutationZs_pos_of_columns`/`pcsZPositions_nonempty`. The conclusion is
    the full upstream source block, its `queryFromPlan` map, the generator `queries`
    result, both set constructions, and the set equality. -/
theorem upstreamDatum_of_validV3
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcols : PermutationColumnsNonempty R.vk) :
    ∃ (dg : Nat) (lc : List Nat),
      R.vk.cs.degree = .ok dg ∧
      ∃ (upstreamSources : List PcsQuerySource)
        (upstreamQueries generatorOrder : List Generator.Query)
        (generatorSets upstreamSets : Generator.IntermediateSets),
        upstreamSources = (pcsAdviceBlock R.vk.cs ++
            pcsCommittedInstanceBlock R.vk.cs 1) ++
          permZUpstream (pcsNumPermutationZs R.vk.cs dg) ++
          (pcsLookupBlock R.vk.cs dg lc ++ pcsTrashBlock R.vk.cs ++
            pcsFixedBlock R.vk.cs ++ pcsPermutationCommonBlock R.vk.cs ++
            [PcsQuerySource.linearization]) ∧
        upstreamSources.mapM (fun source =>
          Generator.queryFromPlan source R.plan.meta_ R.plan.data) = .ok upstreamQueries ∧
        Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder ∧
        Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
        Generator.constructIntermediateSetsImpl upstreamQueries = .ok upstreamSets ∧
        generatorSets.pointSets = upstreamSets.pointSets := by
  obtain ⟨dg, lc, hdeg, hPcs⟩ := plan_meta_pcsBlockList R hR
  have hk : 0 < pcsNumPermutationZs R.vk.cs dg :=
    pcsNumPermutationZs_pos_of_columns R hR dg hdeg hcols
  let z := pcsZPositions (p := p) R.vk.cs 1 dg lc
  have hzdef : z = List.filterMap
      (fun x => if Generator.isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range R.plan.meta_.protocol.pcsQueries.length).zip
        R.plan.meta_.protocol.pcsQueries) := by
    rw [hPcs]
    rfl
  have hzn : z ≠ [] := pcsZPositions_nonempty R.vk.cs 1 dg lc hk
  obtain ⟨upstreamSources, upstreamQueries, generatorOrder, generatorSets, upstreamSets,
    hsrc, hmap, hgen, hgenSets, hupSets, hpoint⟩ :=
    upstreamDatum_of_validV3_ofZDatum R hR dg lc hPcs z hzdef hzn
  exact ⟨dg, lc, hdeg, upstreamSources, upstreamQueries, generatorOrder, generatorSets,
    upstreamSets, hsrc, hmap, hgen, hgenSets, hupSets, hpoint⟩

/-- The mapM half alone, with the z/dg/lc inputs derived. -/
theorem upstreamSources_mapM_of_validV3
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcols : PermutationColumnsNonempty R.vk) :
    ∃ (dg : Nat) (lc : List Nat),
      R.vk.cs.degree = .ok dg ∧
      ∃ (upstreamSources : List PcsQuerySource) (upstreamQueries : List Generator.Query),
        upstreamSources = (pcsAdviceBlock R.vk.cs ++
            pcsCommittedInstanceBlock R.vk.cs 1) ++
          permZUpstream (pcsNumPermutationZs R.vk.cs dg) ++
          (pcsLookupBlock R.vk.cs dg lc ++ pcsTrashBlock R.vk.cs ++
            pcsFixedBlock R.vk.cs ++ pcsPermutationCommonBlock R.vk.cs ++
            [PcsQuerySource.linearization]) ∧
        upstreamSources.mapM (fun source =>
          Generator.queryFromPlan source R.plan.meta_ R.plan.data) = .ok upstreamQueries := by
  obtain ⟨dg, lc, hdeg, upstreamSources, upstreamQueries, _generatorOrder, _generatorSets,
    _upstreamSets, hsrc, hmap, _hgen, _hgenSets, _hupSets, _hpoint⟩ :=
    upstreamDatum_of_validV3 R hR hcols
  exact ⟨dg, lc, hdeg, upstreamSources, upstreamQueries, hsrc, hmap⟩

/-- **THE `LinearizeQueryMap` ASSEMBLY.** Once the per-pair datum supplies, for
    every `linearize` output, the generator query list, the generator's own
    `queries` result, both `constructIntermediateSetsImpl` results, the point-set
    equality and the `KzgQueryMapData`, the plan/count half closes the existential
    `LinearizeQueryMap` requires. The mapM/source-block half is
    `upstreamDatum_of_validV3`, used by the datum's producer under the minimal
    key-side clause `PermutationColumnsNonempty`. -/
theorem LinearizeQueryMap_of_upstreamDatum
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hUp : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∃ (upstreamQueries generatorOrder : List Generator.Query)
        (generatorSets setsG : Generator.IntermediateSets)
        (qm : @KzgQueryMapData (Fr p) G₁ _
          (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries upstreamQueries),
        Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder ∧
        Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
        Generator.constructIntermediateSetsImpl upstreamQueries = .ok setsG ∧
        generatorSets.pointSets = setsG.pointSets) :
    LinearizeQueryMap R := by
  intro inst trace alg queries hlin
  obtain ⟨upstreamQueries, generatorOrder, generatorSets, setsG, qm,
    hgen, hgenSets, hGok, hpoint⟩ := hUp inst trace alg queries hlin
  exact ⟨upstreamQueries, setsG, qm, hGok,
    setsG_pointSets_length_eq_plan_of_generator R hR hgen hgenSets hGok hpoint⟩

/-- **`PrepareLogSlots` FROM EXACTLY THE TWO NAMED RESIDUALS.** The parseTrace
    block, the KZG scalar block, and the plan's eval count (`numEvals`, proved in
    this file) are the whole of the bridge; nothing else is assumed. -/
theorem PrepareLogSlots_of_A6_KZG (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hA6 : ParseTraceSchedule R) (hKZG : KzgMultiPrepareWidths R) :
    Midfall.LoweringV3.PrepareLogSlots R := by
  obtain ⟨nParse, hParse, hQuot⟩ := hA6
  refine PrepareLogSlots_of_parsed R hR nParse
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
      R.plan.proofLayout).numPointSets hParse hKZG hQuot ?_
  rfl

/-- **`PrepareLogSlots` WITH THE A6 WIDTH BLOCK DISCHARGED.** The parseTrace
    schedule is a theorem of `ValidV3` (`parseTraceSchedule`); the KZG scalar
    block is the only remaining premise. -/
theorem PrepareLogSlots_of_advicePhase (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hpin : AdvicePhaseCountFit R.vk)
    (hKZG : KzgMultiPrepareWidths R) :
    Midfall.LoweringV3.PrepareLogSlots R :=
  PrepareLogSlots_of_A6_KZG R hR (parseTraceSchedule_of_advicePhase R hR hpin) hKZG

/-- **`PrepareLogSlots` with the A6 parse side discharged.** Only the KZG scalar
    block remains. -/
theorem PrepareLogSlots_of_parseTrace (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hKZG : KzgMultiPrepareWidths R) :
    Midfall.LoweringV3.PrepareLogSlots R :=
  PrepareLogSlots_of_A6_KZG R hR (parseTraceSchedule R hR) hKZG

/-- **THE A6 LINK.** If `prepare`'s log widths are the emitted parser's own
    schedule `R.tpEvents`, then A6's `tp_events_slots` closes `PrepareLogSlots`
    outright. This is the exact project-level refinement A6's report names; the
    remaining width walk is `PrepareLogSlots_of_A6_KZG`'s two residuals. -/
theorem PrepareLogSlots_of_tpEvents (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R)
    (hEv : ∀ (inst : Array (Fr p)) (π : Bytes)
        (d : DualMSM (Fr p) G₁ G₂ Gₜ) (t : Transcript),
      (Midfall.Halo2.prepare (Gₜ := Gₜ) R.E Features.solidity R.vk
          [[1]] [[inst.toList]]).run (Transcript.initFromBytes π) = .ok (d, t) →
        t.log.toList.map (fun r =>
          if r.1 = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
          else Midfall.Lowering.WireSlot.fr) =
          R.tpEvents.filterMap Midfall.LoweringV3.TranscriptRows.TEv.slot?) :
    Midfall.LoweringV3.PrepareLogSlots R := by
  intro inst π d t hrun
  rw [hEv inst π d t hrun]
  exact Midfall.LoweringV3.TranscriptRows.tp_events_slots R hR

/-- **END-TO-END FROM THE KZG SCALAR BLOCK ALONE.** The full `EndToEndV3`
    statement. The A6 `parseTrace` width block is DISCHARGED: `parseTraceSchedule`
    proves `ParseTraceSchedule` from `ValidV3` (D-GATE7's
    `WellFormed.advicePhaseTotal` supplies the phase-vector length the count
    needs). The KZG `multiPrepare` point-set count is the only extra premise.
    Nothing is added to `ValidV3`, to any row or to the root. -/
theorem end_to_end_of_A6_KZG (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (product : Midfall.Yul.PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : YulSemantics.EVM.ExecEnv) (Lyt : YulSemantics.EVM.Layout) (vkAddr : YulSemantics.EVM.U256)
    (hdep : Midfall.LoweringV2.DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hcd36 : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 36)
    (hside : ∀ cd, Midfall.LoweringV3.calldataOfV3 R π inst = .ok cd →
      Midfall.LoweringV2.SoundSide R keccak256 cd ∧
        Midfall.LoweringV2.CompleteSide R keccak256 cd)
    (hKZG : KzgMultiPrepareWidths R) :
    EndToEndV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside :=
  end_to_end_of_prepareLogSlots R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec
    inst π hn hcd36 hside (PrepareLogSlots_of_parseTrace R hR hKZG)

/-- **END-TO-END FROM THE NAMED D1 QUERY MAP.** The same `EndToEndV3` statement as
    `end_to_end_of_A6_KZG`, with `LinearizeQueryMap` as the only extra premise. This is
    the form a `ValidV3` render consumes once the `linearize` ↔ `Generator.Query`
    correspondence is supplied; nothing is added to `ValidV3`, a row, a bundle or the
    root. -/
theorem end_to_end_of_validV3 (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (product : Midfall.Yul.PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : YulSemantics.EVM.ExecEnv) (Lyt : YulSemantics.EVM.Layout) (vkAddr : YulSemantics.EVM.U256)
    (hdep : Midfall.LoweringV2.DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hcd36 : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 36)
    (hside : ∀ cd, Midfall.LoweringV3.calldataOfV3 R π inst = .ok cd →
      Midfall.LoweringV2.SoundSide R keccak256 cd ∧
        Midfall.LoweringV2.CompleteSide R keccak256 cd)
    (hMap : LinearizeQueryMap R) :
    EndToEndV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside :=
  end_to_end_of_A6_KZG R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside
    (KzgMultiPrepareWidths_of_linearizeQueryMap R hMap)

/-- **END-TO-END FROM THE PER-PAIR DATUM.** The same `EndToEndV3` statement as
    `end_to_end_of_validV3`, with the per-pair datum supplied directly: the
    generator query list, its `queries` result, both `constructIntermediateSetsImpl`
    results, the point-set equality and the `KzgQueryMapData`. The plan/count half
    is discharged by `LinearizeQueryMap_of_upstreamDatum`; the mapM/source-block
    half is the producer's `upstreamDatum_of_validV3` under the minimal key-side
    clause `PermutationColumnsNonempty`. -/
theorem end_to_end_of_validV3_of_upstreamDatum
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (product : Midfall.Yul.PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : YulSemantics.EVM.ExecEnv) (Lyt : YulSemantics.EVM.Layout) (vkAddr : YulSemantics.EVM.U256)
    (hdep : Midfall.LoweringV2.DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hcd36 : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 36)
    (hside : ∀ cd, Midfall.LoweringV3.calldataOfV3 R π inst = .ok cd →
      Midfall.LoweringV2.SoundSide R keccak256 cd ∧
        Midfall.LoweringV2.CompleteSide R keccak256 cd)
    (hUp : ∀ (inst : Array (Fr p)) (trace : VerifierTrace (Fr p) G₁)
      (alg : Verifier.AlgebraRead (Fr p) G₁)
      (queries : Array (VerifierQuery (Fr p) G₁)),
      Verifier.linearize (p := p) (delta := R.E.delta) R.vk
        (adviceCommitments := trace.adviceCommitments)
        (committedInstances := if Features.solidity.committedInstances then
          #[#[(1 : G₁)]] else arrayReplicate (#[#[inst.toList.toArray]]).size
            (#[] : Array G₁))
        (y := trace.y) (beta := trace.beta) (gamma := trace.gamma) (theta := trace.theta)
        (trashChallenge := trace.trashChallenge) (challenges := trace.challenges) alg
        = .ok queries →
      ∃ (upstreamQueries generatorOrder : List Generator.Query)
        (generatorSets setsG : Generator.IntermediateSets)
        (qm : @KzgQueryMapData (Fr p) G₁ _
          (kzgCommitBeq (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) queries upstreamQueries),
        Generator.queries R.plan.meta_ R.plan.data = .ok generatorOrder ∧
        Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
        Generator.constructIntermediateSetsImpl upstreamQueries = .ok setsG ∧
        generatorSets.pointSets = setsG.pointSets) :
    EndToEndV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside :=
  end_to_end_of_validV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside
    (LinearizeQueryMap_of_upstreamDatum R hR hUp)

/-- **END-TO-END FROM THE A6 STATIC SCHEDULE.** The A6 half is stated exactly as
    the project-level refinement between `prepare`'s log widths and `R.tpEvents`;
    A6's `tp_events_slots` then produces the plan slots. This absorbs the KZG
    q-eval block into the event list (whose `tpEvents` already carries the plan's
    `numPointSets` scalars), so it is the strongest A6-only link; the split form
    with both residuals named is `end_to_end_of_A6_KZG`. -/
theorem end_to_end_of_tpEvents (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (product : Midfall.Yul.PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : YulSemantics.EVM.ExecEnv) (Lyt : YulSemantics.EVM.Layout) (vkAddr : YulSemantics.EVM.U256)
    (hdep : Midfall.LoweringV2.DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hcd36 : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 36)
    (hside : ∀ cd, Midfall.LoweringV3.calldataOfV3 R π inst = .ok cd →
      Midfall.LoweringV2.SoundSide R keccak256 cd ∧
        Midfall.LoweringV2.CompleteSide R keccak256 cd)
    (hEv : ∀ (inst : Array (Fr p)) (π : Bytes)
        (d : DualMSM (Fr p) G₁ G₂ Gₜ) (t : Transcript),
      (Midfall.Halo2.prepare (Gₜ := Gₜ) R.E Features.solidity R.vk
          [[1]] [[inst.toList]]).run (Transcript.initFromBytes π) = .ok (d, t) →
        t.log.toList.map (fun r =>
          if r.1 = g1CompressedWidth then Midfall.Lowering.WireSlot.g1
          else Midfall.Lowering.WireSlot.fr) =
          R.tpEvents.filterMap Midfall.LoweringV3.TranscriptRows.TEv.slot?) :
    EndToEndV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hcd36 hside :=
  end_to_end_of_prepareLogSlots R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec
    inst π hn hcd36 hside (PrepareLogSlots_of_tpEvents R hR hEv)

/-! ### Gates for the two named residuals -/

#check @ParseTraceSchedule
#check @AdvicePhaseCountFit
#check @adviceReadCount_eq_phaseSize
#check @advicePhaseCountFit_of_wellFormed
#check @parseTraceSchedule
#check @parseTrace_widths
#check @protocol_parseCounts
#check @parseTraceSchedule_of_advicePhase
#check @PrepareLogSlots_of_advicePhase
#check @KzgMultiPrepareWidths
#check @PrepareLogSlots_of_A6_KZG
#check @PrepareLogSlots_of_tpEvents
#check @end_to_end_of_A6_KZG
#check @end_to_end_of_tpEvents

#cone_sorries Midfall.LoweringV3.end_to_end_of_A6_KZG
#cone_sorries Midfall.LoweringV3.end_to_end_of_tpEvents

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_of_tpEvents
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.PrepareLogSlots_of_tpEvents
  [propext, Classical.choice, Quot.sound, sorryAx] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.adviceReadCount_eq_phaseSize
  [propext, Classical.choice, Quot.sound] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.parseTraceSchedule
  [propext, Classical.choice, Quot.sound] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.parseTrace_widths
  [propext, Classical.choice, Quot.sound] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.protocol_parseCounts
  [propext, Classical.choice, Quot.sound] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.parseTraceSchedule_of_advicePhase
  [propext, Classical.choice, Quot.sound] native []

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_of_A6_KZG
  [propext, Classical.choice, Quot.sound, sorryAx] native []

#assert_axioms multiPrepare_constructIntermediateSets_ok
  [propext, Classical.choice, Quot.sound]
#assert_axioms constructIntermediateSets_empty [propext, Classical.choice, Quot.sound]
#assert_axioms pointSetsCount_forces_zero [propext, Classical.choice, Quot.sound]
#assert_axioms MultiPrepareBlockWidthAt_of_pointSets
  [propext, Classical.choice, Quot.sound]
#assert_axioms MultiPrepareBlockWidth_of_pointSets
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgMultiPrepareWidths_of_pointSets
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgMultiPrepareWidths_of_kzgPartitionBridge
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgPartitionBridge_of_queryMap
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgMultiPrepareWidths_of_queryMap
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgMultiPrepareWidths_of_upstreamDatum
  [propext, Classical.choice, Quot.sound]
#assert_axioms constructIntermediateSets_pointSets_size_eq_of_queryMap
  [propext, Classical.choice, Quot.sound]
#assert_axioms findIdx?_eq_of_equiv
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgQueryMapData.ofList
  [propext, Classical.choice, Quot.sound]
#assert_axioms pairQueries_fst
  [propext, Classical.choice, Quot.sound]
#assert_axioms pairQueries_snd
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_getLast?_some
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_mapM_ok
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_assert_ok
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_getLast?_some
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_last_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_linearization
  [propext, Classical.choice, Quot.sound]
#assert_axioms pcsQueries_append_linearization_last
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_advice_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_committedInstance_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_fixed_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_lookupMultiplicity_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_lookupHelper_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_trash_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_permutationCommon_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_permutationZ_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_lookupAccumulator_rotation
  [propext, Classical.choice, Quot.sound]
#assert_axioms PcsQuerySource.rotation_linearization
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgQueryMapData.ofRotations
  [propext, Classical.choice, Quot.sound]
#assert_axioms Data.new_dummyEvalWords
  [propext, Classical.choice, Quot.sound]
#assert_axioms pass1_step1_sim
  [propext, Classical.choice, Quot.sound]
#assert_axioms numPointSets_eq_of_queries_pointSets_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms constructIntermediateSetsImpl_pointSets_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms rotateOmega_eq_mul_zpow
  [propext, Classical.choice, Quot.sound]
#assert_axioms rotateOmega_injective_on_rotations
  [propext, Classical.choice, Quot.sound]
#assert_axioms rotationKey_injective
  [propext, Classical.choice, Quot.sound]
#assert_axioms exists_pointKey
  [propext, Classical.choice, Quot.sound]
#assert_axioms plan_numPointSets_eq_meta
  [propext, Classical.choice, Quot.sound]
#assert_axioms planMeta_numPointSets_generator
  [propext, Classical.choice, Quot.sound]
#assert_axioms planMeta_numPointSets_generator_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms planMeta_numPointSets_of_generated
  [propext, Classical.choice, Quot.sound]
#assert_axioms planMeta_numPointSets_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms intermediateSets_parts
  [propext, Classical.choice, Quot.sound]
#assert_axioms collectQueries_back?
  [propext, Classical.choice, Quot.sound]
#assert_axioms collectQueries_parts
  [propext, Classical.choice, Quot.sound]
#assert_axioms Trash.Evaluated.queries_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms Permutation.CommonEvaluated.queries_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms Logup.Evaluated.queries_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms mem_mapM
  [propext, Classical.choice, Quot.sound]
#assert_axioms fixedQueryFn_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms collectQueries_fixed_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms adviceQueryFn_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms instanceQueryFn_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms adviceBlock_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms instanceBlock_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms VerifierQuery.new_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms Permutation.Evaluated.queries_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms perProofQueries_parts
  [propext, Classical.choice, Quot.sound]
#assert_axioms lookupBlock_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms trashBlock_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms perProofQueries_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms collectQueries_perProof_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms ProtocolPlan.fromConstraintSystem_pcsQueries
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.fromConstraintSystem_pcsQueries
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_append_ok
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_flatten_ok
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_pcsBlocks
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_blockList_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms queries_pcsBlocks_lengths
  [propext, Classical.choice, Quot.sound]
#assert_axioms collectQueries_single_blocks
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_flatten_length_const
  [propext, Classical.choice, Quot.sound]
#assert_axioms Permutation.Evaluated.queries_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Logup.Evaluated.queries_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Permutation.CommonEvaluated.queries_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Trash.Evaluated.queries_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms adviceBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms instanceBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms fixedBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms trashBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms mapM_flatten_length_of_filter
  [propext, Classical.choice, Quot.sound]
#assert_axioms lookupBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.permZUpstream_length_eq
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsAdviceBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsCommittedInstanceBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsFixedBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsPermutationCommonBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsTrashBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.Generator.pcsLookupBlock_length
  [propext, Classical.choice, Quot.sound]
#assert_axioms Permutation.Evaluated.queries_length_permZUpstream
  [propext, Classical.choice, Quot.sound]
#assert_axioms permZBlock_three
  [propext, Classical.choice, Quot.sound]
#assert_axioms permZUpstream_three
  [propext, Classical.choice, Quot.sound]
#assert_axioms permZBlock_three_beq_upstream
  [propext, Classical.choice, Quot.sound]
#assert_axioms flatten_map_ite
  [propext, Classical.choice, Quot.sound]
#assert_axioms flatten_map_singleton
  [propext, Classical.choice, Quot.sound]
#assert_axioms filter_range_pred_rev
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamBlock_permZBlock
  [propext, Classical.choice, Quot.sound]
#assert_axioms assertPermutationQueryOrderIsUpstreamEquivalent_parts
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamSources_zslice
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamSources_filter_pcsBlockList
  [propext, Classical.choice, Quot.sound]
#assert_axioms exists_pairQueries
  [propext, Classical.choice, Quot.sound]
#assert_axioms KzgQueryMapData.ofPairQueries
  [propext, Classical.choice, Quot.sound]
#assert_axioms Data.new_computedQuotientComm
  [propext, Classical.choice, Quot.sound]
#assert_axioms Data.new_commsNumericOrIdentity
  [propext, Classical.choice, Quot.sound]
#assert_axioms VerifierMemoryLayout.new_numericBases
  [propext, Classical.choice, Quot.sound]
#assert_axioms ecPointBeq_quotient_of_numeric
  [propext, Classical.choice, Quot.sound]
#assert_axioms ecPointBeq_quotient_g1
  [propext, Classical.choice, Quot.sound]
#assert_axioms ecPointBeq_self
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_comm_classification
  [propext, Classical.choice, Quot.sound]
#assert_axioms ecPointBeq_quotient_of_classification
  [propext, Classical.choice, Quot.sound]
#assert_axioms listGetMut_mem
  [propext, Classical.choice, Quot.sound]
#assert_axioms hashMapGet_mem
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_comm_numericOrG1_of_ne_linearization
  [propext, Classical.choice, Quot.sound]
#assert_axioms queryFromPlan_comm_ne_quotient
  [propext, Classical.choice, Quot.sound]
#assert_axioms plan_data_commsNumericOrIdentity
  [propext, Classical.choice, Quot.sound]
#assert_axioms kzgCommitBeq_linear_onePiece
  [propext, Classical.choice, Quot.sound]
#assert_axioms kzgCommitBeq_linear_offdiag
  [propext, Classical.choice, Quot.sound]
#assert_axioms kzgCommitBeq_linear_self
  [propext, Classical.choice, Quot.sound]
#assert_axioms kzgCommitBeq_linear_self_eq
  [propext, Classical.choice, Quot.sound]
#assert_axioms VerifierQuery.newLinear_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms computeLinearizationCommitment_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms VerifierQuery.newLinear_commitment
  [propext, Classical.choice, Quot.sound]
#assert_axioms computeLinearizationCommitment_commitment
  [propext, Classical.choice, Quot.sound]
#assert_axioms linearize_back?_point
  [propext, Classical.choice, Quot.sound]
#assert_axioms rotateOmega_zero
  [propext, Classical.choice, Quot.sound]
#assert_axioms linearize_back?_point_rotateOmega
  [propext, Classical.choice, Quot.sound]
#assert_axioms multiPrepare_width_empty [propext, Classical.choice, Quot.sound]
#assert_axioms multiPrepare_width_at [propext, Classical.choice, Quot.sound]
#assert_axioms MultiPrepareBlockWidth.eq_zero_of_empty_run
  [propext, Classical.choice, Quot.sound]
#assert_axioms PrepareLogSlots_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms readScheduleAgrees_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms end_to_end_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms pointSets_length_eq_plan_of_queryMap
  [propext, Classical.choice, Quot.sound]
#assert_axioms setsG_pointSets_length_eq_plan_of_generator
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamDatum_of_validV3_ofZDatum
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamSources_mapM_of_validV3_ofZDatum
  [propext, Classical.choice, Quot.sound]
#assert_axioms plan_meta_pcsBlockList
  [propext, Classical.choice, Quot.sound]
#assert_axioms PermutationColumnsNonempty
  [propext, Classical.choice, Quot.sound]
#assert_axioms pcsNumPermutationZs_pos_of_columns
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamDatum_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms upstreamSources_mapM_of_validV3
  [propext, Classical.choice, Quot.sound]
#assert_axioms LinearizeQueryMap_of_upstreamDatum
  [propext, Classical.choice, Quot.sound]
#assert_axioms end_to_end_of_validV3_of_upstreamDatum
  [propext, Classical.choice, Quot.sound]

end Composition

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage
set_option maxHeartbeats 2000000 in
theorem xcript_advice_count {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (QAdv : List G₁)
    (hAdv : QAdv.length =
      (R.vk.cs.phases.map (fun ph => (TranscriptRows.phaseCols R.vk.cs ph).length)).sum) :
    QAdv.length =
      Midfall.Lowering.sumNat (R.plan.proofLayout.advicePhases.map (fun s => s.itemCount)) := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hL, _hprot, _hLook, _hChunks,
    _hPerm, _hTrash, _hQuot, _hAdv, _hChall, _hUP, _hUser, _hInst, _hTrunc, _hLookM,
    _hPermM, _hTrashM, _hLH⟩ := TranscriptRows.tp_planFacts hR
  subst hmeta
  subst hlay
  have hfacts := TranscriptRows.tp_fromProtocol hL
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hcounts := protocol_parseCounts (p := p) R.vk hf
    (plan_protocol_fromConstraintSystem R hR)
  have hphase := advicePhaseCountFit_of_wellFormed R.vk hf
  have hsum := hfacts.adviceSum
  have hAdv' : (R.vk.cs.phases.map (fun ph => (TranscriptRows.phaseCols R.vk.cs ph).length)).sum =
      adviceReadCount R.vk.cs 1 := by
    simp [adviceReadCount, TranscriptRows.phaseCols, advicePhaseCols, Nat.one_mul]
  rw [hAdv, hAdv', hphase]
  exact (hsum.trans hcounts.2.2.2.2.2).symm

set_option maxHeartbeats 2000000 in
theorem xcript_quotient_count {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (Qg : List G₁)
    (hQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else R.vk.domain.getQuotientPolyDegree)) :
    Qg.length = R.plan.proofLayout.quotientLimbs.itemCount := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hL, _hprot, _hLook, _hChunks,
    _hPerm, _hTrash, _hQuot, _hAdv, _hChall, _hUP, _hUser, _hInst, _hTrunc, _hLookM,
    _hPermM, _hTrashM, _hLH⟩ := TranscriptRows.tp_planFacts hR
  subst hmeta
  subst hlay
  have hfacts := TranscriptRows.tp_fromProtocol hL
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hcounts := protocol_parseCounts (p := p) R.vk hf
    (plan_protocol_fromConstraintSystem R hR)
  rw [hQ, hfacts.quotient, hcounts.2.2.2.2.1]
  rfl

set_option maxHeartbeats 2000000 in
theorem xcript_qs_count {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Render p G₁ G₂ Gₜ) (qs : List (Fr p)) (hQs : qs.length = R.nSets) :
    qs.length = R.plan.proofLayout.qEvals.itemCount := by
  rw [hQs]
  rfl


theorem xcript_prefix_count {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (Qg : List G₁)
    (hQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else R.vk.domain.getQuotientPolyDegree)) :
    (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout
        R.plan.proofLayout).prefixG1Count =
      R.plan.proofLayout.nonQuotientG1Count + Qg.length := by
  rw [Midfall.Lowering.sum_commitmentReadGroups R.plan.proofLayout,
    ProofCalldataLayout.commitmentG1Count, xcript_quotient_count R hR Qg hQ]

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem xcript_evals_count (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (QEv : List (Fr p)) (hEv : QEv.length =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals) :
    QEv.length = R.plan.proofLayout.evals.itemCount := by
  rw [hEv]
  rfl

theorem xcript_evals_count_of_decoded (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    {cd : Bytes} {ms : List (Msg (Fr p) G₁)} {instW : Array Word256}
    {inst : Array (Fr p)} (hdec : Decoded R cd ms instW inst) :
    ∃ QEv : List (Fr p), QEv.length = R.plan.proofLayout.evals.itemCount := by
  obtain ⟨QPre, QEv, fCom, qs, pi, _hms, _hPre, hEv, _hQs⟩ :=
    TranscriptRows.decoded_ms_split R hdec
  exact ⟨QEv, xcript_evals_count R QEv hEv⟩

theorem foldl_byteLen_eq_sumNat (l : List ProofSection) :
    l.foldl (fun a s => a + s.byteLen) 0 =
      Midfall.Lowering.sumNat (l.map (fun s : ProofSection => s.byteLen)) := by
  rw [show Midfall.Lowering.sumNat (l.map (fun s : ProofSection => s.byteLen)) =
      (l.map (fun s : ProofSection => s.byteLen)).foldl (fun a b => a + b) 0 from rfl]
  rw [List.foldl_map]

/-- The four `MirrorAt` windows at the schedule's block lengths and the
    `fromProtocol` cursor starts. -/
structure XcriptSectionWindows (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (QAdv Qg : List G₁) : Prop where
  adviceLen : R.plan.proofLayout.advicePhases.foldl (fun a s => a + s.byteLen) 0 =
    g1EipWidth * QAdv.length
  quotientStart : R.plan.proofLayout.quotientLimbs.start =
    R.plan.proofLayout.quotientCommCptr
  quotientLen : R.plan.proofLayout.quotientLimbs.byteLen =
    g1EipWidth * Qg.length
  fComStart : R.plan.proofLayout.fCom.start = R.plan.proofLayout.wCptr
  fComLen : R.plan.proofLayout.fCom.byteLen = g1EipWidth
  piStart : R.plan.proofLayout.pi.start =
    R.plan.proofLayout.qEvalCptr + R.plan.proofLayout.qEvals.byteLen
  piLen : R.plan.proofLayout.pi.byteLen = g1EipWidth
  quotientComm : R.plan.proofLayout.quotientCommCptr =
    R.plan.proofLayout.proofCptr + g1EipWidth * R.plan.proofLayout.nonQuotientG1Count
  qEvalsStart : R.plan.proofLayout.qEvals.start = R.plan.proofLayout.qEvalCptr

set_option maxHeartbeats 4000000 in
theorem xcriptSectionWindows_of_valid (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) {QAdv Qg : List G₁}
    (hAdv : QAdv.length =
      (R.vk.cs.phases.map (fun ph => (TranscriptRows.phaseCols R.vk.cs ph).length)).sum)
    (hQ : Qg.length = (if Features.solidity.outerSingleHCommitment then 1
      else R.vk.domain.getQuotientPolyDegree)) :
    XcriptSectionWindows R QAdv Qg := by
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hLay, _hc1, _hc2, _hc3,
    _hc4, _hc5, _hc6, _hc7, _hc8, _hup, _huser, _hnInst, _htrunc, _hnLook, _hnPerm,
    _hnTrash, _hLH⟩ := TranscriptRows.tp_planFacts (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) hR
  have facts := TranscriptRows.tp_fromProtocol hLay
  have starts := TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
    meta_.numPointSets hLay
  obtain ⟨hQStart, _hEvalCptr, _hEvStart, _hW, hFStart, _hQEvalCptr, hQEvalsStart,
    hPiStart, hFByte, hPiByte, _hFCount, _hPiCount⟩ := starts
  have hQComm := TranscriptRows.fromProtocol_quotientComm meta_.protocol meta_.numEvals
    meta_.numPointSets hLay
  have hAdvCount := xcript_advice_count R hR QAdv hAdv
  have hQCount := xcript_quotient_count R hR Qg hQ
  have hAdvFL : QAdv.length =
      Midfall.Lowering.sumNat (L.advicePhases.map (fun s : ProofSection => s.itemCount)) := by
    simpa [hlay] using hAdvCount
  have hQFL : Qg.length = L.quotientLimbs.itemCount := by
    simpa [hlay] using hQCount
  have hAdvL : L.advicePhases.foldl (fun a s => a + s.byteLen) 0 =
      g1EipWidth * QAdv.length := by
    rw [foldl_byteLen_eq_sumNat]
    have hmap : L.advicePhases.map (fun s : ProofSection => s.byteLen) =
        L.advicePhases.map (fun s : ProofSection => s.itemCount * Midfall.Generator.g1Bytes) := by
      apply List.map_congr_left
      intro s hs
      exact facts.adviceByteLen s hs
    rw [hmap]
    calc
      Midfall.Lowering.sumNat (L.advicePhases.map (fun s : ProofSection => s.itemCount * Midfall.Generator.g1Bytes))
          = Midfall.Lowering.sumNat
              ((L.advicePhases.map (fun s : ProofSection => s.itemCount)).map (fun c => c * Midfall.Generator.g1Bytes)) := by
            rw [List.map_map]; rfl
      _ = Midfall.Generator.g1Bytes * Midfall.Lowering.sumNat
              (L.advicePhases.map (fun s : ProofSection => s.itemCount)) :=
            Midfall.Lowering.sumNat_map_mul Midfall.Generator.g1Bytes _
      _ = Midfall.Generator.g1Bytes * QAdv.length := by rw [← hAdvFL]
      _ = g1EipWidth * QAdv.length := by rw [show Midfall.Generator.g1Bytes = g1EipWidth from rfl]
  have hQuotL : L.quotientLimbs.byteLen = g1EipWidth * Qg.length := by
    rw [facts.quotientByte, ← facts.quotient, ← hQFL,
      show Midfall.Generator.g1Bytes = g1EipWidth from rfl, Nat.mul_comm]
  have hgb : Midfall.Generator.g1Bytes = g1EipWidth := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hlay, hgb] using hAdvL
  · simpa [hlay, hgb] using hQStart
  · simpa [hlay, hgb] using hQuotL
  · simpa [hlay, hgb] using hFStart
  · simpa [hlay, hgb] using hFByte
  · simpa [hlay, hgb] using hPiStart
  · simpa [hlay, hgb] using hPiByte
  · simpa [hlay, hgb] using hQComm
  · simpa [hlay, hgb] using hQEvalsStart

theorem xcriptSectionWindows_of_schedule (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (H : Hash) (cd : Bytes) (hR : ValidV3 R)
    (hs : TranscriptRows.XcriptSchedule R H cd)
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (hdec : Decoded R cd ms instW inst) :
    ∃ QAdv Qg : List G₁, XcriptSectionWindows R QAdv Qg := by
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qs,
    fCom, pi, _hms, hAdv, _hMult, _hPerm, _hLook, _hTrash, hQ, _hI, _hA, _hF, _hC,
    _hP, _hL, _hT, _hQs⟩ := hs ms instW inst hdec
  exact ⟨QAdv, Qg, xcriptSectionWindows_of_valid R hR hAdv hQ⟩

theorem xcriptMirrorAt_windows (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    {QAdv Qg : List G₁} (hsec : XcriptSectionWindows R QAdv Qg)
    {st : YulSemantics.EVM.EvmState} {cd : Bytes}
    (hm : Midfall.LoweringV2.MirrorAt R cd st) :
    bytesAt st (ptrAddr R.pv.memory.adviceCommsMptrBase)
        (g1EipWidth * QAdv.length) =
      cdSlice cd R.pv.proofLayout.proofCptr (g1EipWidth * QAdv.length) ∧
    bytesAt st (ptrAddr R.pv.memory.quotientLimbCommsMptrBase)
        (g1EipWidth * Qg.length) =
      cdSlice cd R.pv.proofLayout.quotientCommCptr (g1EipWidth * Qg.length) ∧
    bytesAt st (ptrAddr R.pv.memory.fComMptr) g1EipWidth =
      cdSlice cd R.pv.proofLayout.wCptr g1EipWidth ∧
    bytesAt st (ptrAddr R.pv.memory.piMptr) g1EipWidth =
      cdSlice cd (R.pv.proofLayout.qEvalCptr + R.pv.proofLayout.qEvals.byteLen)
        g1EipWidth := by
  obtain ⟨hAdv, hQStart, hQLen, hFStart, hFLen, hPStart, hPLen, _hQComm, _hQE⟩ := hsec
  have hpv : R.pv.proofLayout = R.plan.proofLayout := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Midfall.LoweringV2.mirrorsSection, hpv, ← hAdv] using hm.advice
  · simpa [Midfall.LoweringV2.mirrorsSection, hpv, ← hQStart, ← hQLen] using hm.quotientLimbs
  · simpa [Midfall.LoweringV2.mirrorsSection, hpv, ← hFStart, ← hFLen] using hm.fCom
  · simpa [Midfall.LoweringV2.mirrorsSection, hpv, ← hPStart, ← hPLen] using hm.pi

#assert_axioms Midfall.LoweringV3.xcript_advice_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.xcript_quotient_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.xcript_prefix_count [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.xcript_qs_count [propext, Classical.choice, Quot.sound] native []

#check @Midfall.LoweringV3.planReadCounts_of_valid
#check @Midfall.LoweringV3.xcriptAlgebraRun_of_valid
#check @Midfall.LoweringV3.tp_agrees_of_valid

#assert_axioms Midfall.LoweringV3.lookupChunkNum_sum_eq_of_chunkedOf
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.protocol_evalPlanFields
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.planPrefixG1_eq
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.planNumEvals_eq
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.planReadCounts_of_valid
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptAlgebraRun_of_valid
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.tp_agrees_of_valid
  [propext, Classical.choice, Quot.sound]
set_option maxHeartbeats 8000000 in
theorem xcriptG1_provenance (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (H : Hash)
    (cd : Bytes) (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (hdec : Decoded R cd ms instW inst) :
    ∃ (QAdv QMult QPerm QLook QTrash Qg : List G₁)
      (Qi Qa Qf Qc Qp Ql Qt qsF : List (Fr p))
      (QPre : List G₁) (QEv : List (Fr p)) (fComD piD fComF piF : G₁)
      (qsD : List (Fr p)),
      ms = (QAdv ++ QMult ++ QPerm ++ QLook ++ QTrash ++ Qg).map
          (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          ([Msg.g1 fComD] ++
            (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))) ∧
      ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
          ([Msg.g1 fComD] ++
            (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))) ∧
      qsD.length = R.nSets ∧
      QPre.length = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count ∧
      QEv.length = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals ∧
      QPre = QAdv ++ QMult ++ QPerm ++ QLook ++ QTrash ++ Qg ∧
      ms = TranscriptRows.xcriptPt QAdv QMult QPerm QLook QTrash ++
        TranscriptRows.xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++
        TranscriptRows.xcriptTail fComF qsF piF ∧
      QAdv.length = (R.vk.cs.phases.map (fun ph => (TranscriptRows.phaseCols R.vk.cs ph).length)).sum ∧
      QMult.length = R.vk.cs.lookups.size ∧
      QPerm.length = Permutation.numChunksOf R.vk.cs.permutation.columns.size
        (R.vk.csDegree - 2) ∧
      QLook.length = (R.vk.cs.lookups.toList.map
        (fun l => TranscriptRows.lookupChunkNum R.vk.csDegree l + 1)).sum ∧
      QTrash.length = R.vk.cs.trashcans.size ∧
      Qg.length = (if Features.solidity.outerSingleHCommitment then 1
        else R.vk.domain.getQuotientPolyDegree) ∧
      Qi.length = (instanceShape inst).size *
        (R.vk.cs.instanceQueries.toList.filter (fun q => decide (q.1.index < 1))).length ∧
      Qa.length = (instanceShape inst).size * R.vk.cs.adviceQueries.size ∧
      Qf.length = R.vk.cs.numFixedColumns - R.vk.cs.numSimpleSelectors ∧
      Qc.length = R.vk.permutation.commitments.size ∧
      Qp.length = 3 * Permutation.numChunksOf R.vk.cs.permutation.columns.size
        (R.vk.csDegree - 2) - 1 ∧
      Ql.length = (R.vk.cs.lookups.toList.map
        (fun l => TranscriptRows.lookupChunkNum R.vk.csDegree l + 3)).sum ∧
      Qt.length = R.vk.cs.trashcans.size ∧
      qsF.length = R.nSets ∧
      (∀ i < QAdv.length, ∃ (b : Bytes) (Q : G₁),
        bytesTake cd (R.plan.proofLayout.proofCptr + g1EipWidth * i) g1EipWidth = some b ∧
          R.E.g1.ofEip? b = some Q ∧ QAdv[i]? = some Q) ∧
      (∀ j < Qg.length, ∃ (b : Bytes) (Q : G₁),
        bytesTake cd (R.plan.proofLayout.quotientCommCptr + g1EipWidth * j) g1EipWidth = some b ∧
          R.E.g1.ofEip? b = some Q ∧ Qg[j]? = some Q) := by
  have hc := planReadCounts_of_valid R hR
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qsF,
    fComF, piF, hmsF, hAdv, hMult, hPerm, hLook, hTrash, hQ, hI, hA, hF, hC, hP, hL,
    hT, hQs⟩ := TranscriptRows.xcriptSchedule_of_planReadCounts R H cd hc ms instW inst hdec
  obtain ⟨QPre, QEv, fComD, qsD, piD, hmsD, hPre, hEv, hQsD⟩ :=
    TranscriptRows.decoded_ms_split R hdec
  let G1s : List G₁ := QAdv ++ QMult ++ QPerm ++ QLook ++ QTrash ++ Qg
  have hG1sLen : G1s.length = QPre.length := by
    rw [hPre, hc.prefixG1]
    simp [G1s, TranscriptRows.planPrefixG1Count, hAdv, hMult, hPerm, hLook, hTrash, hQ]
    omega
  have hmsG : ms = G1s.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      ((Qi ++ Qa ++ Qf ++ Qc ++ Qp ++ Ql ++ Qt).map
        (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComF] ++
          (qsF.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piF]))) := by
    rw [hmsF]
    simp [G1s, TranscriptRows.xcriptPt, TranscriptRows.xcriptRa, TranscriptRows.xcriptTail,
      List.map_append, List.append_assoc]
  have hmsD' : ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComD] ++
          (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))) := hmsD
  let restG := (Qi ++ Qa ++ Qf ++ Qc ++ Qp ++ Ql ++ Qt).map
    (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
    ([Msg.g1 fComF] ++ (qsF.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piF]))
  have hQPreG : QPre = G1s := by
    have hmapEq : QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
        G1s.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) := by
      have hQ : QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          ms.take QPre.length := by
        rw [hmsD']
        simpa using List.take_left (l₁ := QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (l₂ := QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
            ([Msg.g1 fComD] ++
              (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD])))
      have hG : G1s.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) =
          ms.take G1s.length := by
        rw [hmsG]
        simpa using List.take_left (l₁ := G1s.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)))
          (l₂ := restG)
      rw [hQ, hG, hG1sLen]
    exact (List.map_injective_iff.mpr (fun a b h => by cases h; rfl)) hmapEq
  have hQPreAdv : QPre = QAdv ++ (QMult ++ QPerm ++ QLook ++ QTrash ++ Qg) := by
    rw [hQPreG]; simp [G1s, List.append_assoc]
  let preN : List G₁ := QAdv ++ QMult ++ QPerm ++ QLook ++ QTrash
  have hQPreN : QPre = preN ++ Qg := by
    rw [hQPreG]
  have hAdvCount : QAdv.length =
      Midfall.Lowering.sumNat (R.plan.proofLayout.advicePhases.map (fun s => s.itemCount)) :=
    xcript_advice_count R hR QAdv hAdv
  have hPreNLen : preN.length = R.plan.proofLayout.nonQuotientG1Count := by
    have hprefix := xcript_prefix_count R hR Qg hQ
    have hQlen : Qg.length ≤ QPre.length := by rw [hQPreN]; simp
    have hG1sSplit : G1s.length = preN.length + Qg.length := by
      simp [G1s, preN, List.append_assoc]
      omega
    have hQPreLen : QPre.length =
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count := hPre
    have : preN.length + Qg.length = R.plan.proofLayout.nonQuotientG1Count + Qg.length := by
      calc preN.length + Qg.length = G1s.length := hG1sSplit.symm
        _ = QPre.length := hG1sLen
        _ = _ := hQPreLen
        _ = _ := hprefix
    omega
  let restSlots : List Midfall.Lowering.WireSlot :=
    List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
        Midfall.Lowering.WireSlot.fr ++
      ([Midfall.Lowering.WireSlot.g1] ++
        (List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets
            Midfall.Lowering.WireSlot.fr ++ [Midfall.Lowering.WireSlot.g1]))
  have hslotsPre : (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots =
      List.replicate QPre.length Midfall.Lowering.WireSlot.g1 ++ restSlots := by
    rw [hPre]
    simp only [RepackedProofLayoutPlan.slots, restSlots, List.append_assoc]
  have hdecode : decodeSlots (p := p) R.E.g1 cd
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots
      R.plan.proofLayout.proofCptr = some (ms, R.plan.proofLayout.proofEnd) := by
    obtain ⟨_, _, _, _, _, _, _, _, hds, _⟩ :=
      Midfall.Lowering.decodeCalldata_facts R.plan.proofLayout R.cfg.numInstances R.E.g1 cd ms instW hdec.1
    exact hds
  have hprovAll := TranscriptRows.decodeSlots_g1_provenance_of_prefix
    (c := R.E.g1) (cd := cd) (pre := QPre) (restSlots := restSlots)
    (cur := R.plan.proofLayout.proofCptr) (cur' := R.plan.proofLayout.proofEnd)
    (restMs := QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
      ([Msg.g1 fComD] ++
        (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD])))
    (by
      rw [hslotsPre] at hdecode
      rw [hmsD'] at hdecode
      exact hdecode)
  have hprovAdv : ∀ i < QAdv.length, ∃ (b : Bytes) (Q : G₁),
      bytesTake cd (R.plan.proofLayout.proofCptr + g1EipWidth * i) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some Q ∧ QAdv[i]? = some Q := by
    intro i hi
    have hiPre : i < QPre.length := by
      rw [hQPreAdv]; simp; omega
    obtain ⟨b, Q, hb, hq, hQidx⟩ := hprovAll i hiPre
    refine ⟨b, Q, hb, hq, ?_⟩
    rw [hQPreAdv] at hQidx
    rw [List.getElem?_append_left hi] at hQidx
    exact hQidx
  have hprovQuot : ∀ j < Qg.length, ∃ (b : Bytes) (Q : G₁),
      bytesTake cd (R.plan.proofLayout.quotientCommCptr + g1EipWidth * j) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some Q ∧ Qg[j]? = some Q := by
    intro j hj
    have hiPre : preN.length + j < QPre.length := by
      rw [hQPreN]; simp; omega
    obtain ⟨b, Q, hb, hq, hQidx⟩ := hprovAll (preN.length + j) hiPre
    have hqcomm := (xcriptSectionWindows_of_valid R hR hAdv hQ).quotientComm
    have hcur : R.plan.proofLayout.proofCptr + g1EipWidth * (preN.length + j) =
        R.plan.proofLayout.quotientCommCptr + g1EipWidth * j := by
      rw [hqcomm, ← hPreNLen, show g1EipWidth = 128 from rfl]
      omega
    refine ⟨b, Q, ?_, hq, ?_⟩
    · rwa [hcur] at hb
    · rw [hQPreN] at hQidx
      rw [List.getElem?_append_right (by omega)] at hQidx
      simpa using hQidx
  have hmsCoarseG : ms = G1s.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComD] ++
          (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))) := by
    rwa [hQPreG] at hmsD
  have hQsD' : qsD.length = R.nSets := by
    rw [hQsD]
    rfl
  exact ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qsF,
    QPre, QEv, fComD, piD, fComF, piF, qsD, hmsCoarseG, hmsD, hQsD', hPre, hEv,
    (by rw [hQPreG]), hmsF, hAdv,
    hMult, hPerm, hLook, hTrash, hQ, hI, hA, hF, hC, hP, hL, hT, hQs, hprovAdv,
    hprovQuot⟩

end Midfall.LoweringV3

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

set_option maxHeartbeats 8000000 in
theorem xcriptG1_tail_provenance (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (H : Hash)
    (cd : Bytes) (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
    {ms : List (Msg (Fr p) G₁)} {instW : Array Word256} {inst : Array (Fr p)}
    (hdec : Decoded R cd ms instW inst)
    (QPre : List G₁) (QEv : List (Fr p)) (fComD piD : G₁) (qsD : List (Fr p))
    (hmsD : ms = QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComD] ++
          (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD]))))
    (hQsD : qsD.length = R.nSets)
    (hPre : QPre.length =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count)
    (hEv : QEv.length =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals) :
    ∃ (bF bP : Bytes) (QF QP : G₁),
      bytesTake cd R.plan.proofLayout.wCptr g1EipWidth = some bF ∧
        R.E.g1.ofEip? bF = some QF ∧ QF = fComD ∧
      bytesTake cd (R.plan.proofLayout.qEvalCptr + R.plan.proofLayout.qEvals.byteLen)
          g1EipWidth = some bP ∧
        R.E.g1.ofEip? bP = some QP ∧ QP = piD := by
  have hc := planReadCounts_of_valid R hR
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qsF,
    fComF, piF, hmsF, hAdv, hMult, hPerm, hLook, hTrash, hQ, hI, hA, hF, hC, hP, hL,
    hT, hQs⟩ := TranscriptRows.xcriptSchedule_of_planReadCounts R H cd hc ms instW inst hdec
  have hsec := xcriptSectionWindows_of_valid R hR hAdv hQ
  obtain ⟨rawMeta, meta_, L, userPhases, hraw, hmeta, hlay, hLay, _hc1, _hc2, _hc3,
    _hc4, _hc5, _hc6, _hc7, _hc8, _hup, _huser, _hnInst, _htrunc, _hnLook, _hnPerm,
    _hnTrash, _hLH⟩ := TranscriptRows.tp_planFacts (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) hR
  have facts := TranscriptRows.tp_fromProtocol hLay
  obtain ⟨_, _, _, _, _, _, _, _, hds, _⟩ :=
    Midfall.Lowering.decodeCalldata_facts R.plan.proofLayout R.cfg.numInstances R.E.g1 cd ms instW hdec.1
  let prefixMs : List (Msg (Fr p) G₁) :=
    QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁))
  let restD : List (Msg (Fr p) G₁) :=
    [Msg.g1 fComD] ++ (qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++ [Msg.g1 piD])
  have hmsD' : ms = prefixMs ++ restD := by simpa [prefixMs, restD, List.append_assoc] using hmsD
  let sF : List Midfall.Lowering.WireSlot :=
    List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count
        Midfall.Lowering.WireSlot.g1 ++
      List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
        Midfall.Lowering.WireSlot.fr
  let tailF : List Midfall.Lowering.WireSlot :=
    List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets
        Midfall.Lowering.WireSlot.fr ++ [Midfall.Lowering.WireSlot.g1]
  let restF : List Midfall.Lowering.WireSlot :=
    [Midfall.Lowering.WireSlot.g1] ++ tailF
  have hslotsF : (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots =
      sF ++ restF := by
    simp [RepackedProofLayoutPlan.slots, sF, restF, tailF, List.append_assoc]
  have hsplitF := TranscriptRows.decodeSlots_split sF restF R.plan.proofLayout.proofCptr
    ms R.plan.proofLayout.proofEnd (by rwa [hslotsF] at hds)
  obtain ⟨msF, curF, msRest, hF1, hF2, hmsFsplit⟩ := hsplitF
  have hlenF : msF.length = prefixMs.length := by
    have hsl := TranscriptRows.decodeSlots_map_slot (p := p) R.E.g1 cd sF
      R.plan.proofLayout.proofCptr msF curF hF1
    have hmsl : msF.length = sF.length := by
      simpa using congrArg List.length hsl
    rw [hmsl]
    simp [sF, prefixMs, hPre, hEv, List.length_append]
  have hmsF_eq : msF = prefixMs := by
    have htake : msF = ms.take prefixMs.length := by
      rw [hmsFsplit]
      simpa [hlenF] using List.take_left (l₁ := msF) (l₂ := msRest)
    have hpre : prefixMs = ms.take prefixMs.length := by
      rw [hmsD']
      exact (List.take_left (l₁ := prefixMs) (l₂ := restD)).symm
    exact htake.trans hpre.symm
  have hmsRest : msRest = restD := by
    have := hmsFsplit
    rw [hmsF_eq, hmsD'] at this
    exact (List.append_cancel_left this).symm
  obtain ⟨bF, QF, ms0, cur0, hgF, hbF, hqF, hrecF, hms0F, hcurF⟩ :=
    TranscriptRows.decodeSlots_g1_inv tailF curF msRest R.plan.proofLayout.proofEnd hF2
  have hQF : QF = fComD := by
    have := hms0F
    rw [hmsRest] at this
    have := congrArg (fun l => l.head?) this
    simpa [restD] using this.symm
  have hcurFeq : curF = R.plan.proofLayout.wCptr := by
    have hcur := TranscriptRows.decodeSlots_cursor (c := R.E.g1) (cd := cd) sF
      R.plan.proofLayout.proofCptr msF curF hF1
    -- hcur : curF = proofCptr + eipWidthSum sF
    rw [hcur]
    have hsum : Midfall.Lowering.eipWidthSum sF =
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count * g1EipWidth +
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals * 32 := by
      simp [sF, Midfall.Lowering.eipWidthSum_append, TranscriptRows.eipWidthSum_replicate_g1,
        TranscriptRows.eipWidthSum_replicate_fr]
    rw [hsum]
    -- layout arithmetic
    have hEvByte : R.plan.proofLayout.evals.byteLen =
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals * 32 := by
      have hev : L.evals.byteLen = L.evals.itemCount * 32 := by
        simpa [← facts.evals, Midfall.Generator.wordBytes] using facts.evalsByte
      rw [← hlay] at hev
      change R.plan.proofLayout.evals.byteLen =
        R.plan.proofLayout.evals.itemCount * 32
      exact hev
    have hQByte : R.plan.proofLayout.quotientLimbs.byteLen = Qg.length * g1EipWidth := by
      rw [hsec.quotientLen, Nat.mul_comm]
    have hQComm : R.plan.proofLayout.quotientCommCptr =
        R.plan.proofLayout.proofCptr + g1EipWidth * R.plan.proofLayout.nonQuotientG1Count :=
      hsec.quotientComm
    have hPrefix := xcript_prefix_count R hR Qg hQ
    have hEvalC : R.plan.proofLayout.evalCptr =
        R.plan.proofLayout.quotientCommCptr + R.plan.proofLayout.quotientLimbs.byteLen := by
      simpa [hlay] using (TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
        meta_.numPointSets hLay).2.1
    have hW : R.plan.proofLayout.wCptr =
        R.plan.proofLayout.evalCptr + R.plan.proofLayout.evals.byteLen := by
      simpa [hlay] using (TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
        meta_.numPointSets hLay).2.2.2.1
    rw [hW, hEvalC, hQComm, hQByte, hEvByte, hPrefix, Nat.add_mul]
    ring

  let prefixPi : List (Msg (Fr p) G₁) :=
    QPre.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QEv.map (fun q => (Msg.fr q : Msg (Fr p) G₁)) ++
        ([Msg.g1 fComD] ++ qsD.map (fun q => (Msg.fr q : Msg (Fr p) G₁))))
  let restPiD : List (Msg (Fr p) G₁) := [Msg.g1 piD]
  have hmsPiD : ms = prefixPi ++ restPiD := by
    simpa [prefixPi, restPiD, List.append_assoc] using hmsD
  let sPi : List Midfall.Lowering.WireSlot :=
    List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count
        Midfall.Lowering.WireSlot.g1 ++
      List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals
        Midfall.Lowering.WireSlot.fr ++
      (Midfall.Lowering.WireSlot.g1 ::
        List.replicate (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets
          Midfall.Lowering.WireSlot.fr)
  let restPi : List Midfall.Lowering.WireSlot := [Midfall.Lowering.WireSlot.g1]
  have hslotsPi : (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots =
      sPi ++ restPi := by
    simp [RepackedProofLayoutPlan.slots, sPi, restPi, List.append_assoc]
  have hsplitPi := TranscriptRows.decodeSlots_split sPi restPi R.plan.proofLayout.proofCptr
    ms R.plan.proofLayout.proofEnd (by rwa [hslotsPi] at hds)
  obtain ⟨msPi, curPi, msLast, hPi1, hPi2, hmsPisplit⟩ := hsplitPi
  have hlenPi : msPi.length = prefixPi.length := by
    have hsl := TranscriptRows.decodeSlots_map_slot (p := p) R.E.g1 cd sPi
      R.plan.proofLayout.proofCptr msPi curPi hPi1
    have hmsl : msPi.length = sPi.length := by
      simpa using congrArg List.length hsl
    rw [hmsl]
    simp [sPi, prefixPi, hPre, hEv, hQsD, List.length_append]
    have hPN : (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets =
        qsD.length := by
      rw [show (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets = R.nSets from rfl]
      exact hQsD.symm
    omega
  have hmsPi_eq : msPi = prefixPi := by
    have htake : msPi = ms.take prefixPi.length := by
      rw [hmsPisplit]
      simpa [hlenPi] using List.take_left (l₁ := msPi) (l₂ := msLast)
    have hpre : prefixPi = ms.take prefixPi.length := by
      rw [hmsPiD]
      exact (List.take_left (l₁ := prefixPi) (l₂ := restPiD)).symm
    exact htake.trans hpre.symm
  have hmsLast : msLast = restPiD := by
    have := hmsPisplit
    rw [hmsPi_eq, hmsPiD] at this
    exact (List.append_cancel_left this).symm
  obtain ⟨bP, QP, ms0P, cur0P, hgP, hbP, hqP, hrecP, hms0P, hcurP⟩ :=
    TranscriptRows.decodeSlots_g1_inv [] curPi msLast R.plan.proofLayout.proofEnd hPi2
  have hQP : QP = piD := by
    have := hms0P
    rw [hmsLast] at this
    have := congrArg (fun l => l.head?) this
    simpa [restPiD] using this.symm
  have hcurPeq : curPi = R.plan.proofLayout.qEvalCptr + R.plan.proofLayout.qEvals.byteLen := by
    have hcur := TranscriptRows.decodeSlots_cursor (c := R.E.g1) (cd := cd) sPi
      R.plan.proofLayout.proofCptr msPi curPi hPi1
    rw [hcur]
    have hsum : Midfall.Lowering.eipWidthSum sPi =
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count * g1EipWidth +
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals * 32 + g1EipWidth +
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets * 32 := by
      simp [sPi, Midfall.Lowering.eipWidthSum_append, Midfall.Lowering.eipWidthSum_cons,
        Midfall.Lowering.slotEipWidth, TranscriptRows.eipWidthSum_replicate_g1, TranscriptRows.eipWidthSum_replicate_fr]
      ring
    rw [hsum]
    have hEvByte : R.plan.proofLayout.evals.byteLen =
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numEvals * 32 := by
      have hev : L.evals.byteLen = L.evals.itemCount * 32 := by
        simpa [← facts.evals, Midfall.Generator.wordBytes] using facts.evalsByte
      rw [← hlay] at hev
      change R.plan.proofLayout.evals.byteLen =
        R.plan.proofLayout.evals.itemCount * 32
      exact hev
    have hQByte : R.plan.proofLayout.quotientLimbs.byteLen = Qg.length * g1EipWidth := by
      rw [hsec.quotientLen, Nat.mul_comm]
    have hQComm : R.plan.proofLayout.quotientCommCptr =
        R.plan.proofLayout.proofCptr + g1EipWidth * R.plan.proofLayout.nonQuotientG1Count :=
      hsec.quotientComm
    have hPrefix := xcript_prefix_count R hR Qg hQ
    have hEvalC : R.plan.proofLayout.evalCptr =
        R.plan.proofLayout.quotientCommCptr + R.plan.proofLayout.quotientLimbs.byteLen := by
      simpa [hlay] using (TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
        meta_.numPointSets hLay).2.1
    have hW : R.plan.proofLayout.wCptr =
        R.plan.proofLayout.evalCptr + R.plan.proofLayout.evals.byteLen := by
      simpa [hlay] using (TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
        meta_.numPointSets hLay).2.2.2.1
    have hQEvalC : R.plan.proofLayout.qEvalCptr =
        R.plan.proofLayout.wCptr + R.plan.proofLayout.fCom.byteLen := by
      simpa [hlay] using (TranscriptRows.fromProtocol_starts meta_.protocol meta_.numEvals
        meta_.numPointSets hLay).2.2.2.2.2.1
    have hQEvalsByte : R.plan.proofLayout.qEvals.byteLen = qsD.length * 32 := by
      have hev : L.qEvals.byteLen = meta_.numPointSets * Midfall.Generator.wordBytes :=
        facts.qEvalsByte
      have hcount : meta_.numPointSets = qsD.length := by
        rw [← facts.qEvals]
        have hLq : L.qEvals.itemCount =
            (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets := by
          rw [← hlay]; rfl
        rw [hLq, show (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets = R.nSets from rfl, ← hQsD]
      rw [← hlay] at hev
      rw [hev, hcount]
      simp [Midfall.Generator.wordBytes]
    rw [hQEvalC, hQEvalsByte,
      show (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).numPointSets = R.nSets from rfl,
      ← hQsD, hW, hEvalC, hQComm, hQByte, hEvByte, hPrefix, hsec.fComLen, Nat.add_mul]
    ring

  refine ⟨bF, bP, QF, QP, ?_, hqF, hQF, ?_, hqP, hQP⟩
  · rwa [hcurFeq] at hbF
  · rwa [hcurPeq] at hbP

end Midfall.LoweringV3

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.Lowering.Inline Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

set_option maxHeartbeats 16000000 in
theorem xcriptG1 (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
    (horder : TranscriptRows.AdvicePhasesColumnOrder R.vk)
    (hnum : R.cfg.numInstances < 2 ^ 31)
    {st : YulSemantics.EVM.EvmState} (hm : Midfall.LoweringV2.MirrorAt R cd st)
    (h : TranscriptRows.XcriptAlgebraRun R H cd) :
    TranscriptRows.XcriptG1 R H cd st := by
  intro ms instW inst hdec x hx
  have hTail := h ms instW inst hdec
  obtain ⟨QAdv, QMult, QPerm, QLook, QTrash, Qg, Qi, Qa, Qf, Qc, Qp, Ql, Qt, qsF,
    QPre, QEv, fComD, piD, fComF, piF, qsD, hmsCoarse, hmsD, hQsD, hPre, hEv, hQPreG,
    hmsFine, hAdv, hMult, hPerm, hLook, hTrash, hQ, hI, hA, hF, hC, hP, hL, hT, hQs,
    hprovAdv, hprovQuot⟩ := xcriptG1_provenance R H cd hR hcodec hdec
  obtain ⟨bF, bP, QF, QP, hbF, hqF, hQF, hbP, hqP, hQP⟩ :=
    xcriptG1_tail_provenance R H cd hR hcodec hdec QPre QEv fComD piD qsD hmsD hQsD
      hPre hEv
  have hf : R.vk.WellFormed Features.solidity := hR.supported.wf
  have hnc0 : R.vk.cs.numInstanceColumns = 2 := hR.supported.instShape.1
  have hinstQ : ∀ q ∈ R.vk.cs.instanceQueries.toList, ¬ q.1.index < 1 → q.1.index = 1 :=
    fun q hq hge => TranscriptRows.instanceQueries_index_eq_one R.vk hf hnc0 hq hge
  have hinstSize : inst.size < 2 ^ 31 := by
    rw [TranscriptRows.decoded_inst_size hdec]
    exact hnum
  have hp : p ≤ 2 ^ 256 := by
    rw [hR.env.modulus]; norm_num [frModulusConstant]
  have hmsAdv : ms = QAdv.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
      (QMult.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
        (QPerm.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
          (QLook.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++
            (QTrash.map (fun Q => (Msg.g1 Q : Msg (Fr p) G₁)) ++ [])))) ++
      (TranscriptRows.xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++
        TranscriptRows.xcriptTail fComF qsF piF) := by
    rw [hmsFine]
    simp [TranscriptRows.xcriptPt, List.map_append, List.append_assoc]
  have hAdvVal := TranscriptRows.xcript_advice_value R hR hcodec H horder hTail hx
    QAdv QMult QPerm QLook QTrash
    (TranscriptRows.xcriptRa Qg Qi Qa Qf Qc Qp Ql Qt ++
      TranscriptRows.xcriptTail fComF qsF piF) hmsAdv hAdv hMult hPerm hLook hTrash
  have hP' : Qp.length = Permutation.numChunksOf R.vk.cs.permutation.columns.size
      (R.vk.csDegree - 2) * 3 - 1 := by rw [hP, Nat.mul_comm]
  have hQuotVal := TranscriptRows.xcript_quotient_value R hR hcodec H hTail hx
    QAdv QMult QPerm QLook QTrash Qg Qi Qa Qf Qc Qp Ql Qt qsF fComF piF hmsFine
    hAdv hMult hPerm hLook hTrash hQ hI hA hF hC hP' hL hT hinstQ hinstSize
  have hTailVal := TranscriptRows.xcript_tail_fCom_pi R H hTail hx
    hcodec.compressedEncoderFirst hcodec.compressedWidth hp hmsD hQsD
  have hsec := xcriptSectionWindows_of_valid R hR hAdv hQ
  have hmw := xcriptMirrorAt_windows R hsec hm
  obtain ⟨hAdvBytes, hQuotBytes, hFComBytes, hPiBytes⟩ := hmw
  have hprovAdv' : ∀ i (hi : i < QAdv.length), ∃ (b : Bytes) (Q : G₁),
      bytesTake cd (R.plan.proofLayout.proofCptr + g1EipWidth * i) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some Q ∧ QAdv[i]'hi = Q := by
    intro i hi
    obtain ⟨b, Q, hb, hq, hQidx⟩ := hprovAdv i hi
    have hQ : QAdv[i]? = some (QAdv[i]'hi) := List.getElem?_eq_getElem hi
    have hEQ : Q = QAdv[i]'hi := by
      rw [hQ] at hQidx
      exact (Option.some.inj hQidx).symm
    exact ⟨b, Q, hb, hq, hEQ.symm⟩
  have hprovQuot' : ∀ j (hj : j < Qg.length), ∃ (b : Bytes) (Q : G₁),
      bytesTake cd (R.plan.proofLayout.quotientCommCptr + g1EipWidth * j) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some Q ∧ Qg[j]'hj = Q := by
    intro j hj
    obtain ⟨b, Q, hb, hq, hQidx⟩ := hprovQuot j hj
    have hQ : Qg[j]? = some (Qg[j]'hj) := List.getElem?_eq_getElem hj
    have hEQ : Q = Qg[j]'hj := by
      rw [hQ] at hQidx
      exact (Option.some.inj hQidx).symm
    exact ⟨b, Q, hb, hq, hEQ.symm⟩
  -- bounds from the layout cursor arithmetic
  obtain ⟨_, _, _, _, _, _, _, hsz, hds, _⟩ :=
    Midfall.Lowering.decodeCalldata_facts R.plan.proofLayout R.cfg.numInstances R.E.g1 cd ms instW hdec.1
  have hcurAll := TranscriptRows.decodeSlots_cursor (c := R.E.g1) (cd := cd)
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots
    R.plan.proofLayout.proofCptr ms R.plan.proofLayout.proofEnd hds
  have hwidth := Midfall.Lowering.eipWidthSum_slots
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout)
  have hboundProof : R.plan.proofLayout.proofCptr + g1EipWidth *
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count ≤ cd.size := by
    rw [hcurAll, hwidth, show g1EipWidth = 128 from rfl] at hsz
    rw [show g1EipWidth = 128 from rfl]
    omega
  have hAdvLe : QAdv.length ≤
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count := by
    rw [← hPre, hQPreG]
    simp
  have hAdvBound : R.plan.proofLayout.proofCptr + g1EipWidth * QAdv.length ≤ cd.size := by
    have := Nat.mul_le_mul_left g1EipWidth hAdvLe
    omega
  have hPrefix := xcript_prefix_count R hR Qg hQ
  have hQuotBound : R.plan.proofLayout.quotientCommCptr + g1EipWidth * Qg.length ≤ cd.size := by
    have hEq : R.plan.proofLayout.quotientCommCptr + g1EipWidth * Qg.length =
        R.plan.proofLayout.proofCptr + g1EipWidth *
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).prefixG1Count := by
      rw [hsec.quotientComm, hPrefix, Nat.mul_add]
      ring
    rw [hEq]
    exact hboundProof
  have hprovAdv'' : ∀ i (hi : i < QAdv.length), ∃ b : Bytes,
      bytesTake cd (R.plan.proofLayout.proofCptr + g1EipWidth * i) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some (QAdv[i]'hi) := by
    intro i hi
    obtain ⟨b, Q, hb, hq, hQ⟩ := hprovAdv' i hi
    exact ⟨b, hb, by rw [hQ]; exact hq⟩
  have hprovQuot'' : ∀ j (hj : j < Qg.length), ∃ b : Bytes,
      bytesTake cd (R.plan.proofLayout.quotientCommCptr + g1EipWidth * j) g1EipWidth = some b ∧
        R.E.g1.ofEip? b = some (Qg[j]'hj) := by
    intro j hj
    obtain ⟨b, Q, hb, hq, hQ⟩ := hprovQuot' j hj
    exact ⟨b, hb, by rw [hQ]; exact hq⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hAdvHold := TranscriptRows.holdsG1s_section R.E st cd
      (ptrAddr R.pv.memory.adviceCommsMptrBase) R.plan.proofLayout.proofCptr QAdv
      hAdvBytes hAdvBound hprovAdv'' hcodec.eipRoundtrip
    rwa [hAdvVal]
  · have hQuotHold := TranscriptRows.holdsG1s_section R.E st cd
      (ptrAddr R.pv.memory.quotientLimbCommsMptrBase) R.plan.proofLayout.quotientCommCptr Qg
      hQuotBytes hQuotBound hprovQuot'' hcodec.eipRoundtrip
    have hArr : x.alg.quotientLimbComs = Qg.toArray := Array.toList_inj.mp hQuotVal
    rwa [hArr]
  · have hQF' : QF = x.r.fCom := by rw [hQF, ← hTailVal.1]
    have hbF' : bytesTake cd R.plan.proofLayout.fCom.start g1EipWidth = some bF := by
      rw [hsec.fComStart]
      exact hbF
    exact TranscriptRows.holdsG1_of_mirrorsSection R.E hm.fCom hsec.fComLen hbF' (by simpa [hQF'] using hqF)
      hcodec.eipRoundtrip
  · have hQP' : QP = x.r.pi := by rw [hQP, ← hTailVal.2]
    have hbP' : bytesTake cd R.plan.proofLayout.pi.start g1EipWidth = some bP := by
      rw [hsec.piStart]
      exact hbP
    exact TranscriptRows.holdsG1_of_mirrorsSection R.E hm.pi hsec.piLen hbP' (by simpa [hQP'] using hqP)
      hcodec.eipRoundtrip

/-- **THE FIXED `tp_agrees` ROW, NOW WITH `XcriptG1` AND THE PHASE ORDER CLOSED.**
    `XcriptG1` is produced by `xcriptG1` from the schedule run and `TpPost`'s
    `MirrorAt`; `AdvicePhasesColumnOrder` is D-GATE18's
    `advicePhaseColumnOrder_of_wellFormed`. The only remaining named input is the
    calldata bound `hnum`; the fixed `tp_agrees` itself keeps its statement (no
    `hnum` parameter). -/
theorem tp_agrees_of_valid_closed (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpost : TranscriptRows.TpPost R H vkAddr cd V st)
    (hnum : R.cfg.numInstances < 2 ^ 31) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  have hpost' := hpost
  obtain ⟨-, -, -, -, hmirror, -⟩ := hpost
  have horder : TranscriptRows.AdvicePhasesColumnOrder R.vk :=
    TranscriptRows.advicePhaseColumnOrder_of_wellFormed (vk := R.vk) hR.supported.wf
  have hAlg : TranscriptRows.XcriptAlgebraRun R H cd :=
    TranscriptRows.xcriptAlgebraRun_of_planReadCounts R hR hcodec H cd
      (planReadCounts_of_valid R hR) hnum
  have hG1 : TranscriptRows.XcriptG1 R H cd st :=
    xcriptG1 R H cd hR hcodec horder hnum hmirror hAlg
  exact Midfall.LoweringV3.TranscriptRows.tp_agrees_of_xcriptG1
    R hR hcodec H vkAddr cd V st hpost' hAlg hG1

/-- **THE CONSUMER WITH THE CALADATA BOUND INSTEAD OF `hnum`.** D-GATE19's predicate,
    at the consumer rather than in a row/bundle: `cd.size < 2^36` supplies
    `R.cfg.numInstances < 2^31` for every decoding (`numInstances_lt_of_cd_size`).
    This is the exact minimal alternative to adding a field to `Frame`/`EntryFrameV3`;
    the fixed `tp_agrees` itself still has its original statement. -/
theorem tp_agrees_of_valid_closed_cdSize (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpost : TranscriptRows.TpPost R H vkAddr cd V st)
    (hcd : cd.size < 2 ^ 36) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  have hpost' := hpost
  obtain ⟨-, -, -, -, hmirror, -⟩ := hpost
  have horder : TranscriptRows.AdvicePhasesColumnOrder R.vk :=
    TranscriptRows.advicePhaseColumnOrder_of_wellFormed (vk := R.vk) hR.supported.wf
  have hAlg : TranscriptRows.XcriptAlgebraRun R H cd := by
    intro ms instW inst hdec
    exact TranscriptRows.xcriptAlgebraRun_of_planReadCounts R hR hcodec H cd
      (planReadCounts_of_valid R hR) (TranscriptRows.numInstances_lt_of_cd_size hdec hcd)
      ms instW inst hdec
  have hG1 : TranscriptRows.XcriptG1 R H cd st := by
    intro ms instW inst hdec x hx
    exact xcriptG1 R H cd hR hcodec horder
      (TranscriptRows.numInstances_lt_of_cd_size hdec hcd) hmirror hAlg
      ms instW inst hdec x hx
  exact TranscriptRows.tp_agrees_of_xcriptG1 R hR hcodec H vkAddr cd V st hpost' hAlg hG1

namespace TranscriptRows

/-- **THE FIXED `tp_agrees` ROW, CLOSED.** This is the exact statement that used to be
    `TranscriptRows.tp_agrees`, now read from `TpPost`'s `Frame.cdSize36` (D-GATE19)
    and `EndToEndAlgebra.tp_agrees_of_valid_closed_cdSize`. The row's statement is
    unchanged: no `hnum`, no phase-order parameter, no `XcriptG1` premise. The
    calldata bound is the entry predicate `cd.size < 2^36` carried by `Frame`. -/
theorem tp_agrees (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) (H : Hash)
    (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (h : TpPost R H vkAddr cd V st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  have hpost := h
  obtain ⟨hframe, -, -, -, -, -⟩ := h
  exact tp_agrees_of_valid_closed_cdSize R hR hcodec H vkAddr cd V st hpost hframe.cdSize36

/-- **THE GENERIC TRANSCRIPT-PARSER SIMULATION ROW, PROVED from the three leaves.**
    This is the exact `TranscriptRows.tp_blockSim`, moved beside the now-closed
    `tp_agrees`; the statement is unchanged. -/
theorem tp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
    (_hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.transcriptParser H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    rcases TranscriptRows.tp_computes R hR hcodec H vkAddr cd _ g V st hpre V' st' o hrun with
      hrev | ⟨ho, hpost⟩
    · exact Or.inl hrev
    · exact Or.inr (Or.inl ⟨ho, tp_agrees R hR hcodec H vkAddr cd V' st' hpost⟩)
  · intro V st hpre V' st' o hrun
    exact Or.inl (TranscriptRows.tp_poison R hR H vkAddr cd _ g V st hpre V' st' o hrun)

end TranscriptRows

#assert_axioms Midfall.LoweringV3.TranscriptRows.tp_agrees
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.xcript_evals_count
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcript_evals_count_of_decoded
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.foldl_byteLen_eq_sumNat
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptSectionWindows_of_valid
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptSectionWindows_of_schedule
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptMirrorAt_windows
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptG1_provenance
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptG1_tail_provenance
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.xcriptG1
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.tp_agrees_of_valid_closed
  [propext, Classical.choice, Quot.sound]
#assert_axioms Midfall.LoweringV3.tp_agrees_of_valid_closed_cdSize
  [propext, Classical.choice, Quot.sound]


end Midfall.LoweringV3

