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

open Midfall Midfall.Halo2

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

namespace PresWidthSeq

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

end PresWidthSeq

end Midfall.LoweringV3
