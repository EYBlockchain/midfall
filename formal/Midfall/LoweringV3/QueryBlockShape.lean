-- |
-- Midfall.LoweringV3.QueryBlockShape
--
-- The verifier-side `rotateOmega` point shape for the easy query blocks:
-- trashcan queries open at `x`, and the common sigma openings all open at `x`.
-- The remaining blocks (advice/instance/permutationZ/lookup/fixed) need their
-- mapM/zip membership inversion; these two are the first entries of the
-- same-order block theorem.
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Verifier
import Midfall.LoweringV3.KzgQueryMap
import Midfall.Halo2.Exec.Logup
import Midfall.Halo2.Exec.Trash

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}

theorem Trash.Evaluated.queries_point (ev : Trash.Evaluated (Fr p) G₁) (x : Fr p)
    (proof idx : Nat) :
    ∀ q ∈ (Trash.Evaluated.queries ev x proof idx).toList, q.point = x := by
  intro q hq
  unfold Trash.Evaluated.queries at hq
  simp only [List.mem_singleton] at hq
  subst hq
  rfl

theorem Permutation.CommonEvaluated.queries_point
    (common : Permutation.CommonEvaluated (Fr p))
    (vkey : Permutation.VerifyingKey G₁) (x : Fr p) :
    ∀ q ∈ (Permutation.CommonEvaluated.queries common vkey x).toList, q.point = x := by
  intro q hq
  unfold Permutation.CommonEvaluated.queries at hq
  simp only [List.mem_toArray, List.mem_map] at hq
  obtain ⟨a, _ha, rfl⟩ := hq
  rfl

theorem Logup.Evaluated.queries_point (ev : Logup.Evaluated (Fr p) G₁)
    (domain : EvaluationDomain (Fr p)) (x : Fr p) (proof lookup : Nat) :
    ∀ q ∈ (Logup.Evaluated.queries ev domain x proof lookup).toList,
      q.point = x ∨ q.point = domain.rotateOmega x Rotation.next := by
  intro q hq
  simp [Logup.Evaluated.queries] at hq
  rcases hq with hq | hq | hq | hq
  all_goals
    first
    | (rw [hq]; first | left; rfl | right; rfl)
    | (obtain ⟨a, b, c, hmem, rfl⟩ := hq; left; rfl)

def fixedQueryFn (vk : VerifyingKey (Fr p) G₁) (x : Fr p) (fixedEvals : Array (Fr p))
    (q : Nat × (Column × Rotation)) : Except Fault (VerifierQuery (Fr p) G₁) := do
  let com ← Permutation.atIndex vk.fixedCommitments q.2.1.index
    "proofs/src/plonk/verifier.rs:640"
  let ev ← Permutation.atIndex fixedEvals q.1 "proofs/src/plonk/verifier.rs:641"
  pure (VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
    (CommitmentLabel.fixed q.2.1.index) (.fixed q.2.1.index) com ev)

theorem fixedQueryFn_point (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (fixedEvals : Array (Fr p)) (q : Nat × (Column × Rotation))
    (q' : VerifierQuery (Fr p) G₁)
    (h : fixedQueryFn vk x fixedEvals q = .ok q') :
    q'.point = vk.domain.rotateOmega x q.2.2 := by
  unfold fixedQueryFn at h
  obtain ⟨com, _hcom, h1⟩ := except_bind_ok h
  obtain ⟨ev, _hev, h2⟩ := except_bind_ok h1
  cases h2
  rfl

theorem mem_mapM {α β ε : Type} {f : α → Except ε β} :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' →
      ∀ b ∈ l', ∃ a ∈ l, f a = .ok b := by
  intro l
  induction l with
  | nil =>
      intro l' h b hb
      cases h
      simp at hb
  | cons a as ih =>
      intro l' h b hb
      rw [List.mapM_cons] at h
      obtain ⟨b0, hb0, h1⟩ := except_bind_ok h
      obtain ⟨bs, hbs, h2⟩ := except_bind_ok h1
      cases h2
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, by simp, hb0⟩
      · obtain ⟨a', ha', hfa'⟩ := ih bs hbs b hb
        exact ⟨a', by simp [ha'], hfa'⟩

theorem collectQueries_fixed_point (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (committedInstances adviceCommitments : Array (Array G₁))
    (instanceEvals adviceEvals : Array (Array (Fr p)))
    (permutationsEvaluated : Array (Permutation.Evaluated (Fr p) G₁))
    (lookupsEvaluated : Array (Array (Logup.Evaluated (Fr p) G₁)))
    (trashcansEvaluated : Array (Array (Trash.Evaluated (Fr p) G₁)))
    (fixedEvals : Array (Fr p)) (permutationsCommon : Permutation.CommonEvaluated (Fr p))
    (linCom : VerifierQuery (Fr p) G₁) (queries : Array (VerifierQuery (Fr p) G₁))
    (h : Verifier.collectQueries nbCommitted vk x committedInstances adviceCommitments
      instanceEvals adviceEvals permutationsEvaluated lookupsEvaluated trashcansEvaluated
      fixedEvals permutationsCommon linCom = .ok queries) :
    ∃ (perProof : List (List (VerifierQuery (Fr p) G₁)))
      (fixed : List (VerifierQuery (Fr p) G₁)),
      (∀ q ∈ fixed, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r) ∧
      queries.toList = perProof.flatten ++ fixed ++
        (permutationsCommon.queries vk.permutation x).toList ++ [linCom] := by
  unfold Verifier.collectQueries at h
  obtain ⟨perProof, _hper, h1⟩ := except_bind_ok h
  obtain ⟨fixed, hfixed, h2⟩ := except_bind_ok h1
  cases h2
  change ((List.zip (List.range vk.cs.fixedQueries.size) vk.cs.fixedQueries.toList).filter
      (fun q => !vk.cs.hasSimpleSelectorCol q.2.1.index)).mapM
      (fixedQueryFn vk x fixedEvals) = .ok fixed at hfixed
  refine ⟨perProof, fixed, ?_, by simp⟩
  intro q hq
  obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hfixed q hq
  exact ⟨a.2.2, fixedQueryFn_point vk x fixedEvals a q hfa⟩


def adviceQueryFn (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ac : Array G₁) (ae : Array (Fr p)) (proof : Nat)
    (q : Nat × (Column × Rotation)) : Except Fault (List (VerifierQuery (Fr p) G₁)) := do
  let com ← Permutation.atIndex ac q.2.1.index "proofs/src/plonk/verifier.rs:605"
  let ev ← Permutation.atIndex ae q.1 "proofs/src/plonk/verifier.rs:606"
  pure [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
    (CommitmentLabel.advice q.2.1.index) (.advice proof q.2.1.index) com ev]

theorem adviceQueryFn_point (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ac : Array G₁) (ae : Array (Fr p)) (proof : Nat) (q : Nat × (Column × Rotation))
    (q' : VerifierQuery (Fr p) G₁)
    (h : adviceQueryFn vk x ac ae proof q = .ok [q']) :
    q'.point = vk.domain.rotateOmega x q.2.2 := by
  unfold adviceQueryFn at h
  obtain ⟨com, _hcom, h1⟩ := except_bind_ok h
  obtain ⟨ev, _hev, h2⟩ := except_bind_ok h1
  change Except.ok [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
    (CommitmentLabel.advice q.2.1.index) (.advice proof q.2.1.index) com ev] = .ok [q'] at h2
  have hq : q' = VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
    (CommitmentLabel.advice q.2.1.index) (.advice proof q.2.1.index) com ev := by
    have h := Except.ok.inj h2
    exact (List.cons.inj h).1.symm
  rw [hq]
  rfl

def instanceQueryFn (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ci : Array G₁) (ie : Array (Fr p)) (proof : Nat)
    (q : Nat × (Column × Rotation)) : Except Fault (List (VerifierQuery (Fr p) G₁)) := do
  if q.2.1.index < nbCommitted then
    let com ← Permutation.atIndex ci q.2.1.index "proofs/src/plonk/verifier.rs:616"
    let ev ← Permutation.atIndex ie q.1 "proofs/src/plonk/verifier.rs:617"
    pure [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
      (CommitmentLabel.instance_ q.2.1.index) (.instance_ proof q.2.1.index) com ev]
  else
    pure []

theorem instanceQueryFn_point (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ci : Array G₁) (ie : Array (Fr p)) (proof : Nat) (q : Nat × (Column × Rotation))
    (q' : VerifierQuery (Fr p) G₁)
    (h : instanceQueryFn nbCommitted vk x ci ie proof q = .ok [q']) :
    q'.point = vk.domain.rotateOmega x q.2.2 := by
  unfold instanceQueryFn at h
  split at h
  · obtain ⟨com, _hcom, h1⟩ := except_bind_ok h
    obtain ⟨ev, _hev, h2⟩ := except_bind_ok h1
    change Except.ok [VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
      (CommitmentLabel.instance_ q.2.1.index) (.instance_ proof q.2.1.index) com ev] = .ok [q'] at h2
    have hq : q' = VerifierQuery.new (vk.domain.rotateOmega x q.2.2)
      (CommitmentLabel.instance_ q.2.1.index) (.instance_ proof q.2.1.index) com ev := by
      have h := Except.ok.inj h2
      exact (List.cons.inj h).1.symm
    rw [hq]
    rfl
  · change Except.ok ([] : List (VerifierQuery (Fr p) G₁)) = .ok [q'] at h
    cases h

theorem adviceQueryFn_mem (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ac : Array G₁) (ae : Array (Fr p)) (proof : Nat) (q0 : Nat × (Column × Rotation))
    (l : List (VerifierQuery (Fr p) G₁)) (h : adviceQueryFn vk x ac ae proof q0 = .ok l)
    {q : VerifierQuery (Fr p) G₁} (hq : q ∈ l) :
    q.point = vk.domain.rotateOmega x q0.2.2 := by
  unfold adviceQueryFn at h
  obtain ⟨com, _hcom, h1⟩ := except_bind_ok h
  obtain ⟨ev, _hev, h2⟩ := except_bind_ok h1
  change Except.ok [VerifierQuery.new (vk.domain.rotateOmega x q0.2.2)
    (CommitmentLabel.advice q0.2.1.index) (.advice proof q0.2.1.index) com ev] = .ok l at h2
  have hl : l = [VerifierQuery.new (vk.domain.rotateOmega x q0.2.2)
    (CommitmentLabel.advice q0.2.1.index) (.advice proof q0.2.1.index) com ev] :=
    (Except.ok.inj h2).symm
  rw [hl] at hq
  simp only [List.mem_singleton] at hq
  rw [hq]
  rfl

theorem instanceQueryFn_mem (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ci : Array G₁) (ie : Array (Fr p)) (proof : Nat) (q0 : Nat × (Column × Rotation))
    (l : List (VerifierQuery (Fr p) G₁))
    (h : instanceQueryFn nbCommitted vk x ci ie proof q0 = .ok l)
    {q : VerifierQuery (Fr p) G₁} (hq : q ∈ l) :
    q.point = vk.domain.rotateOmega x q0.2.2 := by
  unfold instanceQueryFn at h
  split at h
  · obtain ⟨com, _hcom, h1⟩ := except_bind_ok h
    obtain ⟨ev, _hev, h2⟩ := except_bind_ok h1
    change Except.ok [VerifierQuery.new (vk.domain.rotateOmega x q0.2.2)
      (CommitmentLabel.instance_ q0.2.1.index) (.instance_ proof q0.2.1.index) com ev] = .ok l at h2
    have hl : l = [VerifierQuery.new (vk.domain.rotateOmega x q0.2.2)
      (CommitmentLabel.instance_ q0.2.1.index) (.instance_ proof q0.2.1.index) com ev] :=
      (Except.ok.inj h2).symm
    rw [hl] at hq
    simp only [List.mem_singleton] at hq
    rw [hq]
    rfl
  · change Except.ok ([] : List (VerifierQuery (Fr p) G₁)) = .ok l at h
    cases h
    simp at hq

theorem adviceBlock_point (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ac : Array G₁) (ae : Array (Fr p)) (proof : Nat)
    (adv : List (List (VerifierQuery (Fr p) G₁)))
    (hadv : (List.zip (List.range vk.cs.adviceQueries.size)
        vk.cs.adviceQueries.toList).mapM (adviceQueryFn vk x ac ae proof) = .ok adv) :
    ∀ q ∈ adv.flatten, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r := by
  intro q hq
  rw [List.mem_flatten] at hq
  obtain ⟨l, hl, hql⟩ := hq
  obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hadv l hl
  exact ⟨a.2.2, adviceQueryFn_mem vk x ac ae proof a l hfa hql⟩

theorem instanceBlock_point (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ci : Array G₁) (ie : Array (Fr p)) (proof : Nat)
    (inst : List (List (VerifierQuery (Fr p) G₁)))
    (hinst : (List.zip (List.range vk.cs.instanceQueries.size)
        vk.cs.instanceQueries.toList).mapM (instanceQueryFn nbCommitted vk x ci ie proof)
        = .ok inst) :
    ∀ q ∈ inst.flatten, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r := by
  intro q hq
  rw [List.mem_flatten] at hq
  obtain ⟨l, hl, hql⟩ := hq
  obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hinst l hl
  exact ⟨a.2.2, instanceQueryFn_mem nbCommitted vk x ci ie proof a l hfa hql⟩

theorem VerifierQuery.new_point {F C : Type} (point : F) (label : CommitmentLabel)
    (slot : CommitSlot) (com : C) (ev : F) :
    (VerifierQuery.new point label slot com ev).point = point := rfl

theorem Permutation.Evaluated.queries_point
    (ev : Permutation.Evaluated (Fr p) G₁)
    (domain : EvaluationDomain (Fr p)) (blindingFactors : Nat) (x : Fr p)
    (proof : Nat) (result : Array (VerifierQuery (Fr p) G₁))
    (h : Permutation.Evaluated.queries ev domain blindingFactors x proof = .ok result) :
    ∀ q ∈ result.toList,
      q.point = x ∨ q.point = domain.rotateOmega x Rotation.next ∨
        q.point = domain.rotateOmega x
          (Rotation.value (Permutation.negI32 (Permutation.asI32 (blindingFactors + 1)))) := by
  unfold Permutation.Evaluated.queries at h
  obtain ⟨head, hhead, h1⟩ := except_bind_ok h
  obtain ⟨tail, htail, h2⟩ := except_bind_ok h1
  cases h2
  intro q hq
  rw [Array.toList_append, List.mem_append] at hq
  rcases hq with hq | hq
  · rw [List.mem_flatten] at hq
    obtain ⟨l, hl, hql⟩ := hq
    obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hhead l hl
    obtain ⟨c, _hc, hb⟩ := except_bind_ok hfa
    obtain ⟨c', _hc', hb2⟩ := except_bind_ok hb
    change Except.ok [VerifierQuery.new x CommitmentLabel.noLabel
        (.permProduct proof a.1) c a.2.permutationProductEval,
      VerifierQuery.new (domain.rotateOmega x Rotation.next) CommitmentLabel.noLabel
        (.permProduct proof a.1) c' a.2.permutationProductNextEval] = .ok l at hb2
    have hl' : l = [VerifierQuery.new x CommitmentLabel.noLabel
        (.permProduct proof a.1) c a.2.permutationProductEval,
      VerifierQuery.new (domain.rotateOmega x Rotation.next) CommitmentLabel.noLabel
        (.permProduct proof a.1) c' a.2.permutationProductNextEval] :=
      (Except.ok.inj hb2).symm
    rw [hl'] at hql
    simp at hql
    rcases hql with rfl | rfl
    · left; rfl
    · right; left; rfl
  · rw [List.mem_flatten] at hq
    obtain ⟨l, hl, hql⟩ := hq
    obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ htail l hl
    obtain ⟨set, _hset, hb⟩ := except_bind_ok hfa
    obtain ⟨c, _hc, hb1⟩ := except_bind_ok hb
    cases hlast : set.permutationProductLastEval with
    | none =>
        rw [hlast] at hb1
        cases hb1
    | some e =>
        rw [hlast] at hb1
        change Except.ok [VerifierQuery.new
            (domain.rotateOmega x (Rotation.value
              (Permutation.negI32 (Permutation.asI32 (blindingFactors + 1)))))
            CommitmentLabel.noLabel (.permProduct proof a) c e] = .ok l at hb1
        have hl' : l = [VerifierQuery.new
            (domain.rotateOmega x (Rotation.value
              (Permutation.negI32 (Permutation.asI32 (blindingFactors + 1)))))
            CommitmentLabel.noLabel (.permProduct proof a) c e] :=
          (Except.ok.inj hb1).symm
        rw [hl'] at hql
        simp only [List.mem_singleton] at hql
        rw [hql]
        refine Or.inr (Or.inr ?_)
        rw [VerifierQuery.new_point]


end Midfall.LoweringV3
