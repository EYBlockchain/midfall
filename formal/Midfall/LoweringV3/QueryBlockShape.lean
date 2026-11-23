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


end Midfall.LoweringV3
