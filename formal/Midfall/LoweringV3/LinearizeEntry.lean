-- |
-- Midfall.LoweringV3.LinearizeEntry
--
-- The linearization-entry end of the D-GATE10 datum: `collectQueries` appends
-- exactly one `linCom` last, and `computeLinearizationCommitment` builds it at
-- point `x` (label `linearization_poly`, commitment `.linear`). Hence the last
-- query `linearize` emits is the linearization query, at `alg.x`. This is the
-- order/point half of the `linearize` ↔ `Generator.Query` correspondence; the
-- remaining half is the `.linear` points-vs-`computedQuotientComm` identity.
import Midfall.Halo2.Exec.Verifier
import Midfall.LoweringV3.KzgQueryMap

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}

theorem collectQueries_back? (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
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
    queries.back? = some linCom := by
  unfold Verifier.collectQueries at h
  obtain ⟨perProof, _hper, h1⟩ := except_bind_ok h
  obtain ⟨fixed, _hfixed, h2⟩ := except_bind_ok h1
  cases h2
  have harr : (perProof.flatten ++ fixed ++ (permutationsCommon.queries vk.permutation x).toList ++
      [linCom]).toArray =
      (perProof.flatten ++ fixed ++ (permutationsCommon.queries vk.permutation x).toList).toArray.push linCom := by
    rw [List.toArray_eq_iff]
    simp [Array.toList_push]
  rw [harr, Array.back?_push]


variable {G : Type}

theorem VerifierQuery.newLinear_point {F C : Type} (point : F) (label : CommitmentLabel)
    (pts : Array C) (scals : Array F) (labs : Array CommitmentLabel) (ev : F)
    (q : VerifierQuery F C)
    (h : VerifierQuery.newLinear point label pts scals labs ev = .ok q) :
    q.point = point := by
  unfold VerifierQuery.newLinear at h
  by_cases h1 : (pts.size == scals.size) = true
  · rw [if_pos h1] at h
    by_cases h2 : (pts.size == labs.size) = true
    · rw [if_pos h2] at h
      cases h
      rfl
    · rw [if_neg h2] at h
      change (Except.error (Fault.panic "proofs/src/poly/query.rs:222") :
        Except Fault (VerifierQuery F C)) = .ok q at h
      cases h
  · rw [if_neg h1] at h
    change (Except.error (Fault.panic "proofs/src/poly/query.rs:217") :
      Except Fault (VerifierQuery F C)) = .ok q at h
    cases h

theorem computeLinearizationCommitment_point
    (expressions : Array (Option Nat × Fr p)) (vk : VerifyingKey (Fr p) G)
    (x y xn splittingFactor : Fr p) (quotientLimbCommitments : Array G)
    (linCom : VerifierQuery (Fr p) G)
    (h : Midfall.Halo2.computeLinearizationCommitment
      (F := Fr p) (G₁ := G) expressions vk x y xn splittingFactor quotientLimbCommitments
      = .ok linCom) :
    linCom.point = x := by
  unfold Midfall.Halo2.computeLinearizationCommitment at h
  split at h
  · cases h
  · simp only [Bind.bind, Except.bind] at h
    obtain ⟨tuple, _hfold, hfinal⟩ := except_bind_ok h
    obtain ⟨pts, scals, labs, ev⟩ := tuple
    exact VerifierQuery.newLinear_point x (CommitmentLabel.custom "linearization_poly")
      pts.toArray scals.toArray labs.toArray ev linCom hfinal

theorem linearize_back?_point (delta : Fr p) (vk : VerifyingKey (Fr p) G₁)
    (adviceCommitments : Array (Array G₁)) (committedInstances : Array (Array G₁))
    (y beta gamma theta trashChallenge : Fr p) (challenges : Array (Fr p))
    (alg : Verifier.AlgebraRead (Fr p) G₁)
    (queries : Array (VerifierQuery (Fr p) G₁))
    (h : Verifier.linearize (p := p) delta vk adviceCommitments committedInstances
      y beta gamma theta trashChallenge challenges alg = .ok queries) :
    queries.back?.map (fun q => q.point) = some alg.x := by
  unfold Verifier.linearize at h
  simp only [Bind.bind, Except.bind] at h
  obtain ⟨expressions, _hexp, h1⟩ := except_bind_ok h
  obtain ⟨linCom, _hlin, h2⟩ := except_bind_ok h1
  have hback := collectQueries_back? (p := p) alg.nbCommitted vk alg.x
    committedInstances adviceCommitments alg.instanceEvals alg.adviceEvals
    alg.permutationsEvaluated alg.lookupsEvaluated alg.trashcansEvaluated
    alg.fixedEvals alg.permutationsCommon linCom queries h2
  rw [hback]
  change some linCom.point = some alg.x
  rw [computeLinearizationCommitment_point expressions vk alg.x y alg.xn
    alg.splittingFactor alg.quotientLimbComs linCom _hlin]

end Midfall.LoweringV3
