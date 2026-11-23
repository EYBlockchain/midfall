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
import Midfall.LoweringV3.LinearizeEntry
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


/-! ## The per-proof block

The body of `collectQueries`'s per-proof `mapM`: advice, committed instance,
permutation product, lookups, trashcans.  Factored out so the append
decomposition and the per-block point shapes can be stated and composed. -/
def perProofQueries (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (proof : Nat) (ci : Array G₁) (ie : Array (Fr p))
    (ac : Array G₁) (ae : Array (Fr p))
    (pe : Permutation.Evaluated (Fr p) G₁)
    (le : Array (Logup.Evaluated (Fr p) G₁))
    (te : Array (Trash.Evaluated (Fr p) G₁)) :
    Except Fault (List (VerifierQuery (Fr p) G₁)) := do
  let adv ← (List.zip (List.range vk.cs.adviceQueries.size)
      vk.cs.adviceQueries.toList).mapM (adviceQueryFn vk x ac ae proof)
  let inst ← (List.zip (List.range vk.cs.instanceQueries.size)
      vk.cs.instanceQueries.toList).mapM (instanceQueryFn nbCommitted vk x ci ie proof)
  let bf ← vk.cs.blindingFactors
  let perm ← pe.queries (p := p) vk.domain bf x proof
  let lk := (List.zip (List.range le.size) le.toList).flatMap fun (l, lq) =>
    (lq.queries (p := p) vk.domain x proof l).toList
  let tr := (List.zip (List.range te.size) te.toList).flatMap fun (i, tq) =>
    (tq.queries (p := p) x proof i).toList
  pure (adv.flatten ++ inst.flatten ++ perm.toList ++ lk ++ tr)

theorem perProofQueries_parts (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (proof : Nat) (ci : Array G₁) (ie : Array (Fr p))
    (ac : Array G₁) (ae : Array (Fr p))
    (pe : Permutation.Evaluated (Fr p) G₁)
    (le : Array (Logup.Evaluated (Fr p) G₁))
    (te : Array (Trash.Evaluated (Fr p) G₁))
    (out : List (VerifierQuery (Fr p) G₁))
    (h : perProofQueries nbCommitted vk x proof ci ie ac ae pe le te = .ok out) :
    ∃ (adv inst : List (List (VerifierQuery (Fr p) G₁)))
      (bf : Nat) (perm : Array (VerifierQuery (Fr p) G₁))
      (lk tr : List (VerifierQuery (Fr p) G₁)),
      (List.zip (List.range vk.cs.adviceQueries.size)
          vk.cs.adviceQueries.toList).mapM (adviceQueryFn vk x ac ae proof) = .ok adv ∧
      (List.zip (List.range vk.cs.instanceQueries.size)
          vk.cs.instanceQueries.toList).mapM
          (instanceQueryFn nbCommitted vk x ci ie proof) = .ok inst ∧
      vk.cs.blindingFactors = .ok bf ∧
      pe.queries (p := p) vk.domain bf x proof = .ok perm ∧
      lk = (List.zip (List.range le.size) le.toList).flatMap (fun (l, lq) =>
        (lq.queries (p := p) vk.domain x proof l).toList) ∧
      tr = (List.zip (List.range te.size) te.toList).flatMap (fun (i, tq) =>
        (tq.queries (p := p) x proof i).toList) ∧
      out = adv.flatten ++ inst.flatten ++ perm.toList ++ lk ++ tr := by
  unfold perProofQueries at h
  obtain ⟨adv, hadv, h1⟩ := except_bind_ok h
  obtain ⟨inst, hinst, h2⟩ := except_bind_ok h1
  obtain ⟨bf, hbf, h3⟩ := except_bind_ok h2
  obtain ⟨perm, hperm, h4⟩ := except_bind_ok h3
  cases h4
  exact ⟨adv, inst, bf, perm, _, _, hadv, hinst, hbf, hperm, rfl, rfl, rfl⟩

theorem lookupBlock_point (vk : VerifyingKey (Fr p) G₁) (x : Fr p) (proof : Nat)
    (le : Array (Logup.Evaluated (Fr p) G₁)) :
    ∀ q ∈ (List.zip (List.range le.size) le.toList).flatMap (fun (l, lq) =>
        (lq.queries (p := p) vk.domain x proof l).toList),
      q.point = x ∨ q.point = vk.domain.rotateOmega x Rotation.next := by
  intro q hq
  rw [List.mem_flatMap] at hq
  obtain ⟨a, _ha, hq⟩ := hq
  exact Logup.Evaluated.queries_point a.2 vk.domain x proof a.1 q hq

theorem trashBlock_point (vk : VerifyingKey (Fr p) G₁) (x : Fr p) (proof : Nat)
    (te : Array (Trash.Evaluated (Fr p) G₁)) :
    ∀ q ∈ (List.zip (List.range te.size) te.toList).flatMap (fun (i, tq) =>
        (tq.queries (p := p) x proof i).toList), q.point = x := by
  intro q hq
  rw [List.mem_flatMap] at hq
  obtain ⟨a, _ha, hq⟩ := hq
  exact Trash.Evaluated.queries_point a.2 x proof a.1 q hq

theorem perProofQueries_point (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (proof : Nat) (ci : Array G₁) (ie : Array (Fr p))
    (ac : Array G₁) (ae : Array (Fr p))
    (pe : Permutation.Evaluated (Fr p) G₁)
    (le : Array (Logup.Evaluated (Fr p) G₁))
    (te : Array (Trash.Evaluated (Fr p) G₁))
    (out : List (VerifierQuery (Fr p) G₁))
    (h : perProofQueries nbCommitted vk x proof ci ie ac ae pe le te = .ok out) :
    ∀ q ∈ out, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r := by
  obtain ⟨adv, inst, bf, perm, lk, tr, hadv, hinst, _hbf, hperm, hlk, htr, hout⟩ :=
    perProofQueries_parts nbCommitted vk x proof ci ie ac ae pe le te out h
  subst hout
  intro q hq
  rw [List.mem_append] at hq
  rcases hq with hq | hq
  · rw [List.mem_append] at hq
    rcases hq with hq | hq
    · rw [List.mem_append] at hq
      rcases hq with hq | hq
      · rw [List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨r, hr⟩ := adviceBlock_point vk x ac ae proof adv hadv q hq
          exact ⟨r, hr⟩
        · obtain ⟨r, hr⟩ := instanceBlock_point nbCommitted vk x ci ie proof inst hinst q hq
          exact ⟨r, hr⟩
      · have hr := Permutation.Evaluated.queries_point pe vk.domain bf x proof perm
          hperm q hq
        rcases hr with hr | hr | hr
        · exact ⟨Rotation.value 0, by rw [hr, rotateOmega_zero]⟩
        · exact ⟨Rotation.next, hr⟩
        · exact ⟨Rotation.value (Permutation.negI32
            (Permutation.asI32 (bf + 1))), hr⟩
    · -- the lookup flatMap: collective lemma over the whole block
      have hlk' : lk = (List.zip (List.range le.size) le.toList).flatMap (fun (l, lq) =>
          (lq.queries (p := p) vk.domain x proof l).toList) := hlk
      rw [hlk'] at hq
      have hr := lookupBlock_point vk x proof le q hq
      rcases hr with hr | hr
      · exact ⟨Rotation.value 0, by rw [hr, rotateOmega_zero]⟩
      · exact ⟨Rotation.next, hr⟩
  · have htr' : tr = (List.zip (List.range te.size) te.toList).flatMap (fun (i, tq) =>
        (tq.queries (p := p) x proof i).toList) := htr
    rw [htr'] at hq
    have hr := trashBlock_point vk x proof te q hq
    exact ⟨Rotation.value 0, by rw [hr, rotateOmega_zero]⟩

theorem collectQueries_perProof_point (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
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
      (∀ q ∈ perProof.flatten, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r) ∧
      (∀ q ∈ fixed, ∃ r : Rotation, q.point = vk.domain.rotateOmega x r) ∧
      queries.toList = perProof.flatten ++ fixed ++
        (permutationsCommon.queries vk.permutation x).toList ++ [linCom] := by
  unfold Verifier.collectQueries at h
  dsimp only at h
  obtain ⟨perProof, hper, h1⟩ := except_bind_ok h
  obtain ⟨fixed, hfixed, h2⟩ := except_bind_ok h1
  cases h2
  refine ⟨perProof, fixed, ?_, ?_, by simp⟩
  · intro q hq
    rw [List.mem_flatten] at hq
    obtain ⟨l, hl, hql⟩ := hq
    obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hper l hl
    obtain ⟨proof, e⟩ := a
    have hbody : perProofQueries nbCommitted vk x proof
        e.1.1.1.1.1.1 e.1.1.1.1.1.2 e.1.1.1.1.2 e.1.1.1.2 e.1.1.2 e.1.2 e.2 = .ok l := hfa
    exact perProofQueries_point nbCommitted vk x proof
      e.1.1.1.1.1.1 e.1.1.1.1.1.2 e.1.1.1.1.2 e.1.1.1.2 e.1.1.2 e.1.2 e.2 l hbody q hql
  · intro q hq
    obtain ⟨a, _ha, hfa⟩ := mem_mapM _ _ hfixed q hq
    have hfbody : fixedQueryFn vk x fixedEvals a = .ok q := hfa
    exact ⟨a.2.2, fixedQueryFn_point vk x fixedEvals a q hfbody⟩


theorem collectQueries_single_blocks (nbCommitted : Nat) (vk : VerifyingKey (Fr p) G₁) (x : Fr p)
    (ci ac : G₁) (ie ae : Fr p)
    (pe : Permutation.Evaluated (Fr p) G₁)
    (le : Logup.Evaluated (Fr p) G₁)
    (te : Trash.Evaluated (Fr p) G₁)
    (fixedEvals : Array (Fr p)) (permutationsCommon : Permutation.CommonEvaluated (Fr p))
    (linCom : VerifierQuery (Fr p) G₁) (queries : Array (VerifierQuery (Fr p) G₁))
    (h : Verifier.collectQueries nbCommitted vk x #[#[ci]] #[#[ac]]
      #[#[ie]] #[#[ae]] #[pe] #[#[le]] #[#[te]]
      fixedEvals permutationsCommon linCom = .ok queries) :
    ∃ (adv inst : List (List (VerifierQuery (Fr p) G₁)))
      (perm : Array (VerifierQuery (Fr p) G₁))
      (fixed : List (VerifierQuery (Fr p) G₁)),
      queries.toList = adv.flatten ++ inst.flatten ++ perm.toList ++
        (le.queries vk.domain x 0 0).toList ++ (te.queries x 0 0).toList ++
        fixed ++ (permutationsCommon.queries vk.permutation x).toList ++ [linCom] := by
  unfold Verifier.collectQueries at h
  dsimp only at h
  simp only [List.zip_cons_cons, List.zip_nil_right,
    List.length_cons, List.length_nil] at h
  obtain ⟨perProof, hper, h1⟩ := except_bind_ok h
  obtain ⟨fixed, _hfixed, h2⟩ := except_bind_ok h1
  cases h2
  simp only [Nat.zero_add, List.range_one, List.zip_cons_cons, List.zip_nil_right] at hper
  rw [List.mapM_cons, List.mapM_nil] at hper
  obtain ⟨out, hout, h3⟩ := except_bind_ok hper
  obtain ⟨tail, htail, h4⟩ := except_bind_ok h3
  cases htail
  cases h4
  dsimp only at hout
  obtain ⟨adv, _hadv, h1⟩ := except_bind_ok hout
  obtain ⟨inst, _hinst, h2⟩ := except_bind_ok h1
  obtain ⟨bf, _hbf, h3⟩ := except_bind_ok h2
  obtain ⟨perm, _hperm, h4⟩ := except_bind_ok h3
  cases h4
  refine ⟨adv, inst, perm, fixed, ?_⟩
  simp [List.flatten_cons]


end Midfall.LoweringV3
