-- |
-- Midfall.LoweringV3.QueryTail
--
-- The generator-side tail of the concrete query pairing: `Generator.queries`
-- maps `ProtocolPlan.pcsQueries` with `queryFromPlan`, so on success its last
-- output is the last source's query.  With the protocol plan ending in
-- `PcsQuerySource.linearization`, the last generator query has rotation 0.
-- `mapM_getLast?_some` is the generic `List.mapM` last-element projection.
import Midfall.LoweringV3.KzgQueryMap
import Midfall.LoweringV3.PcsOrder

set_option autoImplicit false

open Midfall Midfall.Halo2 Midfall.Generator
namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)]

theorem mapM_getLast?_some {α β ε : Type} {f : α → Except ε β} :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' →
      ∀ a, l.getLast? = some a → ∀ b, f a = .ok b → l'.getLast? = some b := by
  intro l
  induction l with
  | nil => intro l' _ a hlast _ _; simp at hlast
  | cons x xs ih =>
      intro l' h a hlast b hfb
      rw [List.mapM_cons] at h
      obtain ⟨b0, hb0, h1⟩ := except_bind_ok h
      obtain ⟨bs, hbs, h2⟩ := except_bind_ok h1
      cases h2
      cases xs with
      | nil =>
          cases hbs
          simp only [List.getLast?_cons, List.getLast?_nil, Option.getD_none] at hlast
          have hxa : x = a := Option.some.inj hlast
          subst hxa
          have hb0b : b0 = b := by
            rw [hb0] at hfb
            exact Except.ok.inj hfb
          subst hb0b
          simp
      | cons y ys =>
          rw [List.getLast?_cons_of_ne_nil (by simp)] at hlast
          have hbsLast := ih bs hbs a hlast b hfb
          rw [List.getLast?_cons, hbsLast]
          simp

theorem queries_mapM_ok (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (hq : queries meta_ data = .ok qs) :
    ∃ qs0, meta_.protocol.pcsQueries.mapM (fun source => queryFromPlan source meta_ data)
      = .ok qs0 ∧ qs = qs0 := by
  unfold queries at hq
  simp only [Bind.bind, Except.bind] at hq
  obtain ⟨qs0, hmap, hrest⟩ := except_bind_ok hq
  by_cases hany : (meta_.protocol.pcsQueries.zip qs0).any
      (fun (source, q) => ecPointBeq q.comm g1Identity && ! isCommittedInstanceSource source) = true
  · rw [if_pos hany] at hrest
    cases hrest
  · rw [if_neg hany] at hrest
    cases hass : assertPermutationQueryOrderIsUpstreamEquivalent meta_ data qs0 with
    | error e =>
        rw [hass] at hrest
        cases hrest
    | ok u =>
        rw [hass] at hrest
        simp only [Except.bind] at hrest
        change Except.ok qs0 = Except.ok qs at hrest
        exact ⟨qs0, hmap, (Except.ok.inj hrest).symm⟩

/-- `Generator.queries` runs the I-6 upstream-order check on the list it has just
    built; a successful `queries` therefore exposes that check's success. This is the
    bridge from `ValidV3.generated` to the upstream source datum. -/
theorem queries_assert_ok (meta_ : ConstraintSystemMeta) (dat : Data)
    (qs : List Query) (hq : queries meta_ dat = .ok qs) :
    assertPermutationQueryOrderIsUpstreamEquivalent meta_ dat qs = .ok () := by
  unfold queries at hq
  simp only [Bind.bind, Except.bind] at hq
  obtain ⟨qs0, _hmap, hrest⟩ := except_bind_ok hq
  by_cases hany : (meta_.protocol.pcsQueries.zip qs0).any
      (fun (source, q) => ecPointBeq q.comm g1Identity && ! isCommittedInstanceSource source) = true
  · rw [ite_eq_left hany] at hrest
    cases hrest
  · rw [ite_eq_right hany] at hrest
    cases hass : assertPermutationQueryOrderIsUpstreamEquivalent meta_ dat qs0 with
    | error e => rw [hass] at hrest; cases hrest
    | ok u =>
        rw [hass] at hrest
        simp only [Except.bind] at hrest
        change Except.ok qs0 = Except.ok qs at hrest
        have hqs : qs = qs0 := (Except.ok.inj hrest).symm
        rw [hqs]
        exact hass

theorem queries_getLast?_some (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (hq : queries meta_ data = .ok qs)
    {source : PcsQuerySource} (hsrc : meta_.protocol.pcsQueries.getLast? = some source)
    {q : Query} (hqr : queryFromPlan source meta_ data = .ok q) :
    qs.getLast? = some q := by
  obtain ⟨qs0, hmap, rfl⟩ := queries_mapM_ok meta_ data qs hq
  exact mapM_getLast?_some _ _ hmap source hsrc q hqr

theorem queries_last_rotation (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (hq : queries meta_ data = .ok qs)
    (hsrc : meta_.protocol.pcsQueries.getLast? = some .linearization) :
    qs.getLast?.map (fun q => q.rotation) = some 0 := by
  have hqr : queryFromPlan .linearization meta_ data =
      .ok (Query.new data.computedQuotientComm 0 data.computedQuotientEval) := rfl
  rw [queries_getLast?_some meta_ data qs hq hsrc hqr]
  rfl

/-- The literal `pcsQueries` construction in `fromConstraintSystem` ends in
    `PcsQuerySource.linearization`, so its last source is definitional once the
    final `validate` wrapper is peeled. -/
theorem pcsQueries_append_linearization_last (l : List PcsQuerySource) :
    (l ++ [PcsQuerySource.linearization]).getLast? =
      some PcsQuerySource.linearization := by
  simp

theorem queryFromPlan_advice_rotation (q : QueryKey) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.advice q) meta_ data = .ok q') :
    q'.rotation = q.rotation := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_fixed_rotation (q : QueryKey) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.fixed q) meta_ data = .ok q') :
    q'.rotation = q.rotation := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_lookupMultiplicity_rotation (lookup : Nat) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.lookupMultiplicity lookup) meta_ data = .ok q') :
    q'.rotation = 0 := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_lookupHelper_rotation (lookup chunk : Nat) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.lookupHelper lookup chunk) meta_ data = .ok q') :
    q'.rotation = 0 := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_trash_rotation (index : Nat) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.trash index) meta_ data = .ok q') :
    q'.rotation = 0 := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_permutationCommon_rotation (column : Column) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.permutationCommon column) meta_ data = .ok q') :
    q'.rotation = 0 := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  repeat (first | split at h | cases h | rfl)

theorem queryFromPlan_committedInstance_rotation (q : QueryKey) (meta_ : ConstraintSystemMeta)
    (data : Data) (q' : Query)
    (h : queryFromPlan (.committedInstance q) meta_ data = .ok q') :
    q'.rotation = q.rotation := by
  unfold queryFromPlan at h
  simp only [Bind.bind, Except.bind] at h
  unfold listGetMut at h
  repeat (first | split at h | cases h | rfl)


theorem queryFromPlan_permutationZ_rotation (set : Nat) (kind : PermutationZEval)
    (meta_ : ConstraintSystemMeta) (data : Data) (q' : Query)
    (h : queryFromPlan (.permutationZ set kind) meta_ data = .ok q') :
    q'.rotation = (PcsQuerySource.permutationZ set kind).rotation meta_.rotationLast := by
  unfold queryFromPlan at h
  cases kind
  · obtain ⟨z, _hz, h1⟩ := except_bind_ok h
    cases z with
    | mk zCur rest =>
      obtain ⟨zNext, zLast⟩ := rest
      obtain ⟨re, hre, h2⟩ := except_bind_ok h1
      obtain ⟨comm, _hcomm, h3⟩ := except_bind_ok h2
      cases h3
      change Except.ok (0, zCur) = Except.ok re at hre
      cases Except.ok.inj hre
      rfl
  · obtain ⟨z, _hz, h1⟩ := except_bind_ok h
    cases z with
    | mk zCur rest =>
      obtain ⟨zNext, zLast⟩ := rest
      obtain ⟨re, hre, h2⟩ := except_bind_ok h1
      obtain ⟨comm, _hcomm, h3⟩ := except_bind_ok h2
      cases h3
      change Except.ok (1, zNext) = Except.ok re at hre
      cases Except.ok.inj hre
      rfl
  · obtain ⟨z, _hz, h1⟩ := except_bind_ok h
    cases z with
    | mk zCur rest =>
      obtain ⟨zNext, zLast⟩ := rest
      cases hz : zLast with
      | none =>
          rw [hz] at h1
          cases h1
      | some e =>
          rw [hz] at h1
          obtain ⟨re, hre, h2⟩ := except_bind_ok h1
          obtain ⟨comm, _hcomm, h3⟩ := except_bind_ok h2
          cases h3
          change Except.ok (meta_.rotationLast, e) = Except.ok re at hre
          cases Except.ok.inj hre
          rfl

theorem queryFromPlan_lookupAccumulator_rotation (lookup : Nat) (rotation : Int)
    (meta_ : ConstraintSystemMeta) (data : Data) (q' : Query)
    (h : queryFromPlan (.lookupAccumulator lookup rotation) meta_ data = .ok q') :
    q'.rotation = rotation := by
  unfold queryFromPlan at h
  obtain ⟨z, _hz, h1⟩ := except_bind_ok h
  cases z with
  | mk m rest =>
    obtain ⟨hs, zz⟩ := rest
    obtain ⟨zEval, zNextEval⟩ := zz
    by_cases hr0 : rotation = 0
    · subst hr0
      obtain ⟨eval, heval, h2⟩ := except_bind_ok h1
      obtain ⟨comm, _hcomm, h3⟩ := except_bind_ok h2
      cases h3
      change Except.ok zEval = Except.ok eval at heval
      cases Except.ok.inj heval
      rfl
    · by_cases hr1 : rotation = 1
      · subst hr1
        obtain ⟨eval, heval, h2⟩ := except_bind_ok h1
        obtain ⟨comm, _hcomm, h3⟩ := except_bind_ok h2
        cases h3
        change Except.ok zNextEval = Except.ok eval at heval
        cases Except.ok.inj heval
        rfl
      · simp [hr0, hr1] at h1
        cases h1

theorem queryFromPlan_linearization (meta_ : ConstraintSystemMeta) (data : Data) :
    queryFromPlan .linearization meta_ data =
      .ok (Query.new data.computedQuotientComm 0 data.computedQuotientEval) := rfl

theorem PcsQuerySource.rotation_linearization (rotationLast : Int) :
    PcsQuerySource.linearization.rotation rotationLast = 0 := rfl


/-- Splitting a successful `mapM` over an append. -/
theorem mapM_append_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ (l₁ l₂ : List α) (out : List β),
      (l₁ ++ l₂).mapM f = .ok out →
      ∃ o₁ o₂, l₁.mapM f = .ok o₁ ∧ l₂.mapM f = .ok o₂ ∧ out = o₁ ++ o₂ := by
  intro l₁ l₂ out h
  rw [List.mapM_append] at h
  obtain ⟨o₁, h₁, h⟩ := except_bind_ok h
  obtain ⟨o₂, h₂, h₃⟩ := except_bind_ok h
  cases h₃
  exact ⟨o₁, o₂, h₁, h₂, rfl⟩

/-- A successful `mapM` over a flattened block list splits into one successful
    `mapM` per block, preserving the block order. -/
theorem mapM_flatten_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ (blocks : List (List α)) (out : List β),
      blocks.flatten.mapM f = .ok out →
      ∃ outs, blocks.mapM (fun b => b.mapM f) = .ok outs ∧ out = outs.flatten := by
  intro blocks
  induction blocks with
  | nil =>
      intro out h
      cases h
      exact ⟨[], rfl, rfl⟩
  | cons b bs ih =>
      intro out h
      rw [List.flatten_cons] at h
      obtain ⟨o, obs, ho, hobs, hout⟩ := mapM_append_ok b bs.flatten out h
      obtain ⟨outs, hmap, hfl⟩ := ih obs hobs
      rw [List.mapM_cons]
      refine ⟨o :: outs, ?_, ?_⟩
      · rw [ho, hmap]
        rfl
      · rw [hout, hfl]
        rfl

/-- **The generator's query list is the eight-block spine.** If the plan's
    `pcsQueries` is the literal block list, then a successful `Generator.queries`
    produces exactly one query list per block, in the block order, whose
    flattening is the output. -/
theorem queries_pcsBlocks (meta_ : ConstraintSystemMeta) (data : Data)
    (qs : List Query) (hq : queries meta_ data = .ok qs)
    (cs : ConstraintSystem (Fr p)) (nb dg : Nat) (lc : List Nat)
    (hPcs : meta_.protocol.pcsQueries = pcsBlockList cs nb dg lc) :
    ∃ outs, (pcsBlocks cs nb dg lc).mapM
        (fun b => b.mapM (fun source => queryFromPlan source meta_ data)) = .ok outs ∧
      qs = outs.flatten := by
  obtain ⟨qs0, hmap, rfl⟩ := queries_mapM_ok meta_ data qs hq
  rw [hPcs, pcsBlockList] at hmap
  exact mapM_flatten_ok _ _ hmap

end Midfall.LoweringV3
