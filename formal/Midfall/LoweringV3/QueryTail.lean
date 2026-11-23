-- |
-- Midfall.LoweringV3.QueryTail
--
-- The generator-side tail of the concrete query pairing: `Generator.queries`
-- maps `ProtocolPlan.pcsQueries` with `queryFromPlan`, so on success its last
-- output is the last source's query.  With the protocol plan ending in
-- `PcsQuerySource.linearization`, the last generator query has rotation 0.
-- `mapM_getLast?_some` is the generic `List.mapM` last-element projection.
import Midfall.LoweringV3.KzgQueryMap

set_option autoImplicit false

open Midfall Midfall.Halo2 Midfall.Generator
namespace Midfall.LoweringV3

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

theorem queryFromPlan_linearization (meta_ : ConstraintSystemMeta) (data : Data) :
    queryFromPlan .linearization meta_ data =
      .ok (Query.new data.computedQuotientComm 0 data.computedQuotientEval) := rfl

theorem PcsQuerySource.rotation_linearization (rotationLast : Int) :
    PcsQuerySource.linearization.rotation rotationLast = 0 := rfl

end Midfall.LoweringV3
