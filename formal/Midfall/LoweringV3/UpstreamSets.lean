-- |
-- Midfall.LoweringV3.UpstreamSets
--
-- The successful `assertPermutationQueryOrderIsUpstreamEquivalent` check
-- (`Generator/Kzg.lean:628-665`, KZ:136-223) exposes the upstream query list
-- and the equality of its `constructIntermediateSetsImpl` point sets with the
-- generator-order point sets.  This is the bridge the KZG lane needs for the
-- permutationZ block: the raw `pcsQueries` order interleaves each set's
-- last-row opening, while the verifier emits all cur/next openings first and
-- the last openings in descending set order.
import Midfall.LoweringV3.KzgQueryMap

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

/-- **THE UPSTREAM CHECK, INVERTED.** If
    `assertPermutationQueryOrderIsUpstreamEquivalent` succeeds and the
    permutationZ positions are nonempty, then there is an upstream source list
    whose `queryFromPlan` map succeeds, both set constructions succeed, and the
    two point-set lists are equal.  The upstream source list is exactly the
    generator sources with the z slots overwritten by
    `(filter cur/next) ++ reverse (filter last)` (KZ:159-191). -/
theorem assertPermutationQueryOrderIsUpstreamEquivalent_parts
    (meta_ : ConstraintSystemMeta) (data : Data) (generatorOrder : List Query)
    (zPositions : List Nat)
    (hzdef : zPositions = List.filterMap
      (fun x => if isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range meta_.protocol.pcsQueries.length).zip meta_.protocol.pcsQueries))
    (hzNonempty : zPositions ≠ [])
    (h : assertPermutationQueryOrderIsUpstreamEquivalent meta_ data generatorOrder = .ok ()) :
    ∃ (upstreamSources : List PcsQuerySource) (upstreamQueries : List Query)
      (generatorSets upstreamSets : IntermediateSets),
      upstreamSources.mapM (fun source => queryFromPlan source meta_ data) = .ok upstreamQueries ∧
      constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
      constructIntermediateSetsImpl upstreamQueries = .ok upstreamSets ∧
      generatorSets.pointSets = upstreamSets.pointSets := by
  unfold assertPermutationQueryOrderIsUpstreamEquivalent at h
  simp only [Bind.bind] at h
  rw [← hzdef] at h
  by_cases hz : zPositions.isEmpty = true
  · have hnil : zPositions = [] := List.isEmpty_iff.mp hz
    exact absurd hnil hzNonempty
  · rw [ite_eq_right hz] at h
    split at h
    · obtain ⟨zSources, _hzSources, h⟩ := except_bind_ok h
      obtain ⟨upstreamSources, _hupstream, h⟩ := except_bind_ok h
      obtain ⟨upstreamQueries, hupQ, h⟩ := except_bind_ok h
      obtain ⟨generatorSets, hgen, h⟩ := except_bind_ok h
      obtain ⟨upstreamSets, hupSet, h⟩ := except_bind_ok h
      by_cases hpoint : (generatorSets.pointSets == upstreamSets.pointSets) = true
      · rw [ite_eq_left hpoint] at h
        exact ⟨upstreamSources, upstreamQueries, generatorSets, upstreamSets,
          hupQ, hgen, hupSet, beq_iff_eq.mp hpoint⟩
      · rw [ite_eq_right hpoint] at h
        cases h
    · cases h

end Midfall.LoweringV3
