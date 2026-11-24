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
import Midfall.LoweringV3.PcsOrder

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

variable {p : ℕ} [Fact (Nat.Prime p)]

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
    ∃ (zSources upstreamSources : List PcsQuerySource) (upstreamQueries : List Query)
      (generatorSets upstreamSets : IntermediateSets),
      zPositions.mapM (fun i => listGetMut meta_.protocol.pcsQueries i
        "proofs/solidity-verifier/src/lowering/kzg/mod.rs:158") = .ok zSources ∧
      (zPositions.zip (upstreamBlock zSources)).foldlM
        (fun acc (p : Nat × PcsQuerySource) => listSetMut acc p.1 p.2
          "proofs/solidity-verifier/src/lowering/kzg/mod.rs:190")
        meta_.protocol.pcsQueries = .ok upstreamSources ∧
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
    · obtain ⟨zSources, hzSources, h⟩ := except_bind_ok h
      obtain ⟨upstreamSources, hupstream, h⟩ := except_bind_ok h
      obtain ⟨upstreamQueries, hupQ, h⟩ := except_bind_ok h
      obtain ⟨generatorSets, hgen, h⟩ := except_bind_ok h
      obtain ⟨upstreamSets, hupSet, h⟩ := except_bind_ok h
      by_cases hpoint : (generatorSets.pointSets == upstreamSets.pointSets) = true
      · rw [ite_eq_left hpoint] at h
        exact ⟨zSources, upstreamSources, upstreamQueries, generatorSets, upstreamSets,
          hzSources, hupstream, hupQ, hgen, hupSet, beq_iff_eq.mp hpoint⟩
      · rw [ite_eq_right hpoint] at h
        cases h
    · cases h

theorem map_snd_zipIdx {α : Type} (l : List α) (k : Nat) :
    (l.zipIdx k).map Prod.snd = (List.range l.length).map (fun j => k + j) := by
  induction l generalizing k with
  | nil => rfl
  | cons a as ih =>
      simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range_succ_eq_map]
      rw [ih]
      have h : List.map (fun j => k + 1 + j) (List.range as.length) =
          List.map (fun j => k + j) (List.map Nat.succ (List.range as.length)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro j _hj
        change k + 1 + j = k + (j + 1)
        omega
      rw [h]
      simp

theorem filterMap_zipIdx_false {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (h : ∀ a ∈ l, p a = false) :
    (l.zipIdx k).filterMap (fun x => if p x.1 then some x.2 else none) = [] := by
  induction l generalizing k with
  | nil => rfl
  | cons a as ih =>
      rw [List.zipIdx_cons, List.filterMap_cons, h a (by simp)]
      exact ih (k + 1) (fun b hb => h b (by simp [hb]))

theorem filterMap_zipIdx_true {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (h : ∀ a ∈ l, p a = true) :
    (l.zipIdx k).filterMap (fun x => if p x.1 then some x.2 else none) =
      (l.zipIdx k).map Prod.snd := by
  induction l generalizing k with
  | nil => rfl
  | cons a as ih =>
      have ha : p a = true := h a (by simp)
      rw [List.zipIdx_cons, List.filterMap_cons, List.map_cons]
      simp only [ha, ite_true]
      rw [ih (k + 1) (fun b hb => h b (by simp [hb]))]

theorem filterMap_zipIdx_append_block {α : Type} (p : α → Bool) (pre block post : List α)
    (hpre : ∀ a ∈ pre, p a = false)
    (hblock : ∀ a ∈ block, p a = true)
    (hpost : ∀ a ∈ post, p a = false) :
    (List.filterMap (fun x : α × Nat => if p x.1 then some x.2 else none)
      ((pre ++ block ++ post).zipIdx 0)) =
      (block.zipIdx pre.length).map Prod.snd := by
  rw [List.append_assoc, List.zipIdx_append, List.zipIdx_append,
    List.filterMap_append, List.filterMap_append]
  rw [filterMap_zipIdx_false p pre 0 hpre,
    filterMap_zipIdx_true p block (0 + pre.length) hblock,
    filterMap_zipIdx_false p post (0 + pre.length + block.length) hpost]
  simp

theorem zipIdx_map_swap_eq_zip_range_gen {α : Type} (l : List α) (k : Nat) :
    (l.zipIdx k).map Prod.swap = ((List.range l.length).map (fun j => k + j)).zip l := by
  induction l generalizing k with
  | nil => rfl
  | cons a as ih =>
      simp only [List.zipIdx_cons, List.length_cons, List.map_cons, List.range_succ_eq_map,
        List.zip_cons_cons, Prod.swap]
      rw [ih, List.map_map]
      have h : List.map (fun j => k + 1 + j) (List.range as.length) =
          List.map ((fun j => k + j) ∘ Nat.succ) (List.range as.length) := by
        apply List.map_congr_left
        intro j _hj
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [h]
      simp

theorem zipIdx_map_swap_eq_zip_range_zero {α : Type} (l : List α) :
    (l.zipIdx 0).map Prod.swap = (List.range l.length).zip l := by
  simpa using zipIdx_map_swap_eq_zip_range_gen l 0

theorem filterMap_zip_range_append_block {α : Type} (p : α → Bool) (pre block post : List α)
    (hpre : ∀ a ∈ pre, p a = false)
    (hblock : ∀ a ∈ block, p a = true)
    (hpost : ∀ a ∈ post, p a = false) :
    (List.filterMap (fun x : Nat × α => if p x.2 then some x.1 else none)
      ((List.range (pre ++ block ++ post).length).zip (pre ++ block ++ post))) =
      (List.range block.length).map (fun j => pre.length + j) := by
  rw [← zipIdx_map_swap_eq_zip_range_zero (pre ++ block ++ post)]
  rw [List.filterMap_map]
  simp only [Function.comp_def, Prod.swap]
  rw [filterMap_zipIdx_append_block p pre block post hpre hblock hpost]
  rw [map_snd_zipIdx]

open Midfall.Generator

theorem getElem_append_block {α : Type} (pre block post : List α) (j : Nat) (hj : j < block.length) :
    (pre ++ block ++ post)[pre.length + j]'(by
      simp only [List.length_append]
      omega) = block[j] := by
  have h0 : pre.length + j < (pre ++ block ++ post).length := by
    simp only [List.length_append]; omega
  have h1 : pre.length + j < (pre ++ block).length := by
    simp only [List.length_append]; omega
  have h2 : pre.length ≤ pre.length + j := by omega
  calc
    (pre ++ block ++ post)[pre.length + j]'h0 = (pre ++ block)[pre.length + j]'h1 :=
      List.getElem_append_left (as := pre ++ block) (bs := post) h1
    _ = block[j]'hj := by
      simpa [Nat.add_sub_cancel_left] using
        (List.getElem_append_right (as := pre) (bs := block) (i := pre.length + j) h2)

theorem mapM_get_consecutive {α : Type} (site : String) (pre block post : List α) :
    ((List.range block.length).map (fun j => pre.length + j)).mapM
      (fun i => listGetMut (pre ++ block ++ post) i site) = .ok block := by
  induction block generalizing pre with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.mapM_cons]
      have hidx : pre.length < (pre ++ b :: bs ++ post).length := by
        simp only [List.length_append, List.length_cons]; omega
      have hget : (pre ++ b :: bs ++ post)[pre.length]'hidx = b := by
        simpa using (getElem_append_block pre (b :: bs) post 0 (by simp))
      have hb : listGetMut (pre ++ b :: bs ++ post) pre.length site = .ok b := by
        rw [listGetMut_eq_ok _ _ _ hidx]
        exact congrArg Except.ok hget
      simp only [Nat.add_zero, hb, Bind.bind, Except.bind]
      have hfun : ((fun j : Nat => pre.length + j) ∘ Nat.succ) =
          (fun j => (pre ++ [b]).length + j) := by
        funext x
        simp only [Function.comp_def, List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [hfun]
      have hmap := ih (pre ++ [b])
      simp only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] at hmap ⊢
      rw [hmap]
      rfl

open Midfall.Generator

theorem foldlM_set_consecutive {α : Type} (site : String) (pre old new post : List α)
    (hlen : new.length = old.length) :
    (((List.range new.length).map (fun j => pre.length + j)).zip new).foldlM
        (fun acc (p : Nat × α) => listSetMut acc p.1 p.2 site)
        (pre ++ old ++ post) = .ok (pre ++ new ++ post) := by
  induction new generalizing pre old with
  | nil =>
      cases old with
      | nil => rfl
      | cons o os => simp at hlen
  | cons v vs ih =>
      cases old with
      | nil => simp at hlen
      | cons o os =>
          have hlen' : vs.length = os.length := by simpa using hlen
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.zip_cons_cons,
            List.foldlM_cons]
          have hidx : pre.length < (pre ++ o :: os ++ post).length := by
            simp only [List.length_append, List.length_cons]; omega
          have hset : listSetMut (pre ++ o :: os ++ post) pre.length v site =
              .ok (pre ++ [v] ++ os ++ post) := by
            rw [listSetMut_eq_ok _ _ _ site hidx]
            simp
          simp only [Nat.add_zero, hset, Bind.bind, Except.bind]
          have hmap := ih (pre ++ [v]) os hlen'
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
            List.map_map, Function.comp_def] at hmap ⊢
          convert hmap using 2
          congr 1
          apply List.map_congr_left
          intro x _hx
          omega

theorem permZBlock_partition (k : Nat) :
    ∀ s ∈ Generator.permZBlock k,
      Generator.permZIsCurOrNext s = true ∨ Generator.permZIsLast s = true := by
  intro s hs
  simp only [Generator.permZBlock, List.mem_flatten] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  simp only [List.mem_map] at hl
  obtain ⟨set, _hset, rfl⟩ := hl
  by_cases h : set + 1 != k
  · simp [h] at hsl
    rcases hsl with rfl | rfl | rfl <;> simp [permZIsCurOrNext, permZIsLast]
  · simp [h] at hsl
    rcases hsl with rfl | rfl <;> simp [permZIsCurOrNext, permZIsLast]

theorem permZBlock_disjoint (k : Nat) :
    ∀ s ∈ Generator.permZBlock k,
      Generator.permZIsCurOrNext s = true → Generator.permZIsLast s = true → False := by
  intro s hs hc hl
  simp only [Generator.permZBlock, List.mem_flatten] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  simp only [List.mem_map] at hl
  obtain ⟨set, _hset, rfl⟩ := hl
  by_cases h : set + 1 != k
  · simp [h] at hsl
    rcases hsl with rfl | rfl | rfl <;> simp [permZIsCurOrNext, permZIsLast] at hc hl
  · simp [h] at hsl
    rcases hsl with rfl | rfl <;> simp [permZIsCurOrNext, permZIsLast] at hc hl

theorem length_filter_add_filter_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases h : p a = true <;> simp [h, ih] <;> omega

theorem permZUpstream_length (k : Nat) :
    (Generator.permZUpstream k).length = (Generator.permZBlock k).length := by
  have hpart := permZBlock_partition k
  have hdisj := permZBlock_disjoint k
  have hlast : (Generator.permZBlock k).filter Generator.permZIsLast =
      (Generator.permZBlock k).filter (fun s => !Generator.permZIsCurOrNext s) := by
    apply List.filter_congr
    intro s hs
    by_cases hc : Generator.permZIsCurOrNext s = true
    · have hl : Generator.permZIsLast s = false := by
        cases h : Generator.permZIsLast s with
        | false => rfl
        | true => exact absurd h (hdisj s hs hc)
      simp [hc, hl]
    · have hc' : Generator.permZIsCurOrNext s = false := by simpa using hc
      have hl : Generator.permZIsLast s = true := by
        rcases hpart s hs with h | h
        · exact absurd h hc
        · exact h
      simp [hc', hl]
  rw [← Generator.upstreamBlock_permZBlock]
  unfold Generator.upstreamBlock
  rw [List.length_append, List.length_reverse, hlast]
  exact length_filter_add_filter_not Generator.permZIsCurOrNext (Generator.permZBlock k)

theorem pcsAdviceBlock_zfree (cs : ConstraintSystem (Fr p)) :
    ∀ s ∈ Generator.pcsAdviceBlock cs, Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsAdviceBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, b, _, h⟩
  rw [← h]

theorem pcsCommittedInstanceBlock_zfree (cs : ConstraintSystem (Fr p)) (nb : Nat) :
    ∀ s ∈ Generator.pcsCommittedInstanceBlock cs nb,
      Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsCommittedInstanceBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, b, ⟨_, _⟩, h⟩
  rw [← h]

theorem pcsLookupBlock_zfree (cs : ConstraintSystem (Fr p)) (dg : Nat) (lc : List Nat) :
    ∀ s ∈ Generator.pcsLookupBlock cs dg lc,
      Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsLookupBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, b, _, h | ⟨chunk, _, h⟩ | h | h⟩
  all_goals subst s
  all_goals rfl

theorem pcsTrashBlock_zfree (cs : ConstraintSystem (Fr p)) :
    ∀ s ∈ Generator.pcsTrashBlock cs, Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsTrashBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, _, h⟩
  rw [← h]

theorem pcsFixedBlock_zfree (cs : ConstraintSystem (Fr p)) :
    ∀ s ∈ Generator.pcsFixedBlock cs, Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsFixedBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, b, ⟨_, _⟩, h⟩
  rw [← h]

theorem pcsPermutationCommonBlock_zfree (cs : ConstraintSystem (Fr p)) :
    ∀ s ∈ Generator.pcsPermutationCommonBlock cs,
      Generator.isPermutationZSource s = false := by
  intro s hs
  simp [Generator.pcsPermutationCommonBlock, Generator.isPermutationZSource] at hs ⊢
  rcases hs with ⟨a, _, h⟩
  rw [← h]

theorem pcsBlockList_eq_permZ (cs : ConstraintSystem (Fr p)) (nb dg : Nat) (lc : List Nat) :
    Generator.pcsBlockList cs nb dg lc =
      (Generator.pcsAdviceBlock cs ++ Generator.pcsCommittedInstanceBlock cs nb) ++
      Generator.permZBlock (Generator.pcsNumPermutationZs cs dg) ++
      (Generator.pcsLookupBlock cs dg lc ++ Generator.pcsTrashBlock cs ++
        Generator.pcsFixedBlock cs ++ Generator.pcsPermutationCommonBlock cs ++
        [PcsQuerySource.linearization]) := by
  simp [Generator.pcsBlockList, Generator.pcsBlocks, List.append_assoc]

theorem permZBlock_ztrue (k : Nat) :
    ∀ s ∈ Generator.permZBlock k, Generator.isPermutationZSource s = true := by
  intro s hs
  simp only [Generator.permZBlock, List.mem_flatten, List.mem_map] at hs
  obtain ⟨l, ⟨set, _, rfl⟩, hsl⟩ := hs
  by_cases h : set + 1 != k
  · simp [h] at hsl
    rcases hsl with rfl | rfl | rfl <;> rfl
  · simp [h] at hsl
    rcases hsl with rfl | rfl <;> rfl

theorem filter_append_of_zfree {pre mid post : List PcsQuerySource}
    (hpre : ∀ s ∈ pre, Generator.isPermutationZSource s = false)
    (hpost : ∀ s ∈ post, Generator.isPermutationZSource s = false) :
    (pre ++ mid ++ post).filter Generator.isPermutationZSource =
      mid.filter Generator.isPermutationZSource := by
  have hpre' : pre.filter Generator.isPermutationZSource = [] :=
    List.filter_eq_nil_iff.mpr (fun a ha => by
      have h := hpre a ha
      simp [h])
  have hpost' : post.filter Generator.isPermutationZSource = [] :=
    List.filter_eq_nil_iff.mpr (fun a ha => by
      have h := hpost a ha
      simp [h])
  rw [List.filter_append, List.filter_append, hpre', hpost']
  simp

theorem permZUpstream_filter (k : Nat) :
    (Generator.permZUpstream k).filter Generator.isPermutationZSource =
      Generator.permZUpstream k := by
  rw [List.filter_eq_self]
  intro s hs
  simp only [Generator.permZUpstream, List.mem_append, List.mem_flatten, List.mem_map] at hs
  rcases hs with ⟨l, ⟨set, _, rfl⟩, hsl⟩ | ⟨l, ⟨set, _, rfl⟩, hsl⟩
  · simp at hsl
    rcases hsl with rfl | rfl <;> rfl
  · simp at hsl
    rcases hsl with rfl
    rfl

theorem upstreamSources_zslice
    (meta_ : ConstraintSystemMeta) (data : Data) (generatorOrder : List Query)
    (pre block post : List PcsQuerySource) (zPositions : List Nat) (k : Nat)
    (hsrc : meta_.protocol.pcsQueries = pre ++ block ++ post)
    (hzdef : zPositions = List.filterMap
      (fun x => if Generator.isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range meta_.protocol.pcsQueries.length).zip meta_.protocol.pcsQueries))
    (hzNonempty : zPositions ≠ [])
    (hpre : ∀ s ∈ pre, Generator.isPermutationZSource s = false)
    (hblock : ∀ s ∈ block, Generator.isPermutationZSource s = true)
    (hpost : ∀ s ∈ post, Generator.isPermutationZSource s = false)
    (hblockUp : Generator.upstreamBlock block = Generator.permZUpstream k)
    (hblockLen : (Generator.upstreamBlock block).length = block.length)
    (h : Generator.assertPermutationQueryOrderIsUpstreamEquivalent meta_ data generatorOrder = .ok ()) :
    ∃ (upstreamSources : List PcsQuerySource) (upstreamQueries : List Query)
      (generatorSets upstreamSets : IntermediateSets),
      upstreamSources = pre ++ Generator.permZUpstream k ++ post ∧
      upstreamSources.filter Generator.isPermutationZSource = Generator.permZUpstream k ∧
      upstreamSources.mapM (fun source => Generator.queryFromPlan source meta_ data) =
        .ok upstreamQueries ∧
      Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
      Generator.constructIntermediateSetsImpl upstreamQueries = .ok upstreamSets ∧
      generatorSets.pointSets = upstreamSets.pointSets := by
  obtain ⟨zSources, upstreamSources, upstreamQueries, generatorSets, upstreamSets,
    hzSources, hupstream, hupQ, hgen, hupSet, hpoint⟩ :=
    assertPermutationQueryOrderIsUpstreamEquivalent_parts meta_ data generatorOrder
      zPositions hzdef hzNonempty h
  rw [hsrc] at hzdef hzSources hupstream
  have hzpos : zPositions = (List.range block.length).map (fun j => pre.length + j) := by
    rw [hzdef]
    exact filterMap_zip_range_append_block Generator.isPermutationZSource pre block post
      hpre hblock hpost
  have hzSources' : zSources = block := by
    rw [hzpos] at hzSources
    have hmap := mapM_get_consecutive (α := PcsQuerySource)
      "proofs/solidity-verifier/src/lowering/kzg/mod.rs:158" pre block post
    exact Except.ok.inj (hzSources.symm.trans hmap)
  have hupstream' : upstreamSources = pre ++ Generator.upstreamBlock block ++ post := by
    rw [hzSources', hzpos, ← hblockLen] at hupstream
    have hmap := foldlM_set_consecutive
      "proofs/solidity-verifier/src/lowering/kzg/mod.rs:190" pre block
      (Generator.upstreamBlock block) post hblockLen
    exact Except.ok.inj (hupstream.symm.trans hmap)
  refine ⟨upstreamSources, upstreamQueries, generatorSets, upstreamSets,
    ?_, ?_, hupQ, hgen, hupSet, hpoint⟩
  · rw [hupstream', hblockUp]
  · rw [hupstream', hblockUp]
    rw [filter_append_of_zfree hpre hpost, permZUpstream_filter]

theorem append_zfree {a b : List PcsQuerySource}
    (ha : ∀ s ∈ a, Generator.isPermutationZSource s = false)
    (hb : ∀ s ∈ b, Generator.isPermutationZSource s = false) :
    ∀ s ∈ a ++ b, Generator.isPermutationZSource s = false := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact ha s h
  · exact hb s h

theorem singleton_linearization_zfree :
    ∀ s ∈ [PcsQuerySource.linearization], Generator.isPermutationZSource s = false := by
  intro s hs
  simp only [List.mem_singleton] at hs
  subst hs
  rfl

/-- The permutationZ block is nonempty whenever its set count is positive. The
    first set alone contributes its `cur` and `next` openings. -/
theorem permZBlock_length_pos {k : Nat} (hk : 0 < k) :
    0 < (Generator.permZBlock k).length := by
  have hmem : PcsQuerySource.permutationZ 0 PermutationZEval.cur ∈ Generator.permZBlock k := by
    unfold Generator.permZBlock
    rw [List.mem_flatten]
    refine ⟨[PcsQuerySource.permutationZ 0 PermutationZEval.cur,
             PcsQuerySource.permutationZ 0 PermutationZEval.next]
              ++ (if 0 + 1 != k then
                    [PcsQuerySource.permutationZ 0 PermutationZEval.last] else []),
            ?_, by simp⟩
    rw [List.mem_map]
    exact ⟨0, List.mem_range.mpr hk, rfl⟩
  exact List.length_pos_of_ne_nil (by intro h; rw [h] at hmem; cases hmem)

/-- The z-position list `assertPermutationQueryOrderIsUpstreamEquivalent` computes for
    the literal `pcsBlockList`: the indices of its permutationZ block. -/
def pcsZPositions (cs : ConstraintSystem (Fr p)) (nb dg : Nat) (lc : List Nat) : List Nat :=
  List.filterMap (fun x => if Generator.isPermutationZSource x.2 then some x.1 else none)
    ((List.range (Generator.pcsBlockList cs nb dg lc).length).zip
      (Generator.pcsBlockList cs nb dg lc))

/-- Nonempty permutationZ count gives a nonempty z-position list at `pcsBlockList`.
    This is the nonemptiness A5's `upstreamSources_filter_pcsBlockList` needs, derived
    from the block structure rather than passed in. -/
theorem pcsZPositions_nonempty (cs : ConstraintSystem (Fr p)) (nb dg : Nat) (lc : List Nat)
    (hk : 0 < Generator.pcsNumPermutationZs cs dg) :
    pcsZPositions (p := p) cs nb dg lc ≠ [] := by
  unfold pcsZPositions
  rw [pcsBlockList_eq_permZ]
  have hpre : ∀ s ∈ (Generator.pcsAdviceBlock cs ++
      Generator.pcsCommittedInstanceBlock cs nb),
      Generator.isPermutationZSource s = false := by
    apply append_zfree
    · exact pcsAdviceBlock_zfree cs
    · exact pcsCommittedInstanceBlock_zfree cs nb
  have hblock : ∀ s ∈ Generator.permZBlock (Generator.pcsNumPermutationZs cs dg),
      Generator.isPermutationZSource s = true := permZBlock_ztrue _
  have hpost : ∀ s ∈ (Generator.pcsLookupBlock cs dg lc ++
      Generator.pcsTrashBlock cs ++ Generator.pcsFixedBlock cs ++
      Generator.pcsPermutationCommonBlock cs ++ [PcsQuerySource.linearization]),
      Generator.isPermutationZSource s = false := by
    apply append_zfree
    · apply append_zfree
      · apply append_zfree
        · apply append_zfree
          · exact pcsLookupBlock_zfree cs dg lc
          · exact pcsTrashBlock_zfree cs
        · exact pcsFixedBlock_zfree cs
      · exact pcsPermutationCommonBlock_zfree cs
    · exact singleton_linearization_zfree
  rw [filterMap_zip_range_append_block Generator.isPermutationZSource
    (Generator.pcsAdviceBlock cs ++ Generator.pcsCommittedInstanceBlock cs nb)
    (Generator.permZBlock (Generator.pcsNumPermutationZs cs dg))
    (Generator.pcsLookupBlock cs dg lc ++ Generator.pcsTrashBlock cs ++
      Generator.pcsFixedBlock cs ++ Generator.pcsPermutationCommonBlock cs ++
      [PcsQuerySource.linearization]) hpre hblock hpost]
  have hlen : 0 < (Generator.permZBlock (Generator.pcsNumPermutationZs cs dg)).length :=
    permZBlock_length_pos hk
  intro h
  rw [List.map_eq_nil_iff, List.range_eq_nil] at h
  omega

theorem upstreamSources_filter_pcsBlockList
    (meta_ : ConstraintSystemMeta) (data : Data) (generatorOrder : List Query)
    (cs : ConstraintSystem (Fr p)) (nb dg : Nat) (lc : List Nat)
    (zPositions : List Nat)
    (hzdef : zPositions = List.filterMap
      (fun x => if Generator.isPermutationZSource x.2 = true then some x.1 else none)
      ((List.range meta_.protocol.pcsQueries.length).zip meta_.protocol.pcsQueries))
    (hzNonempty : zPositions ≠ [])
    (hPcs : meta_.protocol.pcsQueries = Generator.pcsBlockList cs nb dg lc)
    (h : Generator.assertPermutationQueryOrderIsUpstreamEquivalent meta_ data generatorOrder = .ok ()) :
    ∃ (upstreamSources : List PcsQuerySource) (upstreamQueries : List Query)
      (generatorSets upstreamSets : IntermediateSets),
      upstreamSources = (Generator.pcsAdviceBlock cs ++
          Generator.pcsCommittedInstanceBlock cs nb) ++
        Generator.permZUpstream (Generator.pcsNumPermutationZs cs dg) ++
        (Generator.pcsLookupBlock cs dg lc ++ Generator.pcsTrashBlock cs ++
          Generator.pcsFixedBlock cs ++ Generator.pcsPermutationCommonBlock cs ++
          [PcsQuerySource.linearization]) ∧
      upstreamSources.filter Generator.isPermutationZSource =
        Generator.permZUpstream (Generator.pcsNumPermutationZs cs dg) ∧
      upstreamSources.mapM (fun source => Generator.queryFromPlan source meta_ data) =
        .ok upstreamQueries ∧
      Generator.constructIntermediateSetsImpl generatorOrder = .ok generatorSets ∧
      Generator.constructIntermediateSetsImpl upstreamQueries = .ok upstreamSets ∧
      generatorSets.pointSets = upstreamSets.pointSets := by
  let pre := Generator.pcsAdviceBlock cs ++ Generator.pcsCommittedInstanceBlock cs nb
  let block := Generator.permZBlock (Generator.pcsNumPermutationZs cs dg)
  let post := Generator.pcsLookupBlock cs dg lc ++ Generator.pcsTrashBlock cs ++
    Generator.pcsFixedBlock cs ++ Generator.pcsPermutationCommonBlock cs ++
    [PcsQuerySource.linearization]
  have hsrc : meta_.protocol.pcsQueries = pre ++ block ++ post := by
    rw [hPcs, pcsBlockList_eq_permZ]
  have hpre : ∀ s ∈ pre, Generator.isPermutationZSource s = false := by
    apply append_zfree
    · exact pcsAdviceBlock_zfree cs
    · exact pcsCommittedInstanceBlock_zfree cs nb
  have hpost : ∀ s ∈ post, Generator.isPermutationZSource s = false := by
    apply append_zfree
    · apply append_zfree
      · apply append_zfree
        · apply append_zfree
          · exact pcsLookupBlock_zfree cs dg lc
          · exact pcsTrashBlock_zfree cs
        · exact pcsFixedBlock_zfree cs
      · exact pcsPermutationCommonBlock_zfree cs
    · exact singleton_linearization_zfree
  have hblock : ∀ s ∈ block, Generator.isPermutationZSource s = true :=
    permZBlock_ztrue (Generator.pcsNumPermutationZs cs dg)
  have hblockUp : Generator.upstreamBlock block =
      Generator.permZUpstream (Generator.pcsNumPermutationZs cs dg) :=
    Generator.upstreamBlock_permZBlock (Generator.pcsNumPermutationZs cs dg)
  have hblockLen : (Generator.upstreamBlock block).length = block.length := by
    rw [hblockUp]
    exact permZUpstream_length (Generator.pcsNumPermutationZs cs dg)
  exact upstreamSources_zslice meta_ data generatorOrder pre block post zPositions
    (Generator.pcsNumPermutationZs cs dg) hsrc hzdef hzNonempty hpre hblock hpost
    hblockUp hblockLen h

end Midfall.LoweringV3
