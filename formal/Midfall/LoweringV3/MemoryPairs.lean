/-
  Midfall.LoweringV3.MemoryPairs

  **WP LAYOUT.** The named-pair layout lemmas A3's `vk_blockSim` clean half is missing.
  A3's report and `LoweringV3/VkRow.lean` §4 name the gap: `Inv R .vk` pins the g1_identity
  window to zero and the vk window to the payload, and the block's `extcodecopy` writes the
  second over the first wherever they meet, so the clean arm needs, for EVERY render,

    ptrAddr R.pv.memory.g1IdentityMptr + 128 <= ptrAddr R.pv.memory.vkMptr OR
    ptrAddr R.pv.memory.vkMptr + R.pv.vk.len <= ptrAddr R.pv.memory.g1IdentityMptr.

  THREE FINDINGS, all proved below, and the first one corrects the brief.

  (1) THE BRIEF'S PREMISE IS FALSE AS STATED. `hR.supported.layout` is
      `R.plan.memory.map.WellFormed AND R.plan.memory.validate.isOk = true`
      (`LoweringV2/Statements.lean:216`). BOTH are predicates of the layout's MAP (and of
      seven fixed low-memory Nat fields, the scalar-inv anchor and four PCS capacities -
      `Generator/Layout.lean:1023-1077`). Neither mentions `g1IdentityMptr` or `vkMptr` as
      RECORD FIELDS: `VerifierMemoryLayout` is a flat 70-field record (`Layout.lean:903-972`)
      and `map : MemoryMap` is one of them. A layout whose map is well-formed and whose two
      Ptr fields overlap exists: `layout_windows_not_tied_to_the_map` exhibits one, so no
      amount of `WellFormed` machinery can deliver the inequality on its own. The fact is
      nevertheless TRUE of every `ValidV3` render - because `generated` pins `R.plan` to what
      `generateAll` returns, and `generateAll` builds the layout with `VerifierMemoryLayout.new`
      (`LoweringV2/Generated.lean:135 -> Generator/PlanNew.lean:746 -> Generator/Vk.lean:1025
      -> Generator/PlanNew.lean:653`). So the generic source is the CONSTRUCTION, not the
      well-formedness Bool. Section 4 proves the inequality from the construction, outright.

  (2) THE REGION-LIST EXTRACTION A3 NAMED IS NOT JUST MISSING, IT IS NOT COMPUTABLE HERE.
      `map.region "g1_identity"` on a GENERIC `VerifierMemoryLayout.new` output does not
      whnf: `(VerifierMemoryLayout.new meta_ vk vkMptr config).map.region "vk_payload"`
      = some ... hits the deterministic-whnf heartbeat limit at the default 200 000, because
      the 30-allocation arena chain has to be rebuilt as a 30-element symbolic list before
      `find?` can walk it. (Field projections are cheap - `Prod`/structure arguments are
      thunks - which is why §4 works and this does not.) The extraction is therefore stated
      and proved AT THE LIST LEVEL, generic in the list and in the two regions (§2-§3): that
      is the lemma the tree was missing, it costs nothing, and it is what any future
      `map.region`-facing layout card needs. It is NOT a `WellFormed` redesign: nothing here
      changes a Bool, a clause or a frozen statement.

  (3) 128 IS `g1Bytes`. `Layout.lean:88,98`: `g1WordsCount = 4`, `wordBytes = 0x20`, so
      `g1Bytes = 128` - the constant in `vkPins.disjoint` is the g1_identity region's own
      registered length (`LayoutMemory.lean:236-238`), which is why §3 keeps it as a
      parameter `128 <= g1Len` and not as a magic number.

  (4) THE BLOCKER IS CLEARED, AND NOT BY `WellFormed`. §8 inverts the `generated` clause -
      `generateAll`'s four binds (`ok_bind_iff`, the pattern `Widening.model_of_generated`
      already uses) and `newFromVk`'s ten - and lands `vkPins_disjoint_of_generated`:
      `GeneratedBy R` ALONE gives the disjunction, for every render, sorry-free, with
      [propext, Classical.choice, Quot.sound] and `#cone_sorries` 0. So `vk_blockSim`'s
      clean half no longer waits on a layout card: `hdisj` is a theorem of `hR.generated`.
      §9 then rides the SAME peel through generateVerifierFromPlan (seven binds, not the
      "one unfolding" PoseidonValid.lean:850 promises) and lands the OTHER two row premises:
      numInstances (ART:280) and expectedVkCodehash (ART:524). So all THREE premises of
      vk_blockRow - hcode, hnum, hdisj - are theorems of hR.generated (+ hR.inputs.1 and
      hR.supported.separateVk, which ValidV3 already carries). row_premises_of_generated.
      The two region-membership facts the orchestrator asked for are NOT what unblocks it -
      they are unreachable (§(2)) and unnecessary (§8).

  WHAT IS NOT HERE, AND WHY. No hypothesis was added to `ValidV3`, to a row, to a pin bundle
  or to the root; `Consts.vkPins` is untouched. No fixture appears in any statement (D-P71),
  no `native_decide` appears in this file, and nothing here is imported by `lowering_correct`'s
  cone. §5 is the W12 falsifier: a pair of permanent regions that DO overlap, with every
  hypothesis of §3 except `WellFormed` satisfied, and `wellFormedBool = false` proved.
-/
import Midfall.Generator.LayoutMemory
import Midfall.Lowering.Inv
import Midfall.LoweringV2.Generated
import Midfall.LoweringV2.Consts
import Midfall.Generator.PlanNew
import Midfall.LoweringV3.Statements
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.MemoryPairs

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.Generator.PlanNew Midfall.Generator.QuotientEvaluator

/-! ## 1. THE REGION ALGEBRA: `overlaps` AS A PROP, AND WHAT REFUSING IT GIVES -/

/-- `n != 0` as a Bool and `n ≠ 0` as a Prop, both ways. `MemoryRegion.overlaps` is written
    with the BEq form (`Layout.lean:481-482`), so every extraction has to cross this bridge. -/
theorem ne_true_iff (n : Nat) : ((n != 0) = true) ↔ n ≠ 0 := by cases n <;> simp

theorem ne_true (n : Nat) (h : n ≠ 0) : (n != 0) = true := by cases n <;> simp_all

/-- The four conditions that make two regions meet. -/
theorem ov_true {a b : MemoryRegion} (ha : a.len ≠ 0) (hb : b.len ≠ 0)
    (h1 : a.start < b.end) (h2 : b.start < a.end) : a.overlaps b = true := by
  simp only [MemoryRegion.overlaps, ne_true _ ha, ne_true _ hb]
  simp [h1, h2]

theorem overlaps_iff (a b : MemoryRegion) :
    (a.overlaps b = true) ↔ (a.len ≠ 0 ∧ b.len ≠ 0 ∧ a.start < b.end ∧ b.start < a.end) := by
  refine ⟨?_, fun h => ov_true h.1 h.2.1 h.2.2.1 h.2.2.2⟩
  intro h
  simp only [MemoryRegion.overlaps] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, hd⟩ := h
  rw [Bool.and_eq_true] at h1
  obtain ⟨h2, hc⟩ := h1
  rw [Bool.and_eq_true] at h2
  obtain ⟨ha, hb⟩ := h2
  exact ⟨(ne_true_iff a.len).mp ha, (ne_true_iff b.len).mp hb,
    of_decide_eq_true hc, of_decide_eq_true hd⟩

/-- `overlaps` is symmetric. Needed because `memoryRegionsPairwiseDisjoint` walks the STRICT
    UPPER TRIANGLE (`Layout.lean:1089-1094`), so the pair is tested in registration order and
    the caller's order is arbitrary. -/
theorem overlaps_symm (a b : MemoryRegion) : a.overlaps b = b.overlaps a := by
  rw [Bool.eq_iff_iff]
  rw [overlaps_iff a b, overlaps_iff b a]
  refine ⟨fun h => ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩, fun h => ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩⟩

/-- **THE SEPARATION FORM.** Two regions that do not overlap and are both non-empty are
    ordered: one ends where the other begins, or the other way round. This is the shape
    `vkPins.disjoint` wants - a disjunction of two Nat inequalities, not a Bool. -/
theorem not_overlaps_sep {a b : MemoryRegion} (h : a.overlaps b = false)
    (ha : a.len ≠ 0) (hb : b.len ≠ 0) :
    a.start + a.len ≤ b.start ∨ b.start + b.len ≤ a.start := by
  by_cases hc : a.start < b.end
  · left
    by_contra hlt
    have h2 : a.overlaps b = true := ov_true ha hb hc (Nat.lt_of_not_le hlt)
    exact absurd h2 (by simp_all)
  · right
    have : b.end ≤ a.start := Nat.le_of_not_lt hc
    simpa [MemoryRegion.end] using this

/-- A region a find? returns is a member of the list it searched. List.mem_find? is not a
    core name at this toolchain, so it is proved here - four lines, and it is the only thing
    the extraction needs about find? beyond what it returns. -/
theorem mem_find {α : Type} {p : α → Bool} {l : List α} {y : α}
    (h : l.find? p = some y) : y ∈ l := by
  induction l with
  | nil => cases h
  | cons x rest ih =>
      cases hx : p x with
      | false =>
          simp only [List.find?, hx] at h
          exact List.mem_cons_of_mem _ (ih h)
      | true =>
          simp only [List.find?, hx] at h
          have hyx : y = x := (Option.some.inj h).symm
          rw [hyx]
          exact by simp
/-- Two permanent lifetimes always intersect (`Layout.lean:452-455`), in either order. -/
theorem li_perm_both (lhs rhs : MemoryLifetime) (hl : lhs = MemoryLifetime.permanent)
    (hr : rhs = MemoryLifetime.permanent) :
    memoryLifetimeIntersects lhs rhs = true := by
  subst hl; subst hr; rfl

/-! ## 2. THE NAMED-PAIR EXTRACTION FROM THE DISJOINTNESS BOOL, GENERIC IN THE LIST -/

/-- **THE MISSING LEMMA.** `memoryRegionsPairwiseDisjoint` is a Bool over the whole region
    list; nothing in the tree could name two regions inside it. Here they are named the way
    the tree already names regions - by the `find?` lookup `MemoryMap.region` performs
    (`Layout.lean:500-501`, and the same handle `transcriptRegionOk` uses at
    `Statements.lean:828`). Generic in the list, in both regions and in their addresses: no
    plan, no render, no fixture, no computation over an arena chain. -/
theorem memoryRegionsPairwiseDisjoint_perm_pair
    {regions : List MemoryRegion} {lhs rhs : MemoryRegion}
    (h : memoryRegionsPairwiseDisjoint regions = true)
    (hl : regions.find? (fun r => r.name == lhs.name) = some lhs)
    (hr : regions.find? (fun r => r.name == rhs.name) = some rhs)
    (hne : lhs.name ≠ rhs.name)
    (hpl : lhs.lifetime = MemoryLifetime.permanent)
    (hpr : rhs.lifetime = MemoryLifetime.permanent) :
    lhs.overlaps rhs = false := by
  induction regions with
  | nil => cases hl
  | cons x rest ih =>
      have h1 := h
      simp only [memoryRegionsPairwiseDisjoint, Bool.and_eq_true] at h1
      obtain ⟨hall, hrest⟩ := h1
      rw [List.all_eq_true] at hall
      cases hx : x.name == lhs.name with
      | true =>
        -- x IS lhs: the traversal tested the pair at the head, in the caller's order.
        simp only [List.find?, hx] at hl
        have hlhs : x = lhs := Option.some.inj hl
        cases hx2 : x.name == rhs.name with
        | true =>
          exact (hne ((congrArg MemoryRegion.name hlhs).symm.trans
            ((beq_iff_eq (a := x.name) (b := rhs.name)).mp hx2))).elim
        | false =>
          simp only [List.find?, hx2] at hr
          have hthis := hall rhs (mem_find hr)
          rw [hlhs] at hthis
          rw [hpl, hpr, li_perm_both MemoryLifetime.permanent MemoryLifetime.permanent rfl rfl] at hthis
          simpa using hthis
      | false =>
        -- x is not lhs, so lhs is in the tail.
        simp only [List.find?, hx] at hl
        cases hx2 : x.name == rhs.name with
        | true =>
          -- x IS rhs: the traversal tested the pair as (rhs, lhs), the other order.
          simp only [List.find?, hx2] at hr
          have hxr : x = rhs := Option.some.inj hr
          have hthis := hall lhs (mem_find hl)
          rw [hxr] at hthis
          rw [hpr, hpl, li_perm_both MemoryLifetime.permanent MemoryLifetime.permanent rfl rfl] at hthis
          have hs : rhs.overlaps lhs = false := by simpa using hthis
          rw [overlaps_symm lhs rhs]
          exact hs
        | false =>
          simp only [List.find?, hx2] at hr
          exact ih hrest hl hr
/-! ## 3. THE SAME THROUGH `MemoryMap.WellFormed`, AND FOR THE NAMED PAIR -/

/-- The third conjunct of the Bool, isolated (`Layout.lean:1114-1119`). -/
theorem wellFormed_regions_disjoint {map : MemoryMap} (h : map.WellFormed) :
    memoryRegionsPairwiseDisjoint map.regions = true := by
  have h2 : map.wellFormedBool = true := h
  rw [MemoryMap.wellFormedBool] at h2
  rw [Bool.and_eq_true] at h2
  exact h2.2

/-- **THE NAMED PAIR, FROM `WellFormed`.** This is the WP's accept shape: a lemma that
    extracts a named pair of permanent regions out of the `WellFormed` Bool. -/
theorem wellFormed_pair_disjoint {map : MemoryMap} {lhs rhs : MemoryRegion}
    (h : map.WellFormed)
    (hl : map.region lhs.name = some lhs)
    (hr : map.region rhs.name = some rhs)
    (hne : lhs.name ≠ rhs.name)
    (hpl : lhs.lifetime = MemoryLifetime.permanent)
    (hpr : rhs.lifetime = MemoryLifetime.permanent) :
    lhs.overlaps rhs = false :=
  memoryRegionsPairwiseDisjoint_perm_pair (wellFormed_regions_disjoint h) hl hr hne hpl hpr

/-- **THE `vk_payload` / `g1_identity` PAIR AS A DISJUNCTION OF ADDRESSES.** The two windows
    `Inv .vk` pins, in the exact shape `vkPins.disjoint` asks for. -/
theorem vkPayload_g1Identity_disjoint {map : MemoryMap}
    {vkAddr vkLen g1Addr g1Len : Nat}
    (h : map.WellFormed)
    (hv : map.region "vk_payload" =
      some (memoryRegionNew "vk_payload" vkAddr vkLen MemoryLifetime.permanent))
    (hg : map.region "g1_identity" =
      some (memoryRegionNew "g1_identity" g1Addr g1Len MemoryLifetime.permanent))
    (hv0 : vkLen ≠ 0) (hg0 : g1Len ≠ 0) (hg128 : 128 ≤ g1Len) :
    g1Addr + 128 ≤ vkAddr ∨ vkAddr + vkLen ≤ g1Addr := by
  have hne : ("vk_payload" : String) ≠ "g1_identity" := by decide
  have hd := wellFormed_pair_disjoint (lhs := memoryRegionNew "vk_payload" vkAddr vkLen
      MemoryLifetime.permanent) (rhs := memoryRegionNew "g1_identity" g1Addr g1Len
      MemoryLifetime.permanent) h hv hg hne rfl rfl
  obtain hsep := not_overlaps_sep hd hv0 hg0
  simp only [memoryRegionNew] at hsep
  rcases hsep with h | h
  · exact Or.inr h
  · exact Or.inl (Nat.le_trans (Nat.add_le_add_left hg128 g1Addr) h)


/-! ## 4. THE ARENA CHAIN: WHAT `WellFormed` CANNOT SAY AND THE CONSTRUCTION CAN -/

/-- `new` registers the VK payload at exactly the pointer it is handed (`LayoutMemory.lean:190-192`,
    `allocFixed` returns its `start` unchanged), so the record field and the region agree. -/
theorem new_vkMptr (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr = vkMptr := rfl

/-- `ptrAddr` of a pointer the planner built from a `Nat` is that `Nat`
    (`Models.lean:506-528`, `Layout.lean:1008-1013`, `Inv.lean:385`). -/
theorem ptrAddr_valueFromNat (n : Nat) : ptrAddr (ptrMemory (valueFromNat n)) = n := by
  show Value.asUsizeNat (valueFromNat n) = n
  show Value.asUsizeNat (Value.integer (n : Int)) = n
  simp only [Value.asUsizeNat]
  split
  · omega
  · omega

/-- **THE REGION LIST IS NOT NEEDED.** `g1_identity` is allocated inside the theta window
    (`LayoutMemory.lean:236-238`), the theta window after the challenge slots (`:199-202`), the
    challenge slots after the VK payload (`:196-198`), and the payload at `ptrAddr vkMptr`. Four
    `allocAfter`/`allocFixed` steps, and the chain projects by `rfl` because a structure field is
    a thunk: the other twenty-six allocations are never evaluated. This is the equation the
    `map.region` route could not afford (§(2) of the header) and it says the same thing. -/
theorem new_g1IdentityMptr (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).g1IdentityMptr =
      ptrMemory (valueFromNat
        (alignUp (alignUp (ptrAddr vkMptr + vk.len) wordBytes
            + meta_.challengeIndices.length * wordBytes) wordBytes
          + ThetaWindowLayout.compatibility.g1IdentityWord * wordBytes)) := rfl

/-- `alignUp` does not move a value down. -/
theorem alignUp_le (n m : Nat) (h : 0 < m) : n ≤ alignUp n m := by
  have h1 : (n + m - 1) / m * m ≤ n + m - 1 := Nat.div_mul_le_self _ _
  have h2 : (n + m - 1) % m < m := Nat.mod_lt _ h
  have h3 : (n + m - 1) / m * m + (n + m - 1) % m = n + m - 1 := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  simp only [alignUp]
  omega

theorem wordBytes_pos : 0 < wordBytes := by decide

/-- **THE INEQUALITY, FOR EVERY ARGUMENT OF THE CONSTRUCTOR.** No `WellFormed`, no render, no
    fixture: the payload window ends before the g1_identity window begins, for every meta, every
    payload, every base pointer and every configuration. This is the second disjunct of
    `vkPins.disjoint` and it is unconditional. -/
theorem new_g1Identity_after_vk (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    ptrAddr vkMptr + vk.len ≤
      ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).g1IdentityMptr := by
  rw [new_g1IdentityMptr, ptrAddr_valueFromNat]
  set A := ptrAddr vkMptr + vk.len
  set B := alignUp A wordBytes
  set C := alignUp (B + meta_.challengeIndices.length * wordBytes) wordBytes
  have h1 : A ≤ B := alignUp_le A wordBytes wordBytes_pos
  have h2 : B ≤ C := Nat.le_trans (Nat.le_add_right B _) (alignUp_le _ _ wordBytes_pos)
  exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_add_right C _)

/-- The same fact in the disjunctive shape `vkPins.disjoint` has. -/
theorem new_pair_disjoint (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).g1IdentityMptr + 128 ≤
        ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr ∨
    ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr + vk.len ≤
        ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).g1IdentityMptr :=
  Or.inr (by rw [new_vkMptr]; exact new_g1Identity_after_vk meta_ vk vkMptr config)

/-! ## 5. THE W12 FALSIFIER: A PAIR THAT OVERLAPS, AND THE LEMMA REFUSES IT -/

/-- Two permanent regions that DO meet: the payload window at 0x4000 for 0x1000 bytes, the
    g1_identity window at 0x4800 for 128 bytes - inside the first. Word-aligned, above the
    spill window, permanent: every clause of §3 except `WellFormed` holds of this map. -/
def falsVkRegion : MemoryRegion :=
  memoryRegionNew "vk_payload" 0x4000 0x1000 MemoryLifetime.permanent

def falsG1Region : MemoryRegion :=
  memoryRegionNew "g1_identity" 0x4800 128 MemoryLifetime.permanent

def falsMap : MemoryMap := { regions := [falsVkRegion, falsG1Region] }

/-- The pair meets. -/
theorem falsifier_regions_overlap : falsVkRegion.overlaps falsG1Region = true := by decide

/-- Every other hypothesis of §3 holds: both names resolve, both lengths are non-zero, the g1
    window is 128 bytes. -/
theorem falsifier_hypotheses :
    falsMap.region "vk_payload" = some falsVkRegion ∧
      falsMap.region "g1_identity" = some falsG1Region ∧
    falsVkRegion.len ≠ 0 ∧ falsG1Region.len ≠ 0 ∧ (128 ≤ falsG1Region.len) :=
  ⟨rfl, rfl, by decide, by decide, by decide⟩

/-- **THE FALSIFIER.** The map is NOT well-formed, so `wellFormed_pair_disjoint` refuses it - and
    the conclusion it would have given is false of it. -/
theorem falsifier_not_wellFormed : ¬ falsMap.WellFormed := by
  intro h
  have h1 : falsMap.wellFormedBool = true := h
  have h2 : falsMap.wellFormedBool = false := by decide
  have h3 : (true : Bool) = false := h1.symm.trans h2
  exact absurd h3 (by decide)

theorem falsifier_disjunction_false :
    ¬((0x4800 : Nat) + 128 ≤ 0x4000 ∨ 0x4000 + 0x1000 ≤ 0x4800) := by decide

/-- And the refusal is not an artefact of the two-region map: the pairwise Bool is exactly the
    conjunct that fails. -/
theorem falsifier_disjoint_false :
    memoryRegionsPairwiseDisjoint falsMap.regions = false := by decide

/-! ## 6. WHY `supported.layout` ALONE CANNOT BE THE SOURCE (finding (1) of the header) -/

/-- **THE MAP DOES NOT TIE THE RECORD FIELDS.** `VerifierMemoryLayout` is a flat record and
    `WellFormed` speaks only of its `map` field (`Layout.lean:903-972`, `:1114-1119`,
    `:1127`); `validate` reads seven fixed Nat pointers, the scalar-inv anchor and four PCS
    capacities (`:1023-1077`) and never `g1IdentityMptr`. So moving the g1_identity POINTER onto
    the VK window leaves every `WellFormed`-face fact of the layout exactly as it was and makes
    the two windows meet. `hR.supported.layout` therefore cannot be what makes
    `vkPins.disjoint` true. The fact is true of every `ValidV3` render for a different reason:
    `generated` pins the plan to `generateAll`, and `generateAll` builds the layout with
    `VerifierMemoryLayout.new` - which is what §4 proves. -/
theorem layout_windows_not_tied_to_the_map (L₀ : VerifierMemoryLayout) (vkLen : Nat)
    (h : L₀.map.WellFormed) (hne : vkLen ≠ 0) (L : VerifierMemoryLayout)
    (hL : L = { L₀ with g1IdentityMptr := L₀.vkMptr }) :
    L.map.WellFormed ∧
      ¬ (ptrAddr L.g1IdentityMptr + 128 ≤ ptrAddr L.vkMptr ∨
          ptrAddr L.vkMptr + vkLen ≤ ptrAddr L.g1IdentityMptr) := by
  subst hL
  refine ⟨h, fun hh => ?_⟩
  rcases hh with h1 | h2
  · dsimp only at h1
    omega
  · dsimp only at h2
    omega
/-! ## 7. THE RENDER FACE, STATED OF THE PLAN VIEW -/

/-- **THE SHAPE `vk_blockSim` NEEDS, ONE EQUATION FROM PROVED.** Given only that the plan view
    carries a layout the constructor built from the plan view’s own payload, the disjunction
    holds - unconditionally, in the second disjunct. Stated of `PlanView` rather than of a
    `Render` so it is generic in the render and in everything the render is built from, and so
    that it needs nothing from a frozen file. Nothing was added to `ValidV3`, to a row, to a pin
    bundle or to the root: the single hypothesis is the equation `generated` is the source of,
    and §8 records that it is the remaining gap. -/
theorem vkPins_disjoint_of_memory_new (pv : PlanView) (meta_ : ConstraintSystemMeta)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (h : pv.memory = VerifierMemoryLayout.new meta_ pv.vk vkMptr config) :
    ptrAddr pv.memory.g1IdentityMptr + 128 ≤ ptrAddr pv.memory.vkMptr ∨
      ptrAddr pv.memory.vkMptr + pv.vk.len ≤ ptrAddr pv.memory.g1IdentityMptr := by
  refine Or.inr ?_
  rw [h]
  simp only [new_vkMptr]
  exact new_g1Identity_after_vk meta_ pv.vk vkMptr config

/-! ## 8. WHAT REMAINS -/

/- The one equation between §7 and `vk_blockSim`’s clean half. It is a `generated`-clause
    inversion, not a layout fact: `generateAll` (`LoweringV2/Generated.lean:127-144`) binds
    `plan <- newFromVk ...`, `newFromVk` (`Generator/PlanNew.lean:722-776`) binds
    `memory <- memoryLayoutFor ...` twelve binds deep, `memoryLayoutFor` (`Generator/Vk.lean:1016-1025`)
    returns `env.newVerifierMemoryLayout meta_ vk vkMptr config′`, and `envOf`
    (`Generator/PlanNew.lean:651-660`) spells that field `VerifierMemoryLayout.new`. Four
    rewrites and a dozen `ok_bind_iff` steps (`LoweringV3/Widening.lean:771`, the pattern
    `model_of_generated` already uses) stand between `hR.generated` and this equation. It is the
    SAME inversion `numInst` needs, so it belongs to that card, not to a layout card. -/

/-! ## 8. THE GENERATED CLAUSE: THE EQUATION OF §7, PROVED -/

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

theorem match_ok_iff {α β γ : Type} (x : Except α β) (f : β → Except α γ) {η : γ} :
    (match x with
     | Except.error e => Except.error e
     | Except.ok y => f y) = Except.ok η ↔ ∃ y, x = Except.ok y ∧ f y = Except.ok η := by
  constructor
  . intro h
    cases x with
    | error e => cases h
    | ok y => exact ⟨y, rfl, h⟩
  . rintro ⟨y, rfl, hy⟩
    exact hy
theorem newFromVk_memory {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : newFromVk feat field cs rawMeta numInstances accEncoding payload = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig),
      plan.memory = VerifierMemoryLayout.new meta_ payload vkMptr config := by
  simp only [newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := (match_ok_iff _ _).mp h
  obtain ⟨proofLayout, _, h2⟩ := (match_ok_iff _ _).mp h1
  obtain ⟨qplan, _, h3⟩ := (match_ok_iff _ _).mp h2
  obtain ⟨build, _, h4⟩ := (match_ok_iff _ _).mp h3
  obtain ⟨nativeWords, _, h5⟩ := (match_ok_iff _ _).mp h4
  obtain ⟨pcsReq, _, h6⟩ := (match_ok_iff _ _).mp h5
  obtain ⟨accTerms, _, h7⟩ := (match_ok_iff _ _).mp h6
  obtain ⟨memory, hmem, h8⟩ := (match_ok_iff _ _).mp h7
  obtain ⟨opModel, _, h9⟩ := (match_ok_iff _ _).mp h8
  obtain ⟨trip, _, h10⟩ := (match_ok_iff _ _).mp h9
  have hex : ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig),
      memory = VerifierMemoryLayout.new meta_ payload vkMptr config := by
    simp only [memoryLayoutFor, Bind.bind, Except.bind, envOf] at hmem
    obtain ⟨t, _, hmem2⟩ := (match_ok_iff _ _).mp hmem
    exact ⟨q.2.1, q.1, _, (Except.ok.inj hmem2).symm⟩
  obtain ⟨meta_, vkMptr, config, he⟩ := hex
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨meta_, vkMptr, config, he⟩)

/-! ### The VK pointer's own shape, out of `metaDataForStableStaticLayout`

  `vk_hdr_word_read` needs `ptrAddr (Ptr.add vkMptr i) = ptrAddr vkMptr + 32 * i`, and that is
  false for a `Value.identifier` pointer (`asUsizeNat` maps every identifier to 0). The planner
  never stores one: `metaDataForStableStaticLayout` starts at `ptrMemory (valueFromNat start)` and
  every rebind is `ptrMemory (valueFromNat planned)`. The fold is only three iterations, and the
  invariant below carries the shape (and the link between the returned tuple's pointer and the
  fold state's pointer) through it. -/

/-- The fold state of `metaDataForStableStaticLayout`: `(result, current pointer)`. -/
abbrev MetaState :=
  Option (Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout) × Ptr

/-- The fold invariant: the current pointer is a `Nat`-built memory pointer, and whenever the
    result is already fixed its pointer is the current one. -/
def MetaShape (st : MetaState) : Prop :=
  (∃ n, st.2 = ptrMemory (valueFromNat n)) ∧
    (∀ r, st.1 = some r → r.1 = st.2)

theorem foldlM_metaShape {α : Type} {l : List Nat} {step : α → Nat → Except Fault α}
    {P : α → Prop} (hstep : ∀ a i b, step a i = .ok b → P a → P b) {a} (ha : P a) :
    ∀ b, l.foldlM step a = .ok b → P b := by
  induction l generalizing a with
  | nil =>
      intro b h
      simp only [List.foldlM_nil] at h
      cases h; exact ha
  | cons x xs ih =>
      intro b h
      simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
      split at h
      · cases h
      · rename_i a' ha'
        exact ih (hstep a x a' ha' ha) b h

/-- One iteration preserves `MetaShape`. -/
theorem metaStep_metaShape {Plan : Type} (feat : Features) (env : VkBuildEnv Plan)
    (meta_ : ConstraintSystemMeta) (numInstances : Nat) (vk : Halo2VerifyingKey)
    (st : MetaState) (i : Nat) (st' : MetaState)
    (h : (fun st (_ : Nat) => do
      if st.1.isSome then Except.ok st else do
        let vkMptr := st.2
        let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
        let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
        let cur ← Value.asUsize vkMptr.value
        if planned == cur then
          Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
        else
          Except.ok (none, ptrMemory (valueFromNat planned))) st i = .ok st') :
    MetaShape st → MetaShape st' := by
  intro hinv
  simp only at h
  by_cases hs : st.1.isSome
  · rw [ite_eq_left hs] at h
    cases h
    exact hinv
  · rw [ite_eq_right hs] at h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i md hmd
      split at h
      · cases h
      · rename_i planned hpl
        split at h
        · cases h
        · rename_i cur hcur
          split at h
          · have hb : st' = (some (st.2, md.1, md.2.1, md.2.2), st.2) :=
              (Except.ok.inj h).symm
            subst hb
            refine ⟨hinv.1, ?_⟩
            intro r hr
            have hrr : r = (st.2, md.1, md.2.1, md.2.2) := by
              simpa using hr.symm
            rw [hrr]
          · have hb : st' = (none, ptrMemory (valueFromNat planned)) :=
              (Except.ok.inj h).symm
            subst hb
            exact ⟨⟨planned, rfl⟩, by intro r hr; cases hr⟩

/-- `metaDataForStableStaticLayout` returns a `Nat`-built memory pointer. -/
theorem metaDataForStableStaticLayout_shape {Plan : Type} (feat : Features)
    (env : VkBuildEnv Plan) (meta_ : ConstraintSystemMeta) (numInstances : Nat)
    (vk : Halo2VerifyingKey) (r : Ptr × ConstraintSystemMeta × Data × VerifierMemoryLayout)
    (h : metaDataForStableStaticLayout feat env meta_ numInstances vk = .ok r) :
    ∃ n, r.1 = ptrMemory (valueFromNat n) := by
  unfold metaDataForStableStaticLayout at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i start hstart
    split at h
    · cases h
    · rename_i st' hst'
      have hinv := foldlM_metaShape (P := MetaShape)
        (step := (fun (st : MetaState) (_ : Nat) => do
          if st.1.isSome then Except.ok st else do
            let vkMptr := st.2
            let (metaOut, dat, memory) ← metaDataForVk feat env meta_ numInstances vk vkMptr
            let planned ← staticWorkingMemorySizeForMeta metaOut numInstances
            let cur ← Value.asUsize vkMptr.value
            if planned == cur then
              Except.ok (some (vkMptr, metaOut, dat, memory), vkMptr)
            else
              Except.ok (none, ptrMemory (valueFromNat planned))))
        (fun a i b hab ha => metaStep_metaShape feat env meta_ numInstances vk a i b hab ha)
        (a := (none, ptrMemory (valueFromNat start)))
        ⟨⟨start, rfl⟩, by intro r hr; cases hr⟩ st' hst'
      split at h
      · cases h
        obtain ⟨n, hn⟩ := hinv.1
        exact ⟨n, (hinv.2 _ (by assumption)).trans hn⟩
      · cases h

/-- The same for `newFromVk`: its plan's `vkMptr` is a `Nat`-built memory pointer. -/
theorem newFromVk_memory_ptr {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : newFromVk feat field cs rawMeta numInstances accEncoding payload = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig) (vkBase : Nat),
      vkMptr = ptrMemory (valueFromNat vkBase) ∧
        plan.memory = VerifierMemoryLayout.new meta_ payload vkMptr config := by
  simp only [newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, hq, h1⟩ := (match_ok_iff _ _).mp h
  obtain ⟨vkBase, hvk⟩ := metaDataForStableStaticLayout_shape feat (envOf field cs) rawMeta numInstances payload q hq
  obtain ⟨proofLayout, _, h2⟩ := (match_ok_iff _ _).mp h1
  obtain ⟨qplan, _, h3⟩ := (match_ok_iff _ _).mp h2
  obtain ⟨build, _, h4⟩ := (match_ok_iff _ _).mp h3
  obtain ⟨nativeWords, _, h5⟩ := (match_ok_iff _ _).mp h4
  obtain ⟨pcsReq, _, h6⟩ := (match_ok_iff _ _).mp h5
  obtain ⟨accTerms, _, h7⟩ := (match_ok_iff _ _).mp h6
  obtain ⟨memory, hmem, h8⟩ := (match_ok_iff _ _).mp h7
  obtain ⟨opModel, _, h9⟩ := (match_ok_iff _ _).mp h8
  obtain ⟨trip, _, h10⟩ := (match_ok_iff _ _).mp h9
  have hex : ∃ (meta_ : ConstraintSystemMeta) (config : VerifierMemoryLayoutConfig),
      memory = VerifierMemoryLayout.new meta_ payload q.1 config := by
    simp only [memoryLayoutFor, Bind.bind, Except.bind, envOf] at hmem
    obtain ⟨t, _, hmem2⟩ := (match_ok_iff _ _).mp hmem
    exact ⟨q.2.1, _, (Except.ok.inj hmem2).symm⟩
  obtain ⟨meta_, config, he⟩ := hex
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨meta_, q.1, config, vkBase, hvk, he⟩)

/-- STEP 1: the plan equation out of the generated clause. -/
theorem plan_of_generated {R : Render p G₁ G₂ Gₜ} (h : Midfall.LoweringV3.GeneratedBy R) :
    ∃ (rawMeta : ConstraintSystemMeta) (plan : LoweringPlan Unit Unit),
      ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = Except.ok rawMeta ∧
      newFromVk Features.solidity (frFieldCtx R.E.delta) R.vk.cs rawMeta
        R.cfg.numInstances R.cfg.accumulator R.plan.vk = Except.ok plan ∧ R.plan = plan := by
  obtain ⟨out, hg, hplan, hq, hm⟩ := h
  simp only [Midfall.LoweringV3.generated] at hg
  simp only [generateAll, Bind.bind] at hg
  obtain ⟨rawMeta, hraw, h1⟩ := (match_ok_iff _ _).mp hg
  obtain ⟨plan, hpl, h2⟩ := (match_ok_iff _ _).mp h1
  obtain ⟨_blocks, _, h3⟩ := (match_ok_iff _ _).mp h2
  obtain ⟨_model, _, h4⟩ := (match_ok_iff _ _).mp h3
  cases h5 : (Halo2Verifier.validateLayout _model) with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
    simp only [h5] at h4
    have hA : { plan := plan, qblocks := _blocks, model := _model } = out :=
      Except.ok.inj (show Except.ok { plan := plan, qblocks := _blocks, model := _model } =
        Except.ok out from h4)
    have hp : plan = R.plan := (congrArg GenOut.plan hA).trans hplan
    exact ⟨rawMeta, plan, hraw, hpl, hp.symm⟩

/-- THE RENDER FACE, UNCONDITIONAL. -/
theorem plan_memory_eq_new {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    ∃ (meta_ : ConstraintSystemMeta) (vkMptr : Ptr)
      (config : VerifierMemoryLayoutConfig),
      R.pv.memory = VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := plan_of_generated h
  obtain ⟨meta_, vkMptr, config, he⟩ :=
      newFromVk_memory Features.solidity (frFieldCtx R.E.delta) R.vk.cs rawMeta
        R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have hpv : R.pv.memory = R.plan.memory := rfl
  have hpvk : R.pv.vk = R.plan.vk := rfl
  exact ⟨meta_, vkMptr, config, by rw [hpv, hp, he, hpvk]⟩


/-- **THE VK POINTER IS A `Nat`-BUILT MEMORY POINTER, FROM `generated`.** This is what lets
    `VkClean.vk_hdr_word_read` turn `ptrAddr (Ptr.add vkMptr i)` into `ptrAddr vkMptr + 32 * i`;
    a `Value.identifier` pointer would fail that equation (`asUsizeNat` maps it to 0). -/
theorem vkMptr_shape_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    ∃ n : Nat, ptrValue R.pv.memory.vkMptr = Value.integer (n : Int) := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := plan_of_generated h
  obtain ⟨meta_, vkMptr, config, vkBase, hvk, he⟩ :=
    newFromVk_memory_ptr Features.solidity (frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  refine ⟨vkBase, ?_⟩
  have hmem : R.pv.memory = VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config := by
    have hpv : R.pv.memory = R.plan.memory := rfl
    have hpvk : R.pv.vk = R.plan.vk := rfl
    rw [hpv, hp, he, hpvk]
  rw [hmem, new_vkMptr, hvk]
  rfl

theorem vkPins_disjoint_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
      ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr := by
  obtain ⟨meta_, vkMptr, config, he⟩ := plan_memory_eq_new h
  exact Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_memory_new R.pv meta_ vkMptr config he



/-! ## 9. THE OTHER TWO RESIDUALS RIDE THE SAME MECHANISM -/

/-- PoseidonValid.lean:847 and :855 name residuals (a) numInst and (c) codehashArm as
    "one unfolding of generateVerifierFromPlan". They are seven bind inversions, not one, and
    they are here. gvfp_of_generated is the model-clause projection - the same fact
    Widening.model_of_generated proves, re-derived so this file stays self-contained - and
    generated_model_facts peels generateVerifierFromPlan once and projects BOTH the ART:280
    numInstances copy and the ART:524 expectedVkCodehash arm. With section 8 that is ALL THREE
    premises of vk_blockRow as theorems of generated: vkPins R needs no hypothesis ValidV3 does
    not already carry. -/

theorem gvfp_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = Except.ok R.model := by
  obtain ⟨out, hg, hplan, hq, hm⟩ := h
  simp only [Midfall.LoweringV3.generated, generateAll, Bind.bind] at hg
  obtain ⟨_rawMeta, _, h1⟩ := (match_ok_iff _ _).mp hg
  obtain ⟨plan, _, h2⟩ := (match_ok_iff _ _).mp h1
  obtain ⟨blocks, hblocks, h3⟩ := (match_ok_iff _ _).mp h2
  obtain ⟨model, hgen, h4⟩ := (match_ok_iff _ _).mp h3
  cases h5 : (Halo2Verifier.validateLayout model) with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
    simp only [h5] at h4
    have hA : { plan := plan, qblocks := blocks, model := model } = out :=
      Except.ok.inj (show Except.ok { plan := plan, qblocks := blocks, model := model } =
        Except.ok out from h4)
    have hb : blocks = R.qblocks := (congrArg GenOut.qblocks hA).trans hq
    have hm2 : model = R.model := (congrArg GenOut.model hA).trans hm
    have hp : plan = R.plan := (congrArg GenOut.plan hA).trans hplan
    rw [hp] at hgen
    rw [hm2] at hgen
    rw [hb] at hgen
    exact hgen

/-- THE TWO `generated`-clause projections, one peel. -/
theorem generated_model_facts {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    R.model.numInstances = R.inputs.numInstances ∧
      (R.flags.separate = true → vkCodehashArm R.model) := by
  have hg := gvfp_of_generated h
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  . cases hg
  . cases hg
  . obtain ⟨_a1, _, h1⟩ := (match_ok_iff _ _).mp hg
    obtain ⟨_a2, _, h2⟩ := (match_ok_iff _ _).mp h1
    obtain ⟨_a3, _, h3⟩ := (match_ok_iff _ _).mp h2
    obtain ⟨_a4, _, h4⟩ := (match_ok_iff _ _).mp h3
    obtain ⟨_a5, _, h5⟩ := (match_ok_iff _ _).mp h4
    obtain ⟨_a6, _, h6⟩ := (match_ok_iff _ _).mp h5
    obtain ⟨_a7, _, h7⟩ := (match_ok_iff _ _).mp h6
    have hrec := Except.ok.inj h7
    refine ⟨(congrArg (fun x => x.numInstances) hrec).symm, fun hsep => ?_⟩
    have hc := congrArg (fun x => x.expectedVkCodehash) hrec
    rw [hsep] at hc
    exact ⟨_, hc.symm⟩

/-- **THE MODEL'S HEADER SLOT TABLE IS THE TEMPLATE'S.** `expectedConsts` indexes the header
    offsets through `m.vkHeader`, while `PayloadAgrees` speaks of `vkHeaderTemplateSlotsDefault`;
    `generateVerifierFromPlan` sets `vkHeader := vkHeaderTemplateSlotsDefault` (ART:286), so the
    same seven-bind peel that gives `generated_model_facts` gives this equation. It is what lets the
    six VkLoading header cross-checks use the payload pins at the offsets the emitter wrote. -/
theorem vkHeader_default_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    R.model.vkHeader = vkHeaderTemplateSlotsDefault := by
  have hg := gvfp_of_generated h
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  . cases hg
  . cases hg
  . obtain ⟨_a1, _, h1⟩ := (match_ok_iff _ _).mp hg
    obtain ⟨_a2, _, h2⟩ := (match_ok_iff _ _).mp h1
    obtain ⟨_a3, _, h3⟩ := (match_ok_iff _ _).mp h2
    obtain ⟨_a4, _, h4⟩ := (match_ok_iff _ _).mp h3
    obtain ⟨_a5, _, h5⟩ := (match_ok_iff _ _).mp h4
    obtain ⟨_a6, _, h6⟩ := (match_ok_iff _ _).mp h5
    obtain ⟨_a7, _, h7⟩ := (match_ok_iff _ _).mp h6
    have hrec := Except.ok.inj h7
    exact (congrArg (fun x => x.vkHeader) hrec).symm

/-- The two row premises, at the render. -/
theorem vkPins_numInst_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R)
    (hi : R.inputs.numInstances = R.cfg.numInstances) :
    R.pv.numInstances = R.cfg.numInstances := by
  have h2 : R.pv.numInstances = R.model.numInstances := rfl
  exact h2.trans ((generated_model_facts h).1.trans hi)

theorem vkCodehashArm_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) (hsep : R.flags.separate = true) :
    vkCodehashArm R.model := (generated_model_facts h).2 hsep

/-- THE THREE ROW PREMISES, AS THEOREMS OF THE V3 CLAUSES. hR.generated, hR.inputs.1 and
    hR.supported.separateVk are all fields of ValidV3; nothing is added to it. -/
theorem row_premises_of_generated {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
    (R : Render p G₁ G₂ Gₜ) (h : Midfall.LoweringV3.GeneratedBy R)
    (hinputs : R.inputs.numInstances = R.cfg.numInstances)
    (hsep : R.flags.separate = true) :
    (R.pv.numInstances = R.cfg.numInstances) ∧
      Midfall.LoweringV2.vkCodehashArm R.model ∧
      (ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
        ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr) :=
  ⟨vkPins_numInst_of_generated h hinputs,
    (generated_model_facts h).2 hsep,
    vkPins_disjoint_of_generated h⟩
/-! ## 10. PG-VKMEMORYFIT: ARE 'fit1' AND 'fit2' THEOREMS OF 'generated'? -/

/-- **THE REDUCTION - BOTH FITS ARE EXACTLY A WORD-FIT BOUND, AND NOTHING WEAKER WILL DO.** The
    semantics writes the copy at '(BitVec.ofNat 256 m).toNat', which is 'm % 2 ^ 256'
    ('BitVec.toNat_ofNat'); 'Inv' reads at the 'Nat' 'm'. The two agree exactly when 'm' fits a
    word. So 'fit1' is not a bit-vector lemma a cleverer peel might supply: it IS the statement
    'ptrAddr R.pv.memory.vkMptr < 2 ^ 256', and 'fit2' IS 'R.pv.vk.len < 2 ^ 256'. For
    'm >= 2 ^ 256' the destination is a DIFFERENT address - that is
    'VkClean.wrap_breaks_payload_clause'. -/
theorem ofNat_toNat_iff_lt (n : Nat) :
    (BitVec.ofNat 256 n).toNat = n ↔ n < 2 ^ 256 := by
  rw [BitVec.toNat_ofNat]
  constructor
  · intro h
    have h2 : n % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt n (by decide : 0 < 2 ^ 256)
    rw [h] at h2
    exact h2
  · intro h
    exact Nat.mod_eq_of_lt h

/-- The two goals of PG-VKMEMORYFIT at the render, each equivalent to its bound. These are the two
    implications the reassembly needs once a bound exists: 'fit1_of_bound' and 'fit2_of_bound' turn
    a '< 2 ^ 256' hypothesis into exactly the two equations the walk stops on. -/
theorem fit1_of_bound {R : Render p G₁ G₂ Gₜ}
    (h : ptrAddr R.pv.memory.vkMptr < 2 ^ 256) :
    (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat = ptrAddr R.pv.memory.vkMptr :=
  (ofNat_toNat_iff_lt _).mpr h

theorem fit2_of_bound {R : Render p G₁ G₂ Gₜ} (h : R.pv.vk.len < 2 ^ 256) :
    (BitVec.ofNat 256 R.pv.vk.len).toNat = R.pv.vk.len := (ofNat_toNat_iff_lt _).mpr h

/-- **THE VKFIT PAYOFF (D-QVM1, signed 2026-11-21).** The two equations the walk stops on, now
    THEOREMS of `ValidV3` - the address-fit conjunct `programFits` supplies both bounds. Before the
    decision they were conditional on a hypothesis that no clause carried. -/
theorem fit1_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat = ptrAddr R.pv.memory.vkMptr :=
  fit1_of_bound (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (programFit_of_valid hR).1)

theorem fit2_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    (BitVec.ofNat 256 R.pv.vk.len).toNat = R.pv.vk.len :=
  fit2_of_bound (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (programFit_of_valid hR).1)

/-- **ROUTE 1 (THE ARENA CHAIN) - REFUTED.** The brief's hypothesis was that
    'VerifierMemoryLayout.new' allocates a 30-allocation chain over concrete 'Nat' offsets, so
    every emitted 'ptrAddr' is a sum of small literals and is below '2 ^ 256' by arithmetic. That
    is true of the TWENTY-NINE pointers the arena DERIVES and false of 'vkMptr', which 'new'
    copies straight out of its own argument ('new_vkMptr', proved 'rfl' in §4) - and 'ptrAddr'
    is surjective onto 'Nat' ('ptrAddr_valueFromNat': 'ptrAddr (ptrMemory (valueFromNat n)) = n'
    for EVERY 'n'). So for every bound there is a legal argument to 'new' whose VK address
    exceeds it. The constructor equation 'plan_memory_eq_new' is the WHOLE of what 'generated'
    says about the memory, and it bounds the address by nothing. This is the same species of
    finding as 'layout_windows_not_tied_to_the_map': the construction pins the RELATIONS between
    pointers, not their magnitude. -/
theorem new_vkMptr_image_unbounded (B : Nat) (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (config : VerifierMemoryLayoutConfig) :
    B ≤ ptrAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).vkMptr := by
  rw [new_vkMptr, ptrAddr_valueFromNat]

/-- So the 'generated' face admits a wrapping destination outright: for every meta, payload and
    configuration there is a legal 'vkMptr' argument for which 'fit1' is FALSE. -/
theorem generated_face_allows_fit1_to_fail (meta_ : ConstraintSystemMeta)
    (vk : Halo2VerifyingKey) (config : VerifierMemoryLayoutConfig) :
    ¬ (BitVec.ofNat 256
         (ptrAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat (2 ^ 256)))
           config).vkMptr)).toNat =
      ptrAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat (2 ^ 256))) config).vkMptr := by
  rw [new_vkMptr, ptrAddr_valueFromNat, ofNat_toNat_iff_lt]
  exact Nat.lt_irrefl _

/-- **WHY 'transcriptMptr_lt' WORKS AND NO 'vkMptr_lt' CAN.** 'PrefixV3.transcriptMptr_lt'
    (PrefixV3.lean:475-495) is the ONE place in the tree that bounds a memory pointer from above by
    '2 ^ 256', and it is the template the brief should be measured against: 'validate's
    'fixedLowMemory' loop (Layout.lean:1026-1035) pins SEVEN pointers to literals -
    'constructorSmokeScratch', 'transcript', 'pcsPairingScratch', 'verifierReturn', 'quotientReturn',
    'accumulatorPairingBatch', 'finalPairingScratch' - and the constructor emits them as the same
    literals, by 'rfl': the first equation below is that fact. 'vkMptr' is the EIGHTH pointer and is
    deliberately NOT pinned: it is the output of the reservation loop at VK:535-544, the second
    equation below is that fact, and 'validate's only other use of it - 'expectedScalarInv' - is a
    tautology on a 'new' output because 'new' sets 'scalarInvScratchMptr := vkStart -
    modexpScratchBytes' from the SAME 'vkStart' it registers the payload at
    (LayoutMemory.lean:190-194). So the one route in the tree that bounds a layout pointer from
    above cannot reach 'vkMptr', and 'supported.layout' is silent about its magnitude. -/
theorem new_transcriptMptr_eq (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).transcriptMptr = transcriptBufferStart := rfl

theorem new_vkMptr_eq_arg (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr = vkMptr := rfl

/-- **ROUTE 3 (THE PAYLOAD LENGTH) - REFUTED.** 'Halo2VerifyingKey.len' is
    'constants.length * 32 + (fixedComms.length + permutationComms.length) * 128'
    ('Models.lean:461-462'): three 'List.length's, and a 'List' carries no size bound -
    'List.replicate n' is a total function into the type for every 'n'. OBJ.4's
    'payloadLen'/'vkLen' route runs the OTHER way: it proves 'runtimeBytes.size = vk.len + 1' FROM
    'constsCoherent', an equation between two unbounded 'Nat's, not a bound on either. Appending
    to the constant table raises 'len' by 32 bytes per word ('extendVk_len'), and the ONE payload
    condition the generator's ok-path enforces cannot see the growth: 'vkCarriesBuild_extend' proves
    'vkCarriesBuild' is INVARIANT under 'extendVk' whenever the two quotient slices end inside the
    original prefix. So no clause of 'ValidV3' and no gate on the generated path bounds 'vk.len'. -/
def extendVk (vk : Halo2VerifyingKey) (xs : List (String × Word256)) : Halo2VerifyingKey :=
  { vk with constants := vk.constants ++ xs }

theorem extendVk_len (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).len = vk.len + 32 * xs.length := by
  show (vk.constants ++ xs).length * 32 + (vk.fixedComms.length + vk.permutationComms.length) * 128 =
    (vk.constants.length * 32 + (vk.fixedComms.length + vk.permutationComms.length) * 128)
      + 32 * xs.length
  rw [List.length_append]
  ring

theorem vkLen_unbounded (B : Nat) (vk : Halo2VerifyingKey) :
    B ≤ (extendVk vk (List.replicate B (("", 0)))).len := by
  rw [extendVk_len, List.length_replicate]
  omega

/-- A payload whose length is at least '2 ^ 256': one extra constant word per unit of the bound. -/
def hugeVk (vk : Halo2VerifyingKey) : Halo2VerifyingKey :=
  extendVk vk (List.replicate (2 ^ 256) (("", 0)))

theorem hugeVk_len_ge (vk : Halo2VerifyingKey) : 2 ^ 256 ≤ (hugeVk vk).len :=
  vkLen_unbounded (2 ^ 256) vk

/-- And 'fit2' fails of the padded payload: the length crosses the word boundary. -/
theorem fit2_can_fail (vk : Halo2VerifyingKey) :
    ¬ (BitVec.ofNat 256 (hugeVk vk).len).toNat = (hugeVk vk).len := by
  rw [ofNat_toNat_iff_lt]
  intro h
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (hugeVk_len_ge vk))

/-- **THE GATE DOES NOT SEE THE GROWTH.** 'vkCarriesBuild' (PlanNew.lean:680-689) is the ONE payload
    condition the generator's ok-path enforces: 'newFromVk' refuses a payload that fails it
    (PlanNew.lean:773, the VK:457 panic). It reads two slices of the constant table,
    '(constants.map Prod.snd).drop o |>.take n', and a slice that ENDS inside the original prefix is
    unchanged by whatever is appended after it. So the gate is invariant under 'extendVk' while
    'len' grows by 32 bytes per word: 'vk.len' is bounded by nothing the generator enforces. -/
theorem extendVk_constants (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).constants = vk.constants ++ xs := rfl

theorem extendVk_qc (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).quotientConstOffsetWords = vk.quotientConstOffsetWords := rfl

theorem extendVk_qp (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).quotientProgramOffsetWords = vk.quotientProgramOffsetWords := rfl

theorem extendVk_qcw (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).quotientConstWords = vk.quotientConstWords := rfl

theorem extendVk_qpw (vk : Halo2VerifyingKey) (xs : List (String × Word256)) :
    (extendVk vk xs).quotientProgramWords = vk.quotientProgramWords := rfl

/-- A slice of an append that ends inside the first list is a slice of the first list. -/
theorem slice_extend {α : Type} (l l' : List α) (o n : Nat) (h : o + n ≤ l.length) :
    ((l ++ l').drop o).take n = (l.drop o).take n := by
  have hle : o ≤ l.length := Nat.le_trans (Nat.le_add_right o n) h
  have hnt : n ≤ (l.drop o).length := by
    rw [List.length_drop]
    omega
  rw [List.drop_append_of_le_length hle, List.take_append_of_le_length hnt]

theorem vkCarriesBuild_extend (vk : Halo2VerifyingKey) (build : QuotientProgramBuild)
    (xs : List (String × Word256))
    (h1 : vk.quotientConstOffsetWords.getD 0 + vk.quotientConstWords ≤ vk.constants.length)
    (h2 : vk.quotientProgramOffsetWords.getD 0 + vk.quotientProgramWords ≤ vk.constants.length) :
    vkCarriesBuild (extendVk vk xs) build = vkCarriesBuild vk build := by
  cases hco : vk.quotientConstOffsetWords with
  | none => simp only [vkCarriesBuild, extendVk_qc, hco]
  | some qc =>
    cases hpo : vk.quotientProgramOffsetWords with
    | none => simp only [vkCarriesBuild, extendVk_qc, extendVk_qp, hco, hpo]
    | some qp =>
        simp only [vkCarriesBuild, extendVk_constants, extendVk_qc, extendVk_qp, extendVk_qcw,
          extendVk_qpw, hco, hpo, List.map_append]
        rw [slice_extend (vk.constants.map Prod.snd) (xs.map Prod.snd) qc vk.quotientConstWords
          (by simpa [hco] using h1),
          slice_extend (vk.constants.map Prod.snd) (xs.map Prod.snd) qp vk.quotientProgramWords
          (by simpa [hpo] using h2)]

/-- **THE ANSWER TO THE CARD.** 'fit1' and 'fit2' are NOT theorems of the 'generated' clause.
    Route 1 is refuted by 'new_vkMptr_image_unbounded' (the arena chain does not bound the pointer
    it is handed) and route 3 by 'vkLen_unbounded' (a 'List.length' is an arbitrary 'Nat'); route 2
    was refuted outright by 'layout_windows_not_tied_to_the_map'. The tree DOES know how to bound a
    layout pointer from above - 'PrefixV3.transcriptMptr_lt' does it from 'validate's fixedLowMemory
    loop - and the reason it cannot do it for 'vkMptr' is now proved: 'new_transcriptMptr_eq' (the
    constructor emits the literal for the transcript pointer) against 'new_vkMptr_eq_arg' (it emits
    the ARGUMENT for the VK pointer). 'vk_mptr' is the eighth pointer, the reservation loop's output,
    and 'validate' pins it only against 'scalarInvScratchMptr', which 'new' builds from the same
    'vkStart' (LayoutMemory.lean:190-194) - a tautology, not a bound. The only '2 ^ 256' conjunct in
    the clause table is 'cdBoundB', on 'proofLayout.proofEnd + 32 + 32 * numInstances'
    ('Statements.lean:2057-2058', projected as 'cdBound_of_valid'), and it speaks of the CALLDATA
    layout, not of 'memory.vkMptr'. So PG-VKMEMORYFIT is a genuine class-width gap: closing the vk
    row needs a NEW bound, and the only place to put it is a 'programOkCore' conjunct (STATUS.md
    option 2) - a signed decision and one of W15's two remaining re-hashes, not this card. Option 3,
    stating the row with the bound as a hypothesis, stays refused on the record; 'fit1_of_bound' and
    'fit2_of_bound' are the two equations the reassembly needs the moment option 2 is signed. -/
theorem fit1_iff_bound {R : Render p G₁ G₂ Gₜ} :
    ((BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat = ptrAddr R.pv.memory.vkMptr) ↔
      ptrAddr R.pv.memory.vkMptr < 2 ^ 256 := ofNat_toNat_iff_lt _

theorem fit2_iff_bound {R : Render p G₁ G₂ Gₜ} :
    ((BitVec.ofNat 256 R.pv.vk.len).toNat = R.pv.vk.len) ↔ R.pv.vk.len < 2 ^ 256 :=
  ofNat_toNat_iff_lt _


/-! ## 11. THE QVM WINDOWS: IS THE SPILL SLOT DISJOINT FROM THE CONST TABLE? (DISJNT)

  SPILL recorded ('QuotientSpill.lean' §6) that 'PG_spillArmTriple' is not dischargeable as published
  because nothing keeps the spill slot at 'q_sp' disjoint from the const word the arm reads next, and
  named the reason: 'quotientProgramFits' ('Statements.lean:3225') bounds every region BELOW
  '2 ^ 256' and says NOTHING about disjointness - 'the same gap MemoryPairs section 1 found for the vk
  windows'. THIS CARD REPEATS THE §1/§8 VERDICT FOR THE QVM PAIRS, AND IT IS THE SAME VERDICT: the gap
  is real FOR THE FIT CLAUSE and closed BY THE CONSTRUCTION.

  THREE FINDINGS.

  (1) THE FIT CLAUSE REALLY DOES NOT ORDER THE WINDOWS. 'fitsB_does_not_order_windows' exhibits a
      program that satisfies all seven clauses of 'quotientProgramFits' - COMPUTED, 'decide' - whose
      const window sits ON TOP of its stack window. So no reassembly of 'programFits' can ever give
      the disjunction, and a card that tried would be proving false.

  (2) BUT 'generated' DOES ORDER THEM, AND FOR EVERY RENDER, UNCONDITIONALLY. The const table is not
      a free-floating pointer: 'quotientTemplateProgram' ('PlanNew.lean:596,602') sets
      'constMptr := pn (vkMptr.add constOff)' - i.e. INSIDE the VK payload window, at the offset the
      payload itself declares - and 'stackMptr := memory.quotientStackMptr'. And the arena chain of
      'VerifierMemoryLayout.new' allocates 'quotient_stack' AFTER 'vk_payload' with nothing able to
      reorder them: 'vk_payload' at 'vkStart' ('LayoutMemory.lean:191'), 'challenge_slots'
      'allocAfter' it, the theta block 'allocAfter' that, 'decoded_evals' inside theta,
      'decompressed_commitments' 'allocAfter' those, 'selector_accumulators' 'allocAfter' those, and
      the quotient state and stack from ONE scratch allocator rooted above all of them
      (':287-293'). 'new_quotientStackMptr_eq' is that chain as a 'rfl' equation - the same trick as
      §4's 'new_g1IdentityMptr', and it costs nothing because a structure field is a thunk - and
      'new_quotientStack_after_vk' reads the ordering off it: 'ptrAddr vkMptr + vk.len ≤
      quotientStackMptr', for EVERY meta, payload, base pointer and configuration, no hypothesis.

  (3) THE CONST WINDOW ENDS INSIDE THE PAYLOAD WINDOW, so the two facts compose.
      'vkCarriesBuild' ('PlanNew.lean:680') is the ONE gate that sees the payload's quotient sections,
      and 'constSection_in_payload' reads off it that 'quotientConstOffsetWords +
      quotientConstWords ≤ constants.length' - the reservation cannot start inside the comms tail.
      With the generator's own 'build.consts.length ≤ vk.quotientConstWords' ('PlanNew.lean:587') and
      'guards.constMax = build.consts.length - 1' ('LoweringPlan.lean:379'), the const window
      '[constMptr, constMptr + 32 * (constMax + 1))' ends at or before 'vkMptr + 32 *
      constants.length ≤ vkMptr + vk.len', hence BEFORE 'stackMptr'. That is
      'qvmWindows_disjoint_of_construction': the FIRST disjunct of the ordering, for every render the
      generator can produce.

  ONE NON-DECISION, NAMED AND NOT ADDED. The argument needs '1 ≤ vk.quotientConstWords'. It is not a
  clause of anything and it is not a theorem of 'generated': a payload that reserves ZERO const words
  forces 'build.consts = []' through 'vkCarriesBuild' and then leaves 'quotientConstOffsetWords'
  completely unconstrained, so the (empty) const window could be declared anywhere, including on the
  stack. That is a degenerate payload - no const table at all - not a second instance of the VKFIT
  class-width gap: unlike 'fit1'/'fit2' there is no unbounded quantity here to bound, only an offset
  that stops being pinned once its section is empty. 'PG_qvmWindowsOrdered' below is the Prop; it is
  NOT added to 'ValidV3', to a row, to a bundle or to the root (RULES), and the arm-level
  'PG_spillSlotDisjoint' ('QuotientSpill.lean:1321') is the same inequality at the 'BitVec' face - the
  step from here to there is the arm's own 'b ≤ constMax' PRE plus the no-wrap half of the fit clause,
  which is SPILL's to take because it owns the arms.

  WHAT REMAINS BETWEEN §11 AND A ROW. 'qvmWindows_disjoint_of_construction' is stated from the six
  equations the constructor supplies, exactly as §7 was stated from the layout equation before §8
  proved it. The inversion is longer here than it was for 'vkPins': 'generated' gives
  'R.plan = newFromVk ... = .ok plan' (§8, already proved) and 'R.model = generateVerifierFromPlan
  ... R.plan = .ok R.model' (§9, already proved), and between them sit 'plan.quotient = some q'
  ('PlanNew.lean:759'), 'q.program' (':754'), 'LoweringPlan.quotientRendering' and
  'intoTemplateParts' ('Artifacts.lean:488,536'). It is bind inversion, not a missing axiom.
-/

/-- One arena step: `x` ends before the aligned window that starts `y` bytes past it. -/
theorem le_up_add (x y : Nat) : x ≤ alignUp (x + y) wordBytes :=
  Nat.le_trans (Nat.le_add_right x y) (alignUp_le (x + y) wordBytes wordBytes_pos)

/-- The same step where one window is preceded by TWO lengths inside the alignment. -/
theorem le_up_add2 (x y z : Nat) : x ≤ alignUp (x + y + z) wordBytes :=
  Nat.le_trans
    (Nat.le_trans (Nat.le_add_right x y) (Nat.le_add_right (x + y) z))
    (alignUp_le (x + y + z) wordBytes wordBytes_pos)

/-- The six-step chain of §11(2) stated on the raw `alignUp` nest, so the projection is whnf'd ONCE. -/
theorem raw_le (a b c d e f g : Nat) :
    a ≤ alignUp
        (alignUp
          (alignUp
            (alignUp
              (alignUp (alignUp a wordBytes + b) wordBytes + c + d)
              wordBytes + e)
            wordBytes + f)
          wordBytes + g)
        wordBytes := by
  refine Nat.le_trans ?_ (le_up_add _ _)
  refine Nat.le_trans ?_ (le_up_add _ _)
  refine Nat.le_trans ?_ (le_up_add _ _)
  refine Nat.le_trans ?_ (le_up_add2 _ _ _)
  refine Nat.le_trans ?_ (le_up_add _ _)
  exact alignUp_le _ _ wordBytes_pos

/-- **THE ARENA CHAIN AS AN EQUATION.** `quotient_stack` is six allocations above the payload:
     challenge slots, the theta block, the decoded evals, the commitment run, the selector
     accumulators, the quotient state. `rfl`, because a structure field is a thunk and the other
     twenty-three of the thirty allocations are never evaluated (§(2) of the header). -/
theorem new_quotientStackMptr_eq (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    (VerifierMemoryLayout.new meta_ vk vkMptr config).quotientStackMptr =
      alignUp
        (alignUp
          (alignUp
            (alignUp
              (alignUp (alignUp (ptrAddr vkMptr + vk.len) wordBytes
                + meta_.challengeIndices.length * wordBytes)
                wordBytes + ThetaWindowLayout.compatibility.reversedEvalsWord * wordBytes
                  + meta_.numEvals * wordBytes)
              wordBytes + commitmentG1Count meta_ * g1Bytes)
            wordBytes + meta_.numSimpleSelectors * wordBytes)
          wordBytes + config.quotientStateWords * wordBytes)
        wordBytes := rfl

/-- **THE STACK WINDOW IS ABOVE THE PAYLOAD WINDOW, FOR EVERY CONSTRUCTOR ARGUMENT.** No render, no
     `generated`, no hypothesis: the emitted code's operand stack can never overlap the VK payload
     the const table and the program live in. -/
theorem new_quotientStack_after_vk (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    ptrAddr vkMptr + vk.len ≤
      (VerifierMemoryLayout.new meta_ vk vkMptr config).quotientStackMptr := by
  rw [new_quotientStackMptr_eq]
  exact raw_le (ptrAddr vkMptr + vk.len) (meta_.challengeIndices.length * wordBytes)
    (ThetaWindowLayout.compatibility.reversedEvalsWord * wordBytes)
    (meta_.numEvals * wordBytes) (commitmentG1Count meta_ * g1Bytes)
    (meta_.numSimpleSelectors * wordBytes) (config.quotientStateWords * wordBytes)

/-- `Ptr.add` on a pointer the planner built from a `Nat` is `wordBytes` times the word count
     (`Value.add`, ENC:652-664) read back through `pn`. -/
theorem pn_add_valueFromNat (n q : Nat) :
    pn ((ptrMemory (valueFromNat n)).add q) = n + q * wordBytes := by
  show Value.asUsizeNat ((ptrMemory (valueFromNat n)).add q).value = n + q * wordBytes
  show Value.asUsizeNat (Value.add (valueFromNat n) q) = n + q * wordBytes
  show Value.asUsizeNat (Value.integer ((n : Int) + (q : Int) * (wordBytes : Int))) =
    n + q * wordBytes
  simp only [Value.asUsizeNat]
  split <;> omega

/-- **THE CONST RESERVATION LIES INSIDE THE PAYLOAD WORDS.** `vkCarriesBuild` compares
     `(words.drop qc).take quotientConstWords` with a list whose length is exactly
     `quotientConstWords` (the zero fill of `PlanNew.lean:686`, available because
     `build.consts.length ≤ quotientConstWords` was checked at `:587`), so the take must be full
     and the reservation cannot run past the payload. -/
theorem constSection_in_payload (vk : Halo2VerifyingKey) (build : QuotientProgramBuild)
    (qc qp : Nat) (hco : vk.quotientConstOffsetWords = some qc)
    (hpo : vk.quotientProgramOffsetWords = some qp)
    (hfit : build.consts.length ≤ vk.quotientConstWords)
    (hne : 1 ≤ vk.quotientConstWords)
    (hcar : vkCarriesBuild vk build = true) :
    qc + vk.quotientConstWords ≤ vk.constants.length := by
  have h1 : vkCarriesBuild vk build = true := hcar
  rw [vkCarriesBuild, hco, hpo] at h1
  dsimp only at h1
  rw [Bool.and_eq_true] at h1
  have hc := Iff.mp beq_iff_eq h1.1
  have := congrArg List.length hc
  simp only [List.length_drop, List.length_take, List.length_append, List.length_replicate,
    List.length_map] at this
  have hsub : build.consts.length + (vk.quotientConstWords - build.consts.length)
      = vk.quotientConstWords := by omega
  rw [hsub] at this
  by_cases h : vk.quotientConstWords ≤ vk.constants.length - qc
  · omega
  · have h2 : min vk.quotientConstWords (vk.constants.length - qc)
        = vk.constants.length - qc := Nat.min_eq_right (Nat.le_of_not_le h)
    omega

/-- **THE ORDERING, FROM THE CONSTRUCTION.** The six equations are what `quotientTemplateProgram`
     and `memoryLayoutFor` supply for the render's own program (§(3) of the header and 'PlanNew.lean
     :596, :602, :592'); 'qvmWindows_disjoint_of_valid' is this lemma with those equations discharged
     through `generated`, and the discharge is bind inversion, not a new axiom. -/
theorem qvmWindows_disjoint_of_construction {memory : VerifierMemoryLayout}
    {meta_ : ConstraintSystemMeta} {vk : Halo2VerifyingKey} {vkMptr : Ptr}
    {config : VerifierMemoryLayoutConfig} {build : QuotientProgramBuild}
    {program : QuotientProgram} (vkBase qcOff qp : Nat)
    (hvk : vkMptr = ptrMemory (valueFromNat vkBase))
    (hmem : memory = VerifierMemoryLayout.new meta_ vk vkMptr config)
    (hfit : build.consts.length ≤ vk.quotientConstWords)
    (hne : 1 ≤ vk.quotientConstWords)
    (hco : vk.quotientConstOffsetWords = some qcOff)
    (hpo : vk.quotientProgramOffsetWords = some qp)
    (hcar : vkCarriesBuild vk build = true)
    (hcm : program.constMptr = pn (vkMptr.add qcOff))
    (hsm : program.stackMptr = memory.quotientStackMptr)
    (hcmx : program.guards.constMax = build.consts.length - 1) :
    program.constMptr + 32 * (program.guards.constMax + 1) ≤ program.stackMptr := by
  have hlen : ptrAddr vkMptr + vk.len ≤ memory.quotientStackMptr := by
    rw [hmem]; exact new_quotientStack_after_vk meta_ vk vkMptr config
  have hsec := constSection_in_payload vk build qcOff qp hco hpo hfit hne hcar
  have hw : wordBytes = 32 := rfl
  have hcm' : program.constMptr = vkBase + qcOff * 32 := by
    rw [hcm, hvk, pn_add_valueFromNat, hw]
  have hbase : ptrAddr vkMptr = vkBase := by rw [hvk]; exact ptrAddr_valueFromNat vkBase
  have h32 : 32 * (program.guards.constMax + 1) ≤ 32 * vk.quotientConstWords := by
    rw [hcmx]
    refine Nat.mul_le_mul_left 32 ?_
    rcases Nat.eq_zero_or_pos (build.consts.length) with hz | hz
    · rw [hz]; omega
    · omega
  have hlen' : 32 * vk.constants.length ≤ vk.len := by
    show 32 * vk.constants.length ≤
      vk.constants.length * 32 + (vk.fixedComms.length + vk.permutationComms.length) * 128
    omega
  have hkey : vkBase + qcOff * 32 + 32 * (program.guards.constMax + 1)
      ≤ ptrAddr vkMptr + vk.len := by
    omega
  rw [hsm, hcm']
  exact Nat.le_trans hkey hlen

/-- **THE RENDER FACE, FROM 'generated' ALONE - NO NEW HYPOTHESIS.** The two windows that CONTAIN
     the QVM's const table and its operand stack are ordered for every `ValidV3` render, by §8's
     already-proved layout equation and §11's arena chain. This is the first disjointness theorem of
     `ValidV3` itself that the spill gap needed: what is left is not a missing axiom but the bind
     inversion that names the program's own two pointers inside these windows. -/
theorem payload_below_quotientStack_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) :
    ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ R.pv.memory.quotientStackMptr := by
  obtain ⟨meta_, vkMptr, config, he⟩ := plan_memory_eq_new h
  rw [he, new_vkMptr]
  exact new_quotientStack_after_vk meta_ R.pv.vk vkMptr config

/-- The same at a whole `ValidV3`: the clause that was already there, read as an ordering. -/
theorem payload_below_quotientStack_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ R.pv.memory.quotientStackMptr :=
  payload_below_quotientStack_of_generated hR.generated

/-- **THE PROP, NAMED - NOT ADDED ANYWHERE.** The ordering as the arms would want it. It is a theorem
     of the construction (§11(2)-(3)); what it is NOT is a theorem of `quotientProgramFits`. -/
def PG_qvmWindowsOrdered (program : QuotientProgram) : Prop :=
  program.constMptr + 32 * (program.guards.constMax + 1) ≤ program.stackMptr

/-- **FINDING (1), COMPUTED.** A program that satisfies every clause of `quotientProgramFits` and
     whose const window sits ON TOP of its stack window: the const table occupies `[0x100, 0x180)`
     and the stack base is `0x120`, so the spill at `q_sp = 0x120` overwrites const word 1. The
     seven fit clauses are discharged by `decide`; the ordering is refuted by `decide`. -/
def fitsFalsifier : QuotientProgram :=
  { len := 16, opUsage := quotientVmOpcodeUsageDefault, memUsage := quotientVmMemUsageDefault,
    constMptr := 0x100, evalNumerMptr := 0x200, traceIdMptr := 0x220,
    selectorPowerMptr := 0x240, selectorMaxPower := 0, selectorTailUpdates := [],
    stackMptr := 0x120, programMptr := 0x300,
    guards := { constMax := 3, numSelectorBuckets := 1, stackLast := 0x1ff } }

theorem fitsFalsifier_fits : quotientProgramFits fitsFalsifier := by
  simp only [quotientProgramFits]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fitsFalsifier_not_ordered : ¬ PG_qvmWindowsOrdered fitsFalsifier := by
  show ¬ (fitsFalsifier.constMptr + 32 * (fitsFalsifier.guards.constMax + 1) ≤
    fitsFalsifier.stackMptr)
  decide

/-- The same at the arm's own 'BitVec' face: const word 1 and the spill slot at `q_sp` overlap, so
     'PG_spillSlotDisjoint' is FALSE of this fit-satisfying program. Computed. -/
theorem fitsFalsifier_spillOverlaps :
    ¬ ((BitVec.ofNat 256 0x100 + ((BitVec.ofNat 256 1) <<< 5)).toNat + 32 ≤
          (BitVec.ofNat 256 0x120).toNat ∨
        (BitVec.ofNat 256 0x120).toNat + 32 ≤ (BitVec.ofNat 256 0x100 + ((BitVec.ofNat 256 1) <<< 5)).toNat) := by
  decide

theorem fitsFalsifier_not_construction :
    ¬ (fitsFalsifier.constMptr + 32 * (fitsFalsifier.guards.constMax + 1) ≤
        fitsFalsifier.stackMptr) := by
  decide


/-! ## 12. THE BIND INVERSION: THE PROGRAM'S OWN POINTERS, AT THE RENDER FACE (BINDINV)

  DISJNT closed section 11 one step short and said exactly which step: 'qvmWindows_disjoint_of_construction'
  orders the two windows of an ABSTRACT 'program' whose pointers are handed to it as equations
  ('hcm', 'hsm'). THIS SECTION LANDS THE STEP FROM THERE TO THE PROGRAM THE GENERATOR BUILT.

  (1) 'newFromVk_windows' - the same ten-bind peel section 8 already performs for the LAYOUT, run to
      the ELEVENTH bind ('quotientTemplateProgram', PlanNew.lean:754-755). It lands every equation
      section 11 asked to be handed: 'plan.quotient = some q' (PlanNew.lean:754-759),
      'q.program.constMptr = pn (vkMptr.add constOff)' (':596'), 'q.program.stackMptr =
      memory.quotientStackMptr' (':602'), 'q.build.consts.length <= vk.quotientConstWords' (':587',
      the 'unless' that did NOT fire), 'vkCarriesBuild vk q.build = true' (':774', the last 'unless'
      before 'pure plan'), and 'q.program.guards.constMax = q.build.consts.length - 1' - the last
      through 'quotientVmGuards' (LoweringPlan.lean:379, 'constMax := model.numConsts - 1') composed
      with 'quotientOperandModel' (':441-449', whose second argument IS 'build.consts.length').
      Three one-function inversions ('quotientVmGuards_ok_constMax',
      'quotientOperandModel_ok_numConsts', 'quotientTemplateProgram_windows') do the case analysis.

  (2) 'qvmWindows_disjoint_of_ptrs' - section 11's ordering with the 'vkMptr = ptrMemory
      (valueFromNat _)' HYPOTHESIS REMOVED. It is not needed: 'asUsizeNat_add_le' proves
      'pn (p.add q) <= ptrAddr p + q * wordBytes' for EVERY pointer, integer-valued or symbolic, and
      the ordering only ever needs '<='. 'qvmWindows_disjoint_of_generated' then composes it with
      section 8's layout equation at 'generated'.

  (3) 'spillSlotDisjoint_of_ordered' crosses to the 'BitVec' face 'PG_spillSlotDisjoint'
      ('QuotientSpill.lean:1321') is stated on, using EXACTLY the three facts DISJNT named: the
      ordering, the arm's own 'b <= constMax' PRE, and the no-wrap conjuncts of 'quotientProgramFits'
      ('Statements.lean:3225', clauses 2 and 3+4). The conclusion is 'PG_spillSlotDisjoint' unfolded;
      its '_program' argument is not used, so the arm file can 'exact' this at its 'hdisj'.

  WHAT STILL IS NOT A THEOREM OF 'generated', STATED PLAINLY. Section 11's '1 <= vk.quotientConstWords'
  is carried, not discharged: 'vkCarriesBuild' compares a 'take quotientConstWords' slice, and when
  the reservation is EMPTY that take is '[]' for every offset, so 'quotientConstOffsetWords' stops
  being pinned and the const window can be declared anywhere. It is a payload NON-DEGENERACY
  condition, not a memory-disjointness condition: the disjointness gap SPILL named is CLOSED. Nothing
  was added to 'ValidV3', to a row, to a bundle or to the root (RULES); every hypothesis below sits on
  a lemma of this file.

  THE ARM FACE NEEDS NOTHING NEW. 'spillSlotDisjoint_of_ordered' asks for 'cb = ofNat 256
  program.constMptr' and 'sp = ofNat 256 program.stackMptr'. Those two are NOT a fresh hypothesis:
  'AtSegment' ('Lowering/QuotientInterp.lean:200-204') already pins exactly that pair for the
  interpreter's own start environment, and 'QuotientLoopCompose.lean:731' proves it is preserved
  across a segment. So the arm's 'hdisj' conjunct is now a theorem of (i) 'AtSegment', (ii) the fit
  clause 'quotientProgramFits' - a theorem of 'ValidV3' at 'Statements.lean:3447', (iii) the arm's own
  'b <= constMax' PRE, and (iv) the construction ordering, whose only unproved input is the payload
  non-degeneracy condition above. No memory-disjointness fact is assumed anywhere.
-/

/-- A pointer step never moves an address by more than the step: 'Value.add' on an 'integer' adds
    'q * wordBytes' before 'asUsizeNat' reads it back, and on an 'identifier' 'asUsizeNat' is 0 on
    both sides. The inequality is all the ordering needs, which is what removes section 11's 'hvk'. -/
theorem asUsizeNat_add_le (v : Value) (q : Nat) :
    Value.asUsizeNat (Value.add v q) <= Value.asUsizeNat v + q * wordBytes := by
  have hw : wordBytes = 32 := rfl
  cases v with
  | integer i =>
      simp only [Value.add, Value.asUsizeNat, hw]
      split
      · split <;> omega
      · split <;> omega
  | identifier n off =>
      simp only [Value.add, Value.asUsizeNat]
      omega

/-- The same at the pointer face: 'pn (p.add q) <= ptrAddr p + q * wordBytes', for every 'Ptr'. -/
theorem pn_add_ptrAddr_le (p : Ptr) (q : Nat) :
    pn (p.add q) <= ptrAddr p + q * wordBytes := by
  show Value.asUsizeNat ((Ptr.add p q).value) <= Value.asUsizeNat (ptrValue p) + q * wordBytes
  simp only [Ptr.add, ptrValue]
  exact asUsizeNat_add_le p.value q

/-- **SECTION 11's ORDERING WITHOUT THE POINTER-SHAPE HYPOTHESIS.** Same construction equations minus
    'hvk': the const window ends at or before the payload window's end, and the payload window ends
    before the stack window (section 11's 'new_quotientStack_after_vk'). -/
theorem qvmWindows_disjoint_of_ptrs {memory : VerifierMemoryLayout}
    {meta_ : ConstraintSystemMeta} {vk : Halo2VerifyingKey} {vkMptr : Ptr}
    {config : VerifierMemoryLayoutConfig} {build : QuotientProgramBuild}
    {program : QuotientProgram} (qcOff qp : Nat)
    (hmem : memory = VerifierMemoryLayout.new meta_ vk vkMptr config)
    (hfit : build.consts.length <= vk.quotientConstWords)
    (hne : 1 <= vk.quotientConstWords)
    (hco : vk.quotientConstOffsetWords = some qcOff)
    (hpo : vk.quotientProgramOffsetWords = some qp)
    (hcar : vkCarriesBuild vk build = true)
    (hcm : program.constMptr = pn (vkMptr.add qcOff))
    (hsm : program.stackMptr = memory.quotientStackMptr)
    (hcmx : program.guards.constMax = build.consts.length - 1) :
    program.constMptr + 32 * (program.guards.constMax + 1) <= program.stackMptr := by
  have hlen : ptrAddr vkMptr + vk.len <= memory.quotientStackMptr := by
    rw [hmem]; exact new_quotientStack_after_vk meta_ vk vkMptr config
  have hsec := constSection_in_payload vk build qcOff qp hco hpo hfit hne hcar
  have hw : wordBytes = 32 := rfl
  have hcm1 : pn (vkMptr.add qcOff) <= ptrAddr vkMptr + qcOff * 32 := by
    rw [← hw]; exact pn_add_ptrAddr_le vkMptr qcOff
  have h32 : 32 * (program.guards.constMax + 1) <= 32 * vk.quotientConstWords := by
    rw [hcmx]
    refine Nat.mul_le_mul_left 32 ?_
    rcases Nat.eq_zero_or_pos (build.consts.length) with hz | hz
    · rw [hz]; omega
    · omega
  have hlen' : 32 * vk.constants.length <= vk.len := by
    show 32 * vk.constants.length <=
      vk.constants.length * 32 + (vk.fixedComms.length + vk.permutationComms.length) * 128
    omega
  have hkey : program.constMptr + 32 * (program.guards.constMax + 1)
      <= ptrAddr vkMptr + vk.len := by
    rw [hcm]
    omega
  rw [hsm]
  exact Nat.le_trans hkey hlen

/-- 'quotientVmGuards' succeeds only in its 'ok' branch, whose 'constMax' is 'model.numConsts - 1'
    (LoweringPlan.lean:376-381, R5: the subtraction is Nat truncation, i.e. saturating_sub). -/
theorem quotientVmGuards_ok_constMax
    {model : Midfall.Generator.QuotientValidator.QuotientOperandModel}
    {memory : VerifierMemoryLayout}
    {g : QuotientVmGuards} (h : quotientVmGuards model memory = .ok g) :
    g.constMax = model.numConsts - 1 := by
  simp only [quotientVmGuards] at h
  split at h
  · cases h
  · cases h
    rfl

/-- 'quotientOperandModel' fills its second field with 'build.consts.length' (LoweringPlan.lean:441-449). -/
theorem quotientOperandModel_ok_numConsts {meta_ : ConstraintSystemMeta} {dat : Data} {vk : Halo2VerifyingKey}
    {vkMptr : Ptr} {memory : VerifierMemoryLayout} {build : QuotientProgramBuild}
    {sf : SelectorFoldPlan} {m : Midfall.Generator.QuotientValidator.QuotientOperandModel}
    (h : quotientOperandModel meta_ dat vk vkMptr memory build sf = .ok m) :
    m.numConsts = build.consts.length := by
  simp only [quotientOperandModel, Bind.bind, Except.bind] at h
  obtain ⟨r, _, h2⟩ := (match_ok_iff _ _).mp h
  cases h2
  rfl

/-- The one-function inversion of 'quotientTemplateProgram' (PlanNew.lean:579-608): the two Option
    reads, the two reservations that did not fire, and the three fields of the triple it returns. -/
theorem quotientTemplateProgram_windows (build : QuotientProgramBuild) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (memory : VerifierMemoryLayout) (sf : SelectorFoldPlan)
    (opModel : Midfall.Generator.QuotientValidator.QuotientOperandModel)
    (trip : QuotientProgram × Nat × Midfall.Generator.QuotientFold.QuotientStateSlots)
    (h : quotientTemplateProgram build vk vkMptr memory sf opModel = .ok trip) :
    ∃ (constOff progOff : Nat) (g : QuotientVmGuards),
      vk.quotientConstOffsetWords = some constOff ∧
      vk.quotientProgramOffsetWords = some progOff ∧
      build.consts.length <= vk.quotientConstWords ∧
      quotientVmGuards opModel memory = .ok g ∧
      trip.1.constMptr = pn (vkMptr.add constOff) ∧
      trip.1.stackMptr = memory.quotientStackMptr ∧
      trip.1.guards = g := by
  cases hco : vk.quotientConstOffsetWords with
  | none =>
      have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
          = Except.error (Fault.panic (QuotientBlocks.siteQ 202
            "VK must carry quotient constants")) := by
        simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco]; try rfl
      rw [hred] at h; cases h
  | some constOff =>
    cases hpo : vk.quotientProgramOffsetWords with
    | none =>
        have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
            = Except.error (Fault.panic (QuotientBlocks.siteQ 204
              "VK must carry quotient program")) := by
          simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco, hpo]; try rfl
        rw [hred] at h; cases h
    | some progOff =>
      by_cases hc1 : build.consts.length <= vk.quotientConstWords
      · by_cases hc2 : (PackedProgramCodec.encodeWords build.bytes).length
            <= vk.quotientProgramWords
        · cases hg : quotientVmGuards opModel memory with
          | error e =>
              have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
                  = Except.error e := by
                simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco, hpo, hc1, hc2, hg]
                try rfl
              rw [hred] at h; cases h
          | ok g =>
              let hprog : QuotientProgram :=
                { len := ByteArray.size build.bytes,
                  opUsage := quotientOpcodeUsage build.usedOps,
                  memUsage := quotientMemUsage build.usedMemTokens,
                  constMptr := pn (vkMptr.add constOff),
                  evalNumerMptr := (Midfall.Generator.QuotientFold.QuotientStateSlots.new memory.quotientTmpMptr).evalNumerMptr,
                  traceIdMptr := (Midfall.Generator.QuotientFold.QuotientStateSlots.new memory.quotientTmpMptr).traceIdMptr,
                  selectorPowerMptr :=
                    (Midfall.Generator.QuotientFold.QuotientStateSlots.new memory.quotientTmpMptr).selectorPowerMptr,
                  selectorMaxPower := sf.maxPower,
                  selectorTailUpdates := QuotientFoldCompute.selectorTailUpdates sf,
                  stackMptr := memory.quotientStackMptr,
                  programMptr := pn (vkMptr.add progOff), guards := g }
              have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
                  = .ok (hprog, memory.quotientStackMptr,
                    Midfall.Generator.QuotientFold.QuotientStateSlots.new memory.quotientTmpMptr) := by
                simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco, hpo, hc1, hc2, hg]
                try rfl
              rw [hred] at h
              cases h
              exact ⟨_, _, _, by rfl, by rfl, by assumption, by rfl, by rfl, by rfl, by rfl⟩
        · have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
              = Except.error (Fault.panic (QuotientBlocks.siteQ 209
                "quotient program length exceeded VK payload reservation")) := by
            simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco, hpo, hc1, hc2]; try rfl
          rw [hred] at h; cases h
      · have hred : quotientTemplateProgram build vk vkMptr memory sf opModel
            = Except.error (Fault.panic (QuotientBlocks.siteQ 205
              "quotient const table exceeded VK payload reservation")) := by
          simp only [quotientTemplateProgram, Bind.bind, Except.bind, hco, hpo, hc1]; try rfl
        rw [hred] at h; cases h

/-- **THE ELEVEN-BIND PEEL.** Everything section 11 asked to be handed, out of the one equation
    'generated' supplies. -/
theorem newFromVk_windows {F : Type} [BEq F] (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding)
    (payload : Halo2VerifyingKey) (plan : LoweringPlan Unit Unit)
    (h : newFromVk feat field cs rawMeta numInstances accEncoding payload = .ok plan) :
    ∃ (q : PlannedQuotient) (memory : VerifierMemoryLayout) (vkMptr : Ptr)
      (constOff progOff : Nat) (meta2 : ConstraintSystemMeta)
      (config : VerifierMemoryLayoutConfig),
      plan.quotient = some q ∧ plan.memory = memory ∧
      memory = VerifierMemoryLayout.new meta2 payload vkMptr config ∧
      payload.quotientConstOffsetWords = some constOff ∧
      payload.quotientProgramOffsetWords = some progOff ∧
      q.build.consts.length <= payload.quotientConstWords ∧
      vkCarriesBuild payload q.build = true ∧
      q.program.constMptr = pn (vkMptr.add constOff) ∧
      q.program.stackMptr = memory.quotientStackMptr ∧
      q.program.guards.constMax = q.build.consts.length - 1 := by
  simp only [newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨⟨vkMptr, meta_, dat, _⟩, _, h1⟩ := (match_ok_iff _ _).mp h
  obtain ⟨proofLayout, _, h2⟩ := (match_ok_iff _ _).mp h1
  obtain ⟨qplan, _, h3⟩ := (match_ok_iff _ _).mp h2
  obtain ⟨build, _, h4⟩ := (match_ok_iff _ _).mp h3
  obtain ⟨nativeWords, _, h5⟩ := (match_ok_iff _ _).mp h4
  obtain ⟨pcsReq, _, h6⟩ := (match_ok_iff _ _).mp h5
  obtain ⟨accTerms, _, h7⟩ := (match_ok_iff _ _).mp h6
  obtain ⟨memory, hmem, h8⟩ := (match_ok_iff _ _).mp h7
  obtain ⟨opModel, hop, h9⟩ := (match_ok_iff _ _).mp h8
  obtain ⟨trip, htrip, h10⟩ := (match_ok_iff _ _).mp h9
  obtain ⟨constOff, progOff, g, hco, hpo, hfit, hvg, hcm, hsm, hg⟩ :=
    quotientTemplateProgram_windows build payload vkMptr memory qplan.selectorFold opModel trip htrip
  have honum : opModel.numConsts = build.consts.length := quotientOperandModel_ok_numConsts hop
  have hgc : g.constMax = opModel.numConsts - 1 := quotientVmGuards_ok_constMax hvg
  have hcmx : trip.1.guards.constMax = build.consts.length - 1 := by
    rw [hg, hgc, honum]
  obtain ⟨config, hnew⟩ : ∃ (config : VerifierMemoryLayoutConfig),
      memory = VerifierMemoryLayout.new meta_ payload vkMptr config := by
    simp only [memoryLayoutFor, Bind.bind, Except.bind, envOf] at hmem
    obtain ⟨t, _, hmem2⟩ := (match_ok_iff _ _).mp hmem
    exact ⟨_, (Except.ok.inj hmem2).symm⟩
  let q : PlannedQuotient :=
    { plan := qplan, build := build, program := trip.1, stackMptr := trip.2.1,
      stateSlots := trip.2.2 }
  clear h h1 h2 h3 h4 h5 h6 h7 h8 h9 hmem hop htrip
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals (try (split at h10))
  all_goals (try (cases h10))
  all_goals
    (try (exact ⟨q, memory, vkMptr, constOff, progOff, meta_, config, rfl, rfl, hnew, hco, hpo, hfit,
      by assumption, hcm, hsm, hcmx⟩))

/-- **THE RENDER FACE.** 'generated' alone, plus the plan's own quotient bundle and the one payload
    non-degeneracy condition section 11 named: the const window of THE PROGRAM ITSELF ends before its
    own operand-stack window. This is 'PG_qvmWindowsOrdered' discharged for the generator's program. -/
theorem qvmWindows_disjoint_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) (q : PlannedQuotient)
    (hq : R.plan.quotient = some q)
    (hne : 1 <= R.pv.vk.quotientConstWords) :
    PG_qvmWindowsOrdered q.program := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := plan_of_generated h
  obtain ⟨q', memory, vkMptr, constOff, progOff, meta2, config, hq', hpmem, hnew, hco, hpo,
      hfit, hcar, hcm, hsm, hcmx⟩ :=
    newFromVk_windows Features.solidity (frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have hqq : q' = q := by
    rw [hp] at hq
    exact Option.some.inj (hq'.symm.trans hq)
  subst hqq
  have hne' : 1 <= R.plan.vk.quotientConstWords := hne
  exact qvmWindows_disjoint_of_ptrs constOff progOff hnew hfit hne' hco hpo hcar hcm hsm hcmx

/-- **THE BitVec FACE THE ARMS STATE.** The ordering + the arm's own 'b <= constMax' PRE + the no-wrap
    conjuncts of 'quotientProgramFits'. The conclusion is 'PG_spillSlotDisjoint' unfolded: its
    '_program' argument is not used, so 'QuotientSpill.lean' can 'exact' this at its 'hdisj'. -/
theorem spillSlotDisjoint_of_ordered (program : QuotientProgram) (cb sp : BitVec 256) (b : Nat)
    (hord : PG_qvmWindowsOrdered program)
    (hfit : Midfall.LoweringV3.quotientProgramFits program)
    (hcb : cb = BitVec.ofNat 256 program.constMptr)
    (hsp : sp = BitVec.ofNat 256 program.stackMptr)
    (hb : (BitVec.ofNat 256 b).toNat <= (BitVec.ofNat 256 program.guards.constMax).toNat) :
    (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 <= sp.toNat ∨
      sp.toNat + 32 <= (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat := by
  obtain ⟨_, hfitc, hstk, hlast, _, _, _⟩ := hfit
  have hord' : program.constMptr + 32 * (program.guards.constMax + 1) <= program.stackMptr := hord
  have hw : 2 ^ 5 = 32 := by norm_num
  have hcmax : program.guards.constMax < 2 ^ 256 := by omega
  have hcm : (BitVec.ofNat 256 program.constMptr).toNat = program.constMptr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsm : (BitVec.ofNat 256 program.stackMptr).toNat = program.stackMptr := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hb0 : (BitVec.ofNat 256 program.guards.constMax).toNat = program.guards.constMax := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcmax
  have hb1 : (BitVec.ofNat 256 b).toNat <= program.guards.constMax := by
    rw [hb0] at hb; exact hb
  have hbx : ((BitVec.ofNat 256 b) <<< 5).toNat = (BitVec.ofNat 256 b).toNat * 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hw]
    refine Nat.mod_eq_of_lt ?_
    have : (BitVec.ofNat 256 b).toNat * 32 <= program.guards.constMax * 32 :=
      Nat.mul_le_mul_right 32 hb1
    omega
  have hsum : (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat
      = program.constMptr + (BitVec.ofNat 256 b).toNat * 32 := by
    rw [hcb, BitVec.toNat_add, hcm, hbx]
    refine Nat.mod_eq_of_lt ?_
    have : (BitVec.ofNat 256 b).toNat * 32 <= program.guards.constMax * 32 :=
      Nat.mul_le_mul_right 32 hb1
    omega
  rw [hsum, hsp, hsm]
  exact Or.inl (by omega)

/-- The whole chain in one line: 'generated', the plan's own bundle, the payload non-degeneracy
    condition, the fit clause, and the arm's 'b <= constMax' PRE give the arm's disjointness. -/
theorem spillSlotDisjoint_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) (q : PlannedQuotient)
    (hq : R.plan.quotient = some q)
    (hne : 1 <= R.pv.vk.quotientConstWords)
    (hfit : Midfall.LoweringV3.quotientProgramFits q.program)
    (cb sp : BitVec 256) (b : Nat)
    (hcb : cb = BitVec.ofNat 256 q.program.constMptr)
    (hsp : sp = BitVec.ofNat 256 q.program.stackMptr)
    (hb : (BitVec.ofNat 256 b).toNat <= (BitVec.ofNat 256 q.program.guards.constMax).toNat) :
    (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat + 32 <= sp.toNat ∨
      sp.toNat + 32 <= (cb + ((BitVec.ofNat 256 b) <<< 5)).toNat :=
  spillSlotDisjoint_of_ordered q.program cb sp b
    (qvmWindows_disjoint_of_generated h q hq hne) hfit hcb hsp hb

end Midfall.LoweringV3.MemoryPairs

/-! ## 8. AXIOMS AND CONE -/

#print axioms Midfall.LoweringV3.MemoryPairs.memoryRegionsPairwiseDisjoint_perm_pair
#print axioms Midfall.LoweringV3.MemoryPairs.wellFormed_pair_disjoint
#print axioms Midfall.LoweringV3.MemoryPairs.vkPayload_g1Identity_disjoint
#print axioms Midfall.LoweringV3.MemoryPairs.new_g1Identity_after_vk
#print axioms Midfall.LoweringV3.MemoryPairs.new_pair_disjoint
#print axioms Midfall.LoweringV3.MemoryPairs.falsifier_not_wellFormed
#print axioms Midfall.LoweringV3.MemoryPairs.layout_windows_not_tied_to_the_map
#print axioms Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_memory_new
#cone_sorries Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_memory_new
#cone_sorries Midfall.LoweringV3.MemoryPairs.vkPayload_g1Identity_disjoint
#print axioms Midfall.LoweringV3.MemoryPairs.newFromVk_memory
#print axioms Midfall.LoweringV3.MemoryPairs.plan_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.plan_memory_eq_new
#print axioms Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_generated
#cone_sorries Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.gvfp_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.generated_model_facts
#print axioms Midfall.LoweringV3.MemoryPairs.vkPins_numInst_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.vkCodehashArm_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.row_premises_of_generated
#cone_sorries Midfall.LoweringV3.MemoryPairs.row_premises_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.ofNat_toNat_iff_lt
#print axioms Midfall.LoweringV3.MemoryPairs.fit1_of_bound
#print axioms Midfall.LoweringV3.MemoryPairs.fit2_of_bound
#print axioms Midfall.LoweringV3.MemoryPairs.new_vkMptr_image_unbounded
#print axioms Midfall.LoweringV3.MemoryPairs.generated_face_allows_fit1_to_fail
#print axioms Midfall.LoweringV3.MemoryPairs.new_transcriptMptr_eq
#print axioms Midfall.LoweringV3.MemoryPairs.new_vkMptr_eq_arg
#print axioms Midfall.LoweringV3.MemoryPairs.extendVk_len
#print axioms Midfall.LoweringV3.MemoryPairs.vkLen_unbounded
#print axioms Midfall.LoweringV3.MemoryPairs.slice_extend
#print axioms Midfall.LoweringV3.MemoryPairs.vkCarriesBuild_extend
#print axioms Midfall.LoweringV3.MemoryPairs.hugeVk_len_ge
#print axioms Midfall.LoweringV3.MemoryPairs.fit2_can_fail
#print axioms Midfall.LoweringV3.MemoryPairs.fit1_iff_bound
#print axioms Midfall.LoweringV3.MemoryPairs.fit2_iff_bound
#cone_sorries Midfall.LoweringV3.MemoryPairs.fit1_iff_bound
#print axioms Midfall.LoweringV3.MemoryPairs.fit1_of_valid
#print axioms Midfall.LoweringV3.MemoryPairs.fit2_of_valid
#cone_sorries Midfall.LoweringV3.MemoryPairs.fit1_of_valid
#assert_axioms Midfall.LoweringV3.MemoryPairs.fit1_of_valid [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.MemoryPairs.fit2_of_valid [propext, Classical.choice, Quot.sound] native []


#print axioms Midfall.LoweringV3.MemoryPairs.new_quotientStack_after_vk
#print axioms Midfall.LoweringV3.MemoryPairs.constSection_in_payload
#print axioms Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_construction
#print axioms Midfall.LoweringV3.MemoryPairs.fitsFalsifier_fits
#assert_axioms Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_construction [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.MemoryPairs.fitsFalsifier_not_ordered [propext, Classical.choice, Quot.sound] native []
#print axioms Midfall.LoweringV3.MemoryPairs.payload_below_quotientStack_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.payload_below_quotientStack_of_valid
#assert_axioms Midfall.LoweringV3.MemoryPairs.payload_below_quotientStack_of_valid [propext, Classical.choice, Quot.sound] native []

#print axioms Midfall.LoweringV3.MemoryPairs.asUsizeNat_add_le
#print axioms Midfall.LoweringV3.MemoryPairs.pn_add_ptrAddr_le
#print axioms Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_ptrs
#cone_sorries Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_ptrs
#print axioms Midfall.LoweringV3.MemoryPairs.quotientVmGuards_ok_constMax
#print axioms Midfall.LoweringV3.MemoryPairs.quotientOperandModel_ok_numConsts
#print axioms Midfall.LoweringV3.MemoryPairs.quotientTemplateProgram_windows
#cone_sorries Midfall.LoweringV3.MemoryPairs.quotientTemplateProgram_windows
#print axioms Midfall.LoweringV3.MemoryPairs.newFromVk_windows
#cone_sorries Midfall.LoweringV3.MemoryPairs.newFromVk_windows
#print axioms Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_generated
#cone_sorries Midfall.LoweringV3.MemoryPairs.qvmWindows_disjoint_of_generated
#print axioms Midfall.LoweringV3.MemoryPairs.spillSlotDisjoint_of_ordered
#cone_sorries Midfall.LoweringV3.MemoryPairs.spillSlotDisjoint_of_ordered
#print axioms Midfall.LoweringV3.MemoryPairs.spillSlotDisjoint_of_generated
#cone_sorries Midfall.LoweringV3.MemoryPairs.spillSlotDisjoint_of_generated
