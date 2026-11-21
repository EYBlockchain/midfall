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

