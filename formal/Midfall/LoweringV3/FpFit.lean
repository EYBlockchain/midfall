/-
  Midfall.LoweringV3.FpFit

  ROW.FP (WP A11) - the named pairing-slot fit obligation `PG-PAIRINGFIT`.

  D-GATE8 (signed 2026-11-23) repaired `programFits` with `staticWorkingSetFits`
  (`pv.memory.traceU256Mptr + wordBytes < 2^256`, the aligned maximum of every
  static region end), so `PG-PAIRINGFIT` is now a THEOREM-target of `ValidV3`,
  not a gap: the clean arm converts the slice's `BitVec.ofNat 256` pointer
  literals back to `Nat` via the slot fits derived from that clause.  The
  falsifier below records why the old VK-only bound was insufficient.
-/
import Midfall.LoweringV3.Totality

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **PG-PAIRINGFIT (the rows' target, now derivable from D-GATE8).** The three
    pairing input pointers fit a word.  This is what the clean arm's
    `BitVec.ofNat 256 … .toNat` conversions need. -/
def PG_PAIRINGFIT (R : Render p G₁ G₂ Gₜ) : Prop :=
  cAddr R.pv.memory.pairingLhsMptr < 2 ^ 256 ∧
  cAddr R.pv.memory.pairingRhsMptr < 2 ^ 256 ∧
  cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) < 2 ^ 256 ∧
  cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) < 2 ^ 256

/-- **PG-PAIRINGFIT (the clause D-GATE8 adopted, in margin form).** -/
def PG_PAIRINGFIT_MARGIN (R : Render p G₁ G₂ Gₜ) : Prop :=
  ptrAddr R.pv.memory.vkMptr + R.pv.vk.len +
      (R.pv.memory.thetaWindows.rotPointsWord * Midfall.Generator.wordBytes) < 2 ^ 256

/-- A `Nat` at or above `2^256` cannot be read back from its `BitVec.ofNat 256`
    literal. -/
theorem ofNat_toNat_ne_of_ge {n : Nat} (h : 2 ^ 256 ≤ n) :
    (BitVec.ofNat 256 n).toNat ≠ n := by
  intro hn
  have hlt := (Midfall.LoweringV3.MemoryPairs.ofNat_toNat_iff_lt n).mp hn
  omega

/-- **THE LAYOUT-LEVEL FALSIFIER, REDUCED.**  The constructor's `allocAfter`
    chain gives `challengeStart = alignUp (B + vk.len) 32`; at
    `B + vk.len = 2^256 - 2` this is `2^256`, and every theta/pairing slot is at
    or above it.  The remaining lower-bound equation is the explicit `hge`:
    unfolding `VerifierMemoryLayout.new`'s `let` chain is the next mechanical
    step, and `hge` is exactly the fact the current clause table does not carry. -/
theorem pairingFit_falsifier_layout
    (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (config : VerifierMemoryLayoutConfig) (B : Nat)
    (hB : B + vk.len = 2 ^ 256 - 2)
    (hge : 2 ^ 256 ≤
      ptrAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr) :
    ¬ (BitVec.ofNat 256
        (cAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr)).toNat
      = cAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr := by
  apply ofNat_toNat_ne_of_ge
  simpa only [cAddr, ptrAddr, ptrValue] using hge

/-- The chosen `B` satisfies both VK bounds of `programFits` whenever the payload
    fits in a word.  This is the legal side of the falsifier: the VK half of the
    clause table is untouched. -/
theorem programFits_vk_bound_at_B {R : Render p G₁ G₂ Gₜ} {B : Nat}
    (hB : B + R.pv.vk.len = 2 ^ 256 - 2)
    (hlen : R.pv.vk.len + 2 ≤ 2 ^ 256) :
    B + R.pv.vk.len < 2 ^ 256 ∧ B + R.pv.vk.runtimeLen < 2 ^ 256 := by
  have hr : R.pv.vk.runtimeLen = R.pv.vk.len + 1 := by
    unfold Midfall.Generator.Halo2VerifyingKey.runtimeLen Midfall.Generator.vkRuntimePrefixLen
    omega
  constructor <;> omega

#assert_axioms Midfall.LoweringV3.ofNat_toNat_ne_of_ge
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingFit_falsifier_layout
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.programFits_vk_bound_at_B
  [propext, Classical.choice, Quot.sound] native []

/-! ## 2. THE D-GATE8 FIT BRIDGE

    `ValidV3`'s `programFits` carries `staticWorkingSetFits`
    (`Statements.lean:3415`): the aligned maximum of every static region end,
    `traceU256Mptr + wordBytes`, fits a word.  The rows' `PG-PAIRINGFIT` asks for
    four individual pointer fits.  The derivation is by the layout's own
    `allocAfter` chain:

      * the `vkMptr` region ends at `ptrAddr vkMptr + vk.len`, and the theta
        windows start at `alignUp (alignUp (ptrAddr vkMptr + vk.len) 32
        + challenge windows) 32`;
      * `pairingLhsMptr` / `pairingRhsMptr` are theta start `+ 44` / `+ 48`
        words, so both are below `thetaStartOf + 52` words;
      * the compatibility theta window (`rotPointsWord = 52`) ends at or below
        `traceU256Mptr` (it is one of the `max` conjuncts), hence every pairing
        slot is below `traceU256Mptr + wordBytes < 2^256`;
      * `g2Base` / `negSG2Base` are word offsets `15` / `23` from the vk
        pointer, and `vkMptr ≤ thetaStart`, so both VK-derived addresses are
        below `thetaStart + 24` words, hence also below the fit bound.

    Nothing here is new hypothesis: the one premise is
    `staticWorkingSetFits R.pv` from `ValidV3` (`staticWorkingSetFits_of_valid`).
    This is what A12's clean arm consumes to turn the slice's
    `BitVec.ofNat 256` pointer literals back into `Nat`. -/

/-- The theta-window start implied by the layout's `allocAfter` chain, named so
    the two pairing slots (at 44 and 48 words) and the VK-derived slots can be
    bounded against one value. -/
def thetaStartOf (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr) : Nat :=
  alignUp (alignUp (ptrAddr vkMptr + vk.len) Midfall.Generator.wordBytes
    + meta_.challengeIndices.length * Midfall.Generator.wordBytes) Midfall.Generator.wordBytes

/-- The theta window (52 compatibility words) ends at or below the layout's
    `traceU256Mptr`: `traceU256Mptr` is the `max` over all static region ends, and
    the theta end is one of its conjuncts. -/
theorem thetaStartOf_le_traceU256Mptr (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    thetaStartOf meta_ vk vkMptr
      + ThetaWindowLayout.compatibility.rotPointsWord * Midfall.Generator.wordBytes ≤
    (VerifierMemoryLayout.new meta_ vk vkMptr config).traceU256Mptr := by
  unfold thetaStartOf VerifierMemoryLayout.new
  refine Nat.le_trans ?_ (MemoryPairs.alignUp_le _ _ MemoryPairs.wordBytes_pos)
  refine (le_foldl_max _ _).2 _ ?_
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))

set_option maxHeartbeats 4000000 in
theorem pairingLhsMptr_eq (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) :
    cAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).pairingLhsMptr =
      thetaStartOf meta_ vk vkMptr + 44 * Midfall.Generator.wordBytes := by
  show Value.asUsizeNat
    (ptrMemory (valueFromNat (thetaStartOf meta_ vk vkMptr
      + 44 * Midfall.Generator.wordBytes))).value = _
  show Value.asUsizeNat (valueFromNat (thetaStartOf meta_ vk vkMptr
      + 44 * Midfall.Generator.wordBytes)) = _
  exact MemoryPairs.ptrAddr_valueFromNat _

set_option maxHeartbeats 4000000 in
theorem pairingRhsMptr_eq (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (config : VerifierMemoryLayoutConfig) :
    cAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).pairingRhsMptr =
      thetaStartOf meta_ vk vkMptr + 48 * Midfall.Generator.wordBytes := by
  show Value.asUsizeNat
    (ptrMemory (valueFromNat (thetaStartOf meta_ vk vkMptr
      + 48 * Midfall.Generator.wordBytes))).value = _
  show Value.asUsizeNat (valueFromNat (thetaStartOf meta_ vk vkMptr
      + 48 * Midfall.Generator.wordBytes)) = _
  exact MemoryPairs.ptrAddr_valueFromNat _

/-- The layout copies its `vkMptr` argument, and the theta chain only adds to
    `ptrAddr vkMptr`, so the VK region's own start is at or below the theta
    start. -/
theorem vkMptr_le_thetaStartOf (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig) :
    ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr ≤ thetaStartOf meta_ vk vkMptr := by
  unfold thetaStartOf VerifierMemoryLayout.new
  exact Nat.le_trans
    (Nat.le_trans (Nat.le_add_right (ptrAddr vkMptr) vk.len)
      (MemoryPairs.alignUp_le (ptrAddr vkMptr + vk.len) Midfall.Generator.wordBytes
        MemoryPairs.wordBytes_pos))
    (Nat.le_trans
      (Nat.le_add_right
        (alignUp (ptrAddr vkMptr + vk.len) Midfall.Generator.wordBytes)
        (meta_.challengeIndices.length * Midfall.Generator.wordBytes))
      (MemoryPairs.alignUp_le
        (alignUp (ptrAddr vkMptr + vk.len) Midfall.Generator.wordBytes
          + meta_.challengeIndices.length * Midfall.Generator.wordBytes)
        Midfall.Generator.wordBytes MemoryPairs.wordBytes_pos))

/-- The left pairing pointer fits a word under the D-GATE8 working-set fit. -/
theorem pairingLhsMptr_lt_of_fit (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (hfit : (VerifierMemoryLayout.new meta_ vk vkMptr config).traceU256Mptr
      + Midfall.Generator.wordBytes < 2 ^ 256) :
    cAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).pairingLhsMptr < 2 ^ 256 := by
  rw [pairingLhsMptr_eq]
  have h := thetaStartOf_le_traceU256Mptr meta_ vk vkMptr config
  have hb : ThetaWindowLayout.compatibility.rotPointsWord = 52 := by decide
  rw [hb] at h
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  omega

/-- The right pairing pointer fits a word under the D-GATE8 working-set fit. -/
theorem pairingRhsMptr_lt_of_fit (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (hfit : (VerifierMemoryLayout.new meta_ vk vkMptr config).traceU256Mptr
      + Midfall.Generator.wordBytes < 2 ^ 256) :
    cAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).pairingRhsMptr < 2 ^ 256 := by
  rw [pairingRhsMptr_eq]
  have h := thetaStartOf_le_traceU256Mptr meta_ vk vkMptr config
  have hb : ThetaWindowLayout.compatibility.rotPointsWord = 52 := by decide
  rw [hb] at h
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  omega

/-- The `g2Base` VK slot (word offset 15) fits a word under the fit bound. -/
theorem g2Addr_lt_of_fit (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (hfit : (VerifierMemoryLayout.new meta_ vk vkMptr config).traceU256Mptr
      + Midfall.Generator.wordBytes < 2 ^ 256) :
    ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr
        + Midfall.Generator.wordBytes * vkHeaderTemplateSlotsDefault.g2Base < 2 ^ 256 := by
  have hle := vkMptr_le_thetaStartOf meta_ vk vkMptr config
  have h := thetaStartOf_le_traceU256Mptr meta_ vk vkMptr config
  have hb : ThetaWindowLayout.compatibility.rotPointsWord = 52 := by decide
  rw [hb] at h
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  show ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr
      + Midfall.Generator.wordBytes * 15 < 2 ^ 256
  omega

/-- The `negSG2Base` VK slot (word offset 23) fits a word under the fit bound. -/
theorem negSG2Addr_lt_of_fit (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (config : VerifierMemoryLayoutConfig)
    (hfit : (VerifierMemoryLayout.new meta_ vk vkMptr config).traceU256Mptr
      + Midfall.Generator.wordBytes < 2 ^ 256) :
    ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr
        + Midfall.Generator.wordBytes * vkHeaderTemplateSlotsDefault.negSG2Base < 2 ^ 256 := by
  have hle := vkMptr_le_thetaStartOf meta_ vk vkMptr config
  have h := thetaStartOf_le_traceU256Mptr meta_ vk vkMptr config
  have hb : ThetaWindowLayout.compatibility.rotPointsWord = 52 := by decide
  rw [hb] at h
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  show ptrAddr (VerifierMemoryLayout.new meta_ vk vkMptr config).vkMptr
      + Midfall.Generator.wordBytes * 23 < 2 ^ 256
  omega

/-- **THE FIT BRIDGE.** `ValidV3` implies the rows' `PG-PAIRINGFIT`: the three
    pairing pointers, including the two VK-derived G2 slots, fit a word.  The
    only premise is D-GATE8's `staticWorkingSetFits` projection. -/
theorem pairingFit_of_staticWorkingSetFits (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    PG_PAIRINGFIT R := by
  obtain ⟨meta_, vkMptr, config, vkBase, hmem, hvk, -⟩ := plan_size_of_generated hR.generated
  unfold PG_PAIRINGFIT
  have hfit := staticWorkingSetFits_of_valid hR
  unfold staticWorkingSetFits at hfit
  rw [hmem] at hfit ⊢
  refine ⟨pairingLhsMptr_lt_of_fit meta_ R.pv.vk vkMptr config hfit,
    pairingRhsMptr_lt_of_fit meta_ R.pv.vk vkMptr config hfit, ?_, ?_⟩
  · have hH := MemoryPairs.vkHeader_default_of_generated hR.generated
    rw [hH]
    show cAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
      vkHeaderTemplateSlotsDefault.g2Base) < 2 ^ 256
    have hptr : ∃ n : ℕ,
        ptrValue (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
          = Value.integer ↑n := by
      refine ⟨vkBase, ?_⟩
      rw [MemoryPairs.new_vkMptr, hvk]
      rfl
    rw [show cAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
        vkHeaderTemplateSlotsDefault.g2Base) =
        ptrAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
          vkHeaderTemplateSlotsDefault.g2Base) from rfl]
    rw [VkClean.ptrAddr_ptr_add_of_integer _ _ hptr]
    exact g2Addr_lt_of_fit meta_ R.pv.vk vkMptr config hfit
  · have hH := MemoryPairs.vkHeader_default_of_generated hR.generated
    rw [hH]
    show cAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
      vkHeaderTemplateSlotsDefault.negSG2Base) < 2 ^ 256
    have hptr : ∃ n : ℕ,
        ptrValue (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
          = Value.integer ↑n := by
      refine ⟨vkBase, ?_⟩
      rw [MemoryPairs.new_vkMptr, hvk]
      rfl
    rw [show cAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
        vkHeaderTemplateSlotsDefault.negSG2Base) =
        ptrAddr (Ptr.add (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr
          vkHeaderTemplateSlotsDefault.negSG2Base) from rfl]
    rw [VkClean.ptrAddr_ptr_add_of_integer _ _ hptr]
    exact negSG2Addr_lt_of_fit meta_ R.pv.vk vkMptr config hfit

/-- **`PG-PAIRINGFIT` FROM `ValidV3`.** -/
theorem PG_PAIRINGFIT_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) : PG_PAIRINGFIT R :=
  pairingFit_of_staticWorkingSetFits R hR

/-- The clean slice reads the left pairing slot back from its emitted
    `BitVec.ofNat 256` literal; the fit bridge supplies the bound. -/
theorem pairingLhsMptr_toNat_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    (BitVec.ofNat 256 (cAddr R.pv.memory.pairingLhsMptr)).toNat =
      ptrAddr R.pv.memory.pairingLhsMptr := by
  have h := (MemoryPairs.ofNat_toNat_iff_lt (cAddr R.pv.memory.pairingLhsMptr)).mpr
    (PG_PAIRINGFIT_of_valid R hR).1
  simpa [cAddr, ptrAddr, Midfall.Generator.ptrValue] using h

/-- The clean slice reads the right pairing slot back from its emitted
    `BitVec.ofNat 256` literal; the fit bridge supplies the bound. -/
theorem pairingRhsMptr_toNat_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    (BitVec.ofNat 256 (cAddr R.pv.memory.pairingRhsMptr)).toNat =
      ptrAddr R.pv.memory.pairingRhsMptr := by
  have h := (MemoryPairs.ofNat_toNat_iff_lt (cAddr R.pv.memory.pairingRhsMptr)).mpr
    (PG_PAIRINGFIT_of_valid R hR).2.1
  simpa [cAddr, ptrAddr, Midfall.Generator.ptrValue] using h

/-- **THE CLEAN SLICE CONSUMES THE FIT BRIDGE.** `block_live`'s finalPairing case
    (`Totality.block_live_finalPairing_of_body`) previously carried the two
    `BitVec.ofNat` read-back equations as premises; they are now
    `pairingLhsMptr_toNat_of_valid`/`pairingRhsMptr_toNat_of_valid`, so the case
    depends only on the helper body run `FpBodyRun`. -/
theorem block_live_finalPairing_of_body_fit
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    (hbody : FpBodyRun R product) :
    BlockLive R .finalPairing H vkAddr product cd :=
  block_live_finalPairing_of_body R product hR hpc H vkAddr cd hbody
    (pairingRhsMptr_toNat_of_valid R hR) (pairingLhsMptr_toNat_of_valid R hR)

#assert_axioms Midfall.LoweringV3.thetaStartOf_le_traceU256Mptr
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingLhsMptr_lt_of_fit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingRhsMptr_lt_of_fit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.g2Addr_lt_of_fit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.negSG2Addr_lt_of_fit
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingFit_of_staticWorkingSetFits
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.PG_PAIRINGFIT_of_valid
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingLhsMptr_toNat_of_valid
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingRhsMptr_toNat_of_valid
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.block_live_finalPairing_of_body_fit
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3
