-- |
-- Midfall.LoweringV3.RenderFresh
--
-- The render-level instance of the quotient freshness predicate.  This file
-- imports `MemoryPairs` (and therefore YulSemantics, whose `data` yul-object
-- token cannot be used as a binder name), so binders here are spelled `dat`.
import Midfall.LoweringV3.QuotientFresh
import Midfall.LoweringV3.MemoryPairs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator

theorem plan_data_commsNumericOrIdentity {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (R : Midfall.LoweringV2.Render p G₁ G₂ Gₜ)
    (h : Midfall.LoweringV3.GeneratedBy R) :
    R.plan.data.CommsNumericOrIdentity := by
  obtain ⟨m0, _n, _hnew, hdata, _hcount, _hmeta⟩ :=
    Midfall.LoweringV3.MemoryPairs.planMeta_of_generated h
  obtain ⟨meta_, vkMptr, config, hmem⟩ :=
    Midfall.LoweringV3.MemoryPairs.plan_memory_eq_new h
  obtain ⟨vkBase, hvkBase⟩ :=
    Midfall.LoweringV3.MemoryPairs.vkMptr_shape_of_generated h
  have hpvMem : R.pv.memory = R.plan.memory := rfl
  have hpvVk : R.pv.vk = R.plan.vk := rfl
  have hmemR : R.plan.memory = VerifierMemoryLayout.new meta_ R.plan.vk vkMptr config := by
    rw [← hpvMem, hmem, hpvVk]
  have hvkMem : R.pv.memory.vkMptr.Numeric := ⟨vkBase, hvkBase⟩
  have hvk : vkMptr.Numeric := by
    have h' : (VerifierMemoryLayout.new meta_ R.pv.vk vkMptr config).vkMptr.Numeric := by
      rw [← hmem]
      exact hvkMem
    simpa [Midfall.LoweringV3.MemoryPairs.new_vkMptr] using h'
  have hbases : R.plan.memory.NumericBases := by
    rw [hmemR]
    exact VerifierMemoryLayout.new_numericBases meta_ R.plan.vk vkMptr config hvk
  exact Midfall.Generator.Data.new_commsNumericOrIdentity (F := Unit)
    (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory R.plan.data hbases hdata

end Midfall.LoweringV3
