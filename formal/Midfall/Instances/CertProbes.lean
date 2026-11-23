/-
  Midfall.Instances.CertProbes  (CERT.1, D2)

  The two CERT.1 suspects, probed against the current tree:

  * `v3_planMeta` — **CLOSED.** `PlanMeta` asks
    `Data.new (rawMeta.setNumDummyEvals 0) R.plan.vk R.plan.memory = .ok R.plan.data`, where
    `R.plan.memory` is the FINAL layout (`metaDataForVk`'s `memory2`, built from the meta AFTER
    `set_num_point_sets`) and the Rust/port calls `Data.new` with the INTERMEDIATE layout
    (`metaDataForVk`: `let memory ← memoryLayoutFor ... meta1 ...; let data0 ← Data.new meta1 vk
    memory`). The missing equality is now PROVED, not assumed:
    `Midfall.Generator.new_dataBases_setNumPointSets` shows `VerifierMemoryLayout.new` gives the
    ten bases `Data.new` reads the same values under `setNumPointSets` and under the plan's
    PCS/quotient config (`Midfall.Generator.LayoutMemory`), `Data.new_congr` transfers the
    equation, and `Midfall.LoweringV3.MemoryPairs.planMeta_of_generated` assembles it against the
    real bind chain. `v3_planMeta` is that theorem at `GeneratedBy`; `PlanMetaStable` below is
    the same fact split in two, and `planMetaStable_of_generated` derives it for every generated
    render, so it is no longer an assumed clause.

  * `v3_cdBound` — **NEEDS CLAUSE.** No generator check bounds `proofEnd` or `numInstances`:
    `proofEnd` is a sum of commitment/evaluation section lengths built by
    `ProofCalldataLayout.fromProtocol` from the circuit's counts, and `SupportedInput.sizeBound`
    bounds only `numInstances < 2^64` and `k < 64`. `cdBoundB` is a conjunct of the current
    `programOk`, so it is an OUTPUT obligation (registered as `v3_cdBound`, CERT.1/CERT.6), not a
    consequence of generation. The candidate clause below is the fit itself; the input-only form
    needs bounds on the circuit's commitment and evaluation counts (the exact arithmetic route is
    the CERT.6 builder lemma). `cdBoundB_of_candidate` typechecks the bridge to the program bundle.

  `CdBoundCandidate` remains a candidate clause, NOT an edit to `SupportedInput`: the structure of
  record is `Midfall.Generator.Certified.SupportedInput`, unchanged. `PlanMetaStable` is now
  derived, not assumed (`planMetaStable_of_generated`), and `planMeta_of_stable` keeps the
  sufficiency direction certified.
-/
import Midfall.Generator.Certified
set_option autoImplicit false

namespace Midfall.Instances.CertProbes

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2
open Midfall.LoweringV3 Midfall.Generator.Certified
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## v3_planMeta: the missing layout-stability equality -/

/-- **`PlanMetaStable`, the CERT.1 candidate split in two.** The data equation is stated on the
    FINAL plan memory (what the port hands `Data.new`) and the meta equation separately; the
    stability fact is that the Rust's intermediate pre-point-set memory agrees with this final
    memory on the ten bases `Data.new` reads. It was a candidate clause; it is now derived from
    generation (`planMetaStable_of_generated`) and equivalent to `PlanMeta`
    (`planMetaStable_iff`). -/
structure PlanMetaStable (R : Render p G₁ G₂ Gₜ) : Prop where
  metaEq : ∃ (m0 : ConstraintSystemMeta) (n : Nat),
    ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok m0 ∧
    numPointSets (m0.setNumDummyEvals 0) R.plan.data = .ok n ∧
    R.plan.meta_ = (m0.setNumDummyEvals 0).setNumPointSets n
  dataOnFinalMemory : ∃ (m0 : ConstraintSystemMeta),
    ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok m0 ∧
    Data.new (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory = .ok R.plan.data

/-- **`PlanMetaStable` ⇒ `PlanMeta`.** The bridge that was always available: the meta equation
    and the data equation on the final memory, sharing their `m0`. PROVED. -/
theorem planMeta_of_stable {R : Render p G₁ G₂ Gₜ} (h : PlanMetaStable R) :
    Midfall.LoweringV3.PlanMeta R := by
  obtain ⟨m0, n, h1, h2, h3⟩ := h.metaEq
  obtain ⟨m0', h1', h4⟩ := h.dataOnFinalMemory
  rw [h1] at h1'
  cases h1'
  exact ⟨m0, n, h1, h4, h2, h3⟩

/-- **`PlanMeta` ⇒ `PlanMetaStable`.** The same existential, split into the two candidate
    fields. PROVED. -/
theorem planMetaStable_of_planMeta {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.PlanMeta R) : PlanMetaStable R := by
  obtain ⟨m0, n, h1, h2, h3, h4⟩ := h
  exact ⟨⟨m0, n, h1, h3, h4⟩, ⟨m0, h1, h2⟩⟩

/-- The candidate clause and the clause it was cut from are EQUIVALENT. PROVED. -/
theorem planMetaStable_iff {R : Render p G₁ G₂ Gₜ} :
    PlanMetaStable R ↔ Midfall.LoweringV3.PlanMeta R :=
  ⟨planMeta_of_stable, planMetaStable_of_planMeta⟩

/-- **THE STABILITY CLAUSE, DISCHARGED FOR EVERY GENERATED RENDER.** `v3_planMeta`'s content is
    the stability fact proved in `Midfall.Generator` (`new_dataBases_setNumPointSets`,
    `Data.new_congr`) and assembled in `Midfall.LoweringV3.MemoryPairs.planMeta_of_generated`.
    This is the form `PlanMetaStable` is consumed in: no hypothesis beyond generation. PROVED. -/
theorem planMetaStable_of_generated {R : Render p G₁ G₂ Gₜ}
    (h : Midfall.LoweringV3.GeneratedBy R) : PlanMetaStable R :=
  planMetaStable_of_planMeta (Midfall.LoweringV3.MemoryPairs.planMeta_of_generated h)

/-! ## v3_cdBound: the output fit, and its Bool face -/

/-- **CANDIDATE CLAUSE for `v3_cdBound`.** Output-side by construction: `proofEnd` is computed by
    `fromProtocol` from the circuit's counts, which `SupportedInput` does not bound. -/
structure CdBoundCandidate (R : Render p G₁ G₂ Gₜ) : Prop where
  bound : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256

/-- The candidate clause gives the `Prop` form. PROVED. -/
theorem cdBound_of_candidate {R : Render p G₁ G₂ Gₜ} (h : CdBoundCandidate R) :
    R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256 :=
  h.bound

/-- The candidate clause gives the `programOkB` conjunct `cdBoundB`. PROVED. -/
theorem cdBoundB_of_candidate {R : Render p G₁ G₂ Gₜ} (h : CdBoundCandidate R) :
    Midfall.LoweringV3.cdBoundB R.pv R.cfg.numInstances = true := by
  unfold Midfall.LoweringV3.cdBoundB
  apply decide_eq_true
  change R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256
  exact h.bound

#print axioms planMeta_of_stable
#print axioms planMetaStable_of_planMeta
#print axioms planMetaStable_of_generated
#print axioms planMetaStable_iff
#assert_axioms planMetaStable_of_generated [propext, Classical.choice, Quot.sound] native []
#print axioms cdBoundB_of_candidate

end Midfall.Instances.CertProbes
