/-
  Midfall.Instances.ValidV3F1Real

  **B4V3: THE F1-REAL `ValidV3`, ASSEMBLED FROM B3'S POINT HALF.**

  `PayloadPointsF1.f1PointRenderCN n` is F1's render with three data lanes re-sourced:
  the Lean key's 19/8 commitments are the payload's decoded points (`f1VkResourced`), the KZG
  parameters carry the payload's `s·H2` (`f1ParamsResourced n`), and `sG2gen` is that point's
  inverse. Its point half is B3's `f1PointRenderCN_payloadPointHalf n hpay`, where the ONE data
  input is

      hpay : vkG2Words f1Pv vkNegSG2BaseSlot = g2foldToEip (g2foldExp n)

  - the tracked artifact's NEG_S_G2 bytes name the exponent `n`. This file assembles the OTHER
  six clauses and the nine scalar payload fields at that render and combines the two halves:

      f1PointRenderCN_validV3 (n) (hpay) : ValidV3 (f1PointRenderCN n)

  No hypothesis is added to `ValidV3`: `hpay` is a DATA statement about the artifact's own bytes,
  consumed through B3's point-half theorem, and the assembly below re-proves every clause at the
  render's own computable faces.

  WHAT TRANSFERS AND WHY. `Render.pv` is derived (`planViewOf R.plan R.model R.cfg.accumulator`,
  `LoweringV2/Statements.lean:162`) and the render carries the same plan/model/cfg as
  `f1GeneratedRender`, so `f1PointRenderC_pv` gives `pv = f1Pv` by `rfl`: the program, the scans,
  the no-writers clause, the layout and the payload's nine scalar fields are the F1 measurements.
  What changes is the Lean key (`poseidonVkExec` -> `f1VkResourced`), the KZG parameters, the
  `sG2gen` slot and `Gₜ` (the constructed pairing `pairingF1`, whose generators are `g1zGen` and
  `g2foldExp 1` by `rfl`), so `generated`, `env` and `supported` are re-established:
  * `generated`: `generateAll` on the re-sourced key is `.ok genFilledOut` - the generator reads
    the commitment COUNTS and the payload, not the commitment elements, and the run's three
    projections are `genFilledOut`'s by `rfl` (`f1ResOut_eq`). Computed, not assumed:
    `f1ResRun_isOk`.
  * `env`: nine fields read only the key/cfg/domain (unchanged by the re-source); `nG2`/`sG2` are
    `rfl` at `f1ParamsResourced n`/`pairingF1`; the plan-view fields are F1's.
  * `supported`: `wf` is D.2's `WellFormed` proof (the re-source changes commitment ELEMENTS, not
    any count, domain or CS face), `vkPoints` is `g1CodecZ_g1Valid` applied to every element of
    the carrier (`ptReadable_g1zToEip`), and the layout pair is F1's plan.

  THE RESIDUAL. This is `ValidV3` at an F1-real render; it is NOT `Done`. `Done` additionally
  needs the gate (`GateAtV3`, which requires `G1CodecLawsV3` - FALSE at this render's codec
  `g1CodecZ`, `VacuityWitnesses.f1_codec_headline_false`), totality, and artifact equality. Those
  are named at the foot.
-/
import Midfall.Instances.PayloadPointsF1

set_option autoImplicit false

namespace Midfall.Instances.ValidV3F1Real

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1 Midfall.Instances.ValidV3InhabitationF1Completion
open Midfall.Instances.PayloadPointsF1

/-! ## 1. The generator at the re-sourced key.

  `generateAll` is run on `f1VkResourced` instead of `poseidonVkExec`. The two keys differ only in
  the ELEMENTS of the two commitment arrays (the sizes are 19/8 on both), and the generator's
  output projections are `genFilledOut`'s by `rfl` - the measurement below is the machine-checked
  face of that, and `f1ResOut_eq` is the kernel equality the `generated` clause consumes. -/

/-- The generator run at the re-sourced key and the F1 payload. -/
def f1ResRun : Except Fault GenOut :=
  generateAll Features.solidity poseidonDelta f1VkResourced poseidonConfig f1FilledPayload
    poseidonInputs poseidonFlags

/-- **THE GENERATOR ACCEPTS THE RE-SOURCED KEY.** AXIOM:
    f1ResRun_isOk._native.native_decide.ax_1_1. -/
theorem f1ResRun_isOk : f1ResRun.isOk = true := by native_decide

/-- The accepted output. -/
def f1ResOut : GenOut := f1ResRun.getOk f1ResRun_isOk

/-- **THE RUN'S OUTPUT IS F1's OUTPUT, BY THE KERNEL.** The change of commitment elements does not
    reach any projection the generator returns. -/
theorem f1ResOut_eq : f1ResOut = genFilledOut := rfl

theorem f1ResRun_eq_ok : f1ResRun = .ok genFilledOut := by
  rw [Except.eq_ok_getOk f1ResRun f1ResRun_isOk]
  exact congrArg Except.ok f1ResOut_eq

/-! ## 2. The clauses at `f1PointRenderCN n` -/

noncomputable section

/-- The constructed pairing `pairingF1` is the instance the point render is stated at; it is the
    same term `PayloadPointsF1` used, repeated locally so this module does not perturb the global
    instance search (a second `AdmissiblePairing ... G₁z` instance makes the `blsGT` search
    diverge - `PayloadPointsF1`'s §3 note). -/
local instance : AdmissiblePairing G₁z G2fold G₁z := pairingF1

/-- `ptReadable` at the exhibit codec's encoder, for EVERY carrier element. This is
    `g1CodecZ_g1Valid` (all four `G1CodecLaws` at the real-curve codec, `G1Agreement.lean`) read
    as the `ptReadable` predicate: no hypothesis, no computation at the render. -/
theorem ptReadable_g1zToEip (Q : G₁z) :
    Midfall.LoweringV2.ptReadable (g1zToEip Q) :=
  g1CodecZ_g1Valid Q

/-- **`generated` AT THE RE-SOURCED RENDER.** The run is `f1ResRun`; the payload argument is the
    render's own plan vk, which is the filled payload by F1's fixed point. -/
theorem f1PointRenderCN_generated (n : Nat) :
    Midfall.LoweringV3.GeneratedBy (f1PointRenderCN n) := by
  refine ⟨genFilledOut, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity poseidonDelta f1VkResourced poseidonConfig
    genFilledOut.plan.vk poseidonInputs poseidonFlags = .ok genFilledOut
  rw [genFilledOut_plan_vk_is_the_payload_it_was_given]
  exact f1ResRun_eq_ok

/-- **`inputs` AT THE RE-SOURCED RENDER.** The key's domain is `poseidonVkExec`'s (the re-source
    changes only the commitment arrays), and the inputs/cfg are F1's. -/
theorem f1PointRenderCN_inputs (n : Nat) :
    (f1PointRenderCN n).inputs.numInstances = (f1PointRenderCN n).cfg.numInstances ∧
      (f1PointRenderCN n).inputs.accEncoding = (f1PointRenderCN n).cfg.accumulator ∧
      (f1PointRenderCN n).inputs.k = (f1PointRenderCN n).vk.domain.k ∧
      (f1PointRenderCN n).inputs.truncatedChallenges =
        Features.solidity.truncatedChallenges :=
  poseidonValid_inputs

/-- **THE DECIDABLE BUNDLE AT THE RE-SOURCED RENDER.** The view is `f1Pv` and the model is
    `genFilledOut`'s; the only re-sourced input the bundle reads is `permCommMatchRepaired`, a
    count comparison (19/8 unchanged). AXIOM:
    f1PointRenderCN_deciding_programOkB._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_deciding_programOkB (n : Nat) :
    Midfall.LoweringV3.programOkB (f1PointRenderCN n) = true := by
  show Midfall.LoweringV3.programOkCore f1Pv f1M poseidonConfig.numInstances
    f1VkResourced = true
  native_decide

/-- **THE PROGRAM CLAUSE.** The program is built from `pv`/`model` only, so the three scans and
    the address fit are F1's; the bundle is re-decided above. -/
theorem f1PointRenderCN_program (n : Nat) :
    Midfall.LoweringV3.programOk (f1PointRenderCN n) := by
  refine ⟨f1PointRenderCN_deciding_programOkB n, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.GasCallOk (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasCallOk
  · show Midfall.LoweringV3.GasFree (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasFree
  · show Midfall.LoweringV3.ExitDiscipline (asmOf f1Pv f1M 0 0)
    exact f1_deciding_exitDiscipline
  · show Midfall.LoweringV3.programFits f1Pv f1M
    exact f1_deciding_programFit

/-- **`noWriters` AT THE RE-SOURCED RENDER.** Same program as F1's. -/
theorem f1PointRenderCN_noWriters (n : Nat) :
    Midfall.Yul.Bridge.NoWriters ((f1PointRenderCN n).prog 0 0) := by
  show Midfall.Yul.Bridge.NoWriters (asmOf f1Pv f1M 0 0)
  exact f1_noWriters

/-- **`env` AT THE RE-SOURCED RENDER.** Domain, CS, field constants and delta are unchanged; the
    two pairing-parameter fields are `rfl` at `f1ParamsResourced n` and `pairingF1`; the three
    plan-view fields are F1's. AXIOM:
    f1PointRenderCN_env._native.native_decide.ax_1_1 through ax_1_3. -/
theorem f1PointRenderCN_env (n : Nat) :
    EnvAgrees (f1PointRenderCN n).E (f1PointRenderCN n).vk (f1PointRenderCN n).pv
      (f1PointRenderCN n).params (f1PointRenderCN n).sG2gen := by
  obtain ⟨hmod, htrunc, hd1, _hd2, hbary, homega, horder, _hng2, _hsg2, _hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, ?_⟩, hbary, homega, horder, ?_, rfl, rfl, ?_⟩
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show poseidonVkExec.domain.k = f1Pv.k
    native_decide
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show f1Pv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
    native_decide
  · rw [show (f1PointRenderCN n).pv = f1Pv from f1PointRenderC_pv _ _ _]
    show (f1Pv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr
    native_decide

/-- **THE NINE SCALAR PAYLOAD FIELDS AT THE RE-SOURCED RENDER.** Same payload, same view, same
    plan meta; the fields that read `vk` read its domain/transcript representation, which the
    re-source does not change. Re-decided at the render's computable faces rather than transferred,
    so the key's changed commitment elements are not assumed away. AXIOM:
    f1PointRenderCN_payloadScalars._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_payloadScalars (n : Nat) :
    PayloadScalarHalf (f1PointRenderCN n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.vkDigest =
      frWord poseidonVkExec.transcriptRepr
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numInstances =
      BitVec.ofNat 256 poseidonConfig.numInstances
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.k =
      BitVec.ofNat 256 poseidonVkExec.domain.k
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.nInv =
      frWord (((2 ^ poseidonVkExec.domain.k : ℕ) : Fr blsR))⁻¹
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omega =
      frWord poseidonVkExec.domain.omega
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omegaInv =
      frWord poseidonVkExec.domain.omegaInv
    native_decide
  · show Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.omegaInvToL =
      frWord (poseidonVkExec.domain.omegaInv ^
        genFilledOut.plan.meta_.rotationLast.natAbs)
    native_decide
  · show ((Midfall.LoweringV3.payloadWord f1Pv
        vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (Midfall.LoweringV3.payloadWord f1Pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding poseidonConfig.accumulator
    native_decide
  · show 11 ≤ f1Pv.vk.constants.length
    native_decide

/-- **`WellFormed` AT THE RE-SOURCED KEY.** Every field is a count, a domain fact or a CS fact;
    the re-source changes only the commitment ELEMENTS. AXIOM:
    f1VkResourced_wf._native.native_decide.ax_1_1 through ax_1_3 (plus
    `deciding_supported_degree_eq`). -/
theorem f1VkResourced_wf : f1VkResourced.WellFormed Features.solidity where
  csDegreeMatches := deciding_supported_degree_eq
  chunkLenPositive := by native_decide
  domainConsistent := by native_decide
  permutationCommitmentsMatch := by native_decide
  fixedCommitmentsMatch := by native_decide
  singlePhase := by native_decide
  committedInstancesOn := rfl

/-- **`supported` AT THE RE-SOURCED RENDER.** `wf` is D.2's `WellFormed` (the re-source changes
    the commitment ELEMENTS; every count, domain and CS face is unchanged), `vkPoints` is
    `ptReadable_g1zToEip`, and the layout pair is F1's plan. AXIOM:
    f1PointRenderCN_supported_layout._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_supported (n : Nat) : SupportedV2 (f1PointRenderCN n) := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, _hlay1, _hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, ?_, ⟨?_, ?_⟩,
    ⟨hprod1, hprod2⟩, f1VkResourced_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩
  · intro C _hC
    exact ptReadable_g1zToEip C
  · show genFilledOut.plan.memory.map.WellFormed
    native_decide
  · show genFilledOut.plan.memory.validate.isOk = true
    native_decide

/-- **THE SIX CLAUSES AND THE SCALAR HALF AT THE RE-SOURCED RENDER, PROVED.** -/
theorem f1PointRenderCN_validV3ExceptPayload (n : Nat) :
    ValidV3ExceptPayload (f1PointRenderCN n) :=
  ⟨f1PointRenderCN_generated n, f1PointRenderCN_inputs n, f1PointRenderCN_program n,
    f1PointRenderCN_noWriters n, f1PointRenderCN_env n, f1PointRenderCN_payloadScalars n,
    f1PointRenderCN_supported n⟩

/-- **THE F1-REAL `ValidV3`, FROM THE ONE PAYLOAD DATA STATEMENT.** `hpay` is B3's data input: the
    artifact's NEG_S_G2 bytes are the EIP encoding of `g2foldExp n`. Everything else is proved. -/
theorem f1PointRenderCN_validV3 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n) :=
  (validV3_iff_exceptPayload_and_points (f1PointRenderCN n)).2
    ⟨f1PointRenderCN_validV3ExceptPayload n, f1PointRenderCN_payloadPointHalf n hpay⟩

/-- The residual expressed as an equivalence: at the re-sourced render, `ValidV3` is EXACTLY
    B3's one data statement about the artifact's neg-S-G2 slot. -/
theorem f1PointRenderCN_validV3_iff (n : Nat) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n)
      ↔ Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
          = g2foldToEip (g2foldExp n) := by
  constructor
  · intro h
    exact (f1PointRenderCN_payloadPointHalf_iff n).1
      ((validV3_iff_exceptPayload_and_points (f1PointRenderCN n)).1 h).2
  · intro h
    exact f1PointRenderCN_validV3 n h

end

end Midfall.Instances.ValidV3F1Real

/-! ## Axiom audit -/

#print axioms Midfall.Instances.ValidV3F1Real.f1ResRun_isOk
#print axioms Midfall.Instances.ValidV3F1Real.f1ResRun_eq_ok
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_generated
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_program
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_env
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_supported
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3ExceptPayload
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3
#print axioms Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3_iff
