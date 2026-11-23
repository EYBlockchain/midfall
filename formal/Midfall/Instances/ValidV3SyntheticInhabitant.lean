/-
  Midfall.Instances.ValidV3SyntheticInhabitant

  **B4V3 step 4: `∃ R, ValidV3 R` FROM THE GENERATOR'S ACCEPTED FILLED PAYLOAD.**

  §3-4 of `ValidV3InhabitationF1Completion.lean` proved the re-sourced F1 render valid except for
  the five point fields, and REFUTED two of those five: the artifact payload carries the real
  deployment commitments while the Lean key `poseidonVkExec` carries `1 : G₁z` everywhere, so
  `fixedComms` and `permutationComms` compare different points. The other three name the pairing's
  generators, which are opaque at this carrier.

  This file closes the route WITHOUT weakening `ValidV3` and WITHOUT changing the payload data to
  a shape no generator run accepts. It builds a synthetic `Render` whose two CODEC FIELDS
  (`E.g1.toEip`, `encG2`) are chosen from the payload words - they are ordinary `Render` fields,
  not hypotheses - and keeps every other field real:

    REAL (data carried from the fixture / the generator):
      * `vk`, `cfg`, `inputs`, `flags`, `sG2gen`, `params`, `E.field`, `E.delta` - `poseidonRender`'s,
        unchanged. In particular the domain, the constraint system, the 19 fixed and 8 permutation
        commitment slots and the build inputs are the deployment's.
      * `plan`, `qblocks`, `model` - the three projections of a `generateAll` run, so `generated`
        holds by the same fixed-point argument as F1's.
      * the payload the run is given is `f1FilledPayload` (the accepted filled payload) with two
        indicated normalisations, both DATA choices and both stated at the construction:
          (i) header slots 11-30 (the G1_BASE / G2_BASE / NEG_S_G2_BASE point images) are zeroed;
         (ii) the two commitment lists are nineteen and eight copies of the zero `G1Words`,
              which is the EIP-2537 image of `1 : G₁z`, the point the Lean key actually carries.
        `generateAll` ACCEPTS this payload (`synthRun_isOk`, by native_decide) and carries it back
        out (`synthOut_plan_vk`), so `generated` is the generator's statement about this payload.

    SYNTHETIC (the two codec functions, and only they):
      * `synthCodec.toEip` is the constant map to `g1zToEip 1`, the all-zero 128-byte image. It is
        the honest codec for a `Render` whose every key commitment is `1`; the real codec
        (`g1CodecZ`) differs from it only on points other than `1`, and `ValidV3` never evaluates
        `toEip` at a point the key does not hold.
      * `synthEncG2` is the constant map to the payload's own G2_BASE image, so the two G2 slots
        (which this payload sets equal, both all-zero) agree with it.

  The theorem this file lands is `exists_validV3 : ∃ R : Render blsR G₁z G2fold blsGT, ValidV3 R`.
  It is an inhabitant of the GENERIC hypothesis `ValidV3 R` at a render whose non-codec data is
  real and whose codec fields are stated. It is NOT an inhabitant at `poseidonRender` (refuted,
  `PoseidonValid.poseidonRender_notValid`) and it is NOT a substitution of a fixture into the root:
  `lowering_correct` stays generic in `R` and still takes `hR : ValidV3 R`.

  No frozen file, no vendor file, no hypothesis on `ValidV3`, no new axiom beyond the one
  `native_decide` per decided fact, all named in the docstrings.
-/
import Midfall.Instances.ValidV3InhabitationF1Completion

set_option autoImplicit false

namespace Midfall.Instances.ValidV3SyntheticInhabitant

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1
open Midfall.Instances.ValidV3InhabitationF1Completion

/-! ## 1. The synthetic payload: the accepted filled payload with its point images normalised. -/

/-- The zero `G1Words`: the EIP-2537 image of `1 : G₁z`, which is what `g1zToEip 1` encodes. -/
def zeroG1 : G1Words := ⟨0, 0, 0, 0⟩

/-- **THE SYNTHETIC PAYLOAD.** `f1FilledPayload` (the payload `generateAll` accepts, with the four
    quotient reservation fields filled) with:
    * header slots 11-30 zeroed (the three point images), and
    * the fixed/permutation commitment lists replaced by nineteen/eight zero words.
    Header slots 0-10 - the eleven scalars `PayloadAgrees` compares against the Lean key - are
    untouched. -/
def synthPayload : Halo2VerifyingKey :=
  { f1FilledPayload with
    constants := f1FilledPayload.constants.zipIdx.map fun (c, i) =>
      if 11 ≤ i ∧ i ≤ 30 then (c.1, (0 : Word256)) else c
    fixedComms := List.replicate 19 zeroG1
    permutationComms := List.replicate 8 zeroG1 }

/-- The generator run on the synthetic payload. -/
def synthRun : Except Fault GenOut :=
  generateAll Features.solidity poseidonDelta poseidonVkExec poseidonConfig synthPayload
    poseidonInputs poseidonFlags

/-- **THE GENERATOR ACCEPTS THE SYNTHETIC PAYLOAD.** This is the load-bearing data fact: the four
    quotient reservation fields are the filled ones, so `quotient.rs:202` is not reached; the point
    images are not read by the generator. AXIOM:
    synthRun_isOk._native.native_decide.ax_1_1. -/
theorem synthRun_isOk : synthRun.isOk = true := by native_decide

/-- The accepted output. -/
def synthOut : GenOut := synthRun.getOk synthRun_isOk

theorem synthRun_eq_ok : synthRun = .ok synthOut :=
  Except.eq_ok_getOk synthRun synthRun_isOk

/-- **THE PAYLOAD IS A FIXED POINT OF THE PROJECTION `generated` READS.** The output plan carries
    the payload it was handed, field for field - the ten-field signature of
    `ValidV3InhabitationF1.genFilledOut_plan_vk_is_the_payload_it_was_given`, re-run on the
    normalised payload. AXIOM:
    synthOut_plan_vk_is_the_payload_it_was_given._native.native_decide.ax_1_1. -/
theorem synthOut_plan_vk_is_the_payload_it_was_given : synthOut.plan.vk = synthPayload := by
  have h := (by native_decide :
      (synthOut.plan.vk.constructorPayloadMptr = synthPayload.constructorPayloadMptr ∧
        synthOut.plan.vk.constants = synthPayload.constants ∧
        List.map g1wTup synthOut.plan.vk.fixedComms
          = List.map g1wTup synthPayload.fixedComms ∧
        List.map g1wTup synthOut.plan.vk.permutationComms
          = List.map g1wTup synthPayload.permutationComms ∧
        synthOut.plan.vk.quotientConstOffsetWords
          = synthPayload.quotientConstOffsetWords ∧
        synthOut.plan.vk.quotientConstWords = synthPayload.quotientConstWords ∧
        synthOut.plan.vk.quotientProgramOffsetWords
          = synthPayload.quotientProgramOffsetWords ∧
        synthOut.plan.vk.quotientProgramWords = synthPayload.quotientProgramWords ∧
        synthOut.plan.vk.quotientConstLabels = synthPayload.quotientConstLabels ∧
        synthOut.plan.vk.quotientConstHeaders = synthPayload.quotientConstHeaders))
  rw [Halo2VerifyingKey.mk.injEq]
  exact ⟨h.1, h.2.1, g1wList_inj h.2.2.1, g1wList_inj h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-! ## 2. The plan view and the two synthetic codec fields. -/

/-- The computable model of the synthetic run. -/
def synthM : Model := synthOut.model

/-- The plan view whose `vk` field is the synthetic payload. `planViewOf` reads only `plan.vk`,
    `plan.vkMptr`, `plan.memory`, `plan.proofLayout`, `plan.meta_` and `plan.data`, so replacing
    the vk field leaves the program-side view unchanged; §3 proves it IS the run's own view. -/
def synthPv : PlanView :=
  planViewOf { synthOut.plan with vk := synthPayload } synthM poseidonConfig.accumulator

/-- `planViewOf` reads the vk field: two plans agreeing on `vk` give the same view. Keeping the
    other plan fields fixed is the point - the memory layout is the generator's. -/
theorem planViewOf_vk_congr {plan : LoweringPlan Unit Unit} {m : Model}
    {acc : Option Midfall.Generator.AccumulatorEncoding} {vk : Halo2VerifyingKey}
    (h : plan.vk = vk) :
    planViewOf plan m acc = planViewOf { plan with vk := vk } m acc := by
  simp only [planViewOf]
  rw [h]

/-- **THE SYNTHETIC RENDER.** Every field is a citation except the codec pair, which is chosen from
    the payload words (§ header). The plan/qblocks/model are the generator's output. -/
noncomputable def synthRender : Render blsR G₁z G2fold blsGT where
  E := { g1 := { g1CodecZ with toEip := fun _ => g1zToEip (1 : G₁z) }
         field := poseidonFc
         delta := poseidonDelta
         fewerPointSetsRuntime := false }
  params := poseidonParams
  vk := poseidonVkExec
  sG2gen := poseidonSG2
  encG2 := fun _ => vkG2Words synthPv vkG2BaseSlot
  cfg := poseidonConfig
  inputs := poseidonInputs
  flags := poseidonFlags
  plan := synthOut.plan
  qblocks := synthOut.qblocks
  model := synthOut.model

theorem synthRender_plan : synthRender.plan = synthOut.plan := rfl
theorem synthRender_model : synthRender.model = synthM := rfl
theorem synthRender_vk : synthRender.vk = poseidonVkExec := rfl
theorem synthRender_cfg : synthRender.cfg = poseidonConfig := rfl
theorem synthRender_inputs_eq : synthRender.inputs = poseidonInputs := rfl
theorem synthRender_flags : synthRender.flags = poseidonFlags := rfl
theorem synthRender_params : synthRender.params = poseidonParams := rfl
theorem synthRender_sG2 : synthRender.sG2gen = poseidonSG2 := rfl
theorem synthRender_codec : synthRender.E.g1.toEip = fun _ => g1zToEip (1 : G₁z) := rfl
theorem synthRender_encG2 : synthRender.encG2 = fun _ => vkG2Words synthPv vkG2BaseSlot := rfl

/-- **THE RUN'S OWN VIEW IS THE SYNTHETIC VIEW.** The only difference is that the payload is
    written into the plan's vk field, which the run already carries (`synthOut_plan_vk`). -/
theorem synthRender_pv_eq : synthRender.pv = synthPv := by
  show planViewOf synthOut.plan synthOut.model poseidonConfig.accumulator = synthPv
  unfold synthPv
  exact planViewOf_vk_congr synthOut_plan_vk_is_the_payload_it_was_given

theorem synthRender_prog_eq :
    synthRender.prog 0 0 = asmOf synthPv synthM 0 0 := by
  show asmOf synthRender.pv synthRender.model 0 0 = asmOf synthPv synthM 0 0
  rw [synthRender_pv_eq]
  rfl

/-! ## 3. `generated` - the same fixpoint proof as F1, at the normalised payload. -/

/-- **THE GENERATED CLAUSE.** `generateAll` on the render's own arguments returns `.ok synthOut`
    and `synthOut`'s three projections are the render's three re-sourced fields. -/
theorem synthRender_generated : Midfall.LoweringV3.GeneratedBy synthRender := by
  refine ⟨synthOut, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity poseidonDelta poseidonVkExec poseidonConfig
    synthOut.plan.vk poseidonInputs poseidonFlags = .ok synthOut
  rw [synthOut_plan_vk_is_the_payload_it_was_given]
  exact synthRun_eq_ok

/-! ## 4. The remaining clauses, each at the computable faces. -/

theorem synthRender_inputs :
    synthRender.inputs.numInstances = synthRender.cfg.numInstances ∧
      synthRender.inputs.accEncoding = synthRender.cfg.accumulator ∧
      synthRender.inputs.k = synthRender.vk.domain.k ∧
      synthRender.inputs.truncatedChallenges = Features.solidity.truncatedChallenges :=
  poseidonValid_inputs

/-- The fourteen-conjunct bundle at the synthetic plan/model. AXIOM:
    synth_deciding_programOkB._native.native_decide.ax_1_1. -/
theorem synth_deciding_programOkB :
    Midfall.LoweringV3.programOkB synthRender = true := by
  simp only [Midfall.LoweringV3.programOkB]
  rw [synthRender_pv_eq]
  show Midfall.LoweringV3.programOkCore synthPv synthM poseidonConfig.numInstances
    poseidonVkExec = true
  native_decide

/-- The gas scan, fuel 20000. AXIOM: synth_deciding_gasCallOk._native.native_decide.ax_1_1. -/
theorem synth_deciding_gasCallOk :
    Midfall.LoweringV3.GasCallOk (asmOf synthPv synthM 0 0) :=
  ⟨20000, by native_decide⟩

/-- No `gas()`, fuel 20000. AXIOM: synth_deciding_gasFree._native.native_decide.ax_1_1. -/
theorem synth_deciding_gasFree : Midfall.LoweringV3.GasFree (asmOf synthPv synthM 0 0) :=
  ⟨20000, by native_decide⟩

/-- The one exit scan, fuel 20000. AXIOM:
    synth_deciding_exitDiscipline._native.native_decide.ax_1_1. -/
theorem synth_deciding_exitDiscipline :
    Midfall.LoweringV3.ExitDiscipline (asmOf synthPv synthM 0 0) :=
  ⟨20000, by native_decide⟩

/-- The address fit. AXIOM: synth_deciding_programFit._native.native_decide.ax_1_1. -/
theorem synth_deciding_programFit : Midfall.LoweringV3.programFits synthPv synthM := by
  rw [← Midfall.LoweringV3.programFitB_eq_true_iff]
  native_decide

/-- **THE PROGRAM CLAUSE.** All five halves at the synthetic program. -/
theorem synthRender_program : Midfall.LoweringV3.programOk synthRender := by
  refine ⟨synth_deciding_programOkB, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.GasCallOk (synthRender.prog 0 0)
    rw [synthRender_prog_eq]
    exact synth_deciding_gasCallOk
  · show Midfall.LoweringV3.GasFree (synthRender.prog 0 0)
    rw [synthRender_prog_eq]
    exact synth_deciding_gasFree
  · show Midfall.LoweringV3.ExitDiscipline (synthRender.prog 0 0)
    rw [synthRender_prog_eq]
    exact synth_deciding_exitDiscipline
  · show Midfall.LoweringV3.programFits synthRender.pv synthRender.model
    rw [synthRender_pv_eq]
    exact synth_deciding_programFit

/-- The no-writers clause, fuel 20000. AXIOM:
    synth_deciding_noWriters._native.native_decide.ax_1_1. -/
theorem synthRender_noWriters : Midfall.Yul.Bridge.NoWriters (synthRender.prog 0 0) := by
  rw [synthRender_prog_eq]
  exact ⟨20000, by native_decide⟩

/-- **THE ENV CLAUSE.** Nine fields are `poseidonValid_slots_nine`'s (only `E.field` and the key
    data are read); the three that read the plan view are re-decided at `synthPv` (k = 6,
    numNegLagranges = 9, slot 0 unchanged). AXIOM:
    synth_deciding_env._native.native_decide.ax_1_1 through ax_1_3. -/
theorem synthRender_env :
    EnvAgrees synthRender.E synthRender.vk synthRender.pv synthRender.params synthRender.sG2gen := by
  obtain ⟨hmod, htrunc, hd1, _hd2, hbary, homega, horder, hng2, hsg2, _hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, ?_⟩, hbary, homega, horder, ?_, hng2, hsg2, ?_⟩
  · rw [synthRender_pv_eq]
    show poseidonVkExec.domain.k = synthPv.k
    native_decide
  · rw [synthRender_pv_eq]
    show synthPv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
    native_decide
  · rw [synthRender_pv_eq]
    show (synthPv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr
    native_decide

/-! ## 5. `payload` - the nine scalar fields and the five point fields, all at the synthetic view. -/

/-- The nine scalar fields: header slots 0-10 are the accepted filled payload's, unchanged.
    AXIOM: synth_deciding_payloadScalars._native.native_decide.ax_1_1. -/
theorem synthRender_payloadScalars : PayloadScalarHalf synthRender := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [synthRender_pv_eq]
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.vkDigest =
      frWord poseidonVkExec.transcriptRepr
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.numInstances =
      BitVec.ofNat 256 poseidonConfig.numInstances
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.k =
      BitVec.ofNat 256 poseidonVkExec.domain.k
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.nInv =
      frWord (((2 ^ poseidonVkExec.domain.k : ℕ) : Fr blsR))⁻¹
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.omega =
      frWord poseidonVkExec.domain.omega
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.omegaInv =
      frWord poseidonVkExec.domain.omegaInv
    native_decide
  · show Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.omegaInvToL =
      frWord (poseidonVkExec.domain.omegaInv ^ synthOut.plan.meta_.rotationLast.natAbs)
    native_decide
  · show ((Midfall.LoweringV3.payloadWord synthPv
        vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (Midfall.LoweringV3.payloadWord synthPv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
      accWordsOfEncoding poseidonConfig.accumulator
    native_decide
  · show 11 ≤ synthPv.vk.constants.length
    native_decide

/-- `G1_BASE` at the synthetic view: the slot's four words are zero and the codec maps every point
    to the all-zero image. AXIOM: synth_deciding_g1Base._native.native_decide.ax_1_1. -/
theorem synth_g1Base : vkG1Words synthPv vkG1BaseSlot = g1zToEip (1 : G₁z) := by
  native_decide

/-- `G2_BASE`: the codec is the constant map to the slot's own image, so the field is `rfl`. -/
theorem synth_g2Base : vkG2Words synthPv vkG2BaseSlot =
    (fun _ => vkG2Words synthPv vkG2BaseSlot) bls12_381Pairing.g₂ := rfl

/-- `NEG_S_G2_BASE`: both G2 slots are zeroed, so the two images coincide. AXIOM:
    synth_deciding_negSG2._native.native_decide.ax_1_1. -/
theorem synth_negSG2 : vkG2Words synthPv vkNegSG2BaseSlot =
    (fun _ => vkG2Words synthPv vkG2BaseSlot) (synthRender.sG2gen⁻¹) := by
  show vkG2Words synthPv vkNegSG2BaseSlot = vkG2Words synthPv vkG2BaseSlot
  native_decide

/-- **THE FIXED COMMITMENTS.** Both sides are nineteen copies of the all-zero 128-byte image: the
    payload's words are zero by construction, and the Lean key's nineteen commitments are all
    `1 : G₁z`, which the chosen codec sends to that image. AXIOM:
    synth_deciding_fixedComms._native.native_decide.ax_1_1. -/
theorem synth_fixedComms :
    synthPv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.fixedCommitments.toList.map (fun _ => g1zToEip (1 : G₁z)) := by
  native_decide

/-- **THE PERMUTATION COMMITMENTS**, the same fact at eight words. AXIOM:
    synth_deciding_permutationComms._native.native_decide.ax_1_1. -/
theorem synth_permutationComms :
    synthPv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.permutation.commitments.toList.map (fun _ => g1zToEip (1 : G₁z)) := by
  native_decide

/-- **THE POINT HALF AT THE SYNTHETIC RENDER.** Five fields, each at the codec the render declares:
    two by the codec's constancy, two by the zeroed images, one (`fixedComms`) by both. -/
theorem synthRender_payloadPoints : PayloadPointHalf synthRender := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show vkG1Words synthRender.pv vkG1BaseSlot = g1zToEip (1 : G₁z)
    rw [synthRender_pv_eq]
    exact synth_g1Base
  · -- `encG2` is the constant map to this slot's own image, so both sides are one term.
    show vkG2Words synthRender.pv vkG2BaseSlot = vkG2Words synthPv vkG2BaseSlot
    rw [synthRender_pv_eq]
  · show vkG2Words synthRender.pv vkNegSG2BaseSlot =
      (fun _ => vkG2Words synthPv vkG2BaseSlot) (poseidonSG2⁻¹)
    rw [synthRender_pv_eq]
    exact synth_negSG2
  · show synthRender.pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.fixedCommitments.toList.map (fun _ => g1zToEip (1 : G₁z))
    rw [synthRender_pv_eq]
    exact synth_fixedComms
  · show synthRender.pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.permutation.commitments.toList.map (fun _ => g1zToEip (1 : G₁z))
    rw [synthRender_pv_eq]
    exact synth_permutationComms

/-- **THE PAYLOAD CLAUSE.** The split theorem of §1 of the completion file puts the nine scalar
    fields and the five point fields back into the frozen `PayloadAgrees`. -/
theorem synthRender_payload : Midfall.LoweringV3.PayloadAgrees synthRender :=
  (payloadAgrees_iff_scalars_and_points synthRender).2
    ⟨synthRender_payloadScalars, synthRender_payloadPoints⟩

/-- **THE SUPPORTED CLAUSE.** Shape, `wf`, `vkPoints` and the flags read only the key/cfg; the
    layout pair is the generator's plan. `vkPoints` is the codec's own fact: every commitment is
    sent to the all-zero image, which decodes to `(0,0)` and the MSM accepts it. AXIOMS:
    synth_deciding_supportedLayout._native.native_decide.ax_1_1, and the two
    `g1Of?/g1PointMsmValid` evaluations inside `vkPoints`. -/
theorem synthRender_supported : SupportedV2 synthRender := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, _hlay1, _hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, ?_, ⟨?_, ?_⟩,
    ⟨hprod1, hprod2⟩, deciding_supported_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩
  · intro C _hC
    show Midfall.LoweringV2.ptReadable (g1zToEip (1 : G₁z))
    exact ⟨(0, 0), by native_decide, by native_decide⟩
  · show synthOut.plan.memory.map.WellFormed
    native_decide
  · show synthOut.plan.memory.validate.isOk = true
    native_decide

/-! ## 6. THE INHABITANT. -/

/-- **`ValidV3` IS INHABITED.** Every clause of the generic headline hypothesis at the synthetic
    render: `generated` (the generator's own output), `inputs`, `program`, `noWriters`, `env`,
    `payload` (nine scalar + five point fields) and `supported`. -/
theorem synthRender_valid : Midfall.LoweringV3.ValidV3 synthRender :=
  ⟨synthRender_generated, synthRender_inputs, synthRender_program, synthRender_noWriters,
    synthRender_env, synthRender_payload, synthRender_supported⟩

/-- **THE DELIVERABLE: `∃ R, ValidV3 R` - GENERIC NON-VACUITY, NOT F1 `Done`.**

    A render carrying the deployment's key, constraint system, configuration, inputs and flags,
    with the generator's own plan/qblocks/model for a payload it ACCEPTS, and two CODEC FIELDS
    chosen from that payload's words, satisfies the headline hypothesis with nothing added.

    This is explicitly NOT the F1 deliverable: the payload's three point images and its two
    commitment lists are normalised so the codec can be the constant image the key's all-`1`
    commitments require (§ header, (i)-(ii)). The F1 render's own point half is REFUTED at
    `fixedComms`/`permutationComms` (`ValidV3InhabitationF1Completion.f1_fixedComms_false`), and
    closing THAT is B3's data lane. What this theorem establishes is that the seven-clause text
    and the `PayloadAgrees` clause are jointly satisfiable by a real generator run - the
    non-vacuity property the headline needs, and not a claim about the artifact's commitments. -/
theorem exists_validV3 :
    ∃ R : Render blsR G₁z G2fold blsGT, Midfall.LoweringV3.ValidV3 R :=
  ⟨synthRender, synthRender_valid⟩

/-! ## 7. THE AXIOMS THIS FILE CARRIES (one per decided fact, all named above). -/

#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRun_isOk
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthOut_plan_vk_is_the_payload_it_was_given
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_generated
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synth_deciding_programOkB
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_program
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_env
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_payloadScalars
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_payloadPoints
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_payload
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_supported
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.synthRender_valid
#print axioms Midfall.Instances.ValidV3SyntheticInhabitant.exists_validV3

end Midfall.Instances.ValidV3SyntheticInhabitant
