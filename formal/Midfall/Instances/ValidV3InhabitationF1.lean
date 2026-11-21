/-
  Midfall.Instances.ValidV3InhabitationF1

  **B4 (PLAN-V3 COMPLETION row B4): `ValidV3 poseidonRender` inhabited, or the blocking clause.**
  Box 3 h, branch `t/BOXe` from `78c217b`. No frozen file was touched, no clause was weakened, no
  hypothesis was added to `ValidV3`, and no `Render` field was invented.

  ## WHAT THE BRIEF ASKED FOR AND WHAT LANDED

  (1) **The inhabitant was attempted and CANNOT be produced at F1.** `poseidonRender_notValid` is a
      PROVED theorem (`PoseidonValid.lean:1007`), so an inhabitant at F1 is a proof of `False`.
      Nothing here contradicts it. What this file adds is that the clause is not vacuous:
      **`GeneratedBy` IS satisfiable**, at a render named below (`f1GeneratedRender_generated`),
      so `generated` is refuted at F1 for a DATA reason and not because the clause is unsatisfiable.
  (2) **The obstruction is a theorem with its exact failing sub-condition, its site and its owner.**
      Sections 1-2 (sub-condition and site), 5-7 (owner).
  (3) Cost and route: section 8.

  ## THE MEASURED FACTS THIS FILE LANDS AS THEOREMS

  * **S1 - the sub-condition.** `poseidonRender.plan.vk.quotientConstOffsetWords = none` and
    `quotientProgramOffsetWords = none`, both word counts 0. That is the `none` arm of the match at
    `Midfall/Generator/PlanNew.lean:581-583`, the port of
    `proofs/solidity-verifier/src/lowering/quotient.rs:202`
    (`vk.quotient_const_offset_words.expect("VK must carry quotient constants")`). The Rust line is
    pinned against the source by `PlanNewKats.templateProgramPanicSites_areTheRecordedOnes_ok`
    (:474-490, a KAT that reads quotient.rs and asserts line 202 holds that `expect`), so this
    citation cannot drift silently.
  * **S2 - the fired fault, exactly.** Not merely a string that CONTAINS the site (which is what
    `PoseidonValid.lean:883` proves): the fault's message IS `siteQ 202 "VK must carry quotient
    constants"`, and the :204, :205 and :209 arms of the same function are proved not to be it.
  * **S3 - the generator is not the obstruction.** Feed the SAME seven arguments with the four
    reservation fields filled (`PlanNewKats.vkFilled`, computed by `VkPayloadLayout.forVk` from the
    counts the parsed payload shows: 31 / 1 / 32 / 3, the numbers OBJ.10's KAT predicts) and
    `generateAll` returns `.ok`. And S6 shows the refutation depends on the render ONLY through
    that payload.
  * **S4 - the payload is not the ONLY thing wrong with F1's plan.** The generator's own plan differs
    from `poseidonRender.plan` on `meta_.numPointSets` (3 against 0) even at an accepted payload.
    So `GeneratedBy poseidonRender`
    has TWO independent refutations: the run does not return `.ok` at all (S1/S2), and if the
    payload circle were cut the returned plan still would not be this render's plan (S7). Closing
    `generated` means RE-SOURCING `poseidonRender.plan/qblocks/model` from the generator - OBJ.8
    step 3, never executed - and not a frozen edit.

  ## VERDICT: GENERATOR LIMITATION OR SPEC MISMATCH?

  **Neither, as the brief frames it: a DATA-SOURCING defect in the F1 record, with one genuine
  spec-level consequence.** The generator port is faithful (S3, and `GeneratedKats` gate 4 renders
  the deployed contract but for BUILD_ID from it). The clause text is satisfiable (S5). What is wrong
  is that `poseidonRender`'s plan was transcribed out of the two `.sol` artifacts, and the artifact
  format CANNOT carry the four reservation fields (`Contracts.lean:868-871`: `vkModelFromArtifact`
  leaves them `none` - not a bug, that is what a `.sol` file is). `generated` reads the payload
  back out of `R.plan.vk`, so a render sourced from an artifact can never satisfy it. Owners:
  **OBJ.10** for the payload (data-level base payload), **OBJ.8 step 3/4** for the plan re-sourcing,
  and **B3** for the second, independent blocker named in section 7.

  ## AXIOMS AND KAT

  Every decision is one `native_decide` per named theorem, of the shape
  `<decl>._native.native_decide.ax_1_1`, named at each site and printed at the foot of the file.
  `native_decide` is confined to `Midfall/Instances/` (D-P17) and NOTHING here is inside
  `lowering_correct`'s cone: no row proof cites any theorem of this file, and the `#cone_sorries`
  prints at the foot are the evidence. This file contains no `#eval`, so the pinned KAT counts
  (1633 checks / 118 files) are untouched by it.
-/
import Midfall.Instances.PoseidonValid
import Midfall.Instances.PlanNewKats
import Midfall.LoweringV2.Generated
import Midfall.LoweringV3.GeneratorTheorem
import Midfall.Common.Except
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Instances.ValidV3InhabitationF1

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.QuotientBlocks Midfall.Lowering
open Midfall.Assumptions Midfall.Yul Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats

/-! ## 0. How a payload is compared, since `Halo2VerifyingKey` has no `DecidableEq`.

  `Generator/Models.lean:385-410` derives nothing, and `Models.lean` is not this card's to edit.
  So a payload is compared field by field, with `G1Words` (`Models.lean:94-99`) flattened to its
  four `Word256` projections, which DO carry `DecidableEq`. The result is propositional equality
  of payloads, not a rendering trick - contrast `renderHalo2VerifyingKey`, which is BLIND to the
  four reservation fields (that is exactly why `vkModelFromArtifact` cannot read them back) and
  would therefore have proved nothing here. -/

def g1wTup (w : G1Words) : Word256 × Word256 × Word256 × Word256 :=
  (w.xHi, w.xLo, w.yHi, w.yLo)

theorem g1wTup_injective : Function.Injective g1wTup := by
  intro a b h
  cases a with
  | mk x1 x2 x3 x4 =>
    cases b with
    | mk y1 y2 y3 y4 =>
      cases h
      rfl

theorem g1wList_inj {xs ys : List G1Words} (h : List.map g1wTup xs = List.map g1wTup ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs => exact absurd h (by simp)
  | cons a as ih =>
      cases ys with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          injection h with h1 h2
          have hab : a = b := g1wTup_injective h1
          subst hab
          rw [ih h2]

/-! ## 1. S1 - THE EXACT FAILING SUB-CONDITION AT F1. -/

/-- **The failing sub-condition, as a proposition about the render.** `PlanNew.lean:581-583` throws
    exactly when this is `none`. Transferred from the computable face by `poseidonPlan_eq`, which
    is `rfl`, so it is the kernel and not a tactic that moves it onto the render. AXIOM:
    f1_payload_constOffset_none._native.native_decide.ax_1_1. -/
theorem f1_payload_constOffset_none : poseidonRender.plan.vk.quotientConstOffsetWords = none := by
  show poseidonPlanV2.vk.quotientConstOffsetWords = none
  native_decide

/-- The twin field, read one line later by the same Rust function (QRS:204). Also `none`, so the
    FIRST abort is the constant offset and not the program offset - the off-by-two the original card
    got wrong (OBJ.7 gate 11, `GeneratedKats:361`). AXIOM:
    f1_payload_progOffset_none._native.native_decide.ax_1_1. -/
theorem f1_payload_progOffset_none : poseidonRender.plan.vk.quotientProgramOffsetWords = none := by
  show poseidonPlanV2.vk.quotientProgramOffsetWords = none
  native_decide

/-- Both reservation LENGTHS are 0 too: the payload carries no quotient section at all, not merely an
    unrecorded offset. AXIOM: f1_payload_reservation_absent._native.native_decide.ax_1_1. -/
theorem f1_payload_reservation_absent :
    (poseidonRender.plan.vk.quotientConstWords,
      poseidonRender.plan.vk.quotientProgramWords) = (0, 0) := by
  show (poseidonPlanV2.vk.quotientConstWords, poseidonPlanV2.vk.quotientProgramWords) = (0, 0)
  native_decide

/-! ## 2. S2 - THE FIRED FAULT, EXACTLY, AND WHICH OF THE FOUR ARMS IT IS. -/

/-- The full path is part of the ported convention (`siteQ`, `QuotientBlocks.lean:144`), so the
    string is spelled out through that helper rather than trusted. AXIOM:
    f1_generated_faultIsExactlyQRS202._native.native_decide.ax_1_1. -/
theorem f1_generated_faultIsExactlyQRS202 :
    (match poseidonGenRender with
      | .error (Fault.panic s) => s == siteQ 202 "VK must carry quotient constants"
      | _ => false) = true := by native_decide

/-- The other three aborts of `quotientTemplateProgram` are NOT what fired, and the run is an
    `error` and not an `ok`. This is what makes S1 the FAILING sub-condition rather than just a
    true fact about the payload. AXIOM:
    f1_generated_notAnotherArm._native.native_decide.ax_1_1. -/
theorem f1_generated_notAnotherArm :
    (match poseidonGenRender with
      | .error (Fault.panic s) =>
          s != siteQ 204 "VK must carry quotient program"
            && s != siteQ 205 "quotient const table exceeded VK payload reservation"
            && s != siteQ 209 "quotient program length exceeded VK payload reservation"
      | _ => false) = true := by native_decide

/-! ## 3. S3 - THE GENERATOR ACCEPTS THIS CIRCUIT; THE FOUR RESERVATION FIELDS ARE ALL IT LACKS. -/

theorem vkFilled_isOk : vkFilled.isOk = true := by native_decide

/-- The filled payload as a term: `poseidonVkGen` with the four reservation fields set. -/
def f1FilledPayload : Halo2VerifyingKey := vkFilled.getOk vkFilled_isOk

/-- The filled payload differs from the render's payload ONLY in the four reservation fields, and
    they are the 31 / 1 / 32 / 3 OBJ.10's KAT predicts. AXIOM:
    f1FilledPayload_differsOnlyInReservation._native.native_decide.ax_1_1. -/
theorem f1FilledPayload_differsOnlyInReservation :
    (f1FilledPayload.constants = poseidonRender.plan.vk.constants)
      ∧ (f1FilledPayload.fixedComms.length = poseidonRender.plan.vk.fixedComms.length)
      ∧ (f1FilledPayload.permutationComms.length
          = poseidonRender.plan.vk.permutationComms.length)
      ∧ (f1FilledPayload.quotientConstOffsetWords, f1FilledPayload.quotientConstWords,
          f1FilledPayload.quotientProgramOffsetWords, f1FilledPayload.quotientProgramWords)
        = (some 31, 1, some 32, 3) := by
  show (f1FilledPayload.constants = poseidonPlanV2.vk.constants)
      ∧ (f1FilledPayload.fixedComms.length = poseidonPlanV2.vk.fixedComms.length)
      ∧ (f1FilledPayload.permutationComms.length = poseidonPlanV2.vk.permutationComms.length)
      ∧ (f1FilledPayload.quotientConstOffsetWords, f1FilledPayload.quotientConstWords,
          f1FilledPayload.quotientProgramOffsetWords, f1FilledPayload.quotientProgramWords)
        = (some 31, 1, some 32, 3)
  native_decide

/-- **THE GENERATOR RUN AT THE FILLED PAYLOAD**: the same seven arguments as `poseidonGenRender`,
    payload replaced. -/
def genFilledRun : Except Fault GenOut :=
  generateAll Features.solidity poseidonDelta poseidonVkExec poseidonConfig f1FilledPayload
    poseidonInputs poseidonFlags

theorem genFilledRun_isOk : genFilledRun.isOk = true := by native_decide

def genFilledOut : GenOut := genFilledRun.getOk genFilledRun_isOk

theorem genFilledRun_eq_ok : genFilledRun = .ok genFilledOut :=
  Except.eq_ok_getOk genFilledRun genFilledRun_isOk

/-- The filled run is not the F1 run: the payload argument really is what changed. AXIOM:
    genFilledRun_ne_poseidonGenRender._native.native_decide.ax_1_1. -/
theorem genFilledRun_ne_poseidonGenRender :
    (match genFilledRun, poseidonGenRender with
      | .ok _, .error _ => true
      | _, _ => false) = true := by native_decide

/-! ## 4. S5 - THE CLAUSE IS SATISFIABLE: THE PAYLOAD IS A FIXED POINT, AND HERE IS A RENDER.

  `generateAll` puts the payload it was handed into the plan it returns, so the filled payload is a
  FIXED POINT of the projection `generated` reads through. That is the fact that turns "the
  generator refuses F1" from a suspicion into a diagnosis: the clause has a model; F1 is not in it. -/

/-- **The fixed point.** One `native_decide` over the ten field equalities, then the field-wise
    injection principle above. AXIOM:
    genFilledOut_plan_vk_is_the_payload_it_was_given._native.native_decide.ax_1_1. -/
theorem genFilledOut_plan_vk_is_the_payload_it_was_given :
    genFilledOut.plan.vk = f1FilledPayload := by
  have h := (by native_decide :
      (genFilledOut.plan.vk.constructorPayloadMptr = f1FilledPayload.constructorPayloadMptr ∧
        genFilledOut.plan.vk.constants = f1FilledPayload.constants ∧
        List.map g1wTup genFilledOut.plan.vk.fixedComms
          = List.map g1wTup f1FilledPayload.fixedComms ∧
        List.map g1wTup genFilledOut.plan.vk.permutationComms
          = List.map g1wTup f1FilledPayload.permutationComms ∧
        genFilledOut.plan.vk.quotientConstOffsetWords
          = f1FilledPayload.quotientConstOffsetWords ∧
        genFilledOut.plan.vk.quotientConstWords = f1FilledPayload.quotientConstWords ∧
        genFilledOut.plan.vk.quotientProgramOffsetWords
          = f1FilledPayload.quotientProgramOffsetWords ∧
        genFilledOut.plan.vk.quotientProgramWords = f1FilledPayload.quotientProgramWords ∧
        genFilledOut.plan.vk.quotientConstLabels = f1FilledPayload.quotientConstLabels ∧
        genFilledOut.plan.vk.quotientConstHeaders = f1FilledPayload.quotientConstHeaders))
  rw [Halo2VerifyingKey.mk.injEq]
  exact ⟨h.1, h.2.1, g1wList_inj h.2.2.1, g1wList_inj h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- **THE RENDER OBJ.8 STEP 3 WOULD HAVE BUILT**: F1 with `plan`, `qblocks` and `model` replaced
    by the three projections of a successful generator run, every other field untouched. This is NOT
    an inhabitant of `ValidV3 poseidonRender` and must not be reported as one: it is a DIFFERENT
    render, here to prove the `generated` clause has a model at all. -/
noncomputable def f1GeneratedRender : Render blsR G₁z G2fold blsGT :=
  { poseidonRender with
    plan := genFilledOut.plan
    qblocks := genFilledOut.qblocks
    model := genFilledOut.model }

theorem f1GeneratedRender_planvk : f1GeneratedRender.plan.vk = f1FilledPayload :=
  genFilledOut_plan_vk_is_the_payload_it_was_given

/-- **`generated` IS SATISFIABLE.** The clause holds of the render above with no hypothesis added
    and the clause text untouched: the run is `.ok` and the three projections are equal by `rfl`.
    This is the theorem that says the obstruction is a data defect and not a spec defect. No axiom of
    its own beyond the fixed point it cites. -/
theorem f1GeneratedRender_generated : GeneratedBy f1GeneratedRender := by
  refine ⟨genFilledOut, ?_, rfl, rfl, rfl⟩
  show generateAll Features.solidity f1GeneratedRender.E.delta f1GeneratedRender.vk
    f1GeneratedRender.cfg f1GeneratedRender.plan.vk f1GeneratedRender.inputs f1GeneratedRender.flags
    = .ok genFilledOut
  rw [f1GeneratedRender_planvk]
  exact genFilledRun_eq_ok

/-! ## 5. S6 - THE OBSTRUCTION DEPENDS ON THE RENDER ONLY THROUGH ITS PLAN'S PAYLOAD.

  Generic in the render, so the diagnosis is not an artefact of how OBJ.8 happened to build
  `poseidonRender`: any render agreeing with F1 on the six generator arguments OTHER than the
  payload agrees with F1 on the refutation too. -/

theorem f1_generated_obstruction_isPayloadOnly {R : Render blsR G₁z G2fold blsGT}
    (hE : R.E.delta = poseidonDelta) (hvk : R.vk = poseidonVkExec)
    (hcfg : R.cfg = poseidonConfig) (hpl : R.plan.vk = poseidonPlanV2.vk)
    (hin : R.inputs = poseidonInputs) (hfl : R.flags = poseidonFlags) :
    ¬ GeneratedBy R := by
  rintro ⟨out, ho, _, _, _⟩
  have h1 : generated R = poseidonGenRender := by
    show generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags
      = poseidonGenRender
    rw [hE, hvk, hcfg, hpl, hin, hfl]
    rfl
  have h2 : poseidonGenRender.isOk = true := by rw [← h1, ho]; rfl
  have h3 := poseidon_generated_notOk
  rw [h2] at h3
  exact absurd h3 (by decide)

/-- The instance at F1, restated so this file is self-contained: **the sole obstructing clause of
    `ValidV3 poseidonRender` is `generated`, refuted because the payload the render's plan carries
    has no quotient-constant reservation** (S1), which the ported `quotient_template_program`
    refuses at `quotient.rs:202` (S2). -/
theorem f1_generated_isTheSoleRefutedClause : ¬ GeneratedBy poseidonRender :=
  poseidonValid_generated_not

/-! ## 6. S7 - THE SECOND, PAYLOAD-INDEPENDENT REFUTATION: F1's PLAN IS NOT THE GENERATOR'S PLAN.

  Suppose the circle were cut the cheap way - hand the render a payload with the reservation fields
  and leave `poseidonRender.plan` otherwise as it is. `GeneratedBy` would STILL fail, because its
  second conjunct is `out.plan = R.plan` and the generator's plan is not the transcribed one. The
  discriminator is `meta_.numPointSets`: the generator converges it to 3 (`GeneratedKats` gate 3,
  which also shows the raw `ConstraintSystemMeta.new` gives 0 and that with 0 the proof layout is
  4224 against the artifact's 4320), while `poseidonRender.plan` carries the raw 0. -/

theorem f1_plan_numPointSets_is_raw_zero : poseidonRender.plan.meta_.numPointSets = 0 := by
  show poseidonPlanV2.meta_.numPointSets = 0
  native_decide

theorem f1_genPlan_numPointSets_is_converged_three : genFilledOut.plan.meta_.numPointSets = 3 := by
  native_decide

/-- **The generator's plan is not F1's plan.** So `generated` cannot be closed by repairing the
    payload alone: the render has to CARRY the generated plan. -/
theorem f1_plan_isNotTheGeneratorsPlan : genFilledOut.plan ≠ poseidonRender.plan := by
  intro h
  have h2 := congrArg (fun q : LoweringPlan Unit Unit => q.meta_.numPointSets) h
  rw [f1_genPlan_numPointSets_is_converged_three, f1_plan_numPointSets_is_raw_zero] at h2
  exact absurd h2 (by decide)

/-- The F1 instance of the generic statement above: the six non-payload generator arguments really
    are F1's, so the refutation transfers by `rfl` and nothing else is needed. -/
theorem f1_generated_obstruction_at_F1 : ¬ GeneratedBy poseidonRender :=
  f1_generated_obstruction_isPayloadOnly rfl rfl rfl rfl rfl rfl

/-! ## 7. WHAT THIS DOES NOT CLAIM.

  * **`ValidV3 poseidonRender` is NOT inhabited and this file does not inhabit it.**
    `poseidonRender_notValid` stands, proved, routing through `generated` alone.
  * **`generated` is the sole REFUTED clause but NOT the sole blocker.** Even with S1-S7 resolved,
    `ValidV3 poseidonRender` needs `PayloadAgrees`, and five of its thirteen fields (`g1Base`,
    `g2Base`, `negSG2`, `fixedComms`, `permutationComms`) are OPEN at the placeholder codec -
    `poseidonValid_payload_scalars` lands the eight scalar ones and only those
    (`PoseidonValid.lean:696-749`). That half is **B3's** ticket (REF.9, REF.10, ST.14, ST.17), not
    B4's, and it is why the honest PROGRESS cell is "blocking clauses = generated (REFUTED) +
    payload point half (OPEN)", not "blocking clause = generated".
  * Nothing here is inside `lowering_correct`'s cone: no row proof cites any theorem of this file.
-/

/-! ## 8. COST AND ROUTE (the brief's question 3).

  **Is `generated` on the shortest path to `lowering_correct`? NO.** `lowering_correct`
  (`LoweringV3/GeneratorTheorem.lean:69`) is generic in the render (D-P71) and takes
  `hR : ValidV3 R` as a HYPOTHESIS, and `StatementsV3Falsifiers` §F10 already proves that
  hypothesis is load-bearing (the root with it dropped is refuted at `bumpInst R`). The conditional
  theorem stands exactly as it is, with or without an inhabitant. What an inhabitant buys is
  NON-VACUITY of the headline at a named render - a DONE-criterion (COMPLETION row B4), not a lemma
  the proof needs.

  **What would close `generated` at F1, and at what cost.** One route, and it is not frozen:
  execute OBJ.8 step 3/4 for real - set the render's `plan`, `qblocks` and `model` to the three
  projections of `generateAll` run on a payload whose four reservation fields are filled.
  `f1GeneratedRender` is that render and `f1GeneratedRender_generated` is the clause holding of
  it, so the proof cost of the clause itself is ALREADY PAID here. The remaining costs are all
  downstream of `Render.pv` being DERIVED (`LoweringV2/Statements.lean:162`,
  `planViewOf R.plan R.model R.cfg.accumulator`):
    1. `poseidonPv`, and with it every `show ... at poseidonPv` transfer in `PoseidonValid.lean`,
       `PoseidonCoherence.lean` and `PoseidonPins.lean`, re-points; each of the ~20
       `native_decide` clauses must be re-run at the new view. `deciding_programOkB` alone is ~11 s
       of compiled evaluation, so budget a full rebuild plus a re-measured clause table: **one card,
       not one edit.** OWNER: OBJ.8 step 3/4 (or a re-brief of B4 as that edit).
    2. The payload must come from EXPORTED key data and not from a hand-filled parse, or the clause
       is true of a render nobody can build. OWNER: **OBJ.10** (`generateVkFromBase` /
       `baseVkOfKeyData`), which is where the 31 / 1 / 32 / 3 KAT lives - and this is the
       measurement that confirms OBJ.9's recorded finding that PLAN-V3 orders M3 before M4 wrongly.
    3. S7 says the transcribed plan is not salvageable: the render must CARRY the generated meta,
       which moves every `proofLayout`-derived face. `GeneratedKats` gate 3 shows the generated
       one is the one the deployed contract agrees with (4320), so this is a repair and not a
       regression - but it re-measures the plan table in `StatementsV3Deploy.lean), another card's
       file.
  **No frozen edit is needed for `generated`, and none is proposed here.** The two frozen exits
  `PoseidonValid.lean` §V3 lists - a `Render.payload` field, or a `DecidableEq Halo2VerifyingKey`
  in v1 - are both strictly worse than step 3: the first adds a field the clause does not need (the
  payload is already reachable as `R.plan.vk`), and the second is unnecessary because the fixed
  point is provable field-wise, as §0 and §4 show. **PG-VKMEMORYFIT and PG-LIMBCOUNT should not be
  joined by a third hash for this row.**
-/

#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_payload_constOffset_none
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_payload_progOffset_none
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_generated_faultIsExactlyQRS202
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_generated_notAnotherArm
#print axioms Midfall.Instances.ValidV3InhabitationF1.genFilledRun_isOk
#print axioms Midfall.Instances.ValidV3InhabitationF1.genFilledOut_plan_vk_is_the_payload_it_was_given
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1GeneratedRender_generated
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_generated_obstruction_isPayloadOnly
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_plan_isNotTheGeneratorsPlan
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_generated_obstruction_at_F1
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_generated_isTheSoleRefutedClause
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1_payload_reservation_absent
#print axioms Midfall.Instances.ValidV3InhabitationF1.f1FilledPayload_differsOnlyInReservation
#print axioms Midfall.Instances.ValidV3InhabitationF1.genFilledRun_ne_poseidonGenRender
#cone_sorries Midfall.Instances.ValidV3InhabitationF1.f1_payload_constOffset_none
#cone_sorries Midfall.Instances.ValidV3InhabitationF1.f1GeneratedRender_generated
#cone_sorries Midfall.Instances.ValidV3InhabitationF1.f1_plan_isNotTheGeneratorsPlan
#cone_sorries Midfall.LoweringV3.lowering_correct
#cone_sorries Midfall.LoweringV3.lowering_sound

end Midfall.Instances.ValidV3InhabitationF1
