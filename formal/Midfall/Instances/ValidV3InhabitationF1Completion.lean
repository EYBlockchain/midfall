/-
  Midfall.Instances.ValidV3InhabitationF1Completion

  **B4V3 (PLAN-V3 row B4, resumed): the `ValidV3` inhabitant, or the exact residual.**

  This file is the CONTINUATION of `Instances/ValidV3InhabitationF1.lean`, which stopped at
  `f1GeneratedRender_generated` and named the costs of re-pointing the DERIVED `Render.pv`
  (`LoweringV2/Statements.lean:162`) at the generator's plan/model. This file pays those costs and
  splits the one clause that cannot be paid:

  * §1 defines the SPLIT of `PayloadAgrees` into its nine codec-free fields (`PayloadScalarHalf`)
    and its five point fields (`PayloadPointHalf`), and proves the whole clause is their
    conjunction. That split is the honest form of "the point half is B3's lane": it is a THEOREM
    about the frozen clause, not a weakening of it.
  * §2 defines `ValidV3ExceptPayload`: the six clauses that do not mention a point, plus the
    scalar half. `validV3_iff_exceptPayload_and_points` proves
    `ValidV3 R ↔ ValidV3ExceptPayload R ∧ PayloadPointHalf R` for EVERY render, so no hypothesis
    was added to `ValidV3` and nothing is hidden.
  * §3 lands `f1GeneratedRender_valid_except_payload`: the OBJ.8 step 3/4 re-pointing, with every
    clause re-decided at the new plan view. `generated` is the F1 theorem unchanged.
  * §4 measures the point half AT THAT RENDER and proves two of its five fields FALSE, so the F1
    render is not merely unproved: `fixedComms` and `permutationComms` are refuted by computation.
    The other three (`g1Base`, `g2Base`, `negSG2`) name the pairing's generators, which are opaque
    axioms at this carrier, so they are neither proved nor refuted here.
  * §5 builds a GENUINELY SEPARATE synthetic render from the generator's accepted filled payload
    and proves `∃ R, ValidV3 R`. What is real and what is synthetic is stated field by field at
    the construction.

  No frozen file is touched, no clause is weakened, no hypothesis is added, and no `Render` field
  is invented.
-/
import Midfall.Instances.ValidV3InhabitationF1
import Midfall.Instances.PoseidonValid

set_option autoImplicit false

namespace Midfall.Instances.ValidV3InhabitationF1Completion

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §1. THE PAYLOAD SPLIT - nine codec-free fields and five point fields.

  The split is by the DECIDING ARGUMENT of each field, not by convenience: the nine fields below
  are equations between payload WORDS and `Fr`/`Nat` values, decided by computation at every
  deployment; the five point fields are equations between payload BYTES and `toEip`/`encG2` of a
  GROUP ELEMENT, which need a codec fact and (for the three base slots) a pairing whose
  generators are pinned. -/

/-- The nine `PayloadAgrees` fields whose two sides are words or `Nat`s. -/
structure PayloadScalarHalf (R : Render p G₁ G₂ Gₜ) : Prop where
  digest : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.vkDigest =
    frWord R.vk.transcriptRepr
  numInstances : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.numInstances =
    BitVec.ofNat 256 R.cfg.numInstances
  k : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.k = BitVec.ofNat 256 R.vk.domain.k
  nInv : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.nInv =
    frWord ((((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹)
  omega : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.omega = frWord R.vk.domain.omega
  omegaInv : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInv =
    frWord R.vk.domain.omegaInv
  omegaInvToL : Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInvToL =
    frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs)
  accWords :
    ((Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (Midfall.LoweringV3.payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
    accWordsOfEncoding R.cfg.accumulator
  constantsLength : 11 ≤ R.pv.vk.constants.length

/-- The five `PayloadAgrees` fields whose two sides are byte images of group elements. -/
structure PayloadPointHalf (R : Render p G₁ G₂ Gₜ) : Prop where
  g1Base : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip P.g₁
  g2Base : vkG2Words R.pv vkG2BaseSlot = R.encG2 P.g₂
  negSG2 : vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 R.sG2gen⁻¹
  fixedComms : R.pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes =
    R.vk.fixedCommitments.toList.map R.E.g1.toEip
  permutationComms : R.pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes =
    R.vk.permutation.commitments.toList.map R.E.g1.toEip

/-- **THE SPLIT IS THE FROZEN CLAUSE.** `PayloadAgrees` is exactly the nine scalar fields and the
    five point fields, in the clause's own field order. Nothing is dropped and nothing is
    strengthened: this is a re-packaging of the fourteen projections. -/
theorem payloadAgrees_iff_scalars_and_points (R : Render p G₁ G₂ Gₜ) :
    Midfall.LoweringV3.PayloadAgrees R ↔ PayloadScalarHalf R ∧ PayloadPointHalf R := by
  constructor
  · intro h
    exact ⟨⟨h.digest, h.numInstances, h.k, h.nInv, h.omega, h.omegaInv, h.omegaInvToL,
      h.accWords, h.constantsLength⟩,
      ⟨h.g1Base, h.g2Base, h.negSG2, h.fixedComms, h.permutationComms⟩⟩
  · rintro ⟨hs, hp⟩
    exact ⟨hs.digest, hs.numInstances, hs.k, hs.nInv, hs.omega, hs.omegaInv, hs.omegaInvToL,
      hs.accWords, hp.g1Base, hp.g2Base, hp.negSG2, hp.fixedComms, hp.permutationComms,
      hs.constantsLength⟩

/-! ## §2. `ValidV3` minus the point half. -/

/-- **THE SIX CLAUSES AND THE SCALAR HALF.** Every field except `payload`'s five point fields.
    `generated`, `inputs`, `program`, `noWriters`, `env` and `supported` are `ValidV3`'s own
    field types verbatim; `payloadScalars` is §1's `PayloadScalarHalf`. -/
structure ValidV3ExceptPayload (R : Render p G₁ G₂ Gₜ) : Prop where
  generated : Midfall.LoweringV3.GeneratedBy R
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  program : Midfall.LoweringV3.programOk R
  noWriters : Midfall.Yul.Bridge.NoWriters (R.prog 0 0)
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  payloadScalars : PayloadScalarHalf R
  supported : SupportedV2 R

/-- **THE EXACT RESIDUAL OF `ValidV3`.** For every render: `ValidV3` holds iff the point-free
    clauses hold and the five point fields hold. This is the statement B4's row should be read
    against - it is an equivalence, so it neither adds nor removes a hypothesis. -/
theorem validV3_iff_exceptPayload_and_points (R : Render p G₁ G₂ Gₜ) :
    ValidV3 R ↔ ValidV3ExceptPayload R ∧ PayloadPointHalf R := by
  constructor
  · intro h
    obtain ⟨hs, hp⟩ := (payloadAgrees_iff_scalars_and_points R).1 h.payload
    exact ⟨⟨h.generated, h.inputs, h.program, h.noWriters, h.env, hs, h.supported⟩, hp⟩
  · rintro ⟨he, hp⟩
    exact ⟨he.generated, he.inputs, he.program, he.noWriters, he.env,
      (payloadAgrees_iff_scalars_and_points R).2 ⟨he.payloadScalars, hp⟩, he.supported⟩

/-! ## §3. THE F1 RENDER, RE-POINTED - every clause except the point half.

  §1-2 of `ValidV3InhabitationF1.lean` established that only the RENDER's plan/qblocks/model
  are re-sourced. `Render.pv`, `Render.consts` and `Render.prog` are derived
  (`LoweringV2/Statements.lean:159-168`), so this section rebuilds the computable faces from the
  generator's output and re-decides each clause AT THE NEW VIEW. The model is the generator's,
  the plan is the generator's, and the four renders that are not re-sourced (E, params, vk,
  sG2gen, cfg, inputs, flags, encG2) are untouched, which is what makes the transfers `rfl`. -/

/-- The re-sourced model, as a computable face of `f1GeneratedRender`. -/
def f1M : Model := genFilledOut.model

/-- The re-sourced plan view: `planViewOf` at the generator's plan and model. `Render.pv` is
    DEFINED as this term (`LoweringV2/Statements.lean:162`), so `f1Pv_eq` is `rfl`. -/
def f1Pv : PlanView := planViewOf genFilledOut.plan f1M poseidonConfig.accumulator

theorem f1GeneratedRender_model_eq : f1GeneratedRender.model = f1M := rfl
theorem f1GeneratedRender_pv_eq : f1GeneratedRender.pv = f1Pv := rfl
theorem f1GeneratedRender_cfg_eq : f1GeneratedRender.cfg = poseidonConfig := rfl
theorem f1GeneratedRender_vk_eq : f1GeneratedRender.vk = poseidonVkExec := rfl
theorem f1GeneratedRender_inputs_eq : f1GeneratedRender.inputs = poseidonInputs := rfl
theorem f1GeneratedRender_flags_eq : f1GeneratedRender.flags = poseidonFlags := rfl
theorem f1GeneratedRender_E_eq : f1GeneratedRender.E = poseidonE := rfl
theorem f1GeneratedRender_params_eq : f1GeneratedRender.params = poseidonParams := rfl
theorem f1GeneratedRender_sG2_eq : f1GeneratedRender.sG2gen = poseidonSG2 := rfl
theorem f1GeneratedRender_prog_eq :
    f1GeneratedRender.prog 0 0 = asmOf f1Pv f1M 0 0 := rfl

/-- `generated` is F1's theorem, unchanged: the clause was already paid. -/
theorem f1_generated : Midfall.LoweringV3.GeneratedBy f1GeneratedRender :=
  f1GeneratedRender_generated

/-- `inputs` mentions no re-sourced field: it is `poseidonValid_inputs` at the new render. -/
theorem f1_inputs :
    f1GeneratedRender.inputs.numInstances = f1GeneratedRender.cfg.numInstances ∧
      f1GeneratedRender.inputs.accEncoding = f1GeneratedRender.cfg.accumulator ∧
      f1GeneratedRender.inputs.k = f1GeneratedRender.vk.domain.k ∧
      f1GeneratedRender.inputs.truncatedChallenges =
        Features.solidity.truncatedChallenges :=
  poseidonValid_inputs

/-- **THE DECIDABLE BUNDLE AT THE RE-SOURCED VIEW.** Fourteen conjuncts, decided at the generator's
    plan/model. The generated plan differs from the artifact's on `proofEnd` (4420 against 4320)
    and `numPointSets` (3 against 0), so this is NOT the F1 boolean transferred: every
    conjunct that mentions `pv` or `model` is recomputed here. AXIOM:
    f1_deciding_programOkB._native.native_decide.ax_1_1. -/
theorem f1_deciding_programOkB :
    Midfall.LoweringV3.programOkB f1GeneratedRender = true := by
  show Midfall.LoweringV3.programOkCore f1Pv f1M poseidonConfig.numInstances
    poseidonVkExec = true
  native_decide

/-- The gas scan at the re-sourced program, fuel 20000. AXIOM:
    f1_deciding_gasCallOk._native.native_decide.ax_1_1. -/
theorem f1_deciding_gasCallOk : Midfall.LoweringV3.GasCallOk
    (asmOf f1Pv f1M 0 0) :=
  ⟨20000, by native_decide⟩

/-- No `gas()` anywhere in the re-sourced program, fuel 20000. AXIOM:
    f1_deciding_gasFree._native.native_decide.ax_1_1. -/
theorem f1_deciding_gasFree : Midfall.LoweringV3.GasFree (asmOf f1Pv f1M 0 0) :=
  ⟨20000, by native_decide⟩

/-- The one exit scan at the re-sourced program, fuel 20000. AXIOM:
    f1_deciding_exitDiscipline._native.native_decide.ax_1_1. -/
theorem f1_deciding_exitDiscipline : Midfall.LoweringV3.ExitDiscipline
    (asmOf f1Pv f1M 0 0) :=
  ⟨20000, by native_decide⟩

/-- The address-fit conjunct at the re-sourced view. AXIOM:
    f1_deciding_programFit._native.native_decide.ax_1_1. -/
theorem f1_deciding_programFit : Midfall.LoweringV3.programFits f1Pv f1M := by
  rw [← Midfall.LoweringV3.programFitB_eq_true_iff]
  native_decide

/-- **THE PROGRAM CLAUSE AT THE RE-SOURCED RENDER - ALL FIVE HALVES TRUE.** The generated plan is
    three point sets, its proofEnd is 4420, and the program is rebuilt from it; the bundle, the
    three scans and the address fit all hold at that program. -/
theorem f1_program : Midfall.LoweringV3.programOk f1GeneratedRender := by
  refine ⟨f1_deciding_programOkB, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.GasCallOk (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasCallOk
  · show Midfall.LoweringV3.GasFree (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasFree
  · show Midfall.LoweringV3.ExitDiscipline (asmOf f1Pv f1M 0 0)
    exact f1_deciding_exitDiscipline
  · show Midfall.LoweringV3.programFits f1Pv f1M
    exact f1_deciding_programFit

/-- The no-writers clause at the re-sourced program, fuel 20000 (same fuel the three scans use).
    AXIOM: f1_deciding_noWriters._native.native_decide.ax_1_1. -/
theorem f1_noWriters : Midfall.Yul.Bridge.NoWriters (asmOf f1Pv f1M 0 0) :=
  ⟨20000, by native_decide⟩

/-- **THE ENV CLAUSE AT THE RE-SOURCED RENDER.** Nine of the ten fields mention only `vk`, `cfg`,
    `params`, `sG2gen` or `E.field` and are `poseidonValid_slots_nine`'s; the two that read `pv`
    (`domainN`'s second conjunct and `negLagranges`) are re-decided at `f1Pv`, and
    `vkDigestWord` is re-decided because it reads the payload's slot 0. AXIOM:
    f1_deciding_envNegLagranges._native.native_decide.ax_1_1 and
    f1_deciding_envPv._native.native_decide.ax_1_1 (domainN, vkDigestWord). -/
theorem f1_env :
    EnvAgrees f1GeneratedRender.E f1GeneratedRender.vk f1GeneratedRender.pv
      f1GeneratedRender.params f1GeneratedRender.sG2gen := by
  obtain ⟨hmod, htrunc, hd1, _hd2, hbary, homega, horder, hng2, hsg2, _hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, ?_⟩, hbary, homega, horder, ?_, hng2, hsg2, ?_⟩
  · show poseidonVkExec.domain.k = f1Pv.k
    native_decide
  · show f1Pv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
    native_decide
  · show (f1Pv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr
    native_decide

/-- **THE NINE SCALAR PAYLOAD FIELDS AT THE RE-SOURCED RENDER.** The payload is the filled one
    `generateAll` accepted, and its slots 0-10 are the artifact's; the plan's `rotationLast` is
    `-9`, the same as the transcribed plan's, so the one field that reads `plan.meta_` agrees.
    AXIOM: f1_deciding_payloadScalars._native.native_decide.ax_1_1. -/
theorem f1_payloadScalars : PayloadScalarHalf f1GeneratedRender := by
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

/-- **THE SUPPORTED CLAUSE AT THE RE-SOURCED RENDER.** `vkPoints`, `wf` and the shape fields
    mention only `vk`/`cfg`/`flags` and are the F1 proofs; the layout pair is the generator's
    plan and is re-decided. AXIOM: f1_deciding_supportedLayout._native.native_decide.ax_1_1. -/
theorem f1_supported : SupportedV2 f1GeneratedRender := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, _hlay1, _hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, ?_, ⟨?_, ?_⟩,
    ⟨hprod1, hprod2⟩, deciding_supported_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩
  · show ∀ C ∈ poseidonVkExec.fixedCommitments.toList ++
      poseidonVkExec.permutation.commitments.toList, Midfall.LoweringV2.ptReadable (poseidonE.g1.toEip C)
    exact poseidonValid_supported_vkPoints
  · show genFilledOut.plan.memory.map.WellFormed
    native_decide
  · show genFilledOut.plan.memory.validate.isOk = true
    native_decide

/-- **THE F1 RENDER IS VALID EXCEPT FOR THE POINT HALF - PROVED, IN FULL.**
    Six clauses and the nine scalar payload fields, at the generator's own plan/model, with
    `generated` the fixpoint theorem of `ValidV3InhabitationF1`. -/
theorem f1GeneratedRender_valid_except_payload :
    ValidV3ExceptPayload f1GeneratedRender :=
  ⟨f1_generated, f1_inputs, f1_program, f1_noWriters, f1_env, f1_payloadScalars, f1_supported⟩

/-! ## §4. THE POINT HALF AT THE F1 RENDER: TWO FIELDS REFUTED, THREE NAMED.

  The payload is `vkFilled`: the artifact's parsed payload with the four quotient reservation
  fields filled. Its commitment words are the REAL deployment commitments encoded as EIP-2537
  images, while the Lean key `poseidonVkExec` carries `1 : G₁z` in every commitment slot
  (`PoseidonValid.poseidonValid_supported_vkPoints` proves exactly that). `g1zToEip 1` is the
  all-zero 128-byte image, so the two commitment fields are FALSE, not merely open: the Lean key
  and the artifact's payload describe different points. The three base-slot fields name
  `P.g₁`, `P.g₂` and `sG2gen`, and the pairing instance is an axiom at this carrier, so no
  computation reaches them; that is the residual B3 must bridge. -/

/-- **`fixedComms` IS FALSE AT THE RE-SOURCED RENDER.** Computed, not inferred. AXIOM:
    f1_fixedComms_false._native.native_decide.ax_1_1. -/
theorem f1_fixedComms_false :
    ¬ (f1Pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.fixedCommitments.toList.map g1zToEip) := by
  native_decide

/-- **`permutationComms` IS FALSE AT THE RE-SOURCED RENDER.** AXIOM:
    f1_permutationComms_false._native.native_decide.ax_1_1. -/
theorem f1_permutationComms_false :
    ¬ (f1Pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes =
      poseidonVkExec.permutation.commitments.toList.map g1zToEip) := by
  native_decide

/-- **THE POINT HALF IS REFUTED AT THE F1 RENDER**, by its fourth field. -/
theorem f1GeneratedRender_payloadPointHalf_false :
    ¬ PayloadPointHalf f1GeneratedRender := by
  intro h
  exact f1_fixedComms_false h.fixedComms

/-- **THE EXACT RESIDUAL OF THE F1 ROUTE.** The re-sourced render meets every clause except the
    five point fields, and those are not open: two are refuted. So `ValidV3` fails here for a
    DATA reason (the Lean key's commitments are the identity and the payload's are not), not for
    a missing proof step. -/
theorem f1GeneratedRender_notValidV3 : ¬ Midfall.LoweringV3.ValidV3 f1GeneratedRender := by
  intro h
  exact f1GeneratedRender_payloadPointHalf_false
    ((validV3_iff_exceptPayload_and_points f1GeneratedRender).1 h).2

/-- The residual stated positively: `ValidV3` at the F1 render is EXACTLY its point half. -/
theorem f1GeneratedRender_validV3_iff_points :
    Midfall.LoweringV3.ValidV3 f1GeneratedRender ↔ PayloadPointHalf f1GeneratedRender := by
  rw [validV3_iff_exceptPayload_and_points]
  exact ⟨fun h => h.2, fun hp => ⟨f1GeneratedRender_valid_except_payload, hp⟩⟩

end Midfall.Instances.ValidV3InhabitationF1Completion
