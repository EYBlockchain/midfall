/-
  Midfall.Instances.ArtifactB5F1

  **B5 AT THE F1 RE-SOURCED RENDER.** `f1PointRenderCCN n`'s model is the generator's
  output `genFilledOut.model` (`PayloadPointsF1.lean`), not the artifact model
  `poseidonModelVal`; the key, the KZG parameters and `sG2gen` are re-sourced as well.
  This file measures the tracked Poseidon artifacts against THAT model, and reports the
  exact residual without restating `ArtifactEq`.

  THE MEASURED RESULT:

  * The verifier text rendered from `genFilledOut.model` is byte-identical to the text
    rendered from the artifact model (`f1_text_eq_poseidon_text`). So the tracked
    `Halo2Verifier.sol` is NOT for a different Yul model: the two models render the same
    175,908 characters. The only residual is the same one D-B5 names, the `BUILD_ID`
    input line (`f1_diff_exact`, `f1_diff_idx`: line 274, 0-based).
  * `main` and `guard` hold at this model as well (`f1_main`, `f1_guard`).
  * `whole` is therefore false, and `¬ ArtifactEq (f1PointRenderCCN n).model
    poseidonVerifierDump` is proved for every `n` (`f1_whole_ne`, `not_artifactEq_f1`).
  * The VK artifact is byte-identical for F1's payload too (`f1Vk_exact`): the payload is
    the filled one, and `renderHalo2VerifyingKey` is blind to the four reservation fields
    (`ValidV3InhabitationF1.f1FilledPayload_differsOnlyInReservation`), so the tracked
    `Halo2VerifyingKey.sol` is the F1 key artifact as well.

  D-GATE17: `artifactEqV3_f1` is the positive artifact gate at the F1 model, with
  `poseidonArtifactBuildId` supplied; it is the field type `DoneAt` now carries.

  `native_decide` is confined to `Midfall/Instances/` (D-P17); the axiom list at the foot
  names each generated decision constant.
-/
import Midfall.Instances.ValidV3F1Real
import Midfall.Instances.ArtifactB5Poseidon
import Midfall.Tools.Done

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Midfall.Instances.ArtifactB5

open Midfall Midfall.Generator Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonV2
open Midfall.Instances.PoseidonValid Midfall.Instances.ValidV3InhabitationF1
open Midfall.Instances.PayloadPointsF1 Midfall.Instances.GeneratorDone

/-- The whole-file render from the F1 generator model. -/
def f1Text : String :=
  renderHalo2Verifier (rootCtxOfVerifier genFilledOut.model) (partsOf genFilledOut.model)

/-- The F1 model is the generator's model by definition (rfl), for every exponent `n`. -/
theorem f1PointRenderCCN_model_eq (n : Nat) :
    (f1PointRenderCCN n).model = genFilledOut.model :=
  rfl

/-- **THE TRACKED ARTIFACT IS NOT FROM A DIFFERENT YUL MODEL.** The F1 model's render is
    byte-identical to the artifact model's render. -/
theorem f1_text_eq_poseidon_text : f1Text = poseidonText := by
  native_decide

/-- `whole` is false at the F1 model, with the same single BUILD_ID residual. -/
theorem f1_whole_ne (n : Nat) :
    renderHalo2Verifier (rootCtxOfVerifier (f1PointRenderCCN n).model)
        (partsOf (f1PointRenderCCN n).model) ≠ poseidonVerifierDump := by
  show f1Text ≠ poseidonVerifierDump
  native_decide

/-- `main` holds at the F1 model. -/
theorem f1_main (n : Nat) :
    (poseidonVerifierDump.splitOn (mainAssemblyText (f1PointRenderCCN n).model)).length = 2 := by
  show (poseidonVerifierDump.splitOn (mainAssemblyText genFilledOut.model)).length = 2
  native_decide

/-- `guard` holds at the F1 model. -/
theorem f1_guard (n : Nat) :
    (poseidonVerifierDump.splitOn (abiGuardText (f1PointRenderCCN n).model)).length = 2 := by
  show (poseidonVerifierDump.splitOn (abiGuardText genFilledOut.model)).length = 2
  native_decide

/-- The exact residual at the F1 model: one line, the BUILD_ID constant. -/
theorem f1_diff_exact :
    diffLines f1Text poseidonVerifierDump =
      [(renderedBuildIdLine, artifactBuildIdLine)] := by
  native_decide

/-- And its 0-based line number, 274. -/
theorem f1_diff_idx :
    diffIdx f1Text poseidonVerifierDump = [274] := by
  native_decide

/-- Sizes at the F1 model. -/
theorem f1_sizes :
    f1Text.length = 175908 ∧ (f1Text.splitOn "\n").length = 3024 := by
  native_decide

/-- **`ArtifactEq` IS FALSE AT THE F1 MODEL TOO**, from its own `whole` field. The
    artifact is not weakened to make this true. -/
theorem not_artifactEq_f1 (n : Nat) :
    ¬ ArtifactEq (f1PointRenderCCN n).model poseidonVerifierDump :=
  fun h => f1_whole_ne n h.whole

/-- **THE F1 VK ARTIFACT IS BYTE-IDENTICAL.** `plan.vk` is the filled payload
    (`f1FilledPayload`), and the VK render ignores the reservation fields. -/
theorem f1Vk_exact (n : Nat) :
    renderHalo2VerifyingKey (f1PointRenderCCN n).plan.vk = poseidonVkDump := by
  show renderHalo2VerifyingKey genFilledOut.plan.vk = poseidonVkDump
  native_decide

/-- The F1 generator model with the artifact's `BUILD_ID` input supplied. -/
def f1ModelArtifactBuildId : Model :=
  { genFilledOut.model with buildId := poseidonArtifactBuildId }

/-- **THE POSITIVE B5 GATE AT THE F1 MODEL AND THE NAMED INPUT.** All three `ArtifactEq` clauses
    hold: the F1 model's render is the artifact once the BUILD_ID input is supplied, and
    `main`/`guard` occur once. The tracked artifact therefore IS for this model up to that input,
    not for a different Yul model. -/
theorem artifactEq_f1_with_artifactBuildId :
    ArtifactEq f1ModelArtifactBuildId poseidonVerifierDump := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **THE D-B5 VARIANT AT `(f1PointRenderCCN n).model`.** Same three clauses, BUILD_ID supplied;
    the F1 model is `genFilledOut.model`, so the positive raw gate transfers by definition. -/
theorem artifactEqV3_f1 (n : Nat) :
    Midfall.LoweringV2.ArtifactEqV3 (f1PointRenderCCN n).model poseidonVerifierDump
      poseidonArtifactBuildId := by
  refine ⟨?_, ?_, ?_⟩
  · exact artifactEq_f1_with_artifactBuildId.whole
  · exact artifactEq_f1_with_artifactBuildId.main
  · exact artifactEq_f1_with_artifactBuildId.guard

end Midfall.Instances.ArtifactB5

/-! ## Axiom audit -/

#print axioms Midfall.Instances.ArtifactB5.f1_text_eq_poseidon_text
#print axioms Midfall.Instances.ArtifactB5.f1_whole_ne
#print axioms Midfall.Instances.ArtifactB5.f1_main
#print axioms Midfall.Instances.ArtifactB5.f1_guard
#print axioms Midfall.Instances.ArtifactB5.f1_diff_exact
#print axioms Midfall.Instances.ArtifactB5.f1_diff_idx
#print axioms Midfall.Instances.ArtifactB5.f1_sizes
#print axioms Midfall.Instances.ArtifactB5.not_artifactEq_f1
#print axioms Midfall.Instances.ArtifactB5.artifactEq_f1_with_artifactBuildId
#print axioms Midfall.Instances.ArtifactB5.artifactEqV3_f1
#print axioms Midfall.Instances.ArtifactB5.f1Vk_exact
