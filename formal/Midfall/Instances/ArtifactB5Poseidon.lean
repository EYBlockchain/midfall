/-
  Midfall.Instances.ArtifactB5Poseidon

  **B5 IN LEAN, THE POSEIDON HALF.** The tracked deployed verifier
  `proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol`
  (`poseidonVerifierDump`) is compared against the text the ported generator renders
  from the render's OWN model, and the tracked VK artifact against the VK payload.

  THE MEASURED RESULT, and it is the one D-B5 pins:

  * `whole` of `ArtifactEq` is FALSE at this model, by exactly one line: the
    `BUILD_ID` constant. The port renders
      BUILD_ID = 0x2f162cd5617f861b3b8945894551b8602be0cdd7d5b84d7352bae91371b17b28
    while the committed artifact carries
      BUILD_ID = 0xf352d2670376fa01229e35428d69c1d623c4b3edf42f15a78622888a9b4285fd.
    Both texts are 175,908 characters / 3,024 lines and differ nowhere else
    (`poseidon_diff_exact`, `poseidon_diff_idx`: the single differing 0-based line is
    274, the `BUILD_ID` line VkLoading.yul renders).
  * `main` and `guard` of `ArtifactEq` are TRUE: each text occurs exactly once in the
    artifact (`splitOn` length 2).
  * The VK artifact is byte-identical (`poseidonVk_exact`, 26,018 bytes / 271 lines),
    which is D-B5's "pins the VK exactly".

  Consequently `¬ ArtifactEq poseidonRender.model poseidonVerifierDump` is a THEOREM,
  not a weakening: the structure is not restated with a weaker `whole`. What is landed
  next to it are the two true fields and the exact one-line residual. The residual is
  the BUILD_ID INPUT, exactly as D-B5 says; it is not a Yul or port difference.

  `native_decide` is the sanctioned computation channel here (`Midfall/Instances/`,
  D-P17). The axiom list at the foot names every generated decision constant.
-/
import Midfall.Instances.GeneratorDone
import Midfall.Tools.Done

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Midfall.Instances.ArtifactB5

open Midfall Midfall.Generator Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonV2
open Midfall.Instances.PoseidonValid

/-! ## The measurement surface -/

/-- The differing-line pairs of two texts, in order, with the ArtifactEq measurement's own
    line split (`splitOn "\n"`). -/
def diffLines (a b : String) : List (String × String) :=
  let ls := (a.splitOn "\n").zip (b.splitOn "\n")
  ls.filterMap fun q => if q.1 == q.2 then none else some (q.1, q.2)

/-- The 0-based line numbers at which two texts differ. -/
def diffIdx (a b : String) : List Nat :=
  (((a.splitOn "\n").zip (b.splitOn "\n")).zipIdx.filter fun q => q.1.1 != q.1.2).map fun q => q.2

/-- The whole-file render from D.1's COMPUTABLE model term. `poseidonRender.model` is this
    term by `rfl` (`PoseidonValid.poseidonM_eq`); the computable spelling is what
    `native_decide` can evaluate. -/
def poseidonText : String :=
  renderHalo2Verifier (rootCtxOfVerifier poseidonModelVal) (partsOf poseidonModelVal)

/-- The line the port renders for `BUILD_ID`. -/
def renderedBuildIdLine : String :=
  "    bytes32 public constant BUILD_ID = 0x2f162cd5617f861b3b8945894551b8602be0cdd7d5b84d7352bae91371b17b28;"

/-- The line the committed artifact carries. -/
def artifactBuildIdLine : String :=
  "    bytes32 public constant BUILD_ID = 0xf352d2670376fa01229e35428d69c1d623c4b3edf42f15a78622888a9b4285fd;"

/-! ## The three `ArtifactEq` clauses, measured -/

/-- `whole` is false: the render is not the artifact. -/
theorem poseidon_whole_ne :
    renderHalo2Verifier (rootCtxOfVerifier poseidonRender.model) (partsOf poseidonRender.model) ≠
      poseidonVerifierDump := by
  show poseidonText ≠ poseidonVerifierDump
  native_decide

/-- `main` holds: the main assembly text occurs exactly once in the artifact. -/
theorem poseidon_main :
    (poseidonVerifierDump.splitOn (mainAssemblyText poseidonRender.model)).length = 2 := by
  show (poseidonVerifierDump.splitOn (mainAssemblyText poseidonModelVal)).length = 2
  native_decide

/-- `guard` holds: the ABI-guard text occurs exactly once in the artifact. -/
theorem poseidon_guard :
    (poseidonVerifierDump.splitOn (abiGuardText poseidonRender.model)).length = 2 := by
  show (poseidonVerifierDump.splitOn (abiGuardText poseidonModelVal)).length = 2
  native_decide

/-- THE EXACT RESIDUAL: one line, the BUILD_ID constant, with both strings named. -/
theorem poseidon_diff_exact :
    diffLines poseidonText poseidonVerifierDump =
      [(renderedBuildIdLine, artifactBuildIdLine)] := by
  native_decide

/-- The differing line number: line 274 (0-based), i.e. line 275 of the artifact,
    `bytes32 public constant BUILD_ID = ...`. -/
theorem poseidon_diff_idx :
    diffIdx poseidonText poseidonVerifierDump = [274] := by
  native_decide

/-- Both texts have the artifact's size and line count, so the one-line residual is not
    hiding a length drift. -/
theorem poseidon_sizes :
    poseidonText.length = 175908 ∧ poseidonVerifierDump.length = 175908 ∧
      (poseidonText.splitOn "\n").length = 3024 ∧
      (poseidonVerifierDump.splitOn "\n").length = 3024 := by
  native_decide

/-- **`ArtifactEq` IS FALSE AT THE POSEIDON MODEL**, from its own `whole` field. This is
    the honest statement; no weakened `ArtifactEq` is introduced. -/
theorem not_artifactEq_poseidon :
    ¬ ArtifactEq poseidonRender.model poseidonVerifierDump :=
  fun h => poseidon_whole_ne h.whole

/-! ## The same gate with D-B5's named input supplied -/

/-- The model with the artifact's `BUILD_ID` input supplied. This is NOT `poseidonRender.model`:
    it is the render model with the one build fact the artifact carries, which is exactly the
    input D-B5 names. Kept as a separate model so nothing here reads as a weakened `ArtifactEq`. -/
def poseidonModelArtifactBuildId : Model :=
  { poseidonModelVal with
    buildId := 0xf352d2670376fa01229e35428d69c1d623c4b3edf42f15a78622888a9b4285fd }

/-- **THE POSITIVE B5 GATE AT THE NAMED INPUT.** With the artifact's BUILD_ID supplied, all three
    `ArtifactEq` clauses hold: the whole text is the artifact, and `main`/`guard` occur once.
    The residual measured above is therefore the build fact and nothing else. -/
theorem artifactEq_poseidon_with_artifactBuildId :
    ArtifactEq poseidonModelArtifactBuildId poseidonVerifierDump := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## The VK artifact: D-B5's exact half -/

/-- The VK artifact is byte-identical to the render of the tracked payload. -/
theorem poseidonVk_exact :
    renderHalo2VerifyingKey poseidonVkGen = poseidonVkDump := by
  native_decide

/-- And at the artifact's own size / line count. -/
theorem poseidonVk_sizes :
    poseidonVkDump.length = 26018 ∧ (poseidonVkDump.splitOn "\n").length = 271 := by
  native_decide

end Midfall.Instances.ArtifactB5

/-! ## Axiom audit -/

#print axioms Midfall.Instances.ArtifactB5.poseidon_whole_ne
#print axioms Midfall.Instances.ArtifactB5.poseidon_main
#print axioms Midfall.Instances.ArtifactB5.poseidon_guard
#print axioms Midfall.Instances.ArtifactB5.poseidon_diff_exact
#print axioms Midfall.Instances.ArtifactB5.poseidon_diff_idx
#print axioms Midfall.Instances.ArtifactB5.poseidon_sizes
#print axioms Midfall.Instances.ArtifactB5.not_artifactEq_poseidon
#print axioms Midfall.Instances.ArtifactB5.artifactEq_poseidon_with_artifactBuildId
#print axioms Midfall.Instances.ArtifactB5.poseidonVk_exact
#print axioms Midfall.Instances.ArtifactB5.poseidonVk_sizes
