/-
  Midfall.Instances.VacuityWitnesses

  **NON-VACUITY EVIDENCE FOR THE HEADLINE'S HYPOTHESES AT F1.** This file is a KAT/witness
  carrier for `formal/docs/VACUITY.md`, not a proof of any row. It answers the three questions a
  register row cannot answer by itself:

    * `ValidV3 poseidonRender` is FALSE, not merely unproved - the root's hypothesis is refuted
      at the only render the tree names (`f1_ValidV3_false`, from `f1_generated_obstruction_at_F1`);
    * the codec bundle the headline and `EndToEndV3` ask for is FALSE at the render's own codec
      (`f1_codec_headline_false`, `f1_codecLawsV3_false`), while it is INHABITED at an abstract
      codec of the same carrier (`StatementsV3Deploy.lawsV3_satisfiable_at_G1z`);
    * `DeploymentV2` and `EntryFrameV3` are INHABITED at F1, so the root's frame hypotheses are
      not empty for a reason hidden behind `ValidV3` (`f1_deploymentV2`, `f1_entryFrameV3`).

  WHAT THIS DOES NOT DO. It does not inhabit `ValidV3` (that is B4's re-sourced render plus B3's
  real commitments), does not inhabit `SupportedInput`, and does not prove any row. No statement
  in `LoweringV3`/`LoweringV2` is weakened or gains a hypothesis. Nothing here is in
  `lowering_correct`'s cone: the file imports `Instances`, and the dependency direction is
  Instances -> LoweringV3, never back (D-P17).

  The `#print axioms` at the foot name every trust the witnesses carry. `f1_ValidV3_false` and the
  two codec refutations inherit the one `native_decide` axiom of `poseidon_generated_notOk`; the
  frame witnesses additionally carry the F1 `poseidonModel_isOk` axiom, and `f1_entryFrameV3`
  carries `poseidonValid_transcriptMptr`'s.
-/
import Midfall.Instances.ValidV3InhabitationF1
import Midfall.Instances.StatementsV3Deploy
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.Instances.VacuityWitnesses

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Assumptions
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid
open Midfall.Instances.ValidV3InhabitationF1
open Midfall.LoweringV3 Midfall.LoweringV3.Deploy
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-! ## 1. The root's F1 hypothesis is refuted -/

/-- **`ValidV3 poseidonRender` IS FALSE.** `generated` alone refutes it: the render's plan carries
    the parsed artifact payload, which `generateAll` refuses at `quotient.rs:202`
    (`f1_generated_obstruction_at_F1`, itself `poseidonValid_generated_not`). This is the V3
    statement, not a paraphrase of the frozen V2 one: the projection `ValidV3.generated` is
    definitionally the `GeneratedBy` the refutation negates (`Composition.lean`'s header records
    that the two namespaces' `GeneratedBy` are equal by `Iff.rfl`). -/
theorem f1_ValidV3_false : ¬ Midfall.LoweringV3.ValidV3 poseidonRender := by
  intro h
  exact f1_generated_obstruction_at_F1 h.generated

/-- **NO WITNESS TO THE ROOT AT F1.** There is no `hR : ValidV3 poseidonRender` together with a
    proof of the headline at that render. This is the precise sense in which the register's
    `ROOT` row is vacuously true at F1: the theorem still quantifies over every render, but its
    only named instance has an empty hypothesis. -/
theorem f1_root_has_no_witness (product : Midfall.Yul.PairingProduct) :
    ¬ ∃ _hR : Midfall.LoweringV3.ValidV3 poseidonRender,
      Midfall.LoweringV3.LoweringEquivalenceV3 poseidonRender product := by
  rintro ⟨hR, _⟩
  exact f1_ValidV3_false hR

/-! ## 2. The codec bundle: false at the deployment codec, inhabited at an abstract one -/

/-- The render's own G1 codec is `g1CodecZ`, whose `ofCompressed?` is the constant `none`. -/
theorem f1_codec_headline_false :
    ¬ Midfall.LoweringV3.G1CodecHeadlineLaws poseidonRender.E.g1 := by
  intro h
  exact g1CodecZ_not_headlineLaws h

/-- Hence the full V3 codec bundle is false at the deployment codec. `EndToEndV3`'s `hcodec` and
    every row's `hcodec` are therefore refuted at `poseidonRender`; the positive satisfiability
    witness is the *different* codec `withCompressed g1CodecZ comp` of
    `StatementsV3Deploy.lawsV3_satisfiable_at_G1z`, not this one. -/
theorem f1_codecLawsV3_false : ¬ Midfall.LoweringV3.G1CodecLawsV3 poseidonRender.E.g1 := by
  intro h
  exact f1_codec_headline_false h.headline

/-! ## 3. The deployment and entry-frame hypotheses are inhabited at F1 -/

/-- The VK address, the tracked runtime bytes, and a world in the shape `DeploymentV2` asks for.
    This is the same construction as `PoseidonExhibit.exhibitW`; it is repeated here so this file
    does not import the large exhibit module. -/
def f1VkAddr : U256 := 0

def f1VkRuntime : List UInt8 := poseidonPlanV2.vk.runtimeBytes.data.toList

def f1W : ExecEnv :=
  { callvalue := 0,
    keccakOf := hashOfBytes keccak256,
    extCodeOf := fun a => if a = f1VkAddr then f1VkRuntime else [],
    extCodeHashOf := fun a =>
      if (if a = f1VkAddr then f1VkRuntime else []).length = 0 then 0
      else hashOfBytes keccak256 (if a = f1VkAddr then f1VkRuntime else []) }

/-- **`DeploymentV2` IS INHABITED AT F1.** The `W.WF` field is the only one that is not `rfl` or
    `decide`: it follows because the world has nonce and balance zero at every address, so
    `projectedCodeHash` is exactly the `if code is empty then 0 else keccak code` this world
    installs. -/
theorem f1_deploymentV2 :
    Midfall.LoweringV2.DeploymentV2 poseidonRender f1W keccak256 f1VkAddr := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, rfl⟩
    intro a
    simp only [f1W, YulSemantics.EVM.projectedCodeHash]
    by_cases h : a = f1VkAddr
    · subst h
      by_cases hc : f1VkRuntime.length = 0
      · simp [hc]
      · simp [hc]
    · simp [h]
  · rfl
  · decide
  · decide

/-- An arbitrary layout: `EntryFrameV3` only stores it in the `initState` shape. -/
def f1Lyt : EVM.Layout := { code := [], dataOffset := fun _ => 0, dataSize := fun _ => 0 }

/-- **`EntryFrameV3` IS INHABITED AT F1**, at the bare four-byte `verifyProof` selector. The
    `TRANSCRIPT_MPTR` premise is `poseidonValid_transcriptMptr`; the length bound is `4 < 2^256`.
    So the frame half of `EndToEndV3` is not empty at the render. -/
theorem f1_entryFrameV3 :
    ∃ st : EvmState,
      Midfall.LoweringV3.EntryFrameV3 poseidonRender f1W f1Lyt keccak256
        fnSigVerifyProof st := by
  apply Midfall.LoweringV3.entryFrame_inhabitedV3
  · rfl
  · rfl
  · exact poseidonValid_transcriptMptr
  · decide
  · decide

/-! ## 4. Axiom prints and cone checks -/

#print axioms Midfall.Instances.VacuityWitnesses.f1_ValidV3_false
#print axioms Midfall.Instances.VacuityWitnesses.f1_root_has_no_witness
#print axioms Midfall.Instances.VacuityWitnesses.f1_codec_headline_false
#print axioms Midfall.Instances.VacuityWitnesses.f1_codecLawsV3_false
#print axioms Midfall.Instances.VacuityWitnesses.f1_deploymentV2
#print axioms Midfall.Instances.VacuityWitnesses.f1_entryFrameV3

#cone_sorries Midfall.Instances.VacuityWitnesses.f1_ValidV3_false
#cone_sorries Midfall.Instances.VacuityWitnesses.f1_deploymentV2

end Midfall.Instances.VacuityWitnesses
