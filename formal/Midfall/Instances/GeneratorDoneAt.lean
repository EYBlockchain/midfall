/-
  Midfall.Instances.GeneratorDoneAt

  A RENDER-GENERIC form of the DG.4 `Done` card.  `Done` (`GeneratorDone.lean`) is stated at
  `poseidonRender`, whose `ValidV3` is REFUTED by the tracked data (`f1_ValidV3_false`); the real
  F1 render is `f1PointRenderCN n`, conditional on the payload's NEG_S_G2 scalar `hpay`.  This file
  states the same five fields at an arbitrary render, proves the bridge to `GeneratorDone`, and
  reduces the F1-real `DoneAt` to exactly the remaining inputs (gate, totality, artifact).  It adds
  no hypothesis to `ValidV3`, any row, or any root; `Done`/`not_done_today` are untouched.
-/
import Midfall.Instances.ValidV3F1Real

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **DONE AT A RENDER.** The five fields of DG.4's definition of done, at `R` and artifact
    `artifact`.  `Done` is the `R = poseidonRender` instance; this form is what a resourced render
    (F1-real) can inhabit without any fixture substitution in the headline. -/
structure DoneAt (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (artifact : String) : Prop where
  /-- 1. THE HEADLINE, for every pairing product. -/
  headline : ∀ product : PairingProduct, LoweringEquivalenceV3 R product
  /-- 2. THE RENDER IS THE GENERATOR'S OUTPUT FOR THIS KEY. -/
  valid : ValidV3 R
  /-- 3. NON-VACUITY at `cd` for some product. -/
  gate : ∃ product : PairingProduct, GateAtV3 R product cd
  /-- 4. TOTALITY: the program is never stuck, for every product. -/
  total : ∀ product : PairingProduct, TotalV3 R product
  /-- 5. THE TEXT IS THE RUST ARTIFACT (whole file, main block, guard block). -/
  artifactEq : Midfall.LoweringV2.ArtifactEq R.model artifact

/-- A `DoneAt` yields the frozen `GeneratorDone`: the headline is the generic root, `valid` + `gate`
    are its `nonvacuous` field. PROVED. -/
theorem DoneAt.toGeneratorDone {R : Render p G₁ G₂ Gₜ} {cd : Bytes} {artifact : String}
    (d : DoneAt R cd artifact) : GeneratorDone R cd :=
  ⟨fun R' product hR => lowering_correct R' product hR, ⟨d.valid, d.gate⟩⟩

/-- What `DoneAt` yields: the frozen non-vacuity statement, for some product, at this calldata. -/
theorem DoneAt.hypothesesInhabitedV3 {R : Render p G₁ G₂ Gₜ} {cd : Bytes} {artifact : String}
    (d : DoneAt R cd artifact) :
    ∃ product : PairingProduct, HypothesesInhabitedV3 R product := by
  obtain ⟨product, hg⟩ := d.gate
  exact ⟨product, hypothesesInhabitedV3_of_gateAtV3 R product cd hg⟩

/-- And an honest run exists, for some product and entry state: the gate is not "the contract never
    returns". -/
theorem DoneAt.returns {R : Render p G₁ G₂ Gₜ} {cd : Bytes} {artifact : String}
    (d : DoneAt R cd artifact) :
    ∃ (product : PairingProduct) (vkAddr : U256) (st₀ : EvmState) (obs : Obs),
      RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs ∧
        obs.view = returnView st₀ := by
  obtain ⟨product, hg⟩ := d.gate
  exact ⟨product, returns_of_inhabited R product (d.headline product)
    (hypothesesInhabitedV3_of_gateAtV3 R product cd hg)⟩

end Midfall.LoweringV3

namespace Midfall.Instances

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.Instances
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1 Midfall.Instances.ValidV3InhabitationF1Completion
open Midfall.Instances.PayloadPointsF1

noncomputable section

/-- The constructed pairing is the instance the point render is stated at. -/
local instance : AdmissiblePairing G₁z G2fold G₁z := pairingF1

/-- **THE F1-REAL `DoneAt`, FROM THE NAMED REMAINING INPUTS.** `valid` is
    `f1PointRenderCN_validV3 n hpay`; `total` is `totalV3_correct`; `gate` and `artifactEq` are the
    two measurement inputs. No hypothesis is added to `ValidV3` or to the headline. -/
theorem f1PointRenderCN_doneAt (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n))
    (cd : Bytes) (artifact : String)
    (hgate : ∃ product : PairingProduct, Midfall.LoweringV3.GateAtV3 (f1PointRenderCN n) product cd)
    (hart : Midfall.LoweringV2.ArtifactEq (f1PointRenderCN n).model artifact) :
    Midfall.LoweringV3.DoneAt (f1PointRenderCN n) cd artifact := by
  have hR : Midfall.LoweringV3.ValidV3 (f1PointRenderCN n) :=
    Midfall.Instances.ValidV3F1Real.f1PointRenderCN_validV3 n hpay
  refine ⟨?_, hR, hgate, ?_, hart⟩
  · intro product
    exact Midfall.LoweringV3.lowering_correct _ product hR
  · intro product
    exact Midfall.LoweringV3.totalV3_correct _ product hR

end

end Midfall.Instances
