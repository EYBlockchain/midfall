/-
  Midfall.Instances.PayloadPointsF1

  B3V3: the POINT HALF of `PayloadAgrees` at the F1 payload, field by field.

  THE LANE. B4's `ValidV3InhabitationF1Completion.lean` splits the frozen clause into nine
  codec-free fields and five point fields, and proves

      ValidV3 R  ↔  ValidV3ExceptPayload R ∧ PayloadPointHalf R

  for every render. At `f1GeneratedRender` the six clauses and the nine scalar fields are proved
  (`f1GeneratedRender_valid_except_payload`), so the point half is the ONLY residual:

      ValidV3 f1GeneratedRender  ↔  PayloadPointHalf f1GeneratedRender.

  This file discharges the point half at the payload the F1 render actually carries.

  WHAT IS COMPUTED AND WHAT IS NOT. The payload's base slots are the published BLS12-381
  generators, so `g1Base`/`g2Base` are a COMPUTATION (`native_decide` on the artifact bytes) plus
  one exact generator pin each - the pairing instance at `Gₜ = blsGT` is an AXIOM
  (`Assumptions/CurvePairing.lean:101`), so `bls12_381Pairing.g₁`/`.g₂` are opaque and no
  computation can name them. §1 proves the bytes and the exact iff. §2 builds the F1 render at
  the CONSTRUCTED pairing (`Instances/PairingByConstruction.lean:62`, repeated here so this
  module does not perturb the global instance search), whose generators are `g1zGen` and
  `g2foldExp 1` by `rfl`, and proves both fields there with NO hypothesis.

  The commitment re-source and the `negSG2`/`sG2gen` bridge are the next increments of this file;
  they are not stated here until proved, so this module contains no `sorry`.

  No frozen file is touched, no clause is weakened, no hypothesis is added to `PayloadAgrees` or
  `ValidV3`, and no `Render` field is invented.
-/
import Midfall.Instances.ValidV3InhabitationF1Completion
import Midfall.Instances.G1Compressed

set_option autoImplicit false

namespace Midfall.Instances.PayloadPointsF1

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering
open Midfall.Assumptions Midfall.Yul Midfall.LoweringV2
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonV2 Midfall.Instances.PoseidonValid Midfall.Instances.PlanNewKats
open Midfall.Instances.ValidV3InhabitationF1
open Midfall.Instances.ValidV3InhabitationF1Completion

/-! ## §1. THE TWO BASE SLOTS ARE THE PUBLISHED GENERATORS. -/

/-- **G1_BASE, BY COMPUTATION.** The F1 payload's four words at slot 11 are the EIP-2537 image
    of the published BLS12-381 G1 generator `g1zGen`. This is the artifact's own bytes, not a
    fixture: `f1Pv.vk` is `f1FilledPayload`, the parsed payload `generateAll` accepted.
    AXIOM: payloadG1Base_bytes._native.native_decide.ax_1_1. -/
theorem payloadG1Base_bytes :
    Midfall.Lowering.vkG1Words f1Pv Midfall.Lowering.vkG1BaseSlot = g1zToEip g1zGen := by
  native_decide

/-- **G2_BASE, BY COMPUTATION.** The eight words at slot 15 are the encoding of the published
    H2, i.e. of the exponent-1 element of the `G2fold` carrier. AXIOM:
    payloadG2Base_bytes._native.native_decide.ax_1_1. -/
theorem payloadG2Base_bytes :
    Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkG2BaseSlot
      = g2foldToEip (g2foldExp 1) := by
  native_decide

/-- **THE EXACT `g1Base` BRIDGE AT B4's RENDER.** `PayloadPointHalf.g1Base` at
    `f1GeneratedRender` holds IFF the opaque pairing generator is the published one. The forward
    direction is injectivity of the encoder, so the pin is not sufficient-only: the byte fact
    already names the payload side. -/
theorem f1GeneratedRender_g1Base_iff :
    (Midfall.Lowering.vkG1Words f1GeneratedRender.pv Midfall.Lowering.vkG1BaseSlot
        = f1GeneratedRender.E.g1.toEip bls12_381Pairing.g₁)
      ↔ bls12_381Pairing.g₁ = g1zGen := by
  have h : Midfall.Lowering.vkG1Words f1Pv Midfall.Lowering.vkG1BaseSlot =
      g1zToEip g1zGen := payloadG1Base_bytes
  change (Midfall.Lowering.vkG1Words f1Pv Midfall.Lowering.vkG1BaseSlot
      = g1zToEip bls12_381Pairing.g₁) ↔ bls12_381Pairing.g₁ = g1zGen
  constructor
  · intro hh
    exact g1zToEip_injective (by rw [← hh]; exact h)
  · intro hh
    rw [hh]
    exact h

/-- **THE EXACT `g2Base` BRIDGE AT B4's RENDER.** Same shape, through
    `g2foldToEip_injective`. -/
theorem f1GeneratedRender_g2Base_iff :
    (Midfall.Lowering.vkG2Words f1GeneratedRender.pv Midfall.Lowering.vkG2BaseSlot
        = f1GeneratedRender.encG2 bls12_381Pairing.g₂)
      ↔ bls12_381Pairing.g₂ = g2foldExp 1 := by
  have h : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkG2BaseSlot =
      g2foldToEip (g2foldExp 1) := payloadG2Base_bytes
  change (Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkG2BaseSlot
      = g2foldToEip bls12_381Pairing.g₂) ↔ bls12_381Pairing.g₂ = g2foldExp 1
  constructor
  · intro hh
    exact g2foldToEip_injective (by rw [← hh]; exact h)
  · intro hh
    rw [hh]
    exact h

/-! ### The tie back to the frozen clause: these are FIELDS, not look-alike equations. -/

/-- The `g1Base` equation above is exactly `PayloadPointHalf.g1Base` at B4's render: the
    projection has the stated type, so the iff is about the field and not an imitation of it. -/
theorem f1PayloadPointHalf_g1Base_is_field
    (h : PayloadPointHalf f1GeneratedRender) :
    Midfall.Lowering.vkG1Words f1GeneratedRender.pv Midfall.Lowering.vkG1BaseSlot
      = f1GeneratedRender.E.g1.toEip bls12_381Pairing.g₁ :=
  h.g1Base

/-- Same tie for `g2Base`. -/
theorem f1PayloadPointHalf_g2Base_is_field
    (h : PayloadPointHalf f1GeneratedRender) :
    Midfall.Lowering.vkG2Words f1GeneratedRender.pv Midfall.Lowering.vkG2BaseSlot
      = f1GeneratedRender.encG2 bls12_381Pairing.g₂ :=
  h.g2Base

/-! ## §2. THE F1 RENDER AT THE CONSTRUCTED PAIRING.

  `PairingByConstruction.lean:62` constructs the D-P62(a) pairing `e(P,k) = k • P` over `G₁z`
  with `g₁ = g1zGen` and `g₂ = g2foldExp 1`. It is repeated here as a plain `def` (not an
  instance) for one reason: importing that module would add a second `AdmissiblePairing` instance
  whose `Gₜ` is `G₁z`, and that makes typeclass search for the `blsGT` instance in §1 diverge.
  A local instance is enough for this section, and no global instance search is perturbed.

  The render carries the F1 generator output (`genFilledOut.plan/qblocks/model`, the same terms
  B4's `f1GeneratedRender` carries), so its derived `pv` is `f1Pv` by `rfl` and the payload is
  the artifact's. The verifying key, the KZG parameters and the `sG2gen` slot are PARAMETERS:
  the commitment re-source supplies the first, and the payload-sourced neg-S-G2 point the other
  two. Neither base field reads them. -/

/-- The constructed pairing's bilinear map, copied from `PairingByConstruction.eC`: it is
    `e(P, k) = k • P`, curried. -/
private noncomputable def eF1 :
    (Additive G₁z) →ₗ[ZMod blsR] (Additive G2fold) →ₗ[ZMod blsR] (Additive G₁z) where
  toFun P :=
    { toFun := fun k => (k.toMul.toAdd : ZMod blsR) • P
      map_add' := fun k l => add_smul (k.toMul.toAdd : ZMod blsR) (l.toMul.toAdd) P
      map_smul' := fun m k => mul_smul m (k.toMul.toAdd : ZMod blsR) P }
  map_add' := fun P Q => LinearMap.ext fun k => smul_add (k.toMul.toAdd : ZMod blsR) P Q
  map_smul' := fun m P => LinearMap.ext fun k => smul_comm (k.toMul.toAdd : ZMod blsR) m P

/-- The published H1 is not the identity - the same proof `PairingByConstruction.lean:44`
    carries, repeated here because that module also registers a competing instance. -/
private theorem g1zGen_ne_oneF1 : g1zGen ≠ 1 := by
  intro h
  have hh := congrArg g1zPair h
  rw [g1zPair_gen, g1zPair_one] at hh
  exact absurd hh (by decide)

/-- The constructed pairing at `Gₜ = G₁z`, as a plain `def`: `g₁`/`g₂` are pinned by `rfl`. -/
noncomputable def pairingF1 : AdmissiblePairing G₁z G2fold G₁z where
  e := eF1
  g₁ := g1zGen
  g₂ := g2foldExp 1
  hG₁ := g1zGen_ne_oneF1
  hG₂ := g2foldExp_one_ne_one
  hNonDeg := by
    intro h
    have h1 : eF1 (Additive.ofMul g1zGen) (Additive.ofMul (g2foldExp 1)) =
        ((1 : ℕ) : ZMod blsR) • Additive.ofMul g1zGen := rfl
    rw [h1, Nat.cast_one, one_smul] at h
    exact g1zGen_ne_oneF1 (Additive.ofMul.injective h)
  decEqG₁ := inferInstance
  decEqGₜ := inferInstance

theorem pairingF1_g1 : pairingF1.g₁ = g1zGen := rfl
theorem pairingF1_g2 : pairingF1.g₂ = g2foldExp 1 := rfl

noncomputable section ConstructedPairing

local instance : AdmissiblePairing G₁z G2fold G₁z := pairingF1

/-- The verifier environment at the constructed pairing. Only `Gₜ` changes; the G1 codec, field
    constants and delta are D.2's. -/
noncomputable def f1EnvC : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecZ, field := poseidonFc, delta := poseidonDelta,
    fewerPointSetsRuntime := false }

/-- **THE F1 RENDER AT THE CONSTRUCTED PAIRING.** -/
noncomputable def f1PointRenderC (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Render blsR G₁z G2fold G₁z :=
  { E := f1EnvC
    params := params
    vk := vk
    sG2gen := sG2
    encG2 := g2foldToEip
    cfg := poseidonConfig
    inputs := poseidonInputs
    flags := poseidonFlags
    plan := genFilledOut.plan
    qblocks := genFilledOut.qblocks
    model := genFilledOut.model }

/-- The derived plan view is F1's, because `pv` reads `plan`, `model` and `cfg` and never `vk`. -/
theorem f1PointRenderC_pv (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    (f1PointRenderC vk params sG2).pv = f1Pv := rfl

/-- **`PayloadPointHalf.g1Base` AT THE RE-SOURCED RENDER, UNCONDITIONALLY.** At the constructed
    pairing the generator is `g1zGen` by `rfl`, so the field is §1's byte fact. -/
theorem f1PointRenderC_g1Base (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Midfall.Lowering.vkG1Words (f1PointRenderC vk params sG2).pv
        Midfall.Lowering.vkG1BaseSlot
      = (f1PointRenderC vk params sG2).E.g1.toEip pairingF1.g₁ := by
  show Midfall.Lowering.vkG1Words f1Pv Midfall.Lowering.vkG1BaseSlot = g1zToEip g1zGen
  exact payloadG1Base_bytes

/-- **`PayloadPointHalf.g2Base` AT THE RE-SOURCED RENDER, UNCONDITIONALLY.** -/
theorem f1PointRenderC_g2Base (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Midfall.Lowering.vkG2Words (f1PointRenderC vk params sG2).pv
        Midfall.Lowering.vkG2BaseSlot
      = (f1PointRenderC vk params sG2).encG2 pairingF1.g₂ := by
  show Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkG2BaseSlot
    = g2foldToEip (g2foldExp 1)
  exact payloadG2Base_bytes

end ConstructedPairing

end Midfall.Instances.PayloadPointsF1
