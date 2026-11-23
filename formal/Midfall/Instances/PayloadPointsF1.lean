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

/-! ## §2. THE 19/8 REAL COMMITMENTS, DECODED FROM THE PARSED PAYLOAD.

  The Lean key `poseidonVkExec` carries `Array.replicate 19 (1 : G₁z)` in `fixedCommitments`
  and `Array.replicate 8 (1 : G₁z)` in `permutation.commitments` (`PoseidonEnv.lean:195-200`),
  while the parsed payload carries the artifact's real points. B4 measured the consequence:
  `fixedComms` and `permutationComms` are FALSE at `f1GeneratedRender`
  (`f1_fixedComms_false`, `f1_permutationComms_false`).

  The repair is DATA, not a clause: decode every payload EIP-2537 word into the carrier with
  the computable decoder `g1zOfEipC?` (`Instances/G1Compressed.lean:132`: width, canonical
  coordinates, curve, r-torsion - no discrete log and no axiom), and put those points in the
  key. `f1DecodedFixed_all`/`f1DecodedPerm_all` are the machine-checked statement that no
  fallback identity was taken; the two re-encode theorems are then exactly the two
  `PayloadPointHalf` commitment fields at the re-sourced key. -/

/-- Every fixed commitment of the parsed F1 payload, decoded (or `none` if it is not an
    r-torsion EIP-2537 point). -/
def f1DecodedFixed : List (Option G₁z) :=
  f1Pv.vk.fixedComms.map (fun w => g1zOfEipC? (Midfall.LoweringV3.g1WordsBytes w))

/-- Every permutation commitment of the parsed F1 payload, decoded. -/
def f1DecodedPerm : List (Option G₁z) :=
  f1Pv.vk.permutationComms.map (fun w => g1zOfEipC? (Midfall.LoweringV3.g1WordsBytes w))

/-- The decoded fixed commitments as carrier elements. The `getD 1` arm is unreachable by the
    two `_all` theorems below; it is what makes the term total. -/
def f1ResourcedFixed : List G₁z := f1DecodedFixed.map (fun o => o.getD 1)

/-- The decoded permutation commitments. -/
def f1ResourcedPerm : List G₁z := f1DecodedPerm.map (fun o => o.getD 1)

/-- **THE RE-SOURCED KEY.** Same domain, CS, degree and transcript representation as D.2's key;
    the two commitment arrays are the payload's own points. -/
def f1VkResourced : VerifyingKey (Fr blsR) G₁z :=
  { poseidonVkExec with
    fixedCommitments := f1ResourcedFixed.toArray
    permutation := { poseidonVkExec.permutation with
      commitments := f1ResourcedPerm.toArray } }

/-- **NO FALLBACK WAS TAKEN: all 19 payload fixed commitments decode into the carrier.**
    AXIOM: f1DecodedFixed_all._native.native_decide.ax_1_1. -/
theorem f1DecodedFixed_all : f1DecodedFixed.all (fun o => o.isSome) = true := by
  native_decide

/-- **NO FALLBACK WAS TAKEN: all 8 payload permutation commitments decode.** AXIOM:
    f1DecodedPerm_all._native.native_decide.ax_1_1. -/
theorem f1DecodedPerm_all : f1DecodedPerm.all (fun o => o.isSome) = true := by
  native_decide

/-- **THE FIXED-COMMITMENT FIELD OF THE RE-SOURCED KEY.** The payload words are the EIP images
    of the decoded points, in order - exactly `PayloadPointHalf.fixedComms`.
    AXIOM: f1VkResourced_fixed_reencodes._native.native_decide.ax_1_1. -/
theorem f1VkResourced_fixed_reencodes :
    f1Pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes =
      f1VkResourced.fixedCommitments.toList.map g1zToEip := by
  native_decide

/-- **THE PERMUTATION-COMMITMENT FIELD OF THE RE-SOURCED KEY.** AXIOM:
    f1VkResourced_perm_reencodes._native.native_decide.ax_1_1. -/
theorem f1VkResourced_perm_reencodes :
    f1Pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes =
      f1VkResourced.permutation.commitments.toList.map g1zToEip := by
  native_decide

/-- The re-sourced key really differs from D.2's identity key: this is not a restatement of the
    placeholder. WITNESS, by the two commitment arrays. -/
theorem f1VkResourced_fixed_ne_placeholder :
    f1VkResourced.fixedCommitments ≠ poseidonVkExec.fixedCommitments := by
  native_decide

/-! ## §3. THE F1 RENDER AT THE CONSTRUCTED PAIRING.

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

/-- **THE PAYLOAD-SOURCED KZG PARAMETERS.** `nG2Prepared` is `g₂⁻¹` at the constructed pairing
    (the `EnvAgrees.nG2` clause), and `sG2Prepared` is the inverse of the payload's neg-S-G2
    point's exponent, i.e. the payload's own `s·H2`. `sG2` is the same point, so the three
    parameters are mutually consistent and no opaque axiom is read. -/
noncomputable def f1ParamsResourced (n : Nat) : ParamsVerifierKZG G₁z G2fold :=
  { sG2 := (g2foldExp n)⁻¹
    nG2Prepared := (g2foldExp 1)⁻¹
    sG2Prepared := (g2foldExp n)⁻¹ }

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

/-- The same environment with the REAL computable G1 codec. Only `g1` changes: `field`, `delta`
    and `fewerPointSetsRuntime` are `f1EnvC`'s. -/
noncomputable def f1EnvCC : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := poseidonDelta,
    fewerPointSetsRuntime := false }

/-- **THE F1 RENDER WITH THE COMPUTABLE CODEC.** Same key/parameters/carrier as
    `f1PointRenderC`; the G1 codec is `g1CodecC`, whose compressed encoder-first law is now
    proved (`g1CodecC_lawsV3`). -/
noncomputable def f1PointRenderCC (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Render blsR G₁z G2fold G₁z :=
  { E := f1EnvCC
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

/-- The point-sourced render at the computable codec. -/
abbrev f1PointRenderCCN (n : Nat) :
    Render blsR G₁z G2fold G₁z :=
  f1PointRenderCC f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)

/-- **THE CODEC LAW AT THE NEW RENDER.** `f1PointRenderCCN n`'s G1 codec is `g1CodecC`
    definitionally, and `g1CodecC_lawsV3` is B3's proved `G1CodecLawsV3`. -/
theorem f1PointRenderCCN_codec_lawsV3 (n : Nat) :
    Midfall.LoweringV3.G1CodecLawsV3 (f1PointRenderCCN n).E.g1 :=
  g1CodecC_lawsV3

/-- The EIP-2537 encoder is the same function at the two renders. -/
theorem f1PointRenderCC_toEip (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    (f1PointRenderCC vk params sG2).E.g1.toEip =
      (f1PointRenderC vk params sG2).E.g1.toEip := rfl

/-- The EIP-2537 decoder transfers by `g1CodecC_ofEip`: the computable codec's `ofEip?` IS the
    exhibit's. -/
theorem f1PointRenderCC_ofEip (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    (f1PointRenderCC vk params sG2).E.g1.ofEip? =
      (f1PointRenderC vk params sG2).E.g1.ofEip? :=
  g1CodecC_ofEip

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

/-- **`PayloadPointHalf.fixedComms` AT THE RE-SOURCED RENDER, UNCONDITIONALLY.** -/
theorem f1PointRenderC_fixedComms (params : ParamsVerifierKZG G₁z G2fold)
    (sG2 : G2fold) :
    (f1PointRenderC f1VkResourced params sG2).pv.vk.fixedComms.map
        Midfall.LoweringV3.g1WordsBytes
      = (f1PointRenderC f1VkResourced params sG2).vk.fixedCommitments.toList.map
          (f1PointRenderC f1VkResourced params sG2).E.g1.toEip := by
  show f1Pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes
    = f1VkResourced.fixedCommitments.toList.map g1zToEip
  exact f1VkResourced_fixed_reencodes

/-- **`PayloadPointHalf.permutationComms` AT THE RE-SOURCED RENDER, UNCONDITIONALLY.** -/
theorem f1PointRenderC_permutationComms (params : ParamsVerifierKZG G₁z G2fold)
    (sG2 : G2fold) :
    (f1PointRenderC f1VkResourced params sG2).pv.vk.permutationComms.map
        Midfall.LoweringV3.g1WordsBytes
      = (f1PointRenderC f1VkResourced params sG2).vk.permutation.commitments.toList.map
          (f1PointRenderC f1VkResourced params sG2).E.g1.toEip := by
  show f1Pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes
    = f1VkResourced.permutation.commitments.toList.map g1zToEip
  exact f1VkResourced_perm_reencodes

/-- **`PayloadPointHalf.g1Base` AT THE COMPUTABLE CODEC, UNCONDITIONALLY.** `g1CodecC.toEip`
    is `g1zToEip`, so the byte fact is §1's. -/
theorem f1PointRenderCC_g1Base (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Midfall.Lowering.vkG1Words (f1PointRenderCC vk params sG2).pv
        Midfall.Lowering.vkG1BaseSlot
      = (f1PointRenderCC vk params sG2).E.g1.toEip pairingF1.g₁ := by
  show Midfall.Lowering.vkG1Words f1Pv Midfall.Lowering.vkG1BaseSlot = g1zToEip g1zGen
  exact payloadG1Base_bytes

/-- **`PayloadPointHalf.g2Base` AT THE COMPUTABLE CODEC, UNCONDITIONALLY.** -/
theorem f1PointRenderCC_g2Base (vk : VerifyingKey (Fr blsR) G₁z)
    (params : ParamsVerifierKZG G₁z G2fold) (sG2 : G2fold) :
    Midfall.Lowering.vkG2Words (f1PointRenderCC vk params sG2).pv
        Midfall.Lowering.vkG2BaseSlot
      = (f1PointRenderCC vk params sG2).encG2 pairingF1.g₂ := by
  show Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkG2BaseSlot
    = g2foldToEip (g2foldExp 1)
  exact payloadG2Base_bytes

/-- **`PayloadPointHalf.fixedComms` AT THE COMPUTABLE CODEC, UNCONDITIONALLY.** -/
theorem f1PointRenderCC_fixedComms (params : ParamsVerifierKZG G₁z G2fold)
    (sG2 : G2fold) :
    (f1PointRenderCC f1VkResourced params sG2).pv.vk.fixedComms.map
        Midfall.LoweringV3.g1WordsBytes
      = (f1PointRenderCC f1VkResourced params sG2).vk.fixedCommitments.toList.map
          (f1PointRenderCC f1VkResourced params sG2).E.g1.toEip := by
  show f1Pv.vk.fixedComms.map Midfall.LoweringV3.g1WordsBytes
    = f1VkResourced.fixedCommitments.toList.map g1zToEip
  exact f1VkResourced_fixed_reencodes

/-- **`PayloadPointHalf.permutationComms` AT THE COMPUTABLE CODEC, UNCONDITIONALLY.** -/
theorem f1PointRenderCC_permutationComms (params : ParamsVerifierKZG G₁z G2fold)
    (sG2 : G2fold) :
    (f1PointRenderCC f1VkResourced params sG2).pv.vk.permutationComms.map
        Midfall.LoweringV3.g1WordsBytes
      = (f1PointRenderCC f1VkResourced params sG2).vk.permutation.commitments.toList.map
          (f1PointRenderCC f1VkResourced params sG2).E.g1.toEip := by
  show f1Pv.vk.permutationComms.map Midfall.LoweringV3.g1WordsBytes
    = f1VkResourced.permutation.commitments.toList.map g1zToEip
  exact f1VkResourced_perm_reencodes

/-- **THE POINT-SOURCED RENDER.** The key is the re-sourced one, the parameters carry the
    payload's `s·H2`, and `sG2gen` is its inverse - the payload's neg-S-G2 point. -/
abbrev f1PointRenderCN (n : Nat) :
    Render blsR G₁z G2fold G₁z :=
  f1PointRenderC f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)

/-- The right-hand side of `PayloadPointHalf.negSG2` at `f1PointRenderCN n`, reduced to the
    payload exponent. -/
theorem f1PointRenderCN_negRhs (n : Nat) :
    (f1PointRenderCN n).encG2 ((f1PointRenderCN n).sG2gen⁻¹)
      = g2foldToEip (g2foldExp n) := by
  show g2foldToEip (((g2foldExp n)⁻¹)⁻¹) = g2foldToEip (g2foldExp n)
  rw [inv_inv]

/-- **THE `negSG2`/`sG2gen` BRIDGE.** If the payload's NEG_S_G2 bytes are the EIP encoding of
    `g2foldExp n` - i.e. `n` is the payload's own `−s`, the discrete-log witness the artifact
    does not carry - then `sG2gen := (g2foldExp n)⁻¹` makes the field true, and `f1ParamsResourced n`
    makes `EnvAgrees.sG2` hold at the same value. No other hypothesis enters. -/
theorem f1PointRenderCN_negSG2 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.Lowering.vkG2Words (f1PointRenderCN n).pv Midfall.Lowering.vkNegSG2BaseSlot
      = (f1PointRenderCN n).encG2 (f1PointRenderCN n).sG2gen⁻¹ := by
  show Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
    = g2foldToEip (((g2foldExp n)⁻¹)⁻¹)
  rw [inv_inv]
  exact hpay

/-- **THE WHOLE POINT HALF AT THE RE-SOURCED RENDER.** Both base slots, both commitment
    lists, and `negSG2` under the one data statement that names the payload's neg-S-G2 point.
    This is the object B4's `f1GeneratedRender_validV3_iff_points` consumes. -/
theorem f1PointRenderCN_payloadPointHalf (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    PayloadPointHalf (f1PointRenderCN n) where
  g1Base := f1PointRenderC_g1Base f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  g2Base := f1PointRenderC_g2Base f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  negSG2 := f1PointRenderCN_negSG2 n hpay
  fixedComms := f1PointRenderC_fixedComms (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  permutationComms := f1PointRenderC_permutationComms (f1ParamsResourced n) ((g2foldExp n)⁻¹)

/-- The `negSG2`/`sG2gen` bridge at the computable codec: `encG2` and `sG2gen` are unchanged,
    so the payload exponent identifies the same point. -/
theorem f1PointRenderCCN_negSG2 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.Lowering.vkG2Words (f1PointRenderCCN n).pv Midfall.Lowering.vkNegSG2BaseSlot
      = (f1PointRenderCCN n).encG2 (f1PointRenderCCN n).sG2gen⁻¹ := by
  show Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
    = g2foldToEip (((g2foldExp n)⁻¹)⁻¹)
  rw [inv_inv]
  exact hpay

/-- **THE WHOLE POINT HALF AT THE COMPUTABLE-CODEC RENDER.** -/
theorem f1PointRenderCCN_payloadPointHalf (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    PayloadPointHalf (f1PointRenderCCN n) where
  g1Base := f1PointRenderCC_g1Base f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  g2Base := f1PointRenderCC_g2Base f1VkResourced (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  negSG2 := f1PointRenderCCN_negSG2 n hpay
  fixedComms := f1PointRenderCC_fixedComms (f1ParamsResourced n) ((g2foldExp n)⁻¹)
  permutationComms := f1PointRenderCC_permutationComms (f1ParamsResourced n) ((g2foldExp n)⁻¹)

/-- **THE EXACT RESIDUAL OF THE POINT HALF AT THE RE-SOURCED RENDER.** Every field except
    `negSG2` is unconditional; the whole point half is EQUIVALENT to the payload having the
    exponent `n` at its neg-S-G2 slot. The forward direction is the `negSG2` projection and
    is what makes this an iff and not a one-way implication. -/
theorem f1PointRenderCN_payloadPointHalf_iff (n : Nat) :
    PayloadPointHalf (f1PointRenderCN n)
      ↔ Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
          = g2foldToEip (g2foldExp n) := by
  constructor
  · intro h
    have hh := h.negSG2
    rw [f1PointRenderCN_negRhs] at hh
    exact hh
  · intro h
    exact f1PointRenderCN_payloadPointHalf n h

/-! ### The transport: `ValidV3` at `f1PointRenderCN n`, with `hpay` the only data input.

  B4's generic theorem `validV3_iff_exceptPayload_and_points` says `ValidV3 R` splits into the six
  point-free clauses plus the scalar half (`ValidV3ExceptPayload R`) and the point half. This
  section proves the first conjunct AT the re-sourced render and composes it with §2's point half,
  so `ValidV3 (f1PointRenderCN n)` is EXACTLY the one data statement `hpay`. Nothing about the
  pairing, the codec or the commitments is assumed: the constructed pairing's generators are
  `rfl`, and the commitments are the payload's own decoded points. -/

/-- The generator call at the re-sourced key is the F1 call definitionally: `generateAll` reads
    the commitments only through their lengths. -/
theorem f1GenEqF1 :
    generateAll Features.solidity poseidonDelta f1VkResourced poseidonConfig
      f1FilledPayload poseidonInputs poseidonFlags = genFilledRun := rfl

theorem f1PointRenderCN_E_delta (n : Nat) :
    (f1PointRenderCN n).E.delta = poseidonDelta := rfl
theorem f1PointRenderCN_vk_eq (n : Nat) : (f1PointRenderCN n).vk = f1VkResourced := rfl
theorem f1PointRenderCN_cfg_eq (n : Nat) : (f1PointRenderCN n).cfg = poseidonConfig := rfl
theorem f1PointRenderCN_inputs_eq (n : Nat) : (f1PointRenderCN n).inputs = poseidonInputs := rfl
theorem f1PointRenderCN_flags_eq (n : Nat) : (f1PointRenderCN n).flags = poseidonFlags := rfl
theorem f1PointRenderCN_plan_eq (n : Nat) : (f1PointRenderCN n).plan = genFilledOut.plan := rfl
theorem f1PointRenderCN_model_eq (n : Nat) : (f1PointRenderCN n).model = f1M := rfl
theorem f1PointRenderCN_pv_eq (n : Nat) : (f1PointRenderCN n).pv = f1Pv := rfl
theorem f1PointRenderCN_prog_eq (n : Nat) :
    (f1PointRenderCN n).prog 0 0 = asmOf f1Pv f1M 0 0 := rfl

/-- **`generated` AT THE RE-SOURCED RENDER.** The generator's plan/model/qblocks are the F1
    fixed point; the resourced key changes no argument `generateAll` reads. -/
theorem f1PointRenderCN_generated (n : Nat) :
    Midfall.LoweringV3.GeneratedBy (f1PointRenderCN n) :=
  ⟨genFilledOut, by
      rw [Midfall.LoweringV3.generated]
      rw [f1PointRenderCN_E_delta, f1PointRenderCN_vk_eq, f1PointRenderCN_cfg_eq,
        f1PointRenderCN_inputs_eq, f1PointRenderCN_flags_eq, f1PointRenderCN_plan_eq,
        genFilledOut_plan_vk_is_the_payload_it_was_given]
      exact f1GenEqF1.trans genFilledRun_eq_ok,
    rfl, rfl, rfl⟩

/-- `inputs` at the re-sourced render: the clause reads no key commitment. -/
theorem f1PointRenderCN_inputsClause (n : Nat) :
    (f1PointRenderCN n).inputs.numInstances = (f1PointRenderCN n).cfg.numInstances ∧
      (f1PointRenderCN n).inputs.accEncoding = (f1PointRenderCN n).cfg.accumulator ∧
      (f1PointRenderCN n).inputs.k = (f1PointRenderCN n).vk.domain.k ∧
      (f1PointRenderCN n).inputs.truncatedChallenges =
        Features.solidity.truncatedChallenges :=
  poseidonValid_inputs

/-- The fourteen-conjunct bundle at the resourced key. Only `permCommMatchRepaired` reads the
    key, and it reads commitment COUNTS, which the re-source preserves. AXIOM:
    f1PointRenderCN_programB._native.native_decide.ax_1_1. -/
theorem f1PointRenderCN_programB (n : Nat) :
    Midfall.LoweringV3.programOkB (f1PointRenderCN n) = true := by
  show Midfall.LoweringV3.programOkCore f1Pv f1M poseidonConfig.numInstances
    f1VkResourced = true
  native_decide

/-- **THE PROGRAM CLAUSE AT THE RE-SOURCED RENDER.** The program is `asmOf f1Pv f1M 0 0` (the
    plan view and model are untouched), so B4's four scan theorems apply verbatim. -/
theorem f1PointRenderCN_program (n : Nat) :
    Midfall.LoweringV3.programOk (f1PointRenderCN n) := by
  refine ⟨f1PointRenderCN_programB n, ?_, ?_, ?_, ?_⟩
  · show Midfall.LoweringV3.GasCallOk (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasCallOk
  · show Midfall.LoweringV3.GasFree (asmOf f1Pv f1M 0 0)
    exact f1_deciding_gasFree
  · show Midfall.LoweringV3.ExitDiscipline (asmOf f1Pv f1M 0 0)
    exact f1_deciding_exitDiscipline
  · show Midfall.LoweringV3.programFits f1Pv f1M
    exact f1_deciding_programFit

/-- `noWriters` at the resourced program: the program is unchanged. -/
theorem f1PointRenderCN_noWriters (n : Nat) :
    Midfall.Yul.Bridge.NoWriters ((f1PointRenderCN n).prog 0 0) := by
  show Midfall.Yul.Bridge.NoWriters (asmOf f1Pv f1M 0 0)
  exact f1_noWriters

/-- **`env` AT THE RE-SOURCED RENDER.** Nine fields are the F1 proofs; `nG2` is `rfl` because
    `pairingF1.g₂ = g2foldExp 1`, and `sG2` is `rfl` because `f1ParamsResourced` sets
    `sG2Prepared` to the same payload-sourced point as `sG2gen`. -/
theorem f1PointRenderCN_env (n : Nat) :
    EnvAgrees (f1PointRenderCN n).E (f1PointRenderCN n).vk
      (f1PointRenderCN n).pv (f1PointRenderCN n).params (f1PointRenderCN n).sG2gen := by
  obtain ⟨hmod, htrunc, hd1, _hd2, hbary, homega, horder, _hng2, _hsg2, _hdig⟩ :=
    poseidonValid_slots_nine
  refine ⟨hmod, htrunc, ⟨hd1, ?_⟩, hbary, homega, horder, ?_, ?_, ?_, ?_⟩
  · show poseidonVkExec.domain.k = f1Pv.k
    native_decide
  · show f1Pv.numNegLagranges = poseidonVkExec.cs.blindingFactors.toOption.getD 0 + 1
    native_decide
  · show ((g2foldExp 1)⁻¹ : G2fold) = pairingF1.g₂⁻¹
    rfl
  · rfl
  · show (f1Pv.vk.constants.getD 0 ("", 0)).2 = frWord poseidonVkExec.transcriptRepr
    native_decide

/-- **THE NINE SCALAR PAYLOAD FIELDS AT THE RE-SOURCED RENDER.** They read the payload's header
    words and the key's domain/transcript representation, none of which the re-source changes.
    AXIOM: one `native_decide` per field, named `f1PointRenderCN_payloadScalars._native...ax_1_k`
    in the order of `PayloadScalarHalf`. -/
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

/-- `WellFormed` at the resourced key: every field reads counts/domain, which the re-source
    preserves. -/
theorem f1VkResourced_wf : f1VkResourced.WellFormed Features.solidity :=
  { csDegreeMatches := deciding_supported_degree_eq
    chunkLenPositive := by
      show 3 ≤ f1VkResourced.csDegree
      native_decide
    domainConsistent := by
      show f1VkResourced.domain.n = 2 ^ f1VkResourced.domain.k ∧
        f1VkResourced.domain.quotientPolyDegree = f1VkResourced.csDegree - 1
      native_decide
    permutationCommitmentsMatch := by
      show f1VkResourced.permutation.commitments.size =
        f1VkResourced.cs.permutation.columns.size
      native_decide
    fixedCommitmentsMatch := by
      show f1VkResourced.fixedCommitments.size = f1VkResourced.cs.numFixedColumns
      native_decide
    singlePhase := by
      show f1VkResourced.cs.numChallenges = 0
      native_decide
    committedInstancesOn := rfl
    advicePhaseTotal := by
      show f1VkResourced.cs.adviceColumnPhase.size = f1VkResourced.cs.numAdviceColumns
      native_decide
    challengePhaseTotal := by
      show f1VkResourced.cs.challengePhase.size = f1VkResourced.cs.numChallenges
      native_decide }

/-- **`supported` AT THE RE-SOURCED RENDER.** The only changed field is `vkPoints`, which is
    `g1CodecZ_g1Valid` for EVERY carrier point (so the real commitments are readable by
    construction); `wf` is `f1VkResourced_wf` and the layout fields are F1's generated plan. -/
theorem f1PointRenderCN_supported (n : Nat) :
    SupportedV2 (f1PointRenderCN n) := by
  obtain ⟨hadvice, hinst1, hinst2, hsphase, hlimbs, _hlay1, _hlay2, hprod1, hprod2, hnoacc,
    hemb1, hemb2, hsep, _hci, hnorot⟩ := poseidonValid_supported_rest
  refine ⟨hadvice, ⟨hinst1, hinst2⟩, hnorot, hsphase, hlimbs, ?_, ⟨?_, ?_⟩,
    ⟨hprod1, hprod2⟩, f1VkResourced_wf, hnoacc, ⟨hemb1, hemb2⟩, hsep⟩
  · intro C hC
    exact g1CodecZ_g1Valid C
  · show genFilledOut.plan.memory.map.WellFormed
    native_decide
  · show genFilledOut.plan.memory.validate.isOk = true
    native_decide

/-- **THE SIX POINT-FREE CLAUSES AND THE NINE SCALARS AT THE RE-SOURCED RENDER - PROVED.** -/
theorem f1PointRenderCN_validExceptPayload (n : Nat) :
    ValidV3ExceptPayload (f1PointRenderCN n) :=
  ⟨f1PointRenderCN_generated n, f1PointRenderCN_inputsClause n, f1PointRenderCN_program n,
    f1PointRenderCN_noWriters n, f1PointRenderCN_env n, f1PointRenderCN_payloadScalars n,
    f1PointRenderCN_supported n⟩

/-- **`ValidV3` AT THE RE-SOURCED F1 RENDER IS EXACTLY THE PAYLOAD EXPONENT.** The six clauses
    and the nine scalars are proved; the five point fields are §2, four unconditionally and
    `negSG2` under `hpay`. So this is an equivalence, not a one-way reduction: `hpay` is a DATA
    statement about the artifact's SRS, not a clause of `ValidV3`. -/
theorem f1PointRenderCN_validV3_iff (n : Nat) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n)
      ↔ Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
          = g2foldToEip (g2foldExp n) := by
  rw [validV3_iff_exceptPayload_and_points]
  exact ⟨fun h => (f1PointRenderCN_payloadPointHalf_iff n).1 h.2,
    fun h => ⟨f1PointRenderCN_validExceptPayload n,
      (f1PointRenderCN_payloadPointHalf_iff n).2 h⟩⟩

/-- **THE INHABITANT: `ValidV3` HOLDS AT THE RE-SOURCED RENDER GIVEN `hpay`.** This is the form
    B4's `f1GeneratedRender_validV3_iff_points` is meant to consume, at the real payload and the
    real commitments. -/
theorem f1PointRenderCN_validV3 (n : Nat)
    (hpay : Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      = g2foldToEip (g2foldExp n)) :
    Midfall.LoweringV3.ValidV3 (f1PointRenderCN n) :=
  (f1PointRenderCN_validV3_iff n).2 hpay

end ConstructedPairing

/-! ## §4. THE DATA BOUNDARY: WHERE `hpay` COMES FROM, AND WHY F1 DOES NOT HAVE IT. -/

/-- The public trapdoor of the TRACKED test-SRS bundle
    (`fixtures/conformance/poseidon-testsrs/params.json`, `trapdoor_s_be_hex`). -/
def sTest : Nat := 0x1bf3a1cfdf9c46596942fab645fc0b03e5697e0604f803b899d065db10dbe23b

/-- The same bundle's `neg_s_g2_eip_hex`, the EIP-2537 encoding of `-s·H2`. -/
def negTestEip : Bytes := Midfall.Instances.hexToBytes
  "000000000000000000000000000000000316dc1cea57704ff4c5a3e6f04378c9856ea2fe15e9df3c6446c8b087a23b728e639203318b634d95e201ad94c4cc27000000000000000000000000000000001627cab699a2a90258f1b9c6fcaeefee12855f67d34f1883bda30e2a1fff8c1dd8b38a97654963eb46b411a732553fb50000000000000000000000000000000004f8c7e504cbfced0074119f866508dbcc0fea14c93041374d4ea085191e2a2142d1d7f67ac0d9261984d0cf107ec20b00000000000000000000000000000000043307da70b19d31b7828df1a839b783153b2096aafe4c1feebf986a0d76614fa2c98c8d281d5be1301e015a4634f1c8"

/-- **THE BRIDGE IS REALIZABLE WITH A KNOWN-TRAPDOOR SRS.** For the tracked test-SRS bundle the
    concrete exponent is `n = r - sTest`, and the encoding is the bundle's own `neg_s_g2_eip_hex`.
    AXIOM: testsrs_negSG2_exponent._native.native_decide.ax_1_1. -/
theorem testsrs_negSG2_exponent :
    g2foldToEip (g2foldExp (blsR - sTest)) = negTestEip := by
  native_decide

/-- **THE F1 PAYLOAD IS NOT THE TEST-SRS PAYLOAD.** The tracked test trapdoor does NOT satisfy
    F1's `hpay`: the production artifact's NEG_S_G2 slot is a different point. So the missing
    datum is not `sTest` (or any exponent derivable from the test bundle). -/
theorem f1NegSG2_not_testTrapdoor :
    Midfall.Lowering.vkG2Words f1Pv Midfall.Lowering.vkNegSG2BaseSlot
      ≠ g2foldToEip (g2foldExp (blsR - sTest)) := by
  native_decide

/-! ### The exact trust boundary.

  The tracked data for F1 consists of

  * `proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2VerifyingKey.sol` - the payload
    itself, including the NEG_S_G2 slot that appears in `hpay`;
  * `formal/fixtures/conformance/poseidon/params.json` - `s_g2_compressed_hex`, the point `s·H2`
    (the same point as the SRS file's `s_g2`; verified in this worktree by searching the
    `bls_filecoin_2p19` SRS tail: its 192-byte `s_g2` x-coordinate is exactly the params file's
    compressed x, and the payload's NEG_S_G2 is that point with the y sign flipped);
  * the downloaded but UNTRACKED `proofs/solidity-verifier/.srs/bls_filecoin_2p19`, which stores
    `g`, `g_lagrange`, `g2`, `s_g2` and **no scalar** (`ParamsKZG` in
    `proofs/src/poly/kzg/params.rs` has exactly those four fields).

  `hpay` for `f1Pv` with `n` is therefore equivalent to the DISCRETE LOG of the production
  Filecoin SRS point `s_g2` with respect to `H2`; `n = r - s` for that SRS's secret `s`. No tracked
  file contains `s`, no tracker exports it, and the tree has no G2 discrete-log algorithm. The
  test-SRS bundle is a DIFFERENT SRS, and `f1NegSG2_not_testTrapdoor` proves its published `s`
  does not produce F1's slot. This is the exact missing data; it is not a clause of `ValidV3` and
  nothing here is assumed about it. What lands is the equivalence
  `f1PointRenderCN_validV3_iff`: `ValidV3` at the resourced render holds iff that one data
  statement does. -/

end Midfall.Instances.PayloadPointsF1
