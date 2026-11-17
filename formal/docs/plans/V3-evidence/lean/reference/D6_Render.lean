/-
  D6 - THE DEPLOYMENT RENDER OVER THE CONSTRUCTED PAIRING AND THE REAL KEY, and the shape of the
  headline once the SRS trapdoor is the one named hypothesis (or a closed term at a test SRS).
-/
import RunLib
import Midfall.Instances.PoseidonV2
import Midfall.Instances.G2Kernel
set_option autoImplicit false

namespace RefRender
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel RefRun
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv
open Midfall.Instances.PoseidonInputs Midfall.Instances.PoseidonV2
open Midfall.Lowering Midfall.LoweringV2

def frDelta : Fr blsR := (7 : Fr blsR) ^ (2 ^ 32)

def poseidonVkReal : VerifyingKey (Fr blsR) G₁z :=
  { domain := poseidonDomain,
    fixedCommitments := (decodeAll poseidonVkData.fixedCommitmentHex).getD #[],
    permutation := { commitments := (decodeAll poseidonVkData.permutationCommitmentHex).getD #[] },
    cs := poseidonCs, csDegree := poseidonVkData.csDegree, transcriptRepr := poseidonTranscriptRepr }

def poseidonEReal : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := frDelta, fewerPointSetsRuntime := false }

def poseidonParamsAt (s : ZMod blsR) : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s)

/-- THE RENDER, at trapdoor `s`. Gₜ is G₁z: the pairing is `pairingC`, constructed. Every
    verifier-side field is now REAL data: codec, delta, commitments, generators. -/
def poseidonRenderAt (s : ZMod blsR) : Render blsR G₁z G2fold G₁z where
  E := poseidonEReal
  params := poseidonParamsAt s
  vk := poseidonVkReal
  sG2gen := Multiplicative.ofAdd s
  encG2 := g2foldToEip
  cfg := poseidonConfig
  inputs := poseidonInputs
  flags := poseidonFlags
  plan := poseidonPlanV2
  qblocks := poseidonQBlocks
  model := poseidonModelVal

/-- NEG_S_G2_BASE of the deployed payload, as bytes. -/
def poseidonNegSG2Bytes : Bytes :=
  ((poseidonVkGen.constants.drop vkNegSG2BaseSlot).take 8).foldl
    (fun acc c => ByteArray.append acc (wordToBytesBE c.2)) Bytes.empty

/-- THE ONE SRS HYPOTHESIS. -/
def SrsEncodes (s : ZMod blsR) : Prop :=
  g2foldToEip (Multiplicative.ofAdd s)⁻¹ = poseidonNegSG2Bytes

/-- **THE HEADLINE SHAPE (stated).** For every trapdoor the payload's NEG_S_G2 encodes and every
    pairing product: the lowering equivalence of the render whose Lean verifier pairs with that
    `s · G2`. Hypotheses: `SrsEncodes s` and (inside `LoweringEquivalence`) `Eip2537.Holds`.
    Axioms once proved: the standard three and the recorded `native_decide` ones - NO curve axiom. -/
theorem lowering_equivalence_poseidon_at (s : ZMod blsR) (hSrs : SrsEncodes s)
    (product : PairingProduct) : LoweringEquivalence (poseidonRenderAt s) product := by
  sorry

/-- The two EnvAgrees generator clauses at this render, with the generators NAMED:
    `nG2Prepared = P.g₂⁻¹` is `rfl` because `pairingC.g₂` is exponent 1 by construction, and
    `sG2Prepared = sG2gen` is `rfl`. -/
theorem poseidonRenderAt_generators (s : ZMod blsR) :
    (poseidonRenderAt s).params.nG2Prepared = (pairingC.g₂)⁻¹ ∧
      (poseidonRenderAt s).params.sG2Prepared = (poseidonRenderAt s).sG2gen := ⟨rfl, rfl⟩

/-- The Lean-side final check at this render is a statement in G₁z alone:
    `e(left, s·G2) + e(right, -G2) = s • left - right`. -/
theorem check_iff_g1 (s : ZMod blsR) (L Rt : G₁z) :
    (pairingC.e (Additive.ofMul L) (Additive.ofMul (poseidonParamsAt s).sG2Prepared) +
        pairingC.e (Additive.ofMul Rt) (Additive.ofMul (poseidonParamsAt s).nG2Prepared) = 0) ↔
      s • Additive.ofMul L = Additive.ofMul Rt := by
  have h1 : pairingC.e (Additive.ofMul L) (Additive.ofMul (poseidonParamsAt s).sG2Prepared)
      = s • Additive.ofMul L := rfl
  have h2 : pairingC.e (Additive.ofMul Rt) (Additive.ofMul (poseidonParamsAt s).nG2Prepared)
      = (-(1 : ZMod blsR)) • Additive.ofMul Rt := by
    show ((Multiplicative.toAdd ((g2foldExp 1)⁻¹ : G2fold)) : ZMod blsR) • Additive.ofMul Rt = _
    congr 1
  rw [h1, h2, neg_smul, one_smul, add_neg_eq_zero]

#print axioms poseidonRenderAt
#print axioms check_iff_g1
#print axioms poseidonRenderAt_generators

end RefRender
