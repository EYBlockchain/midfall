/-
  RefModel - THE COMPUTABLE REAL-CURVE REFERENCE MODEL (scratch; proposed home:
  formal/Midfall/Instances/G1Compressed.lean and formal/Midfall/Instances/PairingByConstruction.lean).

  1. `g1zOfPair?`      a COMPUTABLE decoder  (x, y) -> G₁z   (r-torsion => zpowers, in-tree theorem)
  2. `g1CodecC`        a real G1Codec on G₁z: 48-byte flagged compressed form + EIP-2537 form
  3. `pairingC`        an AdmissiblePairing G₁z G2fold G₁z BY CONSTRUCTION: e(P, k) = k • P,
                       g₁ = the published H1, g₂ = exponent 1. No axiom.
-/
import Midfall.Instances.G1PointCount
import Midfall.Instances.HoldsStaging
import Midfall.Instances.Bls12_381
import Midfall.Instances.G2Codec
import Midfall.Instances.CurveSurface

set_option autoImplicit false

namespace RefModel
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2
open WeierstrassCurve.Affine

/-! ## 1. The computable decoder into the carrier -/

/-- r-torsion (decided on mathlib's own group law) puts an embedded frame in the carrier. -/
theorem mem_zpowers_of_torsion (P : FpFrame) (htor : blsR • emb P = 0) :
    Multiplicative.ofAdd (emb P) ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame)) := by
  obtain ⟨k, hk⟩ := torsion_eq_zpowers_gen (emb P) htor
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Multiplicative.ofAdd hk⟩

/-- THE COMPUTABLE DECODER. Canonical coordinates, on the curve (or the all-zero infinity frame),
    r-torsion. The torsion test is mathlib's `nsmul` on `W.Point` (binary, with `ZMod` inverses by
    extended gcd), which is decidable because `W.Point` derives `DecidableEq`. -/
def g1zOfPair? (pt : Nat × Nat) : Option G₁z :=
  if _hc : pt.1 < blsP ∧ pt.2 < blsP then
    if honc : affineOnCurve fpOps pt = true then
      if htor : blsR • emb ⟨pt, honc⟩ = 0 then
        some ⟨Multiplicative.ofAdd (emb ⟨pt, honc⟩), mem_zpowers_of_torsion ⟨pt, honc⟩ htor⟩
      else none
    else none
  else none

/-- DECODER-FIRST: what decodes is the element with those coordinates. -/
theorem g1zPair_of_g1zOfPair? {pt : Nat × Nat} {Q : G₁z} (h : g1zOfPair? pt = some Q) :
    g1zPair Q = pt := by
  unfold g1zOfPair? at h
  split at h
  · rename_i hc
    split at h
    · rename_i honc
      split at h
      · cases h
        exact ptPair_emb ⟨pt, honc⟩ hc
      · cases h
    · cases h
  · cases h

/-- ENCODER-FIRST: every carrier element is recovered from its coordinates. This is the law the
    placeholder codec could never have (its decoder is the constant `none`). -/
theorem g1zOfPair?_g1zPair (Q : G₁z) : g1zOfPair? (g1zPair Q) = some Q := by
  have hc := g1zPair_canonical Q
  have honc : affineOnCurve fpOps (g1zPair Q) = true := onCurve_ptPair (g1zPoint Q)
  have hemb : emb ⟨g1zPair Q, honc⟩ = g1zPoint Q := emb_frameOf (g1zPoint Q)
  have htor : blsR • emb ⟨g1zPair Q, honc⟩ = 0 := by
    rw [hemb]
    have h1 : (Q : G₁z) ^ blsR = 1 := pow_blsR_eq_one Q
    have h2 : g1zPoint (Q ^ blsR) = blsR • g1zPoint Q := by
      show Multiplicative.toAdd ((Q ^ blsR : G₁z) : Multiplicative W.Point) = _
      rw [Subgroup.coe_pow, toAdd_pow]; rfl
    rw [← h2, h1]; rfl
  unfold g1zOfPair?
  rw [dite_cond_eq_true (eq_true hc), dite_cond_eq_true (eq_true honc), dite_cond_eq_true (eq_true htor)]
  exact congrArg some (Subtype.ext (congrArg Multiplicative.ofAdd hemb))

/-! ## 2. The real codec -/

/-- A carrier element as the affine record `Instances/Bls12_381.lean` compresses. -/
def g1zAffine (Q : G₁z) : G1Affine :=
  let pr := g1zPair Q
  if pr.1 == 0 && pr.2 == 0 then { isInfinity := true, x := 0, y := 0 }
  else { isInfinity := false, x := (pr.1 : Fp), y := (pr.2 : Fp) }

/-- THE 48-BYTE COMPRESSED ENCODER (rust: transcript/implementors.rs:300-302 `to_bytes`, i.e.
    `G1Affine::to_compressed`): big-endian x in 48 bytes with the top three bits of byte 0 used
    as flags - bit 7 compression (always set), bit 6 infinity, bit 5 "y is the lexicographically
    larger root". The infinity encoding is 0xc0 followed by 47 zero bytes. -/
def g1zToCompressed (Q : G₁z) : Bytes := G1Affine.toCompressed (g1zAffine Q)

/-- The decode proper: flags, canonical x, the IETF sign bit, the infinity encoding
    (`G1Affine.ofCompressed?`, already in the tree and already KAT-ed against the Rust fixture),
    THEN the r-torsion test `GroupEncoding::from_bytes` performs (curves g1.rs:369-371). -/
def g1zOfCompressedRaw? (b : Bytes) : Option G₁z :=
  (G1Affine.ofCompressed? b).bind fun P =>
    if P.isInfinity then some 1 else g1zOfPair? (P.x.val, P.y.val)

/-- THE 48-BYTE COMPRESSED DECODER. The final re-encode test makes the decoder-first law hold BY
    CONSTRUCTION: the decoder returns Q only for the canonical encoding of Q. On a canonical
    string the test is a no-op, which the conformance gate measures on every point of the
    fixture. -/
def g1zOfCompressed? (b : Bytes) : Option G₁z :=
  (g1zOfCompressedRaw? b).bind fun Q => if g1zToCompressed Q = b then some Q else none

/-- THE COMPUTABLE EIP-2537 DECODER: width, canonical coordinates, curve, r-torsion. -/
def g1zOfEipC? (b : Bytes) : Option G₁z :=
  if b.size == g1Bytes then (g1Of? b).bind g1zOfPair? else none

/-- THE REAL CODEC ON THE CARRIER. All four fields are computable. -/
def g1CodecC : G1Codec G₁z where
  ofCompressed? := g1zOfCompressed?
  toCompressed := g1zToCompressed
  toEip := g1zToEip
  ofEip? := g1zOfEipC?

/-- The EIP half agrees with the exhibit's codec on the ENCODER, definitionally. -/
theorem g1CodecC_toEip : g1CodecC.toEip = g1CodecZ.toEip := rfl

/-- ... and on the DECODER, as functions: the computable decoder IS the `Classical.choose` one. So
    every theorem the tree states about `g1CodecZ.ofEip?` is a theorem about `g1CodecC.ofEip?`. -/
theorem g1CodecC_ofEip : g1CodecC.ofEip? = g1CodecZ.ofEip? := by
  classical
  funext b
  show g1zOfEipC? b = g1zOfEip? b
  by_cases hex : ∃ Q : G₁z, g1zToEip Q = b
  · have hz : g1zOfEip? b = some (Classical.choose hex) := by
      unfold g1zOfEip?; exact dif_pos hex
    have hspec : g1zToEip (Classical.choose hex) = b := Classical.choose_spec hex
    have hc := g1zPair_canonical (Classical.choose hex)
    have hsz : b.size = g1Bytes := by rw [← hspec]; exact g1PointBytes_size _
    have hof : g1Of? b = some (g1zPair (Classical.choose hex)) := by
      have h1 : g1Of? (g1zToEip (Classical.choose hex)) = some (g1zPair (Classical.choose hex)) :=
        g1Of?_g1PointBytes _ hc.1 hc.2
      rw [hspec] at h1
      exact h1
    rw [hz]
    unfold g1zOfEipC?
    rw [if_pos (beq_iff_eq.mpr hsz), hof]
    exact g1zOfPair?_g1zPair _
  · have hz : g1zOfEip? b = none := by
      unfold g1zOfEip?; exact dif_neg hex
    rw [hz]
    unfold g1zOfEipC?
    by_cases hsz : (b.size == g1Bytes) = true
    · rw [if_pos hsz]
      cases hof : g1Of? b with
      | none => rfl
      | some pt =>
          show g1zOfPair? pt = none
          cases hq : g1zOfPair? pt with
          | none => rfl
          | some Q =>
              exfalso
              apply hex
              refine ⟨Q, ?_⟩
              have hp : g1zPair Q = pt := g1zPair_of_g1zOfPair? hq
              show g1PointBytes (g1zPair Q) = b
              rw [hp]
              exact (g1Of?_some_determines (beq_iff_eq.mp hsz) hof).symm
    · rw [if_neg hsz]

/-- `Eip2537.Holds` transfers from the exhibit's codec to the computable one: `Holds` reads only
    `toEip` and `ofEip?`, and those are the same functions. -/
theorem holds_transfer (e₂ : G2Enc G2fold) (product : PairingProduct)
    {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ blsR] [Module (ZMod blsR) (Additive Gₜ)]
    [P : AdmissiblePairing G₁z G2fold Gₜ]
    (h : Eip2537.Holds g1CodecZ e₂ product) : Eip2537.Holds g1CodecC e₂ product where
  g1Valid := h.g1Valid
  g2Valid := h.g2Valid
  pairing2 := h.pairing2
  g1Add := h.g1Add
  g1Msm1 := h.g1Msm1
  g1Decodes := fun b hb hv => by
    obtain ⟨Q, hQ, hE⟩ := h.g1Decodes b hb hv
    exact ⟨Q, by rw [g1CodecC_ofEip]; exact hQ, hE⟩

/-- DECODER-FIRST for the compressed form (`G1Codec.compressedRoundtrip`), by construction. -/
theorem g1CodecC_compressedRoundtrip : g1CodecC.compressedRoundtrip := by
  intro b P h
  have h' : g1zOfCompressed? b = some P := h
  unfold g1zOfCompressed? at h'
  cases hr : g1zOfCompressedRaw? b with
  | none => rw [hr] at h'; cases h'
  | some Q =>
      rw [hr] at h'
      have h'' : (if g1zToCompressed Q = b then some Q else none) = some P := h'
      by_cases hq : g1zToCompressed Q = b
      · rw [if_pos hq] at h''
        cases h''
        exact hq
      · rw [if_neg hq] at h''
        cases h''

/-- ENCODER-FIRST for the compressed form: THE LAW `verifyMsgs` NEEDS (A-4, E-2, G-1, H-1), which
    the placeholder codec cannot satisfy and which no hypothesis of the frozen headline supplies.
    STATED, not proved here. What the proof consists of (WP-R4b): (i) `g1zOfPair?_g1zPair` above;
    (ii) `fpSqrt` is a square root on squares (p = 3 mod 4, `ZMod.euler_criterion`), so
    `rootFor x s` recovers y from x and the sign bit; (iii) the three flag bits of byte 0 are
    free because x < p < 2^381. -/
theorem g1CodecC_compressedEncoderFirst :
    ∀ Q : G₁z, g1CodecC.ofCompressed? (g1CodecC.toCompressed Q) = some Q := by
  sorry

/-- The whole law bundle at the computable codec, modulo the one stated law above: every other
    field is the exhibit's theorem transported along `g1CodecC_toEip` / `g1CodecC_ofEip`. -/
theorem g1CodecC_laws (hw : ∀ Q : G₁z, (g1zToCompressed Q).size = g1CompressedWidth) :
    G1CodecLaws g1CodecC where
  eipRoundtrip := fun b P h => g1CodecZ_eipRoundtrip b P (by rw [← g1CodecC_ofEip]; exact h)
  compressedRoundtrip := g1CodecC_compressedRoundtrip
  ofEip_toEip := fun Q => by
    rw [g1CodecC_ofEip]; exact g1CodecZ_ofEip_toEip Q
  eipShape := Midfall.Instances.CurveSurface.g1CodecZ_laws.eipShape
  toEip_one := Midfall.Instances.CurveSurface.g1CodecZ_laws.toEip_one
  compressedWidth := hw
  eipWidth := Midfall.Instances.CurveSurface.g1CodecZ_laws.eipWidth

/-! ## 3. The pairing, by construction -/

theorem g1zGen_ne_one : g1zGen ≠ 1 := by
  intro h
  have := congrArg g1zPair h
  rw [g1zPair_gen, g1zPair_one] at this
  exact absurd this (by decide)

/-- e(P, k) = k • P, curried: `ZMod r`-bilinear because `Additive G₁z` is a `ZMod r`-module. -/
def eC : (Additive G₁z) →ₗ[ZMod blsR] (Additive G2fold) →ₗ[ZMod blsR] (Additive G₁z) where
  toFun P :=
    { toFun := fun k => (k.toMul.toAdd : ZMod blsR) • P
      map_add' := fun k l => add_smul (k.toMul.toAdd : ZMod blsR) (l.toMul.toAdd) P
      map_smul' := fun m k => mul_smul m (k.toMul.toAdd : ZMod blsR) P }
  map_add' := fun P Q => LinearMap.ext fun k => smul_add (k.toMul.toAdd : ZMod blsR) P Q
  map_smul' := fun m P => LinearMap.ext fun k => smul_comm (k.toMul.toAdd : ZMod blsR) m P

/-- **THE DEPLOYMENT PAIRING, CONSTRUCTED.** Replaces the five D-P36a axioms. Its generators are
    NAMED: `g₁` is the published H1 (as a carrier element) and `g₂` is exponent 1, whose encoding
    under `g2foldToEip` is the published H2. -/
instance pairingC : AdmissiblePairing G₁z G2fold G₁z where
  e := eC
  g₁ := g1zGen
  g₂ := g2foldExp 1
  hG₁ := g1zGen_ne_one
  hG₂ := g2foldExp_one_ne_one
  hNonDeg := by
    intro h
    have h1 : eC (Additive.ofMul g1zGen) (Additive.ofMul (g2foldExp 1)) =
        ((1 : ℕ) : ZMod blsR) • Additive.ofMul g1zGen := rfl
    rw [h1, Nat.cast_one, one_smul] at h
    exact g1zGen_ne_one (Additive.ofMul.injective h)
  decEqG₁ := inferInstance
  decEqGₜ := inferInstance

theorem pairingC_g1 : pairingC.g₁ = g1zGen := rfl
theorem pairingC_g2 : pairingC.g₂ = g2foldExp 1 := rfl

/-- `Eip2537.Holds` is exhibited with NO pairing axiom: `holds_staged` is generic in Gₜ. -/
theorem holds_exhibited_noAxiom :
    ∃ product : PairingProduct, Eip2537.Holds g1CodecZ g2CodecFold product :=
  holds_staged (Gₜ := G₁z)

/-- ... and at the COMPUTABLE codec, which is the one the deployment should install. -/
theorem holds_exhibited_C :
    ∃ product : PairingProduct, Eip2537.Holds g1CodecC g2CodecFold product := by
  obtain ⟨product, h⟩ := holds_exhibited_noAxiom
  exact ⟨product, holds_transfer g2CodecFold product h⟩

#print axioms pairingC
#print axioms holds_exhibited_noAxiom
#print axioms g1zOfPair?_g1zPair
#print axioms holds_exhibited_C
#print axioms g1CodecC_ofEip
#print axioms g1CodecC_compressedRoundtrip
#print axioms g1CodecC_laws

end RefModel
