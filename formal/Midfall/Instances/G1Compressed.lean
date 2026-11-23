-- |
-- Midfall.Instances.G1Compressed
--
-- REF.4 (card) / D-P62 (decision): A REAL, COMPUTABLE G1 CODEC ON G₁z.
--
-- `g1CodecZ` (Instances/G1Agreement.lean:2002) is a `noncomputable` codec whose
-- `ofCompressed?` is the constant `none`: it can encode a carrier element but can
-- never read one back, so nothing that has to DECODE a 48-byte proof point - which is
-- every read on the verifier's transcript path - can run over it. That is the reason
-- the reference gate (REF.8) could not execute the tree's own `prepare` on real
-- bytes. This file replaces the placeholder's compressed half with a decoder that
-- COMPUTES, and transfers the exhibit's theorems along the proof that the EIP halves
-- are the same function, so nothing already proved about `g1CodecZ` is restated.
--
-- HOW THE DECODER IS COMPUTABLE WITHOUT A DISCRETE LOG. The carrier `G₁z` is
-- `Subgroup.zpowers` of the published H1, so an element of it IS an r-torsion point
-- of the curve, and `G1PointCount.torsion_eq_zpowers_gen` says the converse. So
-- membership is decidable by the torsion test `blsR • P = 0` - mathlib's binary
-- `nsmul` over `W.Point`, which terminates because the inductive derives
-- `DecidableEq`. No discrete log is taken anywhere: the witness that RefModel
-- produced by `Classical.choose` is reconstructed as a subtype element whose
-- membership proof is that decidable test.
--
-- THE ENCODER-FIRST COMPRESSED LAW IS PROVED HERE (B3 REF.9/REF.10): `fpSqrt`
-- recovers y from x and the sign bit (p = 3 mod 4), the flag bits are decoded by the
-- affine codec, and the carrier's unique pair closes the loop. The only computational
-- inputs outside the kernel are the two concrete rejections `g1zOfPair? (0, 2) = none`
-- and `g1zOfPair? (0, pBase-2) = none` (the order-3 points excluded by the r-torsion
-- test), discharged by `native_decide` inside `Midfall/Instances/` per D-P17. Every
-- law the deployment's own headline reads is proved here or transported from the
-- exhibit.

import Midfall.Instances.G1PointCount
import Midfall.Instances.G1Agreement
import Midfall.Instances.HoldsStaging
import Midfall.Instances.Bls12_381
import Midfall.Instances.G2Codec
import Midfall.Instances.CurveSurface
import Midfall.LoweringV3.Statements

set_option autoImplicit false

namespace Midfall.Instances
open Midfall Midfall.Yul Midfall.Assumptions Midfall.Halo2
open WeierstrassCurve.Affine

/-! ## 1. The computable decoder into the carrier -/

/-- r-torsion (decided on mathlib's own group law) puts an embedded frame in the
    carrier: `torsion_eq_zpowers_gen` answers with an integer exponent, and
    `Subgroup.mem_zpowers_iff` takes exactly that. -/
theorem mem_zpowers_of_torsion (P : FpFrame) (htor : blsR • emb P = 0) :
    Multiplicative.ofAdd (emb P) ∈ Subgroup.zpowers (Multiplicative.ofAdd (emb genFrame)) := by
  obtain ⟨k, hk⟩ := torsion_eq_zpowers_gen (emb P) htor
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Multiplicative.ofAdd hk⟩

/-- **THE COMPUTABLE DECODER** (REF.4). Canonical coordinates, on the curve (or the
    all-zero infinity frame), r-torsion. Each of the three tests is a `Bool` decision,
    so this is a `def`, not a `noncomputable def` - which is the whole point of the
    card. -/
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

/-- ENCODER-FIRST on the COORDINATES: every carrier element is recovered from its
    pair. This is the half the placeholder codec could never have, and it is what
    makes `g1CodecC.ofEip?` the same function as `g1CodecZ.ofEip?`. -/
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
  rw [dite_cond_eq_true (eq_true hc), dite_cond_eq_true (eq_true honc),
      dite_cond_eq_true (eq_true htor)]
  exact congrArg some (Subtype.ext (congrArg Multiplicative.ofAdd hemb))

/-! ## 2. The real codec -/

/-- A carrier element as the affine record `Instances/Bls12_381.lean` compresses. -/
def g1zAffine (Q : G₁z) : G1Affine :=
  let pr := g1zPair Q
  if pr.1 == 0 && pr.2 == 0 then { isInfinity := true, x := 0, y := 0 }
  else { isInfinity := false, x := (pr.1 : Fp), y := (pr.2 : Fp) }

/-- **THE 48-BYTE COMPRESSED ENCODER** (rust: transcript/implementors.rs:300-302
    `to_bytes`, i.e. `G1Affine::to_compressed`): big-endian x in 48 bytes with the
    top three bits of byte 0 used as flags - bit 7 compression (always set), bit 6
    infinity, bit 5 "y is the lexicographically larger root". The infinity encoding
    is 0xc0 followed by 47 zero bytes. -/
def g1zToCompressed (Q : G₁z) : Bytes := G1Affine.toCompressed (g1zAffine Q)

/-- The decode proper: flags, canonical x, the IETF sign bit, the infinity encoding
    (`G1Affine.ofCompressed?`, already in the tree and already KAT-ed against the
    Rust fixture), THEN the r-torsion test `GroupEncoding::from_bytes` performs
    (curves g1.rs:369-371). -/
def g1zOfCompressedRaw? (b : Bytes) : Option G₁z :=
  (G1Affine.ofCompressed? b).bind fun P =>
    if P.isInfinity then some 1 else g1zOfPair? (P.x.val, P.y.val)

/-- **THE 48-BYTE COMPRESSED DECODER.** The final re-encode test makes the
    decoder-first law hold BY CONSTRUCTION: the decoder returns Q only for the
    canonical encoding of Q. On a canonical string the test is a no-op, which the
    conformance gate measures on every point of the fixture
    (`Midfall.Instances.NativeReplay.g1CodecC_fixturePoints_ok`). -/
def g1zOfCompressed? (b : Bytes) : Option G₁z :=
  (g1zOfCompressedRaw? b).bind fun Q => if g1zToCompressed Q = b then some Q else none

/-- **THE COMPUTABLE EIP-2537 DECODER**: width, canonical coordinates, curve,
    r-torsion. -/
def g1zOfEipC? (b : Bytes) : Option G₁z :=
  if b.size == g1Bytes then (g1Of? b).bind g1zOfPair? else none

/-- **THE REAL CODEC ON THE CARRIER** (REF.4). All four fields are computable, which
    is what the card asked for and what `g1CodecZ` is not. -/
def g1CodecC : G1Codec G₁z where
  ofCompressed? := g1zOfCompressed?
  toCompressed := g1zToCompressed
  toEip := g1zToEip
  ofEip? := g1zOfEipC?

/-- The EIP half agrees with the exhibit's codec on the ENCODER, definitionally. -/
theorem g1CodecC_toEip : g1CodecC.toEip = g1CodecZ.toEip := rfl

/-- ... and on the DECODER, as functions: the computable decoder IS the
    `Classical.choose` one. So every theorem the tree states about
    `g1CodecZ.ofEip?` is a theorem about `g1CodecC.ofEip?`. -/
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

/-- `Eip2537.Holds` transfers from the exhibit's codec to the computable one:
    `Holds` reads only `toEip` and `ofEip?`, and those are the same functions. This
    is why no theorem of the exhibit had to be reproved. -/
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

/-- DECODER-FIRST for the compressed form (`G1Codec.compressedRoundtrip`), by
    construction: the re-encode test inside `g1zOfCompressed?` IS the law. -/
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

theorem g1Affine_ofCompressed_toCompressed_inf :
    G1Affine.ofCompressed? (G1Affine.toCompressed (⟨true, 0, 0⟩ : G1Affine)) =
      some ⟨true, 0, 0⟩ := by
  unfold G1Affine.toCompressed
  rw [if_pos (by rfl : (⟨true, 0, 0⟩ : G1Affine).isInfinity = true)]
  set b : Bytes := ByteArray.mk (List.toArray (Nat.toUInt8 192 :: List.replicate 47 (0 : UInt8))) with hb
  have hsize : b.size = 48 := by rw [hb]; decide
  have hget : (Option.map (fun u => u.toNat) b.data[0]?).getD 0 = 192 := by rw [hb]; decide
  have hbytes : bytesToNatBE (ByteArray.mk (b.data.extract 1 48)) = 0 := by rw [hb]; decide
  unfold G1Affine.ofCompressed?
  rw [if_neg (by rw [hsize]; decide)]
  rw [hget]
  have h2 : (192 >>> 5) >>> 2 = 1 := by decide
  have h1 : ((192 >>> 5) >>> 1) &&& 1 = 1 := by decide
  have hz : (192 &&& 0x3f) = 0 := by decide
  simp [h2, h1, hz, hbytes]

theorem natToBytesBE_size_local (n len : Nat) : (natToBytesBE n len).size = len := by
  show (ByteArray.mk ((Midfall.natToBytesLowFirst.go n len ByteArray.empty).data.toList.reverse.toArray)).size = len
  rw [show (ByteArray.mk ((Midfall.natToBytesLowFirst.go n len ByteArray.empty).data.toList.reverse.toArray)).size
      = (Midfall.natToBytesLowFirst.go n len ByteArray.empty).data.toList.length by
    rw [← ByteArray.size_data, List.size_toArray, List.length_reverse]]
  rw [show (Midfall.natToBytesLowFirst.go n len ByteArray.empty).data.toList.length
      = (Midfall.natToBytesLowFirst.go n len ByteArray.empty).size by
    rw [Array.length_toList, ByteArray.size_data]]
  have hgo : ∀ (k n : Nat) (acc : Bytes),
      (Midfall.natToBytesLowFirst.go n k acc).size = acc.size + k := by
    intro k
    induction k with
    | zero => intro n acc; rfl
    | succ j ih =>
        intro n acc
        rw [show Midfall.natToBytesLowFirst.go n (j+1) acc =
          Midfall.natToBytesLowFirst.go (n/256) j (acc.push (Nat.toUInt8 (n % 256))) from rfl, ih]
        simp [ByteArray.size_push]; omega
  rw [hgo]; simp

theorem natToBytesBE_one_local (n : Nat) :
    (natToBytesBE n 1).data.toList = [Nat.toUInt8 (n % 256)] := by
  show (Midfall.natToBytesLowFirst n 1).data.toList.reverse = _
  rw [show Midfall.natToBytesLowFirst n 1 =
      Midfall.natToBytesLowFirst.go (n/256) 0 (Bytes.empty.push (Nat.toUInt8 (n % 256))) from rfl]
  rfl

theorem natToBytesBE_head_local (n len : Nat) (h : 0 < len) :
    (natToBytesBE n len).data.toList =
      Nat.toUInt8 (n / 256^(len-1) % 256) ::
        (natToBytesBE (n % 256^(len-1)) (len-1)).data.toList := by
  have hm : len - 1 + 1 = len := by omega
  have hsplit := natToBytesBE_split (hi := n / 256^(len-1)) (lo := n % 256^(len-1))
    (m := len-1) (by exact Nat.mod_lt _ (by positivity)) 1
  rw [Nat.mul_comm (n / 256 ^ (len - 1)) (256 ^ (len - 1)),
      Nat.div_add_mod, hm] at hsplit
  rw [hsplit]
  simp [natToBytesBE_one_local]

theorem fpSqrt_sq (a : Fp) (h : IsSquare a) : fpSqrt a ^ 2 = a := by
  obtain ⟨y, rfl⟩ := h
  unfold fpSqrt
  have h4 : pBase % 4 = 3 := pBase_mod_four
  by_cases hy : y = 0
  · rw [hy, mul_zero, zero_pow (by omega : (pBase + 1) / 4 ≠ 0), zero_pow (by norm_num : 2 ≠ 0)]
  · have hstep1 : ((y * y) ^ ((pBase + 1) / 4)) ^ 2
        = y ^ (2 * (2 * ((pBase + 1) / 4))) := by
      rw [mul_pow, ← pow_two, ← pow_mul, ← pow_mul]
      ring_nf
    rw [hstep1]
    rw [show 2 * (2 * ((pBase + 1) / 4)) = pBase + 1 by omega]
    rw [show pBase + 1 = (pBase - 1) + 2 by omega, pow_add,
      ZMod.pow_card_sub_one_eq_one hy, one_mul, pow_two]

theorem rf_ts (s : Fp) :
    (if true == (s == (if true == true then s else -s)) then s else -s) = s := by
  simp

theorem rf_fs (s : Fp) (hbeq : (s == -s) = false) :
    (if false == (s == (if false == true then s else -s)) then s else -s) = s := by
  simp [hbeq]

theorem rf_tn (s : Fp) (hbeq : (s == -s) = false) :
    (if true == (-s == (if true == true then s else -s)) then s else -s) = -s := by
  have hbeq' : (-s == s) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact (beq_eq_false_iff_ne.mp hbeq) h.symm
  simp [hbeq']

theorem rf_fn (s : Fp) :
    (if false == (-s == (if false == true then s else -s)) then s else -s) = -s := by
  simp

theorem rootFor_recover (x y : Fp) (hy : y * y = x * x * x + 4) :
    rootFor x (y == rootFor x true) = y := by
  set s := fpSqrt (x * x * x + 4) with hs
  have hs2 : s * s = x * x * x + 4 := by
    have h := fpSqrt_sq (x * x * x + 4) ⟨y, hy.symm⟩
    rw [← hs] at h
    simpa [pow_two] using h
  have hy2 : y * y = s * s := by rw [hy, hs2]
  have hroot : ∀ b : Bool, rootFor x b =
      if (decide (s.val > (-s).val)) == b then s else -s := by
    intro b
    unfold rootFor
    rw [show fpSqrt (x * x * x + 4) = s from hs.symm]
  rcases eq_or_eq_neg_of_sq_eq_sq y s (by simpa [pow_two] using hy2) with h | h
  · subst h
    by_cases he : s = -s
    · have hrootS : ∀ b : Bool, rootFor x b = s := by
        intro b
        rw [hroot b]
        split_ifs <;> first | rfl | exact he.symm
        all_goals omega
      rw [hrootS]
    · have hbeq : (s == -s) = false := by
        rw [beq_eq_false_iff_ne]; exact he
      rw [hroot (s == rootFor x true), hroot true]
      by_cases hct : decide (s.val > (-s).val) = true
      · rw [hct]; exact rf_ts s
      · have hcf : decide (s.val > (-s).val) = false := by
          cases h : decide (s.val > (-s).val) with
          | false => rfl
          | true => exact absurd h hct
        rw [hcf]; exact rf_fs s hbeq
  · subst h
    by_cases he : s = -s
    · have hrootS : ∀ b : Bool, rootFor x b = s := by
        intro b
        rw [hroot b]
        split_ifs <;> first | rfl | exact he.symm
        all_goals omega
      rw [hrootS]
      exact he
    · have hbeq : (s == -s) = false := by
        rw [beq_eq_false_iff_ne]; exact he
      rw [hroot (-s == rootFor x true), hroot true]
      by_cases hct : decide (s.val > (-s).val) = true
      · rw [hct]; exact rf_tn s hbeq
      · have hcf : decide (s.val > (-s).val) = false := by
          cases h : decide (s.val > (-s).val) with
          | false => rfl
          | true => exact absurd h hct
        rw [hcf]; exact rf_fn s

theorem pBase_lt_20_pow (x : Nat) (hx : x < pBase) : x / 256^47 % 256 < 32 := by
  have hp : pBase < 0x20 * 256^47 := by
    calc pBase < 2^381 := by decide
      _ = 0x20 * 256^47 := by decide
  have hlt : x < 0x20 * 256^47 := lt_trans hx hp
  have hdiv : x / 256^47 < 0x20 := Nat.div_lt_of_lt_mul hlt
  omega

theorem pBase_le_256_48 : pBase ≤ 256^48 := by
  have h1 : pBase < 2^381 := by decide
  have h2 : (2:Nat)^381 ≤ 256^48 := by
    have h256 : (256:Nat) = 2^8 := by decide
    rw [h256, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

theorem enc_flags (b0 sign : Nat) (hb0 : b0 < 32) (hsign : sign = 0 ∨ sign = 1) :
    let byte := Nat.toUInt8 ((b0 &&& 0x1f) ||| 0x80 ||| (sign <<< 5))
    byte.toNat &&& 0x1f = b0 ∧
    (byte.toNat >>> 5) >>> 2 = 1 ∧
    ((byte.toNat >>> 5) >>> 1) &&& 1 = 0 ∧
    (byte.toNat >>> 5) &&& 1 = sign := by
  rcases hsign with rfl | rfl <;> interval_cases b0 <;> decide

theorem enc_eq' (P : G1Affine) (hinf : P.isInfinity = false) (xb : Bytes) (b0 sign : Nat) (b' : UInt8)
    (hxb : xb = natToBytesBE P.x.val 48)
    (hb0 : b0 = P.x.val / 256^47 % 256)
    (hsign : sign = if P.y == rootFor P.x true then 1 else 0)
    (hb' : b' = Nat.toUInt8 ((b0 &&& 0x1f) ||| 0x80 ||| (sign <<< 5))) :
    G1Affine.toCompressed P = ByteArray.mk (List.toArray (b' :: (natToBytesBE P.x.val 48).data.toList.drop 1)) := by
  subst xb
  subst b0
  subst sign
  subst b'
  have hb0eval : ((natToBytesBE P.x.val 48).data[0]?.map (fun u => u.toNat)).getD 0 =
      P.x.val / 256^47 % 256 := by
    have hhead : (natToBytesBE P.x.val 48).data[0]? =
        some (Nat.toUInt8 (P.x.val / 256^47 % 256)) := by
      rw [show (natToBytesBE P.x.val 48).data[0]? =
        (natToBytesBE P.x.val 48).data.toList[0]? from by simp]
      rw [natToBytesBE_head_local _ 48 (by omega)]
      simp
    rw [hhead]
    have hlt : P.x.val / 256^47 % 256 < 256 := Nat.mod_lt _ (by decide)
    simp [Nat.mod_eq_of_lt hlt]
  unfold G1Affine.toCompressed
  rw [if_neg (by simp [hinf])]
  dsimp only
  rw [hb0eval]

theorem g1Affine_ofCompressed_toCompressed_nonInf (P : G1Affine)
    (hinf : P.isInfinity = false)
    (honc : P.onCurve = true)
    (hx0 : P.x.val ≠ 0) :
    G1Affine.ofCompressed? (G1Affine.toCompressed P) = some P := by
  let xb := natToBytesBE P.x.val 48
  let b0 := P.x.val / 256^47 % 256
  let sign := if P.y == rootFor P.x true then 1 else 0
  let b' := Nat.toUInt8 ((b0 &&& 0x1f) ||| 0x80 ||| (sign <<< 5))
  have hxb : xb = natToBytesBE P.x.val 48 := rfl
  have hb0def : b0 = P.x.val / 256^47 % 256 := rfl
  have hsigndef : sign = (if P.y == rootFor P.x true then 1 else 0) := rfl
  have hb'def : b' = Nat.toUInt8 ((b0 &&& 0x1f) ||| 0x80 ||| (sign <<< 5)) := rfl
  have hxb_len : xb.data.toList.length = 48 := by
    rw [hxb]; simp [ByteArray.size_data, natToBytesBE_size_local]
  have hxb_head : xb.data.toList = Nat.toUInt8 b0 :: xb.data.toList.drop 1 := by
    rw [hxb, show Nat.toUInt8 b0 = Nat.toUInt8 (P.x.val / 256^(48-1) % 256) from by rw [hb0def]]
    rw [natToBytesBE_head_local _ 48 (by omega)]
    rw [show (48 - 1) = 47 from rfl]
    simp
  have hb0lt : b0 < 32 := by
    rw [hb0def]; exact pBase_lt_20_pow P.x.val P.x.val_lt
  have hsignle : sign = 0 ∨ sign = 1 := by
    rw [hsigndef]; split <;> omega
  obtain ⟨hflagand, hflag2, hflaginf, hflagsign⟩ := enc_flags b0 sign hb0lt hsignle
  have hb'lto : b'.toNat < 256 := by
    rw [hb'def]; exact Nat.mod_lt _ (by decide)
  have hb'and : b'.toNat &&& 0x1f = b0 := by
    rw [hb'def]; exact hflagand
  have hb'2 : (b'.toNat >>> 5) >>> 2 = 1 := by rw [hb'def]; exact hflag2
  have hb'inf : ((b'.toNat >>> 5) >>> 1) &&& 1 = 0 := by rw [hb'def]; exact hflaginf
  have hb'sign : (b'.toNat >>> 5) &&& 1 = sign := by rw [hb'def]; exact hflagsign
  have henc : G1Affine.toCompressed P =
      ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1)) :=
    enc_eq' P hinf xb b0 sign b' hxb hb0def hsigndef hb'def
  have honcEq : P.y * P.y = P.x * P.x * P.x + 4 := by
    have h := honc
    rw [G1Affine.onCurve, hinf] at h
    simpa using (beq_iff_eq.mp h)
  rw [henc]
  unfold G1Affine.ofCompressed?
  have hsize : (ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1))).size = 48 := by
    rw [← ByteArray.size_data]
    show (List.toArray (b' :: xb.data.toList.drop 1)).size = 48
    rw [List.size_toArray]
    simp [hxb_len]
  rw [if_neg (by rw [hsize]; decide)]
  dsimp only
  have hhead : (ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1))).data[0]? = some b' := by
    simp
  rw [show ((ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1))).data[0]?.map
        (fun u => u.toNat)).getD 0 = b'.toNat from by rw [hhead]; rfl]
  have hflags2' : ((b'.toNat >>> 5) >>> 2 == 0) = false := by rw [hb'2]; decide
  rw [if_neg (by simpa using hflags2')]
  have hflagsinf' : ((((b'.toNat >>> 5) >>> 1) &&& 1 == 1)) = false := by rw [hb'inf]; decide
  rw [if_neg (by simpa using hflagsinf')]
  -- xbytes = xb
  have hxbytes : ByteArray.mk
      (List.toArray (Nat.toUInt8 (b'.toNat &&& 0x1f) ::
        (ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1))).data.toList.drop 1)) = xb := by
    rw [hb'and]
    have hdrop : (ByteArray.mk (List.toArray (b' :: xb.data.toList.drop 1))).data.toList.drop 1 =
        xb.data.toList.drop 1 := by simp
    rw [hdrop]
    rw [← hxb_head]
  rw [hxbytes]
  have hxn : bytesToNatBE xb = P.x.val := by
    rw [hxb, bytesToNatBE_natToBytesBE,
      Nat.mod_eq_of_lt (lt_of_lt_of_le P.x.val_lt pBase_le_256_48)]
  rw [hxn]
  rw [if_neg (not_le.mpr (ZMod.val_lt P.x))]
  rw [if_neg (by simpa [beq_iff_eq] using hx0)]
  -- sign and y
  have hsignbit : ((b'.toNat >>> 5) &&& 1 == 1) = (P.y == rootFor P.x true) := by
    rw [hb'sign]
    rw [hsigndef]
    by_cases h : P.y == rootFor P.x true <;> simp [h]
  have hy : rootFor ((P.x.val : Nat) : Fp) (((b'.toNat >>> 5) &&& 1 == 1)) = P.y := by
    rw [hsignbit, show ((P.x.val : Nat) : Fp) = P.x from ZMod.natCast_zmod_val P.x]
    exact rootFor_recover P.x P.y honcEq
  have hP : (⟨false, ((P.x.val : Nat) : Fp),
      rootFor ((P.x.val : Nat) : Fp) (((b'.toNat >>> 5) &&& 1 == 1))⟩ : G1Affine) = P := by
    cases P with
    | mk inf x y =>
        rw [G1Affine.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · exact hinf.symm
        · exact ZMod.natCast_zmod_val x
        · simpa using hy
  rw [hP, if_pos honc]

theorem onCurve_of_ptPair_record (pr : Nat × Nat)
    (hcan : pr.1 < pBase ∧ pr.2 < pBase)
    (h : affineOnCurve fpOps pr = true)
    (hne : pr ≠ (0, 0)) :
    (⟨false, (pr.1 : Fp), (pr.2 : Fp)⟩ : G1Affine).onCurve = true := by
  have hca : pr.1 < blsP := hcan.1
  have hcb : pr.2 < blsP := hcan.2
  have hinf : affineIsInfinity fpOps pr = false := by
    cases hb : affineIsInfinity fpOps pr with
    | false => rfl
    | true =>
        exfalso
        apply hne
        cases pr with
        | mk a b =>
            change a < blsP at hca
            change b < blsP at hcb
            simp only [affineIsInfinity, fpOps, Bool.and_eq_true, beq_iff_eq] at hb
            have ha : a = 0 := by
              have h1 := hb.1
              rw [Nat.mod_eq_of_lt hca] at h1
              simpa using h1
            have hb0 : b = 0 := by
              have h2 := hb.2
              rw [Nat.mod_eq_of_lt hcb] at h2
              simpa using h2
            exact Prod.ext ha hb0
  have hcast : (pr.2 : Fp) * pr.2 = (pr.1 : Fp) * pr.1 * pr.1 + 4 := by
    have hh := h
    simp only [affineOnCurve, hinf, Bool.false_or] at hh
    dsimp only [fpOps] at hh
    simp only [g1B] at hh
    have hnat := beq_iff_eq.mp hh
    rw [Midfall.Assumptions.blsP_eq_pBase] at hnat
    simp only [Nat.mod_mod] at hnat
    have hc := congrArg (fun n : Nat => (n : Fp)) hnat
    simp [Nat.cast_mul, Nat.cast_add, ZMod.natCast_mod] at hc
    exact hc
  rw [G1Affine.onCurve, Bool.false_or, beq_iff_eq]
  simpa [Nat.cast_mul, Nat.cast_add] using hcast
theorem g1zPair_ne_zero_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) : g1zPair Q ≠ (0, 0) := by
  intro h
  apply hQ
  have hpair : ptPair (g1zPoint Q) = ptPair (0 : W.Point) := by
    rw [ptPair_zero]; exact h
  have hpt := ptPair_injective hpair
  exact Subtype.ext (congrArg Multiplicative.ofAdd hpt)

theorem g1zAffine_eq_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) :
    g1zAffine Q = ⟨false, ((g1zPair Q).1 : Fp), ((g1zPair Q).2 : Fp)⟩ := by
  unfold g1zAffine
  have hne := g1zPair_ne_zero_of_ne_one Q hQ
  have hcond : ¬ ((g1zPair Q).1 == 0 && (g1zPair Q).2 == 0) = true := by
    intro h
    apply hne
    have hh := h
    simp only [Bool.and_eq_true] at hh
    exact Prod.ext (beq_iff_eq.mp hh.1) (beq_iff_eq.mp hh.2)
  rw [if_neg hcond]

theorem g1zAffine_onCurve_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) :
    (g1zAffine Q).onCurve = true := by
  rw [g1zAffine_eq_of_ne_one Q hQ]
  exact onCurve_of_ptPair_record (g1zPair Q) (g1zPair_canonical Q)
    (onCurve_ptPair (g1zPoint Q)) (g1zPair_ne_zero_of_ne_one Q hQ)

theorem g1zAffine_x_val_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) :
    (g1zAffine Q).x.val = (g1zPair Q).1 := by
  rw [g1zAffine_eq_of_ne_one Q hQ]
  show ((g1zPair Q).1 : Fp).val = (g1zPair Q).1
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← Midfall.Assumptions.blsP_eq_pBase]; exact (g1zPair_canonical Q).1)]

theorem g1zAffine_y_val_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) :
    (g1zAffine Q).y.val = (g1zPair Q).2 := by
  rw [g1zAffine_eq_of_ne_one Q hQ]
  show ((g1zPair Q).2 : Fp).val = (g1zPair Q).2
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← Midfall.Assumptions.blsP_eq_pBase]; exact (g1zPair_canonical Q).2)]

theorem g1zAffine_x_ne_zero_of_ne_one (Q : G₁z) (hQ : Q ≠ 1) :
    (g1zAffine Q).x.val ≠ 0 := by
  intro hx0
  have hx : (g1zPair Q).1 = 0 := by
    rw [← g1zAffine_x_val_of_ne_one Q hQ]; exact hx0
  have honc := g1zAffine_onCurve_of_ne_one Q hQ
  rw [g1zAffine_eq_of_ne_one Q hQ, G1Affine.onCurve, Bool.false_or, beq_iff_eq] at honc
  rw [hx] at honc
  have hy2 : ((g1zPair Q).2 : Fp) * ((g1zPair Q).2 : Fp) = 4 := by
    simpa using honc
  have hyroot : ((g1zPair Q).2 : Fp) = 2 ∨ ((g1zPair Q).2 : Fp) = -2 := by
    have h : (((g1zPair Q).2 : Fp) - 2) * (((g1zPair Q).2 : Fp) + 2) = 0 := by
      linear_combination hy2
    rcases mul_eq_zero.mp h with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hpair := g1zOfPair?_g1zPair Q
  have hval : ((g1zPair Q).2 : Fp).val = (g1zPair Q).2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← Midfall.Assumptions.blsP_eq_pBase]; exact (g1zPair_canonical Q).2)]
  have h2val : ((2 : Fp)).val = 2 := by
    rw [show (2 : Fp) = ((2 : Nat) : Fp) from rfl, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by decide : 2 < pBase)]
  have hneg2val : ((-2 : Fp)).val = pBase - 2 := by
    haveI : NeZero (2 : Fp) := ⟨by
      intro h
      have hv := congrArg ZMod.val h
      rw [h2val, ZMod.val_zero] at hv
      omega⟩
    rw [ZMod.val_neg_of_ne_zero (2 : Fp), h2val]
  have hyval : (g1zPair Q).2 = 2 ∨ (g1zPair Q).2 = pBase - 2 := by
    rcases hyroot with hy | hy
    · left
      have := congrArg ZMod.val hy
      rw [hval, h2val] at this
      exact this
    · right
      have := congrArg ZMod.val hy
      rw [hval, hneg2val] at this
      exact this
  rcases hyval with hy | hy
  · have hpair' : g1zPair Q = (0, 2) := Prod.ext hx hy
    rw [hpair'] at hpair
    have hnone : g1zOfPair? (0, 2) = none := by native_decide
    rw [hnone] at hpair
    cases hpair
  · have hpair' : g1zPair Q = (0, pBase - 2) := Prod.ext hx hy
    rw [hpair'] at hpair
    have hnone : g1zOfPair? (0, pBase - 2) = none := by native_decide
    rw [hnone] at hpair
    cases hpair


/-- **ENCODER-FIRST for the compressed form** - the law `verifyMsgs` needs (A-4, E-2,
    G-1, H-1), which the placeholder codec cannot satisfy and which no hypothesis of
    the frozen headline supplies. The field core (`fpSqrt_sq`, `rootFor_recover`), the
    first-byte flags and the byte plumbing are the lemmas above; the statement is the
    usual compressed round trip on the carrier. -/
theorem g1CodecC_compressedEncoderFirst :
    ∀ Q : G₁z, g1CodecC.ofCompressed? (g1CodecC.toCompressed Q) = some Q := by
  intro Q
  show g1zOfCompressed? (g1zToCompressed Q) = some Q
  by_cases hQ : Q = 1
  · subst Q
    have hP : g1zAffine 1 = ⟨true, 0, 0⟩ := by simp [g1zAffine, g1zPair_one]
    have hdec : G1Affine.ofCompressed? (g1zToCompressed 1) = some ⟨true, 0, 0⟩ := by
      show G1Affine.ofCompressed? (G1Affine.toCompressed (g1zAffine 1)) = some ⟨true, 0, 0⟩
      rw [hP]
      exact g1Affine_ofCompressed_toCompressed_inf
    have hraw : g1zOfCompressedRaw? (g1zToCompressed 1) = some 1 := by
      unfold g1zOfCompressedRaw?
      rw [hdec]
      simp
    unfold g1zOfCompressed?
    rw [hraw]
    simp
  · have hP := g1zAffine_eq_of_ne_one Q hQ
    have hnotinf : (g1zAffine Q).isInfinity = false := by rw [hP]
    have hdec : G1Affine.ofCompressed? (g1zToCompressed Q) = some (g1zAffine Q) := by
      show G1Affine.ofCompressed? (G1Affine.toCompressed (g1zAffine Q)) = some (g1zAffine Q)
      exact g1Affine_ofCompressed_toCompressed_nonInf (g1zAffine Q) hnotinf
        (g1zAffine_onCurve_of_ne_one Q hQ) (g1zAffine_x_ne_zero_of_ne_one Q hQ)
    have hraw : g1zOfCompressedRaw? (g1zToCompressed Q) = some Q := by
      unfold g1zOfCompressedRaw?
      rw [hdec]
      simp only [Option.bind]
      rw [if_neg (by rw [hnotinf]; decide)]
      rw [g1zAffine_x_val_of_ne_one Q hQ, g1zAffine_y_val_of_ne_one Q hQ]
      exact g1zOfPair?_g1zPair Q
    unfold g1zOfCompressed?
    rw [hraw]
    simp

theorem byteArray_size_mk_toArray (l : List UInt8) :
    (ByteArray.mk l.toArray).size = l.length := by
  rw [← ByteArray.size_data]
  exact List.size_toArray

/-- The compressed width is `g1CompressedWidth` for every affine point. -/
theorem g1Affine_toCompressed_width (P : G1Affine) :
    (G1Affine.toCompressed P).size = g1CompressedWidth := by
  unfold G1Affine.toCompressed
  by_cases h : P.isInfinity = true
  · rw [if_pos h]
    decide
  · rw [if_neg h]
    have hxb := natToBytesBE_size_local P.x.val 48
    have hlen : (natToBytesBE P.x.val 48).data.toList.length = 48 := by
      rw [Array.length_toList, ByteArray.size_data]
      exact hxb
    rw [byteArray_size_mk_toArray, List.length_cons, List.length_drop, hlen]
    rfl

/-- The compressed width at the carrier. -/
theorem g1zToCompressed_width (Q : G₁z) :
    (g1zToCompressed Q).size = g1CompressedWidth :=
  g1Affine_toCompressed_width (g1zAffine Q)

/-- The whole frozen law bundle at the computable codec: every field is the exhibit's
    theorem transported along `g1CodecC_toEip` / `g1CodecC_ofEip`; the compressed width
    is `hw`. -/
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

/-- **THE FULL V3 LAW BUNDLE AT THE COMPUTABLE CODEC.** The seven frozen laws come from
    `g1CodecC_laws` at the just-proved compressed width; the eighth is
    `g1CodecC_compressedEncoderFirst`. This is the `G1CodecLawsV3` conjunct of `GateAtV3`
    and the codec bundle `ValidV3` reads. -/
theorem g1CodecC_lawsV3 : Midfall.LoweringV3.G1CodecLawsV3 g1CodecC :=
  { toG1CodecLaws := g1CodecC_laws g1zToCompressed_width
    compressedEncoderFirst := g1CodecC_compressedEncoderFirst }

#print axioms Midfall.Instances.g1zToCompressed_width
#print axioms Midfall.Instances.g1CodecC_compressedEncoderFirst
#print axioms Midfall.Instances.g1CodecC_lawsV3

#print axioms g1zPair_of_g1zOfPair?
#print axioms g1zOfPair?_g1zPair
#print axioms g1CodecC_ofEip
#print axioms g1CodecC_compressedRoundtrip
#print axioms holds_transfer
#print axioms g1CodecC_laws

end Midfall.Instances
