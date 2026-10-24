-- |
-- Midfall.Instances.Bls12_381
--
-- A concrete BLS12-381 G1 CODEC, sufficient to replay the Rust verifier's
-- transcript on real proof bytes. This is the curve instance R-28 and R-33 said
-- was still owed, scoped to what Phase 3 conformance actually needs.
--
-- WHAT THIS IS: real base-field arithmetic. Points are affine (x, y) with an
-- explicit infinity flag, decompression takes a genuine square root, and the
-- on-curve test is the curve equation.
--
-- WHAT THIS IS NOT: a group. There is no addition, no scalar multiplication and
-- no pairing, so this does not instantiate AdmissiblePairing and no theorem
-- depends on it. The dependency runs Instances -> Exec, never back.
--
-- WHY THAT SUFFICES. The Fiat-Shamir chain only ever ENCODES G1 points (to_input
-- = the 128-byte EIP-2537 form) and DECODES them from the proof (48-byte
-- compressed wire). Neither needs the group law. So the transcript - the most
-- safety-critical leaf, and the one docs/REVIEW.md R-20 found broken - can be
-- checked against real Rust output with this file alone. Plan Section 5
-- sanctions exactly this: compare the pairing inputs when the pairing is not
-- executable.

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Assumptions.Pairing

namespace Midfall.Instances

open Midfall

/-- The base field. rust: curves/src/bls12_381/fq.rs. The modulus is the value
    EIP-2537 states and Assumptions.pBase now pins: 381 bits, congruent to 3
    mod 4, which is what makes decompression a single exponentiation. -/
abbrev Fp := ZMod Midfall.Assumptions.pBase

-- p = 3 mod 4, so sqrt(a) = a^((p+1)/4). rust: bls12_381 Field::sqrt.
def fpSqrt (a : Fp) : Fp := a ^ ((Midfall.Assumptions.pBase + 1) / 4)

/-- A point of E : y^2 = x^3 + 4 over Fp, affine with an explicit infinity flag.
    Deliberately not a projective group element: nothing here adds points. -/
structure G1Affine where
  isInfinity : Bool
  x : Fp
  y : Fp
  deriving BEq

/-- The curve equation as a decidable predicate. rust: g1.rs:369-371 also
    requires torsion-freeness, which needs the group law and is therefore out of
    scope here - see the header. -/
def G1Affine.onCurve (P : G1Affine) : Bool :=
  P.isInfinity || (P.y * P.y == P.x * P.x * P.x + 4)

/-- The IETF compressed format's "largest root" convention. -/
-- "largest" is compared on the least non-negative representative, which is what
-- the IETF convention means; ZMod has no Max instance, so compare the Nats.
def rootFor (x : Fp) (signLargest : Bool) : Fp :=
  let y0 := fpSqrt (x * x * x + 4)
  let y1 := -y0
  if (y0.val > y1.val) == signLargest then y0 else y1

/-- Decompress a 48-byte point.

    ESTABLISHED EMPIRICALLY, NOT READ OFF THE FIELD NAME: the fixture field is
    called eip2537_hex but holds 48 bytes, i.e. the COMPRESSED form, not
    EIP-2537's 128-byte uncompressed encoding. The convention is big-endian x
    with the top THREE bits of byte 0 as flags (bit 7 compression, bit 6
    infinity, bit 5 y-sign = largest), which is
    draft-irtf-cfrg-pairing-friendly-curves rather than halo2's own little-endian
    to_compressed. Verified against fixtures/poseidon/rust_trace.json: all 21
    ReadPoint entries decompose onto the curve under this reading, and only 11
    of 21 under the little-endian reading - which is chance. A loader written
    from the field name would absorb 128 bytes instead of decoding 48 and produce
    silently wrong challenges: docs/REVIEW.md R-20, third occurrence. -/
def G1Affine.ofCompressed? (b : Bytes) : Option G1Affine :=
  if b.size ≠ 48 then none
  else
    let b0 := (b.data[0]?.map (fun u => u.toNat)).getD 0
    let flags := b0 >>> 5;
    if flags >>> 2 == 0 then none
    else if (flags >>> 1) &&& 1 == 1 then
      -- blst requires the SORT bit and the low SIX bits of byte 0 to be zero as
      -- well, not just bytes 1..47 (e1.c:269-274: byte_is_zero(in0 & 0x3f) &&
      -- bytes_are_zero(in+1, 47)). Without this, 0xe0, 0xc1, 0xff, 0xdf and 0xf0
      -- followed by 47 zero bytes all decode to the identity, absorb the same 128
      -- zero bytes, and yield identical challenges from distinct proofs - verbatim
      -- the malleability the x < p check exists to prevent, and it falsified
      -- compressedRoundtrip for the infinity case.
      if (b0 &&& 0x3f) == 0 &&
         bytesToNatBE (ByteArray.mk (b.data.extract 1 48)) == 0 then
        some { isInfinity := true, x := 0, y := 0 } else none
    else
      let xbytes := ByteArray.mk
        (List.toArray (Nat.toUInt8 (b0 &&& 0x1f) :: b.data.toList.drop 1))
      let xn := bytesToNatBE xbytes
      -- x must be the canonical representative. Without this the decoder is not
      -- injective on wire bytes: x and x+p are two different 48-byte strings that
      -- reduce to the same field element, absorb the same 128 bytes and therefore
      -- produce identical challenges from distinct proofs. rust: blst rejects this
      -- in blst_p1_uncompress before any curve test runs.
      if xn ≥ Midfall.Assumptions.pBase then none
      -- x = 0 gives y^2 = 4, i.e. (0, +/-2), which blst rejects inside
      -- blst_p1_uncompress with BLST_POINT_NOT_IN_GROUP (e1.c:288-289) BEFORE the
      -- torsion test at g1.rs:369-371 is reached. Not covered by the "torsion needs
      -- the group law, out of scope" disclaimer: this is a zero test. (0, +/-2) are
      -- the order-3 points - the textbook small-subgroup input.
      else if xn == 0 then none
      else
        let x : Fp := xn;
        let P : G1Affine :=
          { isInfinity := false, x := x, y := rootFor x (flags &&& 1 == 1) };
        -- the derived y is a square root of x^3+4 only when that value IS a square;
        -- otherwise fpSqrt returns a non-root and onCurve fails. rust: g1.rs:369-371
        -- is_on_curve() && is_torsion_free() after blst_p1_uncompress. The torsion
        -- half is still omitted (see g1AffineCodec); the curve half is not optional.
        if P.onCurve then some P else none

/-- Compress back to the same 48 bytes. -/
def G1Affine.toCompressed (P : G1Affine) : Bytes :=
  if P.isInfinity then
    ByteArray.mk (List.toArray (Nat.toUInt8 0b1100_0000 :: List.replicate 47 (0 : UInt8)))
  else
    let xb := natToBytesBE P.x.val 48
    let b0 := (xb.data[0]?.map (fun u => u.toNat)).getD 0;
    let sign : Nat := if P.y == rootFor P.x true then 1 else 0;
    -- the sign flag lives in BIT 5 (0x20), not bit 0: the top three bits of
    -- byte 0 are compression | infinity | sign, so the flag must be shifted into
    -- place. OR-ing the bare bit value silently corrupts x's low bits instead.
    ByteArray.mk (List.toArray
      (Nat.toUInt8 ((b0 &&& 0x1f) ||| 0b1000_0000 ||| (sign <<< 5)) ::
        xb.data.toList.drop 1))

/-- The 128-byte EIP-2537 form the transcript absorbs: 16 zeros, x in 48 bytes
    big-endian, 16 zeros, y in 48 bytes. rust: g1.rs to_input and
    transcript/implementors.rs:263-290. -/
def G1Affine.toEip (P : G1Affine) : Bytes :=
  if P.isInfinity then ByteArray.mk (List.toArray (List.replicate 128 (0 : UInt8)))
  else ByteArray.mk (List.toArray (eipPad.data.toList
    ++ (natToBytesBE P.x.val 48).data.toList
    ++ eipPad.data.toList ++ (natToBytesBE P.y.val 48).data.toList))

/-- The codec the 9.2 verifier path takes in VerifierEnv. The torsion-free half of
    g1.rs:369-371 is NOT implemented (it needs the group law), so this is a
    CONFORMANCE codec: sound for replaying a trace whose points the Rust already
    accepted, not a validator of adversarial points. -/
def g1AffineCodec : G1Codec G1Affine where
  ofCompressed? := G1Affine.ofCompressed?
  toCompressed := G1Affine.toCompressed
  toEip := G1Affine.toEip
  ofEip? b :=
    if b.size ≠ 128 then none
    else if bytesToNatBE b == 0 then
      -- EIP-2537 reserves the all-zero encoding for the point at infinity, and
      -- toEip emits exactly that for it, so the round-trip property
      -- (G1Codec.eipRoundtrip) requires accepting it here. (0, 0) is NOT on
      -- y^2 = x^3 + 4, so a naive onCurve-first check rejects the identity and
      -- the round-trip fails for the one point the verifier is most likely to
      -- encode this way. rust: implementors.rs:283-299 has this branch first.
      some { isInfinity := true, x := 0, y := 0 }
    else
      let xn := bytesToNatBE (ByteArray.mk (b.data.extract 16 64))
      let yn := bytesToNatBE (ByteArray.mk (b.data.extract 80 128))
      -- both coordinates must be canonical, for the same injectivity reason as
      -- in ofCompressed?.
      if xn ≥ Midfall.Assumptions.pBase || yn ≥ Midfall.Assumptions.pBase then none
      else
        let P : G1Affine := { isInfinity := false, x := xn, y := yn };
        if P.onCurve then some P else none

/-! ## Checks against real Rust output

    The bytes below are copied verbatim from the ReadPoint entries of
    proofs/solidity-verifier/fixtures/poseidon/rust_trace.json, so these are not
    self-consistent round-trips: they pin the codec to output the reference
    implementation produced. -/

section Kats

def fixturePoints : List String :=
  ["81e60cdbf67ce5879c7c24b3d3413304dad21febd91bee73191acebb2ed5597de2ea65647177e202c983122854298ed4",
   "8e8bf0427660ee129b3ac742b997adf709272d75363146d0880dce510e186fdef0e49e65d30f5304a203642b965b6a31",
   "b30df15f939f9f1e19ac2bf52b805ac80e1379e8fd0a9c588404b95cec2b014f444e396014ce28ab497b5cc2aa941736",
   "b4908b22c8819acb07f0d59150a7118f3c0a2d3b97bb0b16175fa2ac34020077553e5a94a5a99d5809c03435e9aa5a76",
   "83fd77a149152709931d80ffc6e618a834fe0110d53926df32c8728290432217817fd8dca035511a09d4a52844f9c492",
   "a23f3a922265548de6e1e3607311b7a3867156aed5b30b51bcacb21e9a2f06a01820189deaa9fdd1f9cf60dcde5445f5"]

def hexByte (c : Char) : Nat :=
  let v := c.val.toNat
  if v >= 97 then v - 87 else if v >= 65 then v - 55 else v - 48

def hexToBytes (s : String) : Bytes :=
  ByteArray.mk (go (s.toList.map hexByte) #[])
where
  go : List Nat -> Array UInt8 -> Array UInt8
    | [], acc => acc
    | a :: b :: rest, acc => go rest (acc.push (Nat.toUInt8 (a * 16 + b)))
    | [_], acc => acc

/-- Build a compressed encoding for a chosen x, so the rejection tests can name
    their input directly. -/
def mkCompX (x : Nat) (sign : Bool) : Bytes :=
  let xb := natToBytesBE x 48
  let b0 := (xb.data[0]?.map (fun u => u.toNat)).getD 0
  ByteArray.mk (List.toArray
    (Nat.toUInt8 ((b0 &&& 0x1f) ||| 0b1000_0000 ||| (if sign then 0x20 else 0))
      :: xb.data.toList.drop 1))

def blsDecompress_kats_ok : Bool :=
  fixturePoints.all fun h =>
    match G1Affine.ofCompressed? (hexToBytes h) with
    | none => false
    | some P => P.onCurve && !P.isInfinity &&
        (G1Affine.toCompressed P).data.toList == (hexToBytes h).data.toList

def blsEip_kats_ok : Bool :=
  match G1Affine.ofCompressed? (hexToBytes fixturePoints.head!) with
  | none => false
  | some P =>
      let e := G1Affine.toEip P;
      e.size == 128 &&
      (e.data.extract 0 16).all (fun u => u.toNat == 0) &&
      (e.data.extract 64 80).all (fun u => u.toNat == 0) &&
      (match g1AffineCodec.ofEip? e with
       | some Qt => Qt.x == P.x && Qt.y == P.y
       | none => false)

def blsInfinity_kats_ok : Bool :=
  let id := G1Affine.toCompressed { isInfinity := true, x := 0, y := 0 };
  id.size == 48 &&
  ((id.data[0]?.map (fun u => u.toNat)) == some 0b1100_0000) &&
  (match G1Affine.ofCompressed? id with
   | some P => P.isInfinity
   | none => false) &&
  (match G1Affine.ofCompressed? (ByteArray.mk (List.toArray (Nat.toUInt8 0b1100_0000 ::
        Nat.toUInt8 1 :: List.replicate 46 (0 : UInt8)))) with
   | none => true
   | some _ => false)

def blsWidth_kats_ok : Bool :=
  G1Affine.ofCompressed? (natToBytesBE 1 47) == none &&
  G1Affine.ofCompressed? (natToBytesBE 1 49) == none &&
  g1AffineCodec.ofEip? (natToBytesBE 1 127) == none


/-- The rejections an earlier revision got wrong (adversarial review, findings 1
    and 2). Each conjunct is an input that USED to be accepted or USED to fail, so
    this is the regression guard for the soundness hole, not a restatement of the
    happy path. -/
def blsRejects_kats_ok : Bool :=
  -- x = 1 gives x^3 + 4 = 5, a non-residue: no point exists, so decode must
  -- refuse rather than absorb a made-up y.
  (match G1Affine.ofCompressed? (mkCompX 1 false) with
   | none => true
   | some P => false) &&
  -- x and x + p are distinct wire strings for the same field element. Accepting
  -- both makes the transcript malleable: two proofs, identical challenges,
  -- identical decision. Only the canonical one may decode.
  (G1Affine.ofCompressed? (mkCompX 4 false)).isSome &&
  (G1Affine.ofCompressed? (mkCompX (4 + Midfall.Assumptions.pBase) false)) == none &&
  -- the identity must survive the EIP round-trip: toEip emits 128 zeros for it,
  -- and (0, 0) is not on the curve, so ofEip? needs the explicit branch.
  (match g1AffineCodec.ofEip?
      (ByteArray.mk (List.toArray (List.replicate 128 (0 : UInt8)))) with
   | some P => P.isInfinity
   | none => false)
-- a real fixture point still decodes after the tightening (guards against the
-- checks being too strict and silently rejecting every honest proof)
def blsStillAccepts_kats_ok : Bool :=
  fixturePoints.all fun h => (G1Affine.ofCompressed? (hexToBytes h)).isSome

#eval Midfall.Instances.blsRejects_kats_ok      -- expect true
#eval Midfall.Instances.blsStillAccepts_kats_ok -- expect true


-- The BLS12-381 G1 generator: compressed form and published y, taken from the
-- standard rather than computed here. This is the NON-VACUOUS sign-convention
-- test. Every other KAT here decodes with a convention and recompresses with the
-- same one, which is the identity for ANY convention - an external review proved
-- the vacuity by swapping largest-root for odd-root and watching all six KATs
-- stay green. The generator separates them: its y is the SMALLEST root and is
-- ODD while the largest root is even, so a parity convention decodes this input
-- to the wrong point.
def blsGenerator_kats_ok : Bool :=
  let compHex := "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
  let yHex := "08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"
  match G1Affine.ofCompressed? (hexToBytes compHex) with
  | none => false
  | some P =>
      !P.isInfinity && P.onCurve &&
      (natToBytesBE P.y.val 48).data.toList == (hexToBytes yHex).data.toList &&
      (G1Affine.toCompressed P).data.toList == (hexToBytes compHex).data.toList

-- The malleability and small-subgroup inputs an external review found STILL
-- accepted after the first round of fixes, each verified against blst itself
-- (e1.c:269-274 and e1.c:288-289).
def infVariants : List String :=
  (["e0", "c1", "ff", "df", "f0"] : List String)
    |>.map (fun pre => pre ++ String.mk (List.replicate 94 '0'))

def blsRejects2_kats_ok : Bool :=
  -- blst requires the sort bit AND the low six bits of byte 0 to be zero in the
  -- infinity arm, not just bytes 1..47, so all five are BAD_ENCODING there.
  (infVariants.all fun h => G1Affine.ofCompressed? (hexToBytes h) == none) &&
  -- x = 0 gives (0, +/-2), the order-3 points: rejected by blst with
  -- BLST_POINT_NOT_IN_GROUP before any torsion test, and a zero test rather than
  -- a group-law test, so not covered by the torsion disclaimer.
  (G1Affine.ofCompressed? (mkCompX 0 false)) == none &&
  (G1Affine.ofCompressed? (mkCompX 0 true)) == none &&
  -- the canonical infinity encoding must still be accepted, so the tightening
  -- cannot over-reject without this failing
  (match G1Affine.ofCompressed?
        (hexToBytes ("c0" ++ String.mk (List.replicate 94 '0'))) with
   | some P => P.isInfinity
   | none => false)

end Kats
#eval Midfall.Instances.blsGenerator_kats_ok    -- expect true
#eval Midfall.Instances.blsRejects2_kats_ok     -- expect true

#eval Midfall.Instances.blsDecompress_kats_ok   -- expect true
#eval Midfall.Instances.blsEip_kats_ok         -- expect true
#eval Midfall.Instances.blsInfinity_kats_ok    -- expect true
#eval Midfall.Instances.blsWidth_kats_ok       -- expect true

end Midfall.Instances
