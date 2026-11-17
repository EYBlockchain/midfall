/-
  D4 - THE REAL COMPRESSED CODEC ON G₁z: known-answer checks on every G1 point of the fixture
  (27 key commitments, 21 proof points, the committed-instance identity, the generator), and the
  rejections the placeholder could not express.
-/
import RunLib
set_option autoImplicit false

namespace RefCodecKats
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel RefRun
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv Midfall.Conformance

def mk48 (b0 : Nat) (x : Nat) : Bytes :=
  let xb := natToBytesBE x 48
  ByteArray.mk (List.toArray (Nat.toUInt8 (((xb.data[0]?.map (·.toNat)).getD 0) ||| b0) :: xb.data.toList.drop 1))

/-- The smallest x >= 1 that is the abscissa of a curve point (so `G1Affine.ofCompressed?` accepts
    the compressed string) - almost surely NOT in the r-torsion, since the cofactor is ~2^126. -/
def firstCurveX : Nat :=
  ((List.range 40).map (· + 1)).find? (fun x => (G1Affine.ofCompressed? (mk48 0x80 x)).isSome) |>.getD 0

def kats : IO Bool := do
  let (_, tr, committedHex, _) ← loadBundle
  let proofPts := (reads tr).filter (fun b => b.size == 48)
  let all : List Bytes := poseidonVkData.fixedCommitmentHex.toList ++
    poseidonVkData.permutationCommitmentHex.toList ++ proofPts ++ committedHex.toList.flatMap (·.toList) ++
    [poseidonParamsData.g1Hex]
  let c := g1CodecC
  let perPoint (b : Bytes) : Bool :=
    match c.ofCompressed? b with
    | none => false
    | some Q =>
        -- decoder-first (proved: g1CodecC_compressedRoundtrip), re-measured
        decide (c.toCompressed Q = b) &&
        -- ENCODER-FIRST, the law verifyMsgs needs (stated: g1CodecC_compressedEncoderFirst)
        decide (c.ofCompressed? (c.toCompressed Q) = some Q) &&
        -- the EIP half, both directions
        decide (c.ofEip? (c.toEip Q) = some Q) &&
        -- the re-encode test is a no-op on a canonical string
        decide (g1zOfCompressedRaw? b = some Q) &&
        -- widths
        (c.toCompressed Q).size == 48 && (c.toEip Q).size == 128
  let okAll := all.all perPoint
  IO.println s!"points checked: {all.length} (19 fixed + 8 sigma + {proofPts.length} proof + {committedHex.size} committed + generator); all four laws hold on each: {okAll}"
  let idOk := decide (c.ofCompressed? (mk48 0xc0 0) = some 1) && decide (c.toCompressed 1 = mk48 0xc0 0)
  let genOk := decide (c.ofCompressed? poseidonParamsData.g1Hex = some g1zGen)
  IO.println s!"identity is 0xc0||0^47 both ways: {idOk}; params.json g1 decodes to g1zGen: {genOk}"
  -- rejections
  let x := firstCurveX
  let offSubgroup := (G1Affine.ofCompressed? (mk48 0x80 x)).isSome && (c.ofCompressed? (mk48 0x80 x)).isNone
  let nonCanonical := (c.ofCompressed? (mk48 0x80 (blsP + 5))).isNone      -- x >= p
  let noFlag := (c.ofCompressed? (natToBytesBE genPair.1 48)).isNone         -- compression bit clear
  let infTail := (c.ofCompressed? (mk48 0xc0 1)).isNone                      -- infinity with a nonzero tail
  let infSign := (c.ofCompressed? (mk48 0xe0 0)).isNone                      -- infinity with the sign bit
  let short := (c.ofCompressed? (ByteArray.mk #[0xc0])).isNone
  -- the sign bit selects the OTHER root: flipping it gives the inverse point
  let g := poseidonParamsData.g1Hex
  let flipped := ByteArray.mk (List.toArray (Nat.toUInt8 (Nat.xor ((g.data[0]?.map (·.toNat)).getD 0) 0x20) :: g.data.toList.drop 1))
  let signOk := decide (c.ofCompressed? flipped = some g1zGen⁻¹)
  IO.println s!"rejects: curve point x={x} outside the r-torsion {offSubgroup}; x>=p {nonCanonical}; no compression flag {noFlag}; infinity+tail {infTail}; infinity+sign {infSign}; short {short}"
  IO.println s!"sign bit flips to the inverse: {signOk}"
  -- the placeholder, for contrast
  pure (okAll && idOk && genOk && offSubgroup && nonCanonical && noFlag && infTail && infSign && short && signOk)

end RefCodecKats

#eval RefCodecKats.kats     -- expect true
