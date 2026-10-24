-- |
-- Midfall.Halo2.Exec.Accumulator
--
-- The verifier-reachable accumulator pieces (plan Section 4, module map, last
-- row): `KzgAcc`, its `check`, `fromDualMsm`, and the foreign-point
-- public-input encoding `encodeAccInstances` / `decodeAcc`.
--
-- Rust sources, all @formal-baseline:
--   * aggregation/src/ivc/verifier.rs:111-151 (`IvcVerifier::verify_final`)
--   * circuits/src/verifier/accumulator.rs:64-282 (`Accumulator`, `check`,
--     `from_dual_msm`, `accumulate`, `as_public_input`, `trivial`)
--   * circuits/src/verifier/msm.rs:40-242 (`Msm`, `accumulate_with_r`, `eval`,
--     `as_public_input`)
--   * circuits/src/verifier/mod.rs:89-160 (`fixed_commitment_name`,
--     `perm_commitment_name`, `fixed_bases`, `fixed_base_names`)
--   * circuits/src/field/foreign/field_chip.rs:126-139,
--     circuits/src/ecc/foreign/ecc_chip.rs:226-239 and
--     circuits/src/field/foreign/util.rs:81-106 (the foreign-field /
--     foreign-point public-input encoding)
--   * proofs/solidity-verifier/src/api.rs:14-189 (`AccumulatorEncoding`) and
--     proofs/solidity-verifier/src/lowering/layout/mod.rs:288-348 (the layout
--     constants it points at)
--   * proofs/solidity-verifier/templates/partials/verifier/AccumulatorHelpers.yul
--     and .../FinalPairing.yul (the contract side of the same object)
--
-- ## READ THIS BEFORE COMPARING THIS FILE TO THE RUST
--
-- This module models the **contract's** accumulator, not Rust's. docs/REVIEW.md
-- R-10 settled that `verify_final` batches the two accumulators with a scalar
-- `r` taken from the POW2 sponge over the foreign-point public-input encoding
-- (accumulator.rs:224-230), while the deployed contract batches them with
-- `alpha = mod(keccak256(tag ++ vk_digest ++ kzg_rhs ++ kzg_lhs ++ acc_rhs ++
-- acc_lhs), r)`, `0 -> 1` (FinalPairing.yul:21-31). Different hash, different
-- preimage - the contract's includes `vk_digest`, the Rust's has no vk_digest at
-- all - and, under the deployed `truncated-challenges` profile, the Rust
-- truncates its powers (accumulator.rs:229-230) while the contract does not
-- truncate alpha. So `alphaOf` below is the contract's derivation and
-- `KzgAcc.accumulate` takes its batching scalar as an argument instead of
-- deriving one from a sponge: the POW2 sponge is not ported and must not be
-- confused with `alphaOf`. Everything else in this file follows the same rule -
-- `decodeAcc` is `validate_public_accumulator`, `check` is the accumulator
-- invariant, and the encoding is the 7x56 shifted-limb layout the generator
-- emits and the Yul reads back.
--
-- Consequences of R-10 that this file makes visible rather than hiding:
--   1. `lowering_equivalence_noAcc` / `end_to_end_noAcc` need their
--      `accumulator = none` hypothesis: in acc mode Rust accepts iff X*Y^r = 1
--      and the contract iff X*Y^alpha = 1, and those are different predicates
--      (R-10 consequence 1).
--   2. `ContractRef.accepts` in acc mode is `decodeAcc` + `batchedCheck` here,
--      which is contract-vs-Lean-reference, never contract-vs-Rust (R-10
--      consequence 2).
--   3. The contract is *stronger* than the reference in two places: alpha is
--      bound to the vk (R-10 consequence 3), and every decoded accumulator
--      point is pushed through EIP-2537 G1MSM, so curve and subgroup membership
--      are checked on points the Rust never validates
--      (AccumulatorHelpers.yul:235-249, :296-303).

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Curve
import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Kzg.Params
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Halo2.Exec.Query

namespace Midfall.Halo2

-- Only p is a file-level variable: it is pinned by every signature that mentions
-- `Fr p`. The group binders are written out per declaration, exactly as in
-- Exec/Kzg/Msm.lean, because Lean threads a `variable` into a declaration only
-- when the signature pins it and G₂/Gₜ are phantoms (docs/design.md D-P7).
variable {p : ℕ} [Fact (Nat.Prime p)]


/-! ## 1. The public-input layout constants

The contract's accumulator decoder is hard-wired to Midnight's BLS12-381
self-emulation: seven radix-2^56 limbs per base-field coordinate, four limbs
packed per native scalar word, one identity-flag word per point, and two
carried scalars in the point-and-scalar layout. -/

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:296
    (accumulator::LIMB_BITS), and api.rs:75 (SUPPORTED_NUM_LIMB_BITS). -/
def accLimbBits : Nat := 56

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:297
    (accumulator::LIMBS), and api.rs:73 (SUPPORTED_NUM_LIMBS). -/
def accLimbs : Nat := 7

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:299
    (accumulator::LIMBS_PER_WORD): "Four 56-bit limbs fit in one scalar word
    with unused high bits." The generator's api.rs:104 derives the same number
    as `254 / num_limb_bits` from `Fr::CAPACITY = 254`; the two are pinned equal
    by `accLayoutKats_ok`. -/
def accLimbsPerWord : Nat := 4

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:302
    (accumulator::IDENTITY_FLAG_WORDS). -/
def accIdentityFlagWords : Nat := 1

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:304
    (accumulator::CARRIED_SCALARS). -/
def accCarriedScalars : Nat := 2

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:30 (WORD_BYTES)
    and :78 (G1_BYTES); the same numbers as `Midfall.g1EipWidth`. -/
def accWordBytes : Nat := 32
def accG1Bytes : Nat := 128

/-- The BLS12-381 base-field modulus. The accumulator limb codec is the only
    place in Exec that needs Fp rather than Fr, because the shifted-limb layout
    encodes and range-checks base-field coordinates. It is taken from
    `Midfall.Assumptions.pBase` rather than restated here: docs/REVIEW.md R-20 is
    exactly the story of one curve's modulus being typed into a second file and
    being wrong, and the two BLS moduli differ only in their last 50 digits. -/
def accFpModulus : Nat := Midfall.Assumptions.pBase

/-- rust: templates/partials/verifier/Constants.sol:241 (BLS_P_HI), i.e. the
    high word of p in the EIP-2537 two-word split. -/
def accFpHi : Nat := accFpModulus / 2^256

/-- rust: templates/partials/verifier/Constants.sol:242 (BLS_P_MINUS_ONE_LO),
    the low word of p - 1. -/
def accFpMinusOneLo : Nat := (accFpModulus - 1) % 2^256

/-- rust: proofs/solidity-verifier/src/lowering/layout/mod.rs:330-331
    (PAIRING_BATCH_DOMAIN_TAG_HEX). The comment there is load-bearing: this is a
    29-byte numeric literal - ASCII "pairing-batch-acc-kzg" followed by eight
    zero bytes - and `mstore` left-pads it, so the word actually hashed into
    alpha is `00 00 00 || "pairing-batch-acc-kzg" || 00*8`, NOT right-padded
    ASCII. A reimplementation that right-pads disagrees with the deployed
    verifier on every accept/reject decision. -/
def accPairingBatchDomainTag : Word256 :=
  BitVec.ofNat 256 0x70616972696e672d62617463682d6163632d6b7a670000000000000000

/-- rust: layout/mod.rs:338 (PAIRING_BATCH_VK_DIGEST_OFFSET). -/
def accPairingBatchVkDigestOffset : Nat := accWordBytes
/-- rust: layout/mod.rs:340 (PAIRING_BATCH_RHS_OFFSET). -/
def accPairingBatchRhsOffset : Nat := 2 * accWordBytes
/-- rust: layout/mod.rs:342 (PAIRING_BATCH_LHS_OFFSET). -/
def accPairingBatchLhsOffset : Nat := 2 * accWordBytes + accG1Bytes
/-- rust: layout/mod.rs:344 (PAIRING_BATCH_ACC_RHS_OFFSET). -/
def accPairingBatchAccRhsOffset : Nat := 2 * accWordBytes + 2 * accG1Bytes
/-- rust: layout/mod.rs:346 (PAIRING_BATCH_ACC_LHS_OFFSET). -/
def accPairingBatchAccLhsOffset : Nat := 2 * accWordBytes + 3 * accG1Bytes
/-- rust: layout/mod.rs:348 (PAIRING_BATCH_HASH_BYTES); layout/mod.rs:911
    asserts it is 0x240, which `accLayoutKats_ok` repeats. -/
def accPairingBatchHashBytes : Nat := 2 * accWordBytes + 4 * accG1Bytes


/-! ## 2. `AccumulatorEncoding`: the generator config the plan's
`Supported.acc` field quantifies over (plan 9.5 `Supported.acc`:
`∀ enc, g.cfg.accumulator = some enc → enc.validFor g.cfg.numInstances`).

The Rust returns `Result<(), GeneratorError::UnsupportedAccumulatorEncoding>`
with a five-field diagnostic payload (offset, num_limbs, num_limb_bits,
num_instances, reason). The payload is consumed only by `Display` and by tests
(api.rs:664, lowering/tests.rs:2100), never by a decision, so the port returns
`Bool` / `Option` and drops the reason strings; the two distinct failure causes
stay distinct because they land in two different functions. -/

/-- rust: proofs/solidity-verifier/src/api.rs:48-57 (enum
    AccumulatorEncodingKind). Variant order is the source order (rule R1). -/
inductive AccumulatorEncodingKind where
  /-- rust: api.rs:50-52 (PointAndScalar): lhs point, lhs scalar, rhs point,
      rhs scalar, then an optional fixed-base scalar tail. -/
  | pointAndScalar
  /-- rust: api.rs:53-56 (PointPair): already-collapsed lhs point, rhs point,
      both carried scalars implicitly one, no tail accepted. -/
  | pointPair
  deriving BEq

/-- rust: proofs/solidity-verifier/src/api.rs:35-45 (struct AccumulatorEncoding).
    Field order is the Rust order (rule R1). `kind` is Rust `pub(crate)`. -/
structure AccumulatorEncoding where
  /-- rust: offset - public-input index the accumulator tail starts at. -/
  offset : Nat
  /-- rust: num_limbs -/
  numLimbs : Nat
  /-- rust: num_limb_bits -/
  numLimbBits : Nat
  /-- rust: kind -/
  kind : AccumulatorEncodingKind

namespace AccumulatorEncoding

/-- rust: api.rs:82-90 (AccumulatorEncoding::new). -/
def new (offset numLimbs numLimbBits : Nat) : AccumulatorEncoding :=
  { offset, numLimbs, numLimbBits, kind := .pointAndScalar }

/-- rust: api.rs:92-100 (AccumulatorEncoding::point_pair). -/
def pointPair (offset numLimbs numLimbBits : Nat) : AccumulatorEncoding :=
  { offset, numLimbs, numLimbBits, kind := .pointPair }

/-- rust: api.rs:104 (`limbs_per_instance`, computed inside `coordinate_words`),
    and layout/mod.rs:299 (`LIMBS_PER_WORD`, the value the Yul renders). Two
    sources of one number: the Rust derives it from `Fr::CAPACITY = 254`, the
    layout states it. `max 1` keeps a zero limb width from being a division by
    zero in Lean where Rust would panic; `validFor` rejects any limb width other
    than 56 anyway. -/
def limbsPerInstance (enc : AccumulatorEncoding) : Nat :=
  max 1 (254 / enc.numLimbBits)

/-- rust: api.rs:102-106 (coordinate_words, private, hence ported per R1):
    `num_limbs.div_ceil(limbs_per_instance)`. -/
def coordinateWords (enc : AccumulatorEncoding) : Nat :=
  divCeil enc.numLimbs enc.limbsPerInstance

/-- rust: api.rs:108-112 (point_words): x words, y words, identity flag. -/
def pointWords (enc : AccumulatorEncoding) : Nat :=
  2 * enc.coordinateWords + accIdentityFlagWords

/-- rust: api.rs:114-117 (point_pair_words). -/
def pointPairWords (enc : AccumulatorEncoding) : Nat := 2 * enc.pointWords

/-- rust: api.rs:119-122 (has_carried_scalars). -/
def hasCarriedScalars (enc : AccumulatorEncoding) : Bool :=
  enc.kind == .pointAndScalar

/-- rust: api.rs:124-132 (fixed_payload_words). -/
def fixedPayloadWords (enc : AccumulatorEncoding) : Nat :=
  enc.pointPairWords + if enc.hasCarriedScalars then accCarriedScalars else 0

/-- The limb-shape half of `validate_for_num_instances`, factored out because
    `fully_collapsed_public_input_words` (api.rs:136-139) reaches it through the
    `usize::MAX` stand-in for "no length bound" - which in Lean, where `Nat` is
    unbounded, is simply "do not check the length". -/
def limbShapeOk (enc : AccumulatorEncoding) : Bool :=
  enc.numLimbs == accLimbs && enc.numLimbBits == accLimbBits

/-- rust: api.rs:143-171 (validate_for_num_instances). The Rust's
    `offset.saturating_add(required_words) > num_instances` is plain `+` here:
    Lean's `Nat` cannot overflow, and saturating at `usize::MAX` is what makes
    the Rust's own overflow handling a no-op for real inputs.

    This is the check `try_new` runs on the config
    (proofs/solidity-verifier/src/builder/api.rs:49-51) and the one plan 9.5's
    `Supported.acc` names, so `Supported.acc` reads
    `enc.validFor g.cfg.numInstances = true`. -/
def validFor (enc : AccumulatorEncoding) (numInstances : Nat) : Bool :=
  enc.limbShapeOk && enc.offset + enc.fixedPayloadWords ≤ numInstances

/-- rust: api.rs:134-139 (fully_collapsed_public_input_words). -/
def fullyCollapsedPublicInputWords (enc : AccumulatorEncoding) : Option Nat :=
  if enc.limbShapeOk then some enc.fixedPayloadWords else none

/-- rust: api.rs:173-188 (fixed_scalar_count). `none` is the Rust's `Err`:
    either the encoding is not the supported one / does not fit
    (`validate_for_num_instances`) or it is a point-pair with a non-empty tail. -/
def fixedScalarCount (enc : AccumulatorEncoding) (numInstances : Nat) : Option Nat :=
  if ! (enc.validFor numInstances) then none
  else
    let tail := numInstances - (enc.offset + enc.fixedPayloadWords)
    if enc.kind == .pointPair && tail != 0 then none else some tail

end AccumulatorEncoding


/-! ## 3. The foreign-field limb codec

`AssignedField::as_public_input` (circuits/src/field/foreign/field_chip.rs:130-139)
is the encoder and `load_acc_coord` (AccumulatorHelpers.yul:86-114) is the
decoder. The exact layout, read off both sides:

* one coordinate `c` is represented by `v = (c - 1) mod p` - the subtraction is
  in the *foreign* field, so `c = 0` becomes `v = p - 1`, which is the sentinel
  the decoder maps back to zero (field_chip.rs:131 "We shift the value of x by 1
  for the unique-zero representation"; AccumulatorHelpers.yul:53-57, :96-108);
* `v` is split into `num_limbs` little-endian limbs of `num_limb_bits` bits
  (`bi_to_limbs`, util.rs:81-100);
* consecutive limbs are packed little-endian into groups of `limbs_per_word`
  and each group becomes one native field element (`bi_from_limbs`,
  util.rs:104-106, applied per `chunks` slice, field_chip.rs:134-138);
* so one BLS12-381 coordinate is two words: word 0 holds limbs 0..3 (224 bits
  used, 32 bits must be zero) and word 1 holds limbs 4..6 (168 bits used, 88
  bits must be zero). The decoder enforces exactly that
  (`check_acc_coord_packing`, yul:62-83), which is what makes the encoding
  canonical - without it the same coordinate has many calldata encodings.

The contract reconstructs the 384-bit value by splitting it into the EIP-2537
`(hi, lo)` pair as it goes, including the straddle case where limb 4 spans the
256-bit boundary (yul:38-49). Summing the limbs and splitting once at the end is
the same integer; the port sums and splits, and says so at each site. -/

/-- rust: circuits/src/field/foreign/util.rs:81-100 (bi_to_limbs).

    The Rust loop is `div_rem` repeated, i.e. limb `i` is `v / base^i % base`,
    which is what the port computes directly; `List.range` preserves the
    ascending order the Rust pushes in.

    R4 panic site: util.rs:93-98 panics when the leftover quotient is nonzero,
    i.e. when `v >= base^nb_limbs`. The port drops the overflow instead of
    panicking. Unreachable for its only caller: a coordinate is below `p < 2^381`
    and the layout is `7 * 56 = 392` bits. -/
def biToLimbs (numLimbs numLimbBits : Nat) (v : Nat) : Array Nat :=
  (List.range numLimbs).map (fun i => v / 2 ^ (numLimbBits * i) % 2 ^ numLimbBits) |>.toArray

/-- rust: circuits/src/field/foreign/util.rs:102-106 (bi_from_limbs):
    `limbs.iter().rev().fold(0, |acc, limb| acc * base + limb)`, i.e. the limbs
    are little-endian. The reverse is kept explicitly rather than folded away,
    because getting it the other way round is the R-20 class of bug. -/
def biFromLimbs (numLimbBits : Nat) (limbs : Array Nat) : Nat :=
  (limbs.toList.reverse).foldl (fun acc l => acc * 2 ^ numLimbBits + l) 0

/-- rust: circuits/src/field/foreign/field_chip.rs:126-139
    (Instantiable::as_public_input for AssignedField), one coordinate. -/
def encodeAccCoordWords (enc : AccumulatorEncoding) (c : Nat) : Array Word256 :=
  let v := (c + accFpModulus - 1) % accFpModulus
  let limbs := biToLimbs enc.numLimbs enc.numLimbBits v
  let lpw := enc.limbsPerInstance
  (List.range enc.coordinateWords).map (fun j =>
    -- Rust `chunks(nb_limbs_per_batch)`: the last chunk is short, and
    -- `Array.extract` clamps the same way.
    BitVec.ofNat 256 (biFromLimbs enc.numLimbBits (limbs.extract (j * lpw) ((j + 1) * lpw)))) |>.toArray

/-- rust: AccumulatorHelpers.yul:62-83 (check_acc_coord_packing). Rejects any
    unused high bit in a packed word, so each coordinate has exactly one
    encoding. `src` is a *word* index into the instance array, not a byte
    pointer: the Yul's `add(src, mul(word_idx, 0x20))` is `src + word_idx`
    here. -/
def checkAccCoordPacking (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Bool :=
  (List.range enc.coordinateWords).all fun wordIdx =>
    let remaining := enc.numLimbs - wordIdx * enc.limbsPerInstance
    let limbsInWord := min enc.limbsPerInstance remaining
    let usedBits := limbsInWord * enc.numLimbBits
    -- yul:77 only constrains a word when its used bits do not fill the word.
    if usedBits < 256 then (inst.getD (src + wordIdx) 0).toNat < 2 ^ usedBits else true

/-- rust: AccumulatorHelpers.yul:22-51 (load_acc_coord_shifted): the value the
    limbs represent, before the sentinel handling. The Yul accumulates into a
    `(hi, lo)` pair with an explicit straddle case at :40-44; the sum of
    `limb_i * 2^(bits*i)` is the same integer, and `decodeAccCoord` splits it. -/
def loadAccCoordShifted (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) : Nat :=
  (List.range enc.numLimbs).foldl (fun acc i =>
    let packed := (inst.getD (src + i / enc.limbsPerInstance) 0).toNat
    let limb := packed / 2 ^ (enc.numLimbBits * (i % enc.limbsPerInstance)) % 2 ^ enc.numLimbBits
    acc + limb * 2 ^ (enc.numLimbBits * i)) 0

/-- rust: AccumulatorHelpers.yul:55-57 (is_bls_p_minus_one). -/
def isBlsPMinusOne (hi lo : Nat) : Bool := hi == accFpHi && lo == accFpMinusOneLo

/-- rust: AccumulatorHelpers.yul:86-114 (load_acc_coord). Returns the decoded
    coordinate as the EIP-2537 `(hi, lo)` pair the precompiles want.

    The three rejections, in the order the Yul applies them:
    * unused high bits in a packed word (yul:87 via :62-83);
    * the reconstructed value above `p - 1` (yul:89-94), written exactly as the
      contract writes it, i.e. as a `(hi, lo)` comparison against
      `BLS_P_HI`/`BLS_P_MINUS_ONE_LO` rather than as `v < p`;
    * a high word that does not fit the EIP-2537 48-byte coordinate (yul:113).
      Given the range check this is implied - `p < 2^381` - and it is kept
      because the contract has it and a wrong limb count would trip it first.

    Then the sentinel: `v = p - 1` decodes to 0, everything else decodes to
    `v + 1` with the carry into `hi` (yul:96-108, where
    `hi := add(hi, lt(next_lo, lo))` is the carry). -/
def decodeAccCoord (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) :
    Option (Nat × Nat) := do
  let v := loadAccCoordShifted enc inst src
  let hi := v / 2^256
  let lo := v % 2^256
  -- yul:93 `or(lt(hi, BLS_P_HI), and(eq(hi, BLS_P_HI), iszero(gt(lo, ...))))`
  let inField := hi < accFpHi || (hi == accFpHi && ! (lo > accFpMinusOneLo))
  if ! (checkAccCoordPacking enc inst src) then none
  else if ! (inField && hi < 2^128) then none
  else if isBlsPMinusOne hi lo then some (0, 0)
  else some ((v + 1) / 2^256, (v + 1) % 2^256)

/-- rust: AccumulatorHelpers.yul:119-165 (load_acc_point). Returns the
    128-byte EIP-2537 padded point - the four `mstore`s at yul:160-163, or the
    four zero words of yul:137-140 - together with the identity flag.

    Identity handling is the delicate part and it is asymmetric on purpose:
    when the flag is 1 the coordinate words are **not decoded and not
    range-checked at all** (yul:130-141: "the circuit leaves x and y
    unconstrained ('can be anything'), so they carry no meaning and must not be
    decoded or range-checked here"). So every word pair with flag 1 decodes to
    the identity. That is faithful to the contract and it is why
    `decodeAcc_injective` (plan 9.5) is false as written for identity sides;
    see the note at `decodeAcc`.

    The flag itself must be 0 or 1 (yul:127): the circuit constrains it as a
    bit, and anything else is a malformed public input rather than a point.

    A non-identity point whose two decoded coordinates are both zero is
    rejected (yul:152-157): the shifted codec maps the encoded value `p - 1` to
    the coordinate 0, and EIP-2537 reserves the all-zero encoding for the point
    at infinity, so `(0,0)` with flag 0 would be a second encoding of the
    identity.

    The Yul computes both coordinates and ANDs the results (yul:143-151); the
    port short-circuits. Same accept/reject decision, different order of
    evaluation, and no observable effect because nothing after it depends on
    which coordinate failed. -/
def loadAccPoint (enc : AccumulatorEncoding) (inst : Array Word256) (src : Nat) :
    Option (Bytes × Bool) := do
  let cw := enc.coordinateWords
  let flag := (inst.getD (src + 2 * cw) 0).toNat
  if ! (flag < 2) then none
  else if flag == 1 then some (natToBytesBE 0 (4 * accWordBytes), true)
  else
    let (xhi, xlo) ← decodeAccCoord enc inst src
    let (yhi, ylo) ← decodeAccCoord enc inst (src + cw)
    if xhi == 0 && xlo == 0 && yhi == 0 && ylo == 0 then none
    else some (wordToBytesBE (BitVec.ofNat 256 xhi) ++ wordToBytesBE (BitVec.ofNat 256 xlo) ++
               wordToBytesBE (BitVec.ofNat 256 yhi) ++ wordToBytesBE (BitVec.ofNat 256 ylo),
               false)

/-- The i-th coordinate of a 128-byte EIP-2537 padded point, as a natural.
    `Midfall.G1Codec.toEip` is `16 zero bytes || x_BE(48) || 16 zero bytes ||
    y_BE(48)` (Common/Codec.lean, rust:
    proofs/src/transcript/implementors.rs:283-299), so coordinate `i` starts at
    byte `16 + 64*i`. A short buffer reads as 0, which is what the all-zero
    identity encoding gives anyway. -/
def coordOfEip (b : Bytes) (i : Nat) : Nat :=
  match bytesTake b (16 + 64 * i) 48 with
  | some s => bytesToNatBE s
  | none => 0

/-- The canonical 256-bit word carrying a scalar. This is where the port gives
    up expressiveness and says so: the contract reads raw calldata words and
    rejects any carried scalar at or above `r`
    (AccumulatorHelpers.yul:226, :290, :321), and `Fr p = ZMod p` cannot
    represent such a word. Encoding a *decoded* accumulator therefore goes
    through this cast, and the rejection is only visible in the
    `Array Word256`-typed decoder below. Plan Section 13 records the same gap
    for `calldata_canonical`. -/
def frWord (x : Fr p) : Word256 := BitVec.ofNat 256 x.val


/-! ## 4. `AccMsm`: the accumulator's MSM shape

`circuits/src/verifier/msm.rs:40-182` is a *different* Rust type from
`proofs/src/poly/kzg/msm.rs`'s `MSMKZG`, so it gets its own Lean type rather
than being folded into the one in Exec/Kzg/Msm.lean. The name is prefixed
because `Msm` alone would collide with the module's subject; the Rust name is
recorded at every def. -/

/-- rust: circuits/src/verifier/msm.rs:40-54 (struct Msm):
    `<scalars, bases> + <fixed_bases, fixed_base_scalars>`, where the fixed
    bases themselves are not carried - they are globally known and supplied at
    evaluation time.

    Rule R6: `BTreeMap<String, F>` becomes an `Array (String × F)` kept in
    ascending name order, which is the BTreeMap's iteration order. Lean's
    `String` order compares codepoints and Rust's compares UTF-8 bytes; the two
    agree because UTF-8 byte order is codepoint order. That matters here: the
    order of `fixed_base_scalars` is the order of the public-input words
    (msm.rs:215), so a disagreement would be a different encoding. -/
structure AccMsm (F G₁ : Type) where
  /-- rust: bases -/
  bases : Array G₁
  /-- rust: scalars -/
  scalars : Array F
  /-- rust: fixed_base_scalars, ascending by name -/
  fixedBaseScalars : Array (String × F)

/-- Insert `(k, v)` into a name-ascending array, replacing an existing key.
    rust: the three `fixed_base_scalars.insert(name, *scalar)` calls at
    accumulator.rs:106, :111, :115 (BTreeMap::insert overwrites). -/
def accMapInsert {F : Type} (m : Array (String × F)) (k : String) (v : F) : Array (String × F) :=
  (go k v m.toList).toArray
where
  go : String → F → List (String × F) → List (String × F)
    | k, v, [] => [(k, v)]
    | k, v, (k', v') :: rest =>
        if k == k' then (k, v) :: rest
        else if k < k' then (k, v) :: (k', v') :: rest
        else (k', v') :: go k v rest

/-- Add `v` to the entry `k`, inserting it when absent.
    rust: circuits/src/verifier/msm.rs:172-178, the
    `entry(key).and_modify(|e| *e += r_times_value).or_insert(r_times_value)`
    merge of two fixed-base scalar maps. -/
def accMapInsertAdd {F : Type} [Add F] (m : Array (String × F)) (k : String) (v : F) :
    Array (String × F) :=
  match m.findIdx? (fun e => e.1 == k) with
  | some i =>
      let cur := m.getD i (k, v)
      arraySetD m i (k, cur.2 + v)
  | none => accMapInsert m k v

/-- rust: circuits/src/verifier/mod.rs:89-92 (fixed_commitment_name). -/
def fixedCommitmentName (namePrefix : String) (i : Nat) : String :=
  namePrefix ++ "_fixed_com_" ++ toString i

/-- rust: circuits/src/verifier/mod.rs:94-97 (perm_commitment_name). -/
def permCommitmentName (namePrefix : String) (i : Nat) : String :=
  namePrefix ++ "_perm_com_" ++ toString i

/-- rust: circuits/src/verifier/mod.rs:111-133 (fixed_bases). The BTreeMap is
    the name-ascending array again; the Rust inserts `-G` first but a BTreeMap
    orders by key, so insertion order does not matter here - unlike
    `fixed_base_names`, which returns a Vec and does. -/
def fixedBases {G₁ : Type} [Group G₁] (vkName : String)
    (fixedCommitments permCommitments : Array G₁) : Array (String × G₁) :=
  let m0 : Array (String × G₁) := accMapInsert #[] "-G" ((1 : G₁)⁻¹)
  let m1 := (List.range fixedCommitments.size).foldl
    (fun m i => accMapInsert m (fixedCommitmentName vkName i) (fixedCommitments.getD i 1)) m0
  (List.range permCommitments.size).foldl
    (fun m i => accMapInsert m (permCommitmentName vkName i) (permCommitments.getD i 1)) m1

/-- rust: circuits/src/verifier/mod.rs:135-160 (fixed_base_names). Insertion
    order, not sorted order: "-G" first, then the fixed commitments, then the
    permutation commitments. `AssignedMsm::assign` sorts it later
    (msm.rs:331-333), which is why the Rust needs both functions and so does the
    port. -/
def fixedBaseNames (vkName : String) (nbFixed nbPerm : Nat) : Array String :=
  let a := (List.range nbFixed).map (fixedCommitmentName vkName)
  let b := (List.range nbPerm).map (permCommitmentName vkName)
  (["-G"] ++ a ++ b).toArray

namespace AccMsm

/-- rust: msm.rs:76-94 (Msm::new). The `assert_eq!(bases.len(),
    scalars.len())` at msm.rs:88 is a real panic site (rule R4) and it is kept
    as one: an MSM whose two vectors disagree would silently truncate under the
    zip in `msmSpecific`, which is a *different value* rather than an error. -/
def new {F G₁ : Type} (bases : Array G₁) (scalars : Array F)
    (fixedBaseScalars : Array (String × F)) : Except Fault (AccMsm F G₁) :=
  if bases.size == scalars.size then .ok { bases, scalars, fixedBaseScalars }
  else .error (Fault.panic "circuits/src/verifier/msm.rs:88")

/-- rust: msm.rs:111-124 (Msm::from_terms): the same assertion, at :118, with
    an empty fixed-base map. -/
def fromTerms {F G₁ : Type} (bases : Array G₁) (scalars : Array F) :
    Except Fault (AccMsm F G₁) :=
  if bases.size == scalars.size then .ok { bases, scalars, fixedBaseScalars := #[] }
  else .error (Fault.panic "circuits/src/verifier/msm.rs:118")

/-- Look up a fixed base by name. rust: msm.rs:153-154, where a miss is
    `panic!("Base not provided: {key}")`. The port returns the identity for a
    miss so that `eval` stays total (rule R10) and `check` keeps the `Bool` type
    plan 9.2 fixes; the same choice, and the same "Phase 4 discharges the
    fallback" note, is made for `MSMKZG.eval` in Exec/Kzg/Msm.lean. Every
    accumulator built by `fromDualMsm` has its fixed names checked against the
    same `fixedBases` map, so a miss means the caller passed two different
    maps. -/
def lookupFixedBase {G₁ : Type} [Group G₁] (fixedBases : Array (String × G₁))
    (name : String) : G₁ :=
  match fixedBases.findIdx? (fun e => e.1 == name) with
  | some i => (fixedBases.getD i (name, (1 : G₁))).2
  | none => 1

/-- rust: msm.rs:139-161 (Msm::eval): `<scalars, bases> + <fixed_bases,
    fixed_base_scalars>`, one MSM over the concatenation. The Rust uses
    `msm_best`; semantically that is the sum of scalar multiples the port already
    has as `msmSpecific` (see the header of Exec/Kzg/Msm.lean for why the back
    end is not ported). The Rust appends the fixed part in BTreeMap order
    (:153-157); the order is invisible here because the group is abelian, and it
    is kept anyway so a future gas or trace comparison has it. -/
def eval {G₁ : Type}
    [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (m : AccMsm (Fr p) G₁) (fixedBases : Array (String × G₁)) : G₁ :=
  let fixed := m.fixedBaseScalars.map (fun (name, s) => (s, lookupFixedBase fixedBases name))
  msmSpecific (m.scalars ++ fixed.map Prod.fst) (m.bases ++ fixed.map Prod.snd)

/-- rust: msm.rs:163-181 (Msm::accumulate_with_r): `self + r * other`, keeping
    both parts as separate MSM terms rather than evaluating - that is the whole
    point of the type, and it is what lets the contract fold the tail into one
    G1MSM call. Note the Rust scales by `*s * r` for the variable scalars
    (:170) and by `r * value` for the fixed ones (:173); commutativity makes
    that identical, and the port writes `* r` in both. -/
def accumulateWithR {G₁ : Type}
    (m other : AccMsm (Fr p) G₁) (r : Fr p) : AccMsm (Fr p) G₁ :=
  { bases := m.bases ++ other.bases
    scalars := m.scalars ++ other.scalars.map (fun s => s * r)
    fixedBaseScalars :=
      other.fixedBaseScalars.foldl
        (fun acc (name, v) => accMapInsertAdd acc name (r * v)) m.fixedBaseScalars }

/-- rust: msm.rs:126-137 (Msm::collapse): evaluate the variable part to a single
    base with scalar 1, leaving the fixed-base part intact. -/
def collapse {G₁ : Type}
    [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (m : AccMsm (Fr p) G₁) : AccMsm (Fr p) G₁ :=
  { m with bases := #[msmSpecific m.scalars m.bases], scalars := #[1] }

/-- rust: circuits/src/ecc/foreign/ecc_chip.rs:226-239
    (Instantiable::as_public_input for AssignedForeignPoint) plus
    circuits/src/field/foreign/field_chip.rs:126-139 for each coordinate:
    x words, y words, then the identity flag as its own word.

    The coordinates come from `G1Codec.toEip`, i.e. through the EIP-2537 padded
    form, because under D-P1 there is no base-field type to project onto: the
    codec is the only curve-dependent handle the port is allowed, and
    `G1Codec.eipRoundtrip` (Common/Codec.lean) is the hypothesis that says using
    it loses nothing. The identity test is `P.decEqG₁ Q 1`, the same witness
    `DualMSM.check` uses (D-P7).

    For the identity, `toEip` is 128 zero bytes, so both coordinates read as 0
    and the shifted encoding is `p - 1` in each - which is exactly Rust's
    `coordinates().unwrap_or((ZERO, ZERO))` at ecc_chip.rs:227 followed by the
    minus-one shift. -/
def asPublicInputPoint {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : AccumulatorEncoding) (codec : G1Codec G₁) (Q : G₁) : Array Word256 :=
  let eip := codec.toEip Q
  let x := coordOfEip eip 0
  let y := coordOfEip eip 1
  let isId := decideBool (P.decEqG₁ Q 1)
  encodeAccCoordWords enc x ++ encodeAccCoordWords enc y ++
    #[BitVec.ofNat 256 (if isId then 1 else 0)]

/-- rust: circuits/src/verifier/msm.rs:210-221
    (Instantiable::as_public_input for AssignedMsm): every base expanded as a
    foreign point, then the variable scalars, then the fixed-base scalars in
    BTreeMap order. The three blocks are concatenated in that order and nothing
    else - a point/slot swap here is invisible to a length check and fatal to the
    encoding, which is why lowering/tests.rs:2063-2073 uses *distinct* scalars
    ("distinct scalars expose accidental point/slot shifts").

    Note the grouping: ALL bases first, then ALL scalars, then the fixed scalars.
    The contract's decoder instead reads point, scalar, point, scalar, tail
    (AccumulatorHelpers.yul:211-280). The two layouts agree only when each side
    carries exactly one base with one scalar, i.e. for a collapsed accumulator -
    which is what the IVC instance publishes, and what test.rs:2051-2073 builds.
    A non-collapsed `Accumulator` exported through this function would be read
    against the wrong slots by the contract, silently. -/
def asPublicInput {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : AccumulatorEncoding) (codec : G1Codec G₁) (m : AccMsm (Fr p) G₁) :
    Array Word256 :=
  let pts := m.bases.foldl
    (fun acc Q => acc ++ asPublicInputPoint (G₂ := G₂) (Gₜ := Gₜ) enc codec Q)
    (#[] : Array Word256)
  pts ++ m.scalars.map frWord ++ m.fixedBaseScalars.map (fun (_, s) => frWord s)

end AccMsm


/-! ## 5. `KzgAcc`: the accumulator -/

/-- rust: circuits/src/verifier/accumulator.rs:64-73 (struct Accumulator). The
    plan names this type `KzgAcc` (plan Section 4, Exec/Accumulator row, and
    9.5's `decodeAcc` result), so that is its Lean name; the Rust name is
    `Accumulator<S>`.

    G₂ and Gₜ are phantom parameters, for the reason D-P7 gives for `DualMSM`:
    `check` and `batchedCheck` need the pairing, the pairing target appears in no
    data-carrying field of this structure, and without a phantom nothing at the
    call site can pin it.

    The contract sees this type only in its *fully collapsed* form - one base
    with one carried scalar per side, plus the RHS fixed-base tail - because
    that is the only shape `validate_public_accumulator` can read. The Rust type
    is more general, and `decodeAcc_encode` is only statable for the collapsed
    shapes; see the note at `decodeAcc`. -/
structure KzgAcc (F G₁ G₂ Gₜ : Type) where
  /-- rust: lhs -/
  lhs : AccMsm F G₁
  /-- rust: rhs -/
  rhs : AccMsm F G₁

/-- One of the fixed bases the generated verifier embeds for the accumulator
    RHS tail. rust: proofs/solidity-verifier/src/lowering/artifacts.rs:181-227,
    where each entry is `(name, mptr, negate)` and the list is sorted by name at
    :225 to match the BTreeMap order the circuit encodes in.

    `negate` is a sign convention that exists only on the contract side: the
    circuit's fixed base for `-G` is the negated generator
    (circuits/src/verifier/mod.rs:119), while the contract embeds the *positive*
    G1 base from the VK header and negates the public scalar instead
    (artifacts.rs:200 and AccumulatorHelpers.yul:322-326, which is careful to
    reject `s >= r` *before* negating because `mod(sub(r, s), r)` is not `-s`
    for a non-canonical `s`). Both compute the same group element; the port
    models the contract's reading, so the base is positive and the scalar
    carried in `fixedBaseScalars` is the negated one. -/
structure AccFixedBase (G₁ : Type) where
  name : String
  base : G₁
  /-- rust: the `bool` third component of the `(String, usize, bool)` triple. -/
  negate : Bool

namespace KzgAcc

/-- rust: circuits/src/verifier/accumulator.rs:190-193 (Accumulator::new). -/
def new {F G₁ G₂ Gₜ : Type} (lhs rhs : AccMsm F G₁) : KzgAcc F G₁ G₂ Gₜ :=
  { lhs, rhs }

/-- rust: accumulator.rs:82-133 (Accumulator::from_dual_msm).

    The whole job is to move the terms whose commitment is a *verifying-key*
    commitment (fixed, permutation, or the custom `-G`) out of the variable-base
    part and into the name-indexed fixed map, checking each base against the map
    the caller supplied. Those three `assert_eq!(fixed_bases.get(&name),
    Some(base))` calls - accumulator.rs:105, :110, :114 - are panic sites under
    rule R4 and are ported as `Fault.panic`, including the missing-key case,
    which the Rust reaches as `assert_eq!(None, Some(base))`.

    The Rust's match has a guard arm `Custom(s) if s == "-G"`; Lean has no string
    literal patterns, so the guard is an `if` on the same equality and any other
    `Custom` label falls through to the variable-base bucket exactly as the
    Rust's `_` arm does.

    The prefix is the VK name ("self_vk" at ivc/verifier.rs:87 and :143), and
    the fixed-base map is `fixedBases` above. -/
def fromDualMsm {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (namePrefix : String)
    (fixedBases : Array (String × G₁)) : Except Fault (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
  let (lhs, rhs) := DualMSM.split d
  let l ← processMsm lhs.toList namePrefix fixedBases #[] #[] #[]
  let r ← processMsm rhs.toList namePrefix fixedBases #[] #[] #[]
  return { lhs := l, rhs := r }
where
  processMsm : List (CommitmentLabel × Fr p × G₁) → String → Array (String × G₁) →
      Array G₁ → Array (Fr p) → Array (String × Fr p) →
      Except Fault (AccMsm (Fr p) G₁)
    | [], _, _, bases, scalars, fixed => .ok { bases, scalars, fixedBaseScalars := fixed }
    | (label, scalar, base) :: rest, namePrefix, fixedBases, bases, scalars, fixed =>
        match label with
        | .fixed i =>
            let name := fixedCommitmentName namePrefix i
            if sameFixedBase fixedBases name base
            then processMsm rest namePrefix fixedBases bases scalars (accMapInsert fixed name scalar)
            else .error (Fault.panic "circuits/src/verifier/accumulator.rs:105")
        | .permutation i =>
            let name := permCommitmentName namePrefix i
            if sameFixedBase fixedBases name base
            then processMsm rest namePrefix fixedBases bases scalars (accMapInsert fixed name scalar)
            else .error (Fault.panic "circuits/src/verifier/accumulator.rs:110")
        | .custom s =>
            if s == "-G" then
              if sameFixedBase fixedBases "-G" base
              then processMsm rest namePrefix fixedBases bases scalars (accMapInsert fixed "-G" scalar)
              else .error (Fault.panic "circuits/src/verifier/accumulator.rs:114")
            else
              processMsm rest namePrefix fixedBases (bases.push base) (scalars.push scalar) fixed
        | _ => processMsm rest namePrefix fixedBases (bases.push base) (scalars.push scalar) fixed

  sameFixedBase (fixedBases : Array (String × G₁)) (name : String) (base : G₁) : Bool :=
    match fixedBases.findIdx? (fun e => e.1 == name) with
    | some i => decideBool (P.decEqG₁ (fixedBases.getD i (name, (1 : G₁))).2 base)
    | none => false

/-- rust: accumulator.rs:135-149 (Accumulator::check): evaluate both sides and
    hand them to `DualMSM::check` as a one-term-per-side dual MSM, i.e. test the
    accumulator invariant `e(lhs, [tau]_2) = e(rhs, [1]_2)` stated in the module
    header at accumulator.rs:16-25.

    The `#[cfg(feature = "solidity-verifier-trace")]` twin at
    accumulator.rs:153-173 is not ported: it differs only by two
    `record_hashable` calls (ids 29 and 30, "acc_lhs"/"acc_rhs"), and trace
    renders are out of scope (plan Section 1; Exec/Verifier makes the same cut). -/
def check {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (fixedBases : Array (String × G₁)) : Bool :=
  let lhs := a.lhs.eval fixedBases
  let rhs := a.rhs.eval fixedBases
  DualMSM.check (DualMSM.new (MSMKZG.fromBase lhs) (MSMKZG.fromBase rhs)) params

/-- rust: accumulator.rs:175-188 (Accumulator::trivial). Both sides are the
    identity base with scalar one, and the RHS carries a zero scalar for every
    fixed-base name, so both evaluate to the identity and the invariant holds
    unconditionally. The Rust builds the zero map from an *unsorted* slice and
    lets the BTreeMap sort it; the port folds through `accMapInsert` for the
    same reason. -/
def trivial {G₁ G₂ Gₜ : Type} [Group G₁]
    (fixedBaseNames : Array String) : KzgAcc (Fr p) G₁ G₂ Gₜ :=
  let zeroFixed := fixedBaseNames.foldl (fun acc n => accMapInsert acc n 0) #[]
  { lhs := { bases := #[1], scalars := #[1], fixedBaseScalars := #[] }
    rhs := { bases := #[1], scalars := #[1], fixedBaseScalars := zeroFixed } }

/-- rust: accumulator.rs:205-213 (Accumulator::collapse): both sides, in place
    in the Rust; the port returns the value. -/
def collapse {G₁ G₂ Gₜ : Type}
    [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : KzgAcc (Fr p) G₁ G₂ Gₜ :=
  { lhs := a.lhs.collapse, rhs := a.rhs.collapse }

/-- rust: accumulator.rs:215-219 (Accumulator::fully_collapse): evaluate both
    sides to a pair of points, leaving the accumulator itself alone. This is the
    point-pair the contract's `ACC_LHS_MPTR` / `ACC_RHS_MPTR` hold after
    `validate_public_accumulator`. -/
def fullyCollapse {G₁ G₂ Gₜ : Type}
    [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (fixedBases : Array (String × G₁)) : G₁ × G₁ :=
  (a.lhs.eval fixedBases, a.rhs.eval fixedBases)

/-- rust: accumulator.rs:221-239 (Accumulator::accumulate), off-circuit form.

    **The batching scalar is an argument here, and that is the R-10 divergence
    made structural.** The Rust derives it:
    `r = SpongeChip::hash(as_public_input acc0 ++ as_public_input acc1)` then
    `rs = (0..n).map(|i| r.pow(i))`, truncated under `truncated-challenges`
    (accumulator.rs:224-230). The contract derives a different scalar from a
    different preimage (`alphaOf` below), and does not truncate it. The POW2
    sponge is not ported - it is prover-side in-circuit machinery over the native
    field, and porting it here would invite exactly the confusion R-10 warns
    about. Callers that mean the contract pass `alphaOf`; callers replaying
    `verify_final` must supply the sponge value themselves, and must not expect
    agreement with the contract (R-10 consequence 1).

    The shape that *is* shared: the first accumulator is left un-scaled and each
    later one is scaled by its power and merged with `accumulateWithR` on both
    channels (accumulator.rs:232-236), which is `rs = [r^0, r^1]` skipping the
    first - the same order the contract uses (kzg un-scaled, acc by alpha).

    `accs[0]` at accumulator.rs:232 is a slice index that panics on an empty
    slice; rule R4 keeps it as a panic. -/
def accumulate {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    (F : Features) (numBits : Nat) (r : Fr p)
    (accs : Array (KzgAcc (Fr p) G₁ G₂ Gₜ)) : Except Fault (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
  let n := accs.size
  if n == 0 then throw (Fault.panic "circuits/src/verifier/accumulator.rs:232")
  -- rule R8: both branches of `#[cfg(feature = "truncated-challenges")]`.
  let rs := if F.truncatedChallenges
            then truncatedPowers numBits r n
            else powers r n
  let empty : AccMsm (Fr p) G₁ :=
    { bases := #[], scalars := #[], fixedBaseScalars := #[] }
  let first := accs.getD 0 { lhs := empty, rhs := empty }
  return (List.zip accs.toList rs).drop 1 |>.foldl
    (fun acc (other, ri) =>
      { lhs := acc.lhs.accumulateWithR other.lhs ri
        rhs := acc.rhs.accumulateWithR other.rhs ri }) first

/-- rust: accumulator.rs:252-261 (Instantiable::as_public_input for
    AssignedAccumulator): the lhs MSM's public input followed by the rhs MSM's,
    each of them bases-then-scalars-then-fixed-scalars (msm.rs:211-220). This is
    the encoding the plan 9.5 round-trip names `encodeAccInstances`, and the
    layout api.rs:21-34 documents in prose. -/
def asPublicInput {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : AccumulatorEncoding) (codec : G1Codec G₁)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
  AccMsm.asPublicInput (G₂ := G₂) (Gₜ := Gₜ) enc codec a.lhs ++
    AccMsm.asPublicInput (G₂ := G₂) (Gₜ := Gₜ) enc codec a.rhs

end KzgAcc

/-- The plan's name for `KzgAcc.asPublicInput` (plan 9.5
    `decodeAcc_encode : decodeAcc enc (encodeAccInstances enc a) = some a`).
    Kept as a separate name because the plan and the contract-facing proofs use
    it; the definition is the Rust's `as_public_input`, not a second encoding.

    It emits the accumulator *tail* only. The full instance array is
    `prefix ++ encodeAccInstances enc a` for any `prefix` of `enc.offset` words,
    which is the honest shape of `decodeAcc_encode`: the encoder cannot know the
    circuit's other public inputs, and `decodeAcc` reads at `enc.offset`. -/
def encodeAccInstances {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : AccumulatorEncoding) (codec : G1Codec G₁)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
  KzgAcc.asPublicInput enc codec a


/-! ## 6. The contract side: `decodeAcc`, `alphaOf`, `batchedCheck`

These three are what plan 9.5's `ContractRef.accepts` calls in the accumulator
arm:

    | some enc => match decodeAcc enc inst with
      | none => false | some a => batchedCheck g.params (alphaOf H g.vk.digest d a) d a

The plan's pseudo-Lean gives `decodeAcc` two arguments. The port needs four, and
the extra two are not a widening of the statement: D-P1 removes the concrete
curve, so the point decode has to come from somewhere (`G1Codec`, D-P6), and the
fixed-base tail the contract folds into `ACC_RHS` is generated per-VK
(artifacts.rs:181-227), so it has to be an argument. Whoever writes the real
`ContractRef.accepts` supplies both from the generator state. -/

/-- rust: AccumulatorHelpers.yul:190-371 (`validate_public_accumulator`), plus
    the head-guard length checks it depends on (VkLoading.yul:102, :106-112).

    Reads the accumulator tail out of the instance words and returns the
    accumulator the pairing checks then use: lhs is the carried point with the
    carried scalar, rhs is the carried point with the carried scalar plus the
    fixed-base tail. The contract evaluates that same shape eagerly - it runs
    G1MSM once per side and stores the resulting points - so `check` /
    `batchedCheck` below re-evaluate it. Keeping the scalars un-folded is what
    makes `decodeAcc_encode` statable as an equality of `KzgAcc`s rather than an
    equality up to evaluation.

    Rejections, each of which is a `false` in `ContractRef.accepts`:
    * the tail does not fit the instance array, or the limb shape is not 7x56
      (`validFor`, reached through `fixedScalarCount`). On the contract this is
      a *generation-time* error (builder/api.rs:49-51) plus a calldata-shape
      revert (VkLoading.yul:102, :106-112: the instance count and the calldata
      size must both be exactly the generated ones, so a wrong-length instance
      array never reaches the decoder at all, and trailing bytes fail closed);
    * the number of tail scalars does not match the generated fixed-base list.
      The Rust cannot express this mismatch - the template is unrolled from the
      same count - so it is a well-formedness precondition of the config rather
      than a runtime check, and `Supported.acc` is what enforces it;
    * a coordinate word with unused high bits set, a reconstructed coordinate
      above `p - 1`, a high word above 2^128, a flag other than 0 or 1, or a
      non-identity point that decodes to `(0,0)`;
    * a carried or tail scalar at or above `r` (yul:226, :290, :321). This one
      is only expressible because `inst` is `Array Word256`;
    * a decoded point that `G1Codec.ofEip?` rejects, i.e. not on the curve, not
      in the r-torsion, or not canonical. That is the model of the G1MSM calls at
      yul:246 and :357-365, which the contract runs on *every* carried point
      including identity encodings and points paired with scalar zero
      (yul:235-239: "skipping it would let a malformed non-identity point hide
      behind scalar 0"). The Rust has no analogue: its accumulator points come
      from `DualMSM::split` over commitments the transcript already
      subgroup-checked.

    Two things the contract does that this model deliberately does not:
    * it distinguishes a failed decode from a failed precompile call
      (`precompile_failed`, yul:184-189, MF-4) and maps them to different error
      classes. `Option` collapses both to `none`; the error class is a Phase 3
      conformance surface, not a decision.
    * it skips the G1MSM calls once `out` is already false (yul:242, :347),
      which changes gas but not the outcome.

    `decodeAcc_injective` (plan 9.5) is FALSE for this decoder as written, and
    the reason is in the contract, not here: with the identity flag set the
    coordinate words are neither decoded nor range-checked (yul:130-141), so two
    instance tails that differ only in the coordinate words of an identity side
    both decode to the same accumulator. `accIdentityKats_ok` below exhibits the
    pair. The statement survives only if `accWords` projects the coordinate
    words away for identity-flagged points; that is a decision for whoever
    states the theorem, and it is recorded here rather than smoothed over.

    No pairing binder here, and that is deliberate: decoding is arithmetic plus a
    point decode, so unlike `KzgAcc.check` and `batchedCheck` it needs no
    `AdmissiblePairing` - only the phantom G₂ Gₜ that `KzgAcc` carries (D-P7). -/
def decodeAcc {G₁ G₂ Gₜ : Type}
    (enc : AccumulatorEncoding) (codec : G1Codec G₁)
    (fixedBases : Array (AccFixedBase G₁)) (inst : Array Word256) :
    Option (KzgAcc (Fr p) G₁ G₂ Gₜ) := do
  let tail ← AccumulatorEncoding.fixedScalarCount enc inst.size
  if fixedBases.size != tail then none
  else
    let carried := enc.hasCarriedScalars
    let pw := enc.pointWords
    let lhsSrc := enc.offset
    -- yul:211, :273-280: the scalar slot exists only in the carried-scalar
    -- layout, and the rhs point follows it.
    let lhsScalarIdx := lhsSrc + pw
    let rhsSrc := lhsScalarIdx + if carried then 1 else 0
    let rhsScalarIdx := rhsSrc + pw
    let tailIdx := rhsScalarIdx + if carried then 1 else 0
    let lhsScalarWord := (inst.getD lhsScalarIdx 0).toNat
    let rhsScalarWord := (inst.getD rhsScalarIdx 0).toNat
    let tailWords := (List.range tail).map (fun j => (inst.getD (tailIdx + j) 0).toNat)
    if (carried && ! (lhsScalarWord < p)) || (carried && ! (rhsScalarWord < p)) ||
       tailWords.any (fun w => ! (w < p)) then none
    else
      let (lhsBytes, _) ← loadAccPoint enc inst lhsSrc
      let (rhsBytes, _) ← loadAccPoint enc inst rhsSrc
      let lhs ← codec.ofEip? lhsBytes
      let rhs ← codec.ofEip? rhsBytes
      let lhsScalar : Fr p := Nat.cast (if carried then lhsScalarWord else 1)
      let rhsScalar : Fr p := Nat.cast (if carried then rhsScalarWord else 1)
      -- yul:314-337: the tail scalars pair with the generated bases in name
      -- order, and a negated base takes the negated scalar. A zero tail scalar
      -- is left out of the MSM input (yul:327) which is the same value.
      let fixed := (List.zip fixedBases.toList tailWords).foldl
        (fun acc (b, s) => accMapInsert acc b.name (if b.negate then -s else s)) #[]
      let lhsMsm : AccMsm (Fr p) G₁ :=
        { bases := #[lhs], scalars := #[lhsScalar], fixedBaseScalars := #[] }
      let rhsMsm : AccMsm (Fr p) G₁ :=
        { bases := #[rhs], scalars := #[rhsScalar], fixedBaseScalars := fixed }
      return { lhs := lhsMsm, rhs := rhsMsm }

/-- rust: FinalPairing.yul:14-31. The contract's batching scalar:
    `mod(keccak256(DOMAIN || vk_digest || kzg_rhs || kzg_lhs || acc_rhs ||
    acc_lhs), r)`, with a zero draw replaced by one so the accumulator equation
    cannot be dropped (yul:28-31).

    Three things to notice, all of them divergences from the Rust:
    * the preimage is in EIP-2537 padded form (`toEip`), not the shifted-limb
      public-input encoding the Rust hashes (R-10 table, row 2);
    * `vk_digest` is in it (audit I-7, layout/mod.rs:332-337). The Rust has no
      vk_digest in its batch hash at all, so the contract binds alpha to the
      verifying key and the Rust does not - the contract is stronger here
      (R-10 consequence 3);
    * the order is **rhs before lhs**, on both pairs (yul:23-26), which is the
      opposite of the accumulator public-input order (lhs then rhs,
      accumulator.rs:253-261) and the opposite of `DualMSM`'s left/right naming.
      R-11 records the same trap for the pairing call site.

    The four points are the *evaluated* ones: `d.left.eval` / `d.right.eval` for
    the KZG pair and `fullyCollapse` for the accumulator, matching the four
    memory slots the contract hashes. -/
def alphaOf {G₁ : Type}
    (H : Bytes → H256) (vkDigest : Word256) (codec : G1Codec G₁)
    (kzgLhs kzgRhs accLhs accRhs : G₁) : Fr p :=
  let preimage := wordToBytesBE accPairingBatchDomainTag ++ wordToBytesBE vkDigest ++
    codec.toEip kzgRhs ++ codec.toEip kzgLhs ++ codec.toEip accRhs ++ codec.toEip accLhs
  let a := frOfDigest (p := p) (H preimage)
  if a = 0 then 1 else a

/-- rust: FinalPairing.yul:33-60 and :88. The batched check the contract
    actually performs:

      e(kzg_rhs + alpha * acc_rhs, [1]_2) * e(kzg_lhs + alpha * acc_lhs, -[s]_2) = 1

    written in `DualMSM`'s orientation, i.e. left = the point paired with `sG2`
    and right = the point paired with `-G2` (see the note in
    Exec/Kzg/Msm.lean's `DualMSM.check` and R-11 on where the swap lives).

    The contract reaches the same two points by a one-pair G1MSM followed by a
    G1ADD per side (yul:36-60); the port adds one scaled term to each channel of
    the DualMSM, which evaluates to the same group elements. Both then do one
    two-pair pairing check, and both leave the un-batched `d.check` unused in
    accumulator mode. -/
def batchedCheck {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (params : ParamsVerifierKZG G₁ G₂) (alpha : Fr p)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (fixedBases : Array (String × G₁)) : Bool :=
  let accL := (MSMKZG.fromBase (a.lhs.eval fixedBases)).scale alpha
  let accR := (MSMKZG.fromBase (a.rhs.eval fixedBases)).scale alpha
  DualMSM.check (DualMSM.new (d.left.addMsm accL) (d.right.addMsm accR)) params


/-! ## 7. Rust items in the cited sources that are NOT ported, and why

`circuits/src/verifier/accumulator.rs:75-80` - `AssignedAccumulator`, the
in-circuit twin. Every method of it is prover/recursive-circuit machinery:
`assign` (:290-320), `scale_by_bit` (:327-342), `collapse` (:357-365),
`eval` (:371-380), `fully_collapse` (:371-380) and the in-circuit
`accumulate` (:384-415). Plan Section 1 puts the prover out of scope, and none
of them is reachable from `verify_final`. Grep evidence:
`grep -n 'AssignedAccumulator' circuits/src/verifier/accumulator.rs` returns
those declarations and no call from `Accumulator`'s off-circuit impl block
(:82-240).

`circuits/src/verifier/accumulator.rs:242-250` - `InnerValue for
AssignedAccumulator`. A trait impl over in-circuit `Value<_>`; rule R9 turns
traits into structures of functions only where the verifier instantiates more
than one, and nothing here is verifier-reachable.

`circuits/src/verifier/accumulator.rs:264-282` -
`as_public_input_with_committed_scalars`. Splits the RHS scalars into a normal
instance and a *committed* instance. Grep evidence that it is prover-side:
`grep -rn 'as_public_input_with_committed_scalars' --include=*.rs .` finds only
this definition, the `AssignedMsm` twin at msm.rs:223-241, and circuit code
that builds the recursive instance. The Solidity path takes the
committed-instance commitment to be the G1 identity (api.rs:59-69,
`CommittedInstanceCommitmentKind::Identity`), so the committed half of that
split never reaches the contract.

`circuits/src/verifier/accumulator.rs:227` - `SpongeChip::hash`. The POW2
sponge over the native field. Not ported, on purpose: R-10 is the reason, and
the note at `KzgAcc.accumulate` says what a caller must do instead.

`circuits/src/verifier/msm.rs:56-74` and `:184-208` - `AssignedMsm`, its
`PartialEq`, and `InnerValue`. In-circuit again.

`circuits/src/verifier/msm.rs:244-305` and `:307-499` -
`in_circuit_as_public_input`, `constrain_as_public_input*`, `assign`,
`empty`, `from_term`, `from_fixed_term`, `add_term`, `add_msm`, and the
in-circuit `collapse` / `eval` / `scale` / `accumulate_with_r`. Prover-side.

`circuits/src/verifier/msm.rs:96-109` - the `bases`, `scalars` and
`fixed_base_scalars` accessors, which are Lean projections.

`circuits/src/verifier/mod.rs:83-87` - `Instantiable for AssignedVk`:
`as_public_input vk = as_public_input vk.transcript_repr()`. Native-field, not
foreign-point, and it belongs to Exec/VerifyingKey's `transcript_repr`.

`aggregation/src/ivc/verifier.rs:55-97` (`verify`) and `:111-151`
(`verify_final`) themselves: the outer IVC driver. Their verifier-reachable
content is `prepare` (Exec/Verifier), `assert_empty` (Exec/Transcript),
`from_dual_msm`, `accumulate` and `check`, all ported above. What is not
ported is `Ivc` / `IvcInstance` / `IvcCircuit::format_instance` /
`T::decider` (:62-73, :119-130), the `vk_repr` comparison (:62, :119 - a
field equality over the IVC instance, not a verifier primitive), `IvcError`
(a taxonomy of its own, mapped onto `Fault` by Exec/Error), and the
`fixed_bases::<S>("self_vk", ...)` call site, which is `fixedBases` above
with `vkName := "self_vk"`.

`proofs/solidity-verifier/src/api.rs:369-399` - `GeneratorConfig` and
`with_accumulator`: generator configuration, Phase 6. The plan's
`g.cfg.accumulator` and `g.cfg.numInstances` are its fields.

`proofs/solidity-verifier/src/lowering/artifacts.rs:181-245` - the computation
of `acc_fixed_bases`, `expected_acc_offset`, `expected_num_acc_limbs`,
`expected_num_acc_limb_bits` and `expected_acc_has_carried_scalars` from the
encoding and the VK. Phase 6 (the generator port). This file takes their
*outputs* as parameters: `AccFixedBase` for the base list, and the
`AccumulatorEncoding` fields for the rest.

`proofs/solidity-verifier/src/lowering/plan.rs:551-562` (`acc_msm_terms`) and
`lowering/layout/memory.rs:506, :854-859` (the accumulator MSM scratch and the
pairing-batch frame) - memory planning and gas bounds. Phase 6 and Phase 5.

`templates/partials/verifier/VkLoading.yul:82-88` - the VK-header cross-checks
that pin `HAS_ACCUMULATOR_MPTR`, `ACC_OFFSET_MPTR`, `NUM_ACC_LIMBS_MPTR` and
`NUM_ACC_LIMB_BITS_MPTR` against the compiled constants. That is the contract's
defence against a stale VK, and it belongs to the `vkLoading_spec` partial
theorem (plan 9.5), not to the accumulator codec.

`templates/partials/verifier/AccumulatorHelpers.yul:184-189, :246-248,
:357-366` - the `precompile_failed` output and the staticcall plumbing
(`returndatasize` checks, gas bounds). The revert-vs-reject distinction is an
error-class question; `decodeAcc`'s doc note says what is collapsed. -/


/-! ## 8. Known-answer checks

Hand-computed, and deliberately checked against constants this file did not
produce: the two `Constants.sol` words, the EIP-2537 G1 generator, and the
numbers the Rust test suite asserts in
`proofs/solidity-verifier/src/lowering/tests.rs:2034-2125`. Per docs/REVIEW.md
R-20, a round-trip against one's own definition proves nothing about
orientation, so each check below pins at least one value from the outside. -/

section Kats

/-- The EIP-2537 G1 generator's affine coordinates ("Generators: H1: X = ...,
    Y = ...", https://eips.ethereum.org/EIPS/eip-2537). Independently checked
    against `accFpModulus` by `accGeneratorKats_ok`: the point is on the curve
    `y^2 = x^3 + 4`. Membership in the r-torsion was checked offline by
    double-and-add; in this port the subgroup question is exactly what
    `G1Codec.ofEip?` is the named hypothesis for (D-P6), so it is not
    re-derived here. -/
def accGenX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

def accGenY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

/-- The modulus split the contract hard-codes. Constants.sol:241-242 as
    rendered, i.e. what `BLS_P_HI` and `BLS_P_MINUS_ONE_LO` are in the deployed
    verifier, against `accFpModulus` / `accFpHi` / `accFpMinusOneLo` here. This
    is the R-20 guard: if `Assumptions/Pairing.pBase` is ever the wrong curve's
    modulus again, this fails. -/
def accHiLoKats_ok : Bool :=
  accFpHi == 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7 &&
  accFpMinusOneLo == 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa &&
  -- p is 381 bits and 3 mod 4 (the two facts that distinguish BLS12-381 from
  -- the BLS12-377 modulus R-20 caught).
  accFpModulus < 2^381 && accFpModulus ≥ 2^380 && accFpModulus % 4 == 3

/-- The generator really is on the curve over `accFpModulus`. -/
def accGeneratorKats_ok : Bool :=
  (accGenY * accGenY) % accFpModulus == (accGenX * accGenX * accGenX + 4) % accFpModulus

/-- The layout arithmetic, pinned against the Rust's own assertions:
    `api.rs:77` (12 fully-collapsed words), `api.rs:80` (10 point-pair words),
    `lowering/tests.rs:2040` (`point_words()` equals the foreign-point
    encoding's length) and `:2075-2077`. -/
def accLayoutKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  let pp := AccumulatorEncoding.pointPair 0 7 56
  e.limbsPerInstance == accLimbsPerWord &&
  e.limbsPerInstance == 4 &&
  e.coordinateWords == 2 &&
  e.pointWords == 5 &&
  e.pointPairWords == 10 &&
  e.fixedPayloadWords == 12 &&
  e.fullyCollapsedPublicInputWords == some 12 &&
  pp.fixedPayloadWords == 10 &&
  pp.fullyCollapsedPublicInputWords == some 10 &&
  e.hasCarriedScalars && ! pp.hasCarriedScalars &&
  -- the pairing-batch frame: layout/mod.rs:348 and the assert at :911.
  accPairingBatchHashBytes == 0x240 &&
  accPairingBatchAccLhsOffset == 2 * accWordBytes + 3 * accG1Bytes

/-- `validFor` / `fixedScalarCount`, one decision per case the Rust test suite
    exercises (lowering/tests.rs:2082-2124). -/
def accValidForKats_ok : Bool :=
  let fc := AccumulatorEncoding.new 4 7 56
  let pp := AccumulatorEncoding.pointPair 4 7 56
  -- tests.rs:2087-2089
  fc.validFor 16 && fc.fixedScalarCount 16 == some 0 && fc.fixedScalarCount 19 == some 3 &&
  -- tests.rs:2096-2104: a point-pair with a one-word tail is rejected outright
  pp.validFor 14 && pp.fixedScalarCount 14 == some 0 && pp.fixedScalarCount 15 == none &&
  -- tests.rs:2106-2114: wrong limb shape
  ! (AccumulatorEncoding.new 4 8 32).validFor 16 &&
  -- tests.rs:2116-2124: payload does not fit
  ! (AccumulatorEncoding.new 5 7 56).validFor 16 &&
  -- offset 0, 12 words, exactly 12 instances: fits
  (AccumulatorEncoding.new 0 7 56).validFor 12 &&
  ! (AccumulatorEncoding.new 0 7 56).validFor 11

/-- The shifted-limb encoding of one coordinate, against the words computed
    independently from the EIP-2537 generator: `v = x - 1`, limbs little-endian
    radix 2^56, four per word. Note word 0 is 224 bits and word 1 is 157 bits -
    the unused high bits the decoder insists are zero. -/
def accCoordEncodeKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  let wx := encodeAccCoordWords e accGenX
  let wy := encodeAccCoordWords e accGenY
  wx.size == 2 && wy.size == 2 &&
  wx.getD 0 0 == BitVec.ofNat 256
    0x9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6ba &&
  wx.getD 1 0 == BitVec.ofNat 256 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f &&
  wy.getD 0 0 == BitVec.ofNat 256
    0xd5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e0 &&
  wy.getD 1 0 == BitVec.ofNat 256 0x8b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095

/-- The coordinate-minus-one offset, which is the whole sentinel design:
    coordinate 1 encodes as all-zero limbs, coordinate 0 encodes as `p - 1`, and
    the decoder maps `p - 1` back to 0 and adds one to everything else. -/
def accCoordOffsetKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  -- encoding of 1 is zero
  encodeAccCoordWords e 1 == #[0, 0] &&
  -- decoding zero words gives 1, not 0: the +1 is applied
  decodeAccCoord e ((#[0, 0] ++ #[0, 0] : Array Word256)) 0 == some (0, 1) &&
  -- encoding of 0 is p - 1, split as the contract splits it
  encodeAccCoordWords e 0 ==
    #[BitVec.ofNat 256 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa,
      BitVec.ofNat 256 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84] &&
  -- and it decodes back to 0 through the sentinel arm
  decodeAccCoord e (encodeAccCoordWords e 0) 0 == some (0, 0) &&
  -- the straddle case: limb 4 spans bit 256, so hi is nonzero
  (match decodeAccCoord e (encodeAccCoordWords e accGenX) 0 with
   | some (hi, lo) => hi == accGenX / 2^256 && lo == accGenX % 2^256
   | none => false)

/-- Round-trip of both coordinates of a concrete point pair, at the word level:
    this is `decodeAcc_encode` minus the group, which cannot be evaluated until
    `Assumptions/Pairing.lean` supplies a curve (D-P1, D-P6). -/
def accPointRoundTripKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  let inst := encodeAccCoordWords e accGenX ++ encodeAccCoordWords e accGenY ++ #[0]
  match loadAccPoint e inst 0 with
  | some (b, false) =>
      b.size == 128 &&
      coordOfEip b 0 == accGenX && coordOfEip b 1 == accGenY &&
      -- the four stored words are the EIP-2537 padding: 16 zero bytes then the
      -- 48 big-endian bytes, per coordinate
      (match bytesTake b 0 16, bytesTake b 64 16 with
      | some z1, some z2 => z1 == natToBytesBE 0 16 && z2 == natToBytesBE 0 16
      | _, _ => false)
  | _ => false

/-- The identity-flag arm, and the injectivity counterexample it implies.
    `lowering/tests.rs:2048` asserts the flag word of the identity is 1 and
    `:2049` that the generator's is 0; the flag sits at index 4, after the two
    coordinate words of x and the two of y. -/
def accIdentityKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  let idInst := encodeAccCoordWords e 0 ++ encodeAccCoordWords e 0 ++ #[1]
  -- the identity round-trips to the all-zero EIP-2537 encoding
  (match loadAccPoint e idInst 0 with
   | some (b, true) => b == natToBytesBE 0 128
   | _ => false) &&
  -- a non-identity flag over coordinates that decode to (0,0) is rejected:
  -- EIP-2537 reserves the all-zero point for infinity (yul:152-157)
  loadAccPoint e (encodeAccCoordWords e 0 ++ encodeAccCoordWords e 0 ++ #[0]) 0 == none &&
  -- a flag of 2 is malformed, not "some other point" (yul:125-127)
  loadAccPoint e (encodeAccCoordWords e accGenX ++ encodeAccCoordWords e accGenY ++ #[2]) 0 == none &&
  -- COUNTEREXAMPLE to plan 9.5 `decodeAcc_injective`: with the flag set the
  -- coordinate words are not decoded at all, so these two different tails -
  -- neither of which is the canonical identity encoding - decode to the same
  -- identity point.
  (match loadAccPoint e (encodeAccCoordWords e 12345 ++ encodeAccCoordWords e 54321 ++ #[1]) 0 with
   | some (b, true) => b == natToBytesBE 0 128
   | _ => false)

/-- The packing-canonicity check (yul:62-83). Without it the same coordinate has
    several encodings: a bit set above the used limb bits reconstructs to the
    same value, so the contract rejects it before the precompile ever sees it. -/
def accPackingKats_ok : Bool :=
  let e := AccumulatorEncoding.new 0 7 56
  -- word 0 holds 4*56 = 224 bits; bit 224 must be zero. Setting it does not
  -- change any extracted limb, so only this check catches it.
  decodeAccCoord e (#[BitVec.ofNat 256 (2^224), 0] : Array Word256) 0 == none &&
  -- word 1 holds 3*56 = 168 bits; bit 168 must be zero.
  decodeAccCoord e (#[0, BitVec.ofNat 256 (2^168)] : Array Word256) 0 == none &&
  -- and the same words with the bit clear decode fine
  decodeAccCoord e (#[0, 0] : Array Word256) 0 == some (0, 1) &&
  -- a reconstructed coordinate of exactly p is out of the field: 7 limbs of 56
  -- bits reach 2^392, so this arm is reachable even though the limbs look sane.
  decodeAccCoord e (#[BitVec.ofNat 256 (2^224 - 1), BitVec.ofNat 256 (2^168 - 1)] : Array Word256) 0 == none

/-- The limb codec against the two definitions the Rust states: `bi_to_limbs`
    little-endian, `bi_from_limbs` folding the reverse. -/
def accLimbKats_ok : Bool :=
  let ls := biToLimbs 7 56 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa
  ls.size == 7 &&
  ls.getD 0 0 == 0xfeffffffffaaaa &&
  ls.getD 6 0 == 0x1a0111ea397f &&
  biFromLimbs 56 ls == 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa &&
  -- a value that does not fit is truncated rather than panicking, unlike
  -- util.rs:93-98; recorded because the encoder relies on it never happening.
  (biToLimbs 2 8 0x1234).toList == [0x34, 0x12]

/-- The name ordering the fixed-base tail depends on: Rust `String` Ord is
    UTF-8 bytes, Lean's is codepoints, and both put `-G` first and `..._10`
    before `..._2`. -/
def accNameOrderKats_ok : Bool :=
  ("-G" : String) < fixedCommitmentName "self_vk" 0 &&
  fixedCommitmentName "self_vk" 10 < fixedCommitmentName "self_vk" 2 &&
  permCommitmentName "self_vk" 0 == "self_vk_perm_com_0" &&
  -- fixed_base_names is insertion-ordered (mod.rs:143-159) and the tail the
  -- contract reads is name-ordered (artifacts.rs:225); for this VK shape the
  -- two coincide, and accMapInsert is what makes the second one true.
  (fixedBaseNames "self_vk" 2 1).toList ==
    ["-G", "self_vk_fixed_com_0", "self_vk_fixed_com_1", "self_vk_perm_com_0"] &&
  (["self_vk_perm_com_0", "self_vk_fixed_com_1", "-G", "self_vk_fixed_com_0"].foldl
      (fun acc n => accMapInsert acc n 0) (#[] : Array (String × Nat))).toList.map Prod.fst ==
    ["-G", "self_vk_fixed_com_0", "self_vk_fixed_com_1", "self_vk_perm_com_0"]

end Kats

#eval accHiLoKats_ok            -- expect true
#eval accGeneratorKats_ok       -- expect true
#eval accLayoutKats_ok          -- expect true
#eval accValidForKats_ok        -- expect true
#eval accCoordEncodeKats_ok     -- expect true
#eval accCoordOffsetKats_ok     -- expect true
#eval accPointRoundTripKats_ok  -- expect true
#eval accIdentityKats_ok        -- expect true
#eval accPackingKats_ok         -- expect true
#eval accLimbKats_ok            -- expect true
#eval accNameOrderKats_ok       -- expect true

end Midfall.Halo2
