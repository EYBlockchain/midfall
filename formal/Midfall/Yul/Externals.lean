-- |
-- Midfall.Yul.Externals
--
-- Phase 5 groundwork (plan Section 7, the "Externals.lean" bullet; the tree row
-- in Section 3 Midfall/Yul/{Bridge,Externals,...}; milestone M4): the
-- byte-exact EIP-2537 and EIP-198/7883 external-call relations, stated over
-- Midfall.Bytes only.
--
-- Design decision D-P1 (docs/design.md) consequence 2 puts the concrete curve
-- *only* in the execution layer and in these external-call relations, where it
-- is validated differentially against revm rather than proved. This file is
-- therefore self-contained at the byte level: it imports no Phase 2 module, and
-- the field arithmetic it needs is integer arithmetic modulo the two published
-- BLS12-381 moduli, not a curve object.
--
-- Finding Y-1 (docs/ecosystem.md section 10): EVM.ExternalCalls is a *structure*
-- bundling one ternary relation
-- (CallRequest -> EvmState -> CallResponse -> Prop,
-- vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:472-474), so there is
-- no union of relations to define. Everything here is a plain decidable
-- predicate on bytes; the ExternalCalls.mk assembly - and the obligation Y-1
-- states, that the sub-relations agree on any request two of them match -
-- belongs to Midfall/Yul/Bridge.lean.
--
-- ## Provenance shorthand
--
-- Every "-- yul:" citation below names one of these files (repo-root-relative),
-- at the @formal-baseline freeze:
--
--   AssemblyHelpers.yul    proofs/solidity-verifier/templates/partials/verifier/AssemblyHelpers.yul
--   FinalPairing.yul       proofs/solidity-verifier/templates/partials/verifier/FinalPairing.yul
--   AccumulatorHelpers.yul proofs/solidity-verifier/templates/partials/verifier/AccumulatorHelpers.yul
--   PrecompileSmoke.sol    proofs/solidity-verifier/templates/partials/verifier/PrecompileSmoke.sol
--   Constants.sol          proofs/solidity-verifier/templates/partials/verifier/Constants.sol
--   layout/mod.rs          proofs/solidity-verifier/src/lowering/layout/mod.rs
--   render/models.rs       proofs/solidity-verifier/src/lowering/render/models.rs
--   kzg/mod.rs             proofs/solidity-verifier/src/lowering/kzg/mod.rs
--   tests.rs               proofs/solidity-verifier/src/lowering/tests.rs
--
-- ## What is modelled, and what is not
--
-- | EIP-2537 / EIP-198 condition | here |
-- |---|---|
-- | frame byte layout, input and output lengths | modelled, pinned against the generator's own mstore/mcopy offsets |
-- | coordinate canonicity (below p, hence the 16 leading zero bytes) | modelled |
-- | (0,0) encodes the point of infinity, on either side | modelled |
-- | "on the curve or infinity" (G1ADD, G1MSM, PAIRING_CHECK) | modelled, G1 over Fp and G2 over Fp2 |
-- | "in the correct subgroup" (G1MSM, PAIRING_CHECK) | modelled as r * P = O by explicit affine double-and-add |
-- | the G1ADD and G1MSM results | computed, not assumed |
-- | the PAIRING_CHECK result | NOT computed: it needs Fp12. It is the single arithmetic hole, exactly the one plan Section 1 lists as an assumption, and PairingProduct below carries it |
-- | the modexp result (base^exp) mod modulus | computed by square-and-multiply |
-- | EIP-7823 modexp max-size rejection | modelled |
-- | the caller's calldatacopy / returndatacopy behaviour | out of scope: "input" is the already-copied slice, exactly as YulSemantics.CallRequest.input documents (EVMExec.lean:412-426) |
--
-- ## Divergences found while porting (reported, not smoothed over)
--
-- 1. formal/Midfall/Assumptions/Pairing.lean:52-53 defines pBase as
--    0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a06eb9650edc43970ae792c8d1bfa739f9e3d100cb9.
--    That is the BLS12-**377** base-field modulus (385 bits, 1 mod 4), not the
--    BLS12-381 one: EIP-2537 gives p = ...f6b0f6241eabfffeb153ffffb9feffffffffaaab
--    (381 bits, 3 mod 4) and the generator agrees with the EIP
--    (Constants.sol:241-242 render p-1 as BLS_P_HI || BLS_P_MINUS_ONE_LO). This
--    file defines its own blsP and does not import pBase. Owner: Assumptions/
--    (R-3 already makes that file the trust boundary).
-- 2. The generator's modexp constant is a *bound*, not the price of the frame it
--    emits: MODEXP_GAS = 4080 uses the generic 255-iteration upper bound for a
--    32-byte exponent, while the exponent every generated call site writes is
--    r - 2, which is 255 bits and so prices at 16 * 254 = 4064 under EIP-7883.
--    Deliberate and documented at layout/mod.rs:232-236; pinned by
--    modexpGasKats_ok below.
-- 3. EIP-2565 and EIP-7883 spell the long-exponent term as
--    (exponent & (2**256 - 1)).bit_length() - 1, which reads as the LOW 256
--    bits, while EIP-198's prose says "the index of the highest bit in the
--    *first* 32 bytes of EXPONENT" and the clients use the HIGH bytes
--    (revm-precompile-16.2.0/src/modexp.rs: right_pad_with_offset::<32>(input,
--    base_len) then [..exp_highp_len]). The client reading is used here. It
--    cannot matter for the generated frames, which always have expsize = 32.
-- 4. The work-package brief describes three layouts that do not match either
--    source of truth, so they are implemented the EIP's (and the generator's) way:
--      * "G1MSM: input = 0x80*k bytes of points followed by 0x20*k scalars".
--        Both the EIP ("k slices each of them being a byte concatenation of
--        encoding of a G1 point (128 bytes) and encoding of a scalar value
--        (32 bytes)") and the generator (AccumulatorHelpers.yul:300-303, which
--        advances the pair cursor by 0xa0 after writing point then scalar)
--        interleave them. A 0x80*k ‖ 0x20*k frame is 160*k bytes long and so
--        passes the length test while decoding to entirely different pairs.
--      * "G1ADD: input = 0x80 bytes". The frame is 0x100 bytes (two padded
--        points); the brief's own coordinate list says as much.
--      * "modexp output = exactly modsize bytes, left-padded to a multiple of
--        32". EIP-198 says "a byte array with the same length as the modulus"
--        and revm left_pad_vecs to mod_len, so a modsize of 1 returns 1 byte
--        and a modsize of 0 returns nothing. All generated frames use modsize
--        32, where the two readings coincide.
-- 5. The pinned revm (revm-precompile 16.2.0, Cargo.lock:2822-2824) prices
--    modexp with berlin_run, i.e. EIP-2565 with the / 3 divisor, and enforces
--    only a 64-bit overflow guard rather than the EIP-7823 limits. So neither
--    EIP-7883 nor EIP-7823 is reachable from the M4 revm differential as pinned
--    - which is what proofs/solidity-verifier/src/evm.rs:389-400 (MF-1) already
--    says about the gas bound.

import Midfall.Common.Bytes

namespace Midfall.Yul

open Midfall

/-! ### The two moduli, the curve coefficients and the precompile addresses -/

/-- The BLS12-381 base-field modulus.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Curve parameters":
    "Base field modulus = p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab")
    -- yul: Constants.sol:241-242 @formal-baseline
    See divergence 1 in the file header. -/
def blsP : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The BLS12-381 scalar field order, i.e. EIP-2537's "main subgroup order q".
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Main subgroup order = q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
    -- yul: Constants.sol:236 @formal-baseline (FR_MODULUS) -/
def blsR : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The G1 curve coefficient: Y^2 = X^3 + 4 over Fp.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Curve Fp equation: Y^2 = X^3+B (mod p)", "B coefficient = 0x...04") -/
def g1B : Nat := 4

/-- The G2 twist coefficient B*(v+1) = (4, 4).
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Curve Fp2 equation: Y^2 = X^3 + B*(v+1)", "B coefficient for twist c0 = 4", "c1 = 4") -/
def g2B : Nat × Nat := (4, 4)

/-- EIP-198 modexp, address 0x05.
    -- yul: layout/mod.rs:131 (MODEXP_ADDRESS); call sites AssemblyHelpers.yul:33,187,238 and PrecompileSmoke.sol:56 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-198 -/
def modexpAddress : Word256 := 0x05

/-- EIP-2537 G1ADD, address 0x0b.
    -- yul: layout/mod.rs:133 (G1ADD_ADDRESS); call sites FinalPairing.yul:44,58, kzg/mod.rs:1886,1906 and PrecompileSmoke.sol:69,90 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("ABI for G1 addition") -/
def g1AddAddress : Word256 := 0x0b

/-- EIP-2537 G1MSM, address 0x0c.
    -- yul: layout/mod.rs:135 (G1MSM_ADDRESS); call sites FinalPairing.yul:39,53, 
    -- AccumulatorHelpers.yul:246,357-364, kzg/mod.rs:1873,1898 and PrecompileSmoke.sol:124,151,202 
    -- @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("ABI for G1 MSM") -/
def g1MsmAddress : Word256 := 0x0c

/-- EIP-2537 PAIRING_CHECK, address 0x0f.
    -- yul: layout/mod.rs:137 (PAIRING_ADDRESS); call site AssemblyHelpers.yul:294 (ec_pairing) and PrecompileSmoke.sol:176,183,212 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("ABI for pairing check") -/
def pairingAddress : Word256 := 0x0f

/-- The EIP-7823 upper bound on each of the three modexp length words.
    -- eip: https://eips.ethereum.org/EIPS/eip-7823 ("each of the length inputs (length_of_BASE, 
    -- length_of_EXPONENT and length_of_MODULUS) MUST be less than or equal to 8192 bits (1024 bytes) ... 
    -- the precompile execution stops, returns an error, and consumes all gas") -/
def modexpMaxLen : Nat := 1024

/-! ### Byte-level helpers local to this file -/

/-- One EVM word, 32 bytes.
    -- yul: layout/mod.rs:31 (WORD_BYTES) @formal-baseline -/
def wordBytes : Nat := 32

/-- n copies of one byte. Array.mkArray does not exist in v4.35.0 and
    arrayReplicate lives in Exec/Kzg/Utils.lean, which this Phase 5 file must not
    import, so this goes through List.replicate. -/
def bytesReplicate (n : Nat) (v : UInt8) : Bytes :=
  ByteArray.mk (List.replicate n v |>.toArray)

/-- The all-zero byte string of length n. -/
def bytesZero (n : Nat) : Bytes := bytesReplicate n 0

/-- n big-endian bytes of m, most significant byte first: the reading
    bytesToNatBE already implements, and the round-trip
    bytesToNatBE (bytesNatBE v n) == v (for v < 256^n) pins it.

    HISTORY, corrected by package 5 (docs/REVIEW.md R-46): an earlier revision of
    this comment stated that Midfall.natToBytesBE was *little*-endian despite its
    name, that natToBytesBE 0x01020304 4 evaluated to [4, 3, 2, 1], and that
    wordToBytesBE shared the defect. That was true when it was written - it is the
    first bug recorded in R-20 - and it is no longer true. Measured on this tree:
    natToBytesBE 0x01020304 4 = [1, 2, 3, 4] and natToBytesLE 0x01020304 4 =
    [4, 3, 2, 1]; Common/Bytes.lean:59-60 now reverses the low-first accumulator.
    Leaving the warning in place was itself a hazard: a reader would conclude the
    byte-layout gates lean on a broken function and might "fix" working code.
    R-20 keeps the historical record; this comment no longer contradicts it.

    bytesNatBE is retained rather than folded into natToBytesBE: it is the local
    definition this file's own round-trip gate pins, and two independent big-endian
    encoders that must agree is worth more than one shared one. -/
def bytesNatBE (v len : Nat) : Bytes :=
  ByteArray.mk (((List.range len).reverse.map
    (fun (i : Nat) => Nat.toUInt8 ((v / (256 ^ i)) % 256))).toArray)

/-- Concatenation of two byte strings. -/
def bytesAppend (a b : Bytes) : Bytes := ByteArray.mk (a.data ++ b.data)

/-- Byte-string equality (ByteArray carries no BEq of its own). -/
def bytesEq (a b : Bytes) : Bool := a.data == b.data

/-- bs[i, i+n), clamped to the bytes that exist. Unlike bytesTake this is total,
    which is what the EIP-198 padding rule needs. -/
def bytesSlice (bs : Bytes) (i n : Nat) : Bytes :=
  ByteArray.mk (bs.data.extract (min i bs.size) (min (i + n) bs.size))

/-- bs[i, i+n) right-padded with zero bytes: EIP-198's "Call data is assumed to
    be infinitely right-padded with zero bytes, and excess data is ignored". -/
def bytesSlicePad (bs : Bytes) (i n : Nat) : Bytes :=
  let s := bytesSlice bs i n
  bytesAppend s (bytesZero (n - s.size))

/-- Concatenate 32-byte big-endian words. This is the shape every generated call
    site has: a chain of mstores of 32-byte words into a scratch buffer. -/
def bytesOfWords (ws : List Nat) : Bytes :=
  ws.foldl (fun (acc : Bytes) (w : Nat) => bytesAppend acc (bytesNatBE w wordBytes)) Bytes.empty

/-! ### Layout constants, each traced to the generator offset it ports -/

/-- 48 big-endian bytes of an unpadded BLS12-381 base-field coordinate.
    -- yul: layout/mod.rs:76 (BLS_FP_BYTES) @formal-baseline -/
def fpBytes : Nat := 48

/-- The 16 zero bytes that pad a coordinate's high word.
    -- yul: layout/mod.rs:78 (EIP2537_FP_PAD_BYTES) @formal-baseline; Midfall.eipPad is the same 16 bytes -/
def fpPadBytes : Nat := 16

/-- A padded G1 point: x_hi || x_lo || y_hi || y_lo = 4 words = 0x80 bytes.
    -- yul: layout/mod.rs:63,69 (G1_WORDS, G1_BYTES); written as four mstores at PrecompileSmoke.sol:85-88 
    -- and copied as one 0x80 mcopy at AssemblyHelpers.yul:284,286 and FinalPairing.yul:36,42 
    -- @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Total encoding length for a G1 point is thus 128 bytes") -/
def g1Bytes : Nat := 128

/-- A padded G2 point: x_c0 || x_c1 || y_c0 || y_c1 = 8 words = 0x100 bytes.
    -- yul: layout/mod.rs:65,71 (G2_WORDS, G2_BYTES); AssemblyHelpers.yul:285,287 mcopy 0x100 for each G2 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("for a G2 point is 256 bytes") -/
def g2Bytes : Nat := 256

/-- A padded Fr scalar: one 32-byte big-endian word.
    -- yul: layout/mod.rs:67 (FR_BYTES); the MSM scalar slot is at add(pair_ptr, 0x80), AccumulatorHelpers.yul:241,301,331 and FinalPairing.yul:37,51 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Encoding of scalars for multiplication operation": 32 
    -- bytes big-endian, and the integer "is not required to be less than or equal to main subgroup order 
    -- q") -/
def frBytes : Nat := 32

/-- G1ADD input: two padded G1 points, 0x100 bytes.
    -- yul: layout/mod.rs:82 (G1ADD_INPUT_BYTES = 2 * G1_BYTES); the staticcall length argument at FinalPairing.yul:44,58 and kzg/mod.rs:1886,1906 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("G1 addition call expects 256 bytes ... interpreted as byte concatenation of two G1 points (128 bytes each)") -/
def g1AddInputBytes : Nat := 2 * g1Bytes

/-- G1MSM input tuple: one padded G1 then one scalar, 0xa0 bytes, and the tuples
    are INTERLEAVED (point, scalar, point, scalar, ...), not "all points followed
    by all scalars".
    -- yul: layout/mod.rs:80 (G1_MSM_PAIR_BYTES = G1_BYTES + FR_BYTES); the pair cursor advances by 0xa0 at 
    -- AccumulatorHelpers.yul:303,332 and each pair is mcopy(point) then mstore(scalar) at :300-301, 
    -- :330-331 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("G1 MSM call expects 160*k ... k slices each of them 
    -- being a byte concatenation of encoding of a G1 point (128 bytes) and encoding of a scalar value (32 
    -- bytes)") -/
def g1MsmPairBytes : Nat := g1Bytes + frBytes

/-- PAIRING_CHECK tuple: one padded G1 then one padded G2, 0x180 bytes.
    -- yul: layout/mod.rs:95 (PAIRING_PAIR_BYTES); AssemblyHelpers.yul:284-287 lays out [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)] @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Pairing check call expects 384*k ... Each slice has 
    -- the following structure: 128 bytes of G1 point encoding, 256 bytes of G2 point encoding") -/
def pairingPairBytes : Nat := g1Bytes + g2Bytes

/-- The verifier's whole two-pair pairing frame, 0x300 bytes.
    -- yul: layout/mod.rs:97 (PAIRING_TWO_PAIR_BYTES); the staticcall length at AssemblyHelpers.yul:294 and PrecompileSmoke.sol:176 @formal-baseline -/
def pairingTwoPairBytes : Nat := 2 * pairingPairBytes

/-- The modexp header: basesize || expsize || modsize, three words = 0x60.
    -- yul: layout/mod.rs:275-279 (modexp_frame BASE_LEN_OFFSET 0x00, EXP_LEN_OFFSET 0x20, MOD_LEN_OFFSET 0x40), mstored at AssemblyHelpers.yul:27-29 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-198 ("<length_of_BASE> <length_of_EXPONENT> <length_of_MODULUS> <BASE> <EXPONENT> <MODULUS>") -/
def modexpHeaderBytes : Nat := 3 * wordBytes

/-- The modexp base value offset, 0x60.
    -- yul: layout/mod.rs:281 (BASE_OFFSET); mstore(add(p, 0x60), x) at AssemblyHelpers.yul:30 @formal-baseline -/
def modexpBaseOffset : Nat := 3 * wordBytes

/-- The modexp exponent value offset, 0x80.
    -- yul: layout/mod.rs:283 (EXP_OFFSET); mstore(add(p, 0x80), sub(FR_MODULUS, 2)) at AssemblyHelpers.yul:31 @formal-baseline -/
def modexpExpOffset : Nat := 4 * wordBytes

/-- The modexp modulus value offset, 0xa0.
    -- yul: layout/mod.rs:285 (MOD_OFFSET); mstore(add(p, 0xa0), FR_MODULUS) at AssemblyHelpers.yul:32 @formal-baseline -/
def modexpModOffset : Nat := 5 * wordBytes

/-- The generated modexp frame: header plus three 32-byte operands, 0xc0 bytes.
    -- yul: layout/mod.rs:86-87 (MODEXP_FRAME_WORDS = 6, MODEXP_FRAME_BYTES); the staticcall length at AssemblyHelpers.yul:33,187,238 @formal-baseline -/
def modexpFrameBytes : Nat := 6 * wordBytes

/-- The generated modexp output: exactly one word, because modsize is 32.
    -- yul: render/models.rs:214 (output_bytes = WORD_BYTES); returndatasize check at AssemblyHelpers.yul:34,188 @formal-baseline -/
def modexpFrameOutputBytes : Nat := wordBytes


/-! ### Fp, Fp2 and the affine group law

Everything below is integer arithmetic on decoded bytes. There is no curve type
and no field type: a point is a pair of naturals, and the only algebraic facts
needed are the curve equation and r * P = O. -/

/-- Modular exponentiation by explicit square-and-multiply, most-significant bit
    first (plan rule R7: "Exponentiation uses explicit square-and-multiply").
    Folding over List.range instead of recursing keeps this file free of
    termination obligations. The fold is the textbook left-to-right binary
    method: after the iteration for bit i the accumulator holds
    base raised to the bits of exp at and above i. -/
def modPow (base exp m : Nat) : Nat :=
  (List.range (Nat.log2 exp + 1)).reverse.foldl
    (fun (acc : Nat) (i : Nat) =>
      let sq := acc * acc % m
      if Nat.testBit exp i then sq * base % m else sq)
    (1 % m)

/-- Inversion in Fp by Fermat's little theorem; none for 0. p is prime, so this
    is an inverse for every nonzero residue. -/
def fpInv (x : Nat) : Option Nat :=
  if x % blsP == 0 then none else some (modPow x (blsP - 2) blsP)

/-- The tiny field interface the affine group law needs: enough to state
    Y^2 = X^3 + b and the chord-and-tangent law over Fp (G1) and Fp2 (G2) with
    one implementation. A value parameter rather than a class, so every use site
    is plainly computable (rule R9: a family of functions becomes a structure of
    functions). -/
structure FieldOps (alpha : Type) where
  zero : alpha
  one : alpha
  add : alpha -> alpha -> alpha
  sub : alpha -> alpha -> alpha
  mul : alpha -> alpha -> alpha
  neg : alpha -> alpha
  inv : alpha -> Option alpha
  beq : alpha -> alpha -> Bool
  /-- The curve coefficient in Y^2 = X^3 + b. -/
  b : alpha

/-- An affine point over alpha. (zero, zero) is the point of infinity: EIP-2537
    says the all-zero encoding "is instead used by convention to encode the point
    of infinity", and (0,0) is not itself on either curve because b <> 0, so the
    representation is unambiguous. -/
abbrev AffinePt (alpha : Type) : Type := alpha × alpha

/-- Is this the point of infinity? -/
def affineIsInfinity {alpha : Type} (F : FieldOps alpha) (P : AffinePt alpha) : Bool :=
  F.beq P.1 F.zero && F.beq P.2 F.zero

/-- On the curve Y^2 = X^3 + b, or infinity.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Group G1 is defined as a set of Fp pairs (points) (x,y) such that either (x,y) is (0,0) or x,y satisfy the curve Fp equation") -/
def affineOnCurve {alpha : Type} (F : FieldOps alpha) (P : AffinePt alpha) : Bool :=
  affineIsInfinity F P ||
    F.beq (F.mul P.2 P.2) (F.add (F.mul (F.mul P.1 P.1) P.1) F.b)

/-- Negation: (x, y) |-> (x, -y), infinity fixed. -/
def affineNeg {alpha : Type} (F : FieldOps alpha) (P : AffinePt alpha) : AffinePt alpha :=
  if affineIsInfinity F P then P else (P.1, F.neg P.2)

/-- Doubling by the tangent: lambda = 3x^2 / 2y, x3 = lambda^2 - 2x,
    y3 = lambda (x - x3) - y. A zero denominator (y = 0) gives infinity, which
    cannot happen on these prime-order curves but keeps the function total. -/
def affineDouble {alpha : Type} (F : FieldOps alpha) (P : AffinePt alpha) : AffinePt alpha :=
  if affineIsInfinity F P then (F.zero, F.zero)
  else
    let two := F.add F.one F.one
    let three := F.add two F.one
    match F.inv (F.mul two P.2) with
    | none => (F.zero, F.zero)
    | some i =>
        let l := F.mul (F.mul three (F.mul P.1 P.1)) i
        let x := F.sub (F.mul l l) (F.mul two P.1)
        let y := F.sub (F.mul l (F.sub P.1 x)) P.2
        (x, y)

/-- The chord-and-tangent sum, with the doubling and opposite-point cases. -/
def affineAdd {alpha : Type} (F : FieldOps alpha) (P Q : AffinePt alpha) : AffinePt alpha :=
  if affineIsInfinity F P then Q
  else if affineIsInfinity F Q then P
  else if F.beq P.1 Q.1 then
    if F.beq P.2 Q.2 then affineDouble F P else (F.zero, F.zero)
  else
    match F.inv (F.sub Q.1 P.1) with
    | none => (F.zero, F.zero)
    | some i =>
        let l := F.mul (F.sub Q.2 P.2) i
        let x := F.sub (F.sub (F.mul l l) P.1) Q.1
        let y := F.sub (F.mul l (F.sub P.1 x)) P.2
        (x, y)

/-- Scalar multiplication by explicit double-and-add over the bits of n, least
    significant first. n = 0 gives infinity. -/
def affineSmul {alpha : Type} (F : FieldOps alpha) (n : Nat) (P : AffinePt alpha) : AffinePt alpha :=
  ((List.range (Nat.log2 n + 1)).foldl
    (fun (st : AffinePt alpha × AffinePt alpha) (i : Nat) =>
      (if Nat.testBit n i then affineAdd F st.1 st.2 else st.1, affineDouble F st.2))
    ((F.zero, F.zero), P)).1

/-- Arithmetic in Fp. -/
def fpOps : FieldOps Nat where
  zero := 0
  one := 1 % blsP
  add := fun a b => (a + b) % blsP
  sub := fun a b => (a + blsP - b % blsP) % blsP
  mul := fun a b => (a * b) % blsP
  neg := fun x => (blsP - x % blsP) % blsP
  inv := fpInv
  beq := fun a b => a % blsP == b % blsP
  b := g1B

/-- Arithmetic in Fp2 = Fp[v]/(v^2 + 1), an element being (c0, c1) for
    c0 + c1 * v.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Fp2 is Fp[X]/(X^2-nr2)" with
    nr2 = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa,
    which is p - 1, so v^2 = -1 and the product is (a0 b0 - a1 b1, a0 b1 + a1 b0)) -/
def fp2Ops : FieldOps (Nat × Nat) where
  zero := (0, 0)
  one := (1, 0)
  add := fun a b => ((a.1 + b.1) % blsP, (a.2 + b.2) % blsP)
  sub := fun a b => ((a.1 + blsP - b.1 % blsP) % blsP, (a.2 + blsP - b.2 % blsP) % blsP)
  mul := fun a b =>
    ((a.1 * b.1 + (blsP - a.2 * b.2 % blsP)) % blsP, (a.1 * b.2 + a.2 * b.1) % blsP)
  neg := fun x => ((blsP - x.1 % blsP) % blsP, (blsP - x.2 % blsP) % blsP)
  inv := fun x =>
    if x.1 % blsP == 0 && x.2 % blsP == 0 then none
    else
      -- (c0 + c1 v)^-1 = (c0 - c1 v) / (c0^2 + c1^2). The norm is nonzero for
      -- every nonzero element because -1 is a quadratic non-residue mod p, and
      -- p = 3 mod 4 (which is why EIP-2537 picks this tower at all).
      let n := (x.1 * x.1 + x.2 * x.2) % blsP
      match fpInv n with
      | none => none
      | some ni => some ((x.1 * ni) % blsP, (blsP - x.2 * ni % blsP) % blsP)
  beq := fun a b => a.1 % blsP == b.1 % blsP && a.2 % blsP == b.2 % blsP
  b := g2B

/-- A G1 point as the precompile group: the r-torsion, infinity included.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 (G1MSM error case "An input is
    on the G1 elliptic curve but not in the correct subgroup") -/
def g1InSubgroup (P : AffinePt Nat) : Bool :=
  affineSmul fpOps blsR P == (0, 0)

/-- A G2 point in the r-torsion. -/
def g2InSubgroup (P : AffinePt (Nat × Nat)) : Bool :=
  affineSmul fp2Ops blsR P == ((0, 0), (0, 0))

/-! ### Coordinate, point and scalar codecs -/

/-- The 64-byte EIP-2537 padded encoding of an Fp element: 16 zero bytes then
    the 48 big-endian bytes.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("A base field element (Fp) is
    encoded as 64 bytes by performing the BigEndian encoding of the corresponding
    (unsigned) integer. Due to the size of p, the top 16 bytes are always zeroes")
    -- yul: layout/mod.rs:78 (EIP2537_FP_PAD_BYTES); the transcript absorbs the
    same form at AssemblyHelpers.yul:108 (calldatacopy of 0x80) @formal-baseline -/
def fpCoordBytes (x : Nat) : Bytes :=
  bytesAppend eipPad (bytesNatBE x fpBytes)

/-- Decode a 64-byte padded coordinate, requiring canonicity. Canonicity subsumes
    the padding test: p < 2^381, so every value below p has its top 128 bits
    zero. The generator checks the two separately (shr(128, x_hi_word) at
    AssemblyHelpers.yul:94-95, then the BLS_P_HI / BLS_P_MINUS_ONE_LO comparison
    at :99-104) @formal-baseline.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("The corresponding integer must be less than field 
    -- modulus ... On inputs that can not be a valid encodings of field elements the precompile must return 
    -- an error") -/
def fpCoordOf? (b : Bytes) : Option Nat :=
  match bytesTake b 0 (fpPadBytes + fpBytes) with
  | none => none
  | some c => let v := bytesToNatBE c
              if v < blsP then some v else none

/-- Decode a padded G1 point (128 bytes) into (x, y). The all-zero encoding
    decodes to (0, 0), the point of infinity.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Encoding of points in G1/G2: Points of G1 and G2 are 
    -- encoded as byte concatenation of the respective encodings of the x and y coordinates") -/
def g1Of? (b : Bytes) : Option (Nat × Nat) :=
  match fpCoordOf? (bytesSlice b 0 64), fpCoordOf? (bytesSlice b 64 64) with
  | some x, some y => some (x, y)
  | _, _ => none

/-- Encode a padded G1 point (128 bytes). -/
def g1PointBytes (P : Nat × Nat) : Bytes :=
  bytesAppend (fpCoordBytes P.1) (fpCoordBytes P.2)

/-- Decode a padded G2 point (256 bytes) into ((x_c0, x_c1), (y_c0, y_c1)).
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("For an Fp2 element in a form el = c0 + c1 * v ... the corresponding byte encoding will be encode(c0) || encode(c1)")
    -- yul: the generator's G2 slots hold exactly this order: the eight words at
    PrecompileSmoke.sol:161-168 are x_c0 then x_c1 then y_c0 then y_c1 of the
    EIP-2537 H2 generator @formal-baseline -/
def g2Of? (b : Bytes) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match fpCoordOf? (bytesSlice b 0 64), fpCoordOf? (bytesSlice b 64 64),
        fpCoordOf? (bytesSlice b 128 64), fpCoordOf? (bytesSlice b 192 64) with
  | some a, some c, some d, some e => some ((a, c), (d, e))
  | _, _, _, _ => none

/-- Encode a padded G2 point (256 bytes). -/
def g2PointBytes (P : (Nat × Nat) × (Nat × Nat)) : Bytes :=
  [P.1.1, P.1.2, P.2.1, P.2.2].foldl
    (fun (acc : Bytes) (x : Nat) => bytesAppend acc (fpCoordBytes x)) Bytes.empty

/-- A G1 point the G1ADD precompile accepts: infinity, or on the curve. No
    subgroup check - EIP-2537 says so explicitly, and plan Section 13 lists it as
    a risk ("EIP-2537 G1ADD does not check subgroup membership").
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Note: There is no subgroup check for the G1 addition precompile") -/
def g1PointAddValid (P : Nat × Nat) : Bool := affineOnCurve fpOps P

/-- A G1 point G1MSM and PAIRING_CHECK accept: infinity, or on the curve AND in
    the r-torsion. This is the check the whole verifier leans on: the transcript
    helper runs no curve check at all (AssemblyHelpers.yul:80-84 says so and
    points the reader here) @formal-baseline.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 (G1 MSM error cases) -/
def g1PointMsmValid (P : Nat × Nat) : Bool :=
  affineOnCurve fpOps P && (affineIsInfinity fpOps P || g1InSubgroup P)

/-- A G2 point PAIRING_CHECK accepts.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Each point is expected to be in the subgroup of order q", plus the G2 error cases) -/
def g2PointValid (P : (Nat × Nat) × (Nat × Nat)) : Bool :=
  affineOnCurve fp2Ops P && (affineIsInfinity fp2Ops P || g2InSubgroup P)

/-! ### Call frames -/

/-- The G1ADD frame: the two padded points, concatenated.
    -- yul: PrecompileSmoke.sol:85-89 (four mstores then mcopy(add(scratch, 0x80),
    scratch, 0x80)) and FinalPairing.yul:42-44 (mcopy(batch_ptr + 0x80,
    PAIRING_RHS_MPTR, 0x80) then the 0x100-byte staticcall) @formal-baseline -/
def g1AddFrame (p q : Bytes) : Bytes := bytesAppend p q

/-- The G1MSM frame for k (point, scalar) pairs, interleaved point then scalar.
    -- yul: AccumulatorHelpers.yul:300-303 and :330-332 (mcopy(pair_ptr, point,
    0x80); mstore(add(pair_ptr, 0x80), scalar); pair_ptr += 0xa0) @formal-baseline -/
def g1MsmFrame (pairs : List (Bytes × Bytes)) : Bytes :=
  pairs.foldl (fun (acc : Bytes) (pr : Bytes × Bytes) =>
    bytesAppend acc (bytesAppend pr.1 pr.2)) Bytes.empty

/-- The PAIRING_CHECK frame for k (G1, G2) pairs, in the order the caller
    supplies them. The order is not this file's business and it is load-bearing:
    ec_pairing lays out [lhs_g1 | G2_BASE | rhs_g1 | NEG_S_G2_BASE]
    (AssemblyHelpers.yul:284-287) but FinalPairing.yul:88 calls it as
    ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR), so the precompile
    actually evaluates e(PAIRING_RHS, G2) * e(PAIRING_LHS, -sG2) = 1.
    docs/REVIEW.md R-11 is the port finding: the orientation flips at the call
    site, not in the layout, and finalPairing_spec must cite FinalPairing.yul:88.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("It checks the equation e(P1, Q1) * e(P2, Q2) * ... * e(Pk, Qk) == 1") @formal-baseline -/
def pairingFrame (pairs : List (Bytes × Bytes)) : Bytes :=
  pairs.foldl (fun (acc : Bytes) (pr : Bytes × Bytes) =>
    bytesAppend acc (bytesAppend pr.1 pr.2)) Bytes.empty

/-- The modexp frame: the three lengths as big-endian words, then the operands.
    -- yul: AssemblyHelpers.yul:27-32 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-198 -/
def modexpFrame (baseLen expLen modLen : Nat) (base exponent modulus : Bytes) : Bytes :=
  let header := bytesOfWords [baseLen, expLen, modLen]
  bytesAppend (bytesAppend (bytesAppend header base) exponent) modulus

/-- The frame the generated verifier emits for every scalar inversion and every
    batch inversion: basesize = expsize = modsize = 32, base = x, exponent =
    r - 2, modulus = r.
    -- yul: AssemblyHelpers.yul:27-32 (scalar_inv) and :181-186 (batch_invert
    single-element fast path) and :232-237 (batch_invert product path) @formal-baseline -/
def modexpInvFrame (x : Nat) : Bytes :=
  modexpFrame wordBytes wordBytes wordBytes
    (bytesNatBE x wordBytes) (bytesNatBE (blsR - 2) wordBytes)
    (bytesNatBE blsR wordBytes)

/-- The three modexp length words, read from the header with the EIP-198
    right-padding rule. -/
def modexpSizes (input : Bytes) : Nat × Nat × Nat :=
  (bytesToNatBE (bytesSlice input 0 wordBytes),
   bytesToNatBE (bytesSlice input wordBytes wordBytes),
   bytesToNatBE (bytesSlice input (2 * wordBytes) wordBytes))

/-- EIP-7823: any of the three lengths above 1024 bytes is rejected outright. -/
def modexpWithinLimits (input : Bytes) : Bool :=
  match modexpSizes input with
  | (bl, el, ml) => bl <= modexpMaxLen && el <= modexpMaxLen && ml <= modexpMaxLen

/-- A parsed modexp frame: the three lengths and the three operands, each
    right-padded to its declared length. -/
structure ModexpFrame where
  baseLen : Nat
  expLen : Nat
  modLen : Nat
  base : Bytes
  exponent : Bytes
  modulus : Bytes

/-- Parse a modexp frame, or none when EIP-7823 rejects it. The operands are only
    materialised for frames within the limits, so a hostile length word such as
    2^256 - 1 cannot make this allocate.
    -- eip: https://eips.ethereum.org/EIPS/eip-198 (padding) and https://eips.ethereum.org/EIPS/eip-7823 (limits) -/
def modexpParse? (input : Bytes) : Option ModexpFrame :=
  if modexpWithinLimits input then
    match modexpSizes input with
    | (bl, el, ml) =>
        some { baseLen := bl, expLen := el, modLen := ml,
               base := bytesSlicePad input modexpHeaderBytes bl,
               exponent := bytesSlicePad input (modexpHeaderBytes + bl) el,
               modulus := bytesSlicePad input (modexpHeaderBytes + bl + el) ml }
  else none

/-- The exponent value the iteration count is taken from: the integer value of
    the first min(expsize, 32) exponent bytes, i.e. the HIGH bytes when the
    exponent is longer than a word. See divergence 3.
    -- eip: https://eips.ethereum.org/EIPS/eip-198 ("If length_of_EXPONENT <= 32, then return the index of 
    -- the highest bit in EXPONENT ... If length_of_EXPONENT > 32, then ... plus the index of the highest 
    -- bit in the first 32 bytes of EXPONENT")
    -- revm: revm-precompile-16.2.0/src/modexp.rs, exp_highp = left_pad of right_padded_highp[..min(exp_len,32)] -/
def modexpExpHigh (input : Bytes) : Nat :=
  match modexpSizes input with
  | (bl, el, _) => bytesToNatBE (bytesSlice input (modexpHeaderBytes + bl) (min el wordBytes))

/-! ### Gas schedules -/

/-- EIP-2537 G1ADD flat cost: 375.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Gas schedule / G1 addition: 375 gas")
    -- yul: layout/mod.rs:171 (G1ADD_GAS = 375), rendered as G1ADD_GAS at Constants.sol:193 @formal-baseline -/
def g1AddGasScheduled : Nat := 375

/-- EIP-2537 G1 multiplication cost, the MSM base price: 12000.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("G1 multiplication: 12000 gas")
    -- yul: layout/mod.rs:173 (G1_MSM_MULTIPLICATION_COST = 12_000) @formal-baseline -/
def g1MultiplicationCost : Nat := 12000

/-- The MSM discount denominator.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("multiplier = 1000")
    -- yul: layout/mod.rs:175 (MSM_MULTIPLIER = 1_000) @formal-baseline -/
def msmMultiplier : Nat := 1000

/-- The EIP-2537 G1 MSM discount table, discount(k) for k = 1..=128, in parts per
    msmMultiplier. Checked entry by entry against the EIP table in the KATs.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("G1 discounts": the 128 pairs [1, 1000] ... [128, 519])
    -- yul: layout/mod.rs:179-188 (G1_MSM_DISCOUNT : [u64; 128]) @formal-baseline -/
def g1MsmDiscount : List Nat :=
  [1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677, 673, 669,
   665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627, 625, 623, 621, 619,
   617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598, 596, 595, 593, 592, 591, 589,
   588, 586, 585, 584, 582, 581, 580, 579, 577, 576, 575, 574, 573, 572, 570, 569, 568, 567,
   566, 565, 564, 563, 562, 561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 551, 550, 549,
   548, 547, 547, 546, 545, 544, 543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534,
   533, 532, 532, 531, 530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520,
   520, 519]

/-- max_discount, used for k > 128.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("max_discount = 519" for G1)
    -- yul: layout/mod.rs:178 documents the same cap @formal-baseline -/
def g1MsmMaxDiscount : Nat := 519

/-- EIP-2537 G1 MSM cost for k pairs: (k * 12000 * discount(k)) / 1000, with the
    table's last entry as the cap beyond k = 128.
    k = 0 returns 0. The Rust asserts pairs > 0 (layout/mod.rs:193) and the EIP
    rejects an empty variable-length input ("variable input length operations
    must return an error if the input is empty"), so 0 is a sentinel that no
    valid frame reaches; g1MsmValidInput rejects it first.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("The call cost is calculated as (k * multiplication_cost * discount) // multiplier")
    -- yul: layout/mod.rs:192-200 (g1msm_gas) @formal-baseline -/
def g1MsmGasPairs (k : Nat) : Nat :=
  k * g1MultiplicationCost * g1MsmDiscount.getD (k - 1) g1MsmMaxDiscount / msmMultiplier

/-- EIP-2537 pairing-check cost for k pairs: 32600 * k + 37700.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("The cost of the pairing check operation is 32600*k + 37700 where k is a number of pairs")
    -- yul: layout/mod.rs:203-205 (pairing_gas) @formal-baseline -/
def pairingGasPairs (k : Nat) : Nat := 32600 * k + 37700

/-- EIP-2565 multiplication complexity: words^2 with words = ceil(max(base,mod)/8).
    -- eip: https://eips.ethereum.org/EIPS/eip-2565 (calculate_multiplication_complexity) -/
def modexpMultComplexity2565 (baseLen modLen : Nat) : Nat :=
  let w := (max baseLen modLen + 7) / 8
  w * w

/-- EIP-7883 multiplication complexity: a floor of 16 for operands up to 32
    bytes, and 2 * words^2 above it.
    -- eip: https://eips.ethereum.org/EIPS/eip-7883 ("multiplication_complexity = 16; if max_length > 32: multiplication_complexity = 2 * words**2") -/
def modexpMultComplexity7883 (baseLen modLen : Nat) : Nat :=
  let m := max baseLen modLen
  if m > 32 then 2 * ((m + 7) / 8) * ((m + 7) / 8) else 16

/-- The iteration count, shared by both schedules except for the long-exponent
    multiplier: 8 under EIP-2565, 16 under EIP-7883. Both floor it at 1.
    -- eip: https://eips.ethereum.org/EIPS/eip-2565 and https://eips.ethereum.org/EIPS/eip-7883 (calculate_iteration_count) -/
def modexpIterationCount (expLen expHigh longMultiplier : Nat) : Nat :=
  let bitPart := if expHigh == 0 then 0 else Nat.log2 expHigh
  let extra := if expLen > 32 then longMultiplier * (expLen - 32) else 0
  max (extra + bitPart) 1

/-- The pre-EIP-7883 modexp price: max(200, multiplication_complexity *
    iteration_count / 3). EIP-2565 shipped in BERLIN, not Istanbul; the plan and
    the generator both call this the pre-7883 schedule (layout/mod.rs:213-216)
    @formal-baseline.
    -- eip: https://eips.ethereum.org/EIPS/eip-2565 (calculate_gas_cost) -/
def modexpGasEip2565 (input : Bytes) : Nat :=
  match modexpSizes input with
  | (bl, el, ml) =>
      max 200 (modexpMultComplexity2565 bl ml
        * modexpIterationCount el (modexpExpHigh input) 8 / 3)

/-- The EIP-7883 modexp price: max(500, multiplication_complexity *
    iteration_count), i.e. the / 3 divisor removed.
    -- eip: https://eips.ethereum.org/EIPS/eip-7883 (calculate_gas_cost) -/
def modexpGasEip7883 (input : Bytes) : Nat :=
  match modexpSizes input with
  | (bl, el, ml) =>
      max 500 (modexpMultComplexity7883 bl ml
        * modexpIterationCount el (modexpExpHigh input) 16)

/-- The price this relation charges: the maximum over the two live schedules,
    which is the generator's stated policy (layout/mod.rs:156-161: "the bound is
    the MAXIMUM over those schedules") @formal-baseline. EIP-7883 dominates
    EIP-2565 pointwise - the complexity floor 16 is at least words^2 for
    max_length <= 32, the long-exponent multiplier doubles, and the floor rises
    from 200 to 500 - so the maximum is always the EIP-7883 price. -/
def modexpGas (input : Bytes) : Nat :=
  max (modexpGasEip2565 input) (modexpGasEip7883 input)

/-- MODEXP_GAS as the generator renders it: 4080.
    -- yul: layout/mod.rs:237-267 (modexp_gas_word_frame), Constants.sol:196 @formal-baseline -/
def modexpGasScheduled : Nat := 4080

/-- G1MSM_GAS_1PAIR as the generator renders it: 12000.
    -- yul: Constants.sol:194, from layout/mod.rs:207 (g1msm_gas(1)) @formal-baseline -/
def g1MsmOnePairGasScheduled : Nat := 12000

/-- PAIRING_GAS_2PAIR as the generator renders it: 102900.
    -- yul: Constants.sol:195, from layout/mod.rs:208 (pairing_gas(2)) @formal-baseline -/
def pairingTwoPairGasScheduled : Nat := 102900

/-- G1MSM_GAS_SMOKE for the poseidon fixture dump: 47 pairs, input 0x1d60 bytes.
    -- yul: Constants.sol:198 (constructor_g1msm_smoke_gas), rendered as 337836
    with staticcall(G1MSM_GAS_SMOKE, 0x0c, msm_scratch, 0x1d60, ...) at
    PrecompileSmoke.sol:202 @formal-baseline -/
def g1MsmSmokeGasPoseidon : Nat := 337836

/-- G1MSM_GAS_SMOKE for the ivc fixture dump: 78 pairs, input 0x30c0 bytes.
    -- yul: proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol:271,521 @formal-baseline -/
def g1MsmSmokeGasIvc : Nat := 525096

/-! ### The call-request shape and the per-precompile relations -/

/-- The call-family instruction, mirroring YulSemantics.EVM.CallKind
    (vendor/yul-semantics/YulSemantics/Dialect/EVMExec.lean:408-410). Every
    generated precompile call is a staticcall: AssemblyHelpers.yul:33,187,238,294,
    FinalPairing.yul:39,44,53,58, AccumulatorHelpers.yul:246,357 and
    kzg/mod.rs:1873,1886,1898,1906 @formal-baseline. -/
inductive CallKind
  | call | callcode | delegatecall | staticcall
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Everything a callee can observe at the call boundary, shaped like
    YulSemantics.EVM.CallRequest (EVMExec.lean:416-426: kind, gas, target, value,
    input) with input as a Midfall.Bytes rather than a List UInt8. Bridge.lean
    owns the conversion into EVM.CallRequest and the ExternalCalls.mk assembly
    (docs/ecosystem.md finding Y-1). -/
structure CallRequest where
  /-- Which call-family instruction was used. -/
  kind : CallKind
  /-- The gas the caller forwarded. The generator forwards a fixed scheduled
      bound, never gas(): layout/mod.rs:144-154 and tests.rs:1482-1531. -/
  gas : Word256
  /-- The address invoked. -/
  target : Word256
  /-- Value: zero for every staticcall. -/
  value : Word256
  /-- The already-copied caller-memory input slice. -/
  input : Bytes

/-- The caller-visible result, shaped like EVM.CallResponse
    (EVMExec.lean:461-467) minus the world projection, which Bridge supplies: a
    precompile changes no world state, and EIP-2537 says a failing call burns
    everything forwarded ("if a call to one of the precompiles in this EIP
    results in an error then all the gas supplied along with a CALL or STATICCALL
    is burned") - the property the generator's exact-gas policy depends on
    (layout/mod.rs:144-149) @formal-baseline. -/
structure CallOutcome where
  success : Bool
  returndata : Bytes

/-- The decidable pieces of one precompile's relation, as a plain record so that
    Bridge.lean can fold the four of them into the single ternary relation
    EVM.ExternalCalls bundles (finding Y-1). -/
structure ExternalCallRelation where
  /-- The precompile address this relation answers for. -/
  address : Word256
  /-- Does the precompile accept this input at all? -/
  validInput : Bytes -> Bool
  /-- How many bytes does a successful call return? none = the call fails. -/
  outputLen : Bytes -> Option Nat
  /-- The scheduled gas cost of the call, as a function of the frame. -/
  gas : Bytes -> Nat
  /-- The return data of a successful call, when this file can compute it. -/
  output : Bytes -> Option Bytes

/-- A request addresses this precompile and carries an input it accepts. -/
def ExternalCallRelation.accepts (r : ExternalCallRelation) (req : CallRequest) : Bool :=
  req.target == r.address && r.validInput req.input

/-- The honest response to an accepted request: success with the computed return
    data, or - for PAIRING_CHECK, whose arithmetic is a parameter - success with
    the length the EIP fixes. A rejected request is a failed call that burns the
    forwarded gas. -/
def ExternalCallRelation.respond (r : ExternalCallRelation) (req : CallRequest) : Option CallOutcome :=
  if req.target != r.address || ! (r.validInput req.input) then none
  else match r.output req.input with
    | some out => some { success := true, returndata := out }
    | none => if let some n := r.outputLen req.input then
                some { success := true, returndata := bytesZero n }
              else none

/-! #### 0x0b G1ADD -/

/-- G1ADD validity: exactly 0x100 bytes, each of the two points canonically
    encoded and either infinity or on the curve. No subgroup check.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("ABI for G1 addition", error cases: invalid coordinate encoding; neither a point nor infinity; invalid length) -/
def g1AddValidInput (input : Bytes) : Bool :=
  input.size == g1AddInputBytes &&
  match g1Of? (bytesSlice input 0 g1Bytes), g1Of? (bytesSlice input g1Bytes g1Bytes) with
  | some p, some q => g1PointAddValid p && g1PointAddValid q
  | _, _ => false

/-- G1ADD returns one padded G1 point, 0x80 bytes.
    -- yul: the staticcall out-size at FinalPairing.yul:44,58 and kzg/mod.rs:1886,1906 is G1_BYTES = 0x80 @formal-baseline -/
def g1AddOutputLen (input : Bytes) : Option Nat :=
  if g1AddValidInput input then some g1Bytes else none

/-- The G1ADD result: the affine sum, re-encoded in padded form. -/
def g1AddOutput (input : Bytes) : Option Bytes :=
  match g1Of? (bytesSlice input 0 g1Bytes), g1Of? (bytesSlice input g1Bytes g1Bytes) with
  | some p, some q =>
      if g1AddValidInput input then some (g1PointBytes (affineAdd fpOps p q)) else none
  | _, _ => none

/-- G1ADD gas: the flat 375, independent of the input. -/
def g1AddGas (_ : Bytes) : Nat := g1AddGasScheduled

/-- The G1ADD relation. -/
def g1AddRelation : ExternalCallRelation where
  address := g1AddAddress
  validInput := g1AddValidInput
  outputLen := g1AddOutputLen
  gas := g1AddGas
  output := g1AddOutput

/-! #### 0x0c G1MSM -/

/-- The (point, scalar) pairs of a G1MSM frame, or none when the length is not a
    positive multiple of 0xa0 or some point is not canonically encoded.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("160*k (k being a positive integer) bytes"; "variable input length operations must return an error if the input is empty") -/
def g1MsmPairs? (input : Bytes) : Option (List ((Nat × Nat) × Nat)) :=
  if input.size == 0 || input.size % g1MsmPairBytes != 0 then none
  else go input 0 (input.size / g1MsmPairBytes) []
where
  go : Bytes -> Nat -> Nat -> List ((Nat × Nat) × Nat) -> Option (List ((Nat × Nat) × Nat))
    | _, _, 0, acc => some acc.reverse
    | bs, off, n+1, acc =>
        match bytesTake bs off g1Bytes, bytesTake bs (off + g1Bytes) frBytes with
        | some pb, some sb =>
            match g1Of? pb with
            | some P => go bs (off + g1MsmPairBytes) n ((P, bytesToNatBE sb) :: acc)
            | none => none
        | _, _ => none

/-- G1MSM validity: a positive whole number of 0xa0 pairs, each point infinity or
    on the curve AND in the r-torsion. Scalars are unconstrained: EIP-2537 says
    the scalar "is not required to be less than or equal to main subgroup order
    q", which is why the accumulator helper enforces canonicality itself
    (AccumulatorHelpers.yul:226,290,321) @formal-baseline. -/
def g1MsmValidInput (input : Bytes) : Bool :=
  match g1MsmPairs? input with
  | none => false
  | some ps => ps.all (fun pr => g1PointMsmValid pr.1)

/-- G1MSM returns one padded G1 point, 0x80 bytes.
    -- yul: the staticcall out-size at FinalPairing.yul:39,53, AccumulatorHelpers.yul:246 and kzg/mod.rs:1873,1898 is G1_BYTES @formal-baseline -/
def g1MsmOutputLen (input : Bytes) : Option Nat :=
  if g1MsmValidInput input then some g1Bytes else none

/-- The G1MSM result: the sum of scalar_i * point_i, in the order the pairs
    appear. Zero scalars and identity points contribute nothing, which is what
    makes the generator's all-identity worst-case smoke probe return the identity
    (PrecompileSmoke.sol:192-206) @formal-baseline. -/
def g1MsmOutput (input : Bytes) : Option Bytes :=
  match g1MsmPairs? input with
  | some ps =>
      if ps.all (fun pr => g1PointMsmValid pr.1) then
        some (g1PointBytes
          (ps.foldl (fun (acc : Nat × Nat) (pr : (Nat × Nat) × Nat) =>
            affineAdd fpOps acc (affineSmul fpOps pr.2 pr.1)) (0, 0)))
      else none
  | none => none

/-- G1MSM gas: the EIP-2537 MSM formula at k = input.size / 0xa0. -/
def g1MsmGas (input : Bytes) : Nat := g1MsmGasPairs (input.size / g1MsmPairBytes)

/-- The G1MSM relation. -/
def g1MsmRelation : ExternalCallRelation where
  address := g1MsmAddress
  validInput := g1MsmValidInput
  outputLen := g1MsmOutputLen
  gas := g1MsmGas
  output := g1MsmOutput

/-! #### 0x0f PAIRING_CHECK -/

/-- The (G1, G2) pairs of a PAIRING_CHECK frame, or none when the length is not a
    positive multiple of 0x180 or some point is not canonically encoded.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("384*k (k being a positive integer) bytes ... 128 bytes of G1 point encoding, 256 bytes of G2 point encoding") -/
def pairingPairs? (input : Bytes) :
    Option (List ((Nat × Nat) × ((Nat × Nat) × (Nat × Nat)))) :=
  if input.size == 0 || input.size % pairingPairBytes != 0 then none
  else go input 0 (input.size / pairingPairBytes) []
where
  go : Bytes -> Nat -> Nat
      -> List ((Nat × Nat) × ((Nat × Nat) × (Nat × Nat)))
      -> Option (List ((Nat × Nat) × ((Nat × Nat) × (Nat × Nat))))
    | _, _, 0, acc => some acc.reverse
    | bs, off, n+1, acc =>
        match bytesTake bs off g1Bytes, bytesTake bs (off + g1Bytes) g2Bytes with
        | some pb, some qb =>
            match g1Of? pb, g2Of? qb with
            | some P, some Q => go bs (off + pairingPairBytes) n ((P, Q) :: acc)
            | _, _ => none
        | _, _ => none

/-- PAIRING_CHECK validity: a positive whole number of 0x180 pairs, every point
    infinity-or-on-curve and in the r-torsion (both groups, per the EIP). -/
def pairingValidInput (input : Bytes) : Bool :=
  match pairingPairs? input with
  | none => false
  | some ps => ps.all (fun pr => g1PointMsmValid pr.1 && g2PointValid pr.2)

/-- PAIRING_CHECK returns exactly one 32-byte word.
    -- yul: the staticcall out-size at AssemblyHelpers.yul:294 is word_bytes = 0x20 @formal-baseline -/
def pairingOutputLen (input : Bytes) : Option Nat :=
  if pairingValidInput input then some wordBytes else none

/-- The one arithmetic fact this file does not compute: whether the product of the
    pairings of the frame's pairs is 1 in Fp12. Plan Section 1 lists EIP-2537 as
    an assumption for exactly this reason, and plan Section 7 validates it
    differentially on revm. Bridge.lean supplies it (from the revm replay, or
    from a real pairing once one exists in Lean - docs/ecosystem.md gap 2 says
    none does).
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("It checks the equation e(P1, Q1) * e(P2, Q2) * ... * e(Pk, Qk) == 1 in the pairing target field") -/
abbrev PairingProduct := Bytes -> Bool

/-- The PAIRING_CHECK output word: 31 zero bytes then 0x01 or 0x00. Note the
    generator compares the whole word against 1 rather than masking the low bit
    (AssemblyHelpers.yul:297-301) @formal-baseline, which is exactly the shape
    this pins.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Output is 32 bytes where first 31 bytes are equal to 0x00 and the last byte is either 0x00 (false) or 0x01 (true)") -/
def pairingOutputWord (b : Bool) : Bytes := bytesNatBE (if b then 1 else 0) wordBytes

/-- The PAIRING_CHECK result, relative to the pairing-product oracle. -/
def pairingOutput (product : PairingProduct) (input : Bytes) : Option Bytes :=
  if pairingValidInput input then some (pairingOutputWord (product input)) else none

/-- PAIRING_CHECK gas: 32600 * k + 37700 at k = input.size / 0x180. -/
def pairingGasOfInput (input : Bytes) : Nat := pairingGasPairs (input.size / pairingPairBytes)

/-- The PAIRING_CHECK relation, parameterised by the unmodelled arithmetic. -/
def pairingRelation (product : PairingProduct) : ExternalCallRelation where
  address := pairingAddress
  validInput := pairingValidInput
  outputLen := pairingOutputLen
  gas := pairingGasOfInput
  output := pairingOutput product

/-! #### 0x05 modexp -/

/-- Modexp validity: the EIP-7823 size limits and nothing else. Any byte string
    parses, because EIP-198 right-pads the calldata infinitely and ignores
    excess data. -/
def modexpValidInput (input : Bytes) : Bool := modexpWithinLimits input

/-- Modexp output length: exactly modsize bytes.
    -- eip: https://eips.ethereum.org/EIPS/eip-198 ("returns an output (BASE**EXPONENT) % MODULUS as a byte array with the same length as the modulus")
    -- revm: revm-precompile-16.2.0/src/modexp.rs ends with left_pad_vec(&output, mod_len), and its 
    -- eth_tests_modexp_modsize0_returndatasizeFiller vector has modsize 100 and a 100-byte expected output. 
    -- So the output is modsize bytes, NOT rounded up to a multiple of 32; a modsize of 0 returns 0 bytes. 
    -- The generated frames all use modsize 32, where the two readings coincide, so this does not affect the 
    -- verifier. -/
def modexpOutputLen (input : Bytes) : Option Nat :=
  match modexpSizes input with
  | (_, _, ml) => if ml <= modexpMaxLen then some ml else none

/-- The modexp result: base^exp mod modulus, left-padded to modsize bytes. -/
def modexpOutput (input : Bytes) : Option Bytes :=
  match modexpParse? input with
  | none => none
  | some f =>
      -- A zero modulus is the one input the clients special-case: revm's
      -- modexp returns 0, and Lean's Nat.mod by 0 would not reduce at all.
      if bytesToNatBE f.modulus == 0 then some (bytesZero f.modLen)
      else some (bytesNatBE
        (modPow (bytesToNatBE f.base) (bytesToNatBE f.exponent) (bytesToNatBE f.modulus))
        f.modLen)

/-- The modexp relation. -/
def modexpRelation : ExternalCallRelation where
  address := modexpAddress
  validInput := modexpValidInput
  outputLen := modexpOutputLen
  gas := modexpGas
  output := modexpOutput

/-- The four precompiles the generated verifier calls. Bridge.lean folds these
    into one EVM.ExternalCalls (finding Y-1); the quotient-evaluator call of plan
    Section 7 is not a precompile and belongs with the shell model. -/
def honestRelations (product : PairingProduct) : List ExternalCallRelation :=
  [g1AddRelation, g1MsmRelation, pairingRelation product, modexpRelation]

/-! ### Known-answer vectors

Hand-computed, in the style of Midfall/Halo2/Exec/Arith.lean: every expected
value below is read off the Rust generator's own rendered output or the EIP
text, never off this file's implementation. -/

section Kats

/-- The BLS12-381 G1 generator H1 in EIP-2537 padded form, as four 32-byte words.
    -- yul: render/models.rs:199 (g1_generator = g1_words(G1Affine::generator())), rendered at PrecompileSmoke.sol:85-88 and :157-160 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("Generators: H1: X = 
    -- 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb, Y 
    -- = 
    -- 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1") 
    -- -/
def katG1GenWords : List Nat :=
  [0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f,
   0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4,
   0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1]

/-- Twice the G1 generator, as the generator renders it.
    -- yul: render/models.rs:200-203 (g1_double_generator = g1_words((g + g).to_affine())), rendered at PrecompileSmoke.sol:94-99 and :128-133 @formal-baseline -/
def katG1DoubleWords : List Nat :=
  [0x000000000000000000000000000000000572cbea904d67468808c8eb50a9450c,
   0x9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e,
   0x00000000000000000000000000000000166a9d8cabc673a322fda673779d8e38,
   0x22ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28]

/-- The negation of the G1 generator: same x, y replaced by p - y.
    -- yul: the second G1 of the constructor's pairing probe (c), PrecompileSmoke.sol:169-172 @formal-baseline -/
def katG1NegWords : List Nat :=
  [0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f,
   0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f2,
   0x67816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca]

/-- The BLS12-381 G2 generator H2 in EIP-2537 padded form, as eight 32-byte words
    (x_c0, x_c1, y_c0, y_c1).
    -- yul: PrecompileSmoke.sol:161-168 @formal-baseline
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("H2: X c0 = 0x024aa2b2..., X c1 = 0x13e02b60..., Y c0 = 0x0ce5d527..., Y c1 = 0x0606c4a0...") -/
def katG2GenWords : List Nat :=
  [0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051,
   0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
   0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65,
   0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e,
   0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a,
   0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
   0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99,
   0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be]

/-- The G1 point (4, y) that satisfies Y^2 = X^3 + 4 over Fp but is NOT in the
    r-torsion: the generator's negative probe for the G1MSM subgroup check.
    -- yul: PrecompileSmoke.sol:137-151 @formal-baseline ("(4, y) satisfies y^2 = x^3 + 4 over Fp but is NOT 
    -- in the r-order subgroup (checked off-chain: r*P != O). EIP-2537 requires G1MSM to reject it.") -/
def katOffSubgroupWords : List Nat :=
  [0x0000000000000000000000000000000000000000000000000000000000000000,
   0x0000000000000000000000000000000000000000000000000000000000000004,
   0x000000000000000000000000000000000a989badd40d6212b33cffc3f3763e9b,
   0xc760f988c9926b26da9dd85e928483446346b8ed00e1de5d5ea93e354abe706c]

/-- The G1 MSM discount table exactly as the EIP prints it, as (k, discount)
    pairs, so the alignment of g1MsmDiscount is checked and not assumed.
    -- eip: https://eips.ethereum.org/EIPS/eip-2537 ("G1 discounts") -/
def katEipG1Discounts : List (Nat × Nat) :=
  [(1,1000),(2,949),(3,848),(4,797),(5,764),(6,750),(7,738),(8,728),(9,719),(10,712),
   (11,705),(12,698),(13,692),(14,687),(15,682),(16,677),(17,673),(18,669),(19,665),(20,661),
   (21,658),(22,654),(23,651),(24,648),(25,645),(26,642),(27,640),(28,637),(29,635),(30,632),
   (31,630),(32,627),(33,625),(34,623),(35,621),(36,619),(37,617),(38,615),(39,613),(40,611),
   (41,609),(42,608),(43,606),(44,604),(45,603),(46,601),(47,599),(48,598),(49,596),(50,595),
   (51,593),(52,592),(53,591),(54,589),(55,588),(56,586),(57,585),(58,584),(59,582),(60,581),
   (61,580),(62,579),(63,577),(64,576),(65,575),(66,574),(67,573),(68,572),(69,570),(70,569),
   (71,568),(72,567),(73,566),(74,565),(75,564),(76,563),(77,562),(78,561),(79,560),(80,559),
   (81,558),(82,557),(83,556),(84,555),(85,554),(86,553),(87,552),(88,551),(89,550),(90,549),
   (91,548),(92,547),(93,547),(94,546),(95,545),(96,544),(97,543),(98,542),(99,541),(100,540),
   (101,540),(102,539),(103,538),(104,537),(105,536),(106,536),(107,535),(108,534),(109,533),(110,532),
   (111,532),(112,531),(113,530),(114,529),(115,528),(116,528),(117,527),(118,526),(119,525),(120,525),
   (121,524),(122,523),(123,522),(124,522),(125,521),(126,520),(127,520),(128,519)]

/-- Every frame width the generator emits, and the two byte helpers. -/
def layoutKats_ok : Bool :=
  g1Bytes == 0x80 && g2Bytes == 0x100 && frBytes == 0x20 && fpBytes == 48 &&
    fpPadBytes == 16 && fpPadBytes + fpBytes == 64 &&
    g1AddInputBytes == 0x100 && g1MsmPairBytes == 0xa0 && pairingPairBytes == 0x180 &&
    pairingTwoPairBytes == 0x300 && modexpHeaderBytes == 0x60 && modexpFrameBytes == 0xc0 &&
    modexpBaseOffset == 0x60 && modexpExpOffset == 0x80 && modexpModOffset == 0xa0 &&
    wordBytes == 32 && modexpMaxLen == 1024 &&
    bytesToNatBE (bytesNatBE 0x01020304 4) == 0x01020304 &&
    bytesEq (bytesNatBE 0x01020304 4) (ByteArray.mk #[1, 2, 3, 4]) &&
    bytesToNatBE (bytesNatBE (blsR - 2) 32) == blsR - 2 &&
    bytesEq (bytesZero 16) eipPad && (bytesZero 0).size == 0 &&
    (bytesSlice (bytesNatBE 1 1) 0 32).size == 1 &&
    (bytesSlicePad (bytesOfWords [1]) 0 32).size == 32 &&
    bytesToNatBE (bytesSlicePad (bytesOfWords [1]) 0 32) == 1

/-- The padded coordinate codec: canonicity is a strict bound, and it subsumes
    the "top 16 bytes are zero" rule the generator checks separately. -/
def coordKats_ok : Bool :=
  (g1Of? (bytesOfWords katG1GenWords)).isSome &&
    (g2Of? (bytesOfWords katG2GenWords)).isSome &&
    (fpCoordOf? (bytesNatBE (blsP - 1) 64)).isSome &&
    (fpCoordOf? (bytesNatBE blsP 64)).isNone &&
    (fpCoordOf? (bytesNatBE (2^500) 64)).isNone &&
    (fpCoordOf? (bytesZero 64)).isSome && (fpCoordOf? (bytesZero 63)).isNone &&
    (g1Of? (bytesZero 127)).isNone &&
    bytesEq (g1PointBytes (0, 0)) (bytesZero g1Bytes) &&
    bytesEq (g2PointBytes ((0, 0), (0, 0))) (bytesZero g2Bytes) &&
    (match g1Of? (bytesOfWords katG1GenWords) with
     | some q => q.1 == 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
     | none => false)

/-- G1ADD (0x0b): the frame the generator builds, byte for byte; the real double
    G + G = 2G; the identity law on either side; and the fact that G1ADD performs
    NO subgroup check, so the off-subgroup probe is a valid G1ADD input. -/
def g1AddKats_ok : Bool :=
  let frame := g1AddFrame (bytesOfWords katG1GenWords) (bytesOfWords katG1GenWords)
  bytesEq frame (bytesOfWords (katG1GenWords ++ katG1GenWords)) &&
    frame.size == g1AddInputBytes &&
    g1AddValidInput frame &&
    g1AddOutputLen frame == some g1Bytes &&
    g1AddGas frame == 375 &&
    (match g1AddOutput frame with | some o => bytesEq o (bytesOfWords katG1DoubleWords) | none => false) &&
    (let idf := g1AddFrame (bytesZero g1Bytes) (bytesZero g1Bytes)
     g1AddValidInput idf &&
       (match g1AddOutput idf with | some o => bytesEq o (bytesZero g1Bytes) | none => false)) &&
    (let f2 := g1AddFrame (bytesZero g1Bytes) (bytesOfWords katG1GenWords)
     g1AddValidInput f2 &&
       (match g1AddOutput f2 with | some o => bytesEq o (bytesOfWords katG1GenWords) | none => false)) &&
    (let f3 := g1AddFrame (bytesOfWords katG1GenWords) (bytesOfWords katG1NegWords)
     g1AddValidInput f3 &&
       (match g1AddOutput f3 with | some o => bytesEq o (bytesZero g1Bytes) | none => false)) &&
    g1AddValidInput (g1AddFrame (bytesOfWords katOffSubgroupWords) (bytesOfWords katOffSubgroupWords)) &&
    (let bad := bytesAppend (bytesNatBE blsP 64) (bytesZero (g1Bytes - 64))
     !g1AddValidInput (g1AddFrame bad bad)) &&
    !g1AddValidInput (bytesZero g1Bytes) &&
    !g1AddValidInput (bytesZero (g1AddInputBytes + 1))

/-- G1MSM (0x0c): the interleaved pair layout, the [2]G known answer, the
    all-identity worst-case probes at the two rendered sizes, the empty-frame
    rejection, and that a scalar above r is legal and acts as its residue. -/
def g1MsmKats_ok : Bool :=
  let g := bytesOfWords katG1GenWords
  let f := g1MsmFrame [(g, bytesNatBE 2 frBytes)]
  bytesEq f (bytesOfWords (katG1GenWords ++ [2])) &&
    f.size == g1MsmPairBytes &&
    g1MsmValidInput f && g1MsmOutputLen f == some g1Bytes && g1MsmGas f == 12000 &&
    (match g1MsmOutput f with | some o => bytesEq o (bytesOfWords katG1DoubleWords) | none => false) &&
    (let big := g1MsmFrame (List.replicate 47 ((bytesZero g1Bytes), (bytesZero frBytes)))
     big.size == 0x1d60 && g1MsmValidInput big && g1MsmGas big == 337836 &&
       (match g1MsmOutput big with | some o => bytesEq o (bytesZero g1Bytes) | none => false)) &&
    (let big := g1MsmFrame (List.replicate 78 ((bytesZero g1Bytes), (bytesZero frBytes)))
     big.size == 0x30c0 && g1MsmGas big == 525096) &&
    !g1MsmValidInput Bytes.empty && !g1MsmValidInput (bytesZero 1) &&
    !g1MsmValidInput (bytesZero (g1MsmPairBytes + 1)) &&
    !g1MsmValidInput (g1MsmFrame [(bytesOfWords katOffSubgroupWords, bytesNatBE 1 frBytes)]) &&
    (let f2 := g1MsmFrame [(g, bytesNatBE (blsR + 1) frBytes)]
     g1MsmValidInput f2 &&
       (match g1MsmOutput f2 with | some o => bytesEq o g | none => false)) &&
    (let f3 := g1MsmFrame [(g, bytesNatBE 0 frBytes)]
     g1MsmValidInput f3 &&
       (match g1MsmOutput f3 with | some o => bytesEq o (bytesZero g1Bytes) | none => false))

/-- PAIRING_CHECK (0x0f): the two-pair frame the constructor builds, byte for
    byte; its length, validity, output shape and gas; the negation; and the
    all-identity frame. -/
def pairingKats_ok : Bool :=
  let g := bytesOfWords katG1GenWords
  let ng := bytesOfWords katG1NegWords
  let g2 := bytesOfWords katG2GenWords
  let frameC := pairingFrame [(g, g2), (ng, g2)]
  bytesEq frameC (bytesOfWords (katG1GenWords ++ katG2GenWords ++ katG1NegWords ++ katG2GenWords)) &&
    frameC.size == pairingTwoPairBytes &&
    pairingValidInput frameC &&
    pairingOutputLen frameC == some wordBytes &&
    pairingGasOfInput frameC == 102900 &&
    (let frameD := pairingFrame [(g, g2), (g, g2)]
     bytesEq frameD (bytesOfWords (katG1GenWords ++ katG2GenWords ++ katG1GenWords ++ katG2GenWords)) &&
       pairingValidInput frameD) &&
    (match g1Of? g, g1Of? ng with
     | some q, some nq => nq.1 == q.1 && nq.2 == (blsP - q.2) % blsP && affineNeg fpOps q == nq
     | _, _ => false) &&
    (let idf := pairingFrame [((bytesZero g1Bytes), (bytesZero g2Bytes)), ((bytesZero g1Bytes), (bytesZero g2Bytes))]
     idf.size == 0x300 && pairingValidInput idf) &&
    bytesEq (pairingOutputWord true) (bytesNatBE 1 32) &&
    bytesEq (pairingOutputWord false) (bytesZero 32) &&
    (match pairingOutput (fun _ => true) frameC with | some o => bytesEq o (bytesNatBE 1 32) | none => false) &&
    (match pairingOutput (fun _ => false) frameC with | some o => bytesEq o (bytesZero 32) | none => false) &&
    (let one := pairingFrame [(g, g2)]
     one.size == 0x180 && pairingGasOfInput one == 70300) &&
    !pairingValidInput Bytes.empty && !pairingValidInput (bytesZero 0x100)

/-- Modexp (0x05): the frame the generator emits and the Fermat inverse it
    computes, the EIP-198 worked example, the EIP-198 right-padding examples,
    and the EIP-7823 size limits. -/
def modexpKats_ok : Bool :=
  let f := modexpInvFrame 7
  bytesEq f (bytesOfWords [32, 32, 32, 7, blsR - 2, blsR]) &&
    f.size == modexpFrameBytes &&
    modexpValidInput f && modexpOutputLen f == some 32 &&
    (match modexpOutput f with | some o => (bytesToNatBE o * 7) % blsR == 1 | none => false) &&
    (match modexpOutput (modexpInvFrame 2) with
     | some o => bytesToNatBE o == 0x39f6d3a994cebea4199cec0404d0ec02a9ded2017fff2dff7fffffff80000001
                   && (bytesToNatBE o * 2) % blsR == 1
     | none => false) &&
    (let e := modexpFrame 1 32 32 (bytesNatBE 3 1)
                 (bytesNatBE (2^256 - 2^32 - 978) 32) (bytesNatBE (2^256 - 2^32 - 977) 32)
     e.size == 0x60 + 65 && modexpValidInput e && modexpOutputLen e == some 32 &&
       (match modexpOutput e with | some o => bytesToNatBE o == 1 | none => false) &&
       modexpGasEip2565 e == 1360 && modexpGasEip7883 e == 4080 && modexpGas e == 4080) &&
    (let t := modexpFrame 1 1 1 (bytesNatBE 3 1) (bytesNatBE 5 1) (bytesNatBE 244 1)
     modexpValidInput t && modexpOutputLen t == some 1 &&
       (match modexpOutput t with | some o => bytesEq o (bytesNatBE 243 1) | none => false) &&
       modexpGas t == 500) &&
    (let pad := bytesAppend (bytesOfWords [1, 2, 32]) (bytesNatBE 0x03ffff80 4)
     match modexpParse? pad with
     | some fr => fr.baseLen == 1 && fr.expLen == 2 && fr.modLen == 32 &&
         bytesToNatBE fr.base == 3 && bytesToNatBE fr.exponent == 0xffff &&
         bytesToNatBE fr.modulus == 2^255 && fr.modulus.size == 32
     | none => false) &&
    modexpValidInput (modexpFrame 0 0 1024 Bytes.empty Bytes.empty (bytesZero 1024)) &&
    !modexpValidInput (modexpFrame 0 0 1025 Bytes.empty Bytes.empty (bytesZero 1025)) &&
    !modexpValidInput (bytesOfWords [0, 32, 2^256 - 1]) &&
    modexpOutputLen (bytesOfWords [0, 32, 2^256 - 1]) == none &&
    (match modexpParse? Bytes.empty with
     | some fr => fr.modLen == 0 &&
         (match modexpOutput Bytes.empty with | some o => o.size == 0 | none => false)
     | none => false)

/-- The gas constants the generator schedules, and the EIP formulas behind them. -/
def gasScheduleKats_ok : Bool :=
  g1AddGasScheduled == 375 && g1MsmOnePairGasScheduled == 12000 &&
    pairingTwoPairGasScheduled == 102900 && modexpGasScheduled == 4080 &&
    g1MsmDiscount.length == 128 && g1MsmMaxDiscount == 519 &&
    katEipG1Discounts.length == 128 &&
    (List.range 128).all (fun i =>
      (katEipG1Discounts.getD i (0, 0)).1 == i + 1 &&
        (katEipG1Discounts.getD i (0, 0)).2 == g1MsmDiscount.getD i 0) &&
    g1MsmGasPairs 1 == 12000 && g1MsmGasPairs 2 == 22776 && g1MsmGasPairs 128 == 797184 &&
    g1MsmGasPairs 200 == 200 * 12000 * 519 / 1000 && g1MsmGasPairs 0 == 0 &&
    g1MsmSmokeGasPoseidon == g1MsmGasPairs (0x1d60 / g1MsmPairBytes) &&
    g1MsmSmokeGasIvc == g1MsmGasPairs (0x30c0 / g1MsmPairBytes) &&
    g1MsmGas (bytesZero 0x1d60) == g1MsmSmokeGasPoseidon &&
    g1MsmGas (bytesZero 0x30c0) == g1MsmSmokeGasIvc &&
    pairingGasPairs 2 == pairingTwoPairGasScheduled && pairingGasPairs 1 == 70300 &&
    g1AddGas (g1AddFrame (bytesOfWords katG1GenWords) (bytesOfWords katG1GenWords)) == g1AddGasScheduled

/-- Divergence 2: the scheduled modexp constant is a bound over every 32-byte
    exponent, not the price of the exponent the generator emits. -/
def modexpGasKats_ok : Bool :=
  let f := modexpInvFrame 2
  modexpExpHigh f == blsR - 2 &&
    modexpIterationCount 32 (blsR - 2) 16 == 254 &&
    modexpGasEip7883 f == 4064 && modexpGasEip2565 f == 1354 && modexpGas f == 4064 &&
    modexpGasScheduled == 4080 && modexpGas f < modexpGasScheduled &&
    modexpIterationCount 32 (2^255) 16 == 255 && 16 * 255 == 4080 &&
    modexpMultComplexity7883 32 32 == 16 && modexpMultComplexity2565 32 32 == 16 &&
    modexpMultComplexity7883 64 64 == 128 && modexpMultComplexity2565 64 64 == 64 &&
    modexpIterationCount 32 0 16 == 1 &&
    modexpGasEip7883 (bytesOfWords [64, 32, 64]) == 500 &&
    modexpGasEip2565 (bytesOfWords [64, 32, 64]) == 200

/-- The subgroup facts the verifier's deferred validation depends on: every
    absorbed proof point reaches G1MSM or the pairing, and those two - not the
    transcript helper - are what reject an on-curve point outside the r-torsion. -/
def subgroupKats_ok : Bool :=
  match g1Of? (bytesOfWords katG1GenWords), g1Of? (bytesOfWords katG1DoubleWords),
        g1Of? (bytesOfWords katOffSubgroupWords), g2Of? (bytesOfWords katG2GenWords) with
  | some g, some d, some q, some h =>
      affineOnCurve fpOps g && affineOnCurve fpOps d && affineOnCurve fpOps q &&
        g1InSubgroup g && g1InSubgroup d && !g1InSubgroup q &&
        g1PointAddValid q && !g1PointMsmValid q &&
        q.1 == 4 &&
        affineOnCurve fp2Ops h && g2InSubgroup h &&
        affineSmul fpOps blsR g == (0, 0)
  | _, _, _, _ => false

/-- The bundled records, the request shape, and the honest response. -/
def relationKats_ok : Bool :=
  let req (a : Word256) (i : Bytes) : CallRequest :=
    { kind := CallKind.staticcall, gas := BitVec.ofNat 256 375, target := a, value := 0, input := i }
  let g := bytesOfWords katG1GenWords
  let frame := g1AddFrame g g
  ((honestRelations (fun _ => true)).map (fun r => r.address) == [0x0b, 0x0c, 0x0f, 0x05]) &&
    g1AddRelation.accepts (req g1AddAddress frame) &&
    !g1AddRelation.accepts (req g1MsmAddress frame) &&
    (match g1AddRelation.respond (req g1AddAddress frame) with
     | some o => o.success && bytesEq o.returndata (bytesOfWords katG1DoubleWords)
     | none => false) &&
    (match g1AddRelation.respond (req g1AddAddress (bytesZero 0x80)) with
     | none => true | some _ => false) &&
    (match (pairingRelation (fun _ => true)).respond
             (req pairingAddress (pairingFrame [(g, bytesOfWords katG2GenWords), (bytesOfWords katG1NegWords, bytesOfWords katG2GenWords)])) with
     | some o => bytesEq o.returndata (bytesNatBE 1 32)
     | none => false) &&
    (match modexpRelation.respond (req modexpAddress (modexpInvFrame 2)) with
     | some o => o.returndata.size == 32
     | none => false)

end Kats

#eval layoutKats_ok   -- expect true
#eval coordKats_ok   -- expect true
#eval g1AddKats_ok   -- expect true
#eval g1MsmKats_ok   -- expect true
#eval pairingKats_ok   -- expect true
#eval modexpKats_ok   -- expect true
#eval gasScheduleKats_ok   -- expect true
#eval modexpGasKats_ok   -- expect true
#eval subgroupKats_ok   -- expect true
#eval relationKats_ok   -- expect true
