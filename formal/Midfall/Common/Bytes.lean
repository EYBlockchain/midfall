-- |
-- Midfall.Common.Bytes
--
-- Byte-level vocabulary shared by the execution layer, the transcript and the
-- EIP-2537 / EIP-198 external-call relations. Everything here is executable:
-- the port rules (plan Section 4, R10) forbid `partial` in Exec/Common code.
--
-- Endianness is the whole content of this file, so every encoder is pinned
-- against its decoder by a round-trip check at the bottom, and those checks are
-- wired into scripts/checks.sh. That is not ceremony: an earlier revision of
-- this file had `wordToBytesBE` and `natToBytesBE` sharing the little-endian
-- accumulator, so the BE pair silently emitted LE, and no check noticed because
-- each only ever appeared on one side of a comparison with itself. See
-- docs/REVIEW.md R-20.

import Mathlib.Data.BitVec

namespace Midfall

/-- An EVM 32-byte word. -/
abbrev Word256 := BitVec 256

/-- A Keccak-256 digest. -/
abbrev H256 := BitVec 256

/-- The byte type the Rust side uses everywhere (Vec<u8>). -/
abbrev Bytes := ByteArray

/-- The empty byte array, spelled so that Lean does not default to `Array`. -/
def Bytes.empty : Bytes := ByteArray.mk #[]

/-- Big-endian bytes to a word, like Rust `U256::from_be_slice`. -/
def bytesToWordBE (bs : Bytes) : Word256 :=
  BitVec.ofNat 256 (bs.data.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0)

/-- Little-endian bytes to a word, like the halo2 `PrimeField::from_repr`. -/
def bytesToWordLE (bs : Bytes) : Word256 :=
  BitVec.ofNat 256 (bs.data.toList.reverse.foldl
    (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0)

/-- The one byte-emitting accumulator in this file: `len` bytes of `n`,
    LEAST significant first. Both public encoders are derived from it, one
    directly and one reversed, which is what prevents the two from drifting
    apart again. -/
def natToBytesLowFirst (n : Nat) (len : Nat) : Bytes :=
  go n len Bytes.empty
where
  go : Nat → Nat → Bytes → Bytes
    | _, 0, acc => acc
    | n, k+1, acc => go (n / 256) k (ByteArray.push acc (Nat.toUInt8 (n % 256)))

/-- `len` little-endian bytes of `n`: the halo2 `PrimeField::to_repr` /
    `GroupEncoding::to_bytes` order. -/
def natToBytesLE (n : Nat) (len : Nat) : Bytes := natToBytesLowFirst n len

/-- `len` big-endian bytes of `n`, most significant byte first; the inverse of
    `bytesToNatBE`. High bytes are dropped if `n` does not fit, which is what a
    fixed-width Rust `to_bytes` does. -/
def natToBytesBE (n : Nat) (len : Nat) : Bytes :=
  ByteArray.mk (natToBytesLowFirst n len).data.toList.reverse.toArray

/-- 32 big-endian bytes, most significant first - the inverse of
    `bytesToWordBE`. -/
def wordToBytesBE (w : Word256) : Bytes := natToBytesBE w.toNat 32

/-- 32 little-endian bytes, like Rust `PrimeField::to_repr`. -/
def wordToBytesLE (w : Word256) : Bytes := natToBytesLE w.toNat 32

/-- The 16 zero bytes that pad an EIP-2537 coordinate's high word. -/
def eipPad : Bytes := go 16 Bytes.empty
where
  go : Nat → Bytes → Bytes
    | 0, acc => acc
    | n+1, acc => go n (ByteArray.push acc 0)

/-- Read exactly `n` bytes at offset `i`, or `none` if the buffer is
    shorter. This is Rust's `Read::read_exact` on a `Cursor`: a short read is
    `ErrorKind::UnexpectedEof`, and every caller in the transcript turns that
    into `Error::Transcript`. -/
def bytesTake (bs : Bytes) (i n : Nat) : Option Bytes :=
  if i + n <= bs.size then
    some (ByteArray.mk (bs.data.extract i (i + n)))
  else none

/-- The number of bytes still unread after offset `i`. -/
def bytesRemaining (bs : Bytes) (i : Nat) : Nat :=
  if i >= bs.size then 0 else bs.size - i

/-- Big-endian bytes to a natural, without the 256-bit truncation of
    `bytesToWordBE`. Used where the value must then be compared against a
    modulus: a field repr is canonical only below it. -/
def bytesToNatBE (bs : Bytes) : Nat :=
  bs.data.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0

/-- Little-endian bytes to a natural: the halo2 `PrimeField::from_repr` /
    `GroupEncoding::to_bytes` order. -/
def bytesToNatLE (bs : Bytes) : Nat :=
  bytesToNatBE (ByteArray.mk bs.data.toList.reverse.toArray)

-- ## Round-trip checks
--
-- Every encoder paired with its own decoder, plus the cross-checks the
-- transcript and the codecs actually depend on. These are evaluated by
-- scripts/checks.sh, so an endianness regression fails the build instead of
-- surfacing as a wrong challenge in Phase 3.

def bytesRoundTrip_ok : Bool :=
  -- BE: value -> bytes -> value, and the bytes really are most-significant
  -- first (0x01020304 over 4 bytes is [1,2,3,4], not [4,3,2,1]).
  (bytesToNatBE (natToBytesBE 0x01020304 4) == 0x01020304) &&
  ((natToBytesBE 0x01020304 4).data.toList.map (fun x => x.toNat)) == [1, 2, 3, 4] &&
  (bytesToNatLE (natToBytesLE 0x01020304 4) == 0x01020304) &&
  ((natToBytesLE 0x01020304 4).data.toList.map (fun x => x.toNat)) == [4, 3, 2, 1] &&
  -- the two encoders agree on the value and differ only in order
  (bytesToNatLE (natToBytesLE 258 32) == 258) &&
  (bytesToNatBE (natToBytesBE 258 32) == 258) &&
  -- words round-trip through both orders
  (bytesToWordBE (wordToBytesBE 1) == (1 : Word256)) &&
  (bytesToWordLE (wordToBytesLE 1) == (1 : Word256)) &&
  (bytesToWordBE (wordToBytesBE 0xdeadbeef) == (0xdeadbeef : Word256)) &&
  -- wordToBytesBE and natToBytesBE agree, and wordToBytesBE is NOT wordToBytesLE
  ((wordToBytesBE 1).data[31]?.map (fun x => x.toNat)) == some 1 &&
  ((wordToBytesLE 1).data[0]?.map (fun x => x.toNat)) == some 1 &&
  wordToBytesBE 1 != wordToBytesLE 1 &&
  -- truncation matches a fixed-width Rust to_bytes: 0x1_00 dropped into 1 byte
  (natToBytesBE 0x100 1).size == 1 &&
  -- bytesTake bounds
  (bytesTake (natToBytesBE 0x01020304 4) 1 2).map (fun b => bytesToNatBE b) == some 0x0203 &&
  bytesTake (natToBytesBE 0x01020304 4) 3 2 == none

#eval bytesRoundTrip_ok   -- expect true, and scripts/checks.sh asserts it

end Midfall
