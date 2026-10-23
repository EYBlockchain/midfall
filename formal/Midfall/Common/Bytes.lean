-- |
-- Midfall.Common.Bytes
--
-- Byte-level vocabulary shared by the execution layer, the transcript and the
-- EIP-2537 / EIP-198 external-call relations. Everything here is executable:
-- the port rules (plan Section 4, R10) forbid `partial` in Exec/Common code.

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


/-- 32 big-endian bytes, most significant first. -/
def wordToBytesBE (w : Word256) : Bytes := goBE w.toNat 32 Bytes.empty
where
  goBE : Nat -> Nat -> Bytes -> Bytes
    | _, 0, acc => acc
    | n, k+1, acc => goBE (n / 256) k (ByteArray.push acc (Nat.toUInt8 (n % 256)))

/-- 32 little-endian bytes, like Rust `PrimeField::to_repr`. -/
def wordToBytesLE (w : Word256) : Bytes := goLE w.toNat 32 Bytes.empty
where
  goLE : Nat -> Nat -> Bytes -> Bytes
    | _, 0, acc => acc
    | n, k+1, acc => goLE (n / 256) k (ByteArray.push acc (Nat.toUInt8 (n % 256)))

/-- The 16 zero bytes that pad an EIP-2537 coordinate's high word. -/
def eipPad : Bytes := go 16 Bytes.empty
where
  go : Nat -> Bytes -> Bytes
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

/-- `len` big-endian bytes of `n`, high bytes dropped if `n` does not fit
    (which is what a fixed-width Rust `to_bytes` does). -/
def natToBytesBE (n : Nat) (len : Nat) : Bytes :=
  go n len Bytes.empty
where
  go : Nat -> Nat -> Bytes -> Bytes
    | _, 0, acc => acc
    | n, k+1, acc => go (n / 256) k (ByteArray.push acc (Nat.toUInt8 (n % 256)))

/-- `len` little-endian bytes of `n`. -/
def natToBytesLE (n : Nat) (len : Nat) : Bytes :=
  go n len Bytes.empty
where
  go : Nat -> Nat -> Bytes -> Bytes
    | _, 0, acc => acc
    | n, k+1, acc => go (n / 256) k (ByteArray.push acc (Nat.toUInt8 (n % 256)))

end Midfall
