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

end Midfall
