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
/-! ### The value half of the byte round trips (design1 M5-2)

    Earlier rounds recorded this as blocked: `bytesToNatBE` folds with
    `Array.foldl`, which is not *definitionally* `List.foldl` on `toList`, and
    "core has no `Array.foldl_eq_foldl_data`". The first half of that sentence is
    right and the second is not: core exports the equation as `Array.foldl_toList`
    (`Init/Data/Array/Bootstrap.lean:45`, `@[simp]`), which is exactly the transfer
    the induction needs. Nothing below reasons about `Array` internals, and nothing
    below needs a `decide` on a byte string. -/

/-- A digit list read LEAST significant first:
    `ofLowDigits b [d0, ..., dk-1] = sum_i di * b^i`. This is the value
    `bytesToNatLE` computes; naming it is what lets the round trip be proved by
    induction on the digits the emitter builds rather than on the array it pushes
    them into. -/
def ofLowDigits (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: l => d + b * ofLowDigits b l

@[simp]
theorem ofLowDigits_nil (b : Nat) : ofLowDigits b [] = 0 := rfl

theorem ofLowDigits_cons (b : Nat) (d : Nat) (l : List Nat) :
    ofLowDigits b (d :: l) = d + b * ofLowDigits b l := rfl

theorem ofLowDigits_singleton (b : Nat) (d : Nat) : ofLowDigits b [d] = d := by
  rw [ofLowDigits_cons, ofLowDigits_nil, mul_zero, add_zero]

/-- On an append the LEFT list occupies the low positions. -/
theorem ofLowDigits_append (b : Nat) : ∀ (l l' : List Nat),
    ofLowDigits b (l ++ l') = ofLowDigits b l + b ^ l.length * ofLowDigits b l' := by
  intro l
  induction l with
  | nil => intro l'; simp [ofLowDigits_nil]
  | cons d t ih =>
      intro l'
      have h1 : ofLowDigits b ((d :: t) ++ l') = d + b * ofLowDigits b (t ++ l') := rfl
      have h2 : ofLowDigits b (d :: t) = d + b * ofLowDigits b t := rfl
      rw [h1, h2, ih l', List.length_cons, Nat.pow_succ', Nat.mul_add]
      simp [Nat.mul_assoc, Nat.add_assoc]

/-- Horner's rule in the shape the byte readers need: folding
    `fun acc x => acc * b + f x` over a list read MOST significant first is `init`
    shifted past the list plus the value of the list read LEAST significant first.
    Generalised over `init` because that is the only form that inducts. -/
theorem foldl_horner_eq_ofLowDigits {α : Type} (b : Nat) (f : α → Nat) :
    ∀ (l : List α) (init : Nat),
      l.reverse.foldl (fun (acc : Nat) (x : α) => acc * b + f x) init
        = init * b ^ l.length + ofLowDigits b (l.map f) := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a t ih =>
      intro init
      have hstep : ∀ acc : Nat,
          List.foldl (fun (acc : Nat) (x : α) => acc * b + f x) acc [a] = acc * b + f a :=
        fun _ => rfl
      rw [List.reverse_cons, List.foldl_append, hstep, ih, List.length_cons, List.map_cons,
        ofLowDigits_cons, Nat.pow_succ', Nat.add_mul]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm, Nat.add_left_comm]

/-- The forward spelling, obtained by reversing twice. -/
theorem foldl_eq_ofLowDigits_reverse {α : Type} (b : Nat) (f : α → Nat)
    (l : List α) (init : Nat) :
    l.foldl (fun (acc : Nat) (x : α) => acc * b + f x) init
      = init * b ^ l.length + ofLowDigits b (l.reverse.map f) := by
  have h := foldl_horner_eq_ofLowDigits b f l.reverse init
  rwa [List.reverse_reverse, List.length_reverse] at h

/-- `bytesToNatBE` as a `List.foldl` over the array's elements in order. This is
    the single step the earlier rounds believed was unavailable; the equation is
    core's own `Array.foldl_toList`. -/
theorem bytesToNatBE_toList (bs : Bytes) :
    bytesToNatBE bs =
      bs.data.toList.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 := by
  show bs.data.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 = _
  exact (Array.foldl_toList (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat)
    (init := 0) (xs := bs.data)).symm

/-- `bytesToNatLE` as a `List.foldl` over the reversed element list. -/
theorem bytesToNatLE_toList_foldl (bs : Bytes) :
    bytesToNatLE bs =
      bs.data.toList.reverse.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 := by
  show bytesToNatBE (ByteArray.mk bs.data.toList.reverse.toArray) = _
  rw [bytesToNatBE_toList]

/-- Little-endian reading is `ofLowDigits` on the byte values in array order. -/
theorem bytesToNatLE_eq_ofLowDigits (bs : Bytes) :
    bytesToNatLE bs = ofLowDigits 256 (bs.data.toList.map UInt8.toNat) := by
  rw [bytesToNatLE_toList_foldl, foldl_horner_eq_ofLowDigits]
  simp

/-- Big-endian reading is `ofLowDigits` on the byte values reversed, i.e. most
    significant byte first - the mirror image of the lemma above, and the reason
    the two orders can never agree on a non-palindromic value. -/
theorem bytesToNatBE_eq_ofLowDigits_reverse (bs : Bytes) :
    bytesToNatBE bs = ofLowDigits 256 ((bs.data.toList.map UInt8.toNat).reverse) := by
  rw [← List.map_reverse, bytesToNatBE_toList, foldl_eq_ofLowDigits_reverse]
  simp

/-- The one number-theory step: the low digit, plus the rest shifted up one
    place, is the residue modulo one more digit. -/
theorem mod_low_digit (x b k : Nat) (hb : 0 < b) :
    x % b + b * (x / b % b ^ k) = x % b ^ (k + 1) := by
  have hk : 0 < b ^ k := Nat.pow_pos hb
  have h1 : x / b % b ^ k < b ^ k := Nat.mod_lt _ hk
  have h2 : x % b < b := Nat.mod_lt _ hb
  have hlt : b * (x / b % b ^ k) + x % b < b ^ (k + 1) := by
    have h5 : b * (x / b % b ^ k + 1) ≤ b * b ^ k :=
      Nat.mul_le_mul_left b (Nat.succ_le_of_lt h1)
    rw [Nat.mul_add, Nat.mul_one] at h5
    have h6 : b * (x / b % b ^ k) + x % b < b * b ^ k := by omega
    rw [Nat.pow_succ' (m := b) (n := k)]
    exact h6
  have e1 : x = b * (x / b) + x % b := by
    have := Nat.div_add_mod x b; omega
  have e2 : x / b = b ^ k * (x / b / b ^ k) + x / b % b ^ k := by
    have := Nat.div_add_mod (x / b) (b ^ k); omega
  have e4 : b ^ (k + 1) * (x / b / b ^ k) + (b * (x / b % b ^ k) + x % b) = x := by
    rw [Nat.pow_succ' (m := b) (n := k), Nat.mul_assoc, ← Nat.add_assoc, ← Nat.mul_add, ← e2, ← e1]
  have h := congrArg (fun t : Nat => t % b ^ (k + 1)) e4
  rw [Nat.add_mod, Nat.mul_comm, Nat.mul_mod_left, zero_add] at h
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] at h
  omega

/-- The value the emitter appends, as digits: `go n len acc` writes the `len`
    low-order base-256 digits of `n` after whatever `acc` already holds, so the
    little-endian value of the result is the value of `acc` plus `n % 256^len`
    shifted past it. -/
theorem natToBytesLowFirst_go_ofLowDigits : ∀ (len : Nat) (n : Nat) (acc : Bytes),
    ofLowDigits 256 ((Midfall.natToBytesLowFirst.go n len acc).data.toList.map UInt8.toNat)
      = ofLowDigits 256 (acc.data.toList.map UInt8.toNat)
          + 256 ^ acc.size * (n % 256 ^ len) := by
  intro len
  induction len with
  | zero =>
      intro n acc
      show ofLowDigits 256 (acc.data.toList.map UInt8.toNat) = _
      simp [Nat.mod_one, pow_zero, mul_zero]
  | succ k ih =>
      intro n acc
      show ofLowDigits 256 ((Midfall.natToBytesLowFirst.go (n / 256) k
            (acc.push (Nat.toUInt8 (n % 256)))).data.toList.map UInt8.toNat) = _
      rw [ih, ← mod_low_digit n 256 k (by decide)]
      have hpush : (acc.push (Nat.toUInt8 (n % 256))).data.toList
          = acc.data.toList ++ [Nat.toUInt8 (n % 256)] := by
        cases acc with
        | mk arr => simp [ByteArray.push, Array.toList_push]
      have hsize : (acc.push (Nat.toUInt8 (n % 256))).size = acc.size + 1 :=
        ByteArray.size_push
      have hsz : acc.size = acc.data.toList.length := by
        rw [← ByteArray.size_data]; exact Array.size_eq_length_toList
      have hu8 : (Nat.toUInt8 (n % 256)).toNat = n % 256 := by simp [Nat.toUInt8]
      rw [hpush, List.map_append, List.map_singleton, ofLowDigits_append, ofLowDigits_singleton,
        hsize, hsz, hu8, List.length_map, Nat.pow_succ', Nat.mul_add]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- **The value half of the repr round trip.** Reading back what the emitter
    wrote, in the same order, recovers `n` modulo the width. The modulus is not
    decoration: at `n = 256, len = 1` the round trip gives `0`, not `256` - the
    D-P23 falsifiability witness is `bytesValueRoundTrip_ok` below, and the same
    truncation at `len = 32` is why `p <= 2^256` is load-bearing in
    `Midfall.Assumptions.frOfRepr_frToRepr`. -/
theorem bytesToNatLE_natToBytesLE (n len : Nat) :
    bytesToNatLE (natToBytesLE n len) = n % 256 ^ len := by
  show bytesToNatLE (Midfall.natToBytesLowFirst n len) = _
  rw [bytesToNatLE_eq_ofLowDigits]
  show ofLowDigits 256
        ((Midfall.natToBytesLowFirst.go n len Bytes.empty).data.toList.map UInt8.toNat) = _
  rw [natToBytesLowFirst_go_ofLowDigits]
  have h0 : Bytes.empty.data.toList = [] := rfl
  have h1 : Bytes.empty.size = 0 := rfl
  simp only [h0, h1, List.map_nil, ofLowDigits_nil, pow_zero, Nat.one_mul, Nat.zero_add]

/-- The big-endian mirror: the two orders are the same fold on the two ends of
    the same digit list, so both round trips have the same value. -/
theorem bytesToNatBE_natToBytesBE (n len : Nat) :
    bytesToNatBE (natToBytesBE n len) = n % 256 ^ len := by
  show bytesToNatBE (ByteArray.mk (Midfall.natToBytesLowFirst n len).data.toList.reverse.toArray) = _
  rw [bytesToNatBE_toList]
  have h : (ByteArray.mk (Midfall.natToBytesLowFirst n len).data.toList.reverse.toArray).data
      = (Midfall.natToBytesLowFirst n len).data.toList.reverse.toArray := rfl
  rw [h, List.toList_toArray, foldl_horner_eq_ofLowDigits, Nat.zero_mul, Nat.zero_add,
    ← bytesToNatLE_eq_ofLowDigits]
  exact bytesToNatLE_natToBytesLE n len

/-- `bytesToWordLE` is `bytesToNatLE` reduced into 256 bits, so the word reader
    truncates exactly where the byte reader does. -/
theorem bytesToWordLE_eq_bytesToNatLE (bs : Bytes) :
    bytesToWordLE bs = BitVec.ofNat 256 (bytesToNatLE bs) :=
  congrArg (BitVec.ofNat 256) (bytesToNatLE_toList_foldl bs).symm

/-- `bytesToWordBE` is `bytesToNatBE` reduced into 256 bits. -/
theorem bytesToWordBE_eq_bytesToNatBE (bs : Bytes) :
    bytesToWordBE bs = BitVec.ofNat 256 (bytesToNatBE bs) := rfl

/-- The width of a 32-byte word in the emitter's own base: `256^32 = 2^256`.
    Named because it is the equation that turns "the repr is 32 bytes" into "the
    repr is canonical below `2^256`", which is what `frOfRepr_frToRepr` consumes. -/
theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := rfl

private theorem two_pow_256_pos : 0 < (2 : Nat) ^ 256 := by decide

/-- The word-level round trip design1 M5-2 asks for. No bound on `n`: both sides
    reduce mod `2^256`, so this holds even where the Nat-level round trip above
    truncates. That is exactly why `feToU256_frToRepr` needs no `p <= 2^256`. -/
theorem bytesToWordLE_natToBytesLE (n : Nat) :
    bytesToWordLE (natToBytesLE n 32) = BitVec.ofNat 256 n := by
  rw [bytesToWordLE_eq_bytesToNatLE, bytesToNatLE_natToBytesLE, pow_256_32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.mod_lt n two_pow_256_pos

theorem bytesToWordLE_wordToBytesLE (w : Word256) : bytesToWordLE (wordToBytesLE w) = w := by
  rw [wordToBytesLE, bytesToWordLE_natToBytesLE]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_mod_cancel w]

theorem bytesToWordBE_wordToBytesBE (w : Word256) : bytesToWordBE (wordToBytesBE w) = w := by
  rw [wordToBytesBE, bytesToWordBE_eq_bytesToNatBE, bytesToNatBE_natToBytesBE, pow_256_32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_mod_cancel w, BitVec.toNat_mod_cancel w]
/-- The VALUE half, computed - the D-P23 witness for `bytesToNatLE_natToBytesLE`
    and `bytesToNatBE_natToBytesBE`. The last five conjuncts are the falsifiability
    half: the round trip is `n % 256^len` and NOT `n`, so the width bound in
    `frOfRepr_frToRepr` is doing real work. `2^256` is the first value a 32-byte
    repr cannot carry, and it decodes to `0`; `256` at width 1 is the same failure
    small enough for a reviewer to check by hand. -/
def bytesValueRoundTrip_ok : Bool :=
  (bytesToNatLE (natToBytesLE 0x01020304 4) == 0x01020304) &&
  (bytesToNatBE (natToBytesBE 0x01020304 4) == 0x01020304) &&
  (bytesToNatLE (natToBytesLE (2 ^ 200 + 5) 32) == 2 ^ 200 + 5) &&
  (bytesToNatLE (natToBytesLE (2 ^ 256 - 1) 32) == 2 ^ 256 - 1) &&
  (bytesToWordLE (natToBytesLE (2 ^ 256 - 1) 32) == BitVec.ofNat 256 (2 ^ 256 - 1)) &&
  (bytesToWordBE (natToBytesBE (2 ^ 256 - 1) 32) == BitVec.ofNat 256 (2 ^ 256 - 1)) &&
  -- the truncation, at the width the scalar repr actually uses
  (bytesToNatLE (natToBytesLE (2 ^ 256) 32) == 0) &&
  (bytesToNatBE (natToBytesBE (2 ^ 256) 32) == 0) &&
  -- and the same failure at a width a reviewer can check by hand
  (bytesToNatLE (natToBytesLE 256 1) == 0) &&
  (bytesToNatLE (natToBytesLE 257 1) == 1) &&
  (bytesToNatLE (natToBytesLE 256 1) != 256)

#eval bytesValueRoundTrip_ok   -- expect true, and scripts/checks.sh asserts it

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
