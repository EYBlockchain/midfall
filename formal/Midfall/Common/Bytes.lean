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

/-! ### Fixed-width frame lemmas (P-BYTES)

    The EIP-2537 encodings the accumulator codec reads and writes are
    concatenations of fixed-width big-endian fields, so what the decoder and the
    codec's laws need is a SPLIT lemma: write x = hi * 256^m + lo with
    lo < 256^m; then the m + n big-endian bytes of x are the n bytes of hi
    followed by the m bytes of lo. Nothing in the tree had it.
    bytesToNatBE_natToBytesBE above round-trips a VALUE and says nothing about how
    an emitted string is laid out, which is why the decodeAcc round trips were
    stuck: the decoder rebuilds one coordinate as two 32-byte words while the
    codec's law speaks of one 48-byte field, and the two are equal only by a fact
    about digit lists. -/

private theorem go_zero : ∀ (n : Nat) (acc : Bytes),
    Midfall.natToBytesLowFirst.go n 0 acc = acc := by
  intro n acc; rfl

private theorem go_succ : ∀ (n : Nat) (k : Nat) (acc : Bytes),
    Midfall.natToBytesLowFirst.go n (k+1) acc =
      Midfall.natToBytesLowFirst.go (n/256) k (acc.push (Nat.toUInt8 (n % 256))) := by
  intro n k acc; rfl

private theorem empty_data_toList : Bytes.empty.data.toList = [] := rfl

private theorem push_data_toList : ∀ (a : Bytes) (x : UInt8),
    (a.push x).data.toList = a.data.toList ++ [x] := by
  intro a x
  cases a with
  | mk arr => simp [ByteArray.push, Array.toList_push]

/-- The emitter APPENDS: go n len acc is acc followed by what the emitter writes
    from empty. Stated on the underlying list because that is where ByteArray.push
    becomes an append of a singleton. -/
private theorem go_data_toList : ∀ (len : Nat) (n : Nat) (acc : Bytes),
    (Midfall.natToBytesLowFirst.go n len acc).data.toList =
      acc.data.toList ++ (Midfall.natToBytesLowFirst.go n len Bytes.empty).data.toList := by
  intro len
  induction len with
  | zero =>
      intro n acc
      rw [go_zero, go_zero, empty_data_toList, List.append_nil]
  | succ k ih =>
      intro n acc
      have key := ih (n := n / 256)
      rw [go_succ, key (acc := acc.push (Nat.toUInt8 (n % 256))), go_succ,
          key (acc := Bytes.empty.push (Nat.toUInt8 (n % 256))),
          push_data_toList, push_data_toList, empty_data_toList]
      simp [List.append_assoc, List.nil_append]

/-- Split at a byte boundary in the emitter's own least-significant-first order.
    The hypothesis is load-bearing: lo = 256^m would carry into hi's digits. -/
theorem natToBytesLowFirst_split : ∀ (m : Nat) (hi lo : Nat), lo < 256 ^ m →
    ∀ (n : Nat),
      (natToBytesLowFirst (hi * 256 ^ m + lo) (m + n)).data.toList =
        (natToBytesLowFirst lo m).data.toList ++ (natToBytesLowFirst hi n).data.toList := by
  intro m
  induction m with
  | zero =>
      intro hi lo hlo n
      have h0 : lo = 0 := by omega
      subst h0
      rw [Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
      simp [natToBytesLowFirst, go_zero, empty_data_toList, List.nil_append]
  | succ k ih =>
      intro hi lo hlo n
      have hpow : 256 ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ']
      have hdm : 256 * (lo / 256) + lo % 256 = lo := Nat.div_add_mod lo 256
      have hdv : hi * 256 ^ (k + 1) + lo = 256 * (hi * 256 ^ k + lo / 256) + lo % 256 := by
        rw [hpow, Nat.mul_add, Nat.add_assoc, hdm, Nat.mul_left_comm 256 hi (256 ^ k)]
      have hmod : (hi * 256 ^ (k + 1) + lo) % 256 = lo % 256 := by
        rw [hdv, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_mod]
      have hdiv : (hi * 256 ^ (k + 1) + lo) / 256 = hi * 256 ^ k + lo / 256 := by
        rw [hdv, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 256),
            Nat.div_eq_of_lt (Nat.mod_lt lo (by decide : 0 < 256)), Nat.zero_add]
      have hlen : k + 1 + n = (k + n) + 1 := by omega
      have hc : lo / 256 < 256 ^ k := by
        have h : lo < 256 * 256 ^ k := by rwa [← hpow]
        exact Nat.div_lt_of_lt_mul h
      have hL : (natToBytesLowFirst (hi * 256 ^ (k + 1) + lo) (k + 1 + n)).data.toList =
          [Nat.toUInt8 (lo % 256)] ++
            (natToBytesLowFirst (hi * 256 ^ k + lo / 256) (k + n)).data.toList := by
        show (Midfall.natToBytesLowFirst.go (hi * 256 ^ (k + 1) + lo) (k + 1 + n)
                Bytes.empty).data.toList = _
        rw [hlen, go_succ, hmod, hdiv,
            go_data_toList (len := k + n) (n := hi * 256 ^ k + lo / 256)
              (acc := Bytes.empty.push (Nat.toUInt8 (lo % 256)))]
        rw [push_data_toList, empty_data_toList, List.nil_append]
        simp only [natToBytesLowFirst]
      have hR : (natToBytesLowFirst lo (k + 1)).data.toList =
          [Nat.toUInt8 (lo % 256)] ++ (natToBytesLowFirst (lo / 256) k).data.toList := by
        show (Midfall.natToBytesLowFirst.go lo (k + 1) Bytes.empty).data.toList = _
        rw [go_succ,
            go_data_toList (len := k) (n := lo / 256)
              (acc := Bytes.empty.push (Nat.toUInt8 (lo % 256)))]
        rw [push_data_toList, empty_data_toList, List.nil_append]
        simp only [natToBytesLowFirst]
      rw [hL, ih hi (lo / 256) hc, ← List.append_assoc, ← hR]

/-- **The split lemma, big-endian**: the m + n bytes of hi * 256^m + lo are hi's n
    bytes followed by lo's m bytes. This is the fact that makes the decoder's
    two-word rebuild of a coordinate equal the codec's one 48-byte field. -/
theorem natToBytesBE_split (hi lo m : Nat) (hlo : lo < 256 ^ m) : ∀ (n : Nat),
    natToBytesBE (hi * 256 ^ m + lo) (m + n) = natToBytesBE hi n ++ natToBytesBE lo m := by
  intro n
  have hb (x l : Nat) : (natToBytesBE x l).data.toList =
      (natToBytesLowFirst x l).data.toList.reverse := by
    simp [natToBytesBE, List.toList_toArray]
  have hap (a b : Bytes) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := rfl
  apply ByteArray.ext
  rw [← Array.toList_inj, hb, hap, hb, hb,
      natToBytesLowFirst_split (m := m) hi lo hlo n, List.reverse_append]

/-- ByteArray append is append on the underlying array. Not rfl: the projection
    does not reduce through the core implementation of append. -/
private theorem append_data (u v : Bytes) : (u ++ v).data = u.data ++ v.data := by
  apply Array.toList_inj.mp
  show (u ++ v).data.toList = (u.data ++ v.data).toList
  rw [Array.toList_append]
  rfl

/-- Reading a window that lies inside the left operand of a concatenation - the
    EIP frame's first coordinate. -/
theorem bytesTake_append_left (u v : Bytes) (i n : Nat) (h : i + n ≤ u.size) :
    bytesTake (u ++ v) i n = bytesTake u i n := by
  have hdp := append_data u v
  unfold bytesTake
  rw [hdp]
  have h1 : i + n ≤ (u ++ v).size := Nat.le_trans h (by
    rw [ByteArray.size_append]; omega)
  rw [if_pos h1, if_pos h, Array.extract_append]
  have h2 : i - u.data.size = 0 := Nat.sub_eq_zero_of_le (by
    have hz : u.data.size = u.size := rfl
    omega)
  have h3 : i + n - u.data.size = 0 := Nat.sub_eq_zero_of_le (by
    have hz : u.data.size = u.size := rfl
    omega)
  rw [h2, h3, Array.extract_zero, Array.append_empty]

/-- Reading a window that lies inside the right operand of a concatenation - the
    EIP frame's second coordinate. -/
theorem bytesTake_append_right (u v : Bytes) (i n : Nat) (h : i + n ≤ v.size) :
    bytesTake (u ++ v) (u.size + i) n = bytesTake v i n := by
  have hdp := append_data u v
  unfold bytesTake
  rw [hdp]
  have h1 : u.size + i + n ≤ (u ++ v).size := by
    rw [ByteArray.size_append]; omega
  rw [if_pos h1, if_pos h, Array.extract_append]
  have h2 : u.size + i - u.data.size = i := by
    have hz : u.data.size = u.size := rfl
    omega
  have h3 : u.size + i + n - u.data.size = i + n := by
    have hz : u.data.size = u.size := rfl
    omega
  rw [h2, h3]
  have h4 : u.data.extract (u.size + i) (u.size + i + n) = #[] :=
    Array.extract_eq_empty_of_le (by
      have hz : u.data.size = u.size := rfl
      have : min (u.size + i + n) u.data.size ≤ u.data.size := Nat.min_le_right _ _
      omega)
  rw [h4, Array.empty_append]

set_option exponentiation.threshold 512 in
/-- The width of a 48-byte EIP-2537 field in the emitter's base. Stated by the
    power law rather than by rfl: the kernel refuses to EVALUATE 2^384 (the
    exponentiation threshold is 256), and every attempt to do so is a warning. -/
theorem pow_256_48 : (256 : Nat) ^ 48 = 2 ^ 384 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- The width of the 16-byte EIP zero pad. -/
theorem pow_256_16 : (256 : Nat) ^ 16 = 2 ^ 128 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

end Midfall

/-! ## `BEq ByteArray` is reflexive (card BEQ · PG-G1BEQ128)

`Midfall.Lowering.InvAt`'s g1_identity window is a Bool,

    bytesAt st (ptrAddr M.g1IdentityMptr) 128 == Midfall.natToBytesBE 0 128

and once the window EQUALITY is rewritten into it the goal is the same term on both sides:

    (Midfall.natToBytesBE 0 128 == Midfall.natToBytesBE 0 128) = true

That equation is not `rfl` and not `decide`: `ByteArray.beq lhs rhs = lhs.data == rhs.data`, so
evaluating it walks the payload, and at 128 bytes the kernel gives up - measured on this tree,
`by rfl` and `by decide` on the goal above both fail with `maximum recursion depth has been
reached`, while the SAME `decide` at 64 bytes succeeds. Raising `maxRecDepth` is out of bounds.
It is not `simp` either: `simp` makes no progress, because the reflexivity simp lemma for this
shape is `BEq.rfl` / `beq_self_eq_true`, and both need `ReflBEq ByteArray`, which nothing in
scope provides -

    failed to synthesize instance of type class
      ReflBEq ByteArray

THE GAP IS IN THE INSTANCE GRAPH, NOT IN THE STATEMENT. Core does have
`instance [DecidableEq α] : LawfulBEq α` and `ByteArray` does have `DecidableEq`, but that route
does not reach this `BEq`: `ByteArray`'s own `instance : BEq ByteArray := ⟨ByteArray.beq⟩` wins
for a `ByteArray` goal, whereas the `DecidableEq` route builds `instBEqOfDecidableEq`. So
`beq_self_eq_true'` - the `DecidableEq` spelling, which does elaborate - states

    @BEq.beq ByteArray instBEqOfDecidableEq b b = true

while the goal says `@BEq.beq ByteArray ByteArray.instBEq b b = true`: a BEq mismatch, not a
proof. What is missing is reflexivity of the `BEq` that `ByteArray` actually uses.

It is true, and cheaply so: `ByteArray` is the one-field structure `{ data : Array UInt8 }`
(Prelude.lean:3561), `ByteArray.beq` is `Array`'s `beq` on that field, and core proves
`ReflBEq (Array UInt8)` (Init/Data/Array/DecidableEq.lean:175). So this is a transport along the
projection. It adds no axiom, does not change the definition of `BEq ByteArray`, and does not
weaken any clause: it makes a Bool that was already true reachable without evaluating 128 bytes. -/

/-- **`BEq ByteArray` is reflexive.** `(b == b) = true` for a SYMBOLIC byte array, with no
evaluation of the payload. Without this instance the equation is unprovable by `rfl`, `decide` or
`simp` at 128 bytes - see the section note. Declared on `ByteArray` itself, not on the
`Midfall.Bytes` abbrev, so that it is the `ReflBEq` the `ByteArray.instBEq` in scope asks for. -/
instance byteArrayReflBEq : ReflBEq ByteArray where
  rfl {a} := by
    -- `ByteArray.beq a a` is `a.data == a.data`, and core has `ReflBEq (Array UInt8)`.
    cases a with
    | mk arr => exact (inferInstance : ReflBEq (Array UInt8)).rfl

/-- The same fact as a theorem, for a caller that uses `simp only [...]` and so will not pick the
instance up by itself: `rw [ByteArray.beq_self]` or `exact ByteArray.beq_self _`. -/
theorem ByteArray.beq_self (b : ByteArray) : (b == b) = true := beq_self_eq_true b

#print axioms byteArrayReflBEq
#print axioms ByteArray.beq_self

