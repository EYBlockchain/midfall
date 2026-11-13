-- |
-- Midfall.Assumptions.Codec
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 3; PLAN
-- P-SE-semantic-equivalence.md section C and index item 3; design1.md
-- 'G1CodecLaws (structure; statable-now; M5)').
--
-- WHAT THIS FILE IS FOR. Every headline semantic-equivalence statement consumes
-- a G1 point codec: the contract absorbs 128-byte EIP-2537 encodings straight out
-- of calldata, and the Lean verifier absorbs the DECODED points re-serialised by
-- the same codec. The two agree only if the codec is canonical in both directions,
-- so the laws are named here once instead of being scattered through the
-- theorems. design1 lists the consumers: decodeAcc_encode, decodeAcc_injective,
-- calldata_roundtrip, calldata_canonical and the provable restatement of
-- Statements.verifyNative_iff_msgs (finding B1).
--
-- WHY A HYPOTHESIS STRUCTURE AND NOT A CLASS. R-34 (docs/REVIEW.md): no Lean
-- instance proves any of these laws, and the only real BLS12-381 codec lives in
-- Midfall/Instances/Bls12_381.lean, which no theorem-bearing file may import
-- (D-P17, enforced by scripts/checks.sh). So each law is a binder, exactly as
-- Midfall/Assumptions/Pairing.lean does for the pairing itself: a hypothesis is a
-- binder, not a proof hole, and the gap policy (plan Section 3) prefers it to a
-- bare sorry.
--
-- WHICH SET OF LAWS. attack.md line 15 records that the three design passes
-- proposed two different bundles in this file (P1 G1Codec.Laws with four fields,
-- P3 G1CodecLaws with six) and line 180 FIX settles it: one structure, P3 fields
-- plus eipWidth, because the headline theorems need toEip_one (the committed point
-- absorbed as 128 zero bytes), eipShape and ofEip_toEip, and P1 set is
-- insufficient. The two round trips are the tree decoder-first properties
-- (Common/Codec.lean:106 and :113); the encoder-first law was deliberately
-- REMOVED from G1Codec (Common/Codec.lean:97-105 records why) and must stay a
-- hypothesis here rather than being restated as a fact.
--
-- THE FALSEHOOD THIS FILE DOES NOT STATE, AND WHAT HAPPENED TO IT. The frozen
-- Midfall.Statements.verifyNative_iff_msgs WAS false for a degenerate codec
-- (finding B1: toCompressed := fun _ => Bytes.empty re-serialises a 48-byte
-- stream to nothing, so prepareMsgs faults while verifyNative accepts). That
-- sentence is now past tense: D-P27, executed by P-REPIN, amended the frozen text
-- to carry hc : E.g1.compressedRoundtrip - the law defined in this file's own
-- bundle, at Common/Codec.lean:113 - and the refutation is no longer a comment
-- anywhere but a theorem, repair1_old_false_at_degEnv in
-- Midfall/Instances/StatementsRepair.lean, with repair1_satisfiable on the other
-- side of D-P23. scripts/check_statement_fingerprints.py pins the repaired shape
-- and refuses the old one, so this paragraph cannot go back to being present tense
-- without a gate reddening. Its restatement, verifyNative_iff_msgs_codec, belongs
-- to Obligations.lean (stage 6) because it needs the transcript-log invariant; it
-- is NOT hidden here. attack.md line 107 FIX also drops the p <= 2^256 hypothesis
-- from that restatement as decorative while KEEPING it here, where the
-- encoder-first direction is used.

import Midfall.Common.Codec
import Midfall.Common.Bytes
import Midfall.Assumptions.Pairing

namespace Midfall.Assumptions
open Midfall

/-! ### The G1 codec law bundle -/

/-- The G1 codec laws the accumulator and calldata statements consume (R-34: each
    is a binder, none is proved in-tree). The two round trips are decoder-first
    (Common/Codec.lean:106, :113); ofEip_toEip is the encoder-first law that
    Common/Codec.lean:97-105 deliberately removed from G1Codec, and it is needed
    only where the encoder is OURS (asPublicInputPoint, encodeContractProof).

    eipShape is the EIP-2537 frame shape with in-field, non-(0,0) coordinates:
    AssemblyHelpers.yul:94-104 and AccumulatorHelpers.yul:152-157 reject (0,0)
    under flag 0, so a codec that encoded a nonzero point as all-zero bytes would
    make the contract and the transcript disagree about the identity. toEip_one is
    the other half of the same pin: the committed point is absorbed as 128 zero
    bytes by the contract (TranscriptProofParser.yul:36-46) while Lean absorbs
    toEip 1, and attack.md line 32 (FIX, binding) makes both laws hypotheses of
    every headline field. -/
structure G1CodecLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  /-- decoder-first: whatever ofEip? accepts re-encodes to the same bytes. -/
  eipRoundtrip : c.eipRoundtrip
  /-- decoder-first for the 48-byte transcript form. -/
  compressedRoundtrip : c.compressedRoundtrip
  /-- encoder-first, restricted to real points: needed by decodeAcc_encode and
      calldata_roundtrip. -/
  ofEip_toEip : ∀ Q : G₁, c.ofEip? (c.toEip Q) = some Q
  /-- the 16-48-16-48 EIP-2537 frame, coordinates in field and not both zero. -/
  eipShape : ∀ Q : G₁, Q ≠ 1 → ∃ x y : Nat, x < pBase ∧ y < pBase ∧ ¬ (x = 0 ∧ y = 0) ∧
    c.toEip Q = natToBytesBE 0 16 ++ natToBytesBE x 48 ++ natToBytesBE 0 16 ++ natToBytesBE y 48
  /-- identity is exactly 128 zero bytes (AccumulatorHelpers.yul:137-140). -/
  toEip_one : c.toEip 1 = natToBytesBE 0 128
  /-- the two widths, so a wrong-length repr is a shape error, not a silent none. -/
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  eipWidth : ∀ Q : G₁, (c.toEip Q).size = g1EipWidth

/-! ### Byte lemmas (design1 M5-2)

design1 M5-2 assigns this stage the byte lemmas the VkDigest, Calldata and
Accumulator statements share. They are stated here, in the assumption layer,
because this is the first file that needs them and because their natural home -
Midfall/Common/Bytes.lean - is the P-05 row's file, which stage 2 may not edit
(the standing rule against touching another package's Lean file). Only the SHAPE
half is still here; the VALUE half landed in Common/Bytes.lean when P-BYTES was
given edit rights on it - see bytesToNatLE_natToBytesLE there and
frOfRepr_frToRepr below. -/

/-- The digits natToBytesLowFirst emits, least significant first, as a list. This
    is the shape the emitter's accumulator builds, and naming it is what makes the
    induction go through without reasoning about ByteArray internals. -/
def lowDigits : Nat → Nat → List UInt8
  | _, 0 => []
  | n, k+1 => Nat.toUInt8 (n % 256) :: lowDigits (n / 256) k

/-- The emitter's accumulator step, as a list equation. -/
theorem lowDigits_go : ∀ (len : Nat) (n : Nat) (acc : Bytes),
    (Midfall.natToBytesLowFirst.go n len acc).data.toList =
      acc.data.toList ++ lowDigits n len := by
  intro len
  induction len with
  | zero => intro n acc; simp [Midfall.natToBytesLowFirst.go, lowDigits]
  | succ k ih =>
      intro n acc
      show (Midfall.natToBytesLowFirst.go (n/256) k
            (acc.push (Nat.toUInt8 (n % 256)))).data.toList = _
      rw [ih (n := n/256) (acc := acc.push (Nat.toUInt8 (n % 256)))]
      have hpush : (acc.push (Nat.toUInt8 (n % 256))).data.toList =
          acc.data.toList ++ [Nat.toUInt8 (n % 256)] := by
        cases acc with
        | mk arr => simp [ByteArray.push, Array.toList_push]
      rw [hpush, List.append_assoc]
      rfl

/-- The emitter always produces exactly len bytes - which is the half of
    frOfRepr_frToRepr that is about the SHAPE of a repr rather than its value, and
    the half that makes feToU256's length guard unreachable for frToRepr. -/
theorem natToBytesLowFirst_size (n len : Nat) :
    (natToBytesLowFirst n len).size = len := by
  show (Midfall.natToBytesLowFirst.go n len Bytes.empty).size = len
  have h : ∀ (len : Nat) (n : Nat) (acc : Bytes),
      (Midfall.natToBytesLowFirst.go n len acc).size = acc.size + len := by
    intro len
    induction len with
    | zero => intro n acc; simp [Midfall.natToBytesLowFirst.go]
    | succ k ih =>
        intro n acc
        show (Midfall.natToBytesLowFirst.go (n/256) k
              (acc.push (Nat.toUInt8 (n % 256)))).size = _
        rw [ih (n := n/256) (acc := acc.push (Nat.toUInt8 (n % 256)))]
        rw [ByteArray.size_push]
        omega
  rw [h]
  have h0 : Bytes.empty.size = 0 := rfl
  omega

/-- The same fact for the two public spellings, so a caller never has to know that
    natToBytesLE is natToBytesLowFirst. -/
theorem frToRepr_size {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) :
    (frToRepr x).size = 32 := natToBytesLowFirst_size x.val 32

/-! ### The scalar repr round trip -/

/-- A canonical scalar round-trips through its 32-byte little-endian repr
    (rust: ff::PrimeField::to_repr then from_repr, implementors.rs:322-334). The
    bound p <= 2^256 is load-bearing: frToRepr truncates to 32 bytes
    (Common/Bytes.lean:45-54), so for p > 2^256 a value at or above 2^256 decodes
    to its residue, not to itself. attack.md line 107 FIX keeps hp HERE (the
    encoder-first direction) while dropping it from verifyNative_iff_msgs_codec,
    which is decoder-first and does not need it.

    PROVED by P-BYTES. The two byte lemmas design1 M5-2 assigns are
    natToBytesLowFirst_size (above: the SHAPE half, so frOfRepr?'s width test
    passes) and bytesToNatLE_natToBytesLE (Common/Bytes.lean: the VALUE half).
    The obstacle recorded here for several rounds - Array.foldl is not
    definitionally List.foldl on toList, and "core exports no
    Array.foldl_eq_foldl_data" - was only half true and blocked nothing: Array.foldl
    indeed is not definitionally the list fold, but core DOES export the equation,
    under the name Array.foldl_toList (Init/Data/Array/Bootstrap.lean:45), and that
    is the single step bytesToNatBE_toList needs. D-P23 halves: the witness is
    frReprKats_ok below, computed at p = 17; the falsification is
    frOfRepr_fails_above_width, which shows the conclusion is false for EVERY
    modulus above 2^256, so hp is not decoration. -/
theorem frOfRepr_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≤ 2 ^ 256) (x : Fr p) :
    frOfRepr? (p := p) (frToRepr x) = some x := by
  have hval : x.val < p := ZMod.val_lt x
  have hv : bytesToNatLE (frToRepr x) = x.val := by
    show bytesToNatLE (Midfall.natToBytesLE x.val 32) = x.val
    rw [Midfall.bytesToNatLE_natToBytesLE, Midfall.pow_256_32]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hval hp)
  have hcast : (x.val : Fr p) = x := by
    apply ZMod.val_injective p
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hval]
  rw [frOfRepr?, frToRepr_size x, hv]
  split
  · rw [hcast]
  · simp_all

/-- The bound p <= 2^256 in frOfRepr_frToRepr is not decoration: for EVERY
    modulus above it the element 2^256 has a 32-byte repr of all zeros, which
    decodes to 0 and not to itself, so the encoder-first round trip fails. This is
    the D-P23 falsification half for frOfRepr_frToRepr, and it is a theorem rather
    than a comment.

    Why it is stated under a hypothesis instead of at a literal prime: a
    Fact (Nat.Prime p) instance for a prime above 2^256 cannot be produced inside
    the kernel budget (it is primality of a 257-bit number), so the counterexample
    is proved for an arbitrary such p and the antecedent is discharged
    independently by primes_above_two_pow_256. What can be computed is computed:
    bytesValueRoundTrip_ok in Common/Bytes.lean evaluates
    bytesToNatLE (natToBytesLE (2^256) 32) == 0, the single step this lemma turns
    into a theorem. -/
theorem frOfRepr_fails_above_width {p : ℕ} [Fact (Nat.Prime p)] (hp : 2 ^ 256 < p) :
    ∃ x : Fr p, frOfRepr? (p := p) (frToRepr x) ≠ some x := by
  set x : Fr p := ((2 ^ 256 : ℕ) : Fr p) with hx
  have hval : x.val = 2 ^ 256 := by
    show ((2 ^ 256 : ℕ) : Fr p).val = 2 ^ 256
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hp]
  have hv : bytesToNatLE (frToRepr x) = 0 := by
    show bytesToNatLE (Midfall.natToBytesLE x.val 32) = 0
    rw [hval, Midfall.bytesToNatLE_natToBytesLE, Midfall.pow_256_32, Nat.mod_self]
  have hzero : (0 : Fr p) ≠ x := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_zero, hval] at this
    exact absurd this (by omega)
  have hpos : (0 : Nat) < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  refine ⟨x, ?_⟩
  rw [frOfRepr?, frToRepr_size x, hv]
  split
  · intro h
    exact hzero (by simpa using h)
  · simp_all

/-- The hypothesis of frOfRepr_fails_above_width is satisfiable, so that lemma is
    not an implication with an impossible antecedent: primes above 2^256 exist
    (Euclid, as Nat.exists_infinite_primes). -/
theorem primes_above_two_pow_256 : ∃ p : ℕ, 2 ^ 256 < p ∧ p.Prime := by
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (2 ^ 256 + 1)
  exact ⟨q, by omega, hq2⟩

/-! ### Non-vacuity -/

/-- The bundle is not the trivial predicate: three of its seven fields are
    refuted by the two degenerate codecs below, so no field can be discharged by
    accident (design1 non-vacuity note; attack.md line 180). Both are written over
    Multiplicative (ZMod 17), a nontrivial group that needs no curve instance and
    so does not drag Midfall/Instances/ into a theorem-bearing file (D-P17). -/
def shortEipCodec : G1Codec (Multiplicative (ZMod 17)) where
  toEip := fun _ => natToBytesBE 0 96
  ofEip? := fun _ => none
  toCompressed := fun _ => Bytes.empty
  ofCompressed? := fun _ => none

/-- The honest 128-zero identity encoding with a decoder that answers nothing:
    the shape is right and the encoder-first law is what fails. -/
def nullDecoderCodec : G1Codec (Multiplicative (ZMod 17)) where
  toEip := fun _ => natToBytesBE 0 128
  ofEip? := fun _ => none
  toCompressed := fun _ => natToBytesBE 0 48
  ofCompressed? := fun _ => none

/-- toEip_one and eipWidth are load-bearing: a codec that drops the two padding
    words satisfies every algebraic law you can write and still disagrees with the
    contract about the committed point. Refuted by byte count, which is the cheap
    way to keep the gate inside the kernel budget (a 128-element decide blows the
    recursion depth). -/
example : G1CodecLaws shortEipCodec → False := by
  intro l
  have h : (shortEipCodec.toEip 1).size = (natToBytesBE 0 128).size := congrArg ByteArray.size l.toEip_one
  exact absurd h (by decide)

example : G1CodecLaws shortEipCodec → False := by
  intro l
  have h : (shortEipCodec.toEip (1 : Multiplicative (ZMod 17))).size = g1EipWidth :=
    l.eipWidth (1 : Multiplicative (ZMod 17))
  exact absurd h (by decide)

/-- ofEip_toEip is load-bearing: a decoder that rejects everything makes the
    encoder-first law false at the identity, which is the one point the contract
    always sees (the committed instance column). -/
example : G1CodecLaws nullDecoderCodec → False := by
  intro l
  have h := l.ofEip_toEip (1 : Multiplicative (ZMod 17))
  simp [nullDecoderCodec] at h

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The scalar repr gate, computed at a small prime so the kernel can reduce it:
    32 bytes out, the round trip frOfRepr_frToRepr states on the value the
    transcript actually reads, and a negative control - a decoder that ignored
    canonicity would answer some for the value 17 as well, which is exactly the
    malleability frOfRepr? exists to reject (Common/Codec.lean:35-39). The last two
    lines pin the byte ORDER: little-endian, so 2 is the first byte and not the
    last - the R-20 defect class. -/
def frReprKats_ok : Bool :=
  (frToRepr (p := 17) (2 : Fr 17)).size == 32 &&
    frOfRepr? (p := 17) (frToRepr (p := 17) (2 : Fr 17)) == some (2 : Fr 17) &&
    frOfRepr? (p := 17) (frToRepr (p := 17) (16 : Fr 17)) == some (16 : Fr 17) &&
    frOfRepr? (p := 17) (natToBytesLE 17 32) == none &&
    (frToRepr (p := 17) (2 : Fr 17)).data[0]? == some 2 &&
    (frToRepr (p := 17) (2 : Fr 17)).data[1]? == some 0

#eval frReprKats_ok   -- expect true

/-- The two widths the law bundle pins, against the encoders they describe, and
    the 16-48-16-48 split of the EIP frame that eipShape asserts. A codec that
    emitted 47 compressed bytes would satisfy every algebraic law and still be
    wrong on the wire. -/
def codecWidthKats_ok : Bool :=
  g1CompressedWidth == 48 && g1EipWidth == 128 &&
    (natToBytesBE 0 16).size == 16 && (natToBytesBE 0 48).size == 48 &&
    (natToBytesBE 0 16).size + (natToBytesBE 0 48).size +
      (natToBytesBE 0 16).size + (natToBytesBE 0 48).size == g1EipWidth &&
    eipPad.size == 16 && (natToBytesBE 0 128).size == g1EipWidth

#eval codecWidthKats_ok   -- expect true


/-! ### Item 1 of P-CODEC-A: the decoder-first BYTE-level Fr repr round trip

    `frOfRepr? b = some x` implies `frToRepr x = b`. P-BYTES landed the
    ENCODER-FIRST value-level `frOfRepr_frToRepr` (above); this is the other
    direction, at byte level, and it is the half `decodeRust` needs: the decoder is
    handed raw bytes and has to know that re-encoding what it decoded reproduces
    them. Note there is NO `p <= 2^256` hypothesis here, unlike the encoder-first
    lemma: the decoder already rejected anything at or above `p`, so the value it
    returns is canonical by construction and the width bound is not needed - which
    is the same reason attack.md line 107 drops `hp` from
    `verifyNative_iff_msgs_codec`. This is the lemma that note was pointing at.

    THE RECORDED PREMISE THAT WAS HALF-WRONG. P-LOGCONCAT named the missing step as
    `natToBytesLE (bytesToNatLE b) b.size = b`, "provable from `lowDigits_go` plus a
    digits lemma". The lemma is right and it is provable, but NOT from
    `lowDigits_go`: the proof below never touches the emitter's digit list. What it
    needs instead is (a) `bytesToNatLE_eq_ofLowDigits` and `bytesToNatLE_natToBytesLE`,
    both already in Common/Bytes.lean, and (b) ONE new digit fact - that base-`b`
    positional notation is injective on equal-length digit lists
    (`ofLowDigits_inj`) - plus the matching bound (`ofLowDigits_lt_pow`) that says the
    reader's value is small enough for an emitter of the same width to reproduce.
    Third recorded premise in this chain found half-wrong; the substance survived and
    the named route did not. -/

private theorem bytes_toList_length (bs : Bytes) : bs.data.toList.length = bs.size :=
  Array.size_eq_length_toList (xs := bs.data)

private theorem natToBytesLE_toList_length (n len : Nat) :
    (natToBytesLE n len).data.toList.length = len :=
  ((bytes_toList_length (natToBytesLowFirst n len)).trans (natToBytesLowFirst_size n len))

/-- A base-`b` digit list whose digits are all `< b` has value below `b ^ length`:
    small enough for an emitter of that width to reproduce it exactly. -/
theorem ofLowDigits_lt_pow {b : ℕ} (_hb : 0 < b) : ∀ (l : List ℕ),
    (∀ d ∈ l, d < b) → ofLowDigits b l < b ^ l.length := by
  intro l
  induction l with
  | nil => intro _; rw [ofLowDigits_nil]; simp
  | cons d t ih =>
      intro h
      have hd : d < b := h d List.mem_cons_self
      have ht : ∀ x ∈ t, x < b := fun x hx => h x (List.mem_cons_of_mem d hx)
      have hV := ih ht
      have h1 : d + 1 ≤ b := Nat.succ_le_of_lt hd
      have h2 : ofLowDigits b t + 1 ≤ b ^ t.length := Nat.succ_le_of_lt hV
      have h3 : b * (ofLowDigits b t + 1) ≤ b * b ^ t.length := Nat.mul_le_mul_left b h2
      have h4 : b * (ofLowDigits b t + 1) = b * ofLowDigits b t + b := by
        rw [Nat.mul_add, Nat.mul_one]
      have hpow : b ^ (d :: t).length = b * b ^ t.length := by
        rw [List.length_cons, Nat.pow_succ']
      rw [ofLowDigits_cons, hpow]
      have h5 : d + b * ofLowDigits b t + 1 ≤ b * b ^ t.length := by
        calc d + b * ofLowDigits b t + 1 = (d + 1) + b * ofLowDigits b t := by omega
          _ ≤ b + b * ofLowDigits b t := Nat.add_le_add_right h1 _
          _ = b * (ofLowDigits b t + 1) := by rw [h4]; omega
          _ ≤ b * b ^ t.length := h3
      omega

/-- **Positional notation is unique**: two equal-length lists of digits `< b` with the
    same value are the same list. This is the digits lemma the repr round trip was
    missing, and the length hypothesis is load-bearing - `[0]` and `[0, 0]` have the
    same value at every base, which `frReprBytesKats_ok` pins by computation. -/
theorem ofLowDigits_inj {b : ℕ} (hb : 1 < b) : ∀ (l l' : List ℕ),
    (∀ d ∈ l, d < b) → (∀ d ∈ l', d < b) → l.length = l'.length →
    ofLowDigits b l = ofLowDigits b l' → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' _ _ hlen _
      cases l'
      · rfl
      · simp at hlen
  | cons d t ih =>
      intro l' hd hl' hlen heq
      cases l'
      · simp at hlen
      · next d' t' =>
          have h1 : ofLowDigits b (d :: t) = d + b * ofLowDigits b t := rfl
          have h2 : ofLowDigits b (d' :: t') = d' + b * ofLowDigits b t' := rfl
          rw [h1, h2] at heq
          have hdv : d < b := hd d List.mem_cons_self
          have hdv' : d' < b := hl' d' List.mem_cons_self
          have hlen' : t.length = t'.length := by simpa using hlen
          have hleft : (d + b * ofLowDigits b t) % b = d := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdv]
          have hright : (d' + b * ofLowDigits b t') % b = d' := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdv']
          have hmod : (d + b * ofLowDigits b t) % b = (d' + b * ofLowDigits b t') % b :=
            congrArg (fun x => x % b) heq
          rw [hleft, hright] at hmod
          have hrest : b * ofLowDigits b t = b * ofLowDigits b t' := by omega
          have hV : ofLowDigits b t = ofLowDigits b t' :=
            Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_one.trans hb) hrest
          have hdd : d = d' := hmod
          subst hdd
          have hsame := ih t' (fun x hx => hd x (List.mem_cons_of_mem d hx))
            (fun x hx => hl' x (List.mem_cons_of_mem d hx)) hlen' hV
          exact congrArg (List.cons d) hsame

/-- Reading a byte list as `Nat`s is injective: the `UInt8` is recoverable from its
    value, which is what lets the digit argument end at the byte array. -/
private theorem uint8_toNat_map_inj : ∀ {l l' : List UInt8},
    l.map UInt8.toNat = l'.map UInt8.toNat → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l'
      · rfl
      · simp at h
  | cons a t ih =>
      intro l' h
      cases l'
      · simp at h
      · next b t' =>
          simp only [List.map_cons] at h
          obtain ⟨h1, h2⟩ := List.cons.inj h
          have hab : a = b := UInt8.toNat_inj.mp h1
          subst hab
          exact congrArg (List.cons a) (ih h2)

private theorem digits_lt_map (l : List UInt8) :
    ∀ y ∈ l.map UInt8.toNat, y < 256 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact UInt8.toNat_lt x

/-- **The byte half of the decoder-first round trip**, the step P-LOGCONCAT named:
    re-encoding what the little-endian reader read gives back the SAME bytes, at the
    width the string actually has. It holds at every width, not just 32 - the
    truncation in `bytesToNatLE_natToBytesLE` is exactly what a reader of that width
    cannot produce, so no side condition is needed. -/
theorem natToBytesLE_bytesToNatLE (b : Bytes) : natToBytesLE (bytesToNatLE b) b.size = b := by
  have hsz : b.size = (b.data.toList.map UInt8.toNat).length := by
    rw [List.length_map]
    exact (bytes_toList_length b).symm
  have hb : bytesToNatLE b < 256 ^ b.size := by
    rw [bytesToNatLE_eq_ofLowDigits, hsz]
    refine ofLowDigits_lt_pow (by decide) _ (digits_lt_map b.data.toList)
  have hlen : (natToBytesLE (bytesToNatLE b) b.size).data.toList.length =
      b.data.toList.length := by
    rw [natToBytesLE_toList_length, bytes_toList_length]
  have hmap : (natToBytesLE (bytesToNatLE b) b.size).data.toList.map UInt8.toNat
      = b.data.toList.map UInt8.toNat := by
    refine ofLowDigits_inj (by decide) _ _ (digits_lt_map _) (digits_lt_map _) ?_ ?_
    · rw [List.length_map, List.length_map, hlen]
    · rw [← bytesToNatLE_eq_ofLowDigits, bytesToNatLE_natToBytesLE, Nat.mod_eq_of_lt hb,
        ← bytesToNatLE_eq_ofLowDigits]
  apply ByteArray.ext
  rw [← Array.toList_inj]
  exact uint8_toNat_map_inj hmap

/-- **Item 1.** The decoder-first byte-level Fr repr round trip: whatever `frOfRepr?`
    accepts, `frToRepr` re-emits byte for byte. No `p <= 2^256` hypothesis, in
    contrast with `frOfRepr_frToRepr` above: the canonicity test inside `frOfRepr?`
    already forces `bytesToNatLE b < p`, so the decoded value is the value the bytes
    spell. This is what `decodeRust` needs to re-serialise a `Msg.fr` it decoded from
    a log record. -/
theorem frOfRepr_frToRepr_bytes {p : ℕ} [Fact (Nat.Prime p)] {b : Bytes} {x : Fr p}
    (h : frOfRepr? (p := p) b = some x) : frToRepr x = b := by
  rw [frOfRepr?] at h
  by_cases hc : (b.size == 32 && bytesToNatLE b < p)
  · have hcs : b.size = 32 ∧ bytesToNatLE b < p := by simpa using hc
    rw [if_pos hc] at h
    have hval : x.val = bytesToNatLE b := by
      have hx := Option.some.inj h
      rw [← hx, ZMod.val_natCast, Nat.mod_eq_of_lt hcs.2]
    show natToBytesLE x.val 32 = b
    rw [hval, ← hcs.1]
    exact natToBytesLE_bytesToNatLE b
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- D-P23 satisfiability for `frOfRepr_frToRepr_bytes`: the hypothesis is inhabited,
    and the conclusion holds of a real 32-byte string. -/
theorem frOfRepr_bytes_witness :
    ∃ (b : Bytes) (x : Fr 17), frOfRepr? (p := 17) b = some x ∧ frToRepr (p := 17) x = b := by
  refine ⟨frToRepr (p := 17) (5 : Fr 17), 5, ?_, ?_⟩
  · exact frOfRepr_frToRepr (by decide) 5
  · rfl

/-- D-P23 falsification, as a THEOREM: the canonicity test inside `frOfRepr?` is what
    makes the conclusion true. Here is a 32-byte string whose value is NOT below `p`:
    the naive decoder that drops the `< p` test still answers `some x` for the cast of
    that value, and the re-encoding of that `x` is not the string it read. So item 1
    is a fact about a CANONICAL decoder, not about any function of 32 bytes. -/
theorem frOfRepr_bytesRefutesNonCanonical :
    ∃ (b : Bytes) (x : Fr 17), b.size = 32 ∧ x = (bytesToNatLE b : Fr 17) ∧
      frToRepr (p := 17) x ≠ b := by
  refine ⟨natToBytesLE 17 32, 0, rfl, by decide, by decide⟩

/-- D-P23 falsification, as a THEOREM: the width argument in
    `natToBytesLE (bytesToNatLE b) b.size = b` is the string's own size, not a
    constant that happens to be nearby. At 31 bytes the same reader-emitter pair
    cannot reproduce a 32-byte string, so the `b.size = 32` hypothesis inside
    `frOfRepr?` is doing real work rather than being decorative. -/
theorem frOfRepr_bytesRefutesWrongWidth :
    ∃ (b : Bytes), b.size = 32 ∧ natToBytesLE (bytesToNatLE b) 31 ≠ b := by
  refine ⟨natToBytesLE 256 32, natToBytesLowFirst_size _ _, ?_⟩
  intro h
  have h1 := congrArg ByteArray.size h
  have h2 : (natToBytesLE (bytesToNatLE (natToBytesLE 256 32)) 31).size = 31 :=
    natToBytesLowFirst_size _ _
  rw [h2, show ByteArray.size (natToBytesLE 256 32) = 32 from natToBytesLowFirst_size _ _] at h1
  exact absurd h1 (by decide)

/-- D-P23, computed: the decoder-first byte round trip on real reprs at `p = 17`, the
    two negative controls the theorems above state, and the equal-length hypothesis of
    `ofLowDigits_inj`. -/
def frReprBytesKats_ok : Bool :=
  let b := frToRepr (p := 17) (5 : Fr 17)
  (match frOfRepr? (p := 17) b with
   | some x => frToRepr (p := 17) x == b
   | none => false) &&
  (natToBytesLE (bytesToNatLE b) b.size == b) &&
  (b.size == 32) &&
  (let c := natToBytesLE 16 32;
    match frOfRepr? (p := 17) c with
    | some x => frToRepr (p := 17) x == c
    | none => false) &&
  (frOfRepr? (p := 17) (natToBytesLE 17 32) == none) &&
  (frToRepr (p := 17) (17 : Fr 17) != natToBytesLE 17 32) &&
  (natToBytesLE (bytesToNatLE (natToBytesLE 256 32)) 31 != natToBytesLE 256 32) &&
  (ofLowDigits 256 [0] == ofLowDigits 256 [0, 0])

#eval frReprBytesKats_ok   -- expect true

end Midfall.Assumptions