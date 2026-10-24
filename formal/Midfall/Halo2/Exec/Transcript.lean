-- |
-- Midfall.Halo2.Exec.Transcript
--
-- Faithful port of the Keccak transcript (plan Section 4 module map, row
-- transcript/{mod,implementors}.rs): CircuitTranscript<Keccak256> only.
--
-- The three facts the port turns on, each read off the Rust:
--
-- 1. absorb is update, and squeeze finalises a *clone* and then reseeds the
--    state from the digest it just returned (implementors.rs:198-212). So
--    the hasher is exactly the byte string absorbed so far, and the
--    transcript state can be a Bytes rather than an incremental sponge.
-- 2. read decodes a fixed-width repr from the proof buffer and then absorbs
--    to_input of the *decoded value*, not the bytes that encoded it
--    (mod.rs:134-138). Transcript malleability therefore shows up as a
--    decode failure or a to_input collision, never as a raw-byte
--    difference.
-- 3. assert_empty compares the cursor position with the buffer length and
--    fails with ErrorKind::NotFound (mod.rs:150-159) - a different io kind
--    from the UnexpectedEof a short read produces, which is why
--    IoErrorKind has both.
--
-- Out of scope by plan Section 1: the blake2b transcript, and
-- TranscriptInputBytes (mod.rs:14-35), which exists only for the verifier
-- trace hooks.

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Keccak
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- rust: proofs/src/transcript/mod.rs:52-63 (trait Hashable<H>), with
    H = Keccak256 whose Input = Output = Vec<u8> (implementors.rs:186-187).
    Rule R9: the trait becomes a structure of functions. width is the length
    of the Rust Repr type, which is what read_exact consumes. -/
structure Hashable (T : Type) where
  /-- rust: to_input. What the transcript absorbs. -/
  toInput : T → Bytes
  /-- rust: to_bytes. What the proof stream carries (prover side; kept
      because repack_proof in the generator has to reproduce it exactly). -/
  toBytes : T → Bytes
  /-- rust: the associated Repr length: 48 for a compressed G1 point, 32 for
      a scalar, 4 for a u32. -/
  width : Nat
  /-- rust: the body of read after read_exact: from_bytes / from_repr as an
      Option. none is the io::Error::other arm. -/
  readRepr? : Bytes → Option T

/-- rust: proofs/src/transcript/implementors.rs:314-345
    (Hashable<Keccak256> and Sampleable<Keccak256> for midnight_curves::Fq,
    i.e. the scalar field). Wire format little-endian (to_repr), absorbed
    format big-endian (the reversed repr). -/
def hashableFr {p : ℕ} [Fact (Nat.Prime p)] : Hashable (Fr p) where
  toInput := frToInputBE
  toBytes := frToRepr
  width := 32
  readRepr? := frOfRepr?

/-- rust: proofs/src/transcript/implementors.rs:263-311
    (Hashable<Keccak256> for midnight_curves::G1Projective): absorbed as the
    128-byte EIP-2537 padded uncompressed form, transmitted as the 48-byte
    compressed form. The codecs come from G1Codec (design decision D-P6). -/
def hashableG1 {G₁ : Type} (c : G1Codec G₁) : Hashable G₁ where
  toInput := c.toEip
  toBytes := c.toCompressed
  width := g1CompressedWidth
  readRepr? := c.ofCompressed?

/-- rust: proofs/src/transcript/implementors.rs:65-76 (Hashable<T> for u32),
    reached by the committed-instance count. Little-endian on the wire and in
    the absorb. The port uses Nat for a u32 and does not emulate the width: a
    value above 2^32 cannot come from a 4-byte read. -/
def hashableU32 : Hashable Nat where
  toInput := fun n => natToBytesLE n 4
  toBytes := fun n => natToBytesLE n 4
  width := 4
  readRepr? := fun b => if b.size == 4 then some (bytesToNatLE b) else none

/-- rust: proofs/src/transcript/mod.rs:104-108
    CircuitTranscript<Keccak256> { state: Keccak256, buffer: Cursor<Vec<u8>> }.

    state is the byte string fed to the hasher (fact 1 above); buffer and pos
    are the cursor Vec<u8> and its position(). -/
structure Transcript where
  state : Bytes
  buffer : Bytes
  pos : Nat
  /-- The hash the squeeze step uses. Rule R9 says the hash is a parameter
      everywhere, defaulting to keccak256 - the default keeps every existing call
      site and the frozen 9.2 statements unchanged, while prepareMsgs can honour an
      arbitrary H. -/
  hash : Bytes → H256 := keccak256
  /-- Every read the verifier performed, as (wire width, raw bytes), in order.

      This exists so that decodeRust is DERIVED from the schedule instead of being
      a second copy of it. Duplicating a read schedule is the exact failure mode
      of docs/REVIEW.md R-30 and R-32, where a paraphrased loop or a normalisation
      applied in one of two places silently changed the transcript. Recording what
      the pipeline actually consumed makes that class of bug impossible in the
      decoder. -/
  log : Array (Nat × Bytes) := #[]

/-- The transcript state monad with the verifier failure type (plan 9.2). -/
abbrev TranscriptM := StateT Transcript (Except Fault)

/-- rust: proofs/src/transcript/mod.rs:117-124 (init and init_from_bytes).
    A fresh Keccak256 has absorbed nothing, so state is empty. -/
def Transcript.initFromBytes (bytes : Bytes) : Transcript :=
  { state := Bytes.empty, buffer := bytes, pos := 0 }

/-- The same, with an explicit hash (rule R9). Used by prepareMsgs, which must
    honour whatever H it is given rather than keccak256. -/
def Transcript.initWithHash (H : Bytes -> H256) (bytes : Bytes) : Transcript :=
  { state := Bytes.empty, buffer := bytes, pos := 0, hash := H }

/-- rust: proofs/src/transcript/mod.rs:126-128 common + implementors.rs
    194-196 absorb = update. -/
def Transcript.common {T : Type} (h : Hashable T) (t : Transcript) (input : T) :
    Transcript :=
  { t with state := ByteArray.append t.state (h.toInput input) }

/-- rust: implementors.rs:198-212 squeeze: the digest of the state absorbed
    so far, then the state is *replaced* by that digest (a new hasher seeded
    with out). Returns the digest bytes and the new state. -/
def Transcript.squeeze (t : Transcript) : Bytes × Transcript :=
  let d := wordToBytesBE (t.hash t.state)
  (d, { t with state := d })

/-- rust: proofs/src/transcript/mod.rs:126 squeeze_challenge::<Fq> composed
    with Sampleable<Keccak256> for Fq (implementors.rs:347-351), i.e.
    sample_keccak_digest_be_mod_r (implementors.rs:20-39). The Rust asserts
    the digest is 32 bytes; squeeze builds it from a BitVec 256, so that
    assertion is discharged by construction and is not a panic site. -/
def Transcript.squeezeChallenge {p : ℕ} [Fact (Nat.Prime p)] (t : Transcript) :
    Fr p × Transcript :=
  let (d, t2) := t.squeeze
  (frOfDigest (bytesToWordBE d), t2)

/-- rust: proofs/src/transcript/mod.rs:134-138 read: decode from the cursor,
    then common. A short read is ErrorKind::UnexpectedEof and a failed decode
    is io::Error::other; both surface as Error::Transcript in the verifier
    (proofs/src/plonk/error.rs:33). -/
def Transcript.read {T : Type} (h : Hashable T) (t : Transcript) :
    Except Fault (T × Transcript) :=
  match bytesTake t.buffer t.pos h.width with
  | none => .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof))
  | some repr =>
      match h.readRepr? repr with
      | none => .error (Fault.error (Error.transcript IoErrorKind.other))
      | some val =>
          let t2 := { t with pos := t.pos + h.width, log := t.log.push (h.width, repr) }
          .ok (val, t2.common h val)

/-- rust: proofs/src/transcript/mod.rs:150-159 assert_empty. Note the kind is
    NotFound, and that the Rust compares length with position: a cursor that
    read past the end cannot happen, but trailing bytes can. -/
def Transcript.assertEmpty (t : Transcript) : Except Fault Unit :=
  if t.buffer.size == t.pos then .ok ()
  else .error (Fault.error (Error.transcript IoErrorKind.notFound))

/-- rust: proofs/src/transcript/mod.rs:181-183 read_n:
    (0..n).map(|_| transcript.read()).collect(), i.e. n values in order and
    the whole thing fails if any single read fails. -/
def Transcript.readN {T : Type} (h : Hashable T) (t : Transcript) (n : Nat) :
    Except Fault (Array T × Transcript) :=
  go t #[] n
where
  go : Transcript → Array T → Nat → Except Fault (Array T × Transcript)
    | t, acc, 0 => .ok (acc, t)
    | t, acc, m + 1 => do
        let (v, t2) ← t.read h
        go t2 (acc.push v) m
  termination_by _ _ n => n

/-- squeeze_challenge in the verifier monad (plan 9.2 TranscriptM). -/
def tmSqueezeChallenge {p : ℕ} [Fact (Nat.Prime p)] : TranscriptM (Fr p) := do
  let t ← StateT.get
  let (x, t2) := t.squeezeChallenge
  StateT.set t2
  pure x

/-- transcript.read() in the verifier monad. -/
def tmRead {T : Type} (h : Hashable T) : TranscriptM T := do
  let t ← StateT.get
  let (v, t2) ← StateT.lift (t.read h)
  StateT.set t2
  pure v

/-- transcript.common(&x) in the verifier monad. -/
def tmCommon {T : Type} (h : Hashable T) (input : T) : TranscriptM Unit := do
  let t ← StateT.get
  StateT.set (t.common h input)

/-- read_n(transcript, n) in the verifier monad. -/
def tmReadN {T : Type} (h : Hashable T) (n : Nat) : TranscriptM (Array T) := do
  let t ← StateT.get
  let (v, t2) ← StateT.lift (t.readN h n)
  StateT.set t2
  pure v


-- Known-answer and structural checks for the transcript port, as decidable
-- booleans in the style of keccak256_kats_ok. They pin exactly the three facts
-- in the header, which is where a port of this module is most likely to drift.
-- The conformance runner (plan Section 5) replays the same shapes against the
-- Rust trace; here they only have to be executable.

/-- a short read is UnexpectedEof (rust: mod.rs:135 via read_exact). -/
def transcriptKat_eof : Bool :=
  match (Transcript.initFromBytes (natToBytesLE 7 3)).read hashableU32 with
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
  | _ => false

/-- a full-width repr that *is* valid decodes to the value it encodes. The
    companion failure mode - a width that is present but not a valid repr, which
    Rust reports as io::Error::other - needs the scalar codec and so a concrete
    modulus; it is exercised by the conformance runner instead. -/
def transcriptKat_decode : Bool :=
  match (Transcript.initFromBytes (natToBytesLE (2^32 - 1) 4)).read hashableU32 with
  | .ok (v, _) => v == 2^32 - 1
  | .error _ => false

/-- a successful read returns the decoded value, advances the cursor by the
    repr width, and absorbs to_input rather than the repr bytes. -/
def transcriptKat_read : Bool :=
  let h := hashableU32
  match (Transcript.initFromBytes (natToBytesLE 7 4)).read h with
  | .ok (v, t) => v == 7 && t.pos == 4 && t.state == h.toInput 7
  | .error _ => false

/-- assert_empty: exact consumption is ok, trailing bytes are NotFound. -/
def transcriptKat_empty : Bool :=
  match (Transcript.initFromBytes Bytes.empty).assertEmpty with
  | .ok () => true
  | .error _ => false

def transcriptKat_trailing : Bool :=
  match (Transcript.initFromBytes (natToBytesLE 1 5)).assertEmpty with
  | .error (Fault.error (Error.transcript IoErrorKind.notFound)) => true
  | _ => false

/-- squeeze reseeds the state with its own digest, so the next digest is
    keccak of the previous one and not of the old state. -/
def transcriptKat_reseed : Bool :=
  let (d, t) := (Transcript.initFromBytes Bytes.empty).squeeze
  t.state == d && d.size == 32

def transcriptKat_chain : Bool :=
  let (_, t) := (Transcript.initFromBytes Bytes.empty).squeeze
  let (d2, _) := t.squeeze
  d2 == wordToBytesBE (keccak256 t.state)

/-- read_n reads n values in order and leaves the cursor after them. -/
def transcriptKat_readN : Bool :=
  let buf := natToBytesLE 1 4 ++ natToBytesLE 2 4 ++ natToBytesLE 3 4
  match (Transcript.initFromBytes buf).readN hashableU32 3 with
  | .ok (vs, t) => vs.size == 3 && t.pos == 12
  | .error _ => false

/-- A NON-CIRCULAR known-answer test for the whole squeeze path. Earlier checks
    compared wordToBytesBE against itself, so when that function was emitting
    little-endian bytes (docs/REVIEW.md R-20) they still passed. This one pins the
    digest of the empty state against the keccak256 of the empty input, byte for
    byte, in the order the transcript actually uses. -/
def transcriptKat_keccak : Bool :=
  let (d, t2) := (Transcript.initFromBytes Bytes.empty).squeeze
  -- keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
  (d.data.toList.map (fun x => x.toNat)) ==
    [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2,
     0xdc, 0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
     0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70] &&
  t2.state == d

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The challenge reduces the big-endian digest mod the field order
    undefined
    a low-byte truncation would give 254. Deliberately cheap - reducing the
    real 256-bit digest in the kernel blows the recursion limit, which is itself
    worth knowing before Phase 3 tries to run a Moonlight fixture natively
    (plan Section 13 flags exactly this performance risk). -/
def transcriptKat_challenge : Bool :=
  ZMod.val (frOfDigest (p := 17) (0xfe : H256)) == 16 &&
  ZMod.val (frOfDigest (p := 17) (0x11 : H256)) == 0

/-- frToInputBE absorbs the big-endian repr, i.e. the reverse of the wire repr
    (implementors.rs:316-324). If these two ever agree byte-for-byte the
    endianness bug (docs/REVIEW.md R-20) is back. 5 is used because it is
    canonical mod 17. -/
def codecKat_endianness : Bool :=
  let be := (frToInputBE (p := 17) 5).data.toList.map (fun x => x.toNat);
  let le := (frToRepr (p := 17) 5).data.toList.map (fun x => x.toNat);
  be ≠ le &&
  be.drop 31 == [5] &&
  le.take 1 == [5] &&
  (match frOfRepr? (p := 17) (frToRepr (p := 17) 5) with
   | some (x : Fr 17) => ZMod.val x == 5
   | none => false) &&
  -- non-canonical reprs are rejected (rule R7): 17 is congruent to 0, so the
  -- canonical repr of 0 is all-zeros and [17] must be refused
  (match frOfRepr? (p := 17) (natToBytesLE 17 32) with
   | none => true
   | some _ => false)
def transcriptKats_ok : Bool :=
  [ transcriptKat_eof, transcriptKat_decode, transcriptKat_read,
    transcriptKat_empty, transcriptKat_trailing, transcriptKat_reseed,
    transcriptKat_chain, transcriptKat_readN,
    transcriptKat_keccak, transcriptKat_challenge ].all id

#eval transcriptKats_ok   -- expect true

end Midfall.Halo2
