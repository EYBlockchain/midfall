-- |
-- Midfall.Generator.Layout
--
-- The memory-layout and payload-layout layer: `lowering/layout/vk_payload.rs`
-- in full, the memory-planner core of `lowering/layout/memory.rs`, and the two
-- `Halo2VerifyingKey` methods those files feed - `payload_layout` and
-- `validate_payload_layout` - which `Models.lean` deferred precisely because
-- these types did not exist yet.
--
-- It also carries the `pub(crate) mod trace` block of
-- `lowering/layout/mod.rs:774-786` - six LOG topic namespaces - because that
-- block is Layout-row material; `Midfall/Generator/Protocol.lean` re-exports two
-- of the six and cites `PM:` for the re-export only.
--
-- Citation prefixes this file introduces. Review R-40 F6 was a phantom citation
-- found in a file that used a bare prefix, so every cite below names the file it
-- came from as well:
--
-- * `VP:`  `proofs/solidity-verifier/src/lowering/layout/vk_payload.rs` (322 lines)
-- * `MEM:` `proofs/solidity-verifier/src/lowering/layout/memory.rs` (1603 lines)
-- * `LM:`  `proofs/solidity-verifier/src/lowering/layout/mod.rs` (927 lines)
-- * `M:`   `proofs/solidity-verifier/src/lowering/render/models.rs` (1494 lines)
--
-- Three porting decisions are recorded here rather than silently taken:
--
-- * `Vec` is modelled as `List`, following `Models.lean` and `Templates.lean`.
--   Every Vec operation the ported code uses - `iter`, `find`, `any`, `push`,
--   `chunks`, `skip` - is order-preserving and index-independent, so the two
--   readings agree on everything observable here.
-- * `usize` is modelled as `Nat`, which cannot wrap. The reference profile is
--   release (docs/REVIEW.md R-6), where `+` and `*` wrap rather than panic, so
--   a wrapped `usize` and a `Nat` differ only past `2^64 - 1`; every value that
--   flows through this layer is a word or byte count of a few kilobytes. The
--   Exactly one `checked_*` exists in the ported scope, the `checked_sub` at
--   M:346, and it is ported as written. The only `ok_or_else` in
--   `vk_payload.rs` (VP:139) is the missing-section error, not an overflow
--   check: every product in that file is a plain `*`. Unreachability is stated
--   at the site where it matters, not assumed.
-- * `#[cfg(test)]` items are ported where a ported test needs them - six of
--   them: `PayloadSection.byte_offset` (VP:44), `PayloadSection.byte_len`
--   (VP:50), `VkPayloadLayout.byte_offset` (VP:153), `VkPayloadLayout.byte_len`
--   (VP:159), `MemoryMap.region` (MEM:229) and
--   `PackedProgramCodec.decode_words` (VP:213) - and are marked as test-only at
--   the site, which is the convention `Exec/Circuit.lean` sets.

import Midfall.Common.Bytes
import Midfall.Generator.Models
import Midfall.Halo2.Exec.Error

namespace Midfall.Generator

/-! ## Constants from `lowering/layout/mod.rs` -/

/-- rust: LM:17 (`const WORD_BYTES: usize = 0x20`) @formal-baseline. The same
    fact `Midfall/Yul/Externals.lean` reaches from the EVM side; the cross-check
    `layoutConstants_matchYul_ok` below is what keeps the two ports from drifting. -/
def wordBytes : Nat := 0x20

/-- rust: LM:19 (`const SOLIDITY_SCRATCH_SPACE_BYTES`) @formal-baseline. -/
def solidityScratchSpaceBytes : Nat := 0x40

/-- rust: LM:21 (`const SOLIDITY_FREE_MEMORY_POINTER_SLOT`) @formal-baseline. -/
def solidityFreeMemoryPointerSlot : Nat := 0x40

/-- rust: LM:23 (`const SOLIDITY_ZERO_SLOT`) @formal-baseline. -/
def solidityZeroSlot : Nat := 0x60

/-- rust: LM:25 (`const SOLIDITY_ALLOCATABLE_MEMORY_START`) @formal-baseline. -/
def solidityAllocatableMemoryStart : Nat := 0x80

/-- rust: LM:27 (`const SOLIDITY_RESERVED_MEMORY_BYTES`) @formal-baseline. -/
def solidityReservedMemoryBytes : Nat := solidityAllocatableMemoryStart

/-- rust: LM:44 (`const LOW_MEMORY_SCRATCH_START: usize = 0x1000`)
    @formal-baseline. -/
def lowMemoryScratchStart : Nat := 0x1000

/-- rust: LM:59 (`const VK_CONSTRUCTOR_PAYLOAD_START`) @formal-baseline. -/
def vkConstructorPayloadStart : Nat := solidityAllocatableMemoryStart

/-- rust: LM:61 (`const FR_WORDS: usize = 1`) @formal-baseline. -/
def frWords : Nat := 1

/-- rust: LM:63 (`const G1_WORDS: usize = 4`) @formal-baseline. R2 would name
    this `g1Words`, which `Models.lean` already occupies for the function
    `g1_words` (M:178-181); the constant is `g1WordsCount` instead, and the
    collision is recorded here rather than resolved by renaming a ported def. -/
def g1WordsCount : Nat := 4

/-- rust: LM:65 (`const G2_WORDS: usize = 8`) @formal-baseline; same R2 collision
    note as `g1WordsCount`. -/
def g2WordsCount : Nat := 8

/-- rust: LM:67 (`const FR_BYTES`) @formal-baseline. -/
def frBytes : Nat := frWords * wordBytes

/-- rust: LM:69 (`const G1_BYTES`) @formal-baseline. -/
def g1Bytes : Nat := g1WordsCount * wordBytes

/-- rust: LM:71 (`const G2_BYTES`) @formal-baseline. -/
def g2Bytes : Nat := g2WordsCount * wordBytes

/-- rust: LM:80 (`const G1_MSM_PAIR_BYTES`) @formal-baseline. -/
def g1MsmPairBytes : Nat := g1Bytes + frBytes

/-- rust: LM:82 (`const G1ADD_INPUT_BYTES`) @formal-baseline. -/
def g1AddInputBytes : Nat := 2 * g1Bytes

/-- rust: LM:86-87 (`const MODEXP_FRAME_WORDS`, `const MODEXP_FRAME_BYTES`)
    @formal-baseline. The two Rust consts are one def here because the word
    count is used nowhere except to build the byte count. -/
def modexpFrameBytes : Nat := 6 * wordBytes

/-- rust: LM:92-93 (`const MODEXP_SCRATCH_WORDS`, `const MODEXP_SCRATCH_BYTES`)
    @formal-baseline; same collapsing note as `modexpFrameBytes`. -/
def modexpScratchBytes : Nat := 8 * wordBytes

/-- rust: LM:95 (`const PAIRING_PAIR_BYTES`) @formal-baseline. -/
def pairingPairBytes : Nat := g1Bytes + g2Bytes

/-- rust: LM:97 (`const PAIRING_TWO_PAIR_BYTES`) @formal-baseline. -/
def pairingTwoPairBytes : Nat := 2 * pairingPairBytes

/-- rust: LM:102 (`const ACC_MSM_MIN_SCRATCH_BYTES: usize = 0x7000`)
    @formal-baseline. -/
def accMsmMinScratchBytes : Nat := 0x7000

/-- rust: LM:108 (`const PCS_STATIC_WORKING_WORDS: usize = 32`)
    @formal-baseline. -/
def pcsStaticWorkingWords : Nat := 32

/-- rust: LM:110 (`const PAIRING_STATIC_WORKING_WORDS`) @formal-baseline. -/
def pairingStaticWorkingWords : Nat := pairingTwoPairBytes / wordBytes + 1

/-- rust: LM:395 (`const VK_HEADER_SCALAR_WORDS: usize = 11`)
    @formal-baseline. -/
def vkHeaderScalarWords : Nat := 11

/-- rust: LM:397 (`const VK_HEADER_G1_BASE_WORD`) @formal-baseline. -/
def vkHeaderG1BaseWord : Nat := vkHeaderScalarWords

/-- rust: LM:399 (`const VK_HEADER_G2_BASE_WORD`) @formal-baseline. -/
def vkHeaderG2BaseWord : Nat := vkHeaderG1BaseWord + g1WordsCount

/-- rust: LM:401 (`const VK_HEADER_NEG_S_G2_BASE_WORD`) @formal-baseline. -/
def vkHeaderNegSG2BaseWord : Nat := vkHeaderG2BaseWord + g2WordsCount

/-- rust: LM:445 (`const VK_HEADER_WORDS`) @formal-baseline. This is the
    `header_words` the reference's own layout tests pass to `for_vk`, so it is
    the number that ties `VkPayloadLayout.for_vk` to the header schema. -/
def vkHeaderWords : Nat := vkHeaderNegSG2BaseWord + g2WordsCount

/-- rust: MEM:374 (`usize::next_multiple_of(WORD_BYTES)`) @formal-baseline,
    the same standard-library call MEM:322 and MEM:539 make, so it is cited at
    its call sites rather than as an item of its own. Alignment 0 is a panic in
    Rust and cannot arise here because the only alignment passed is
    `WORD_BYTES`. -/
def alignUp (value align : Nat) : Nat :=
  (value + align - 1) / align * align

/-! ## `lowering/layout/vk_payload.rs` -/

/-- rust: VP:12-24 (`enum PayloadSectionKind`) @formal-baseline. The Rust also
    derives `PartialOrd`/`Ord`/`Hash`; no ported path orders or hashes a kind,
    so only `BEq` is derived here and `Ord` is derived for the record in the
    declaration order the Rust lists. -/
inductive PayloadSectionKind
  /-- VP:15: fixed VK header words, shared by embedded and external VK paths. -/
  | header
  /-- VP:17: deduplicated Fr constants for the compact quotient VM. -/
  | quotientConstants
  /-- VP:19: packed compact-VM bytecode words. -/
  | quotientProgram
  /-- VP:21: EIP-2537-padded fixed polynomial commitments. -/
  | fixedCommitments
  /-- VP:23: EIP-2537-padded permutation commitment bases. -/
  | permutationCommitments
  deriving BEq, Ord

/-- rust: VP:106 (`{kind:?}` in the duplicate-section message) @formal-baseline,
    the same rendering VP:139 uses, i.e. the constructor name the `Debug` derive
    of VP:12 produces. Every error message in this file that mentions a section
    kind goes through here, so a renamed constructor cannot quietly change a
    message the Rust tests match on. -/
def payloadSectionKindDebug : PayloadSectionKind → String
  | .header => "Header"
  | .quotientConstants => "QuotientConstants"
  | .quotientProgram => "QuotientProgram"
  | .fixedCommitments => "FixedCommitments"
  | .permutationCommitments => "PermutationCommitments"

/-- rust: VP:27-35 (`struct PayloadSection`) @formal-baseline. -/
structure PayloadSection where
  /-- VP:30: logical section kind. -/
  kind : PayloadSectionKind
  /-- VP:32: start word relative to the beginning of the VK payload. -/
  wordOffset : Nat
  /-- VP:34: length in EVM words. -/
  wordLen : Nat
  deriving BEq

/-- rust: VP:39-41 (`PayloadSection::word_end`) @formal-baseline. `usize`
    addition wraps in the release profile; a wrapped end word would have to come
    from an offset above `2^64`, which no VK payload does, so the wrap is not
    emulated (rule R5). -/
def PayloadSection.wordEnd (self : PayloadSection) : Nat :=
  self.wordOffset + self.wordLen

/-- rust: VP:44-47 (`PayloadSection::byte_offset`, `#[cfg(test)]`)
    @formal-baseline. Test-only in the reference; ported because
    `vk_payload.rs`'s own regression test asserts on it and that assertion is
    reproduced as a gate below. -/
def PayloadSection.byteOffset (self : PayloadSection) : Nat :=
  self.wordOffset * wordBytes

/-- rust: VP:50-53 (`PayloadSection::byte_len`, `#[cfg(test)]`)
    @formal-baseline; same test-only note as `PayloadSection.byteOffset`. -/
def PayloadSection.byteLen (self : PayloadSection) : Nat :=
  self.wordLen * wordBytes

/-- rust: VP:60-64 (`struct VkPayloadLayout`, `#[derive(Default)]`)
    @formal-baseline. -/
structure VkPayloadLayout where
  /-- VP:62: reserved sections, in reservation order. -/
  sections : List PayloadSection
  /-- VP:63: next free word. -/
  cursorWords : Nat
  deriving BEq

/-- rust: VP:60 (`#[derive(Default)]` on `VkPayloadLayout`) @formal-baseline:
    empty section list, cursor at zero. -/
def vkPayloadLayoutDefault : VkPayloadLayout :=
  { sections := [], cursorWords := 0 }

/-- rust: VP:68-70 (`VkPayloadLayout::new`) @formal-baseline. -/
def VkPayloadLayout.new : VkPayloadLayout := vkPayloadLayoutDefault

/-- rust: VP:100-117 (`VkPayloadLayout::reserve`) @formal-baseline. The Rust
    takes `&mut self` and returns `Result<PayloadSection, String>`; the
    receiver-passing reading returns the updated layout alongside the section,
    which is the same relation spelled functionally. -/
def VkPayloadLayout.reserve (self : VkPayloadLayout)
    (kind : PayloadSectionKind) (wordLen : Nat) :
    Except String (VkPayloadLayout × PayloadSection) :=
  if self.sections.any fun sec => sec.kind == kind then
    Except.error ("duplicate VK payload section: " ++ payloadSectionKindDebug kind)
  else
    let sec : PayloadSection :=
      { kind := kind, wordOffset := self.cursorWords, wordLen := wordLen }
    let next : VkPayloadLayout :=
      { sections := self.sections ++ [sec], cursorWords := self.cursorWords + wordLen }
    Except.ok (next, sec)

/-- rust: VP:120-126 (`VkPayloadLayout::reserve_g1`) @formal-baseline. The
    reference multiplies with plain `*` (release profile: wrapping, no panic),
    so there is no overflow arm to port; `Nat` cannot wrap either, so both
    readings agree on every input this layer can receive. -/
def VkPayloadLayout.reserveG1 (self : VkPayloadLayout)
    (kind : PayloadSectionKind) (commitments : Nat) :
    Except String (VkPayloadLayout × PayloadSection) :=
  self.reserve kind (commitments * g1WordsCount)

/-- rust: VP:129-131 (`VkPayloadLayout::section`) @formal-baseline. -/
def VkPayloadLayout.section (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Option PayloadSection :=
  self.sections.find? fun sec => sec.kind == kind

/-- rust: VP:134-140 (`VkPayloadLayout::require_section`) @formal-baseline. -/
def VkPayloadLayout.requireSection (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String PayloadSection :=
  match self.section kind with
  | some sec => Except.ok sec
  | none => Except.error ("missing VK payload section: " ++ payloadSectionKindDebug kind)

/-- rust: VP:143-145 (`VkPayloadLayout::word_offset`) @formal-baseline. -/
def VkPayloadLayout.wordOffset (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String Nat :=
  Except.map PayloadSection.wordOffset (self.requireSection kind)

/-- rust: VP:148-150 (`VkPayloadLayout::word_len`) @formal-baseline. -/
def VkPayloadLayout.wordLen (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String Nat :=
  Except.map PayloadSection.wordLen (self.requireSection kind)

/-- rust: VP:153-156 (`VkPayloadLayout::byte_offset`, `#[cfg(test)]`)
    @formal-baseline. The `Result` is `require_section`'s missing-section error
    (VP:139) propagated through `?`; the `word_offset * WORD_BYTES` underneath
    it (VP:46) is a plain `*`, with no overflow arm in the Rust to port. -/
def VkPayloadLayout.byteOffset (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String Nat :=
  Except.map PayloadSection.byteOffset (self.requireSection kind)

/-- rust: VP:159-162 (`VkPayloadLayout::byte_len`, `#[cfg(test)]`)
    @formal-baseline; same shape as `VkPayloadLayout.byteOffset` - the `Result`
    is `require_section`'s, the product at VP:52 is a plain `*`. -/
def VkPayloadLayout.byteLen (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String Nat :=
  Except.map PayloadSection.byteLen (self.requireSection kind)

/-- rust: VP:165-167 (`VkPayloadLayout::total_words`) @formal-baseline. -/
def VkPayloadLayout.totalWords (self : VkPayloadLayout) : Nat :=
  self.cursorWords

/-- rust: VP:170-172 (`VkPayloadLayout::total_bytes`) @formal-baseline. -/
def VkPayloadLayout.totalBytes (self : VkPayloadLayout) : Nat :=
  self.totalWords * wordBytes

/-- rust: VP:175-193 (`VkPayloadLayout::validate`) @formal-baseline. The first
    loop walks the sections in order checking each starts where the cursor of the
    walk has reached; the second check is the cursor agreement. -/
def VkPayloadLayout.validate (self : VkPayloadLayout) : Except String Unit := do
  let cursor ← validateSections self.sections 0
  if cursor != self.cursorWords then
    Except.error ("VK payload cursor mismatch: sections end at " ++ hashHex cursor
      ++ ", cursor is " ++ hashHex self.cursorWords)
where
  validateSections : List PayloadSection → Nat → Except String Nat
    | [], cursor => pure cursor
    | sec :: rest, cursor =>
      if sec.wordOffset != cursor then
        Except.error ("VK payload section " ++ payloadSectionKindDebug sec.kind
          ++ " starts at " ++ hashHex sec.wordOffset
          ++ ", expected " ++ hashHex cursor)
      else
        validateSections rest sec.wordEnd

/-- rust: VP:76-94 (`VkPayloadLayout::for_vk`) @formal-baseline. Placed after
    `validate` rather than in its Rust position directly after `new`, because it
    calls `reserve`, `reserve_g1` and `validate`: those three come after
    `for_vk` in the Rust and must come before their caller in Lean. -/
def VkPayloadLayout.forVk
    (headerWords quotientConstWords quotientProgramWords
      fixedCommitments permutationCommitments : Nat) :
    Except String VkPayloadLayout := do
  let (l1, _) ← VkPayloadLayout.new.reserve PayloadSectionKind.header headerWords
  let (l2, _) ← l1.reserve PayloadSectionKind.quotientConstants quotientConstWords
  let (l3, _) ← l2.reserve PayloadSectionKind.quotientProgram quotientProgramWords
  let (l4, _) ← l3.reserveG1 PayloadSectionKind.fixedCommitments fixedCommitments
  let (l5, _) ← l4.reserveG1 PayloadSectionKind.permutationCommitments permutationCommitments
  l5.validate
  Except.ok l5

/-- rust: VP:206 (`bytes: &[u8]`) @formal-baseline. A modelling helper rather
    than a Rust item: it is how this port reads the byte buffer whose chunk and
    extend steps the codec works through. -/
def bytesToList (bs : Bytes) : List Nat := bs.data.toList.map UInt8.toNat

/-- rust: VP:197 (`struct PackedProgramCodec`) @formal-baseline: a unit
    namespace, no fields. -/
structure PackedProgramCodec deriving BEq

/-- rust: VP:201-203 (`PackedProgramCodec::word_len_for_bytes`)
    @formal-baseline: `usize::div_ceil`. -/
def PackedProgramCodec.wordLenForBytes (byteLen : Nat) : Nat :=
  (byteLen + wordBytes - 1) / wordBytes

/-- rust: VP:209 (`chunks(WORD_BYTES).map(U256::from_be_slice)`)
    @formal-baseline, over a buffer whose length is already a whole number of
    words. The word count is passed in so the recursion is structural rather
    than on a `drop`. -/
def packedPackWords : List Nat → Nat → List Word256
  | _, 0 => []
  | l, n + 1 => (l.take wordBytes).foldl (fun acc b => acc * 256 + b) 0
      :: packedPackWords (l.drop wordBytes) n

/-- rust: VP:206-210 (`PackedProgramCodec::encode_words`) @formal-baseline.
    The Rust pads to a whole number of words with `resize` and then takes
    `chunks(WORD_BYTES)`, which - unlike `chunks_exact` - keeps the final
    partial chunk; after the resize there is no partial chunk, and the word count
    is exactly `word_len_for_bytes`. -/
def PackedProgramCodec.encodeWords (bytes : Bytes) : List Word256 :=
  let bs := bytesToList bytes
  packedPackWords
    (bs ++ List.replicate (PackedProgramCodec.wordLenForBytes bs.length * wordBytes - bs.length) 0)
    (PackedProgramCodec.wordLenForBytes bs.length)

/-- rust: VP:213-233 (`PackedProgramCodec::decode_words`, `#[cfg(test)]`)
    @formal-baseline. Test-only in the reference and ported because
    `vk_payload.rs`'s three codec tests run through it. -/
def PackedProgramCodec.decodeWords
    (words : List Word256) (byteLen : Nat) : Except String Bytes :=
  let capacity := words.length * wordBytes
  if byteLen > capacity then
    Except.error ("packed program byte length " ++ toString byteLen
      ++ " exceeds word capacity " ++ toString capacity)
  else
    let all := words.flatMap fun w => (wordToBytesBE w).data.toList.map UInt8.toNat
    if (all.drop byteLen).any (fun b => b != 0) then
      Except.error "packed program has non-zero padding bytes"
    else
      Except.ok (ByteArray.mk ((all.take byteLen).map Nat.toUInt8).toArray)

/-- A modelling helper rather than a Rust item: the five section offsets in the
    order `for_vk` reserves them (VP:84-91), which is the accessor shape the
    reference tests at M:1313-1324 and M:1282-1340 use through `word_offset`. -/
def vkPayloadSectionOffsets (layout : VkPayloadLayout) : List Nat :=
  [PayloadSectionKind.header, .quotientConstants, .quotientProgram,
    .fixedCommitments, .permutationCommitments].filterMap
    fun kind => Option.map (·.wordOffset) (layout.section kind)

/-! ## Memory-planner core from `lowering/layout/memory.rs` -/

/-- rust: MEM:121-155 (`enum MemoryPhase`) @formal-baseline. The Rust derives
    `Ord`; that ordering is observable only through the `BTreeMap` cursor in
    `ScratchAllocator`, and rule R6 turns that map into a list kept in this same
    order, so `Ord` is derived here in declaration order. -/
inductive MemoryPhase
  /-- MEM:124: generated verifying-key constructor return payload. -/
  | vkConstructorPayload
  /-- MEM:126: constructor-only precompile smoke tests. -/
  | constructorSmoke
  /-- MEM:128: streaming Fiat-Shamir buffer before generated VK memory is live. -/
  | transcript
  /-- MEM:130: single scalar inversion scratch used by the modexp wrapper. -/
  | scalarInv
  /-- MEM:132: batch inversion for Lagrange denominator terms. -/
  | lagrangeBatchInvert
  /-- MEM:134: compact quotient VM temps and stack. -/
  | quotientVm
  /-- MEM:136: historical fixed PCS windows rooted at `ROT_POINTS_MPTR`. -/
  | pcsFixed
  /-- MEM:138: source-address table used by the rolled q_eval fold. -/
  | pcsQEvalSourceTable
  /-- MEM:140: optional trace-only q_com MSM materialization. -/
  | pcsQComTrace
  /-- MEM:142: fused final PCS MSM input buffer. -/
  | pcsFinalMsm
  /-- MEM:144: low-memory PCS pairing input helpers. -/
  | pcsPairing
  /-- MEM:146: public-accumulator MSM input buffer. -/
  | accumulatorMsm
  /-- MEM:148: public-accumulator pairing-batch hash and two G1 frames. -/
  | accumulatorPairingBatch
  /-- MEM:150: final two-pair KZG pairing frame. -/
  | finalPairing
  /-- MEM:152: main verifier return word. -/
  | verifierReturn
  /-- MEM:154: standalone quotient evaluator output frame. -/
  | quotientReturn
  deriving BEq, Ord

/-- rust: MEM:157-165 (`enum MemoryLifetime`) @formal-baseline. -/
inductive MemoryLifetime
  /-- MEM:161: live after being written; must never overlap another live region. -/
  | permanent
  /-- MEM:164: live only during the named phase. -/
  | phase (memoryPhase : MemoryPhase)
  deriving BEq

/-- rust: MEM:169-174 (`MemoryLifetime::intersects`) @formal-baseline. Private
    in the reference. -/
def memoryLifetimeIntersects : MemoryLifetime → MemoryLifetime → Bool
  | .permanent, _ => true
  | _, .permanent => true
  | .phase lhs, .phase rhs => lhs == rhs

/-- rust: MEM:177-187 (`struct MemoryRegion`) @formal-baseline. -/
structure MemoryRegion where
  /-- MEM:180: stable human-readable name used in validation errors. -/
  name : String
  /-- MEM:182: start byte offset in EVM memory. -/
  start : Nat
  /-- MEM:184: length in bytes; zero-length regions are allowed. -/
  len : Nat
  /-- MEM:186: permanent or phase-bounded lifetime. -/
  lifetime : MemoryLifetime

/-- rust: MEM:191-203 (`MemoryRegion::new`) @formal-baseline. -/
def memoryRegionNew (name : String) (start len : Nat)
    (lifetime : MemoryLifetime) : MemoryRegion :=
  { name := name, start := start, len := len, lifetime := lifetime }

/-- rust: MEM:206-208 (`MemoryRegion::end`) @formal-baseline. Private in the
    reference. `start + len` cannot wrap for any address this planner emits, so
    the release-profile wrap is not emulated (rule R5). -/
def MemoryRegion.end (self : MemoryRegion) : Nat :=
  self.start + self.len

/-- rust: MEM:211-213 (`MemoryRegion::overlaps`) @formal-baseline. Private in
    the reference. -/
def MemoryRegion.overlaps (self other : MemoryRegion) : Bool :=
  self.len != 0 && other.len != 0 && self.start < other.end && other.start < self.end

/-- rust: MEM:216-219 (`struct MemoryMap`, `#[derive(Default)]`)
    @formal-baseline. -/
structure MemoryMap where
  /-- MEM:218: registered regions, in registration order. -/
  regions : List MemoryRegion

/-- rust: MEM:216 (`#[derive(Default)]` on `MemoryMap`) @formal-baseline. -/
def memoryMapDefault : MemoryMap := { regions := [] }

/-- rust: MEM:223-225 (`MemoryMap::push`) @formal-baseline. -/
def MemoryMap.push (self : MemoryMap) (region : MemoryRegion) : MemoryMap :=
  { regions := self.regions ++ [region] }

/-- rust: MEM:229-231 (`MemoryMap::region`, `#[cfg(test)]`) @formal-baseline.
    Test-only in the reference and ported because `memory.rs`'s constructor
    tests look regions up by name. -/
def MemoryMap.region (self : MemoryMap) (name : String) : Option MemoryRegion :=
  self.regions.find? fun region => region.name == name

/-- rust: MEM:238-268 (`MemoryMap::validate`, first loop) @formal-baseline:
    the Solidity-reserved-memory and word-alignment checks, in the source order
    that decides which error a bad map reports. The `debug_assert_eq!` at
    MEM:243-246 is compiled out in the reference profile (docs/REVIEW.md R-6),
    so it is recorded and not enforced. -/
def memoryMapValidateReserved : List MemoryRegion → Except String Unit
  | [] => pure ()
  | region :: rest =>
    if region.len != 0 && region.start < solidityReservedMemoryBytes then
      let reservedName :=
        if region.start < solidityScratchSpaceBytes then "scratch space"
        else if region.start < solidityZeroSlot then "free-memory pointer"
        else "zero slot"
      Except.error ("memory region " ++ region.name ++ " starts at "
        ++ hashHex region.start
        ++ ", inside Solidity-reserved " ++ reservedName
        ++ " memory [0x00.." ++ hashHex solidityReservedMemoryBytes ++ ")")
    else if region.start % wordBytes != 0 then
      Except.error ("memory region " ++ region.name
        ++ " starts at unaligned byte offset " ++ hashHex region.start)
    else if region.len % wordBytes != 0 then
      Except.error ("memory region " ++ region.name
        ++ " has unaligned length " ++ hashHex region.len)
    else
      memoryMapValidateReserved rest

/-- rust: MEM:273-285 (`for rhs in self.regions.iter().skip(idx + 1)`) -/
def memoryMapValidateAgainst : MemoryRegion → List MemoryRegion → Except String Unit
  | _, [] => pure ()
  | lhs, rhs :: rest =>
    if lhs.overlaps rhs && memoryLifetimeIntersects lhs.lifetime rhs.lifetime then
      Except.error ("memory region " ++ lhs.name ++ " [" ++ hashHex lhs.start
        ++ ".." ++ hashHex lhs.end ++ ") overlaps " ++ rhs.name
        ++ " [" ++ hashHex rhs.start ++ ".." ++ hashHex rhs.end ++ ")")
    else
      memoryMapValidateAgainst lhs rest

/-- rust: MEM:272-286 (`MemoryMap::validate`, second loop) @formal-baseline:
    the `enumerate()`/`skip(idx + 1)` pair is the strict upper triangle of the
    region list, in order. -/
def memoryMapValidatePairs : List MemoryRegion → Except String Unit
  | [] => pure ()
  | lhs :: rhs => do
    memoryMapValidateAgainst lhs rhs
    memoryMapValidatePairs rhs

/-- rust: MEM:234-289 (`MemoryMap::validate`) @formal-baseline: the two loops
    are separate definitions above, in the order that fixes which error a bad map
    reports. -/
def MemoryMap.validate (self : MemoryMap) : Except String Unit := do
  memoryMapValidateReserved self.regions
  memoryMapValidatePairs self.regions

/-- rust: MEM:292-295 (`struct MemoryArena`, `#[derive(Default)]`)
    @formal-baseline. -/
structure MemoryArena where
  /-- MEM:294: the map under construction. -/
  map : MemoryMap

/-- rust: MEM:292 (`#[derive(Default)]` on `MemoryArena`) @formal-baseline. -/
def memoryArenaDefault : MemoryArena := { map := memoryMapDefault }

/-- rust: MEM:300-309 (`MemoryArena::alloc_fixed`) @formal-baseline. -/
def MemoryArena.allocFixed (self : MemoryArena) (name : String)
    (start len : Nat) (lifetime : MemoryLifetime) : MemoryArena × Nat :=
  ({ map := self.map.push (memoryRegionNew name start len lifetime) }, start)

/-- rust: MEM:314-324 (`MemoryArena::alloc_after`) @formal-baseline. -/
def MemoryArena.allocAfter (self : MemoryArena) (name : String)
    (anchorStart anchorLen len : Nat) (lifetime : MemoryLifetime) : MemoryArena × Nat :=
  let start := alignUp (anchorStart + anchorLen) wordBytes
  self.allocFixed name start len lifetime

/-- rust: MEM:327-335 (`MemoryArena::alloc_phase_scratch`) @formal-baseline. -/
def MemoryArena.allocPhaseScratch (self : MemoryArena) (name : String)
    (start len : Nat) (phase : MemoryPhase) : MemoryArena × Nat :=
  self.allocFixed name start len (MemoryLifetime.phase phase)

/-- rust: MEM:352-354 (`MemoryArena::into_map`) @formal-baseline. -/
def MemoryArena.intoMap (self : MemoryArena) : MemoryMap := self.map

/-- rust: MEM:358-362 (`struct ScratchAllocator`) @formal-baseline. The Rust
    holds `&mut MemoryArena`; functionally that is the arena travelling with
    the allocator. `cursors` is the `BTreeMap<MemoryPhase, usize>` of R6, a
    list kept in `MemoryPhase` order. Only `entry(..).or_insert` and one
    overwrite are ever performed on it, neither of which observes the order, so
    the sorted-list reading is exact rather than an approximation. -/
structure ScratchAllocator where
  /-- MEM:359: the arena allocations are registered into. -/
  arena : MemoryArena
  /-- MEM:360: the base every phase cursor starts from. -/
  base : Nat
  /-- MEM:361: per-phase cursor, ordered by `MemoryPhase`. -/
  cursors : List (MemoryPhase × Nat)

/-- rust: MEM:343-349 (`MemoryArena::scratch_allocator`) @formal-baseline. -/
def MemoryArena.scratchAllocator (self : MemoryArena) (base : Nat) : ScratchAllocator :=
  { arena := self, base := base, cursors := [] }

/-- rust: MEM:372-373 (`self.cursors.entry(phase).or_insert(self.base)`) -/
def ScratchAllocator.cursor (self : ScratchAllocator) (phase : MemoryPhase) : Nat :=
  match self.cursors.find? (fun (p, _) => p == phase) with
  | some (_, cursor) => cursor
  | none => self.base

/-- rust: MEM:374 (`*cursor = value`), an insert-or-overwrite. -/
def ScratchAllocator.setCursor (self : ScratchAllocator)
    (phase : MemoryPhase) (value : Nat) : ScratchAllocator :=
  if self.cursors.any fun (p, _) => p == phase then
    { self with cursors := self.cursors.map fun (p, c) => if p == phase then (p, value) else (p, c) }
  else
    { self with cursors := insertCursor phase value self.cursors }
where
  insertCursor : MemoryPhase → Nat → List (MemoryPhase × Nat) → List (MemoryPhase × Nat)
    | phase, value, [] => [(phase, value)]
    | phase, value, x :: xs =>
      if compare phase x.1 != Ordering.gt then (phase, value) :: x :: xs
      else x :: insertCursor phase value xs

/-- rust: MEM:366-376 (`ScratchAllocator::alloc_phase_scratch`)
    @formal-baseline. Note the asymmetry the port must keep: the cursor advances
    to the next word boundary, while the registered region keeps the unrounded
    `len`. -/
def ScratchAllocator.allocPhaseScratch (self : ScratchAllocator)
    (name : String) (len : Nat) (phase : MemoryPhase) : ScratchAllocator × Nat :=
  let start := self.cursor phase
  let next := { self with
    cursors := (ScratchAllocator.setCursor self phase (alignUp (start + len) wordBytes)).cursors }
  let (arena', reached) := next.arena.allocPhaseScratch name start len phase
  ({ next with arena := arena' }, reached)

/-- rust: MEM:528-533 (`struct VkConstructorMemoryLayout`) @formal-baseline. -/
structure VkConstructorMemoryLayout where
  /-- MEM:530: the constructor's own memory map. -/
  map : MemoryMap
  /-- MEM:532: constructor return-runtime buffer. -/
  payloadMptr : Nat

/-- rust: MEM:537-550 (`VkConstructorMemoryLayout::new`) @formal-baseline. -/
def VkConstructorMemoryLayout.new (runtimeLen : Nat) : VkConstructorMemoryLayout :=
  let arena := memoryArenaDefault
  let reservedLen := alignUp runtimeLen wordBytes
  let (arena', payloadMptr) :=
    arena.allocPhaseScratch "vk_constructor_payload" vkConstructorPayloadStart
      reservedLen MemoryPhase.vkConstructorPayload
  { map := arena'.intoMap, payloadMptr := payloadMptr }

/-- rust: MEM:553-561 (`VkConstructorMemoryLayout::validate`) @formal-baseline. -/
def VkConstructorMemoryLayout.validate
    (self : VkConstructorMemoryLayout) : Except String Unit := do
  if self.payloadMptr != vkConstructorPayloadStart then
    Except.error ("VK constructor payload pointer drifted: got "
      ++ hashHex self.payloadMptr
      ++ ", expected " ++ hashHex vkConstructorPayloadStart)
  self.map.validate

/-! ## `Halo2VerifyingKey` methods those two files feed -/

/-- rust: M:344-378 (`Halo2VerifyingKey::payload_layout`) @formal-baseline.
    The `checked_sub` at M:346 is a real error path - a VK whose constant table
    is shorter than its own quotient sections - so it is ported as a check and
    not as saturating `Nat` subtraction. -/
def Halo2VerifyingKey.payloadLayout (self : Halo2VerifyingKey) :
    Except String VkPayloadLayout := do
  let quotientWords := self.quotientConstWords + self.quotientProgramWords
  let constantsLen := self.constants.length
  let headerWords ←
    if quotientWords ≤ constantsLen then
      pure (constantsLen - quotientWords)
    else
      Except.error ("VK constant table too short: constants=" ++ toString constantsLen
        ++ " quotient_words=" ++ toString quotientWords)
  let layout ←
    VkPayloadLayout.forVk headerWords self.quotientConstWords
      self.quotientProgramWords self.fixedComms.length self.permutationComms.length
  match self.quotientConstOffsetWords with
  | none => pure ()
  | some offset =>
    let expected ← layout.wordOffset PayloadSectionKind.quotientConstants
    if offset != expected then
      Except.error ("quotient const offset mismatch: got " ++ hashHex offset
        ++ ", expected " ++ hashHex expected)
  match self.quotientProgramOffsetWords with
  | none => pure ()
  | some offset =>
    let expected ← layout.wordOffset PayloadSectionKind.quotientProgram
    if offset != expected then
      Except.error ("quotient program offset mismatch: got " ++ hashHex offset
        ++ ", expected " ++ hashHex expected)
  Except.ok layout

/-- rust: M:381-399 (`Halo2VerifyingKey::validate_payload_layout`)
    @formal-baseline. -/
def Halo2VerifyingKey.validatePayloadLayout (self : Halo2VerifyingKey) :
    Except String Unit := do
  let layout ← self.payloadLayout
  if layout.totalBytes != self.len then
    Except.error ("VK payload byte length mismatch: layout="
      ++ toString layout.totalBytes ++ " bytes rendered=" ++ toString self.len
      ++ " bytes")
  let constructorMemory := VkConstructorMemoryLayout.new self.runtimeLen
  constructorMemory.validate
  if self.constructorPayloadMptr != constructorMemory.payloadMptr then
    Except.error ("VK constructor payload pointer mismatch: got "
      ++ hashHex self.constructorPayloadMptr ++ ", expected "
      ++ hashHex constructorMemory.payloadMptr)

/-! ## Verifier memory layout

`VerifierMemoryLayout` is the record `Halo2Verifier` and `Halo2QuotientEvaluator`
carry as their `Memory` parameter, and `VerifierMemoryLayout::validate` is the
first thing both deferred `validate_layout` methods call.

`VerifierMemoryLayout::new` (MEM:591-973) IS now ported - in `LayoutMemory.lean`,
not here, and not because of file size. Its first parameter is `ConstraintSystemMeta`,
declared at Encoding.lean:364, and Encoding.lean imports THIS file directly
(Encoding.lean:158, and again through Abi.lean:99 and Protocol.lean:93), so `new`
right that the two argument types exist and incomplete about where: they exist
downstream of this file, not beside it. What is ported here remains the record, its
config and the validator - the part M:830 and M:965 need, and the part testable
against the reference's own fixed addresses without a meta in scope.
`LayoutMemory.lean` adds the constructor, `commitment_g1_count` (MEM:1080-1088)
and the two batch-inversion helpers (MEM:1099-1117), which is what lets Vk.lean's
`VkBuildEnv.newVerifierMemoryLayout` shim be retired. -/

def transcriptBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:48 (`PCS_PAIRING_SCRATCH_START`) @formal-baseline. -/
def pcsPairingScratchStart : Nat := lowMemoryScratchStart

/-- rust: LM:50 (`VERIFIER_RETURN_BUFFER_START`) @formal-baseline. -/
def verifierReturnBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:52 (`QUOTIENT_RETURN_BUFFER_START`) @formal-baseline. -/
def quotientReturnBufferStart : Nat := lowMemoryScratchStart

/-- rust: LM:313 (`accumulator::PAIRING_BATCH_PTR`) @formal-baseline. -/
def accumulatorPairingBatchPtr : Nat := lowMemoryScratchStart

/-- rust: LM:348 (`accumulator::PAIRING_BATCH_HASH_BYTES`) @formal-baseline.
    Tag word, `vk_digest` word, then four G1 points, which is why the frame ends
    at `0x1240` rather than `0x1220` (LM:113-115). -/
def accumulatorPairingBatchHashBytes : Nat := 2 * wordBytes + 4 * g1Bytes

/-- rust: LM:121-122 (`FINAL_PAIRING_SCRATCH_START`) @formal-baseline. -/
def finalPairingScratchStart : Nat := accumulatorPairingBatchPtr
  + accumulatorPairingBatchHashBytes

/-- rust: LM:668-725 (`enum ThetaSlot`, `#[repr(usize)]`) @formal-baseline. The
    discriminants are explicit in the Rust, so they are ported as an explicit
    table in `ThetaSlot.word` rather than as Lean's implicit constructor order;
    the jumps (33 to 38, 40 to 44) and the gaps between the G1 slots are the
    historical padding LM:45-66 describes. -/
inductive ThetaSlot where
  | theta | beta | gamma | trashChallenge | y | x | x1 | x2 | x3 | x4
  | fCom | pi | accLhs | accRhs | xN | xNMinus1Inv | lLast | lBlind | l0
  | instanceEval | quotientEval | quotient | fEval | v | finalCom
  | pairingLhs | pairingRhs

/-- rust: LM:729-731 (`ThetaSlot::word`, `self as usize`) @formal-baseline, read
    against the discriminants of LM:672-724. -/
def ThetaSlot.word : ThetaSlot → Nat
  | .theta => 0
  | .beta => 1
  | .gamma => 2
  | .trashChallenge => 3
  | .y => 4
  | .x => 5
  | .x1 => 6
  | .x2 => 7
  | .x3 => 8
  | .x4 => 9
  | .fCom => 10
  | .pi => 14
  | .accLhs => 18
  | .accRhs => 22
  | .xN => 26
  | .xNMinus1Inv => 27
  | .lLast => 28
  | .lBlind => 29
  | .l0 => 30
  | .instanceEval => 31
  | .quotientEval => 32
  | .quotient => 33
  | .fEval => 38
  | .v => 39
  | .finalCom => 40
  | .pairingLhs => 44
  | .pairingRhs => 48

/-- rust: LM:745 (`theta_window::ROT_POINTS_CAP_WORDS`) @formal-baseline. -/
def thetaRotPointsCapWords : Nat := 28

/-- rust: LM:747 (`theta_window::X1_POWERS_CAP_WORDS`) @formal-baseline. -/
def thetaX1PowersCapWords : Nat := 65

/-- rust: LM:749 (`theta_window::Q_EVAL_SET_CAP_WORDS`) @formal-baseline. -/
def thetaQEvalSetCapWords : Nat := 56

/-- rust: LM:751 (`theta_window::Q_EVAL_CPTR_PADDING_WORDS`) @formal-baseline. -/
def thetaQEvalCptrPaddingWords : Nat := 7

/-- rust: LM:753 (`theta_window::G1_IDENTITY_PADDING_WORDS`) @formal-baseline. -/
def thetaG1IdentityPaddingWords : Nat := 7

/-- rust: LM:756 (`theta_window::ROT_POINTS_WORD`) @formal-baseline. -/
def thetaRotPointsWord : Nat := ThetaSlot.pairingRhs.word + g1WordsCount

/-- rust: LM:758 (`theta_window::X1_POWERS_WORD`) @formal-baseline. -/
def thetaX1PowersWord : Nat := thetaRotPointsWord + thetaRotPointsCapWords

/-- rust: LM:760 (`theta_window::Q_COM_WORD`) @formal-baseline. -/
def thetaQComWord : Nat := thetaX1PowersWord + thetaX1PowersCapWords

/-- rust: LM:762 (`theta_window::Q_EVAL_SET_WORD`) @formal-baseline. -/
def thetaQEvalSetWord : Nat := thetaQComWord

/-- rust: LM:764 (`theta_window::Q_COM_CAP_WORDS`) @formal-baseline. The window
    aliases q_eval_set, so this is definitionally zero. -/
def thetaQComCapWords : Nat := thetaQEvalSetWord - thetaQComWord

/-- rust: LM:766 (`theta_window::Q_EVAL_CPTR_WORD`) @formal-baseline. -/
def thetaQEvalCptrWord : Nat := thetaQEvalSetWord + thetaQEvalSetCapWords

/-- rust: LM:768 (`theta_window::G1_IDENTITY_WORD`) @formal-baseline. -/
def thetaG1IdentityWord : Nat := thetaQEvalCptrWord + 1 + thetaQEvalCptrPaddingWords

/-- rust: LM:770-771 (`theta_window::REVERSED_EVALS_WORD`) @formal-baseline. -/
def thetaReversedEvalsWord : Nat :=
  thetaG1IdentityWord + g1WordsCount + thetaG1IdentityPaddingWords

/-- rust: MEM:67-80 (`struct ThetaWindowLayout`) @formal-baseline. Field order is
    the Rust's, field for field. -/
structure ThetaWindowLayout where
  rotPointsWord : Nat
  x1PowersWord : Nat
  qComWord : Nat
  qEvalSetWord : Nat
  qEvalCptrWord : Nat
  g1IdentityWord : Nat
  reversedEvalsWord : Nat
  rotPointsCapWords : Nat
  x1PowersCapWords : Nat
  qComCapWords : Nat
  qEvalSetCapWords : Nat

/-- rust: MEM:87-118 (`ThetaWindowLayout::compatibility`) @formal-baseline, in
    the Rust's own let-then-construct shape. The seven `debug_assert_eq!` of
    MEM:97-103 are compiled out in the reference profile (docs/REVIEW.md R-6),
    so they are not enforced inside the definition; the gate
    `thetaWindow_compatibility_ok` asserts the same seven equalities from
    outside, which is what makes recording them worth the space. -/
def ThetaWindowLayout.compatibility : ThetaWindowLayout := 
  let rotPointsWord := ThetaSlot.pairingRhs.word + g1WordsCount
  let x1PowersWord := rotPointsWord + thetaRotPointsCapWords
  let qComWord := x1PowersWord + thetaX1PowersCapWords
  let qEvalSetWord := qComWord
  let qEvalCptrWord := qEvalSetWord + thetaQEvalSetCapWords
  let g1IdentityWord := qEvalCptrWord + 1 + thetaQEvalCptrPaddingWords
  let reversedEvalsWord := g1IdentityWord + g1WordsCount + thetaG1IdentityPaddingWords
  { rotPointsWord := rotPointsWord, x1PowersWord := x1PowersWord,
    qComWord := qComWord, qEvalSetWord := qEvalSetWord,
    qEvalCptrWord := qEvalCptrWord, g1IdentityWord := g1IdentityWord,
    reversedEvalsWord := reversedEvalsWord,
    rotPointsCapWords := thetaRotPointsCapWords,
    x1PowersCapWords := thetaX1PowersCapWords, qComCapWords := thetaQComCapWords,
    qEvalSetCapWords := thetaQEvalSetCapWords }

/-- rust: MEM:379-385 (`struct FinalMsmShape`) @formal-baseline. -/
structure FinalMsmShape where
  terms : Nat
  inputBytes : Nat

/-- The `#[derive(Default)]` of MEM:379, for `FinalMsmShape`. -/
def finalMsmShapeDefault : FinalMsmShape := { terms := 0, inputBytes := 0 }

/-- rust: MEM:389-394 (`FinalMsmShape::from_terms`) @formal-baseline. -/
def FinalMsmShape.fromTerms (terms : Nat) : FinalMsmShape :=
  { terms := terms, inputBytes := terms * g1MsmPairBytes }

/-- rust: MEM:397-414 (`struct PcsMemoryRequirements`) @formal-baseline. Field
    order is the Rust's, field for field. -/
structure PcsMemoryRequirements where
  rotPointsWords : Nat
  x1PowersWords : Nat
  qComWords : Nat
  qEvalSetWords : Nat
  qEvalSourceTableWords : Nat
  qComTraceMsm : FinalMsmShape
  finalMsm : FinalMsmShape

/-- The `#[derive(Default)]` of MEM:397, for `PcsMemoryRequirements`. -/
def pcsMemoryRequirementsDefault : PcsMemoryRequirements :=
  { rotPointsWords := 0, x1PowersWords := 0, qComWords := 0, qEvalSetWords := 0,
    qEvalSourceTableWords := 0, qComTraceMsm := finalMsmShapeDefault,
    finalMsm := finalMsmShapeDefault }
/-- rust: MEM:416-519 (`struct VerifierMemoryLayout`) @formal-baseline. Field
    order is the Rust's, field for field. The `Ptr`-typed fields stay `Ptr`
    because the Rust fields are `Ptr`, not `usize`, and `validate` reads them
    through `Ptr::value` and `Value::as_usize`. -/
structure VerifierMemoryLayout where
  map : MemoryMap
  thetaWindows : ThetaWindowLayout
  constructorSmokeScratchMptr : Nat
  constructorG1msmSmokeScratchMptr : Nat
  constructorG1msmSmokeInputBytes : Nat
  transcriptMptr : Nat
  pcsPairingScratchMptr : Nat
  verifierReturnMptr : Nat
  quotientReturnMptr : Nat
  vkMptr : Ptr
  scalarInvScratchMptr : Nat
  challengeMptr : Ptr
  thetaMptr : Ptr
  betaMptr : Ptr
  gammaMptr : Ptr
  trashChallengeMptr : Ptr
  yMptr : Ptr
  xMptr : Ptr
  x1Mptr : Ptr
  x2Mptr : Ptr
  x3Mptr : Ptr
  x4Mptr : Ptr
  fComMptr : Ptr
  piMptr : Ptr
  accLhsMptr : Ptr
  accRhsMptr : Ptr
  xNMptr : Ptr
  xNMinus1InvMptr : Ptr
  lLastMptr : Ptr
  lBlindMptr : Ptr
  l0Mptr : Ptr
  instanceEvalMptr : Ptr
  quotientEvalMptr : Ptr
  quotientMptr : Ptr
  fEvalMptr : Ptr
  vMptr : Ptr
  finalComMptr : Ptr
  pairingLhsMptr : Ptr
  pairingRhsMptr : Ptr
  rotPointsMptr : Ptr
  x1PowersMptr : Ptr
  qComMptr : Ptr
  qEvalSetMptr : Ptr
  qEvalCptrMptr : Ptr
  g1IdentityMptr : Ptr
  reversedEvalsMptr : Ptr
  commsMptrBase : Ptr
  adviceCommsMptrBase : Ptr
  lookupMCommsMptrBase : Ptr
  permZCommsMptrBase : Ptr
  lookupHelperCommsMptrBase : Ptr
  lookupZCommsMptrBase : Ptr
  trashcanCommsMptrBase : Ptr
  quotientLimbCommsMptrBase : Ptr
  selectorAccMptr : Nat
  batchInvertScratchMptr : Nat
  lagrangeDenomsMptr : Nat
  quotientTmpMptr : Nat
  quotientStackMptr : Nat
  quotientStackHi : Nat
  pcsQEvalSourceTableMptr : Nat
  pcsQComTraceScratchMptr : Nat
  pcsFinalMsmScratchMptr : Nat
  accMsmScratch : Nat
  accumulatorPairingBatchMptr : Nat
  finalPairingScratchMptr : Nat
  traceU256Mptr : Nat
  pcs : PcsMemoryRequirements

/-- rust: MEM:564-583 (`struct VerifierMemoryLayoutConfig`) @formal-baseline. -/
structure VerifierMemoryLayoutConfig where
  transcriptWords : Nat
  numInstances : Nat
  quotientStateWords : Nat
  quotientStackWords : Nat
  accMsmTerms : Nat
  pcs : PcsMemoryRequirements

/-- The `#[derive(Default)]` of MEM:564, for `VerifierMemoryLayoutConfig`. -/
def verifierMemoryLayoutConfigDefault : VerifierMemoryLayoutConfig :=
  { transcriptWords := 0, numInstances := 0, quotientStateWords := 0,
    quotientStackWords := 0, accMsmTerms := 0, pcs := pcsMemoryRequirementsDefault }

/-- rust: ENC:594-601 (`Value::as_usize`) @formal-baseline. `*int as usize` is a
    wrapping cast, so a negative offset becomes its 2^64 two's complement rather
    than clamping; `Nat` cannot hold an `isize` directly, so the wrap is spelled
    out the way `fmtHex` (F:65-66) spells out the same cast. The
    `Value::Identifier` arm is `unreachable!()`, which rule R4 renders as a
    `Fault.panic` rather than a silent total. It is reachable as a TYPE:
    `Ptr::new` (ENC:688-693) takes `impl Into<Value>` and
    `From<&'static str> for Value` (ENC:611) makes a symbolic pointer
    well-typed, so the arm is modelled rather than assumed away. No current call
    path reaches it - every one of the 49 `Ptr::memory`/`Ptr::calldata` sites in
    the reference passes a `usize` - which is why this returns `Except` and why
    `value_asUsize_panic_ok` feeds it an identifier directly. -/
def Value.asUsize (v : Value) : Except Midfall.Halo2.Fault Nat :=
  match v with
  | .integer i => pure (if i >= 0 then i.toNat else (i + (2 : Int) ^ 64).toNat)
  | .identifier _ _ => throw (Midfall.Halo2.Fault.panic
      "proofs/solidity-verifier/src/lowering/encoding/mod.rs:599")

/-- `Value::as_usize` at the one site that cannot carry an `Except`: MEM:1039,
    where the reference does not handle the panic and would abort the process.
    `Nat` has no failure case to return, so the symbolic arm maps to a value no
    caller can observe; `asUsizeNat_agrees_ok` pins it to `Value.asUsize` on
    every concrete offset, which is the whole domain the reference can reach. -/
def Value.asUsizeNat (v : Value) : Nat :=
  match v with
  | .integer i => if i >= 0 then i.toNat else (i + (2 : Int) ^ 64).toNat
  | .identifier _ _ => 0

/-- rust: MEM:974-1076 (`VerifierMemoryLayout::validate`) @formal-baseline. Four
    checks in the source order that decides which error a bad layout reports:
    the seven fixed low-memory pointers against their constants, every registered
    region against `LOW_MEMORY_SCRATCH_START`, the scalar-inversion scratch
    against `VK_MPTR - MODEXP_SCRATCH_BYTES` (`saturating_sub`, which is `Nat`
    subtraction), and the four PCS window capacities. The first three message
    formats are hex (`{:#x}`); the four capacity messages are DECIMAL (`{}`),
    which the gate expectations show. -/
def VerifierMemoryLayout.validate (self : VerifierMemoryLayout) :
    Except String Unit := do
  let failErr (msg : String) : Except String Unit := Except.error msg
  let fixedLowMemory : List (String × Nat × Nat) :=
    [("constructor_smoke_scratch_mptr", self.constructorSmokeScratchMptr,
       lowMemoryScratchStart),
     ("transcript_mptr", self.transcriptMptr, transcriptBufferStart),
     ("pcs_pairing_scratch_mptr", self.pcsPairingScratchMptr, pcsPairingScratchStart),
     ("verifier_return_mptr", self.verifierReturnMptr, verifierReturnBufferStart),
     ("quotient_return_mptr", self.quotientReturnMptr, quotientReturnBufferStart),
     ("accumulator_pairing_batch_mptr", self.accumulatorPairingBatchMptr,
       accumulatorPairingBatchPtr),
     ("final_pairing_scratch_mptr", self.finalPairingScratchMptr,
       finalPairingScratchStart)]
  for (name, actual, expected) in fixedLowMemory do
    if actual != expected then
      failErr ("fixed memory pointer " ++ name ++ " drifted: got "
        ++ hashHex actual ++ ", expected " ++ hashHex expected)
    else pure ()
  for region in self.map.regions do
    if region.len != 0 && region.start < lowMemoryScratchStart then
      failErr ("memory region " ++ region.name ++ " starts at "
        ++ hashHex region.start
        ++ ", below LOW_MEMORY_SCRATCH_START (" ++ hashHex lowMemoryScratchStart
        ++ "); it can overlap solc's via-IR stack-to-memory spill window"
        ++ " [0x80, reserved_end)")
    else pure ()
  let expectedScalarInv := (ptrValue self.vkMptr).asUsizeNat - modexpScratchBytes
  if self.scalarInvScratchMptr != expectedScalarInv then
    failErr ("scalar inversion scratch drifted: got "
      ++ hashHex self.scalarInvScratchMptr
      ++ ", expected " ++ hashHex expectedScalarInv)
  else pure ()
  let windows := self.thetaWindows
  if self.pcs.rotPointsWords > windows.rotPointsCapWords then
    failErr ("PCS scratch layout mismatch: ROT_POINTS_MPTR needs "
      ++ toString self.pcs.rotPointsWords ++ " word(s), capacity is "
      ++ toString windows.rotPointsCapWords)
  else pure ()
  if self.pcs.x1PowersWords > windows.x1PowersCapWords then
    failErr ("PCS scratch layout mismatch: X1_POWERS_MPTR needs "
      ++ toString self.pcs.x1PowersWords ++ " word(s), capacity is "
      ++ toString windows.x1PowersCapWords)
  else pure ()
  if self.pcs.qComWords > windows.qComCapWords then
    failErr ("PCS scratch layout mismatch: Q_COM_MPTR needs "
      ++ toString self.pcs.qComWords ++ " word(s), capacity is "
      ++ toString windows.qComCapWords)
  else pure ()
  if self.pcs.qEvalSetWords > windows.qEvalSetCapWords then
    failErr ("PCS scratch layout mismatch: Q_EVAL_SET_MPTR needs "
      ++ toString self.pcs.qEvalSetWords ++ " word(s), capacity is "
      ++ toString windows.qEvalSetCapWords)
  else pure ()
  MemoryMap.validate self.map

/-! ## Layout well-formedness: the `Supported.layout` side condition of PLAN 9.5 -/

/-- A modelling helper rather than a Rust item: the pair loop of
    `MemoryMap::validate` (MEM:272-286) read as a Bool.
    `memoryMapValidateAgainst` and `memoryMapValidatePairs` are the same
    strict-upper-triangle traversal in `Except` form, which stops at the first
    offending pair in order to name it; this one only answers. The body mirrors
    MEM:274 exactly - a pair is a problem when the regions overlap AND their
    lifetimes intersect - so two regions that share bytes under two different
    phases are not a problem at all. -/
def memoryRegionsPairwiseDisjoint : List MemoryRegion → Bool
  | [] => true
  | lhs :: rest =>
    rest.all (fun rhs =>
      ! (lhs.overlaps rhs && memoryLifetimeIntersects lhs.lifetime rhs.lifetime))
      && memoryRegionsPairwiseDisjoint rest

/-- A modelling helper rather than a Rust item: the three conditions
    `MemoryMap::validate` (MEM:234-289) enforces, as one Bool.

    * word alignment is the `region.start % WORD_BYTES != 0` arm of the first
      loop (MEM:256-261);
    * the spill-window bound is the
      `region.start < SOLIDITY_RESERVED_MEMORY_BYTES` arm of the same loop
      (MEM:239-255), read as "at or above" because the Rust rejects
      strictly-below starts;
    * disjointness is `memoryRegionsPairwiseDisjoint` above (MEM:272-286).

    Two divergences from `validate` are recorded rather than hidden. The
    `len == 0` exemptions follow MEM:239 and the two `len != 0` conjuncts of
    `MemoryRegion::overlaps` (MEM:212), which makes this predicate WEAKER than
    `validate`: a zero-length region at an unaligned start is rejected there and
    accepted here. And the `region.len % WORD_BYTES != 0` arm (MEM:262-267) is
    not part of this predicate at all, so nothing here says a length is a whole
    number of words. -/
def MemoryMap.wellFormedBool (self : MemoryMap) : Bool :=
  self.regions.all (fun region =>
    region.len == 0 || region.start % wordBytes == 0)
    && self.regions.all (fun region =>
      region.len == 0 || solidityReservedMemoryBytes <= region.start)
    && memoryRegionsPairwiseDisjoint self.regions

/-- `WellFormed` is decidable BY CONSTRUCTION, and that is the whole claim: the
    Prop is the Bool equality `wellFormedBool = true`, so the instance below is
    `instDecidableEqBool` applied to that one value - no search and no proof
    component. Nothing further is claimed: it is not proved equivalent to
    `MemoryMap.validate = .ok ()`, and the two divergences listed on
    `wellFormedBool` make it strictly weaker than `validate`. -/
def MemoryMap.WellFormed (self : MemoryMap) : Prop := self.wellFormedBool = true

/-- Decidable by construction, for the reason stated on `MemoryMap.WellFormed`. -/
instance (self : MemoryMap) : Decidable self.WellFormed :=
  instDecidableEqBool self.wellFormedBool true

/-! ## `lowering/layout/mod.rs:774-786` - the `trace` topic namespaces

This section is the `pub(crate) mod trace` block. It lives here, and not in
`Protocol.lean` where two of its constants are re-exported, because the block
belongs to the Layout row of plan Section 8's module map and every cite in it is
an `LM:` cite. `Midfall/Generator/Protocol.lean` re-exports
`TRACE_QUOTIENT_IDENTITY_BASE` and `TRACE_PCS_QUERY_BASE`, citing `PM:` for the
re-export and `LM:` for the value.

All six are `u64` or `usize` in Rust and `Nat` here (rule R5). No wrapping can
occur: they are LOG topic namespaces, the reference's own test LM:877-882 pins
each to a literal below 100000, and the only arithmetic done on them in the
ported scope is `base + index` with `index` a count of queries or identities.

The Rust doc comment (LM:775-779) is worth carrying verbatim: "The gaps are
intentional: they keep broad event families visually separated in traces and
preserve historical IDs consumed by tests and external comparison scripts." That
is why the six are transcribed as independent literals and not derived from one
another. -/

/-- rust: LM:781 (`PCS_QUERY_BASE: u64 = 2_000`) @formal-baseline. KZG query
    trace IDs; re-exported by `Protocol.lean` at PM:180 and consumed there by
    `from_constraint_system` for `pcs_query_trace_ids`. -/
def Trace.pcsQueryBase : Nat := 2_000

/-- rust: LM:782 (`PROOF_COMMIT_BASE: usize = 10_000`) @formal-baseline. Proof
    G1 reads. Reached from this file only through M:1284, which puts it in
    `TemplateConstants.proofCommitTraceBase`. -/
def Trace.proofCommitBase : Nat := 10_000

/-- rust: LM:783 (`PROOF_EVAL_BASE: usize = 20_000`) @formal-baseline. Proof
    scalar eval reads; same M:1285 consumer note. -/
def Trace.proofEvalBase : Nat := 20_000

/-- rust: LM:784 (`QUOTIENT_IDENTITY_BASE: u64 = 30_000`) @formal-baseline.
    Quotient identities; re-exported by `Protocol.lean` at PM:178 and also read
    at M:1286 and quotient.rs:1365. -/
def Trace.quotientIdentityBase : Nat := 30_000

/-- rust: LM:785 (`PCS_SERIALIZED_POINT_SET_BASE: u64 = 41_000`)
    @formal-baseline. PCS point sets. Not used by the protocol plan; ported
    because rule R1 ports the whole block, and the gaps are load-bearing per the
    module doc comment above. -/
def Trace.pcsSerializedPointSetBase : Nat := 41_000

/-- rust: LM:786 (`SELECTOR_FOLD_BASE: usize = 60_000`) @formal-baseline.
    Selector accumulators; read at M:1287. -/
def Trace.selectorFoldBase : Nat := 60_000


end Midfall.Generator


/-! # Known-answer tests for the ported layout layer

Every gate names the wrong implementation it rules out, in the sense docs/REVIEW.md
R-38 states at the end of its entry. The expected sides come in three kinds, and
the kinds are not equally strong.

The strongest are the assertions of the reference's own test modules, which this
file does not control: `vk_payload.rs` VP:242-321, `memory.rs` MEM:1131-1257,
and `models.rs` M:1300-1327 and M:1329-1341 for the payload layout. Gates built
on those are evidence rather than transcription.

The second kind is arithmetic derived here from the ported definitions - the
`payload_layout` and `theta_window` offsets, chiefly. Those are checked against
the port, not against an outside source, and each says so.

The third is the cross-check against `Midfall/Yul/Externals.lean`. That file
documents its constants as transcriptions of `layout/mod.rs`, the same Rust this
file transcribes, so agreement there is a drift check between two copies rather
than an independent derivation; EIP-2537 and the EVM memory model corroborate the
numbers but are not what Externals cites. Where a Rust error arm cannot be reached
at all, that is said at the site and no gate is claimed for it. -/



namespace Midfall.Generator.LayoutKats

open Midfall Midfall.Generator

/-- Reading an `Except String` as "it failed with exactly this message". The
    reference tests use `err.contains(..)`; asserting the whole string is
    strictly stronger, and it is what makes the `{:#x}` formatting part of the
    obligation. -/
def errIs {α : Type} (e : Except String α) (want : String) : Bool :=
  match e with
  | .error m => m == want
  | .ok _ => false

/-- Reading an `Except String` as "it succeeded with exactly this value". -/
def okIs {α : Type} [BEq α] (e : Except String α) (want : α) : Bool :=
  match e with
  | .ok a => a == want
  | .error _ => false

/-- Reading an `Except String` as "it succeeded at all". -/
def isOk {α : Type} (e : Except String α) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- The fixture of VP:244, `VkPayloadLayout::for_vk(31, 3, 5, 7, 2)`. Read by
    `forVk_offsets_ok`, `forVk_totalWords_ok` and `forVk_bytes_ok`; if the
    construction fails it degrades to the empty layout, which makes those three
    fail loudly rather than quietly. The other gates do not read it. -/
def forVkFixture : VkPayloadLayout :=
  match VkPayloadLayout.forVk vkHeaderWords 3 5 7 2 with
  | .ok layout => layout
  | .error _ => vkPayloadLayoutDefault

/-- THE SECTION OFFSETS ARE THE ONES THE REFERENCE ASSERTS. VP:246-262 pins
     0, 31, 34, 39 and 67. Rules out a wrong G1 word width (67 is 31+3+5+28, so
     `g1WordsCount` enters twice), a swapped quotient order, and a cursor that
     does not advance. -/
def forVk_offsets_ok : Bool :=
  vkPayloadSectionOffsets forVkFixture == [0, 31, 34, 39, 67]

/-- THE CURSOR IS THE SUM. VP:263 asserts 75 = 31+3+5+28+8. Rules out a section
    whose width is dropped from the cursor. -/
def forVk_totalWords_ok : Bool := forVkFixture.totalWords == 75

/-- WORDS ARE NOT BYTES. VP:264-271 asserts the fixed section starts at
     39 * 0x20 and the permutation section is 2 * 0x80 bytes long. Rules out a
     missing or doubled `WORD_BYTES` factor in the byte accessors, which the
     word-offset gates above cannot see. -/
def forVk_bytes_ok : Bool :=
  okIs (forVkFixture.byteOffset PayloadSectionKind.fixedCommitments) (39 * 0x20)
    && okIs (forVkFixture.byteLen PayloadSectionKind.permutationCommitments) (2 * 0x80)

/-- A DUPLICATE KIND IS REJECTED, BY NAME. VP:105-107 and VP:275-288. Rules out
     the duplicate check being dropped (a duplicate section makes
     `word_offset` ambiguous, and `find?` would silently return the first), and
     pins the `{:?}` rendering the message embeds. -/
def reserve_duplicate_err_ok : Bool :=
  match vkPayloadLayoutDefault.reserve PayloadSectionKind.header vkHeaderWords with
  | .ok (layout, _) =>
    errIs (layout.reserve PayloadSectionKind.header 1)
      "duplicate VK payload section: Header"
  | .error _ => false

/-- A MISSING SECTION SAYS WHICH. VP:138-139. Rules out `require_section`
     falling back to a default offset, which would turn a wrong VK into a wrong
     offset rather than an error. -/
def requireSection_missing_err_ok : Bool :=
  errIs (vkPayloadLayoutDefault.wordOffset PayloadSectionKind.quotientProgram)
    "missing VK payload section: QuotientProgram"

/-- A section that does not start where the cursor is. -/
def holeSection : PayloadSection :=
  { kind := PayloadSectionKind.header, wordOffset := 32, wordLen := 3 }

/-- A layout whose first section does not start at word 0. -/
def holeLayout : VkPayloadLayout :=
  { sections := [holeSection], cursorWords := 35 }

/-- A HOLE IN THE SECTION MAP IS REJECTED. VP:178-183. Rules out `validate`
     only checking the cursor, which would accept a layout with a gap and let
     the runtime `extcodecopy` read the wrong words. -/

def validate_startErr_err_ok : Bool :=
  errIs holeLayout.validate
    "VK payload section Header starts at 0x20, expected 0x0"

/-- A section that ends at word 4. -/
def cursorSection : PayloadSection :=
  { kind := PayloadSectionKind.header, wordOffset := 0, wordLen := 4 }

/-- A layout whose cursor does not match where its sections end. -/
def cursorMismatchLayout : VkPayloadLayout :=
  { sections := [cursorSection], cursorWords := 5 }

/-- THE CURSOR MUST AGREE WITH THE SECTIONS. VP:186-191. Rules out the opposite
     slip: sections that run past or short of the cursor, i.e. a payload whose
     declared length is not the length that was reserved. -/

def validate_cursorErr_err_ok : Bool :=
  errIs cursorMismatchLayout.validate
    "VK payload cursor mismatch: sections end at 0x4, cursor is 0x5"

/-- CEILING DIVISION, INCLUDING THE EXACT-MULTIPLE CASES. VP:201-203. Rules out
     `byte_len / 32` (which would drop the last word for 33 and 37) and
     `+ 1` unconditionally (which would over-allocate at 0 and 32 and then
     reserve a word the payload does not have). -/
def packed_wordLenForBytes_ok : Bool :=
  [0, 32, 33, 37, 64].map PackedProgramCodec.wordLenForBytes == [0, 1, 2, 2, 2]

/-- THE PACKER KEEPS THE PARTIAL FINAL WORD. VP:206-210 with the VP:291-300
     assertions: 37 bytes become 2 words and decode back exactly. Rules out
     dropping the resize padding at VP:208, which would leave 5 bytes unrouted and
     decode back 32 - a truncated quotient program that still passes every length
     check upstream. It does NOT rule out `chunks_exact` in place of
     `chunks`: the port pads to a whole number of words first, exactly as the
     Rust does, so the two iteration idioms coincide on every input this function
     can receive. -/
def packed_roundTrip_ok : Bool :=
  let bytes := ByteArray.mk ((List.range 37).map Nat.toUInt8).toArray
  let words := PackedProgramCodec.encodeWords bytes
  words.length == 2
    && match PackedProgramCodec.decodeWords words 37 with
       | .ok back => bytesToList back == List.range 37
       | .error _ => false

/-- A LENGTH PAST THE WORDS IS REFUSED. VP:215-220 with VP:303-309. Rules out
     the capacity check being dropped, which would make `bytes[byte_len..]`
     index past the decoded buffer. -/
def packed_capacity_err_ok : Bool :=
  errIs (PackedProgramCodec.decodeWords
    (PackedProgramCodec.encodeWords (ByteArray.mk #[1, 2, 3])) 33)
    "packed program byte length 33 exceeds word capacity 32"

/-- NON-ZERO PADDING IS REFUSED. VP:227-229 with VP:312-321: 31 bytes of 0xaa
     pack into one word whose low byte is zero, so adding one is the Rust's
     `words[0] |= 1` and puts a byte past the declared length; the decode
     must fail. Rules out accepting a word whose padding
     carries data the decoder will drop - the silent-loss half of the same bug
     class as the `chunks_exact` one above. -/
def packed_padding_err_ok : Bool :=
  let words := (PackedProgramCodec.encodeWords
    (ByteArray.mk ((List.replicate 31 (Nat.toUInt8 0xaa)).toArray))).map (· + 1)
  errIs (PackedProgramCodec.decodeWords words 31)
    "packed program has non-zero padding bytes"

/-- TWO PERMANENT REGIONS MAY NOT SHARE BYTES. MEM:1132-1149. Rules out the
     overlap check being phase-only, which would let a permanent buffer be
     clobbered by anything. -/
def memory_overlappingPermanent_err_ok : Bool :=
  errIs ((memoryMapDefault.push (memoryRegionNew "a" 0x100 (2 * wordBytes)
      MemoryLifetime.permanent)).push
      (memoryRegionNew "b" 0x120 wordBytes MemoryLifetime.permanent)).validate
    "memory region a [0x100..0x140) overlaps b [0x120..0x140)"

/-- BUT TWO PHASES MAY. MEM:1152-1158. The other half of the same rule: without
     it the intentional scratch aliasing the generated verifier relies on would
     be rejected, so a plan that only ever passes one of these two gates is not
     implementing this rule at all. -/
def memory_disjointPhases_ok : Bool :=
  isOk ((memoryMapDefault.push (memoryRegionNew "a" 0x100 wordBytes
      (MemoryLifetime.phase MemoryPhase.quotientVm))).push
      (memoryRegionNew "b" 0x100 wordBytes
      (MemoryLifetime.phase MemoryPhase.pcsFinalMsm))).validate

/-- BYTE-GRANULAR RANGES ARE A BUG, NOT A PACKING WIN. MEM:256-267 with
     MEM:1161-1169: an unaligned start and an unaligned length are different
     errors, and both are caught. -/
def memory_unaligned_err_ok : Bool :=
  errIs ((memoryMapDefault.push
    (memoryRegionNew "a" 0x101 wordBytes (MemoryLifetime.phase MemoryPhase.quotientVm))).validate)
    "memory region a starts at unaligned byte offset 0x101"
    && errIs ((memoryMapDefault.push
      (memoryRegionNew "a" 0x100 (wordBytes - 1)
        (MemoryLifetime.phase MemoryPhase.quotientVm))).validate)
    "memory region a has unaligned length 0x1f"

/-- NOTHING MAY BE PLACED IN SOLC'S RESERVED WINDOW. MEM:239-255 with
     MEM:1172-1194. The window is what the via-IR stack-to-memory mover uses for
     spill slots, so a region inside it can be silently overwritten; the message
     also has to name which reserved sub-range was hit. -/
def memory_reserved_err_ok : Bool :=
  errIs ((memoryMapDefault.push
    (memoryRegionNew "free_memory_pointer" solidityFreeMemoryPointerSlot wordBytes
      (MemoryLifetime.phase MemoryPhase.transcript))).validate)
    "memory region free_memory_pointer starts at 0x40, inside Solidity-reserved free-memory pointer memory [0x00..0x80)"
    && errIs ((memoryMapDefault.push
      (memoryRegionNew "zero_slot" solidityZeroSlot wordBytes
        (MemoryLifetime.phase MemoryPhase.transcript))).validate)
    "memory region zero_slot starts at 0x60, inside Solidity-reserved zero slot memory [0x00..0x80)"

/-- `alloc_after` PLACES AFTER THE ANCHOR, ROUNDED UP. MEM:322 with
     MEM:1197-1211: 0x101 + 0x20 rounds to 0x140, and the registered region
     starts there and validates. Rules out placing at the raw sum (0x121), which
     would fail the alignment rule the very next line enforces. -/
def memory_allocAfter_ok : Bool :=
  let (arena, after) :=
    memoryArenaDefault.allocAfter "after" 0x101 wordBytes wordBytes MemoryLifetime.permanent
  after == 0x140
    && match arena.intoMap.region "after" with
       | some region => region.start == 0x140
       | none => false
    && isOk arena.intoMap.validate

/-- ONE CURSOR PER PHASE. MEM:372-375 with MEM:1214-1229: two allocations in
     one phase advance, the first in another phase returns to the base. Rules out
     a single global cursor (which would move `reused` to 0x440 and change every
     generated address) and a cursor that never advances (which would alias
     `second` onto `first`). -/
def memory_scratchAllocator_ok : Bool :=
  let s0 := memoryArenaDefault.scratchAllocator 0x400
  let (s1, first) := s0.allocPhaseScratch "first" wordBytes MemoryPhase.quotientVm
  let (s2, second) := s1.allocPhaseScratch "second" wordBytes MemoryPhase.quotientVm
  let (s3, reused) := s2.allocPhaseScratch "reused" wordBytes MemoryPhase.pcsFinalMsm
  first == 0x400 && second == 0x420 && reused == 0x400
    && isOk s3.arena.intoMap.validate

/-- THE VK CONSTRUCTOR PAYLOAD IS REGISTERED, NOT JUST ASSUMED. MEM:1232-1243:
     the pointer is 0x80, the region is there with the requested length, and the
     map validates. Rules out the constructor payload being a bare constant with
     no planner entry, which is what let it sit inside the reserved window
     unnoticed before the layout was registered. -/
def vkConstructor_registered_ok : Bool :=
  let layout := VkConstructorMemoryLayout.new 0x660
  layout.payloadMptr == vkConstructorPayloadStart
    && match layout.map.region "vk_constructor_payload" with
       | some region => region.start == vkConstructorPayloadStart && region.len == 0x660
       | none => false
    && isOk layout.validate

/-- AN UNALIGNED RUNTIME LENGTH RESERVES ALIGNED MEMORY. MEM:539 with
     MEM:1246-1257: 0x661 bytes reserves 0x680. Rules out registering the raw
     runtime length, which the alignment rule in `MemoryMap::validate` would
     then reject - so the layout would only fail in the build that validates. -/
def vkConstructor_roundsUp_ok : Bool :=
  let layout := VkConstructorMemoryLayout.new 0x661
  layout.payloadMptr == vkConstructorPayloadStart
    && match layout.map.region "vk_constructor_payload" with
       | some region => region.start == vkConstructorPayloadStart && region.len == 0x680
       | none => false
    && isOk layout.validate

/-- The same map with a pointer that is not the constant. -/
def driftedConstructorLayout : VkConstructorMemoryLayout :=
  { map := memoryMapDefault, payloadMptr := 0x100 }

/-- THE POINTER CHECK ITSELF. MEM:554-559. This arm is unreachable through
     `VkConstructorMemoryLayout::new`, which always returns 0x80, so the gate
     feeds the record directly: what it pins is that `validate` compares against
     the constant rather than returning `Ok` unconditionally. -/

def vkConstructor_drift_err_ok : Bool :=
  errIs driftedConstructorLayout.validate
    "VK constructor payload pointer drifted: got 0x100, expected 0x80"

/-- The VK of MEM:1260-1279: a full header, one fixed commitment, no permutation
    commitments, no quotient sections. -/
def syntheticVk : Halo2VerifyingKey where
  constructorPayloadMptr := (VkConstructorMemoryLayout.new
    (vkHeaderWords * wordBytes + g1Bytes)).payloadMptr
  constants := (List.range vkHeaderWords).map fun _ => ("c", 0)
  fixedComms := [{ xHi := 0, xLo := 0, yHi := 0, yLo := 0 }]
  permutationComms := []
  quotientConstOffsetWords := none
  quotientConstWords := 0
  quotientProgramOffsetWords := none
  quotientProgramWords := 0
  quotientConstLabels := []
  quotientConstHeaders := []

/-- A commitment word with no content; the reference test fixtures do not read
    the coordinates, only the count. -/
def g1Zero : G1Words :=
  { xHi := 0, xLo := 0, yHi := 0, yLo := 0 }

/-- The VK of M:1300-1327: `synthetic_vk(2, 1)` has 31 + 2 + 1 = 34 constants,
    the test sets the quotient offsets to 34 and 36, then extends the table by
    2 + 3 words to 39. -/
def referenceTestVk : Halo2VerifyingKey :=
  { constructorPayloadMptr := vkConstructorPayloadStart,
    constants := (List.range 39).map fun _ => ("c", 0),
    fixedComms := [g1Zero, g1Zero],
    permutationComms := [g1Zero],
    quotientConstOffsetWords := some 34,
    quotientConstWords := 2,
    quotientProgramOffsetWords := some 36,
    quotientProgramWords := 3,
    quotientConstLabels := [],
    quotientConstHeaders := [] }
/-- `payload_layout` ON THE REFERENCE VK. With no quotient sections the header
     is the whole constant table, so the sections are 0, 31, 31, 31 and 35 - the
     three zero-width sections collapse onto the cursor. Rules out the commitment
     widths being dropped, and out the header width being read as something other
     than `constants - quotient_words`. The checked-vs-saturating distinction
     belongs to `vk_payloadLayout_tooShort_err_ok`, where the two differ; with
     zero quotient words this fixture cannot see it. -/
def vk_payloadLayout_offsets_ok : Bool :=
  match syntheticVk.payloadLayout with
  | .ok layout => vkPayloadSectionOffsets layout == [0, 31, 31, 31, 35]
  | .error _ => false

/-- THE REFERENCE TEST ITSELF, ported as a gate: M:1300-1327,
    `verifying_key_payload_layout_matches_rendered_byte_order`. Its four
    assertions are the quotient-constant offset (34), the quotient-program offset
    (36), the fixed-commitment offset (39, the extended table length), and
    `total_bytes == len()`; M:1326 then requires `validate_payload_layout` to
    succeed. Unlike the derived gates above, every expected number here is copied
    from a reference assertion. Rules out the header being read as the extended
    table length rather than the table length minus the quotient words - the two
    differ by exactly 5 here, where the zero-quotient fixture above cannot see it. -/
def vk_payloadLayout_referenceTest_ok : Bool :=
  match referenceTestVk.payloadLayout with
  | .ok layout =>
      vkPayloadSectionOffsets layout == [0, 34, 36, 39, 47]
        && layout.totalBytes == referenceTestVk.len
        && isOk referenceTestVk.validatePayloadLayout
  | .error _ => false

/-- THE HEADER IS THE CONSTANT TABLE `MINUS` THE QUOTIENT SECTIONS. With
     4 + 2 quotient words the header is 31 - 6 = 25 words, so the quotient
     sections start at 25 and 29 and the commitments still start at 31 and 35 -
     the payload does not grow because the VK carries quotient data. Rules out
     reading the header width as the whole constant table, which would place the
     quotient constants on top of the header's own words. -/
def vk_payloadLayout_quotientOffsets_ok : Bool :=
  match ({ syntheticVk with quotientConstWords := 4, quotientProgramWords := 2 }
      : Halo2VerifyingKey).payloadLayout with
  | .ok layout => vkPayloadSectionOffsets layout == [0, 25, 29, 31, 35]
  | .error _ => false

/-- THE LAYOUT AND THE RENDERED BYTES AGREE. M:381-399 on the reference VK.
     Note what this does NOT claim: for every VK whose `payload_layout` succeeds
     the two sides are equal by arithmetic - the header is the constant table
     minus the quotient words, so the total is always
     `constants + 4 * commitments` words, which is exactly `len`. The Rust's
     `VK payload byte length mismatch` arm is therefore unreachable after a
     successful `payload_layout`, and no gate here claims otherwise. What this
     gate can fail on is therefore the constructor path: `VkConstructorMemoryLayout
     ::new`/validate and the pointer agreement. Perturbing the constructor
     alignment reddens it; deleting the pointer check alone does not, because
     through this fixture both sides are the same `new` call - that arm is
     covered by `vk_validatePayloadLayout_ptr_err_ok`, not here. -/
def vk_validatePayloadLayout_ok : Bool := isOk syntheticVk.validatePayloadLayout

/-- A CONSTANT TABLE SHORTER THAN ITS OWN QUOTIENT SECTIONS IS AN ERROR, NOT A
     WRAP. M:346-351. Rules out reading `checked_sub` as saturating `Nat`
     subtraction, which would silently build a header of width 0 and emit a VK
     whose quotient words sit at the start of the payload. -/
def vk_payloadLayout_tooShort_err_ok : Bool :=
  errIs ({ syntheticVk with quotientConstWords := 32, quotientProgramWords := 2 }
    : Halo2VerifyingKey).payloadLayout
    "VK constant table too short: constants=31 quotient_words=34"

/-- A STALE QUOTIENT-CONSTANT OFFSET IS CAUGHT. M:360-367, the arm the reference
     test M:1329-1341 (`..._rejects_stale_quotient_offsets`) exercises. The
     offset is a separate field from the layout, so it can drift when the header
     changes; rules out the field being trusted. -/
def vk_payloadLayout_qcOffset_err_ok : Bool :=
  errIs ({ syntheticVk with quotientConstOffsetWords := some 30 }
    : Halo2VerifyingKey).payloadLayout
    "quotient const offset mismatch: got 0x1e, expected 0x1f"

/-- A STALE QUOTIENT-PROGRAM OFFSET IS CAUGHT. M:368-375, the same drift in the
     other field. -/
def vk_payloadLayout_qpOffset_err_ok : Bool :=
  errIs ({ syntheticVk with quotientProgramOffsetWords := some 34 }
    : Halo2VerifyingKey).payloadLayout
    "quotient program offset mismatch: got 0x22, expected 0x1f"

/-- A CONSTRUCTOR POINTER THAT DOES NOT MATCH THE PLANNER IS CAUGHT. M:392-397.
     Rules out `validate_payload_layout` stopping at the length check. -/
def vk_validatePayloadLayout_ptr_err_ok : Bool :=
  errIs ({ syntheticVk with constructorPayloadMptr := 0x100 }
    : Halo2VerifyingKey).validatePayloadLayout
    "VK constructor payload pointer mismatch: got 0x100, expected 0x80"

/-- THE TWO INDEPENDENT PORTS AGREE ON THE SHARED NUMBERS. `Midfall/Yul` derives
     these from EIP-2537 and the EVM memory model; this file takes them from
     `layout/mod.rs`. Neither cites the other, so agreement is evidence and not
     transcription. -/
def layoutConstants_matchYul_ok : Bool :=
  wordBytes == Midfall.Yul.wordBytes
    && g1Bytes == Midfall.Yul.g1Bytes
    && g2Bytes == Midfall.Yul.g2Bytes
    && frBytes == Midfall.Yul.frBytes
    && g1MsmPairBytes == Midfall.Yul.g1MsmPairBytes
    && g1AddInputBytes == Midfall.Yul.g1AddInputBytes
    && modexpFrameBytes == Midfall.Yul.modexpFrameBytes
    && pairingTwoPairBytes == Midfall.Yul.pairingTwoPairBytes

/-- THE DERIVED HEADER WIDTHS. LM:399 and LM:401 place the g2 and neg_s_g2
     bases at 11 + 4 and 11 + 4 + 8, and LM:445 totals the schema at 31. The two
     base constants that are literally `vkHeaderScalarWords` and
     `vkHeaderScalarWords + g1WordsCount` are not re-asserted - that would
     restate the definitions without being falsifiable by anything the definitions
     do not already fix. The header-to-payload link is carried by
     `forVk_offsets_ok`, which feeds this total into `for_vk`. -/
def vkHeaderWords_ok : Bool :=
  vkHeaderG2BaseWord == 15 && vkHeaderNegSG2BaseWord == 23
    && vkHeaderWords == 31

/-- The declaration order of MEM:121-155. -/
def memoryPhaseOrder : List MemoryPhase := [
    MemoryPhase.vkConstructorPayload,
    MemoryPhase.constructorSmoke,
    MemoryPhase.transcript,
    MemoryPhase.scalarInv,
    MemoryPhase.lagrangeBatchInvert,
    MemoryPhase.quotientVm,
    MemoryPhase.pcsFixed,
    MemoryPhase.pcsQEvalSourceTable,
    MemoryPhase.pcsQComTrace,
    MemoryPhase.pcsFinalMsm,
    MemoryPhase.pcsPairing,
    MemoryPhase.accumulatorMsm,
    MemoryPhase.accumulatorPairingBatch,
    MemoryPhase.finalPairing,
    MemoryPhase.verifierReturn,
    MemoryPhase.quotientReturn
]

/-- Adjacent pairs are strictly increasing in the derived `Ord`. -/
def memoryPhaseOrdered : List MemoryPhase → Bool
  | a :: b :: rest => compare a b == Ordering.lt && memoryPhaseOrdered (b :: rest)
  | _ => true

/-- THE CURSOR LIST IS SORTED BY THE DERIVED `Ord`. MEM:121-155 derives `Ord`
     in declaration order, and R6 turns the cursor `BTreeMap` into a list kept in
     that order. The gate requires the transcription of MEM:121-155 to be strictly
     increasing under the derived `Ord`, with sixteen entries and no duplicates.
     That reddens on a transposition, a dropped variant, or a repeated one.
     Scope, stated honestly: it cannot redden on the derived `Ord` itself
     drifting from MEM:121-155, because reordering the inductive moves both sides
     together. That link is carried by the citation on the inductive, not here. -/
def memoryPhase_order_ok : Bool :=
  memoryPhaseOrdered memoryPhaseOrder
    && memoryPhaseOrder.length == 16
    && memoryPhaseOrder.eraseDups.length == 16

#eval forVk_offsets_ok -- expect true
#eval forVk_totalWords_ok -- expect true
#eval forVk_bytes_ok -- expect true
#eval reserve_duplicate_err_ok -- expect true
#eval requireSection_missing_err_ok -- expect true
#eval validate_startErr_err_ok -- expect true
#eval validate_cursorErr_err_ok -- expect true
#eval packed_wordLenForBytes_ok -- expect true
#eval packed_roundTrip_ok -- expect true
#eval packed_capacity_err_ok -- expect true
#eval packed_padding_err_ok -- expect true
#eval memory_overlappingPermanent_err_ok -- expect true
#eval memory_disjointPhases_ok -- expect true
#eval memory_unaligned_err_ok -- expect true
#eval memory_reserved_err_ok -- expect true
#eval memory_allocAfter_ok -- expect true
#eval memory_scratchAllocator_ok -- expect true
#eval vkConstructor_registered_ok -- expect true
#eval vkConstructor_roundsUp_ok -- expect true
#eval vkConstructor_drift_err_ok -- expect true
#eval vk_payloadLayout_offsets_ok -- expect true
#eval vk_payloadLayout_referenceTest_ok -- expect true
#eval vk_payloadLayout_quotientOffsets_ok -- expect true
#eval vk_validatePayloadLayout_ok -- expect true
#eval vk_payloadLayout_tooShort_err_ok -- expect true
#eval vk_payloadLayout_qcOffset_err_ok -- expect true
#eval vk_payloadLayout_qpOffset_err_ok -- expect true
#eval vk_validatePayloadLayout_ptr_err_ok -- expect true
#eval layoutConstants_matchYul_ok -- expect true
#eval vkHeaderWords_ok -- expect true
#eval memoryPhase_order_ok -- expect true

/-- A layout whose seven fixed low-memory pointers, scalar-inversion anchor,
    and PCS capacities all sit exactly where `VerifierMemoryLayout::validate`
    expects them, so every error arm below is a one-field perturbation of this.
    The `Ptr` fields are inert except `vkMptr`, which MEM:1039 reads through
    `Value::as_usize`; the remaining slots are zero because `validate` never
    looks at them. -/
def verifierLayoutFixture : VerifierMemoryLayout :=
  { map := { regions := [] },
    thetaWindows := ThetaWindowLayout.compatibility,
    constructorSmokeScratchMptr := lowMemoryScratchStart,
    constructorG1msmSmokeScratchMptr := 0,
    constructorG1msmSmokeInputBytes := 0,
    transcriptMptr := transcriptBufferStart,
    pcsPairingScratchMptr := pcsPairingScratchStart,
    verifierReturnMptr := verifierReturnBufferStart,
    quotientReturnMptr := quotientReturnBufferStart,
    vkMptr := ptrMemory (valueFromNat 0x4000),
    scalarInvScratchMptr := 0x4000 - modexpScratchBytes,
    challengeMptr := ptrMemory (valueFromNat 0),
    thetaMptr := ptrMemory (valueFromNat 0),
    betaMptr := ptrMemory (valueFromNat 0),
    gammaMptr := ptrMemory (valueFromNat 0),
    trashChallengeMptr := ptrMemory (valueFromNat 0),
    yMptr := ptrMemory (valueFromNat 0),
    xMptr := ptrMemory (valueFromNat 0),
    x1Mptr := ptrMemory (valueFromNat 0),
    x2Mptr := ptrMemory (valueFromNat 0),
    x3Mptr := ptrMemory (valueFromNat 0),
    x4Mptr := ptrMemory (valueFromNat 0),
    fComMptr := ptrMemory (valueFromNat 0),
    piMptr := ptrMemory (valueFromNat 0),
    accLhsMptr := ptrMemory (valueFromNat 0),
    accRhsMptr := ptrMemory (valueFromNat 0),
    xNMptr := ptrMemory (valueFromNat 0),
    xNMinus1InvMptr := ptrMemory (valueFromNat 0),
    lLastMptr := ptrMemory (valueFromNat 0),
    lBlindMptr := ptrMemory (valueFromNat 0),
    l0Mptr := ptrMemory (valueFromNat 0),
    instanceEvalMptr := ptrMemory (valueFromNat 0),
    quotientEvalMptr := ptrMemory (valueFromNat 0),
    quotientMptr := ptrMemory (valueFromNat 0),
    fEvalMptr := ptrMemory (valueFromNat 0),
    vMptr := ptrMemory (valueFromNat 0),
    finalComMptr := ptrMemory (valueFromNat 0),
    pairingLhsMptr := ptrMemory (valueFromNat 0),
    pairingRhsMptr := ptrMemory (valueFromNat 0),
    rotPointsMptr := ptrMemory (valueFromNat 0),
    x1PowersMptr := ptrMemory (valueFromNat 0),
    qComMptr := ptrMemory (valueFromNat 0),
    qEvalSetMptr := ptrMemory (valueFromNat 0),
    qEvalCptrMptr := ptrMemory (valueFromNat 0),
    g1IdentityMptr := ptrMemory (valueFromNat 0),
    reversedEvalsMptr := ptrMemory (valueFromNat 0),
    commsMptrBase := ptrMemory (valueFromNat 0),
    adviceCommsMptrBase := ptrMemory (valueFromNat 0),
    lookupMCommsMptrBase := ptrMemory (valueFromNat 0),
    permZCommsMptrBase := ptrMemory (valueFromNat 0),
    lookupHelperCommsMptrBase := ptrMemory (valueFromNat 0),
    lookupZCommsMptrBase := ptrMemory (valueFromNat 0),
    trashcanCommsMptrBase := ptrMemory (valueFromNat 0),
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0),
    selectorAccMptr := 0,
    batchInvertScratchMptr := 0,
    lagrangeDenomsMptr := 0,
    quotientTmpMptr := 0,
    quotientStackMptr := 0,
    quotientStackHi := 0,
    pcsQEvalSourceTableMptr := 0,
    pcsQComTraceScratchMptr := 0,
    pcsFinalMsmScratchMptr := 0,
    accMsmScratch := 0,
    accumulatorPairingBatchMptr := accumulatorPairingBatchPtr,
    finalPairingScratchMptr := finalPairingScratchStart,
    traceU256Mptr := 0,
    pcs := pcsMemoryRequirementsDefault }

/-- The reference's own `ThetaSlot` discriminants, LM:672-724, as data. -/
def thetaSlotExpected : List (ThetaSlot × Nat) :=
  [(ThetaSlot.theta, 0), (ThetaSlot.beta, 1), (ThetaSlot.gamma, 2),
   (ThetaSlot.trashChallenge, 3), (ThetaSlot.y, 4), (ThetaSlot.x, 5),
   (ThetaSlot.x1, 6), (ThetaSlot.x2, 7), (ThetaSlot.x3, 8), (ThetaSlot.x4, 9),
   (ThetaSlot.fCom, 10), (ThetaSlot.pi, 14), (ThetaSlot.accLhs, 18),
   (ThetaSlot.accRhs, 22), (ThetaSlot.xN, 26), (ThetaSlot.xNMinus1Inv, 27),
   (ThetaSlot.lLast, 28), (ThetaSlot.lBlind, 29), (ThetaSlot.l0, 30),
   (ThetaSlot.instanceEval, 31), (ThetaSlot.quotientEval, 32),
   (ThetaSlot.quotient, 33), (ThetaSlot.fEval, 38), (ThetaSlot.v, 39),
   (ThetaSlot.finalCom, 40), (ThetaSlot.pairingLhs, 44),
   (ThetaSlot.pairingRhs, 48)]

/-- `ThetaSlot.word` against the `#[repr(usize)]` discriminants of LM:672-724,
    plus that no two slots share a word. It rules out the word table drifting, or
    two slots colliding on one offset; it does NOT rule out the CONSTRUCTOR order
    of the inductive, because `word` is an explicit table rather than a derived
    `Ord` - which is exactly why the discriminants are ported that way. -/
def thetaSlot_word_ok : Bool :=
  thetaSlotExpected.all fun (s, n) => s.word == n
    && (thetaSlotExpected.map Prod.snd).eraseDups.length == thetaSlotExpected.length
    && thetaSlotExpected.length == 27

/-- `ThetaWindowLayout::compatibility` (MEM:87-118) at the seven offsets the
    reference pins with `debug_assert_eq!` (MEM:97-103), which the release profile
    compiles out (docs/REVIEW.md R-6). Asserting them here from the outside is
    what keeps the drift the debug asserts were written to catch from being
    invisible in the port. Numbers derive from LM:745-771: 48+4, +28, +65, alias,
    +56, +1+7, +4+7. -/
def thetaWindow_compatibility_ok : Bool :=
  let w := ThetaWindowLayout.compatibility
  w.rotPointsWord == 52 && w.x1PowersWord == 80 && w.qComWord == 145
    && w.qEvalSetWord == 145 && w.qEvalCptrWord == 201
    && w.g1IdentityWord == 209 && w.reversedEvalsWord == 220

/-- The five `theta_window` capacities and paddings, LM:745-753, including that
    `Q_COM_CAP_WORDS` is zero because the q_com window aliases q_eval_set
    (LM:762-764). That zero is what makes the Q_COM capacity arm of
    `VerifierMemoryLayout::validate` fire on any nonzero request at all. -/
def thetaWindow_caps_ok : Bool :=
  thetaRotPointsCapWords == 28 && thetaX1PowersCapWords == 65
    && thetaQEvalSetCapWords == 56 && thetaQEvalCptrPaddingWords == 7
    && thetaG1IdentityPaddingWords == 7 && thetaQComCapWords == 0

/-- `FinalMsmShape::from_terms` (MEM:389-394): input_bytes is terms times the
    160-byte G1MSM pair (LM:80), not terms times 128 or 192. -/
def finalMsmShape_fromTerms_ok : Bool :=
  (FinalMsmShape.fromTerms 0).inputBytes == 0
    && (FinalMsmShape.fromTerms 3).inputBytes == 480
    && (FinalMsmShape.fromTerms 17).inputBytes == 2720
    && (FinalMsmShape.fromTerms 17).terms == 17

/-- The baseline: the fixture satisfies all four checks of
    `VerifierMemoryLayout::validate` (MEM:974-1076). Every gate below is a
    one-field perturbation of it, so this is what makes them comparisons rather
    than assertions about an arbitrary record. -/
def verifierLayout_validate_ok : Bool := isOk verifierLayoutFixture.validate

/-- MEM:1012-1018. A fixed low-memory pointer that has moved off its constant.
    Rules out the drift table being read as a no-op, and rules out the message
    losing the got/expected pair. -/
def verifierLayout_fixedDrift_err_ok : Bool :=
  errIs (({ verifierLayoutFixture with transcriptMptr := 0x1020 } : VerifierMemoryLayout).validate)
    "fixed memory pointer transcript_mptr drifted: got 0x1020, expected 0x1000"

/-- MEM:1028-1036. A registered region below `LOW_MEMORY_SCRATCH_START`, which is
    the solc via-IR spill-window guard. It is a check on the MAP, not on the
    seven pointers, so it is exercised with the pointers untouched; the zero-length
    exemption at MEM:1029 is the other half of the same arm. -/
def lowRegion : MemoryRegion :=
  { name := "low", start := 0x100, len := 0x20,
    lifetime := MemoryLifetime.permanent }

def zeroLenLowRegion : MemoryRegion :=
  { name := "low", start := 0x100, len := 0x0,
    lifetime := MemoryLifetime.permanent }

def lowRegionMap : MemoryMap := { regions := [lowRegion] }

def zeroLenLowMap : MemoryMap := { regions := [zeroLenLowRegion] }

def verifierLayout_lowRegion_err_ok : Bool :=
  errIs (({ verifierLayoutFixture with map := lowRegionMap } : VerifierMemoryLayout).validate)
    ("memory region low starts at 0x100, below LOW_MEMORY_SCRATCH_START"
      ++ " (0x1000); it can overlap solc's via-IR stack-to-memory spill window"
      ++ " [0x80, reserved_end)")
    && isOk (({ verifierLayoutFixture with map := zeroLenLowMap } : VerifierMemoryLayout).validate)

/-- MEM:1038-1045: the scalar-inversion scratch must sit exactly
    `VK_MPTR - MODEXP_SCRATCH_BYTES` below the VK. The expected side is computed,
    not copied, so this also pins `Value::as_usize` on the `Ptr` read at MEM:1039. -/
def verifierLayout_scalarInv_err_ok : Bool :=
  errIs (({ verifierLayoutFixture with scalarInvScratchMptr := 0x3e00 } : VerifierMemoryLayout).validate)
    "scalar inversion scratch drifted: got 0x3e00, expected 0x3f00"

/-- MEM:1048-1071, all four capacity arms. The messages are DECIMAL (`{}` in the
    Rust), unlike the three hex arms above, and Q_COM's capacity is 0, so a
    one-word request already fails there. Rules out the four arms sharing one
    message, and rules out hex formatting leaking into them. -/
def pcsRotPoints : PcsMemoryRequirements :=
  { pcsMemoryRequirementsDefault with rotPointsWords := 29 }

def pcsX1Powers : PcsMemoryRequirements :=
  { pcsMemoryRequirementsDefault with x1PowersWords := 66 }

def pcsQCom : PcsMemoryRequirements :=
  { pcsMemoryRequirementsDefault with qComWords := 1 }

def pcsQEvalSet : PcsMemoryRequirements :=
  { pcsMemoryRequirementsDefault with qEvalSetWords := 57 }

def pcsWithinCaps : PcsMemoryRequirements :=
  { rotPointsWords := 28, x1PowersWords := 65, qComWords := 0, qEvalSetWords := 56,
    qEvalSourceTableWords := 0, qComTraceMsm := finalMsmShapeDefault,
    finalMsm := finalMsmShapeDefault }

def verifierLayout_pcsCapacity_err_ok : Bool :=
  errIs (({ verifierLayoutFixture with pcs := pcsRotPoints } : VerifierMemoryLayout).validate)
    "PCS scratch layout mismatch: ROT_POINTS_MPTR needs 29 word(s), capacity is 28"
    && errIs (({ verifierLayoutFixture with pcs := pcsX1Powers } : VerifierMemoryLayout).validate)
      "PCS scratch layout mismatch: X1_POWERS_MPTR needs 66 word(s), capacity is 65"
    && errIs (({ verifierLayoutFixture with pcs := pcsQCom } : VerifierMemoryLayout).validate)
      "PCS scratch layout mismatch: Q_COM_MPTR needs 1 word(s), capacity is 0"
    && errIs (({ verifierLayoutFixture with pcs := pcsQEvalSet } : VerifierMemoryLayout).validate)
      "PCS scratch layout mismatch: Q_EVAL_SET_MPTR needs 57 word(s), capacity is 56"
    && isOk (({ verifierLayoutFixture with pcs := pcsWithinCaps } : VerifierMemoryLayout).validate)

/-- ENC:596-601. The concrete arm is the wrapping `*int as usize`, so -1 becomes
    2^64-1 rather than 0; the symbolic arm is the `unreachable!()` rendered as a
    `Fault.panic` under rule R4. Rules out clamping the negative case and rules
    out the panic arm being dropped. -/
def value_asUsize_ok : Bool :=
  (match Value.asUsize (Value.integer 0x1000) with
   | .ok n => n == 0x1000
   | .error _ => false)
    && (match Value.asUsize (Value.integer (-1 : Int)) with
        | .ok n => n == (2 : Nat) ^ 64 - 1
        | .error _ => false)
    && (match Value.asUsize (Value.identifier "x" 4) with
        | .error (Midfall.Halo2.Fault.panic site) =>
          site == "proofs/solidity-verifier/src/lowering/encoding/mod.rs:599"
        | _ => false)

/-- `Value.asUsizeNat` is the total adapter MEM:1039 uses; this pins it to
    `Value.asUsize` on every concrete offset the reference can actually reach,
    including the wrapped negatives, so the adapter cannot drift from the port. -/
def asUsizeNat_agrees_ok : Bool :=
  [0, 1, 0x20, 0x1000, 0x1240, (2 : Int) ^ 63, (-1 : Int), (-0x100 : Int)].all
    fun i =>
      Value.asUsizeNat (Value.integer i)
        == match Value.asUsize (Value.integer i) with
           | .ok n => n
           | .error _ => 0

/-- Two permanent regions, both word-aligned and at or above the spill window,
    the first starting exactly AT `solidityReservedMemoryBytes`. -/
def permanentAtWindowEnd : MemoryRegion :=
  { name := "at_window_end", start := solidityReservedMemoryBytes,
    len := 2 * wordBytes, lifetime := MemoryLifetime.permanent }

def permanentAbove : MemoryRegion :=
  { name := "above", start := solidityReservedMemoryBytes + 2 * wordBytes,
    len := wordBytes, lifetime := MemoryLifetime.permanent }

def wellFormedMap : MemoryMap :=
  { regions := [permanentAtWindowEnd, permanentAbove] }

/-- A WELL-FORMED MAP SATISFIES `WellFormed`; the `Decidable` instance is what
    lets a gate read that Prop as a Bool at all. The scope is the three
    conditions of `wellFormedBool` together: tightening the spill-window bound
    from `solidityReservedMemoryBytes <= start` to a strict `<` reddens this
    gate, because the first region starts exactly on that bound. -/
def memoryMap_wellFormed_true_ok : Bool := decide wellFormedMap.WellFormed

/-- A word-aligned region inside the solc spill window: 0x40 is the free-memory
    pointer slot. -/
def spillWindowRegion : MemoryRegion :=
  { name := "spill", start := solidityFreeMemoryPointerSlot, len := wordBytes,
    lifetime := MemoryLifetime.permanent }

def spillWindowMap : MemoryMap := { regions := [spillWindowRegion] }

/-- A REGION BELOW THE SPILL WINDOW IS NOT WELL-FORMED. The region is aligned and
    alone in its map, so of the three conditions only the spill-window bound can
    answer here: replacing `solidityReservedMemoryBytes <= region.start` with
    `true` reddens this gate. -/
def memoryMap_spillWindow_false_ok : Bool := decide (! spillWindowMap.WellFormed)

/-- A region one byte past a word boundary, well above the spill window. -/
def unalignedRegion : MemoryRegion :=
  { name := "unaligned", start := 0x101, len := wordBytes,
    lifetime := MemoryLifetime.permanent }

def unalignedMap : MemoryMap := { regions := [unalignedRegion] }

/-- AN UNALIGNED START IS NOT WELL-FORMED. 0x101 is above the spill window and
    the length is a whole word, so only the alignment condition can answer here:
    replacing `region.start % wordBytes == 0` with `true` - or with a test on
    `region.len`, which is the same shape of bug in a different place - reddens
    this gate. -/
def memoryMap_unaligned_false_ok : Bool := decide (! unalignedMap.WellFormed)

/-- The two overlapping permanent ranges [0x100..0x140) and [0x120..0x160). -/
def overlapFirst : MemoryRegion :=
  { name := "first", start := 0x100, len := 0x40,
    lifetime := MemoryLifetime.permanent }

def overlapSecond : MemoryRegion :=
  { name := "second", start := 0x120, len := 0x40,
    lifetime := MemoryLifetime.permanent }

def overlappingPermanentMap : MemoryMap :=
  { regions := [overlapFirst, overlapSecond] }

/-- The same two byte ranges, live in two different phases. -/
def phaseTranscriptRegion : MemoryRegion :=
  { name := "first", start := 0x100, len := 0x40,
    lifetime := MemoryLifetime.phase MemoryPhase.transcript }

def phaseFinalMsmRegion : MemoryRegion :=
  { name := "second", start := 0x120, len := 0x40,
    lifetime := MemoryLifetime.phase MemoryPhase.pcsFinalMsm }

def overlappingPhasesMap : MemoryMap :=
  { regions := [phaseTranscriptRegion, phaseFinalMsmRegion] }

/-- OVERLAP IS A FUNCTION OF LIFETIME, NOT OF BYTES - the asymmetry MEM:274
    draws, and the reason a disjointness condition that ignores lifetimes is
    wrong in both directions rather than one. The same [0x100..0x140) and
    [0x120..0x160) pair is rejected when both lifetimes are permanent and
    accepted when the two are live in different phases. Dropping the
    `memoryLifetimeIntersects` conjunct reddens the second half; making the pair
    condition never fire reddens the first. -/
def memoryMap_overlapLifetime_asymmetry_ok : Bool :=
  (decide (! overlappingPermanentMap.WellFormed)) && decide overlappingPhasesMap.WellFormed

#eval thetaSlot_word_ok -- expect true
#eval thetaWindow_compatibility_ok -- expect true
#eval thetaWindow_caps_ok -- expect true
#eval finalMsmShape_fromTerms_ok -- expect true
#eval verifierLayout_validate_ok -- expect true
#eval verifierLayout_fixedDrift_err_ok -- expect true
#eval verifierLayout_lowRegion_err_ok -- expect true
#eval verifierLayout_scalarInv_err_ok -- expect true
#eval verifierLayout_pcsCapacity_err_ok -- expect true
#eval value_asUsize_ok -- expect true
#eval asUsizeNat_agrees_ok -- expect true
#eval memoryMap_wellFormed_true_ok -- expect true
#eval memoryMap_spillWindow_false_ok -- expect true
#eval memoryMap_unaligned_false_ok -- expect true
#eval memoryMap_overlapLifetime_asymmetry_ok -- expect true

/-- THE SIX TRACE TOPIC BASES ARE THE LITERALS THE REFERENCE ASSERTS. LM:877-882 is
    the reference's own test of this block, and it pins all six with
    debug-free assert_eq! - so this is a transcription checked against an outside
    source rather than against itself. The gaps (2000, 10000, 20000, 30000, 41000,
    60000) are the load-bearing part: 41000 rather than 40000 and 60000 rather than
    50000 are what LM:776-779 says external comparison scripts consume, so a
    "rounding" edit is a real divergence and this is the only thing in the tree
    that would notice. Transcribing all six to 1..6 reddens it. -/
def traceBases_ok : Bool :=
  Trace.pcsQueryBase == 2_000
    && Trace.proofCommitBase == 10_000
    && Trace.proofEvalBase == 20_000
    && Trace.quotientIdentityBase == 30_000
    && Trace.pcsSerializedPointSetBase == 41_000
    && Trace.selectorFoldBase == 60_000

#eval traceBases_ok -- expect true
end Midfall.Generator.LayoutKats
