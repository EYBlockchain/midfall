-- |
-- Midfall.Generator.Layout
--
-- The memory-layout and payload-layout layer: `lowering/layout/vk_payload.rs`
-- in full, the memory-planner core of `lowering/layout/memory.rs`, and the two
-- `Halo2VerifyingKey` methods those files feed - `payload_layout` and
-- `validate_payload_layout` - which `Models.lean` deferred precisely because
-- these types did not exist yet.
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
--   three places the Rust spells the overflow out with `checked_*` or
--   `ok_or_else` are ported as written and their unreachability is stated at the
--   site, not assumed.
-- * `#[cfg(test)]` items are ported where a ported test needs them
--   (`PayloadSection.byte_offset`, `PayloadSection.byte_len`,
--   `MemoryMap.region`, `PackedProgramCodec.decode_words`) and are marked as
--   test-only at the site, which is the convention `Exec/Circuit.lean` sets.

import Midfall.Common.Bytes
import Midfall.Generator.Models

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
    @formal-baseline. The Rust wraps the product in `.ok_or_else` because
    `checked_mul` can fail on `usize`; on `Nat` it cannot, so the arm is
    unreachable here and is not ported as a branch. -/
def VkPayloadLayout.byteOffset (self : VkPayloadLayout)
    (kind : PayloadSectionKind) : Except String Nat :=
  Except.map PayloadSection.byteOffset (self.requireSection kind)

/-- rust: VP:159-162 (`VkPayloadLayout::byte_len`, `#[cfg(test)]`)
    @formal-baseline; same unreachable-overflow note as
    `VkPayloadLayout.byteOffset`. -/
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

/-- rust: VP:76-94 (`VkPayloadLayout::for_vk`) @formal-baseline. -/
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

/-- rust: VP:84-91 via `VkPayloadLayout::for_vk` @formal-baseline: the section
    offsets in reservation order, used to reproduce the reference regression test. -/
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

end Midfall.Generator


/-! # Known-answer tests for the ported layout layer

Every gate names the wrong implementation it rules out, in the sense docs/REVIEW.md
R-38 states at the end of its entry. The expected sides here are of two kinds.
Most are the assertions of the reference's own test modules - `vk_payload.rs`
VP:242-321 and `memory.rs` MEM:1131-1257 - which this file does not control, so
they are evidence rather than transcription. The rest are cross-checks against
`Midfall/Yul/Externals.lean`, which derives the same numbers from EIP-2537 and
the EVM memory model rather than from this Rust. Where a Rust error arm cannot be
reached at all, that is said at the site and no gate is claimed for it. -/

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

/-- The fixture of VP:244, `VkPayloadLayout::for_vk(31, 3, 5, 7, 2)`. A failure
    here degrades to the empty layout, which makes every gate below fail loudly
    rather than quietly. -/
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
     `chunks_exact` semantics, which would silently drop bytes 32..37 - a
     truncated quotient program that still passes every length check upstream. -/
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

/-- `payload_layout` ON THE REFERENCE VK. With no quotient sections the header
     is the whole constant table, so the sections are 0, 31, 31, 31 and 35 - the
     three zero-width sections collapse onto the cursor. Rules out `checked_sub`
     being read as saturating subtraction, and out the commitment widths being
     dropped. -/
def vk_payloadLayout_offsets_ok : Bool :=
  match syntheticVk.payloadLayout with
  | .ok layout => vkPayloadSectionOffsets layout == [0, 31, 31, 31, 35]
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
     successful `payload_layout`, and no gate here claims otherwise; what is
     reachable, and what this gate covers, is the constructor-pointer check that
     follows it. -/
def vk_validatePayloadLayout_ok : Bool := isOk syntheticVk.validatePayloadLayout

/-- A CONSTANT TABLE SHORTER THAN ITS OWN QUOTIENT SECTIONS IS AN ERROR, NOT A
     WRAP. M:346-351. Rules out reading `checked_sub` as saturating `Nat`
     subtraction, which would silently build a header of width 0 and emit a VK
     whose quotient words sit at the start of the payload. -/
def vk_payloadLayout_tooShort_err_ok : Bool :=
  errIs ({ syntheticVk with quotientConstWords := 32, quotientProgramWords := 2 }
    : Halo2VerifyingKey).payloadLayout
    "VK constant table too short: constants=31 quotient_words=34"

/-- A STALE QUOTIENT-CONSTANT OFFSET IS CAUGHT. M:360-367. The offset is a
     separate field from the layout, so it can drift when the header changes;
     rules out the field being trusted. -/
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

/-- THE HEADER SCHEMA IS THE WIDTH `for_vk` IS CALLED WITH. LM:395-445 builds
     11 + 4 + 8 + 8 = 31 words, and 31 is the `header_words` the reference
     layout tests pass. Rules out the header schema and the payload layout
     disagreeing about where the commitments start. -/
def vkHeaderWords_ok : Bool :=
  vkHeaderScalarWords == 11 && vkHeaderG1BaseWord == 11
    && vkHeaderG2BaseWord == 15 && vkHeaderNegSG2BaseWord == 23
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

/-- THE PHASE ORDER IS THE `BTreeMap` ORDER. MEM:121-155 derives `Ord` in
     declaration order, and R6 turns the cursor map into a list kept in that same
     order. Rules out `Ord` deriving to any other permutation: the gate walks
     the sixteen phases and requires each to compare strictly below the next. -/
def memoryPhase_order_ok : Bool := memoryPhaseOrdered memoryPhaseOrder

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
#eval vk_payloadLayout_quotientOffsets_ok -- expect true
#eval vk_validatePayloadLayout_ok -- expect true
#eval vk_payloadLayout_tooShort_err_ok -- expect true
#eval vk_payloadLayout_qcOffset_err_ok -- expect true
#eval vk_payloadLayout_qpOffset_err_ok -- expect true
#eval vk_validatePayloadLayout_ptr_err_ok -- expect true
#eval layoutConstants_matchYul_ok -- expect true
#eval vkHeaderWords_ok -- expect true
#eval memoryPhase_order_ok -- expect true

end Midfall.Generator.LayoutKats
