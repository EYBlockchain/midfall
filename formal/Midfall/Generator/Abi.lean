-- |
-- Midfall.Generator.Abi
--
-- The codegen-time proof-calldata section map and the streaming
-- transcript-buffer bound: a port of
-- proofs/solidity-verifier/src/lowering/abi/proof.rs (537 lines), every non-test
-- item, in source order (rule R1).
--
-- CITATION NOTATION. Four prefixes, each named here with its file and its line
-- count, because docs/REVIEW.md R-38 finding 3 and R-40 F3 are both about cites
-- that silently pointed at the wrong file:
--
-- * AP:  proofs/solidity-verifier/src/lowering/abi/proof.rs (537 lines) - the
--   file this module ports.
-- * AM:  proofs/solidity-verifier/src/lowering/abi/mod.rs (9 lines) - the module
--   surface, accounted for below.
-- * PM:  proofs/solidity-verifier/src/lowering/protocol/mod.rs (1252 lines) -
--   cited only where this file consumes the ProtocolPlan row, which
--   Midfall/Generator/Protocol.lean ports.
-- * LM:  proofs/solidity-verifier/src/lowering/layout/mod.rs (927 lines) - the
--   two constant blocks AP:8-11 imports through `layout::{self, G1_BYTES,
--   WORD_BYTES}` and `layout::transcript`.
--
-- WHAT abi/mod.rs (AM) IS, AND WHY IT NEEDS NO COUNTERPART. Nine lines: a doc
-- comment, `pub(crate) mod proof;` (AM:7) and `pub(crate) use proof::{
-- ProofCalldataLayout, TranscriptBufferLayout};` (AM:9). Lean has no
-- module-vs-re-export distinction, so the re-export surface is absorbed: the two
-- re-exported types are plain defs in Midfall.Generator here, exactly as they are
-- in the Rust crate root's view. Two facts about AM:9 are worth keeping because
-- they constrain later packages. (1) It re-exports TWO of the four types the
-- file defines; `ProofSection` and `ProofLookupCommitmentsLayout` are not on
-- the list, and grep over the whole reference shows neither name occurs outside
-- proof.rs at all, so nothing outside this file can reach them and no counterpart
-- is missing. (2) The re-export is what plan Section 8's "Encoding, Abi,
-- Calldata" row hangs off: `ProofCalldataLayout` is the type Models.lean
-- defers `Halo2Verifier::validate_layout` (M:830-952) and
-- `Halo2QuotientEvaluator::validate_layout` (M:965-1005) on, and those two stay
-- deferred - this package ports the type, not the functions that consume it.
--
-- WHAT THIS FILE DOES NOT PORT, AND WHY.
--
-- * AP:371-537, the #[cfg(test)] mod tests. Rule R8's convention in this repo
--   (Layout.lean's header states it, Protocol.lean's applies it) is that test
--   items are ported where a ported gate needs them, and the ASSERTIONS are what
--   is worth keeping. All five #[test] fns and their shared builder map to gates
--   in the KAT section below:
--     protocol_shape (AP:377-418)                       -> protocolShape, TEST-ONLY
--     proof_layout_matches_legacy_offsets (AP:421-439)  -> proofLayout_matchesLegacyOffsets_ok
--     proof_layout_preserves_lookup_helper_accumulator_grouping
--                                       (AP:442-454)    -> proofLayout_preservesLookupGrouping_ok
--     proof_layout_rejects_commitment_order_drift (AP:457-475)
--                                       (AP:457-475)    -> proofLayout_rejectsOrderDrift_ok
--     proof_layout_handles_zero_lookup_and_trash (AP:478-487)
--                                       (AP:478-487)    -> proofLayout_handlesZeroLookupAndTrash_ok
--     transcript_layout_matches_current_conservative_bound (AP:490-501)
--                                       (AP:490-501)    -> transcriptLayout_conservativeBound_ok
--     transcript_layout_covers_multi_phase_advice_before_first_squeeze (AP:504-536)
--                                       (AP:504-536)    -> transcriptLayout_multiPhaseAdvice_ok
--   The one thing that does NOT transfer is named at proofLayout_rejectsOrderDrift_ok:
--   the Rust's #[should_panic(expected = "proof commitment plan drift")] asserts
--   on the panic PAYLOAD, and Fault.panic (Exec/Error.lean:56-58) carries a site
--   and no payload. Protocol.lean records the same limitation for the PM:642
--   panic; here it bites a reference test rather than a production message.
-- * LM:365-377 and LM:379-393, the transcript and abi constant blocks AP:8-11
--   imports. They are ported below rather than in Layout.lean, which carries the
--   LM:774-786 trace block for the same reason: these two blocks exist only to
--   size the transcript buffer and the calldata head, so they belong with the
--   consumer. Layout.lean does not define them and this package does not edit
--   Layout.lean.
--
-- DECISIONS RECORDED RATHER THAN TAKEN SILENTLY (rules R3, R5, R6).
--
-- * usize is Nat everywhere in this file (rule R5). Two sites do a subtraction
--   that could in principle underflow and one does a multiplication that could in
--   principle wrap; each says so AT THE SITE. The reference profile is release
--   (BASELINE.md "reference profile for the port: release"), where + and * wrap
--   rather than panic, and the debug profile where they panic - so on every value
--   a real plan can hold the two profiles and Nat agree, which is what
--   proofSection_arithNoWrap_ok states.
-- * Vec is List, following Layout.lean, Models.lean and Protocol.lean. PLAN
--   Section 4's R6 literally says "Vec becomes Array"; the whole Generator row
--   diverges from that and this file follows the row rather than the sentence,
--   which is the same call Protocol.lean's header records. Every Vec operation
--   used here - iter, map, filter, chain, flat_map, enumerate, sum, then_some,
--   once, collect, get, len - is order-preserving or order-independent, so the two
--   readings agree on everything observable.
-- * AP:105 uses Vec::get, which returns Option and does NOT panic out of range,
--   so it is List.get? and not an index. Confusing the two would turn a plan-drift
--   panic into a silent default, which is exactly what the assert exists to
--   prevent.
-- * AP:339 uses slice::get on phase_challenge_counts with unwrap_or(0), again a
--   non-panicking read; List.getD with default 0 is the same function.
-- * The three mutable cursors (cursor, read_idx, and the &mut they are passed as)
--   become an explicit state triple threaded through a foldlM. The Rust's
--   map-with-captured-mutable-state and a fold that appends in order are the same
--   function; rule R3's "mirror the iterator chain" is about truncation and
--   ordering, both of which are preserved.

import Midfall.Generator.Layout
import Midfall.Generator.Protocol
import Midfall.Halo2.Exec.Arith

namespace Midfall.Generator
open Midfall Midfall.Halo2

/-! ## The two constant blocks AP:8-11 imports (LM:365-377, LM:379-393) -/

/-- rust: LM:372 (`transcript::WORD_ABSORB_BYTES`) @formal-baseline. Defined in
    the Rust as `WORD_BYTES`, so it is a name and not a second number;
    abiAndTranscriptConstants_ok pins that reading. -/
def transcriptWordAbsorbBytes : Nat := wordBytes

/-- rust: LM:374 (`transcript::G1_ABSORB_BYTES`) @formal-baseline, = G1_BYTES. -/
def transcriptG1AbsorbBytes : Nat := g1Bytes

/-- rust: LM:376 (`transcript::POST_SQUEEZE_CUSHION_WORDS`) @formal-baseline. -/
def transcriptPostSqueezeCushionWords : Nat := 32

/-- rust: LM:381 (`abi::SELECTOR_BYTES`) @formal-baseline. -/
def abiSelectorBytes : Nat := 0x04

/-- rust: LM:384 (`abi::VERIFY_PROOF_HEAD_WORDS`) @formal-baseline. -/
def abiVerifyProofHeadWords : Nat := 2

/-- rust: LM:386 (`abi::VERIFY_PROOF_HEAD_BYTES`) @formal-baseline. -/
def abiVerifyProofHeadBytes : Nat := abiVerifyProofHeadWords * wordBytes

/-- rust: LM:389-390 (`abi::VERIFY_PROOF_PROOF_CPTR`) @formal-baseline. The
    reference's own layout test pins the value at LM:802 (`assert_eq!(
    abi::VERIFY_PROOF_PROOF_CPTR, 0x64)`), and abiAndTranscriptConstants_ok below
    reproduces all four of LM:800-803. -/
def abiVerifyProofProofCptr : Nat :=
  abiSelectorBytes + abiVerifyProofHeadBytes + wordBytes

/-- rust: LM:392 (`abi::VERIFY_PROOF_PROOF_HEAD_OFFSET`) @formal-baseline. Not
    used by proof.rs; ported because it is part of the same const block and
    models.rs:1235 reads it, so the next package that needs it must not have to
    invent it. -/
def abiVerifyProofProofHeadOffset : Nat := abiVerifyProofHeadBytes

/-! ## ProofSection (rust: AP:13-40) -/

/-- rust: AP:13-23 (struct ProofSection) @formal-baseline. Four usize fields in
    declaration order; #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]. -/
structure ProofSection where
  /-- rust: AP:16 (start: usize) - start byte offset in verifier calldata. -/
  start : Nat
  /-- rust: AP:18 (item_count: usize) - homogeneous item count. -/
  itemCount : Nat
  /-- rust: AP:20 (item_bytes: usize) - byte length of one item. -/
  itemBytes : Nat
  /-- rust: AP:22 (byte_len: usize) - total byte length, DERIVED by new and never
      recomputed. A hand-built ProofSection can therefore disagree with its own
      fields, which is what proofSection_new_derivesByteLen_ok pins. -/
  byteLen : Nat
  deriving BEq

/-- The #[derive(Default)] of AP:13: four zeros, i.e. an empty section at 0. -/
def proofSectionDefault : ProofSection :=
  { start := 0, itemCount := 0, itemBytes := 0, byteLen := 0 }

/-- rust: AP:27-34 (ProofSection::new), private (rule R1 keeps private helpers).
    HAZARD 5, stated at the site rather than assumed away: `item_count *
    item_bytes` is a usize multiply and the reference profile is release, where
    it WRAPS (BASELINE.md: no [profile.release] override, so overflow-checks is
    off). It cannot wrap here. item_bytes is only ever G1_BYTES (0x80),
    WORD_BYTES (0x20) or a value derived from them at AP:103, AP:131, AP:218 and
    AP:222, so wrapping needs item_count >= 2^59, i.e. a proof whose calldata is
    half an exabyte; every item_count in scope is a column, lookup, chunk,
    trashcan, quotient, eval or point-set count of a circuit that has to fit in a
    transaction. In the debug profile the same multiply PANICS instead of
    wrapping, so the two Rust profiles also agree on every reachable value and
    the Nat reading differs from neither. proofSection_arithNoWrap_ok asserts the
    concrete widths. -/
def ProofSection.new (start itemCount itemBytes : Nat) : ProofSection :=
  { start := start
    itemCount := itemCount
    itemBytes := itemBytes
    byteLen := itemCount * itemBytes }

/-- rust: AP:37-39 (ProofSection::end), the exclusive end offset. Same release-
    wrapping note as ProofSection.new: `start + byte_len` wraps only for offsets
    past 2^64, unreachable for the same reason, and panics rather than wraps in
    debug. -/
def ProofSection.end (self : ProofSection) : Nat := self.start + self.byteLen

/-! ## ProofLookupCommitmentsLayout (rust: AP:42-51) -/

/-- rust: AP:43-51 (struct ProofLookupCommitmentsLayout) @formal-baseline.
    #[derive(Clone, Debug, Default, Eq, PartialEq)]; field order preserved. -/
structure ProofLookupCommitmentsLayout where
  /-- rust: AP:46 (lookup: usize) - lookup argument index. -/
  lookup : Nat
  /-- rust: AP:48 (helpers: ProofSection) - chunk helper commitments. -/
  helpers : ProofSection
  /-- rust: AP:50 (accumulator: ProofSection) - the LogUp accumulator. -/
  accumulator : ProofSection
  deriving BEq

/-- The #[derive(Default)] of AP:43: the index 0 and two default sections. -/
def proofLookupCommitmentsLayoutDefault : ProofLookupCommitmentsLayout :=
  { lookup := 0, helpers := proofSectionDefault, accumulator := proofSectionDefault }

/-! ## ProofCalldataLayout (rust: AP:53-90) -/

/-- rust: AP:54-90 (struct ProofCalldataLayout) @formal-baseline. All seventeen
    fields in source order (rule R1), the eleven sections first and the six plain
    offsets after them, which is the Rust's grouping rather than a numeric one. -/
structure ProofCalldataLayout where
  /-- rust: AP:57 (proof_cptr: usize) - first proof payload byte. -/
  proofCptr : Nat
  /-- rust: AP:59 (advice_phases: Vec<ProofSection>) - advice grouped by phase. -/
  advicePhases : List ProofSection
  /-- rust: AP:61 (lookup_multiplicities: ProofSection) -/
  lookupMultiplicities : ProofSection
  /-- rust: AP:63 (permutation_products: ProofSection) -/
  permutationProducts : ProofSection
  /-- rust: AP:65 (lookups: Vec<ProofLookupCommitmentsLayout>) -/
  lookups : List ProofLookupCommitmentsLayout
  /-- rust: AP:67 (trash: ProofSection) -/
  trash : ProofSection
  /-- rust: AP:69 (quotient_limbs: ProofSection) -/
  quotientLimbs : ProofSection
  /-- rust: AP:71 (evals: ProofSection) - main scalar evaluation block. -/
  evals : ProofSection
  /-- rust: AP:73 (f_com: ProofSection) - the KZG f_com commitment. -/
  fCom : ProofSection
  /-- rust: AP:75 (q_evals: ProofSection) - KZG point-set evaluation scalars. -/
  qEvals : ProofSection
  /-- rust: AP:77 (pi: ProofSection) - the KZG proof commitment. -/
  pi : ProofSection
  /-- rust: AP:79 (quotient_comm_cptr: usize) -/
  quotientCommCptr : Nat
  /-- rust: AP:81 (eval_cptr: usize) -/
  evalCptr : Nat
  /-- rust: AP:83 (w_cptr: usize) -/
  wCptr : Nat
  /-- rust: AP:85 (q_eval_cptr: usize) -/
  qEvalCptr : Nat
  /-- rust: AP:87 (proof_end: usize) - end byte offset, exclusive. -/
  proofEnd : Nat
  /-- rust: AP:89 (proof_len: usize) - payload byte length. AP:243 computes it as
      `proof_end - proof_cptr`, a usize subtraction. It cannot underflow: every
      section new writes a non-negative byte_len and every cursor advance at
      AP:113, AP:132, AP:219 and AP:223 sets the cursor to a section end, which is
      the old cursor plus a byte_len, so proof_end >= proof_cptr by induction.
      Said at the site per rule R5; proofLayout_sectionsTileExactly_ok is the
      concrete form. -/
  proofLen : Nat
  deriving BEq

/-- The #[derive(Default)] of AP:54: every usize 0, every section
    proofSectionDefault, and the two Vec fields empty. -/
def proofCalldataLayoutDefault : ProofCalldataLayout :=
  { proofCptr := 0
    advicePhases := []
    lookupMultiplicities := proofSectionDefault
    permutationProducts := proofSectionDefault
    lookups := []
    trash := proofSectionDefault
    quotientLimbs := proofSectionDefault
    evals := proofSectionDefault
    fCom := proofSectionDefault
    qEvals := proofSectionDefault
    pi := proofSectionDefault
    quotientCommCptr := 0
    evalCptr := 0
    wCptr := 0
    qEvalCptr := 0
    proofEnd := 0
    proofLen := 0 }
/-! ## impl ProofCalldataLayout (rust: AP:92-293)

Lean is order-sensitive: from_protocol (AP:122) calls take_commitment_section
(AP:95), and the Rust source order already puts the callee first, so no item
moves. The one item that is not a Rust top-level fn is word_section, the closure
AP:130-134 binds inside from_protocol; Lean cannot carry a let-bound closure
across a def, so it is hoisted to a def directly above its caller. Protocol.lean
does the same thing for the remapping closure at PM:377-398 and records it. -/

/-- rust: AP:95-115 (ProofCalldataLayout::take_commitment_section), private.

    The Rust takes `&mut read_idx` and `&mut cursor`; the port returns the
    updated pair, which is the same function. `label` is accepted and dropped:
    it reaches only the assert_eq! message at AP:106-110, and Fault.panic carries
    a site and no payload (Exec/Error.lean:56-58). The binder is therefore
    spelled _label here. That is a real loss against
    the reference - the Rust message names the failing local index, the phase
    label and both Debug renderings - and it is the same loss Protocol.lean
    records for the PM:642 panic. Nothing in the ported scope reads a panic
    payload, so the site is what a gate can pin. -/
def ProofCalldataLayout.takeCommitmentSection (protocol : ProtocolPlan)
    (readIdx cursor : Nat) (expected : CommitmentRead) (count : Nat) (_label : String) :
    Except Fault (ProofSection × Nat × Nat) := do
  -- AP:103
  let sect := ProofSection.new cursor count g1Bytes
  -- AP:104-112: `for local in 0..count`. `local` appears only in the message,
  -- so the loop body is a check on read_idx and an increment of it.
  let readIdx ← (List.range count).foldlM
    (fun idx _ => do
      -- AP:105: Vec::get, i.e. Option, not an index panic.
      let actual := protocol.proof.commitments[idx]?
      -- AP:106-110: assert_eq!(actual, Some(expected), ...). A real assert_eq!,
      -- so it aborts in the release profile too (rule R4).
      if actual != some expected then
        throw (Fault.panic "proofs/solidity-verifier/src/lowering/abi/proof.rs:106")
      Except.ok (idx + 1))
    readIdx
  -- AP:113-114
  Except.ok (sect, readIdx, sect.end)

/-- rust: AP:130-134, the `word_section` closure inside from_protocol, hoisted.
    It takes `&mut usize` in the Rust, so the port returns the new cursor. -/
def ProofCalldataLayout.wordSection (cursor itemCount : Nat) : ProofSection × Nat :=
  let sect := ProofSection.new cursor itemCount wordBytes
  (sect, sect.end)

/-- rust: AP:122-245 (ProofCalldataLayout::from_protocol) @formal-baseline. The
    bulk of the file: it replays the protocol proof-read order and reserves one
    section per group.

    Three things to notice before reading the code.

    * The two cursors are threaded, not mutated. The Rust's
      `.map(|count| Self::take_commitment_section(protocol, &mut read_idx, &mut
      cursor, ..))` followed by `.collect::<Vec<_>>()` is a left-to-right fold
      that appends in order, which is what foldlM with an accumulator list does;
      rule R3's ordering obligation is satisfied because both visit the input in
      order and both keep every element.
    * AP:210-214 is an assert_eq! and so aborts in release (rule R4). It is the
      only place that checks the commitment plan was consumed exactly, and
      proofLayout_rejectsTrailingCommitments_ok is what makes it observable.
    * AP:243's subtraction cannot underflow; see the field comment. -/
def ProofCalldataLayout.fromProtocol (protocol : ProtocolPlan) (proofCptr numEvals numPointSets : Nat) :
    Except Fault ProofCalldataLayout := do
  -- AP:128-129: cursor = proof_cptr, read_idx = 0.
  -- AP:136-150: one advice section per user phase, in phase order.
  let (advicePhases, readIdx1, cursor1) ←
    protocol.numUserAdvices.foldlM
      (fun st count => do
        let (phases, readIdx, cursor) := st
        let (sect, readIdx, cursor) ←
          ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor
            CommitmentRead.advice count "advice phase"
        Except.ok (phases ++ [sect], readIdx, cursor))
      (([] : List ProofSection), 0, proofCptr)
  -- AP:151-158
  let (lookupMultiplicities, readIdx2, cursor2) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx1 cursor1
      CommitmentRead.lookupMultiplicity protocol.numLookups "lookup multiplicity"
  -- AP:159-166
  let (permutationProducts, readIdx3, cursor3) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx2 cursor2
      CommitmentRead.permutationProduct protocol.numPermutationZs "permutation product"
  -- AP:167-191: enumerate + map, so the lookup index is the position in
  -- lookup_chunks, and each row reserves helpers and THEN the accumulator.
  let (lookups, readIdx4, cursor4) ←
    ((List.range protocol.lookupChunks.length).zip protocol.lookupChunks).foldlM
      (fun st pair => do
        let (rows, readIdx, cursor) := st
        let (lookup, chunks) := pair
        let (helpers, readIdx, cursor) ←
          ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor
            CommitmentRead.lookupHelper chunks "lookup helper"
        let (accumulator, readIdx, cursor) ←
          ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor
            CommitmentRead.lookupAccumulator 1 "lookup accumulator"
        Except.ok (rows ++ [{ lookup := lookup, helpers := helpers,
                              accumulator := accumulator }], readIdx, cursor))
      (([] : List ProofLookupCommitmentsLayout), readIdx3, cursor3)
  -- AP:192-199
  let (trash, readIdx5, cursor5) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx4 cursor4
      CommitmentRead.trash protocol.numTrashcans "trash"
  -- AP:201: the cursor is snapshotted BEFORE the quotient limbs are reserved.
  let quotientCommCptr := cursor5
  let (quotientLimbs, readIdx6, cursor6) ←
    ProofCalldataLayout.takeCommitmentSection protocol readIdx5 cursor5
      CommitmentRead.quotient protocol.numQuotients "quotient limb"
  -- AP:210-214
  if readIdx6 != protocol.proof.commitments.length then
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/abi/proof.rs:210")
  -- AP:215-216
  let evalCptr := cursor6
  let (evals, cursor7) := ProofCalldataLayout.wordSection cursor6 numEvals
  -- AP:217-219
  let wCptr := cursor7
  let fCom := ProofSection.new cursor7 1 g1Bytes
  let cursor8 := fCom.end
  -- AP:220-223
  let qEvalCptr := cursor8
  let (qEvals, cursor9) := ProofCalldataLayout.wordSection cursor8 numPointSets
  let pi := ProofSection.new cursor9 1 g1Bytes
  let cursor10 := pi.end
  -- AP:224
  let proofEnd := cursor10
  -- AP:226-244: the struct literal, field order as written. Protocol.lean uses
  -- the same let-then-return shape for the PM:616-641 literal.
  let layout : ProofCalldataLayout :=
    { proofCptr := proofCptr
      advicePhases := advicePhases
      lookupMultiplicities := lookupMultiplicities
      permutationProducts := permutationProducts
      lookups := lookups
      trash := trash
      quotientLimbs := quotientLimbs
      evals := evals
      fCom := fCom
      qEvals := qEvals
      pi := pi
      quotientCommCptr := quotientCommCptr
      evalCptr := evalCptr
      wCptr := wCptr
      qEvalCptr := qEvalCptr
      proofEnd := proofEnd
      proofLen := proofEnd - proofCptr }
  Except.ok layout

/-- rust: AP:248-258 (ProofCalldataLayout::non_quotient_g1_count). Five terms,
    the first and fourth of which are sums over a Vec. The Rust writes
    `.sum::<usize>()` twice; a Nat fold is the same function (rule R6 note in
    the header). -/
def ProofCalldataLayout.nonQuotientG1Count (self : ProofCalldataLayout) : Nat :=
  let adviceSum := (self.advicePhases.map fun sect => sect.itemCount).foldl (fun a b => a + b) 0
  let lookupSum := (self.lookups.map fun lookup =>
    lookup.helpers.itemCount + lookup.accumulator.itemCount).foldl (fun a b => a + b) 0
  adviceSum + self.lookupMultiplicities.itemCount + self.permutationProducts.itemCount
    + lookupSum + self.trash.itemCount

/-- rust: AP:261-263 (ProofCalldataLayout::commitment_g1_count): the
    transcript-facing count, i.e. non-quotient plus the quotient limbs. -/
def ProofCalldataLayout.commitmentG1Count (self : ProofCalldataLayout) : Nat :=
  self.nonQuotientG1Count + self.quotientLimbs.itemCount

/-- rust: AP:266-268 (ProofCalldataLayout::total_g1_count): the
    Solidity-facing payload count, i.e. the transcript commitments plus f_com and
    pi. Note that f_com and pi are counted by item_count and not as 1, so a
    hand-built layout with a two-item f_com would be counted as two - the Rust
    reads the field, and so does this. -/
def ProofCalldataLayout.totalG1Count (self : ProofCalldataLayout) : Nat :=
  self.commitmentG1Count + self.fCom.itemCount + self.pi.itemCount

/-- rust: AP:271-292 (ProofCalldataLayout::commitment_read_groups)
    @formal-baseline. The group sizes in the exact read/repack order.

    HAZARD 6, and the answer is: this is NOT the same function as
    ProtocolPlan::commitment_read_groups (PM:665-690), which Protocol.lean ports
    separately, and nothing in the reference asserts they agree. The two are
    spelled differently - PM filters two single pushes with two ifs, this one
    filters a two-element array; PM reads the protocol's counts, this reads the
    layout's item_counts - and they agree only because from_protocol copies each
    count into the section it reserves. So they CAN disagree: a layout that was
    not produced by from_protocol (proofCalldataLayoutDefault, or a struct update)
    reports its own item_counts while the plan reports its counts. The reference
    has no test for that; commitmentReadGroups_agreesWithProtocolPlan_ok is the
    gate this package adds, over every shape the reference's own tests use plus
    the Protocol.lean fixture, and commitmentReadGroups_disagreeWhenHandBuilt_ok
    pins the disagreement case so the distinction cannot be tidied away later.

    The iterator chain is mirrored exactly (rule R3): advice phases filtered for
    non-zero, then the two-element array filtered for non-zero, then a flat_map
    with NO filter - so a zero-chunk lookup contributes [0, 1], not nothing -
    then then_some for trash, then once for the quotient limbs.

    WHAT AP:486 DOES AND DOES NOT PIN, corrected after perturbation: its shape is
    vec![0, 4] / vec![] / 0 / 0 / 1, so it pins the advice-phase filter (the 0
    phase is dropped), the multiplicity/permutation filter (both 0) and the trash
    filter (0 dropped) - but its quotient count is 1, so it does NOT pin the last
    link, the unconditional quotient push. That behaviour is pinned instead by
    commitmentReadGroups_pushesEmptyQuotient_ok, which is this package's own case
    and has no counterpart in the reference. -/
def ProofCalldataLayout.commitmentReadGroups (self : ProofCalldataLayout) : List Nat :=
  let groups0 := (self.advicePhases.map fun sect => sect.itemCount).filter fun count => count != 0
  let pair := [self.lookupMultiplicities.itemCount, self.permutationProducts.itemCount]
  let groups1 := groups0 ++ pair.filter (fun count => count != 0)
  let perLookup := self.lookups.flatMap fun lookup =>
    [lookup.helpers.itemCount, lookup.accumulator.itemCount]
  let groups2 := groups1 ++ perLookup
  let groups3 := if self.trash.itemCount != 0 then groups2 ++ [self.trash.itemCount] else groups2
  groups3 ++ [self.quotientLimbs.itemCount]

/-! ## TranscriptBufferLayout (rust: AP:295-369) -/

/-- rust: AP:296-306 (struct TranscriptBufferLayout) @formal-baseline. A
    conservative bound for the streaming transcript buffer; four usize fields,
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]. -/
structure TranscriptBufferLayout where
  /-- rust: AP:299 (initial_run_bytes: usize) - max bytes before the first
      challenge squeeze. -/
  initialRunBytes : Nat
  /-- rust: AP:301 (eval_run_bytes: usize) -/
  evalRunBytes : Nat
  /-- rust: AP:303 (total_run_bytes: usize) -/
  totalRunBytes : Nat
  /-- rust: AP:305 (words: usize) - required EVM words above
      TRANSCRIPT_BUFFER_START. -/
  words : Nat
  deriving BEq

/-- The #[derive(Default)] of AP:296: four zeros. -/
def transcriptBufferLayoutDefault : TranscriptBufferLayout :=
  { initialRunBytes := 0, evalRunBytes := 0, totalRunBytes := 0, words := 0 }

/-- rust: AP:318-368 (TranscriptBufferLayout::from_proof_layout) @formal-baseline.

    THIS IS THE CODE THAT COMMIT 6b3d209 FIXED, and BASELINE.md records why it
    has to survive on both paths ("The transcript buffer sizing and const-table
    fix (6b3d209) is an ancestor of all three branches, so it survives on both
    paths by construction"). The fix is the loop at AP:336-342: the pre-squeeze
    run counts every advice phase up to and INCLUDING the first phase that owns a
    challenge, not just the first phase. The comment at AP:327-335 says what the
    old bound did - it under-sized the buffer for a valid "advice in an early
    phase, challenge in a later phase" shape and let the G1 absorb loop overrun
    VK_MPTR - and AP:529-535 is the reference's own test that the fix was
    load-bearing. transcriptLayout_multiPhaseAdvice_ok reproduces that test,
    including its two inequality assertions, and the perturbation recorded there
    is the one that puts the old bound back.

    Two readings of the loop that matter:

    * AP:339 reads phase_challenge_counts with slice::get + unwrap_or(0), so a
      SHORTER slice means "this phase owns no challenge" and the loop keeps
      going. An empty slice therefore sums every phase, which is what the doc
      comment at AP:314-317 promises and what
      transcriptLayout_emptyChallengeCountsSumsEveryPhase_ok pins.
    * The addition happens BEFORE the break test (AP:338 then AP:339-341), so the
      challenge-bearing phase's own advices are included. Swapping those two
      lines is the single-token perturbation that reddens
      transcriptLayout_multiPhaseAdvice_ok. -/
def TranscriptBufferLayout.fromProofLayout (proof : ProofCalldataLayout)
    (numInstances : Nat) (phaseChallengeCounts : List Nat) : TranscriptBufferLayout :=
  let wordAbsorb := transcriptWordAbsorbBytes
  let g1Absorb := transcriptG1AbsorbBytes
  let squeezeCushion := transcriptPostSqueezeCushionWords * wordBytes
  -- AP:336-342, with the early break kept as a stopped flag (rule R3).
  let preSqueezeAdvices :=
    ((List.range proof.advicePhases.length).zip proof.advicePhases).foldl
      (fun st pair =>
        let (phase, sect) := pair
        if st.snd then st
        else (st.fst + sect.itemCount, (phaseChallengeCounts.getD phase 0) > 0))
      (0, false)
  -- AP:343-348
  let initialRunBytes :=
    wordAbsorb + g1Absorb + wordAbsorb + numInstances * wordAbsorb
      + preSqueezeAdvices.fst * g1Absorb + squeezeCushion
  -- AP:350-353
  let evalRunBytes :=
    proof.quotientLimbs.byteLen + proof.evals.byteLen + proof.qEvals.byteLen + squeezeCushion
  -- AP:355-357. Note the Rust repeats POST_SQUEEZE_CUSHION_WORDS here but
  -- multiplies it by word_absorb rather than by WORD_BYTES (AP:357 versus the
  -- squeeze_cushion of AP:325). The two are equal because LM:372 defines
  -- WORD_ABSORB_BYTES = WORD_BYTES, so this is not a divergence - but it is a
  -- second spelling of the same cushion, and transcriptCushionSpellingsAgree_ok
  -- is what stops the equality from being assumed.
  let totalScalarBytes :=
    proof.evals.byteLen + proof.qEvals.byteLen
      + transcriptPostSqueezeCushionWords * wordAbsorb
  -- AP:358-359
  let totalRunBytes :=
    wordAbsorb + proof.totalG1Count * g1Absorb + totalScalarBytes + squeezeCushion
  -- AP:361-367
  let maxBytes := max (max initialRunBytes evalRunBytes) totalRunBytes
  { initialRunBytes := initialRunBytes
    evalRunBytes := evalRunBytes
    totalRunBytes := totalRunBytes
    words := divCeil maxBytes wordBytes }

end Midfall.Generator

/-! # Known-answer tests

Two kinds of expected value, and they are not equally strong.

The first kind is the reference's own assertions, AP:371-537, which this file does
not control: proofLayout_matchesLegacyOffsets_ok,
proofLayout_preservesLookupGrouping_ok, proofLayout_rejectsOrderDrift_ok,
proofLayout_handlesZeroLookupAndTrash_ok, transcriptLayout_conservativeBound_ok
and transcriptLayout_multiPhaseAdvice_ok are transcriptions of the six #[test]
fns. Where the Rust asserts an inequality this file asserts the exact value as
well, and says so.

The second kind is arithmetic derived here - the hand-computed byte offsets in
proofLayout_matchesLegacyOffsets_ok and the two agreement gates for hazard 6 -
checked against the port and not against an outside source.

Per docs/REVIEW.md R-41 every gate below names the perturbation that reddens it,
and each of those perturbations was actually run; the record is in the package
report and, where the gate's own doc makes a claim, at the gate. -/

namespace Midfall.Generator.AbiKats

open Midfall Midfall.Halo2 Midfall.Generator

/-- Reading an Except Fault as "it failed at exactly this panic site", which is
    the strongest thing Fault.panic can express (Exec/Error.lean:56-58). -/
def panickedAtSite {alpha : Type} (e : Except Fault alpha) (site : String) : Bool :=
  match e with
  | .error (Fault.panic s) => s == site
  | _ => false

/-- Vec::swap (AP:472) for the case the reference actually uses it in, i.e. two
    in-range indices with i <= j: exchange the two entries and leave everything
    else alone. Returns none when either index is out of range, which is the
    reference's swap panicking, so a gate that gets an index wrong fails loudly
    instead of comparing an unswapped plan. -/
def swapIdx {α : Type} (xs : List α) (i j : Nat) : Option (List α) := do
  let a ← (xs.drop i).head?
  let b ← (xs.drop j).head?
  pure (xs.take i ++ [b] ++ (xs.drop (i + 1)).take (j - i - 1) ++ [a] ++ xs.drop (j + 1))

/-- rust: AP:377-418 (protocol_shape), the reference test module's synthetic
    proof-read-plan builder, so TEST-ONLY (rule R8: ported because the gates that
    transcribe AP:421-536 cannot be stated without it). Field order and the
    ..ProtocolPlan::default() fill are the Rust's: everything not named here is
    protocolPlanDefault's.

    Note what this builder does NOT do: it does not call
    ProtocolPlan::from_constraint_system, so the plans it builds are not
    circuit-derived and plan.validate would reject several of them (no PCS
    queries, no trace ids). That is the Rust's design - the layout code only
    reads the commitment stream and the counts - and it is why the gates below
    call fromProtocol directly rather than going through a validated plan. -/
def protocolShape (userAdvices lookupChunks : List Nat) (permutationZs trashcans quotients : Nat) :
    ProtocolPlan :=
  -- AP:384
  let numLookups := lookupChunks.length
  -- AP:385-400: the extends, in order.
  let commitments :=
    List.replicate (userAdvices.foldl (fun a b => a + b) 0) CommitmentRead.advice
      ++ List.replicate numLookups CommitmentRead.lookupMultiplicity
      ++ List.replicate permutationZs CommitmentRead.permutationProduct
      ++ (lookupChunks.flatMap fun chunks =>
            List.replicate chunks CommitmentRead.lookupHelper
              ++ [CommitmentRead.lookupAccumulator])
      ++ List.replicate trashcans CommitmentRead.trash
      ++ List.replicate quotients CommitmentRead.quotient
  -- AP:404-409: 0..(number of Advice reads)
  let numAdviceReads := (commitments.filter fun read => read == CommitmentRead.advice).length
  { protocolPlanDefault with
    numUserAdvices := userAdvices
    adviceIndices := List.range numAdviceReads
    lookupChunks := lookupChunks
    numLookups := numLookups
    numPermutationZs := permutationZs
    numTrashcans := trashcans
    numQuotients := quotients
    proof := { proofReadPlanDefault with commitments := commitments } }

/-- The four LM:800-803 assertions and the three LM:923-925 ones, ported as gates
    because the constants they pin are ported here and nowhere else. Rules out a
    transcript absorb width being written as a word count, and rules out
    VERIFY_PROOF_PROOF_CPTR being read as 0x40 (the ABI head offset) instead of
    0x64 - the difference is the proof length word, and every offset in
    proofLayout_matchesLegacyOffsets_ok moves by 0x24 if it is got wrong.
    PERTURBATIONS RUN: P6 (abiVerifyProofHeadWords 2 -> 1) reddens this gate and
    proofLayout_matchesLegacyOffsets_ok; P21 (transcriptWordAbsorbBytes -> 64) reddens
    this gate, transcriptCushionSpellingsAgree_ok and all three transcript gates. -/
def abiAndTranscriptConstants_ok : Bool :=
  abiSelectorBytes == 0x04
    && abiVerifyProofHeadBytes == 0x40
    && abiVerifyProofProofCptr == 0x64
    && abiVerifyProofProofHeadOffset == 0x40
    && transcriptWordAbsorbBytes == 0x20
    && transcriptG1AbsorbBytes == 0x80
    && transcriptPostSqueezeCushionWords == 32

/-- HAZARD-5 ADJACENT, and an honest negative result. AP:366 computes
    `max_bytes.div_ceil(WORD_BYTES)`. Perturbing it to floor division reddens NO
    gate in this file, and the reason is a property of the inputs rather than of the
    gate: every term of all three runs is a multiple of WORD_BYTES - word_absorb =
    0x20, g1_absorb = 0x80, the cushion is 32 words, and every byte_len is
    item_count * 0x20 or item_count * 0x80 - so max_bytes is always word-aligned
    and div_ceil and / agree on everything this function can be handed. Rather than
    leave that as prose, the rows below assert the precondition itself, so a future
    change that made one run unaligned (a byte-granular cushion, say) reddens this
    gate and the div_ceil question becomes live again. That is the strongest thing
    available here: the rounding is unobservable, and the alignment that makes it
    unobservable is pinned.
    PERTURBATIONS RUN: P11 (div_ceil -> floor division) reddens NOTHING in the file, which is
    the limitation stated above and the reason this gate exists; P24 (cushion one byte
    past word alignment) reddens this gate plus all three transcript gates, so the
    precondition is live; P5 (cushion 32 -> 16 words) leaves this gate green, correctly,
    because 16 words is still word-aligned. -/
def transcriptRunsAreWordAligned_ok : Bool :=
  match ProofCalldataLayout.fromProtocol (protocolShape [2, 1] [2, 0] 1 1 3) 0x64 5 2 with
  | .error _ => false
  | .ok proof =>
    let t := TranscriptBufferLayout.fromProofLayout proof 7 [0, 1]
    t.initialRunBytes % wordBytes == 0
      && t.evalRunBytes % wordBytes == 0
      && t.totalRunBytes % wordBytes == 0
      && t.words * wordBytes == max (max t.initialRunBytes t.evalRunBytes) t.totalRunBytes
      && t.words == (max (max t.initialRunBytes t.evalRunBytes) t.totalRunBytes) / wordBytes

/-- The two derived constants must stay derived: LM:372 defines WORD_ABSORB_BYTES
    AS WORD_BYTES and LM:374 defines G1_ABSORB_BYTES AS G1_BYTES, and AP:325 and
    AP:357 then spell the cushion twice, once as
    POST_SQUEEZE_CUSHION_WORDS * WORD_BYTES and once as
    POST_SQUEEZE_CUSHION_WORDS * WORD_ABSORB_BYTES. That double spelling is only
    harmless while the identity holds, so it is asserted rather than assumed:
    this is the gate that reddens if LM:372 ever stops being WORD_BYTES.
    PERTURBATIONS RUN: P21 (transcriptWordAbsorbBytes -> 64) reddens this gate,
    abiAndTranscriptConstants_ok and the three transcript gates; P5 (cushion 32 -> 16)
    reddens this gate and the three transcript gates. -/
def transcriptCushionSpellingsAgree_ok : Bool :=
  transcriptWordAbsorbBytes == wordBytes
    && transcriptG1AbsorbBytes == g1Bytes
    && transcriptPostSqueezeCushionWords * transcriptWordAbsorbBytes
      == transcriptPostSqueezeCushionWords * wordBytes
    && transcriptPostSqueezeCushionWords * wordBytes == 1024
    && g1Bytes == Midfall.Yul.g1Bytes

/-- ProofSection::new derives byte_len and end derives the exclusive end
    (AP:32, AP:38). HAZARD 5: both are release-wrapping usize ops. The concrete
    widths are what makes the argument checkable rather than rhetorical - every
    item_bytes this file ever passes is g1Bytes (0x80) or wordBytes (0x20), so
    wrapping needs an item_count of 2^59 or 2^59 respectively, and the counts
    come from circuit shapes. Rules out byte_len being computed as
    item_count + item_bytes, as start * byte_len, or left at the caller's value.
    PERTURBATIONS RUN: P7 (byteLen := itemCount + itemBytes) reddens this gate,
    proofSection_new_derivesByteLen_ok, three layout gates and both transcript gates; P15
    (end := start - byteLen) reddens this gate and four layout gates. -/
def proofSection_arithNoWrap_ok : Bool :=
  (ProofSection.new 0x64 3 g1Bytes).byteLen == 3 * 128
    && (ProofSection.new 0x64 3 g1Bytes).end == 0x64 + 384
    && (ProofSection.new 0 0 wordBytes).byteLen == 0
    && (ProofSection.new 0 0 wordBytes).end == 0
    && (ProofSection.new 0x1000 5 wordBytes).byteLen == 160
    && (ProofSection.new 0x1000 5 wordBytes).end == 0x1000 + 160
    && proofSectionDefault.end == 0

/-- new is the only thing that fills byte_len, and every section in a layout
    comes from new, so byte_len == item_count * item_bytes holds for every
    section of every layout fromProtocol builds. Rules out a section being built
    with a stale or hand-written byte_len, which would move eval_run_bytes and
    total_run_bytes without moving any offset. -/
def proofSection_new_derivesByteLen_ok : Bool :=
  match ProofCalldataLayout.fromProtocol (protocolShape [2, 1] [2, 0] 1 1 3) 0x64 5 2 with
  | .ok layout =>
    (layout.advicePhases.all fun sect => sect.byteLen == sect.itemCount * sect.itemBytes)
      && layout.lookupMultiplicities.byteLen == layout.lookupMultiplicities.itemCount * g1Bytes
      && layout.permutationProducts.byteLen == layout.permutationProducts.itemCount * g1Bytes
      && (layout.lookups.all fun row =>
            row.helpers.byteLen == row.helpers.itemCount * g1Bytes
              && row.accumulator.byteLen == row.accumulator.itemCount * g1Bytes)
      && layout.trash.byteLen == layout.trash.itemCount * g1Bytes
      && layout.quotientLimbs.byteLen == layout.quotientLimbs.itemCount * g1Bytes
      && layout.evals.byteLen == layout.evals.itemCount * wordBytes
      && layout.fCom.byteLen == layout.fCom.itemCount * g1Bytes
      && layout.qEvals.byteLen == layout.qEvals.itemCount * wordBytes
      && layout.pi.byteLen == layout.pi.itemCount * g1Bytes
  | .error _ => false

/-- rust: AP:421-439 (proof_layout_matches_legacy_offsets), transcribed. The
    arithmetic on the right of each assertion is the Rust's own spelling
    (`3 + 2 + 1 + 4 + 1`, `(non_quotient_g1s + 3 + 2) * G1_BYTES + (5 + 2) *
    WORD_BYTES`) so the gate can be checked against the test and not only against
    the port.

    PERTURBATIONS RUN: P3 (quotient_comm_cptr one byte late), P6, P7, P8 (wordSection at the
    G1 width), P10, P15, P16 (cursor not advanced), P21 and P22 each redden this gate. An
    earlier draft of this note claimed a cursor-argument swap that was not run; the list
    here is what was. -/
def proofLayout_matchesLegacyOffsets_ok : Bool :=
  let protocol := protocolShape [2, 1] [2, 0] 1 1 3
  let proofCptr := abiVerifyProofProofCptr
  match ProofCalldataLayout.fromProtocol protocol proofCptr 5 2 with
  | .error _ => false
  | .ok layout =>
    let nonQuotientG1s := 3 + 2 + 1 + 4 + 1
    layout.nonQuotientG1Count == nonQuotientG1s
      && layout.quotientCommCptr == proofCptr + nonQuotientG1s * g1Bytes
      && layout.evalCptr == layout.quotientCommCptr + 3 * g1Bytes
      && layout.wCptr == layout.evalCptr + 5 * wordBytes
      && layout.qEvalCptr == layout.wCptr + g1Bytes
      && layout.proofLen == (nonQuotientG1s + 3 + 2) * g1Bytes + (5 + 2) * wordBytes
      -- the exact numbers, so a drift that leaves every RELATION intact still
      -- shows: 0x64 + 1408 = 1508, + 384 = 1892, + 160 = 2052, + 128 = 2180,
      -- and proof_len 2272.
      && layout.quotientCommCptr == 1508
      && layout.evalCptr == 1892
      && layout.wCptr == 2052
      && layout.qEvalCptr == 2180
      && layout.proofEnd == 2372
      && layout.proofLen == 2272
      && layout.proofCptr == proofCptr

/-- rust: AP:442-454
    (proof_layout_preserves_lookup_helper_accumulator_grouping), transcribed. The
    point of the shape is the SECOND lookup having a zero-chunk first lookup
    neighbour: helpers of lookup 1 start where lookup 0's accumulator ends, so a
    grouping that reserved the accumulator before the helpers, or that skipped a
    zero-chunk lookup's accumulator, moves 6*G1 and 7*G1 together and reddens
    the last two conjuncts while leaving every count green.
    PERTURBATIONS RUN: P13 (the accumulator section filled with the helpers section) reddens
    this gate and the hazard-6 agreement gate; P7 and P15 reach it through the offsets.
    The zero-chunk filter was not run separately - P13 is what exercises the pairing. -/
def proofLayout_preservesLookupGrouping_ok : Bool :=
  let protocol := protocolShape [1] [2, 1] 0 0 2
  match ProofCalldataLayout.fromProtocol protocol 0 0 0 with
  | .error _ => false
  | .ok layout =>
    layout.lookups.length == 2
      && (layout.lookups.getD 0 proofLookupCommitmentsLayoutDefault).helpers.itemCount == 2
      && (layout.lookups.getD 0 proofLookupCommitmentsLayoutDefault).accumulator.itemCount == 1
      && (layout.lookups.getD 0 proofLookupCommitmentsLayoutDefault).helpers.start == 3 * g1Bytes
      && (layout.lookups.getD 0 proofLookupCommitmentsLayoutDefault).accumulator.start
        == 5 * g1Bytes
      && (layout.lookups.getD 1 proofLookupCommitmentsLayoutDefault).helpers.itemCount == 1
      && (layout.lookups.getD 1 proofLookupCommitmentsLayoutDefault).helpers.start == 6 * g1Bytes
      && (layout.lookups.getD 1 proofLookupCommitmentsLayoutDefault).accumulator.start
        == 7 * g1Bytes
      -- the enumerate index is the position, not the chunk count
      && layout.lookups.map (fun row => row.lookup) == [0, 1]

/-- rust: AP:457-475 (proof_layout_rejects_commitment_order_drift), a
    #[should_panic(expected = "proof commitment plan drift")] test.

    WHAT CANNOT BE REPRODUCED, stated rather than hidden: the Rust asserts on the
    panic PAYLOAD substring. Fault.panic carries a site and no payload
    (Exec/Error.lean:56-58), so the port pins the SITE instead - AP:106, the
    assert_eq! inside take_commitment_section - and the payload half of the
    reference's assertion is lost. Protocol.lean records the same loss for the
    PM:642 panic; here it bites a test rather than a production message.

    The swap is the Rust's: position of the first LookupMultiplicity with the
    position of the first PermutationProduct, which for this shape is indices 1
    and 2. Rules out the assert being a no-op, being written against the wrong
    expected variant, or being written against the read index instead of the
    PERTURBATION RUN: P2 (the assert replaced by `false && actual != some expected`) reddens
    this gate and proofLayout_rejectsShortCommitmentPlan_ok and nothing else. -/
def proofLayout_rejectsOrderDrift_ok : Bool :=
  let base := protocolShape [1] [1] 1 0 1
  let commitments := base.proof.commitments
  let lhs? := (List.range commitments.length).find? fun i =>
    commitments[i]? == some CommitmentRead.lookupMultiplicity
  let rhs? := (List.range commitments.length).find? fun i =>
    commitments[i]? == some CommitmentRead.permutationProduct
  match lhs?, rhs? with
  | some lhs, some rhs =>
    match swapIdx commitments lhs rhs with
    | none => false
    | some driftedCommitments =>
      let drifted : ProtocolPlan := { base with proof := { base.proof with
        commitments := driftedCommitments } }
      -- the drift really is a drift, or the gate below proves nothing
      drifted.proof.commitments.length == commitments.length
        && drifted.proof.commitments != commitments
        && drifted.proof.commitments[lhs]? == some CommitmentRead.permutationProduct
        && drifted.proof.commitments[rhs]? == some CommitmentRead.lookupMultiplicity
        && panickedAtSite (ProofCalldataLayout.fromProtocol drifted 0 0 0)
          "proofs/solidity-verifier/src/lowering/abi/proof.rs:106"
        && match ProofCalldataLayout.fromProtocol base 0 0 0 with
           | .ok _ => true
           | .error _ => false
  | _, _ => false

/-- AP:105 reads the commitment plan with Vec::get, so a plan that is SHORTER
    than the sections ask for is `none` and not an index panic - and the assert
    is what turns it into an abort. Rules out the get being ported as a defaulting
    index (which would silently reserve a section for a commitment that does not
    exist) and rules out the none case being treated as "stop early".
    PERTURBATION RUN: P2 (assert deleted) reddens this gate and the drift gate; that pairing
    is the reference's own test suite's blind spot. -/
def proofLayout_rejectsShortCommitmentPlan_ok : Bool :=
  let base := protocolShape [2] [] 0 0 0
  let short : ProtocolPlan :=
    { base with proof := { commitments := [CommitmentRead.advice], evals := [] } }
  panickedAtSite (ProofCalldataLayout.fromProtocol short 0 0 0)
    "proofs/solidity-verifier/src/lowering/abi/proof.rs:106"

/-- AP:210-214, the other assert in from_protocol: the layout must consume the
    whole commitment plan. A plan with one commitment more than the sections
    reserve must abort there and not at 106, which is what makes this gate
    distinguish from proofLayout_rejectsOrderDrift_ok. Rules out the assert being
    dropped, which would let a protocol that grew a new commitment kind silently
    produce a layout that omits it - the exact drift the doc comment at
    PERTURBATION RUN: P12 (the check replaced by `if false`) reddens THIS GATE AND NOTHING
    ELSE in the file, the cleanest single-gate result here. The site-swap variant was not
    run. -/
def proofLayout_rejectsTrailingCommitments_ok : Bool :=
  let base := protocolShape [1] [] 0 0 1
  let extra : ProtocolPlan :=
    { base with proof := { base.proof with
        commitments := base.proof.commitments ++ [CommitmentRead.trash] } }
  panickedAtSite (ProofCalldataLayout.fromProtocol extra 0 0 0)
    "proofs/solidity-verifier/src/lowering/abi/proof.rs:210"
    && match ProofCalldataLayout.fromProtocol base 0 0 0 with
       | .ok _ => true
       | .error _ => false

/-- rust: AP:478-487 (proof_layout_handles_zero_lookup_and_trash), transcribed.
    The shape is the one that exercises the filter asymmetry: a zero-count advice
    PHASE is dropped by the filter, a zero-count lookup/trash section is dropped
    by its own filter, and the quotient limbs are pushed unconditionally - so
    [4, 1] and not [0, 4, 1] and not [4]. Rules out the quotient group being
    filtered like the others, which is the mistake this shape catches and that
    none of the other four reference tests can see.
    PERTURBATIONS RUN: P4 (advice-phase filter dropped), P9 (quotient group filtered), P15,
    P18 and P22 each redden this gate. P4 and P9 leave every offset gate green, which is
    why the group list is asserted here and not only through the agreement gate. -/
def proofLayout_handlesZeroLookupAndTrash_ok : Bool :=
  let protocol := protocolShape [0, 4] [] 0 0 1
  match ProofCalldataLayout.fromProtocol protocol 0x64 7 0 with
  | .error _ => false
  | .ok layout =>
    layout.lookupMultiplicities.byteLen == 0
      && layout.permutationProducts.byteLen == 0
      && layout.trash.byteLen == 0
      && layout.quotientCommCptr == 0x64 + 4 * g1Bytes
      && layout.commitmentReadGroups == [4, 1]

/-- The one link of AP:271-292 that NO reference test reaches: the quotient
    group is pushed by std::iter::once with no filter, so a plan with zero quotient
    limbs still contributes a 0 group. This is the case the P9 perturbation
    exercises, and it is a package-added gate, not a transcription - the reference's
    own AP:486 shape has one quotient. Both definitions agree on it (PM:683 pushes
    unconditionally too), which is the point: the two must agree on the degenerate
    case as well as the ordinary ones.
    PERTURBATION RUN: P9 (wrapping the final push in `if != 0`) reddens this gate and the
    agreement gate and nothing else - the gap this gate was added to close. -/
def commitmentReadGroups_pushesEmptyQuotient_ok : Bool :=
  let plan := protocolShape [1] [] 0 0 0
  match ProofCalldataLayout.fromProtocol plan 0 0 0 with
  | .error _ => false
  | .ok layout =>
    layout.quotientLimbs.itemCount == 0
      && layout.commitmentReadGroups == [1, 0]
      && plan.commitmentReadGroups == [1, 0]
      && layout.commitmentReadGroups == plan.commitmentReadGroups
      && layout.commitmentG1Count == 1
      && layout.totalG1Count == 3

/-- rust: AP:490-501 (transcript_layout_matches_current_conservative_bound),
    transcribed. The Rust asserts an INEQUALITY (words * WORD_BYTES >=
    first_phase_run) and one equality; both are here, plus the exact word count,
    which the Rust leaves free. The inequality is the load-bearing half: the
    buffer must be at least as big as the run, and 350 words is 11200 bytes
    against a 9408-byte first run, i.e. the total run is what binds here.
    PERTURBATIONS RUN: P1 (the old pre-squeeze bound) and P19 (the term dropped outright) both
    redden this gate. CORRECTION to an earlier draft, which claimed dropping the term
    would slip past here because the total run binds: it does not, because this gate
    asserts initialRunBytes exactly - but the reference's own test, which asserts only the
    inequality, WOULD have missed P19, and that is worth saying out loud. P5, P14, P17,
    P21, P23 and P24 also reach this gate; P11 (div_ceil -> floor) does not and cannot,
    see transcriptRunsAreWordAligned_ok. -/
def transcriptLayout_conservativeBound_ok : Bool :=
  let protocol := protocolShape [64] [] 0 0 2
  match ProofCalldataLayout.fromProtocol protocol 0 10 3 with
  | .error _ => false
  | .ok proof =>
    let transcript := TranscriptBufferLayout.fromProofLayout proof 0 [1]
    let firstPhaseRun := 32 + 128 + 32 + 64 * 128 + 32 * 32
    transcript.words * wordBytes >= firstPhaseRun
      && transcript.evalRunBytes == 2 * g1Bytes + (10 + 3) * wordBytes + 32 * wordBytes
      && firstPhaseRun == 9408
      && transcript.initialRunBytes == 9408
      && transcript.evalRunBytes == 1696
      && transcript.totalRunBytes == 11200
      && transcript.words == 350

/-- rust: AP:504-536
    (transcript_layout_covers_multi_phase_advice_before_first_squeeze),
    transcribed in full including its two inequality assertions. THIS IS THE
    6b3d209 GATE. The shape is legal (plan_allows_challenge_phase_beyond_advice,
    PM:1104): phase 0 has advice but no challenge, so BOTH phases' advices are
    absorbed before the first squeeze. The Rust then proves the fix was
    load-bearing by showing the OLD bound - phase 0's advice alone - is smaller
    than the true run even after the cushion is added.
    PERTURBATIONS RUN, and this is the gate that earns its keep: P1 moves the accumulate BELOW
    the break test - the old bound, a one-line edit - and reddens this gate,
    conservativeBound and the empty-phase gate; P14 (advices absorbed at the WORD width
    rather than the G1 width) reddens the same three; P17 and P19 also redden it. A
    loop-order variant claimed in an earlier draft was not run and has been removed. -/
def transcriptLayout_multiPhaseAdvice_ok : Bool :=
  let protocol := protocolShape [1, 9] [] 0 0 1
  match ProofCalldataLayout.fromProtocol protocol 0 12 2 with
  | .error _ => false
  | .ok proof =>
    let numInstances := 86
    let transcript := TranscriptBufferLayout.fromProofLayout proof numInstances [0, 1]
    let word := transcriptWordAbsorbBytes
    let g1 := transcriptG1AbsorbBytes
    let cushion := transcriptPostSqueezeCushionWords * wordBytes
    let trueInitialRun := word + g1 + word + numInstances * word + (1 + 9) * g1
    let phase0OnlyRun := word + g1 + word + numInstances * word + g1
    transcript.words * wordBytes >= trueInitialRun
      && transcript.initialRunBytes == trueInitialRun + cushion
      && phase0OnlyRun < trueInitialRun
      && phase0OnlyRun + cushion < trueInitialRun
      -- the exact numbers the shape produces
      && trueInitialRun == 4224
      && phase0OnlyRun == 3072
      && transcript.initialRunBytes == 5248
      && transcript.evalRunBytes == 1600
      && transcript.totalRunBytes == 4192
      && transcript.words == 164

/-- AP:314-317 promises that an EMPTY phase_challenge_counts slice is read as "no
    phase owns a challenge" and so sums every advice phase as a safe upper bound.
    That is the unwrap_or(0) at AP:339 doing real work, and it is a separate
    behaviour from the break rule above: a port that read the slice with an index
    (panicking), or that defaulted a missing phase to "owns a challenge" (stopping
    at phase 0), would under-size the buffer here.
    PERTURBATION RUN: P20 (the getD default 0 -> 1, i.e. a missing phase is read as owning a
    challenge) reddens THIS GATE AND NOTHING ELSE in the file, which is exactly the point
    - the unwrap_or(0) at AP:339 has no other observable effect. -/
def transcriptLayout_emptyChallengeCountsSumsEveryPhase_ok : Bool :=
  let protocol := protocolShape [1, 9] [] 0 0 1
  match ProofCalldataLayout.fromProtocol protocol 0 12 2 with
  | .error _ => false
  | .ok proof =>
    let empty := TranscriptBufferLayout.fromProofLayout proof 0 []
    let onlyFirst := TranscriptBufferLayout.fromProofLayout proof 0 [1]
    empty.initialRunBytes == 32 + 128 + 32 + 0 + 10 * 128 + 1024
      && onlyFirst.initialRunBytes == 32 + 128 + 32 + 0 + 1 * 128 + 1024
      && empty.initialRunBytes > onlyFirst.initialRunBytes

/-- HAZARD 6, first half. commitment_read_groups is defined TWICE in the
    reference - PM:667-690 on ProtocolPlan and AP:271-292 on
    ProofCalldataLayout - and NO Rust test relates them: the only tests that
    touch either are PM:1024 and PM:1228 (plan side) and AP:486 (layout side),
    and each names only its own. The two are spelled differently and agree only
    because from_protocol copies each protocol count into the section it
    reserves. This gate is the relation the reference does not have, asserted over
    every shape the reference's own tests use plus the Protocol.lean fixture,
    which is the one circuit-derived plan available here.
    PERTURBATIONS RUN: P4, P9, P10, P17 and P18 each redden this gate. The plan-side guard was
    not perturbed separately: Protocol.lean is not this package's file to edit. -/
def commitmentReadGroups_agreesWithProtocolPlan_ok : Bool :=
  let shapes : List (List Nat × List Nat × Nat × Nat × Nat) :=
    [([2, 1], [2, 0], 1, 1, 3), ([1], [2, 1], 0, 0, 2), ([0, 4], [], 0, 0, 1),
     ([64], [], 0, 0, 2), ([1, 9], [], 0, 0, 1), ([1], [1], 1, 0, 1),
     ([1], [], 0, 0, 0)]
  let perShape := shapes.all fun shape =>
    let plan := protocolShape shape.1 shape.2.1 shape.2.2.1 shape.2.2.2.1 shape.2.2.2.2
    match ProofCalldataLayout.fromProtocol plan 0 plan.proof.evals.length 0 with
    | .error _ => false
    | .ok layout =>
      layout.commitmentReadGroups == plan.commitmentReadGroups
        && ! layout.commitmentReadGroups.isEmpty
        && layout.commitmentReadGroups.sum == plan.proof.commitments.length
        && layout.totalG1Count == plan.proof.commitments.length + 2
        && layout.commitmentG1Count == plan.proof.commitments.length
        && layout.nonQuotientG1Count == plan.numNonQuotientCommitments
        && layout.commitmentReadGroups.sum == layout.commitmentG1Count
  let fixture := Midfall.Generator.ProtocolKats.fixturePlan
  let fixtureCase := match ProofCalldataLayout.fromProtocol fixture 0 fixture.numMainEvals 22 with
    | .error _ => false
    | .ok layout =>
      layout.commitmentReadGroups == [4, 1, 2, 2, 1, 1, 4]
        && layout.commitmentReadGroups == fixture.commitmentReadGroups
        && layout.nonQuotientG1Count == 11
        && layout.commitmentG1Count == 15
        && layout.totalG1Count == 17
  perShape && fixtureCase

/-- HAZARD 6, second half: the two functions really are independent readings, so
    the agreement above is a property of from_protocol and not an identity. A
    hand-built layout reports its own item_counts even when the plan says
    something else. Rules out a later package "simplifying" one of the two into
    the other, which would silently change what the repacker sees for any layout
    PERTURBATION RUN: P18 (the permutation group off by one) reddens this gate and shows the
    layout side really is read from the sections. The collapse-the-two-definitions
    perturbation is a rewrite rather than a single-token edit and was NOT run. -/
def commitmentReadGroups_disagreeWhenHandBuilt_ok : Bool :=
  let plan := protocolShape [1] [] 0 0 1
  let handBuilt : ProofCalldataLayout :=
    { proofCalldataLayoutDefault with
      advicePhases := [ProofSection.new 0 1 g1Bytes]
      quotientLimbs := ProofSection.new 128 5 g1Bytes }
  plan.commitmentReadGroups == [1, 1]
    && handBuilt.commitmentReadGroups == [1, 5]
    && plan.commitmentReadGroups != handBuilt.commitmentReadGroups

/-- The three count accessors form a strict chain: non_quotient <= commitment <=
    total, the two extra G1s being f_com and pi and the quotient limbs the
    difference between the first two. Rules out total_g1_count dropping the
    quotient limbs, and rules out commitment_g1_count being the same as
    non_quotient_g1_count, which would under-size total_run_bytes by the whole
    PERTURBATIONS RUN: P10 (non_quotient drops the trash term) and P17 (commitment_g1_count
    drops the quotient limbs) each redden this gate; P17 also reddens both transcript
    gates, which is the downstream consequence AP:260-263's comment is about. -/
def g1CountChain_ok : Bool :=
  match ProofCalldataLayout.fromProtocol (protocolShape [2, 1] [2, 0] 1 1 3) 0x64 5 2 with
  | .error _ => false
  | .ok layout =>
    layout.nonQuotientG1Count == 11
      && layout.commitmentG1Count == 14
      && layout.totalG1Count == 16
      && layout.commitmentG1Count == layout.nonQuotientG1Count + layout.quotientLimbs.itemCount
      && layout.totalG1Count == layout.commitmentG1Count + layout.fCom.itemCount
        + layout.pi.itemCount
      && layout.fCom.itemCount == 1
      && layout.pi.itemCount == 1

/-- The sections tile the payload exactly: proof_end is the last section's end
    and proof_len is the sum of every section's byte_len, which is the property
    AP:243's subtraction relies on and the property the repacker needs. Rules out
    a section being reserved without advancing the cursor, and rules out the
    PERTURBATION RUN: P16 (wordSection returns the cursor unchanged) reddens this gate and
    proofLayout_matchesLegacyOffsets_ok; P3 and P15 also reach it. -/
def proofLayout_sectionsTileExactly_ok : Bool :=
  match ProofCalldataLayout.fromProtocol (protocolShape [2, 1] [2, 0] 1 1 3) 0x64 5 2 with
  | .error _ => false
  | .ok layout =>
    let allSections := layout.advicePhases ++ [layout.lookupMultiplicities,
      layout.permutationProducts]
      ++ (layout.lookups.flatMap fun row => [row.helpers, row.accumulator])
      ++ [layout.trash, layout.quotientLimbs, layout.evals, layout.fCom,
          layout.qEvals, layout.pi]
    let total := allSections.foldl (fun acc sect => acc + sect.byteLen) 0
    total == layout.proofLen
      && layout.proofEnd == layout.pi.end
      && layout.proofEnd >= layout.proofCptr
      && allSections.all (fun sect => sect.start + sect.byteLen <= layout.proofEnd)
      && layout.evals.start == layout.evalCptr
      && layout.qEvals.start == layout.qEvalCptr
      && layout.fCom.start == layout.wCptr
      && layout.quotientLimbs.start == layout.quotientCommCptr

#eval abiAndTranscriptConstants_ok -- expect true
#eval transcriptCushionSpellingsAgree_ok -- expect true
#eval proofSection_arithNoWrap_ok -- expect true
#eval proofSection_new_derivesByteLen_ok -- expect true
#eval proofLayout_matchesLegacyOffsets_ok -- expect true
#eval proofLayout_preservesLookupGrouping_ok -- expect true
#eval proofLayout_rejectsOrderDrift_ok -- expect true
#eval proofLayout_rejectsShortCommitmentPlan_ok -- expect true
#eval proofLayout_rejectsTrailingCommitments_ok -- expect true
#eval proofLayout_handlesZeroLookupAndTrash_ok -- expect true
#eval transcriptLayout_conservativeBound_ok -- expect true
#eval transcriptLayout_multiPhaseAdvice_ok -- expect true
#eval transcriptLayout_emptyChallengeCountsSumsEveryPhase_ok -- expect true
#eval commitmentReadGroups_pushesEmptyQuotient_ok -- expect true
#eval transcriptRunsAreWordAligned_ok -- expect true
#eval commitmentReadGroups_agreesWithProtocolPlan_ok -- expect true
#eval commitmentReadGroups_disagreeWhenHandBuilt_ok -- expect true
#eval g1CountChain_ok -- expect true
#eval proofLayout_sectionsTileExactly_ok -- expect true

end Midfall.Generator.AbiKats

