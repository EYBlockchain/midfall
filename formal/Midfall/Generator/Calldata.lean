-- |
-- Midfall.Generator.Calldata
--
-- THE PROOF REPACKER and the build-inputs calldata entry point: the deterministic
-- boundary conversion from midnight-proofs' on-the-wire compressed proof (48-byte
-- ZCash G1s, little-endian Fr scalars) to the Solidity-facing form (EIP-2537 padded
-- G1 words, big-endian scalar words), plus the encode-and-wrap step. Ported from
-- proofs/solidity-verifier/src/lowering/calldata.rs (160 lines at HEAD, cited as CD)
-- and from the one helper it imports. Work package P-12.
--
-- CITATION NOTATION (docs/plans/README.md standing note 2: every range below was
-- re-derived from git show HEAD:<path>).
-- * CD:   proofs/solidity-verifier/src/lowering/calldata.rs (160 lines at HEAD).
-- * QVM:  proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs
--   (4336 lines at HEAD) - only QVM:934-944 is here; see ITEM 0 below.
-- * EVM:  proofs/solidity-verifier/src/evm.rs (656 lines at HEAD) - the wire
--   encoder CD:148 calls; ported in Evm.lean.
-- * BREP: proofs/solidity-verifier/src/builder/repack.rs (27 lines at HEAD) - the
--   public wrappers over CD; ported in Builder.lean (they are SolidityGenerator
--   methods and the record lives there).
-- * AP:   proofs/solidity-verifier/src/api.rs - AT HEAD. The working copy carries
--   an UNCOMMITTED 57-line insertion at AP:530 (git diff --stat), so every HEAD
--   cite at or after AP:530 - including the RepackError block Api.lean cites at
--   API:531-590 - is shifted by +57 in the file on disk. The Display gate below
--   therefore searches by CONTENT, not by line number. Reported as a finding.
-- * GEN:  proofs/solidity-verifier/src/lowering/layout/mod.rs - the two widths
--   CD:64/CD:89 slice by (G1_COMPRESSED_BYTES = 48, WORD_BYTES = 32), already
--   ported as g1CompressedBytes (Api.lean:164) and wordBytes (Layout.lean:57).
-- * TPLV: proofs/solidity-verifier/templates/partials/verifier/
--     TranscriptProofParser.yul (424 lines at HEAD) and
--     proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol
--     (tracked) - the CONTRACT side, which the hazard-1 decoder gates read at
--     #eval time.
--
-- ITEM 0 - THE MISSING HELPER (plan P-12 item 0).
--
-- scalar_le_to_be_word (QVM:934-944) is ported here, not in the quotient VM.
-- VmTypes.lean:62-64 declined it with the reason "it is a proof-repacking byte
-- helper that sits between the tables and the expression types. Not vocabulary; it
-- belongs with the repacker" - and this file IS the repacker, so the hole between
-- P-09a (declined) and P-12 (needs it) closes here. CD:19 imports it and CD:105
-- calls it; nothing in this package works until it lands.
--
-- WHAT IS NOT PORTED, AND WHY.
-- * CD:24 impl VerifierBuildInputs: the receiver type is Vk.lean:359-377's, and
--   D-P17 forbids importing Generator.Vk (LoweringPlan.lean:126-131 spells out the
--   reason: Vk.lean:289 pulls in Instances.ExponentModel, and P-SE's stage-2 files
--   must import this row). So the two methods become plain functions taking the
--   facts the Rust body actually reads: the plan (CD:46-48, from
--   self.repacked_proof_layout_plan()) and, for encode_calldata, num_instances
--   (CD:137). This is the same deviation LoweringPlan.lean:126-131 makes for
--   acc_msm_terms, and it is recorded at each def.
-- * CD:157-159 repacked_proof_layout_plan is lowering_plan() composed with
--   RepackedProofLayoutPlan::from_proof_layout; the second half is already ported
--   (VmTypes.lean:720) and the composition is already ported as
--   LoweringPlan.repackedProofLayoutPlan (LoweringPlan.lean:318). Re-declaring it
--   here would be a duplicate name for an existing def - the P-11 correction-2
--   precedent.
-- * The G1 DECOMPRESSION itself (G1Affine::from_bytes, CD:67) is not a Lean item:
--   it is the curve codec, which the tree carries as G1Codec (Common/Codec.lean:81,
--   PLAN R9: a trait becomes a structure of functions). The port is therefore
--   parameterised by a G1Codec, exactly as P-SE's decodeCalldata and calldataOf are
--   (P-SE plan:229-230). The concrete BLS12-381 codec lives in
--   Instances/Bls12_381.lean, which D-P17 puts out of reach here, so the G1 leg is
--   exercised by a toy codec in the KAT section and by the artifact gates' POSITION
--   and PADDING checks; the arithmetic leg is P-SE's repack_spec_wire obligation,
--   not this package's.
--
-- HAZARD ANSWERS RECORDED HERE.
-- * Hazard 2: RepackError is REUSED from Api.lean:257 with its verbatim Display
--   (Api.lean:282), and every RepackError is lifted through
--   GeneratorError.fromRepackError (Api.lean:388) - the coercion the Rust's ? at
--   CD:147 applies. The channel is ApiFault rather than Except RepackError because
--   the walk has three panic sites (CD:64, CD:89 indexing and QVM:939's assert)
--   that Except RepackError cannot carry; R4 forbids dropping them. repackErrorOf?
--   exposes the discriminant for callers that match on it, and
--   repackProof_lengthMismatchFields_ok shows the P-SE composition (mapError
--   fromRepackError) recovers the same value.
-- * Hazard 3 (P-09e F-3, fixed_scalar_count not total on the domain
--   validate_for_num_instances accepts): NOT REACHED. fixed_scalar_count has
--   exactly two Rust callers - plan.rs:556 and artifacts.rs:184 - and neither
--   calldata.rs nor builder/api.rs is one of them (grep at HEAD). builder/api.rs
--   calls validate_for_num_instances only (BAPI:50), which is total. The F-3 defect
--   therefore stays where P-09e filed it, in Api.lean:622's own domain; this
--   package neither triggers nor repairs it.
-- * Hazard 1 (canonicity) is measured by the decoder gates at the bottom of the
--   KAT section and answered in the report: the tracked contract and template
--   reject trailing bytes, non-canonical instance words, non-canonical proof
--   scalars and unpadded G1 words, i.e. they agree with P-SE D7 and contradict
--   PLAN 13:587's "may be accepted".
-- * R4: the debug_assert_eq! at CD:127 is COMPILED OUT in the release profile
--   (BASELINE.md, and the brief's R4 note), so the port does NOT check it.
--   repackProof_walkConsumesExactly_ok asserts the equation as a GATE instead,
--   which is where it belongs: a debug_assert is a developer invariant, not runtime
--   behaviour.
-- * R6: Vec -> List (plans/README.md standing note 4).
-- * D-P17: no Generator.Vk, no Midfall.Instances/.

import Midfall.Assumptions.Pairing
import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Generator.Api
import Midfall.Generator.Evm
import Midfall.Generator.Layout
import Midfall.Generator.Quotient.VmTypes

namespace Midfall.Generator

/-- Reverse a byte buffer, i.e. Rust's <[u8]>::reverse. The one primitive the
    repacker's two reversals (QVM:942 and CD:99) both need; Common/Bytes.lean has
    no in-place reverse because Bytes is an immutable ByteArray. -/
def bytesReverse (bs : Bytes) : Bytes :=
  ByteArray.mk (bs.data.toList.reverse.toArray)

/-- rust: QVM:934-944 (scalar_le_to_be_word) @formal-baseline. "Convert a
    little-endian proof scalar into the big-endian 32-byte EVM word. Proof calldata
    uses scalar-byte order from the host encoding; EVM mstore and arithmetic
    consume canonical big-endian words."

    ITEM 0 of plan P-12: the helper P-09a declined (VmTypes.lean:62-64, "it belongs
    with the repacker") and CD:19 imports. R4: the assert_eq! at QVM:939 is a PANIC,
    not a debug_assert, so it survives the release profile and the port keeps it as
    a fault with the site as its payload; the message "scalar proof element must be
    32 bytes" is lost because ApiFault.panic carries only a site (the F2 convention
    LoweringPlan.lean:104-113 records). -/
def scalarLeToBeWord (bytes : Bytes) : Except ApiFault Bytes :=
  if bytes.size != wordBytes then
    .error (ApiFault.panic
      "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs:939")
  else
    .ok (bytesReverse bytes)

/-- hex::encode (external crate), called at CD:71 and CD:102. Not a Rust item in
    the ported file, but the two error payloads are Strings built from it, so the
    port needs it to keep them faithful. Lowercase, no 0x: the Display impl at
    AP:576/AP:582 supplies the 0x itself (Api.lean:290-296). -/
def hexEncodeLower (bs : Bytes) : String :=
  (bytesToNats bs).foldl (fun (acc : String) (b : Nat) =>
    let hi := (Nat.toDigits 16 (b / 16)).head?.getD '0'
    let lo := (Nat.toDigits 16 (b % 16)).head?.getD '0'
    (acc.push hi).push lo) ""

/-- rust: CD:61-87 (the push_g1 closure) @formal-baseline. Reads one 48-byte
    compressed commitment at cursor, rejects it if the codec cannot decode it
    (CD:67-73), and appends the EIP-2537 padded form.

    CD:74-77 (identity -> 128 zero bytes) and CD:78-85 (16 zeros || x_BE(48) ||
    16 zeros || y_BE(48)) are the two arms of the padded encoding that G1Codec.toEip
    already implements (Common/Codec.lean:66-68, citing implementors.rs:283-299), so
    the port calls the codec once instead of inlining the byte shape.
    repackPushG1_paddedShapeMatchesRust_ok pins that the shape the Rust inlines is
    the shape the codec emits, so the substitution is not silent. R4: CD:64's
    compressed[cursor..cursor+48] is an out-of-bounds PANIC when the buffer is
    short; the port keeps it as a fault site even though CD:49's length check makes
    it unreachable. -/
def repackPushG1 {G₁ : Type} (c : G1Codec G₁) (compressed : Bytes)
    (cursor : Nat) (out : Bytes) : Except ApiFault (Nat × Bytes) :=
  match bytesTake compressed cursor g1CompressedBytes with
  | none =>
      .error (ApiFault.panic "proofs/solidity-verifier/src/lowering/calldata.rs:64")
  | some comp =>
      match c.ofCompressed? comp with
      | none =>
          .error (ApiFault.error (GeneratorError.repack
            (RepackError.invalidCompressedG1 (offset := cursor)
              (bytesHex := hexEncodeLower comp))))
      | some pt => .ok (cursor + g1CompressedBytes, out ++ c.toEip pt)

/-- rust: CD:88-108 (the push_scalar_be closure) @formal-baseline. Reads one
    32-byte little-endian proof scalar and appends its big-endian word.

    CD:96-104 is the canonicity gate the comment at CD:90-93 explains: "the
    generated verifier reverts on any eval or q_eval word that is not a canonical Fr
    element, so reject it here rather than handing the caller calldata that is
    guaranteed to revert on-chain". The Rust spells that as Fq::from_repr(repr)
    being none; the tree's port of from_repr is frOfRepr? (Common/Codec.lean:38-39,
    PLAN R7 "from_repr checks canonicity"), the same bound test at the same
    modulus, so the port uses it. The error's bytes_hex is the hex of the REVERSED
    bytes (CD:98-99 reverse arr into be before hexing), i.e. the big-endian
    spelling. -/
def repackPushScalarBe (compressed : Bytes) (cursor : Nat) (out : Bytes) :
    Except ApiFault (Nat × Bytes) :=
  match bytesTake compressed cursor wordBytes with
  | none =>
      .error (ApiFault.panic "proofs/solidity-verifier/src/lowering/calldata.rs:89")
  | some le =>
      if (frOfRepr? (p := Midfall.Assumptions.r) le).isSome then
        match scalarLeToBeWord le with
        | .ok w => .ok (cursor + wordBytes, out ++ w)
        | .error f => .error f
      else
        .error (ApiFault.error (GeneratorError.repack
          (RepackError.nonCanonicalScalar (offset := cursor)
            (bytesHex := hexEncodeLower (bytesReverse le)))))

/-- rust: CD:24-129 (VerifierBuildInputs::repack_proof) @formal-baseline. "Repack a
    midnight-proofs proof from the on-the-wire compressed form (each G1 = 48 bytes
    ZCash compressed) into the EIP-2537 padded form (each G1 = 4 x 32-byte BE words)
    and rewrites scalar proof elements from midnight-proofs' canonical LE bytes into
    canonical BE calldata words."

    The walk is the Rust's five passes in order: the g1_groups nested loop
    (CD:109-113), the eval block (CD:116-118), f_com (CD:120), the q_eval block
    (CD:122-124), pi (CD:126). cursor threads through them exactly as the Rust's
    &mut usize does, and the ? on each push is the left-arrow in Except (R3).
    CD:59's Vec::with_capacity is an allocation hint with no observable effect and
    is not ported. CD:127's debug_assert_eq! is compiled out (R4; see the header). -/
def repackProof {G₁ : Type} (c : G1Codec G₁) (plan : RepackedProofLayoutPlan)
    (compressed : Bytes) : Except ApiFault Bytes := do
  let expected := plan.compressedLen
  if compressed.size != expected then
    throw (ApiFault.error (GeneratorError.repack (RepackError.lengthMismatch
      (expected := expected) (actual := compressed.size)
      (prefixG1 := plan.prefixG1Count) (numEvals := plan.numEvals)
      (numPointSets := plan.numPointSets))))
  -- CD:109-113: for each group, that many compressed G1s.
  let (cursor0, out0) ← plan.g1Groups.foldlM
    (fun (st : Nat × Bytes) (n : Nat) =>
      (List.range n).foldlM
        (fun (st : Nat × Bytes) (_ : Nat) => repackPushG1 c compressed st.1 st.2) st)
    (0, Bytes.empty)
  -- CD:114-118: evals (Fr 32-byte LE in native proof) -> BE calldata words
  -- (incl. dummy slots).
  let (cursor1, out1) ← (List.range plan.numEvals).foldlM
    (fun (st : Nat × Bytes) (_ : Nat) => repackPushScalarBe compressed st.1 st.2)
    (cursor0, out0)
  -- CD:119-120: f_com.
  let (cursor2, out2) ← repackPushG1 c compressed cursor1 out1
  -- CD:121-124: q_evals.
  let (cursor3, out3) ← (List.range plan.numPointSets).foldlM
    (fun (st : Nat × Bytes) (_ : Nat) => repackPushScalarBe compressed st.1 st.2)
    (cursor2, out2)
  -- CD:125-126: pi.
  let (_cursor4, out4) ← repackPushG1 c compressed cursor3 out3
  pure out4

/-- rust: CD:131-149 (VerifierBuildInputs::encode_calldata) @formal-baseline.
    "Repack a native proof and encode verifier calldata for verifyProof."

    R2 NAME DEVIATION, recorded because a reviewer will look: the Rust has TWO
    encode_calldata - CD:132 (the build-inputs method, which validates the instance
    count and repacks) and EVM:22 (the wire encoder). The Lean namespace is flat, so
    the wire encoder keeps the bare name encodeCalldata (it is the one PLAN 9.5 and
    P-SE name) and this one is encodeCalldataWithInstances. The ? at CD:147 is
    Rust's From<RepackError> for GeneratorError, i.e. exactly
    GeneratorError.fromRepackError (Api.lean:388); this port's repackProof already
    lifts, so the coercion is applied once, not twice. CD:140-144's format! payload
    is KEPT verbatim (it is an Err message, not a panic message, so R4's site-only
    rule does not apply). -/
def encodeCalldataWithInstances {G₁ : Type} (c : G1Codec G₁)
    (plan : RepackedProofLayoutPlan) (numInstances : Nat)
    (compressedProof : Bytes) (instances : List Word256) : Except ApiFault Bytes := do
  if instances.length != numInstances then
    throw (ApiFault.error (GeneratorError.planning (stage := "calldata")
      (message := "instance length mismatch: expected " ++ toString numInstances
        ++ ", got " ++ toString instances.length)))
  let proof ← repackProof c plan compressedProof
  pure (encodeCalldata proof instances)

/-- rust: CD:151-154 (repacked_proof_scalar_layout_for_test) @formal-baseline.
    Test-only (R8: cfg(all(test, feature = "evm")), the same reading
    VmTypes.lean:684-691 adopts for RepackedProofScalarLayout): the Rust body is
    self.repacked_proof_layout_plan().scalar_layout(), i.e. the plan accessor this
    file declines to re-declare composed with VmTypes.lean:758. -/
def repackedProofScalarLayoutForTest (plan : RepackedProofLayoutPlan) :
    RepackedProofScalarLayout := plan.scalarLayout

/-- The projection the P-SE composition needs: recover the RepackError a repack
    failure carried out of the ApiFault channel, i.e. the inverse of the
    GeneratorError.fromRepackError lift CD:147 performs. Not a Rust item - it
    exists so a caller can match on RepackError::LengthMismatch the way
    proofs/solidity-verifier/fuzz/fuzz_targets/solidity_calldata.rs:173-192 does. -/
def repackErrorOf? (f : ApiFault) : Option RepackError :=
  match f with
  | ApiFault.error (GeneratorError.repack err) => some err
  | _ => none

end Midfall.Generator

/-! # Known-answer tests

    ## Which artifacts, and which of them are actually tracked

    Three groups of oracles below are TRACKED and their gates are hard:

    * the generated contract
      proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol - the
      proof length, the instance count, the eval and q_eval section widths and the
      ABI head constants are read out of it, so the plan the repack gates use is
      DERIVED from Rust output rather than pasted;
    * the Yul partials VkLoading.yul, TranscriptProofParser.yul and
      AssemblyHelpers.yul - the hazard-1 decoder gates;
    * src/lowering/quotient_numerator/vm/mod.rs and src/api.rs - the item-0 and
      Display gates.

    Two are NOT tracked, and that is a finding against the brief: plan P-12 says
    "the tracked calldata.bin and proof.bin are the right oracles", but git ls-files
    lists no calldata.bin in the index and git check-ignore reports
    proofs/solidity-verifier/.gitignore:4: target/ for it. The dump directory is
    force-added file by file (Halo2Verifier.sol, Halo2VerifyingKey.sol and
    instances.be are tracked; calldata.bin, proof.bin and instance.be in the same
    directory are not). The gates that need the raw proof and calldata bytes
    therefore return true when the artifact is absent, and
    calldataDumpBytesPresent_ok reports their reachability as a VALUE rather than as
    an assertion, so a fresh clone loses those gates LOUDLY and visibly instead of
    silently. The tracked-.sol gates carry the load in either case. -/

namespace Midfall.Generator.CalldataKats

open Midfall.Generator.EvmKats

/-- Count non-overlapping occurrences of needle (the LoweringPlan.lean:791 helper,
    re-declared rather than imported so this file does not pull in the plan row). -/
def countMatches (haystack needle : String) : Nat := (haystack.splitOn needle).length - 1

/-- The n-th line of a source, 1-based, or the empty string. -/
def lineOf (src : String) (n : Nat) : String :=
  match (src.splitOn "\n").drop (n - 1) |>.head? with
  | some l => l
  | none => ""

/-- The first byte of a buffer as a Nat. -/
def firstByteOf (b : Bytes) : Option Nat := (bytesToNats b).head?

/-- Is this repack result the panic for the given site? (Except has no BEq here, so
    the comparison is a match rather than an equality.) -/
def isPanicAt {α : Type} (site : String) (r : Except ApiFault α) : Bool :=
  match r with
  | .error (ApiFault.panic s) => s == site
  | _ => false

/-! ## The toy G1 codec -/

/-- A toy curve point for the gates: an infinity flag and two coordinate blobs. The
    real BLS12-381 codec is Instances/Bls12_381.lean's, which D-P17 keeps out of this
    file's import graph, so the G1 leg is exercised structurally (widths, padding,
    ordering, error arms) and not arithmetically. -/
structure ToyG1 where
  isInfinity : Bool
  x : Bytes
  y : Bytes

/-- The toy compressed format: byte 0 a tag, bytes 1..25 the x blob, bytes 25..48
    the y blob. A 0xff leading byte is the "undecodable" marker and the all-zero
    block is the identity, so both the error arm of CD:67-73 and the identity arm of
    CD:74-77 are reachable in a gate. -/
def toyOfCompressed? (b : Bytes) : Option ToyG1 :=
  let nats := bytesToNats b
  if nats.length != g1CompressedBytes then none
  else if nats.head?.getD 0 == 0xff then none
  else if nats.all (fun v => v == 0) then some ⟨true, Bytes.empty, Bytes.empty⟩
  else some ⟨false, bytesFromNats (List.take 24 (List.drop 1 nats)),
              bytesFromNats (List.take 23 (List.drop 25 nats))⟩

/-- Pad a toy coordinate out to the 48 bytes a real Fq repr occupies, so the padded
    word arithmetic below is width-faithful. -/
def toyPad48 (b : Bytes) : Bytes :=
  bytesFromNats (List.replicate (g1CompressedBytes - b.size) 0 ++ bytesToNats b)

/-- The toy padded form: exactly the shape CD:80-85 inlines, 16 zeros || x(48) ||
    16 zeros || y(48), and 128 zero bytes for the identity (CD:75). -/
def toyToEip (P : ToyG1) : Bytes :=
  if P.isInfinity then bytesFromNats (List.replicate g1Bytes 0)
  else bytesFromNats (List.replicate 16 0 ++ bytesToNats (toyPad48 P.x)
    ++ List.replicate 16 0 ++ bytesToNats (toyPad48 P.y))

def toyToCompressed (P : ToyG1) : Bytes :=
  if P.isInfinity then bytesFromNats (List.replicate g1CompressedBytes 0)
  else bytesFromNats ([0x01] ++ bytesToNats P.x ++ bytesToNats P.y)

/-- The toy decode of the padded form, used by the round-trip gate. -/
def toyOfEip? (b : Bytes) : Option ToyG1 :=
  let nats := bytesToNats b
  if nats.length != g1Bytes then none
  else if nats.all (fun v => v == 0) then some ⟨true, Bytes.empty, Bytes.empty⟩
  else if (List.take 16 nats).all (fun v => v == 0)
      && (List.take 16 (List.drop 64 nats)).all (fun v => v == 0) then
    some ⟨false, bytesFromNats (List.take 48 (List.drop 16 nats)),
          bytesFromNats (List.take 48 (List.drop 80 nats))⟩
  else none

def toyCodec : G1Codec ToyG1 :=
  { ofCompressed? := toyOfCompressed?, toCompressed := toyToCompressed,
    toEip := toyToEip, ofEip? := toyOfEip? }

/-- The KAT plan: SEVEN groups summing to 19 prefix G1s, 48 evals and 3 point sets -
    the poseidon shape, with the group list split so a dropped group changes the
    number (R-48). -/
def fixturePlan : RepackedProofLayoutPlan :=
  { g1Groups := [8, 1, 3, 1, 1, 4, 1], numEvals := 48, numPointSets := 3 }

/-- The same plan flattened to a single group count. -/
def fixturePrefixG1 : Nat := fixturePlan.prefixG1Count

/-- A compressed proof built to fixturePlan: every G1 block and every scalar slot
    carries distinguishable bytes, and every scalar is small, hence canonical. -/
def fixtureCompressed : Bytes :=
  let g1 (i : Nat) : List Nat :=
    [0x80 + i] ++ (List.range 23).map (fun j => (i * 7 + j) % 256)
      ++ (List.range 24).map (fun j => (i * 11 + j) % 256)
  let scalar (i : Nat) : List Nat := (List.range 32).map (fun j =>
    if j == 0 then (i % 251) + 1 else if j == 1 then i / 251 + 1 else 0)
  let blocks : List (List Nat) :=
    (List.range fixturePrefixG1).map g1
      ++ (List.range fixturePlan.numEvals).map scalar
      ++ [g1 90]
      ++ (List.range fixturePlan.numPointSets).map (fun i => scalar (48 + i))
      ++ [g1 91]
  bytesFromNats (blocks.flatten)

/-- Where the eval block starts in a repacked proof: after the prefix G1s. -/
def fixtureEvalOffset (plan : RepackedProofLayoutPlan) : Nat :=
  plan.prefixG1Count * g1Bytes

/-- Where the q_eval block starts: after the evals and the f_com block. -/
def fixtureQEvalOffset (plan : RepackedProofLayoutPlan) : Nat :=
  fixtureEvalOffset plan + plan.numEvals * wordBytes + g1Bytes

/-- The compressed offset of the f_com block. -/
def fixtureFComCompressed (plan : RepackedProofLayoutPlan) : Nat :=
  plan.prefixG1Count * g1CompressedBytes + plan.numEvals * wordBytes

/-! ## Artifact readers -/

def dumpDirCandidates : List String :=
  ["../proofs/solidity-verifier/target/poseidon-fixture-dump",
   "proofs/solidity-verifier/target/poseidon-fixture-dump"]

def parserPartialCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/verifier/TranscriptProofParser.yul",
   "proofs/solidity-verifier/templates/partials/verifier/TranscriptProofParser.yul"]

def vkLoadingCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/verifier/VkLoading.yul",
   "proofs/solidity-verifier/templates/partials/verifier/VkLoading.yul"]

def asmHelpersCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/verifier/AssemblyHelpers.yul",
   "proofs/solidity-verifier/templates/partials/verifier/AssemblyHelpers.yul"]

def qvmCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs",
   "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs"]

def apiRsCandidates : List String :=
  ["../proofs/solidity-verifier/src/api.rs", "proofs/solidity-verifier/src/api.rs"]

/-- Read a binary artifact; the empty buffer means "absent", never a partial read.
    IO.FS.readFile decodes UTF-8 and would corrupt proof bytes, so this opens a
    handle and reads raw bytes. -/
def readBinOrEmpty (path : String) (cap : Nat) : IO Bytes := do
  try
    let h ← IO.FS.Handle.mk path IO.FS.Mode.read
    h.read cap.toUSize
  catch _e =>
    pure Bytes.empty

def readBinFirst (candidates : List String) (cap : Nat) : IO Bytes :=
  candidates.foldl
    (fun (acc : IO Bytes) (path : String) =>
      acc >>= fun got => if got.size != 0 then pure got else readBinOrEmpty path cap)
    (pure Bytes.empty)

def readDumpProofBin : IO Bytes := readBinFirst
  (dumpDirCandidates.map (fun d => d ++ "/proof.bin")) 65536
def readDumpCalldataBin : IO Bytes := readBinFirst
  (dumpDirCandidates.map (fun d => d ++ "/calldata.bin")) 65536
def readDumpInstanceBe : IO Bytes := readBinFirst
  (dumpDirCandidates.map (fun d => d ++ "/instance.be")) 4096
def readParserPartial : IO String := readFirst parserPartialCandidates
def readVkLoading : IO String := readFirst vkLoadingCandidates
def readAsmHelpers : IO String := readFirst asmHelpersCandidates
def readQvmRs : IO String := readFirst qvmCandidates
def readApiRs : IO String := readFirst apiRsCandidates

/-- GATE 1 (reachability first, per the standing D-P19 note). The TRACKED artifacts
    must open, so a wrong path is a named red rather than a vacuous needle match. -/
def calldataArtifactsReachable_ok : IO Bool :=
  readGeneratedVerifier >>= fun sol =>
  readParserPartial >>= fun pp =>
  readVkLoading >>= fun vl =>
  readAsmHelpers >>= fun ah =>
  readQvmRs >>= fun qvm =>
  readApiRs >>= fun api =>
  pure (generatedReadOk sol && pp.length > 10000 && vl.length > 2000
    && ah.length > 3000 && qvm.length > 100000 && api.length > 20000)

/-- The untracked-artifact report (see the section header): a VALUE, not an
    assertion, so a fresh clone shows false here and still builds. -/
def calldataDumpBytesPresent_ok : IO Bool :=
  readDumpProofBin >>= fun c =>
  readDumpCalldataBin >>= fun d =>
  pure (c.size > 1000 && d.size > 1000)

/-- The first add(proof_cptr, 0x..) after the first line containing needle: how the
    eval and q_eval section widths are read out of the generated contract instead of
    being pasted. -/
def solSectionByteLen (src : String) (needle : String) : Option Nat :=
  let lines := src.splitOn "\n"
  match lines.findIdx? (fun l => l.contains needle) with
  | none => none
  | some i =>
      match (lines.drop i).find? (fun l => l.contains "add(proof_cptr, 0x") with
      | some l =>
          let after := (l.splitOn "add(proof_cptr, 0x").drop 1
          some (hexNatOf (after.head?.getD ""))
      | none => none

/-- The poseidon plan, DERIVED: the eval and q_eval widths come from the tracked
    contract, the compressed length from the dump's proof.bin, and the prefix G1
    count is solved from CD:49's own equation. none when the untracked bytes are
    absent. -/
def poseidonPlanFromArtifacts : IO (Option RepackedProofLayoutPlan) := do
  let src ← readGeneratedVerifier
  let comp ← readDumpProofBin
  let e? := (solSectionByteLen src "let eval_buf := REVERSED_EVALS_MPTR").map (fun b => b / wordBytes)
  let q? := (solSectionByteLen src "mstore(Q_EVAL_CPTR_MPTR, proof_cptr)").map (fun b => b / wordBytes)
  pure (do
    let e ← e?
    let q ← q?
    if comp.size == 0 || comp.size < (e + q) * wordBytes + 2 * g1CompressedBytes then none
    else
      let rest := comp.size - ((e + q) * wordBytes + 2 * g1CompressedBytes)
      if rest % g1CompressedBytes != 0 then none
      else some { g1Groups := [rest / g1CompressedBytes], numEvals := e, numPointSets := q })

/-! ## Item 0 -/

/-- GATE 2 (item 0). QVM:934-944 read from the file at #eval time: the assert on the
    32-byte width, the copy, the reverse, and nothing else, so the Lean def cannot
    drift unnoticed. The line numbers are HEAD's and vm/mod.rs is unmodified. -/
def item0_matchesQvmSource_ok : IO Bool :=
  readQvmRs >>= fun src => pure (
    (lineOf src 938).contains "pub(crate) fn scalar_le_to_be_word(bytes: &[u8]) -> [u8; 32]"
      && (lineOf src 939).contains "assert_eq!(bytes.len(), 32"
      && (lineOf src 942).contains "scalar.reverse()"
      && (lineOf src 940).contains "let mut scalar = [0u8; 32]"
      && (src.splitOn "\n").length == 4337)

/-- GATE 3. The reversal itself, on 32 pairwise-distinct bytes, plus every width that
    must fault: 0, 31, 33 and 64. The panic site is the Rust's assert line. -/
def scalarLeToBeWord_reversesAndGuards_ok : Bool :=
  let b := bytesFromNats ((List.range 32).map (fun i => i + 1))
  (match scalarLeToBeWord b with
   | .ok w => bytesToNats w == (List.range 32).map (fun i => (31 - i) + 1)
   | .error _ => false)
    && [0, 31, 33, 64].all (fun n =>
      isPanicAt "proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs:939"
        (scalarLeToBeWord (bytesFromNats (List.replicate n 7))))

/-- GATE 4. hex::encode fidelity: lowercase, no 0x prefix, two digits per byte. -/
def hexEncodeLower_matchesRustHex_ok : Bool :=
  hexEncodeLower (bytesFromNats [0x00, 0x0f, 0xff, 0xa3]) == "000fffa3"
    && hexEncodeLower Bytes.empty == ""
    && (hexEncodeLower (bytesFromNats (List.range 32))).length == 64

/-! ## repack_proof -/

/-- GATE 5 (hazard 2). The length-mismatch arm carries the plan's own five numbers
    and repackErrorOf? recovers the RepackError, i.e. the P-SE composition
    mapError GeneratorError.fromRepackError sees the same discriminant the Rust's ?
    at CD:147 produces. The counts are pairwise DISTINCT so a swapped field cannot
    hide (R-48). -/
def repackProof_lengthMismatchFields_ok : Bool :=
  match repackProof toyCodec fixturePlan (bytesFromNats (List.replicate 100 0)) with
  | .error f =>
      repackErrorOf? f == some (RepackError.lengthMismatch
        (expected := fixturePlan.compressedLen) (actual := 100)
        (prefixG1 := fixturePrefixG1) (numEvals := fixturePlan.numEvals)
        (numPointSets := fixturePlan.numPointSets))
        && fixturePlan.compressedLen != 100 && fixturePrefixG1 != fixturePlan.numEvals
        && fixturePlan.numEvals != fixturePlan.numPointSets
        && fixturePlan.numPointSets != fixturePrefixG1
  | .ok _ => false

/-- GATE 6 (hazard 2). The three Display strings, verbatim, tied to api.rs read at
    eval-time. api.rs is MODIFIED in the working tree (an uncommitted 57-line
    insertion at AP:530), so this searches by content: the strings are unchanged,
    the HEAD line numbers Api.lean cites are not. -/
def repackError_displayVerbatim_ok : IO Bool :=
  readApiRs >>= fun src => pure (
    src.contains "compressed proof length mismatch: expected {expected} bytes (prefix_g1={prefix_g1}, num_evals={num_evals}, num_point_sets={num_point_sets}, +f_com+pi), got {actual}"
      && src.contains "invalid compressed G1 at compressed[{offset}..{}]: bytes = 0x{bytes_hex}"
      && src.contains "non-canonical Fr scalar at compressed[{offset}..{}]: bytes = 0x{bytes_hex}"
      && printRepackError (RepackError.lengthMismatch (expected := 608) (actual := 7)
            (prefixG1 := 6) (numEvals := 5) (numPointSets := 2))
          == "compressed proof length mismatch: expected 608 bytes (prefix_g1=6, num_evals=5, num_point_sets=2, +f_com+pi), got 7"
      && printRepackError (RepackError.invalidCompressedG1 (offset := 48) (bytesHex := "aa"))
          == "invalid compressed G1 at compressed[48..96]: bytes = 0xaa"
      && printRepackError (RepackError.nonCanonicalScalar (offset := 0) (bytesHex := "ff"))
          == "non-canonical Fr scalar at compressed[0..32]: bytes = 0xff")

/-- GATE 7 (P-SE proofLen_eq_repackedLen). The walk's output length is exactly
    plan.repackedLen, and the two lengths differ by exactly the G1 widening, on a
    plan whose group list has seven entries. -/
def repackProof_layoutWidths_ok : Bool :=
  match repackProof toyCodec fixturePlan fixtureCompressed with
  | .ok out =>
      out.size == fixturePlan.repackedLen
        && fixturePlan.repackedLen - fixturePlan.compressedLen
             == (fixturePrefixG1 + 2) * (g1Bytes - g1CompressedBytes)
        && fixturePlan.compressedLen == fixtureCompressed.size
        && fixturePlan.g1Groups.length == 7
        && fixturePrefixG1 == 19
  | .error _ => false

/-- GATE 8 (the R1 note at repackPushG1). The codec's padded form IS the byte shape
    CD:80-85 inlines: 16 zeros, x(48), 16 zeros, y(48); and the identity arm
    (CD:74-77) is 128 zeros. Both arms are checked, and they differ. -/
def repackPushG1_paddedShapeMatchesRust_ok : Bool :=
  let x := bytesFromNats ((List.range 48).map (fun i => i + 1))
  let y := bytesFromNats ((List.range 48).map (fun i => 200 - i))
  let P : ToyG1 := { isInfinity := false, x := x, y := y }
  let Z : ToyG1 := { isInfinity := true, x := Bytes.empty, y := Bytes.empty }
  let padded := bytesToNats (toyToEip P)
  List.take 16 padded == List.replicate 16 0
    && List.take 48 (List.drop 16 padded) == bytesToNats (toyPad48 x)
    && List.take 16 (List.drop 64 padded) == List.replicate 16 0
    && List.take 48 (List.drop 80 padded) == bytesToNats (toyPad48 y)
    && (toyToEip P).size == 128
    && toyToEip Z == bytesFromNats (List.replicate 128 0)
    && toyToEip P != toyToEip Z

/-- GATE 9. The InvalidCompressedG1 arm (CD:67-73): the offset is the cursor into the
    compressed buffer, and the hex is of the compressed bytes, not the padded ones.
    Placed in the third prefix slot so the offset is not 0. -/
def repackProof_invalidCompressedG1_ok : Bool :=
  let good (i : Nat) : List Nat := [0x81 + i] ++ List.replicate 47 (i + 1)
  let bad : List Nat := [0xff] ++ List.replicate 47 3
  let scalar (i : Nat) : List Nat := List.replicate 32 ((i % 250) + 1)
  let plan : RepackedProofLayoutPlan := { g1Groups := [3], numEvals := 49, numPointSets := 0 }
  let blocks : List (List Nat) := [good 0, good 1, bad] ++ (List.range 49).map scalar
    ++ [good 2, good 3]
  match repackProof toyCodec plan (bytesFromNats (blocks.flatten)) with
  | .error f =>
      match repackErrorOf? f with
      | some (RepackError.invalidCompressedG1 offset bytesHex) =>
          offset == 96 && bytesHex == hexEncodeLower (bytesFromNats bad)
            && printRepackError (RepackError.invalidCompressedG1 offset bytesHex)
                 == "invalid compressed G1 at compressed[96..144]: bytes = 0x" ++ bytesHex
      | _ => false
  | .ok _ => false

/-- GATE 10. The NonCanonicalScalar arm (CD:96-104): a word at or above r is
    rejected, the offset is the scalar slot's position, and the hex is of the
    BIG-endian bytes (CD:98-99 reverse before hexing). Three slots are probed so the
    offset is not always the same, and a canonical word in the same slot passes. -/
def repackProof_nonCanonicalScalar_ok : Bool :=
  let g1blk : List Nat := [0x81] ++ List.replicate 47 2
  let canon (i : Nat) : List Nat := (List.range 32).map (fun j => if j == 0 then i + 1 else 0)
  let nonCanon : List Nat := bytesToNats (natToBytesLE Midfall.Assumptions.r 32)
  let nonCanon2 : List Nat := bytesToNats (natToBytesLE (Midfall.Assumptions.r + 7) 32)
  let plan : RepackedProofLayoutPlan := { g1Groups := [1], numEvals := 3, numPointSets := 0 }
  let mk (badAt : Nat) (bad : List Nat) : Bytes :=
    let blocks : List (List Nat) :=
      [g1blk] ++ (List.range 3).map (fun i => if i == badAt then bad else canon (i + 1))
        ++ [g1blk, g1blk]
    bytesFromNats (blocks.flatten)
  match repackProof toyCodec plan (mk 1 nonCanon) with
  | .error f =>
      (match repackErrorOf? f with
      | some (RepackError.nonCanonicalScalar offset bytesHex) =>
          offset == 80 && bytesHex == hexEncodeLower (bytesReverse (bytesFromNats nonCanon))
      | _ => false)
      && (match repackProof toyCodec plan (mk 2 nonCanon2) with
          | .error f2 => match repackErrorOf? f2 with
            | some (RepackError.nonCanonicalScalar o2 _) => o2 == 112
            | _ => false
          | .ok _ => false)
      && (match repackProof toyCodec plan (mk 0 (canon 9)) with
          | .ok _ => true
          | .error _ => false)
  | .ok _ => false

/-- GATE 11. Round trip: repack, then read every padded word back, and the scalars
    come out as the original LE bytes and the G1 slots as 128-byte blocks. This is
    the property P-SE calls calldata_roundtrip at the repack layer; it fails if any
    slot is dropped, duplicated or reordered. -/
def repackProof_roundtrip_ok : Bool :=
  match repackProof toyCodec fixturePlan fixtureCompressed with
  | .ok out =>
      let nats := bytesToNats out
      let src := bytesToNats fixtureCompressed
      let evalOk := (List.range fixturePlan.numEvals).all (fun i =>
        (List.take wordBytes (List.drop (fixtureEvalOffset fixturePlan + i * wordBytes) nats)).reverse
          == List.take wordBytes (List.drop (fixturePrefixG1 * g1CompressedBytes + i * wordBytes) src))
      let qOk := (List.range fixturePlan.numPointSets).all (fun i =>
        (List.take wordBytes (List.drop (fixtureQEvalOffset fixturePlan + i * wordBytes) nats)).reverse
          == List.take wordBytes (List.drop (fixtureFComCompressed fixturePlan + g1CompressedBytes
                + i * wordBytes) src))
      -- The 21 G1 slots are NOT contiguous: the eval block sits between the
      -- prefix and f_com, and the q_eval block between f_com and pi.
      let g1Slots : List Nat :=
        (List.range fixturePrefixG1).map (fun i => i * g1Bytes)
          ++ [fixtureQEvalOffset fixturePlan - g1Bytes, out.size - g1Bytes]
      let g1Ok := g1Slots.length == fixturePrefixG1 + 2
        && g1Slots.all (fun off =>
             List.take 16 (List.drop off nats) == List.replicate 16 0)
      evalOk && qOk && g1Ok && out.size == fixturePlan.repackedLen
  | .error _ => false

/-- A well-formed compressed proof for ANY plan: canonical scalars (small) and
    decodable G1 blocks, so the walk cannot fail on shape and the gate below is
    really about the tiling. -/
def mkValidCompressed (plan : RepackedProofLayoutPlan) : Bytes :=
  let g1blk : List Nat := [0x81] ++ List.replicate 47 0
  let sc (i : Nat) : List Nat := [i % 250 + 1] ++ List.replicate 31 0
  let blocks : List (List Nat) :=
    (List.range plan.prefixG1Count).map (fun _ => g1blk)
      ++ (List.range plan.numEvals).map sc ++ [g1blk]
      ++ (List.range plan.numPointSets).map sc ++ [g1blk]
  bytesFromNats (blocks.flatten)

/-- GATE 12. The debug_assert at CD:127 that R4 compiles out, asserted as a gate
    instead: the five passes tile the compressed proof with no slack. Checked for
    three distinct plans, including one with an empty group list and one with no
    scalars, and against mkValidCompressed so a shape failure cannot masquerade as
    a tiling failure. -/
def repackProof_walkConsumesExactly_ok : Bool :=
  let plans : List RepackedProofLayoutPlan :=
    [ { g1Groups := [8, 1, 3, 1, 1, 4, 1], numEvals := 48, numPointSets := 3 },
      { g1Groups := [], numEvals := 1, numPointSets := 1 },
      { g1Groups := [2, 2], numEvals := 0, numPointSets := 0 } ]
  plans.all (fun plan =>
    let input := mkValidCompressed plan
    input.size == plan.compressedLen
      && match repackProof toyCodec plan input with
         | .ok out => out.size == plan.repackedLen && plan.compressedLen
             == (plan.prefixG1Count + 2) * g1CompressedBytes
               + (plan.numEvals + plan.numPointSets) * wordBytes
         | .error _ => false)

/-! ## encode_calldata -/

/-- GATE 13 (CD:137-146). The instance-count guard, with the Rust's format! payload
    verbatim, checked at two distinct (expected, got) pairs so the two interpolations
    cannot be swapped. -/
def encodeCalldataWithInstances_instanceMismatch_ok : Bool :=
  (match encodeCalldataWithInstances toyCodec fixturePlan 2 fixtureCompressed [1, 2, 3] with
   | .error (ApiFault.error (GeneratorError.planning stage message)) =>
       stage == "calldata" && message == "instance length mismatch: expected 2, got 3"
   | _ => false)
    && (match encodeCalldataWithInstances toyCodec fixturePlan 5 fixtureCompressed [1] with
       | .error (ApiFault.error (GeneratorError.planning stage message)) =>
           stage == "calldata" && message == "instance length mismatch: expected 5, got 1"
       | _ => false)
    && printGeneratorError (GeneratorError.planning (stage := "calldata")
        (message := "instance length mismatch: expected 2, got 3"))
         == "generator planning failed during calldata: instance length mismatch: expected 2, got 3"

/-- GATE 14 (PLAN 9.5's end_to_end_noAcc right-hand side). Repack then encode: the
    calldata's proof-length word equals plan.repackedLen, the proof payload is the
    repacked bytes, and the whole envelope is what Evm.lean's encoder produces from
    them. Three distinct instance counts. -/
def encodeCalldataWithInstances_endToEnd_ok : Bool :=
  let cases : List (Nat × List Word256) := [ (0, []), (1, [7]), (3, [1, 2, 3]) ]
  cases.all (fun (n, inst) =>
    match encodeCalldataWithInstances toyCodec fixturePlan n fixtureCompressed inst,
          repackProof toyCodec fixturePlan fixtureCompressed with
    | .ok cd, .ok repacked =>
        cd == encodeCalldata repacked inst
          && bytesToNatBE (bytesTake cd 0x44 0x20 |>.getD Bytes.empty) == fixturePlan.repackedLen
          && bytesTake cd 0x64 repacked.size == some repacked
          && bytesToNatBE (bytesTake cd (0x64 + repacked.size) 0x20 |>.getD Bytes.empty) == n
    | _, _ => false)

/-! ## The Rust artifact: the poseidon fixture -/

/-- GATE 15 (D-P19, UNTRACKED-CONDITIONAL - see the section header). The scalar leg
    of repackProof against the real Rust repack: the plan is derived from the tracked
    contract, the compressed bytes are the dump's real proof, and the repacked bytes
    are the ones inside the dump's real calldata. Every eval and q_eval word my walk
    emits must equal the word the Rust emitted. -/
def repackProof_scalarLeg_matchesRust_ok : IO Bool :=
  poseidonPlanFromArtifacts >>= fun mp =>
  readDumpProofBin >>= fun comp =>
  readDumpCalldataBin >>= fun cd =>
  pure (match mp with
    | none => true
    | some plan =>
        if comp.size == 0 || cd.size == 0 then true
        else match repackProof toyCodec plan comp with
          | .error _ => false
          | .ok out =>
              match bytesTake cd 0x64 out.size with
              | none => false
              | some real =>
                  out.size == real.size && out.size == plan.repackedLen
                    && (List.range plan.numEvals).all (fun i =>
                        bytesTake out (fixtureEvalOffset plan + i * wordBytes) wordBytes
                          == bytesTake real (fixtureEvalOffset plan + i * wordBytes) wordBytes)
                    && (List.range plan.numPointSets).all (fun i =>
                        bytesTake out (fixtureQEvalOffset plan + i * wordBytes) wordBytes
                          == bytesTake real (fixtureQEvalOffset plan + i * wordBytes) wordBytes)
          )

/-- GATE 16 (D-P19, UNTRACKED-CONDITIONAL). The G1 leg's POSITIONS and PADDING
    against the real repacked proof: at each of the prefix-plus-two slots my walk
    emits, the Rust's bytes have the 16-byte high pad on both coordinates, and the x
    word's leading byte is the compressed block's leading byte with the ZCash
    compression bits masked off. The square root is the codec's, not this package's
    (D-P17); the FRAME this package builds is checked against real bytes. -/
def repackProof_g1Frame_matchesRust_ok : IO Bool :=
  poseidonPlanFromArtifacts >>= fun mp =>
  readDumpProofBin >>= fun comp =>
  readDumpCalldataBin >>= fun cd =>
  pure (match mp with
    | none => true
    | some plan =>
        if comp.size == 0 || cd.size == 0 then true
        else
          let repackedSlots : List Nat := (List.range plan.prefixG1Count).map (fun i => i * g1Bytes)
            ++ [fixtureQEvalOffset plan - g1Bytes, plan.repackedLen - g1Bytes]
          let compressedSlots : List Nat :=
            (List.range plan.prefixG1Count).map (fun i => i * g1CompressedBytes)
              ++ [fixtureFComCompressed plan, comp.size - g1CompressedBytes]
          repackedSlots.length == compressedSlots.length
            && repackedSlots.length == plan.prefixG1Count + 2
            && (repackedSlots.zip compressedSlots).all (fun rc =>
                 let rp := rc.1
                 let cp := rc.2
                 bytesToNats (bytesTake cd (0x64 + rp) 16 |>.getD Bytes.empty)
                     == List.replicate 16 0
                   && bytesToNats (bytesTake cd (0x64 + rp + 64) 16 |>.getD Bytes.empty)
                     == List.replicate 16 0
                   && match firstByteOf (bytesTake cd (0x64 + rp + 16) 1 |>.getD Bytes.empty),
                           firstByteOf (bytesTake comp cp 1 |>.getD Bytes.empty) with
                      | some hx, some hc => hx % 32 == hx && hc % 32 == hx
                      | _, _ => false))

/-- GATE 17 (D-P19, UNTRACKED-CONDITIONAL). The whole envelope: re-encoding the
    Rust's own repacked proof with the Rust's own instance word must reproduce
    calldata.bin byte for byte. This is the strongest form of the round trip and
    exactly the gate the brief asked for; it is conditional only because the artifact
    is gitignored. Note instance.be is a to_repr, i.e. LITTLE-endian despite the
    name, which is what feToU256 expects. -/
def encodeCalldata_matchesDumpCalldata_ok : IO Bool :=
  readDumpCalldataBin >>= fun cd =>
  readDumpInstanceBe >>= fun inst =>
  pure (if cd.size == 0 || inst.size != 32 then true
    else match bytesTake cd 0x64 (cd.size - 0x64 - 0x40) with
      | none => false
      | some proof => match feToU256 (bytesToNats inst) with
        | .ok w => encodeCalldata proof [w] == cd && cd.size == 4484
        | .error _ => false)

/-! ## HAZARD 1: what the decoder actually accepts -/

/-- GATE 18. Trailing bytes: the template pins the total calldatasize and the
    generated contract renders the pin with the instance-array end. PLAN 13:587's
    claim that trailing bytes may be accepted is FALSE of the current tree. -/
def decoderAcceptance_trailingBytesRejected_ok : IO Bool :=
  readVkLoading >>= fun vl =>
  readGeneratedVerifier >>= fun sol =>
  pure (vl.contains "eq(calldatasize(), add(INSTANCE_CPTR, {{ (num_instances * 32)|hex() }}))"
    && sol.contains "eq(calldatasize(), add(INSTANCE_CPTR,"
    && sol.contains "Any trailing bytes fail closed")

/-- GATE 19. Instance words at or above r: rejected, and the rejection is deferred
    onto the success fold rather than reverting inline - which is why the fold's own
    fail(ERR_NON_CANONICAL_SCALAR) has to be there too. -/
def decoderAcceptance_instanceWordsCanonical_ok : IO Bool :=
  readParserPartial >>= fun pp =>
  pure (pp.contains "success := and(success, lt(inst_be, r))"
    && pp.contains "if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }"
    && countMatches pp "lt(inst_be, r)" == 1)

/-- GATE 20. Proof eval and q_eval words at or above r: rejected inline, twice. -/
def decoderAcceptance_proofScalarsCanonical_ok : IO Bool :=
  readParserPartial >>= fun pp =>
  pure (countMatches pp "if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }" == 2)

/-- GATE 21. G1 words: the 16-byte high pad is enforced on both coordinates (the
    shr(128, ..) must be zero) and both coordinates are range-checked below p, and
    the 128 bytes are absorbed VERBATIM, so the accepted encoding is the only
    encoding of that point - which is what makes D7's EXACT claim over raw Word256
    the right shape. -/
def decoderAcceptance_g1WordsCanonical_ok : IO Bool :=
  readAsmHelpers >>= fun ah =>
  pure (ah.contains "if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }"
    && ah.contains "if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }"
    && ah.contains "calldatacopy(buf_len, cptr, 0x80)"
    && countMatches ah "fail(ERR_BAD_POINT_ENCODING)" == 4)

/-- GATE 22 (the required finding, as a gate). All four contract guards are present,
    AND the parser's own end-of-proof cursor check is present, AND the repacker
    rejects the same non-canonical scalars on the host side. If any of these ever
    disappears, D7's EXACT claim is the thing that breaks, and this gate reddens
    first. -/
def decoderAcceptance_agreesWithD7_ok : IO Bool :=
  decoderAcceptance_trailingBytesRejected_ok >>= fun t =>
  decoderAcceptance_instanceWordsCanonical_ok >>= fun i =>
  decoderAcceptance_proofScalarsCanonical_ok >>= fun e =>
  decoderAcceptance_g1WordsCanonical_ok >>= fun g =>
  readParserPartial >>= fun pp =>
  pure (t && i && e && g
    && pp.contains "if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }")

end Midfall.Generator.CalldataKats

#eval Midfall.Generator.CalldataKats.calldataArtifactsReachable_ok -- expect true
#eval Midfall.Generator.CalldataKats.calldataDumpBytesPresent_ok -- expect true
#eval Midfall.Generator.CalldataKats.item0_matchesQvmSource_ok -- expect true
#eval Midfall.Generator.CalldataKats.scalarLeToBeWord_reversesAndGuards_ok -- expect true
#eval Midfall.Generator.CalldataKats.hexEncodeLower_matchesRustHex_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_lengthMismatchFields_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackError_displayVerbatim_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_layoutWidths_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackPushG1_paddedShapeMatchesRust_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_invalidCompressedG1_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_nonCanonicalScalar_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_roundtrip_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_walkConsumesExactly_ok -- expect true
#eval Midfall.Generator.CalldataKats.encodeCalldataWithInstances_instanceMismatch_ok -- expect true
#eval Midfall.Generator.CalldataKats.encodeCalldataWithInstances_endToEnd_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_scalarLeg_matchesRust_ok -- expect true
#eval Midfall.Generator.CalldataKats.repackProof_g1Frame_matchesRust_ok -- expect true
#eval Midfall.Generator.CalldataKats.encodeCalldata_matchesDumpCalldata_ok -- expect true
#eval Midfall.Generator.CalldataKats.decoderAcceptance_trailingBytesRejected_ok -- expect true
#eval Midfall.Generator.CalldataKats.decoderAcceptance_instanceWordsCanonical_ok -- expect true
#eval Midfall.Generator.CalldataKats.decoderAcceptance_proofScalarsCanonical_ok -- expect true
#eval Midfall.Generator.CalldataKats.decoderAcceptance_g1WordsCanonical_ok -- expect true
#eval Midfall.Generator.CalldataKats.decoderAcceptance_agreesWithD7_ok -- expect true
