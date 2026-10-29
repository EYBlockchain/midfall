-- |
-- Midfall.Generator.VerifierPartials
--
-- P-13a: the first five Askama partials under
-- proofs/solidity-verifier/templates/partials/verifier/ ported as Lean render
-- functions - AssemblyHelpers.yul (310 lines at HEAD), VkLoading.yul (141),
-- Lagrange.yul (99), QuotientAndLinearization.yul (165), FinalPairing.yul (92).
-- P-13b (this package) extends the same layer with two more of them:
-- TranscriptProofParser.yul (424 lines at HEAD) and AccumulatorHelpers.yul (372
-- at HEAD). Nothing here is a parallel render layer: PartialCtx, jinjaFor,
-- hexFilter, occ / artifactMatch / includeBoundary and readDump are P-13a's and
-- the two new renders are gated with them.
-- This is a TEXT port: each renderX returns the BYTES Askama returns for that
-- partial, not an AST. It extends the render layer (Filters.lean owns the Jinja
-- filters, Models.lean the records, Render.lean the AST printer, YulGolden.lean
-- the structural golden test) rather than paralleling it.
--
-- TWO TARGETS, PINNED SEPARATELY - the distinction the plan insists on (D-P13).
--
--   * TEXTUAL. M3 acceptance is golden byte-equality. The gates named
--     <partial>_bytesExact_ok read the TRACKED rendered artifact
--     proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol at
--     #eval time (D-P19 - no pasted strings) and require the rendered bytes to
--     occur there EXACTLY ONCE with the include boundary on both sides. These are
--     the gates that die from one wrong space.
--   * STRUCTURAL. Phase 5's irCheck uses YulSemantics.SyntaxEq.stmtsBeq on the
--     vendored AST. The gates <slice>_astAgrees_ok compare the token stream of the
--     SAME rendered bytes against YulSemantics.EVM.print of a yul% AST, and
--     finalPairing_beq_ok compares that AST against raw constructors under
--     stmtsBeq. No structural gate here stands in for a textual one, and no
--     textual gate is offered as evidence for irCheck. The token relation is the
--     SECONDARY one: YulGolden.lean's header explains why stmtsBeq is
--     authoritative and the token stream is strictly weaker than it.
--
-- THE WHITESPACE MODEL, measured off the artifact (hazard 1). Askama is Jinja
-- shaped and the rules that decide the bytes are:
--
--   1. Text outside a tag is emitted verbatim, one output line per source line.
--   2. A tag written with a leading dash strips ALL whitespace immediately before
--      it, including the newline that ended the previous line and the tag line's
--      own indent; a trailing dash strips after. So a control line alone on its
--      line contributes no line of its own, and an if whose condition is false
--      removes its newline rather than leaving a blank one. Measured: no rendered
--      line of any of the five partials is whitespace-only, while the DUMP has six
--      such lines (D:85, 525, 1098, 1103, 1891, 3010) and every one of them comes
--      from the CONTRACT template's include lines, i.e. outside a partial.
--      zeroRenderNewlineLaw_ok pins this.
--   3. An include emits the included file's render with NO separator, and the
--      parent's own text around it is kept: the four spaces that indent the
--      include line land at the START of the partial's first line (which is why
--      D:1497 carries 16 spaces where Lagrange.yul:1 has 12), and the parent
--      contributes LF LF four-space after it.
--   4. FINDING, not stated in the brief: Askama does NOT emit the included file's
--      FINAL newline. The dump proves it - after each partial's last line there
--      are exactly two newlines before the next include's four spaces, which is
--      the parent's own LF LF four-space and nothing else; had the partial kept
--      its trailing newline there would be three. The root template behaves the
--      same way (the dump's last byte is '}' while
--      T:contracts/Halo2Verifier.sol ends '}' + LF). Every renderX here therefore
--      omits the trailing newline, and the boundary half of each byte-exact gate
--      is what pins it: put the newline back and perturb_trailingNewline_ok goes
--      red.
--   5. An if/else branch changes the bytes but NOT the indentation: both branches
--      are written at the same column in the source, so the difference is content,
--      not depth. The one ragged site is AssemblyHelpers.yul:294, where the
--      template author typed 32 spaces instead of 16; the port keeps it verbatim
--      and perturb_raggedIndent_ok shows the gate would notice a tidy-up.
--
-- THE DEPLOYED PROFILE (the poseidon fixture dump, R4 release profile). Read off
-- the artifact and re-derived by poseidonCtx_derivedFromArtifact_ok:
-- trace = false, gas_checkpoints = false (zero 'gas_checkpoint' occurrences in
-- the whole dump), quotient_probe = false, expected_has_accumulator = FALSE,
-- embedded_vk = None, quotient_external = None, quotient_direct = None,
-- k = 6, num_instances = 1, num_neg_lagranges = 9, proof_len = 0x10e0,
-- VK_MPTR = 0x2900, scalar_inv_scratch_mptr = 0x2800,
-- final_pairing_scratch_mptr = 0x1240.
-- P-13b adds, all read off the same artifact and re-derived by
-- parserProofLayout_derivedFromArtifact_ok: ONE user phase of 8 advice G1s and
-- ZERO user challenges (D:1271-1283); ten proof sections tiling 0x64..0x1144
-- (advice 0x0400, lookup_m 0x80, perm_z 0x0180, lookup helpers 0x80 + acc 0x80,
-- trash 0x80, quotient limbs 0x0200, evals 0x0600, f_com 0x80, q_evals 0x60,
-- pi 0x80 - and they sum to exactly 0x10e0, gate 35); num_lookups 1,
-- num_permutation_zs 3, lookup_h_plus_acc 2, num_trashcans 1;
-- truncated_challenges TRUE (the x3 mask at D:1449 is the observable, so this
-- fixture was built with that cargo feature on); and expected_has_accumulator
-- FALSE, which zeroes the whole of validate_public_accumulator.
--
-- WHAT THE PORT DOES NOT PIN, said out loud:
--   * QuotientAndLinearization.yul's deployed arm is a match on quotient_external
--     -> None, then on quotient_direct -> None, then two includes of the
--     quotient_numerator partials, which are P-13c's. Those bytes are PARAMETERS
--     here (quotientHelpers, quotientNumeratorBlock), so the gate pins every byte
--     this partial owns and none of the bytes P-13c owns.
--   * Arms the deployed profile does not take - the accumulator-batched pairing
--     block, the trace arms, the gas-checkpoint lines, the embedded-VK loop, the
--     external-quotient block, the quotient probe - have NO tracked artifact. They
--     are ported so another profile can be rendered, and gated only for SELECTION
--     (flipping the flag changes the bytes and breaks the artifact match), never
--     for content. inertFields_ok names the context fields no gate can see.
--   * P-13b: the ENTIRE accumulator arm of AccumulatorHelpers.yul - 206 of its
--     372 template lines, both G1MSM staticcalls, the carried-scalar arms and the
--     fixed-base tail loop - has no tracked artifact, because the deployed profile
--     has no public accumulator. Gates 37-38 render it against a SYNTHETIC context
--     (accSynthCtx / accSynthCollapsedCtx) whose values are chosen, not observed;
--     they pin that the arms exist and discriminate, never that the Rust generator
--     would ship these bytes. Gate 36 states how much the profile does render.
--   * The dump's proof.bin and calldata.bin are NOT tracked (R-53 / P-12 F-1);
--     nothing here reads them.
--
-- CITATION NOTATION, as in Render.lean and Filters.lean: D: is the tracked dump
-- target/poseidon-fixture-dump/Halo2Verifier.sol (3024 lines, no trailing
-- newline); DVK: is Halo2VerifyingKey.sol beside it; T: is
-- proofs/solidity-verifier/templates/; M: is src/lowering/render/models.rs.
-- P-13b adds: ART: is src/lowering/artifacts.rs (the Halo2Verifier assembly, the
-- only place the template inputs are COMPUTED), AP: is src/lowering/abi/proof.rs
-- (ProofCalldataLayout, ported in Abi.lean), LM: is src/lowering/layout/mod.rs,
-- and memory.rs is src/lowering/layout/memory.rs.

import YulSemantics.Syntax
import YulSemantics.PrettyPrint
import Midfall.Generator.Filters
import Midfall.Generator.Models
import Midfall.Generator.Layout
import Midfall.Generator.Abi
import Midfall.Generator.Evm
import Midfall.Generator.YulGolden
import Midfall.Generator.Quotient.Evaluator

namespace Midfall.Generator
open YulSemantics

/-! ## The Jinja-shaped plumbing

jinjaFor is the one piece of template machinery this port needs beyond the filters
already in Filters.lean: Askama's for-loop binds the loop variable plus a loop
object carrying index0/index/first/last, and a zero-iteration loop emits nothing
at all - including no newline (hazard 1). -/

/-- Askama's loop object. Only index0 and last are read by the five partials;
    index and first are ported because the template language has them and a later
    package will reach for one. -/
structure JinjaLoop where
  index0 : Nat
  index : Nat
  first : Bool
  last : Bool

/-- The loop body is called once per element with the element and its loop value;
    an empty list renders the empty string. rust: the Askama for code path; the
    corpus sites are T:VkLoading.yul:33, :37, :47 and
    T:QuotientAndLinearization.yul:55, :137, :146. -/
def jinjaFor {alpha : Type} (xs : List alpha) (f : alpha -> JinjaLoop -> String) : String :=
  String.join (List.zipIdx xs |>.map fun (x, i) =>
    f x { index0 := i, index := i + 1, first := i == 0, last := i + 1 == xs.length })

/-! ## The render context

The five partials read 26 template expressions between them. This is that set and
nothing else: it is NOT a second Halo2Verifier record (Models.lean owns that, and
D-P17 keeps Generator.Vk and Midfall/Instances/ out). Each field names the Rust
model field it mirrors. -/

/-- The template inputs of the five verifier partials: field for field the subset
    of Midfall.Generator.Halo2Verifier (Models.lean, rust: M:497-637) that these
    templates interpolate, plus the three memory.* slots they read (rust:
    VerifierMemoryLayout, layout/memory.rs:437, :510, :512). -/
structure PartialCtx where
  /-- M:498 templateConstants. The values come from Models.lean's port of the
      Rust Default impl for TemplateConstants (M:183-284), NOT from the artifact. -/
  templateConstants : TemplateConstants
  /-- memory.rs:437 scalar_inv_scratch_mptr. -/
  scalarInvScratchMptr : Nat
  /-- memory.rs:512 final_pairing_scratch_mptr. -/
  finalPairingScratchMptr : Nat
  /-- memory.rs:510 accumulator_pairing_batch_mptr. -/
  accumulatorPairingBatchMptr : Nat
  /-- The VK_MPTR the embedded-VK arm indexes from (M:604-606 fixed_comm_mptr is
      the sibling slot). -/
  vkMptr : Nat
  /-- M:499 trace. -/
  trace : Bool
  /-- M:502 gas_checkpoints. -/
  gasCheckpoints : Bool
  /-- M:506 quotient_probe. -/
  quotientProbe : Bool
  /-- M:615 expected_has_accumulator. -/
  expectedHasAccumulator : Bool
  /-- M:616-624: the four words VkLoading cross-checks against the VK header. -/
  expectedHasAccumulatorWord : Nat
  expectedAccOffset : Nat
  expectedNumAccLimbs : Nat
  expectedNumAccLimbBits : Nat
  /-- M:524 embedded_vk, which drives the match at T:VkLoading.yul:22. -/
  embeddedVk : Option Halo2VerifyingKey
  /-- M:620 expected_quotient_codehash, the match at
      T:QuotientAndLinearization.yul:15. -/
  expectedQuotientCodehash : Option Word256
  /-- M:618 quotient_external, the outer match at T:QuotientAndLinearization.yul:1. -/
  quotientExternal : Option QuotientExternal
  /-- M:594 quotient_direct, the inner match at T:QuotientAndLinearization.yul:53. -/
  quotientDirect : Option DirectQuotientRendering
  /-- M:534 k, M:531 num_instances, plus the three counts the Lagrange and
      linearization blocks interpolate. -/
  k : Nat
  numInstances : Nat
  numNegLagranges : Nat
  numQuotients : Nat
  /-- M:536 proof_len. -/
  proofLen : Nat
  /-- M:599 simple_selector_cols and M:606 fixed_comm_mptr, read only by arms the
      deployed profile does not take. -/
  simpleSelectorCols : List Nat
  fixedCommMptr : Nat
  /-- P-13b. M:558 user_phases (rust: ART:160-170, one UserPhase per advice
      phase, advice_bytes taken from proof_layout.advice_phases[idx]). Drives the
      for at T:TranscriptProofParser.yul:105. -/
  userPhases : List UserPhase
  /-- P-13b. M:536 codegen_layout.proof (rust: ART:282-284 clones
      plan.proof_layout; the type is ProofCalldataLayout, AP:54-90). Every
      codegen_layout.proof.X.byte_len the parser interpolates comes from here:
      T::147, :177, :207, :247, :279, :312, :377, and the per-lookup helpers at
      :205 and :207. -/
  proofLayout : ProofCalldataLayout
  /-- P-13b. M:560 num_lookups (ART:291), the guard at T::142. -/
  numLookups : Nat
  /-- P-13b. M:561 num_permutation_zs (ART:292), the guard at T::172. -/
  numPermutationZs : Nat
  /-- P-13b. M:562 lookup_h_plus_acc (ART:172: sum of lookup_chunks plus
      num_lookups), the guard at T::195. -/
  lookupHPlusAcc : Nat
  /-- P-13b. M:563 num_trashcans (ART:294), the guard at T::242. -/
  numTrashcans : Nat
  /-- P-13b. M:614 truncated_challenges, a CARGO-FEATURE flag (ART:328:
      cfg!(feature = "truncated-challenges")), the guard at
      T:TranscriptProofParser.yul:355. The deployed dump HAS the x3 mask, so this
      fixture was built with that feature on. -/
  truncatedChallenges : Bool
  /-- P-13b. M:600 proof_commit_trace_base (ART:323, = LM:782 PROOF_COMMIT_BASE),
      read only by the trace arms, T:TranscriptProofParser.yul:101. -/
  proofCommitTraceBase : Nat
  /-- P-13b. M:601 proof_eval_trace_base (ART:324, = LM:783 PROOF_EVAL_BASE), read
      only by the trace arms, T:TranscriptProofParser.yul:102. -/
  proofEvalTraceBase : Nat
  /-- P-13b. M:628 expected_acc_has_carried_scalars (ART:233 and :242 from
      AccumulatorEncoding::has_carried_scalars; ART:245's unwrap_or gives false
      when there is no accumulator at all). Drives the ifs at
      T:AccumulatorHelpers.yul:218, :253, :272, :287 and :306. -/
  expectedAccHasCarriedScalars : Bool
  /-- P-13b. M:636 acc_fixed_bases, the RHS MSM fixed-base tail as
      (point_mptr, negate_scalar) in BTreeMap name order (ART:181-227, sorted at
      ART:225; ART:224's unwrap_or_default gives [] with no accumulator). Drives
      the ifs at T:AccumulatorHelpers.yul:252 and :305 and the for at :314. -/
  accFixedBases : List (Nat × Bool)
  /-- P-13b. memory.rs:507 acc_msm_scratch (Lean port: Layout.lean:967), the one
      memory.* slot T:AccumulatorHelpers.yul:216 interpolates. It sits inside the
      expected_has_accumulator arm, so the deployed profile never renders it. -/
  accMsmScratch : Nat
  /-- P-13c. M:590 quotient_program, the match at T:QuotientNumeratorBlock.yul:133.
    Some selects the compact-VM arm (:134-1395); None selects the legacy/direct arm
    (:1396-1440). The deployed dump takes the Some arm. -/
  quotientProgram : Option QuotientProgram
  /-- P-13c. M:584 quotient_inline_computations, the double for at
      T:QuotientNumeratorBlock.yul:198-202 (the direct inline prefix before the VM). -/
  quotientInlineComputations : List (List String)
  /-- P-13c. M:585 quotient_eval_numer_computations, the double for at :1417-1421, inside
      the 'when None' arm the deployed profile does not take. -/
  quotientEvalNumerComputations : List (List String)
  /-- P-13c. M:586 quotient_post_vm_computations, the double for at :1368-1372. -/
  quotientPostVmComputations : List (List String)
  /-- P-13c. M:587 quotient_native_permutation_computation, the for at :1225-1227. -/
  quotientNativePermutationComputation : List String
  /-- P-13c. M:588 quotient_native_lookup_computation, the for at :1249-1251. -/
  quotientNativeLookupComputation : List String
  /-- P-13c. M:589 quotient_native_identity_computations, the outer for at :1272-1278.
      This is the ONE generated list whose block partition is observable: each block
      becomes its own 'case N { ... }' arm, so the number of blocks is rendered. The
      four flat lists above render their blocks back to back with no separator, so a
      render cannot distinguish [[a,b]] from [[a],[b]] - stated here because the
      extraction in this file hands those back as a single block. -/
  quotientNativeIdentityComputations : List (List String)
  /-- P-13c. M:602 quotient_identity_trace_base, read only by the trace arms
      (T:QuotientNumeratorBlock.yul:165 and :1412). Inert while trace = false. -/
  quotientIdentityTraceBase : Nat
  /-- P-13c. M:507-509: the three shape-recognition flags that gate the optional helpers
      at T:QuotientHelpers.yul:16, :35 and :59. The deployed fixture recognises pow5 only. -/
  quotientPow5Helper : Bool
  quotientLimb7Helper : Bool
  quotientWideLimb7Helper : Bool
  /-- P-13c. M:521-522: the two coefficient tables the limb7 helpers iterate
      (T:QuotientHelpers.yul:49 and :72). Both loops are inside ifs the deployed profile
      does not take, so both tables are inert here; Models.lean's limbCoeffArrays_length_ok
      is what pins their length. -/
  limb7YulCoeffs : List String
  wideLimb7YulCoeffs : List String
  /-- P-13c. M:523 fr_delta (rust: QVM:4131-4133 fr_delta_literal), interpolated only at
      T:QuotientNumeratorBlock.yul:1407 - inside the 'when None' arm. Inert for the byte
      gate, but NOT unobservable: the same literal is emitted by the generated permutation
      callback at D:1975, which quotientFrDelta_derivedFromArtifact_ok reads. -/
  frDelta : String
  /-- P-13e. M:537 memory: the whole VerifierMemoryLayout the deployed artifact
      declares. Constants.sol interpolates 50 of its slots and PrecompileSmoke.sol
      three more; poseidonMemoryLayout below is the transcription and
      constants_memoryMatchesArtifact_ok re-reads every one of them out of the
      artifact's own constant block, so a transcribed digit that disagrees with the
      dump is a red gate rather than a silently wrong render. -/
  memory : VerifierMemoryLayout
  /-- P-13e. M:538 vk_header: the VK header WORD offsets, rendered as
      `memory.vk_mptr + vk_header.X` at T:Constants.sol:51-64. The values are
      Models.lean's port of LM:406-435's discriminants, not the artifact's. -/
  vkHeader : VkHeaderTemplateSlots
  /-- P-13e. M:530 vk_len: EXPECTED_VK_PAYLOAD_LENGTH, rendered DECIMAL at
      T:Constants.sol:9-10 (and +1 for EXPECTED_VK_LENGTH, the INVALID byte). -/
  vkLen : Nat
  /-- P-13e. M:525 expected_vk_codehash: the outer match of T:Constants.sol:1 and
      T:Constructors.sol:1, and the hex_padded(64) word at T:Constants.sol:11. -/
  expectedVkCodehash : Option Word256
  /-- P-13e. M:529 build_id: the BUILD_ID constant at T:Constants.sol:216. -/
  buildId : Word256
  /-- P-13e. M:514 constructor_g1msm_smoke_gas: G1MSM_GAS_SMOKE at
      T:Constants.sol:198, and the bound the smoke probe forwards at
      T:PrecompileSmoke.sol:202. -/
  constructorG1msmSmokeGas : Nat
  /-- P-13e. M:511 constructor_g1msm_smoke_input_bytes: the loop bound and
      staticcall length at T:PrecompileSmoke.sol:197-202. -/
  constructorG1msmSmokeInputBytes : Nat
  /-- P-13e. M:520 acc_rhs_msm_gas, read only inside the expected_has_accumulator
      arm at T:Constants.sol:199-204, which the deployed profile does not take. -/
  accRhsMsmGas : Nat
  /-- P-13e. M:582 expected_quotient_len, read only by T:Constants.sol:24 inside
      the Some arm of the expected_quotient_codehash match. -/
  expectedQuotientLen : Option Nat
  /-- P-13e. M:542 proof_cptr. A Ptr, so `proof_cptr - 1` at T:Constants.sol:35 is
      WORD-wise (ENC:733-741): 0x64 - 1 renders 0x44, not 0x63. -/
  proofCptr : Ptr
  /-- P-13e. M:551 num_instance_cptr and M:554 instance_cptr, both through
      hex_padded(2) at T:Constants.sol:37-38. -/
  numInstanceCptr : Nat
  instanceCptr : Nat
  /-- P-13e. M:603 selector_trace_base, read only by the trace arm at
      T:Pcs.yul:36-37. Inert while trace = false. -/
  selectorTraceBase : Nat

/-- The poseidon fixture's proof calldata layout (P-13b). Every number here is a
    byte length the DEPLOYED artifact interpolates, and
    parserProofLayout_derivedFromArtifact_ok re-reads each one out of the dump's own
    `add(proof_cptr, 0x..)` lines, so the parser byte gate is not self-fulfilling.
    The starts tile: each is the previous end, and the last end is proofEnd, which is
    why the parser's :416 cursor check can hold at all. rust: AP:54-90 with
    ProofSection.new (AP:27-34) deriving byteLen = itemCount * itemBytes. -/
def poseidonProofLayout : ProofCalldataLayout :=
  { proofCptr := 0x64                       -- D:101 PROOF_CPTR
    advicePhases := [ProofSection.new 0x64 8 g1Bytes]      -- D:1275 0x0400
    lookupMultiplicities := ProofSection.new 0x464 1 g1Bytes  -- D:1295 0x80
    permutationProducts := ProofSection.new 0x4e4 3 g1Bytes   -- D:1314 0x0180
    lookups := [{ lookup := 0
                  helpers := ProofSection.new 0x664 1 g1Bytes     -- D:1332 0x80
                  accumulator := ProofSection.new 0x6e4 1 g1Bytes } ] -- D:1343 0x80
    trash := ProofSection.new 0x764 1 g1Bytes              -- D:1357 0x80
    quotientLimbs := ProofSection.new 0x7e4 4 g1Bytes      -- D:1380 0x0200
    evals := ProofSection.new 0x9e4 48 wordBytes           -- D:1405 0x0600
    fCom := ProofSection.new 0xfe4 1 g1Bytes               -- D:1434 0x80
    qEvals := ProofSection.new 0x1064 3 wordBytes          -- D:1460 0x60
    pi := ProofSection.new 0x10c4 1 g1Bytes                -- D:1481 0x80
    quotientCommCptr := 0x7e4
    evalCptr := 0x9e4
    wCptr := 0xfe4
    qEvalCptr := 0x1064
    proofEnd := 0x1144                        -- D:102 NUM_INSTANCE_CPTR
    proofLen := 0x10e0 }                      -- D:1164

/-- The deployed fixture's VerifierMemoryLayout, transcribed from the artifact's
    own constant block (D:104-166). This is the generator's INPUT record, not a
    re-derivation: the Rust builds it in `VerifierMemoryLayout::new` (MEM:591-973,
    ported in LayoutMemory.lean) from a plan the tree does not port yet (P-11), so
    the numbers cannot be recomputed here and are transcribed instead. What makes
    the transcription evidence rather than a copy is constants_memoryMatches_ok:
    the seven fixed low-memory pointers and the scalar-inversion anchor are
    checked against Layout.lean's OWN ported constants and against MEM:1039's
    rule, i.e. against a channel the artifact does not control. The slots no
    deployed partial renders (quotientTmp/quotientStack/pcs scratch windows,
    comms_mptr_base) are set to their validate-legal anchors and are labelled
    INERT at the gate. -/
def poseidonMemoryLayout : VerifierMemoryLayout :=
  { map := { regions := [] }
    thetaWindows := ThetaWindowLayout.compatibility
    pcs := pcsMemoryRequirementsDefault
    constructorSmokeScratchMptr := lowMemoryScratchStart
    constructorG1msmSmokeScratchMptr := 0x65e0
    constructorG1msmSmokeInputBytes := 0x1d60
    transcriptMptr := transcriptBufferStart
    pcsPairingScratchMptr := pcsPairingScratchStart
    verifierReturnMptr := verifierReturnBufferStart
    quotientReturnMptr := quotientReturnBufferStart
    vkMptr := ptrMemory (valueFromNat 0x2900)
    scalarInvScratchMptr := 0x2900 - modexpScratchBytes
    challengeMptr := ptrMemory (valueFromNat 0x3ae0)
    thetaMptr := ptrMemory (valueFromNat 0x3ae0)
    betaMptr := ptrMemory (valueFromNat 0x3b00)
    gammaMptr := ptrMemory (valueFromNat 0x3b20)
    trashChallengeMptr := ptrMemory (valueFromNat 0x3b40)
    yMptr := ptrMemory (valueFromNat 0x3b60)
    xMptr := ptrMemory (valueFromNat 0x3b80)
    x1Mptr := ptrMemory (valueFromNat 0x3ba0)
    x2Mptr := ptrMemory (valueFromNat 0x3bc0)
    x3Mptr := ptrMemory (valueFromNat 0x3be0)
    x4Mptr := ptrMemory (valueFromNat 0x3c00)
    fComMptr := ptrMemory (valueFromNat 0x3c20)
    piMptr := ptrMemory (valueFromNat 0x3ca0)
    accLhsMptr := ptrMemory (valueFromNat 0x3d20)
    accRhsMptr := ptrMemory (valueFromNat 0x3da0)
    xNMptr := ptrMemory (valueFromNat 0x3e20)
    xNMinus1InvMptr := ptrMemory (valueFromNat 0x3e40)
    lLastMptr := ptrMemory (valueFromNat 0x3e60)
    lBlindMptr := ptrMemory (valueFromNat 0x3e80)
    l0Mptr := ptrMemory (valueFromNat 0x3ea0)
    instanceEvalMptr := ptrMemory (valueFromNat 0x3ec0)
    quotientEvalMptr := ptrMemory (valueFromNat 0x3ee0)
    quotientMptr := ptrMemory (valueFromNat 0x3f00)
    fEvalMptr := ptrMemory (valueFromNat 0x3fa0)
    vMptr := ptrMemory (valueFromNat 0x3fc0)
    finalComMptr := ptrMemory (valueFromNat 0x3fe0)
    pairingLhsMptr := ptrMemory (valueFromNat 0x4060)
    pairingRhsMptr := ptrMemory (valueFromNat 0x40e0)
    rotPointsMptr := ptrMemory (valueFromNat 0x4160)
    x1PowersMptr := ptrMemory (valueFromNat 0x44e0)
    qComMptr := ptrMemory (valueFromNat 0x4d00)
    qEvalSetMptr := ptrMemory (valueFromNat 0x4d00)
    qEvalCptrMptr := ptrMemory (valueFromNat 0x5400)
    g1IdentityMptr := ptrMemory (valueFromNat 0x5500)
    reversedEvalsMptr := ptrMemory (valueFromNat 0x5660)
    commsMptrBase := ptrMemory (valueFromNat 0x5c60)
    adviceCommsMptrBase := ptrMemory (valueFromNat 0x5c60)
    lookupMCommsMptrBase := ptrMemory (valueFromNat 0x6060)
    permZCommsMptrBase := ptrMemory (valueFromNat 0x60e0)
    lookupHelperCommsMptrBase := ptrMemory (valueFromNat 0x6260)
    lookupZCommsMptrBase := ptrMemory (valueFromNat 0x62e0)
    trashcanCommsMptrBase := ptrMemory (valueFromNat 0x6360)
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0x63e0)
    selectorAccMptr := 0x65e0
    batchInvertScratchMptr := 0x65e0
    lagrangeDenomsMptr := 0x67c0
    quotientTmpMptr := lowMemoryScratchStart
    quotientStackMptr := lowMemoryScratchStart
    quotientStackHi := lowMemoryScratchStart
    pcsQEvalSourceTableMptr := lowMemoryScratchStart
    pcsQComTraceScratchMptr := lowMemoryScratchStart
    pcsFinalMsmScratchMptr := lowMemoryScratchStart
    accMsmScratch := lowMemoryScratchStart
    accumulatorPairingBatchMptr := accumulatorPairingBatchPtr
    finalPairingScratchMptr := finalPairingScratchStart
    traceU256Mptr := 0x83c0 }
/-- The poseidon fixture profile: the configuration the tracked dump was generated
    with. templateConstants is Lean's own port of the Rust defaults and
    finalPairingScratchMptr / accumulatorPairingBatchMptr are Lean's own port of
    the memory layout (Layout.lean:740, :748), so those numbers reach the render
    through a channel the artifact does not control; scalarInvScratchMptr is
    derived from vkMptr by Layout.lean:1050's rule. The rest are profile inputs,
    and poseidonCtx_derivedFromArtifact_ok re-reads every one of them out of the
    dump's own lines so the byte gates are not self-fulfilling. -/
def poseidonCtx : PartialCtx := {
  templateConstants := templateConstantsDefault
  vkMptr := 0x2900
  scalarInvScratchMptr := 0x2900 - modexpScratchBytes
  finalPairingScratchMptr := finalPairingScratchStart
  accumulatorPairingBatchMptr := accumulatorPairingBatchPtr
  trace := false
  gasCheckpoints := false
  quotientProbe := false
  expectedHasAccumulator := false
  expectedHasAccumulatorWord := 0
  expectedAccOffset := 0
  expectedNumAccLimbs := 0
  expectedNumAccLimbBits := 0
  embeddedVk := none
  expectedQuotientCodehash := none
  quotientExternal := none
  quotientDirect := none
  k := 6
  numInstances := 1
  numNegLagranges := 9
  numQuotients := 4
  proofLen := 0x10e0
  simpleSelectorCols := [0, 1, 2, 3]
  fixedCommMptr := 0x4000
  -- P-13b. One advice phase of 8 G1s and NO user challenges: the dump renders
  -- the phase loop (D:1275) and then goes straight to theta, with no
  -- "User-phase challenge" line anywhere. challenge_offset is the running sum of
  -- the earlier phases' challenge counts (ART:168), so 0 for the first phase.
  userPhases := [{ adviceBytes := 0x400, numChallenges := 0, challengeOffset := 0 }]
  proofLayout := poseidonProofLayout
  numLookups := 1
  numPermutationZs := 3
  lookupHPlusAcc := 2
  numTrashcans := 1
  truncatedChallenges := true
  proofCommitTraceBase := 10000
  proofEvalTraceBase := 20000
  -- No accumulator at all in this profile, so ART:245's unwrap_or gives false for
  -- both of these and [] for the tail.
  expectedAccHasCarriedScalars := false
  accFixedBases := []
  accMsmScratch := 0
  -- P-13c. The inert defaults that keep poseidonCtx a complete record; the deployed
  -- quotient profile lives in quotientCtx, which extends this one.
  quotientProgram := none
  quotientInlineComputations := []
  quotientEvalNumerComputations := []
  quotientPostVmComputations := []
  quotientNativePermutationComputation := []
  quotientNativeLookupComputation := []
  quotientNativeIdentityComputations := []
  quotientIdentityTraceBase := 0
  quotientPow5Helper := false
  quotientLimb7Helper := false
  quotientWideLimb7Helper := false
  limb7YulCoeffs := []
  wideLimb7YulCoeffs := []
  frDelta := ""
  -- P-13e. The deployed memory layout, the VK header offsets and the Constants.sol
  -- inputs. Every number is transcribed from the artifact's own constant block and
  -- re-read by constants_memoryMatches_ok; the header offsets and the template
  -- constants come from Lean's own ports of the Rust, not from the dump.
  memory := poseidonMemoryLayout
  vkHeader := vkHeaderTemplateSlotsDefault
  vkLen := 4576
  expectedVkCodehash := some 0x233a1a8063ef1a9bfd30983d3034d3d90ab75ff6ac95c0e72d770bf08dcff51b
  buildId := 0xf352d2670376fa01229e35428d69c1d623c4b3edf42f15a78622888a9b4285fd
  constructorG1msmSmokeGas := 337836
  constructorG1msmSmokeInputBytes := 0x1d60
  accRhsMsmGas := 0
  expectedQuotientLen := none
  proofCptr := ptrCalldata (valueFromNat 0x64)
  numInstanceCptr := 0x1144
  instanceCptr := 0x1164
  selectorTraceBase := 27
}


/-! ## The five render functions

One Lean function per template, as PLAN section 8 requires. Each is a structural
transcription of the Askama source: every if is an if, every match is a match,
every hex interpolation is hexFilter, and the text between tags is the template's
own bytes. They were generated from the template files by a one-pass node walk
(the generator is not committed; the byte-exact gates are what make the
transcription trustworthy), so a mistyped space is a red gate rather than an
invisible typo. -/

  /-- T:partials/verifier/AssemblyHelpers.yul:1-310 (310 lines at HEAD).
      Deployed render: D:627-930, 16,223 bytes, 304 lines. Control flow: one
      {% if self.trace %} at :302-309, whose else-arm the release profile takes.
      Lines :94-104 are the G1 canonicality checks P-12 used for the EXACT-decoder
      finding; hazard4_decoderRegionAgreesWithP12_ok ties them. -/
  def renderAssemblyHelpers (ctx : PartialCtx) : String :=
  "            // Revert with a 4-byte custom-error selector (P4/L-3). Writing at\n            // 0x00 is Solidity's legal scratch space and never touches the\n            // generated layout, which starts at TRANSCRIPT_MPTR.\n            function fail(sel) {\n                mstore(0x00, shl(224, sel))\n                revert(0x00, 0x04)\n            }\n\n            // Inverse of a Fr scalar via modexp(x, r-2, r). The verifier\n            // calls this only after transcript absorption is complete, so it\n            // reuses the dead transcript buffer just below VK_MPTR instead of\n            // a fixed post-VK address that can collide with live PCS scratch\n            // when the VK payload becomes smaller.\n            function scalar_inv(x) -> inv {\n                // Zero has no multiplicative inverse in Fr; callers rely on a\n                // revert here rather than a bogus modexp result. Check the\n                // full canonical range, not just the literal word 0: for any\n                // x congruent to 0 mod r (x = r, say) modexp returns 0, which\n                // downstream mulmod chains would silently absorb. Every\n                // current call site feeds addmod/mulmod output, so this only\n                // guards against a future emitter passing a raw scalar.\n                if iszero(lt(x, FR_MODULUS)) { fail(ERR_NON_CANONICAL_SCALAR) }\n                if iszero(x) { fail(ERR_NON_CANONICAL_SCALAR) }\n                let p := " ++ hexFilter (ctx.scalarInvScratchMptr) ++ "\n                // EIP-198 modexp frame:\n                //   [base_len, exp_len, mod_len, base, exponent, modulus]\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.baseLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")        // base len\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.expLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")        // exp len\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.modLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")        // mod len\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.baseOffset) ++ "), x)\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.expOffset) ++ "), sub(FR_MODULUS, 2))\n                mstore(add(p, " ++ hexFilter (ctx.templateConstants.modexp.modOffset) ++ "), FR_MODULUS)\n                if iszero(staticcall(MODEXP_GAS, " ++ hexFilter (ctx.templateConstants.modexp.address) ++ ", p, " ++ hexFilter (ctx.templateConstants.modexp.frameBytes) ++ ", p, " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ ")) { fail(ERR_PRECOMPILE_FAILED) }\n                if iszero(eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ ")) { fail(ERR_PRECOMPILE_FAILED) }\n                inv := mload(p)\n            }\n\n            // ---------- Streaming Keccak256 transcript helpers ----------\n            //\n            // The transcript buffer lives at\n            // memory[TRANSCRIPT_MPTR..buf_len). On verifier entry it starts\n            // empty. Each common(input) appends raw bytes. squeeze_*(buf_len)\n            // computes one Keccak digest, reseeds the buffer with that\n            // 32-byte digest, and samples a Fq element as\n            // uint256(digest_be) mod r.\n\n            function transcript_init() -> buf_len {\n                // Empty transcript buffer starts exactly at TRANSCRIPT_MPTR.\n                buf_len := TRANSCRIPT_MPTR\n            }\n\n            // Append one 32-byte big-endian field/transcript word at the\n            // current end of the transcript buffer.\n            function common_word(buf_len, word) -> ret {\n                mstore(buf_len, word)\n                ret := add(buf_len, 32)\n            }\n\n            // Absorb a BLS12-381 G1 point in EIP-2537 padded\n            // uncompressed form (4 calldata words = 128 bytes:\n            // x_hi || x_lo || y_hi || y_lo, each coord = 16 zero\n            // pad bytes + 48 big-endian field bytes) into the\n            // transcript buffer at `buf_len`.\n            //\n            // Matches the patched `Hashable<Keccak256> for\n            // midnight_curves::G1Projective::to_input` in\n            // midnight-proofs, which now emits the same 128-byte form\n            // (`midfall/proofs/src/transcript/implementors.rs`). The\n            // previous emitter hashed the 48-byte ZCash compressed\n            // encoding instead and ran a 384-bit `lex(y) > lex(p − y)`\n            // ladder + identity flag fixup to derive the sign bit on\n            // the fly; switching to the uncompressed form drops that\n            // ladder entirely.\n            //\n            // Canonicality: reject non-zero bytes in the top 16 bytes\n            // of each `_hi` calldata word and reject coordinates\n            // outside Fp. Normalizing those bytes before hashing would\n            // make multiple calldata encodings share one transcript.\n            //\n            // This helper does not run an independent curve/subgroup\n            // check. Instead, ProtocolPlan::validate rejects generated\n            // plans where an absorbed proof commitment would not later be\n            // consumed by an EIP-2537 G1MSM or pairing path, and those\n            // precompiles perform the curve/subgroup validation.\n            //\n            // The point's uncompressed form remains in calldata; the\n            // call site is responsible for `calldatacopy`-ing it into\n            // memory afterwards if it needs the on-curve coordinates.\n            function common_uncompressed_g1(buf_len, cptr) -> ret {\n                let x_hi_word := calldataload(cptr)\n                let x_lo := calldataload(add(cptr, 0x20))\n                let y_hi_word := calldataload(add(cptr, 0x40))\n                let y_lo := calldataload(add(cptr, 0x60))\n                if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }\n                if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }\n\n                let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)\n                let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)\n                if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {\n                    fail(ERR_BAD_POINT_ENCODING)\n                }\n                if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {\n                    fail(ERR_BAD_POINT_ENCODING)\n                }\n\n                // Memcpy the 4 calldata words (128 bytes) verbatim\n                // into the keccak buffer.\n                calldatacopy(buf_len, cptr, 0x80)\n                ret := add(buf_len, 0x80)\n            }\n\n            // One Keccak finalization + reseed. Returns the new buffer\n            // cursor (= TRANSCRIPT_MPTR + 32) and stores the squeezed Fq at\n            // `mptr`.\n            function squeeze_to(buf_len, mptr) -> ret {\n                let h0 := keccak256(TRANSCRIPT_MPTR, sub(buf_len, TRANSCRIPT_MPTR))\n                // Reseed: write the 32-byte digest at start of buffer.\n                mstore(TRANSCRIPT_MPTR, h0)\n                let r := FR_MODULUS\n                // Sample Fq as uint256(keccak_digest_be) mod r.\n                mstore(mptr, mod(h0, r))\n                ret := add(TRANSCRIPT_MPTR, 32)\n            }\n\n            // ---------- EC primitives (EIP-2537 wrappers) ----------\n            //\n            // These mirror the BN254 helpers but operate on 4-word G1\n            // points. They use planned memory windows above Solidity's\n            // reserved prefix; the streaming transcript buffer is no longer\n            // needed once all challenges are squeezed.\n\n            // Invert a contiguous run of Fr words in-place using Montgomery's\n            // batch inversion trick:\n            //   1. write prefix products to scratch;\n            //   2. invert the total product once with modexp;\n            //   3. walk backward to recover each individual inverse.\n            //\n            // The function returns a boolean instead of reverting so callers\n            // can combine it with other `success` plumbing until a section\n            // boundary decides whether to fail closed.\n            //\n            // MF-4: the second return value separates a FAILED PRECOMPILE\n            // (staticcall reverted / OOG'd / returned the wrong size -- a\n            // chain or gas-schedule fault) from a REJECTED INPUT (a zero or\n            // non-canonical denominator, which for the Lagrange batch means\n            // the squeezed x landed on a domain point). Both fail closed at\n            // the section boundary, but they are different incidents and used\n            // to surface under the same PrecompileFailed selector, pointing\n            // responders at the node when the transcript was the cause.\n            function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret, precompile_failed {\n                ret := success\n                if iszero(ret) { leave }\n                // Memory ranges must be forward and word-aligned by\n                // construction; a reversed range is always a codegen error.\n                if lt(mptr_end, mptr_start) {\n                    ret := 0\n                    leave\n                }\n\n                let count_bytes := sub(mptr_end, mptr_start)\n                // Empty batch is valid and leaves memory untouched.\n                if iszero(count_bytes) { leave }\n\n                // Fast path for a single denominator: avoid prefix scratch and\n                // just run one modexp inverse in place.\n                if eq(count_bytes, 0x20) {\n                    let x := mload(mptr_start)\n                    // Reject anything congruent to zero mod r, not just the\n                    // literal word 0: modexp would return 0 for those too, and\n                    // the caller would take it for a valid inverse.\n                    if iszero(lt(x, r)) {\n                        ret := 0\n                        leave\n                    }\n                    if iszero(x) {\n                        ret := 0\n                        leave\n                    }\n\n                    let single_scratch := scratch_mptr\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.baseLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.expLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.modLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.baseOffset) ++ "), x)\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.expOffset) ++ "), sub(r, 2))\n                    mstore(add(single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.modOffset) ++ "), r)\n                    ret := staticcall(MODEXP_GAS, " ++ hexFilter (ctx.templateConstants.modexp.address) ++ ", single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.frameBytes) ++ ", single_scratch, " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ ")\n                    ret := and(ret, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ "))\n                    precompile_failed := iszero(ret)\n                    if ret { mstore(mptr_start, mload(single_scratch)) }\n                    leave\n                }\n\n                // Forward pass: scratch stores prefix products up to, but not\n                // including, the final element. `gp` becomes the total product.\n                //\n                // Match the single-element path: reject non-canonical words\n                // (x >= r) instead of letting mulmod reduce them silently, so\n                // accept/reject semantics do not depend on batch length.\n                let gp_mptr := scratch_mptr\n                let gp := mload(mptr_start)\n                if iszero(lt(gp, r)) {\n                    ret := 0\n                    leave\n                }\n                let mptr := add(mptr_start, 0x20)\n                for {} lt(mptr, sub(mptr_end, 0x20)) {} {\n                    let x := mload(mptr)\n                    if iszero(lt(x, r)) {\n                        ret := 0\n                        leave\n                    }\n                    gp := mulmod(gp, x, r)\n                    mstore(gp_mptr, gp)\n                    mptr := add(mptr, 0x20)\n                    gp_mptr := add(gp_mptr, 0x20)\n                }\n                let x_last := mload(mptr)\n                if iszero(lt(x_last, r)) {\n                    ret := 0\n                    leave\n                }\n                gp := mulmod(gp, x_last, r)\n                // A zero total product means at least one denominator was\n                // zero, so no batch inverse exists.\n                if iszero(gp) {\n                    ret := 0\n                    leave\n                }\n\n                // Invert the total product once.\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.baseLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.expLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.modLenOffset) ++ "), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.baseOffset) ++ "), gp)\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.expOffset) ++ "), sub(r, 2))\n                mstore(add(gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.modOffset) ++ "), r)\n                ret := staticcall(MODEXP_GAS, " ++ hexFilter (ctx.templateConstants.modexp.address) ++ ", gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.frameBytes) ++ ", gp_mptr, " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ ")\n                ret := and(ret, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.modexp.outputBytes) ++ "))\n                precompile_failed := iszero(ret)\n                // Leave before the backward pass on a failed modexp. A failed\n                // staticcall writes no output, so `mload(gp_mptr)` would read\n                // back the stale frame header and the pass below would\n                // overwrite every denominator in [mptr_start, mptr_end) with\n                // garbage products before returning ret = 0.\n                if iszero(ret) { leave }\n                let all_inv := mload(gp_mptr)\n\n                // Backward pass: derive each inverse from the inverted total\n                // product and the saved prefix products.\n                let first_mptr := mptr_start\n                let second_mptr := add(first_mptr, 0x20)\n                gp_mptr := sub(gp_mptr, 0x20)\n                for {} lt(second_mptr, mptr) {} {\n                    let inv := mulmod(all_inv, mload(gp_mptr), r)\n                    all_inv := mulmod(all_inv, mload(mptr), r)\n                    mstore(mptr, inv)\n                    mptr := sub(mptr, 0x20)\n                    gp_mptr := sub(gp_mptr, 0x20)\n                }\n                let inv_first := mulmod(all_inv, mload(second_mptr), r)\n                let inv_second := mulmod(all_inv, mload(first_mptr), r)\n                mstore(first_mptr, inv_first)\n                mstore(second_mptr, inv_second)\n            }\n\n            // Final EIP-2537 pairing wrapper. `lhs_mptr` and `rhs_mptr` are\n            // 4-word G1 slots; G2 bases are loaded from the pinned VK payload.\n            function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret {\n                ret := success\n                // `leave` (not a revert) keeps the trace render able to return\n                // `false`; the terminal guard in TraceReturn.yul now reverts\n                // with ProofRejected in a production render, so no path hands\n                // control back to a caller that would report success for an\n                // unverified proof.\n                if iszero(ret) { leave }\n                // Lay out two (G1, G2) pairs at scratch..scratch+0x300:\n                //   [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)]\n                // Cancun MCOPY (3 + 3·words gas) replaces what used to\n                // be a 4-step mstore chain for each G1 (~60 gas) and an\n                // 8-iter mstore loop for each G2 (~240 gas). Net saving\n                // here is ~500 gas per ec_pairing call.\n                let scratch := " ++ hexFilter (ctx.finalPairingScratchMptr) ++ "\n                mcopy(scratch,              lhs_mptr,                 0x80)\n                mcopy(add(scratch, 0x80),   G2_BASE_MPTR,             0x100)\n                mcopy(add(scratch, 0x180),  rhs_mptr,                 0x80)\n                mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)\n                // MF-4: separate \"the chain could not run the pairing\" from\n                // \"the pairing ran and rejected this proof\". Both fail closed,\n                // but they are different incidents: the first points at the\n                // node/fork (a missing, repriced, or short-returning\n                // precompile), the second at the proof. Collapsing them into\n                // ProofRejected sent every responder looking at the wrong one.\n                                ret := staticcall(PAIRING_GAS_2PAIR, " ++ hexFilter (ctx.templateConstants.eip2537.pairingAddress) ++ ", scratch, " ++ hexFilter (ctx.templateConstants.pairingTwoPairBytes) ++ ", scratch, " ++ hexFilter (ctx.templateConstants.wordBytes) ++ ")\n                ret := and(ret, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.wordBytes) ++ "))\n                if iszero(ret) { fail(ERR_PRECOMPILE_FAILED) }\n                // Compare against 1 rather than truncating to the low bit:\n                // `and(ret, word)` would accept any odd result word. EIP-2537\n                // only ever returns 0 or 1, so this matches the strict form\n                // the constructor smoke test already uses.\n                ret := and(ret, eq(mload(scratch), 1))" ++
      (if ctx.trace then
       "\n                // Trace renders record the failure and return false from the\n                // verifier (see TraceReturn) so the trace logs survive.\n                ret := iszero(iszero(ret))"
       else
       "\n                if iszero(ret) { fail(ERR_PROOF_REJECTED) }\n                ret := 1") ++
      "\n            }"

  /-- T:partials/verifier/VkLoading.yul:1-141 (141 lines at HEAD). Deployed
      render: D:1103-1176, 4,494 bytes, 74 lines. Control flow: gas_checkpoints
      ifs at :1-3 and :139-141 (both zero-render in the deployed profile), the
      embedded_vk match at :22-75 (None arm taken: extcodecopy at :74), and the
      expected_has_accumulator if at :115-137 (zero-render). -/
  def renderVkLoading (ctx : PartialCtx) : String :=
  (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(1) // entry: before VK loading"
       else
       "") ++
      "\n\n            // ===============================================================\n            // VK loading: either bake in the embedded VK bytes or fetch\n            // them from the linked AUTHORIZED_VK contract.\n            //\n            // This is the first verifier phase after helper definitions. Its\n            // job is to make the generated VK payload available at VK_MPTR in\n            // one canonical memory layout, regardless of whether this render\n            // embeds the VK directly or links a separate Halo2VerifyingKey\n            // contract.\n            //\n            // Later template partials treat VK_MPTR as already populated with:\n            //   - header words: vk_digest, domain data, accumulator metadata;\n            //   - BLS12-381 base points used by the final pairing;\n            //   - compact quotient VM constants/program bytes, when enabled;\n            //   - fixed and permutation commitments in 4-word G1 slots.\n            // ===============================================================\n            {" ++
      (match ctx.embeddedVk with
       | some embedded_vk =>
        "\n                // Embedded VK render: materialize the generated payload\n                // directly into the same VK_MPTR memory layout that the\n                // external-VK path obtains via extcodecopy.\n                //\n                // Embedded mode increases verifier bytecode size but avoids an\n                // external VK deployment and proof-time extcodecopy. The\n                // generated constants below are still organized as the same VK\n                // payload words used by the separate contract.\n                // The trailing inline names identify generated payload slots." ++
        (jinjaFor embedded_vk.constants (fun (name, chunk) loop =>
          "\n                // Header/base/quotient-payload word " ++ toString (loop.index0) ++ ".\n                mstore(" ++ toString (ctx.vkMptr + loop.index0) ++ ", " ++ hexPaddedFilter 64 (chunk.toNat) ++ ") // " ++ name)) ++
        (jinjaFor embedded_vk.fixedComms (fun g1 loop =>
          "" ++
          ((fun offset =>
           "\n                // Fixed-column commitment " ++ toString (loop.index0) ++ ".\n                // Stored as EIP-2537 padded uncompressed G1:\n                //   x_hi, x_lo, y_hi, y_lo.\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0) ++ ", " ++ hexPaddedFilter 64 (g1.xHi.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 1) ++ ", " ++ hexPaddedFilter 64 (g1.xLo.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 2) ++ ", " ++ hexPaddedFilter 64 (g1.yHi.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 3) ++ ", " ++ hexPaddedFilter 64 (g1.yLo.toNat) ++ ")"
          ) embedded_vk.constants.length))) ++
        (jinjaFor embedded_vk.permutationComms (fun g1 loop =>
          "" ++
          ((fun offset =>
           "\n                // Permutation commitment " ++ toString (loop.index0) ++ ".\n                // These follow fixed commitments contiguously in the generated\n                // VK payload, also as 4-word EIP-2537 G1 slots.\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0) ++ ", " ++ hexPaddedFilter 64 (g1.xHi.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 1) ++ ", " ++ hexPaddedFilter 64 (g1.xLo.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 2) ++ ", " ++ hexPaddedFilter 64 (g1.yHi.toNat) ++ ")\n                mstore(" ++ toString (ctx.vkMptr + offset + 4 * loop.index0 + 3) ++ ", " ++ hexPaddedFilter 64 (g1.yLo.toNat) ++ ")"
          ) (embedded_vk.constants.length + 4 * embedded_vk.fixedComms.length))))
       | none =>
        "\n                // Re-check the pinned VK dependency on every proof. The\n                // constructor check catches normal deployment mistakes, while\n                // this fresh check hardens forks or same-transaction edge\n                // cases where code at the authorized address could differ\n                // from the runtime originally pinned by this verifier.\n                //\n                // EXPECTED_VK_LENGTH includes the leading INVALID byte in the\n                // Halo2VerifyingKey runtime. EXPECTED_VK_CODEHASH_WORD is the\n                // full runtime hash, not only the payload hash.\n                if iszero(and(\n                    eq(extcodesize(vk), EXPECTED_VK_LENGTH),\n                    eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)\n                )) { fail(ERR_VK_MISMATCH) }\n                // Runtime byte 0 is INVALID so direct calls cannot execute the\n                // payload. Copy from byte 1 into VK_MPTR to reconstruct the\n                // exact payload layout used by the embedded branch.\n                extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)") ++
      "\n\n                // Cross-check loaded VK header words against the verifier\n                // constants used by later parser, domain, and accumulator\n                // paths. Codehash pinning protects the external VK address;\n                // these checks catch generator drift before calldata parsing\n                // chooses a stale schema.\n                success := and(success, eq(mload(NUM_INSTANCES_MPTR), " ++ toString (ctx.numInstances) ++ "))\n                success := and(success, eq(mload(K_MPTR), " ++ toString (ctx.k) ++ "))\n                success := and(success, eq(mload(HAS_ACCUMULATOR_MPTR), " ++ toString (ctx.expectedHasAccumulatorWord) ++ "))\n                success := and(success, eq(mload(ACC_OFFSET_MPTR), " ++ toString (ctx.expectedAccOffset) ++ "))\n                success := and(success, eq(mload(NUM_ACC_LIMBS_MPTR), " ++ toString (ctx.expectedNumAccLimbs) ++ "))\n                success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), " ++ toString (ctx.expectedNumAccLimbBits) ++ "))\n                if iszero(success) { fail(ERR_VK_MISMATCH) }\n                //\n                // The checks below validate the dynamic ABI envelope before the\n                // transcript parser starts walking raw calldata:\n                //   - proof bytes length equals the generated proof layout;\n                //   - instance array length equals the generated public input\n                //     count;\n                //   - total calldata length has no missing or trailing words.\n                //\n                // `success` is folded through `and` for consistency with later\n                // sections, then immediately enforced at the end of this block.\n                // A failure here means the verifier is not looking at the proof\n                // shape it was generated to parse.\n                success := and(success, eq(" ++ hexFilter (ctx.proofLen) ++ ", calldataload(PROOF_LEN_CPTR)))\n                success := and(success, eq(" ++ toString (ctx.numInstances) ++ ", calldataload(NUM_INSTANCE_CPTR)))\n                // Calldata must contain exactly the ABI selector, proof bytes,\n                // instance-array length, and generated number of instance\n                // words. Any trailing bytes fail closed.\n                success := and(\n                    success,\n                    eq(calldatasize(), add(INSTANCE_CPTR, " ++ hexFilter ((ctx.numInstances * 32)) ++ "))\n                )\n                // Stop before any transcript absorption if the ABI/proof shape\n                // is not exactly the generated one.\n                if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }\n            }" ++
      (if ctx.expectedHasAccumulator then
       "\n            // Fail malformed accumulator public inputs before transcript,\n            // quotient, PCS, and final pairing work. The late accumulator block\n            // only batches these already-validated G1 outputs into the final\n            // pairing equation.\n            //\n            // Accumulator validation decodes shifted public-input limbs into\n            // EIP-2537 G1 slots, checks canonical encodings, and routes points\n            // through G1MSM for curve/subgroup validation. Doing it here means\n            // invalid accumulator public inputs cannot influence transcript\n            // challenge derivation or waste gas in later quotient/PCS work.\n            // validate_public_accumulator returns a boolean to share the same\n            // success-plumbing style as other helper calls; this boundary is\n            // where the verifier converts failure to a revert.\n            let acc_precompile_failed := 0\n            success, acc_precompile_failed := validate_public_accumulator(success, r)\n            if iszero(success) {\n                // MF-4: a G1MSM that could not run at all is a chain fault,\n                // not a malformed accumulator point.\n                if acc_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }\n                fail(ERR_BAD_POINT_ENCODING)\n            }"
       else
       "") ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(2) // after VK loading + accumulator public-input precheck"
       else
       "")

  /-- T:partials/verifier/Lagrange.yul:1-99 (99 lines at HEAD). Deployed render:
      D:1497-1586, 4,742 bytes, 90 lines. Control flow: the num_instances == 0
      if at :25-29 (zero-render: the fixture has one instance) and the
      gas_checkpoints if at :89-91. -/
  def renderLagrange (ctx : PartialCtx) : String :=
  "            // ===============================================================\n            // Lagrange & instance-evaluation block (pure Fr arithmetic).\n            // ===============================================================\n            // MF-4: hoisted so the section boundary below can tell a failed\n            // modexp (chain fault) from a rejected denominator (x landed on a\n            // domain point) instead of reporting both as PrecompileFailed.\n            let lagrange_precompile_failed := 0\n            {\n                let k := " ++ toString (ctx.k) ++ "\n                let x := mload(X_MPTR)\n                // Compute x^n by repeated squaring, with n = 2^k.\n                let x_n := x\n                for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {\n                    x_n := mulmod(x_n, x_n, r)\n                }\n\n                let omega := mload(OMEGA_MPTR)\n\n                // First pass writes denominators (x - omega_i) for every\n                // Lagrange value needed below, then appends x^n - 1. The\n                // batch inversion pass turns all of them into inverses in one\n                // modexp call.\n                let mptr := LAGRANGE_DENOMS_MPTR\n                let mptr_end := add(mptr, " ++ hexFilter (((ctx.numInstances + ctx.numNegLagranges) * 32)) ++ ")" ++
      (if ctx.numInstances == 0 then
       "\n                // No public instances still need one denominator slot so\n                // L_0 can be recovered for boundary identities.\n                mptr_end := add(mptr_end, 0x20)"
       else
       "") ++
      "\n                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }\n                    lt(mptr, mptr_end)\n                    { mptr := add(mptr, 0x20) } {\n                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))\n                    pow_of_omega := mulmod(pow_of_omega, omega, r)\n                }\n                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)\n                mstore(mptr_end, x_n_minus_1)\n                success, lagrange_precompile_failed := batch_invert(success, LAGRANGE_DENOMS_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)\n\n                // Convert inverted denominators into Lagrange evaluations:\n                // L_i(x) = (x^n - 1) * n^-1 * omega_i / (x - omega_i).\n                mptr := LAGRANGE_DENOMS_MPTR\n                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)\n                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }\n                    lt(mptr, mptr_end)\n                    { mptr := add(mptr, 0x20) } {\n                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))\n                    pow_of_omega := mulmod(pow_of_omega, omega, r)\n                }\n\n                // l_blind is the sum of the negative-rotation Lagrange terms\n                // used by the midnight-proofs blinding identity.\n                let l_blind := mload(add(LAGRANGE_DENOMS_MPTR, 0x20))\n                let l_i_cptr := add(LAGRANGE_DENOMS_MPTR, 0x40)\n                for { let l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, " ++ hexFilter ((ctx.numNegLagranges * 32)) ++ ") }\n                    lt(l_i_cptr, l_i_cptr_end)\n                    { l_i_cptr := add(l_i_cptr, 0x20) } {\n                    l_blind := addmod(l_blind, mload(l_i_cptr), r)\n                }\n\n                // Public instance polynomial evaluation at x. Instance words\n                // have already been range-checked and absorbed in transcript\n                // order; this loop only forms the linear combination.\n                let instance_eval := 0\n                for {\n                        let instance_cptr := INSTANCE_CPTR\n                        let instance_cptr_end := add(instance_cptr, " ++ hexFilter ((ctx.numInstances * 32)) ++ ")\n                    }\n                    lt(instance_cptr, instance_cptr_end)\n                    { instance_cptr := add(instance_cptr, 0x20)\n                      l_i_cptr := add(l_i_cptr, 0x20) } {\n                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)\n                }\n\n                // Persist the derived values into named memory slots consumed\n                // by quotient reconstruction and PCS preparation.\n                let x_n_minus_1_inv := mload(mptr_end)\n                let l_last := mload(LAGRANGE_DENOMS_MPTR)\n                let l_0 := mload(add(LAGRANGE_DENOMS_MPTR, " ++ hexFilter ((ctx.numNegLagranges * 32)) ++ "))\n\n                mstore(X_N_MPTR, x_n)\n                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)\n                mstore(L_LAST_MPTR, l_last)\n                mstore(L_BLIND_MPTR, l_blind)\n                mstore(L_0_MPTR, l_0)\n                mstore(INSTANCE_EVAL_MPTR, instance_eval)\n            }" ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(11) // after Lagrange + instance evaluation block"
       else
       "") ++
      "\n\n            if iszero(success) {\n                // A zero or non-canonical denominator is a rejected input,\n                // not a broken chain: the only way to reach it is a squeezed\n                // x that coincides with a domain point (probability ~n/r).\n                if lagrange_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }\n                fail(ERR_PROOF_REJECTED)\n            }"

  /-- T:partials/verifier/QuotientAndLinearization.yul:1-165 (165 lines at
      HEAD). The deployed arm is the outer match :1-62 -> None, inner match
      :53-61 -> None, so the partial emits ONLY the two quotient_numerator
      includes at :59-60 (P-13c's, passed in as arguments) followed by the
      linearization block: D:2539-2580, 1,898 bytes, 42 lines. Untaken arms:
      external quotient :3-51, direct :54-57, probe :64-82, trace :129-161,
      gas checkpoints :84-86 and :163-165. -/
  def renderQuotientAndLinearization (ctx : PartialCtx) (quotientHelpers : String) (quotientNumeratorBlock : String) : String :=
  (match ctx.quotientExternal with
       | some qext =>
        "\n            // ===============================================================\n            // External batched identity numerator reconstruction.\n            //\n            // The quotient evaluator receives the verifier memory image from\n            // QUOTIENT_FRAME_BASE..+QUOTIENT_FRAME_LEN, reconstructs the same\n            // y-batched numerator, and returns:\n            //   word 0: magic/version\n            //   word 1: linearization expected eval\n            //   word 2..: simple-selector accumulators\n            // ===============================================================\n            {\n                let q_out := QUOTIENT_RETURN_MPTR" ++
        (match ctx.expectedQuotientCodehash with
         | some _ =>
          "\n                // The quotient evaluator is as correctness-critical as the VK:\n                // it reconstructs the y-batched identity numerator and\n                // selector buckets. Re-check the pinned runtime before every\n                // external call, mirroring the VK freshness guard above.\n                if iszero(and(\n                    eq(extcodesize(quotientEvaluator), EXPECTED_QUOTIENT_LENGTH),\n                    eq(extcodehash(quotientEvaluator), EXPECTED_QUOTIENT_CODEHASH_WORD)\n                )) { fail(ERR_VK_MISMATCH) }"
         | none =>
          "") ++
        (if ctx.trace then
         "\n                if iszero(call(gas(), quotientEvaluator, 0, " ++ hexFilter (qext.frameBase) ++ ", " ++ hexFilter (qext.frameLen) ++ ", q_out, " ++ hexFilter (qext.outputLen) ++ ")) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }"
         else
         "\n                // gas() forwarding is deliberate here, unlike the precompile\n                // call sites: this is a regular contract call, so a reverting\n                // or failing callee refunds its unused gas -- only precompile\n                // ERRORS burn everything forwarded (EIP-2537). The callee is\n                // also pinned by codehash above, not attacker-supplied.\n                if iszero(staticcall(gas(), quotientEvaluator, " ++ hexFilter (qext.frameBase) ++ ", " ++ hexFilter (qext.frameLen) ++ ", q_out, " ++ hexFilter (qext.outputLen) ++ ")) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }") ++
        "\n                if iszero(eq(returndatasize(), " ++ hexFilter (qext.outputLen) ++ ")) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }\n                if iszero(eq(mload(q_out), " ++ hexPaddedFilter 64 (qext.magic) ++ ")) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }\n                // Word 1 is the negated y-batched identity numerator, stored\n                // in the same memory slot used by the monolithic path.\n                mstore(QUOTIENT_EVAL_MPTR, mload(add(q_out, 0x20)))" ++
        (if 0 < ctx.simpleSelectorCols.length then
         "\n                // Remaining return words are selector linearization buckets.\n                // Copy them back into the canonical selector accumulator region\n                // so the PCS code path is identical for split and monolithic\n                // quotient renders.\n                for { let q_i := 0 } lt(q_i, " ++ toString (ctx.simpleSelectorCols.length) ++ ") { q_i := add(q_i, 1) } {\n                    mstore(add(SELECTOR_ACC_MPTR, shl(5, q_i)), mload(add(q_out, add(0x40, shl(5, q_i)))))\n                }"
         else
         "") ++
        "\n            }"
       | none =>
        (match ctx.quotientDirect with
         | some qdirect =>
          (jinjaFor qdirect.block (fun line _loop =>
            "\n            " ++ line))
         | none =>
          quotientHelpers ++
          quotientNumeratorBlock)) ++
      (if ctx.quotientProbe then
       "\n            // ===============================================================\n            // TEST-ONLY QUOTIENT PROBE (SolidityGenerator::render_quotient_probe;\n            // never produced by `render`). Returns the quotient section's\n            // outputs instead of verifying the proof:\n            //   word 0      expected_eval (QUOTIENT_EVAL_MPTR)\n            //   word 1 + s  selector accumulator s (SELECTOR_ACC_MPTR + 32 s)\n            // The output is staged at 0x80 (above Solidity's reserved words)\n            // with no stack variables, and the probe returns immediately; the\n            // selector words are moved with `mcopy` (overlap-safe).\n            // ===============================================================\n            {\n                mstore(0x80, mload(QUOTIENT_EVAL_MPTR))" ++
       (if 0 < ctx.simpleSelectorCols.length then
        "\n                mcopy(0xa0, SELECTOR_ACC_MPTR, " ++ hexFilter ((ctx.simpleSelectorCols.length * 0x20)) ++ ")"
        else
        "") ++
       "\n                return(0x80, " ++ hexFilter (((ctx.simpleSelectorCols.length + 1) * 0x20)) ++ ")\n            }"
       else
       "") ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(12) // after batched identity numerator reconstruction"
       else
       "") ++
      "\n\n            // ===============================================================\n            // Prepare linearization scalars for the final PCS MSM.\n            //\n            // The linearized commitment is\n            //   (1 - x^n) * Σ_i x_split^i * Q_i\n            // + Σ_j sel_acc_j * S_j_com,\n            // where x_split = x^(n-1). Instead of materializing that point\n            // with a standalone G1MSM here, PCS block 5 expands the\n            // linearized commitment into its quotient and selector\n            // pairs inside the already-fused final MSM.\n            //\n            // QUOTIENT_MPTR is no longer a G1 point in this path. Its first\n            // two words carry:\n            //   word 0: x_split\n            //   word 1: one_minus_x_n\n            // ===============================================================\n            {\n                let x := mload(X_MPTR)\n                let k := " ++ toString (ctx.k) ++ "\n                // Compute both x^n and x^(n-1) with the same squaring walk:\n                // x_pow_2i tracks x^(2^i), while x_pow_2i_minus1 tracks\n                // x^(2^i - 1).\n                let x_pow_2i := x\n                let x_pow_2i_minus1 := 1\n                for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {\n                    x_pow_2i_minus1 := mulmod(\n                        mulmod(x_pow_2i_minus1, x_pow_2i_minus1, r),\n                        x,\n                        r\n                    )\n                    x_pow_2i := mulmod(x_pow_2i, x_pow_2i, r)\n                }\n                let x_split := x_pow_2i_minus1\n                let one_minus_x_n := addmod(1, sub(r, x_pow_2i), r)\n\n                // PCS block 5 interprets this 2-word payload as scalar\n                // metadata, not as a materialized G1 point.\n                mstore(QUOTIENT_MPTR, x_split)\n                mstore(add(QUOTIENT_MPTR, 0x20), one_minus_x_n)\n            }" ++
      (if ctx.trace then
       "\n            // Materialize the linearization commitment for trace comparison.\n            // The production path expands the same terms directly into the\n            // fused final PCS MSM below.\n            {\n                let lin_scratch := add(SELECTOR_ACC_MPTR, " ++ hexFilter ((ctx.simpleSelectorCols.length * 0x20)) ++ ")\n                let lin_pair := lin_scratch\n                let lin_cur_scalar := mload(add(QUOTIENT_MPTR, 0x20))" ++
       (jinjaFor (List.range ctx.numQuotients) (fun _ loop =>
         "\n                // Trace-only quotient limb term: Q_i * ((1 - x^n) * x_split^i).\n                mcopy(lin_pair, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, " ++ hexFilter ((loop.index0 * 0x80)) ++ "), 0x80)\n                mstore(add(lin_pair, 0x80), lin_cur_scalar)\n                lin_pair := add(lin_pair, 0xa0)" ++
         (if ! loop.last then
          "\n                lin_cur_scalar := mulmod(lin_cur_scalar, mload(QUOTIENT_MPTR), r)"
          else
          ""))) ++
       (jinjaFor ctx.simpleSelectorCols (fun col loop =>
         "\n                // Trace-only selector term: fixed selector commitment times\n                // the generated selector accumulator bucket.\n                mcopy(lin_pair, " ++ hexFilter ((ctx.fixedCommMptr + col * 0x80)) ++ ", 0x80)\n                mstore(add(lin_pair, 0x80), mload(add(SELECTOR_ACC_MPTR, " ++ hexFilter ((loop.index0 * 0x20)) ++ ")))\n                lin_pair := add(lin_pair, 0xa0)")) ++
       "\n                let lin_trace_ok := staticcall(gas(), " ++ hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++ ", lin_scratch, " ++ hexFilter (((ctx.numQuotients + ctx.simpleSelectorCols.length) * ctx.templateConstants.g1MsmPairBytes)) ++ ", lin_scratch, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                lin_trace_ok := and(lin_trace_ok, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "))\n                if iszero(lin_trace_ok) {\n                    mstore(TRACE_U256_MPTR, 34)\n                    revert(TRACE_U256_MPTR, 0x20)\n                }\n                trace_point(34, lin_scratch)\n            }"
       else
       "") ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(13) // after linearization scalar prep"
       else
       "")

  /-- T:partials/verifier/FinalPairing.yul:1-92 (92 lines at HEAD). Deployed
      render: D:2980-3008, 1,546 bytes, 29 lines - the object of P-SE proof step
      P5. Control flow: the expected_has_accumulator if at :14-62 (ZERO-render in
      the deployed profile: the poseidon VK has no public accumulator, so the
      batched pairing block is absent and D:2980-2992 are the comment lines that
      sit outside the if), the gas_checkpoints ifs at :64-66 and :90-92
      (zero-render), and the trace if at :81-87 whose ELSE arm (:86) the release
      profile takes. With the flag flipped the acc arm adds 48 lines / 2,617
      bytes. -/
  def renderFinalPairing (ctx : PartialCtx) : String :=
  "            // Batch the prevalidated public IVC accumulator pairing equation\n            // into the final KZG pairing.\n            //\n            // We do not simply multiply the two pairing equations together:\n            // two bad equations could cancel. Instead, after all four G1\n            // pairing inputs are fixed, derive a verifier-local randomizer\n            // alpha and check:\n            //\n            //   e(kzg_rhs + alpha * acc_rhs, G2_BASE)\n            // * e(kzg_lhs + alpha * acc_lhs, NEG_S_G2_BASE) == 1\n            //\n            // If either original equation is bad, this combined equation\n            // holds for at most one alpha in Fr." ++
      (if ctx.expectedHasAccumulator then
       "\n            {\n                let batch_ptr := " ++ hexFilter (ctx.accumulatorPairingBatchMptr) ++ "\n\n                // Domain || vk_digest || KZG rhs/lhs || accumulator rhs/lhs.\n                // vk_digest makes alpha's binding to the verifying key local\n                // instead of transitive-through-the-points (audit I-7).\n                mstore(batch_ptr, " ++ ctx.templateConstants.accumulator.pairingBatchDomainTagHex ++ ")\n                mstore(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchVkDigestOffset) ++ "), mload(VK_DIGEST_MPTR))\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchRhsOffset) ++ "),  PAIRING_RHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchLhsOffset) ++ "),  PAIRING_LHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchAccRhsOffset) ++ "), ACC_RHS_MPTR,     " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchAccLhsOffset) ++ "), ACC_LHS_MPTR,     " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                // alpha is Fiat-Shamir over the fully materialized pairing\n                // inputs. Replace the negligible zero draw with one so the\n                // accumulator equation cannot be accidentally dropped.\n                let acc_pair_alpha := mod(keccak256(batch_ptr, " ++ hexFilter (ctx.templateConstants.accumulator.pairingBatchHashBytes) ++ "), r)\n                if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }\n\n                // PAIRING_RHS_MPTR += alpha * ACC_RHS_MPTR.\n                // First compute alpha * ACC_RHS with a one-pair G1MSM, then\n                // add it into the KZG RHS point.\n                mcopy(batch_ptr, ACC_RHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                mstore(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "), acc_pair_alpha)\n                if success {\n                    success := staticcall(G1MSM_GAS_1PAIR, " ++ hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1MsmPairBytes) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                    success := and(success, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "))\n                }\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "), PAIRING_RHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                if success {\n                    success := staticcall(G1ADD_GAS, " ++ hexFilter (ctx.templateConstants.eip2537.g1addAddress) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1addInputBytes) ++ ", PAIRING_RHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                    success := and(success, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "))\n                }\n\n                // PAIRING_LHS_MPTR += alpha * ACC_LHS_MPTR.\n                // Mirror the same randomized batching on the KZG LHS point.\n                mcopy(batch_ptr, ACC_LHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                mstore(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "), acc_pair_alpha)\n                if success {\n                    success := staticcall(G1MSM_GAS_1PAIR, " ++ hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1MsmPairBytes) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                    success := and(success, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "))\n                }\n                mcopy(add(batch_ptr, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "), PAIRING_LHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                if success {\n                    success := staticcall(G1ADD_GAS, " ++ hexFilter (ctx.templateConstants.eip2537.g1addAddress) ++ ", batch_ptr, " ++ hexFilter (ctx.templateConstants.g1addInputBytes) ++ ", PAIRING_LHS_MPTR, " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ ")\n                    success := and(success, eq(returndatasize(), " ++ hexFilter (ctx.templateConstants.g1Bytes) ++ "))\n                }\n            }"
       else
       "") ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(15) // after public accumulator pairing batch prep (omitted for no-accumulator VKs)"
       else
       "") ++
      "\n\n            // The Yul `ec_pairing` helper checks\n            //   e(arg0, G2_BASE) * e(arg1, NEG_S_G2_BASE) == 1\n            // i.e.  e(arg0, [1]_2) = e(arg1, [s]_2).\n            //\n            // The KZG pairing identity is\n            //   e(final_com - v*G + x3*pi, [1]_2) = e(pi, [s]_2),\n            // so arg0 must be (final_com - v*G + x3*pi) and arg1 must be\n            // pi. The PAIRING_*_MPTR slots store\n            //   PAIRING_LHS_MPTR := pi\n            //   PAIRING_RHS_MPTR := final_com - v*G + x3*pi\n            // -- the historical \"LHS\"/\"RHS\" naming follows the dual MSM\n            // accumulator (left = pi, right = combined) and *not* the\n            // pairing argument order. Pass them swapped to ec_pairing." ++
      (if ctx.trace then
       "\n            // Trace renders do not revert on a failed final check: `success`\n            // (0 or 1) is traced and returned by TraceReturn, so the logs of\n            // a rejected proof remain observable. Production renders revert."
       else
       "\n            if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }") ++
      "\n            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)" ++
      (if ctx.gasCheckpoints then
       "\n            gas_checkpoint(16) // after final ec_pairing"
       else
       "")

  /-- T:partials/verifier/TranscriptProofParser.yul:1-424 (424 lines at HEAD,
      re-measured). Deployed render: D:1178-1495, 17,136 bytes (17,140 in the artifact once the
      include's four spaces are added), 318 lines. Control
      flow: the 8 {% if self.gas_checkpoints %} sites (:71, :131, :161, :191, :232,
      :261, :292, :422) and the 12 {% if self.trace %} sites (:98, :116, :152, :182,
      :212, :223, :248, :284, :326, :346, :384, :402) all zero-render; the four shape
      guards :142 num_lookups, :172 num_permutation_zs, :195 lookup_h_plus_acc and
      :242 num_trashcans are all TRUE here, as is :355 truncated_challenges; the
      advice-phase loop :105 runs once and its inner challenge loop :123 runs zero
      times. 424 - 318 = 106 lines dropped: 56 control lines, 46 lines inside
      branches this profile does not take, and 4 blank lines absorbed by the
      leading-dash strips. :416 is the cursor check P-12's gate 22 cites, and
      :63/:319/:382 are the canonicity guards P-12's gates 19-20 count. -/
  def renderTranscriptProofParser (ctx : PartialCtx) : String :=
  "            // ===============================================================\n            // Transcript: VK digest + instances + proof.\n            //\n            // This block is the Solidity mirror of the native Midfall verifier\n            // transcript schedule. It does three jobs at once:\n            //\n            //   1. Absorb public data and proof bytes into the streaming\n            //      Keccak transcript in exactly the native order.\n            //   2. Decode/range-check proof scalars and canonical G1 calldata.\n            //   3. Copy proof commitments/evaluations into planned memory\n            //      slots consumed by Lagrange, quotient, PCS, and pairing\n            //      blocks later in the verifier.\n            //\n            // `buf_len` is a write cursor into the transcript buffer. The\n            // helper functions append bytes and return the new cursor; squeeze\n            // helpers hash memory[TRANSCRIPT_MPTR..buf_len), reseed the buffer\n            // with the digest, and write the sampled Fr challenge to memory.\n            // ===============================================================\n            let buf_len := transcript_init()\n            // VK_DIGEST_MPTR holds the digest as a BE 32-byte word (the\n            // VK contract stores it via `mstore`, which matches the\n            // Keccak Fq transcript input).\n            //\n            // This digest commits to the verifier key / constraint system\n            // before any proof material is read.\n            buf_len := common_word(buf_len, mload(VK_DIGEST_MPTR))\n\n            // Absorb committed_pi = G1Affine::identity() when the\n            // `committed-instances` feature is on in midnight-proofs.\n            // Under the patched `Hashable<Keccak256>::to_input` (see\n            // `midfall/proofs/src/transcript/implementors.rs`), the\n            // identity hashes as 128 zero bytes (EIP-2537 (0,0)\n            // convention), NOT the 48-byte ZCash compressed form\n            // 0xc0||47*0x00 that the previous emitter produced.\n            // Native verifier absorbs this BEFORE the instance count.\n            {\n                // 128 zero bytes: zero out 4 consecutive 32-byte words\n                // at buf_len.\n                // This is a raw transcript absorb, not a memory slot kept for\n                // later elliptic-curve operations.\n                mstore(buf_len, 0)\n                mstore(add(buf_len, 0x20), 0)\n                mstore(add(buf_len, 0x40), 0)\n                mstore(add(buf_len, 0x60), 0)\n                buf_len := add(buf_len, 0x80)\n            }\n\n            {\n                // Native verifier absorbs a length scalar before instance\n                // values; Keccak Fq transcript input is canonical BE.\n                // The ABI length was already checked against this generated\n                // constant in VkLoading.yul.\n                buf_len := common_word(buf_len, " ++
        toString ctx.numInstances ++
        ")\n\n                let instance_cptr := INSTANCE_CPTR\n                for { let instance_cptr_end := add(instance_cptr, " ++
        hexFilter (ctx.numInstances * 32) ++
        ") }\n                    lt(instance_cptr, instance_cptr_end)\n                    { instance_cptr := add(instance_cptr, 0x20) } {\n                    let inst_be := calldataload(instance_cptr)\n                    // Public inputs are BLS12-381 scalar-field elements. They\n                    // must be canonical before transcript absorption; accepting\n                    // non-canonical encodings would admit transcript aliases.\n                    success := and(success, lt(inst_be, r))\n                    // Instances are passed BE in calldata, matching the\n                    // Keccak Fq transcript input.\n                    buf_len := common_word(buf_len, inst_be)\n                }\n                if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }\n            }" ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(3) // after VK digest + committed_pi + instance absorbs"
         else
         "") ++
        "\n\n            // ===============================================================\n            // Per-user-phase reads + challenge squeezes.\n            //\n            // Each proof G1 is already EIP-2537 padded in calldata. The\n            // verifier validates and absorbs that 128-byte form, then copies\n            // it into the corresponding per-category MPTR. The PCS /\n            // quotient-fold blocks below dereference those MPTRs.\n            //\n            // All G1 reads follow the same pattern:\n            //   - common_uncompressed_g1 canonicalizes/range-checks the two Fp\n            //     coordinates and appends the exact 128 calldata bytes;\n            //   - calldatacopy stores the same 4-word G1 slot in planned\n            //     memory for later EIP-2537 precompile calls;\n            //   - proof_cptr advances by one G1 byte length.\n            // ===============================================================\n            // proof_cptr walks the raw proof bytes inside the ABI `bytes`\n            // payload. Every successful read advances it exactly once, and the\n            // final equality check below proves the parser consumed the whole\n            // generated proof layout.\n            let proof_cptr := PROOF_CPTR\n            // advice_walk mirrors proof commitment order into the contiguous\n            // G1 commitment memory region used by PCS and quotient folding.\n            let advice_walk := ADVICE_COMMS_MPTR_BASE" ++
        (if ctx.trace then
         "\n            // Trace IDs are monotonic across all commitments/evaluations in\n            // transcript order, matching the Rust trace comparison harness.\n            let proof_commit_trace_id := " ++
         toString ctx.proofCommitTraceBase ++
         "\n            let proof_eval_trace_id := " ++
         toString ctx.proofEvalTraceBase
         else
         "") ++
        (jinjaFor ctx.userPhases (fun phase loop =>
          "\n            // ---- User phase " ++
          toString loop.index ++
          " ----\n            // Advice commitments for this phase are absorbed before the phase's\n            // challenge squeezes. The number of commitments and challenges is\n            // generated from the protocol plan.\n            for { let end := add(proof_cptr, " ++
          hexFilter phase.adviceBytes ++
          ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                // Store the commitment at its phase-ordered advice slot.\n                calldatacopy(advice_walk, proof_cptr, " ++
          hexFilter (ctx.templateConstants.g1Bytes) ++
          ")" ++
          (if ctx.trace then
           "\n                trace_point(proof_commit_trace_id, advice_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
           else
           "") ++
          "\n                advice_walk := add(advice_walk, " ++
          hexFilter (ctx.templateConstants.g1Bytes) ++
          ")\n                proof_cptr := add(proof_cptr, " ++
          hexFilter (ctx.templateConstants.g1Bytes) ++
          ")\n            }" ++
          (jinjaFor (List.range phase.numChallenges) (fun j loop =>
            "\n            // User-phase challenge " ++
            toString j ++
            " for phase " ++
            toString loop.index ++
            ". The\n            // challenge slots are contiguous under CHALLENGE_MPTR, but each\n            // phase owns a generated offset.\n            buf_len := squeeze_to(buf_len, add(CHALLENGE_MPTR, " ++
            hexFilter ((phase.challengeOffset + j) * 32) ++
            "))")))) ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(4) // after user-phase advice reads + user challenge squeezes"
         else
         "") ++
        "\n\n            // ---- theta ----\n            // From this point onward the transcript alternates between\n            // squeezed challenges and proof commitments exactly as\n            // midnight-proofs does in `plonk/verifier.rs`.\n            // theta batches lookup input expressions.\n            buf_len := squeeze_to(buf_len, THETA_MPTR)" ++
        (if ctx.numLookups != 0 then
         "\n            // ---- multiplicities (one G1 per lookup) ----\n            // Lookup multiplicity commitments are absorbed after theta and\n            // copied into their own contiguous G1 region.\n            let lookup_m_walk := LOOKUP_M_COMMS_MPTR_BASE\n            for { let end := add(proof_cptr, " ++
         hexFilter (ctx.proofLayout.lookupMultiplicities.byteLen) ++
         ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                calldatacopy(lookup_m_walk, proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")" ++
         (if ctx.trace then
          "\n                trace_point(proof_commit_trace_id, lookup_m_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
          else
          "") ++
         "\n                lookup_m_walk := add(lookup_m_walk, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n                proof_cptr := add(proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n            }"
         else
         "") ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(5) // after theta squeeze + lookup multiplicities"
         else
         "") ++
        "\n\n            // ---- beta, gamma ----\n            // beta and gamma are the permutation/lookup randomizers. They are\n            // squeezed after lookup multiplicities and before permutation\n            // product commitments, matching the native verifier schedule.\n            buf_len := squeeze_to(buf_len, BETA_MPTR)\n            buf_len := squeeze_to(buf_len, GAMMA_MPTR)" ++
        (if ctx.numPermutationZs != 0 then
         "\n            // ---- permutation Z products ----\n            // Permutation product commitments are used by the permutation\n            // identities in the quotient numerator and later by PCS openings.\n            let perm_z_walk := PERM_Z_COMMS_MPTR_BASE\n            for { let end := add(proof_cptr, " ++
         hexFilter (ctx.proofLayout.permutationProducts.byteLen) ++
         ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                calldatacopy(perm_z_walk, proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")" ++
         (if ctx.trace then
          "\n                trace_point(proof_commit_trace_id, perm_z_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
          else
          "") ++
         "\n                perm_z_walk := add(perm_z_walk, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n                proof_cptr := add(proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n            }"
         else
         "") ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(6) // after beta/gamma + permutation Z products"
         else
         "") ++
        (if ctx.lookupHPlusAcc != 0 then
         "\n            // ---- lookup helpers + accumulators (per-lookup) ----\n            // Each lookup contributes zero or more helper commitments followed\n            // by its lookup accumulator Z commitment. The generated layout keeps\n            // helper commitments and accumulator commitments in separate memory\n            // regions because the quotient/PCS schedules address them\n            // differently.\n            let lookup_helper_walk := LOOKUP_HELPER_COMMS_MPTR_BASE\n            let lookup_z_walk := LOOKUP_Z_COMMS_MPTR_BASE" ++
         (jinjaFor ctx.proofLayout.lookups (fun lookup loop =>
           "\n            // lookup " ++
           toString loop.index0 ++
           ": " ++
           toString lookup.helpers.itemCount ++
           " helper(s) + 1 acc\n            // Helper commitments for lookup " ++
           toString loop.index0 ++
           ".\n            for { let end := add(proof_cptr, " ++
           hexFilter (lookup.helpers.byteLen) ++
           ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                calldatacopy(lookup_helper_walk, proof_cptr, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")" ++
           (if ctx.trace then
            "\n                trace_point(proof_commit_trace_id, lookup_helper_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
            else
            "") ++
           "\n                lookup_helper_walk := add(lookup_helper_walk, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")\n                proof_cptr := add(proof_cptr, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")\n            }\n            // Accumulator commitment for lookup " ++
           toString loop.index0 ++
           ". This is\n            // always one G1 when the lookup section is present.\n            buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n            calldatacopy(lookup_z_walk, proof_cptr, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")" ++
           (if ctx.trace then
            "\n            trace_point(proof_commit_trace_id, lookup_z_walk)\n            proof_commit_trace_id := add(proof_commit_trace_id, 1)"
            else
            "") ++
           "\n            lookup_z_walk := add(lookup_z_walk, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")\n            proof_cptr := add(proof_cptr, " ++
           hexFilter (ctx.templateConstants.g1Bytes) ++
           ")"))
         else
         "") ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(7) // after lookup helpers + Z accumulators"
         else
         "") ++
        "\n\n            // ---- trash_challenge ----\n            // Midnight squeezes this challenge unconditionally, even when the\n            // circuit has no trash arguments.\n            // Keeping this squeeze unconditional preserves transcript\n            // compatibility across circuits with and without trash columns.\n            buf_len := squeeze_to(buf_len, TRASH_CHALLENGE_MPTR)" ++
        (if ctx.numTrashcans != 0 then
         "\n            // ---- trashcans ----\n            // Trashcan commitments are optional, but when present they are\n            // absorbed before y so the quotient batching challenge binds them.\n            let trashcan_walk := TRASHCAN_COMMS_MPTR_BASE\n            for { let end := add(proof_cptr, " ++
         hexFilter (ctx.proofLayout.trash.byteLen) ++
         ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                calldatacopy(trashcan_walk, proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")" ++
         (if ctx.trace then
          "\n                trace_point(proof_commit_trace_id, trashcan_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
          else
          "") ++
         "\n                trashcan_walk := add(trashcan_walk, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n                proof_cptr := add(proof_cptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n            }"
         else
         "") ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(8) // after trash_challenge + trashcans"
         else
         "") ++
        "\n\n            // ---- y ----\n            // y batches all quotient identities. Quotient commitments are read\n            // only after y is sampled, matching the Rust verifier flow.\n            buf_len := squeeze_to(buf_len, Y_MPTR)\n\n            // ---- quotient commitment(s) ----\n            // Each uncompressed quotient commitment is calldatacopied directly to\n            // QUOTIENT_LIMB_COMMS_MPTR_BASE; the Horner fold below reads\n            // them back from memory. common_uncompressed_g1 absorbs the\n            // 128-byte calldata form into the transcript verbatim.\n            //\n            // Multi-limb quotient mode reads several Q_i commitments; single-H\n            // mode renders this loop with one limb.\n            let quotient_walk := QUOTIENT_LIMB_COMMS_MPTR_BASE\n            for { let end := add(proof_cptr, " ++
        hexFilter (ctx.proofLayout.quotientLimbs.byteLen) ++
        ") }\n                lt(proof_cptr, end)\n                {} {\n                buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n                calldatacopy(quotient_walk, proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")" ++
        (if ctx.trace then
         "\n                trace_point(proof_commit_trace_id, quotient_walk)\n                proof_commit_trace_id := add(proof_commit_trace_id, 1)"
         else
         "") ++
        "\n                quotient_walk := add(quotient_walk, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")\n                proof_cptr := add(proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")\n            }" ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(9) // after y squeeze + quotient-limb reads"
         else
         "") ++
        "\n\n            // ---- x ----\n            // x is the main evaluation point. Values read after this point are\n            // alleged polynomial evaluations at x or derived PCS openings.\n            buf_len := squeeze_to(buf_len, X_MPTR)\n\n            // ---- evaluations ----\n            // Optimisation H3: the off-chain Solidity proof shim rewrites\n            // proof scalars into BE calldata words. Spill each decoded eval\n            // into REVERSED_EVALS_MPTR in the same iteration we range-check\n            // it, so downstream references can use cheap mload.\n            //\n            // The Rust verifier conceptually reads evaluations in query order.\n            // The lowering plan arranges REVERSED_EVALS_MPTR in the order used\n            // by the quotient VM/direct evaluator, hence the generated name.\n            {\n                let eval_buf := REVERSED_EVALS_MPTR\n                for { let end := add(proof_cptr, " ++
        hexFilter (ctx.proofLayout.evals.byteLen) ++
        ") }\n                    lt(proof_cptr, end)\n                    {} {\n                    let eval := calldataload(proof_cptr)\n                    // Proof evaluation scalars must be canonical Fr elements\n                    // before they are absorbed or made available to quotient\n                    // reconstruction.\n                    if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }\n                    // Spill for quotient numerator and PCS codegen.\n                    mstore(eval_buf, eval)\n                    eval_buf := add(eval_buf, " ++
        hexFilter (ctx.templateConstants.wordBytes) ++
        ")\n                    // Absorb the exact BE field word used by the native\n                    // Keccak transcript.\n                    buf_len := common_word(buf_len, eval)" ++
        (if ctx.trace then
         "\n                    trace_u256(proof_eval_trace_id, eval)\n                    proof_eval_trace_id := add(proof_eval_trace_id, 1)"
         else
         "") ++
        "\n                    proof_cptr := add(proof_cptr, " ++
        hexFilter (ctx.templateConstants.wordBytes) ++
        ")\n                }\n            }\n\n            // ---- x1, x2 ----\n            // x1 and x2 batch the KZG multi-opening reduction. They are\n            // squeezed after all polynomial evaluations are absorbed.\n            buf_len := squeeze_to(buf_len, X1_MPTR)\n            buf_len := squeeze_to(buf_len, X2_MPTR)\n\n            // ---- f_com (1 uncompressed G1) ----\n            // f_com is the commitment to the batched polynomial used by the PCS\n            // multi-open protocol. It is both transcript material and later\n            // pairing/MSM input.\n            buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n            calldatacopy(F_COM_MPTR, proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")" ++
        (if ctx.trace then
         "\n            trace_point(proof_commit_trace_id, F_COM_MPTR)\n            proof_commit_trace_id := add(proof_commit_trace_id, 1)"
         else
         "") ++
        "\n            proof_cptr := add(proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")\n\n            // ---- x3 ----\n            // x3 is the PCS evaluation point for f_com.\n            buf_len := squeeze_to(buf_len, X3_MPTR)" ++
        (if ctx.truncatedChallenges then
         "\n            // truncated-challenges mirrors midnight-proofs\n            // proofs/src/poly/kzg/mod.rs:\n            //   - x3 is the f_com evaluation point and is truncated\n            //     immediately after squeeze.\n            //   - x1 and x4 remain full squeezed Fr words, but later PCS\n            //     batching stores truncate(x1^i) and truncate(x4^i) while\n            //     keeping the internal power accumulators full precision.\n            // This direct x3 mask is therefore one part of the PCS truncation\n            // rule, not the only truncated value used by the verifier.\n            mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))"
         else
         "") ++
        "\n\n            // ---- q_evals (one Fq per point set) ----\n            // q_evals are not spilled into REVERSED_EVALS_MPTR because the PCS\n            // emitter reads them as a contiguous calldata range from the saved\n            // Q_EVAL_CPTR_MPTR cursor.\n            //\n            // Each q_eval is the claimed evaluation for one prepared point set\n            // in the KZG multi-open reduction. They are still transcript\n            // material and must be range-checked as Fr scalars.\n            mstore(Q_EVAL_CPTR_MPTR, proof_cptr)\n            for { let end := add(proof_cptr, " ++
        hexFilter (ctx.proofLayout.qEvals.byteLen) ++
        ") }\n                lt(proof_cptr, end)\n                {} {\n                let eval := calldataload(proof_cptr)\n                // Canonical Fr check before transcript absorption.\n                if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }\n                buf_len := common_word(buf_len, eval)" ++
        (if ctx.trace then
         "\n                trace_u256(proof_eval_trace_id, eval)\n                proof_eval_trace_id := add(proof_eval_trace_id, 1)"
         else
         "") ++
        "\n                proof_cptr := add(proof_cptr, " ++
        hexFilter (ctx.templateConstants.wordBytes) ++
        ")\n            }\n\n            // ---- x4 ----\n            // x4 is the final PCS batching challenge, sampled after q_evals\n            // and before the opening proof point pi.\n            buf_len := squeeze_to(buf_len, X4_MPTR)\n\n            // ---- pi (1 uncompressed G1) ----\n            // pi is the KZG opening proof commitment. It is the last proof\n            // object absorbed into the transcript and later becomes one side of\n            // the final pairing check.\n            buf_len := common_uncompressed_g1(buf_len, proof_cptr)\n            calldatacopy(PI_MPTR, proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")" ++
        (if ctx.trace then
         "\n            trace_point(proof_commit_trace_id, PI_MPTR)\n            proof_commit_trace_id := add(proof_commit_trace_id, 1)"
         else
         "") ++
        "\n            proof_cptr := add(proof_cptr, " ++
        hexFilter (ctx.templateConstants.g1Bytes) ++
        ")\n\n            // The hand-rolled proof parser must consume exactly the ABI\n            // `proof` bytes before the `instances` length word. This is\n            // redundant with the generated proof length today, but makes\n            // future proof-layout drift fail closed.\n            //\n            // NUM_INSTANCE_CPTR is the calldata word immediately after the\n            // dynamic proof bytes payload. If proof_cptr lands anywhere else,\n            // some section was under-read or over-read.\n            if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }\n\n            // `success` carries deferred canonicality failures from public\n            // instance reads. G1/proof scalar helpers revert immediately.\n            if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }" ++
        (if ctx.gasCheckpoints then
         "\n            gas_checkpoint(10) // after evaluations + x1/x2 + f_com + x3 + q_evals + x4 + pi (transcript done)"
         else
         "")

  /-- T:partials/verifier/AccumulatorHelpers.yul:1-372 (372 lines at HEAD,
      re-measured). Deployed render: D:932-1096, 8,962 bytes (8,966 in the artifact with the
      include's four spaces), 165 lines - and that count IS the hazard-2 finding. The four decoder helpers (:22-165) sit OUTSIDE
      the {% if self.expected_has_accumulator %} at :167, so they render for every
      profile; validate_public_accumulator (:167-372, 206 template lines) renders
      ZERO times here. So the byte gate is not vacuous, but it pins 165 of 372 lines
      and none of the accumulator-specific arms; those are gated structurally and
      against a labelled synthetic context instead. R-25: the identity-flag arm at
      :130-141 deliberately does not decode or range-check x and y, and
      accR25_identityArmIsVerbatim_ok pins that the port keeps it exactly as written. -/
  def renderAccumulatorHelpers (ctx : PartialCtx) : String :=
  "            // ---------- IVC accumulator public-input decoding ----------\n            //\n            // `AssignedForeignPoint<BLS12-381>` exposes each base-field coordinate\n            // through `AssignedField::as_public_input`: seven radix-2^56 limbs of\n            // (coord - 1) are packed four-at-a-time into native field elements.\n            // The point's identity flag follows the y coordinate as its own\n            // public-input word. Rebuild EIP-2537 padded\n            // (x_hi, x_lo, y_hi, y_lo) words from that encoding.\n            //\n            // Public-input layout for one coordinate:\n            //   word 0: limb_0 | limb_1 << bits | ... up to limbs_per_word\n            //   word 1: next limbs, if any\n            //\n            // Public-input layout for one point:\n            //   x coordinate words, y coordinate words, identity flag word\n            //\n            // The limbs are little-endian in the represented integer even\n            // though calldata words are loaded as big 256-bit values. The loop\n            // below extracts each limb by shifting inside the packed word and\n            // reconstructs the full coordinate into the two-word EIP-2537\n            // representation expected by the BLS12-381 precompiles.\n            function load_acc_coord_shifted(src, bits, n, base, limbs_per_word) -> hi, lo {\n                // Mask for one radix limb, e.g. 2^56 - 1 for the current\n                // BLS12-381 self-emulation parameters.\n                let mask := sub(base, 1)\n                for { let i := 0 } lt(i, n) { i := add(i, 1) } {\n                    // Limb words are little-endian packed inside each Fr\n                    // public input.\n                    let packed := calldataload(add(src, mul(div(i, limbs_per_word), 0x20)))\n                    // Select limb i from its packed field word. The mod/div\n                    // pair maps a limb index to an intra-word limb slot and\n                    // the calldata word containing it.\n                    let limb := and(shr(mul(mod(i, limbs_per_word), bits), packed), mask)\n\n                    let shift := mul(i, bits)\n                    // Split the reconstructed 384-bit coordinate into the\n                    // EIP-2537 high/low words expected by the precompiles.\n                    if lt(shift, 256) {\n                        lo := add(lo, shl(shift, limb))\n                        if gt(add(shift, bits), 256) {\n                            // A limb can straddle the 256-bit low/high split.\n                            // Move the overflow bits into hi.\n                            hi := add(hi, shr(sub(256, shift), limb))\n                        }\n                    }\n                    if iszero(lt(shift, 256)) {\n                        // Once shift >= 256 the whole limb belongs to hi.\n                        hi := add(hi, shl(sub(shift, 256), limb))\n                    }\n                }\n            }\n\n            // The shifted coordinate codec represents zero as p-1 before the\n            // final +1 below, so keep this sentinel explicit.\n            function is_bls_p_minus_one(hi, lo) -> yes {\n                yes := and(eq(hi, BLS_P_HI), eq(lo, BLS_P_MINUS_ONE_LO))\n            }\n\n            // Reject unused high bits in the packed public-input words. This\n            // makes each accumulator point encoding canonical before it reaches\n            // the precompile-based curve/subgroup validation.\n            function check_acc_coord_packing(src, bits, n, limbs_per_word) -> ok {\n                ok := 1\n                // Number of packed native-field public-input words occupied by\n                // one coordinate.\n                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)\n                for { let word_idx := 0 } lt(word_idx, coord_words) { word_idx := add(word_idx, 1) } {\n                    // The final word may contain fewer than limbs_per_word\n                    // limbs. Any unused high bits must be zero, otherwise the\n                    // same coordinate would have multiple calldata encodings.\n                    let remaining := sub(n, mul(word_idx, limbs_per_word))\n                    let limbs_in_word := limbs_per_word\n                    if lt(remaining, limbs_per_word) {\n                        limbs_in_word := remaining\n                    }\n                    let used_bits := mul(limbs_in_word, bits)\n                    if lt(used_bits, 256) {\n                        // shl(used_bits, 1) == 2^used_bits. The packed word\n                        // must be strictly less than that bound.\n                        ok := and(ok, lt(calldataload(add(src, mul(word_idx, 0x20))), shl(used_bits, 1)))\n                    }\n                }\n            }\n\n            // Decode one shifted coordinate of a non-identity point.\n            function load_acc_coord(src, bits, n, base, limbs_per_word) -> ok, hi, lo {\n                ok := check_acc_coord_packing(src, bits, n, limbs_per_word)\n                hi, lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word)\n                ok := and(\n                    ok,\n                    // Coordinate must be in the BLS12-381 base field, i.e.\n                    // <= p - 1 in split hi/lo form.\n                    or(lt(hi, BLS_P_HI), and(eq(hi, BLS_P_HI), iszero(gt(lo, BLS_P_MINUS_ONE_LO))))\n                )\n\n                let was_p_minus_one := is_bls_p_minus_one(hi, lo)\n                if was_p_minus_one {\n                    // Shifted encoding maps p-1 back to zero.\n                    hi := 0\n                    lo := 0\n                }\n                if iszero(was_p_minus_one) {\n                    // All other coordinates are encoded as coord - 1, so add\n                    // one back with carry into the high word.\n                    let next_lo := add(lo, 1)\n                    hi := add(hi, lt(next_lo, lo))\n                    lo := next_lo\n                }\n\n                // EIP-2537 pads each 48-byte Fp coordinate to 64 bytes,\n                // so the high word must fit in its low 128 bits.\n                // This also catches impossible reconstructions above 384 bits.\n                ok := and(ok, lt(hi, shl(128, 1)))\n            }\n\n            // Decode a public accumulator point into an EIP-2537 4-word G1\n            // slot. Non-identity points are curve/subgroup checked later by\n            // routing them through G1MSM.\n            function load_acc_point(dst, src, bits, n, base) -> ok, is_id {\n                // x and y occupy coord_words packed public-input words each;\n                // the identity flag word immediately follows y.\n                let limbs_per_word := " ++
        toString (ctx.templateConstants.accumulator.limbsPerWord) ++
        "\n                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)\n                let flag := calldataload(add(src, mul(mul(2, coord_words), 0x20)))\n                // The circuit constrains the flag as a bit. Anything else is a\n                // malformed public input rather than a non-identity point.\n                ok := lt(flag, 2)\n                is_id := eq(flag, 1)\n\n                if is_id {\n                    // When the flag is set the circuit leaves x and y\n                    // unconstrained (\"can be anything\"), so they carry no\n                    // meaning and must not be decoded or range-checked here.\n                    // The proof itself still binds whatever words were\n                    // supplied. EIP-2537 encodes G1 identity as four zero\n                    // words: x_hi = x_lo = y_hi = y_lo = 0.\n                    mstore(dst, 0)\n                    mstore(add(dst, 0x20), 0)\n                    mstore(add(dst, 0x40), 0)\n                    mstore(add(dst, 0x60), 0)\n                }\n                if iszero(is_id) {\n                    let x_ok, x_hi, x_lo := load_acc_coord(src, bits, n, base, limbs_per_word)\n                    let y_ok, y_hi, y_lo := load_acc_coord(\n                        add(src, mul(coord_words, 0x20)),\n                        bits,\n                        n,\n                        base,\n                        limbs_per_word\n                    )\n                    ok := and(ok, and(x_ok, y_ok))\n                    // The coordinate codec maps encoded p-1 to decoded\n                    // zero. EIP-2537 reserves affine (0,0) for the point at\n                    // infinity, so a decoded infinity is only valid when the\n                    // identity flag word is set.\n                    let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))\n                    ok := and(ok, iszero(decoded_zero))\n                    // Store the affine point in the exact precompile input\n                    // layout: x_hi, x_lo, y_hi, y_lo.\n                    mstore(dst, x_hi)\n                    mstore(add(dst, 0x20), x_lo)\n                    mstore(add(dst, 0x40), y_hi)\n                    mstore(add(dst, 0x60), y_lo)\n                }\n            }" ++
        (if ctx.expectedHasAccumulator then
         "\n            // Validate and prepare the public accumulator equation before the\n            // main transcript starts. This fails malformed public inputs early\n            // and writes ACC_LHS_MPTR / ACC_RHS_MPTR for final pairing batching.\n            //\n            // The accumulator public input represents an equality of two G1\n            // commitments used by the recursive KZG accumulator. This helper:\n            //   1. decodes carried public G1 points from shifted limbs;\n            //   2. forces every decoded point through EIP-2537 G1MSM so the\n            //      precompile validates curve/subgroup membership;\n            //   3. folds the RHS carried point and fixed-base scalar tail into\n            //      ACC_RHS_MPTR, leaving ACC_LHS_MPTR / ACC_RHS_MPTR ready for\n            //      randomized batching in FinalPairing.yul.\n            // `r` is consumed only by the canonicality guards in the\n            // carried-scalar and fixed-base-tail arms; renders whose\n            // accumulator layout has neither (e.g. point_pair with no tail)\n            // legally leave it unused.\n            // MF-4: `precompile_failed` separates a G1MSM staticcall that\n            // could not run (chain/gas fault) from a public-input point this\n            // verifier decoded and rejected (bad packing, out-of-field\n            // coordinate, non-canonical identity encoding, or a point the\n            // precompile found off-curve/out-of-subgroup). Both fail closed at\n            // the call site; only the second is a BadPointEncoding.\n            function validate_public_accumulator(success, r) -> out, precompile_failed {\n                out := success\n                let bits := " ++
         toString ctx.expectedNumAccLimbBits ++
         "\n                let n := " ++
         toString ctx.expectedNumAccLimbs ++
         "\n                // The BLS12-381 self-emulation currently exposes Fp\n                // coordinates as 7 radix-2^56 limbs.\n                let limb_base := shl(bits, 1)\n                let limbs_per_word := " ++
         toString (ctx.templateConstants.accumulator.limbsPerWord) ++
         "\n                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)\n                // One public point is its x and y coordinate words followed\n                // by the identity flag word.\n                let point_words := add(mul(2, coord_words), " ++
         toString (ctx.templateConstants.accumulator.identityFlagWords) ++
         ")\n                // acc_offset is generated from the VK/protocol shape and\n                // points into the ABI `instances` array.\n                let acc_instance_ptr := add(INSTANCE_CPTR, " ++
         hexFilter (ctx.expectedAccOffset * 32) ++
         ")\n\n                // LHS layout: point limbs (x,y), identity flag, then either an\n                // explicit scalar word or an implicit unit scalar for\n                // already-collapsed point-pair public inputs.\n                // The scalar pointer is computed unconditionally; the rendered\n                // branch below decides whether to read it or use scalar 1.\n                let lhs_scalar_ptr := add(acc_instance_ptr, mul(point_words, 0x20))\n                let lhs_ok, lhs_is_id := load_acc_point(ACC_LHS_MPTR, acc_instance_ptr, bits, n, limb_base)\n                out := and(out, lhs_ok)\n                // Shared scratch for one-pair LHS validation and the later\n                // variable-length RHS MSM.\n                let acc_scratch := " ++
         hexFilter ctx.accMsmScratch ++
         "\n                {" ++
         (if ctx.expectedAccHasCarriedScalars then
          "\n                    // Carried-scalar layout: the circuit exposes the scalar\n                    // that multiplies the carried LHS point.\n                    let lhs_scalar := calldataload(lhs_scalar_ptr)\n                    // Canonicality is enforced here rather than relying on the\n                    // later instance-absorption loop: G1MSM reduces scalars\n                    // mod r implicitly, so s and s+r would be indistinguishable\n                    // inside this helper.\n                    out := and(out, lt(lhs_scalar, r))"
          else
          "\n                    // Already-collapsed point-pair layout: carried scalars are\n                    // implicit one.\n                    let lhs_scalar := 1") ++
         "\n                    // Identity status is useful for decoding checks above, but\n                    // validation still goes through G1MSM for all points.\n                    pop(lhs_is_id)\n                    // Always route the decoded carried point through G1MSM,\n                    // even for identity points and zero/one scalars. The\n                    // precompile is the on-curve/subgroup validator for this\n                    // public-input point; skipping it would let a malformed\n                    // non-identity point hide behind scalar 0.\n                    mcopy(acc_scratch, ACC_LHS_MPTR, 0x80)\n                    mstore(add(acc_scratch, 0x80), lhs_scalar)\n                    if out {\n                        // Single-pair MSM output overwrites ACC_LHS_MPTR with\n                        // lhs_scalar * decoded_lhs. If lhs_scalar is one, this\n                        // is also a curve/subgroup validation round-trip.\n                        out := staticcall(G1MSM_GAS_1PAIR, " ++
         hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++
         ", acc_scratch, " ++
         hexFilter (ctx.templateConstants.g1MsmPairBytes) ++
         ", ACC_LHS_MPTR, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n                        out := and(out, eq(returndatasize(), " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         "))\n                        precompile_failed := iszero(out)\n                    }\n                }" ++
         (if ctx.accFixedBases.length == 0 then
          (if ctx.expectedAccHasCarriedScalars then
           "\n                // RHS layout for this generated verifier is fully collapsed:\n                // point limbs (x,y), identity flag, scalar. There is no\n                // fixed-base scalar tail; fixed-base contributions were\n                // already folded into ACC_RHS by the circuit/native\n                // accumulator construction."
           else
           "\n                // RHS layout for this generated verifier is an already\n                // collapsed point pair: lhs point, rhs point. Both carried\n                // scalars are implicit one, and there is no fixed-base scalar\n                // tail.")
          else
          "\n                // RHS layout for this generated verifier is partially\n                // collapsed: point limbs (x,y), identity flag, scalar, then\n                // fixed-base scalars in BTreeMap key order (`-G`, fixed_i, perm_i\n                // lexicographically by name). Each tail scalar is consumed\n                // below and appended to the RHS MSM with its generated base.") ++
         (if ctx.expectedAccHasCarriedScalars then
          "\n                let rhs_instance_ptr := add(lhs_scalar_ptr, 0x20)"
          else
          "\n                let rhs_instance_ptr := lhs_scalar_ptr") ++
         "\n                // RHS scalar, when present, immediately follows the RHS point\n                // limbs and identity flag. The fixed-base scalar tail starts\n                // after it.\n                let rhs_scalar_ptr := add(rhs_instance_ptr, mul(point_words, 0x20))\n                let rhs_ok, rhs_is_id := load_acc_point(ACC_RHS_MPTR, rhs_instance_ptr, bits, n, limb_base)\n                out := and(out, rhs_ok)\n                // acc_pair_ptr appends (G1, scalar) pairs into acc_scratch for\n                // one final RHS MSM.\n                let acc_pair_ptr := acc_scratch\n                {" ++
         (if ctx.expectedAccHasCarriedScalars then
          "\n                    // Explicit carried RHS scalar.\n                    let rhs_scalar := calldataload(rhs_scalar_ptr)\n                    out := and(out, lt(rhs_scalar, r))"
          else
          "\n                    // Implicit unit scalar for already-collapsed point pairs.\n                    let rhs_scalar := 1") ++
         "\n                    pop(rhs_is_id)\n                    // Keep the carried RHS point in the MSM input even when\n                    // it is encoded as identity or has scalar 0/1, so EIP-2537\n                    // validates every decoded public accumulator point before\n                    // it can affect, or be erased from, the pairing batch.\n                    mcopy(acc_pair_ptr, ACC_RHS_MPTR, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         ")\n                    mstore(add(acc_pair_ptr, " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         "), rhs_scalar)\n                    // Move to the next (G1, scalar) pair slot.\n                    acc_pair_ptr := add(acc_pair_ptr, " ++
         hexFilter (ctx.templateConstants.g1MsmPairBytes) ++
         ")\n                }" ++
         (if 0 < ctx.accFixedBases.length then
          (if ctx.expectedAccHasCarriedScalars then
           "\n                // Fixed-base tail starts after the explicit RHS scalar.\n                let fixed_scalar_ptr := add(rhs_scalar_ptr, 0x20)"
           else
           "\n                // Without carried scalars, the tail starts where an explicit\n                // RHS scalar would otherwise have lived.\n                let fixed_scalar_ptr := rhs_scalar_ptr") ++
          (jinjaFor ctx.accFixedBases (fun ⟨base_mptr, negate_scalar⟩ loop =>
            "\n                // Generated fixed-base scalar " ++
            toString loop.index0 ++
            ". The\n                // corresponding base point is embedded in verifier memory at\n                // " ++
            hexFilter base_mptr ++
            ".\n                let fixed_scalar_" ++
            toString loop.index0 ++
            " := calldataload(fixed_scalar_ptr)\n                // Reject non-canonical tail scalars before the negation below:\n                // for s >= r, `mod(sub(r, s), r)` is not -s mod r.\n                out := and(out, lt(fixed_scalar_" ++
            toString loop.index0 ++
            ", r))" ++
            (if negate_scalar then
             "\n                // Some accumulator bases are represented with a negated scalar\n                // so the MSM can reuse the generated positive base point.\n                fixed_scalar_" ++
             toString loop.index0 ++
             " := mod(sub(r, fixed_scalar_" ++
             toString loop.index0 ++
             "), r)"
             else
             "") ++
            "\n                if fixed_scalar_" ++
            toString loop.index0 ++
            " {\n                    // Zero scalars do not need a pair in the RHS MSM. Nonzero\n                    // tail scalars append their generated fixed base.\n                    mcopy(acc_pair_ptr, " ++
            hexFilter base_mptr ++
            ", " ++
            hexFilter (ctx.templateConstants.g1Bytes) ++
            ")\n                    mstore(add(acc_pair_ptr, " ++
            hexFilter (ctx.templateConstants.g1Bytes) ++
            "), fixed_scalar_" ++
            toString loop.index0 ++
            ")\n                    acc_pair_ptr := add(acc_pair_ptr, " ++
            hexFilter (ctx.templateConstants.g1MsmPairBytes) ++
            ")\n                }\n                // Advance to the next public tail scalar regardless of whether\n                // this one was zero and omitted from the MSM input.\n                fixed_scalar_ptr := add(fixed_scalar_ptr, 0x20)"))
          else
          "") ++
         "\n                // Total byte length of the appended RHS MSM input pairs. This\n                // is at least one pair because the carried RHS point is always\n                // appended; keep the guard for synthetic render configurations.\n                let acc_msm_len := sub(acc_pair_ptr, acc_scratch)\n                if acc_msm_len {\n                    // Fold the carried RHS point and any generated fixed-base\n                    // tail into ACC_RHS_MPTR. The later final pairing block\n                    // randomizes this equation together with the KZG pairing.\n                    if out {\n                        // Output overwrites ACC_RHS_MPTR with:\n                        //   rhs_scalar * carried_rhs\n                        // + sum_i fixed_scalar_i * fixed_base_i\n                        //\n                        // The precompile also validates every nonzero fixed\n                        // base embedded by codegen and the carried RHS point.\n                        // ACC_RHS_MSM_GAS is the compile-time worst case\n                        // (every tail scalar nonzero); acc_msm_len can only\n                        // select a same-size-or-smaller MSM at runtime.\n                        out := staticcall(\n                            ACC_RHS_MSM_GAS,\n                            " ++
         hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++
         ",\n                            acc_scratch,\n                            acc_msm_len,\n                            ACC_RHS_MPTR,\n                            " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         "\n                        )\n                        out := and(out, eq(returndatasize(), " ++
         hexFilter (ctx.templateConstants.g1Bytes) ++
         "))\n                        precompile_failed := iszero(out)\n                    }\n                }\n                // The caller checks `out` and reverts before transcript work if\n                // any decode, canonicality, or precompile validation failed.\n            }"
         else
         "")

/-- The compact quotient program of the deployed poseidon fixture. Every number is read
    off the artifact by quotientProgram_derivedFromArtifact_ok except traceIdMptr, which
    the dump cannot show (trace = false) and which is therefore DERIVED instead:
    quotient.rs:59 sets trace_id_mptr = state_mptr + WORD_BYTES, i.e. evalNumerMptr + 0x20,
    and quotientProgram_traceIdDerived_ok pins that equation. guards.constMax is the third
    case: it is num_consts - 1 (quotient.rs:252) and the single '// quotient_const' word in
    the VK dump (DVK:99) makes num_consts = 1, so constMax = 0 - pinned by
    quotientConstMax_derivedFromVkDump_ok rather than assumed. -/
def quotientDeployedProgram : QuotientProgram :=
  { len := 0x58
    opUsage := { quotientVmOpcodeUsageDefault with
      pushMemU16 := true, add := true, neg := true, foldSelector := true,
      mulConstU8 := true, addMemU16 := true, mulMemU16 := true,
      nativePermutation := true, nativeLookup := true, nativeIdentity := true }
    memUsage := quotientVmMemUsageDefault
    constMptr := 0x2ce0
    evalNumerMptr := 0x6660
    traceIdMptr := 0x6680
    selectorPowerMptr := 0x66a0
    selectorMaxPower := 21
    selectorTailUpdates :=
      [ { selectorOffset := 0x00, powerOffset := 0x02a0 }
      , { selectorOffset := 0x20, powerOffset := 0x0280 }
      , { selectorOffset := 0x40, powerOffset := 0x0220 }
      , { selectorOffset := 0x60, powerOffset := 0x0160 } ]
    stackMptr := 0x6960
    programMptr := 0x2d00
    guards := { constMax := 0, numSelectorBuckets := 4, stackLast := 0x6c60 } }

/-- The deployed profile for the two quotient_numerator partials: P-13b's poseidonCtx plus
    the 14 fields P-13c adds. The five generated-code lists are EMPTY here - they are the
    Rust emitter's output, not this template's, and quotientDeployedCtx fills them from the
    artifact at gate time rather than pasting them. -/
def quotientCtx : PartialCtx :=
  { poseidonCtx with
    quotientProgram := some quotientDeployedProgram
    quotientInlineComputations := []
    quotientEvalNumerComputations := []
    quotientPostVmComputations := []
    quotientNativePermutationComputation := []
    quotientNativeLookupComputation := []
    quotientNativeIdentityComputations := []
    quotientIdentityTraceBase := 0
    quotientPow5Helper := true
    quotientLimb7Helper := false
    quotientWideLimb7Helper := false
    limb7YulCoeffs := limb7YulCoeffsTable
    wideLimb7YulCoeffs := wideLimb7YulCoeffsTable
    frDelta := "0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7" }

/-! ### Reading the generated-code regions out of the artifact

The five for-sites over Rust-emitted Yul are the only part of these two templates whose
content this package does not own. D-P19 says a gate should read the artifact rather than
compare a pasted string, so the lists are SLICED from the dump at #eval time between anchors
that belong to the template's own fixed text. Each anchor below occurs exactly once in the
artifact (qnb_anchorsUnique_ok), so the slice is determined, not chosen. -/

def qAnchorInlineBefore : String := "// VM/native identities, so they occupy the same y-batch order."
def qAnchorInlineAfter : String := "\n\n                // VM registers:"
def qAnchorPermBefore : String := "// y-batch positions remain contiguous."
def qAnchorPermAfter : String := "\n                    }\n                    // Native lookup callback."
def qAnchorLookupBefore : String := "// as the Rust identity stream."
def qAnchorLookupAfter : String := "\n                    }\n                    // Native callbacks are generated only"
def qAnchorNiBefore : String := "switch q_native_idx"
def qAnchorNiAfter : String := "\n                        default { q_program_fail() }"
def qAnchorPostBefore : String := "// into the same numerator / selector accumulators."
def qAnchorPostAfter : String :=
  "\n                // Finish selector buckets by applying the codegen-known tail"

/-- The artifact text strictly between two anchors, each of which must occur exactly once. -/
def sliceBetween (sol before after : String) : Option String :=
  match sol.splitOn before with
  | [_, r] => match r.splitOn after with
              | [mid, _] => some mid
              | _ => none
  | _ => none

def spaces (n : Nat) : String := String.mk (List.replicate n ' ')

/-- The generated lines of one flat region: the template puts LF + ind spaces in front of
    every line interpolation, so the region text is that prefix repeated once per line. -/
def genLines (ind : Nat) (t : String) : List String :=
  let pre := "\n" ++ spaces ind
  if ! t.startsWith pre then [] else ((t.drop pre.length).toString).splitOn pre

/-- The native-identity region: 'case N {' per block, '}' closing it, and LF + 28 spaces per
    line. Unlike the flat regions the block partition is rendered, so it is recovered here. -/
def genBlocks (t : String) : List (List String) :=
  let openP := "\n" ++ spaces 24 ++ "case "
  let closeP := "\n" ++ spaces 24 ++ "}"
  let pre := "\n" ++ spaces 28
  match t.splitOn openP with
  | "" :: arms => arms.map fun a =>
      let afterKw := ((a.dropWhile (fun c => c != '{')).drop 1)
      let body := if afterKw.endsWith closeP then afterKw.dropEnd closeP.length else afterKw
      if body.startsWith pre then ((body.drop pre.length).toString).splitOn pre else []
  | _ => []

/-- The deployed ctx with the five generated-code regions filled from the artifact. None if
    any anchor is missing or duplicated, so a drifted artifact reddens the gates rather than
    silently rendering a shorter program. -/
def quotientDeployedCtx (sol : String) : Option PartialCtx := do
  let inline ← sliceBetween sol qAnchorInlineBefore qAnchorInlineAfter
  let perm ← sliceBetween sol qAnchorPermBefore qAnchorPermAfter
  let lookup ← sliceBetween sol qAnchorLookupBefore qAnchorLookupAfter
  let nident ← sliceBetween sol qAnchorNiBefore qAnchorNiAfter
  let postvm ← sliceBetween sol qAnchorPostBefore qAnchorPostAfter
  pure { quotientCtx with
    quotientInlineComputations := [genLines 16 inline]
    quotientNativePermutationComputation := genLines 24 perm
    quotientNativeLookupComputation := genLines 24 lookup
    quotientNativeIdentityComputations := genBlocks nident
    quotientPostVmComputations := [genLines 16 postvm] }

  /-- T:partials/quotient_numerator/QuotientHelpers.yul:1-81 (81 lines at HEAD). The
      deployed render is D:1588-1618 (1,621 bytes, 31 lines): the q_program_fail helper
      plus the q_pow5 block, because the profile sets quotient_pow5_helper and clears the
      other two. The two limb7 ifs and BOTH of their coefficient loops render zero times,
      so limb7YulCoeffs / wideLimb7YulCoeffs are inert here (inertFields13c_ok). The file
      ends with an endif, so the last thing it emits is the helper closing brace and
      Askama drops the file final newline - which is what makes the concatenation with
      the next include land on the following line at all. -/
  def renderQuotientHelpers (ctx : PartialCtx) : String :=
  "            // Revert with the QuotientProgramInvalid() selector\n            // (bytes4(keccak256) = 0x3cc81b89; pinned by\n            // p4_error_selectors_match_declared_errors). Defined here rather\n            // than in AssemblyHelpers.yul because the quotient VM renders in\n            // BOTH the main verifier and the standalone evaluator assembly.\n            function q_program_fail() {\n                mstore(0x00, shl(224, 0x3cc81b89))\n                revert(0x00, 0x04)\n            }\n\n            // Optional quotient helper functions. Each one is rendered only\n            // when the Rust lowering pass recognized the corresponding\n            // expression shape in this generated verifier. They are pure Fr\n            // helpers and share the same FR_MODULUS as the surrounding\n            // numerator block." ++
  (if ctx.quotientPow5Helper then
   "\n            // VK-specialized identity helper for Poseidon S-box terms.\n            //\n            // Rust source shape:\n            //   circuits/src/hash/poseidon/poseidon_chip.rs::sbox\n            //   full_round_gate / partial_round_gate\n            //   circuits/src/hash/poseidon/round_skips.rs::RoundId\n            //\n            // The Rust verifier only sees this as an Expression tree from\n            // `vk.cs.gates`; the generator emits q_pow5 after recognizing five\n            // equal multiplicative factors. It is a codegen shortcut for x^5,\n            // not a separate verifier rule.\n            function q_pow5(x) -> z {\n                let q_r := FR_MODULUS\n                let x2 := mulmod(x, x, q_r)\n                z := mulmod(x, mulmod(x2, x2, q_r), q_r)\n            }"
  else
  "") ++
  (if ctx.quotientLimb7Helper then
   "\n            // Compact evaluator for a recurring 7-limb foreign-field linear\n            // combination.\n            //\n            // Rust source shape:\n            //   circuits/src/field/foreign/params.rs::base_powers\n            //   foreign/gates/norm.rs::Foreign-field normalization\n            //   foreign/gates/mul.rs::Foreign-field multiplication\n            //\n            // This evaluates sum_i base_powers[i] * limb_i over Fr for this\n            // generated 7-limb basis. It is used for normalization and the\n            // sum_x/sum_y/sum_z pieces of multiplication.\n            function q_limb7(x0, x1, x2, x3, x4, x5, x6) -> z {\n                let q_r := FR_MODULUS" ++
   (jinjaFor ctx.limb7YulCoeffs (fun coeff loop =>
    (if loop.first then
     "\n                z := addmod(x0, mulmod(" ++
     coeff ++
     ", x" ++
     toString (loop.index) ++
     ", q_r), q_r)"
    else
    "\n                z := addmod(z, mulmod(" ++
     coeff ++
     ", x" ++
     toString (loop.index) ++
     ", q_r), q_r)"))) ++
   "\n            }"
  else
  "") ++
  (if ctx.quotientWideLimb7Helper then
   "\n            // Wide helper for the pairwise-product side of foreign-field\n            // multiplication.\n            //\n            // Rust source shape:\n            //   foreign/gates/mul.rs::Foreign-field multiplication\n            //   xys = pair_wise_prod(xs, ys)\n            //   sum_exprs(double_base_powers, xys)\n            //\n            // Native multiplication callbacks group repeated 7-term slices of\n            // the double-base product-convolution basis into q_limb7_wide.\n            function q_limb7_wide(x0, x1, x2, x3, x4, x5, x6) -> z {\n                let q_r := FR_MODULUS" ++
   (jinjaFor ctx.wideLimb7YulCoeffs (fun coeff loop =>
    (if loop.first then
     "\n                z := addmod(x0, mulmod(" ++
     coeff ++
     ", x" ++
     toString (loop.index) ++
     ", q_r), q_r)"
    else
    "\n                z := addmod(z, mulmod(" ++
     coeff ++
     ", x" ++
     toString (loop.index) ++
     ", q_r), q_r)"))) ++
   "\n            }"
  else
  "")

  /-- The five QVM-01 guard macros of T:QuotientNumeratorBlock.yul:41-55.
      Each is defined with a right-trim, so its body renders as ONE inline statement
      with no leading indent of its own; the call sites keep their own indentation in the
      surrounding text. They take program explicitly because in the template they are
      called from inside the match arm that binds it. -/
  def qConstGuard (program : QuotientProgram) (idx : String) : String :=
    "if gt(" ++
    idx ++
    ", " ++
    hexFilter (program.guards.constMax) ++
    ") { q_program_fail() }"

  def qSpillGuard (program : QuotientProgram) : String :=
    "if gt(q_sp, " ++
    hexFilter (program.guards.stackLast) ++
    ") { q_program_fail() }"

  def qPopGuard (program : QuotientProgram) : String :=
    "if eq(q_sp, " ++
    hexFilter (program.stackMptr) ++
    ") { q_program_fail() }"

  def qFoldGuard (program : QuotientProgram) : String :=
    "if iszero(and(q_has_top, eq(q_sp, " ++
    hexFilter (program.stackMptr) ++
    "))) { q_program_fail() }"

  def qNativeGuard (program : QuotientProgram) : String :=
    "if or(q_has_top, xor(q_sp, " ++
    hexFilter (program.stackMptr) ++
    ")) { q_program_fail() }"

  /-- T:partials/quotient_numerator/QuotientNumeratorBlock.yul:1-1442 (1,442 lines at
      HEAD) - the largest template in the tree. The deployed render is D:1619-2539
      (55,597 bytes, 921 lines) and takes the match arm at :134 (Some program), so the
      legacy arm at :1396-1440 - including the :1439 negation line the brief names -
      renders zero times. Of the 88 conditional sites only 68 are reached and 23 are
      true; 21 of the 31 opcode arms and all 9 token arms render zero times. The five
      generated-code for-sites contribute 528 of the 921 lines. See the P-13c gate
      header for the full exercised-region counts. -/
  def renderQuotientNumeratorBlock (ctx : PartialCtx) : String :=
  "\n            // ===============================================================\n            // Batched identity numerator / linearization target.\n            //\n            // This block does not evaluate the quotient polynomial h(x), and\n            // the proof does not provide an h(x) scalar to trust. Instead it:\n            //\n            //   1. Reconstructs the y-batched constraint numerator nu_y(x)\n            //      from the alleged polynomial evaluations read after the\n            //      transcript sampled x.\n            //   2. Stores -nu_y(x) as the expected opening scalar for the\n            //      linearized commitment.\n            //\n            // The commitment side is built in the next block from the quotient\n            // limb commitments as (1 - x^n) * Σ_i x_split^i * Q_i, plus any\n            // simple-selector commitments. The PCS check later binds that\n            // linearized commitment to this expected scalar at x.\n            //\n            // Rust source-of-truth:\n            //   - verifier.rs reads quotient commitments, samples x, then\n            //     reads/computes all evaluations used below.\n            //   - mod.rs::partially_evaluate_identities returns identities in\n            //     gate, permutation, lookup, trash order.\n            //   - linearization/verifier.rs::compute_linearization_commitment\n            //     reverse-folds those identities by powers of y, sends\n            //     simple-selector identities to selector commitment scalars,\n            //     and subtracts fully-evaluated identities into expected_eval.\n            //\n            // This template is shared by the monolithic and external quotient\n            // paths. In the external path, Halo2QuotientEvaluator first copies\n            // the verifier memory frame into the same generated addresses.\n            //\n            // Runtime inputs expected to exist before this block starts:\n            //   - `r` is the BLS12-381 scalar-field modulus.\n            //   - Y_MPTR holds the quotient batching challenge y.\n            //   - X_MPTR, L_*_MPTR, INSTANCE_EVAL_MPTR, and\n            //     REVERSED_EVALS_MPTR hold values parsed or derived by the\n            //     main verifier after the transcript sampled x.\n            //   - VK_MPTR holds the pinned VK payload; in compact mode that\n            //     payload includes the quotient constant table and bytecode.\n            //\n            // Runtime outputs written by this block:\n            //   - QUOTIENT_EVAL_MPTR receives the scalar expected opening for\n            //     the linearized commitment, namely -nu_y(x).\n            //   - SELECTOR_ACC_MPTR[0..num_simple_selectors) receives one\n            //     linearization scalar per generated simple selector.\n            //\n            // Line-by-line reading conventions used below:\n            //\n            //   * Every runtime value is one canonical Fr element stored in a\n            //     256-bit EVM memory word. The small integer operands decoded\n            //     from q_program are never field values; they are pointers,\n            //     constant-table slots, selector indexes, offsets, or counts.\n            //\n            //   * `mload(ptr)` is the only way the VM turns a small pointer\n            //     operand into a real 255-bit field element. The value loaded\n            //     from memory is then combined with `addmod(..., r)` or\n            //     `mulmod(..., r)`, so every arithmetic line is reduced modulo\n            //     the BLS12-381 scalar-field order.\n            //\n            //   * `q_top` is the cached top of the VM operand stack. When an\n            //     opcode needs to push while `q_top` is already live, the old\n            //     value is written to `q_sp` and `q_sp` is advanced by one\n            //     word. Binary `ADD`/`MUL` move `q_sp` back by one word and\n            //     combine that spilled value with `q_top`.\n            //\n            //   * Identity boundaries are explicit. Expression opcodes leave\n            //     one value in `q_top`; `FOLD_MAIN` or `FOLD_SELECTOR` consumes\n            //     it and advances the global y-batch position. Native callback\n            //     opcodes are only emitted at empty-stack boundaries and run\n            //     generated Yul that performs the same fold side effects.\n            //\n            //   * The generated Solidity source intentionally emits comments\n            //     before opcode cases. Those comments are documentation only:\n            //     they do not affect bytecode, but they make rendered verifier\n            //     assembly readable without jumping back to Rust codegen.\n            // ===============================================================\n            {" ++
  (match ctx.quotientProgram with
   | some program =>
   "\n                // Compact quotient-program mode.\n                //\n                // The largest identity expressions are not all emitted as\n                // unrolled Yul. Instead, most arithmetic is encoded as a small\n                // q_program bytecode stored in the VK payload. This block\n                // interprets that program, while selected heavy identities may\n                // still be emitted as native callbacks for gas.\n                //\n                // Compact mode is a code-size trade: short bytecode operands\n                // name already-planned memory slots, and the interpreter turns\n                // those names into Fr arithmetic. The opcode stream is fully\n                // generated and pinned by the VK/runtime codehash; no proof\n                // calldata can alter control flow.\n                // Load the quotient batching challenge used by every fold.\n                let y := mload(Y_MPTR)\n\n                // q_const_mptr points to Fr constants used by the VM.\n                // q_program_mptr points to the bytecode stream.\n                // Constants are stored as consecutive 32-byte Fr words.\n                let q_const_mptr := " ++
   hexFilter (program.constMptr) ++
   "\n                // Program bytes are also stored in the VK payload, packed into\n                // 32-byte words by PackedProgramCodec.\n                let q_program_mptr := " ++
   hexFilter (program.programMptr) ++
   "\n                // Running Horner accumulator for fully evaluated identities.\n                // After all identities, this is nu_y(x) for the `None`\n                // identity group.\n                // Initialize A = 0 before scanning the identity stream.\n                mstore(" ++
   hexFilter (program.evalNumerMptr) ++
   ", 0)" ++
   (if ctx.trace then
    "\n                // Trace builds label each emitted identity in y-batch order.\n                mstore(" ++
    hexFilter (program.traceIdMptr) ++
    ", " ++
    toString (ctx.quotientIdentityTraceBase) ++
    ")"
   else
   "") ++
   (if (ctx.simpleSelectorCols).length > 0 then
    "\n                // Simple selectors are grouped into separate linearization\n                // buckets. They start at zero for every proof.\n                // q_sel_zero_off walks selector bucket byte offsets.\n                for { let q_sel_zero_off := 0 } lt(q_sel_zero_off, " ++
    hexFilter (((ctx.simpleSelectorCols).length * 0x20)) ++
    ") { q_sel_zero_off := add(q_sel_zero_off, 0x20) } {\n                    // B_s = 0 for each simple selector bucket.\n                    mstore(add(SELECTOR_ACC_MPTR, q_sel_zero_off), 0)\n                }" ++
    (if program.selectorMaxPower > 0 then
     "\n                // Codegen knows the selector identity positions. Precompute\n                // the y^k powers needed for selector gap and tail updates,\n                // avoiding a runtime y^-1 modexp and per-identity selector\n                // scale maintenance.\n                {\n                    // q_y_power holds y^i at the current loop index.\n                    let q_y_power := 1\n                    // Start at i=1 because y^0 = 1 is implicit and never read.\n                    for { let q_y_power_i := 1 } lt(q_y_power_i, " ++
     toString (program.selectorMaxPower + 1) ++
     ") { q_y_power_i := add(q_y_power_i, 1) } {\n                        // Advance from y^(i-1) to y^i modulo Fr.\n                        q_y_power := mulmod(q_y_power, y, r)\n                        // Store y^i at selector_power_mptr + 32*i.\n                        mstore(add(" ++
     hexFilter (program.selectorPowerMptr) ++
     ", shl(5, q_y_power_i)), q_y_power)\n                    }\n                }"
    else
    "")
   else
   "") ++
   "\n\n                // Direct inline prefix. These identities are generated as Yul\n                // before entering the VM. They use the same fold snippets as\n                // VM/native identities, so they occupy the same y-batch order." ++
   (jinjaFor ctx.quotientInlineComputations (fun code_block loop =>
    (jinjaFor code_block (fun line loop =>
     "\n                " ++
     line)))) ++
   "\n\n                // VM registers:\n                //   q_pc      current bytecode pointer\n                //   q_end     end of bytecode stream\n                //   q_sp      memory stack pointer for non-top stack values\n                //   q_top     cached top-of-stack value\n                //   q_has_top whether q_top currently holds a stack value\n                //\n                // The cached top reduces memory traffic in the interpreter.\n                // q_sp's registered range must cover the interpreted operand\n                // stack plus any native callback scratch that reuses this base\n                // pointer. In particular, the native permutation callback\n                // writes a structured scratch table at program.stack_mptr.\n                // q_pc starts at the first encoded instruction.\n                let q_pc := q_program_mptr\n                // q_end is an exclusive byte pointer for the VM loop.\n                let q_end := add(q_program_mptr, " ++
   hexFilter (program.len) ++
   ")\n                // q_sp starts at the first free stack word.\n                let q_sp := " ++
   hexFilter (program.stackMptr) ++
   "\n                // q_top is meaningless until q_has_top is set.\n                let q_top := 0\n                // q_has_top = 0 means the VM stack is empty.\n                let q_has_top := 0\n\n                // q_program opcode summary. Rendered from the same\n                // program.op_usage predicates that gate the interpreter's\n                // case arms below, so this artifact documents exactly the\n                // opcodes its program can contain -- no more, no fewer." ++
   (if program.opUsage.pushConst then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushConst) ++
    " push_const"
   else
   "") ++
   (if program.opUsage.pushMemLiteral then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemLiteral) ++
    " push_mem_literal"
   else
   "") ++
   (if program.opUsage.pushMemToken then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemToken) ++
    " push_mem_token"
   else
   "") ++
   (if program.opUsage.pushMemTokenOffset then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemTokenOffset) ++
    " push_mem_token_offset"
   else
   "") ++
   (if program.opUsage.pushMemU16 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemU16) ++
    " push_mem_u16"
   else
   "") ++
   (if program.opUsage.add then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.add) ++
    " add"
   else
   "") ++
   (if program.opUsage.mul then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mul) ++
    " mul"
   else
   "") ++
   (if program.opUsage.neg then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.neg) ++
    " neg"
   else
   "") ++
   (if program.opUsage.pushConstU8 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushConstU8) ++
    " push_const_u8"
   else
   "") ++
   (if program.opUsage.foldMain then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.foldMain) ++
    " fold_main"
   else
   "") ++
   (if program.opUsage.foldSelector then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.foldSelector) ++
    " fold_selector"
   else
   "") ++
   (if program.opUsage.addConstU8 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addConstU8) ++
    " add_const_u8"
   else
   "") ++
   (if program.opUsage.mulConstU8 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulConstU8) ++
    " mul_const_u8"
   else
   "") ++
   (if program.opUsage.addConst then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addConst) ++
    " add_const"
   else
   "") ++
   (if program.opUsage.mulConst then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulConst) ++
    " mul_const"
   else
   "") ++
   (if program.opUsage.addMemU16 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMemU16) ++
    " add_mem_u16"
   else
   "") ++
   (if program.opUsage.mulMemU16 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulMemU16) ++
    " mul_mem_u16"
   else
   "") ++
   (if program.opUsage.addMulMemMemConstU8 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulMemMemConstU8) ++
    " add_mul_mem_mem_const_u8"
   else
   "") ++
   (if program.opUsage.addMulConstU8MemU16 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulConstU8MemU16) ++
    " add_mul_const_u8_mem_u16"
   else
   "") ++
   (if program.opUsage.addMulMemMem then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulMemMem) ++
    " add_mul_mem_mem"
   else
   "") ++
   (if program.opUsage.runAddMulMemMemConstU8 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.runAddMulMemMemConstU8) ++
    " run_add_mul_mem_mem_const_u8"
   else
   "") ++
   (if program.opUsage.runAddMulConstU8MemU16 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.runAddMulConstU8MemU16) ++
    " run_add_mul_const_u8_mem_u16"
   else
   "") ++
   (if program.opUsage.affineSum then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.affineSum) ++
    " affine_sum"
   else
   "") ++
   (if program.opUsage.nativePermutation then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativePermutation) ++
    " native_permutation"
   else
   "") ++
   (if program.opUsage.nativeLookup then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativeLookup) ++
    " native_lookup"
   else
   "") ++
   (if program.opUsage.nativeIdentity then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativeIdentity) ++
    " native_identity"
   else
   "") ++
   (if program.opUsage.lin7 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.lin7) ++
    " lin7"
   else
   "") ++
   (if program.opUsage.bilin7Row then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.bilin7Row) ++
    " bilin7_row"
   else
   "") ++
   (if program.opUsage.bilin7Pairwise then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.bilin7Pairwise) ++
    " bilin7_pairwise"
   else
   "") ++
   (if program.opUsage.modarith7 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.modarith7) ++
    " modarith7"
   else
   "") ++
   (if program.opUsage.pow5 then
    "\n                //   " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pow5) ++
    " pow5"
   else
   "") ++
   "\n                //\n                // The default IVC verifier uses one physical encoding for the\n                // logical VM: compact byte-oriented opcodes with variable-width\n                // operands, dynamic runs, and limb-aware cases.\n                " ++
   "\n                // Byte-oriented encoding: opcodes are one byte followed by\n                // variable-width operand bytes.\n                for { } lt(q_pc, q_end) { } {\n                    // The bytecode table is byte-addressed, but EVM memory\n                    // loads whole words. `byte(0, mload(q_pc))` extracts the\n                    // opcode at the current byte cursor; each case advances\n                    // q_pc by exactly its operand width.\n                    let q_op := byte(0, mload(q_pc))\n                    q_pc := add(q_pc, 1)\n\n                    switch q_op" ++
   (if program.opUsage.pushConst then
    "\n                    // VM 0x01 PUSH_CONST (bytes): next two bytes are a constant-table slot.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushConst) ++
    " {\n                        // Operand layout: u16 const_idx. Constants are 32-byte\n                        // Fr words, so shl(5, const_idx) converts an index to\n                        // a byte offset.\n                        let qconst := shr(240, mload(q_pc))\n                        " ++
    qConstGuard program "qconst" ++
    "\n                        // Push semantics: spill the old cached top, if any,\n                        // then install the loaded constant as the new q_top.\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(add(q_const_mptr, shl(5, qconst)))\n                        q_has_top := 1\n                        q_pc := add(q_pc, 2)\n                    }"
   else
   "") ++
   (if program.opUsage.pushMemLiteral then
    "\n                    // VM 0x02 PUSH_MEM_LITERAL (bytes): next four bytes are a memory pointer.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemLiteral) ++
    " {\n                        // Operand layout: u32 absolute memory pointer. This is\n                        // emitted only for planned addresses that do not fit in\n                        // the smaller u16 form or token map.\n                        let q_ptr := shr(224, mload(q_pc))\n                        q_pc := add(q_pc, " ++
    hexFilter (ctx.templateConstants.quotientVm.byteU32Bytes) ++
    ")\n                        // Load one canonical Fr word from generated memory and\n                        // push it through the cached-top stack discipline.\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(q_ptr)\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.pushMemToken then
    "\n                    // VM 0x03 PUSH_MEM_TOKEN (bytes): next byte selects a symbolic memory pointer.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemToken) ++
    " {\n                        // Operand layout: u8 token. Tokens cover the hot\n                        // global verifier scalars used in many identities.\n                        let q_token := byte(0, mload(q_pc))\n                        q_pc := add(q_pc, 1)\n                        let q_ptr := 0\n                        // Token cases decode generated symbolic memory addresses.\n                        switch q_token" ++
    (if program.memUsage.l0 then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.l0) ++
     " { q_ptr := L_0_MPTR }"
    else
    "") ++
    (if program.memUsage.lLast then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.lLast) ++
     " { q_ptr := L_LAST_MPTR }"
    else
    "") ++
    (if program.memUsage.lBlind then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.lBlind) ++
     " { q_ptr := L_BLIND_MPTR }"
    else
    "") ++
    (if program.memUsage.beta then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.beta) ++
     " { q_ptr := BETA_MPTR }"
    else
    "") ++
    (if program.memUsage.gamma then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.gamma) ++
     " { q_ptr := GAMMA_MPTR }"
    else
    "") ++
    (if program.memUsage.x then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.x) ++
     " { q_ptr := X_MPTR }"
    else
    "") ++
    (if program.memUsage.theta then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.theta) ++
     " { q_ptr := THETA_MPTR }"
    else
    "") ++
    (if program.memUsage.trashChallenge then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.trashChallenge) ++
     " { q_ptr := TRASH_CHALLENGE_MPTR }"
    else
    "") ++
    (if program.memUsage.instanceEval then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.instanceEval) ++
     " { q_ptr := INSTANCE_EVAL_MPTR }"
    else
    "") ++
    "\n                        // A token not advertised by the VM usage manifest is\n                        // impossible for valid generated bytecode.\n                        default { q_program_fail() }\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(q_ptr)\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.pushMemTokenOffset then
    "\n                    // VM 0x04 PUSH_MEM_TOKEN_OFFSET (bytes): token byte plus u32 byte offset.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemTokenOffset) ++
    " {\n                        // Operand layout: u8 token, u32 byte offset. This is\n                        // used when a symbolic base such as REVERSED_EVALS_MPTR\n                        // is known, but the expression needs a specific word\n                        // inside that generated region.\n                        let q_word := mload(q_pc)\n                        let q_token := byte(0, q_word)\n                        let q_off := and(shr(216, q_word), 0xffffffff)\n                        q_pc := add(q_pc, 5)\n                        let q_ptr := 0\n                        // Token-offset cases reuse the same token table, then add q_off.\n                        switch q_token" ++
    (if program.memUsage.l0 then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.l0) ++
     " { q_ptr := add(L_0_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.lLast then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.lLast) ++
     " { q_ptr := add(L_LAST_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.lBlind then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.lBlind) ++
     " { q_ptr := add(L_BLIND_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.beta then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.beta) ++
     " { q_ptr := add(BETA_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.gamma then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.gamma) ++
     " { q_ptr := add(GAMMA_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.x then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.x) ++
     " { q_ptr := add(X_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.theta then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.theta) ++
     " { q_ptr := add(THETA_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.trashChallenge then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.trashChallenge) ++
     " { q_ptr := add(TRASH_CHALLENGE_MPTR, q_off) }"
    else
    "") ++
    (if program.memUsage.instanceEval then
     "\n                        case " ++
     hexFilter (ctx.templateConstants.quotientVm.mem.instanceEval) ++
     " { q_ptr := add(INSTANCE_EVAL_MPTR, q_off) }"
    else
    "") ++
    "\n                        default { q_program_fail() }\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(q_ptr)\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.pushMemU16 then
    "\n                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushMemU16) ++
    " {\n                        // Operand layout: u16 absolute memory pointer. The\n                        // memory planner keeps the hot quotient frame below\n                        // 64 KiB when this compact form is emitted.\n                        let q_ptr := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(q_ptr)\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.add then
    "\n                    // VM 0x06 ADD: pop one spilled stack word and add it to q_top.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.add) ++
    " {\n                        // The safety validator guarantees a spilled operand\n                        // exists before ADD. q_top is the right operand.\n                        " ++
    qPopGuard program ++
    "\n                        q_sp := sub(q_sp, 0x20)\n                        q_top := addmod(mload(q_sp), q_top, r)\n                    }"
   else
   "") ++
   (if program.opUsage.mul then
    "\n                    // VM 0x07 MUL: pop one spilled stack word and multiply it by q_top.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mul) ++
    " {\n                        // Same stack contract as ADD, with multiplication\n                        // reduced directly modulo Fr.\n                        " ++
    qPopGuard program ++
    "\n                        q_sp := sub(q_sp, 0x20)\n                        q_top := mulmod(mload(q_sp), q_top, r)\n                    }"
   else
   "") ++
   (if program.opUsage.neg then
    "\n                    // VM 0x08 NEG: replace q_top with its Fr negation.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.neg) ++
    " {\n                        // addmod(0, r - x, r) maps zero back to zero and every\n                        // nonzero scalar to its canonical additive inverse.\n                        q_top := addmod(0, sub(r, q_top), r)\n                    }"
   else
   "") ++
   (if program.opUsage.pow5 then
    "\n                    // VM 0x20 POW5: replace q_top with q_top^5.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pow5) ++
    " {\n                        // Poseidon S-box shortcut: x^5 = x * (x^2)^2.\n                        let q2 := mulmod(q_top, q_top, r)\n                        q_top := mulmod(q_top, mulmod(q2, q2, r), r)\n                    }"
   else
   "") ++
   (if program.opUsage.pushConstU8 then
    "\n                    // VM 0x09 PUSH_CONST_U8 (bytes): next byte is a constant-table slot.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.pushConstU8) ++
    " {\n                        // One-byte variant for the common case where the\n                        // constant table has fewer than 256 referenced slots.\n                        let qconst := byte(0, mload(q_pc))\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        q_top := mload(add(q_const_mptr, shl(5, qconst)))\n                        q_has_top := 1\n                        q_pc := add(q_pc, 1)\n                    }"
   else
   "") ++
   (if program.opUsage.addConstU8 then
    "\n                    // VM 0x0c ADD_CONST_U8: add a small constant-table slot into q_top.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addConstU8) ++
    " {\n                        // Accumulator opcode: mutates q_top in place instead\n                        // of pushing a new stack value.\n                        let qconst := byte(0, mload(q_pc))\n                        q_pc := add(q_pc, 1)\n                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)\n                    }"
   else
   "") ++
   (if program.opUsage.mulConstU8 then
    "\n                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulConstU8) ++
    " {\n                        // One-byte constant-index multiply, used by short\n                        // affine chains after an initial PUSH.\n                        let qconst := byte(0, mload(q_pc))\n                        q_pc := add(q_pc, 1)\n                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)\n                    }"
   else
   "") ++
   (if program.opUsage.addConst then
    "\n                    // VM 0x0e ADD_CONST: add a wider constant-table slot into q_top.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addConst) ++
    " {\n                        // Two-byte constant-index form for larger generated\n                        // constant tables.\n                        let qconst := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        " ++
    qConstGuard program "qconst" ++
    "\n                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)\n                    }"
   else
   "") ++
   (if program.opUsage.mulConst then
    "\n                    // VM 0x0f MUL_CONST: multiply q_top by a wider constant-table slot.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulConst) ++
    " {\n                        // Two-byte constant-index multiply.\n                        let qconst := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        " ++
    qConstGuard program "qconst" ++
    "\n                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)\n                    }"
   else
   "") ++
   (if program.opUsage.addMemU16 then
    "\n                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMemU16) ++
    " {\n                        // Operand layout: u16 pointer. The pointed word is an\n                        // already range-checked Fr scalar in verifier memory.\n                        let q_ptr := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        q_top := addmod(q_top, mload(q_ptr), r)\n                    }"
   else
   "") ++
   (if program.opUsage.mulMemU16 then
    "\n                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.mulMemU16) ++
    " {\n                        // In-place multiply by a planned memory word.\n                        let q_ptr := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        q_top := mulmod(q_top, mload(q_ptr), r)\n                    }"
   else
   "") ++
   (if program.opUsage.addMulMemMemConstU8 then
    "\n                    // VM 0x12 ADD_MUL_MEM_MEM_CONST_U8: fused q_top += lhs * rhs * const.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulMemMemConstU8) ++
    " {\n                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr,\n                        // u8 const_idx. This fuses a frequent affine-product\n                        // term without spending opcodes on PUSH/MUL/MUL/ADD.\n                        let q_word := mload(q_pc)\n                        let q_lhs := shr(240, q_word)\n                        let q_rhs := and(shr(224, q_word), 0xffff)\n                        let qconst := byte(4, q_word)\n                        q_pc := add(q_pc, 5)\n                        q_top := addmod(\n                            q_top,\n                            mulmod(\n                                mulmod(mload(q_lhs), mload(q_rhs), r),\n                                mload(add(q_const_mptr, shl(5, qconst))),\n                                r\n                            ),\n                            r\n                        )\n                    }"
   else
   "") ++
   (if program.opUsage.addMulConstU8MemU16 then
    "\n                    // VM 0x13 ADD_MUL_CONST_U8_MEM_U16: fused q_top += mem * const.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulConstU8MemU16) ++
    " {\n                        // Operand layout: u16 ptr, u8 const_idx.\n                        let q_word := mload(q_pc)\n                        let q_ptr := shr(240, q_word)\n                        let qconst := byte(2, q_word)\n                        q_pc := add(q_pc, 3)\n                        q_top := addmod(\n                            q_top,\n                            mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),\n                            r\n                        )\n                    }"
   else
   "") ++
   (if program.opUsage.addMulMemMem then
    "\n                    // VM 0x14 ADD_MUL_MEM_MEM: fused q_top += lhs * rhs.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.addMulMemMem) ++
    " {\n                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr. This is\n                        // the unit-coefficient sibling of opcode 0x12.\n                        let q_word := mload(q_pc)\n                        let q_lhs := shr(240, q_word)\n                        let q_rhs := and(shr(224, q_word), 0xffff)\n                        q_pc := add(q_pc, " ++
    hexFilter (ctx.templateConstants.quotientVm.byteU32Bytes) ++
    ")\n                        q_top := addmod(q_top, mulmod(mload(q_lhs), mload(q_rhs), r), r)\n                    }"
   else
   "") ++
   (if program.opUsage.runAddMulMemMemConstU8 then
    "\n                    // VM 0x15 RUN_ADD_MUL_MEM_MEM_CONST_U8: byte-only loop over fused 0x12 payloads.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.runAddMulMemMemConstU8) ++
    " {\n                        // Operand layout: u16 count followed by `count`\n                        // packed 0x12-style payloads. The run header saves a\n                        // dispatch per term in long affine product chains.\n                        let q_count := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        let q_run_end := add(q_pc, mul(q_count, 5))\n                        for { } lt(q_pc, q_run_end) { } {\n                            let q_word := mload(q_pc)\n                            let q_lhs := shr(240, q_word)\n                            let q_rhs := and(shr(224, q_word), 0xffff)\n                            let qconst := byte(4, q_word)\n                            q_pc := add(q_pc, 5)\n                            q_top := addmod(\n                                q_top,\n                                mulmod(\n                                    mulmod(mload(q_lhs), mload(q_rhs), r),\n                                    mload(add(q_const_mptr, shl(5, qconst))),\n                                    r\n                                ),\n                                r\n                            )\n                        }\n                    }"
   else
   "") ++
   (if program.opUsage.runAddMulConstU8MemU16 then
    "\n                    // VM 0x16 RUN_ADD_MUL_CONST_U8_MEM_U16: byte-only loop over fused 0x13 payloads.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.runAddMulConstU8MemU16) ++
    " {\n                        // Operand layout: u16 count followed by `count`\n                        // packed 0x13-style payloads.\n                        let q_count := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        let q_run_end := add(q_pc, mul(q_count, 3))\n                        for { } lt(q_pc, q_run_end) { } {\n                            let q_word := mload(q_pc)\n                            let q_ptr := shr(240, q_word)\n                            let qconst := byte(2, q_word)\n                            q_pc := add(q_pc, 3)\n                            q_top := addmod(\n                                q_top,\n                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),\n                                r\n                            )\n                        }\n                    }"
   else
   "") ++
   (if program.opUsage.affineSum then
    "\n                    // VM 0x22 AFFINE_SUM: mixed byte-only affine linear/product loop.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.affineSum) ++
    " {\n                        // Operand layout:\n                        //   u16 lin_count, u16 product_count,\n                        //   lin_count * {u16 ptr, u8 const_idx},\n                        //   product_count * {u16 lhs, u16 rhs, u8 const_idx}.\n                        // The opcode appends all terms into the existing\n                        // q_top accumulator.\n                        let q_lin_count := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        let q_product_count := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        // Linear part: q_top += c_i * mload(ptr_i).\n                        let q_lin_end := add(q_pc, mul(q_lin_count, 3))\n                        for { } lt(q_pc, q_lin_end) { } {\n                            let q_word := mload(q_pc)\n                            let q_ptr := shr(240, q_word)\n                            let qconst := byte(2, q_word)\n                            q_pc := add(q_pc, 3)\n                            q_top := addmod(\n                                q_top,\n                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),\n                                r\n                            )\n                        }\n                        // Product part: q_top += c_i * mload(lhs_i) * mload(rhs_i).\n                        let q_product_end := add(q_pc, mul(q_product_count, 5))\n                        for { } lt(q_pc, q_product_end) { } {\n                            let q_word := mload(q_pc)\n                            let q_lhs := shr(240, q_word)\n                            let q_rhs := and(shr(224, q_word), 0xffff)\n                            let qconst := byte(4, q_word)\n                            q_pc := add(q_pc, 5)\n                            q_top := addmod(\n                                q_top,\n                                mulmod(\n                                    mulmod(mload(q_lhs), mload(q_rhs), r),\n                                    mload(add(q_const_mptr, shl(5, qconst))),\n                                    r\n                                ),\n                                r\n                            )\n                        }\n                    }"
   else
   "") ++
   (if program.opUsage.lin7 || program.opUsage.bilin7Row || program.opUsage.bilin7Pairwise || program.opUsage.modarith7 then
    "\n                    // Limb-aware opcodes are opt-in compact forms for\n                    // structurally recognized non-SHA foreign-field shapes.\n                    // Coefficients are indexes into q_const_mptr, which is\n                    // generated from VK/program data, never from proof\n                    // calldata.\n                    //\n                    // Rust source shape:\n                    //   proofs/src/plonk/mod.rs::partially_evaluate_identities\n                    //   circuits/src/field/foreign/util.rs::{sum_exprs,pair_wise_prod}\n                    //   circuits/src/field/foreign/params.rs::{base_powers,double_base_powers}\n                    //\n                    // \"Foreign field\" means the circuit represents elements\n                    // modulo another modulus m as 7 limbs in base\n                    // 2^LOG2_BASE. The verifier does not switch fields; it\n                    // evaluates the lowered identity over BLS12-381 Fr, using\n                    // Fr coefficients equal to base^i mod m or base^(i+j) mod m."
   else
   "") ++
   (if program.opUsage.lin7 then
    "\n                    // VM 0x1c LIN7: byte-only 7-term foreign-field linear form.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.lin7) ++
    " {\n                        // LIN7: sum_i coeff[i] * value[i] over Fr.\n                        // Typical Rust origin: foreign/gates/norm.rs\n                        // normalization and foreign/gates/mul.rs base-power\n                        // sums for x/y/z limbs.\n                        //\n                        // Operand layout: seven repeated {u8 const_idx,\n                        // u16 ptr} pairs. The result is pushed as a fresh\n                        // stack value.\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        let q_acc := 0\n                        // Accumulate exactly seven limbs, matching the\n                        // generated foreign-field limb width.\n                        for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                            let q_word := mload(q_pc)\n                            let qconst := byte(0, q_word)\n                            let q_ptr := and(shr(232, q_word), 0xffff)\n                            q_pc := add(q_pc, 3)\n                            q_acc := addmod(\n                                q_acc,\n                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),\n                                r\n                            )\n                        }\n                        q_top := q_acc\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.bilin7Row then
    "\n                    // VM 0x1d BILIN7_ROW: byte-only lhs times a 7-term weighted row.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.bilin7Row) ++
    " {\n                        // BILIN7_ROW: lhs * sum_i coeff[i] * rhs[i].\n                        // Typical Rust origin: one row/slice of\n                        // pair_wise_prod in foreign multiplication and EC\n                        // on_curve/slope/tangent/lambda_squared gates.\n                        //\n                        // Operand layout: u16 lhs_ptr, then seven repeated\n                        // {u8 const_idx, u16 rhs_ptr} pairs. The lhs value is\n                        // loaded once and reused for all seven products.\n                        let q_lhs := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        let q_lhs_value := mload(q_lhs)\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        let q_acc := 0\n                        for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                            let q_word := mload(q_pc)\n                            let qconst := byte(0, q_word)\n                            let q_rhs := and(shr(232, q_word), 0xffff)\n                            q_pc := add(q_pc, 3)\n                            q_acc := addmod(\n                                q_acc,\n                                mulmod(\n                                    mulmod(q_lhs_value, mload(q_rhs), r),\n                                    mload(add(q_const_mptr, shl(5, qconst))),\n                                    r\n                                ),\n                                r\n                            )\n                        }\n                        q_top := q_acc\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.bilin7Pairwise then
    "\n                    // VM 0x1e BILIN7_PAIRWISE: byte-only 7-by-7 weighted convolution.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.bilin7Pairwise) ++
    " {\n                        // BILIN7_PAIRWISE:\n                        //   sum_{i=0..6,j=0..6} coeff[i+j] * lhs[i] * rhs[j].\n                        // Bases point to contiguous 7-word limb vectors.\n                        // Typical Rust origin:\n                        //   sum_exprs(double_base_powers,\n                        //             pair_wise_prod(lhs, rhs))\n                        // where double_base_powers[k] = base^k mod m.\n                        //\n                        // Operand layout: u16 lhs_base, u16 rhs_base, then 13\n                        // one-byte coefficient indexes. Coefficients are\n                        // addressed by i+j, so 7-by-7 products need 13 slots.\n                        let q_word := mload(q_pc)\n                        let q_lhs_base := shr(240, q_word)\n                        let q_rhs_base := and(shr(224, q_word), 0xffff)\n                        q_pc := add(q_pc, " ++
    hexFilter (ctx.templateConstants.quotientVm.byteU32Bytes) ++
    ")\n                        let q_coeff_pc := q_pc\n                        q_pc := add(q_pc, " ++
    toString (ctx.templateConstants.quotientVm.limbPairwiseCoeffs) ++
    ")\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n                        let q_acc := 0\n                        // Nested limb convolution over two contiguous\n                        // 7-word vectors.\n                        for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                            let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))\n                            for { let q_j := 0 } lt(q_j, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_j := add(q_j, 1) } {\n                                let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))\n                                q_acc := addmod(\n                                    q_acc,\n                                    mulmod(\n                                        mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),\n                                        mload(add(q_const_mptr, shl(5, qconst))),\n                                        r\n                                    ),\n                                    r\n                                )\n                            }\n                        }\n                        q_top := q_acc\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.modarith7 then
    "\n                    // VM 0x21 MODARITH7: byte-only fused affine 7-limb foreign-field/ECC identity.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.modarith7) ++
    " {\n                        // MODARITH7:\n                        //   maybe_cond * (\n                        //       c\n                        //     + sum LIN7 blocks\n                        //     + sum BILIN7_ROW blocks\n                        //     + sum BILIN7_PAIRWISE blocks\n                        //     + sum coeff[k] * mload(ptr[k])\n                        //     + sum coeff[k] * mload(lhs[k]) * mload(rhs[k])\n                        //   )\n                        // It is a dispatch/operand-load optimization only;\n                        // all coefficients still come from the generated\n                        // quotient constant table.\n                        //\n                        // Flags:\n                        //   bit 0: multiply the final affine sum by a memory\n                        //          condition word.\n                        //   bit 1: seed q_acc from a constant-table word\n                        //          before reading the counted term blocks.\n                        let q_flags := byte(0, mload(q_pc))\n                        q_pc := add(q_pc, 1)\n                        // Only the COND (0x01) and CONST (0x02) flag bits are\n                        // defined; the byte validator rejects any other bit.\n                        if gt(q_flags, 0x03) { q_program_fail() }\n                        let q_cond_ptr := 0\n                        if and(q_flags, 0x01) {\n                            // Optional condition pointer. When present, the\n                            // whole identity is gated by mload(q_cond_ptr).\n                            q_cond_ptr := shr(240, mload(q_pc))\n                            q_pc := add(q_pc, 2)\n                        }\n\n                        let q_acc := 0\n                        if and(q_flags, 0x02) {\n                            // Optional constant seed for affine identities\n                            // with a standalone constant term.\n                            let qconst := byte(0, mload(q_pc))\n                            q_pc := add(q_pc, 1)\n                            q_acc := mload(add(q_const_mptr, shl(5, qconst)))\n                        }\n\n                        // Five one-byte counters describe the blocks that\n                        // follow. Each block has a fixed-width internal layout,\n                        // so q_pc can advance without per-term tags.\n                        let q_counts_word := mload(q_pc)\n                        let q_lin_count := byte(0, q_counts_word)\n                        let q_row_count := byte(1, q_counts_word)\n                        let q_pairwise_count := byte(2, q_counts_word)\n                        let q_mem_count := byte(3, q_counts_word)\n                        let q_product_count := byte(4, q_counts_word)\n                        q_pc := add(q_pc, 5)\n\n                        if q_has_top {\n                            " ++
    qSpillGuard program ++
    "\n                            mstore(q_sp, q_top)\n                            q_sp := add(q_sp, 0x20)\n                        }\n\n                        // LIN7 blocks: q_acc += sum_i c_i * limb_i.\n                        for { let q_lin_block := 0 } lt(q_lin_block, q_lin_count) { q_lin_block := add(q_lin_block, 1) } {\n                            for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                                let q_word := mload(q_pc)\n                                let qconst := byte(0, q_word)\n                                let q_ptr := and(shr(232, q_word), 0xffff)\n                                q_pc := add(q_pc, 3)\n                                q_acc := addmod(\n                                    q_acc,\n                                    mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),\n                                    r\n                                )\n                            }\n                        }\n\n                        // BILIN7_ROW blocks: q_acc += lhs * sum_i c_i * rhs_i.\n                        for { let q_row_block := 0 } lt(q_row_block, q_row_count) { q_row_block := add(q_row_block, 1) } {\n                            let q_lhs := shr(240, mload(q_pc))\n                            q_pc := add(q_pc, 2)\n                            let q_lhs_value := mload(q_lhs)\n                            for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                                let q_word := mload(q_pc)\n                                let qconst := byte(0, q_word)\n                                let q_rhs := and(shr(232, q_word), 0xffff)\n                                q_pc := add(q_pc, 3)\n                                q_acc := addmod(\n                                    q_acc,\n                                    mulmod(\n                                        mulmod(q_lhs_value, mload(q_rhs), r),\n                                        mload(add(q_const_mptr, shl(5, qconst))),\n                                        r\n                                    ),\n                                    r\n                                )\n                            }\n                        }\n\n                        // BILIN7_PAIRWISE blocks: q_acc += weighted 7-by-7\n                        // product convolution.\n                        for { let q_pair_block := 0 } lt(q_pair_block, q_pairwise_count) { q_pair_block := add(q_pair_block, 1) } {\n                            let q_pair_word := mload(q_pc)\n                            let q_lhs_base := shr(240, q_pair_word)\n                            let q_rhs_base := and(shr(224, q_pair_word), 0xffff)\n                            q_pc := add(q_pc, " ++
    hexFilter (ctx.templateConstants.quotientVm.byteU32Bytes) ++
    ")\n                            let q_coeff_pc := q_pc\n                            q_pc := add(q_pc, " ++
    toString (ctx.templateConstants.quotientVm.limbPairwiseCoeffs) ++
    ")\n                            for { let q_i := 0 } lt(q_i, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_i := add(q_i, 1) } {\n                                let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))\n                                for { let q_j := 0 } lt(q_j, " ++
    toString (ctx.templateConstants.quotientVm.limbCount) ++
    ") { q_j := add(q_j, 1) } {\n                                    let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))\n                                    q_acc := addmod(\n                                        q_acc,\n                                        mulmod(\n                                            mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),\n                                            mload(add(q_const_mptr, shl(5, qconst))),\n                                            r\n                                        ),\n                                        r\n                                    )\n                                }\n                            }\n                        }\n\n                        // Extra linear memory terms outside the 7-limb shapes.\n                        for { let q_mem_block := 0 } lt(q_mem_block, q_mem_count) { q_mem_block := add(q_mem_block, 1) } {\n                            let q_word := mload(q_pc)\n                            let qconst := byte(0, q_word)\n                            let q_ptr := and(shr(232, q_word), 0xffff)\n                            q_pc := add(q_pc, 3)\n                            q_acc := addmod(\n                                q_acc,\n                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),\n                                r\n                            )\n                        }\n\n                        // Extra binary product terms outside the 7-limb shapes.\n                        for { let q_product_block := 0 } lt(q_product_block, q_product_count) { q_product_block := add(q_product_block, 1) } {\n                            let q_word := mload(q_pc)\n                            let qconst := byte(0, q_word)\n                            let q_lhs := and(shr(232, q_word), 0xffff)\n                            let q_rhs := and(shr(216, q_word), 0xffff)\n                            q_pc := add(q_pc, 5)\n                            q_acc := addmod(\n                                q_acc,\n                                mulmod(\n                                    mulmod(mload(q_lhs), mload(q_rhs), r),\n                                    mload(add(q_const_mptr, shl(5, qconst))),\n                                    r\n                                ),\n                                r\n                            )\n                        }\n\n                        if and(q_flags, 0x01) {\n                            // Apply the optional gate condition last so every\n                            // subterm shares the same selector/condition.\n                            q_acc := mulmod(mload(q_cond_ptr), q_acc, r)\n                        }\n                        // MODARITH7 pushes its fused identity value.\n                        q_top := q_acc\n                        q_has_top := 1\n                    }"
   else
   "") ++
   (if program.opUsage.nativePermutation && (ctx.quotientNativePermutationComputation).length > 0 then
    "\n                    // Native permutation callback. It evaluates the\n                    // permutation identities from permutation.rs at this exact\n                    // VM position, preserving the Rust identity order while\n                    // avoiding a large interpreted product loop.\n                    // VM 0x19 NATIVE_PERMUTATION: marker for the generated permutation callback.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativePermutation) ++
    " {\n                        // Native callbacks are identity-boundary opcodes. They\n                        // must not inherit any partially evaluated VM stack\n                        // state from the previous expression, so the stack\n                        // must already be empty (no live top, nothing spilled).\n                        " ++
    qNativeGuard program ++
    "\n                        // The generated loop below uses program.stack_mptr as\n                        // its scratch-table base, not as a conventional VM\n                        // stack. The Rust memory planner must reserve enough\n                        // words for structured_permutation_scratch_words(meta)\n                        // whenever this opcode can appear.\n                        // The generated lines below call the same fold snippets\n                        // used by interpreted expressions, so trace IDs and\n                        // y-batch positions remain contiguous." ++
    (jinjaFor ctx.quotientNativePermutationComputation (fun line loop =>
     "\n                        " ++
     line)) ++
    "\n                    }"
   else
   "") ++
   (if program.opUsage.nativeLookup && (ctx.quotientNativeLookupComputation).length > 0 then
    "\n                    // Native lookup callback. This whole-family opcode\n                    // evaluates the LogUp boundary, helper-chunk, and\n                    // accumulator identities at this VM position, preserving\n                    // the Rust y-batch order while avoiding many interpreted\n                    // product-loop opcodes.\n                    // VM 0x1f NATIVE_LOOKUP: marker for the generated LogUp lookup callback.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativeLookup) ++
    " {\n                        // The VM stack must be empty before entering\n                        // structured lookup Yul. Lookup callbacks own their\n                        // scratch layout and perform all needed folds\n                        // internally.\n                        " ++
    qNativeGuard program ++
    "\n                        // The generated loop below uses program.stack_mptr as\n                        // f+beta/prefix/suffix scratch rather than as a\n                        // conventional VM stack. The Rust memory planner must\n                        // reserve structured_lookup_scratch_words(meta).\n                        // Generated LogUp code follows the same y-batch order\n                        // as the Rust identity stream." ++
    (jinjaFor ctx.quotientNativeLookupComputation (fun line loop =>
     "\n                        " ++
     line)) ++
    "\n                    }"
   else
   "") ++
   (if program.opUsage.nativeIdentity && (ctx.quotientNativeIdentityComputations).length > 0 then
    "\n                    // Native callbacks are generated only for the heaviest\n                    // recognized Midfall gate identities. All other gate and\n                    // non-native identity arithmetic remains in\n                    // the compact q_program VM above, preserving the Rust\n                    // `partially_evaluate_identities` order.\n                    // VM 0x1b NATIVE_IDENTITY: marker for generated heavy-gate callbacks.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.nativeIdentity) ++
    " {\n                        // Operand layout: u16 native callback index. The\n                        // manifest validates that callback indexes appear in\n                        // generated order and target existing switch cases.\n                        let q_native_idx := shr(240, mload(q_pc))\n                        q_pc := add(q_pc, 2)\n                        // Heavy identities are whole expressions, so the\n                        // interpreter stack must be empty before dispatching.\n                        " ++
    qNativeGuard program ++
    "\n                        // Native identity sub-cases are generated from selected heavy gate identities.\n                        switch q_native_idx" ++
    (jinjaFor ctx.quotientNativeIdentityComputations (fun code_block loop =>
     "\n                        case " ++
     toString (loop.index0) ++
     " {" ++
     (jinjaFor code_block (fun line loop =>
      "\n                            " ++
      line)) ++
     "\n                        }")) ++
    "\n                        default { q_program_fail() }\n                    }"
   else
   "") ++
   (if program.opUsage.foldMain then
    "\n                    // VM 0x0a FOLD_MAIN: consume q_top into the fully evaluated numerator fold.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.foldMain) ++
    " {\n                        // q_top is the complete value of one fully evaluated\n                        // identity at x. It leaves the expression stack here.\n                        " ++
    qFoldGuard program ++
    "\n                        let q_eval := q_top\n                        q_has_top := 0" ++
    (if ctx.trace then
     "\n                        trace_u256(mload(" ++
     hexFilter (program.traceIdMptr) ++
     "), q_eval)\n                        mstore(" ++
     hexFilter (program.traceIdMptr) ++
     ", add(mload(" ++
     hexFilter (program.traceIdMptr) ++
     "), 1))"
    else
    "") ++
    "\n                        // Fully-evaluated identity: qn = qn*y + eval.\n                        // This matches the reverse y-power fold in Rust\n                        // linearization once all identities have been read.\n                        mstore(" ++
    hexFilter (program.evalNumerMptr) ++
    ", mulmod(mload(" ++
    hexFilter (program.evalNumerMptr) ++
    "), y, r))\n                        mstore(" ++
    hexFilter (program.evalNumerMptr) ++
    ", addmod(mload(" ++
    hexFilter (program.evalNumerMptr) ++
    "), q_eval, r))\n                    }"
   else
   "") ++
   (if program.opUsage.foldSelector then
    "\n                    // VM 0x0b FOLD_SELECTOR: consume q_top into one simple-selector bucket.\n                    case " ++
    hexFilter (ctx.templateConstants.quotientVm.op.foldSelector) ++
    " {\n                        // Operand layout packed into three bytes:\n                        //   high byte: selector bucket index;\n                        //   low u16 : y-power gap since this selector's\n                        //             previous contribution.\n                        let q_selector_payload := shr(232, mload(q_pc))\n                        q_pc := add(q_pc, 3)\n                        let q_sel_idx := shr(16, q_selector_payload)\n                        let q_sel_gap := and(q_selector_payload, 0xffff)\n                        // The bucket index addresses SELECTOR_ACC and the gap\n                        // indexes the precomputed y-power table; both sizes\n                        // are codegen-known, so check them before any write.\n                        if iszero(lt(q_sel_idx, " ++
    toString (program.guards.numSelectorBuckets) ++
    ")) { q_program_fail() }\n                        if gt(q_sel_gap, " ++
    hexFilter (program.selectorMaxPower) ++
    ") { q_program_fail() }\n                        " ++
    qFoldGuard program ++
    "\n                        let q_eval := q_top\n                        q_has_top := 0" ++
    (if ctx.trace then
     "\n                        trace_u256(mload(" ++
     hexFilter (program.traceIdMptr) ++
     "), q_eval)\n                        mstore(" ++
     hexFilter (program.traceIdMptr) ++
     ", add(mload(" ++
     hexFilter (program.traceIdMptr) ++
     "), 1))"
    else
    "") ++
    "\n                        // Simple-selector identity: keep the same y-batch\n                        // position as main identities, then advance only this\n                        // selector bucket by its codegen-known gap.\n                        //\n                        // The global fully-evaluated accumulator is still\n                        // multiplied by y so later main identities land at the\n                        // same y powers as Rust's reverse fold.\n                        mstore(" ++
    hexFilter (program.evalNumerMptr) ++
    ", mulmod(mload(" ++
    hexFilter (program.evalNumerMptr) ++
    "), y, r))\n                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))\n                        let q_sel_acc := mload(q_target_ptr)\n                        if q_sel_gap {\n                            // Selector buckets are sparse in the global\n                            // identity stream. Precomputed y^gap advances only\n                            // this selector's local accumulator.\n                            q_sel_acc := mulmod(q_sel_acc, mload(add(" ++
    hexFilter (program.selectorPowerMptr) ++
    ", shl(5, q_sel_gap))), r)\n                        }\n                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))\n                    }"
   else
   "") ++
   "\n                    // Invalid generated bytecode should fail closed. 0x1a intentionally lands here.\n                    default {\n                        q_program_fail()\n                    }\n                }\n                // The VK-pinned bytecode must end exactly at q_end and every\n                // identity must have been consumed by a fold/native callback.\n                // This catches malformed generator output whose final opcode\n                // over-reads operands or leaves a partial expression live.\n                if iszero(eq(q_pc, q_end)) { q_program_fail() }\n                if q_has_top { q_program_fail() }\n                // The spilled stack must also be balanced. A FOLD executed\n                // with more than one operand live consumes only the cached\n                // top, leaving abandoned words below q_sp with q_has_top\n                // clear -- so both checks above pass while an operand of the\n                // identity has been silently dropped from nu_y(x).\n                if iszero(eq(q_sp, " ++
   hexFilter (program.stackMptr) ++
   ")) { q_program_fail() }\n\n                // Structured post-VM suffix. The current default uses this for\n                // regular trash constraints: it is smaller than fully unrolled\n                // Yul and cheaper than interpreting every trash operation.\n                //\n                // These generated blocks run after q_pc reaches q_end, but\n                // they still participate in the same identity order and write\n                // into the same numerator / selector accumulators." ++
   (jinjaFor ctx.quotientPostVmComputations (fun code_block loop =>
    (jinjaFor code_block (fun line loop =>
     "\n                " ++
     line)))) ++
   (if (ctx.simpleSelectorCols).length > 0 then
    "\n                // Finish selector buckets by applying the codegen-known tail\n                // from each selector's last identity to the end of the global\n                // y-batch.\n                //\n                // After this step, every selector bucket is aligned with the\n                // final global y position and can be multiplied by its fixed\n                // selector commitment in the linearized MSM." ++
    (jinjaFor program.selectorTailUpdates (fun tail loop =>
     "\n                {\n                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, " ++
     hexFilter (tail.selectorOffset) ++
     ")\n                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(" ++
     hexFilter (program.selectorPowerMptr) ++
     ", " ++
     hexFilter (tail.powerOffset) ++
     ")), r))\n                }"))
   else
   "") ++
   "\n\n                // Fully evaluated identities are the constant-polynomial side\n                // of the linearization query. Rust subtracts that grouped\n                // scalar into expected_eval, so Solidity stores -nu_y(x).\n                let linearization_expected_eval := addmod(0, sub(r, mload(" ++
   hexFilter (program.evalNumerMptr) ++
   ")), r)\n                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)\n                pop(y)"
   | none =>
   "\n                // Legacy/direct mode. This path emits the numerator\n                // reconstruction directly instead of interpreting q_program.\n                // It is used by older monolithic/experimental generation\n                // modes and remains available as a fallback for models that do\n                // not carry compact quotient bytecode.\n                //\n                // The generated statements in quotient_eval_numer_computations\n                // are already ordered and folded by the Rust renderer. They\n                // must leave `quotient_eval_numer` as nu_y(x), matching the\n                // compact VM accumulator in program.eval_numer_mptr.\n                let delta := " ++
   ctx.frDelta ++
   " // BLS12-381 Fr::DELTA\n                let y := mload(Y_MPTR)" ++
   (if ctx.trace then
    "\n                // Direct mode increments q_trace_id inside generated fold\n                // snippets, mirroring compact-mode trace_id_mptr.\n                let q_trace_id := " ++
    toString (ctx.quotientIdentityTraceBase)
   else
   "") ++
   "\n\n                // Direct/generated numerator body. This may contain unrolled\n                // gate, permutation, lookup, trash, and selector-fold code." ++
   (jinjaFor ctx.quotientEvalNumerComputations (fun code_block loop =>
    (jinjaFor code_block (fun line loop =>
     "\n                " ++
     line)))) ++
   "\n\n                // Silence Yul unused-variable warnings in renders where the\n                // direct body did not need one of these common constants.\n                pop(y)\n                pop(delta)\n\n                // Store the expected opening scalar for the linearized\n                // commitment at x: the negated sum of fully-evaluated\n                // identities. See\n                // `compute_linearization_commitment` in\n                // midfall/proofs/src/plonk/linearization/verifier.rs:\n                //\n                //   expected_eval -= eval     (for col_idx == None)\n                //\n                // The commitment side already includes the quotient-limb\n                // factor (1 - x^n), so this scalar is -nu_y(x), not\n                // h(x) = nu_y(x) / (x^n - 1).\n                let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)\n                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)") ++
  "\n            }"

/-- rust: the Askama expansion of T:partials/verifier/Constants.sol (255 template
    lines at HEAD), the FIRST of the thirteen includes of
    T:contracts/Halo2Verifier.sol. Deployed render: D:85-306, 13,873 bytes, 222
    lines - the render opens with the newline that turns D:85 into one of the
    dump's six whitespace-only lines, because the template's first line is a
    `{%- match %}` whose arm body starts on the line after it. Control flow: the
    expected_vk_codehash match at :1-14 takes its SOME arm (this artifact pins the
    VK by codehash), the quotient_external match at :15-30 takes None, the
    expected_has_accumulator if at :199-204 zero-renders, and the quotient_direct
    match at :248-255 takes None, so the partial ends on the
    BLS_P_MINUS_ONE_PACKED_1 literal with no trailing newline (rule 4).

    THE FILTER SPLIT, which is the whole risk of this partial: `{{ vk_len }}` and
    the four `template_constants.gas.*` sites render DECIMAL (D:92 '4576',
    D:259 '375'), `|hex()` renders byte-padded hex, `|hex_padded(64)` renders a
    64-nibble word, and a bare `{{ memory.vk_mptr }}` renders through Ptr's
    Display, i.e. MINIMAL-width hex with no byte pad. Gate 71 pins all four
    spellings against the same artifact. `proof_cptr - 1` is WORD-wise: 0x64 - 1
    renders 0x44 (ENC:733-741), which is PROOF_LEN_CPTR at D:101. -/
def renderConstants (ctx : PartialCtx) : String :=   (match ctx.expectedVkCodehash with 
    | some expectedVkCodehash =>
      "\n    /// @notice Verifying-key contract address authorized for this verifier.\n    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.\n    address public immutable AUTHORIZED_VK;\n    // Expected VK runtime metadata. The deployed VK runtime is\n    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than\n    // EXPECTED_VK_PAYLOAD_LENGTH.\n    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = " ++
      toString (ctx.vkLen) ++
      ";\n    uint256 internal constant EXPECTED_VK_LENGTH = " ++
      toString (ctx.vkLen + 1) ++
      ";\n    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = " ++
      hexPaddedFilter 64 (expectedVkCodehash.toNat) ++
      ";\n    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);"
    | none =>
      "") ++
    (match ctx.quotientExternal with 
    | some _ =>
      "\n    /// @notice Quotient evaluator contract authorized for split quotient reconstruction.\n    /// @dev The evaluator returns the linearization expected scalar and selector buckets; its runtime may be pinned by generated constants.\n    address public immutable AUTHORIZED_QUOTIENT;" ++
      (match ctx.expectedQuotientCodehash with 
      | some expectedQuotientCodehash =>
        "\n    // Expected split evaluator runtime metadata. It is checked at deployment\n    // and again immediately before each external quotient reconstruction.\n    uint256 internal constant EXPECTED_QUOTIENT_LENGTH = " ++
        toString (ctx.expectedQuotientLen.getD 0) ++
        ";\n    uint256 internal constant EXPECTED_QUOTIENT_CODEHASH_WORD = " ++
        hexPaddedFilter 64 (expectedQuotientCodehash.toNat) ++
        ";\n    bytes32 internal constant EXPECTED_QUOTIENT_CODEHASH = bytes32(EXPECTED_QUOTIENT_CODEHASH_WORD);"
      | none =>
        "")
    | none =>
      "") ++
    "\n\n    // Solidity ABI calldata cursors. The generated verifier accepts exactly\n    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`\n    // bytes itself in the same order as the Rust verifier transcript.\n    uint256 internal constant    PROOF_LEN_CPTR = " ++
    printPtr ((Ptr.sub ctx.proofCptr 1).value) ++
    ";\n    uint256 internal constant        PROOF_CPTR = " ++
    printPtr (ctx.proofCptr.value) ++
    ";\n    uint256 internal constant NUM_INSTANCE_CPTR = " ++
    hexPaddedFilter 2 (ctx.numInstanceCptr) ++
    ";\n    uint256 internal constant     INSTANCE_CPTR = " ++
    hexPaddedFilter 2 (ctx.instanceCptr) ++
    ";\n    // First general-purpose memory words reserved by the generated verifier.\n    // RETURN_MPTR is a single word set to 1 on success.\n    uint256 internal constant    TRANSCRIPT_MPTR = " ++
    hexFilter (ctx.memory.transcriptMptr) ++
    ";\n    uint256 internal constant        RETURN_MPTR = " ++
    hexFilter (ctx.memory.verifierReturnMptr) ++
    ";\n\n    // ----------------------------------------------------------------------\n    // Verifying-key memory map. The VK header lives at VK_MPTR, followed\n    // by the quotient VM payload and commitments. After the full VK\n    // runtime comes the challenge slots (challenge_mptr..) and the\n    // per-stage scratch (theta_mptr..).\n    // ----------------------------------------------------------------------\n    uint256 internal constant                VK_MPTR = " ++
    printPtr (ctx.memory.vkMptr.value) ++
    ";\n    uint256 internal constant         VK_DIGEST_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.vkDigest).value) ++
    ";\n    uint256 internal constant     NUM_INSTANCES_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numInstances).value) ++
    ";\n    uint256 internal constant                 K_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.k).value) ++
    ";\n    uint256 internal constant             N_INV_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.nInv).value) ++
    ";\n    uint256 internal constant             OMEGA_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omega).value) ++
    ";\n    uint256 internal constant         OMEGA_INV_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInv).value) ++
    ";\n    uint256 internal constant    OMEGA_INV_TO_L_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInvToL).value) ++
    ";\n    uint256 internal constant   HAS_ACCUMULATOR_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.hasAccumulator).value) ++
    ";\n    uint256 internal constant        ACC_OFFSET_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.accOffset).value) ++
    ";\n    uint256 internal constant     NUM_ACC_LIMBS_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbs).value) ++
    ";\n    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbBits).value) ++
    ";\n    uint256 internal constant            G1_BASE_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g1Base).value) ++
    ";\n    uint256 internal constant            G2_BASE_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g2Base).value) ++
    ";\n    uint256 internal constant      NEG_S_G2_BASE_MPTR = " ++
    printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.negSG2Base).value) ++
    ";\n\n    uint256 internal constant CHALLENGE_MPTR = " ++
    printPtr (ctx.memory.challengeMptr.value) ++
    ";\n\n    // Challenge layout. Squeeze order in midnight-proofs:\n    //   user_phase challenges (variable count)\n    //   theta -> beta, gamma -> trash_challenge -> y -> x ->\n    //   x1, x2 -> x3 -> x4\n    uint256 internal constant            THETA_MPTR = " ++
    printPtr (ctx.memory.thetaMptr.value) ++
    ";\n    uint256 internal constant             BETA_MPTR = " ++
    printPtr (ctx.memory.betaMptr.value) ++
    ";\n    uint256 internal constant            GAMMA_MPTR = " ++
    printPtr (ctx.memory.gammaMptr.value) ++
    ";\n    uint256 internal constant TRASH_CHALLENGE_MPTR = " ++
    printPtr (ctx.memory.trashChallengeMptr.value) ++
    ";\n    uint256 internal constant                Y_MPTR = " ++
    printPtr (ctx.memory.yMptr.value) ++
    ";\n    uint256 internal constant                X_MPTR = " ++
    printPtr (ctx.memory.xMptr.value) ++
    ";\n    uint256 internal constant               X1_MPTR = " ++
    printPtr (ctx.memory.x1Mptr.value) ++
    ";\n    uint256 internal constant               X2_MPTR = " ++
    printPtr (ctx.memory.x2Mptr.value) ++
    ";\n    uint256 internal constant               X3_MPTR = " ++
    printPtr (ctx.memory.x3Mptr.value) ++
    ";\n    uint256 internal constant               X4_MPTR = " ++
    printPtr (ctx.memory.x4Mptr.value) ++
    ";\n\n    // Batch-open commitments live in 4-word EIP-2537 padded slots.\n    uint256 internal constant             F_COM_MPTR = " ++
    printPtr (ctx.memory.fComMptr.value) ++
    ";\n    uint256 internal constant                PI_MPTR = " ++
    printPtr (ctx.memory.piMptr.value) ++
    ";\n\n    // Accumulator (KZG IVC).\n    uint256 internal constant          ACC_LHS_MPTR = " ++
    printPtr (ctx.memory.accLhsMptr.value) ++
    ";\n    uint256 internal constant          ACC_RHS_MPTR = " ++
    printPtr (ctx.memory.accRhsMptr.value) ++
    ";\n\n    // Lagrange / linearization scratch.\n    uint256 internal constant              X_N_MPTR = " ++
    printPtr (ctx.memory.xNMptr.value) ++
    ";\n    uint256 internal constant  X_N_MINUS_1_INV_MPTR = " ++
    printPtr (ctx.memory.xNMinus1InvMptr.value) ++
    ";\n    uint256 internal constant           L_LAST_MPTR = " ++
    printPtr (ctx.memory.lLastMptr.value) ++
    ";\n    uint256 internal constant          L_BLIND_MPTR = " ++
    printPtr (ctx.memory.lBlindMptr.value) ++
    ";\n    uint256 internal constant              L_0_MPTR = " ++
    printPtr (ctx.memory.l0Mptr.value) ++
    ";\n    uint256 internal constant     INSTANCE_EVAL_MPTR = " ++
    printPtr (ctx.memory.instanceEvalMptr.value) ++
    ";\n    // Legacy name: this is not h(x). It stores the expected opening\n    // scalar for the linearized commitment, i.e. the negated y-batched\n    // identity numerator reconstructed from the alleged evals at x.\n    uint256 internal constant     QUOTIENT_EVAL_MPTR = " ++
    printPtr (ctx.memory.quotientEvalMptr.value) ++
    ";\n    uint256 internal constant         QUOTIENT_MPTR = " ++
    printPtr (ctx.memory.quotientMptr.value) ++
    ";   // 4 words\n    uint256 internal constant            F_EVAL_MPTR = " ++
    printPtr (ctx.memory.fEvalMptr.value) ++
    ";\n    uint256 internal constant                 V_MPTR = " ++
    printPtr (ctx.memory.vMptr.value) ++
    ";\n    uint256 internal constant         FINAL_COM_MPTR = " ++
    printPtr (ctx.memory.finalComMptr.value) ++
    ";   // 4 words\n    uint256 internal constant      PAIRING_LHS_MPTR = " ++
    printPtr (ctx.memory.pairingLhsMptr.value) ++
    ";   // 4 words\n    uint256 internal constant      PAIRING_RHS_MPTR = " ++
    printPtr (ctx.memory.pairingRhsMptr.value) ++
    ";   // 4 words\n\n    // Multi-prepare scratch (sized at codegen time).\n    uint256 internal constant       ROT_POINTS_MPTR = " ++
    printPtr (ctx.memory.rotPointsMptr.value) ++
    ";\n    uint256 internal constant       X1_POWERS_MPTR = " ++
    printPtr (ctx.memory.x1PowersMptr.value) ++
    ";\n    // Q_COM materialization is currently fused into the final MSM scratch,\n    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero\n    // reserved capacity until a future emitter starts writing Q_COM_MPTR.\n    uint256 internal constant            Q_COM_MPTR = " ++
    printPtr (ctx.memory.qComMptr.value) ++
    ";\n    uint256 internal constant      Q_EVAL_SET_MPTR = " ++
    printPtr (ctx.memory.qEvalSetMptr.value) ++
    ";\n\n    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals\n    // block of the proof; we keep it as a memory slot for symmetry.\n    uint256 internal constant         Q_EVAL_CPTR_MPTR = " ++
    printPtr (ctx.memory.qEvalCptrMptr.value) ++
    ";\n\n    // Reserved 4-word slot for the G1 identity (point at infinity) in\n    // EIP-2537 padded form. EVM memory is zero-initialised, and the verifier\n    // never writes to this region, so any read of this slot (the PCS\n    // emitters `mcopy` from it when staging identity commitments) yields\n    // 0,0,0,0 -- exactly the identity encoding the EIP-2537 precompiles\n    // accept. Artifacts whose PCS plan never stages an identity commitment\n    // still emit the constant; it costs no runtime bytes beyond the\n    // declaration and keeps the emitters' pointer model uniform.\n    uint256 internal constant       G1_IDENTITY_MPTR = " ++
    printPtr (ctx.memory.g1IdentityMptr.value) ++
    ";\n\n    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain\n    // Solidity proof shim rewrites proof scalars into canonical BE words,\n    // so `calldataload` gives the field element directly. The transcript-\n    // side `evaluations` loop range-checks and spills that value here so\n    // downstream eval references (gate evaluator + PCS q_eval Horner)\n    // become 3-gas `mload(...)` instead of calldata reads.\n    uint256 internal constant     REVERSED_EVALS_MPTR = " ++
    printPtr (ctx.memory.reversedEvalsMptr.value) ++
    ";\n    uint256 internal constant      SELECTOR_ACC_MPTR = " ++
    hexFilter (ctx.memory.selectorAccMptr) ++
    ";\n    uint256 internal constant   QUOTIENT_RETURN_MPTR = " ++
    hexFilter (ctx.memory.quotientReturnMptr) ++
    ";\n    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = " ++
    hexFilter (ctx.memory.batchInvertScratchMptr) ++
    ";\n    uint256 internal constant   LAGRANGE_DENOMS_MPTR = " ++
    hexFilter (ctx.memory.lagrangeDenomsMptr) ++
    ";\n    uint256 internal constant        TRACE_U256_MPTR = " ++
    hexFilter (ctx.memory.traceU256Mptr) ++
    ";\n\n    // ----------------------------------------------------------------------\n    // Per-category bases for EIP-2537 padded G1 commitments. The proof\n    // calldata carries 128-byte uncompressed/padded G1s after the off-chain\n    // proof shim repacks midnight-proofs' native compressed stream; this\n    // region stores the 4-word slots used by PCS / quotient-fold sections.\n    //\n    // Cumulative offsets (in words from `comms_mptr_base`):\n    //   ADVICE_COMMS_MPTR_BASE          + 0\n    //   LOOKUP_M_COMMS_MPTR_BASE        + 4*total_advices\n    //   PERM_Z_COMMS_MPTR_BASE          + 4*total_advices + 4*num_lookups\n    //   LOOKUP_HELPER_COMMS_MPTR_BASE   + ... + 4*num_permutation_zs\n    //   LOOKUP_Z_COMMS_MPTR_BASE        + ... + 4*lookup_helper_chunks_total\n    //   TRASHCAN_COMMS_MPTR_BASE        + ... + 4*num_lookups\n    //   QUOTIENT_LIMB_COMMS_MPTR_BASE   + ... + 4*num_trashcans\n    // ----------------------------------------------------------------------\n    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.adviceCommsMptrBase.value) ++
    ";\n    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.lookupMCommsMptrBase.value) ++
    ";\n    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.permZCommsMptrBase.value) ++
    ";\n    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.lookupHelperCommsMptrBase.value) ++
    ";\n    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.lookupZCommsMptrBase.value) ++
    ";\n    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.trashcanCommsMptrBase.value) ++
    ";\n    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = " ++
    printPtr (ctx.memory.quotientLimbCommsMptrBase.value) ++
    ";\n\n    // ----------------------------------------------------------------------\n    // Precompile gas bounds: the scheduled EIP-2537 costs, and for modexp the\n    // maximum over the EIP-2565 and EIP-7883 schedules.\n    //\n    // A failing EIP-2537 or modexp call consumes ALL gas supplied to the\n    // STATICCALL, so every generated call site forwards the exact scheduled\n    // cost instead of gas(). A malformed proof point then burns at most the\n    // scheduled cost of the single failing call instead of 63/64 of the\n    // transaction budget. The schedule is the spec-guaranteed worst case\n    // (EIP-2537 \"DDoS protection\" rationale), so these bounds are sufficient\n    // by construction on any conformant chain.\n    //\n    // MODEXP_GAS covers both live modexp schedules: EIP-2565 prices this\n    // frame at 1360, EIP-7883 (Osaka/Fusaka) removes the /3 divisor and\n    // prices it at 4080, so the larger bound is rendered. Forwarding the\n    // EIP-7883 bound on a pre-Osaka chain is free on success -- unused gas is\n    // returned -- while forwarding the EIP-2565 bound on a repriced chain\n    // reverts every proof.\n    //\n    // Liveness caveat: if a future fork reprices these precompiles above the\n    // bounds below, this verifier must be regenerated and redeployed. The\n    // constructor smoke probes forward the same bounds for EVERY precompile\n    // the runtime calls, modexp included, so deployment onto an\n    // already-repriced chain fails fast instead of bricking at proof time.\n    // ----------------------------------------------------------------------\n    uint256 internal constant          G1ADD_GAS = " ++
    toString (ctx.templateConstants.gas.g1add) ++
    ";\n    uint256 internal constant   G1MSM_GAS_1PAIR = " ++
    toString (ctx.templateConstants.gas.g1msmOnePair) ++
    ";\n    uint256 internal constant PAIRING_GAS_2PAIR = " ++
    toString (ctx.templateConstants.gas.pairingTwoPair) ++
    ";\n    uint256 internal constant        MODEXP_GAS = " ++
    toString (ctx.templateConstants.gas.modexp) ++
    ";\n    // Exact cost of the deployment-time worst-case G1MSM smoke probe.\n    uint256 internal constant G1MSM_GAS_SMOKE = " ++
    toString (ctx.constructorG1msmSmokeGas) ++
    ";" ++
    (if ctx.expectedHasAccumulator then "\n    // Worst-case accumulator RHS MSM: carried RHS point plus every generated\n    // fixed-base tail scalar nonzero. Zero tail scalars are omitted at\n    // runtime, which only lowers the actual cost below this bound.\n    uint256 internal constant ACC_RHS_MSM_GAS = " ++
      toString (ctx.accRhsMsmGas) ++
      ";" else "") ++
    "\n\n    /// @notice Build identity for this generated artifact (P10/L-8).\n    /// @dev keccak256 over: the domain tag \"halo2-solidity-verifier-build-v1\",\n    ///      the u64-length-prefixed generator feature profile, the vk_digest,\n    ///      the expected VK runtime codehash (zero when the VK is embedded),\n    ///      the SRS fingerprint keccak(\"halo2-solidity-verifier-srs-v1\" || n\n    ///      || G2 || s_g2 || [tau]G1), and an optional 32-byte deployment\n    ///      provenance tag (0x00 marker when absent, 0x01 || tag when set).\n    ///      The deployment record must publish these preimage components so\n    ///      third parties can recompute the id; see\n    ///      docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md.\n    bytes32 public constant BUILD_ID = " ++
    hexPaddedFilter 64 (ctx.buildId.toNat) ++
    ";\n\n    // ----------------------------------------------------------------------\n    // Typed-error selectors (P4/L-3): bytes4(keccak256(\"Name()\")) of the\n    // errors declared on the contract, as Yul-readable constants. The\n    // `fail(sel)` helper in AssemblyHelpers.yul writes the selector to\n    // scratch 0x00 and reverts with 4 bytes. Pinned by\n    // `p4_error_selectors_match_declared_errors` in src/lowering/tests.rs.\n    // ----------------------------------------------------------------------\n    uint256 internal constant ERR_BAD_CALLDATA_SHAPE      = 0x1b99e37c;\n    uint256 internal constant ERR_VK_MISMATCH             = 0xa447d73e;\n    uint256 internal constant ERR_NON_CANONICAL_SCALAR    = 0x77530042;\n    uint256 internal constant ERR_BAD_POINT_ENCODING      = 0xf27905ec;\n    uint256 internal constant ERR_PRECOMPILE_FAILED       = 0x84e81692;\n    uint256 internal constant ERR_PROOF_REJECTED          = 0xc3b0d8cd;\n    uint256 internal constant ERR_QUOTIENT_PROGRAM_INVALID = 0x3cc81b89;\n    uint256 internal constant ERR_MEMORY_LAYOUT_VIOLATED   = 0xc9888d23;\n\n    // BLS12-381 scalar-field modulus, used for transcript challenges and all\n    // Halo2 verifier arithmetic.\n    uint256 internal constant FR_MODULUS        = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;\n\n    // BLS12-381 Fp modulus minus one, split like an EIP-2537 coordinate:\n    // high word = 16 zero bytes || top 16 coordinate bytes, low word =\n    // bottom 32 coordinate bytes.\n    uint256 internal constant BLS_P_HI             = 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7;\n    uint256 internal constant BLS_P_MINUS_ONE_LO   = 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    // Packed public-accumulator sentinels for the shifted coordinate codec.\n    // The `_WITH_ID_FLAG` variant is used only for the first x-coordinate word.\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0 = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_1 = 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84;" ++
    (match ctx.quotientDirect with 
    | some qdirect =>
      (jinjaFor qdirect.constants (fun line loop => "\n    " ++
        line))
    | none =>
      "")

/-- rust: the Askama expansion of T:partials/verifier/PrecompileSmoke.sol (216
    template lines at HEAD). Deployed render: D:308-523, 14,414 bytes, 216 lines
    - the ONLY one of the six with no control-flow tag at all, so every template
    line survives and the render is 216 lines of text with 27 interpolations.
    scripts/check_golden_provenance.py already anchors its :357 slice into the
    artifact as the `smoke` golden fixture; constants_smokeProbesPresent_ok is
    the render-side half of that. The two memory slots it reads
    (constructor_smoke_scratch_mptr, constructor_g1msm_smoke_scratch_mptr) and
    constructor_g1msm_smoke_input_bytes are the ones no earlier partial touches,
    so this is the only place in the tree where they are gated. -/
def renderPrecompileSmoke (ctx : PartialCtx) : String :=   "    /// @notice Smoke-check the Cancun/EIP-2537/modexp runtime features required by the verifier.\n    /// @dev Exercises MCOPY, modexp, and EIP-2537 inputs to catch incompatible chain/fork configurations at deployment.\n    ///      The probes forward the same exact gas bounds the runtime uses, for\n    ///      every precompile it calls -- 0x05 modexp included (see the\n    ///      gas-bound constants block) -- so a chain whose precompile schedule\n    ///      was repriced above those bounds fails here, at deployment, instead\n    ///      of bricking verifyProof later.\n    function require_eip2537_precompiles() private view {\n        assembly (\"memory-safe\") {\n               // Same free-memory-pointer guard as verifyProof, typed for the\n            // same reason: a build fault must fail the DEPLOYMENT, not the\n            // first proof. The smoke probes below keep bare reverts (a\n            // chain-capability failure, which the transaction identifies).\n            if gt(mload(0x40), " ++
    hexFilter (ctx.memory.constructorSmokeScratchMptr) ++
    ") {\n                mstore(0x00, shl(224, ERR_MEMORY_LAYOUT_VIOLATED))\n                revert(0x00, 0x04)\n            }\n\n            // Scratch is reused for every runtime-prerequisite probe.\n            let scratch := " ++
    hexFilter (ctx.memory.constructorSmokeScratchMptr) ++
    "\n\n            // MCOPY must be available because the verifier uses it for\n            // proof-time point/scratch staging. Execute the opcode here so a\n            // non-Cancun fork fails during deployment instead of later proofs.\n            mstore(scratch, 0x1234)\n            mcopy(add(scratch, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    "), scratch, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")\n            if iszero(eq(mload(add(scratch, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")), 0x1234)) { revert(0, 0) }\n\n            // ----------------------------------------------------------------\n            // modexp (0x05) known-answer probe at the pinned runtime bound.\n            //\n            // MF-1: every other precompile the runtime calls was probed here,\n            // but modexp -- which the MANDATORY Lagrange batch inversion and\n            // every scalar_inv call depend on -- was not. Two live schedules\n            // price this frame differently (EIP-2565: 1360, EIP-7883: 4080),\n            // and a bound below the chain's price does not degrade: the\n            // staticcall forwards a fixed amount, the precompile OOGs, and\n            // EVERY proof reverts PrecompileFailed. Without this probe that\n            // failure is invisible until the first verifyProof call, on a\n            // contract that deployed cleanly.\n            //\n            // The vector is the runtime's own operation -- Fermat inversion\n            // in Fr -- so it exercises the exact frame shape, exponent width,\n            // and gas bound used at proof time: 2^(FR_MODULUS - 2) == 2^-1.\n            // Checking mulmod(result, 2, FR_MODULUS) == 1 rather than a\n            // rendered constant keeps the probe self-contained while still\n            // rejecting a stub: a precompile returning zeros (or its input)\n            // fails, since 0 * 2 != 1 mod r.\n            // ----------------------------------------------------------------\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.baseLenOffset) ++
    "), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")        // base len\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.expLenOffset) ++
    "), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")        // exp len\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.modLenOffset) ++
    "), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")        // mod len\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.baseOffset) ++
    "), 2)\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.expOffset) ++
    "), sub(FR_MODULUS, 2))\n            mstore(add(scratch, " ++
    hexFilter (ctx.templateConstants.modexp.modOffset) ++
    "), FR_MODULUS)\n            if iszero(staticcall(MODEXP_GAS, " ++
    hexFilter (ctx.templateConstants.modexp.address) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.modexp.frameBytes) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.modexp.outputBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.modexp.outputBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(mulmod(mload(scratch), 2, FR_MODULUS), 1)) { revert(0, 0) }\n\n            // Start the EIP-2537 probes with the identity encoding for G1/G2:\n            // all-zero padded words. This also clears the modexp frame above.\n            for { let off := 0 } lt(off, " ++
    hexFilter (ctx.templateConstants.eip2537.smokeScratchBytes) ++
    ") { off := add(off, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ") } {\n                mstore(add(scratch, off), 0)\n            }\n\n            // G1ADD(identity, identity) -> identity, 128-byte return.\n            // This catches chains where the precompile is missing or returns a\n            // non-standard success shape.\n            if iszero(staticcall(G1ADD_GAS, " ++
    hexFilter (ctx.templateConstants.eip2537.g1addAddress) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.g1addInputBytes) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {\n                revert(0, 0)\n            }\n\n            // Known-answer probe: G1ADD(G, G) == 2G.\n            //\n            // Every probe above uses the point at infinity, which is exactly\n            // the input an implementation gets right without doing any curve\n            // arithmetic -- a precompile that returns its zero-filled input, or\n            // zeros for anything, satisfies them. The identity is also the one\n            // input on which an implementation that omits the EIP-2537 subgroup\n            // check still answers correctly, and the production verifier leans\n            // on G1MSM as its subgroup validator for absorbed commitments. So\n            // add one vector whose answer a stub cannot guess.\n            mstore(add(scratch, 0x00), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1Generator.xHi.toNat) ++
    ")\n            mstore(add(scratch, 0x20), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1Generator.xLo.toNat) ++
    ")\n            mstore(add(scratch, 0x40), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1Generator.yHi.toNat) ++
    ")\n            mstore(add(scratch, 0x60), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1Generator.yLo.toNat) ++
    ")\n            mcopy(add(scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    "), scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")\n            if iszero(staticcall(G1ADD_GAS, " ++
    hexFilter (ctx.templateConstants.eip2537.g1addAddress) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.g1addInputBytes) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(and(\n                and(\n                    eq(mload(add(scratch, 0x00)), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1DoubleGenerator.xHi.toNat) ++
    "),\n                    eq(mload(add(scratch, 0x20)), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1DoubleGenerator.xLo.toNat) ++
    ")\n                ),\n                and(\n                    eq(mload(add(scratch, 0x40)), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1DoubleGenerator.yHi.toNat) ++
    "),\n                    eq(mload(add(scratch, 0x60)), " ++
    hexPaddedFilter 64 (ctx.templateConstants.eip2537.g1DoubleGenerator.yLo.toNat) ++
    ")\n                )\n            )) { revert(0, 0) }\n\n\n            // ----------------------------------------------------------------\n            // Known-answer probes for the two precompiles that actually decide\n            // acceptance.\n            //\n            // Every probe above this point uses the point at infinity or a\n            // G1ADD vector. That leaves the two precompiles the verifier's\n            // security actually rests on untested for *rejection* behaviour:\n            //   - 0x0c G1MSM is the curve/subgroup validator for every absorbed\n            //     proof commitment (common_uncompressed_g1 runs no curve check);\n            //   - 0x0f PAIRING_CHECK is the sole accept gate, so a chain whose\n            //     0x0f always returns 1 accepts every proof.\n            // These four probes cost deployment gas only.\n            // ----------------------------------------------------------------\n\n            // (a) G1MSM known answer: [2]*G == 2G.\n            mstore(add(scratch, 0x00), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)\n            mstore(add(scratch, 0x20), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)\n            mstore(add(scratch, 0x40), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)\n            mstore(add(scratch, 0x60), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)\n            mstore(add(scratch, 0x80), 2)\n            if iszero(staticcall(G1MSM_GAS_1PAIR, " ++
    hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++
    ", scratch, 0xa0, scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(and(\n                and(\n                    eq(mload(add(scratch, 0x00)), 0x000000000000000000000000000000000572cbea904d67468808c8eb50a9450c),\n                    eq(mload(add(scratch, 0x20)), 0x9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e)\n                ),\n                and(\n                    eq(mload(add(scratch, 0x40)), 0x00000000000000000000000000000000166a9d8cabc673a322fda673779d8e38),\n                    eq(mload(add(scratch, 0x60)), 0x22ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28)\n                )\n            )) { revert(0, 0) }\n\n            // (b) G1MSM negative probe. (4, y) satisfies y^2 = x^3 + 4 over Fp\n            // but is NOT in the r-order subgroup (checked off-chain: r*P != O).\n            // EIP-2537 requires G1MSM to reject it. This is the one property\n            // the verifier's deferred-validation strategy depends on and the\n            // one property no other probe exercises.\n            //\n            // Gas is bounded on purpose: a precompile that rejects its input\n            // consumes everything forwarded to it, so an unbounded `gas()` here\n            // would burn 63/64 of the deployment gas before the probes below.\n            mstore(add(scratch, 0x00), 0x0000000000000000000000000000000000000000000000000000000000000000)\n            mstore(add(scratch, 0x20), 0x0000000000000000000000000000000000000000000000000000000000000004)\n            mstore(add(scratch, 0x40), 0x000000000000000000000000000000000a989badd40d6212b33cffc3f3763e9b)\n            mstore(add(scratch, 0x60), 0xc760f988c9926b26da9dd85e928483446346b8ed00e1de5d5ea93e354abe706c)\n            mstore(add(scratch, 0x80), 1)\n            if staticcall(200000, " ++
    hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++
    ", scratch, 0xa0, scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ") { revert(0, 0) }\n\n            // (c)+(d) Pairing known answers. Lay out [G1 | G2 | G1' | G2] once:\n            // with G1' = -G the product is 1, with G1' = +G it is not. G2 is\n            // written literally because the VK payload is not loaded during\n            // construction.\n            mstore(add(scratch, 0x000), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)\n            mstore(add(scratch, 0x020), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)\n            mstore(add(scratch, 0x040), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)\n            mstore(add(scratch, 0x060), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)\n            mstore(add(scratch, 0x080), 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)\n            mstore(add(scratch, 0x0a0), 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)\n            mstore(add(scratch, 0x0c0), 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)\n            mstore(add(scratch, 0x0e0), 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)\n            mstore(add(scratch, 0x100), 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)\n            mstore(add(scratch, 0x120), 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)\n            mstore(add(scratch, 0x140), 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)\n            mstore(add(scratch, 0x160), 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)\n            mstore(add(scratch, 0x180), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)\n            mstore(add(scratch, 0x1a0), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)\n            mstore(add(scratch, 0x1c0), 0x00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f2)\n            mstore(add(scratch, 0x1e0), 0x67816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca)\n            mcopy(add(scratch, 0x200), add(scratch, 0x80), 0x100)\n\n            // (c) e(G, G2) * e(-G, G2) == 1.\n            if iszero(staticcall(PAIRING_GAS_2PAIR, " ++
    hexFilter (ctx.templateConstants.eip2537.pairingAddress) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.pairingTwoPairBytes) ++
    ", add(scratch, 0x300), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(mload(add(scratch, 0x300)), 1)) { revert(0, 0) }\n\n            // (d) e(G, G2) * e(G, G2) != 1. Flip the second G1 back to +G.\n            mstore(add(scratch, 0x1c0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)\n            mstore(add(scratch, 0x1e0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)\n            if iszero(staticcall(PAIRING_GAS_2PAIR, " ++
    hexFilter (ctx.templateConstants.eip2537.pairingAddress) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.pairingTwoPairBytes) ++
    ", add(scratch, 0x300), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(iszero(mload(add(scratch, 0x300)))) { revert(0, 0) }\n\n            // Restore the identity encoding for the probes below.\n            for { let off := 0 } lt(off, " ++
    hexFilter (ctx.templateConstants.eip2537.smokeScratchBytes) ++
    ") { off := add(off, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ") } {\n                mstore(add(scratch, off), 0)\n            }\n\n            // Worst-case generated G1MSM with all identity/zero terms ->\n            // identity, 128-byte return. This exercises the largest MSM input\n            // length rendered by this verifier instead of only a one-pair\n            // smoke call.\n            let msm_scratch := " ++
    hexFilter (ctx.memory.constructorG1msmSmokeScratchMptr) ++
    "\n            for { let off := 0 } lt(off, " ++
    hexFilter (ctx.constructorG1msmSmokeInputBytes) ++
    ") { off := add(off, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ") } {\n                mstore(add(msm_scratch, off), 0)\n            }\n            // The production verifier uses G1MSM both for commitments and as\n            // the subgroup validator for absorbed proof points.\n            if iszero(staticcall(G1MSM_GAS_SMOKE, " ++
    hexFilter (ctx.templateConstants.eip2537.g1msmAddress) ++
    ", msm_scratch, " ++
    hexFilter (ctx.constructorG1msmSmokeInputBytes) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.g1Bytes) ++
    ")) { revert(0, 0) }\n            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {\n                revert(0, 0)\n            }\n\n            // PAIRING_CHECK([(identity_g1, identity_g2), (identity_g1, identity_g2)])\n            // -> true, 32-byte return. This matches the runtime two-pair KZG\n            // pairing input size and catches absent pairing precompiles,\n            // short return data, and obviously incompatible semantics.\n            if iszero(staticcall(PAIRING_GAS_2PAIR, " ++
    hexFilter (ctx.templateConstants.eip2537.pairingAddress) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.pairingTwoPairBytes) ++
    ", scratch, " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(returndatasize(), " ++
    hexFilter (ctx.templateConstants.wordBytes) ++
    ")) { revert(0, 0) }\n            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }\n        }\n    }"

/-- rust: the Askama expansion of T:partials/verifier/Constructors.sol (92 template
    lines at HEAD). Deployed render: D:525-540, 733 bytes, 16 lines. Four nested
    matches give four shapes; the deployed profile takes expected_vk_codehash =
    Some, quotient_external = None, so it emits the single-address constructor at
    :41-55 and NOTHING else - the two `when Some with (_)` arms of the inner
    expected_quotient_codehash matches at :35-38 and :78-81 are EMPTY arms in the
    template, ported as empty strings so the arm structure is visible. The render
    opens with a newline, which is what makes D:525 whitespace-only. -/
def renderConstructors (ctx : PartialCtx) : String :=   (match ctx.expectedVkCodehash with 
    | some _ =>
      (match ctx.quotientExternal with 
      | some _ =>
        "\n    /// @notice Create a verifier pinned to a verifying key and quotient evaluator.\n    /// @dev Checks MCOPY/EIP-2537 availability and verifies both dependency runtimes before storing their addresses.\n    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.\n    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.\n    constructor(address authorizedVk, address authorizedQuotient) {\n        // Verifier correctness depends on chain support for MCOPY and the\n        // BLS12-381 precompiles; fail deployment before pinning dependencies.\n        require_eip2537_precompiles();\n        // Pin the generated VK runtime exactly. The verifier later repeats the\n        // codehash/length check before copying the VK payload for a proof.\n        require(\n            authorizedVk.code.length == EXPECTED_VK_LENGTH\n                && authorizedVk.codehash == EXPECTED_VK_CODEHASH,\n            \"invalid vk\"\n        );" ++
        (match ctx.expectedQuotientCodehash with 
        | some _ =>
          "\n        // The split evaluator contains generated verifier logic, not a generic\n        // library. Pin it with the same strictness as the verifying key.\n        require(\n            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH\n                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,\n            \"invalid quotient\"\n        );"
        | none =>
          "") ++
        "\n        // Store the already-validated dependency addresses for proof-time\n        // memory loading and quotient reconstruction.\n        AUTHORIZED_VK = authorizedVk;\n        AUTHORIZED_QUOTIENT = authorizedQuotient;" ++
        (match ctx.expectedQuotientCodehash with 
        | some _ =>
          ""
        | none =>
          "") ++
        "\n    }"
      | none =>
        "\n    /// @notice Create a verifier pinned to a generated verifying key.\n    /// @dev Checks MCOPY/EIP-2537 availability and verifies the VK runtime before storing its address.\n    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.\n    constructor(address authorizedVk) {\n        // Embedded quotient path: only the external VK runtime needs to be\n        // pinned, but the runtime opcode/precompile prerequisites are still\n        // mandatory.\n        require_eip2537_precompiles();\n        require(\n            authorizedVk.code.length == EXPECTED_VK_LENGTH\n                && authorizedVk.codehash == EXPECTED_VK_CODEHASH,\n            \"invalid vk\"\n        );\n        AUTHORIZED_VK = authorizedVk;\n    }")
    | none =>
      (match ctx.quotientExternal with 
      | some _ =>
        "\n    /// @notice Create a verifier pinned to a quotient evaluator.\n    /// @dev Used when the VK is embedded in the verifier but quotient reconstruction is split out.\n    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.\n    constructor(address authorizedQuotient) {\n        // Embedded VK path: the verifier bytecode carries the VK payload, but\n        // the runtime prerequisites and external quotient evaluator still\n        // need to be checked before storing the dependency address.\n        require_eip2537_precompiles();" ++
        (match ctx.expectedQuotientCodehash with 
        | some _ =>
          "\n        require(\n            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH\n                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,\n            \"invalid quotient\"\n        );"
        | none =>
          "") ++
        "\n        AUTHORIZED_QUOTIENT = authorizedQuotient;" ++
        (match ctx.expectedQuotientCodehash with 
        | some _ =>
          ""
        | none =>
          "") ++
        "\n    }"
      | none =>
        "\n    /// @notice Create a verifier with embedded verifier data.\n    /// @dev Checks MCOPY/EIP-2537 availability at deployment.\n    constructor() {\n        // Fully embedded verifier: no external generated dependency exists,\n        // so deployment only checks runtime opcode/precompile availability.\n        require_eip2537_precompiles();\n    }"))

/-- rust: the Askama expansion of T:partials/verifier/TraceAndGasHelpers.yul (23
    template lines at HEAD). THE DEPLOYED RENDER IS THE EMPTY STRING: both of its
    ifs (`self.trace` at :1-13, `self.gas_checkpoints` at :14-23) are false in the
    release profile and every byte of the file is inside one of them. Contracts.lean
    gate 9 already PROVES that from the artifact - the run between the
    AccumulatorHelpers render and the two hoisted locals is exactly the include
    glue, so there is no room for a byte of this partial. A byte gate on an empty
    string would pin nothing (hazard 2), so gate 74 is STRUCTURAL and SYNTHETIC and
    says so: it pins that the two arms exist, that each flag selects its own arm,
    and that the deployed render is zero-length. -/
def renderTraceAndGasHelpers (ctx : PartialCtx) : String :=   (if ctx.trace then "\n            // Trace builds emit u256 values through a planned scratch slot.\n            // The topic is the stable trace ID used by Rust/Solidity fixture\n            // comparison; the data word is the observed scalar.\n            function trace_u256(id, value) {\n                mstore(TRACE_U256_MPTR, value)\n                log1(TRACE_U256_MPTR, 0x20, id)\n            }\n            // Trace G1 points as their 128-byte EIP-2537 memory slot.\n            function trace_point(id, mptr) {\n                log1(mptr, 0x80, id)\n            }" else "") ++
    (if ctx.gasCheckpoints then "\n            // Section-boundary gas-attribution checkpoint. Emits a\n            // single LOG1 (no data) with topic = (id << 248) | gas().\n            // Cost: 375 (LOG base) + 375 (1 topic) = 750 gas/call.\n            // Host-side parses the topic into (id, gas_left) and prints\n            // pairwise deltas (see `dump_gas_checkpoints`).\n            function gas_checkpoint(id) {\n                log1(0, 0, or(shl(248, id), gas()))\n            }" else "")

/-- rust: the Askama expansion of T:partials/verifier/Pcs.yul (39 template lines at
    HEAD). Deployed render: D:2583-2980, 23,311 bytes, 398 lines - the largest of
    the six, and the only one whose bytes are mostly NOT the template's: the outer
    for at :12-24 emits `pcs_computations`, the multi-prepare lowering pass's
    output (M:595, `Vec&lt;Vec&lt;String&gt;`), which is P-09/P-10's territory and is not
    ported. So the blocks are a PARAMETER, exactly as P-13c made the two
    quotient_numerator includes parameters of renderQuotientAndLinearization:
    generated bytes are an argument, never a paste. Unlike the quotient's four
    FLAT lists, the block partition here IS observable - each block gets its own
    `{ ... }` wrapper and its own numbered comment - so the byte gate pins that
    there are eight blocks and which lines belong to which.

    HAZARD 3, the regions a later `pcs_spec` would induct over: (1) the banner
    :1-10, fixed text; (2) the outer block `{` ... `}` :11-25, one generated
    sub-block per iteration of the for at :12; (3) inside each sub-block, the
    generated lines themselves, which are opaque strings to this port; (4) the
    gas-checkpoint interleave at :21-23, which is where a per-block induction
    hypothesis would live; (5) the trace tail :27-39. The DEPLOYED render is NOT
    expressible as a single `Yul.Block` under D-P13's structural identity: the
    generated lines are Strings, not parsed statements, and the region is a
    sequence of eight sibling blocks inside one enclosing `{ }` with no bindings
    declared at the outer level - so the honest structural statement is per
    sub-block, not per partial. Gate 75 therefore gates the TEMPLATE's structure
    (banner, brace nesting, block count) against the artifact and leaves the
    contents opaque; a `pcs_spec` proof would induct over the parameter list.
    scripts/check_golden_provenance.py's `pcsBasis` fixture already pins 30 lines
    of the generated region (D:2744-2773) as a golden slice, so the parameter is
    not unconstrained either. -/
def renderPcs (ctx : PartialCtx) (pcsComputations : List (List String)) : String :=   "            // ===============================================================\n            // PCS computation (multi-prepare emitter from Step 5).\n            //\n            // The Rust lowering stage has already expanded the KZG multi-open\n            // equation into a sequence of generated Yul sub-blocks. Those\n            // blocks populate:\n            //   - F_EVAL_MPTR / V_MPTR scalar batching values;\n            //   - FINAL_COM_MPTR for the fused commitment MSM;\n            //   - PAIRING_LHS_MPTR and PAIRING_RHS_MPTR for the final pairing.\n            // ===============================================================\n            {" ++
    (jinjaFor pcsComputations (fun codeBlock loop => "\n                // Generated PCS sub-block " ++
      toString (loop.index) ++
      ". These lines are\n                // emitted by the multi-prepare lowering pass and are kept\n                // grouped so gas checkpoints can attribute their cost.\n                {" ++
      (jinjaFor codeBlock (fun line loop => "\n                    " ++
        line)) ++
      "\n                }" ++
      (if ctx.gasCheckpoints && ! loop.last then "\n                gas_checkpoint(" ++
        toString (17 + loop.index0) ++
        ") // after PCS sub-block " ++
        toString (loop.index) else ""))) ++
    "\n            }" ++
    (if ctx.gasCheckpoints then "\n            gas_checkpoint(14) // after PCS computation block (= sub-block 6)" else "") ++
    (if ctx.trace then "\n            // Trace the final pairing inputs and selector accumulator buckets\n            // after PCS expansion, matching the Rust verifier trace labels.\n            trace_point(27, PAIRING_LHS_MPTR)\n            trace_point(28, PAIRING_RHS_MPTR)" ++
      (jinjaFor ctx.simpleSelectorCols (fun _ loop => "\n            trace_u256(" ++
        toString (ctx.selectorTraceBase + loop.index0) ++
        ", mload(add(SELECTOR_ACC_MPTR, " ++
        hexFilter (loop.index0 * 32) ++
        ")))")) else "")

/-- rust: the Askama expansion of T:partials/verifier/TraceReturn.yul (73 template
    lines at HEAD). Deployed render: D:3010-3021, 563 bytes, 12 lines - the whole
    of template :55-73's else arm plus the two newlines the `{% if %}` at :55
    leaves behind, which is what makes D:3010 whitespace-only. The trace block at
    :1-53 zero-renders, so 53 of the 73 template lines are absent from the
    artifact.

    HAZARD 3, the regions a later `traceReturn_spec` would induct over: (1) the
    trace-emission block :1-53, itself split into the fixed header (:5-10), the
    user-phase challenge loop (:11-15, a nested for over user_phases x
    0..num_challenges), the fixed challenge tail (:16-21), the num_trashcans
    guard (:21-23), the fixed scratch tail (:24-48) and the accumulator guard
    (:49-52); and (2) the TERMINAL ARM CHOICE at :55-73, which is the whole
    semantic content of this partial for the deployed profile: trace renders
    `return(RETURN_MPTR, 0x20)` with `iszero(iszero success)`, production renders
    `if iszero(success) { fail(ERR_PROOF_REJECTED) }` and then return 1. That is
    expressible as a Yul.Block under D-P13's structural identity for the DEPLOYED
    arm - three statements, no bindings, all identifiers in scope from the
    enclosing block - and gate 76 says so by tokenising the render against a
    hand-written `yul%` block. The trace arm is NOT: it references `success`,
    `r` and the MPTR constants from the enclosing frame and its content depends on
    the phase loop, so a spec for it would state a relation over the emission
    sequence rather than a standalone block. -/
def renderTraceReturn (ctx : PartialCtx) : String :=   (if ctx.trace then "\n            // Terminal trace emission. IDs are intentionally stable across\n            // generated verifiers so fixture tooling can diff Rust and\n            // Solidity executions without understanding a particular circuit.\n            trace_u256(1,  mload(VK_DIGEST_MPTR))\n            trace_u256(2,  " ++
      toString (ctx.numInstances) ++
      ")\n            trace_u256(3,  " ++
      toString (ctx.k) ++
      ")\n            trace_u256(4,  mload(N_INV_MPTR))\n            trace_u256(5,  mload(OMEGA_MPTR))\n            trace_u256(6,  mload(OMEGA_INV_MPTR))" ++
      (jinjaFor ctx.userPhases (fun phase loop => (jinjaFor (List.range phase.numChallenges) (fun j loop => "\n            trace_u256(" ++
          toString (1000 + phase.challengeOffset + j) ++
          ", mload(add(CHALLENGE_MPTR, " ++
          hexFilter ((phase.challengeOffset + j) * 32) ++
          ")))")))) ++
      "\n            trace_u256(7,  mload(THETA_MPTR))\n            trace_u256(8,  mload(BETA_MPTR))\n            trace_u256(9,  mload(GAMMA_MPTR))\n            trace_u256(10, mload(Y_MPTR))\n            trace_u256(11, mload(X_MPTR))" ++
      (if ctx.numTrashcans != 0 then "\n            trace_u256(12, mload(TRASH_CHALLENGE_MPTR))" else "") ++
      "\n            trace_u256(13, mload(X1_MPTR))\n            trace_u256(14, mload(X2_MPTR))\n            trace_u256(15, mload(X3_MPTR))\n            trace_u256(16, mload(X4_MPTR))\n            trace_u256(17, mload(X_N_MPTR))\n            trace_u256(18, mload(X_N_MINUS_1_INV_MPTR))\n            trace_u256(19, mload(L_LAST_MPTR))\n            trace_u256(20, mload(L_BLIND_MPTR))\n            trace_u256(21, mload(L_0_MPTR))\n            trace_u256(22, mload(INSTANCE_EVAL_MPTR))\n            trace_u256(23, mload(QUOTIENT_EVAL_MPTR))\n            // Rust traces often print the positive numerator; the verifier\n            // stores the negated expected scalar for the linearized opening.\n            trace_u256(36, addmod(0, sub(r, mload(QUOTIENT_EVAL_MPTR)), r))\n            // QUOTIENT_MPTR carries scalar metadata in the fused production\n            // path. Zero the unused point words before tracing it as a G1 slot.\n            mstore(add(QUOTIENT_MPTR, 0x40), 0)\n            mstore(add(QUOTIENT_MPTR, 0x60), 0)\n            trace_point(24, QUOTIENT_MPTR)\n            trace_point(25, F_COM_MPTR)\n            trace_point(26, PI_MPTR)\n            trace_u256(31, mload(F_EVAL_MPTR))\n            trace_u256(32, mload(V_MPTR))\n            trace_point(33, FINAL_COM_MPTR)\n            trace_u256(35, success)" ++
      (if ctx.expectedHasAccumulator then "\n            trace_point(29, ACC_LHS_MPTR)\n            trace_point(30, ACC_RHS_MPTR)" else "") else "") ++
    "\n\n            " ++
    (if ctx.trace then "// Trace renders return the final check result (`true` for an\n            // accepted proof, `false` when the final pairing / accumulated\n            // checks failed) instead of reverting, so the LOG1 trace events\n            // above are kept. Early calldata / encoding failures still revert.\n            mstore(RETURN_MPTR, iszero(iszero(success)))\n            return(RETURN_MPTR, 0x20)" else "// Success path is terminal. Invalid inputs have already reverted,\n            // so the Solidity ABI observes `true`.\n            //\n            // The guard is redundant today -- every failure path above reverts\n            // rather than clearing `success` -- but it keeps acceptance a local\n            // property of this file instead of an invariant split across\n            // FinalPairing.yul and ec_pairing.\n            if iszero(success) { fail(ERR_PROOF_REJECTED) }\n            mstore(RETURN_MPTR, 1)\n            return(RETURN_MPTR, 0x20)")

/-! ## Gates

Twenty-eight gates here (P-13a), plus eighteen from P-13b after them (29-46). Gate 1 is the reachability gate D-P19 demands before any
section that reads files, so a wrong path is a named red rather than a needle
that matches nothing. Gates 2-6 are the TEXTUAL ones (hazard 1): the rendered
bytes must occur exactly once in the tracked dump with the include boundary on
both sides. Gates 7-8 pin each Jinja filter the five partials use against an
artifact (hazard 2). Gates 9-10 pin the newline law and the indent boundary.
Gates 11-13 answer hazards 3 and 4. Gate 14 is the anti-self-fulfilment check
that re-derives every profile input from the artifact. Gates 15-19 are the
STRUCTURAL ones (D-P13): they tie the rendered bytes to a vendored AST, and they
are NOT byte gates. Gates 20-26 are the R-41 perturbations, run inside the scope
of the gates they attack; gates 27-28 are the two perturbation classes that
provably CANNOT redden, asserted as inertness/absorption rather than hidden. -/

namespace VerifierPartialKats

open Midfall.Generator YulSemantics

/-- Occurrences of needle in hay: n occurrences leave n + 1 pieces. -/
def occ (hay needle : String) : Nat := (hay.splitOn needle).length - 1

/-- needle occurs in hay exactly once. -/
def occursOnce (hay needle : String) : Bool := occ hay needle == 1

/-- Delete the first occurrence of needle (all later ones are put back). -/
def deleteFirst (s needle : String) : String :=
  match s.splitOn needle with
  | a :: rest => a ++ String.intercalate needle rest
  | [] => s

/-- Insert ins after the first occurrence of needle. -/
def insertAfterFirst (s needle ins : String) : String :=
  match s.splitOn needle with
  | a :: rest => a ++ needle ++ ins ++ String.intercalate needle rest
  | [] => s

/-- The include boundary, both sides. T:contracts/Halo2Verifier.sol indents every
    include line with four spaces and separates consecutive includes with one
    blank line (:201-229), so a partial's bytes are preceded by LF + four spaces
    and followed by LF LF + four spaces. -/
def includeBoundary (sol render : String) : Bool :=
  match sol.splitOn render with
  | [before, after] => before.endsWith "\n    " && after.startsWith "\n\n    "
  | _ => false

/-- The artifact match the perturbation gates use: the render occurs exactly once
    and the include boundary FOLLOWS it. The before-side is excluded because
    QuotientAndLinearization's own bytes begin after the two quotient includes,
    so its predecessor is P-13c's text, not the contract template's four spaces;
    includeIndentBoundary_ok covers the before-side for the four partials where
    it is the contract template. -/
def artifactMatch (sol render : String) : Bool :=
  match sol.splitOn render with
  | [_before, after] => after.startsWith "\n\n    "
  | _ => false

/-- One space removed from every " := " - an interior whitespace site, which is
    where the byte gate is actually sensitive (see the leading-whitespace note on
    perturb_leadingWhitespaceAbsorbed_note). -/
def shrinkAssignSpaces (s : String) : String := String.replace s " := " " :="

/-- Delete the LAST newline: the final two lines fuse. -/
def deleteLastNewline (s : String) : String :=
  match (s.splitOn "\n").reverse with
  | a :: rest => String.intercalate "\n" rest.reverse ++ a
  | [] => s

/-- A line that is whitespace but not empty: what a zero-render tag leaves behind
    if its newline is not removed. -/
def hasWsOnlyLine (s : String) : Bool :=
  (s.splitOn "\n").any fun l => l.length > 0 && l.toList.all (fun c => c == ' ')

def lineCount (s : String) : Nat := (s.splitOn "\n").length

def vkDumpCandidates : List String :=
  ["../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2VerifyingKey.sol",
   "proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2VerifyingKey.sol"]

def templateDirCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/verifier/",
   "proofs/solidity-verifier/templates/partials/verifier/"]

/-- The tracked rendered artifact, read at #eval time (D-P19). -/
def readDump : IO String := EvmKats.readGeneratedVerifier

def readVkDump : IO String := EvmKats.readFirst vkDumpCandidates

def readTemplate (name : String) : IO String :=
  EvmKats.readFirst (templateDirCandidates.map fun d => d ++ name)

/-- The deployed renders, once. Five landed with P-13a; P-13b added the transcript
    parser and the accumulator helpers, so the whitespace perturbation gates 20-22
    below now bite seven renders rather than five. -/
def deployedRenders : List String :=
  [renderAssemblyHelpers poseidonCtx, renderVkLoading poseidonCtx, renderLagrange poseidonCtx,
   renderQuotientAndLinearization poseidonCtx "" "", renderFinalPairing poseidonCtx,
   renderTranscriptProofParser poseidonCtx, renderAccumulatorHelpers poseidonCtx]

/-- GATE 1 (reachability, first). The tracked artifact and the template sources
    must open, so a wrong path is a named red and not a silent needle miss. -/
def artifactsReachable_ok : IO Bool :=
  readDump >>= fun sol =>
  readVkDump >>= fun dvk =>
  readTemplate "AssemblyHelpers.yul" >>= fun ah =>
  readTemplate "FinalPairing.yul" >>= fun fp =>
  pure (EvmKats.generatedReadOk sol && dvk.length > 20000 && ah.length > 10000 && fp.length > 3000)

/-- GATE 2 (TEXTUAL, hazard 1). AssemblyHelpers.yul renders byte-identically to
    D:627-930 (16,223 bytes) and occurs nowhere else. -/
def assemblyHelpers_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderAssemblyHelpers poseidonCtx))

/-- GATE 3 (TEXTUAL). VkLoading.yul renders byte-identically to D:1103-1176 (4,494 bytes). -/
def vkLoading_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderVkLoading poseidonCtx))

/-- GATE 4 (TEXTUAL). Lagrange.yul renders byte-identically to D:1497-1586 (4,742 bytes). -/
def lagrange_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderLagrange poseidonCtx))

/-- GATE 5 (TEXTUAL). FinalPairing.yul renders byte-identically to D:2980-3008 (1,546 bytes). -/
def finalPairing_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderFinalPairing poseidonCtx))

/-- GATE 6 (TEXTUAL, with a scope caveat). QuotientAndLinearization.yul's own
    bytes: in the deployed arm the partial renders the two quotient_numerator
    includes and then the linearization block, so with empty include arguments
    the render IS the bytes this partial owns - D:2539-2580, 1,898 bytes. The startsWith pins
    that the match selected the None/None arm (any other arm puts text first),
    and the trailing boundary pins the handoff to Pcs.yul. -/
def quotientAndLinearization_ownBytes_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderQuotientAndLinearization poseidonCtx "" ""
  pure (r.startsWith "\n\n" && occursOnce sol r
    && match sol.splitOn r with
       | [_before, after] => after.startsWith "\n\n    "
       | _ => false)

/-- GATE 7 (hazard 2, the hex filter). Every hex() call site in the five
    partials, rebuilt from the FILTER and searched for in the artifact. If
    hexFilter dropped the odd-nibble pad zero, 0x0100 / 0x0300 / 0x0140 / 0x0120
    would stop matching and this reddens; the values are Lean's own context
    fields, not strings copied from the dump. -/
def hexFilter_sitesMatchArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  let tc := poseidonCtx.templateConstants
  pure (sol.contains ("mstore(add(p, " ++ hexFilter tc.modexp.baseLenOffset ++ "), "
                        ++ hexFilter tc.wordBytes ++ ")        // base len")
    && sol.contains ("let p := " ++ hexFilter poseidonCtx.scalarInvScratchMptr)
    && sol.contains ("let scratch := " ++ hexFilter poseidonCtx.finalPairingScratchMptr)
    && sol.contains ("staticcall(PAIRING_GAS_2PAIR, " ++ hexFilter tc.eip2537.pairingAddress
                        ++ ", scratch, " ++ hexFilter tc.pairingTwoPairBytes ++ ", scratch, "
                        ++ hexFilter tc.wordBytes ++ ")")
    && sol.contains ("let mptr_end := add(mptr, "
                        ++ hexFilter ((poseidonCtx.numInstances + poseidonCtx.numNegLagranges) * 32) ++ ")")
    && sol.contains ("l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, "
                        ++ hexFilter (poseidonCtx.numNegLagranges * 32) ++ ")")
    && sol.contains ("eq(" ++ hexFilter poseidonCtx.proofLen ++ ", calldataload(PROOF_LEN_CPTR))")
    && sol.contains ("eq(calldatasize(), add(INSTANCE_CPTR, "
                        ++ hexFilter (poseidonCtx.numInstances * 32) ++ "))"))

/-- The first payload word of the poseidon VK, as pinned by YulGolden.lean's
    DVK:62-72 fixture (0x4cc2e5ac...), used here only to ask the artifact a
    question about hex_padded(64). -/
def dvkPayloadWord0 : Nat :=
  34720129961312545684992424441958071501550675660370520772129419266726773916820

/-- GATE 8 (hazard 2, the hex_padded filter). hex_padded(64) is NOT reached by
    the deployed verifier profile - it appears only in the embedded-VK arm of
    VkLoading and the external-quotient arm of QuotientAndLinearization, neither
    of which the dump takes - so it is pinned against the OTHER tracked rendered
    artifact, DVK:68, whose offsets use hex_padded(4) and whose words use
    hex_padded(64). -/
def hexPaddedFilter_matchesVkArtifact_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (dvk.contains ("mstore(add(payload, " ++ hexPaddedFilter 4 0 ++ "), "
                        ++ hexPaddedFilter 64 dvkPayloadWord0 ++ ")")
    && dvk.contains ("mstore(add(payload, " ++ hexPaddedFilter 4 32 ++ "), "
                        ++ hexPaddedFilter 64 1 ++ ")"))

/-- GATE 9 (hazard 1, the newline law). Line counts of the five deployed renders,
    no whitespace-only line anywhere, and zero gas_checkpoint text in either the
    renders or the artifact: every {% if self.gas_checkpoints %} renders zero
    times and takes its newline with it. VkLoading drops 67 of its 141 template
    lines, FinalPairing 63 of 92 - a port that kept the control lines' newlines
    would show up here as extra blank lines before the byte gates even ran. -/
def zeroRenderNewlineLaw_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (lineCount (renderAssemblyHelpers poseidonCtx) == 304
    && lineCount (renderVkLoading poseidonCtx) == 74
    && lineCount (renderLagrange poseidonCtx) == 90
    && lineCount (renderQuotientAndLinearization poseidonCtx "" "") == 42
    && lineCount (renderFinalPairing poseidonCtx) == 29
    && ! (deployedRenders.any hasWsOnlyLine)
    && occ sol "gas_checkpoint" == 0
    && ! (deployedRenders.any fun r => r.contains "gas_checkpoint"))

/-- GATE 10 (hazard 1, the indent boundary). The four spaces of the include line
    land on the partial's first line, so the artifact shows 16 spaces where the
    template has 12 - Lagrange.yul:1 vs D:1497 is the clearest case. -/
def includeIndentBoundary_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (List.all [renderAssemblyHelpers poseidonCtx, renderVkLoading poseidonCtx,
                  renderLagrange poseidonCtx, renderFinalPairing poseidonCtx] fun r =>
    match sol.splitOn r with
    | [before, _after] => before.endsWith "\n    "
    | _ => false)

/-- GATE 11 (hazard 3). Which arm FinalPairing takes in the deployed profile:
    expected_has_accumulator is FALSE, so the accumulator-batched block
    (T:FinalPairing.yul:15-61) renders zero times, and its 48 lines / 2,617 bytes are
    absent from the artifact, and trace is FALSE, so the
    else-arm at :86 renders the plain precompile guard and :88 the swapped
    ec_pairing call. Both arms' ranges: acc arm = template lines 15-61 (47
    lines), plain arm = line 86 plus line 88; the trace arm is lines 82-84. -/
def finalPairing_deployedArmIsPlain_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderFinalPairing poseidonCtx
  pure (occ sol r == 1 && ! r.contains "acc_pair_alpha" && ! r.contains "batch_ptr"
    && r.contains "if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }"
    && ! r.contains "Trace renders do not revert")

/-- GATE 12 (hazard 3, the other arm). With the flag flipped the batch block
    renders - 47 template lines of it, with the accumulator offsets and the
    domain tag interpolated - and the result is NOT in the artifact, which is
    what pins the selection. No tracked artifact pins the CONTENT of that arm:
    the dump is a no-accumulator profile, so this gate can only say the bytes
    changed and where they came from. -/
def finalPairing_accumulatorArm_ok : IO Bool :=
  readDump >>= fun sol =>
  let acc := renderFinalPairing { poseidonCtx with expectedHasAccumulator := true }
  pure (acc.contains ("let batch_ptr := " ++ hexFilter poseidonCtx.accumulatorPairingBatchMptr)
    && acc.contains "acc_pair_alpha := mod(keccak256(batch_ptr, "
    && acc.contains "success := staticcall(G1MSM_GAS_1PAIR, "
    && acc.length > (renderFinalPairing poseidonCtx).length + 2000
    && ! occursOnce sol acc)

/-- GATE 13 (hazard 4, the stop-and-report check). P-12's gate 21
    (Calldata.lean decoderAcceptance_g1WordsCanonical_ok) reads
    AssemblyHelpers.yul:94-104 out of the TEMPLATE and asserts the two
    shr(128, ..) guards, the verbatim calldatacopy, and exactly four
    fail(ERR_BAD_POINT_ENCODING). This re-runs those three assertions on MY
    render and ties the render to the template's own lines 94-104 and to the
    artifact. Agreement: the region is pure literal text in the template, so the
    port cannot disagree without a red gate here. -/
def hazard4_decoderRegionAgreesWithP12_ok : IO Bool :=
  readTemplate "AssemblyHelpers.yul" >>= fun t =>
  readDump >>= fun sol =>
  let r := renderAssemblyHelpers poseidonCtx
  let region := String.intercalate "\n" ((t.splitOn "\n").drop 93 |>.take 11)
  pure (region.startsWith "                if shr(128, x_hi_word)"
    && r.contains region && sol.contains region
    && occ r "fail(ERR_BAD_POINT_ENCODING)" == 4
    && occ r "if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }" == 1
    && occ r "if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }" == 1
    && r.contains "calldatacopy(buf_len, cptr, 0x80)")

/-- GATE 14 (anti-self-fulfilment). Every profile input poseidonCtx carries is
    re-read from the dump's OWN lines - the VK header cross-checks, the ABI
    envelope, the Lagrange window, the constant declarations - and the derived
    scratch pointer is checked against Layout.lean:1050's rule rather than
    pasted. Without this the byte gates would be comparing the artifact to
    itself. -/
def poseidonCtx_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (sol.contains ("eq(mload(K_MPTR), " ++ toString poseidonCtx.k ++ ")")
    && sol.contains ("eq(mload(NUM_INSTANCES_MPTR), " ++ toString poseidonCtx.numInstances ++ ")")
    && sol.contains ("eq(" ++ hexFilter poseidonCtx.proofLen ++ ", calldataload(PROOF_LEN_CPTR))")
    && sol.contains ("VK_MPTR = " ++ hashHex poseidonCtx.vkMptr ++ ";")
    && sol.contains ("add(LAGRANGE_DENOMS_MPTR, " ++ hexFilter (poseidonCtx.numNegLagranges * 32) ++ ")")
    && sol.contains ("let mptr_end := add(mptr, "
                        ++ hexFilter ((poseidonCtx.numInstances + poseidonCtx.numNegLagranges) * 32) ++ ")")
    && sol.contains ("let scratch := " ++ hexFilter poseidonCtx.finalPairingScratchMptr)
    && poseidonCtx.scalarInvScratchMptr == poseidonCtx.vkMptr - modexpScratchBytes
    && poseidonCtx.expectedHasAccumulator == false
    && sol.contains "eq(mload(HAS_ACCUMULATOR_MPTR), 0)")

private def varX (s : String) : Expr EVM.Op := .var s
private def binOp (op : EVM.Op) (args : List (Expr EVM.Op)) : Expr EVM.Op := .builtin op args
private def usrFn (nm : String) (args : List (Expr EVM.Op)) : Expr EVM.Op := .call nm args
private def stmtE (e : Expr EVM.Op) : Stmt EVM.Op := .exprStmt e

/-- The deployed FinalPairing arm as the vendored AST. This is the object of P-SE
    proof step P5 (finalPairing_spec): two statements, the plain precompile
    guard and the swapped ec_pairing call. -/
def finalPairing_ast : Block EVM.Op := yul% {
  if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
  success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)
}

/-- The same program with raw constructors. fail is a user function
    (AssemblyHelpers.yul:4) and so is ec_pairing (:269), so both are Expr.call -
    the distinction the token relation cannot make (YulGolden.lean). -/
def finalPairing_direct : Block EVM.Op :=
  [ Stmt.cond (binOp EVM.Op.iszero [varX "success"])
      [stmtE (usrFn "fail" [varX "ERR_PRECOMPILE_FAILED"])]
  , Stmt.assign ["success"]
      (usrFn "ec_pairing" [varX "success", varX "PAIRING_RHS_MPTR", varX "PAIRING_LHS_MPTR"])
  ]

/-- GATE 15 (STRUCTURAL, authoritative). The AST the render's source text
    elaborates to equals the raw-constructor AST under stmtsBeq - the relation
    Phase 5's irCheck will use. This says NOTHING about bytes. -/
def finalPairing_beq_ok : Bool := SyntaxEq.stmtsBeq finalPairing_ast finalPairing_direct

/-- GATE 16 (STRUCTURAL, render -> AST). The rendered BYTES tokenise to the same
    Yul program as the AST. yulTokens strips the comments D-P13 puts outside the
    equality and reduces hex literals to values, so this is the secondary
    relation - it is the only one a text port can reach without a runtime Yul
    parser, and it is labelled as such. EVM.print wraps the block in braces, so
    the render is wrapped to match. -/
def finalPairing_astAgrees_ok : Bool :=
  yulTokens ("{" ++ renderFinalPairing poseidonCtx ++ "}") == yulTokens (EVM.print finalPairing_ast)

/-- The fail helper, the first statement AssemblyHelpers contributes. -/
def failFunction_ast : Block EVM.Op := yul% {
  function fail(sel) {
    mstore(0x00, shl(224, sel))
    revert(0x00, 0x04)
  }
}

/-- GATE 17 (STRUCTURAL). AssemblyHelpers' first seven rendered lines - three
    comment lines and the function - tokenise to failFunction_ast. -/
def assemblyHelpers_failAgrees_ok : Bool :=
  yulTokens ("{" ++ String.intercalate "\n"
                (((renderAssemblyHelpers poseidonCtx).splitOn "\n").take 7) ++ "}")
    == yulTokens (EVM.print failFunction_ast)

/-- The whole deployed Lagrange partial as the vendored AST: 33 statements
    including three multi-line for headers, a multi-name assignment, and the
    nested MF-4 error split. -/
def lagrange_ast : Block EVM.Op := yul% {
  let lagrange_precompile_failed := 0
  {
    let k := 6
    let x := mload(X_MPTR)
    let x_n := x
    for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
      x_n := mulmod(x_n, x_n, r)
    }
    let omega := mload(OMEGA_MPTR)
    let mptr := LAGRANGE_DENOMS_MPTR
    let mptr_end := add(mptr, 0x0140)
    for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
        lt(mptr, mptr_end)
        { mptr := add(mptr, 0x20) } {
      mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
      pow_of_omega := mulmod(pow_of_omega, omega, r)
    }
    let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
    mstore(mptr_end, x_n_minus_1)
    success, lagrange_precompile_failed := batch_invert(success, LAGRANGE_DENOMS_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)
    mptr := LAGRANGE_DENOMS_MPTR
    let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
    for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
        lt(mptr, mptr_end)
        { mptr := add(mptr, 0x20) } {
      mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
      pow_of_omega := mulmod(pow_of_omega, omega, r)
    }
    let l_blind := mload(add(LAGRANGE_DENOMS_MPTR, 0x20))
    let l_i_cptr := add(LAGRANGE_DENOMS_MPTR, 0x40)
    for { let l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, 0x0120) }
        lt(l_i_cptr, l_i_cptr_end)
        { l_i_cptr := add(l_i_cptr, 0x20) } {
      l_blind := addmod(l_blind, mload(l_i_cptr), r)
    }
    let instance_eval := 0
    for {
        let instance_cptr := INSTANCE_CPTR
        let instance_cptr_end := add(instance_cptr, 0x20)
      }
      lt(instance_cptr, instance_cptr_end)
      { instance_cptr := add(instance_cptr, 0x20)
        l_i_cptr := add(l_i_cptr, 0x20) } {
      instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
    }
    let x_n_minus_1_inv := mload(mptr_end)
    let l_last := mload(LAGRANGE_DENOMS_MPTR)
    let l_0 := mload(add(LAGRANGE_DENOMS_MPTR, 0x0120))
    mstore(X_N_MPTR, x_n)
    mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
    mstore(L_LAST_MPTR, l_last)
    mstore(L_BLIND_MPTR, l_blind)
    mstore(L_0_MPTR, l_0)
    mstore(INSTANCE_EVAL_MPTR, instance_eval)
  }
  if iszero(success) {
    if lagrange_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
    fail(ERR_PROOF_REJECTED)
  }
}

/-- GATE 18 (STRUCTURAL, render -> AST). The whole rendered Lagrange partial
    tokenises to lagrange_ast: 90 rendered lines, 33 statements, comments and
    hex spelling outside the relation. -/
def lagrange_astAgrees_ok : Bool :=
  yulTokens ("{" ++ renderLagrange poseidonCtx ++ "}") == yulTokens (EVM.print lagrange_ast)

/-- The linearization block QuotientAndLinearization contributes after the
    quotient includes. -/
def qalLinearization_ast : Block EVM.Op := yul% {
  {
    let x := mload(X_MPTR)
    let k := 6
    let x_pow_2i := x
    let x_pow_2i_minus1 := 1
    for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
      x_pow_2i_minus1 := mulmod(mulmod(x_pow_2i_minus1, x_pow_2i_minus1, r), x, r)
      x_pow_2i := mulmod(x_pow_2i, x_pow_2i, r)
    }
    let x_split := x_pow_2i_minus1
    let one_minus_x_n := addmod(1, sub(r, x_pow_2i), r)
    mstore(QUOTIENT_MPTR, x_split)
    mstore(add(QUOTIENT_MPTR, 0x20), one_minus_x_n)
  }
}

/-- GATE 19 (STRUCTURAL, render -> AST). -/
def quotientAndLinearization_astAgrees_ok : Bool :=
  yulTokens ("{" ++ renderQuotientAndLinearization poseidonCtx "" "" ++ "}")
    == yulTokens (EVM.print qalLinearization_ast)

/-- GATE 20 (R-41). One space deleted from each deployed render - the first
    space of its first line - and the artifact match dies. This is the
    whitespace-sensitivity proof for the byte gates: a gate that only compared
    tokens would stay green here. -/
def perturb_singleSpace_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (List.all deployedRenders fun r =>
    artifactMatch sol r && ! artifactMatch sol (shrinkAssignSpaces r))

/-- GATE 21 (R-41). One newline deleted: the two lines fuse and the match dies.
    Together with gate 20 this covers both ways a zero-render tag can go wrong -
    a stray space, or a stray line break. -/
def perturb_newlineDeletion_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (List.all deployedRenders fun r =>
    artifactMatch sol r && ! artifactMatch sol (deleteLastNewline r))

/-- GATE 22 (R-41, hazard 1 rule 4). Put the included file's trailing newline
    back and the boundary half fails: the artifact has LF LF four-space after
    each partial, not LF LF LF four-space. This is the gate that pins the
    Askama-drops-the-final-newline finding. -/
def perturb_trailingNewline_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (List.all deployedRenders fun r =>
    artifactMatch sol r && ! artifactMatch sol (r ++ "\n"))

/-- GATE 23 (R-41). Every context value the deployed arms interpolate, perturbed
    by one: k, num_instances, num_neg_lagranges, proof_len, the two scratch
    pointers. For each, at least one of the five renders stops matching the
    artifact. -/
def perturb_contextValue_ok : IO Bool :=
  readDump >>= fun sol =>
  let allMatch (c : PartialCtx) :=
    artifactMatch sol (renderAssemblyHelpers c) && artifactMatch sol (renderVkLoading c)
      && artifactMatch sol (renderLagrange c) && artifactMatch sol (renderFinalPairing c)
  pure (allMatch poseidonCtx
    && ! allMatch { poseidonCtx with k := poseidonCtx.k + 1 }
    && ! allMatch { poseidonCtx with numInstances := poseidonCtx.numInstances + 1 }
    && ! allMatch { poseidonCtx with numNegLagranges := poseidonCtx.numNegLagranges + 1 }
    && ! allMatch { poseidonCtx with proofLen := poseidonCtx.proofLen + 32 }
    && ! allMatch { poseidonCtx with scalarInvScratchMptr := poseidonCtx.scalarInvScratchMptr + 32 }
    && ! allMatch { poseidonCtx with finalPairingScratchMptr := poseidonCtx.finalPairingScratchMptr + 32 })

/-- GATE 24 (R-41). Every profile flag flipped: trace, gas_checkpoints,
    expected_has_accumulator, quotient_probe, embedded_vk, quotient_external.
    Each makes at least one render disagree with the artifact, which is what
    pins the arm selection. -/
def perturb_flagFlip_ok : IO Bool :=
  readDump >>= fun sol =>
  let someVk : Halo2VerifyingKey :=
    { constructorPayloadMptr := 0x80, constants := [("digest", 1), ("k", 6)],
      fixedComms := [{ xHi := 1, xLo := 2, yHi := 3, yLo := 4 }], permutationComms := [],
      quotientConstOffsetWords := none, quotientConstWords := 0,
      quotientProgramOffsetWords := none, quotientProgramWords := 0,
      quotientConstLabels := [], quotientConstHeaders := [] }
  let qext : QuotientExternal :=
    { frameBase := 0x2000, frameLen := 0x1000, outputLen := 0x100, magic := 0x4d494446 }
  let allMatch (c : PartialCtx) :=
    artifactMatch sol (renderAssemblyHelpers c) && artifactMatch sol (renderVkLoading c)
      && artifactMatch sol (renderLagrange c)
      && artifactMatch sol (renderQuotientAndLinearization c "" "")
      && artifactMatch sol (renderFinalPairing c)
  pure (allMatch poseidonCtx
    && ! allMatch { poseidonCtx with trace := true }
    && ! allMatch { poseidonCtx with gasCheckpoints := true }
    && ! allMatch { poseidonCtx with expectedHasAccumulator := true }
    && ! allMatch { poseidonCtx with quotientProbe := true }
    && ! allMatch { poseidonCtx with embeddedVk := some someVk }
    && ! allMatch { poseidonCtx with quotientExternal := some qext })

/-- GATE 25 (R-41, hazard 2). A hex filter that forgot the odd-nibble pad: the
    unpadded spelling of 768 (0x300 for 0x0300) is absent from the artifact
    where the padded one is present. -/
def perturb_hexSpelling_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (sol.contains ("staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, scratch, 0x20)")
    && ! sol.contains ("staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x300, scratch, 0x20)"))

/-- GATE 26 (R-41, hazard 1 rule 5). The ragged 32-space indent at
    AssemblyHelpers.yul:294 tidied to the surrounding 16: the artifact keeps the
    ragged bytes, so the tidied render is absent. -/
def perturb_raggedIndent_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderAssemblyHelpers poseidonCtx
  let tidied := String.replace r
    "\n                                ret := staticcall(PAIRING_GAS_2PAIR"
    "\n                ret := staticcall(PAIRING_GAS_2PAIR"
  pure (occ sol r == 1 && occ sol tidied == 0)

/-- GATE 27 (R-41, the honest non-bite). These context fields appear ONLY in arms
    the deployed profile does not take, so NO byte gate can see them: perturbing
    them leaves the deployed renders byte-identical. Asserted as inertness, not
    hidden as a passing test - this is the one perturbation class that cannot
    redden, and the report names it. -/
def inertFields_ok : Bool :=
  let q := renderQuotientAndLinearization poseidonCtx "" ""
  let v := renderVkLoading poseidonCtx
  (renderQuotientAndLinearization { poseidonCtx with numQuotients := 99 } "" "") == q
    && (renderQuotientAndLinearization { poseidonCtx with simpleSelectorCols := [7, 9, 11] } "" "") == q
    && (renderQuotientAndLinearization { poseidonCtx with fixedCommMptr := 1 } "" "") == q
    && (renderQuotientAndLinearization { poseidonCtx with expectedQuotientCodehash := some 1 } "" "") == q
    && renderVkLoading { poseidonCtx with vkMptr := 1 } == v

/-- GATE 28 (R-41, the honest non-bite, part 2). A perturbation at the very START
    of a render can be ABSORBED by the include's own whitespace, and the exact
    shape is measured here rather than assumed. (a) Deleting one space from the
    first line of the three renders that START with an indented line still matches:
    the artifact has four extra spaces there (D:627 carries 16 where
    T:AssemblyHelpers.yul:1 has 12), so the shortened needle matches one column
    further right. (b) Deleting the first newline is absorbed for the two renders
    that begin with two of them (VkLoading and QuotientAndLinearization, whose
    first line is a false {% if %} that leaves LF LF) and DETECTED for the other
    three. So the leading whitespace is pinned by includeIndentBoundary_ok (the
    before-side) and by the artifact's own byte count, not by a one-character
    deletion at the head; the interior is pinned by perturb_singleSpace_ok and
    perturb_newlineDeletion_ok. Asserted rather than hidden. -/
def perturb_leadingWhitespaceAbsorbed_note : IO Bool :=
  readDump >>= fun sol =>
  let three := [renderAssemblyHelpers poseidonCtx, renderLagrange poseidonCtx,
                renderFinalPairing poseidonCtx]
  let two := [renderVkLoading poseidonCtx, renderQuotientAndLinearization poseidonCtx "" ""]
  pure (List.all three (fun r => artifactMatch sol (deleteFirst r " "))
    && List.all two (fun r => artifactMatch sol (deleteFirst r "\n"))
    && List.all three (fun r => ! artifactMatch sol (deleteFirst r "\n")))

/-! ## P-13b gates: the transcript parser and the accumulator helpers

Eighteen more gates (29-46). Gate 29 is the reachability gate D-P19 demands, and it
re-measures the two template line counts the brief quoted. Gates 30-31 are the
TEXTUAL ones: both partials DO render in the deployed profile (AccumulatorHelpers
renders its four decoder helpers unconditionally), so neither byte gate is vacuous -
gate 36 says exactly how much of AccumulatorHelpers the profile exercises and what it
leaves unrendered. Gates 32-33 answer hazards 1 and 3 by re-running P-12's gate-19/20/22
conjuncts on MY render and tying them to the template's own lines and to the artifact.
Gate 34 is the anti-self-fulfilment gate for the twelve new context fields and gate 35
is the arithmetic behind :416. Gates 37-40 cover the arms the deployed profile does not
take, against a SYNTHETIC accumulator context that is labelled as such: no tracked
artifact pins their content, so they pin SELECTION and STRUCTURE only. Gate 39 is the
R-25 gate. Gate 41 is hazard 4's line-count law and hazard 5's answer (neither template
uses a right-trimming -%} tag, so there is nothing new to pin beyond rule 4). Gates
42-45 are the R-41 perturbations, including the class that provably cannot redden. Gate
46 is the STRUCTURAL one (D-P13): the :416 region against the vendored AST, which is a
different relation from the byte gate and is not offered as a substitute for it. -/

/-- The SYNTHETIC accumulator context (P-13b hazard 2). The deployed profile has no
    public accumulator, so NOTHING in the tracked artifact pins the bytes of
    validate_public_accumulator. This context exists to give the untaken arms SOME
    render to be tested against, and it is labelled synthetic at every use: the values
    are chosen, not observed. expectedNumAccLimbs / expectedNumAccLimbBits are the
    7 x 2^56 self-emulation shape the template's own comment at :194-195 names;
    accFixedBases uses G1_BASE_MPTR = 0x2a60 (D:127) for the "-G" entry with
    negate = true, which is what ART:200 produces, and 0x4000 (the fixed-comm base)
    for a second, unnegated entry so the for at :314 runs twice; accMsmScratch is the
    address LayoutMemory.lean:783 pins for the accumulator_msm region. -/
def accSynthCtx : PartialCtx :=
  { poseidonCtx with
    expectedHasAccumulator := true
    expectedHasAccumulatorWord := 1
    expectedAccHasCarriedScalars := true
    expectedAccOffset := 2
    expectedNumAccLimbs := 7
    expectedNumAccLimbBits := 56
    accMsmScratch := 0x7000
    accFixedBases := [(0x2a60, true), (0x4000, false)] }

/-- The same, with the COLLAPSED point-pair shape: no carried scalars and no fixed-base
    tail, which is the arm ART:245's unwrap_or and ART:224's unwrap_or_default describe
    for a Moonlight-style wrap. Also synthetic. -/
def accSynthCollapsedCtx : PartialCtx :=
  { accSynthCtx with
    expectedAccHasCarriedScalars := false
    expectedHasAccumulatorWord := 1
    accFixedBases := [] }

/-- GATE 29 (reachability, first, and the brief's numbers re-measured). Both template
    files open, and their line counts are the ones the brief quoted: 424 and 372 lines
    terminated by LF, i.e. 425 and 373 pieces after splitting on LF. -/
def parser13b_artifactsReachable_ok : IO Bool :=
  readTemplate "TranscriptProofParser.yul" >>= fun pp =>
  readTemplate "AccumulatorHelpers.yul" >>= fun ah =>
  readDump >>= fun sol =>
  pure (EvmKats.generatedReadOk sol && pp.length > 15000 && ah.length > 10000
    && lineCount pp == 425 && lineCount ah == 373)

/-- GATE 30 (TEXTUAL). TranscriptProofParser.yul renders byte-identically to
    D:1178-1495: 318 lines, 17,136 bytes (17,140 in the artifact once the include's
    four spaces are added), occurring nowhere else, with the include boundary on both
    sides. -/
def transcriptProofParser_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderTranscriptProofParser poseidonCtx))

/-- GATE 31 (TEXTUAL, and NOT vacuous - see gate 36). AccumulatorHelpers.yul renders
    byte-identically to D:932-1096: 165 lines, 8,962 bytes (8,966 with the include's
    four spaces), occurring nowhere else. -/
def accumulatorHelpers_bytesExact_ok : IO Bool :=
  readDump >>= fun sol => pure (includeBoundary sol (renderAccumulatorHelpers poseidonCtx))

/-- GATE 32 (hazard 1, THE REQUIRED FINDING). P-12's gate 22
    (Calldata.lean:890 decoderAcceptance_agreesWithD7_ok) asserts of the TEMPLATE that
    it contains 'if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }',
    and its gates 19-20 assert the three scalar-canonicity conjuncts. This re-runs every
    one of those conjuncts on MY RENDER and ties the render to the template's own line
    416 and to the artifact. AGREEMENT: :416 is pure literal text in the template - no
    tag, no indentation change - so the port cannot disagree with P-12 without reddening
    this gate. The brief said stop and report on disagreement; there is none. -/
def parser_hazard1SatisfiesP12Gate22_ok : IO Bool :=
  readTemplate "TranscriptProofParser.yul" >>= fun t =>
  readDump >>= fun sol =>
  let r := renderTranscriptProofParser poseidonCtx
  let guard := "if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }"
  let line416 := ((t.splitOn "\n").drop 415).head?.getD ""
  pure (line416 == "            " ++ guard
    && r.contains guard
    && occ sol guard == 1
    && occ r "fail(ERR_BAD_CALLDATA_SHAPE)" == 1
    && r.contains "success := and(success, lt(inst_be, r))"
    && r.contains "if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }"
    && occ r "lt(inst_be, r)" == 1
    && occ r "if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }" == 2)

/-- GATE 33 (hazard 3, the COUNT). The canonicity guards P-12 cited: exactly one
    'lt(inst_be, r)' (T:63) and EXACTLY TWO 'if iszero(lt(eval, r)) { ... }' (T:319 and
    T:382). Counted in the template, in the render and in the whole artifact, so a third
    one appearing anywhere - in this partial or in another - is a red gate, not a
    silent widening of what the decoder accepts. -/
def parser_canonicityGuardCount_ok : IO Bool :=
  readTemplate "TranscriptProofParser.yul" >>= fun t =>
  readDump >>= fun sol =>
  let r := renderTranscriptProofParser poseidonCtx
  pure (occ t "lt(inst_be, r)" == 1 && occ r "lt(inst_be, r)" == 1 && occ sol "lt(inst_be, r)" == 1
    && occ t "if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }" == 2
    && occ r "if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }" == 2
    && occ sol "if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }" == 2
    && occ r "fail(ERR_NON_CANONICAL_SCALAR)" == 4
    && occ t "fail(ERR_NON_CANONICAL_SCALAR)" == 4)

/-- GATE 34 (anti-self-fulfilment for the twelve new fields). Every profile input P-13b
    added is re-read from the dump's OWN lines: each section width from the
    'for { let end := add(proof_cptr, 0x..) }' the render interpolates it into, the two
    ABI cursor constants, the proof length, the x3 mask that makes
    truncated_challenges observable, and the absence of every accumulator marker that
    makes the four accumulator flags false. Without this the two new byte gates would be
    comparing the artifact to itself. -/
def parserProofLayout_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  let L := poseidonCtx.proofLayout
  let ph := poseidonCtx.userPhases
  let sect (n : Nat) := "for { let end := add(proof_cptr, " ++ hexFilter n ++ ") }"
  pure (sol.contains (sect L.lookupMultiplicities.byteLen)
    && sol.contains (sect L.permutationProducts.byteLen)
    && sol.contains (sect L.trash.byteLen)
    && sol.contains (sect L.quotientLimbs.byteLen)
    && sol.contains (sect L.evals.byteLen)
    && sol.contains (sect L.qEvals.byteLen)
    && occ sol (sect 0x80) == 3
    && (match ph with
        | [p] => sol.contains (sect p.adviceBytes) && p.numChallenges == 0
        | _ => false)
    && (match L.lookups with
        | [lk] => lk.helpers.itemCount == 1 && sol.contains (sect lk.helpers.byteLen)
        | _ => false)
    && sol.contains ("PROOF_CPTR = " ++ hashHex L.proofCptr ++ ";")
    && sol.contains ("NUM_INSTANCE_CPTR = " ++ hashHex L.proofEnd ++ ";")
    && sol.contains ("eq(" ++ hexFilter L.proofLen ++ ", calldataload(PROOF_LEN_CPTR))")
    && L.proofLen == poseidonCtx.proofLen
    && sol.contains "mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))"
    && poseidonCtx.truncatedChallenges == true
    && occ sol "User-phase challenge" == 0
    && occ sol "validate_public_accumulator" == 0
    && poseidonCtx.expectedHasAccumulator == false
    && poseidonCtx.expectedAccHasCarriedScalars == false
    && poseidonCtx.accFixedBases == []
    && sol.contains ("let limbs_per_word := "
                      ++ toString poseidonCtx.templateConstants.accumulator.limbsPerWord))

/-- GATE 35 (the arithmetic :416 stands for). The parser walks the proof in ten
    sections; their byte lengths tile the payload exactly, and the payload is exactly
    NUM_INSTANCE_CPTR - PROOF_CPTR bytes, which is the same 0x10e0 the ABI length check
    in VkLoading pins. So the cursor equality at T:416 is not a tautology of the
    template: it is the claim that these ten numbers add up, and this is where that
    claim is checked. rust: AP:243 (proof_len := proof_end - proof_cptr) and
    ART:307 (num_instance_cptr = proof_layout.proof_end). -/
def parser_cursorIdentity_ok : Bool :=
  let L := poseidonCtx.proofLayout
  let walked := (L.advicePhases.map fun s => s.byteLen).foldl (fun a b => a + b) 0
    + L.lookupMultiplicities.byteLen + L.permutationProducts.byteLen
    + (L.lookups.map fun lk => lk.helpers.byteLen + lk.accumulator.byteLen).foldl (fun a b => a + b) 0
    + L.trash.byteLen + L.quotientLimbs.byteLen + L.evals.byteLen
    + L.fCom.byteLen + L.qEvals.byteLen + L.pi.byteLen
  walked == L.proofLen
    && L.proofEnd == L.proofCptr + L.proofLen
    && L.proofLen == poseidonCtx.proofLen
    && L.pi.start + L.pi.byteLen == L.proofEnd
    && L.proofCptr == 0x64 && L.proofEnd == 0x1144 && L.proofLen == 0x10e0
    && (L.advicePhases.all fun s => s.byteLen == s.itemCount * s.itemBytes)

/-- GATE 36 (hazard 2, the vacuity trap, ANSWERED WITH NUMBERS). What the deployed
    profile actually renders of AccumulatorHelpers: the four decoder helpers
    (T:22-165), which are OUTSIDE the {% if self.expected_has_accumulator %} at :167 and
    so render for EVERY profile - 165 of the file's 372 lines, 8,962 bytes. What it
    renders NOTHING of: validate_public_accumulator, T:167-372, 206 template lines,
    including both G1MSM calls, the carried-scalar arms and the fixed-base tail loop.
    So gate 31 is a real byte gate, but it is not a gate on the accumulator logic, and
    gates 37-40 are what stand in for that. -/
def acc_deployedRenderIsHelpersOnly_ok : IO Bool :=
  readDump >>= fun sol =>
  readTemplate "AccumulatorHelpers.yul" >>= fun t =>
  let r := renderAccumulatorHelpers poseidonCtx
  pure (occ sol r == 1
    && lineCount r == 165 && lineCount t == 373
    && r.contains "function load_acc_coord_shifted"
    && r.contains "function is_bls_p_minus_one"
    && r.contains "function check_acc_coord_packing"
    && r.contains "function load_acc_point"
    && ! r.contains "validate_public_accumulator"
    && occ sol "validate_public_accumulator" == 0
    && occ sol "ACC_RHS_MSM_GAS" == 0
    && occ sol "acc_pair_alpha" == 0
    && occ sol "batch_ptr" == 0
    && occ sol "calldataload(fixed_scalar_ptr)" == 0
    && occ sol "let acc_scratch" == 0
    && t.length - r.length > 13000)

/-- GATE 37 (hazard 2, the untaken arm, SYNTHETIC CONTEXT). With
    expected_has_accumulator TRUE and carried scalars TRUE and a two-entry fixed-base
    tail, the accumulator function renders: the explicit scalar reads, their
    canonicality guards, the tail pointer arithmetic, one tail block per base, the
    negation for the base flagged negate = true and not for the other, and the
    partially-collapsed comment arm. None of these bytes are pinned by any tracked
    artifact - this gate pins that the PORT emits an arm at all and that the arms
    DISCRIMINATE, not that the arm is what the Rust generator would ship. -/
def acc_syntheticCarriedScalarsArm_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderAccumulatorHelpers accSynthCtx
  pure (occ r "function validate_public_accumulator(success, r) -> out, precompile_failed {" == 1
    && occ r "let bits := 56" == 1 && occ r "let n := 7" == 1
    && occ r "let limbs_per_word := 4" == 2
    && occ r "let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)" == 3
    && occ r "add(INSTANCE_CPTR, 0x40)" == 1
    && occ r "let acc_scratch := 0x7000" == 1
    && occ r "let lhs_scalar := calldataload(lhs_scalar_ptr)" == 1
    && occ r "out := and(out, lt(lhs_scalar, r))" == 1
    && occ r "let rhs_instance_ptr := add(lhs_scalar_ptr, 0x20)" == 1
    && occ r "let rhs_scalar := calldataload(rhs_scalar_ptr)" == 1
    && occ r "out := and(out, lt(rhs_scalar, r))" == 1
    && occ r "let fixed_scalar_ptr := add(rhs_scalar_ptr, 0x20)" == 1
    && occ r "calldataload(fixed_scalar_ptr)" == 2
    && occ r "out := and(out, lt(fixed_scalar_0, r))" == 1
    && occ r "out := and(out, lt(fixed_scalar_1, r))" == 1
    && occ r "fixed_scalar_0 := mod(sub(r, fixed_scalar_0), r)" == 1
    && occ r "fixed_scalar_1 := mod(sub(r, fixed_scalar_1), r)" == 0
    && occ r "mcopy(acc_pair_ptr, 0x2a60, 0x80)" == 1
    && occ r "mcopy(acc_pair_ptr, 0x4000, 0x80)" == 1
    && occ r "RHS layout for this generated verifier is partially" == 1
    && occ r "RHS layout for this generated verifier is fully collapsed" == 0
    && occ r "already\n                // collapsed point pair" == 0
    && occ r "staticcall(G1MSM_GAS_1PAIR, 0x0c, acc_scratch, 0xa0, ACC_LHS_MPTR, 0x80)" == 1
    && occ r "ACC_RHS_MSM_GAS" == 2
    && occ r "pop(lhs_is_id)" == 1 && occ r "pop(rhs_is_id)" == 1
    && r.length > (renderAccumulatorHelpers poseidonCtx).length + 8000
    && ! occursOnce sol r)

/-- GATE 38 (hazard 2, the OTHER untaken arm, SYNTHETIC CONTEXT). With carried scalars
    FALSE and an EMPTY tail the collapsed point-pair arms render instead: implicit unit
    scalars, the RHS pointer that does not skip a scalar word, the tail pointer that
    lands where an explicit scalar would have been, and the "already collapsed point
    pair" comment. The two comment arms at T:252-271 are mutually exclusive and this
    checks that the port keeps them so. It also checks the template's own note at
    :180-183: with neither carried scalars nor a tail, 'r' is legally unused, so no
    canonicality guard on a scalar is rendered at all. -/
def acc_syntheticCollapsedArm_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderAccumulatorHelpers accSynthCollapsedCtx
  pure (occ r "let lhs_scalar := 1" == 1
    && occ r "let rhs_scalar := 1" == 1
    && occ r "let rhs_instance_ptr := lhs_scalar_ptr" == 1
    && occ r "let fixed_scalar_ptr := rhs_scalar_ptr" == 0
    && occ r "calldataload(fixed_scalar_ptr)" == 0
    && occ r "out := and(out, lt(lhs_scalar, r))" == 0
    && occ r "out := and(out, lt(rhs_scalar, r))" == 0
    && occ r "RHS layout for this generated verifier is an already" == 1
    && occ r "collapsed point pair: lhs point, rhs point" == 1
    && occ r "RHS layout for this generated verifier is fully collapsed" == 0
    && occ r "RHS layout for this generated verifier is partially" == 0
    && occ r "Without carried scalars, the tail starts where an explicit" == 0
    && ! occursOnce sol r
    && r != renderAccumulatorHelpers accSynthCtx)

/-- GATE 39 (hazard 2 x R-25). The accumulator decoder does NOT decode or range-check
    the coordinate words of a point whose identity flag is set: T:130-141 stores four
    zero words and nothing else, which is the malleability R-25 records
    (P-SE-evidence/survey.md:1022: "Identity-flagged coordinate words are neither
    decoded nor range-checked (AccumulatorHelpers.yul:130-141). The fix is to project
    accWords to (0,0,1) for flagged points"). The fix belongs in the Lean decoder's
    projection, NOT in this render: a port that "tidied" the arm by adding checks would
    make the Solidity and the Lean accept different languages. This gate pins the region
    to the template's own lines 130-141 VERBATIM and asserts the arm contains no decode
    call and no range check, and separately that the non-identity arm keeps the
    decoded-(0,0) rejection at T:156-157 that stops a flagged-free point from encoding
    the infinity. -/
def accR25_identityArmIsVerbatim_ok : IO Bool :=
  readTemplate "AccumulatorHelpers.yul" >>= fun t =>
  readDump >>= fun sol =>
  let r := renderAccumulatorHelpers poseidonCtx
  let region := String.intercalate "\n" ((t.splitOn "\n").drop 129 |>.take 12)
  pure (region.startsWith "                if is_id {"
    && r.contains region
    && sol.contains region
    && occ region "mstore(" == 4
    && region.contains "mstore(dst, 0)"
    && region.contains "mstore(add(dst, 0x20), 0)"
    && region.contains "mstore(add(dst, 0x40), 0)"
    && region.contains "mstore(add(dst, 0x60), 0)"
    && ! region.contains "load_acc_coord"
    && ! region.contains "lt("
    && occ r "ok := lt(flag, 2)" == 1
    && occ r "is_id := eq(flag, 1)" == 1
    && occ r "let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))" == 1
    && occ r "ok := and(ok, iszero(decoded_zero))" == 1)

/-- GATE 40 (brief correction, and a real property). The brief listed accRhsMsmGas and
    gas.* as fields this partial needs. It does not: T:AccumulatorHelpers.yul names the
    gas as the Yul IDENTIFIERS G1MSM_GAS_1PAIR (T:246) and ACC_RHS_MSM_GAS (T:358),
    whose values come from M:520 and M:82 through T:partials/verifier/Constants.sol -
    a different partial. Interpolating a number here instead would decouple the call
    site from the constant declaration the artifact pins at D:259. So no such field was
    added, and this gate pins the identifiers: one of each in the synthetic render,
    zero of the accumulator one in the deployed render, and the deployed artifact's four
    G1MSM_GAS_1PAIR sites all outside this partial. -/
def acc_gasNamesAreRenderLiterals_ok : IO Bool :=
  readTemplate "AccumulatorHelpers.yul" >>= fun t =>
  readDump >>= fun sol =>
  let dep := renderAccumulatorHelpers poseidonCtx
  let syn := renderAccumulatorHelpers accSynthCtx
  pure (occ t "G1MSM_GAS_1PAIR" == 1 && occ t "ACC_RHS_MSM_GAS" == 2
    && occ dep "G1MSM_GAS_1PAIR" == 0 && occ dep "ACC_RHS_MSM_GAS" == 0
    && occ syn "G1MSM_GAS_1PAIR" == 1 && occ syn "ACC_RHS_MSM_GAS" == 2
    && occ sol "G1MSM_GAS_1PAIR" == 4 && occ sol "ACC_RHS_MSM_GAS" == 0
    && ! syn.contains ("staticcall(" ++ toString poseidonCtx.proofLen)
    && occ syn "0x0c," == 2)

/-- GATE 41 (hazard 4 and hazard 5). The newline law for the two new renders: 424
    template lines become 318 and 372 become 165, no rendered line is whitespace-only,
    and neither render contains a single trace or gas-checkpoint byte - the 12 trace
    sites and 8 gas sites in the parser all took their newline with them. Hazard 5's
    answer is measured too: neither template uses a right-trimming -%} tag at all
    (checked against the template text), so the only whitespace-control rule this
    package needs is the leading-dash strip plus the dropped final newline. -/
def parser13b_newlineLaw_ok : IO Bool :=
  readTemplate "TranscriptProofParser.yul" >>= fun t1 =>
  readTemplate "AccumulatorHelpers.yul" >>= fun t2 =>
  let p := renderTranscriptProofParser poseidonCtx
  let a := renderAccumulatorHelpers poseidonCtx
  pure (lineCount p == 318 && lineCount a == 165
    && ! hasWsOnlyLine p && ! hasWsOnlyLine a
    && ! p.contains "gas_checkpoint" && ! a.contains "gas_checkpoint"
    && ! p.contains "trace_point" && ! p.contains "trace_u256"
    && ! p.contains "proof_commit_trace_id" && ! p.contains "proof_eval_trace_id"
    && occ t1 "-%}" == 0 && occ t2 "-%}" == 0
    && occ t1 "{%-" > 0
    && ! p.endsWith "\n" && ! a.endsWith "\n")

/-- GATE 42 (R-41). Twelve perturbations of the new numeric context, each by one item,
    one word or one nibble: num_instances (T::53 and :56), the phase's advice bytes, a second user challenge, six of
    the ten proof-section widths (the four the parser interpolates into a loop bound
    plus evals and q_evals), the empty-lookups list, and the three template constants
    these two partials interpolate (g1_bytes, word_bytes, accumulator.limbs_per_word).
    For each, at least one of the two new renders stops matching the artifact. NOT
    included, because it provably cannot redden: challenge_offset, which the deployed
    profile never interpolates - gate 45 asserts that inertness. -/
def perturb_parserContextValue_ok : IO Bool :=
  readDump >>= fun sol =>
  let both (c : PartialCtx) :=
    artifactMatch sol (renderTranscriptProofParser c) && artifactMatch sol (renderAccumulatorHelpers c)
  let L := poseidonCtx.proofLayout
  let ph0 := match poseidonCtx.userPhases with
             | [p] => p
             | _ => { adviceBytes := 0, numChallenges := 0, challengeOffset := 0 }
  let tc := poseidonCtx.templateConstants
  pure (both poseidonCtx
    && ! both { poseidonCtx with numInstances := poseidonCtx.numInstances + 1 }
    && ! both { poseidonCtx with userPhases := [{ ph0 with adviceBytes := ph0.adviceBytes + 32 }] }
    && ! both { poseidonCtx with userPhases := [{ ph0 with numChallenges := ph0.numChallenges + 1 }] }
    && ! both { poseidonCtx with proofLayout := { L with lookupMultiplicities := ProofSection.new 0x464 2 g1Bytes } }
    && ! both { poseidonCtx with proofLayout := { L with permutationProducts := ProofSection.new 0x4e4 2 g1Bytes } }
    && ! both { poseidonCtx with proofLayout := { L with trash := ProofSection.new 0x764 2 g1Bytes } }
    && ! both { poseidonCtx with proofLayout := { L with quotientLimbs := ProofSection.new 0x7e4 3 g1Bytes } }
    && ! both { poseidonCtx with proofLayout := { L with evals := ProofSection.new 0x9e4 49 wordBytes } }
    && ! both { poseidonCtx with proofLayout := { L with qEvals := ProofSection.new 0x1064 4 wordBytes } }
    && ! both { poseidonCtx with proofLayout := { L with lookups := [] } }
    && ! both { poseidonCtx with templateConstants := { tc with g1Bytes := 96 } }
    && ! both { poseidonCtx with templateConstants := { tc with wordBytes := 64 } }
    && ! both { poseidonCtx with templateConstants :=
                 { tc with accumulator := { tc.accumulator with limbsPerWord := 3 } } })

/-- GATE 43 (R-41). Every new FLAG perturbed: trace on (12 arms appear), gas checkpoints
    on (8 lines appear), truncated_challenges off (the x3 mask disappears), and each of
    the four shape guards driven to zero (its section disappears). Each reddens at least
    one of the two new renders against the artifact. -/
def perturb_parserFlags_ok : IO Bool :=
  readDump >>= fun sol =>
  let both (c : PartialCtx) :=
    artifactMatch sol (renderTranscriptProofParser c) && artifactMatch sol (renderAccumulatorHelpers c)
  pure (both poseidonCtx
    && ! both { poseidonCtx with trace := true }
    && ! both { poseidonCtx with gasCheckpoints := true }
    && ! both { poseidonCtx with truncatedChallenges := false }
    && ! both { poseidonCtx with numLookups := 0 }
    && ! both { poseidonCtx with numPermutationZs := 0 }
    && ! both { poseidonCtx with lookupHPlusAcc := 0 }
    && ! both { poseidonCtx with numTrashcans := 0 })

/-- GATE 44 (R-41). The accumulator flag flipped: validate_public_accumulator appears
    (8,000+ bytes of it), the deployed render is unchanged in its first 165 lines, and
    the flipped render is NOT in the artifact - which is the selection pin, and the
    reason gate 36 had to say out loud how little the profile exercises. -/
def perturb_accFlagFlip_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderAccumulatorHelpers poseidonCtx
  let flipped := renderAccumulatorHelpers { poseidonCtx with expectedHasAccumulator := true }
  pure (artifactMatch sol dep && ! occursOnce sol flipped
    && flipped.contains "function validate_public_accumulator"
    && ! dep.contains "function validate_public_accumulator"
    && flipped.length > dep.length + 7000
    && flipped.startsWith dep)

/-- GATE 45 (R-41, the honest non-bites). These P-13b fields appear ONLY in arms the
    deployed profile does not take, so NO byte gate can see them and perturbing them
    leaves both deployed renders byte-identical: the two trace bases (trace = false),
    the accumulator offset / limb counts and limb bits, the carried-scalar flag, the
    fixed-base tail and the acc MSM scratch address (expected_has_accumulator = false).
    Asserted as inertness rather than hidden as a passing test, in the same spirit as
    inertFields_ok above. Named in the brief and inert here: expectedAccHasCarriedScalars and
    accFixedBases. Missed by the brief and inert here: accMsmScratch, the two trace
    bases, and challenge_offset - the deployed profile's single phase has ZERO user
    challenges, so the one site that interpolates challenge_offset (T::127) never runs
    and gate 42 cannot redden it; it reddens as soon as numChallenges is non-zero, which
    is why numChallenges itself IS in gate 42. -/
def inertFields13b_ok : Bool :=
  let p := renderTranscriptProofParser poseidonCtx
  let a := renderAccumulatorHelpers poseidonCtx
  renderTranscriptProofParser { poseidonCtx with proofCommitTraceBase := 1 } == p
    && renderTranscriptProofParser { poseidonCtx with proofEvalTraceBase := 999999 } == p
    && renderTranscriptProofParser { poseidonCtx with trace := false, proofCommitTraceBase := 7 } == p
    && renderAccumulatorHelpers { poseidonCtx with expectedAccOffset := 41 } == a
    && renderAccumulatorHelpers { poseidonCtx with expectedNumAccLimbs := 11 } == a
    && renderAccumulatorHelpers { poseidonCtx with expectedNumAccLimbBits := 64 } == a
    && renderAccumulatorHelpers { poseidonCtx with expectedAccHasCarriedScalars := true } == a
    && renderAccumulatorHelpers { poseidonCtx with accFixedBases := [(0x1, true), (0x2, false)] } == a
    && renderAccumulatorHelpers { poseidonCtx with accMsmScratch := 0xdead } == a
    && renderTranscriptProofParser
         { poseidonCtx with userPhases := [{ adviceBytes := 0x400, numChallenges := 0,
                                             challengeOffset := 41 }] } == p

/-- The last five rendered lines of the parser: the :416 cursor check, the blank and the
    two comment lines the template puts between it and the deferred success check, and
    that success check. Read out of the render, not pasted. -/
def parserTail_region : String :=
  String.intercalate "\n" (((renderTranscriptProofParser poseidonCtx).splitOn "\n").drop 313 |>.take 5)

/-- The same five lines as the vendored AST. -/
def parserTail_ast : Block EVM.Op := yul% {
  if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }
  if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }
}

/-- The same program with raw constructors: two Stmt.cond, each guarding one user-fn
    call to fail (AssemblyHelpers.yul:4). This is the relation irCheck will use, so it
    is stated with constructors and not only with the parser. -/
def parserTail_direct : Block EVM.Op :=
  [ Stmt.cond (binOp EVM.Op.iszero [binOp EVM.Op.eq [varX "proof_cptr", varX "NUM_INSTANCE_CPTR"]])
      [stmtE (usrFn "fail" [varX "ERR_BAD_CALLDATA_SHAPE"])]
  , Stmt.cond (binOp EVM.Op.iszero [varX "success"])
      [stmtE (usrFn "fail" [varX "ERR_NON_CANONICAL_SCALAR"])] ]

/-- GATE 46 (STRUCTURAL, D-P13). The tail region the render produces tokenises to the
    vendored AST, and that AST equals the raw-constructor one under stmtsBeq. This is a
    DIFFERENT relation from gate 32's byte equality and does not substitute for it: the
    token stream cannot see the four-space include boundary, and stmtsBeq cannot see a
    wrong hex spelling. What it adds is that :416 parses as the two-statement guard pair
    P-12's EXACT claim reads it as - iszero of an eq of the cursor against the constant,
    not an eq against a computed offset. -/
def parserTail_astAgrees_ok : Bool :=
  yulTokens ("{" ++ parserTail_region ++ "}") == yulTokens (EVM.print parserTail_ast)
    && SyntaxEq.stmtsBeq parserTail_ast parserTail_direct

/-! ## P-13c gates: QuotientHelpers.yul and QuotientNumeratorBlock.yul

Twenty-two gates (47-68). The two templates' deployed bytes are D:1588-2539 of the tracked
artifact - 57,218 bytes, 952 lines - and gate 50 is the free end-to-end check the earlier
packages left: the two renders are exactly the two arguments
renderQuotientAndLinearization already takes, so feeding them in and re-running gate 6's
boundary checks the whole chain from these templates to the contract template's include.

HAZARD 3, ANSWERED WITH NUMBERS (gates 58, 59, 60). The QNB template has 88 conditional
sites and 11 for-sites. In the deployed profile only 68 of the 88 ifs are even REACHED (20
sit inside arms the profile does not take, including the whole legacy 'when None' arm), 23
of those 68 are true and 45 false, and all 11 for-sites run (537 iterations, none of them
zero). Of the 31 opcode switch arms, 10 render and 21 render ZERO times; the 9 memory-token
arms render zero times because their only host arm (push_mem_token) is off, so mem_usage is
wholly unobservable. 528 of the 921 rendered lines are Rust-emitted text sliced from the
artifact, not this template's own bytes; 393 are the template's. A byte gate over the whole
region therefore pins 393 template lines and the PLACEMENT of 528 it cannot own - and gate
65 shows those 528 are load-bearing rather than decorative by perturbing one of them. The
dead arms are gated structurally and synthetically (gates 59-60) with a label saying they
pin that the arm EXISTS and DISCRIMINATES, never that the Rust would ship those bytes. -/

/-- The quotient_numerator template directory (a sibling of P-13a's verifier directory). -/
def quotientTemplateDirCandidates : List String :=
  ["../proofs/solidity-verifier/templates/partials/quotient_numerator/",
   "proofs/solidity-verifier/templates/partials/quotient_numerator/"]

def readQuotientTemplate (name : String) : IO String :=
  EvmKats.readFirst (quotientTemplateDirCandidates.map fun d => d ++ name)

/-- GATE 47 (reachability, first). The dump and BOTH template sources must open, so a wrong
    path is a named red rather than a needle miss that matches nothing. -/
def quotient13c_artifactsReachable_ok : IO Bool :=
  readDump >>= fun sol =>
  readQuotientTemplate "QuotientHelpers.yul" >>= fun qh =>
  readQuotientTemplate "QuotientNumeratorBlock.yul" >>= fun qnb =>
  pure (EvmKats.generatedReadOk sol && qh.length > 1500 && qnb.length > 50000)

def qIsHexDigit (c : Char) : Bool :=
  (c ≥ '0' && c ≤ '9') || (c ≥ 'a' && c ≤ 'f') || (c ≥ 'A' && c ≤ 'F')

def qHexDigitVal (c : Char) : Nat :=
  if c ≥ '0' && c ≤ '9' then c.toNat - '0'.toNat
  else if c ≥ 'a' && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def qTakeHex (s : String) : String := String.mk (s.toList.takeWhile qIsHexDigit)

def qHexValue? (s : String) : Option Nat :=
  let ds := qTakeHex s
  if ds.isEmpty then none else some (ds.foldl (fun acc c => acc * 16 + qHexDigitVal c) 0)

/-- Every 0x.. literal in every line of sol containing needle, in document order. -/
def qHexesInLinesWith (sol needle : String) : List Nat :=
  (sol.splitOn "\n").flatMap fun l =>
    if ! l.contains needle then []
    else match (l.splitOn "0x").tail? with
         | some ps => ps.filterMap fun h => qHexValue? (qTakeHex h)
         | none => []

/-- The decimal integer immediately after the unique occurrence of needle. -/
def qNatAfter (sol needle : String) : Option Nat :=
  match sol.splitOn needle with
  | [_, r] =>
      let ds := r.toList.takeWhile (fun c => c ≥ '0' && c ≤ '9')
      if ds.isEmpty then none
      else some (ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
  | _ => none

/-- The hex literal that begins the text right after the unique occurrence of needle. -/
def qHexHere (sol needle : String) : Option Nat :=
  match sol.splitOn needle with
  | [_, r] => qHexValue? (qTakeHex r)
  | _ => none

/-- The next 0x literal after the unique occurrence of needle. -/
def qHexAfter (sol needle : String) : Option Nat :=
  match sol.splitOn needle with
  | [_, r] => match (r.splitOn "0x").tail? with
              | some hs => qHexValue? (qTakeHex (hs.head?.getD ""))
              | none => none
  | _ => none

/-- Every second element of a list, starting from the second. -/
def qOddIdx (xs : List Nat) : List Nat :=
  xs.zipIdx.filterMap fun hn => if hn.snd % 2 == 1 then some hn.fst else none

/-- Leading and trailing spaces removed (String.trim is not in scope in this build). -/
def qTrim (s : String) : String :=
  String.mk (((s.toList.dropWhile (fun c => c == ' ')).reverse.dropWhile (fun c => c == ' ')).reverse)

/-- GATE 48 (TEXTUAL). QuotientHelpers.yul renders byte-identically to D:1588-1618
    (1,621 bytes, 31 lines) and occurs nowhere else. Its include boundary is the BEFORE
    half only: the four spaces of the contract template's include line land on its first
    line (P-13a rule 3), and what follows it is P-13c's own second template, not the
    parent's LF LF four-space. That is why this gate checks the prefix and gate 49 the
    suffix, and why neither can stand in for the other. -/
def quotientHelpers_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            -- Length asserted explicitly (orchestrator, round 40). `occursOnce` plus the
            -- prefix boundary is satisfied by a TRUNCATED render: a strict prefix still
            -- occurs exactly once with the same text before it. P-13c flagged this as
            -- gate 48's known weakness (perturbation N11 showed the composite gates catch
            -- it but 48 alone could not). 1621 bytes / 31 lines, measured from the render
            -- against the tracked artifact rather than copied from a report.
            qh.length == 1621 && (qh.splitOn "\n").length == 31
              && occursOnce sol qh
              && match sol.splitOn qh with
                 | [before, _] => before.endsWith "\n    "
                 | _ => false
        | none => false)

/-- GATE 49 (TEXTUAL). QuotientNumeratorBlock.yul renders byte-identically to D:1619-2539
    (55,597 bytes, 921 lines) and occurs nowhere else. Its boundary is the AFTER half only:
    its predecessor is QuotientHelpers' render - the two includes are concatenated with no
    separator because QAL:59-60 both open with a left-trimming brace-dash - and its
    successor is the contract template's LF LF four-space. -/
def quotientNumeratorBlock_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx => artifactMatch sol (renderQuotientNumeratorBlock ctx)
        | none => false)

/-- GATE 50 (THE FREE GATE P-13a left). The two renders are exactly the two arguments
    renderQuotientAndLinearization already takes, so feeding them in reproduces the whole
    partial and re-runs quotientAndLinearization_ownBytes_ok's boundary: the result occurs
    exactly once and is followed by LF LF + four spaces (the handoff to Pcs.yul). End to
    end from these two templates to the contract template's include, and the gate that dies
    if either render gains or loses a byte at either end. -/
def quotientAndLinearization_withPartials_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            let full := renderQuotientAndLinearization ctx qh
              (renderQuotientNumeratorBlock ctx)
            full.startsWith qh && artifactMatch sol full
        | none => false)

/-- GATE 51 (hazard 1, the brief's numbers re-measured). The two renders occupy D:1588
    through D:2539 INCLUSIVE. The brief said 1588-2538 and called 2539
    QuotientAndLinearization's own tail, but the closing brace at D:2539 is
    QuotientNumeratorBlock.yul:1442; QAL's own bytes begin at the newline that terminates
    it, which is why gate 6's render starts with LF LF. 57,218 bytes, 952 lines, once. -/
def quotientRegion_span_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            let qnb := renderQuotientNumeratorBlock ctx
            let comb := qh ++ qnb
            sol.contains ("\n    " ++ comb)
              && comb.length == 57218 && lineCount comb == 952
              && qh.length == 1621 && lineCount qh == 31
              && qnb.length == 55597
              && occ sol comb == 1
              && match sol.splitOn comb with
                 | [before, _] => (before.splitOn "\n").length == 1588
                 | _ => false
        | none => false)

/-- GATE 52 (anti-self-fulfilment). Every scalar of quotientDeployedProgram the dump can
    show is re-read from the dump's own lines: the five base pointers, the program length,
    the spill ceiling, the selector bucket count, the selector max power (rendered as the
    loop bound, i.e. max_power + 1) and all four (selector_offset, power_offset) tail pairs.
    Nothing here is copied from the brief. -/
def quotientProgram_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  let p := quotientDeployedProgram
  pure (qHexHere sol "let q_const_mptr := 0x" == some p.constMptr
    && qHexHere sol "let q_program_mptr := 0x" == some p.programMptr
    && qHexHere sol "let q_sp := 0x" == some p.stackMptr
    && qHexHere sol "let q_end := add(q_program_mptr, 0x" == some p.len
    && qHexHere sol "addmod(0, sub(r, mload(0x" == some p.evalNumerMptr
    && qHexHere sol "if gt(q_sp, 0x" == some p.guards.stackLast
    && qNatAfter sol "if iszero(lt(q_sel_idx, " == some p.guards.numSelectorBuckets
    && qNatAfter sol "lt(q_y_power_i, " == some (p.selectorMaxPower + 1)
    && qHexesInLinesWith sol "shl(5, q_y_power_i)), q_y_power)" == [p.selectorPowerMptr]
    && qHexesInLinesWith sol "let q_sel_ptr := add(SELECTOR_ACC_MPTR,"
         == p.selectorTailUpdates.map (fun t => t.selectorOffset)
    && qOddIdx (qHexesInLinesWith sol "mstore(q_sel_ptr, mulmod")
         == p.selectorTailUpdates.map (fun t => t.powerOffset)
    && p.selectorTailUpdates.length == 4)

/-- GATE 53 (hazard 2, the two fields the dump cannot show). trace_id_mptr and
    guards.const_max are rendered by no arm the deployed profile takes, so they are DERIVED
    from their Rust rules instead: quotient.rs:59 (trace_id_mptr = state_mptr + WORD_BYTES)
    and quotient.rs:252 (const_max = num_consts - 1, with num_consts the count of
    'quotient_const' words in the VK dump - exactly one, DVK:99). If either derivation
    stops holding, the port's claim to have derived rather than invented them fails here. -/
def quotientProgram_inertFieldsDerived_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  let p := quotientDeployedProgram
  pure (p.traceIdMptr == p.evalNumerMptr + 0x20
    && occ dvk "// quotient_const" == 1
    && p.guards.constMax == occ dvk "// quotient_const" - 1)

/-- The one rendered line that binds linearization_expected_eval, read out of the render. -/
def qnbNegationLine (ctx : PartialCtx) : Option String :=
  match ((renderQuotientNumeratorBlock ctx).splitOn "\n").filterMap
          fun l => if (qTrim l).startsWith "let linearization_expected_eval"
                   then some (qTrim l) else none with
  | [l] => some l
  | _ => none

/-- GATE 54 (hazard 2, the required finding's first half). The DEPLOYED arm's negation is
    the compact form at T:QuotientNumeratorBlock.yul:1393 - addmod(0, sub(r, mload(E)), r)
    with E = eval_numer_mptr - NOT the :1439 line the brief names, which lives in the
    legacy arm. Exactly one rendered line binds the scalar, it is that form, it occurs once
    in the artifact, and the store into QUOTIENT_EVAL_MPTR follows it. -/
def qnb_negation_deployedLine_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            match qnbNegationLine ctx with
            | some line =>
                line == "let linearization_expected_eval := addmod(0, sub(r, mload("
                  ++ hexFilter quotientDeployedProgram.evalNumerMptr ++ ")), r)"
                  && occ sol line == 1
                  && occ sol "mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)" == 1
            | none => false
        | none => false)

/-- GATE 55 (hazard 2 + hazard 4, THE REQUIRED FINDING AS AN EXECUTABLE CLAIM). The
    rendered negation line - taken from the render, not pasted - is handed to the Yul TEXT
    READER P-09h built in Evaluator.lean (yulRun / yulValue, which predates this package
    and is an independent implementation of the addmod / sub / mload subset). It must
    evaluate the rendered bytes to qvmFrNeg of the same memory word: the arithmetic
    FoldCompute already models as quotientExpectedEval (FoldCompute.lean:860, :891, :952).
    The negative control is the same line with sub(r, .) removed: it must return the value
    UNNEGATED, so it agrees with the reader and disagrees with the model. That asymmetry is
    what makes this a modelling check rather than a text match. -/
def qnb_negation_isModelled_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            match qnbNegationLine ctx with
            | some line =>
                let p := quotientDeployedProgram
                let st : QuotientEvaluatorKats.YSt :=
                  { mem := QuotientEvaluatorKats.xMem, vars := [] }
                let (v, _) := QuotientEvaluatorKats.xMem.literal p.evalNumerMptr
                let plain := "let linearization_expected_eval := addmod(mload("
                  ++ hexFilter p.evalNumerMptr ++ "), 0, r)"
                match QuotientEvaluatorKats.yulRun [line] "linearization_expected_eval" st,
                      QuotientEvaluatorKats.yulRun [plain] "linearization_expected_eval" st with
                | .ok (r, _), .ok (bad, _) =>
                    v != 0 && r == qvmFrNeg v && bad == v && bad != qvmFrNeg v
                | _, _ => false
            | none => false
        | none => false)

/-- The rendered negation statement as the vendored AST. -/
def qnbNegation_ast : Block EVM.Op := yul% {
  let linearization_expected_eval := addmod(0, sub(r, mload(0x6660)), r)
}

/-- The same statement with raw constructors: letDecl of one identifier over a builtin
    addmod whose second argument is builtin sub applied to (var r, builtin mload literal).
    This is the relation irCheck will use, so it is stated with constructors and not only
    with the quotation parser. -/
def qnbNegation_direct : Block EVM.Op :=
  [ Stmt.letDecl ["linearization_expected_eval"]
      (some (binOp EVM.Op.addmod
        [ Expr.lit (Literal.number 0)
        , binOp EVM.Op.sub [ varX "r"
                           , binOp EVM.Op.mload [Expr.lit (Literal.number 0x6660)] ]
        , varX "r" ])) ]

/-- GATE 56 (STRUCTURAL, D-P13). The rendered negation line tokenises to the vendored AST
    of the same statement, and that AST equals the raw-constructor one under stmtsBeq. A
    DIFFERENT relation from gate 55's: 55 says the bytes denote the modelled arithmetic,
    56 says the bytes parse as the structure the AST printer emits. Neither substitutes for
    the other, and neither substitutes for the byte gates. -/
def qnb_negation_astAgrees_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            match qnbNegationLine ctx with
            | some line =>
                yulTokens ("{" ++ line ++ "}") == yulTokens (EVM.print qnbNegation_ast)
                  && SyntaxEq.stmtsBeq qnbNegation_ast qnbNegation_direct
            | none => false
        | none => false)

/-- The 31 opcode summary names paired with the template_constants byte and the op_usage
    flag each one gates, in template order (T:QuotientNumeratorBlock.yul:231-322). -/
def deployedOpUsageTable (sol : String) : List (String × Bool × Bool) :=
  let tc := templateConstantsDefault.quotientVm.op
  let u := quotientDeployedProgram.opUsage
  let rows : List (String × Nat × Bool) :=
    [ ("push_const", tc.pushConst, u.pushConst)
    , ("push_mem_literal", tc.pushMemLiteral, u.pushMemLiteral)
    , ("push_mem_token", tc.pushMemToken, u.pushMemToken)
    , ("push_mem_token_offset", tc.pushMemTokenOffset, u.pushMemTokenOffset)
    , ("push_mem_u16", tc.pushMemU16, u.pushMemU16)
    , ("add", tc.add, u.add)
    , ("mul", tc.mul, u.mul)
    , ("neg", tc.neg, u.neg)
    , ("push_const_u8", tc.pushConstU8, u.pushConstU8)
    , ("fold_main", tc.foldMain, u.foldMain)
    , ("fold_selector", tc.foldSelector, u.foldSelector)
    , ("add_const_u8", tc.addConstU8, u.addConstU8)
    , ("mul_const_u8", tc.mulConstU8, u.mulConstU8)
    , ("add_const", tc.addConst, u.addConst)
    , ("mul_const", tc.mulConst, u.mulConst)
    , ("add_mem_u16", tc.addMemU16, u.addMemU16)
    , ("mul_mem_u16", tc.mulMemU16, u.mulMemU16)
    , ("add_mul_mem_mem_const_u8", tc.addMulMemMemConstU8, u.addMulMemMemConstU8)
    , ("add_mul_const_u8_mem_u16", tc.addMulConstU8MemU16, u.addMulConstU8MemU16)
    , ("add_mul_mem_mem", tc.addMulMemMem, u.addMulMemMem)
    , ("run_add_mul_mem_mem_const_u8", tc.runAddMulMemMemConstU8, u.runAddMulMemMemConstU8)
    , ("run_add_mul_const_u8_mem_u16", tc.runAddMulConstU8MemU16, u.runAddMulConstU8MemU16)
    , ("affine_sum", tc.affineSum, u.affineSum)
    , ("native_permutation", tc.nativePermutation, u.nativePermutation)
    , ("native_lookup", tc.nativeLookup, u.nativeLookup)
    , ("native_identity", tc.nativeIdentity, u.nativeIdentity)
    , ("lin7", tc.lin7, u.lin7)
    , ("bilin7_row", tc.bilin7Row, u.bilin7Row)
    , ("bilin7_pairwise", tc.bilin7Pairwise, u.bilin7Pairwise)
    , ("modarith7", tc.modarith7, u.modarith7)
    , ("pow5", tc.pow5, u.pow5) ]
  rows.map fun row =>
    (row.1, sol.contains ("//   " ++ hexFilter row.2.1 ++ " " ++ row.1), row.2.2)

/-- GATE 57 (hazard 2, the flag set). The artifact's own opcode-summary block is the
    generator's statement of which arms it emitted: for all 31 opcodes, the presence of its
    summary line agrees with the flag the port carries. Plus the three counts the template
    comment at :227-230 claims are equal: 10 summary lines, 10 rendered case arms, 10 true
    flags. (No BEq on QuotientVmOpcodeUsage - Models.lean derives it only on
    QuotientVmGuards - so the flag set is checked through the table, not by record equality.) -/
def opUsage_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let tbl := deployedOpUsageTable sol
            let observed := tbl.filterMap fun row => if row.2.1 then some row.1 else none
            let ported := tbl.filterMap fun row => if row.2.2 then some row.1 else none
            (tbl.all fun row => row.2.1 == row.2.2)
              && tbl.length == 31
              && observed.length == 10
              && ported.length == 10
              && observed == ported
              && occ sol "//   0x" == 10
              && occ (renderQuotientNumeratorBlock ctx) "case 0x" == 10
        | none => false)

/-- GATE 58 (hazard 3, THE COUNTS). What the deployed profile actually exercises, as
    numbers the render is measured against rather than as prose: the five generated regions
    (99 / 82 / 43 / 3x37 / 193 lines = 528 of the 921 rendered), the dead opcode arms
    leaving no trace, and the four guard macros appearing exactly as often as the arms that
    call them render. -/
def qnb_deployedExercisedRegions_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let r := renderQuotientNumeratorBlock ctx
            (ctx.quotientInlineComputations.map List.length) == [99]
              && ctx.quotientNativePermutationComputation.length == 82
              && ctx.quotientNativeLookupComputation.length == 43
              && (ctx.quotientNativeIdentityComputations.map List.length) == [37, 37, 37]
              && (ctx.quotientPostVmComputations.map List.length) == [193]
              && lineCount r == 922
              && ! r.contains "PUSH_CONST (bytes)"
              && ! r.contains "MODARITH7"
              && ! r.contains "AFFINE_SUM"
              && ! r.contains "Fully-evaluated identity: qn = qn*y + eval."
              && ! r.contains "PUSH_MEM_TOKEN"
              && ! r.contains "q_ptr := L_0_MPTR"
              && ! r.contains "trace_u256(mload("
              && ! r.contains "let q_trace_id :="
              && occ r "if gt(q_sp, " == 1
              && occ r "if eq(q_sp, " == 1
              && occ r "if iszero(and(q_has_top, eq(q_sp, " == 1
              && occ r "if or(q_has_top, xor(q_sp, " == 3
        | none => false)

/-- All 31 op_usage flags on, for the synthetic arm-coverage gate. -/
def qnbAllOnUsage : QuotientVmOpcodeUsage :=
  { pushConst := true, pushMemLiteral := true, pushMemToken := true,
    pushMemTokenOffset := true, pushMemU16 := true, add := true, mul := true, neg := true,
    pushConstU8 := true, foldMain := true, foldSelector := true, addConstU8 := true,
    mulConstU8 := true, addConst := true, mulConst := true, addMemU16 := true,
    mulMemU16 := true, addMulMemMemConstU8 := true, addMulConstU8MemU16 := true,
    addMulMemMem := true, runAddMulMemMemConstU8 := true, runAddMulConstU8MemU16 := true,
    affineSum := true, nativePermutation := true, nativeLookup := true,
    nativeIdentity := true, lin7 := true, bilin7Row := true, bilin7Pairwise := true,
    modarith7 := true, pow5 := true }

/-- All 9 memory-token flags on, for the same gate. -/
def qnbAllOnMemUsage : QuotientVmMemUsage :=
  { l0 := true, lLast := true, lBlind := true, beta := true, gamma := true, x := true,
    theta := true, trashChallenge := true, instanceEval := true }

/-- GATE 59 (hazard 3, the dead arms, SYNTHETIC CONTEXT). With every op_usage and every
    mem_usage flag forced on, all 31 opcode arms and both 9-arm token tables appear (49
    'case 0x' sites in total), the guards the deployed profile never renders appear, and the
    render grows from 55,597 to 88,850 bytes.
    LABEL: this pins that the arms EXIST in the port and that the flags DISCRIMINATE. It
    does NOT pin that the Rust would ever ship these bytes - no tracked artifact covers
    them, and the operand layouts inside them are verified by nothing here. -/
def qnb_allArms_synthetic_ok : IO Bool :=
  readDump >>= fun sol =>
  let p := quotientDeployedProgram
  let pAll := { p with opUsage := qnbAllOnUsage, memUsage := qnbAllOnMemUsage }
  pure (match quotientDeployedCtx sol with
        | none => false
        | some base =>
            let ctx : PartialCtx := { base with quotientProgram := some pAll }
            let r := renderQuotientNumeratorBlock ctx
            occ r "case 0x" == 49
              && occ r "q_ptr := " == 30
              && r.contains "if gt(qconst, "
              && r.contains "q_ptr := L_BLIND_MPTR"
              && r.contains "q_ptr := add(INSTANCE_EVAL_MPTR, q_off)"
              && r.contains "Limb-aware opcodes are opt-in"
              && r.contains "MODARITH7: byte-only fused affine"
              && r.contains "AFFINE_SUM: mixed byte-only"
              && r.length == 88850)
/-- GATE 60 (hazard 2, the OTHER arm, SYNTHETIC CONTEXT). The line the brief names -
    QuotientNumeratorBlock.yul:1439, addmod(0, sub(r, quotient_eval_numer), r) - is in the
    'when None' legacy arm, which the deployed profile does not take; the deployed negation
    is the mload form at :1393. With quotient_program := None the port renders the :1439
    line verbatim, the fr_delta literal appears, and the compact VM text disappears.
    LABEL: this pins that the legacy arm exists and discriminates. It is NOT evidence that
    the shipped verifier takes it, and it is NOT what the required finding rests on - gate
    55 is, and gate 55 reads the DEPLOYED arm's line. -/
def qnb_directArm_synthetic_ok : Bool :=
  let ctx : PartialCtx := { quotientCtx with
    quotientProgram := none
    quotientEvalNumerComputations := [["let quotient_eval_numer := 0"]]
    frDelta := "0xDEADBEEF" }
  let r := renderQuotientNumeratorBlock ctx
  r.contains "let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)"
    && r.contains "let delta := 0xDEADBEEF"
    && r.contains "Legacy/direct mode"
    && ! r.contains "switch q_op"
    && ! r.contains "Compact quotient-program mode"
    && occ r "let linearization_expected_eval" == 1

/-- GATE 61 (hazard 1, the anchors). Every slice anchor occurs exactly once in the
    artifact, so the generated-code regions are determined rather than chosen. -/
def qnb_anchorsUnique_ok : IO Bool :=
  readDump >>= fun sol =>
  let anchors := [qAnchorInlineBefore, qAnchorInlineAfter, qAnchorPermBefore, qAnchorPermAfter,
                  qAnchorLookupBefore, qAnchorLookupAfter, qAnchorNiBefore, qAnchorNiAfter,
                  qAnchorPostBefore, qAnchorPostAfter]
  pure (anchors.all fun a => occ sol a == 1 && anchors.length == 10)

/-- GATE 62 (R-41). Every artifact-derivable scalar of the program record perturbed by one,
    each in its own scope: the render must stop matching the artifact. Twelve edits, all
    run; any that failed to redden is reported in the package report. -/
def perturb_quotientProgramScalars_ok : IO Bool :=
  readDump >>= fun sol =>
  let p := quotientDeployedProgram
  let edits : List (QuotientProgram -> QuotientProgram) :=
    [ fun p => { p with constMptr := p.constMptr + 0x20 }
    , fun p => { p with programMptr := p.programMptr + 0x20 }
    , fun p => { p with evalNumerMptr := p.evalNumerMptr + 0x20 }
    , fun p => { p with stackMptr := p.stackMptr + 0x20 }
    , fun p => { p with selectorPowerMptr := p.selectorPowerMptr + 0x20 }
    , fun p => { p with len := p.len + 1 }
    , fun p => { p with selectorMaxPower := p.selectorMaxPower + 1 }
    , fun p => { p with guards := { p.guards with stackLast := p.guards.stackLast + 0x20 } }
    , fun p => { p with guards := { p.guards with numSelectorBuckets := 5 } }
    , fun p => { p with selectorTailUpdates :=
        [ { selectorOffset := 0x00, powerOffset := 0x0000 }
        , { selectorOffset := 0x20, powerOffset := 0x0280 }
        , { selectorOffset := 0x40, powerOffset := 0x0220 }
        , { selectorOffset := 0x60, powerOffset := 0x0160 } ] }
    , fun p => { p with selectorTailUpdates := p.selectorTailUpdates.drop 1 }
    , fun p => { p with selectorTailUpdates := [] } ]
  pure (match quotientDeployedCtx sol with
        | some ctx => edits.all fun f =>
            let fp := f p
            let c : PartialCtx := { ctx with quotientProgram := some fp }
            ! artifactMatch sol (renderQuotientNumeratorBlock c)
        | none => false)

/-- GATE 63 (R-41). All 31 op_usage flags flipped, each in its own scope: the render
    changes and stops matching. The 10 true ones remove an arm, the 21 false ones add one -
    so this is also the discrimination proof for the dead arms, run one flag at a time. -/
def perturb_quotientOpUsageFlags_ok : IO Bool :=
  readDump >>= fun sol =>
  let p := quotientDeployedProgram
  let u := p.opUsage
  let flips : List (QuotientVmOpcodeUsage -> QuotientVmOpcodeUsage) :=
    [ fun u => { u with pushConst := ! u.pushConst }
    , fun u => { u with pushMemLiteral := ! u.pushMemLiteral }
    , fun u => { u with pushMemToken := ! u.pushMemToken }
    , fun u => { u with pushMemTokenOffset := ! u.pushMemTokenOffset }
    , fun u => { u with pushMemU16 := ! u.pushMemU16 }
    , fun u => { u with add := ! u.add }
    , fun u => { u with mul := ! u.mul }
    , fun u => { u with neg := ! u.neg }
    , fun u => { u with pushConstU8 := ! u.pushConstU8 }
    , fun u => { u with foldMain := ! u.foldMain }
    , fun u => { u with foldSelector := ! u.foldSelector }
    , fun u => { u with addConstU8 := ! u.addConstU8 }
    , fun u => { u with mulConstU8 := ! u.mulConstU8 }
    , fun u => { u with addConst := ! u.addConst }
    , fun u => { u with mulConst := ! u.mulConst }
    , fun u => { u with addMemU16 := ! u.addMemU16 }
    , fun u => { u with mulMemU16 := ! u.mulMemU16 }
    , fun u => { u with addMulMemMemConstU8 := ! u.addMulMemMemConstU8 }
    , fun u => { u with addMulConstU8MemU16 := ! u.addMulConstU8MemU16 }
    , fun u => { u with addMulMemMem := ! u.addMulMemMem }
    , fun u => { u with runAddMulMemMemConstU8 := ! u.runAddMulMemMemConstU8 }
    , fun u => { u with runAddMulConstU8MemU16 := ! u.runAddMulConstU8MemU16 }
    , fun u => { u with affineSum := ! u.affineSum }
    , fun u => { u with nativePermutation := ! u.nativePermutation }
    , fun u => { u with nativeLookup := ! u.nativeLookup }
    , fun u => { u with nativeIdentity := ! u.nativeIdentity }
    , fun u => { u with lin7 := ! u.lin7 }
    , fun u => { u with bilin7Row := ! u.bilin7Row }
    , fun u => { u with bilin7Pairwise := ! u.bilin7Pairwise }
    , fun u => { u with modarith7 := ! u.modarith7 }
    , fun u => { u with pow5 := ! u.pow5 } ]
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let dep := renderQuotientNumeratorBlock ctx
            flips.all fun f =>
              let pf := { p with opUsage := f u }
              let c : PartialCtx := { ctx with quotientProgram := some pf }
              renderQuotientNumeratorBlock c != dep && ! artifactMatch sol
                (renderQuotientNumeratorBlock c)
        | none => false)

/-- GATE 64 (R-41). The three QuotientHelpers flags and the profile flags the new templates
    read: each flip changes the render and breaks the artifact match. -/
def perturb_quotientHelperFlags_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            let qnb := renderQuotientNumeratorBlock ctx
            let p := quotientDeployedProgram
            let noPow5 := renderQuotientHelpers { ctx with quotientPow5Helper := false }
            let withLimb7 := renderQuotientHelpers { ctx with quotientLimb7Helper := true }
            let withWide := renderQuotientHelpers { ctx with quotientWideLimb7Helper := true }
            let traced := renderQuotientNumeratorBlock { ctx with trace := true }
            let noSels := renderQuotientNumeratorBlock { ctx with simpleSelectorCols := [] }
            let pZero := { p with selectorMaxPower := 0 }
            let zeroCtx := { ctx with quotientProgram := some pZero }
            let zeroPow := renderQuotientNumeratorBlock zeroCtx
            noPow5 != qh && noPow5.isPrefixOf qh
              && occ sol noPow5 == 1
              && ! noPow5.contains "VK-specialized"
              && match sol.splitOn noPow5 with
                 | [_, after] => after.startsWith "\n            // VK-specialized"
                 | _ => false
              && ! occursOnce sol withLimb7 && withLimb7 != qh
              && ! occursOnce sol withWide && withWide != qh
              && traced != qnb && ! artifactMatch sol traced
              && noSels != qnb && ! artifactMatch sol noSels
              && zeroPow != qnb && ! artifactMatch sol zeroPow
        | none => false)

/-- GATE 65 (R-41, the generated inputs are load-bearing). Change ONE sliced generated line
    and the render stops matching; drop one native-identity block and it stops matching.
    Without this the five regions could be any text at all and the byte gate would still
    pass - this is what makes them arguments rather than decoration. -/
def perturb_quotientGeneratedInput_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let tamper (i : Nat) (xs : List String) : List String :=
              xs.zipIdx.map fun xj => if xj.snd == i then "let tampered := 1" else xj.fst
            let c1 : PartialCtx := { ctx with quotientInlineComputations :=
              [tamper 0 ctx.quotientInlineComputations.flatten] }
            let c2 : PartialCtx := { ctx with
              quotientNativePermutationComputation := tamper 3 ctx.quotientNativePermutationComputation }
            let c3 : PartialCtx := { ctx with
              quotientNativeLookupComputation := tamper 7 ctx.quotientNativeLookupComputation }
            let niTampered := ctx.quotientNativeIdentityComputations.zipIdx.map
              fun bj => if bj.snd == 1 then tamper 0 bj.fst else bj.fst
            let c4 : PartialCtx := { ctx with quotientNativeIdentityComputations := niTampered }
            let c5 : PartialCtx := { ctx with quotientPostVmComputations :=
              [tamper 11 ctx.quotientPostVmComputations.flatten] }
            let c6 : PartialCtx := { ctx with
              quotientNativeIdentityComputations := ctx.quotientNativeIdentityComputations.drop 1 }
            artifactMatch sol (renderQuotientNumeratorBlock ctx)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c1)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c2)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c3)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c4)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c5)
              && ! artifactMatch sol (renderQuotientNumeratorBlock c6)
        | none => false)

/-- GATE 66 (R-41, the honest non-bites). Fields no deployed gate can see, asserted as
    inertness rather than hidden as a passing test: the nine mem_usage flags (their only
    host arm is off), guards.constMax (every const-guard arm is off), traceIdMptr (trace is
    off), quotientEvalNumerComputations (the legacy arm is not taken), frDelta (same arm),
    the two limb7 coefficient tables (their ifs are off) and quotientIdentityTraceBase
    (trace is off). Perturbing any of them leaves BOTH deployed renders byte identical. -/
def inertFields13c_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            let qnb := renderQuotientNumeratorBlock ctx
            let p := quotientDeployedProgram
            let memu := { p.memUsage with l0 := true, instanceEval := true, lBlind := true }
            let pMem := { p with memUsage := memu }
            let cMem : PartialCtx := { ctx with quotientProgram := some pMem }
            let pConst := { p with guards := { p.guards with constMax := 999 } }
            let cConst : PartialCtx := { ctx with quotientProgram := some pConst }
            let pTrace := { p with traceIdMptr := 0xdead }
            let cTrace : PartialCtx := { ctx with quotientProgram := some pTrace }
            let cEval : PartialCtx := { ctx with quotientEvalNumerComputations := [["let a := 1"]] }
            let cDelta : PartialCtx := { ctx with frDelta := "0x1" }
            let cLimb : PartialCtx := { ctx with limb7YulCoeffs := ["0x1"] }
            let cWide : PartialCtx := { ctx with wideLimb7YulCoeffs := ["0x2"] }
            let cBase : PartialCtx := { ctx with quotientIdentityTraceBase := 77 }
            renderQuotientNumeratorBlock cMem == qnb
              && renderQuotientNumeratorBlock cConst == qnb
              && renderQuotientNumeratorBlock cTrace == qnb
              && renderQuotientNumeratorBlock cEval == qnb
              && renderQuotientNumeratorBlock cDelta == qnb
              && renderQuotientHelpers cLimb == qh
              && renderQuotientHelpers cWide == qh
              && renderQuotientHelpers cBase == qh
        | none => false)

/-- GATE 67 (hazard 6, the trailing-newline rule pinned for these two files). Askama drops
    each included file's final newline: QuotientHelpers' render ends at '}' with none, and
    QuotientNumeratorBlock's ends at '}' with none. QNB's render OPENS with LF, because its
    leading block comment and its five macro definitions trim everything up to the last
    endmacro and the newline after it survives - which is what keeps QH's last line and
    QNB's first line separate in the artifact even though the two includes are concatenated
    with no separator. Exactly one whitespace-only line sits inside the region (D:1891), the
    residue of the NON-trimming template comment at :328-480. -/
def qnb13c_newlineLaw_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
        | some ctx =>
            let qh := renderQuotientHelpers ctx
            let qnb := renderQuotientNumeratorBlock ctx
            let wsLines := ((qh ++ qnb).splitOn "\n").filter
              fun l => l.length > 0 && l.toList.all (fun c => c == ' ')
            ! qh.endsWith "\n" && ! qnb.endsWith "\n"
              && qnb.startsWith "\n"
              && qh.endsWith "            }"
              && wsLines.length == 1
        | none => false)

/-- GATE 68 (hazard 6, the right-trim count, read from the TEMPLATE SOURCES). QNB uses a
    right-trim exactly five times - once per macro definition, which is what makes each
    guard render as one inline statement with no leading indent of its own - and QH uses it
    zero times. No other right-trim exists in either file, so P-13d inherits the rule
    unchanged and can pin it from the sources rather than from a render. -/
def qnb13c_rightTrimCount_ok : IO Bool :=
  readQuotientTemplate "QuotientHelpers.yul" >>= fun qh =>
  readQuotientTemplate "QuotientNumeratorBlock.yul" >>= fun qnb =>
  pure (occ qh "-%}" == 0 && occ qnb "-%}" == 5)

/-! ## P-13e gates: the six partials the P-13 split never assigned

Twenty gates (69-88). This section exists because the P-13 split enumerated seven
verifier templates when the directory holds thirteen: Constants.sol, 
PrecompileSmoke.sol, Constructors.sol, TraceAndGasHelpers.yul, Pcs.yul and
TraceReturn.yul had no render function anywhere, and their bytes - 52,894 of the
deployed artifact s 175,908, 30.1% - were read out of the dump by Contracts.lean
gate 10 rather than produced. Gate 79 pins that 52,894 as a number this tree now
produces; Contracts.lean gate 10 is the tiling that goes to zero as a result, and
Contracts gate 29 is the WHOLE-FILE render that was impossible before this package.

Gate 69 is the reachability gate D-P19 demands first. Gates 71-76 are the TEXTUAL
byte gates, each with its length asserted (hazard 1). Gate 74 is LABELLED
structural/synthetic because the deployed render it describes is the empty string
(hazard 2). Gates 77-78 are the anti-self-fulfilment pair: the memory layout and
the profile inputs are re-read out of the artifact and tied to Layout.lean's own
ported constants and to `VerifierMemoryLayout.validate`. Gates 80-81 are
STRUCTURAL (D-P13) and are not byte gates. Gates 82-87 are the R-41 perturbations,
each run inside the scope of the gate it attacks. Gate 88 names what no gate here
can see.
-/

/-- The six templates this package ports. -/
def partials13e : List String :=
  ["Constants.sol", "PrecompileSmoke.sol", "Constructors.sol",
   "TraceAndGasHelpers.yul", "Pcs.yul", "TraceReturn.yul"]

/-- All thirteen verifier template files as the FILESYSTEM sees them, so gate 70
    compares against a directory listing and not against a list someone typed. -/
def listVerifierTemplates : IO (List String) := go templateDirCandidates
where
  go : List String -> IO (List String)
  | [] => pure []
  | d :: rest => do
      try
        let es ← System.FilePath.readDir d
        let names := es.toList.map fun x => x.path.fileName.getD ""
        pure (names.filter fun n => n.endsWith ".yul" || n.endsWith ".sol")
      catch _e => go rest

/-- GATE 69 (reachability, first: D-P19). The artifact and all six template files
    must open, so a wrong path is a named red and not a needle that matches
    nothing. -/
def p13e_artifactsReachable_ok : IO Bool :=
  readDump >>= fun sol =>
  listVerifierTemplates >>= fun files =>
  partials13e.mapM (fun n => readTemplate n) >>= fun ts =>
  pure (EvmKats.generatedReadOk sol && sol.length == 175908 && files.length == 13
    && ts.length == 6 && ts.all (fun t => t.length > 500))

/-- The thirteen registry basenames, in registry order. Contracts.lean gate 30 ties
    this list to verifierPartPaths, which gate 2 ties to the template. -/
def verifierTemplateFiles : List String :=
  ["Constants.sol", "PrecompileSmoke.sol", "Constructors.sol", "AssemblyHelpers.yul",
   "AccumulatorHelpers.yul", "TraceAndGasHelpers.yul", "VkLoading.yul",
   "TranscriptProofParser.yul", "Lagrange.yul", "QuotientAndLinearization.yul",
   "Pcs.yul", "FinalPairing.yul", "TraceReturn.yul"]

/-- GATE 70 (THE SEVENTH FILE - the finding the brief asks for, made permanent).
    The directory holds exactly the thirteen files the include registry names, so
    there is no FOURTEENTH template nobody owns and no file on disk that the
    registry does not include. This is the gate that would have caught the P-13
    split: it compares a listing against the registry rather than a listing against
    a plan document. Contracts.lean gate 2 is the half that ties the registry to the
    template file itself. -/
def p13e_noOrphanTemplate_ok : IO Bool :=
  listVerifierTemplates >>= fun files =>
  pure (files.length == 13 && verifierTemplateFiles.length == 13
    && verifierTemplateFiles.all (fun n => files.contains n)
    && files.all (fun n => verifierTemplateFiles.contains n)
    && partials13e.all (fun n => verifierTemplateFiles.contains n)
    && files.eraseDups.length == 13)



/-- GATE 71 (TEXTUAL, byte-exact; hazard 1: LENGTH asserted). Constants.sol renders
    D:85-306, 13,873 bytes, 222 lines, once, with the include boundary on both
    sides. The four interpolation spellings are pinned separately because they are
    the risk in this partial: DECIMAL for vk_len and the gas bounds, byte-padded hex
    for the |hex() slots, 64-nibble hex_padded for the codehash, and Ptr Display
    for the bare memory pointers. PROOF_LEN_CPTR = 0x44 is the word-wise-subtraction
    pin: a port that read `proof_cptr - 1` as a byte subtraction renders 0x63 and
    dies here. -/
def constants_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderConstants poseidonCtx
  pure (occ sol r == 1 && r.length == 13873 && lineCount r == 222
    && includeBoundary sol r
    && r.startsWith "\n    /// @notice Verifying-key contract address authorized"
    && r.endsWith "BLS_P_MINUS_ONE_PACKED_1 = 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84;"
    && occ sol ("EXPECTED_VK_PAYLOAD_LENGTH = " ++ toString poseidonCtx.vkLen) == 1
    && occ sol " constant                VK_MPTR = 0x2900" == 1
    && occ sol "PROOF_LEN_CPTR = 0x44" == 1
    && occ sol "NUM_INSTANCE_CPTR = 0x1144" == 1
    && occ sol "          G1ADD_GAS = 375" == 1
    && occ sol "G1MSM_GAS_SMOKE = 337836" == 1
    && occ sol "EXPECTED_VK_CODEHASH_WORD = 0x233a1a8063ef1a9bfd30983d3034d3d90ab75ff6ac95c0e72d770bf08dcff51b" == 1)
/-- GATE 72 (TEXTUAL, byte-exact, length asserted). PrecompileSmoke.sol renders
    D:308-523, 14,414 bytes, 216 lines - one output line per template line,
    because the file has NO control-flow tag at all. Its 27 interpolations are the
    modexp frame offsets, the four precompile addresses, the EIP-2537 generator and
    double-generator words, and three memory slots no other partial reads. -/
def precompileSmoke_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderPrecompileSmoke poseidonCtx
  pure (occ sol r == 1 && r.length == 14414 && lineCount r == 216
    && includeBoundary sol r
    && r.startsWith "    /// @notice Smoke-check the Cancun/EIP-2537/modexp runtime features"
    && r.endsWith "        }\n    }"
    && occ sol "let scratch := 0x1000" == 1
    && occ sol "let msm_scratch := 0x65e0" == 1
    && occ sol "lt(off, 0x1d60)" == 1
    && occ sol "staticcall(MODEXP_GAS, 0x05, scratch, 0xc0, scratch, 0x20)" == 1)

/-- GATE 73 (TEXTUAL, byte-exact, length asserted). Constructors.sol renders
    D:525-540, 733 bytes, 16 lines: the Some/None arm of the two nested matches.
    The AUTHORIZED_QUOTIENT assignment is asserted ABSENT, not merely unrendered -
    the None arm does not emit it, and neither does anything else in the artifact. -/
def constructors_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderConstructors poseidonCtx
  pure (occ sol r == 1 && r.length == 733 && lineCount r == 16
    && includeBoundary sol r
    && r.startsWith "\n    /// @notice Create a verifier pinned to a generated verifying key."
    && r.endsWith "        AUTHORIZED_VK = authorizedVk;\n    }"
    && occ sol "AUTHORIZED_QUOTIENT = authorizedQuotient;" == 0
    && occ sol "constructor(address authorizedVk, address authorizedQuotient)" == 0)

/-- GATE 74 (hazard 2 - LABEL: STRUCTURAL and SYNTHETIC, NOT a byte gate, and it
    would be vacuous if it were one). The deployed render of TraceAndGasHelpers.yul
    is the EMPTY STRING: both ifs are false in the release profile and every byte of
    the file is inside one of them. Contracts.lean gate 9 proves that from the
    artifact - the run between the AccumulatorHelpers render and the two hoisted
    locals is exactly the include glue, so there is no room for a byte of this
    partial. A byte gate here would compare "" against "" and pin nothing, so this
    gate is structural instead: it pins that the two arms EXIST, that each flag
    selects its own arm and only its own arm, that the arms are additive, and that
    neither arm's text occurs in the artifact (i.e. no artifact covers their
    CONTENT - that is the honest limit, stated not hidden). -/
def traceAndGasHelpers_structuralEmpty_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderTraceAndGasHelpers poseidonCtx
  let traced := renderTraceAndGasHelpers { poseidonCtx with trace := true }
  let gassed := renderTraceAndGasHelpers { poseidonCtx with gasCheckpoints := true }
  let both := renderTraceAndGasHelpers { poseidonCtx with trace := true, gasCheckpoints := true }
  pure (dep == "" && dep.length == 0 && lineCount dep == 1
    && traced.length == 541 && lineCount traced == 12
    && gassed.length == 449 && lineCount gassed == 9
    && both.length == traced.length + gassed.length
    && both == traced ++ gassed
    && traced.contains "function trace_u256(id, value)" && traced.contains "function trace_point(id, mptr)"
    && ! traced.contains "function gas_checkpoint"
    && gassed.contains "function gas_checkpoint(id)" && ! gassed.contains "function trace_u256"
    && occ sol "function trace_u256(id, value)" == 0 && occ sol "function gas_checkpoint(id)" == 0
    && occ sol traced == 0 && occ sol gassed == 0)

/-- The per-block preamble the template writes before each generated sub-block, and
    the brace that closes it. These are the anchors pcsDeployedComputations reads
    the parameter back out with, so they are part of the port and not a hack: the
    template text at T:Pcs.yul:13-16 and :20 is exactly this. -/
def pcsBlockMarker : String := "                // Generated PCS sub-block "
def pcsBlockOpen : String :=
  ". These lines are\n                // emitted by the multi-prepare lowering pass and are kept"
  ++ "\n                // grouped so gas checkpoints can attribute their cost.\n                {\n"
def pcsBlockClose : String := "\n                }"
def pcsLineIndent : Nat := 20

/-- The generated multi-prepare sub-blocks, read back out of the artifact. rust:
    M:595 pcs_computations, `Vec<Vec<String>>`, emitted by the lowering pass that
    P-09/P-10 own and that this tree does not port. They are a PARAMETER of the
    render (P-13c's rule for generated bytes), and the block partition is observable
    here - each block gets its own numbered comment and its own braces - so the byte
    gate pins how many blocks there are and which lines belong to which. -/
def pcsDeployedComputations (sol : String) : List (List String) :=
  (sol.splitOn pcsBlockMarker).drop 1 |>.filterMap fun piece =>
    match piece.splitOn pcsBlockOpen with
    | [_, rest] =>
        match rest.splitOn pcsBlockClose with
        | body :: _ => some ((body.splitOn "\n").map fun l => (l.drop pcsLineIndent).toString)
        | _ => none
    | _ => none

/-- GATE 75 (TEXTUAL, byte-exact, length asserted). Pcs.yul renders D:2583-2980,
    23,311 bytes, 398 lines, of which the template owns the 10-line banner, the
    outer braces and eight 4-line block preambles/closers - 42 lines - and the
    other 356 are the generated parameter. The extraction round-trips: eight blocks,
    345 generated lines, and the render of what was extracted is the artifact's own
    bytes. That round trip is the honest form of a gate on content this port does
    not compute: it pins the TEMPLATE half exactly and says out loud that the other
    half is a transcription. -/
def pcs_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  let blocks := pcsDeployedComputations sol
  let r := renderPcs poseidonCtx blocks
  pure (occ sol r == 1 && r.length == 23311 && lineCount r == 397
    && includeBoundary sol r
    && blocks.length == 8
    && (blocks.map (fun b => b.length)).sum == 345
    && r.startsWith "            // ===============================================================\n            // PCS computation"
    && r.endsWith "\n                }\n            }"
    && occ r "// Generated PCS sub-block " == 8
    && occ sol "gas_checkpoint" == 0)

/-- GATE 76 (TEXTUAL, byte-exact, length asserted). TraceReturn.yul renders
    D:3010-3021, 563 bytes, 12 lines - the else arm of the terminal if, plus the
    two newlines the untrimmed `{% if self.trace -%}` leaves behind, which is what
    makes D:3010 whitespace-only. Its right boundary is NOT the include glue: this
    is the LAST partial in the file, so what follows is the shell footer, and the
    gate says so by requiring the suffix to be exactly vhFooter's text. -/
def traceReturn_bytesExact_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderTraceReturn poseidonCtx
  pure (occ sol r == 1 && r.length == 563 && lineCount r == 12
    && (match sol.splitOn r with
        | [before, after] => before.endsWith "\n\n    " && after == "\n        }\n    }\n}"
        | _ => false)
    && r.startsWith "\n\n            // Success path is terminal."
    && r.endsWith "mstore(RETURN_MPTR, 1)\n            return(RETURN_MPTR, 0x20)"
    && occ sol "trace_u256" == 0 && occ sol "trace_point" == 0)

/-- The fourteen VK-header slots Constants.sol derives as `memory.vk_mptr +
    vk_header.X`, paired with the header WORD offset the template adds. The gate
    below re-reads each derived address from the artifact and requires it to be
    VK_MPTR plus that offset in BYTES, i.e. it pins the word-wise reading of Ptr +
    usize (ENC:723-731) against the dump rather than trusting the render. -/
def constantsVkHeaderDecls : List (String × Nat) :=
  [("VK_DIGEST_MPTR", poseidonCtx.vkHeader.vkDigest),
   ("NUM_INSTANCES_MPTR", poseidonCtx.vkHeader.numInstances),
   ("K_MPTR", poseidonCtx.vkHeader.k),
   ("N_INV_MPTR", poseidonCtx.vkHeader.nInv),
   ("OMEGA_MPTR", poseidonCtx.vkHeader.omega),
   ("OMEGA_INV_MPTR", poseidonCtx.vkHeader.omegaInv),
   ("OMEGA_INV_TO_L_MPTR", poseidonCtx.vkHeader.omegaInvToL),
   ("HAS_ACCUMULATOR_MPTR", poseidonCtx.vkHeader.hasAccumulator),
   ("ACC_OFFSET_MPTR", poseidonCtx.vkHeader.accOffset),
   ("NUM_ACC_LIMBS_MPTR", poseidonCtx.vkHeader.numAccLimbs),
   ("NUM_ACC_LIMB_BITS_MPTR", poseidonCtx.vkHeader.numAccLimbBits),
   ("G1_BASE_MPTR", poseidonCtx.vkHeader.g1Base),
   ("G2_BASE_MPTR", poseidonCtx.vkHeader.g2Base),
   ("NEG_S_G2_BASE_MPTR", poseidonCtx.vkHeader.negSG2Base)]

/-- Every memory slot Constants.sol declares, paired with the field of
    poseidonMemoryLayout that must hold the same number. Built from the record, not
    copied from the dump: the gate below asks the DUMP what it declares for each
    name and requires the record to agree. -/
def constantsMemoryDecls : List (String × Nat) :=
  [ ("TRANSCRIPT_MPTR", poseidonMemoryLayout.transcriptMptr),
    ("RETURN_MPTR", poseidonMemoryLayout.verifierReturnMptr),
    ("VK_MPTR", poseidonMemoryLayout.vkMptr.value.asUsizeNat),
    ("CHALLENGE_MPTR", poseidonMemoryLayout.challengeMptr.value.asUsizeNat),
    ("THETA_MPTR", poseidonMemoryLayout.thetaMptr.value.asUsizeNat),
    ("BETA_MPTR", poseidonMemoryLayout.betaMptr.value.asUsizeNat),
    ("GAMMA_MPTR", poseidonMemoryLayout.gammaMptr.value.asUsizeNat),
    ("TRASH_CHALLENGE_MPTR", poseidonMemoryLayout.trashChallengeMptr.value.asUsizeNat),
    ("Y_MPTR", poseidonMemoryLayout.yMptr.value.asUsizeNat),
    ("X_MPTR", poseidonMemoryLayout.xMptr.value.asUsizeNat),
    ("X1_MPTR", poseidonMemoryLayout.x1Mptr.value.asUsizeNat),
    ("X2_MPTR", poseidonMemoryLayout.x2Mptr.value.asUsizeNat),
    ("X3_MPTR", poseidonMemoryLayout.x3Mptr.value.asUsizeNat),
    ("X4_MPTR", poseidonMemoryLayout.x4Mptr.value.asUsizeNat),
    ("F_COM_MPTR", poseidonMemoryLayout.fComMptr.value.asUsizeNat),
    ("PI_MPTR", poseidonMemoryLayout.piMptr.value.asUsizeNat),
    ("ACC_LHS_MPTR", poseidonMemoryLayout.accLhsMptr.value.asUsizeNat),
    ("ACC_RHS_MPTR", poseidonMemoryLayout.accRhsMptr.value.asUsizeNat),
    ("X_N_MPTR", poseidonMemoryLayout.xNMptr.value.asUsizeNat),
    ("X_N_MINUS_1_INV_MPTR", poseidonMemoryLayout.xNMinus1InvMptr.value.asUsizeNat),
    ("L_LAST_MPTR", poseidonMemoryLayout.lLastMptr.value.asUsizeNat),
    ("L_BLIND_MPTR", poseidonMemoryLayout.lBlindMptr.value.asUsizeNat),
    ("L_0_MPTR", poseidonMemoryLayout.l0Mptr.value.asUsizeNat),
    ("INSTANCE_EVAL_MPTR", poseidonMemoryLayout.instanceEvalMptr.value.asUsizeNat),
    ("QUOTIENT_EVAL_MPTR", poseidonMemoryLayout.quotientEvalMptr.value.asUsizeNat),
    ("QUOTIENT_MPTR", poseidonMemoryLayout.quotientMptr.value.asUsizeNat),
    ("F_EVAL_MPTR", poseidonMemoryLayout.fEvalMptr.value.asUsizeNat),
    ("V_MPTR", poseidonMemoryLayout.vMptr.value.asUsizeNat),
    ("FINAL_COM_MPTR", poseidonMemoryLayout.finalComMptr.value.asUsizeNat),
    ("PAIRING_LHS_MPTR", poseidonMemoryLayout.pairingLhsMptr.value.asUsizeNat),
    ("PAIRING_RHS_MPTR", poseidonMemoryLayout.pairingRhsMptr.value.asUsizeNat),
    ("ROT_POINTS_MPTR", poseidonMemoryLayout.rotPointsMptr.value.asUsizeNat),
    ("X1_POWERS_MPTR", poseidonMemoryLayout.x1PowersMptr.value.asUsizeNat),
    ("Q_COM_MPTR", poseidonMemoryLayout.qComMptr.value.asUsizeNat),
    ("Q_EVAL_SET_MPTR", poseidonMemoryLayout.qEvalSetMptr.value.asUsizeNat),
    ("Q_EVAL_CPTR_MPTR", poseidonMemoryLayout.qEvalCptrMptr.value.asUsizeNat),
    ("G1_IDENTITY_MPTR", poseidonMemoryLayout.g1IdentityMptr.value.asUsizeNat),
    ("REVERSED_EVALS_MPTR", poseidonMemoryLayout.reversedEvalsMptr.value.asUsizeNat),
    ("SELECTOR_ACC_MPTR", poseidonMemoryLayout.selectorAccMptr),
    ("QUOTIENT_RETURN_MPTR", poseidonMemoryLayout.quotientReturnMptr),
    ("BATCH_INV_SCRATCH_MPTR", poseidonMemoryLayout.batchInvertScratchMptr),
    ("LAGRANGE_DENOMS_MPTR", poseidonMemoryLayout.lagrangeDenomsMptr),
    ("TRACE_U256_MPTR", poseidonMemoryLayout.traceU256Mptr),
    ("ADVICE_COMMS_MPTR_BASE", poseidonMemoryLayout.adviceCommsMptrBase.value.asUsizeNat),
    ("LOOKUP_M_COMMS_MPTR_BASE", poseidonMemoryLayout.lookupMCommsMptrBase.value.asUsizeNat),
    ("PERM_Z_COMMS_MPTR_BASE", poseidonMemoryLayout.permZCommsMptrBase.value.asUsizeNat),
    ("LOOKUP_HELPER_COMMS_MPTR_BASE", poseidonMemoryLayout.lookupHelperCommsMptrBase.value.asUsizeNat),
    ("LOOKUP_Z_COMMS_MPTR_BASE", poseidonMemoryLayout.lookupZCommsMptrBase.value.asUsizeNat),
    ("TRASHCAN_COMMS_MPTR_BASE", poseidonMemoryLayout.trashcanCommsMptrBase.value.asUsizeNat),
    ("QUOTIENT_LIMB_COMMS_MPTR_BASE", poseidonMemoryLayout.quotientLimbCommsMptrBase.value.asUsizeNat)
  ]

/-- GATE 77 (anti-self-fulfilment, hazard 4 adjacent). The transcribed memory layout
    is checked three ways: (a) every slot above equals what the artifact declares for
    that name, so a mistyped digit in the transcription is a red; (b) the seven fixed
    low-memory pointers and the scalar-inversion anchor equal Layout.lean's OWN
    ported constants and MEM:1039's rule - a channel the artifact does not control,
    which is what makes this more than a copy; and (c)] the whole record passes the
    ported `VerifierMemoryLayout.validate`. The VK-header offsets are checked the
    same way against the derived *_MPTR lines, and the four decimal gas bounds
    against templateConstantsDefault, which is Models.lean's port of the Rust
    Default impl and reaches the render through a channel the dump cannot touch. -/
def constants_memoryMatches_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (constantsMemoryDecls.length == 50
    && constantsMemoryDecls.all (fun (n, v) => qHexHere sol (" " ++ n ++ " = 0x") == some v)
    && poseidonMemoryLayout.transcriptMptr == transcriptBufferStart
    && poseidonMemoryLayout.verifierReturnMptr == verifierReturnBufferStart
    && poseidonMemoryLayout.quotientReturnMptr == quotientReturnBufferStart
    && poseidonMemoryLayout.constructorSmokeScratchMptr == lowMemoryScratchStart
    && poseidonMemoryLayout.pcsPairingScratchMptr == pcsPairingScratchStart
    && poseidonMemoryLayout.accumulatorPairingBatchMptr == accumulatorPairingBatchPtr
    && poseidonMemoryLayout.finalPairingScratchMptr == finalPairingScratchStart
    && poseidonMemoryLayout.scalarInvScratchMptr == poseidonCtx.vkMptr - modexpScratchBytes
    && poseidonMemoryLayout.vkMptr.value.asUsizeNat == poseidonCtx.vkMptr
    && poseidonMemoryLayout.scalarInvScratchMptr == poseidonCtx.scalarInvScratchMptr
    && poseidonMemoryLayout.finalPairingScratchMptr == poseidonCtx.finalPairingScratchMptr
    && poseidonMemoryLayout.accumulatorPairingBatchMptr == poseidonCtx.accumulatorPairingBatchMptr
    && poseidonMemoryLayout.validate.isOk
    && qHexHere sol "        RETURN_MPTR = 0x" == some poseidonMemoryLayout.verifierReturnMptr
    && qHexHere sol "    TRANSCRIPT_MPTR = 0x" == some poseidonMemoryLayout.transcriptMptr
    && constantsVkHeaderDecls.all (fun (n, w) =>
         qHexHere sol (" " ++ n ++ " = 0x") == some (poseidonCtx.vkMptr + w * 32))
    && constantsVkHeaderDecls.length == 14)

/-- GATE 78 (anti-self-fulfilment on the profile inputs). vk_len, the VK codehash,
    BUILD_ID, the two ABI cursors and the smoke gas bound are re-read out of the
    artifact and required to equal the fields of poseidonCtx the render puts there.
    The four DECIMAL gas bounds are pinned against templateConstantsDefault, i.e.
    against Models.lean's port of the Rust Default impl rather than against the
    dump, which is the only direction in this file that is not self-fulfilling. -/
def constants_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (qNatAfter sol "EXPECTED_VK_PAYLOAD_LENGTH = " == some poseidonCtx.vkLen
    && qNatAfter sol "EXPECTED_VK_LENGTH = " == some (poseidonCtx.vkLen + 1)
    && qHexHere sol "EXPECTED_VK_CODEHASH_WORD = 0x" == poseidonCtx.expectedVkCodehash.map (·.toNat)
    && qHexHere sol "BUILD_ID = 0x" == some poseidonCtx.buildId.toNat
    && qHexHere sol "    PROOF_CPTR = 0x" == some poseidonCtx.proofCptr.value.asUsizeNat
    && qHexHere sol "NUM_INSTANCE_CPTR = 0x" == some poseidonCtx.numInstanceCptr
    && qHexHere sol "     INSTANCE_CPTR = 0x" == some poseidonCtx.instanceCptr
    && qNatAfter sol "G1MSM_GAS_SMOKE = " == some poseidonCtx.constructorG1msmSmokeGas
    && qNatAfter sol "G1ADD_GAS = " == some templateConstantsDefault.gas.g1add
    && qNatAfter sol "G1MSM_GAS_1PAIR = " == some templateConstantsDefault.gas.g1msmOnePair
    && qNatAfter sol "PAIRING_GAS_2PAIR = " == some templateConstantsDefault.gas.pairingTwoPair
    && qNatAfter sol "MODEXP_GAS = " == some templateConstantsDefault.gas.modexp
    && occ sol "ACC_RHS_MSM_GAS" == 0 && occ sol "AUTHORIZED_QUOTIENT" == 0
    && poseidonCtx.expectedQuotientLen == none
    && (match poseidonCtx.quotientExternal with | none => true | _ => false)
    && (match poseidonCtx.quotientDirect with | none => true | _ => false)
    && poseidonCtx.expectedHasAccumulator == false)
/-- GATE 79 (THE HEADLINE NUMBER). The six partials together account for 52,894
    bytes of the deployed artifact - 30.1% of its 175,908 - and until this package
    not one of them was produced by a Lean function. This gate adds the six
    deployed renders up and requires the total, which is the quantity the P-13
    split left unassigned and the quantity Contracts.lean gate 10 reports as gaps. -/
def p13e_bytesNowRendered_ok : IO Bool :=
  readDump >>= fun sol =>
  let rs := [renderConstants poseidonCtx, renderPrecompileSmoke poseidonCtx,
             renderConstructors poseidonCtx, renderTraceAndGasHelpers poseidonCtx,
             renderPcs poseidonCtx (pcsDeployedComputations sol),
             renderTraceReturn poseidonCtx]
  pure (rs.length == 6 && (rs.map String.length).sum == 52894
    && (rs.map String.length) == [13873, 14414, 733, 0, 23311, 563]
    && 52894 * 100 < 175908 * 31 && 52894 * 100 > 175908 * 30)

/-- The deployed TraceReturn arm as the vendored AST, and the same three statements
    built with raw constructors. `fail` is a user function (AssemblyHelpers.yul:4);
    mstore and ret are dialect builtins, and `ret` is the dialect name for the
    `return` opcode (EVMOp.lean:26, :53, :169). -/
def traceReturn_deployedRegion : String := renderTraceReturn poseidonCtx

def traceReturn_ast : Block EVM.Op := yul% {
  if iszero(success) { fail(ERR_PROOF_REJECTED) }
  mstore(RETURN_MPTR, 1)
  return(RETURN_MPTR, 0x20)
}

def traceReturn_direct : Block EVM.Op :=
  [ Stmt.cond (binOp EVM.Op.iszero [varX "success"])
      [stmtE (usrFn "fail" [varX "ERR_PROOF_REJECTED"])]
  , stmtE (binOp EVM.Op.mstore [varX "RETURN_MPTR", Expr.lit (Literal.number 1)])
  , stmtE (binOp EVM.Op.ret [varX "RETURN_MPTR", Expr.lit (Literal.number 0x20)]) ]

/-- GATE 80 (STRUCTURAL, D-P13 - hazard 3 answered for TraceReturn). The deployed
    render IS expressible as a Yul.Block: three statements, no bindings, every
    identifier supplied by the enclosing frame. This gate tokenises the rendered
    bytes and requires the same token stream as EVM.print of the quotation, and then
    requires the quotation to equal the raw-constructor AST under stmtsBeq - the
    relation Phase 5's irCheck will use. It is NOT a byte gate and does not
    substitute for gate 76: the token relation cannot see the four-space include
    boundary or the leading blank line, and stmtsBeq cannot see a wrong hex
    spelling. What a later traceReturn_spec would induct over is named on the render:
    the terminal arm choice here, and the six regions of the trace block that the
    deployed profile does not render. -/
def traceReturn_astAgrees_ok : Bool :=
  yulTokens ("{" ++ traceReturn_deployedRegion ++ "}") == yulTokens (EVM.print traceReturn_ast)
    && SyntaxEq.stmtsBeq traceReturn_ast traceReturn_direct

/-- A one-block synthetic render, for the structural check: the template's own brace
    nesting with the generated parameter replaced by two readable lines. -/
def pcsSynthRender : String := renderPcs poseidonCtx [["let x := 1", "mstore(0x80, x)"]]

def pcsSynth_ast : Block EVM.Op := yul% {
  {
    {
      let x := 1
      mstore(0x80, x)
    }
  }
}

/-- GATE 81 (STRUCTURAL, D-P13 - hazard 3 answered for Pcs). What IS expressible as
    a Yul.Block is the template's SKELETON: one outer block containing one sibling
    block per generated sub-block. With a synthetic one-block parameter the render
    tokenises to exactly that AST, which is the structural content of the partial.
    What is NOT expressible is the deployed render as a whole: its 345 generated
    lines are opaque Strings to this port (the multi-prepare lowering pass is P-09/
    P-10 territory), so a pcs_spec would state a theorem over the parameter list -
    for every block b, the frame after emitting b equals the frame the lowering pass
    computes - and induct over `pcsComputations`, not over the rendered text. The
    brace-count clauses below are the same claim at byte level: eight blocks, eight
    closers, one outer pair, and the nesting is well formed. -/
def pcs_structure_ok : Bool :=
  yulTokens ("{" ++ pcsSynthRender ++ "}") == yulTokens (EVM.print pcsSynth_ast)
    && occ pcsSynthRender "\n            {" == 1 && occ pcsSynthRender "\n            }" == 1
    && occ pcsSynthRender "\n                {" == 1 && occ pcsSynthRender "\n                }" == 1
    && (pcsSynthRender.toList.filter (fun c => c == '{')).length
       == (pcsSynthRender.toList.filter (fun c => c == '}')).length
    && lineCount pcsSynthRender == 19

/-- GATE 82 (R-41). Nine profile inputs Constants.sol interpolates, perturbed one at
    a time inside this gate's own scope: the render changes and stops occurring in
    the artifact. -/
def perturb_constantsValues_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderConstants poseidonCtx
  let edits : List (PartialCtx -> PartialCtx) :=
    [ fun c => { c with vkLen := c.vkLen + 1 },
      fun c => { c with expectedVkCodehash := some 1 },
      fun c => { c with buildId := 1 },
      fun c => { c with constructorG1msmSmokeGas := c.constructorG1msmSmokeGas + 1 },
      fun c => { c with numInstanceCptr := c.numInstanceCptr + 0x20 },
      fun c => { c with instanceCptr := c.instanceCptr + 0x20 },
      fun c => { c with proofCptr := Ptr.add c.proofCptr 1 },
      fun c => { c with vkHeader := { c.vkHeader with k := c.vkHeader.k + 1 } } ]
  let truncated := renderConstants { poseidonCtx with expectedVkCodehash := none }
  pure (occ sol dep == 1 && dep.length == 13873
    && edits.all (fun f => let r := renderConstants (f poseidonCtx); r != dep && occ sol r == 0)
    && edits.length == 8
    && truncated != dep && truncated.length < dep.length && occ sol truncated == 1)

/-- GATE 83 (R-41). Eight memory slots, perturbed one at a time: the render changes
    and disappears. These are the slots a transcription typo would hit, and the
    reason gate 77 exists: a slot perturbation that still produced artifact bytes
    would mean the render was not reading the record at all. -/
def perturb_constantsMemory_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderConstants poseidonCtx
  let edits : List (PartialCtx -> PartialCtx) :=
    [ fun c => { c with memory := { c.memory with thetaMptr := ptrMemory (valueFromNat 0x3ae1) } },
      fun c => { c with memory := { c.memory with xMptr := ptrMemory (valueFromNat 0x0000) } },
      fun c => { c with memory := { c.memory with traceU256Mptr := 0x83c1 } },
      fun c => { c with memory := { c.memory with selectorAccMptr := 0x65e1 } },
      fun c => { c with memory := { c.memory with adviceCommsMptrBase := ptrMemory (valueFromNat 0x5c61) } },
      fun c => { c with memory := { c.memory with qEvalCptrMptr := ptrMemory (valueFromNat 0x5401) } },
      fun c => { c with memory := { c.memory with quotientMptr := ptrMemory (valueFromNat 0x3f01) } },
      fun c => { c with memory := { c.memory with vkMptr := ptrMemory (valueFromNat 0x2901) } } ]
  pure (occ sol dep == 1
    && edits.all (fun f => let r := renderConstants (f poseidonCtx); r != dep && occ sol r == 0)
    && edits.length == 8)

/-- GATE 84 (R-41). The generated PCS parameter, perturbed six ways. The fifth and
    sixth clauses are the point: the BLOCK PARTITION is observable here, because each
    block gets its own numbered comment and its own braces, so [[a,b]] and [[a],[b]]
    render differently - the property P-13c had to say out loud that its four flat
    quotient lists do NOT have. -/
def perturb_pcsBlocks_ok : IO Bool :=
  readDump >>= fun sol =>
  let blocks := pcsDeployedComputations sol
  let dep := renderPcs poseidonCtx blocks
  let swap := match blocks with
    | a :: b :: rest => b :: a :: rest
    | _ => blocks
  let edited := blocks.map (fun l => l ++ ["// extra"])
  let prepended := blocks.map (fun l => ["// extra"] ++ l)
  let reddening := [blocks.reverse, swap, edited, prepended,
    blocks.take 7, blocks.drop 1]
  pure (occ sol dep == 1 && dep.length == 23311 && blocks.length == 8
    && reddening.all (fun v => let r := renderPcs poseidonCtx v; r != dep && occ sol r == 0)
    && reddening.length == 6
    && (renderPcs poseidonCtx []).length == 662 && lineCount (renderPcs poseidonCtx []) == 12
    && occ sol (renderPcs poseidonCtx []) == 0
    && renderPcs poseidonCtx [["a", "b"]] != renderPcs poseidonCtx [["a"], ["b"]]
    && (renderPcs poseidonCtx [["a", "b"]]).length + 245
       == (renderPcs poseidonCtx [["a"], ["b"]]).length)

/-- GATE 85 (R-41). TraceReturn's flag-driven arms. The deployed profile takes the
    else arm; flipping trace swaps in the 48-line emission block, which is absent
    from the artifact, and the two guards inside it (num_trashcans,
    expected_has_accumulator) and the nested user-phase loop each change the bytes.
    The last clause is the zero-iteration law: a phase with two challenges adds two
    lines, a phase with none adds none. -/
def perturb_traceReturnFlags_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderTraceReturn poseidonCtx
  let traced := renderTraceReturn { poseidonCtx with trace := true }
  let noTrash := renderTraceReturn { poseidonCtx with trace := true, numTrashcans := 0 }
  let withAcc := renderTraceReturn { poseidonCtx with trace := true, expectedHasAccumulator := true }
  let twoChal := renderTraceReturn { poseidonCtx with trace := true, userPhases := [{ adviceBytes := 0x400, numChallenges := 2, challengeOffset := 0 }] }
  pure (occ sol dep == 1 && dep.length == 563
    && traced != dep && occ sol traced == 0 && traced.length == 2451
    && traced.contains "trace_u256(1,  mload(VK_DIGEST_MPTR))"
    && ! noTrash.contains "TRASH_CHALLENGE_MPTR" && noTrash.length == traced.length - 56
    && withAcc.contains "trace_point(29, ACC_LHS_MPTR)" && withAcc.length == traced.length + 84
    && (twoChal.splitOn "\n").length == (traced.splitOn "\n").length + 2
    && twoChal.contains "trace_u256(1000, mload(add(CHALLENGE_MPTR, 0x00)))")

/-- GATE 86 (R-41). The four arms of Constructors.sol, selected by flipping the two
    matches: each arm is distinct text, and only the deployed one occurs in the
    artifact. The two empty `when Some with (_)` arms of the inner
    expected_quotient_codehash matches are asserted to be empty, which is the
    template's own shape at :35-38 and :78-81 and the reason the None-arm render
    ends with a bare closing brace. -/
def perturb_constructorsArms_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := renderConstructors poseidonCtx
  let qext : QuotientExternal :=
    { frameBase := 0x4000, frameLen := 0x2000, outputLen := 0xc0, magic := quotientExternalMagic }
  let embedded := renderConstructors { poseidonCtx with expectedVkCodehash := none }
  let split := renderConstructors { poseidonCtx with quotientExternal := some qext }
  let both := renderConstructors { poseidonCtx with quotientExternal := some qext, expectedQuotientCodehash := some 1, expectedQuotientLen := some 4096 }
  pure (occ sol dep == 1 && dep.length == 733
    && embedded != dep && occ sol embedded == 0 && embedded.contains "constructor() {"
    && split != dep && occ sol split == 0 && split.contains "constructor(address authorizedVk, address authorizedQuotient)"
    && both != split && occ sol both == 0 && both.contains "EXPECTED_QUOTIENT_CODEHASH"
    && renderConstructors { poseidonCtx with expectedQuotientCodehash := some 1 } == dep)

/-- GATE 87 (hazard 1, demonstrated rather than hidden). For each of the six
    renders, a strict prefix still occurs exactly once in the artifact: occursOnce
    plus a prefix boundary is satisfied by a TRUNCATED render, which is the hole
    P-13c found in its own gate and P-13d showed in gate 20. Every byte gate above
    therefore asserts a length alongside the occurrence, and gate 79 asserts the
    six lengths sum to 52,894. -/
def perturb_truncation13e_ok : IO Bool :=
  readDump >>= fun sol =>
  let rs := [renderConstants poseidonCtx, renderPrecompileSmoke poseidonCtx,
             renderConstructors poseidonCtx, renderPcs poseidonCtx (pcsDeployedComputations sol),
             renderTraceReturn poseidonCtx]
  pure (rs.length == 5 && rs.all (fun r => occ sol r == 1
    && occ sol ((r.drop 1).toString) == 1 && ((r.drop 1).toString).length < r.length
    && occ sol ((r.take (r.length / 2)).toString) == 1)
    && occ sol (renderTraceAndGasHelpers poseidonCtx) != 1)

/-- GATE 88 (R-41, the honest non-bites). What no gate in this section can see,
    asserted as absence rather than hidden as a passing test:

    * The trace arm of TraceReturn (2,451 bytes) and of Pcs, and the gas-checkpoint
      arms of both: no tracked artifact renders them, so a typo inside them reddens
      nothing. Measured: a same-length typo inside the trace-only line
      `trace_u256(35, success)` reddened NO gate, because gate 76 pins only the
      else arm and gate 85 only checks that the trace arm differs and is absent.
    * The Some arm of the Constants quotient_external match and the
      expected_has_accumulator if: AUTHORIZED_QUOTIENT and ACC_RHS_MSM_GAS do not
      occur in the artifact at all, so poseidonCtx.expectedQuotientLen and
      accRhsMsmGas are unconstrained by any byte gate. Gate 78 asserts their
      ABSENCE rather than their values.
    * The 345 generated PCS lines: they are read out of the artifact and rendered
      back, so a change to the lowering pass cannot redden gate 75 - only the
      template's own 42 lines are pinned. This is stated on the render.
    * The inert VerifierMemoryLayout slots (quotientTmp, quotientStack, the PCS
      window scratch, commsMptrBase): no deployed partial renders them; they are
      set to validate-legal anchors and gate 77 only proves the record passes
      validate, not that those numbers are the generator's.

    What DID bite is recorded in the package report: 34 source mutations were run
    across gates 82-86 and gate 77, and the count that failed to redden is the
    four-item list above. -/
def inertFields13e_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol "AUTHORIZED_QUOTIENT" == 0 && occ sol "ACC_RHS_MSM_GAS" == 0
    && occ sol "EXPECTED_QUOTIENT_LENGTH" == 0 && occ sol "trace_u256" == 0
    && occ sol "gas_checkpoint" == 0 && occ sol "trace_point" == 0
    && poseidonCtx.expectedQuotientLen == none && poseidonCtx.accRhsMsmGas == 0
    && poseidonCtx.trace == false && poseidonCtx.gasCheckpoints == false
    && ! ((renderTraceReturn poseidonCtx).contains "trace_u256(35, success)"))



/-- GATE 89 (FINDING, and the reason a later pcs_spec need not read the artifact).
    The eight generated sub-blocks are not opaque: their HEAD lines are the
    landmarks of the ported emitter. Kzg.lean:1320 `computations` (rust:
    kzg/mod.rs:930, `Except Fault (List (List String))` - the SAME type as this
    render's parameter) is already in the tree, and the deployed block sequence is
    exactly its documented shape: one rotation-walk block, one x1-powers block
    (present because nbX1Powers > 0), one q_eval_set block per intermediate set
    (three here), the f_eval Horner, the fused final MSM, and the pairing staging.
    So the 23,311-byte region this gate reads back out of the artifact is not
    unported - it is ported, and what is missing is only the deployed
    ConstraintSystemMeta and Data to feed it. That is the concrete next step for
    P-SE step P5 (survey.md:741 and :1040 ask for exactly this), and it is why the
    parameter is a List (List String) and not a String blob. -/
def pcs_blocksMatchEmitterShape_ok : IO Bool :=
  readDump >>= fun sol =>
  let blocks := pcsDeployedComputations sol
  let firstOf (xs : List String) : String := match xs with | x :: _ => x | [] => ""
  let nth (i : Nat) : String := match (blocks.drop i).head? with
    | some b => firstOf b
    | none => ""
  pure (blocks.length == 8
    && nth 0 == "// 3 distinct rotation(s)"
    && nth 1 == "// pre-compute 33 x1 power(s)"
    && (blocks.filter fun b => (firstOf b).startsWith "// q_eval_set[").length == 3
    && nth 5 == "// f_eval via Horner over 3 reversed set(s)"
    && nth 6 == "// build final_com and v (KZG single-opening proof, fused MSM)"
    && nth 7 == "// Scale z*pi - vG before the final pairing check")

/-! ### P-AST3b: the VkLoading snapshots

    The two quotations below are the record relation for the vkLoading slice: an
    independent elaboration of the deployed bytes through the vendored `yul%` parser,
    which GenAst's `emitVkLoading_beq_ok` then compares the constructor-built AST
    against. They are transcribed from the same template region the text port renders
    (T:partials/verifier/VkLoading.yul:1-141, deployed at D:1103-1176), in the same
    shape `qalLinearization_ast` and `lagrange_ast` already establish - the parser is
    not the converter, so a gate between them is not self-fulfilling (D-P30 clause 2). -/

/-- The deployed VK-loading block: the external-VK arm (poseidonCtx.embeddedVk is none,
    so the extcodesize / extcodehash guard and the extcodecopy are what the artifact
    carries), the six header cross-checks, and the three ABI-envelope checks. The four
    accumulator words are the deployed profile's zeros, read off the artifact and not
    chosen: gate 90 below re-derives them from the dump's own lines. -/
def vkLoading_ast : Block EVM.Op := yul% {
  {
    if iszero(and(
        eq(extcodesize(vk), EXPECTED_VK_LENGTH),
        eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)
    )) { fail(ERR_VK_MISMATCH) }
    extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)
    success := and(success, eq(mload(NUM_INSTANCES_MPTR), 1))
    success := and(success, eq(mload(K_MPTR), 6))
    success := and(success, eq(mload(HAS_ACCUMULATOR_MPTR), 0))
    success := and(success, eq(mload(ACC_OFFSET_MPTR), 0))
    success := and(success, eq(mload(NUM_ACC_LIMBS_MPTR), 0))
    success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), 0))
    if iszero(success) { fail(ERR_VK_MISMATCH) }
    success := and(success, eq(0x10e0, calldataload(PROOF_LEN_CPTR)))
    success := and(success, eq(1, calldataload(NUM_INSTANCE_CPTR)))
    success := and(
        success,
        eq(calldatasize(), add(INSTANCE_CPTR, 0x20))
    )
    if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }
  }
}

/-- The accumulator precheck the same template appends when
    expected_has_accumulator is set (VkLoading.yul:115-137). The deployed artifact does
    NOT contain it - gate 44 pins that flipping the flag changes the bytes and breaks
    the artifact match - so this is the arm the text port reaches only through an
    override, quoted from the render rather than from the dump, exactly as
    `accBatch_snapshot` is in GenAst. -/
def vkLoadingAccArm_ast : Block EVM.Op := yul% {
  let acc_precompile_failed := 0
  success, acc_precompile_failed := validate_public_accumulator(success, r)
  if iszero(success) {
    if acc_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
    fail(ERR_BAD_POINT_ENCODING)
  }
}

/-- GATE 90 (STRUCTURAL, render -> AST, and the slice's provenance). The rendered
    vkLoading partial tokenises to `vkLoading_ast`, and the render is the deployed
    slice: 4,494 bytes / 74 lines occurring EXACTLY ONCE in the tracked artifact. The
    last three conjuncts are the anti-self-fulfilment half: the six header words the
    quotation pins to 0 / 0 / 0 / 0 are re-read from the dump's own lines, so the
    snapshot matches because the artifact says so and not because the transcription
    agreed with itself. -/
def vkLoading_astAgrees_ok : IO Bool :=
  readDump >>= fun sol =>
  let r := renderVkLoading poseidonCtx
  pure (r.length == 4494 && lineCount r == 74 && occ sol r == 1 &&
    yulTokens ("{" ++ r ++ "}") == yulTokens (EVM.print vkLoading_ast) &&
    sol.contains "eq(mload(HAS_ACCUMULATOR_MPTR), 0)" &&
    sol.contains "eq(mload(ACC_OFFSET_MPTR), 0)" &&
    sol.contains "eq(mload(NUM_ACC_LIMBS_MPTR), 0)" &&
    sol.contains "eq(mload(NUM_ACC_LIMB_BITS_MPTR), 0)" &&
    sol.contains "eq(mload(NUM_INSTANCES_MPTR), 1)" &&
    sol.contains "eq(mload(K_MPTR), 6)")

/-- GATE 91 (STRUCTURAL, the untaken arm). The render with the accumulator flag flipped
    tokenises to the arm quotation appended to the deployed block: the arm is gated for
    SELECTION and for content, never only for existence (D-P30 clause 2). -/
def vkLoadingAccArm_astAgrees_ok : Bool :=
  yulTokens ("{" ++ renderVkLoading
    { poseidonCtx with expectedHasAccumulator := true } ++ "}") ==
    yulTokens (EVM.print (vkLoading_ast ++ vkLoadingAccArm_ast))

end VerifierPartialKats

#eval Midfall.Generator.VerifierPartialKats.vkLoading_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.vkLoadingAccArm_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.pcs_blocksMatchEmitterShape_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.p13e_artifactsReachable_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.p13e_noOrphanTemplate_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.constants_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.precompileSmoke_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.constructors_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.traceAndGasHelpers_structuralEmpty_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.pcs_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.traceReturn_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.constants_memoryMatches_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.constants_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.p13e_bytesNowRendered_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.traceReturn_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.pcs_structure_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_constantsValues_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_constantsMemory_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_pcsBlocks_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_traceReturnFlags_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_constructorsArms_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_truncation13e_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.inertFields13e_ok -- expect true

#eval Midfall.Generator.VerifierPartialKats.artifactsReachable_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.assemblyHelpers_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.vkLoading_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.lagrange_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.finalPairing_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientAndLinearization_ownBytes_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.hexFilter_sitesMatchArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.hexPaddedFilter_matchesVkArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.zeroRenderNewlineLaw_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.includeIndentBoundary_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.finalPairing_deployedArmIsPlain_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.finalPairing_accumulatorArm_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.hazard4_decoderRegionAgreesWithP12_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.poseidonCtx_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.finalPairing_beq_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.finalPairing_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.assemblyHelpers_failAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.lagrange_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientAndLinearization_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_singleSpace_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_newlineDeletion_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_trailingNewline_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_contextValue_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_flagFlip_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_hexSpelling_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_raggedIndent_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.inertFields_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_leadingWhitespaceAbsorbed_note -- expect true
#eval Midfall.Generator.VerifierPartialKats.parser13b_artifactsReachable_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.transcriptProofParser_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.accumulatorHelpers_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parser_hazard1SatisfiesP12Gate22_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parser_canonicityGuardCount_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parserProofLayout_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parser_cursorIdentity_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.acc_deployedRenderIsHelpersOnly_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.acc_syntheticCarriedScalarsArm_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.acc_syntheticCollapsedArm_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.accR25_identityArmIsVerbatim_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.acc_gasNamesAreRenderLiterals_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parser13b_newlineLaw_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_parserContextValue_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_parserFlags_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_accFlagFlip_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.inertFields13b_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.parserTail_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotient13c_artifactsReachable_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientHelpers_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientNumeratorBlock_bytesExact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientAndLinearization_withPartials_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientRegion_span_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientProgram_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.quotientProgram_inertFieldsDerived_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_negation_deployedLine_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_negation_isModelled_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_negation_astAgrees_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.opUsage_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_deployedExercisedRegions_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_allArms_synthetic_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_directArm_synthetic_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb_anchorsUnique_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_quotientProgramScalars_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_quotientOpUsageFlags_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_quotientHelperFlags_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.perturb_quotientGeneratedInput_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.inertFields13c_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb13c_newlineLaw_ok -- expect true
#eval Midfall.Generator.VerifierPartialKats.qnb13c_rightTrimCount_ok -- expect true
