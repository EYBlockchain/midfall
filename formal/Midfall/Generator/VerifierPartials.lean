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


end VerifierPartialKats

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
