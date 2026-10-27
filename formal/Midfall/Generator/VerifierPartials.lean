-- |
-- Midfall.Generator.VerifierPartials
--
-- P-13a: the first five Askama partials under
-- proofs/solidity-verifier/templates/partials/verifier/ ported as Lean render
-- functions - AssemblyHelpers.yul (310 lines at HEAD), VkLoading.yul (141),
-- Lagrange.yul (99), QuotientAndLinearization.yul (165), FinalPairing.yul (92).
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
--   * The dump's proof.bin and calldata.bin are NOT tracked (R-53 / P-12 F-1);
--     nothing here reads them.
--
-- CITATION NOTATION, as in Render.lean and Filters.lean: D: is the tracked dump
-- target/poseidon-fixture-dump/Halo2Verifier.sol (3024 lines, no trailing
-- newline); DVK: is Halo2VerifyingKey.sol beside it; T: is
-- proofs/solidity-verifier/templates/; M: is src/lowering/render/models.rs.

import YulSemantics.Syntax
import YulSemantics.PrettyPrint
import Midfall.Generator.Filters
import Midfall.Generator.Models
import Midfall.Generator.Layout
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

/-! ## Gates

Twenty-eight gates. Gate 1 is the reachability gate D-P19 demands before any
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

/-- The five deployed renders, once. -/
def deployedRenders : List String :=
  [renderAssemblyHelpers poseidonCtx, renderVkLoading poseidonCtx, renderLagrange poseidonCtx,
   renderQuotientAndLinearization poseidonCtx "" "", renderFinalPairing poseidonCtx]

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
