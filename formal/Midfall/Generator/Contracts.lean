-- |
-- Midfall.Generator.Contracts
--
-- P-13d: the three ROOT templates - the contract shells - ported as Lean render
-- functions, plus the include glue that splices the partials into them. rust:
-- T:contracts/Halo2Verifier.sol (232 lines at HEAD),
-- T:contracts/Halo2VerifyingKey.sol (98) and
-- T:contracts/Halo2QuotientEvaluator.sol (170) - 500 lines of Askama between
-- them - together with the three Askama render wrappers at M:820-825,
-- M:955-960 and M:1008-1013, each of which is exactly
-- 'self.render_into(writer)' and nothing else. So one Lean render function per
-- template IS the port of the Rust render method; there is no other code in
-- those impls to port.
--
-- NOTHING HERE IS A PARALLEL RENDER LAYER. PartialCtx, jinjaFor, hexFilter,
-- hexPaddedFilter, printPtr, occ / occursOnce / artifactMatch / includeBoundary,
-- readDump / readVkDump and quotientDeployedCtx are P-13a / P-13b / P-13c's and
-- are reused, not restated. The partial renders this file splices are their
-- render functions. What is new is the shell text and the glue, which no earlier
-- package owned.
--
-- THE ONE THING THIS FILE CAN DO THAT NO EARLIER ONE COULD: a WHOLE-FILE byte
-- gate. Halo2VerifyingKey.sol includes nothing, so its root render is a closed
-- term and can be compared to the tracked DVK artifact in full - every byte,
-- every line, the final newline included. That is gate 12, and it is the first
-- place in the tree where a rendered ROOT template is byte-equal to a committed
-- artifact.
--
-- WHY THERE IS NO WHOLE-FILE GATE FOR Halo2Verifier.sol, and what replaced it.
-- The verifier contract includes thirteen partials and only SEVEN of them have
-- been ported: P-13a did five, P-13b two more, P-13c the two quotient_numerator
-- ones. Six verifier partials have no render function anywhere in the tree -
-- Constants.sol (255 template lines), PrecompileSmoke.sol (216),
-- Constructors.sol (92), TraceAndGasHelpers.yul (23), Pcs.yul (39) and
-- TraceReturn.yul (73): 698 lines of Askama. The full file therefore cannot be
-- produced, and this file does not pretend otherwise. What it does instead is
-- gate the shell TEXT and the GLUE completely: gate 10 walks every shell-owned
-- byte run and every ported partial render through the artifact in order,
-- requires each to occur exactly once, requires the first to start at byte 0 and
-- the last to end at the last byte, and requires the leftover gaps to be exactly
-- the unported regions. That is an accounting, not a sample: a wrong byte
-- anywhere in the shell, a glue that is not the include boundary, or a ported
-- partial that has grown a byte the artifact does not carry, reddens it. Gate 9
-- goes further on one of the six: TraceAndGasHelpers' deployed render is PROVED
-- to be the empty string, because the gap where it should be is exactly the
-- include glue and nothing more.
--
-- HAZARD 3, SAID PLAINLY. Halo2QuotientEvaluator.sol is NOT exercised by the
-- deployed profile at all. The dump directory contains Halo2Verifier.sol and
-- Halo2VerifyingKey.sol and no evaluator file; the verifier artifact contains no
-- 'contract Halo2QuotientEvaluator', no 'fallback() external', no
-- 'QUOTIENT_FRAME_BASE' and no 'AUTHORIZED_QUOTIENT', because quotient_external
-- is None (P-13a's profile note) and the split evaluator is never rendered.
-- Gate 16 asserts that absence from the artifact instead of asserting it in
-- prose. Gates 17 to 19 therefore gate the evaluator SYNTHETICALLY and each says
-- LABEL at the gate: they pin that the arms exist, that the flags discriminate,
-- that the memory constants interpolated are the ones the verifier renders, and
-- that the two included blocks splice byte-identically to the bytes the artifact
-- carries for them. NOT ONE of them is offered as evidence that the Rust would
-- ship these bytes, because there is no artifact to ship.
--
-- HAZARD 1, THE RIGHT-TRIM. The brief said -%} appears at
-- Halo2Verifier.sol:91, 96, 111, 115, 117. Measured at HEAD it appears TWICE, at
-- :91 and :96, both in the quotient_probe if/else. Lines 111, 115 and 117 are
-- LEFT-trims, and neither Halo2VerifyingKey.sol nor Halo2QuotientEvaluator.sol
-- contains a right-trim at all. Gate 5 is the behavioural pin for the two real
-- sites and gate 6 the pin for the left-trim sites the brief conflated with
-- them. The observable is not subtle: without the right-trim the artifact would
-- carry a whitespace-only line at the notice, and gate 5 asserts that the
-- untrimmed form occurs ZERO times.
--
-- THE ROOT FINAL NEWLINE, owned here. Gated twice: gate 4 for the verifier
-- shell, gate 13 for the VK shell. Both tracked artifacts end with '}' and no LF
-- while both template files end with '}' + LF, and both renders reproduce that.
-- Gate 4 also asserts the template's own trailing LF is present in the SOURCE, so
-- the law is a claim about a difference and not about a constant.
--
-- CITATION NOTATION, unchanged: D: is the tracked dump
-- target/poseidon-fixture-dump/Halo2Verifier.sol (3024 lines, 175,908 bytes, no
-- trailing newline); DVK: is Halo2VerifyingKey.sol beside it (271 lines, 26,018
-- bytes, no trailing newline); T: is proofs/solidity-verifier/templates/; M: is
-- src/lowering/render/models.rs.
--
-- D-P17 respected: no Generator.Vk, no Midfall/Instances/. D-P13 respected: every
-- gate below is a BYTE gate or is labelled STRUCTURAL / SYNTHETIC; none is
-- substituted for the other.

import YulSemantics.Syntax
import YulSemantics.PrettyPrint
import Midfall.Generator.Render
import Midfall.Generator.Models
import Midfall.Generator.Layout
import Midfall.Generator.LoweringPlan
import Midfall.Generator.Templates
import Midfall.Generator.VerifierPartials

namespace Midfall.Generator
open Midfall YulSemantics
open Midfall.Generator.VerifierPartialKats

/-! ## The include parameters

The root verifier template has thirteen include holes. They are PARAMETERS of
the render, exactly as P-13a made the two quotient_numerator includes parameters
of renderQuotientAndLinearization: a hole whose bytes another package owns is an
argument, not something to paste. The field order below is verifierIncludes'
order and gate 2 checks it against it. -/

/-- The thirteen include renders of T:contracts/Halo2Verifier.sol, in template
    order. Seven are produced by render functions that already exist; the six
    marked NOT PORTED stay parameters until a later package ports them. -/
structure VerifierParts where
  /-- T:partials/verifier/Constants.sol - NOT PORTED (255 template lines). -/
  constants : String
  /-- T:partials/verifier/PrecompileSmoke.sol - NOT PORTED (216 lines). -/
  precompileSmoke : String
  /-- T:partials/verifier/Constructors.sol - NOT PORTED (92 lines). -/
  constructors : String
  /-- T:partials/verifier/AssemblyHelpers.yul - renderAssemblyHelpers. -/
  assemblyHelpers : String
  /-- T:partials/verifier/AccumulatorHelpers.yul - renderAccumulatorHelpers. -/
  accumulatorHelpers : String
  /-- T:partials/verifier/TraceAndGasHelpers.yul - NOT PORTED (23 lines), and its
      deployed render is the empty string, which gate 9 proves rather than
      assumes. -/
  traceAndGasHelpers : String
  /-- T:partials/verifier/VkLoading.yul - renderVkLoading. -/
  vkLoading : String
  /-- T:partials/verifier/TranscriptProofParser.yul - renderTranscriptProofParser. -/
  transcriptProofParser : String
  /-- T:partials/verifier/Lagrange.yul - renderLagrange. -/
  lagrange : String
  /-- T:partials/verifier/QuotientAndLinearization.yul -
      renderQuotientAndLinearization fed the two quotient_numerator renders. -/
  quotientAndLinearization : String
  /-- T:partials/verifier/Pcs.yul - NOT PORTED (39 lines). -/
  pcs : String
  /-- T:partials/verifier/FinalPairing.yul - renderFinalPairing. -/
  finalPairing : String
  /-- T:partials/verifier/TraceReturn.yul - NOT PORTED (73 lines). -/
  traceReturn : String

/-- The include paths in the order VerifierParts declares its fields, so gate 2
    can tie the record to the registry that scripts/check_golden_provenance.py
    re-reads from the template. -/
def verifierPartPaths : List String :=
  [ "partials/verifier/Constants.sol",
    "partials/verifier/PrecompileSmoke.sol",
    "partials/verifier/Constructors.sol",
    "partials/verifier/AssemblyHelpers.yul",
    "partials/verifier/AccumulatorHelpers.yul",
    "partials/verifier/TraceAndGasHelpers.yul",
    "partials/verifier/VkLoading.yul",
    "partials/verifier/TranscriptProofParser.yul",
    "partials/verifier/Lagrange.yul",
    "partials/verifier/QuotientAndLinearization.yul",
    "partials/verifier/Pcs.yul",
    "partials/verifier/FinalPairing.yul",
    "partials/verifier/TraceReturn.yul" ]

/-- The three template expressions the root verifier template interpolates that
    PartialCtx does not carry: abi_selector_bytes, abi_proof_head_offset and
    abi_instances_head_cptr (M:543-545). They are added here rather than to
    PartialCtx because VerifierPartials.lean is P-13a's file and this package does
    not edit another package's record. -/
structure RootCtx where
  base : PartialCtx
  /-- M:543 abi_selector_bytes. -/
  abiSelectorBytes : Nat
  /-- M:544 abi_proof_head_offset. -/
  abiProofHeadOffset : Nat
  /-- M:545 abi_instances_head_cptr. -/
  abiInstancesHeadCptr : Nat

/-- The deployed profile plus the three ABI numbers. The ABI numbers are not
    pasted-and-hoped: gate 7 re-reads all three out of the artifact's own guard
    line (D:586) and fails if they disagree. -/
def poseidonRootCtx : RootCtx :=
  { base := poseidonCtx
    abiSelectorBytes := 4
    abiProofHeadOffset := 0x40
    abiInstancesHeadCptr := 0x24 }

/-! ## The root templates' own text

Every literal below is one text node of the Askama source after the whitespace
trimming the left-dash and right-dash markers ask for, transcribed by a one-pass
walk of the template file (the walker is not committed; the gates are what make
the transcription trustworthy, exactly as in VerifierPartials.lean). Nothing was
retyped by hand and nothing was copied from the artifact. The first literal is
the whole template text before the first include, so the artifact's first 84
lines are it verbatim; the last two are the closing braces of the two contract
shells, each WITHOUT the final newline the template file carries. -/

--   vhPrologue template text before the first include: licence, pinned pragma, NatSpec,
--   contract opener, the eight typed errors, and the four spaces that indent the
--   Constants.sol include line.
--   vhPrologue the template text before the first include: licence, pinned pragma, the
--   whole NatSpec block, the contract opener and the eight typed errors. Ends with the
--   four spaces that indent the Constants.sol include line, which is why D:85 is a
--   whitespace-only line: Constants.sol opens with a match tag whose arm body starts on
--   the next line.
def vhPrologue : String := "// SPDX-License-Identifier: CC0-1.0\n// Pinned, not floating. Two properties of this artifact are compiler- and\n// optimiser-dependent, and neither is visible in the source:\n//   1. The generated layout writes absolute addresses from TRANSCRIPT_MPTR\n//      upward. That is only safe while solc's stack-spill reservation stays\n//      below it -- measured 0x8c0 on 0.8.24 and 0x8e0 on 0.8.26+, so it is not\n//      a constant this file controls. verifyProof now asserts the separation.\n//   2. Runtime size depends on --optimize-runs. Measured: 0.8.24 at runs=1\n//      emits 29,567 bytes and 0.8.30 at runs=100000 emits 29,836 -- both over\n//      the EIP-170 24,576-byte limit, so neither can be deployed. Only the\n//      pinned (version, runs) pair is known to produce a deployable contract.\n// A floating `^0.8.24` advertises compatibility this contract does not have.\npragma solidity 0.8.30;\n\n/// @title Halo2 BLS12-381 KZG verifier.\n/// @notice Circuit-specialized verifier for Midfall/midnight-proofs Halo2\n/// proofs rendered by this repository's Rust generator.\n/// @dev This contract ports the verifier flow from\n/// `midfall/proofs/src/plonk/verifier.rs`, the Keccak transcript comments from\n/// `midfall/proofs/src/transcript/implementors.rs`, and the KZG multi-open\n/// comments from `midfall/proofs/src/poly/kzg/mod.rs`.\n/// @dev It is not a generic verifier. The proof layout, VK payload, quotient\n/// identity program, memory layout, and optional quotient evaluator are all\n/// generated for one `VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>`.\n///\n/// Halo2 KZG verifier for the BLS12-381 curve, midnight-proofs flavour.\n///\n/// Differences vs the original BN254 / halo2 v0.4 template:\n//\n/// - BLS12-381 base field Fp is 381 bits and does not fit in a uint256.\n///   Each Fp coord is encoded EIP-2537 padded (16 zero bytes + 48 bytes).\n///   A G1 point is 128 bytes (4 words); a G2 point is 256 bytes (8).\n/// - Calldata carries G1 commitments in uncompressed EIP-2537 padded\n///   form (4 words = 128 bytes per point: x_hi, x_lo, y_hi, y_lo). The\n///   proof bytes produced by midnight-proofs prover are repacked off\n///   chain (compressed -> uncompressed) before being passed to\n///   `verifyProof`. The verifier hashes the uncompressed 128-byte form into\n///   the transcript verbatim, matching `Hashable<Keccak256> for G1Projective::to_input`;\n///   see `common_uncompressed_g1`.\n/// - Transcript `common` absorbs raw inputs in order. `squeeze` computes one\n///   Keccak digest, resets the transcript buffer to that digest, then samples\n///   by interpreting the digest as a big-endian integer modulo r.\n/// - Scalar inversion uses modexp(scalar, r-2, r).\n/// - Constructors run deployment-time smoke tests for MCOPY and the EIP-2537\n///   precompiles using identity inputs. Compile with Solidity >=0.8.24 and\n///   deploy only on chains/forks that support MCOPY and EIP-2537.\ncontract Halo2Verifier {\n    // ----------------------------------------------------------------------\n    // Typed failure taxonomy (P4/L-3, docs/audit/HALO2_VERIFIER_REVIEW).\n    // verifyProof is success-or-revert; these errors let integrators and\n    // incident responders distinguish malformed calldata from a swapped VK,\n    // a non-canonical scalar, a failed precompile, or a rejected proof.\n    // Constructor smoke probes intentionally keep bare reverts -- they report\n    // a chain-capability failure, and the deployment transaction identifies\n    // itself. The one constructor exception is the memory-layout guard\n    // (MF-2), which reports a BUILD fault and is typed on both paths.\n    // ----------------------------------------------------------------------\n    /// @notice Calldata does not match the generated ABI shape (heads,\n    ///         lengths, instance count, or exact calldatasize).\n    error BadCalldataShape();\n    /// @notice The pinned verifying-key (or VK header cross-check) does not\n    ///         match the generated constants.\n    error VkMismatch();\n    /// @notice A public instance or proof scalar is >= the BLS12-381 scalar\n    ///         modulus.\n    error NonCanonicalScalar();\n    /// @notice A proof point violates the EIP-2537 padded encoding or its\n    ///         coordinates are >= the base-field modulus.\n    error BadPointEncoding();\n    /// @notice A precompile call failed or returned an unexpected size.\n    error PrecompileFailed();\n    /// @notice The final pairing (or its staging) rejected the proof.\n    error ProofRejected();\n    /// @notice The pinned quotient program or evaluator violated a structural\n    ///         invariant (bad opcode, operand out of window, stack misuse,\n    ///         or evaluator frame mismatch).\n    error QuotientProgramInvalid();\n    /// @notice solc's stack-spill reservation overlaps the generated absolute\n    ///         memory layout. This is a BUILD fault, not a proof fault: the\n    ///         artifact was compiled with a (version, optimiser) pair whose\n    ///         free-memory pointer starts at or above TRANSCRIPT_MPTR, so no\n    ///         input can ever verify. Redeploy from the pinned toolchain.\n    error MemoryLayoutViolated();\n\n    "

--   includeGlue the glue between two consecutive include lines: the LF that ends the
--   include line, the blank separator line, and the four-space indent of the next
--   include. P-13a rule 3. The artifact contains it 114 times, which is why no gate
--   searches for it alone.
def includeGlue : String := "\n\n    "

--   vhProbeNotice the quotient_probe = true arm of the only right-trimming tags in the
--   corpus, T:contracts/Halo2Verifier.sol:91 and :96. No artifact covers it - see
--   inertFields13d_ok.
def vhProbeNotice : String := "/// @notice TEST-ONLY QUOTIENT PROBE, NOT A VERIFIER: returns the quotient\n    /// section's outputs `[expected_eval, selector_acc[0..n)]` for any\n    /// well-formed calldata. Rendered only by\n    /// `SolidityGenerator::render_quotient_probe` for differential tests."

--   vhVerifyNotice the quotient_probe = false arm, the production notice line. The
--   right-trim on the else tag is what leaves it carrying the PARENT's four spaces
--   instead of its own eight, and what stops a whitespace-only line from being emitted
--   before it.
def vhVerifyNotice : String := "/// @notice Verify a Halo2/Midfall proof for the generated verifying key."

--   vhNatSpecA the first @dev NatSpec run, between the notice and the failure-policy
--   sentence.
def vhNatSpecA : String := "\n    /// @dev This checks only that `proof` verifies for the supplied public\n    /// `instances` under this pinned VK/protocol. Application contracts must\n    /// bind the meaning of those instances separately: state roots, program\n    /// identifiers, expected IVC outputs, chain/domain separation, and any\n    /// protocol-specific authorization are outside this raw verifier ABI.\n    /// @dev Production renders are success-or-revert: accepted proofs return\n    /// `true`; a production render NEVER returns `false`. Every rejection\n    /// reverts with one of the typed errors declared above\n    /// (BadCalldataShape, VkMismatch, NonCanonicalScalar, BadPointEncoding,\n    /// PrecompileFailed, ProofRejected, QuotientProgramInvalid), so callers\n    /// using `if (!verifier.verifyProof(...))` never take the false branch —\n    /// wrap the call or decode the revert data instead."

--   vhTraceFailure the trace = true arm of the failure-policy sentence. No artifact
--   covers it.
def vhTraceFailure : String := " This is a trace\n    /// render: a failed final pairing / accumulated check returns `false`\n    /// (keeping the trace logs) instead of reverting; early calldata and\n    /// encoding failures still revert."

--   vhGasFailure the trace = false arm. It opens with a space because the left-trim on
--   its tag ate the newline that ended the previous line, so this sentence CONTINUES the
--   line above it - the artifact reads '...revert data instead. Gas renders keep the' on
--   one line.
def vhGasFailure : String := " Gas renders keep the\n    /// same failure policy."

--   vhNatSpecB the second @dev NatSpec run, up to and including the 'function
--   verifyProof(' signature opener.
def vhNatSpecB : String := "\n    /// @dev Calldata must be EXACTLY the ABI selector, proof bytes, and\n    /// generated instance words — `calldatasize` is pinned and any trailing\n    /// bytes revert with BadCalldataShape. In particular, ERC-2771 forwarders\n    /// and other calldata-appending relayers (multicall wrappers, paymaster\n    /// contexts) CANNOT call this contract directly; route such traffic\n    /// through an application wrapper that reassembles exact calldata.\n    /// @dev The generated verifier uses absolute Yul memory addresses instead\n    /// of Solidity's free-memory pointer. Generated scratch starts at\n    /// `TRANSCRIPT_MPTR`, which leaves Solidity's reserved prefix *and* solc's\n    /// stack-spill reservation below it untouched; the assembly block asserts\n    /// that separation on entry rather than assuming it. The main\n    /// assembly block remains terminal: accepted proofs return from assembly\n    /// and all rejected inputs revert. Do not inline this body into Solidity\n    /// code that continues executing after verification without reviewing the\n    /// memory strategy; see `docs/architecture/MEMORY_LAYOUT.md`.\n    /// @param proof Solidity-facing proof bytes, with G1 elements repacked into EIP-2537 padded uncompressed form.\n    /// @param instances Public instance scalars encoded as canonical BLS12-381 scalar-field words.\n    /// @return Always `true` for accepted proofs; invalid proofs revert instead of returning `false`.\n    function verifyProof(\n        bytes calldata proof,\n        uint256[] calldata instances\n    ) external"

--   vhReturnsBool the trace || gas_checkpoints arm of the returns clause.
def vhReturnsBool : String := " returns (bool)"

--   vhViewReturns the production arm of the returns clause.
def vhViewReturns : String := " view returns (bool)"

--   vhGuardOpen the body opener and the cheap ABI-shape guard up to its first
--   interpolation.
def vhGuardOpen : String := " {\n        // Cheap ABI-shape guard before any generated memory work:\n        //   - proof head must point at the bytes payload;\n        //   - instances head must point at the generated instance array.\n        //\n        // The verifier below is a hand-rolled calldata parser. Failing here\n        // keeps malformed dynamic-argument layouts from being interpreted as a\n        // valid Midfall proof stream.\n        assembly (\"memory-safe\") {\n            if iszero(and(eq(calldataload("

--   vhGuardSep1 between abi_selector_bytes and abi_proof_head_offset.
def vhGuardSep1 : String := "), "

--   vhGuardSep2 between abi_proof_head_offset and abi_instances_head_cptr.
def vhGuardSep2 : String := "), eq(calldataload("

--   vhGuardSep3 between abi_instances_head_cptr and the second abi_selector_bytes.
def vhGuardSep3 : String := "), sub(NUM_INSTANCE_CPTR, "

--   vhGuardClose the tail of the guard block, including the inline BadCalldataShape
--   selector write.
def vhGuardClose : String := ")))) {\n                // BadCalldataShape() -- fail() is not in scope in this early\n                // guard block, so write the selector inline.\n                mstore(0x00, shl(224, ERR_BAD_CALLDATA_SHAPE))\n                revert(0x00, 0x04)\n            }\n        }"

--   vhNonEmbeddedVk the 'when None' arm of the embedded_vk match: the AUTHORIZED_VK
--   binding.
def vhNonEmbeddedVk : String := "\n        // Non-embedded renders pin the VK by address and codehash. The Yul\n        // loader rechecks the runtime before every proof and copies the\n        // INVALID-prefixed payload into VK_MPTR.\n        address vk = AUTHORIZED_VK;"

--   vhSplitQuotient the 'when Some' arm of the quotient_external match, the
--   AUTHORIZED_QUOTIENT binding. The deployed profile never takes it.
def vhSplitQuotient : String := "\n        // Split quotient renders delegate the scalar-side identity numerator\n        // reconstruction to a separately deployed generated evaluator.\n        address quotientEvaluator = AUTHORIZED_QUOTIENT;"

--   vhMainAssemblyOpen the main assembly opener, the MF-2 memory-layout guard and the
--   helper-section banner, ending with the four spaces that indent the AssemblyHelpers
--   include line.
def vhMainAssemblyOpen : String := "\n        assembly (\"memory-safe\") {\n            // The `memory-safe` annotation above is what enables solc's\n            // stack-to-memory mover, which reserves spill slots upward from\n            // 0x80. The generated layout below writes absolute addresses from\n            // TRANSCRIPT_MPTR upward and never consults the free-memory\n            // pointer, so the two regions must not meet. The size of that\n            // reservation is compiler-version and optimiser dependent, so\n            // assert the invariant in the deployed bytecode instead of relying\n            // on a generator-side test the integrator never runs. ~6 gas.\n            //\n            // MF-2: this is the only on-chain guard against a recompile that\n            // silently moves the spill region, and the failure it catches is\n            // permanent (no input can verify). 'fail()' is not in scope this\n            // early, so write the MemoryLayoutViolated() selector inline\n            // rather than reverting bare -- an empty revert here is\n            // indistinguishable from every other empty revert, which is\n            // exactly the wrong signal for a build fault.\n            if gt(mload(0x40), TRANSCRIPT_MPTR) {\n                mstore(0x00, shl(224, ERR_MEMORY_LAYOUT_VIOLATED))\n                revert(0x00, 0x04)\n            }\n\n            // This block owns the call-frame memory and remains terminal.\n            // Generated scratch starts at TRANSCRIPT_MPTR (0x80), preserving\n            // Solidity's reserved scratch, free-memory-pointer, and zero-slot\n            // words. See docs/architecture/MEMORY_LAYOUT.md.\n            // ===============================================================\n            // Helpers: modexp, transcript, EIP-2537 calls\n            // ===============================================================\n\n    "

--   vhDirectIndent the indent the quotient_direct for-loop puts before each generated
--   function line.
def vhDirectIndent : String := "\n            "

--   vhAfterTraceAndGas what the template emits between the TraceAndGasHelpers include and
--   the VkLoading include once the direct-quotient match renders nothing: the two hoisted
--   locals and the include glue.
def vhAfterTraceAndGas : String := "\n\n            let r := FR_MODULUS\n            let success := true\n\n    "

--   vhFooter the closing braces of the verifier shell, WITHOUT the final newline the
--   template file carries - gate 4 owns that law.
def vhFooter : String := "\n        }\n    }\n}"

--   vkvPrologue the whole VK template before the constructor body: licence, pragma, the
--   layout NatSpec, the contract opener and the constructor and assembly openers.
def vkvPrologue : String := "// SPDX-License-Identifier: CC0-1.0\n\n// Pinned to match the verifier, so both halves of a deployment are provably\n// built by one toolchain. (This contract's runtime is pure returned data, so\n// its codehash is compiler-independent -- the pin is for the pair, not for it.)\npragma solidity 0.8.30;\n\n/// @title Halo2 BLS12-381 verifying-key payload.\n/// @notice Contract whose deployed runtime is `INVALID || generated verifier-key payload`.\n/// @dev Byte 0 is an unconditional INVALID opcode so direct calls cannot execute payload bytes as code. The linked verifier pins the full runtime by length/codehash and copies the payload starting at byte 1.\n/// @dev The layout follows the verifier inputs derived from\n/// `midfall/proofs/src/plonk/mod.rs::VerifyingKey` and the transcript\n/// `vk.hash_into` behavior used by `midfall/proofs/src/plonk/verifier.rs`.\n///\n/// Layout (in 32-byte words, big-endian). The header slots are generated from\n/// Rust's `VkHeaderLayout`; the byte offsets are absolute from the start of the\n/// VK payload, not from byte 0 of the runtime. Runtime byte 0 is the INVALID\n/// prefix; the verifier loads the payload via\n/// `extcodecopy(vk, VK_MPTR, 0x01, vk_payload_len)` and then references each\n/// slot by `VK_MPTR + i`.\n///\n///   word  0  : vk_digest                    (Fq, transcript_repr of the CS)\n///   word  1  : num_instances\n///   word  2  : k                            (log2 of the domain size)\n///   word  3  : n_inv                        (1/n in Fr)\n///   word  4  : omega                        (n-th primitive root of unity)\n///   word  5  : omega_inv\n///   word  6  : omega_inv_to_l               (omega_inv ^ |rotation_last|)\n///   word  7  : has_accumulator              (0 or 1)\n///   word  8  : acc_offset                   (instance index of the accumulator)\n///   word  9  : num_acc_limbs\n///   word 10  : num_acc_limb_bits\n///   word 11..14 : G1_BASE                   (4 words, EIP-2537 padded)\n///   word 15..22 : G2_BASE                   (8 words, EIP-2537 padded)\n///   word 23..30 : NEG_S_G2_BASE             (8 words, EIP-2537 padded)\n///   word 31..30 + Q_PAYLOAD      : quotient VM constants + packed bytecode\n///   word 31 + Q_PAYLOAD ..       : fixed_comms (4 words each)\n///   word 31 + Q_PAYLOAD + 4*N_FIXED ..\n///                                : permutation_comms (4 words each)\n///\n/// Notes:\n/// - `extcodehash` of this contract is pinned by the linked verifier via\n///   `EXPECTED_VK_CODEHASH`, so any byte tweak is detected at deploy time.\n/// - The quotient identity interpreter's static program is stored in this\n///   pinned VK runtime. The verifier reads it from memory after `extcodecopy`,\n///   avoiding verifier-side PUSH32/mstore immediates while keeping the program\n///   covered by `EXPECTED_VK_CODEHASH`.\n/// - The midnight-proofs migration bakes the per-lookup chunk counts, trashcan\n///   structure, and `num_simple_selectors` into the generated verifier code.\ncontract Halo2VerifyingKey {\n    /// @notice Deploy the verifying-key payload as this contract's runtime bytecode.\n    /// @dev The constructor writes an INVALID byte followed by generated words into memory and returns that prefixed runtime.\n    /// @dev The transient construction buffer starts at `0x80`, preserving Solidity's reserved memory words.\n    constructor() {\n        assembly {"

--   vkvEpilogue the VK shell's closing braces, again with no final newline - gate 13 owns
--   that half.
def vkvEpilogue : String := "\n        }\n    }\n}"


/-! ## The three render functions -/

/-- The run of the root verifier template from the Constructors include up to the
    AssemblyHelpers include: the notice block (the only right-trimming tags in the
    corpus), the two NatSpec runs, the failure-policy arm, the returns clause, the
    ABI-shape guard with its four hex() interpolations, and the two match arms
    that sit between the guard block and the main assembly block. -/
def verifierNoticeSection (ctx : RootCtx) : String :=
  includeGlue ++
  (if ctx.base.quotientProbe then vhProbeNotice else vhVerifyNotice) ++
  vhNatSpecA ++
  (if ctx.base.trace then vhTraceFailure else vhGasFailure) ++
  vhNatSpecB ++
  (if (ctx.base.trace || ctx.base.gasCheckpoints) then vhReturnsBool else vhViewReturns) ++
  vhGuardOpen ++ hexFilter ctx.abiSelectorBytes ++ vhGuardSep1
    ++ hexFilter ctx.abiProofHeadOffset ++ vhGuardSep2
    ++ hexFilter ctx.abiInstancesHeadCptr ++ vhGuardSep3
    ++ hexFilter ctx.abiSelectorBytes ++ vhGuardClose ++
  (match ctx.base.embeddedVk with
   | none => vhNonEmbeddedVk
   | some _ => "") ++
  (match ctx.base.quotientExternal with
   | some _ => vhSplitQuotient
   | none => "") ++
  vhMainAssemblyOpen

/-- The quotient_direct match inside the main assembly block (template :206-212).
    The deployed profile takes the None arm and renders nothing; the Some arm
    emits one indented line per generated function. Note this is a SECOND
    quotient_direct match, in the contract shell, distinct from the one inside
    QuotientAndLinearization.yul that P-13a ported - the template really does
    interpolate qdirect.functions in both places, and only the shell one is
    ported here. -/
def verifierDirectSection (ctx : RootCtx) : String :=
  match ctx.base.quotientDirect with
  | some qdirect => jinjaFor qdirect.functions (fun line _loop => vhDirectIndent ++ line)
  | none => ""

/-- rust: the Askama expansion of T:contracts/Halo2Verifier.sol, i.e.
    M:955-960 (Halo2Verifier::render). Thirteen include holes, four flag-driven
    branches, two matches, one for-loop and four hex() interpolations; the rest
    is the template's own text. The trailing newline the template file carries is
    NOT emitted - see vhFooter and gate 4. -/
def renderHalo2Verifier (ctx : RootCtx) (parts : VerifierParts) : String :=
  vhPrologue ++ parts.constants ++ includeGlue ++
  parts.precompileSmoke ++ includeGlue ++ parts.constructors ++
  verifierNoticeSection ctx ++ parts.assemblyHelpers ++ includeGlue ++
  parts.accumulatorHelpers ++ includeGlue ++ parts.traceAndGasHelpers ++
  verifierDirectSection ctx ++ vhAfterTraceAndGas ++ parts.vkLoading ++ includeGlue ++
  parts.transcriptProofParser ++ includeGlue ++ parts.lagrange ++ includeGlue ++
  parts.quotientAndLinearization ++ includeGlue ++ parts.pcs ++ includeGlue ++
  parts.finalPairing ++ includeGlue ++ parts.traceReturn ++ vhFooter

/-- rust: the Askama expansion of T:contracts/Halo2VerifyingKey.sol, i.e.
    M:820-825 (Halo2VerifyingKey::render). The shell is prologue + the
    constructor body stream Templates.lean already owns + the closing braces.
    Because this template includes nothing, this is a closed term and gate 12 can
    compare it to the whole tracked artifact. -/
def renderHalo2VerifyingKey (vk : Halo2VerifyingKey) : String :=
  vkvPrologue ++ "\n" ++ renderLines vk.constructorLines ++ vkvEpilogue

/-- ARCHITECTURAL EQUATION, hazard 4, and what it does NOT establish. This is a
    DEFINITIONAL equality: it holds by rfl because renderHalo2VerifyingKey is
    defined as its right-hand side. What it buys is a factorisation claim - the
    root template's expansion is exactly (fixed prologue) ++ (the constructor line
    stream that Templates.lean already gates against the pinned DVK:62-72 slice)
    ++ (fixed epilogue), with nothing else in between. It cannot fail, it says
    nothing about the Rust, and it is NOT evidence of byte correctness; gate 12 is
    that, and gate 14 is the cross-channel check that has content. Stated because
    PLAN 9.5 lists render_eq_print as a theorem and the honest form of it in this
    port is a definitional equation plus a decidable cross-channel one, not a
    proof. -/
theorem vkRoot_render_eq_print (vk : Halo2VerifyingKey) :
    renderHalo2VerifyingKey vk
    = vkvPrologue ++ "\n" ++ renderLines vk.constructorLines ++ vkvEpilogue :=
  rfl

/-- The thirteen fields of a parts record, in declaration order. Gate 2 ties this
    list to verifierPartPaths and gate 11 ties it to the render's hole order. -/
def verifierPartFields (p : VerifierParts) : List String :=
  [ p.constants, p.precompileSmoke, p.constructors, p.assemblyHelpers,
    p.accumulatorHelpers, p.traceAndGasHelpers, p.vkLoading,
    p.transcriptProofParser, p.lagrange, p.quotientAndLinearization,
    p.pcs, p.finalPairing, p.traceReturn ]

/-! ## The standalone quotient evaluator shell

The evaluator template interpolates nineteen memory.* slots plus the four
quotient_external fields. The Rust record (M:690-716) reads them from
VerifierMemoryLayout, so the Lean context keeps the Ptr-typed ones as Ptr and the
two usize ones as Nat, and the render routes the Ptr ones through printPtr
exactly as the Rust Display does. -/

/-- The template inputs of T:contracts/Halo2QuotientEvaluator.sol. Field types
    mirror M:690-716: Ptr where the Rust field is a Ptr, Nat where it is a usize. -/
structure EvaluatorCtx where
  vkMptr : Ptr
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
  xNMptr : Ptr
  xNMinus1InvMptr : Ptr
  lLastMptr : Ptr
  lBlindMptr : Ptr
  l0Mptr : Ptr
  instanceEvalMptr : Ptr
  quotientEvalMptr : Ptr
  reversedEvalsMptr : Ptr
  selectorAccMptr : Nat
  quotientReturnMptr : Nat
  quotientExternal : QuotientExternal
  simpleSelectorCols : List Nat
  trace : Bool

/-- M:711 num_simple_selectors, i.e. the length the template's
    simple_selector_cols.len() renders twice. -/
def EvaluatorCtx.numSimpleSelectors (c : EvaluatorCtx) : Nat := c.simpleSelectorCols.length

/-- The evaluator's memory constants, every one of them READ FROM THE VERIFIER
    ARTIFACT rather than invented: the evaluator and the verifier are generated
    from the same VerifierMemoryLayout (M:700 'memory' in both records), and the
    verifier's Constants region renders all nineteen of these slots as named
    declarations. Gate 16 re-reads each one and fails if this record disagrees.
    The frame metadata is the one part the artifact cannot supply, because the
    deployed profile never renders an external quotient frame at all; it comes
    from quotientExternalFrameFromBounds, the ported Rust frame builder
    (QRS:778-794), fed with the VK length and the evals base the artifact does
    carry. LABEL: no artifact pins this record's rendered file. -/
def evaluatorCtxFromDump (sol : String) : Option EvaluatorCtx := do
  let vkM ← qHexHere sol " VK_MPTR = 0x"
  let chal ← qHexHere sol " CHALLENGE_MPTR = 0x"
  let theta ← qHexHere sol " THETA_MPTR = 0x"
  let beta ← qHexHere sol " BETA_MPTR = 0x"
  let gamma ← qHexHere sol " GAMMA_MPTR = 0x"
  let trash ← qHexHere sol " TRASH_CHALLENGE_MPTR = 0x"
  let y ← qHexHere sol " Y_MPTR = 0x"
  let x ← qHexHere sol " X_MPTR = 0x"
  let x1 ← qHexHere sol " X1_MPTR = 0x"
  let x2 ← qHexHere sol " X2_MPTR = 0x"
  let x3 ← qHexHere sol " X3_MPTR = 0x"
  let x4 ← qHexHere sol " X4_MPTR = 0x"
  let xn ← qHexHere sol " X_N_MPTR = 0x"
  let xninv ← qHexHere sol " X_N_MINUS_1_INV_MPTR = 0x"
  let llast ← qHexHere sol " L_LAST_MPTR = 0x"
  let lblind ← qHexHere sol " L_BLIND_MPTR = 0x"
  let l0 ← qHexHere sol " L_0_MPTR = 0x"
  let ieval ← qHexHere sol " INSTANCE_EVAL_MPTR = 0x"
  let qeval ← qHexHere sol " QUOTIENT_EVAL_MPTR = 0x"
  let rev ← qHexHere sol " REVERSED_EVALS_MPTR = 0x"
  let sels ← qHexHere sol " SELECTOR_ACC_MPTR = 0x"
  let qret ← qHexHere sol " QUOTIENT_RETURN_MPTR = 0x"
  let vkLen ← qNatAfter sol "EXPECTED_VK_PAYLOAD_LENGTH = "
  let selCount := poseidonCtx.simpleSelectorCols.length
  pure { vkMptr := ptrMemory (valueFromNat vkM)
         challengeMptr := ptrMemory (valueFromNat chal)
         thetaMptr := ptrMemory (valueFromNat theta)
         betaMptr := ptrMemory (valueFromNat beta)
         gammaMptr := ptrMemory (valueFromNat gamma)
         trashChallengeMptr := ptrMemory (valueFromNat trash)
         yMptr := ptrMemory (valueFromNat y)
         xMptr := ptrMemory (valueFromNat x)
         x1Mptr := ptrMemory (valueFromNat x1)
         x2Mptr := ptrMemory (valueFromNat x2)
         x3Mptr := ptrMemory (valueFromNat x3)
         x4Mptr := ptrMemory (valueFromNat x4)
         xNMptr := ptrMemory (valueFromNat xn)
         xNMinus1InvMptr := ptrMemory (valueFromNat xninv)
         lLastMptr := ptrMemory (valueFromNat llast)
         lBlindMptr := ptrMemory (valueFromNat lblind)
         l0Mptr := ptrMemory (valueFromNat l0)
         instanceEvalMptr := ptrMemory (valueFromNat ieval)
         quotientEvalMptr := ptrMemory (valueFromNat qeval)
         reversedEvalsMptr := ptrMemory (valueFromNat rev)
         selectorAccMptr := sels
         quotientReturnMptr := qret
         quotientExternal := quotientExternalFrameFromBounds 0x4000 vkLen rev
           poseidonCtx.proofLayout.evals.itemCount selCount
         simpleSelectorCols := poseidonCtx.simpleSelectorCols
         trace := false }

/-- rust: the Askama expansion of T:contracts/Halo2QuotientEvaluator.sol, i.e.
    M:1008-1013 (Halo2QuotientEvaluator::render). The two includes are
    parameters, as in renderQuotientAndLinearization; the template's own text
    between them is EMPTY, because both include tags left-trim and the whitespace
    between them is nothing but the two line indents. -/
def renderHalo2QuotientEvaluator (ctx : EvaluatorCtx)
    (quotientHelpers : String) (quotientNumeratorBlock : String) : String :=
    "// SPDX-License-Identifier: CC0-1.0\n// Pinned to match the verifier, so both halves of a deployment are provably\n// built by one toolchain. (This contract's runtime is pure returned data, so\n// its codehash is compiler-independent -- the pin is for the pair, not for it.)\npragma solidity 0.8.30;\n\n/// @title Split Halo2 quotient numerator evaluator.\n/// @notice Reconstructs the scalar side of the linearization query for a generated verifier.\n/// @dev This is the split-out implementation of the expensive\n/// `partially_evaluate_identities` / `compute_linearization_commitment` side\n/// from the Midfall Rust verifier:\n/// - `midfall/proofs/src/plonk/mod.rs::partially_evaluate_identities`\n/// - `midfall/proofs/src/plonk/linearization/verifier.rs::compute_linearization_commitment`\n/// - `midfall/proofs/src/plonk/{permutation,logup,trash}.rs`\n/// @dev The main verifier has already parsed calldata, checked proof scalar\n/// ranges, sampled Fiat-Shamir challenges, loaded the VK payload, and computed\n/// local Lagrange/public-input values before making the staticcall.\n///\n/// Instead of receiving structured Solidity arguments, the evaluator receives\n/// the verifier's memory frame as raw calldata:\n///\n///   calldata[0..QUOTIENT_FRAME_LEN)\n///      == memory[QUOTIENT_FRAME_BASE..QUOTIENT_FRAME_BASE+QUOTIENT_FRAME_LEN)\n///\n/// The fallback copies that frame back into the same generated memory\n/// addresses. All constants below are therefore memory addresses inside that\n/// copied frame, not ABI offsets.\n///\n/// Output is a compact fixed frame consumed by Halo2Verifier:\n///\n///   word 0: QUOTIENT_MAGIC, a generated version/magic guard\n///   word 1: linearization_expected_eval\n///   word 2..: simple-selector accumulator scalars\n///\n/// This contract reconstructs the Rust verifier's y-batched identity numerator\n/// nu_y(x) and returns the linearization expected scalar -nu_y(x). It does not\n/// evaluate or trust a quotient scalar h(x).\n///\n/// The quotient limb commitments are handled by Halo2Verifier on the commitment\n/// side as (1 - x^n) * sum_i x_split^i * Q_i. That is why this scalar side is\n/// -nu_y(x), not h(x) = nu_y(x) / (x^n - 1).\n///\n/// See docs/QUOTIENT_NUMERATOR_EVALUATOR.md for the full Rust/Solidity mapping.\ncontract Halo2QuotientEvaluator {\n    // BLS12-381 scalar field modulus. All arithmetic in this contract is over\n    // Fr and uses addmod/mulmod with this modulus.\n    uint256 internal constant FR_MODULUS =\n        0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;\n\n    // Start of the copied verifier-key payload in memory. The VK payload also\n    // carries the compact quotient VM constant/program tables used by the\n    // included numerator block.\n    uint256 internal constant                VK_MPTR = " ++ printPtr ctx.vkMptr.value ++ ";\n\n    // Fiat-Shamir challenge slots. Halo2Verifier sampled these in transcript\n    // order before the external call. The evaluator only reads them.\n    uint256 internal constant        CHALLENGE_MPTR = " ++ printPtr ctx.challengeMptr.value ++ ";\n    uint256 internal constant            THETA_MPTR = " ++ printPtr ctx.thetaMptr.value ++ ";\n    uint256 internal constant             BETA_MPTR = " ++ printPtr ctx.betaMptr.value ++ ";\n    uint256 internal constant            GAMMA_MPTR = " ++ printPtr ctx.gammaMptr.value ++ ";\n    uint256 internal constant TRASH_CHALLENGE_MPTR = " ++ printPtr ctx.trashChallengeMptr.value ++ ";\n    uint256 internal constant                Y_MPTR = " ++ printPtr ctx.yMptr.value ++ ";\n    uint256 internal constant                X_MPTR = " ++ printPtr ctx.xMptr.value ++ ";\n    uint256 internal constant               X1_MPTR = " ++ printPtr ctx.x1Mptr.value ++ ";\n    uint256 internal constant               X2_MPTR = " ++ printPtr ctx.x2Mptr.value ++ ";\n    uint256 internal constant               X3_MPTR = " ++ printPtr ctx.x3Mptr.value ++ ";\n    uint256 internal constant               X4_MPTR = " ++ printPtr ctx.x4Mptr.value ++ ";\n\n    // Common polynomial values at x. Halo2Verifier computes these once after\n    // sampling x and places them in the frame so the numerator block can share\n    // the exact Rust verifier inputs.\n    uint256 internal constant              X_N_MPTR = " ++ printPtr ctx.xNMptr.value ++ ";\n    uint256 internal constant  X_N_MINUS_1_INV_MPTR = " ++ printPtr ctx.xNMinus1InvMptr.value ++ ";\n    uint256 internal constant           L_LAST_MPTR = " ++ printPtr ctx.lLastMptr.value ++ ";\n    uint256 internal constant          L_BLIND_MPTR = " ++ printPtr ctx.lBlindMptr.value ++ ";\n    uint256 internal constant              L_0_MPTR = " ++ printPtr ctx.l0Mptr.value ++ ";\n    uint256 internal constant     INSTANCE_EVAL_MPTR = " ++ printPtr ctx.instanceEvalMptr.value ++ ";\n    uint256 internal constant     QUOTIENT_EVAL_MPTR = " ++ printPtr ctx.quotientEvalMptr.value ++ ";\n\n    // Proof evaluation table. Values are already decoded as canonical Fr words\n    // by Halo2Verifier. The generated numerator code indexes this table by the\n    // same query order as the Rust verifier.\n    uint256 internal constant     REVERSED_EVALS_MPTR = " ++ printPtr ctx.reversedEvalsMptr.value ++ ";\n\n    // Scratch/output region for simple-selector linearization accumulators.\n    // The numerator block writes one bucket per simple selector, then the\n    // fallback copies those buckets into the compact return frame.\n    uint256 internal constant      SELECTOR_ACC_MPTR = " ++ hexFilter ctx.selectorAccMptr ++ ";\n    // Callee-local scratch for trace hooks. Trace-enabled verifier builds call\n    // this evaluator with CALL so quotient identity logs can be compared with\n    // the native Rust trace. Production verifier builds keep using STATICCALL\n    // and render this evaluator without trace hooks.\n    uint256 internal constant        TRACE_U256_MPTR = " ++ hexFilter ctx.quotientReturnMptr ++ ";\n    uint256 internal constant    QUOTIENT_OUTPUT_MPTR = " ++ hexFilter ctx.quotientReturnMptr ++ ";\n\n    // External-call frame metadata. The main verifier calls this contract with\n    // exactly QUOTIENT_FRAME_LEN bytes starting at\n    // QUOTIENT_FRAME_BASE, then checks the return length and QUOTIENT_MAGIC.\n    uint256 internal constant QUOTIENT_FRAME_BASE = " ++ hexFilter ctx.quotientExternal.frameBase ++ ";\n    uint256 internal constant QUOTIENT_FRAME_LEN = " ++ hexFilter ctx.quotientExternal.frameLen ++ ";\n    uint256 internal constant QUOTIENT_OUTPUT_LEN = " ++ hexFilter ctx.quotientExternal.outputLen ++ ";\n    uint256 internal constant QUOTIENT_MAGIC = " ++ hexPaddedFilter 64 ctx.quotientExternal.magic ++ ";\n\n    /// @notice Evaluate the generated quotient numerator block for one verifier memory frame.\n    /// @dev Calldata is exactly the raw frame, not ABI-encoded arguments. Returns `QUOTIENT_MAGIC`, the linearization expected eval, and selector buckets.\n    /// @dev This fallback also uses generated absolute memory addresses and\n    /// returns directly from assembly. Its compact return frame starts at\n    /// `0x80`, preserving Solidity's reserved memory words.\n    fallback() external {\n        assembly (\"memory-safe\") {\n            // Reject malformed calls. This contract is not a general-purpose\n            // ABI endpoint; accepting partial or shifted frames would make the\n            // generated memory addresses point at the wrong data.\n            if iszero(eq(calldatasize(), QUOTIENT_FRAME_LEN)) { revert(0, 0) }\n\n            // Rehydrate the verifier memory image. From this point onward the\n            // generated Yul can use the same MPTR constants as the monolithic\n            // verifier path.\n            calldatacopy(QUOTIENT_FRAME_BASE, 0, QUOTIENT_FRAME_LEN)\n\n            let r := FR_MODULUS" ++ (if ctx.trace then "\n            // Trace-only side channel used by fixture comparison. Production\n            // split evaluators are called via STATICCALL and render without\n            // this LOG helper.\n            function trace_u256(id, value) {\n                mstore(TRACE_U256_MPTR, value)\n                log1(TRACE_U256_MPTR, 0x20, id)\n            }" else "" ) ++ "\n\n            // This included block is the main body of the evaluator. It:\n            //   1. evaluates gate/permutation/lookup/trash identities in the\n            //      same order as Rust `partially_evaluate_identities`;\n            //   2. y-batches fully evaluated identities into\n            //      quotient_eval_numer;\n            //   3. y-batches simple-selector identities into\n            //      SELECTOR_ACC_MPTR buckets;\n            //   4. writes -quotient_eval_numer to QUOTIENT_EVAL_MPTR.\n            //\n            // Depending on codegen settings, some identities are native Yul\n            // callbacks and the rest are executed by the compact q_program VM\n            // stored in the copied VK payload.\n            //\n            // The upstream Rust comments call out that simple multiplicative\n            // selectors do not appear as normal proof eval scalars. The Yul\n            // block mirrors that rule by accumulating those identities into\n            // SELECTOR_ACC_MPTR buckets for later multiplication by fixed\n            // selector commitments, while fully evaluated identities contribute\n            // to the negated expected scalar." ++ quotientHelpers ++ quotientNumeratorBlock ++ "\n\n            // Return the compact output frame. Halo2Verifier checks the magic,\n            // stores word 1 as the linearization expected eval, then expands\n            // selector buckets into the fused final PCS MSM.\n            mstore(QUOTIENT_OUTPUT_MPTR, QUOTIENT_MAGIC)\n            mstore(add(QUOTIENT_OUTPUT_MPTR, 0x20), mload(QUOTIENT_EVAL_MPTR))" ++ (if 0 < ctx.simpleSelectorCols.length then "\n            // Copy selector buckets from the generated absolute memory region\n            // into the compact external-call return frame.\n            for { let q_i := 0 } lt(q_i, " ++ toString ctx.numSimpleSelectors ++ ") { q_i := add(q_i, 1) } {\n                mstore(add(QUOTIENT_OUTPUT_MPTR, add(0x40, shl(5, q_i))), mload(add(SELECTOR_ACC_MPTR, shl(5, q_i))))\n            }" else "" ) ++ "\n            return(QUOTIENT_OUTPUT_MPTR, QUOTIENT_OUTPUT_LEN)\n        }\n    }\n}"


end Midfall.Generator

/-! ## Known-answer tests for the contract shells

Twenty-eight gates. Gate 1 is the reachability gate D-P19 demands first. Gates
2-11 are the verifier shell: 2 ties the include record to the provenance-checked
registry, 3-9 are the TEXTUAL gates on the shell's own text and glue, 10 is the
accounting gate that every byte of the artifact belongs to the shell, to one of
the seven ported partial renders, or to one of the unported regions, and 11
ties the render's field order to the registry. Gates 12-15 are the VK shell,
including the only WHOLE-FILE byte gate in the tree. Gates 16-19 are the
evaluator and every one of them says LABEL: no artifact exists. Gate 20 is the
hazard-6 hole demonstrated rather than hidden. Gates 21-27 are the R-41
perturbations, each run inside the scope of the gate it attacks. Gate 28 names
the arms no gate can see, and lists the four perturbations that provably do not
bite. -/

namespace Midfall.Generator.ContractKats

open Midfall Midfall.Generator Midfall.Generator.VerifierPartialKats
open Midfall.Generator.TemplateKats YulSemantics

def contractTemplateDirCandidates : List String :=
  ["../proofs/solidity-verifier/templates/contracts/",
   "proofs/solidity-verifier/templates/contracts/"]

def readContractTemplate (name : String) : IO String :=
  EvmKats.readFirst (contractTemplateDirCandidates.map fun d => d ++ name)

/-- The evaluator's rendered artifact. There is none: this reads the empty string
    and gate 16 asserts that it does, so the absence is a checked fact about the
    tracked tree rather than a sentence in a comment. -/
def readEvaluatorDump : IO String :=
  EvmKats.readFirst
    ["../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2QuotientEvaluator.sol",
     "proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2QuotientEvaluator.sol"]

/-- The first occurrence of needle in hay as a character index, or none unless it
    occurs EXACTLY once. -/
def uniqueIndex (hay needle : String) : Option Nat :=
  match hay.splitOn needle with
  | [before, _after] => some before.length
  | _ => none

/-- Walk pieces through hay in the given order. Each must occur exactly once in
    hay and at or after the end of the previous one; an empty piece is a
    failure, because it would let a hole be claimed without evidence. Returns the
    gaps: one more than the number of pieces, the first before the first piece
    and the last after the last. none if any piece is missing, duplicated or out
    of order. -/
partial def gapsGo (whole hay : String) (pieces : List String)
    (acc : List String) : Option (List String) :=
  match pieces with
  | [] => some (acc.reverse ++ [hay])
  | p :: ps =>
      if p.isEmpty || occ whole p != 1 then none
      else match hay.splitOn p with
           | [before, after] => gapsGo whole after ps (before :: acc)
           | _ => none

def gapsOf (hay : String) (pieces : List String) : Option (List String) :=
  gapsGo hay hay pieces []

/-- String.take / String.drop that give a String back: in Lean 4.35 both return a
    String.Slice, which is not what these gates want. -/
def takeS (n : Nat) (s : String) : String := (s.take n).toString
def dropS (n : Nat) (s : String) : String := (s.drop n).toString

/-- A parts value whose fields are thirteen distinct markers, so the render's
    HOLE ORDER can be tested without needing the six unported partials. -/
def partMarker (i : Nat) : String := "\u00abP" ++ toString i ++ "\u00bb"

def markerParts : VerifierParts :=
  { constants := partMarker 1, precompileSmoke := partMarker 2,
    constructors := partMarker 3, assemblyHelpers := partMarker 4,
    accumulatorHelpers := partMarker 5, traceAndGasHelpers := partMarker 6,
    vkLoading := partMarker 7, transcriptProofParser := partMarker 8,
    lagrange := partMarker 9, quotientAndLinearization := partMarker 10,
    pcs := partMarker 11, finalPairing := partMarker 12, traceReturn := partMarker 13 }

/-- The eleven byte runs the deployed artifact can be walked with: the nine
    shell-owned runs and the seven ported partial renders, with the two adjacent
    shell runs around the unported TraceAndGasHelpers hole kept separate so that
    hole is visible as a gap. The quotient hole is inside the notice run's
    successor and the Pcs / TraceReturn holes are gaps 9 and 10. -/
def deployedShellPieces (sol : String) : Option (List String) := do
  let qctx ← quotientDeployedCtx sol
  let b := poseidonRootCtx.base
  pure [vhPrologue, verifierNoticeSection poseidonRootCtx, renderAssemblyHelpers b,
        renderAccumulatorHelpers b, vhAfterTraceAndGas, renderVkLoading b,
        renderTranscriptProofParser b, renderLagrange b,
        renderQuotientAndLinearization qctx (renderQuotientHelpers qctx)
          (renderQuotientNumeratorBlock qctx),
        renderFinalPairing b, vhFooter]

/-- GATE 1 (reachability, first: D-P19). The two tracked artifacts and all three
    contract templates must open, so a wrong path is a named red and not a needle
    that matches nothing. -/
def contracts13d_artifactsReachable_ok : IO Bool :=
  readDump >>= fun sol =>
  readVkDump >>= fun dvk =>
  readContractTemplate "Halo2Verifier.sol" >>= fun t =>
  readContractTemplate "Halo2VerifyingKey.sol" >>= fun tv =>
  readContractTemplate "Halo2QuotientEvaluator.sol" >>= fun te =>
  pure (EvmKats.generatedReadOk sol && dvk.length > 20000 && t.length > 5000
    && tv.length > 2000 && te.length > 3000)

/-- GATE 2. The include record is the registry: same thirteen paths, same order.
    verifierIncludes is what scripts/check_golden_provenance.py re-reads from the
    template file, so this gate is what ties VerifierParts' field order to the
    template rather than to a comment. What reddens it: renaming a path,
    reordering the list, or changing its length. -/
def verifierPartOrder_matchesRegistry_ok : Bool :=
  verifierPartPaths == verifierIncludes && verifierPartPaths.length == 13
    && verifierPartPaths.all (fun p => p.startsWith "partials/verifier/")
    && verifierPartFields markerParts == (List.range' 1 13).map partMarker

/-- GATE 3 (TEXTUAL). The shell prologue is the template's own text up to the
    first include AND the artifact's own text up to line 85. Both sides are read
    at #eval time: the template source for the first clause, the artifact for the
    second. Length asserted (hazard 6): a truncated prologue still occurs once. -/
def verifierPrologue_matchesTemplateAndArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  readContractTemplate "Halo2Verifier.sol" >>= fun t =>
  pure (t.startsWith vhPrologue && (t.drop vhPrologue.length).startsWith "{% include"
    && occ sol vhPrologue == 1 && sol.startsWith vhPrologue
    && vhPrologue.length == 5153 && lineCount vhPrologue == 85)

/-- GATE 4 (TEXTUAL, the root final newline - hazard 2 of the brief, owned here).
    The template file ends with '}' + LF; the artifact ends with '}' and NO LF;
    the render reproduces the artifact. The first clause is what makes this a
    claim about a difference rather than about a constant: if Askama stopped
    dropping the final newline, the template would still end the same way and the
    artifact would gain an LF, and this gate is the pair that notices. -/
def verifierFooter_rootNewlineLaw_ok : IO Bool :=
  readDump >>= fun sol =>
  readContractTemplate "Halo2Verifier.sol" >>= fun t =>
  pure (t.endsWith "\n        }\n    }\n}\n"
    && vhFooter == "\n        }\n    }\n}" && vhFooter.length == 18
    && occ sol vhFooter == 1 && sol.endsWith vhFooter
    && ! sol.endsWith "\n" && sol.length == 175908)

/-- GATE 5 (TEXTUAL, hazard 1: the right-trim, first real exercise). The two
    -%} sites in the corpus are T:contracts/Halo2Verifier.sol:91 and :96, both in
    the quotient_probe if/else - NOT the five sites the brief names; :111, :115
    and :117 are left-trims and are gate 6's business. The observable: the else
    arm's notice line carries the PARENT's four spaces (the indent of the if
    line, which the untrimmed tag would have emitted) and not its own eight, and
    no whitespace-only line is left behind. The negative control is the point:
    the UNTRIMMED form must occur zero times, so a port that ignored -%} would
    redden this gate rather than silently pass it. -/
def verifierRightTrim_noticeArm_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol (includeGlue ++ vhVerifyNotice) == 1
    && (includeGlue ++ vhVerifyNotice).length == 79
    && vhVerifyNotice.length == 73
    && vhVerifyNotice.startsWith "/// @notice Verify a Halo2/Midfall proof"
    && occ sol (includeGlue ++ "\n    " ++ vhVerifyNotice) == 0
    && occ sol (includeGlue ++ "\n    /// @notice Verify a Halo2/Midfall proof") == 0
    && occ sol vhProbeNotice == 0 && vhProbeNotice.length == 268)

/-- GATE 6 (TEXTUAL, the left-trims the brief called right-trims). The
    failure-policy arm and the returns clause both open with a SPACE because the
    {%- on their tag ate the newline that ended the previous line, so each
    continues the line above it instead of starting one. That is what makes the
    artifact read '...revert data instead. Gas renders keep the' on one line. -/
def verifierLeftTrim_failurePolicyAndReturns_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol (vhNatSpecA ++ vhGasFailure) == 1
    && (vhNatSpecA ++ vhGasFailure).length == 934
    && vhGasFailure == " Gas renders keep the\n    /// same failure policy."
    && occ sol vhTraceFailure == 0 && vhTraceFailure.length == 205
    && occ sol (vhNatSpecB ++ vhViewReturns ++ " {") == 1
    && (vhNatSpecB ++ vhViewReturns ++ " {").length == 1578
    && occ sol (vhNatSpecB ++ vhReturnsBool ++ " {") == 0)

/-- GATE 7 (TEXTUAL, anti-self-fulfilment on the three ABI numbers). The artifact's
    own guard line is parsed for its four 0x literals and each is required to be
    the field of poseidonRootCtx that the render puts in that position; then the
    whole rendered guard run is required to occur exactly once, with its length.
    A wrong abi_* number, or a hex filter that pads differently, reddens it. -/
def verifierAbiGuard_derivedFromArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match qHexesInLinesWith sol "if iszero(and(eq(calldataload(" with
    | [sel, head, inst, sel2] =>
        sel == poseidonRootCtx.abiSelectorBytes
          && head == poseidonRootCtx.abiProofHeadOffset
          && inst == poseidonRootCtx.abiInstancesHeadCptr && sel2 == sel
          && occ sol (vhGuardOpen ++ hexFilter sel ++ vhGuardSep1 ++ hexFilter head
                        ++ vhGuardSep2 ++ hexFilter inst ++ vhGuardSep3
                        ++ hexFilter sel2 ++ vhGuardClose) == 1
          && (vhGuardOpen ++ hexFilter sel ++ vhGuardSep1 ++ hexFilter head
                ++ vhGuardSep2 ++ hexFilter inst ++ vhGuardSep3
                ++ hexFilter sel2 ++ vhGuardClose).length == 819
    | _ => false)

/-- GATE 8 (TEXTUAL). The two matches between the guard block and the main
    assembly block: embedded_vk takes its None arm and quotient_external takes
    its empty arm, so the guard block runs straight into the AUTHORIZED_VK
    binding and then into the assembly opener with nothing in between. The Some
    arm of the second match is asserted ABSENT, not merely unrendered. -/
def verifierMatchArms_deployedSelection_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol (vhGuardClose ++ vhNonEmbeddedVk ++ vhMainAssemblyOpen) == 1
    && (vhGuardClose ++ vhNonEmbeddedVk ++ vhMainAssemblyOpen).length == 2353
    && occ sol vhSplitQuotient == 0 && vhSplitQuotient.length == 207
    && occ sol "AUTHORIZED_QUOTIENT" == 0
    && occ sol "address vk = AUTHORIZED_VK;" == 1)

/-- GATE 9 (TEXTUAL, and the strongest thing said about an UNPORTED partial).
    TraceAndGasHelpers.yul has no render function, but the artifact pins what its
    deployed render must be: the run between the AccumulatorHelpers render and
    the two hoisted locals is exactly the include glue, so the hole is empty.
    Both of the partial's ifs are false in the release profile and every byte of
    its body is inside one of them, so the empty render is not an assumption
    about the port - it is a fact about the artifact, and the four negative
    clauses below are what say so. -/
def verifierTraceAndGasRendersEmpty_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol (renderAccumulatorHelpers poseidonCtx ++ includeGlue
                  ++ vhAfterTraceAndGas) == 1
    && vhAfterTraceAndGas.length == 71 && lineCount vhAfterTraceAndGas == 6
    && occ sol "gas_checkpoint" == 0
    && occ sol "function trace_u256" == 0
    && occ sol "function trace_point" == 0)

/-- GATE 10 (THE ACCOUNTING - the closest this package can come to a whole-file
    gate, and the honest substitute for one). Every shell-owned byte run and every
    ported partial render is walked through the artifact in template order. Each
    must occur EXACTLY ONCE; the first must start at byte 0 and the last must end
    at the last byte; the glue gaps between ported neighbours must be exactly the
    include glue; and the three remaining gaps must be the unported regions. The
    final clause is the length accounting hazard 6 asks for: the pieces and the
    gaps tile the artifact exactly, so no byte is unaccounted and no piece can
    have silently grown or shrunk. What it does NOT do: it does not say what the
    three gaps contain. Constants.sol, PrecompileSmoke.sol, Constructors.sol,
    Pcs.yul and TraceReturn.yul are still unported and their bytes are read from
    the artifact, not produced by this port. -/
def verifierShell_accountsForArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match deployedShellPieces sol with
    | none => false
    | some pieces => match gapsOf sol pieces with
    | some gaps =>
        [gaps.getD 0 "", gaps.getD 2 "", gaps.getD 5 ""].all (· == "")
          && gaps.getD 11 "" == ""
          && [3, 4, 6, 7, 8].all (fun i => gaps.getD i "" == includeGlue)
          && (gaps.getD 1 "").length == 29032
          && (gaps.getD 9 "").startsWith includeGlue
          && (gaps.getD 9 "").endsWith includeGlue
          && (gaps.getD 9 "").length == 23323
          && (gaps.getD 10 "").startsWith includeGlue
          && (gaps.getD 10 "").length == 569
          && gaps.length == 12
          && gaps.map String.length == [0, 29032, 0, 6, 6, 0, 6, 6, 6, 23323, 569, 0]
          && sol.length == (gaps.map (·.length)).sum + (pieces.map (·.length)).sum
    | none => false)

/-- The marker render must be the shell text plus thirteen markers and nothing
    else: its length is the shell's own byte count plus the markers. -/
def verifierPartFieldsLengthCheck (r : String) : Bool :=
  r.length == (List.range' 1 13).foldl (fun acc i => acc + (partMarker i).length) 0
    + vhPrologue.length + (verifierNoticeSection poseidonRootCtx).length
    + vhAfterTraceAndGas.length + vhFooter.length + 10 * includeGlue.length

/-- GATE 11. The render's HOLE ORDER, tested without the six unported partials:
    substitute thirteen distinct markers, require each to occur exactly once and
    in registry order. Swapping any two parts.x in renderHalo2Verifier reddens
    this and nothing else in the tree. -/
def verifierRender_markerOrder_ok : Bool :=
  let r := renderHalo2Verifier poseidonRootCtx markerParts
  let ps := (List.range' 1 13).filterMap fun i => uniqueIndex r (partMarker i)
  ps.length == 13 && ps.Pairwise (· < ·)
    && verifierPartFieldsLengthCheck r

/-- G1Words carries no BEq (finding F5 of the standing notes is the same class),
    so commitment lists are compared through their Nat coordinates. -/
def g1Tuples (gs : List G1Words) : List (Nat × Nat × Nat × Nat) :=
  gs.map fun g => (g.xHi.toNat, g.xLo.toNat, g.yHi.toNat, g.yLo.toNat)

/-- One 'mstore(add(payload, 0xNNNN), 0xHH..) // label' line of the rendered VK
    contract, as (word index, value, label). The word index is the byte offset
    divided by 32, i.e. the index the template's loop.index0 would have written. -/
def vkPayloadLine? (l : String) : Option (Nat × Nat × String) :=
  match l.splitOn "mstore(add(payload, 0x" with
  | [_, r] =>
      match r.splitOn ") // " with
      | [head, label] =>
          match head.splitOn "), 0x" with
          | [offHex, valHex] =>
              match qHexValue? offHex, qHexValue? valHex with
              | some off, some val => some (off / 32, val, label)
              | _, _ => none
          | _ => none
      | _ => none
  | _ => none

/-- The commitment index a payload label names, for a given section prefix. -/
def vkCommIndex? (pref : String) (l : String) : Option Nat :=
  if ! l.startsWith (pref ++ "[") then none
  else
    let ds := (l.drop (pref.length + 1)).toString.toList.takeWhile (fun c => c ≥ '0' && c ≤ '9')
    if ds.isEmpty then none
    else some (ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)

/-- The single value labelled 'prefix[j].which', or none unless it is labelled
    exactly once. -/
def vkCommWord? (ws : List (Nat × Nat × String)) (label : String) : Option Nat :=
  match ws.filterMap fun w => if w.2.2 == label then some w.2.1 else none with
  | [x] => some x
  | _ => none

def vkG1At (ws : List (Nat × Nat × String)) (pref : String) (j : Nat) : Option G1Words :=
  let base := pref ++ "[" ++ toString j ++ "]."
  match vkCommWord? ws (base ++ "x_hi"), vkCommWord? ws (base ++ "x_lo"),
        vkCommWord? ws (base ++ "y_hi"), vkCommWord? ws (base ++ "y_lo") with
  | some a, some b, some c, some d =>
      some { xHi := BitVec.ofNat 256 a, xLo := BitVec.ofNat 256 b,
             yHi := BitVec.ofNat 256 c, yLo := BitVec.ofNat 256 d }
  | _, _, _, _ => none

/-- The commitments of one section, in the order the artifact first names them. -/
def vkCommList (ws : List (Nat × Nat × String)) (pref : String) : List G1Words :=
  (ws.filterMap fun w => vkCommIndex? pref w.2.2).eraseDups
    |>.filterMap (vkG1At ws pref)

/-- THE MODEL READ OUT OF THE ARTIFACT. constructor_payload_mptr from the 'let
    runtime' line, the constant table from the labels that name a slot, and the
    two commitment sections from the labels that name a G1 word. This is what
    makes gate 12 a whole-file render check rather than a transcription: the
    renderer is run on the generator's own inputs, recovered from the generator's
    own output, and the result must be the output again, byte for byte. -/
def vkModelFromArtifact (dvk : String) : Option Halo2VerifyingKey := do
  let ws := (dvk.splitOn "\n").filterMap vkPayloadLine?
  let mptr ← match dvk.splitOn "let runtime := 0x" with
             | [_, r] => qHexValue? (qTakeHex r)
             | _ => none
  pure { constructorPayloadMptr := mptr
         constants := ws.filterMap fun w =>
           if w.2.2.startsWith "fixed_comms[" || w.2.2.startsWith "permutation_comms["
           then none else some (w.2.2, BitVec.ofNat 256 w.2.1)
         fixedComms := vkCommList ws "fixed_comms"
         permutationComms := vkCommList ws "permutation_comms"
         quotientConstOffsetWords := none
         quotientConstWords := 0
         quotientProgramOffsetWords := none
         quotientProgramWords := 0
         quotientConstLabels := []
         quotientConstHeaders := [] }

/-- GATE 12 (TEXTUAL, WHOLE FILE). The rendered VK contract IS the tracked
    artifact: every byte, every line, no trailing newline, and the length
    asserted alongside the equality (hazard 6 - an equality already implies it,
    and it is stated anyway because every byte gate in this package states it).
    The model is read out of the artifact by vkModelFromArtifact, so what this
    gate proves is that the renderer reproduces the generator's file from that
    model: the prologue, the three loops, the offsets, the padding widths, the
    comment wording, the section order, the return length and the dropped final
    newline. What it does NOT prove: that the model's VALUES are right - they
    came from the artifact - which is why gate 14 ties them to the
    hand-transcribed model in Templates.lean and to the provenance-pinned slice. -/
def vkContract_bytesExact_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | some vk =>
        let r := renderHalo2VerifyingKey vk
        r == dvk && r.length == dvk.length && r.length == 26018
          && lineCount r == 271 && ! r.endsWith "\n"
    | none => false)

/-- GATE 13 (TEXTUAL, the VK shell's own text and its final newline). -/
def vkContract_prologueEpilogue_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  readContractTemplate "Halo2VerifyingKey.sol" >>= fun t =>
  pure (t.startsWith vkvPrologue && vkvPrologue.length == 3337
    && lineCount vkvPrologue == 55 && dvk.startsWith vkvPrologue
    && t.endsWith "\n        }\n    }\n}\n" && dvk.endsWith vkvEpilogue
    && vkvEpilogue == "\n        }\n    }\n}" && vkvEpilogue.length == 18
    && ! dvk.endsWith "\n" && occ dvk vkvEpilogue == 1)

/-- GATE 14 (anti-self-fulfilment on the model). The derived model is the model
    Templates.lean hand-transcribed for the pinned slices, the payload word
    offsets in the artifact are exactly 0..142 with no gap or repeat (which is
    what makes the derivation's word-index read honest), and the runtime length
    the artifact returns is the one the model computes. -/
def vkContract_modelDerivedFromArtifact_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | some vk =>
        vk.constants == poseidonVkFullConstants
          && g1Tuples (vk.fixedComms.take 5) == g1Tuples poseidonVkFullComms
          && vk.constants.length == 35 && vk.fixedComms.length == 19
          && vk.permutationComms.length == 8
          && vk.constructorPayloadMptr == 0x80 && vk.runtimeLen == 4577
          && ((dvk.splitOn "\n").filterMap vkPayloadLine?).map (·.1) == List.range 143
    | none => false)

/-- GATE 15 (STRUCTURAL, D-P13 - the cross-channel equation hazard 4 asks for).
    The text channel the root template emits and the vendored AST channel
    Templates.lean builds for the same model tokenise identically. This is the
    one equation in this file that has content: two independently written
    renderers, one model, one token stream. What it does NOT establish: agreement
    with the Rust (gate 12 is the artifact's verdict on that), the hex SPELLING
    (the token relation reduces literals to values - loss class 2 of
    Render.lean), or any semantic property of the contract. -/
def vkRoot_textChannel_eq_astChannel_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | some vk => yulTokens ("{" ++ renderLines vk.constructorLines ++ "}")
                    == yulTokens (EVM.print vk.constructorStmts)
    | none => false)

/-- GATE 16 (HAZARD 3, stated plainly and checked). The standalone quotient
    evaluator is NOT exercised by the deployed profile. There is no
    Halo2QuotientEvaluator.sol in the tracked dump directory, and the verifier
    artifact contains none of the five strings that only that contract emits.
    Every evaluator gate below is therefore synthetic, and none of them is offered
    as byte evidence. -/
def evaluator_notExercisedByDeployedProfile_ok : IO Bool :=
  readDump >>= fun sol =>
  readEvaluatorDump >>= fun ev =>
  pure (ev == "" && occ sol "contract Halo2QuotientEvaluator" == 0
    && occ sol "AUTHORIZED_QUOTIENT" == 0 && occ sol "QUOTIENT_FRAME_BASE" == 0
    && occ sol "QUOTIENT_MAGIC" == 0 && occ sol "fallback() external" == 0)

/-- The evaluator's own declaration name for each memory slot, paired with the
    needle that finds the same slot's declaration in the verifier artifact. -/
def evaluatorDeclNeedles : List (String × String) :=
  [ ("VK_MPTR", " VK_MPTR = 0x"), ("CHALLENGE_MPTR", " CHALLENGE_MPTR = 0x"),
    ("THETA_MPTR", " THETA_MPTR = 0x"), ("BETA_MPTR", " BETA_MPTR = 0x"),
    ("GAMMA_MPTR", " GAMMA_MPTR = 0x"),
    ("TRASH_CHALLENGE_MPTR", " TRASH_CHALLENGE_MPTR = 0x"),
    ("Y_MPTR", " Y_MPTR = 0x"), ("X_MPTR", " X_MPTR = 0x"),
    ("X1_MPTR", " X1_MPTR = 0x"), ("X2_MPTR", " X2_MPTR = 0x"),
    ("X3_MPTR", " X3_MPTR = 0x"), ("X4_MPTR", " X4_MPTR = 0x"),
    ("X_N_MPTR", " X_N_MPTR = 0x"),
    ("X_N_MINUS_1_INV_MPTR", " X_N_MINUS_1_INV_MPTR = 0x"),
    ("L_LAST_MPTR", " L_LAST_MPTR = 0x"), ("L_BLIND_MPTR", " L_BLIND_MPTR = 0x"),
    ("L_0_MPTR", " L_0_MPTR = 0x"),
    ("INSTANCE_EVAL_MPTR", " INSTANCE_EVAL_MPTR = 0x"),
    ("QUOTIENT_EVAL_MPTR", " QUOTIENT_EVAL_MPTR = 0x"),
    ("REVERSED_EVALS_MPTR", " REVERSED_EVALS_MPTR = 0x"),
    ("SELECTOR_ACC_MPTR", " SELECTOR_ACC_MPTR = 0x"),
    ("TRACE_U256_MPTR", " QUOTIENT_RETURN_MPTR = 0x"),
    ("QUOTIENT_OUTPUT_MPTR", " QUOTIENT_RETURN_MPTR = 0x") ]

/-- GATE 17 (LABEL: synthetic file, derived inputs). The evaluator's twenty-three
    interpolated memory constants are not invented: each one is the value the
    VERIFIER artifact declares for the same slot, because both contracts are
    generated from one VerifierMemoryLayout. The check reads the artifact's
    declaration and requires the evaluator render to carry the same number under
    the evaluator's own name. Plus the two frame facts that come from ported Rust
    rather than from the artifact: the magic is quotientExternalMagic and the
    output length is (2 + num_simple_selectors) words, which is M:1000's
    validate_layout rule. -/
def evaluatorCtx_derivedFromVerifierDump_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match evaluatorCtxFromDump sol with
    | some c =>
        let ev := renderHalo2QuotientEvaluator c "\x01" "\x02"
        evaluatorDeclNeedles.all (fun (decl, needle) =>
          match qHexHere sol needle with
          | some v => ev.contains (" " ++ decl ++ " = " ++ hexFilter v)
          | none => false)
          && evaluatorDeclNeedles.length == 23
          && c.vkMptr.value.asUsizeNat == poseidonCtx.vkMptr
          && c.simpleSelectorCols == poseidonCtx.simpleSelectorCols
          && c.numSimpleSelectors == 4
          && c.quotientExternal.magic == quotientExternalMagic
          && c.quotientExternal.outputLen == (2 + c.numSimpleSelectors) * 32
          && c.quotientReturnMptr == quotientReturnBufferStart
    | none => false)

/-- GATE 18 (LABEL: the include splice, tied to committed bytes). The evaluator's
    two include holes are the same two partials P-13c ported, and the bytes they
    produce for the deployed quotient profile occur EXACTLY ONCE in the verifier
    artifact and once inside the evaluator render, concatenated with no separator
    in both. So the evaluator's glue is checked against real bytes even though
    its file is not. What this cannot say: that the evaluator's own surrounding
    text is what the Rust would emit - no artifact covers it. -/
def evaluator_includesMatchArtifact_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol, evaluatorCtxFromDump sol with
    | some qctx, some ectx =>
        let qh := renderQuotientHelpers qctx
        let qnb := renderQuotientNumeratorBlock qctx
        let ev := renderHalo2QuotientEvaluator ectx qh qnb
        occ ev (qh ++ qnb) == 1 && occ sol (qh ++ qnb) == 1
          && (qh ++ qnb).length == 57218 && ev.length > (qh ++ qnb).length
    | _, _ => false)

/-- GATE 19 (LABEL: SYNTHETIC, structural). The evaluator shell renders: the
    constants block, the fallback frame guard, the two spliced includes, the
    selector-bucket loop bounded by the simple-selector count, and the compact
    return - 156 lines, 8,807 bytes with two 5-byte markers standing in for the two
    included blocks, 28 constant declarations, ending '}' with no LF. The
    trace arm is asserted ABSENT for the deployed profile. No artifact is
    involved; this pins the port's shape, not the generator's bytes. -/
def evaluator_structure_synthetic_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match evaluatorCtxFromDump sol with
    | some c =>
        let ev := renderHalo2QuotientEvaluator c "\x01QH\x01" "\x01QNB\x01"
        ev.startsWith "// SPDX-License-Identifier: CC0-1.0"
          && ev.endsWith "}" && ! ev.endsWith "\n"
          && occ ev "uint256 internal constant" == 28
          && lineCount ev == 156 && ev.length == 8806
          && occ ev "\x01QH\x01" == 1 && occ ev "\x01QNB\x01" == 1
          && ev.contains "if iszero(eq(calldatasize(), QUOTIENT_FRAME_LEN)) { revert(0, 0) }"
          && ev.contains "calldatacopy(QUOTIENT_FRAME_BASE, 0, QUOTIENT_FRAME_LEN)"
          && ev.contains "for { let q_i := 0 } lt(q_i, 4) { q_i := add(q_i, 1) }"
          && ev.contains "return(QUOTIENT_OUTPUT_MPTR, QUOTIENT_OUTPUT_LEN)"
          && ! ev.contains "function trace_u256"
    | none => false)

/-- GATE 20 (hazard 6, the hole demonstrated rather than hidden). A strict prefix
    of a needle occurs exactly once wherever the needle does, so occursOnce alone
    cannot detect a truncated render. Shown here on three of this file's own
    needles, and closed by asserting lengths in gates 3-13 and whole-string
    equality in gate 12. -/
def hazard6_truncationWouldPassOcc_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol vhPrologue == 1 && occ sol (dropS 1 vhPrologue) == 1
    && (dropS 1 vhPrologue).length < vhPrologue.length
    && occ sol vhAfterTraceAndGas == 1 && occ sol (dropS 1 vhAfterTraceAndGas) == 1
    && occ sol vhVerifyNotice == 1 && occ sol (dropS 1 vhVerifyNotice) == 1
    && occ sol vhNonEmbeddedVk == 1 && occ sol (dropS 1 vhNonEmbeddedVk) == 1)

/-- GATE 21 (R-41). The five flag-driven arms of the notice section, flipped one
    at a time: the rendered run changes and stops occurring in the artifact. -/
def perturb_rootFlagArms_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := verifierNoticeSection poseidonRootCtx
  let qext : QuotientExternal :=
    { frameBase := 0x4000, frameLen := 0x2000, outputLen := 0xc0,
      magic := quotientExternalMagic }
  let flips : List (PartialCtx -> PartialCtx) :=
    [ fun c => { c with quotientProbe := true },
      fun c => { c with trace := true },
      fun c => { c with gasCheckpoints := true },
      fun c => { c with embeddedVk := some poseidonVkHead },
      fun c => { c with quotientExternal := some qext } ]
  pure (occ sol dep == 1 && flips.all (fun f =>
    let c := { poseidonRootCtx with base := f poseidonRootCtx.base }
    let r := verifierNoticeSection c
    r != dep && occ sol r == 0))

/-- GATE 22 (R-41). The quotient_direct match in the shell: one generated
    function line appears, indented as the template writes it, and is absent from
    the artifact; an empty function list renders the empty string, which is
    Askama's zero-iteration law and the reason the deployed render is unchanged. -/
def perturb_directArm_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := verifierDirectSection poseidonRootCtx
  let one : RootCtx := { poseidonRootCtx with base := { poseidonCtx with
    quotientDirect := some { constants := [], functions := ["let q_direct := 1"], block := [] } } }
  let two : RootCtx := { poseidonRootCtx with base := { poseidonCtx with
    quotientDirect := some { constants := [], functions := ["a", "b"], block := [] } } }
  let empty : RootCtx := { poseidonRootCtx with base := { poseidonCtx with
    quotientDirect := some { constants := [], functions := [], block := [] } } }
  pure (dep == "" && verifierDirectSection empty == ""
    && verifierDirectSection one == "\n            let q_direct := 1"
    && occ sol (verifierDirectSection one) == 0
    && verifierDirectSection two == "\n            a\n            b"
    && (verifierDirectSection two).length == 28)

/-- GATE 23 (R-41). Each of the three ABI numbers perturbed by one: the rendered
    guard run changes and stops occurring in the artifact. -/
def perturb_abiNumbers_ok : IO Bool :=
  readDump >>= fun sol =>
  let dep := verifierNoticeSection poseidonRootCtx
  let edits : List (RootCtx -> RootCtx) :=
    [ fun c => { c with abiSelectorBytes := c.abiSelectorBytes + 1 },
      fun c => { c with abiProofHeadOffset := c.abiProofHeadOffset + 0x20 },
      fun c => { c with abiInstancesHeadCptr := c.abiInstancesHeadCptr + 0x20 } ]
  pure (occ sol dep == 1 && edits.all (fun f =>
    let c := f poseidonRootCtx
    verifierNoticeSection c != dep && occ sol (verifierNoticeSection c) == 0))

/-- GATE 24 (R-41). Swapping any two include holes reddens the order gate: all
    twelve adjacent transpositions are run. -/
def perturb_partOrderSwap_ok : Bool :=
  let swap (i j : Nat) (p : VerifierParts) : VerifierParts :=
    let f := verifierPartFields p
    let a := f.getD i ""; let b := f.getD j ""
    { p with
      constants := if i == 0 then b else if j == 0 then a else p.constants,
      precompileSmoke := if i == 1 then b else if j == 1 then a else p.precompileSmoke,
      constructors := if i == 2 then b else if j == 2 then a else p.constructors,
      assemblyHelpers := if i == 3 then b else if j == 3 then a else p.assemblyHelpers,
      accumulatorHelpers := if i == 4 then b else if j == 4 then a else p.accumulatorHelpers,
      traceAndGasHelpers := if i == 5 then b else if j == 5 then a else p.traceAndGasHelpers,
      vkLoading := if i == 6 then b else if j == 6 then a else p.vkLoading,
      transcriptProofParser := if i == 7 then b else if j == 7 then a else p.transcriptProofParser,
      lagrange := if i == 8 then b else if j == 8 then a else p.lagrange,
      quotientAndLinearization := if i == 9 then b else if j == 9 then a else p.quotientAndLinearization,
      pcs := if i == 10 then b else if j == 10 then a else p.pcs,
      finalPairing := if i == 11 then b else if j == 11 then a else p.finalPairing,
      traceReturn := if i == 12 then b else if j == 12 then a else p.traceReturn }
  (List.range' 0 12).all fun i =>
    let r := renderHalo2Verifier poseidonRootCtx (swap i (i + 1) markerParts)
    let ps := (List.range' 1 13).filterMap fun k => uniqueIndex r (partMarker k)
    ps.length != 13 || ! ps.Pairwise (· < ·)

/-- GATE 25 (R-41). The VK model perturbed six ways, each in its own scope: the
    whole-file render stops matching the artifact. -/
def perturb_vkModel_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | some vk =>
        let edits : List (Halo2VerifyingKey -> Halo2VerifyingKey) :=
          [ fun v => { v with constructorPayloadMptr := v.constructorPayloadMptr + 0x20 },
            fun v => { v with constants := v.constants.drop 1 },
            fun v => { v with constants := (v.constants.head?.getD ("", 0)) :: v.constants.drop 2 },
            fun v => { v with fixedComms := v.fixedComms.reverse },
            fun v => { v with permutationComms := v.permutationComms.drop 1 },
            fun v => { v with fixedComms := v.fixedComms.map (fun g => { g with xLo := g.yHi }) } ]
        edits.all (fun f => renderHalo2VerifyingKey (f vk) != dvk)
          && renderHalo2VerifyingKey vk == dvk
    | none => false)

/-- GATE 26 (R-41). The evaluator's two flags discriminate: trace adds the
    nine-line LOG helper inside the fallback, and an empty selector list removes
    the bucket-copy loop. LABEL: no artifact can check the CONTENT of either arm. -/
def perturb_evaluatorFlags_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match evaluatorCtxFromDump sol with
    | some c =>
        let dep := renderHalo2QuotientEvaluator c "\x01" "\x02"
        let traced := renderHalo2QuotientEvaluator { c with trace := true } "\x01" "\x02"
        let noSels := renderHalo2QuotientEvaluator
          { c with simpleSelectorCols := [] } "\x01" "\x02"
        traced != dep && traced.contains "function trace_u256(id, value)"
          && traced.length > dep.length + 200
          && noSels != dep && ! noSels.contains "for { let q_i := 0 }"
          && noSels.length < dep.length
    | none => false)

/-- GATE 27 (R-41, the shell text is load-bearing). For ten shell runs, deleting
    ONE interior character destroys the artifact match. Without this the shell
    text could be any text at all and gates 3-10 would still pass. -/
def perturb_shellText_ok : IO Bool :=
  readDump >>= fun sol =>
  let pieces := [vhPrologue, vhNatSpecA, vhNatSpecB, vhGuardOpen, vhGuardClose,
                 vhNonEmbeddedVk, vhMainAssemblyOpen, vhAfterTraceAndGas,
                 vhGasFailure, vhVerifyNotice]
  pure (pieces.all (fun p => occ sol p == 1
    && occ sol (takeS (p.length / 2) p ++ dropS (p.length / 2 + 1) p) == 0)
    && pieces.length == 10)

/-- GATE 28 (R-41, the honest non-bites). The arms no deployed gate can see,
    asserted as absence rather than hidden as a passing test. vhProbeNotice,
    vhTraceFailure, vhReturnsBool and vhSplitQuotient are ported text that no
    tracked artifact contains, so a typo in any of them reddens NOTHING in this
    tree; the same is true of the Some arm of the embedded_vk match, which is
    empty in the template and so cannot even be typo'd. And the six unported
    partials' bytes are read from the artifact by gate 10 rather than produced,
    so nothing here checks them at all.

    MEASURED, not asserted (R-41). Four source mutations reddened NOTHING and the
    causes are these: a same-length typo inside vhSplitQuotient ('delegate' ->
    'delegatf') - gate 8 pins that arm's LENGTH (207) and its absence from the
    artifact, never its content; a same-length typo inside vhProbeNotice
    ('VERIFIER' -> 'VERIFIEBS' with the length held) - same shape, gate 5 pins
    length 268 and absence; a same-length typo inside vhTraceFailure - gate 6
    pins length 205 and absence; and a length-preserving typo inside
    vhReturnsBool - nothing at all pins that arm, not even its length, because
    gate 6 only asserts that the composite containing it fails to occur. What DID
    bite, with the gates each reddened, is recorded in the package report: 15
    source mutations were run, 11 reddened between two and seven gates apiece. -/
def inertFields13d_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (occ sol vhProbeNotice == 0 && occ sol vhTraceFailure == 0
    && occ sol vhSplitQuotient == 0
    && occ sol (vhNatSpecB ++ vhReturnsBool ++ " {") == 0
    && vhNonEmbeddedVk.length == 235
    && occ sol "when Some" == 0)

end Midfall.Generator.ContractKats

#eval Midfall.Generator.ContractKats.contracts13d_artifactsReachable_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierPartOrder_matchesRegistry_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierPrologue_matchesTemplateAndArtifact_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierFooter_rootNewlineLaw_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierRightTrim_noticeArm_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierLeftTrim_failurePolicyAndReturns_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierAbiGuard_derivedFromArtifact_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierMatchArms_deployedSelection_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierTraceAndGasRendersEmpty_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierShell_accountsForArtifact_ok -- expect true
#eval Midfall.Generator.ContractKats.verifierRender_markerOrder_ok -- expect true
#eval Midfall.Generator.ContractKats.vkContract_bytesExact_ok -- expect true
#eval Midfall.Generator.ContractKats.vkContract_prologueEpilogue_ok -- expect true
#eval Midfall.Generator.ContractKats.vkContract_modelDerivedFromArtifact_ok -- expect true
#eval Midfall.Generator.ContractKats.vkRoot_textChannel_eq_astChannel_ok -- expect true
#eval Midfall.Generator.ContractKats.evaluator_notExercisedByDeployedProfile_ok -- expect true
#eval Midfall.Generator.ContractKats.evaluatorCtx_derivedFromVerifierDump_ok -- expect true
#eval Midfall.Generator.ContractKats.evaluator_includesMatchArtifact_ok -- expect true
#eval Midfall.Generator.ContractKats.evaluator_structure_synthetic_ok -- expect true
#eval Midfall.Generator.ContractKats.hazard6_truncationWouldPassOcc_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_rootFlagArms_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_directArm_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_abiNumbers_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_partOrderSwap_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_vkModel_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_evaluatorFlags_ok -- expect true
#eval Midfall.Generator.ContractKats.perturb_shellText_ok -- expect true
#eval Midfall.Generator.ContractKats.inertFields13d_ok -- expect true


