// SPDX-License-Identifier: CC0-1.0
// Pinned, not floating. Two properties of this artifact are compiler- and
// optimiser-dependent, and neither is visible in the source:
//   1. The generated layout writes absolute addresses from TRANSCRIPT_MPTR
//      upward. That is only safe while solc's stack-spill reservation stays
//      below it -- measured 0x8c0 on 0.8.24 and 0x8e0 on 0.8.26+, so it is not
//      a constant this file controls. verifyProof now asserts the separation.
//   2. Runtime size depends on --optimize-runs. Measured: 0.8.24 at runs=1
//      emits 29,567 bytes and 0.8.30 at runs=100000 emits 29,836 -- both over
//      the EIP-170 24,576-byte limit, so neither can be deployed. Only the
//      pinned (version, runs) pair is known to produce a deployable contract.
// A floating `^0.8.24` advertises compatibility this contract does not have.
pragma solidity 0.8.30;

/// @title Halo2 BLS12-381 KZG verifier.
/// @notice Circuit-specialized verifier for Midfall/midnight-proofs Halo2
/// proofs rendered by this repository's Rust generator.
/// @dev This contract ports the verifier flow from
/// `midfall/proofs/src/plonk/verifier.rs`, the Keccak transcript comments from
/// `midfall/proofs/src/transcript/implementors.rs`, and the KZG multi-open
/// comments from `midfall/proofs/src/poly/kzg/mod.rs`.
/// @dev It is not a generic verifier. The proof layout, VK payload, quotient
/// identity program, memory layout, and optional quotient evaluator are all
/// generated for one `VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>`.
///
/// Halo2 KZG verifier for the BLS12-381 curve, midnight-proofs flavour.
///
/// Differences vs the original BN254 / halo2 v0.4 template:
//
/// - BLS12-381 base field Fp is 381 bits and does not fit in a uint256.
///   Each Fp coord is encoded EIP-2537 padded (16 zero bytes + 48 bytes).
///   A G1 point is 128 bytes (4 words); a G2 point is 256 bytes (8).
/// - Calldata carries G1 commitments in uncompressed EIP-2537 padded
///   form (4 words = 128 bytes per point: x_hi, x_lo, y_hi, y_lo). The
///   proof bytes produced by midnight-proofs prover are repacked off
///   chain (compressed -> uncompressed) before being passed to
///   `verifyProof`. The verifier hashes the uncompressed 128-byte form into
///   the transcript verbatim, matching `Hashable<Keccak256> for G1Projective::to_input`;
///   see `common_uncompressed_g1`.
/// - Transcript `common` absorbs raw inputs in order. `squeeze` computes one
///   Keccak digest, resets the transcript buffer to that digest, then samples
///   by interpreting the digest as a big-endian integer modulo r.
/// - Scalar inversion uses modexp(scalar, r-2, r).
/// - Constructors run deployment-time smoke tests for MCOPY and the EIP-2537
///   precompiles using identity inputs. Compile with Solidity >=0.8.24 and
///   deploy only on chains/forks that support MCOPY and EIP-2537.
contract Halo2Verifier {
    // ----------------------------------------------------------------------
    // Typed failure taxonomy (P4/L-3, docs/audit/HALO2_VERIFIER_REVIEW).
    // verifyProof is success-or-revert; these errors let integrators and
    // incident responders distinguish malformed calldata from a swapped VK,
    // a non-canonical scalar, a failed precompile, or a rejected proof.
    // Constructor smoke probes intentionally keep bare reverts -- they report
    // a chain-capability failure, and the deployment transaction identifies
    // itself. The one constructor exception is the memory-layout guard
    // (MF-2), which reports a BUILD fault and is typed on both paths.
    // ----------------------------------------------------------------------
    /// @notice Calldata does not match the generated ABI shape (heads,
    ///         lengths, instance count, or exact calldatasize).
    error BadCalldataShape();
    /// @notice The pinned verifying-key (or VK header cross-check) does not
    ///         match the generated constants.
    error VkMismatch();
    /// @notice A public instance or proof scalar is >= the BLS12-381 scalar
    ///         modulus.
    error NonCanonicalScalar();
    /// @notice A proof point violates the EIP-2537 padded encoding or its
    ///         coordinates are >= the base-field modulus.
    error BadPointEncoding();
    /// @notice A precompile call failed or returned an unexpected size.
    error PrecompileFailed();
    /// @notice The final pairing (or its staging) rejected the proof.
    error ProofRejected();
    /// @notice The pinned quotient program or evaluator violated a structural
    ///         invariant (bad opcode, operand out of window, stack misuse,
    ///         or evaluator frame mismatch).
    error QuotientProgramInvalid();
    /// @notice solc's stack-spill reservation overlaps the generated absolute
    ///         memory layout. This is a BUILD fault, not a proof fault: the
    ///         artifact was compiled with a (version, optimiser) pair whose
    ///         free-memory pointer starts at or above TRANSCRIPT_MPTR, so no
    ///         input can ever verify. Redeploy from the pinned toolchain.
    error MemoryLayoutViolated();

    {% include "partials/verifier/Constants.sol" %}

    {% include "partials/verifier/PrecompileSmoke.sol" %}

    {% include "partials/verifier/Constructors.sol" %}

    /// @notice Verify a Halo2/Midfall proof for the generated verifying key.
    /// @dev This checks only that `proof` verifies for the supplied public
    /// `instances` under this pinned VK/protocol. Application contracts must
    /// bind the meaning of those instances separately: state roots, program
    /// identifiers, expected IVC outputs, chain/domain separation, and any
    /// protocol-specific authorization are outside this raw verifier ABI.
    /// Wrapper obligations (replaceable verifier address, wrapper-held pause,
    /// chainid/address/anti-replay binding) and the incident-response
    /// playbook are REQUIREMENTS documented in
    /// `docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md`.
    /// @dev Production renders are success-or-revert: accepted proofs return
    /// `true`; this function NEVER returns `false`. Every rejection reverts
    /// with one of the typed errors declared above (BadCalldataShape,
    /// VkMismatch, NonCanonicalScalar, BadPointEncoding, PrecompileFailed,
    /// ProofRejected, QuotientProgramInvalid), so callers using
    /// `if (!verifier.verifyProof(...))` never take the false branch — wrap
    /// the call or decode the revert data instead. Trace and gas renders keep
    /// the same failure policy.
    /// @dev Calldata must be EXACTLY the ABI selector, proof bytes, and
    /// generated instance words — `calldatasize` is pinned and any trailing
    /// bytes revert with BadCalldataShape. In particular, ERC-2771 forwarders
    /// and other calldata-appending relayers (multicall wrappers, paymaster
    /// contexts) CANNOT call this contract directly; route such traffic
    /// through an application wrapper that reassembles exact calldata.
    /// @dev The generated verifier uses absolute Yul memory addresses instead
    /// of Solidity's free-memory pointer. Generated scratch starts at
    /// `TRANSCRIPT_MPTR`, which leaves Solidity's reserved prefix *and* solc's
    /// stack-spill reservation below it untouched; the assembly block asserts
    /// that separation on entry rather than assuming it. The main
    /// assembly block remains terminal: accepted proofs return from assembly
    /// and all rejected inputs revert. Do not inline this body into Solidity
    /// code that continues executing after verification without reviewing the
    /// memory strategy; see `docs/architecture/MEMORY_LAYOUT.md`.
    /// @param proof Solidity-facing proof bytes, with G1 elements repacked into EIP-2537 padded uncompressed form.
    /// @param instances Public instance scalars encoded as canonical BLS12-381 scalar-field words.
    /// @return Always `true` for accepted proofs; invalid proofs revert instead of returning `false`.
    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) external {%- if self.trace || self.gas_checkpoints %} returns (bool) {%- else %} view returns (bool) {%- endif %} {
        // Cheap ABI-shape guard before any generated memory work:
        //   - proof head must point at the bytes payload;
        //   - instances head must point at the generated instance array.
        //
        // The verifier below is a hand-rolled calldata parser. Failing here
        // keeps malformed dynamic-argument layouts from being interpreted as a
        // valid Midfall proof stream.
        assembly ("memory-safe") {
            if iszero(and(eq(calldataload({{ abi_selector_bytes|hex() }}), {{ abi_proof_head_offset|hex() }}), eq(calldataload({{ abi_instances_head_cptr|hex() }}), sub(NUM_INSTANCE_CPTR, {{ abi_selector_bytes|hex() }})))) {
                // BadCalldataShape() -- fail() is not in scope in this early
                // guard block, so write the selector inline.
                mstore(0x00, shl(224, ERR_BAD_CALLDATA_SHAPE))
                revert(0x00, 0x04)
            }
        }

        {%- match self.embedded_vk %}
        {%- when None %}
        // Non-embedded renders pin the VK by address and codehash. The Yul
        // loader rechecks the runtime before every proof and copies the
        // INVALID-prefixed payload into VK_MPTR.
        address vk = AUTHORIZED_VK;
        {%- else %}
        {%- endmatch %}
        {%- match quotient_external %}
        {%- when Some with (_) %}
        // Split quotient renders delegate the scalar-side identity numerator
        // reconstruction to a separately deployed generated evaluator.
        address quotientEvaluator = AUTHORIZED_QUOTIENT;
        {%- when None %}
        {%- endmatch %}
        assembly ("memory-safe") {
            // The `memory-safe` annotation above is what enables solc's
            // stack-to-memory mover, which reserves spill slots upward from
            // 0x80. The generated layout below writes absolute addresses from
            // TRANSCRIPT_MPTR upward and never consults the free-memory
            // pointer, so the two regions must not meet. The size of that
            // reservation is compiler-version and optimiser dependent, so
            // assert the invariant in the deployed bytecode instead of relying
            // on a generator-side test the integrator never runs. ~6 gas.
            //
            // MF-2: this is the only on-chain guard against a recompile that
            // silently moves the spill region, and the failure it catches is
            // permanent (no input can verify). `fail()` is not in scope this
            // early, so write the MemoryLayoutViolated() selector inline
            // rather than reverting bare -- an empty revert here is
            // indistinguishable from every other empty revert, which is
            // exactly the wrong signal for a build fault.
            if gt(mload(0x40), TRANSCRIPT_MPTR) {
                mstore(0x00, shl(224, ERR_MEMORY_LAYOUT_VIOLATED))
                revert(0x00, 0x04)
            }

            // This block owns the call-frame memory and remains terminal.
            // Generated scratch starts at TRANSCRIPT_MPTR, preserving
            // Solidity's reserved scratch, free-memory-pointer, and zero-slot
            // words. See docs/architecture/MEMORY_LAYOUT.md.
            // ===============================================================
            // Helpers: modexp, transcript, EIP-2537 calls
            // ===============================================================

    {% include "partials/verifier/AssemblyHelpers.yul" %}

    {% include "partials/verifier/AccumulatorHelpers.yul" %}

    {% include "partials/verifier/TraceAndGasHelpers.yul" %}

            let r := FR_MODULUS
            let success := true

    {% include "partials/verifier/VkLoading.yul" %}

    {% include "partials/verifier/TranscriptProofParser.yul" %}

    {% include "partials/verifier/Lagrange.yul" %}

    {% include "partials/verifier/QuotientAndLinearization.yul" %}

    {% include "partials/verifier/Pcs.yul" %}

    {% include "partials/verifier/FinalPairing.yul" %}

    {% include "partials/verifier/TraceReturn.yul" %}
        }
    }
}
