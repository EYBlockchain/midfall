// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.24;

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
/// - Constructors run a deployment-time smoke test for the EIP-2537
///   precompiles using identity inputs. Compile with Solidity >=0.8.24 and
///   deploy only on chains/forks that support MCOPY and EIP-2537.
contract Halo2Verifier {
    {% include "partials/verifier/Constants.sol" %}

    {% include "partials/verifier/PrecompileSmoke.sol" %}

    {% include "partials/verifier/Constructors.sol" %}

    /// @notice Verify a Halo2/Midfall proof for the generated verifying key.
    /// @dev This checks only that `proof` verifies for the supplied public
    /// `instances` under this pinned VK/protocol. Application contracts must
    /// bind the meaning of those instances separately: state roots, program
    /// identifiers, expected IVC outputs, chain/domain separation, and any
    /// protocol-specific authorization are outside this raw verifier ABI.
    /// @dev Production renders are success-or-revert: accepted proofs return
    /// `true`, while malformed calldata, invalid proof material, failed
    /// precompiles, or mismatched pinned dependency code revert. Trace and gas
    /// renders keep the same failure policy.
    /// @dev The generated verifier uses absolute Yul memory addresses instead
    /// of Solidity's free-memory pointer, but generated scratch starts at
    /// `0x80` so Solidity's reserved memory prefix is preserved. The main
    /// assembly block remains terminal: accepted proofs return from assembly
    /// and all rejected inputs revert. Do not inline this body into Solidity
    /// code that continues executing after verification without reviewing the
    /// memory strategy; see `docs/MEMORY_LAYOUT.md`.
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
                revert(0, 0)
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
            // This block owns the call-frame memory and remains terminal.
            // Generated scratch starts at TRANSCRIPT_MPTR (0x80), preserving
            // Solidity's reserved scratch, free-memory-pointer, and zero-slot
            // words. See docs/MEMORY_LAYOUT.md.
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
