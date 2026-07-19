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
/// - Constructors run deployment-time smoke tests for MCOPY and the EIP-2537
///   precompiles using identity inputs. Compile with Solidity >=0.8.24 and
///   deploy only on chains/forks that support MCOPY and EIP-2537.
contract Halo2Verifier {
    
    /// @notice Verifying-key contract address authorized for this verifier.
    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.
    address public immutable AUTHORIZED_VK;
    // Expected VK runtime metadata. The deployed VK runtime is
    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than
    // EXPECTED_VK_PAYLOAD_LENGTH.
    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = 8032;
    uint256 internal constant EXPECTED_VK_LENGTH = 8033;
    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = 0x327e3a0642d1a157521eb891596256086b59006348710f0cd960b89ed35e5854;
    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);

    // Solidity ABI calldata cursors. The generated verifier accepts exactly
    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`
    // bytes itself in the same order as the Rust verifier transcript.
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x14e4;
    uint256 internal constant     INSTANCE_CPTR = 0x1504;
    // First general-purpose memory words reserved by the generated verifier.
    // RETURN_MPTR is a single word set to 1 on success.
    uint256 internal constant    TRANSCRIPT_MPTR = 0x80;
    uint256 internal constant        RETURN_MPTR = 0x80;

    // ----------------------------------------------------------------------
    // Verifying-key memory map. The VK header lives at VK_MPTR, followed
    // by the quotient VM payload and commitments. After the full VK
    // runtime comes the challenge slots (challenge_mptr..) and the
    // per-stage scratch (theta_mptr..).
    // ----------------------------------------------------------------------
    uint256 internal constant                VK_MPTR = 0x1d20;
    uint256 internal constant         VK_DIGEST_MPTR = 0x1d20;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x1d40;
    uint256 internal constant                 K_MPTR = 0x1d60;
    uint256 internal constant             N_INV_MPTR = 0x1d80;
    uint256 internal constant             OMEGA_MPTR = 0x1da0;
    uint256 internal constant         OMEGA_INV_MPTR = 0x1dc0;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x1de0;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x1e00;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x1e20;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x1e40;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x1e60;
    uint256 internal constant            G1_BASE_MPTR = 0x1e80;
    uint256 internal constant            G2_BASE_MPTR = 0x1f00;
    uint256 internal constant      NEG_S_G2_BASE_MPTR = 0x2000;

    uint256 internal constant CHALLENGE_MPTR = 0x3c80;

    // Challenge layout. Squeeze order in midnight-proofs:
    //   user_phase challenges (variable count)
    //   theta -> beta, gamma -> trash_challenge -> y -> x ->
    //   x1, x2 -> x3 -> x4
    uint256 internal constant            THETA_MPTR = 0x3c80;
    uint256 internal constant             BETA_MPTR = 0x3ca0;
    uint256 internal constant            GAMMA_MPTR = 0x3cc0;
    uint256 internal constant TRASH_CHALLENGE_MPTR = 0x3ce0;
    uint256 internal constant                Y_MPTR = 0x3d00;
    uint256 internal constant                X_MPTR = 0x3d20;
    uint256 internal constant               X1_MPTR = 0x3d40;
    uint256 internal constant               X2_MPTR = 0x3d60;
    uint256 internal constant               X3_MPTR = 0x3d80;
    uint256 internal constant               X4_MPTR = 0x3da0;

    // Batch-open commitments live in 4-word EIP-2537 padded slots.
    uint256 internal constant             F_COM_MPTR = 0x3dc0;
    uint256 internal constant                PI_MPTR = 0x3e40;

    // Accumulator (KZG IVC).
    uint256 internal constant          ACC_LHS_MPTR = 0x3ec0;
    uint256 internal constant          ACC_RHS_MPTR = 0x3f40;

    // Lagrange / linearization scratch.
    uint256 internal constant              X_N_MPTR = 0x3fc0;
    uint256 internal constant  X_N_MINUS_1_INV_MPTR = 0x3fe0;
    uint256 internal constant           L_LAST_MPTR = 0x4000;
    uint256 internal constant          L_BLIND_MPTR = 0x4020;
    uint256 internal constant              L_0_MPTR = 0x4040;
    uint256 internal constant     INSTANCE_EVAL_MPTR = 0x4060;
    // Legacy name: this is not h(x). It stores the expected opening
    // scalar for the linearized commitment, i.e. the negated y-batched
    // identity numerator reconstructed from the alleged evals at x.
    uint256 internal constant     QUOTIENT_EVAL_MPTR = 0x4080;
    uint256 internal constant         QUOTIENT_MPTR = 0x40a0;   // 4 words
    uint256 internal constant            F_EVAL_MPTR = 0x4140;
    uint256 internal constant                 V_MPTR = 0x4160;
    uint256 internal constant         FINAL_COM_MPTR = 0x4180;   // 4 words
    uint256 internal constant      PAIRING_LHS_MPTR = 0x4200;   // 4 words
    uint256 internal constant      PAIRING_RHS_MPTR = 0x4280;   // 4 words

    // Multi-prepare scratch (sized at codegen time).
    uint256 internal constant       ROT_POINTS_MPTR = 0x4300;
    uint256 internal constant       X1_POWERS_MPTR = 0x4680;
    // Q_COM materialization is currently fused into the final MSM scratch,
    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero
    // reserved capacity until a future emitter starts writing Q_COM_MPTR.
    uint256 internal constant            Q_COM_MPTR = 0x4ea0;
    uint256 internal constant      Q_EVAL_SET_MPTR = 0x4ea0;

    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals
    // block of the proof; we keep it as a memory slot for symmetry.
    uint256 internal constant         Q_EVAL_CPTR_MPTR = 0x55a0;

    // Reserved 4-word slot for the G1 identity (point at infinity) in
    // EIP-2537 padded form. EVM memory is zero-initialised, and we
    // never write to this region, so the four `mload`s below produce
    // 0,0,0,0 which is exactly the identity encoding the EIP-2537
    // ec_add / ec_mul precompiles accept.
    uint256 internal constant       G1_IDENTITY_MPTR = 0x56a0;

    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain
    // Solidity proof shim rewrites proof scalars into canonical BE words,
    // so `calldataload` gives the field element directly. The transcript-
    // side `evaluations` loop range-checks and spills that value here so
    // downstream eval references (gate evaluator + PCS q_eval Horner)
    // become 3-gas `mload(...)` instead of calldata reads.
    uint256 internal constant     REVERSED_EVALS_MPTR = 0x5800;
    uint256 internal constant      SELECTOR_ACC_MPTR = 0x6b00;
    uint256 internal constant   QUOTIENT_RETURN_MPTR = 0x80;
    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = 0x6b00;
    uint256 internal constant        TRACE_U256_MPTR = 0x9420;

    // ----------------------------------------------------------------------
    // Per-category bases for EIP-2537 padded G1 commitments. The proof
    // calldata carries 128-byte uncompressed/padded G1s after the off-chain
    // proof shim repacks midnight-proofs' native compressed stream; this
    // region stores the 4-word slots used by PCS / quotient-fold sections.
    //
    // Cumulative offsets (in words from `comms_mptr_base`):
    //   ADVICE_COMMS_MPTR_BASE          + 0
    //   LOOKUP_M_COMMS_MPTR_BASE        + 4*total_advices
    //   PERM_Z_COMMS_MPTR_BASE          + 4*total_advices + 4*num_lookups
    //   LOOKUP_HELPER_COMMS_MPTR_BASE   + ... + 4*num_permutation_zs
    //   LOOKUP_Z_COMMS_MPTR_BASE        + ... + 4*lookup_helper_chunks_total
    //   TRASHCAN_COMMS_MPTR_BASE        + ... + 4*num_lookups
    //   QUOTIENT_LIMB_COMMS_MPTR_BASE   + ... + 4*num_trashcans
    // ----------------------------------------------------------------------
    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = 0x6080;
    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = 0x6480;
    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = 0x6580;
    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = 0x6700;
    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = 0x6800;
    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = 0x6900;
    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = 0x6900;

    // BLS12-381 scalar-field modulus, used for transcript challenges and all
    // Halo2 verifier arithmetic.
    uint256 internal constant FR_MODULUS        = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    // BLS12-381 Fp modulus minus one, split like an EIP-2537 coordinate:
    // high word = 16 zero bytes || top 16 coordinate bytes, low word =
    // bottom 32 coordinate bytes.
    uint256 internal constant BLS_P_HI             = 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7;
    uint256 internal constant BLS_P_MINUS_ONE_LO   = 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;
    // Packed public-accumulator sentinels for the shifted coordinate codec.
    // The `_WITH_ID_FLAG` variant is used only for the first x-coordinate word.
    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0 = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;
    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa;
    uint256 internal constant BLS_P_MINUS_ONE_PACKED_1 = 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84;

        /// @notice Smoke-check the Cancun/EIP-2537 runtime features required by the verifier.
    /// @dev Exercises MCOPY and identity EIP-2537 inputs to catch incompatible chain/fork configurations at deployment.
    function require_eip2537_precompiles() private view {
        assembly ("memory-safe") {
            // Scratch is reused for every runtime-prerequisite probe.
            let scratch := 0x80

            // MCOPY must be available because the verifier uses it for
            // proof-time point/scratch staging. Execute the opcode here so a
            // non-Cancun fork fails during deployment instead of later proofs.
            mstore(scratch, 0x1234)
            mcopy(add(scratch, 0x20), scratch, 0x20)
            if iszero(eq(mload(add(scratch, 0x20)), 0x1234)) { revert(0, 0) }

            // Start the EIP-2537 probes with the identity encoding for G1/G2:
            // all-zero padded words.
            for { let off := 0 } lt(off, 0x0300) { off := add(off, 0x20) } {
                mstore(add(scratch, off), 0)
            }

            // G1ADD(identity, identity) -> identity, 128-byte return.
            // This catches chains where the precompile is missing or returns a
            // non-standard success shape.
            if iszero(staticcall(gas(), 0x0b, scratch, 0x0100, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // Worst-case generated G1MSM with all identity/zero terms ->
            // identity, 128-byte return. This exercises the largest MSM input
            // length rendered by this verifier instead of only a one-pair
            // smoke call.
            let msm_scratch := 0x6b00
            for { let off := 0 } lt(off, 0x2760) { off := add(off, 0x20) } {
                mstore(add(msm_scratch, off), 0)
            }
            // The production verifier uses G1MSM both for commitments and as
            // the subgroup validator for absorbed proof points.
            if iszero(staticcall(gas(), 0x0c, msm_scratch, 0x2760, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // PAIRING_CHECK([(identity_g1, identity_g2), (identity_g1, identity_g2)])
            // -> true, 32-byte return. This matches the runtime two-pair KZG
            // pairing input size and catches absent pairing precompiles,
            // short return data, and obviously incompatible semantics.
            if iszero(staticcall(gas(), 0x0f, scratch, 0x0300, scratch, 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
        }
    }

    
    /// @notice Create a verifier pinned to a generated verifying key.
    /// @dev Checks MCOPY/EIP-2537 availability and verifies the VK runtime before storing its address.
    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.
    constructor(address authorizedVk) {
        // Embedded quotient path: only the external VK runtime needs to be
        // pinned, but the runtime opcode/precompile prerequisites are still
        // mandatory.
        require_eip2537_precompiles();
        require(
            authorizedVk.code.length == EXPECTED_VK_LENGTH
                && authorizedVk.codehash == EXPECTED_VK_CODEHASH,
            "invalid vk"
        );
        AUTHORIZED_VK = authorizedVk;
    }

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
    ) external view returns (bool) {
        // Cheap ABI-shape guard before any generated memory work:
        //   - proof head must point at the bytes payload;
        //   - instances head must point at the generated instance array.
        //
        // The verifier below is a hand-rolled calldata parser. Failing here
        // keeps malformed dynamic-argument layouts from being interpreted as a
        // valid Midfall proof stream.
        assembly ("memory-safe") {
            if iszero(and(eq(calldataload(0x04), 0x40), eq(calldataload(0x24), sub(NUM_INSTANCE_CPTR, 0x04)))) {
                revert(0, 0)
            }
        }
        // Non-embedded renders pin the VK by address and codehash. The Yul
        // loader rechecks the runtime before every proof and copies the
        // INVALID-prefixed payload into VK_MPTR.
        address vk = AUTHORIZED_VK;
        assembly ("memory-safe") {
            // This block owns the call-frame memory and remains terminal.
            // Generated scratch starts at TRANSCRIPT_MPTR (0x80), preserving
            // Solidity's reserved scratch, free-memory-pointer, and zero-slot
            // words. See docs/MEMORY_LAYOUT.md.
            // ===============================================================
            // Helpers: modexp, transcript, EIP-2537 calls
            // ===============================================================

                // Inverse of a Fr scalar via modexp(x, r-2, r). The verifier
            // calls this only after transcript absorption is complete, so it
            // reuses the dead transcript buffer just below VK_MPTR instead of
            // a fixed post-VK address that can collide with live PCS scratch
            // when the VK payload becomes smaller.
            function scalar_inv(x) -> inv {
                // Zero has no multiplicative inverse in Fr; callers rely on a
                // revert here rather than a bogus modexp result. Check the
                // full canonical range, not just the literal word 0: for any
                // x congruent to 0 mod r (x = r, say) modexp returns 0, which
                // downstream mulmod chains would silently absorb. Every
                // current call site feeds addmod/mulmod output, so this only
                // guards against a future emitter passing a raw scalar.
                if iszero(lt(x, FR_MODULUS)) { revert(0, 0) }
                if iszero(x) { revert(0, 0) }
                let p := 0x1c20
                // EIP-198 modexp frame:
                //   [base_len, exp_len, mod_len, base, exponent, modulus]
                mstore(add(p, 0x00), 0x20)        // base len
                mstore(add(p, 0x20), 0x20)        // exp len
                mstore(add(p, 0x40), 0x20)        // mod len
                mstore(add(p, 0x60), x)
                mstore(add(p, 0x80), sub(FR_MODULUS, 2))
                mstore(add(p, 0xa0), FR_MODULUS)
                if iszero(staticcall(gas(), 0x05, p, 0xc0, p, 0x20)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
                inv := mload(p)
            }

            // ---------- Streaming Keccak256 transcript helpers ----------
            //
            // The transcript buffer lives at
            // memory[TRANSCRIPT_MPTR..buf_len). On verifier entry it starts
            // empty. Each common(input) appends raw bytes. squeeze_*(buf_len)
            // computes one Keccak digest, reseeds the buffer with that
            // 32-byte digest, and samples a Fq element as
            // uint256(digest_be) mod r.

            function transcript_init() -> buf_len {
                // Empty transcript buffer starts exactly at TRANSCRIPT_MPTR.
                buf_len := TRANSCRIPT_MPTR
            }

            // Append one 32-byte big-endian field/transcript word at the
            // current end of the transcript buffer.
            function common_word(buf_len, word) -> ret {
                mstore(buf_len, word)
                ret := add(buf_len, 32)
            }

            // Absorb a BLS12-381 G1 point in EIP-2537 padded
            // uncompressed form (4 calldata words = 128 bytes:
            // x_hi || x_lo || y_hi || y_lo, each coord = 16 zero
            // pad bytes + 48 big-endian field bytes) into the
            // transcript buffer at `buf_len`.
            //
            // Matches the patched `Hashable<Keccak256> for
            // midnight_curves::G1Projective::to_input` in
            // midnight-proofs, which now emits the same 128-byte form
            // (`midfall/proofs/src/transcript/implementors.rs`). The
            // previous emitter hashed the 48-byte ZCash compressed
            // encoding instead and ran a 384-bit `lex(y) > lex(p − y)`
            // ladder + identity flag fixup to derive the sign bit on
            // the fly; switching to the uncompressed form drops that
            // ladder entirely.
            //
            // Canonicality: reject non-zero bytes in the top 16 bytes
            // of each `_hi` calldata word and reject coordinates
            // outside Fp. Normalizing those bytes before hashing would
            // make multiple calldata encodings share one transcript.
            //
            // This helper does not run an independent curve/subgroup
            // check. Instead, ProtocolPlan::validate rejects generated
            // plans where an absorbed proof commitment would not later be
            // consumed by an EIP-2537 G1MSM or pairing path, and those
            // precompiles perform the curve/subgroup validation.
            //
            // The point's uncompressed form remains in calldata; the
            // call site is responsible for `calldatacopy`-ing it into
            // memory afterwards if it needs the on-curve coordinates.
            function common_uncompressed_g1(buf_len, cptr) -> ret {
                let x_hi_word := calldataload(cptr)
                let x_lo := calldataload(add(cptr, 0x20))
                let y_hi_word := calldataload(add(cptr, 0x40))
                let y_lo := calldataload(add(cptr, 0x60))
                if shr(128, x_hi_word) { revert(0, 0) }
                if shr(128, y_hi_word) { revert(0, 0) }

                let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)
                let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)
                if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
                    revert(0, 0)
                }
                if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
                    revert(0, 0)
                }

                // Memcpy the 4 calldata words (128 bytes) verbatim
                // into the keccak buffer.
                calldatacopy(buf_len, cptr, 0x80)
                ret := add(buf_len, 0x80)
            }

            // One Keccak finalization + reseed. Returns the new buffer
            // cursor (= TRANSCRIPT_MPTR + 32) and stores the squeezed Fq at
            // `mptr`.
            function squeeze_to(buf_len, mptr) -> ret {
                let h0 := keccak256(TRANSCRIPT_MPTR, sub(buf_len, TRANSCRIPT_MPTR))
                // Reseed: write the 32-byte digest at start of buffer.
                mstore(TRANSCRIPT_MPTR, h0)
                let r := FR_MODULUS
                // Sample Fq as uint256(keccak_digest_be) mod r.
                mstore(mptr, mod(h0, r))
                ret := add(TRANSCRIPT_MPTR, 32)
            }

            // ---------- EC primitives (EIP-2537 wrappers) ----------
            //
            // These mirror the BN254 helpers but operate on 4-word G1
            // points. They use planned memory windows above Solidity's
            // reserved prefix; the streaming transcript buffer is no longer
            // needed once all challenges are squeezed.

            // Invert a contiguous run of Fr words in-place using Montgomery's
            // batch inversion trick:
            //   1. write prefix products to scratch;
            //   2. invert the total product once with modexp;
            //   3. walk backward to recover each individual inverse.
            //
            // The function returns a boolean instead of reverting so callers
            // can combine it with other `success` plumbing until a section
            // boundary decides whether to fail closed.
            function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret {
                ret := success
                if iszero(ret) { leave }
                // Memory ranges must be forward and word-aligned by
                // construction; a reversed range is always a codegen error.
                if lt(mptr_end, mptr_start) {
                    ret := 0
                    leave
                }

                let count_bytes := sub(mptr_end, mptr_start)
                // Empty batch is valid and leaves memory untouched.
                if iszero(count_bytes) { leave }

                // Fast path for a single denominator: avoid prefix scratch and
                // just run one modexp inverse in place.
                if eq(count_bytes, 0x20) {
                    let x := mload(mptr_start)
                    // Reject anything congruent to zero mod r, not just the
                    // literal word 0: modexp would return 0 for those too, and
                    // the caller would take it for a valid inverse.
                    if iszero(lt(x, r)) {
                        ret := 0
                        leave
                    }
                    if iszero(x) {
                        ret := 0
                        leave
                    }

                    let single_scratch := scratch_mptr
                    mstore(add(single_scratch, 0x00), 0x20)
                    mstore(add(single_scratch, 0x20), 0x20)
                    mstore(add(single_scratch, 0x40), 0x20)
                    mstore(add(single_scratch, 0x60), x)
                    mstore(add(single_scratch, 0x80), sub(r, 2))
                    mstore(add(single_scratch, 0xa0), r)
                    ret := staticcall(gas(), 0x05, single_scratch, 0xc0, single_scratch, 0x20)
                    ret := and(ret, eq(returndatasize(), 0x20))
                    if ret { mstore(mptr_start, mload(single_scratch)) }
                    leave
                }

                // Forward pass: scratch stores prefix products up to, but not
                // including, the final element. `gp` becomes the total product.
                let gp_mptr := scratch_mptr
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for {} lt(mptr, sub(mptr_end, 0x20)) {} {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)
                // A zero total product means at least one denominator was
                // zero, so no batch inverse exists.
                if iszero(gp) {
                    ret := 0
                    leave
                }

                // Invert the total product once.
                mstore(add(gp_mptr, 0x00), 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
                ret := staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20)
                ret := and(ret, eq(returndatasize(), 0x20))
                // Leave before the backward pass on a failed modexp. A failed
                // staticcall writes no output, so `mload(gp_mptr)` would read
                // back the stale frame header and the pass below would
                // overwrite every denominator in [mptr_start, mptr_end) with
                // garbage products before returning ret = 0.
                if iszero(ret) { leave }
                let all_inv := mload(gp_mptr)

                // Backward pass: derive each inverse from the inverted total
                // product and the saved prefix products.
                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for {} lt(second_mptr, mptr) {} {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Final EIP-2537 pairing wrapper. `lhs_mptr` and `rhs_mptr` are
            // 4-word G1 slots; G2 bases are loaded from the pinned VK payload.
            function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret {
                ret := success
                // Every other exit from this function reverts, and the
                // terminal `return(RETURN_MPTR, 0x20)` in TraceReturn.yul
                // returns true without consulting `success`. Revert here too,
                // so this helper has no path that hands control back to a
                // caller that would report success for an unverified proof.
                if iszero(ret) { revert(0, 0) }
                // Lay out two (G1, G2) pairs at scratch..scratch+0x300:
                //   [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)]
                // Cancun MCOPY (3 + 3·words gas) replaces what used to
                // be a 4-step mstore chain for each G1 (~60 gas) and an
                // 8-iter mstore loop for each G2 (~240 gas). Net saving
                // here is ~500 gas per ec_pairing call.
                let scratch := 0x0320
                mcopy(scratch,              lhs_mptr,                 0x80)
                mcopy(add(scratch, 0x80),   G2_BASE_MPTR,             0x100)
                mcopy(add(scratch, 0x180),  rhs_mptr,                 0x80)
                mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)
                ret := staticcall(gas(), 0x0f, scratch, 0x0300, scratch, 0x20)
                ret := and(ret, eq(returndatasize(), 0x20))
                ret := and(ret, mload(scratch))
                if iszero(ret) { revert(0, 0) }
                ret := 1
            }

                // ---------- IVC accumulator public-input decoding ----------
            //
            // `AssignedForeignPoint<BLS12-381>` exposes each base-field coordinate
            // through `AssignedField::as_public_input`: seven radix-2^56 limbs of
            // (coord - 1) are packed four-at-a-time into native field elements.
            // The x coordinate's first packed word carries the identity flag by
            // adding one raw radix base. Rebuild EIP-2537 padded
            // (x_hi, x_lo, y_hi, y_lo) words from that encoding.
            //
            // Public-input layout for one coordinate:
            //   word 0: limb_0 | limb_1 << bits | ... up to limbs_per_word
            //   word 1: next limbs, if any
            //
            // The limbs are little-endian in the represented integer even
            // though calldata words are loaded as big 256-bit values. The loop
            // below extracts each limb by shifting inside the packed word and
            // reconstructs the full coordinate into the two-word EIP-2537
            // representation expected by the BLS12-381 precompiles.
            function load_acc_coord_shifted(src, bits, n, base, limbs_per_word, first_adjust) -> hi, lo {
                // Mask for one radix limb, e.g. 2^56 - 1 for the current
                // BLS12-381 self-emulation parameters.
                let mask := sub(base, 1)
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    // Limb words are little-endian packed inside each Fr
                    // public input. `first_adjust` removes the identity flag
                    // base from the first x word when present.
                    let packed := calldataload(add(src, mul(div(i, limbs_per_word), 0x20)))
                    if and(iszero(div(i, limbs_per_word)), first_adjust) {
                        packed := sub(packed, first_adjust)
                    }
                    // Select limb i from its packed field word. The mod/div
                    // pair maps a limb index to an intra-word limb slot and
                    // the calldata word containing it.
                    let limb := and(shr(mul(mod(i, limbs_per_word), bits), packed), mask)

                    let shift := mul(i, bits)
                    // Split the reconstructed 384-bit coordinate into the
                    // EIP-2537 high/low words expected by the precompiles.
                    if lt(shift, 256) {
                        lo := add(lo, shl(shift, limb))
                        if gt(add(shift, bits), 256) {
                            // A limb can straddle the 256-bit low/high split.
                            // Move the overflow bits into hi.
                            hi := add(hi, shr(sub(256, shift), limb))
                        }
                    }
                    if iszero(lt(shift, 256)) {
                        // Once shift >= 256 the whole limb belongs to hi.
                        hi := add(hi, shl(sub(shift, 256), limb))
                    }
                }
            }

            // The shifted coordinate codec represents zero as p-1 before the
            // final +1 below, so keep this sentinel explicit.
            function is_bls_p_minus_one(hi, lo) -> yes {
                yes := and(eq(hi, BLS_P_HI), eq(lo, BLS_P_MINUS_ONE_LO))
            }

            // Canonical encoded accumulator identity:
            //   x = p-1 plus the identity flag in the first packed word,
            //   y = p-1 with no identity flag.
            // It decodes to the EIP-2537 point-at-infinity slot (all zeros).
            //
            // This fast path is deliberately stricter than "decodes to zero":
            // the point at infinity has exactly one accepted public-input
            // encoding. Non-canonical zero-like encodings are rejected later.
            function is_acc_encoded_identity(src) -> yes {
                yes := and(
                    and(
                        eq(calldataload(src), BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG),
                        eq(calldataload(add(src, 0x20)), BLS_P_MINUS_ONE_PACKED_1)
                    ),
                    and(
                        eq(calldataload(add(src, 0x40)), BLS_P_MINUS_ONE_PACKED_0),
                        eq(calldataload(add(src, 0x60)), BLS_P_MINUS_ONE_PACKED_1)
                    )
                )
            }

            // Reject unused high bits in the packed public-input words. This
            // makes each accumulator point encoding canonical before it reaches
            // the precompile-based curve/subgroup validation.
            function check_acc_coord_packing(src, bits, n, limbs_per_word) -> ok {
                ok := 1
                // Number of packed native-field public-input words occupied by
                // one coordinate.
                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                for { let word_idx := 0 } lt(word_idx, coord_words) { word_idx := add(word_idx, 1) } {
                    // The final word may contain fewer than limbs_per_word
                    // limbs. Any unused high bits must be zero, otherwise the
                    // same coordinate would have multiple calldata encodings.
                    let remaining := sub(n, mul(word_idx, limbs_per_word))
                    let limbs_in_word := limbs_per_word
                    if lt(remaining, limbs_per_word) {
                        limbs_in_word := remaining
                    }
                    let used_bits := mul(limbs_in_word, bits)
                    if lt(used_bits, 256) {
                        // shl(used_bits, 1) == 2^used_bits. The packed word
                        // must be strictly less than that bound.
                        ok := and(ok, lt(calldataload(add(src, mul(word_idx, 0x20))), shl(used_bits, 1)))
                    }
                }
            }

            // Decode one shifted coordinate. `allow_id` is true only for x,
            // because the identity flag lives in x's first packed word.
            function load_acc_coord(src, allow_id, bits, n, base, limbs_per_word) -> ok, hi, lo, is_id {
                ok := check_acc_coord_packing(src, bits, n, limbs_per_word)
                if and(allow_id, iszero(lt(calldataload(src), base))) {
                    // Probe the x identity flag by removing one radix base and
                    // checking whether the adjusted coordinate is p-1.
                    //
                    // `calldataload(src) >= base` is a cheap prefilter: only x
                    // can carry this flag, and adding one radix base must make
                    // the first packed word at least base.
                    let adj_hi, adj_lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, base)
                    is_id := is_bls_p_minus_one(adj_hi, adj_lo)
                }

                // Decode again with the identity adjustment applied only when
                // the canonical identity flag was actually detected.
                hi, lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, mul(is_id, base))
                ok := and(
                    ok,
                    // Coordinate must be in the BLS12-381 base field, i.e.
                    // <= p - 1 in split hi/lo form.
                    or(lt(hi, BLS_P_HI), and(eq(hi, BLS_P_HI), iszero(gt(lo, BLS_P_MINUS_ONE_LO))))
                )

                let was_p_minus_one := is_bls_p_minus_one(hi, lo)
                if was_p_minus_one {
                    // Shifted encoding maps p-1 back to zero.
                    hi := 0
                    lo := 0
                }
                if iszero(was_p_minus_one) {
                    // All other coordinates are encoded as coord - 1, so add
                    // one back with carry into the high word.
                    let next_lo := add(lo, 1)
                    hi := add(hi, lt(next_lo, lo))
                    lo := next_lo
                }

                // EIP-2537 pads each 48-byte Fp coordinate to 64 bytes,
                // so the high word must fit in its low 128 bits.
                // This also catches impossible reconstructions above 384 bits.
                ok := and(ok, lt(hi, shl(128, 1)))
            }

            // Decode a public accumulator point into an EIP-2537 4-word G1
            // slot. Non-identity points are curve/subgroup checked later by
            // routing them through G1MSM.
            function load_acc_point(dst, src, bits, n, base) -> ok, is_id {
                // Prefer the canonical all-coordinate identity encoding before
                // attempting coordinate-level shifted decoding. This accepts
                // the point at infinity only in the exact form generated by the
                // circuit's public-input codec.
                is_id := is_acc_encoded_identity(src)
                if is_id {
                    ok := 1
                    // EIP-2537 encodes G1 identity as four zero words:
                    // x_hi = x_lo = y_hi = y_lo = 0.
                    mstore(dst, 0)
                    mstore(add(dst, 0x20), 0)
                    mstore(add(dst, 0x40), 0)
                    mstore(add(dst, 0x60), 0)
                }
                if iszero(is_id) {
                    // x occupies coord_words packed public-input words; y
                    // starts immediately after x.
                    let limbs_per_word := 4
                    let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                    // Only x may carry the identity flag. y must decode as a
                    // normal shifted coordinate.
                    let x_ok, x_hi, x_lo, x_is_id := load_acc_coord(src, 1, bits, n, base, limbs_per_word)
                    let y_ok, y_hi, y_lo, y_id := load_acc_coord(
                        add(src, mul(coord_words, 0x20)),
                        0,
                        bits,
                        n,
                        base,
                        limbs_per_word
                    )
                    // y_id is always zero because allow_id was false, but the
                    // tuple shape is shared with x decoding.
                    pop(y_id)
                    ok := and(x_ok, y_ok)
                    is_id := x_is_id

                    if is_id {
                        // If x carried the identity flag, both decoded
                        // coordinates must be zero after shifting. Any other y
                        // value would be a malformed infinity encoding.
                        ok := and(ok, iszero(or(or(x_hi, x_lo), or(y_hi, y_lo))))
                        mstore(dst, 0)
                        mstore(add(dst, 0x20), 0)
                        mstore(add(dst, 0x40), 0)
                        mstore(add(dst, 0x60), 0)
                    }
                    if iszero(is_id) {
                        // The coordinate codec maps encoded p-1 to decoded
                        // zero. EIP-2537 reserves affine (0,0) for the point
                        // at infinity, so a decoded infinity is only valid
                        // when the canonical accumulator identity encoding
                        // was used above.
                        let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))
                        ok := and(ok, iszero(decoded_zero))
                        // Store the affine point in the exact precompile input
                        // layout: x_hi, x_lo, y_hi, y_lo.
                        mstore(dst, x_hi)
                        mstore(add(dst, 0x20), x_lo)
                        mstore(add(dst, 0x40), y_hi)
                        mstore(add(dst, 0x60), y_lo)
                    }
                }
            }

    

            let r := FR_MODULUS
            let success := true

    

            // ===============================================================
            // VK loading: either bake in the embedded VK bytes or fetch
            // them from the linked AUTHORIZED_VK contract.
            //
            // This is the first verifier phase after helper definitions. Its
            // job is to make the generated VK payload available at VK_MPTR in
            // one canonical memory layout, regardless of whether this render
            // embeds the VK directly or links a separate Halo2VerifyingKey
            // contract.
            //
            // Later template partials treat VK_MPTR as already populated with:
            //   - header words: vk_digest, domain data, accumulator metadata;
            //   - BLS12-381 base points used by the final pairing;
            //   - compact quotient VM constants/program bytes, when enabled;
            //   - fixed and permutation commitments in 4-word G1 slots.
            // ===============================================================
            {
                // Re-check the pinned VK dependency on every proof. The
                // constructor check catches normal deployment mistakes, while
                // this fresh check hardens forks or same-transaction edge
                // cases where code at the authorized address could differ
                // from the runtime originally pinned by this verifier.
                //
                // EXPECTED_VK_LENGTH includes the leading INVALID byte in the
                // Halo2VerifyingKey runtime. EXPECTED_VK_CODEHASH_WORD is the
                // full runtime hash, not only the payload hash.
                if iszero(and(
                    eq(extcodesize(vk), EXPECTED_VK_LENGTH),
                    eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)
                )) { revert(0, 0) }
                // Runtime byte 0 is INVALID so direct calls cannot execute the
                // payload. Copy from byte 1 into VK_MPTR to reconstruct the
                // exact payload layout used by the embedded branch.
                extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)

                // Cross-check loaded VK header words against the verifier
                // constants used by later parser, domain, and accumulator
                // paths. Codehash pinning protects the external VK address;
                // these checks catch generator drift before calldata parsing
                // chooses a stale schema.
                success := and(success, eq(mload(NUM_INSTANCES_MPTR), 32))
                success := and(success, eq(mload(K_MPTR), 13))
                success := and(success, eq(mload(HAS_ACCUMULATOR_MPTR), 0))
                success := and(success, eq(mload(ACC_OFFSET_MPTR), 0))
                success := and(success, eq(mload(NUM_ACC_LIMBS_MPTR), 0))
                success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), 0))
                if iszero(success) { revert(0, 0) }
                //
                // The checks below validate the dynamic ABI envelope before the
                // transcript parser starts walking raw calldata:
                //   - proof bytes length equals the generated proof layout;
                //   - instance array length equals the generated public input
                //     count;
                //   - total calldata length has no missing or trailing words.
                //
                // `success` is folded through `and` for consistency with later
                // sections, then immediately enforced at the end of this block.
                // A failure here means the verifier is not looking at the proof
                // shape it was generated to parse.
                success := and(success, eq(0x1480, calldataload(PROOF_LEN_CPTR)))
                success := and(success, eq(32, calldataload(NUM_INSTANCE_CPTR)))
                // Calldata must contain exactly the ABI selector, proof bytes,
                // instance-array length, and generated number of instance
                // words. Any trailing bytes fail closed.
                success := and(
                    success,
                    eq(calldatasize(), add(INSTANCE_CPTR, 0x0400))
                )
                // Stop before any transcript absorption if the ABI/proof shape
                // is not exactly the generated one.
                if iszero(success) { revert(0, 0) }
            }

                // ===============================================================
            // Transcript: VK digest + instances + proof.
            //
            // This block is the Solidity mirror of the native Midfall verifier
            // transcript schedule. It does three jobs at once:
            //
            //   1. Absorb public data and proof bytes into the streaming
            //      Keccak transcript in exactly the native order.
            //   2. Decode/range-check proof scalars and canonical G1 calldata.
            //   3. Copy proof commitments/evaluations into planned memory
            //      slots consumed by Lagrange, quotient, PCS, and pairing
            //      blocks later in the verifier.
            //
            // `buf_len` is a write cursor into the transcript buffer. The
            // helper functions append bytes and return the new cursor; squeeze
            // helpers hash memory[TRANSCRIPT_MPTR..buf_len), reseed the buffer
            // with the digest, and write the sampled Fr challenge to memory.
            // ===============================================================
            let buf_len := transcript_init()
            // VK_DIGEST_MPTR holds the digest as a BE 32-byte word (the
            // VK contract stores it via `mstore`, which matches the
            // Keccak Fq transcript input).
            //
            // This digest commits to the verifier key / constraint system
            // before any proof material is read.
            buf_len := common_word(buf_len, mload(VK_DIGEST_MPTR))

            // Absorb committed_pi = G1Affine::identity() when the
            // `committed-instances` feature is on in midnight-proofs.
            // Under the patched `Hashable<Keccak256>::to_input` (see
            // `midfall/proofs/src/transcript/implementors.rs`), the
            // identity hashes as 128 zero bytes (EIP-2537 (0,0)
            // convention), NOT the 48-byte ZCash compressed form
            // 0xc0||47*0x00 that the previous emitter produced.
            // Native verifier absorbs this BEFORE the instance count.
            {
                // 128 zero bytes: zero out 4 consecutive 32-byte words
                // at buf_len.
                // This is a raw transcript absorb, not a memory slot kept for
                // later elliptic-curve operations.
                mstore(buf_len, 0)
                mstore(add(buf_len, 0x20), 0)
                mstore(add(buf_len, 0x40), 0)
                mstore(add(buf_len, 0x60), 0)
                buf_len := add(buf_len, 0x80)
            }

            {
                // Native verifier absorbs a length scalar before instance
                // values; Keccak Fq transcript input is canonical BE.
                // The ABI length was already checked against this generated
                // constant in VkLoading.yul.
                buf_len := common_word(buf_len, 32)

                let instance_cptr := INSTANCE_CPTR
                for { let instance_cptr_end := add(instance_cptr, 0x0400) }
                    lt(instance_cptr, instance_cptr_end)
                    { instance_cptr := add(instance_cptr, 0x20) } {
                    let inst_be := calldataload(instance_cptr)
                    // Public inputs are BLS12-381 scalar-field elements. They
                    // must be canonical before transcript absorption; accepting
                    // non-canonical encodings would admit transcript aliases.
                    success := and(success, lt(inst_be, r))
                    // Instances are passed BE in calldata, matching the
                    // Keccak Fq transcript input.
                    buf_len := common_word(buf_len, inst_be)
                }
                if iszero(success) { revert(0, 0) }
            }

            // ===============================================================
            // Per-user-phase reads + challenge squeezes.
            //
            // Each proof G1 is already EIP-2537 padded in calldata. The
            // verifier validates and absorbs that 128-byte form, then copies
            // it into the corresponding per-category MPTR. The PCS /
            // quotient-fold blocks below dereference those MPTRs.
            //
            // All G1 reads follow the same pattern:
            //   - common_uncompressed_g1 canonicalizes/range-checks the two Fp
            //     coordinates and appends the exact 128 calldata bytes;
            //   - calldatacopy stores the same 4-word G1 slot in planned
            //     memory for later EIP-2537 precompile calls;
            //   - proof_cptr advances by one G1 byte length.
            // ===============================================================
            // proof_cptr walks the raw proof bytes inside the ABI `bytes`
            // payload. Every successful read advances it exactly once, and the
            // final equality check below proves the parser consumed the whole
            // generated proof layout.
            let proof_cptr := PROOF_CPTR
            // advice_walk mirrors proof commitment order into the contiguous
            // G1 commitment memory region used by PCS and quotient folding.
            let advice_walk := ADVICE_COMMS_MPTR_BASE
            // ---- User phase 1 ----
            // Advice commitments for this phase are absorbed before the phase's
            // challenge squeezes. The number of commitments and challenges is
            // generated from the protocol plan.
            for { let end := add(proof_cptr, 0x0400) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                // Store the commitment at its phase-ordered advice slot.
                calldatacopy(advice_walk, proof_cptr, 0x80)
                advice_walk := add(advice_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }

            // ---- theta ----
            // From this point onward the transcript alternates between
            // squeezed challenges and proof commitments exactly as
            // midnight-proofs does in `plonk/verifier.rs`.
            // theta batches lookup input expressions.
            buf_len := squeeze_to(buf_len, THETA_MPTR)
            // ---- multiplicities (one G1 per lookup) ----
            // Lookup multiplicity commitments are absorbed after theta and
            // copied into their own contiguous G1 region.
            let lookup_m_walk := LOOKUP_M_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, 0x0100) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(lookup_m_walk, proof_cptr, 0x80)
                lookup_m_walk := add(lookup_m_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }

            // ---- beta, gamma ----
            // beta and gamma are the permutation/lookup randomizers. They are
            // squeezed after lookup multiplicities and before permutation
            // product commitments, matching the native verifier schedule.
            buf_len := squeeze_to(buf_len, BETA_MPTR)
            buf_len := squeeze_to(buf_len, GAMMA_MPTR)
            // ---- permutation Z products ----
            // Permutation product commitments are used by the permutation
            // identities in the quotient numerator and later by PCS openings.
            let perm_z_walk := PERM_Z_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, 0x0180) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(perm_z_walk, proof_cptr, 0x80)
                perm_z_walk := add(perm_z_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            // ---- lookup helpers + accumulators (per-lookup) ----
            // Each lookup contributes zero or more helper commitments followed
            // by its lookup accumulator Z commitment. The generated layout keeps
            // helper commitments and accumulator commitments in separate memory
            // regions because the quotient/PCS schedules address them
            // differently.
            let lookup_helper_walk := LOOKUP_HELPER_COMMS_MPTR_BASE
            let lookup_z_walk := LOOKUP_Z_COMMS_MPTR_BASE
            // lookup 0: 1 helper(s) + 1 acc
            // Helper commitments for lookup 0.
            for { let end := add(proof_cptr, 0x80) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(lookup_helper_walk, proof_cptr, 0x80)
                lookup_helper_walk := add(lookup_helper_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            // Accumulator commitment for lookup 0. This is
            // always one G1 when the lookup section is present.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(lookup_z_walk, proof_cptr, 0x80)
            lookup_z_walk := add(lookup_z_walk, 0x80)
            proof_cptr := add(proof_cptr, 0x80)
            // lookup 1: 1 helper(s) + 1 acc
            // Helper commitments for lookup 1.
            for { let end := add(proof_cptr, 0x80) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(lookup_helper_walk, proof_cptr, 0x80)
                lookup_helper_walk := add(lookup_helper_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            // Accumulator commitment for lookup 1. This is
            // always one G1 when the lookup section is present.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(lookup_z_walk, proof_cptr, 0x80)
            lookup_z_walk := add(lookup_z_walk, 0x80)
            proof_cptr := add(proof_cptr, 0x80)

            // ---- trash_challenge ----
            // Midnight squeezes this challenge unconditionally, even when the
            // circuit has no trash arguments.
            // Keeping this squeeze unconditional preserves transcript
            // compatibility across circuits with and without trash columns.
            buf_len := squeeze_to(buf_len, TRASH_CHALLENGE_MPTR)

            // ---- y ----
            // y batches all quotient identities. Quotient commitments are read
            // only after y is sampled, matching the Rust verifier flow.
            buf_len := squeeze_to(buf_len, Y_MPTR)

            // ---- quotient commitment(s) ----
            // Each uncompressed quotient commitment is calldatacopied directly to
            // QUOTIENT_LIMB_COMMS_MPTR_BASE; the Horner fold below reads
            // them back from memory. common_uncompressed_g1 absorbs the
            // 128-byte calldata form into the transcript verbatim.
            //
            // Multi-limb quotient mode reads several Q_i commitments; single-H
            // mode renders this loop with one limb.
            let quotient_walk := QUOTIENT_LIMB_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, 0x0200) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(quotient_walk, proof_cptr, 0x80)
                quotient_walk := add(quotient_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }

            // ---- x ----
            // x is the main evaluation point. Values read after this point are
            // alleged polynomial evaluations at x or derived PCS openings.
            buf_len := squeeze_to(buf_len, X_MPTR)

            // ---- evaluations ----
            // Optimisation H3: the off-chain Solidity proof shim rewrites
            // proof scalars into BE calldata words. Spill each decoded eval
            // into REVERSED_EVALS_MPTR in the same iteration we range-check
            // it, so downstream references can use cheap mload.
            //
            // The Rust verifier conceptually reads evaluations in query order.
            // The lowering plan arranges REVERSED_EVALS_MPTR in the order used
            // by the quotient VM/direct evaluator, hence the generated name.
            {
                let eval_buf := REVERSED_EVALS_MPTR
                for { let end := add(proof_cptr, 0x0880) }
                    lt(proof_cptr, end)
                    {} {
                    let eval := calldataload(proof_cptr)
                    // Proof evaluation scalars must be canonical Fr elements
                    // before they are absorbed or made available to quotient
                    // reconstruction.
                    if iszero(lt(eval, r)) { revert(0, 0) }
                    // Spill for quotient numerator and PCS codegen.
                    mstore(eval_buf, eval)
                    eval_buf := add(eval_buf, 0x20)
                    // Absorb the exact BE field word used by the native
                    // Keccak transcript.
                    buf_len := common_word(buf_len, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                }
            }

            // ---- x1, x2 ----
            // x1 and x2 batch the KZG multi-opening reduction. They are
            // squeezed after all polynomial evaluations are absorbed.
            buf_len := squeeze_to(buf_len, X1_MPTR)
            buf_len := squeeze_to(buf_len, X2_MPTR)

            // ---- f_com (1 uncompressed G1) ----
            // f_com is the commitment to the batched polynomial used by the PCS
            // multi-open protocol. It is both transcript material and later
            // pairing/MSM input.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(F_COM_MPTR, proof_cptr, 0x80)
            proof_cptr := add(proof_cptr, 0x80)

            // ---- x3 ----
            // x3 is the PCS evaluation point for f_com.
            buf_len := squeeze_to(buf_len, X3_MPTR)
            // truncated-challenges mirrors midnight-proofs
            // proofs/src/poly/kzg/mod.rs:
            //   - x3 is the f_com evaluation point and is truncated
            //     immediately after squeeze.
            //   - x1 and x4 remain full squeezed Fr words, but later PCS
            //     batching stores truncate(x1^i) and truncate(x4^i) while
            //     keeping the internal power accumulators full precision.
            // This direct x3 mask is therefore one part of the PCS truncation
            // rule, not the only truncated value used by the verifier.
            mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))

            // ---- q_evals (one Fq per point set) ----
            // q_evals are not spilled into REVERSED_EVALS_MPTR because the PCS
            // emitter reads them as a contiguous calldata range from the saved
            // Q_EVAL_CPTR_MPTR cursor.
            //
            // Each q_eval is the claimed evaluation for one prepared point set
            // in the KZG multi-open reduction. They are still transcript
            // material and must be range-checked as Fr scalars.
            mstore(Q_EVAL_CPTR_MPTR, proof_cptr)
            for { let end := add(proof_cptr, 0x80) }
                lt(proof_cptr, end)
                {} {
                let eval := calldataload(proof_cptr)
                // Canonical Fr check before transcript absorption.
                if iszero(lt(eval, r)) { revert(0, 0) }
                buf_len := common_word(buf_len, eval)
                proof_cptr := add(proof_cptr, 0x20)
            }

            // ---- x4 ----
            // x4 is the final PCS batching challenge, sampled after q_evals
            // and before the opening proof point pi.
            buf_len := squeeze_to(buf_len, X4_MPTR)

            // ---- pi (1 uncompressed G1) ----
            // pi is the KZG opening proof commitment. It is the last proof
            // object absorbed into the transcript and later becomes one side of
            // the final pairing check.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(PI_MPTR, proof_cptr, 0x80)
            proof_cptr := add(proof_cptr, 0x80)

            // The hand-rolled proof parser must consume exactly the ABI
            // `proof` bytes before the `instances` length word. This is
            // redundant with the generated proof length today, but makes
            // future proof-layout drift fail closed.
            //
            // NUM_INSTANCE_CPTR is the calldata word immediately after the
            // dynamic proof bytes payload. If proof_cptr lands anywhere else,
            // some section was under-read or over-read.
            if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { revert(0, 0) }

            // `success` carries deferred canonicality failures from public
            // instance reads. G1/proof scalar helpers revert immediately.
            if iszero(success) { revert(0, 0) }

                // ===============================================================
            // Lagrange & instance-evaluation block (pure Fr arithmetic).
            // ===============================================================
            {
                let k := 13
                let x := mload(X_MPTR)
                // Compute x^n by repeated squaring, with n = 2^k.
                let x_n := x
                for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                // First pass writes denominators (x - omega_i) for every
                // Lagrange value needed below, then appends x^n - 1. The
                // batch inversion pass turns all of them into inverses in one
                // modexp call.
                let mptr := X_N_MPTR
                let mptr_end := add(mptr, 0x0520)
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)

                // Convert inverted denominators into Lagrange evaluations:
                // L_i(x) = (x^n - 1) * n^-1 * omega_i / (x - omega_i).
                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                // l_blind is the sum of the negative-rotation Lagrange terms
                // used by the midnight-proofs blinding identity.
                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for { let l_i_cptr_end := add(X_N_MPTR, 0x0120) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) } {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                // Public instance polynomial evaluation at x. Instance words
                // have already been range-checked and absorbed in transcript
                // order; this loop only forms the linear combination.
                let instance_eval := 0
                for {
                        let instance_cptr := INSTANCE_CPTR
                        let instance_cptr_end := add(instance_cptr, 0x0400)
                    }
                    lt(instance_cptr, instance_cptr_end)
                    { instance_cptr := add(instance_cptr, 0x20)
                      l_i_cptr := add(l_i_cptr, 0x20) } {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                // Persist the derived values into named memory slots consumed
                // by quotient reconstruction and PCS preparation.
                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0x0120))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            if iszero(success) { revert(0, 0) }

                // Optional quotient helper functions. Each one is rendered only
            // when the Rust lowering pass recognized the corresponding
            // expression shape in this generated verifier. They are pure Fr
            // helpers and share the same FR_MODULUS as the surrounding
            // numerator block.            // ===============================================================
            // Batched identity numerator / linearization target.
            //
            // This block does not evaluate the quotient polynomial h(x), and
            // the proof does not provide an h(x) scalar to trust. Instead it:
            //
            //   1. Reconstructs the y-batched constraint numerator nu_y(x)
            //      from the alleged polynomial evaluations read after the
            //      transcript sampled x.
            //   2. Stores -nu_y(x) as the expected opening scalar for the
            //      linearized commitment.
            //
            // The commitment side is built in the next block from the quotient
            // limb commitments as (1 - x^n) * Σ_i x_split^i * Q_i, plus any
            // simple-selector commitments. The PCS check later binds that
            // linearized commitment to this expected scalar at x.
            //
            // Rust source-of-truth:
            //   - verifier.rs reads quotient commitments, samples x, then
            //     reads/computes all evaluations used below.
            //   - mod.rs::partially_evaluate_identities returns identities in
            //     gate, permutation, lookup, trash order.
            //   - linearization/verifier.rs::compute_linearization_commitment
            //     reverse-folds those identities by powers of y, sends
            //     simple-selector identities to selector commitment scalars,
            //     and subtracts fully-evaluated identities into expected_eval.
            //
            // This template is shared by the monolithic and external quotient
            // paths. In the external path, Halo2QuotientEvaluator first copies
            // the verifier memory frame into the same generated addresses.
            //
            // Runtime inputs expected to exist before this block starts:
            //   - `r` is the BLS12-381 scalar-field modulus.
            //   - Y_MPTR holds the quotient batching challenge y.
            //   - X_MPTR, L_*_MPTR, INSTANCE_EVAL_MPTR, and
            //     REVERSED_EVALS_MPTR hold values parsed or derived by the
            //     main verifier after the transcript sampled x.
            //   - VK_MPTR holds the pinned VK payload; in compact mode that
            //     payload includes the quotient constant table and bytecode.
            //
            // Runtime outputs written by this block:
            //   - QUOTIENT_EVAL_MPTR receives the scalar expected opening for
            //     the linearized commitment, namely -nu_y(x).
            //   - SELECTOR_ACC_MPTR[0..num_simple_selectors) receives one
            //     linearization scalar per generated simple selector.
            //
            // Line-by-line reading conventions used below:
            //
            //   * Every runtime value is one canonical Fr element stored in a
            //     256-bit EVM memory word. The small integer operands decoded
            //     from q_program are never field values; they are pointers,
            //     constant-table slots, selector indexes, offsets, or counts.
            //
            //   * `mload(ptr)` is the only way the VM turns a small pointer
            //     operand into a real 255-bit field element. The value loaded
            //     from memory is then combined with `addmod(..., r)` or
            //     `mulmod(..., r)`, so every arithmetic line is reduced modulo
            //     the BLS12-381 scalar-field order.
            //
            //   * `q_top` is the cached top of the VM operand stack. When an
            //     opcode needs to push while `q_top` is already live, the old
            //     value is written to `q_sp` and `q_sp` is advanced by one
            //     word. Binary `ADD`/`MUL` move `q_sp` back by one word and
            //     combine that spilled value with `q_top`.
            //
            //   * Identity boundaries are explicit. Expression opcodes leave
            //     one value in `q_top`; `FOLD_MAIN` or `FOLD_SELECTOR` consumes
            //     it and advances the global y-batch position. Native callback
            //     opcodes are only emitted at empty-stack boundaries and run
            //     generated Yul that performs the same fold side effects.
            //
            //   * The generated Solidity source intentionally emits comments
            //     before opcode cases. Those comments are documentation only:
            //     they do not affect bytecode, but they make rendered verifier
            //     assembly readable without jumping back to Rust codegen.
            // ===============================================================
            {
                // Compact quotient-program mode.
                //
                // The largest identity expressions are not all emitted as
                // unrolled Yul. Instead, most arithmetic is encoded as a small
                // q_program bytecode stored in the VK payload. This block
                // interprets that program, while selected heavy identities may
                // still be emitted as native callbacks for gas.
                //
                // Compact mode is a code-size trade: short bytecode operands
                // name already-planned memory slots, and the interpreter turns
                // those names into Fr arithmetic. The opcode stream is fully
                // generated and pinned by the VK/runtime codehash; no proof
                // calldata can alter control flow.
                // Load the quotient batching challenge used by every fold.
                let y := mload(Y_MPTR)

                // q_const_mptr points to Fr constants used by the VM.
                // q_program_mptr points to the bytecode stream.
                // Constants are stored as consecutive 32-byte Fr words.
                let q_const_mptr := 0x2100
                // Program bytes are also stored in the VK payload, packed into
                // 32-byte words by PackedProgramCodec.
                let q_program_mptr := 0x2660
                // Running Horner accumulator for fully evaluated identities.
                // After all identities, this is nu_y(x) for the `None`
                // identity group.
                // Initialize A = 0 before scanning the identity stream.
                mstore(0x6cc0, 0)
                // Simple selectors are grouped into separate linearization
                // buckets. They start at zero for every proof.
                // q_sel_zero_off walks selector bucket byte offsets.
                for { let q_sel_zero_off := 0 } lt(q_sel_zero_off, 0x01c0) { q_sel_zero_off := add(q_sel_zero_off, 0x20) } {
                    // B_s = 0 for each simple selector bucket.
                    mstore(add(SELECTOR_ACC_MPTR, q_sel_zero_off), 0)
                }
                // Codegen knows the selector identity positions. Precompute
                // the y^k powers needed for selector gap and tail updates,
                // avoiding a runtime y^-1 modexp and per-identity selector
                // scale maintenance.
                {
                    // q_y_power holds y^i at the current loop index.
                    let q_y_power := 1
                    // Slot 0 holds y^0 = 1. Codegen never emits a read of it
                    // (FOLD_SELECTOR guards on a nonzero gap, and
                    // selector_tail_updates drops zero tails), but the tail
                    // block multiplies by mload(selector_power_mptr + offset)
                    // unconditionally -- so initialize the slot rather than
                    // leaving correctness to two filters in another file.
                    mstore(0x6d00, 1)
                    // Start at i=1 because y^0 = 1 is written above.
                    for { let q_y_power_i := 1 } lt(q_y_power_i, 35) { q_y_power_i := add(q_y_power_i, 1) } {
                        // Advance from y^(i-1) to y^i modulo Fr.
                        q_y_power := mulmod(q_y_power, y, r)
                        // Store y^i at selector_power_mptr + 32*i.
                        mstore(add(0x6d00, shl(5, q_y_power_i)), q_y_power)
                    }
                }

                // Direct inline prefix. These identities are generated as Yul
                // before entering the VM. They use the same fold snippets as
                // VM/native identities, so they occupy the same y-batch order.
                {
                let var0 := 0x1
                let f_3 := mload(0x5c40)
                let f_4 := mload(0x5b40)
                let a_0 := mload(0x5820)
                let var1 := mulmod(f_4, a_0, r)
                let var2 := addmod(f_3, var1, r)
                let f_5 := mload(0x5b60)
                let a_1 := mload(0x5840)
                let var3 := mulmod(f_5, a_1, r)
                let var4 := addmod(var2, var3, r)
                let f_6 := mload(0x5b80)
                let a_2 := mload(0x5860)
                let var5 := mulmod(f_6, a_2, r)
                let var6 := addmod(var4, var5, r)
                let f_7 := mload(0x5ba0)
                let a_3 := mload(0x5880)
                let var7 := mulmod(f_7, a_3, r)
                let var8 := addmod(var6, var7, r)
                let f_8 := mload(0x5bc0)
                let a_4 := mload(0x58a0)
                let var9 := mulmod(f_8, a_4, r)
                let var10 := addmod(var8, var9, r)
                let f_0 := mload(0x5be0)
                let a_0_next_1 := mload(0x58c0)
                let var11 := mulmod(f_0, a_0_next_1, r)
                let var12 := addmod(var10, var11, r)
                let f_1 := mload(0x5c00)
                let var13 := mulmod(f_1, a_0, r)
                let var14 := mulmod(var13, a_1, r)
                let var15 := addmod(var12, var14, r)
                let f_2 := mload(0x5c20)
                let var16 := mulmod(f_2, a_0, r)
                let var17 := mulmod(var16, a_2, r)
                let var18 := addmod(var15, var17, r)
                let var19 := mulmod(var0, var18, r)
                mstore(0x7160, var19)
                }
                mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x0)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x5840)
                let a_2 := mload(0x5860)
                let var1 := addmod(a_1, a_2, r)
                let a_3 := mload(0x5880)
                let var2 := addmod(0, sub(r, a_3), r)
                let var3 := addmod(var1, var2, r)
                let a_4 := mload(0x58a0)
                let var4 := addmod(0, sub(r, a_4), r)
                let var5 := addmod(var3, var4, r)
                let var6 := mulmod(var0, var5, r)
                mstore(0x7160, var6)
                }
                mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                }
                {
                let var0 := 0x1
                let a_0 := mload(0x5820)
                let f_4 := mload(0x5b40)
                let var1 := addmod(a_0, f_4, r)
                let a_0_next_1 := mload(0x58c0)
                let var2 := addmod(0, sub(r, a_0_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0x7160, var4)
                }
                mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x5840)
                let f_5 := mload(0x5b60)
                let var1 := addmod(a_1, f_5, r)
                let a_1_next_1 := mload(0x58e0)
                let var2 := addmod(0, sub(r, a_1_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0x7160, var4)
                }
                mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                q_selector_acc := mulmod(q_selector_acc, mload(add(0x6d00, 0x20)), r)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                }

                // VM registers:
                //   q_pc      current bytecode pointer
                //   q_end     end of bytecode stream
                //   q_sp      memory stack pointer for non-top stack values
                //   q_top     cached top-of-stack value
                //   q_has_top whether q_top currently holds a stack value
                //
                // The cached top reduces memory traffic in the interpreter.
                // q_sp's registered range must cover the interpreted operand
                // stack plus any native callback scratch that reuses this base
                // pointer. In particular, the native permutation callback
                // writes a structured scratch table at program.stack_mptr.
                // q_pc starts at the first encoded instruction.
                let q_pc := q_program_mptr
                // q_end is an exclusive byte pointer for the VM loop.
                let q_end := add(q_program_mptr, 0x019b)
                // q_sp starts at the first free stack word.
                let q_sp := 0x7160
                // q_top is meaningless until q_has_top is set.
                let q_top := 0
                // q_has_top = 0 means the VM stack is empty.
                let q_has_top := 0

                // q_program opcode summary:
                //   0x01/0x09 push const       0x02/0x05 push memory
                //   0x03/0x04 push token ptr   0x06 add, 0x07 mul, 0x08 neg
                //   0x0a fold main identity    0x0b fold selector identity
                //   0x0c..0x11 add/mul const or memory into top
                //   0x12..0x16 fused add-mul runs
                //   0x17/0x18 reserved
                //   0x19 native permutation    0x1b native heavy identity
                //   0x1c LIN7                 0x1d BILIN7_ROW
                //   0x1e BILIN7_PAIRWISE      0x1f native lookup
                //   0x20 POW5                 0x21 MODARITH7
                //   0x22 AFFINE_SUM
                //
                // The default IVC verifier uses one physical encoding for the
                // logical VM: compact byte-oriented opcodes with variable-width
                // operands, dynamic runs, and limb-aware cases.
                
                // Byte-oriented encoding: opcodes are one byte followed by
                // variable-width operand bytes.
                for { } lt(q_pc, q_end) { } {
                    // The bytecode table is byte-addressed, but EVM memory
                    // loads whole words. `byte(0, mload(q_pc))` extracts the
                    // opcode at the current byte cursor; each case advances
                    // q_pc by exactly its operand width.
                    let q_op := byte(0, mload(q_pc))
                    q_pc := add(q_pc, 1)

                    switch q_op
                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.
                    case 0x05 {
                        // Operand layout: u16 absolute memory pointer. The
                        // memory planner keeps the hot quotient frame below
                        // 64 KiB when this compact form is emitted.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    // VM 0x06 ADD: pop one spilled stack word and add it to q_top.
                    case 0x06 {
                        // The safety validator guarantees a spilled operand
                        // exists before ADD. q_top is the right operand.
                        q_sp := sub(q_sp, 0x20)
                        q_top := addmod(mload(q_sp), q_top, r)
                    }
                    // VM 0x08 NEG: replace q_top with its Fr negation.
                    case 0x08 {
                        // addmod(0, r - x, r) maps zero back to zero and every
                        // nonzero scalar to its canonical additive inverse.
                        q_top := addmod(0, sub(r, q_top), r)
                    }
                    // VM 0x09 PUSH_CONST_U8 (bytes): next byte is a constant-table slot.
                    case 0x09 {
                        // One-byte variant for the common case where the
                        // constant table has fewer than 256 referenced slots.
                        let qconst := byte(0, mload(q_pc))
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(add(q_const_mptr, shl(5, qconst)))
                        q_has_top := 1
                        q_pc := add(q_pc, 1)
                    }
                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.
                    case 0x0d {
                        // One-byte constant-index multiply, used by short
                        // affine chains after an initial PUSH.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.
                    case 0x10 {
                        // Operand layout: u16 pointer. The pointed word is an
                        // already range-checked Fr scalar in verifier memory.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := addmod(q_top, mload(q_ptr), r)
                    }
                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.
                    case 0x11 {
                        // In-place multiply by a planned memory word.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := mulmod(q_top, mload(q_ptr), r)
                    }
                    // VM 0x13 ADD_MUL_CONST_U8_MEM_U16: fused q_top += mem * const.
                    case 0x13 {
                        // Operand layout: u16 ptr, u8 const_idx.
                        let q_word := mload(q_pc)
                        let q_ptr := shr(240, q_word)
                        let qconst := byte(2, q_word)
                        q_pc := add(q_pc, 3)
                        q_top := addmod(
                            q_top,
                            mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                            r
                        )
                    }
                    // Limb-aware opcodes are opt-in compact forms for
                    // structurally recognized non-SHA foreign-field shapes.
                    // Coefficients are indexes into q_const_mptr, which is
                    // generated from VK/program data, never from proof
                    // calldata.
                    //
                    // Rust source shape:
                    //   proofs/src/plonk/mod.rs::partially_evaluate_identities
                    //   circuits/src/field/foreign/util.rs::{sum_exprs,pair_wise_prod}
                    //   circuits/src/field/foreign/params.rs::{base_powers,double_base_powers}
                    //
                    // "Foreign field" means the circuit represents elements
                    // modulo another modulus m as 7 limbs in base
                    // 2^LOG2_BASE. The verifier does not switch fields; it
                    // evaluates the lowered identity over BLS12-381 Fr, using
                    // Fr coefficients equal to base^i mod m or base^(i+j) mod m.
                    // VM 0x1c LIN7: byte-only 7-term foreign-field linear form.
                    case 0x1c {
                        // LIN7: sum_i coeff[i] * value[i] over Fr.
                        // Typical Rust origin: foreign/gates/norm.rs
                        // normalization and foreign/gates/mul.rs base-power
                        // sums for x/y/z limbs.
                        //
                        // Operand layout: seven repeated {u8 const_idx,
                        // u16 ptr} pairs. The result is pushed as a fresh
                        // stack value.
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        // Accumulate exactly seven limbs, matching the
                        // generated foreign-field limb width.
                        for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_ptr := and(shr(232, q_word), 0xffff)
                            q_pc := add(q_pc, 3)
                            q_acc := addmod(
                                q_acc,
                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                r
                            )
                        }
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // VM 0x21 MODARITH7: byte-only fused affine 7-limb foreign-field/ECC identity.
                    case 0x21 {
                        // MODARITH7:
                        //   maybe_cond * (
                        //       c
                        //     + sum LIN7 blocks
                        //     + sum BILIN7_ROW blocks
                        //     + sum BILIN7_PAIRWISE blocks
                        //     + sum coeff[k] * mload(ptr[k])
                        //     + sum coeff[k] * mload(lhs[k]) * mload(rhs[k])
                        //   )
                        // It is a dispatch/operand-load optimization only;
                        // all coefficients still come from the generated
                        // quotient constant table.
                        //
                        // Flags:
                        //   bit 0: multiply the final affine sum by a memory
                        //          condition word.
                        //   bit 1: seed q_acc from a constant-table word
                        //          before reading the counted term blocks.
                        let q_flags := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        let q_cond_ptr := 0
                        if and(q_flags, 0x01) {
                            // Optional condition pointer. When present, the
                            // whole identity is gated by mload(q_cond_ptr).
                            q_cond_ptr := shr(240, mload(q_pc))
                            q_pc := add(q_pc, 2)
                        }

                        let q_acc := 0
                        if and(q_flags, 0x02) {
                            // Optional constant seed for affine identities
                            // with a standalone constant term.
                            let qconst := byte(0, mload(q_pc))
                            q_pc := add(q_pc, 1)
                            q_acc := mload(add(q_const_mptr, shl(5, qconst)))
                        }

                        // Five one-byte counters describe the blocks that
                        // follow. Each block has a fixed-width internal layout,
                        // so q_pc can advance without per-term tags.
                        let q_counts_word := mload(q_pc)
                        let q_lin_count := byte(0, q_counts_word)
                        let q_row_count := byte(1, q_counts_word)
                        let q_pairwise_count := byte(2, q_counts_word)
                        let q_mem_count := byte(3, q_counts_word)
                        let q_product_count := byte(4, q_counts_word)
                        q_pc := add(q_pc, 5)

                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }

                        // LIN7 blocks: q_acc += sum_i c_i * limb_i.
                        for { let q_lin_block := 0 } lt(q_lin_block, q_lin_count) { q_lin_block := add(q_lin_block, 1) } {
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_word := mload(q_pc)
                                let qconst := byte(0, q_word)
                                let q_ptr := and(shr(232, q_word), 0xffff)
                                q_pc := add(q_pc, 3)
                                q_acc := addmod(
                                    q_acc,
                                    mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                    r
                                )
                            }
                        }

                        // BILIN7_ROW blocks: q_acc += lhs * sum_i c_i * rhs_i.
                        for { let q_row_block := 0 } lt(q_row_block, q_row_count) { q_row_block := add(q_row_block, 1) } {
                            let q_lhs := shr(240, mload(q_pc))
                            q_pc := add(q_pc, 2)
                            let q_lhs_value := mload(q_lhs)
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_word := mload(q_pc)
                                let qconst := byte(0, q_word)
                                let q_rhs := and(shr(232, q_word), 0xffff)
                                q_pc := add(q_pc, 3)
                                q_acc := addmod(
                                    q_acc,
                                    mulmod(
                                        mulmod(q_lhs_value, mload(q_rhs), r),
                                        mload(add(q_const_mptr, shl(5, qconst))),
                                        r
                                    ),
                                    r
                                )
                            }
                        }

                        // BILIN7_PAIRWISE blocks: q_acc += weighted 7-by-7
                        // product convolution.
                        for { let q_pair_block := 0 } lt(q_pair_block, q_pairwise_count) { q_pair_block := add(q_pair_block, 1) } {
                            let q_pair_word := mload(q_pc)
                            let q_lhs_base := shr(240, q_pair_word)
                            let q_rhs_base := and(shr(224, q_pair_word), 0xffff)
                            q_pc := add(q_pc, 0x04)
                            let q_coeff_pc := q_pc
                            q_pc := add(q_pc, 13)
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))
                                for { let q_j := 0 } lt(q_j, 7) { q_j := add(q_j, 1) } {
                                    let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))
                                    q_acc := addmod(
                                        q_acc,
                                        mulmod(
                                            mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),
                                            mload(add(q_const_mptr, shl(5, qconst))),
                                            r
                                        ),
                                        r
                                    )
                                }
                            }
                        }

                        // Extra linear memory terms outside the 7-limb shapes.
                        for { let q_mem_block := 0 } lt(q_mem_block, q_mem_count) { q_mem_block := add(q_mem_block, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_ptr := and(shr(232, q_word), 0xffff)
                            q_pc := add(q_pc, 3)
                            q_acc := addmod(
                                q_acc,
                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                r
                            )
                        }

                        // Extra binary product terms outside the 7-limb shapes.
                        for { let q_product_block := 0 } lt(q_product_block, q_product_count) { q_product_block := add(q_product_block, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_lhs := and(shr(232, q_word), 0xffff)
                            let q_rhs := and(shr(216, q_word), 0xffff)
                            q_pc := add(q_pc, 5)
                            q_acc := addmod(
                                q_acc,
                                mulmod(
                                    mulmod(mload(q_lhs), mload(q_rhs), r),
                                    mload(add(q_const_mptr, shl(5, qconst))),
                                    r
                                ),
                                r
                            )
                        }

                        if and(q_flags, 0x01) {
                            // Apply the optional gate condition last so every
                            // subterm shares the same selector/condition.
                            q_acc := mulmod(mload(q_cond_ptr), q_acc, r)
                        }
                        // MODARITH7 pushes its fused identity value.
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // Native permutation callback. It evaluates the
                    // permutation identities from permutation.rs at this exact
                    // VM position, preserving the Rust identity order while
                    // avoiding a large interpreted product loop.
                    // VM 0x19 NATIVE_PERMUTATION: marker for the generated permutation callback.
                    case 0x19 {
                        // Native callbacks are identity-boundary opcodes. They
                        // must not inherit any partially evaluated VM stack
                        // state from the previous expression.
                        q_top := 0
                        q_has_top := 0
                        // The generated loop below uses program.stack_mptr as
                        // its scratch-table base, not as a conventional VM
                        // stack. The Rust memory planner must reserve enough
                        // words for structured_permutation_scratch_words(meta)
                        // whenever this opcode can appear.
                        q_sp := 0x7160
                        // The generated lines below call the same fold snippets
                        // used by interpreted expressions, so trace IDs and
                        // y-batch positions remain contiguous.
                        {
                        let delta := 0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
                        let q_perm_vals := 0x7160
                        let q_perm_sigmas := 0x7280
                        let q_perm_z_cur := 0x73a0
                        let q_perm_z_next := 0x7400
                        let q_perm_z_last := 0x7460
                        let q_perm_delta_base_ptr := 0x74a0
                        let q_perm_num_cols := 9
                        let q_perm_num_sets := 3
                        let q_perm_chunk_len := 3
                        let q_perm_delta_chunk := 0x4285088329c399ea457a8ca1d30f8957e74c7f529842a1579b4fee55b3982923
                        mstore(add(q_perm_vals, 0x0), mload(0x5b20))
                        {
                        for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 5) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {
                        let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)
                        let q_perm_val_load_src_off := q_perm_val_load_dst_off
                        mstore(add(add(q_perm_vals, 0x20), q_perm_val_load_dst_off), mload(add(0x5820, q_perm_val_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_vals, 0xc0), mload(0x5800))
                        mstore(add(q_perm_vals, 0xe0), mload(INSTANCE_EVAL_MPTR))
                        mstore(add(q_perm_vals, 0x100), mload(0x5920))
                        {
                        for { let q_perm_sigma_load_i := 0 } lt(q_perm_sigma_load_i, 9) { q_perm_sigma_load_i := add(q_perm_sigma_load_i, 1) } {
                        let q_perm_sigma_load_dst_off := shl(5, q_perm_sigma_load_i)
                        let q_perm_sigma_load_src_off := q_perm_sigma_load_dst_off
                        mstore(add(add(q_perm_sigmas, 0x0), q_perm_sigma_load_dst_off), mload(add(0x5d60, q_perm_sigma_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_cur_load_i := 0 } lt(q_perm_z_cur_load_i, 3) { q_perm_z_cur_load_i := add(q_perm_z_cur_load_i, 1) } {
                        let q_perm_z_cur_load_dst_off := shl(5, q_perm_z_cur_load_i)
                        let q_perm_z_cur_load_src_off := mul(q_perm_z_cur_load_i, 0x60)
                        mstore(add(add(q_perm_z_cur, 0x0), q_perm_z_cur_load_dst_off), mload(add(0x5e80, q_perm_z_cur_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_next_load_i := 0 } lt(q_perm_z_next_load_i, 3) { q_perm_z_next_load_i := add(q_perm_z_next_load_i, 1) } {
                        let q_perm_z_next_load_dst_off := shl(5, q_perm_z_next_load_i)
                        let q_perm_z_next_load_src_off := mul(q_perm_z_next_load_i, 0x60)
                        mstore(add(add(q_perm_z_next, 0x0), q_perm_z_next_load_dst_off), mload(add(0x5ea0, q_perm_z_next_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_z_last, 0x0), mload(0x5ec0))
                        mstore(add(q_perm_z_last, 0x20), mload(0x5f20))
                        let q_perm_eval := 0
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_perm_eval, r))
                        let q_perm_zn := mload(add(q_perm_z_cur, 0x40))
                        q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_perm_eval, r))
                        for { let q_perm_i := 1 } lt(q_perm_i, 3) { q_perm_i := add(q_perm_i, 1) } {
                        let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))
                        let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_perm_eval, r))
                        }
                        mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))
                        for { let q_perm_set := 0 } lt(q_perm_set, 3) { q_perm_set := add(q_perm_set, 1) } {
                        let q_perm_start := mul(q_perm_set, q_perm_chunk_len)
                        let q_perm_end := add(q_perm_start, q_perm_chunk_len)
                        if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }
                        let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))
                        let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))
                        let q_perm_delta_pow := mload(q_perm_delta_base_ptr)
                        for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {
                        let q_perm_off := shl(5, q_perm_j)
                        let q_perm_v := mload(add(q_perm_vals, q_perm_off))
                        let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))
                        q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)
                        q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)
                        q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)
                        }
                        q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_perm_eval, r))
                        mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))
                        }
                        }
                    }
                    // Native lookup callback. This whole-family opcode
                    // evaluates the LogUp boundary, helper-chunk, and
                    // accumulator identities at this VM position, preserving
                    // the Rust y-batch order while avoiding many interpreted
                    // product-loop opcodes.
                    // VM 0x1f NATIVE_LOOKUP: marker for the generated LogUp lookup callback.
                    case 0x1f {
                        // Reset VM stack state before entering structured
                        // lookup Yul. Lookup callbacks own their scratch
                        // layout and perform all needed folds internally.
                        q_top := 0
                        q_has_top := 0
                        // The generated loop below uses program.stack_mptr as
                        // f+beta/prefix/suffix scratch rather than as a
                        // conventional VM stack. The Rust memory planner must
                        // reserve structured_lookup_scratch_words(meta).
                        q_sp := 0x7160
                        // Generated LogUp code follows the same y-batch order
                        // as the Rust identity stream.
                        {
                        let q_lookup_f := 0x7160
                        let q_lookup_prefix := 0x71a0
                        let q_lookup_suffix := 0x71e0
                        let q_lookup_l0 := mload(L_0_MPTR)
                        let q_lookup_llast := mload(L_LAST_MPTR)
                        let q_lookup_lblind := mload(L_BLIND_MPTR)
                        let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)
                        let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)
                        let q_lookup_beta := mload(BETA_MPTR)
                        let q_lookup_theta := mload(THETA_MPTR)
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x5fc0), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        {
                        let f_10 := mload(0x5c60)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_10, r)
                        let a_1 := mload(0x5840)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), a_1, r)
                        let q_lookup_eval := addmod(mulmod(mload(0x5fa0), addmod(var1, q_lookup_beta, r), r), sub(r, 1), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0x5fa0)
                        let f_19 := mload(0x5d20)
                        let f_11 := mload(0x5c80)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_11, r)
                        let f_12 := mload(0x5ca0)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), f_12, r)
                        let q_lookup_s_sum_h := mulmod(f_19, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0x5fe0), sub(r, addmod(mload(0x5fc0), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var1, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x5f80), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        }
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x6040), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        {
                        let f_0 := mload(0x5be0)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_0, r)
                        let a_6 := mload(0x5940)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), a_6, r)
                        let a_0 := mload(0x5820)
                        let var2 := addmod(mulmod(var1, q_lookup_theta, r), a_0, r)
                        mstore(add(q_lookup_f, 0x0), addmod(var2, q_lookup_beta, r))
                        let f_1 := mload(0x5c00)
                        let var3 := addmod(mulmod(0, q_lookup_theta, r), f_1, r)
                        let a_7 := mload(0x5960)
                        let var4 := addmod(mulmod(var3, q_lookup_theta, r), a_7, r)
                        let a_1 := mload(0x5840)
                        let var5 := addmod(mulmod(var4, q_lookup_theta, r), a_1, r)
                        mstore(add(q_lookup_f, 0x20), addmod(var5, q_lookup_beta, r))
                        let q_lookup_product := 1
                        for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, 2) { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {
                        q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)
                        }
                        mstore(q_lookup_prefix, 1)
                        for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, 2) { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {
                        let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)
                        mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))
                        }
                        mstore(add(q_lookup_suffix, 0x20), 1)
                        for { let q_lookup_suf_i := sub(2, 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {
                        let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)
                        mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))
                        }
                        let q_lookup_sum := 0
                        for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, 2) { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {
                        q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)
                        }
                        let q_lookup_eval := addmod(mulmod(mload(0x6020), q_lookup_product, r), sub(r, q_lookup_sum), r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0x6020)
                        let f_20 := mload(0x5d40)
                        let f_13 := mload(0x5cc0)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_13, r)
                        let f_14 := mload(0x5ce0)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), f_14, r)
                        let f_15 := mload(0x5d00)
                        let var2 := addmod(mulmod(var1, q_lookup_theta, r), f_15, r)
                        let q_lookup_s_sum_h := mulmod(f_20, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0x6060), sub(r, addmod(mload(0x6040), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var2, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x6000), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        mstore(0x6cc0, addmod(mload(0x6cc0), q_lookup_eval, r))
                        }
                        }
                        }
                    }
                    // Native callbacks are generated only for the heaviest
                    // recognized Midfall gate identities. All other gate and
                    // non-native identity arithmetic remains in
                    // the compact q_program VM above, preserving the Rust
                    // `partially_evaluate_identities` order.
                    // VM 0x1b NATIVE_IDENTITY: marker for generated heavy-gate callbacks.
                    case 0x1b {
                        // Operand layout: u16 native callback index. The
                        // manifest validates that callback indexes appear in
                        // generated order and target existing switch cases.
                        let q_native_idx := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        // Heavy identities are whole expressions, so clear the
                        // interpreter stack before dispatching.
                        q_top := 0
                        q_has_top := 0
                        q_sp := 0x7160
                        // Native identity sub-cases are generated from selected heavy gate identities.
                        switch q_native_idx
                        case 0 {
                            {
                            let var0 := 0x1
                            let a_3_prev_1 := mload(0x5980)
                            let a_4_prev_1 := mload(0x59a0)
                            let var1 := addmod(a_3_prev_1, a_4_prev_1, r)
                            let a_3 := mload(0x5880)
                            let var2 := addmod(var1, a_3, r)
                            let var3 := 0x40000000000
                            let a_1_prev_1 := mload(0x59e0)
                            let var4 := mulmod(var3, a_1_prev_1, r)
                            let var5 := 0x100000
                            let a_1 := mload(0x5840)
                            let var6 := mulmod(var5, a_1, r)
                            let var7 := addmod(var4, var6, r)
                            let a_1_next_1 := mload(0x58e0)
                            let var8 := addmod(var7, a_1_next_1, r)
                            let var9 := 0x2
                            let a_0_prev_1 := mload(0x59c0)
                            let var10 := mulmod(var3, a_0_prev_1, r)
                            let a_0 := mload(0x5820)
                            let var11 := mulmod(var5, a_0, r)
                            let var12 := addmod(var10, var11, r)
                            let a_0_next_1 := mload(0x58c0)
                            let var13 := addmod(var12, a_0_next_1, r)
                            let var14 := mulmod(var9, var13, r)
                            let var15 := addmod(var8, var14, r)
                            let var16 := addmod(0, sub(r, var15), r)
                            let var17 := addmod(var2, var16, r)
                            let var18 := mulmod(var0, var17, r)
                            mstore(0x7160, var18)
                            }
                            mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                            }
                        }
                        case 1 {
                            {
                            let var0 := 0x1
                            let a_3_prev_1 := mload(0x5980)
                            let a_4_prev_1 := mload(0x59a0)
                            let var1 := addmod(a_3_prev_1, a_4_prev_1, r)
                            let var2 := 0x40000000000
                            let a_1_prev_1 := mload(0x59e0)
                            let var3 := mulmod(var2, a_1_prev_1, r)
                            let var4 := 0x100000
                            let a_1 := mload(0x5840)
                            let var5 := mulmod(var4, a_1, r)
                            let var6 := addmod(var3, var5, r)
                            let a_1_next_1 := mload(0x58e0)
                            let var7 := addmod(var6, a_1_next_1, r)
                            let var8 := 0x2
                            let a_0_prev_1 := mload(0x59c0)
                            let var9 := mulmod(var2, a_0_prev_1, r)
                            let a_0 := mload(0x5820)
                            let var10 := mulmod(var4, a_0, r)
                            let var11 := addmod(var9, var10, r)
                            let a_0_next_1 := mload(0x58c0)
                            let var12 := addmod(var11, a_0_next_1, r)
                            let var13 := mulmod(var8, var12, r)
                            let var14 := addmod(var7, var13, r)
                            let var15 := addmod(0, sub(r, var14), r)
                            let var16 := addmod(var1, var15, r)
                            let var17 := mulmod(var0, var16, r)
                            mstore(0x7160, var17)
                            }
                            mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                            }
                        }
                        case 2 {
                            {
                            let var0 := 0x1
                            let var1 := 0x1000000000000000
                            let a_4 := mload(0x58a0)
                            let var2 := mulmod(var1, a_4, r)
                            let var3 := 0x10000000000
                            let a_3_prev_1 := mload(0x5980)
                            let var4 := mulmod(var3, a_3_prev_1, r)
                            let var5 := addmod(var2, var4, r)
                            let var6 := 0x400000
                            let a_4_prev_1 := mload(0x59a0)
                            let var7 := mulmod(var6, a_4_prev_1, r)
                            let var8 := addmod(var5, var7, r)
                            let a_3 := mload(0x5880)
                            let var9 := addmod(var8, a_3, r)
                            let var10 := 0x40000000000
                            let var11 := mulmod(var10, a_3, r)
                            let var12 := 0x4000000000
                            let var13 := mulmod(var12, a_4, r)
                            let var14 := addmod(var11, var13, r)
                            let var15 := 0x40000
                            let var16 := mulmod(var15, a_3_prev_1, r)
                            let var17 := addmod(var14, var16, r)
                            let var18 := addmod(var17, a_4_prev_1, r)
                            let var19 := addmod(var9, var18, r)
                            let var20 := 0x400000000000
                            let var21 := mulmod(var20, a_4_prev_1, r)
                            let var22 := 0x1000000
                            let var23 := mulmod(var22, a_3, r)
                            let var24 := addmod(var21, var23, r)
                            let var25 := 0x100000
                            let var26 := mulmod(var25, a_4, r)
                            let var27 := addmod(var24, var26, r)
                            let var28 := addmod(var27, a_3_prev_1, r)
                            let var29 := addmod(var19, var28, r)
                            let a_0_prev_1 := mload(0x59c0)
                            let var30 := mulmod(var10, a_0_prev_1, r)
                            let a_0 := mload(0x5820)
                            let var31 := mulmod(var25, a_0, r)
                            let var32 := addmod(var30, var31, r)
                            let a_0_next_1 := mload(0x58c0)
                            let var33 := addmod(var32, a_0_next_1, r)
                            let var34 := 0x2
                            let a_1_prev_1 := mload(0x59e0)
                            let var35 := mulmod(var10, a_1_prev_1, r)
                            let a_1 := mload(0x5840)
                            let var36 := mulmod(var25, a_1, r)
                            let var37 := addmod(var35, var36, r)
                            let a_1_next_1 := mload(0x58e0)
                            let var38 := addmod(var37, a_1_next_1, r)
                            let var39 := mulmod(var34, var38, r)
                            let var40 := addmod(var33, var39, r)
                            let var41 := addmod(0, sub(r, var40), r)
                            let var42 := addmod(var29, var41, r)
                            let var43 := mulmod(var0, var42, r)
                            mstore(0x7160, var43)
                            }
                            mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0xa0)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                            }
                        }
                        case 3 {
                            {
                            let var0 := 0x1
                            let var1 := 0x10000000000000
                            let a_3_next_1 := mload(0x5a00)
                            let var2 := mulmod(var1, a_3_next_1, r)
                            let var3 := 0x4000000000
                            let a_3_prev_1 := mload(0x5980)
                            let var4 := mulmod(var3, a_3_prev_1, r)
                            let var5 := addmod(var2, var4, r)
                            let var6 := 0x4000
                            let a_4_prev_1 := mload(0x59a0)
                            let var7 := mulmod(var6, a_4_prev_1, r)
                            let var8 := addmod(var5, var7, r)
                            let var9 := 0x400
                            let a_3 := mload(0x5880)
                            let var10 := mulmod(var9, a_3, r)
                            let var11 := addmod(var8, var10, r)
                            let a_4 := mload(0x58a0)
                            let var12 := addmod(var11, a_4, r)
                            let var13 := 0x40000000000000
                            let var14 := mulmod(var13, a_4, r)
                            let var15 := 0x40000000000
                            let var16 := mulmod(var15, a_3_next_1, r)
                            let var17 := addmod(var14, var16, r)
                            let var18 := 0x10000000
                            let var19 := mulmod(var18, a_3_prev_1, r)
                            let var20 := addmod(var17, var19, r)
                            let var21 := 0x10
                            let var22 := mulmod(var21, a_4_prev_1, r)
                            let var23 := addmod(var20, var22, r)
                            let var24 := addmod(var23, a_3, r)
                            let var25 := addmod(var12, var24, r)
                            let var26 := 0x10000000000
                            let var27 := mulmod(var26, a_4_prev_1, r)
                            let var28 := 0x1000000000
                            let var29 := mulmod(var28, a_3, r)
                            let var30 := addmod(var27, var29, r)
                            let var31 := 0x4000000
                            let var32 := mulmod(var31, a_4, r)
                            let var33 := addmod(var30, var32, r)
                            let var34 := mulmod(var6, a_3_next_1, r)
                            let var35 := addmod(var33, var34, r)
                            let var36 := addmod(var35, a_3_prev_1, r)
                            let var37 := addmod(var25, var36, r)
                            let a_0_prev_1 := mload(0x59c0)
                            let var38 := mulmod(var15, a_0_prev_1, r)
                            let var39 := 0x100000
                            let a_0 := mload(0x5820)
                            let var40 := mulmod(var39, a_0, r)
                            let var41 := addmod(var38, var40, r)
                            let a_0_next_1 := mload(0x58c0)
                            let var42 := addmod(var41, a_0_next_1, r)
                            let var43 := 0x2
                            let a_1_prev_1 := mload(0x59e0)
                            let var44 := mulmod(var15, a_1_prev_1, r)
                            let a_1 := mload(0x5840)
                            let var45 := mulmod(var39, a_1, r)
                            let var46 := addmod(var44, var45, r)
                            let a_1_next_1 := mload(0x58e0)
                            let var47 := addmod(var46, a_1_next_1, r)
                            let var48 := mulmod(var43, var47, r)
                            let var49 := addmod(var42, var48, r)
                            let var50 := addmod(0, sub(r, var49), r)
                            let var51 := addmod(var37, var50, r)
                            let var52 := mulmod(var0, var51, r)
                            mstore(0x7160, var52)
                            }
                            mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0xc0)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0x7160), r))
                            }
                        }
                        default { revert(0, 0) }
                    }
                    // VM 0x0b FOLD_SELECTOR: consume q_top into one simple-selector bucket.
                    case 0x0b {
                        // Operand layout packed into three bytes:
                        //   high byte: selector bucket index;
                        //   low u16 : y-power gap since this selector's
                        //             previous contribution.
                        let q_selector_payload := shr(232, mload(q_pc))
                        q_pc := add(q_pc, 3)
                        let q_sel_idx := shr(16, q_selector_payload)
                        let q_sel_gap := and(q_selector_payload, 0xffff)
                        let q_eval := q_top
                        q_has_top := 0
                        // Simple-selector identity: keep the same y-batch
                        // position as main identities, then advance only this
                        // selector bucket by its codegen-known gap.
                        //
                        // The global fully-evaluated accumulator is still
                        // multiplied by y so later main identities land at the
                        // same y powers as Rust's reverse fold.
                        mstore(0x6cc0, mulmod(mload(0x6cc0), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add(0x6d00, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
                    }
                    // Invalid generated bytecode should fail closed. 0x1a intentionally lands here.
                    default {
                        revert(0, 0)
                    }
                }
                // The VK-pinned bytecode must end exactly at q_end and every
                // identity must have been consumed by a fold/native callback.
                // This catches malformed generator output whose final opcode
                // over-reads operands or leaves a partial expression live.
                if iszero(eq(q_pc, q_end)) { revert(0, 0) }
                if q_has_top { revert(0, 0) }
                // The spilled stack must also be balanced. A FOLD executed
                // with more than one operand live consumes only the cached
                // top, leaving abandoned words below q_sp with q_has_top
                // clear -- so both checks above pass while an operand of the
                // identity has been silently dropped from nu_y(x).
                if iszero(eq(q_sp, 0x7160)) { revert(0, 0) }

                // Structured post-VM suffix. The current default uses this for
                // regular trash constraints: it is smaller than fully unrolled
                // Yul and cheaper than interpreting every trash operation.
                //
                // These generated blocks run after q_pc reaches q_end, but
                // they still participate in the same identity order and write
                // into the same numerator / selector accumulators.
                // Finish selector buckets by applying the codegen-known tail
                // from each selector's last identity to the end of the global
                // y-batch.
                //
                // After this step, every selector bucket is aligned with the
                // final global y position and can be multiplied by its fixed
                // selector commitment in the linearized MSM.
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x00)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0440)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0420)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x03c0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x03a0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0360)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xa0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0340)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xc0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0320)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xe0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0300)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0100)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x02e0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0120)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x02c0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0140)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0280)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0160)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x0240)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0180)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x01c0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x01a0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0x6d00, 0x01a0)), r))
                }

                // Fully evaluated identities are the constant-polynomial side
                // of the linearization query. Rust subtracts that grouped
                // scalar into expected_eval, so Solidity stores -nu_y(x).
                let linearization_expected_eval := addmod(0, sub(r, mload(0x6cc0)), r)
                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)
                pop(y)
            }

            // ===============================================================
            // Prepare linearization scalars for the final PCS MSM.
            //
            // The linearized commitment is
            //   (1 - x^n) * Σ_i x_split^i * Q_i
            // + Σ_j sel_acc_j * S_j_com,
            // where x_split = x^(n-1). Instead of materializing that point
            // with a standalone G1MSM here, PCS block 5 expands the
            // linearized commitment into its quotient and selector
            // pairs inside the already-fused final MSM.
            //
            // QUOTIENT_MPTR is no longer a G1 point in this path. Its first
            // two words carry:
            //   word 0: x_split
            //   word 1: one_minus_x_n
            // ===============================================================
            {
                let x := mload(X_MPTR)
                let k := 13
                // Compute both x^n and x^(n-1) with the same squaring walk:
                // x_pow_2i tracks x^(2^i), while x_pow_2i_minus1 tracks
                // x^(2^i - 1).
                let x_pow_2i := x
                let x_pow_2i_minus1 := 1
                for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
                    x_pow_2i_minus1 := mulmod(
                        mulmod(x_pow_2i_minus1, x_pow_2i_minus1, r),
                        x,
                        r
                    )
                    x_pow_2i := mulmod(x_pow_2i, x_pow_2i, r)
                }
                let x_split := x_pow_2i_minus1
                let one_minus_x_n := addmod(1, sub(r, x_pow_2i), r)

                // PCS block 5 interprets this 2-word payload as scalar
                // metadata, not as a materialized G1 point.
                mstore(QUOTIENT_MPTR, x_split)
                mstore(add(QUOTIENT_MPTR, 0x20), one_minus_x_n)
            }

                // ===============================================================
            // PCS computation (multi-prepare emitter from Step 5).
            //
            // The Rust lowering stage has already expanded the KZG multi-open
            // equation into a sequence of generated Yul sub-blocks. Those
            // blocks populate:
            //   - F_EVAL_MPTR / V_MPTR scalar batching values;
            //   - FINAL_COM_MPTR for the fused commitment MSM;
            //   - PAIRING_LHS_MPTR and PAIRING_RHS_MPTR for the final pairing.
            // ===============================================================
            {
                // Generated PCS sub-block 1. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // 4 distinct rotation(s)
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := x
                    mstore(add(ROT_POINTS_MPTR, 0x40), x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega, r)
                    mstore(add(ROT_POINTS_MPTR, 0x60), x_pow_of_omega)
                    x_pow_of_omega := x
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(add(ROT_POINTS_MPTR, 0x20), x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(add(ROT_POINTS_MPTR, 0x0), x_pow_of_omega)
                }
                // Generated PCS sub-block 2. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // pre-compute 33 x1 power(s)
                    let x1 := mload(X1_MPTR)
                    mstore(X1_POWERS_MPTR, 1)
                    let acc := 1
                    let p := X1_POWERS_MPTR
                    for { let i := 0 } lt(i, 0x20) { i := add(i, 1) } {
                        p := add(p, 0x20)
                        acc := mulmod(acc, x1, r)
                        mstore(p, and(acc, 0xffffffffffffffffffffffffffffffff))
                    }
                }
                // Generated PCS sub-block 3. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[0]: 33 commitment(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0x6cc0, 0x5800)
                    mstore(0x6ce0, 0x5f80)
                    mstore(0x6d00, 0x5fa0)
                    mstore(0x6d20, 0x6000)
                    mstore(0x6d40, 0x6020)
                    mstore(0x6d60, 0x5b20)
                    mstore(0x6d80, 0x5b40)
                    mstore(0x6da0, 0x5b60)
                    mstore(0x6dc0, 0x5b80)
                    mstore(0x6de0, 0x5ba0)
                    mstore(0x6e00, 0x5bc0)
                    mstore(0x6e20, 0x5be0)
                    mstore(0x6e40, 0x5c00)
                    mstore(0x6e60, 0x5c20)
                    mstore(0x6e80, 0x5c40)
                    mstore(0x6ea0, 0x5c60)
                    mstore(0x6ec0, 0x5c80)
                    mstore(0x6ee0, 0x5ca0)
                    mstore(0x6f00, 0x5cc0)
                    mstore(0x6f20, 0x5ce0)
                    mstore(0x6f40, 0x5d00)
                    mstore(0x6f60, 0x5d20)
                    mstore(0x6f80, 0x5d40)
                    mstore(0x6fa0, 0x5d60)
                    mstore(0x6fc0, 0x5d80)
                    mstore(0x6fe0, 0x5da0)
                    mstore(0x7000, 0x5dc0)
                    mstore(0x7020, 0x5de0)
                    mstore(0x7040, 0x5e00)
                    mstore(0x7060, 0x5e20)
                    mstore(0x7080, 0x5e40)
                    mstore(0x70a0, 0x5e60)
                    mstore(0x70c0, QUOTIENT_EVAL_MPTR)
                    let q_eval_set_0 := mload(0x5800)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0x6cc0, 0x20)
                    for { let i := 1 } lt(i, 0x21) { i := add(i, 1) } {
                        let pow := mload(pow_p)
                        q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)
                        pow_p := add(pow_p, 0x20)
                        eval_p := add(eval_p, 0x20)
                    }
                    mstore(add(Q_EVAL_SET_MPTR, 0x0), q_eval_set_0)
                }
                // Generated PCS sub-block 4. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[1]: 3 commitment(s)
                    let q_eval_set_0 := mload(0x5f40)
                    let q_eval_set_1 := mload(0x5f60)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x5fc0), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x5fe0), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x6040), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x6060), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0x20), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x40), q_eval_set_1)
                }
                // Generated PCS sub-block 5. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[2]: 8 commitment(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0x6cc0, 0x5820)
                    mstore(0x6ce0, 0x58c0)
                    mstore(0x6d00, 0x59c0)
                    mstore(0x6d20, 0x5840)
                    mstore(0x6d40, 0x58e0)
                    mstore(0x6d60, 0x59e0)
                    mstore(0x6d80, 0x5860)
                    mstore(0x6da0, 0x5900)
                    mstore(0x6dc0, 0x5a80)
                    mstore(0x6de0, 0x5880)
                    mstore(0x6e00, 0x5a00)
                    mstore(0x6e20, 0x5980)
                    mstore(0x6e40, 0x58a0)
                    mstore(0x6e60, 0x5a20)
                    mstore(0x6e80, 0x59a0)
                    mstore(0x6ea0, 0x5920)
                    mstore(0x6ec0, 0x5ae0)
                    mstore(0x6ee0, 0x5ac0)
                    mstore(0x6f00, 0x5940)
                    mstore(0x6f20, 0x5a60)
                    mstore(0x6f40, 0x5a40)
                    mstore(0x6f60, 0x5960)
                    mstore(0x6f80, 0x5b00)
                    mstore(0x6fa0, 0x5aa0)
                    let q_eval_set_0 := mload(0x5820)
                    let q_eval_set_1 := mload(0x58c0)
                    let q_eval_set_2 := mload(0x59c0)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0x6cc0, 0x60)
                    for { let i := 1 } lt(i, 0x8) { i := add(i, 1) } {
                        let pow := mload(pow_p)
                        q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)
                        q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(mload(add(eval_p, 0x20))), pow, r), r)
                        q_eval_set_2 := addmod(q_eval_set_2, mulmod(mload(mload(add(eval_p, 0x40))), pow, r), r)
                        pow_p := add(pow_p, 0x20)
                        eval_p := add(eval_p, 0x60)
                    }
                    mstore(add(Q_EVAL_SET_MPTR, 0x60), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x80), q_eval_set_1)
                    mstore(add(Q_EVAL_SET_MPTR, 0xa0), q_eval_set_2)
                }
                // Generated PCS sub-block 6. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[3]: 2 commitment(s)
                    let q_eval_set_0 := mload(0x5e80)
                    let q_eval_set_1 := mload(0x5ea0)
                    let q_eval_set_2 := mload(0x5ec0)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x5ee0), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x5f00), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_2 := addmod(q_eval_set_2, mulmod(mload(0x5f20), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0xc0), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0xe0), q_eval_set_1)
                    mstore(add(Q_EVAL_SET_MPTR, 0x100), q_eval_set_2)
                }
                // Generated PCS sub-block 7. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // f_eval via Horner over 4 reversed set(s)
                    let x2 := mload(X2_MPTR)
                    let x3 := mload(X3_MPTR)
                    let f_eval := 0
                    let Q_EVAL_CPTR := mload(Q_EVAL_CPTR_MPTR)
                    let rot_pt_0 := mload(add(ROT_POINTS_MPTR, 0x0))
                    let rot_pt_1 := mload(add(ROT_POINTS_MPTR, 0x20))
                    let rot_pt_2 := mload(add(ROT_POINTS_MPTR, 0x40))
                    let rot_pt_3 := mload(add(ROT_POINTS_MPTR, 0x60))
                    // --- set 3 (cardinality 3) ---
                    {
                    let dx_0 := addmod(x3, sub(r, rot_pt_2), r)
                    let dx_1 := addmod(x3, sub(r, rot_pt_3), r)
                    let dx_2 := addmod(x3, sub(r, rot_pt_0), r)
                    let lbasis_0 := 1
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_3), r), r)
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_0), r), r)
                    let lbasis_1 := 1
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_3, sub(r, rot_pt_2), r), r)
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_3, sub(r, rot_pt_0), r), r)
                    let lbasis_2 := 1
                    lbasis_2 := mulmod(lbasis_2, addmod(rot_pt_0, sub(r, rot_pt_2), r), r)
                    lbasis_2 := mulmod(lbasis_2, addmod(rot_pt_0, sub(r, rot_pt_3), r), r)
                    let bp_0 := dx_0
                    let bp_1 := mulmod(bp_0, dx_1, r)
                    let bp_2 := mulmod(bp_1, dx_2, r)
                    let bp_3 := mulmod(bp_2, lbasis_0, r)
                    let bp_4 := mulmod(bp_3, lbasis_1, r)
                    let bp_5 := mulmod(bp_4, lbasis_2, r)
                    let bq := scalar_inv(bp_5)
                    let lbasis_inv_2 := mulmod(bq, bp_4, r)
                    bq := mulmod(bq, lbasis_2, r)
                    let lbasis_inv_1 := mulmod(bq, bp_3, r)
                    bq := mulmod(bq, lbasis_1, r)
                    let lbasis_inv_0 := mulmod(bq, bp_2, r)
                    bq := mulmod(bq, lbasis_0, r)
                    let dx_inv_2 := mulmod(bq, bp_1, r)
                    bq := mulmod(bq, dx_2, r)
                    let dx_inv_1 := mulmod(bq, bp_0, r)
                    bq := mulmod(bq, dx_1, r)
                    let dx_inv_0 := bq
                    let den_inv := dx_inv_0
                    den_inv := mulmod(den_inv, dx_inv_1, r)
                    den_inv := mulmod(den_inv, dx_inv_2, r)
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x60)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xc0)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xe0)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    let term_2 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x100)), dx_inv_2, r), lbasis_inv_2, r)
                    eval := addmod(eval, sub(r, term_2), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 2 (cardinality 3) ---
                    {
                    let dx_0 := addmod(x3, sub(r, rot_pt_2), r)
                    let dx_1 := addmod(x3, sub(r, rot_pt_3), r)
                    let dx_2 := addmod(x3, sub(r, rot_pt_1), r)
                    let lbasis_0 := 1
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_3), r), r)
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_1), r), r)
                    let lbasis_1 := 1
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_3, sub(r, rot_pt_2), r), r)
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_3, sub(r, rot_pt_1), r), r)
                    let lbasis_2 := 1
                    lbasis_2 := mulmod(lbasis_2, addmod(rot_pt_1, sub(r, rot_pt_2), r), r)
                    lbasis_2 := mulmod(lbasis_2, addmod(rot_pt_1, sub(r, rot_pt_3), r), r)
                    let bp_0 := dx_0
                    let bp_1 := mulmod(bp_0, dx_1, r)
                    let bp_2 := mulmod(bp_1, dx_2, r)
                    let bp_3 := mulmod(bp_2, lbasis_0, r)
                    let bp_4 := mulmod(bp_3, lbasis_1, r)
                    let bp_5 := mulmod(bp_4, lbasis_2, r)
                    let bq := scalar_inv(bp_5)
                    let lbasis_inv_2 := mulmod(bq, bp_4, r)
                    bq := mulmod(bq, lbasis_2, r)
                    let lbasis_inv_1 := mulmod(bq, bp_3, r)
                    bq := mulmod(bq, lbasis_1, r)
                    let lbasis_inv_0 := mulmod(bq, bp_2, r)
                    bq := mulmod(bq, lbasis_0, r)
                    let dx_inv_2 := mulmod(bq, bp_1, r)
                    bq := mulmod(bq, dx_2, r)
                    let dx_inv_1 := mulmod(bq, bp_0, r)
                    bq := mulmod(bq, dx_1, r)
                    let dx_inv_0 := bq
                    let den_inv := dx_inv_0
                    den_inv := mulmod(den_inv, dx_inv_1, r)
                    den_inv := mulmod(den_inv, dx_inv_2, r)
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x40)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x60)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x80)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    let term_2 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xa0)), dx_inv_2, r), lbasis_inv_2, r)
                    eval := addmod(eval, sub(r, term_2), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 1 (cardinality 2) ---
                    {
                    let dx_0 := addmod(x3, sub(r, rot_pt_2), r)
                    let dx_1 := addmod(x3, sub(r, rot_pt_3), r)
                    let lbasis_0 := 1
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_3), r), r)
                    let lbasis_1 := 1
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_3, sub(r, rot_pt_2), r), r)
                    let bp_0 := dx_0
                    let bp_1 := mulmod(bp_0, dx_1, r)
                    let bp_2 := mulmod(bp_1, lbasis_0, r)
                    let bp_3 := mulmod(bp_2, lbasis_1, r)
                    let bq := scalar_inv(bp_3)
                    let lbasis_inv_1 := mulmod(bq, bp_2, r)
                    bq := mulmod(bq, lbasis_1, r)
                    let lbasis_inv_0 := mulmod(bq, bp_1, r)
                    bq := mulmod(bq, lbasis_0, r)
                    let dx_inv_1 := mulmod(bq, bp_0, r)
                    bq := mulmod(bq, dx_1, r)
                    let dx_inv_0 := bq
                    let den_inv := dx_inv_0
                    den_inv := mulmod(den_inv, dx_inv_1, r)
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x20)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x20)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x40)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 0 (cardinality 1) ---
                    {
                    let dx0 := addmod(x3, sub(r, rot_pt_2), r)
                    let dx0_inv := scalar_inv(dx0)
                    let eval := mulmod(addmod(calldataload(add(Q_EVAL_CPTR, 0x0)), sub(r, mload(add(Q_EVAL_SET_MPTR, 0x0))), r), dx0_inv, r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    mstore(F_EVAL_MPTR, f_eval)
                }
                // Generated PCS sub-block 8. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // build final_com and v (KZG single-opening proof, fused MSM)
                    // final MSM input length from circuit/VK shape: 63 term(s)
                    let x4 := mload(X4_MPTR)
                    let lin_x_split := mload(QUOTIENT_MPTR)
                    let lin_one_minus_x_n := mload(add(QUOTIENT_MPTR, 0x20))
                    let Q_EVAL_CPTR := mload(Q_EVAL_CPTR_MPTR)
                    let x4_pow_full := 1
                    x4_pow_full := mulmod(x4_pow_full, x4, r)
                    let x4_pow_1 := and(x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                    x4_pow_full := mulmod(x4_pow_full, x4, r)
                    let x4_pow_2 := and(x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                    x4_pow_full := mulmod(x4_pow_full, x4, r)
                    let x4_pow_3 := and(x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                    x4_pow_full := mulmod(x4_pow_full, x4, r)
                    let x4_pow_4 := and(x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                    let v := calldataload(Q_EVAL_CPTR)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x20)), x4_pow_1, r), r)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x40)), x4_pow_2, r), r)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x60)), x4_pow_3, r), r)
                    v := addmod(v, mulmod(mload(F_EVAL_MPTR), x4_pow_4, r), r)
                    mcopy(0x6cc0, 0x6480, 0x80)
                    mstore(0x6d40, mload(add(X1_POWERS_MPTR, 0x20)))
                    mcopy(0x6d60, 0x6700, 0x80)
                    mstore(0x6de0, mload(add(X1_POWERS_MPTR, 0x40)))
                    mcopy(0x6e00, 0x6500, 0x80)
                    mstore(0x6e80, mload(add(X1_POWERS_MPTR, 0x60)))
                    mcopy(0x6ea0, 0x6780, 0x80)
                    mstore(0x6f20, mload(add(X1_POWERS_MPTR, 0x80)))
                    mcopy(0x6f40, 0x2c80, 0x80)
                    mstore(0x6fc0, mload(add(X1_POWERS_MPTR, 0xa0)))
                    mcopy(0x6fe0, 0x2a00, 0x80)
                    mstore(0x7060, mload(add(X1_POWERS_MPTR, 0xc0)))
                    mcopy(0x7080, 0x2a80, 0x80)
                    mstore(0x7100, mload(add(X1_POWERS_MPTR, 0xe0)))
                    mcopy(0x7120, 0x2b00, 0x80)
                    mstore(0x71a0, mload(add(X1_POWERS_MPTR, 0x100)))
                    mcopy(0x71c0, 0x2b80, 0x80)
                    mstore(0x7240, mload(add(X1_POWERS_MPTR, 0x120)))
                    mcopy(0x7260, 0x2c00, 0x80)
                    mstore(0x72e0, mload(add(X1_POWERS_MPTR, 0x140)))
                    mcopy(0x7300, 0x2800, 0x80)
                    mstore(0x7380, mload(add(X1_POWERS_MPTR, 0x160)))
                    mcopy(0x73a0, 0x2880, 0x80)
                    mstore(0x7420, mload(add(X1_POWERS_MPTR, 0x180)))
                    mcopy(0x7440, 0x2900, 0x80)
                    mstore(0x74c0, mload(add(X1_POWERS_MPTR, 0x1a0)))
                    mcopy(0x74e0, 0x2980, 0x80)
                    mstore(0x7560, mload(add(X1_POWERS_MPTR, 0x1c0)))
                    mcopy(0x7580, 0x2d00, 0x80)
                    mstore(0x7600, mload(add(X1_POWERS_MPTR, 0x1e0)))
                    mcopy(0x7620, 0x2d80, 0x80)
                    mstore(0x76a0, mload(add(X1_POWERS_MPTR, 0x200)))
                    mcopy(0x76c0, 0x2e00, 0x80)
                    mstore(0x7740, mload(add(X1_POWERS_MPTR, 0x220)))
                    mcopy(0x7760, 0x2e80, 0x80)
                    mstore(0x77e0, mload(add(X1_POWERS_MPTR, 0x240)))
                    mcopy(0x7800, 0x2f00, 0x80)
                    mstore(0x7880, mload(add(X1_POWERS_MPTR, 0x260)))
                    mcopy(0x78a0, 0x2f80, 0x80)
                    mstore(0x7920, mload(add(X1_POWERS_MPTR, 0x280)))
                    mcopy(0x7940, 0x3180, 0x80)
                    mstore(0x79c0, mload(add(X1_POWERS_MPTR, 0x2a0)))
                    mcopy(0x79e0, 0x3200, 0x80)
                    mstore(0x7a60, mload(add(X1_POWERS_MPTR, 0x2c0)))
                    mcopy(0x7a80, 0x3800, 0x80)
                    mstore(0x7b00, mload(add(X1_POWERS_MPTR, 0x2e0)))
                    mcopy(0x7b20, 0x3880, 0x80)
                    mstore(0x7ba0, mload(add(X1_POWERS_MPTR, 0x300)))
                    mcopy(0x7bc0, 0x3900, 0x80)
                    mstore(0x7c40, mload(add(X1_POWERS_MPTR, 0x320)))
                    mcopy(0x7c60, 0x3980, 0x80)
                    mstore(0x7ce0, mload(add(X1_POWERS_MPTR, 0x340)))
                    mcopy(0x7d00, 0x3a00, 0x80)
                    mstore(0x7d80, mload(add(X1_POWERS_MPTR, 0x360)))
                    mcopy(0x7da0, 0x3a80, 0x80)
                    mstore(0x7e20, mload(add(X1_POWERS_MPTR, 0x380)))
                    mcopy(0x7e40, 0x3b00, 0x80)
                    mstore(0x7ec0, mload(add(X1_POWERS_MPTR, 0x3a0)))
                    mcopy(0x7ee0, 0x3b80, 0x80)
                    mstore(0x7f60, mload(add(X1_POWERS_MPTR, 0x3c0)))
                    mcopy(0x7f80, 0x3c00, 0x80)
                    mstore(0x8000, mload(add(X1_POWERS_MPTR, 0x3e0)))
                    let lin_query_scalar_31 := mload(add(X1_POWERS_MPTR, 0x400))
                    let lin_cur_scalar_31 := mulmod(lin_query_scalar_31, lin_one_minus_x_n, r)
                    mcopy(0x8020, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x0), 0x80)
                    mstore(0x80a0, lin_cur_scalar_31)
                    lin_cur_scalar_31 := mulmod(lin_cur_scalar_31, lin_x_split, r)
                    mcopy(0x80c0, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x80), 0x80)
                    mstore(0x8140, lin_cur_scalar_31)
                    lin_cur_scalar_31 := mulmod(lin_cur_scalar_31, lin_x_split, r)
                    mcopy(0x8160, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x100), 0x80)
                    mstore(0x81e0, lin_cur_scalar_31)
                    lin_cur_scalar_31 := mulmod(lin_cur_scalar_31, lin_x_split, r)
                    mcopy(0x8200, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x180), 0x80)
                    mstore(0x8280, lin_cur_scalar_31)
                    mcopy(0x82a0, 0x3000, 0x80)
                    mstore(0x8320, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x0)), r))
                    mcopy(0x8340, 0x3080, 0x80)
                    mstore(0x83c0, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x20)), r))
                    mcopy(0x83e0, 0x3100, 0x80)
                    mstore(0x8460, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x40)), r))
                    mcopy(0x8480, 0x3280, 0x80)
                    mstore(0x8500, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x60)), r))
                    mcopy(0x8520, 0x3300, 0x80)
                    mstore(0x85a0, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x80)), r))
                    mcopy(0x85c0, 0x3380, 0x80)
                    mstore(0x8640, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0xa0)), r))
                    mcopy(0x8660, 0x3400, 0x80)
                    mstore(0x86e0, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0xc0)), r))
                    mcopy(0x8700, 0x3480, 0x80)
                    mstore(0x8780, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0xe0)), r))
                    mcopy(0x87a0, 0x3500, 0x80)
                    mstore(0x8820, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x100)), r))
                    mcopy(0x8840, 0x3580, 0x80)
                    mstore(0x88c0, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x120)), r))
                    mcopy(0x88e0, 0x3600, 0x80)
                    mstore(0x8960, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x140)), r))
                    mcopy(0x8980, 0x3680, 0x80)
                    mstore(0x8a00, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x160)), r))
                    mcopy(0x8a20, 0x3700, 0x80)
                    mstore(0x8aa0, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x180)), r))
                    mcopy(0x8ac0, 0x3780, 0x80)
                    mstore(0x8b40, mulmod(lin_query_scalar_31, mload(add(SELECTOR_ACC_MPTR, 0x1a0)), r))
                    mcopy(0x8b60, 0x6680, 0x80)
                    mstore(0x8be0, x4_pow_1)
                    mcopy(0x8c00, 0x6800, 0x80)
                    mstore(0x8c80, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_1, r))
                    mcopy(0x8ca0, 0x6880, 0x80)
                    mstore(0x8d20, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_1, r))
                    mcopy(0x8d40, 0x6080, 0x80)
                    mstore(0x8dc0, x4_pow_2)
                    mcopy(0x8de0, 0x6100, 0x80)
                    mstore(0x8e60, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_2, r))
                    mcopy(0x8e80, 0x6180, 0x80)
                    mstore(0x8f00, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_2, r))
                    mcopy(0x8f20, 0x6200, 0x80)
                    mstore(0x8fa0, mulmod(mload(add(X1_POWERS_MPTR, 0x60)), x4_pow_2, r))
                    mcopy(0x8fc0, 0x6280, 0x80)
                    mstore(0x9040, mulmod(mload(add(X1_POWERS_MPTR, 0x80)), x4_pow_2, r))
                    mcopy(0x9060, 0x6300, 0x80)
                    mstore(0x90e0, mulmod(mload(add(X1_POWERS_MPTR, 0xa0)), x4_pow_2, r))
                    mcopy(0x9100, 0x6380, 0x80)
                    mstore(0x9180, mulmod(mload(add(X1_POWERS_MPTR, 0xc0)), x4_pow_2, r))
                    mcopy(0x91a0, 0x6400, 0x80)
                    mstore(0x9220, mulmod(mload(add(X1_POWERS_MPTR, 0xe0)), x4_pow_2, r))
                    mcopy(0x9240, 0x6580, 0x80)
                    mstore(0x92c0, x4_pow_3)
                    mcopy(0x92e0, 0x6600, 0x80)
                    mstore(0x9360, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_3, r))
                    mcopy(0x9380, F_COM_MPTR, 0x80)
                    mstore(0x9400, x4_pow_4)
                    if success {
                        success := staticcall(gas(), 0x0c, 0x6cc0, 0x2760, FINAL_COM_MPTR, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mstore(V_MPTR, v)
                }
                // Generated PCS sub-block 9. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // Scale z*pi - vG before the final pairing check
                    // pairing inputs (LHS = pi; RHS = final_com - v*G + x3*pi)
                    mcopy(PAIRING_LHS_MPTR, PI_MPTR, 0x80)
                    mcopy(0x80, G1_BASE_MPTR, 0x80)
                    mstore(0x100, addmod(0, sub(r, mload(V_MPTR)), r))
                    if success {
                        success := staticcall(gas(), 0x0c, 0x80, 0xa0, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x100, FINAL_COM_MPTR, 0x80)
                    if success {
                        success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x100, PI_MPTR, 0x80)
                    mstore(0x180, mload(X3_MPTR))
                    if success {
                        success := staticcall(gas(), 0x0c, 0x100, 0xa0, 0x100, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    if success {
                        success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(PAIRING_RHS_MPTR, 0x80, 0x80)
                }
            }

                // Batch the prevalidated public IVC accumulator pairing equation
            // into the final KZG pairing.
            //
            // We do not simply multiply the two pairing equations together:
            // two bad equations could cancel. Instead, after all four G1
            // pairing inputs are fixed, derive a verifier-local randomizer
            // alpha and check:
            //
            //   e(kzg_rhs + alpha * acc_rhs, G2_BASE)
            // * e(kzg_lhs + alpha * acc_lhs, NEG_S_G2_BASE) == 1
            //
            // If either original equation is bad, this combined equation
            // holds for at most one alpha in Fr.

            // The Yul `ec_pairing` helper checks
            //   e(arg0, G2_BASE) * e(arg1, NEG_S_G2_BASE) == 1
            // i.e.  e(arg0, [1]_2) = e(arg1, [s]_2).
            //
            // The KZG pairing identity is
            //   e(final_com - v*G + x3*pi, [1]_2) = e(pi, [s]_2),
            // so arg0 must be (final_com - v*G + x3*pi) and arg1 must be
            // pi. The PAIRING_*_MPTR slots store
            //   PAIRING_LHS_MPTR := pi
            //   PAIRING_RHS_MPTR := final_com - v*G + x3*pi
            // -- the historical "LHS"/"RHS" naming follows the dual MSM
            // accumulator (left = pi, right = combined) and *not* the
            // pairing argument order. Pass them swapped to ec_pairing.
            if iszero(success) { revert(0, 0) }
            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)

    

            // Success path is terminal. Invalid inputs have already reverted,
            // so the Solidity ABI observes `true`.
            //
            // The guard is redundant today -- every failure path above reverts
            // rather than clearing `success` -- but it keeps acceptance a local
            // property of this file instead of an invariant split across
            // FinalPairing.yul and ec_pairing.
            if iszero(success) { revert(0, 0) }
            mstore(RETURN_MPTR, 1)
            return(RETURN_MPTR, 0x20)
        }
    }
}