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
    
    /// @notice Verifying-key contract address authorized for this verifier.
    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.
    address public immutable AUTHORIZED_VK;
    // Expected VK runtime metadata. The deployed VK runtime is
    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than
    // EXPECTED_VK_PAYLOAD_LENGTH.
    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = 17024;
    uint256 internal constant EXPECTED_VK_LENGTH = 17025;
    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = 0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009;
    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);

    // Solidity ABI calldata cursors. The generated verifier accepts exactly
    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`
    // bytes itself in the same order as the Rust verifier transcript.
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x1ec4;
    uint256 internal constant     INSTANCE_CPTR = 0x1ee4;
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
    uint256 internal constant                VK_MPTR = 0x2700;
    uint256 internal constant         VK_DIGEST_MPTR = 0x2700;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x2720;
    uint256 internal constant                 K_MPTR = 0x2740;
    uint256 internal constant             N_INV_MPTR = 0x2760;
    uint256 internal constant             OMEGA_MPTR = 0x2780;
    uint256 internal constant         OMEGA_INV_MPTR = 0x27a0;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x27c0;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x27e0;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x2800;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x2820;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x2840;
    uint256 internal constant            G1_BASE_MPTR = 0x2860;
    uint256 internal constant            G2_BASE_MPTR = 0x28e0;
    uint256 internal constant      NEG_S_G2_BASE_MPTR = 0x29e0;

    uint256 internal constant CHALLENGE_MPTR = 0x6980;

    // Challenge layout. Squeeze order in midnight-proofs:
    //   user_phase challenges (variable count)
    //   theta -> beta, gamma -> trash_challenge -> y -> x ->
    //   x1, x2 -> x3 -> x4
    uint256 internal constant            THETA_MPTR = 0x6980;
    uint256 internal constant             BETA_MPTR = 0x69a0;
    uint256 internal constant            GAMMA_MPTR = 0x69c0;
    uint256 internal constant TRASH_CHALLENGE_MPTR = 0x69e0;
    uint256 internal constant                Y_MPTR = 0x6a00;
    uint256 internal constant                X_MPTR = 0x6a20;
    uint256 internal constant               X1_MPTR = 0x6a40;
    uint256 internal constant               X2_MPTR = 0x6a60;
    uint256 internal constant               X3_MPTR = 0x6a80;
    uint256 internal constant               X4_MPTR = 0x6aa0;

    // Batch-open commitments live in 4-word EIP-2537 padded slots.
    uint256 internal constant             F_COM_MPTR = 0x6ac0;
    uint256 internal constant                PI_MPTR = 0x6b40;

    // Accumulator (KZG IVC).
    uint256 internal constant          ACC_LHS_MPTR = 0x6bc0;
    uint256 internal constant          ACC_RHS_MPTR = 0x6c40;

    // Lagrange / linearization scratch.
    uint256 internal constant              X_N_MPTR = 0x6cc0;
    uint256 internal constant  X_N_MINUS_1_INV_MPTR = 0x6ce0;
    uint256 internal constant           L_LAST_MPTR = 0x6d00;
    uint256 internal constant          L_BLIND_MPTR = 0x6d20;
    uint256 internal constant              L_0_MPTR = 0x6d40;
    uint256 internal constant     INSTANCE_EVAL_MPTR = 0x6d60;
    // Legacy name: this is not h(x). It stores the expected opening
    // scalar for the linearized commitment, i.e. the negated y-batched
    // identity numerator reconstructed from the alleged evals at x.
    uint256 internal constant     QUOTIENT_EVAL_MPTR = 0x6d80;
    uint256 internal constant         QUOTIENT_MPTR = 0x6da0;   // 4 words
    uint256 internal constant            F_EVAL_MPTR = 0x6e40;
    uint256 internal constant                 V_MPTR = 0x6e60;
    uint256 internal constant         FINAL_COM_MPTR = 0x6e80;   // 4 words
    uint256 internal constant      PAIRING_LHS_MPTR = 0x6f00;   // 4 words
    uint256 internal constant      PAIRING_RHS_MPTR = 0x6f80;   // 4 words

    // Multi-prepare scratch (sized at codegen time).
    uint256 internal constant       ROT_POINTS_MPTR = 0x7000;
    uint256 internal constant       X1_POWERS_MPTR = 0x7380;
    // Q_COM materialization is currently fused into the final MSM scratch,
    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero
    // reserved capacity until a future emitter starts writing Q_COM_MPTR.
    uint256 internal constant            Q_COM_MPTR = 0x7ba0;
    uint256 internal constant      Q_EVAL_SET_MPTR = 0x7ba0;

    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals
    // block of the proof; we keep it as a memory slot for symmetry.
    uint256 internal constant         Q_EVAL_CPTR_MPTR = 0x82a0;

    // Reserved 4-word slot for the G1 identity (point at infinity) in
    // EIP-2537 padded form. EVM memory is zero-initialised, and we
    // never write to this region, so the four `mload`s below produce
    // 0,0,0,0 which is exactly the identity encoding the EIP-2537
    // ec_add / ec_mul precompiles accept.
    uint256 internal constant       G1_IDENTITY_MPTR = 0x83a0;

    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain
    // Solidity proof shim rewrites proof scalars into canonical BE words,
    // so `calldataload` gives the field element directly. The transcript-
    // side `evaluations` loop range-checks and spills that value here so
    // downstream eval references (gate evaluator + PCS q_eval Horner)
    // become 3-gas `mload(...)` instead of calldata reads.
    uint256 internal constant     REVERSED_EVALS_MPTR = 0x8500;
    uint256 internal constant      SELECTOR_ACC_MPTR = 0xa1c0;
    uint256 internal constant   QUOTIENT_RETURN_MPTR = 0x80;
    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = 0xa1c0;
    uint256 internal constant        TRACE_U256_MPTR = 0xd3c0;

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
    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = 0x91c0;
    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = 0x9940;
    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = 0x9a40;
    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = 0x9d40;
    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = 0x9e40;
    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = 0x9f40;
    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = 0x9fc0;

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

        /// @notice Smoke-check the BLS12-381 precompiles required by the verifier.
    /// @dev Uses identity inputs to catch absent EIP-2537 implementations, short return data, and incompatible pairing semantics at deployment.
    function require_eip2537_precompiles() private view {
        assembly ("memory-safe") {
            // Scratch is reused for every precompile probe. Start with the
            // EIP-2537 identity encoding for G1/G2: all-zero padded words.
            let scratch := 0x80
            for { let off := 0 } lt(off, 0x0180) { off := add(off, 0x20) } {
                mstore(add(scratch, off), 0)
            }

            // G1ADD(identity, identity) -> identity, 128-byte return.
            // This catches chains where the precompile is missing or returns a
            // non-standard success shape.
            if iszero(staticcall(50000, 0x0b, scratch, 0x0100, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // G1MSM([(identity, 0)]) -> identity, 128-byte return.
            // The production verifier uses G1MSM both for commitments and as
            // the subgroup validator for absorbed proof points.
            if iszero(staticcall(60000, 0x0c, scratch, 0xa0, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // PAIRING_CHECK([(identity_g1, identity_g2)]) -> true,
            // 32-byte return. This catches absent pairing precompiles,
            // short return data, and obviously incompatible semantics.
            if iszero(staticcall(120000, 0x0f, scratch, 0x0180, scratch, 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
        }
    }

    
    /// @notice Create a verifier pinned to a generated verifying key.
    /// @dev Checks EIP-2537 availability and verifies the VK runtime before storing its address.
    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.
    constructor(address authorizedVk) {
        // Embedded quotient path: only the external VK runtime needs to be
        // pinned, but the curve precompiles are still mandatory.
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
    ) external returns (bool) {
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
                // revert here rather than a bogus modexp result.
                if iszero(x) { revert(0, 0) }
                let p := 0x2600
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
                if iszero(ret) { leave }
                // Lay out two (G1, G2) pairs at scratch..scratch+0x300:
                //   [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)]
                // Cancun MCOPY (3 + 3·words gas) replaces what used to
                // be a 4-step mstore chain for each G1 (~60 gas) and an
                // 8-iter mstore loop for each G2 (~240 gas). Net saving
                // here is ~500 gas per ec_pairing call.
                let scratch := 0x0300
                mcopy(scratch,              lhs_mptr,                 0x80)
                mcopy(add(scratch, 0x80),   G2_BASE_MPTR,             0x100)
                mcopy(add(scratch, 0x180),  rhs_mptr,                 0x80)
                mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)
                ret := staticcall(170000, 0x0f, scratch, 0x0300, scratch, 0x20)
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
            // Validate and prepare the public accumulator equation before the
            // main transcript starts. This fails malformed public inputs early
            // and writes ACC_LHS_MPTR / ACC_RHS_MPTR for final pairing batching.
            //
            // The accumulator public input represents an equality of two G1
            // commitments used by the recursive KZG accumulator. This helper:
            //   1. decodes carried public G1 points from shifted limbs;
            //   2. forces every decoded point through EIP-2537 G1MSM so the
            //      precompile validates curve/subgroup membership;
            //   3. folds the RHS carried point and fixed-base scalar tail into
            //      ACC_RHS_MPTR, leaving ACC_LHS_MPTR / ACC_RHS_MPTR ready for
            //      randomized batching in FinalPairing.yul.
            function validate_public_accumulator(success, r) -> out {
                out := success
                let bits := 56
                let n := 7
                // The BLS12-381 self-emulation currently exposes Fp
                // coordinates as 7 radix-2^56 limbs.
                let limb_base := shl(bits, 1)
                let limbs_per_word := 4
                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                // acc_offset is generated from the VK/protocol shape and
                // points into the ABI `instances` array.
                let acc_instance_ptr := add(INSTANCE_CPTR, 0x0160)

                // LHS layout: point limbs (x,y), then either an explicit
                // scalar word or an implicit unit scalar for already-collapsed
                // point-pair public inputs.
                // The scalar pointer is computed unconditionally; the rendered
                // branch below decides whether to read it or use scalar 1.
                let lhs_scalar_ptr := add(acc_instance_ptr, mul(mul(2, coord_words), 0x20))
                let lhs_ok, lhs_is_id := load_acc_point(ACC_LHS_MPTR, acc_instance_ptr, bits, n, limb_base)
                out := and(out, lhs_ok)
                // Shared scratch for one-pair LHS validation and the later
                // variable-length RHS MSM.
                let acc_scratch := 0xa1c0
                {
                    // Already-collapsed point-pair layout: carried scalars are
                    // implicit one.
                    let lhs_scalar := 1
                    // Identity status is useful for decoding checks above, but
                    // validation still goes through G1MSM for all points.
                    pop(lhs_is_id)
                    // Always route the decoded carried point through G1MSM,
                    // even for identity points and zero/one scalars. The
                    // precompile is the on-curve/subgroup validator for this
                    // public-input point; skipping it would let a malformed
                    // non-identity point hide behind scalar 0.
                    mcopy(acc_scratch, ACC_LHS_MPTR, 0x80)
                    mstore(add(acc_scratch, 0x80), lhs_scalar)
                    if out {
                        // Single-pair MSM output overwrites ACC_LHS_MPTR with
                        // lhs_scalar * decoded_lhs. If lhs_scalar is one, this
                        // is also a curve/subgroup validation round-trip.
                        out := staticcall(62000, 0x0c, acc_scratch, 0xa0, ACC_LHS_MPTR, 0x80)
                        out := and(out, eq(returndatasize(), 0x80))
                    }
                }
                // RHS layout for this generated verifier is an already
                // collapsed point pair: lhs point, rhs point. Both carried
                // scalars are implicit one, and there is no fixed-base scalar
                // tail.
                let rhs_instance_ptr := lhs_scalar_ptr
                // RHS scalar, when present, immediately follows the RHS point
                // limbs. The fixed-base scalar tail starts after it.
                let rhs_scalar_ptr := add(rhs_instance_ptr, mul(mul(2, coord_words), 0x20))
                let rhs_ok, rhs_is_id := load_acc_point(ACC_RHS_MPTR, rhs_instance_ptr, bits, n, limb_base)
                out := and(out, rhs_ok)
                // acc_pair_ptr appends (G1, scalar) pairs into acc_scratch for
                // one final RHS MSM.
                let acc_pair_ptr := acc_scratch
                {
                    // Implicit unit scalar for already-collapsed point pairs.
                    let rhs_scalar := 1
                    pop(rhs_is_id)
                    // Keep the carried RHS point in the MSM input even when
                    // it is encoded as identity or has scalar 0/1, so EIP-2537
                    // validates every decoded public accumulator point before
                    // it can affect, or be erased from, the pairing batch.
                    mcopy(acc_pair_ptr, ACC_RHS_MPTR, 0x80)
                    mstore(add(acc_pair_ptr, 0x80), rhs_scalar)
                    // Move to the next (G1, scalar) pair slot.
                    acc_pair_ptr := add(acc_pair_ptr, 0xa0)
                }
                // Total byte length of the appended RHS MSM input pairs. This
                // is at least one pair because the carried RHS point is always
                // appended; keep the guard for synthetic render configurations.
                let acc_msm_len := sub(acc_pair_ptr, acc_scratch)
                if acc_msm_len {
                    // Fold the carried RHS point and any generated fixed-base
                    // tail into ACC_RHS_MPTR. The later final pairing block
                    // randomizes this equation together with the KZG pairing.
                    if out {
                        // Output overwrites ACC_RHS_MPTR with:
                        //   rhs_scalar * carried_rhs
                        // + sum_i fixed_scalar_i * fixed_base_i
                        //
                        // The precompile also validates every nonzero fixed
                        // base embedded by codegen and the carried RHS point.
                        out := staticcall(
                            62000,
                            0x0c,
                            acc_scratch,
                            acc_msm_len,
                            ACC_RHS_MPTR,
                            0x80
                        )
                        out := and(out, eq(returndatasize(), 0x80))
                    }
                }
                // The caller checks `out` and reverts before transcript work if
                // any decode, canonicality, or precompile validation failed.
            }

    
            // Section-boundary gas-attribution checkpoint. Emits a
            // single LOG1 (no data) with topic = (id << 248) | gas().
            // Cost: 375 (LOG base) + 375 (1 topic) = 750 gas/call.
            // Host-side parses the topic into (id, gas_left) and prints
            // pairwise deltas (see `dump_gas_checkpoints`).
            function gas_checkpoint(id) {
                log1(0, 0, or(shl(248, id), gas()))
            }

            let r := FR_MODULUS
            let success := true

    
            gas_checkpoint(1) // entry: before VK loading

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

                // This verifier is pinned to one generated VK, so schema
                // values such as instance count and accumulator layout are
                // rendered as constants instead of reread from the VK header.
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
                success := and(success, eq(0x1e60, calldataload(PROOF_LEN_CPTR)))
                success := and(success, eq(19, calldataload(NUM_INSTANCE_CPTR)))
                // Calldata must contain exactly the ABI selector, proof bytes,
                // instance-array length, and generated number of instance
                // words. Any trailing bytes fail closed.
                success := and(
                    success,
                    eq(calldatasize(), add(INSTANCE_CPTR, 0x0260))
                )
                // Stop before any transcript absorption if the ABI/proof shape
                // is not exactly the generated one.
                if iszero(success) { revert(0, 0) }
            }
            // Fail malformed accumulator public inputs before transcript,
            // quotient, PCS, and final pairing work. The late accumulator block
            // only batches these already-validated G1 outputs into the final
            // pairing equation.
            //
            // Accumulator validation decodes shifted public-input limbs into
            // EIP-2537 G1 slots, checks canonical encodings, and routes points
            // through G1MSM for curve/subgroup validation. Doing it here means
            // invalid accumulator public inputs cannot influence transcript
            // challenge derivation or waste gas in later quotient/PCS work.
            // validate_public_accumulator returns a boolean to share the same
            // success-plumbing style as other helper calls; this boundary is
            // where the verifier converts failure to a revert.
            success := validate_public_accumulator(success, r)
            if iszero(success) { revert(0, 0) }
            gas_checkpoint(2) // after VK loading + accumulator public-input precheck

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
                buf_len := common_word(buf_len, 19)

                let instance_cptr := INSTANCE_CPTR
                for { let instance_cptr_end := add(instance_cptr, 0x0260) }
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
            }
            gas_checkpoint(3) // after VK digest + committed_pi + instance absorbs

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
            for { let end := add(proof_cptr, 0x0780) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                // Store the commitment at its phase-ordered advice slot.
                calldatacopy(advice_walk, proof_cptr, 0x80)
                advice_walk := add(advice_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            gas_checkpoint(4) // after user-phase advice reads + user challenge squeezes

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
            gas_checkpoint(5) // after theta squeeze + lookup multiplicities

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
            for { let end := add(proof_cptr, 0x0300) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(perm_z_walk, proof_cptr, 0x80)
                perm_z_walk := add(perm_z_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            gas_checkpoint(6) // after beta/gamma + permutation Z products
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
            gas_checkpoint(7) // after lookup helpers + Z accumulators

            // ---- trash_challenge ----
            // Midnight squeezes this challenge unconditionally, even when the
            // circuit has no trash arguments.
            // Keeping this squeeze unconditional preserves transcript
            // compatibility across circuits with and without trash columns.
            buf_len := squeeze_to(buf_len, TRASH_CHALLENGE_MPTR)
            // ---- trashcans ----
            // Trashcan commitments are optional, but when present they are
            // absorbed before y so the quotient batching challenge binds them.
            let trashcan_walk := TRASHCAN_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, 0x80) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(trashcan_walk, proof_cptr, 0x80)
                trashcan_walk := add(trashcan_walk, 0x80)
                proof_cptr := add(proof_cptr, 0x80)
            }
            gas_checkpoint(8) // after trash_challenge + trashcans

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
            gas_checkpoint(9) // after y squeeze + quotient-limb reads

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
                for { let end := add(proof_cptr, 0x0cc0) }
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
            for { let end := add(proof_cptr, 0xa0) }
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
            gas_checkpoint(10) // after evaluations + x1/x2 + f_com + x3 + q_evals + x4 + pi (transcript done)

                // ===============================================================
            // Lagrange & instance-evaluation block (pure Fr arithmetic).
            // ===============================================================
            {
                let k := 20
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
                let mptr_end := add(mptr, 0x03a0)
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
                for { let l_i_cptr_end := add(X_N_MPTR, 0x0140) }
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
                        let instance_cptr_end := add(instance_cptr, 0x0260)
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
                let l_0 := mload(add(X_N_MPTR, 0x0140))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }
            gas_checkpoint(11) // after Lagrange + instance evaluation block

            if iszero(success) { revert(0, 0) }

                // Optional quotient helper functions. Each one is rendered only
            // when the Rust lowering pass recognized the corresponding
            // expression shape in this generated verifier. They are pure Fr
            // helpers and share the same FR_MODULUS as the surrounding
            // numerator block.
            // VK-specialized identity helper for Poseidon S-box terms.
            //
            // Rust source shape:
            //   circuits/src/hash/poseidon/poseidon_chip.rs::sbox
            //   full_round_gate / partial_round_gate
            //   circuits/src/hash/poseidon/round_skips.rs::RoundId
            //
            // The Rust verifier only sees this as an Expression tree from
            // `vk.cs.gates`; the generator emits q_pow5 after recognizing five
            // equal multiplicative factors. It is a codegen shortcut for x^5,
            // not a separate verifier rule.
            function q_pow5(x) -> z {
                let q_r := FR_MODULUS
                let x2 := mulmod(x, x, q_r)
                z := mulmod(x, mulmod(x2, x2, q_r), q_r)
            }            // ===============================================================
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
                let q_const_mptr := 0x2ae0
                // Program bytes are also stored in the VK payload, packed into
                // 32-byte words by PackedProgramCodec.
                let q_program_mptr := 0x4120
                // Running Horner accumulator for fully evaluated identities.
                // After all identities, this is nu_y(x) for the `None`
                // identity group.
                // Initialize A = 0 before scanning the identity stream.
                mstore(0xa300, 0)
                // Simple selectors are grouped into separate linearization
                // buckets. They start at zero for every proof.
                // q_sel_zero_off walks selector bucket byte offsets.
                for { let q_sel_zero_off := 0 } lt(q_sel_zero_off, 0x0140) { q_sel_zero_off := add(q_sel_zero_off, 0x20) } {
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
                    // Start at i=1 because y^0 = 1 is implicit and never read.
                    for { let q_y_power_i := 1 } lt(q_y_power_i, 49) { q_y_power_i := add(q_y_power_i, 1) } {
                        // Advance from y^(i-1) to y^i modulo Fr.
                        q_y_power := mulmod(q_y_power, y, r)
                        // Store y^i at selector_power_mptr + 32*i.
                        mstore(add(0xa340, shl(5, q_y_power_i)), q_y_power)
                    }
                }

                // Direct inline prefix. These identities are generated as Yul
                // before entering the VM. They use the same fold snippets as
                // VM/native identities, so they occupy the same y-batch order.
                {
                let var0 := 0x1
                let f_3 := mload(0x8b40)
                let f_4 := mload(0x8a40)
                let a_0 := mload(0x8520)
                let var1 := mulmod(f_4, a_0, r)
                let var2 := addmod(f_3, var1, r)
                let f_5 := mload(0x8a60)
                let a_1 := mload(0x8540)
                let var3 := mulmod(f_5, a_1, r)
                let var4 := addmod(var2, var3, r)
                let f_6 := mload(0x8a80)
                let a_2 := mload(0x8560)
                let var5 := mulmod(f_6, a_2, r)
                let var6 := addmod(var4, var5, r)
                let f_7 := mload(0x8aa0)
                let a_3 := mload(0x8580)
                let var7 := mulmod(f_7, a_3, r)
                let var8 := addmod(var6, var7, r)
                let f_8 := mload(0x8ac0)
                let a_4 := mload(0x85a0)
                let var9 := mulmod(f_8, a_4, r)
                let var10 := addmod(var8, var9, r)
                let f_0 := mload(0x8ae0)
                let a_0_next_1 := mload(0x85c0)
                let var11 := mulmod(f_0, a_0_next_1, r)
                let var12 := addmod(var10, var11, r)
                let f_1 := mload(0x8b00)
                let var13 := mulmod(f_1, a_0, r)
                let var14 := mulmod(var13, a_1, r)
                let var15 := addmod(var12, var14, r)
                let f_2 := mload(0x8b20)
                let var16 := mulmod(f_2, a_0, r)
                let var17 := mulmod(var16, a_2, r)
                let var18 := addmod(var15, var17, r)
                let var19 := mulmod(var0, var18, r)
                mstore(0xa960, var19)
                }
                mstore(0xa300, mulmod(mload(0xa300), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x0)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x8540)
                let a_2 := mload(0x8560)
                let var1 := addmod(a_1, a_2, r)
                let a_3 := mload(0x8580)
                let var2 := addmod(0, sub(r, a_3), r)
                let var3 := addmod(var1, var2, r)
                let a_4 := mload(0x85a0)
                let var4 := addmod(0, sub(r, a_4), r)
                let var5 := addmod(var3, var4, r)
                let var6 := mulmod(var0, var5, r)
                mstore(0xa960, var6)
                }
                mstore(0xa300, mulmod(mload(0xa300), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                }
                {
                let var0 := 0x1
                let a_0 := mload(0x8520)
                let f_4 := mload(0x8a40)
                let var1 := addmod(a_0, f_4, r)
                let a_0_next_1 := mload(0x85c0)
                let var2 := addmod(0, sub(r, a_0_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0xa960, var4)
                }
                mstore(0xa300, mulmod(mload(0xa300), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x8540)
                let f_5 := mload(0x8a60)
                let var1 := addmod(a_1, f_5, r)
                let a_1_next_1 := mload(0x85e0)
                let var2 := addmod(0, sub(r, a_1_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0xa960, var4)
                }
                mstore(0xa300, mulmod(mload(0xa300), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                q_selector_acc := mulmod(q_selector_acc, mload(add(0xa340, 0x20)), r)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
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
                let q_end := add(q_program_mptr, 0x11cf)
                // q_sp starts at the first free stack word.
                let q_sp := 0xa960
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
                        q_sp := 0xa960
                        // The generated lines below call the same fold snippets
                        // used by interpreted expressions, so trace IDs and
                        // y-batch positions remain contiguous.
                        {
                        let delta := 0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
                        let q_perm_vals := 0xa960
                        let q_perm_sigmas := 0xaba0
                        let q_perm_z_cur := 0xade0
                        let q_perm_z_next := 0xaea0
                        let q_perm_z_last := 0xaf60
                        let q_perm_delta_base_ptr := 0xb000
                        let q_perm_num_cols := 18
                        let q_perm_num_sets := 6
                        let q_perm_chunk_len := 3
                        let q_perm_delta_chunk := 0x4285088329c399ea457a8ca1d30f8957e74c7f529842a1579b4fee55b3982923
                        mstore(add(q_perm_vals, 0x0), mload(0x8a20))
                        {
                        for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 5) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {
                        let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)
                        let q_perm_val_load_src_off := q_perm_val_load_dst_off
                        mstore(add(add(q_perm_vals, 0x20), q_perm_val_load_dst_off), mload(add(0x8520, q_perm_val_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_vals, 0xc0), mload(0x8500))
                        mstore(add(q_perm_vals, 0xe0), mload(INSTANCE_EVAL_MPTR))
                        {
                        for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 9) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {
                        let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)
                        let q_perm_val_load_src_off := q_perm_val_load_dst_off
                        mstore(add(add(q_perm_vals, 0x100), q_perm_val_load_dst_off), mload(add(0x8620, q_perm_val_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_vals, 0x220), mload(0x8a00))
                        {
                        for { let q_perm_sigma_load_i := 0 } lt(q_perm_sigma_load_i, 18) { q_perm_sigma_load_i := add(q_perm_sigma_load_i, 1) } {
                        let q_perm_sigma_load_dst_off := shl(5, q_perm_sigma_load_i)
                        let q_perm_sigma_load_src_off := q_perm_sigma_load_dst_off
                        mstore(add(add(q_perm_sigmas, 0x0), q_perm_sigma_load_dst_off), mload(add(0x8c40, q_perm_sigma_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_cur_load_i := 0 } lt(q_perm_z_cur_load_i, 6) { q_perm_z_cur_load_i := add(q_perm_z_cur_load_i, 1) } {
                        let q_perm_z_cur_load_dst_off := shl(5, q_perm_z_cur_load_i)
                        let q_perm_z_cur_load_src_off := mul(q_perm_z_cur_load_i, 0x60)
                        mstore(add(add(q_perm_z_cur, 0x0), q_perm_z_cur_load_dst_off), mload(add(0x8e80, q_perm_z_cur_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_next_load_i := 0 } lt(q_perm_z_next_load_i, 6) { q_perm_z_next_load_i := add(q_perm_z_next_load_i, 1) } {
                        let q_perm_z_next_load_dst_off := shl(5, q_perm_z_next_load_i)
                        let q_perm_z_next_load_src_off := mul(q_perm_z_next_load_i, 0x60)
                        mstore(add(add(q_perm_z_next, 0x0), q_perm_z_next_load_dst_off), mload(add(0x8ea0, q_perm_z_next_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_last_load_i := 0 } lt(q_perm_z_last_load_i, 5) { q_perm_z_last_load_i := add(q_perm_z_last_load_i, 1) } {
                        let q_perm_z_last_load_dst_off := shl(5, q_perm_z_last_load_i)
                        let q_perm_z_last_load_src_off := mul(q_perm_z_last_load_i, 0x60)
                        mstore(add(add(q_perm_z_last, 0x0), q_perm_z_last_load_dst_off), mload(add(0x8ec0, q_perm_z_last_load_src_off)))
                        }
                        }
                        let q_perm_eval := 0
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_perm_eval, r))
                        let q_perm_zn := mload(add(q_perm_z_cur, 0xa0))
                        q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_perm_eval, r))
                        for { let q_perm_i := 1 } lt(q_perm_i, 6) { q_perm_i := add(q_perm_i, 1) } {
                        let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))
                        let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_perm_eval, r))
                        }
                        mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))
                        for { let q_perm_set := 0 } lt(q_perm_set, 6) { q_perm_set := add(q_perm_set, 1) } {
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
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_perm_eval, r))
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
                        q_sp := 0xa960
                        // Generated LogUp code follows the same y-batch order
                        // as the Rust identity stream.
                        {
                        let q_lookup_f := 0xa960
                        let q_lookup_prefix := 0xa9e0
                        let q_lookup_suffix := 0xaa60
                        let q_lookup_l0 := mload(L_0_MPTR)
                        let q_lookup_llast := mload(L_LAST_MPTR)
                        let q_lookup_lblind := mload(L_BLIND_MPTR)
                        let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)
                        let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)
                        let q_lookup_beta := mload(BETA_MPTR)
                        let q_lookup_theta := mload(THETA_MPTR)
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x90e0), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
                        }
                        {
                        let f_10 := mload(0x8b60)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_10, r)
                        let var1 := mulmod(var0, q_lookup_theta, r)
                        for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, 4) { q_lookup_shared_i := add(q_lookup_shared_i, 1) } {
                        let q_lookup_shared_off := shl(5, q_lookup_shared_i)
                        let q_lookup_shared_tail := mload(add(0x8540, q_lookup_shared_off))
                        let q_lookup_shared_compressed := addmod(var1, q_lookup_shared_tail, r)
                        mstore(add(q_lookup_f, q_lookup_shared_off), addmod(q_lookup_shared_compressed, q_lookup_beta, r))
                        }
                        let q_lookup_product := 1
                        for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, 4) { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {
                        q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)
                        }
                        mstore(q_lookup_prefix, 1)
                        for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, 4) { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {
                        let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)
                        mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))
                        }
                        mstore(add(q_lookup_suffix, 0x60), 1)
                        for { let q_lookup_suf_i := sub(4, 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {
                        let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)
                        mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))
                        }
                        let q_lookup_sum := 0
                        for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, 4) { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {
                        q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)
                        }
                        let q_lookup_eval := addmod(mulmod(mload(0x90c0), q_lookup_product, r), sub(r, q_lookup_sum), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0x90c0)
                        let f_17 := mload(0x8be0)
                        let f_11 := mload(0x8b80)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_11, r)
                        let f_12 := mload(0x8ba0)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), f_12, r)
                        let q_lookup_s_sum_h := mulmod(f_17, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0x9100), sub(r, addmod(mload(0x90e0), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var1, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x90a0), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
                        }
                        }
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0x9160), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
                        }
                        {
                        let a_14 := mload(0x8a00)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), a_14, r)
                        let a_0 := mload(0x8520)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), a_0, r)
                        let a_1 := mload(0x8540)
                        let var2 := addmod(mulmod(var1, q_lookup_theta, r), a_1, r)
                        let a_2 := mload(0x8560)
                        let var3 := addmod(mulmod(var2, q_lookup_theta, r), a_2, r)
                        let a_3 := mload(0x8580)
                        let var4 := addmod(mulmod(var3, q_lookup_theta, r), a_3, r)
                        let a_4 := mload(0x85a0)
                        let var5 := addmod(mulmod(var4, q_lookup_theta, r), a_4, r)
                        let a_5 := mload(0x8620)
                        let var6 := addmod(mulmod(var5, q_lookup_theta, r), a_5, r)
                        let a_6 := mload(0x8640)
                        let var7 := addmod(mulmod(var6, q_lookup_theta, r), a_6, r)
                        let a_7 := mload(0x8660)
                        let var8 := addmod(mulmod(var7, q_lookup_theta, r), a_7, r)
                        let a_8 := mload(0x8680)
                        let var9 := addmod(mulmod(var8, q_lookup_theta, r), a_8, r)
                        let a_9 := mload(0x86a0)
                        let var10 := addmod(mulmod(var9, q_lookup_theta, r), a_9, r)
                        let a_10 := mload(0x86c0)
                        let var11 := addmod(mulmod(var10, q_lookup_theta, r), a_10, r)
                        let a_11 := mload(0x86e0)
                        let var12 := addmod(mulmod(var11, q_lookup_theta, r), a_11, r)
                        let a_12 := mload(0x8700)
                        let var13 := addmod(mulmod(var12, q_lookup_theta, r), a_12, r)
                        let a_13 := mload(0x8720)
                        let var14 := addmod(mulmod(var13, q_lookup_theta, r), a_13, r)
                        let f_13 := mload(0x8bc0)
                        let var15 := addmod(mulmod(var14, q_lookup_theta, r), f_13, r)
                        let q_lookup_eval := addmod(mulmod(mload(0x9140), addmod(var15, q_lookup_beta, r), r), sub(r, 1), r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0x9140)
                        let var0 := 0x1
                        let f_24 := mload(0x8c00)
                        let var1 := addmod(0, sub(r, f_24), r)
                        let var2 := addmod(var0, var1, r)
                        let a_14 := mload(0x8a00)
                        let var3 := mulmod(var2, a_14, r)
                        let var4 := addmod(mulmod(0, q_lookup_theta, r), var3, r)
                        let a_0 := mload(0x8520)
                        let var5 := mulmod(var2, a_0, r)
                        let var6 := addmod(mulmod(var4, q_lookup_theta, r), var5, r)
                        let a_1 := mload(0x8540)
                        let var7 := mulmod(var2, a_1, r)
                        let var8 := addmod(mulmod(var6, q_lookup_theta, r), var7, r)
                        let a_2 := mload(0x8560)
                        let var9 := mulmod(var2, a_2, r)
                        let var10 := addmod(mulmod(var8, q_lookup_theta, r), var9, r)
                        let a_3 := mload(0x8580)
                        let var11 := mulmod(var2, a_3, r)
                        let var12 := addmod(mulmod(var10, q_lookup_theta, r), var11, r)
                        let a_4 := mload(0x85a0)
                        let var13 := mulmod(var2, a_4, r)
                        let var14 := addmod(mulmod(var12, q_lookup_theta, r), var13, r)
                        let a_5 := mload(0x8620)
                        let var15 := mulmod(var2, a_5, r)
                        let var16 := addmod(mulmod(var14, q_lookup_theta, r), var15, r)
                        let a_6 := mload(0x8640)
                        let var17 := mulmod(var2, a_6, r)
                        let var18 := addmod(mulmod(var16, q_lookup_theta, r), var17, r)
                        let a_7 := mload(0x8660)
                        let var19 := mulmod(var2, a_7, r)
                        let var20 := addmod(mulmod(var18, q_lookup_theta, r), var19, r)
                        let a_8 := mload(0x8680)
                        let var21 := mulmod(var2, a_8, r)
                        let var22 := addmod(mulmod(var20, q_lookup_theta, r), var21, r)
                        let a_9 := mload(0x86a0)
                        let var23 := mulmod(var2, a_9, r)
                        let var24 := addmod(mulmod(var22, q_lookup_theta, r), var23, r)
                        let a_10 := mload(0x86c0)
                        let var25 := mulmod(var2, a_10, r)
                        let var26 := addmod(mulmod(var24, q_lookup_theta, r), var25, r)
                        let a_11 := mload(0x86e0)
                        let var27 := mulmod(var2, a_11, r)
                        let var28 := addmod(mulmod(var26, q_lookup_theta, r), var27, r)
                        let a_12 := mload(0x8700)
                        let var29 := mulmod(var2, a_12, r)
                        let var30 := addmod(mulmod(var28, q_lookup_theta, r), var29, r)
                        let a_13 := mload(0x8720)
                        let var31 := mulmod(var2, a_13, r)
                        let var32 := addmod(mulmod(var30, q_lookup_theta, r), var31, r)
                        let f_13 := mload(0x8bc0)
                        let var33 := mulmod(var2, f_13, r)
                        let var34 := addmod(mulmod(var32, q_lookup_theta, r), var33, r)
                        let q_lookup_s_sum_h := mulmod(var0, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0x9180), sub(r, addmod(mload(0x9160), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var34, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0x9120), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        mstore(0xa300, addmod(mload(0xa300), q_lookup_eval, r))
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
                        q_sp := 0xa960
                        // Native identity sub-cases are generated from selected heavy gate identities.
                        switch q_native_idx
                        case 0 {
                            {
                            let var0 := 0x1
                            let a_0 := mload(0x8520)
                            let a_0_next_1 := mload(0x85c0)
                            let var1 := mulmod(a_0, a_0_next_1, r)
                            let var2 := 0x100000000000000
                            let a_1_next_1 := mload(0x85e0)
                            let var3 := mulmod(a_0, a_1_next_1, r)
                            let var4 := mulmod(var2, var3, r)
                            let var5 := addmod(var1, var4, r)
                            let var6 := 0x10000000000000000000000000000
                            let a_2_next_1 := mload(0x8600)
                            let var7 := mulmod(a_0, a_2_next_1, r)
                            let var8 := mulmod(var6, var7, r)
                            let var9 := addmod(var5, var8, r)
                            let a_1 := mload(0x8540)
                            let var10 := mulmod(a_1, a_0_next_1, r)
                            let var11 := mulmod(var2, var10, r)
                            let var12 := addmod(var9, var11, r)
                            let var13 := mulmod(a_1, a_1_next_1, r)
                            let var14 := mulmod(var6, var13, r)
                            let var15 := addmod(var12, var14, r)
                            let var16 := 0x3212e00cde6d2002b119d800000347fcb8
                            let a_6_next_1 := mload(0x87a0)
                            let var17 := mulmod(a_1, a_6_next_1, r)
                            let var18 := mulmod(var16, var17, r)
                            let var19 := addmod(var15, var18, r)
                            let a_2 := mload(0x8560)
                            let var20 := mulmod(a_2, a_0_next_1, r)
                            let var21 := mulmod(var6, var20, r)
                            let var22 := addmod(var19, var21, r)
                            let a_5_next_1 := mload(0x8780)
                            let var23 := mulmod(a_2, a_5_next_1, r)
                            let var24 := mulmod(var16, var23, r)
                            let var25 := addmod(var22, var24, r)
                            let var26 := 0x297784894e27525bc342b7fde37dba9366
                            let var27 := mulmod(a_2, a_6_next_1, r)
                            let var28 := mulmod(var26, var27, r)
                            let var29 := addmod(var25, var28, r)
                            let a_3 := mload(0x8580)
                            let a_4_next_1 := mload(0x8760)
                            let var30 := mulmod(a_3, a_4_next_1, r)
                            let var31 := mulmod(var16, var30, r)
                            let var32 := addmod(var29, var31, r)
                            let var33 := mulmod(a_3, a_5_next_1, r)
                            let var34 := mulmod(var26, var33, r)
                            let var35 := addmod(var32, var34, r)
                            let var36 := 0x340f2ebe380a0f5eff4360543988a61dc2
                            let var37 := mulmod(a_3, a_6_next_1, r)
                            let var38 := mulmod(var36, var37, r)
                            let var39 := addmod(var35, var38, r)
                            let a_4 := mload(0x85a0)
                            let a_3_next_1 := mload(0x8740)
                            let var40 := mulmod(a_4, a_3_next_1, r)
                            let var41 := mulmod(var16, var40, r)
                            let var42 := addmod(var39, var41, r)
                            let var43 := mulmod(a_4, a_4_next_1, r)
                            let var44 := mulmod(var26, var43, r)
                            let var45 := addmod(var42, var44, r)
                            let var46 := mulmod(a_4, a_5_next_1, r)
                            let var47 := mulmod(var36, var46, r)
                            let var48 := addmod(var45, var47, r)
                            let var49 := 0x13af65741744bd7bb2c6872df2b800320
                            let var50 := mulmod(a_4, a_6_next_1, r)
                            let var51 := mulmod(var49, var50, r)
                            let var52 := addmod(var48, var51, r)
                            let a_5 := mload(0x8620)
                            let var53 := mulmod(a_5, a_2_next_1, r)
                            let var54 := mulmod(var16, var53, r)
                            let var55 := addmod(var52, var54, r)
                            let var56 := mulmod(a_5, a_3_next_1, r)
                            let var57 := mulmod(var26, var56, r)
                            let var58 := addmod(var55, var57, r)
                            let var59 := mulmod(a_5, a_4_next_1, r)
                            let var60 := mulmod(var36, var59, r)
                            let var61 := addmod(var58, var60, r)
                            let var62 := mulmod(a_5, a_5_next_1, r)
                            let var63 := mulmod(var49, var62, r)
                            let var64 := addmod(var61, var63, r)
                            let var65 := 0x2cb9b546d20373eaf85e8f53db883cb548
                            let var66 := mulmod(a_5, a_6_next_1, r)
                            let var67 := mulmod(var65, var66, r)
                            let var68 := addmod(var64, var67, r)
                            let a_6 := mload(0x8640)
                            let var69 := mulmod(a_6, a_1_next_1, r)
                            let var70 := mulmod(var16, var69, r)
                            let var71 := addmod(var68, var70, r)
                            let var72 := mulmod(a_6, a_2_next_1, r)
                            let var73 := mulmod(var26, var72, r)
                            let var74 := addmod(var71, var73, r)
                            let var75 := mulmod(a_6, a_3_next_1, r)
                            let var76 := mulmod(var36, var75, r)
                            let var77 := addmod(var74, var76, r)
                            let var78 := mulmod(a_6, a_4_next_1, r)
                            let var79 := mulmod(var49, var78, r)
                            let var80 := addmod(var77, var79, r)
                            let var81 := mulmod(a_6, a_5_next_1, r)
                            let var82 := mulmod(var65, var81, r)
                            let var83 := addmod(var80, var82, r)
                            let var84 := 0xc8557e86f90d0d89eed6eb5349a0f8820
                            let var85 := mulmod(a_6, a_6_next_1, r)
                            let var86 := mulmod(var84, var85, r)
                            let var87 := addmod(var83, var86, r)
                            let var88 := mulmod(var2, a_1, r)
                            let var89 := addmod(a_0, var88, r)
                            let var90 := mulmod(var6, a_2, r)
                            let var91 := addmod(var89, var90, r)
                            let var92 := addmod(var87, var91, r)
                            let var93 := mulmod(var2, a_1_next_1, r)
                            let var94 := addmod(a_0_next_1, var93, r)
                            let var95 := mulmod(var6, a_2_next_1, r)
                            let var96 := addmod(var94, var95, r)
                            let var97 := addmod(var92, var96, r)
                            let a_7 := mload(0x8660)
                            let a_8 := mload(0x8680)
                            let var98 := mulmod(var2, a_8, r)
                            let var99 := addmod(a_7, var98, r)
                            let a_9 := mload(0x86a0)
                            let var100 := mulmod(var6, a_9, r)
                            let var101 := addmod(var99, var100, r)
                            let var102 := addmod(0, sub(r, var101), r)
                            let var103 := addmod(var97, var102, r)
                            let a_7_next_1 := mload(0x87c0)
                            let var104 := 0x241eabfffeb153ffffb9feffffffffaaab
                            let var105 := mulmod(a_7_next_1, var104, r)
                            let var106 := addmod(0, sub(r, var105), r)
                            let var107 := addmod(var103, var106, r)
                            let var108 := addmod(0, sub(r, var16), r)
                            let var109 := addmod(var107, var108, r)
                            let a_8_next_1 := mload(0x87e0)
                            let var110 := 0x73eda753299d7d483339d80809a1d80553b9202d7ffe85d4800008bb20000001
                            let var111 := addmod(a_8_next_1, var110, r)
                            let var112 := 0x4000000000000000000000000000000000
                            let var113 := mulmod(var111, var112, r)
                            let var114 := addmod(0, sub(r, var113), r)
                            let var115 := addmod(var109, var114, r)
                            let var116 := mulmod(var0, var115, r)
                            mstore(0xa960, var116)
                            }
                            mstore(0xa300, mulmod(mload(0xa300), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                            }
                        }
                        case 1 {
                            {
                            let var0 := 0x1
                            let a_0 := mload(0x8520)
                            let var1 := 0x10000000000000000000000000000
                            let var2 := addmod(a_0, var1, r)
                            let var3 := 0x100000000000000
                            let a_1 := mload(0x8540)
                            let var4 := addmod(a_1, var1, r)
                            let var5 := mulmod(var3, var4, r)
                            let var6 := addmod(var2, var5, r)
                            let a_2 := mload(0x8560)
                            let var7 := addmod(a_2, var1, r)
                            let var8 := mulmod(var1, var7, r)
                            let var9 := addmod(var6, var8, r)
                            let a_7 := mload(0x8660)
                            let a_8 := mload(0x8680)
                            let var10 := mulmod(var3, a_8, r)
                            let var11 := addmod(a_7, var10, r)
                            let a_9 := mload(0x86a0)
                            let var12 := mulmod(var1, a_9, r)
                            let var13 := addmod(var11, var12, r)
                            let var14 := addmod(0, sub(r, var13), r)
                            let var15 := addmod(var9, var14, r)
                            let var16 := addmod(0, sub(r, var1), r)
                            let var17 := addmod(var15, var16, r)
                            let a_7_next_1 := mload(0x87c0)
                            let var18 := 0x241eabfffeb153ffffb9feffffffffaaab
                            let var19 := mulmod(a_7_next_1, var18, r)
                            let var20 := addmod(0, sub(r, var19), r)
                            let var21 := addmod(var17, var20, r)
                            let var22 := 0xd9d44a30b019261257667fde3844a8cd6
                            let var23 := addmod(0, sub(r, var22), r)
                            let var24 := addmod(var21, var23, r)
                            let a_8_next_1 := mload(0x87e0)
                            let var25 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5b6e855000003ab00002
                            let var26 := addmod(a_8_next_1, var25, r)
                            let var27 := 0x4000000000000000000000000000000000
                            let var28 := mulmod(var26, var27, r)
                            let var29 := addmod(0, sub(r, var28), r)
                            let var30 := addmod(var24, var29, r)
                            let var31 := mulmod(var0, var30, r)
                            mstore(0xa960, var31)
                            }
                            mstore(0xa300, mulmod(mload(0xa300), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                            }
                        }
                        case 2 {
                            {
                            let var0 := 0x1
                            let f_0 := mload(0x8ae0)
                            let a_0_next_1 := mload(0x85c0)
                            let var1 := addmod(0, sub(r, a_0_next_1), r)
                            let var2 := addmod(f_0, var1, r)
                            let var3 := 0x1b8114c381b922fd5d6d241210e2d8a68ad5744053ba9e776118de4107b51ace
                            let a_0 := mload(0x8520)
                            let var4 := mulmod(a_0, a_0, r)
                            let a_3 := mload(0x8580)
                            let var5 := mulmod(var4, a_3, r)
                            let var6 := mulmod(var3, var5, r)
                            let var7 := addmod(var2, var6, r)
                            let var8 := 0x3df32e4cc4cb2ed20e5d21899cf5331775990ccaec4c09b4e3717213fcc0d763
                            let a_1 := mload(0x8540)
                            let var9 := mulmod(a_1, a_1, r)
                            let a_4 := mload(0x85a0)
                            let var10 := mulmod(var9, a_4, r)
                            let var11 := mulmod(var8, var10, r)
                            let var12 := addmod(var7, var11, r)
                            let var13 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                            let a_2 := mload(0x8560)
                            let var14 := mulmod(a_2, a_2, r)
                            let a_5 := mload(0x8620)
                            let var15 := mulmod(var14, a_5, r)
                            let var16 := mulmod(var13, var15, r)
                            let var17 := addmod(var12, var16, r)
                            let var18 := mulmod(var0, var17, r)
                            mstore(0xa960, var18)
                            }
                            mstore(0xa300, mulmod(mload(0xa300), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x120)
                            let q_selector_acc := mload(q_selector_ptr)
                            q_selector_acc := mulmod(q_selector_acc, mload(add(0xa340, 0x20)), r)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
                            }
                        }
                        case 3 {
                            {
                            let var0 := 0x1
                            let f_1 := mload(0x8b00)
                            let a_1_next_1 := mload(0x85e0)
                            let var1 := addmod(0, sub(r, a_1_next_1), r)
                            let var2 := addmod(f_1, var1, r)
                            let var3 := 0x404d21073985d14e432a4ad76d3fae06ca74314b950fe7b1d7f501cd31a8b374
                            let a_0 := mload(0x8520)
                            let var4 := mulmod(a_0, a_0, r)
                            let a_3 := mload(0x8580)
                            let var5 := mulmod(var4, a_3, r)
                            let var6 := mulmod(var3, var5, r)
                            let var7 := addmod(var2, var6, r)
                            let var8 := 0xb2cc8704264c6bd81bc620e9e524d4b73e9b2317679422ff7fa1603955649f1
                            let a_1 := mload(0x8540)
                            let var9 := mulmod(a_1, a_1, r)
                            let a_4 := mload(0x85a0)
                            let var10 := mulmod(var9, a_4, r)
                            let var11 := mulmod(var8, var10, r)
                            let var12 := addmod(var7, var11, r)
                            let var13 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                            let a_2 := mload(0x8560)
                            let var14 := mulmod(a_2, a_2, r)
                            let a_5 := mload(0x8620)
                            let var15 := mulmod(var14, a_5, r)
                            let var16 := mulmod(var13, var15, r)
                            let var17 := addmod(var12, var16, r)
                            let var18 := mulmod(var0, var17, r)
                            mstore(0xa960, var18)
                            }
                            mstore(0xa300, mulmod(mload(0xa300), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x120)
                            let q_selector_acc := mload(q_selector_ptr)
                            q_selector_acc := mulmod(q_selector_acc, mload(add(0xa340, 0x20)), r)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xa960), r))
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
                        mstore(0xa300, mulmod(mload(0xa300), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add(0xa340, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
                    }
                    // Invalid generated bytecode should fail closed. 0x1a intentionally lands here.
                    default {
                        revert(0, 0)
                    }
                }

                // Structured post-VM suffix. The current default uses this for
                // regular trash constraints: it is smaller than fully unrolled
                // Yul and cheaper than interpreting every trash operation.
                //
                // These generated blocks run after q_pc reaches q_end, but
                // they still participate in the same identity order and write
                // into the same numerator / selector accumulators.
                {
                let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)
                {
                let f_0 := mload(0x8ae0)
                let a_0_next_1 := mload(0x85c0)
                let var0 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
                let var1 := mulmod(a_0_next_1, var0, r)
                let var2 := addmod(f_0, var1, r)
                let var3 := 0x590ba402032e82eb1f660ef09796c5686345a5054ed96dae8e2d233633788771
                let a_0 := mload(0x8520)
                let var4 := mulmod(var3, a_0, r)
                let var5 := addmod(var2, var4, r)
                let var6 := 0x52f789e4afc3801f7411102ee2f47cc5954a744e71cac98e75ea962a55a0a76f
                let a_1 := mload(0x8540)
                let var7 := mulmod(var6, a_1, r)
                let var8 := addmod(var5, var7, r)
                let var9 := 0x3509dd2fe3aac0080783557fec090fb1cb4b2b0901253c55282024331d1fe1a8
                let a_2 := mload(0x8560)
                let var10 := q_pow5(a_2)
                let var11 := mulmod(var9, var10, r)
                let var12 := addmod(var8, var11, r)
                let var13 := 0x333f8046ece5579cbd6872449c57f2703dfc8864cfadc06d587ff104a0d0c1f2
                let a_3 := mload(0x8580)
                let var14 := q_pow5(a_3)
                let var15 := mulmod(var13, var14, r)
                let var16 := addmod(var12, var15, r)
                let var17 := 0x412c98232b6ab8a47aa76ee814ef7ec6261987c9802f2cfc490e007951a60ca5
                let a_4 := mload(0x85a0)
                let var18 := q_pow5(a_4)
                let var19 := mulmod(var17, var18, r)
                let var20 := addmod(var16, var19, r)
                let var21 := 0x53fded36d490ba6b05a5d10fd99ffe5456baec6a6a8753199d5ebdc33c99790e
                let a_5 := mload(0x8620)
                let var22 := q_pow5(a_5)
                let var23 := mulmod(var21, var22, r)
                let var24 := addmod(var20, var23, r)
                let var25 := 0x6ccb1c7d87f3c12a2bde4e68ac7f1e8b03481ba15d7f88f9a7f9b8310dd6d34
                let a_6 := mload(0x8640)
                let var26 := q_pow5(a_6)
                let var27 := mulmod(var25, var26, r)
                let var28 := addmod(var24, var27, r)
                let var29 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                let a_7 := mload(0x8660)
                let var30 := q_pow5(a_7)
                let var31 := mulmod(var29, var30, r)
                let var32 := addmod(var28, var31, r)
                let var33 := addmod(mulmod(0, q_trash_tau, r), var32, r)
                let f_1 := mload(0x8b00)
                let a_1_next_1 := mload(0x85e0)
                let var34 := mulmod(a_1_next_1, var0, r)
                let var35 := addmod(f_1, var34, r)
                let var36 := 0x5b1fc262a28cbb8bf75d9b1a6edaa74591ec24cd9a209512213cec3a3c0f1a5d
                let var37 := mulmod(var36, a_0, r)
                let var38 := addmod(var35, var37, r)
                let var39 := 0x4d0ea7f9c3fda06d9535b0fdafd8338bd47c2200b284fa71a325ff41ac358028
                let var40 := mulmod(var39, a_1, r)
                let var41 := addmod(var38, var40, r)
                let var42 := 0x26cc223e16f47c20e17cc6069605fa5a8af05ea4f6eb36029a641d23b818eb10
                let var43 := mulmod(var42, var10, r)
                let var44 := addmod(var41, var43, r)
                let var45 := 0x31e823a45e567484c1544e310c0fa5cd66547a8f0dde659ac61698c30e838d25
                let var46 := mulmod(var45, var14, r)
                let var47 := addmod(var44, var46, r)
                let var48 := 0x275a20361ea91992193920270d3e2d1f6361880ac0a439c64bef815d4469ba85
                let var49 := mulmod(var48, var18, r)
                let var50 := addmod(var47, var49, r)
                let var51 := 0x5f3a15bab4ce4097b1edc3a25002694b92395ce355a8a12fe557459d9633f701
                let var52 := mulmod(var51, var22, r)
                let var53 := addmod(var50, var52, r)
                let var54 := 0x301cf56f9b4577112cc4241cddf6484aaadedbf1bbd0f2351adf2e41c2fb2ecd
                let var55 := mulmod(var54, var26, r)
                let var56 := addmod(var53, var55, r)
                let var57 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                let var58 := mulmod(var57, var30, r)
                let var59 := addmod(var56, var58, r)
                let var60 := addmod(mulmod(var33, q_trash_tau, r), var59, r)
                let f_2 := mload(0x8b20)
                let var61 := mulmod(a_3, var0, r)
                let var62 := addmod(f_2, var61, r)
                let var63 := 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140
                let var64 := mulmod(var63, a_0, r)
                let var65 := addmod(var62, var64, r)
                let var66 := 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a
                let var67 := mulmod(var66, a_1, r)
                let var68 := addmod(var65, var67, r)
                let var69 := 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db
                let var70 := mulmod(var69, var10, r)
                let var71 := addmod(var68, var70, r)
                let var72 := addmod(mulmod(var60, q_trash_tau, r), var71, r)
                let f_3 := mload(0x8b40)
                let var73 := mulmod(a_4, var0, r)
                let var74 := addmod(f_3, var73, r)
                let var75 := 0x222e83e70453dfee19b402e9fa8dfe2c4987b034d0be3ceb478b3022e97934c1
                let var76 := mulmod(var75, a_0, r)
                let var77 := addmod(var74, var76, r)
                let var78 := 0x26c2cc87f95726b28f33ca03409a460ec987cfe12adae32769e3565865d07191
                let var79 := mulmod(var78, a_1, r)
                let var80 := addmod(var77, var79, r)
                let var81 := 0x4382d0938a760120dd6cef8f3b90a0c38abae475e3d21e39365472b76d780272
                let var82 := mulmod(var81, var10, r)
                let var83 := addmod(var80, var82, r)
                let var84 := mulmod(var69, var14, r)
                let var85 := addmod(var83, var84, r)
                let var86 := addmod(mulmod(var72, q_trash_tau, r), var85, r)
                let f_4 := mload(0x8a40)
                let var87 := mulmod(a_5, var0, r)
                let var88 := addmod(f_4, var87, r)
                let var89 := 0x726df1506749848155630b86ae25a82b281ecd050fe3a52d85a181fa87202e4b
                let var90 := mulmod(var89, a_0, r)
                let var91 := addmod(var88, var90, r)
                let var92 := 0x24822e1af9aa2887c912c87eb0f20bd332330e7e55cd784de67cb407a9f05520
                let var93 := mulmod(var92, a_1, r)
                let var94 := addmod(var91, var93, r)
                let var95 := 0x4e5280109d8f96b8bfb543a6b1af25fb56a9db616af85a90eedc558e3eb1ea29
                let var96 := mulmod(var95, var10, r)
                let var97 := addmod(var94, var96, r)
                let var98 := mulmod(var81, var14, r)
                let var99 := addmod(var97, var98, r)
                let var100 := mulmod(var69, var18, r)
                let var101 := addmod(var99, var100, r)
                let var102 := addmod(mulmod(var86, q_trash_tau, r), var101, r)
                let f_5 := mload(0x8a60)
                let var103 := mulmod(a_6, var0, r)
                let var104 := addmod(f_5, var103, r)
                let var105 := 0x2f5908b169c6cf1bd26dcf0f9e5105481f5164f3ece0582bf3098312167751a7
                let var106 := mulmod(var105, a_0, r)
                let var107 := addmod(var104, var106, r)
                let var108 := 0x23a6684b942d726a22e4d5b8d8ff83aeaa773f62600184efe5d033d7c7c6e827
                let var109 := mulmod(var108, a_1, r)
                let var110 := addmod(var107, var109, r)
                let var111 := 0x1981b4b33d6a9dab957b351d981d3323e65da39493af5bc01f7e8ffe17f98d4e
                let var112 := mulmod(var111, var10, r)
                let var113 := addmod(var110, var112, r)
                let var114 := mulmod(var95, var14, r)
                let var115 := addmod(var113, var114, r)
                let var116 := mulmod(var81, var18, r)
                let var117 := addmod(var115, var116, r)
                let var118 := mulmod(var69, var22, r)
                let var119 := addmod(var117, var118, r)
                let var120 := addmod(mulmod(var102, q_trash_tau, r), var119, r)
                let f_6 := mload(0x8a80)
                let var121 := mulmod(a_7, var0, r)
                let var122 := addmod(f_6, var121, r)
                let var123 := 0x6d05a41959f539a7fc9ec0972ea1e3dbb6fc67dd51daf3414f7fbbb091c7274a
                let var124 := mulmod(var123, a_0, r)
                let var125 := addmod(var122, var124, r)
                let var126 := 0x27e7119226c42a6d19c1541904b99ae40685511ed2e078964b74594d38340849
                let var127 := mulmod(var126, a_1, r)
                let var128 := addmod(var125, var127, r)
                let var129 := 0xd94c46a8456352aa44d7a885ab59e3a36664e6fb25e826f8a4cd79822f0533
                let var130 := mulmod(var129, var10, r)
                let var131 := addmod(var128, var130, r)
                let var132 := mulmod(var111, var14, r)
                let var133 := addmod(var131, var132, r)
                let var134 := mulmod(var95, var18, r)
                let var135 := addmod(var133, var134, r)
                let var136 := mulmod(var81, var22, r)
                let var137 := addmod(var135, var136, r)
                let var138 := mulmod(var69, var26, r)
                let var139 := addmod(var137, var138, r)
                let var140 := addmod(mulmod(var120, q_trash_tau, r), var139, r)
                let f_7 := mload(0x8aa0)
                let a_2_next_1 := mload(0x8600)
                let var141 := mulmod(a_2_next_1, var0, r)
                let var142 := addmod(f_7, var141, r)
                let var143 := 0x70d8f2a733a64d650faccc9b1c2a766a9544bb3ff1a11ee73cb43947ef386633
                let var144 := mulmod(var143, a_0, r)
                let var145 := addmod(var142, var144, r)
                let var146 := 0x40fa389feb2522bb934881ac9ed749aee2296502af592418c6b5675c0f560261
                let var147 := mulmod(var146, a_1, r)
                let var148 := addmod(var145, var147, r)
                let var149 := 0x1f61345b652161410c5e29f51e301ae56342af824bc110649393d2b911c50d3e
                let var150 := mulmod(var149, var10, r)
                let var151 := addmod(var148, var150, r)
                let var152 := mulmod(var129, var14, r)
                let var153 := addmod(var151, var152, r)
                let var154 := mulmod(var111, var18, r)
                let var155 := addmod(var153, var154, r)
                let var156 := mulmod(var95, var22, r)
                let var157 := addmod(var155, var156, r)
                let var158 := mulmod(var81, var26, r)
                let var159 := addmod(var157, var158, r)
                let var160 := mulmod(var69, var30, r)
                let var161 := addmod(var159, var160, r)
                let var162 := addmod(mulmod(var140, q_trash_tau, r), var161, r)
                let f_26 := mload(0x8c20)
                let q_trash_one_minus_selector := addmod(1, sub(r, f_26), r)
                let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0x91a0), r)
                let q_trash_eval := addmod(var162, sub(r, q_trash_scaled), r)
                mstore(0xa300, mulmod(mload(0xa300), y, r))
                mstore(0xa300, addmod(mload(0xa300), q_trash_eval, r))
                }
                }
                // Finish selector buckets by applying the codegen-known tail
                // from each selector's last identity to the end of the global
                // y-batch.
                //
                // After this step, every selector bucket is aligned with the
                // final global y position and can be multiplied by its fixed
                // selector commitment in the linearized MSM.
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x00)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0600)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x05e0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0580)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0520)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x04c0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xa0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0460)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xc0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0400)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xe0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x03a0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0100)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0340)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0120)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xa340, 0x0280)), r))
                }

                // Fully evaluated identities are the constant-polynomial side
                // of the linearization query. Rust subtracts that grouped
                // scalar into expected_eval, so Solidity stores -nu_y(x).
                let linearization_expected_eval := addmod(0, sub(r, mload(0xa300)), r)
                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)
                pop(y)
            }
            gas_checkpoint(12) // after batched identity numerator reconstruction

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
                let k := 20
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
            gas_checkpoint(13) // after linearization scalar prep

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
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(add(ROT_POINTS_MPTR, 0x0), x_pow_of_omega)
                }
                gas_checkpoint(17) // after PCS sub-block 1
                // Generated PCS sub-block 2. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // pre-compute 43 x1 power(s)
                    let x1 := mload(X1_MPTR)
                    mstore(X1_POWERS_MPTR, 1)
                    let acc := 1
                    let p := X1_POWERS_MPTR
                    for { let i := 0 } lt(i, 0x2a) { i := add(i, 1) } {
                        p := add(p, 0x20)
                        acc := mulmod(acc, x1, r)
                        mstore(p, and(acc, 0xffffffffffffffffffffffffffffffff))
                    }
                }
                gas_checkpoint(18) // after PCS sub-block 2
                // Generated PCS sub-block 3. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[0]: 43 commitment(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xa300, 0x8a00)
                    mstore(0xa320, 0x8500)
                    mstore(0xa340, 0x90a0)
                    mstore(0xa360, 0x90c0)
                    mstore(0xa380, 0x9120)
                    mstore(0xa3a0, 0x9140)
                    mstore(0xa3c0, 0x91a0)
                    mstore(0xa3e0, 0x8a20)
                    mstore(0xa400, 0x8a40)
                    mstore(0xa420, 0x8a60)
                    mstore(0xa440, 0x8a80)
                    mstore(0xa460, 0x8aa0)
                    mstore(0xa480, 0x8ac0)
                    mstore(0xa4a0, 0x8ae0)
                    mstore(0xa4c0, 0x8b00)
                    mstore(0xa4e0, 0x8b20)
                    mstore(0xa500, 0x8b40)
                    mstore(0xa520, 0x8b60)
                    mstore(0xa540, 0x8b80)
                    mstore(0xa560, 0x8ba0)
                    mstore(0xa580, 0x8bc0)
                    mstore(0xa5a0, 0x8be0)
                    mstore(0xa5c0, 0x8c00)
                    mstore(0xa5e0, 0x8c20)
                    mstore(0xa600, 0x8c40)
                    mstore(0xa620, 0x8c60)
                    mstore(0xa640, 0x8c80)
                    mstore(0xa660, 0x8ca0)
                    mstore(0xa680, 0x8cc0)
                    mstore(0xa6a0, 0x8ce0)
                    mstore(0xa6c0, 0x8d00)
                    mstore(0xa6e0, 0x8d20)
                    mstore(0xa700, 0x8d40)
                    mstore(0xa720, 0x8d60)
                    mstore(0xa740, 0x8d80)
                    mstore(0xa760, 0x8da0)
                    mstore(0xa780, 0x8dc0)
                    mstore(0xa7a0, 0x8de0)
                    mstore(0xa7c0, 0x8e00)
                    mstore(0xa7e0, 0x8e20)
                    mstore(0xa800, 0x8e40)
                    mstore(0xa820, 0x8e60)
                    mstore(0xa840, QUOTIENT_EVAL_MPTR)
                    let q_eval_set_0 := mload(0x8a00)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xa300, 0x20)
                    for { let i := 1 } lt(i, 0x2b) { i := add(i, 1) } {
                        let pow := mload(pow_p)
                        q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)
                        pow_p := add(pow_p, 0x20)
                        eval_p := add(eval_p, 0x20)
                    }
                    mstore(add(Q_EVAL_SET_MPTR, 0x0), q_eval_set_0)
                }
                gas_checkpoint(19) // after PCS sub-block 3
                // Generated PCS sub-block 4. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[1]: 3 commitment(s)
                    let q_eval_set_0 := mload(0x86e0)
                    let q_eval_set_1 := mload(0x89a0)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x8700), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x89c0), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x8720), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x89e0), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0x20), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x40), q_eval_set_1)
                }
                gas_checkpoint(20) // after PCS sub-block 4
                // Generated PCS sub-block 5. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[2]: 3 commitment(s)
                    let q_eval_set_0 := mload(0x9060)
                    let q_eval_set_1 := mload(0x9080)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x90e0), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x9100), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x9160), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x9180), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0x60), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x80), q_eval_set_1)
                }
                gas_checkpoint(21) // after PCS sub-block 5
                // Generated PCS sub-block 6. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[3]: 11 commitment(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xa300, 0x8520)
                    mstore(0xa320, 0x85c0)
                    mstore(0xa340, 0x8840)
                    mstore(0xa360, 0x8540)
                    mstore(0xa380, 0x85e0)
                    mstore(0xa3a0, 0x8860)
                    mstore(0xa3c0, 0x8560)
                    mstore(0xa3e0, 0x8600)
                    mstore(0xa400, 0x8880)
                    mstore(0xa420, 0x8580)
                    mstore(0xa440, 0x8740)
                    mstore(0xa460, 0x88a0)
                    mstore(0xa480, 0x85a0)
                    mstore(0xa4a0, 0x8760)
                    mstore(0xa4c0, 0x88c0)
                    mstore(0xa4e0, 0x8620)
                    mstore(0xa500, 0x8780)
                    mstore(0xa520, 0x88e0)
                    mstore(0xa540, 0x8640)
                    mstore(0xa560, 0x87a0)
                    mstore(0xa580, 0x8900)
                    mstore(0xa5a0, 0x8660)
                    mstore(0xa5c0, 0x87c0)
                    mstore(0xa5e0, 0x8920)
                    mstore(0xa600, 0x8680)
                    mstore(0xa620, 0x87e0)
                    mstore(0xa640, 0x8940)
                    mstore(0xa660, 0x86a0)
                    mstore(0xa680, 0x8800)
                    mstore(0xa6a0, 0x8960)
                    mstore(0xa6c0, 0x86c0)
                    mstore(0xa6e0, 0x8820)
                    mstore(0xa700, 0x8980)
                    let q_eval_set_0 := mload(0x8520)
                    let q_eval_set_1 := mload(0x85c0)
                    let q_eval_set_2 := mload(0x8840)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xa300, 0x60)
                    for { let i := 1 } lt(i, 0xb) { i := add(i, 1) } {
                        let pow := mload(pow_p)
                        q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)
                        q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(mload(add(eval_p, 0x20))), pow, r), r)
                        q_eval_set_2 := addmod(q_eval_set_2, mulmod(mload(mload(add(eval_p, 0x40))), pow, r), r)
                        pow_p := add(pow_p, 0x20)
                        eval_p := add(eval_p, 0x60)
                    }
                    mstore(add(Q_EVAL_SET_MPTR, 0xa0), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0xc0), q_eval_set_1)
                    mstore(add(Q_EVAL_SET_MPTR, 0xe0), q_eval_set_2)
                }
                gas_checkpoint(22) // after PCS sub-block 6
                // Generated PCS sub-block 7. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[4]: 5 commitment(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xa300, 0x8e80)
                    mstore(0xa320, 0x8ea0)
                    mstore(0xa340, 0x8ec0)
                    mstore(0xa360, 0x8ee0)
                    mstore(0xa380, 0x8f00)
                    mstore(0xa3a0, 0x8f20)
                    mstore(0xa3c0, 0x8f40)
                    mstore(0xa3e0, 0x8f60)
                    mstore(0xa400, 0x8f80)
                    mstore(0xa420, 0x8fa0)
                    mstore(0xa440, 0x8fc0)
                    mstore(0xa460, 0x8fe0)
                    mstore(0xa480, 0x9000)
                    mstore(0xa4a0, 0x9020)
                    mstore(0xa4c0, 0x9040)
                    let q_eval_set_0 := mload(0x8e80)
                    let q_eval_set_1 := mload(0x8ea0)
                    let q_eval_set_2 := mload(0x8ec0)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xa300, 0x60)
                    for { let i := 1 } lt(i, 0x5) { i := add(i, 1) } {
                        let pow := mload(pow_p)
                        q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(mload(eval_p)), pow, r), r)
                        q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(mload(add(eval_p, 0x20))), pow, r), r)
                        q_eval_set_2 := addmod(q_eval_set_2, mulmod(mload(mload(add(eval_p, 0x40))), pow, r), r)
                        pow_p := add(pow_p, 0x20)
                        eval_p := add(eval_p, 0x60)
                    }
                    mstore(add(Q_EVAL_SET_MPTR, 0x100), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x120), q_eval_set_1)
                    mstore(add(Q_EVAL_SET_MPTR, 0x140), q_eval_set_2)
                }
                gas_checkpoint(23) // after PCS sub-block 7
                // Generated PCS sub-block 8. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // f_eval via Horner over 5 reversed set(s)
                    let x2 := mload(X2_MPTR)
                    let x3 := mload(X3_MPTR)
                    let f_eval := 0
                    let Q_EVAL_CPTR := mload(Q_EVAL_CPTR_MPTR)
                    let rot_pt_0 := mload(add(ROT_POINTS_MPTR, 0x0))
                    let rot_pt_1 := mload(add(ROT_POINTS_MPTR, 0x20))
                    let rot_pt_2 := mload(add(ROT_POINTS_MPTR, 0x40))
                    let rot_pt_3 := mload(add(ROT_POINTS_MPTR, 0x60))
                    // --- set 4 (cardinality 3) ---
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
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x80)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x100)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x120)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    let term_2 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x140)), dx_inv_2, r), lbasis_inv_2, r)
                    eval := addmod(eval, sub(r, term_2), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 3 (cardinality 3) ---
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
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x60)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xa0)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xc0)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    let term_2 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0xe0)), dx_inv_2, r), lbasis_inv_2, r)
                    eval := addmod(eval, sub(r, term_2), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 2 (cardinality 2) ---
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
                    let eval := mulmod(calldataload(add(Q_EVAL_CPTR, 0x40)), den_inv, r)
                    let term_0 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x60)), dx_inv_0, r), lbasis_inv_0, r)
                    eval := addmod(eval, sub(r, term_0), r)
                    let term_1 := mulmod(mulmod(mload(add(Q_EVAL_SET_MPTR, 0x80)), dx_inv_1, r), lbasis_inv_1, r)
                    eval := addmod(eval, sub(r, term_1), r)
                    f_eval := addmod(mulmod(f_eval, x2, r), eval, r)
                    }
                    // --- set 1 (cardinality 2) ---
                    {
                    let dx_0 := addmod(x3, sub(r, rot_pt_2), r)
                    let dx_1 := addmod(x3, sub(r, rot_pt_1), r)
                    let lbasis_0 := 1
                    lbasis_0 := mulmod(lbasis_0, addmod(rot_pt_2, sub(r, rot_pt_1), r), r)
                    let lbasis_1 := 1
                    lbasis_1 := mulmod(lbasis_1, addmod(rot_pt_1, sub(r, rot_pt_2), r), r)
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
                gas_checkpoint(24) // after PCS sub-block 8
                // Generated PCS sub-block 9. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // build final_com and v (KZG single-opening proof, fused MSM)
                    // final MSM input length from circuit/VK shape: 78 term(s)
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
                    x4_pow_full := mulmod(x4_pow_full, x4, r)
                    let x4_pow_5 := and(x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                    let v := calldataload(Q_EVAL_CPTR)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x20)), x4_pow_1, r), r)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x40)), x4_pow_2, r), r)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x60)), x4_pow_3, r), r)
                    v := addmod(v, mulmod(calldataload(add(Q_EVAL_CPTR, 0x80)), x4_pow_4, r), r)
                    v := addmod(v, mulmod(mload(F_EVAL_MPTR), x4_pow_5, r), r)
                    mcopy(0xa300, 0x98c0, 0x80)
                    mstore(0xa380, 1)
                    mcopy(0xa3a0, 0x9940, 0x80)
                    mstore(0xa420, mload(add(X1_POWERS_MPTR, 0x40)))
                    mcopy(0xa440, 0x9d40, 0x80)
                    mstore(0xa4c0, mload(add(X1_POWERS_MPTR, 0x60)))
                    mcopy(0xa4e0, 0x99c0, 0x80)
                    mstore(0xa560, mload(add(X1_POWERS_MPTR, 0x80)))
                    mcopy(0xa580, 0x9dc0, 0x80)
                    mstore(0xa600, mload(add(X1_POWERS_MPTR, 0xa0)))
                    mcopy(0xa620, 0x9f40, 0x80)
                    mstore(0xa6a0, mload(add(X1_POWERS_MPTR, 0xc0)))
                    mcopy(0xa6c0, 0x5780, 0x80)
                    mstore(0xa740, mload(add(X1_POWERS_MPTR, 0xe0)))
                    mcopy(0xa760, 0x5500, 0x80)
                    mstore(0xa7e0, mload(add(X1_POWERS_MPTR, 0x100)))
                    mcopy(0xa800, 0x5580, 0x80)
                    mstore(0xa880, mload(add(X1_POWERS_MPTR, 0x120)))
                    mcopy(0xa8a0, 0x5600, 0x80)
                    mstore(0xa920, mload(add(X1_POWERS_MPTR, 0x140)))
                    mcopy(0xa940, 0x5680, 0x80)
                    mstore(0xa9c0, mload(add(X1_POWERS_MPTR, 0x160)))
                    mcopy(0xa9e0, 0x5700, 0x80)
                    mstore(0xaa60, mload(add(X1_POWERS_MPTR, 0x180)))
                    mcopy(0xaa80, 0x5300, 0x80)
                    mstore(0xab00, mload(add(X1_POWERS_MPTR, 0x1a0)))
                    mcopy(0xab20, 0x5380, 0x80)
                    mstore(0xaba0, mload(add(X1_POWERS_MPTR, 0x1c0)))
                    mcopy(0xabc0, 0x5400, 0x80)
                    mstore(0xac40, mload(add(X1_POWERS_MPTR, 0x1e0)))
                    mcopy(0xac60, 0x5480, 0x80)
                    mstore(0xace0, mload(add(X1_POWERS_MPTR, 0x200)))
                    mcopy(0xad00, 0x5800, 0x80)
                    mstore(0xad80, mload(add(X1_POWERS_MPTR, 0x220)))
                    mcopy(0xada0, 0x5880, 0x80)
                    mstore(0xae20, mload(add(X1_POWERS_MPTR, 0x240)))
                    mcopy(0xae40, 0x5900, 0x80)
                    mstore(0xaec0, mload(add(X1_POWERS_MPTR, 0x260)))
                    mcopy(0xaee0, 0x5980, 0x80)
                    mstore(0xaf60, mload(add(X1_POWERS_MPTR, 0x280)))
                    mcopy(0xaf80, 0x5b80, 0x80)
                    mstore(0xb000, mload(add(X1_POWERS_MPTR, 0x2a0)))
                    mcopy(0xb020, 0x5f00, 0x80)
                    mstore(0xb0a0, mload(add(X1_POWERS_MPTR, 0x2c0)))
                    mcopy(0xb0c0, 0x6000, 0x80)
                    mstore(0xb140, mload(add(X1_POWERS_MPTR, 0x2e0)))
                    mcopy(0xb160, 0x6080, 0x80)
                    mstore(0xb1e0, mload(add(X1_POWERS_MPTR, 0x300)))
                    mcopy(0xb200, 0x6100, 0x80)
                    mstore(0xb280, mload(add(X1_POWERS_MPTR, 0x320)))
                    mcopy(0xb2a0, 0x6180, 0x80)
                    mstore(0xb320, mload(add(X1_POWERS_MPTR, 0x340)))
                    mcopy(0xb340, 0x6200, 0x80)
                    mstore(0xb3c0, mload(add(X1_POWERS_MPTR, 0x360)))
                    mcopy(0xb3e0, 0x6280, 0x80)
                    mstore(0xb460, mload(add(X1_POWERS_MPTR, 0x380)))
                    mcopy(0xb480, 0x6300, 0x80)
                    mstore(0xb500, mload(add(X1_POWERS_MPTR, 0x3a0)))
                    mcopy(0xb520, 0x6380, 0x80)
                    mstore(0xb5a0, mload(add(X1_POWERS_MPTR, 0x3c0)))
                    mcopy(0xb5c0, 0x6400, 0x80)
                    mstore(0xb640, mload(add(X1_POWERS_MPTR, 0x3e0)))
                    mcopy(0xb660, 0x6480, 0x80)
                    mstore(0xb6e0, mload(add(X1_POWERS_MPTR, 0x400)))
                    mcopy(0xb700, 0x6500, 0x80)
                    mstore(0xb780, mload(add(X1_POWERS_MPTR, 0x420)))
                    mcopy(0xb7a0, 0x6580, 0x80)
                    mstore(0xb820, mload(add(X1_POWERS_MPTR, 0x440)))
                    mcopy(0xb840, 0x6600, 0x80)
                    mstore(0xb8c0, mload(add(X1_POWERS_MPTR, 0x460)))
                    mcopy(0xb8e0, 0x6680, 0x80)
                    mstore(0xb960, mload(add(X1_POWERS_MPTR, 0x480)))
                    mcopy(0xb980, 0x6700, 0x80)
                    mstore(0xba00, mload(add(X1_POWERS_MPTR, 0x4a0)))
                    mcopy(0xba20, 0x6780, 0x80)
                    mstore(0xbaa0, mload(add(X1_POWERS_MPTR, 0x4c0)))
                    mcopy(0xbac0, 0x6800, 0x80)
                    mstore(0xbb40, mload(add(X1_POWERS_MPTR, 0x4e0)))
                    mcopy(0xbb60, 0x6880, 0x80)
                    mstore(0xbbe0, mload(add(X1_POWERS_MPTR, 0x500)))
                    mcopy(0xbc00, 0x6900, 0x80)
                    mstore(0xbc80, mload(add(X1_POWERS_MPTR, 0x520)))
                    let lin_query_scalar_41 := mload(add(X1_POWERS_MPTR, 0x540))
                    let lin_cur_scalar_41 := mulmod(lin_query_scalar_41, lin_one_minus_x_n, r)
                    mcopy(0xbca0, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x0), 0x80)
                    mstore(0xbd20, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xbd40, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x80), 0x80)
                    mstore(0xbdc0, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xbde0, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x100), 0x80)
                    mstore(0xbe60, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xbe80, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x180), 0x80)
                    mstore(0xbf00, lin_cur_scalar_41)
                    mcopy(0xbf20, 0x5a00, 0x80)
                    mstore(0xbfa0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x0)), r))
                    mcopy(0xbfc0, 0x5a80, 0x80)
                    mstore(0xc040, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x20)), r))
                    mcopy(0xc060, 0x5b00, 0x80)
                    mstore(0xc0e0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x40)), r))
                    mcopy(0xc100, 0x5c00, 0x80)
                    mstore(0xc180, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x60)), r))
                    mcopy(0xc1a0, 0x5c80, 0x80)
                    mstore(0xc220, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x80)), r))
                    mcopy(0xc240, 0x5d00, 0x80)
                    mstore(0xc2c0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xa0)), r))
                    mcopy(0xc2e0, 0x5d80, 0x80)
                    mstore(0xc360, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xc0)), r))
                    mcopy(0xc380, 0x5e00, 0x80)
                    mstore(0xc400, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xe0)), r))
                    mcopy(0xc420, 0x5e80, 0x80)
                    mstore(0xc4a0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x100)), r))
                    mcopy(0xc4c0, 0x5f80, 0x80)
                    mstore(0xc540, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x120)), r))
                    mcopy(0xc560, 0x9740, 0x80)
                    mstore(0xc5e0, x4_pow_1)
                    mcopy(0xc600, 0x97c0, 0x80)
                    mstore(0xc680, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_1, r))
                    mcopy(0xc6a0, 0x9840, 0x80)
                    mstore(0xc720, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_1, r))
                    mcopy(0xc740, 0x9cc0, 0x80)
                    mstore(0xc7c0, x4_pow_2)
                    mcopy(0xc7e0, 0x9e40, 0x80)
                    mstore(0xc860, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_2, r))
                    mcopy(0xc880, 0x9ec0, 0x80)
                    mstore(0xc900, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_2, r))
                    mcopy(0xc920, 0x91c0, 0x80)
                    mstore(0xc9a0, x4_pow_3)
                    mcopy(0xc9c0, 0x9240, 0x80)
                    mstore(0xca40, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_3, r))
                    mcopy(0xca60, 0x92c0, 0x80)
                    mstore(0xcae0, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_3, r))
                    mcopy(0xcb00, 0x9340, 0x80)
                    mstore(0xcb80, mulmod(mload(add(X1_POWERS_MPTR, 0x60)), x4_pow_3, r))
                    mcopy(0xcba0, 0x93c0, 0x80)
                    mstore(0xcc20, mulmod(mload(add(X1_POWERS_MPTR, 0x80)), x4_pow_3, r))
                    mcopy(0xcc40, 0x9440, 0x80)
                    mstore(0xccc0, mulmod(mload(add(X1_POWERS_MPTR, 0xa0)), x4_pow_3, r))
                    mcopy(0xcce0, 0x94c0, 0x80)
                    mstore(0xcd60, mulmod(mload(add(X1_POWERS_MPTR, 0xc0)), x4_pow_3, r))
                    mcopy(0xcd80, 0x9540, 0x80)
                    mstore(0xce00, mulmod(mload(add(X1_POWERS_MPTR, 0xe0)), x4_pow_3, r))
                    mcopy(0xce20, 0x95c0, 0x80)
                    mstore(0xcea0, mulmod(mload(add(X1_POWERS_MPTR, 0x100)), x4_pow_3, r))
                    mcopy(0xcec0, 0x9640, 0x80)
                    mstore(0xcf40, mulmod(mload(add(X1_POWERS_MPTR, 0x120)), x4_pow_3, r))
                    mcopy(0xcf60, 0x96c0, 0x80)
                    mstore(0xcfe0, mulmod(mload(add(X1_POWERS_MPTR, 0x140)), x4_pow_3, r))
                    mcopy(0xd000, 0x9a40, 0x80)
                    mstore(0xd080, x4_pow_4)
                    mcopy(0xd0a0, 0x9ac0, 0x80)
                    mstore(0xd120, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_4, r))
                    mcopy(0xd140, 0x9b40, 0x80)
                    mstore(0xd1c0, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_4, r))
                    mcopy(0xd1e0, 0x9bc0, 0x80)
                    mstore(0xd260, mulmod(mload(add(X1_POWERS_MPTR, 0x60)), x4_pow_4, r))
                    mcopy(0xd280, 0x9c40, 0x80)
                    mstore(0xd300, mulmod(mload(add(X1_POWERS_MPTR, 0x80)), x4_pow_4, r))
                    mcopy(0xd320, F_COM_MPTR, 0x80)
                    mstore(0xd3a0, x4_pow_5)
                    if success {
                        success := staticcall(575096, 0x0c, 0xa300, 0x30c0, FINAL_COM_MPTR, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mstore(V_MPTR, v)
                }
                gas_checkpoint(25) // after PCS sub-block 9
                // Generated PCS sub-block 10. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // Scale z*pi - vG before the final pairing check
                    // pairing inputs (LHS = pi; RHS = final_com - v*G + x3*pi)
                    mcopy(PAIRING_LHS_MPTR, PI_MPTR, 0x80)
                    mcopy(0x80, G1_BASE_MPTR, 0x80)
                    mstore(0x100, addmod(0, sub(r, mload(V_MPTR)), r))
                    if success {
                        success := staticcall(62000, 0x0c, 0x80, 0xa0, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x100, FINAL_COM_MPTR, 0x80)
                    if success {
                        success := staticcall(50000, 0x0b, 0x80, 0x100, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x100, PI_MPTR, 0x80)
                    mstore(0x180, mload(X3_MPTR))
                    if success {
                        success := staticcall(62000, 0x0c, 0x100, 0xa0, 0x100, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    if success {
                        success := staticcall(50000, 0x0b, 0x80, 0x100, 0x80, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(PAIRING_RHS_MPTR, 0x80, 0x80)
                }
            }
            gas_checkpoint(14) // after PCS computation block (= sub-block 6)

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
            {
                let batch_ptr := 0x0100

                // Domain || KZG rhs/lhs || accumulator rhs/lhs.
                mstore(batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
                mcopy(add(batch_ptr, 0x20),  PAIRING_RHS_MPTR, 0x80)
                mcopy(add(batch_ptr, 0xa0),  PAIRING_LHS_MPTR, 0x80)
                mcopy(add(batch_ptr, 0x0120), ACC_RHS_MPTR,     0x80)
                mcopy(add(batch_ptr, 0x01a0), ACC_LHS_MPTR,     0x80)
                // alpha is Fiat-Shamir over the fully materialized pairing
                // inputs. Replace the negligible zero draw with one so the
                // accumulator equation cannot be accidentally dropped.
                let acc_pair_alpha := mod(keccak256(batch_ptr, 0x0220), r)
                if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }

                // PAIRING_RHS_MPTR += alpha * ACC_RHS_MPTR.
                // First compute alpha * ACC_RHS with a one-pair G1MSM, then
                // add it into the KZG RHS point.
                mcopy(batch_ptr, ACC_RHS_MPTR, 0x80)
                mstore(add(batch_ptr, 0x80), acc_pair_alpha)
                if success {
                    success := staticcall(62000, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
                mcopy(add(batch_ptr, 0x80), PAIRING_RHS_MPTR, 0x80)
                if success {
                    success := staticcall(50000, 0x0b, batch_ptr, 0x0100, PAIRING_RHS_MPTR, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }

                // PAIRING_LHS_MPTR += alpha * ACC_LHS_MPTR.
                // Mirror the same randomized batching on the KZG LHS point.
                mcopy(batch_ptr, ACC_LHS_MPTR, 0x80)
                mstore(add(batch_ptr, 0x80), acc_pair_alpha)
                if success {
                    success := staticcall(62000, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
                mcopy(add(batch_ptr, 0x80), PAIRING_LHS_MPTR, 0x80)
                if success {
                    success := staticcall(50000, 0x0b, batch_ptr, 0x0100, PAIRING_LHS_MPTR, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
            }
            gas_checkpoint(15) // after public accumulator pairing batch prep (omitted for no-accumulator VKs)

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
            gas_checkpoint(16) // after final ec_pairing

    

            // Success path is terminal. Invalid inputs have already reverted,
            // so the Solidity ABI observes `true`.
            mstore(RETURN_MPTR, 1)
            return(RETURN_MPTR, 0x20)
        }
    }
}