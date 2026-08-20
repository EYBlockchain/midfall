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

    
    /// @notice Verifying-key contract address authorized for this verifier.
    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.
    address public immutable AUTHORIZED_VK;
    // Expected VK runtime metadata. The deployed VK runtime is
    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than
    // EXPECTED_VK_PAYLOAD_LENGTH.
    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = 17024;
    uint256 internal constant EXPECTED_VK_LENGTH = 17025;
    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = 0x67bac137fa7e479c25b63324812752e4b6e13d9841d5bf83c322170bf91c0f88;
    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);
    /// @notice Quotient evaluator contract authorized for split quotient reconstruction.
    /// @dev The evaluator returns the linearization expected scalar and selector buckets; its runtime is pinned by generated constants.
    address public immutable AUTHORIZED_QUOTIENT;
    // Expected split evaluator runtime metadata. It is checked at deployment
    // and again immediately before each external quotient reconstruction.
    uint256 internal constant EXPECTED_QUOTIENT_LENGTH = 9848;
    uint256 internal constant EXPECTED_QUOTIENT_CODEHASH_WORD = 0x38aa196503a12b7256a838dc03ea4ef1cae518f9c0ad5151c1c5b887de4d5ce3;
    bytes32 internal constant EXPECTED_QUOTIENT_CODEHASH = bytes32(EXPECTED_QUOTIENT_CODEHASH_WORD);

    // Solidity ABI calldata cursors. The generated verifier accepts exactly
    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`
    // bytes itself in the same order as the Rust verifier transcript.
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x1ec4;
    uint256 internal constant     INSTANCE_CPTR = 0x1ee4;
    // First general-purpose memory words reserved by the generated verifier.
    // RETURN_MPTR is a single word set to 1 on success.
    uint256 internal constant    TRANSCRIPT_MPTR = 0x1000;
    uint256 internal constant        RETURN_MPTR = 0x1000;

    // ----------------------------------------------------------------------
    // Verifying-key memory map. The VK header lives at VK_MPTR, followed
    // by the quotient VM payload and commitments. After the full VK
    // runtime comes the challenge slots (challenge_mptr..) and the
    // per-stage scratch (theta_mptr..).
    // ----------------------------------------------------------------------
    uint256 internal constant                VK_MPTR = 0x3680;
    uint256 internal constant         VK_DIGEST_MPTR = 0x3680;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x36a0;
    uint256 internal constant                 K_MPTR = 0x36c0;
    uint256 internal constant             N_INV_MPTR = 0x36e0;
    uint256 internal constant             OMEGA_MPTR = 0x3700;
    uint256 internal constant         OMEGA_INV_MPTR = 0x3720;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x3740;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x3760;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x3780;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x37a0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x37c0;
    uint256 internal constant            G1_BASE_MPTR = 0x37e0;
    uint256 internal constant            G2_BASE_MPTR = 0x3860;
    uint256 internal constant      NEG_S_G2_BASE_MPTR = 0x3960;

    uint256 internal constant CHALLENGE_MPTR = 0x7900;

    // Challenge layout. Squeeze order in midnight-proofs:
    //   user_phase challenges (variable count)
    //   theta -> beta, gamma -> trash_challenge -> y -> x ->
    //   x1, x2 -> x3 -> x4
    uint256 internal constant            THETA_MPTR = 0x7900;
    uint256 internal constant             BETA_MPTR = 0x7920;
    uint256 internal constant            GAMMA_MPTR = 0x7940;
    uint256 internal constant TRASH_CHALLENGE_MPTR = 0x7960;
    uint256 internal constant                Y_MPTR = 0x7980;
    uint256 internal constant                X_MPTR = 0x79a0;
    uint256 internal constant               X1_MPTR = 0x79c0;
    uint256 internal constant               X2_MPTR = 0x79e0;
    uint256 internal constant               X3_MPTR = 0x7a00;
    uint256 internal constant               X4_MPTR = 0x7a20;

    // Batch-open commitments live in 4-word EIP-2537 padded slots.
    uint256 internal constant             F_COM_MPTR = 0x7a40;
    uint256 internal constant                PI_MPTR = 0x7ac0;

    // Accumulator (KZG IVC).
    uint256 internal constant          ACC_LHS_MPTR = 0x7b40;
    uint256 internal constant          ACC_RHS_MPTR = 0x7bc0;

    // Lagrange / linearization scratch.
    uint256 internal constant              X_N_MPTR = 0x7c40;
    uint256 internal constant  X_N_MINUS_1_INV_MPTR = 0x7c60;
    uint256 internal constant           L_LAST_MPTR = 0x7c80;
    uint256 internal constant          L_BLIND_MPTR = 0x7ca0;
    uint256 internal constant              L_0_MPTR = 0x7cc0;
    uint256 internal constant     INSTANCE_EVAL_MPTR = 0x7ce0;
    // Legacy name: this is not h(x). It stores the expected opening
    // scalar for the linearized commitment, i.e. the negated y-batched
    // identity numerator reconstructed from the alleged evals at x.
    uint256 internal constant     QUOTIENT_EVAL_MPTR = 0x7d00;
    uint256 internal constant         QUOTIENT_MPTR = 0x7d20;   // 4 words
    uint256 internal constant            F_EVAL_MPTR = 0x7dc0;
    uint256 internal constant                 V_MPTR = 0x7de0;
    uint256 internal constant         FINAL_COM_MPTR = 0x7e00;   // 4 words
    uint256 internal constant      PAIRING_LHS_MPTR = 0x7e80;   // 4 words
    uint256 internal constant      PAIRING_RHS_MPTR = 0x7f00;   // 4 words

    // Multi-prepare scratch (sized at codegen time).
    uint256 internal constant       ROT_POINTS_MPTR = 0x7f80;
    uint256 internal constant       X1_POWERS_MPTR = 0x8300;
    // Q_COM materialization is currently fused into the final MSM scratch,
    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero
    // reserved capacity until a future emitter starts writing Q_COM_MPTR.
    uint256 internal constant            Q_COM_MPTR = 0x8b20;
    uint256 internal constant      Q_EVAL_SET_MPTR = 0x8b20;

    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals
    // block of the proof; we keep it as a memory slot for symmetry.
    uint256 internal constant         Q_EVAL_CPTR_MPTR = 0x9220;

    // Reserved 4-word slot for the G1 identity (point at infinity) in
    // EIP-2537 padded form. EVM memory is zero-initialised, and the verifier
    // never writes to this region, so any read of this slot (the PCS
    // emitters `mcopy` from it when staging identity commitments) yields
    // 0,0,0,0 -- exactly the identity encoding the EIP-2537 precompiles
    // accept. Artifacts whose PCS plan never stages an identity commitment
    // still emit the constant; it costs no runtime bytes beyond the
    // declaration and keeps the emitters' pointer model uniform.
    uint256 internal constant       G1_IDENTITY_MPTR = 0x9320;

    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain
    // Solidity proof shim rewrites proof scalars into canonical BE words,
    // so `calldataload` gives the field element directly. The transcript-
    // side `evaluations` loop range-checks and spills that value here so
    // downstream eval references (gate evaluator + PCS q_eval Horner)
    // become 3-gas `mload(...)` instead of calldata reads.
    uint256 internal constant     REVERSED_EVALS_MPTR = 0x9480;
    uint256 internal constant      SELECTOR_ACC_MPTR = 0xb140;
    uint256 internal constant   QUOTIENT_RETURN_MPTR = 0x1000;
    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = 0xb140;
    // Lagrange batch-inversion input run: denominators, in-place inverses,
    // then Lagrange values, consumed and distilled into the named theta
    // slots by the Lagrange block. Planner-registered phase scratch.
    uint256 internal constant    LAGRANGE_DENOMS_MPTR = 0xb4e0;
    uint256 internal constant        TRACE_U256_MPTR = 0xe340;

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
    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = 0xa140;
    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = 0xa8c0;
    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = 0xa9c0;
    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = 0xacc0;
    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = 0xadc0;
    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = 0xaec0;
    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = 0xaf40;

    // ----------------------------------------------------------------------
    // Precompile gas bounds: the scheduled EIP-2537 costs, and for modexp the
    // maximum over the EIP-2565 and EIP-7883 schedules.
    //
    // A failing EIP-2537 or modexp call consumes ALL gas supplied to the
    // STATICCALL, so every generated call site forwards the exact scheduled
    // cost instead of gas(). A malformed proof point then burns at most the
    // scheduled cost of the single failing call instead of 63/64 of the
    // transaction budget. The schedule is the spec-guaranteed worst case
    // (EIP-2537 "DDoS protection" rationale), so these bounds are sufficient
    // by construction on any conformant chain.
    //
    // MODEXP_GAS covers both live modexp schedules: EIP-2565 prices this
    // frame at 1360, EIP-7883 (Osaka/Fusaka) removes the /3 divisor and
    // prices it at 4080, so the larger bound is rendered. Forwarding the
    // EIP-7883 bound on a pre-Osaka chain is free on success -- unused gas is
    // returned -- while forwarding the EIP-2565 bound on a repriced chain
    // reverts every proof.
    //
    // Liveness caveat: if a future fork reprices these precompiles above the
    // bounds below, this verifier must be regenerated and redeployed. The
    // constructor smoke probes forward the same bounds for EVERY precompile
    // the runtime calls, modexp included, so deployment onto an
    // already-repriced chain fails fast instead of bricking at proof time.
    // ----------------------------------------------------------------------
    uint256 internal constant          G1ADD_GAS = 375;
    uint256 internal constant   G1MSM_GAS_1PAIR = 12000;
    uint256 internal constant PAIRING_GAS_2PAIR = 102900;
    uint256 internal constant        MODEXP_GAS = 4080;
    // Exact cost of the deployment-time worst-case G1MSM smoke probe.
    uint256 internal constant G1MSM_GAS_SMOKE = 525096;
    // Worst-case accumulator RHS MSM: carried RHS point plus every generated
    // fixed-base tail scalar nonzero. Zero tail scalars are omitted at
    // runtime, which only lowers the actual cost below this bound.
    uint256 internal constant ACC_RHS_MSM_GAS = 12000;

    /// @notice Build identity for this generated artifact (P10/L-8).
    /// @dev keccak256 over: the domain tag "halo2-solidity-verifier-build-v1",
    ///      the u64-length-prefixed generator feature profile, the vk_digest,
    ///      the expected VK runtime codehash (zero when the VK is embedded),
    ///      the SRS fingerprint keccak("halo2-solidity-verifier-srs-v1" || n
    ///      || G2 || s_g2 || [tau]G1), and an optional 32-byte deployment
    ///      provenance tag (0x00 marker when absent, 0x01 || tag when set).
    ///      The deployment record must publish these preimage components so
    ///      third parties can recompute the id; see
    ///      docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md.
    bytes32 public constant BUILD_ID = 0xcac63429fbd8833ae32ee2fa8d63109cdae7e99b8487af78c539f1cabf58cc22;

    // ----------------------------------------------------------------------
    // Typed-error selectors (P4/L-3): bytes4(keccak256("Name()")) of the
    // errors declared on the contract, as Yul-readable constants. The
    // `fail(sel)` helper in AssemblyHelpers.yul writes the selector to
    // scratch 0x00 and reverts with 4 bytes. Pinned by
    // `p4_error_selectors_match_declared_errors` in src/lowering/tests.rs.
    // ----------------------------------------------------------------------
    uint256 internal constant ERR_BAD_CALLDATA_SHAPE      = 0x1b99e37c;
    uint256 internal constant ERR_VK_MISMATCH             = 0xa447d73e;
    uint256 internal constant ERR_NON_CANONICAL_SCALAR    = 0x77530042;
    uint256 internal constant ERR_BAD_POINT_ENCODING      = 0xf27905ec;
    uint256 internal constant ERR_PRECOMPILE_FAILED       = 0x84e81692;
    uint256 internal constant ERR_PROOF_REJECTED          = 0xc3b0d8cd;
    uint256 internal constant ERR_QUOTIENT_PROGRAM_INVALID = 0x3cc81b89;
    uint256 internal constant ERR_MEMORY_LAYOUT_VIOLATED   = 0xc9888d23;

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

        /// @notice Smoke-check the Cancun/EIP-2537/modexp runtime features required by the verifier.
    /// @dev Exercises MCOPY, modexp, and EIP-2537 inputs to catch incompatible chain/fork configurations at deployment.
    ///      The probes forward the same exact gas bounds the runtime uses, for
    ///      every precompile it calls -- 0x05 modexp included (see the
    ///      gas-bound constants block) -- so a chain whose precompile schedule
    ///      was repriced above those bounds fails here, at deployment, instead
    ///      of bricking verifyProof later.
    function require_eip2537_precompiles() private view {
        // __phase:constructor_smoke
        assembly ("memory-safe") {
            // Same free-memory-pointer guard as verifyProof. This body runs in
            // the *creation* frame, which the generator's memoryguard test does
            // not inspect (it parses the runtime prologue only).
            //
            // MF-2: typed like the runtime guard, and for a stronger reason.
            // The runtime guard turns a bad recompile into a revert on every
            // proof; this one turns it into a failed DEPLOYMENT, which is
            // where a build fault belongs. The probes below keep bare reverts
            // (a chain-capability failure, not a build fault).
            if gt(mload(0x40), 0x1000) {
                mstore(0x00, shl(224, ERR_MEMORY_LAYOUT_VIOLATED))
                revert(0x00, 0x04)
            }

            // Scratch is reused for every runtime-prerequisite probe.
            let scratch := 0x1000

            // MCOPY must be available because the verifier uses it for
            // proof-time point/scratch staging. Execute the opcode here so a
            // non-Cancun fork fails during deployment instead of later proofs.
            mstore(scratch, 0x1234)
            mcopy(add(scratch, 0x20), scratch, 0x20)
            if iszero(eq(mload(add(scratch, 0x20)), 0x1234)) { revert(0, 0) }

            // ----------------------------------------------------------------
            // modexp (0x05) known-answer probe at the pinned runtime bound.
            //
            // MF-1: every other precompile the runtime calls was probed here,
            // but modexp -- which the MANDATORY Lagrange batch inversion and
            // every scalar_inv call depend on -- was not. Two live schedules
            // price this frame differently (EIP-2565: 1360, EIP-7883: 4080),
            // and a bound below the chain's price does not degrade: the
            // staticcall forwards a fixed amount, the precompile OOGs, and
            // EVERY proof reverts PrecompileFailed. Without this probe that
            // failure is invisible until the first verifyProof call, on a
            // contract that deployed cleanly.
            //
            // The vector is the runtime's own operation -- Fermat inversion
            // in Fr -- so it exercises the exact frame shape, exponent width,
            // and gas bound used at proof time: 2^(FR_MODULUS - 2) == 2^-1.
            // Checking mulmod(result, 2, FR_MODULUS) == 1 rather than a
            // rendered constant keeps the probe self-contained while still
            // rejecting a stub: a precompile returning zeros (or its input)
            // fails, since 0 * 2 != 1 mod r.
            // ----------------------------------------------------------------
            mstore(add(scratch, 0x00), 0x20)        // base len
            mstore(add(scratch, 0x20), 0x20)        // exp len
            mstore(add(scratch, 0x40), 0x20)        // mod len
            mstore(add(scratch, 0x60), 2)
            mstore(add(scratch, 0x80), sub(FR_MODULUS, 2))
            mstore(add(scratch, 0xa0), FR_MODULUS)
            if iszero(staticcall(MODEXP_GAS, 0x05, scratch, 0xc0, scratch, 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(eq(mulmod(mload(scratch), 2, FR_MODULUS), 1)) { revert(0, 0) }

            // Start the EIP-2537 probes with the identity encoding for G1/G2:
            // all-zero padded words. This also clears the modexp frame above.
            for { let off := 0 } lt(off, 0x0300) { off := add(off, 0x20) } {
                mstore(add(scratch, off), 0)
            }

            // G1ADD(identity, identity) -> identity, 128-byte return.
            // This catches chains where the precompile is missing or returns a
            // non-standard success shape.
            if iszero(staticcall(G1ADD_GAS, 0x0b, scratch, 0x0100, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // Known-answer probe: G1ADD(G, G) == 2G.
            //
            // Every probe above uses the point at infinity, which is exactly
            // the input an implementation gets right without doing any curve
            // arithmetic -- a precompile that returns its zero-filled input, or
            // zeros for anything, satisfies them. The identity is also the one
            // input on which an implementation that omits the EIP-2537 subgroup
            // check still answers correctly, and the production verifier leans
            // on G1MSM as its subgroup validator for absorbed commitments. So
            // add one vector whose answer a stub cannot guess.
            mstore(add(scratch, 0x00), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(add(scratch, 0x20), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(add(scratch, 0x40), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(add(scratch, 0x60), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
            mcopy(add(scratch, 0x80), scratch, 0x80)
            if iszero(staticcall(G1ADD_GAS, 0x0b, scratch, 0x0100, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if iszero(and(
                and(
                    eq(mload(add(scratch, 0x00)), 0x000000000000000000000000000000000572cbea904d67468808c8eb50a9450c),
                    eq(mload(add(scratch, 0x20)), 0x9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e)
                ),
                and(
                    eq(mload(add(scratch, 0x40)), 0x00000000000000000000000000000000166a9d8cabc673a322fda673779d8e38),
                    eq(mload(add(scratch, 0x60)), 0x22ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28)
                )
            )) { revert(0, 0) }


            // ----------------------------------------------------------------
            // Known-answer probes for the two precompiles that actually decide
            // acceptance.
            //
            // Every probe above this point uses the point at infinity or a
            // G1ADD vector. That leaves the two precompiles the verifier's
            // security actually rests on untested for *rejection* behaviour:
            //   - 0x0c G1MSM is the curve/subgroup validator for every absorbed
            //     proof commitment (common_uncompressed_g1 runs no curve check);
            //   - 0x0f PAIRING_CHECK is the sole accept gate, so a chain whose
            //     0x0f always returns 1 accepts every proof.
            // These four probes cost deployment gas only.
            // ----------------------------------------------------------------

            // (a) G1MSM known answer: [2]*G == 2G.
            mstore(add(scratch, 0x00), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(add(scratch, 0x20), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(add(scratch, 0x40), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(add(scratch, 0x60), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
            mstore(add(scratch, 0x80), 2)
            if iszero(staticcall(G1MSM_GAS_1PAIR, 0x0c, scratch, 0xa0, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if iszero(and(
                and(
                    eq(mload(add(scratch, 0x00)), 0x000000000000000000000000000000000572cbea904d67468808c8eb50a9450c),
                    eq(mload(add(scratch, 0x20)), 0x9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e)
                ),
                and(
                    eq(mload(add(scratch, 0x40)), 0x00000000000000000000000000000000166a9d8cabc673a322fda673779d8e38),
                    eq(mload(add(scratch, 0x60)), 0x22ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28)
                )
            )) { revert(0, 0) }

            // (b) G1MSM negative probe. (4, y) satisfies y^2 = x^3 + 4 over Fp
            // but is NOT in the r-order subgroup (checked off-chain: r*P != O).
            // EIP-2537 requires G1MSM to reject it. This is the one property
            // the verifier's deferred-validation strategy depends on and the
            // one property no other probe exercises.
            //
            // Gas is bounded on purpose: a precompile that rejects its input
            // consumes everything forwarded to it, so an unbounded `gas()` here
            // would burn 63/64 of the deployment gas before the probes below.
            mstore(add(scratch, 0x00), 0x0000000000000000000000000000000000000000000000000000000000000000)
            mstore(add(scratch, 0x20), 0x0000000000000000000000000000000000000000000000000000000000000004)
            mstore(add(scratch, 0x40), 0x000000000000000000000000000000000a989badd40d6212b33cffc3f3763e9b)
            mstore(add(scratch, 0x60), 0xc760f988c9926b26da9dd85e928483446346b8ed00e1de5d5ea93e354abe706c)
            mstore(add(scratch, 0x80), 1)
            if staticcall(200000, 0x0c, scratch, 0xa0, scratch, 0x80) { revert(0, 0) }

            // (c)+(d) Pairing known answers. Lay out [G1 | G2 | G1' | G2] once:
            // with G1' = -G the product is 1, with G1' = +G it is not. G2 is
            // written literally because the VK payload is not loaded during
            // construction.
            mstore(add(scratch, 0x000), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(add(scratch, 0x020), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(add(scratch, 0x040), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(add(scratch, 0x060), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
            mstore(add(scratch, 0x080), 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)
            mstore(add(scratch, 0x0a0), 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)
            mstore(add(scratch, 0x0c0), 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)
            mstore(add(scratch, 0x0e0), 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
            mstore(add(scratch, 0x100), 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)
            mstore(add(scratch, 0x120), 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)
            mstore(add(scratch, 0x140), 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)
            mstore(add(scratch, 0x160), 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
            mstore(add(scratch, 0x180), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
            mstore(add(scratch, 0x1a0), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
            mstore(add(scratch, 0x1c0), 0x00000000000000000000000000000000114d1d6855d545a8aa7d76c8cf2e21f2)
            mstore(add(scratch, 0x1e0), 0x67816aef1db507c96655b9d5caac42364e6f38ba0ecb751bad54dcd6b939c2ca)
            mcopy(add(scratch, 0x200), add(scratch, 0x80), 0x100)

            // (c) e(G, G2) * e(-G, G2) == 1.
            if iszero(staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, add(scratch, 0x300), 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(eq(mload(add(scratch, 0x300)), 1)) { revert(0, 0) }

            // (d) e(G, G2) * e(G, G2) != 1. Flip the second G1 back to +G.
            mstore(add(scratch, 0x1c0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(add(scratch, 0x1e0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
            if iszero(staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, add(scratch, 0x300), 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(iszero(mload(add(scratch, 0x300)))) { revert(0, 0) }

            // Restore the identity encoding for the probes below.
            for { let off := 0 } lt(off, 0x0300) { off := add(off, 0x20) } {
                mstore(add(scratch, off), 0)
            }

            // Worst-case generated G1MSM with all identity/zero terms ->
            // identity, 128-byte return. This exercises the largest MSM input
            // LENGTH rendered by this verifier instead of only a one-pair
            // smoke call, proving the target chain's precompile accepts the
            // full-size input. It runs in the creation frame at its own
            // scratch base, so it does not (and cannot) pre-expand the
            // runtime call frame's memory -- constructor memory is discarded;
            // only the input size coverage carries over.
            let msm_scratch := 0xb140
            for { let off := 0 } lt(off, 0x30c0) { off := add(off, 0x20) } {
                mstore(add(msm_scratch, off), 0)
            }
            // The production verifier uses G1MSM both for commitments and as
            // the subgroup validator for absorbed proof points.
            if iszero(staticcall(G1MSM_GAS_SMOKE, 0x0c, msm_scratch, 0x30c0, scratch, 0x80)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // PAIRING_CHECK([(identity_g1, identity_g2), (identity_g1, identity_g2)])
            // -> true, 32-byte return. This matches the runtime two-pair KZG
            // pairing input size and catches absent pairing precompiles,
            // short return data, and obviously incompatible semantics.
            if iszero(staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, scratch, 0x20)) { revert(0, 0) }
            if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
        }
    }

    
    /// @notice Create a verifier pinned to a verifying key and quotient evaluator.
    /// @dev Checks MCOPY/EIP-2537 availability and verifies both dependency runtimes before storing their addresses.
    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.
    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.
    constructor(address authorizedVk, address authorizedQuotient) {
        // Verifier correctness depends on chain support for MCOPY and the
        // BLS12-381 precompiles; fail deployment before pinning dependencies.
        require_eip2537_precompiles();
        // Pin the generated VK runtime exactly. The verifier later repeats the
        // codehash/length check before copying the VK payload for a proof.
        require(
            authorizedVk.code.length == EXPECTED_VK_LENGTH
                && authorizedVk.codehash == EXPECTED_VK_CODEHASH,
            "invalid vk"
        );
        // The split evaluator contains generated verifier logic, not a generic
        // library. Pin it with the same strictness as the verifying key.
        require(
            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH
                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,
            "invalid quotient"
        );
        // Store the already-validated dependency addresses for proof-time
        // memory loading and quotient reconstruction.
        AUTHORIZED_VK = authorizedVk;
        AUTHORIZED_QUOTIENT = authorizedQuotient;
    }

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
                // BadCalldataShape() -- fail() is not in scope in this early
                // guard block, so write the selector inline.
                mstore(0x00, shl(224, ERR_BAD_CALLDATA_SHAPE))
                revert(0x00, 0x04)
            }
        }
        // Non-embedded renders pin the VK by address and codehash. The Yul
        // loader rechecks the runtime before every proof and copies the
        // INVALID-prefixed payload into VK_MPTR.
        address vk = AUTHORIZED_VK;
        // Split quotient renders delegate the scalar-side identity numerator
        // reconstruction to a separately deployed generated evaluator.
        address quotientEvaluator = AUTHORIZED_QUOTIENT;
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
            // MF-12: by the letter of Solidity's memory-safety contract this
            // annotation is a lie -- the block writes memory it never
            // allocated through the free-memory pointer. Three properties
            // make it safe HERE, and all three must hold together: this
            // block is terminal (no Solidity executes after it), the pragma
            // is pinned so codegen cannot shift underneath it, and the guard
            // below fails closed if the spill reservation ever reaches the
            // generated layout. Lifting this body into a non-terminal
            // context, or unpinning the pragma, invalidates the annotation.
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

                // Revert with a 4-byte custom-error selector (P4/L-3). Writing at
            // 0x00 is Solidity's legal scratch space and never touches the
            // generated layout, which starts at TRANSCRIPT_MPTR.
            function fail(sel) {
                mstore(0x00, shl(224, sel))
                revert(0x00, 0x04)
            }

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
                if iszero(lt(x, FR_MODULUS)) { fail(ERR_NON_CANONICAL_SCALAR) }
                if iszero(x) { fail(ERR_NON_CANONICAL_SCALAR) }
                let p := 0x3580
                // EIP-198 modexp frame:
                //   [base_len, exp_len, mod_len, base, exponent, modulus]
                mstore(add(p, 0x00), 0x20)        // base len
                mstore(add(p, 0x20), 0x20)        // exp len
                mstore(add(p, 0x40), 0x20)        // mod len
                mstore(add(p, 0x60), x)
                mstore(add(p, 0x80), sub(FR_MODULUS, 2))
                mstore(add(p, 0xa0), FR_MODULUS)
                if iszero(staticcall(MODEXP_GAS, 0x05, p, 0xc0, p, 0x20)) { fail(ERR_PRECOMPILE_FAILED) }
                if iszero(eq(returndatasize(), 0x20)) { fail(ERR_PRECOMPILE_FAILED) }
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
                if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
                if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }

                let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)
                let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)
                if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
                    fail(ERR_BAD_POINT_ENCODING)
                }
                if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
                    fail(ERR_BAD_POINT_ENCODING)
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
            //
            // MF-4: the second return value separates a FAILED PRECOMPILE
            // (staticcall reverted / OOG'd / returned the wrong size -- a
            // chain or gas-schedule fault) from a REJECTED INPUT (a zero or
            // non-canonical denominator, which for the Lagrange batch means
            // the squeezed x landed on a domain point). Both fail closed at
            // the section boundary, but they are different incidents and used
            // to surface under the same PrecompileFailed selector, pointing
            // responders at the node when the transcript was the cause.
            function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret, precompile_failed {
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
                    ret := staticcall(MODEXP_GAS, 0x05, single_scratch, 0xc0, single_scratch, 0x20)
                    ret := and(ret, eq(returndatasize(), 0x20))
                    precompile_failed := iszero(ret)
                    if ret { mstore(mptr_start, mload(single_scratch)) }
                    leave
                }

                // Forward pass: scratch stores prefix products up to, but not
                // including, the final element. `gp` becomes the total product.
                //
                // Match the single-element path: reject non-canonical words
                // (x >= r) instead of letting mulmod reduce them silently, so
                // accept/reject semantics do not depend on batch length.
                let gp_mptr := scratch_mptr
                let gp := mload(mptr_start)
                if iszero(lt(gp, r)) {
                    ret := 0
                    leave
                }
                let mptr := add(mptr_start, 0x20)
                for {} lt(mptr, sub(mptr_end, 0x20)) {} {
                    let x := mload(mptr)
                    if iszero(lt(x, r)) {
                        ret := 0
                        leave
                    }
                    gp := mulmod(gp, x, r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                let x_last := mload(mptr)
                if iszero(lt(x_last, r)) {
                    ret := 0
                    leave
                }
                gp := mulmod(gp, x_last, r)
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
                ret := staticcall(MODEXP_GAS, 0x05, gp_mptr, 0xc0, gp_mptr, 0x20)
                ret := and(ret, eq(returndatasize(), 0x20))
                precompile_failed := iszero(ret)
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
                if iszero(ret) { fail(ERR_PROOF_REJECTED) }
                // Lay out two (G1, G2) pairs at scratch..scratch+0x300:
                //   [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)]
                // Cancun MCOPY (3 + 3·words gas) replaces what used to
                // be a 4-step mstore chain for each G1 (~60 gas) and an
                // 8-iter mstore loop for each G2 (~240 gas). Net saving
                // here is ~500 gas per ec_pairing call.
                let scratch := 0x1240
                mcopy(scratch,              lhs_mptr,                 0x80)
                mcopy(add(scratch, 0x80),   G2_BASE_MPTR,             0x100)
                mcopy(add(scratch, 0x180),  rhs_mptr,                 0x80)
                mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)
                // MF-4: separate "the chain could not run the pairing" from
                // "the pairing ran and rejected this proof". Both fail closed,
                // but they are different incidents: the first points at the
                // node/fork (a missing, repriced, or short-returning
                // precompile), the second at the proof. Collapsing them into
                // ProofRejected sent every responder looking at the wrong one.
                ret := staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, scratch, 0x20)
                ret := and(ret, eq(returndatasize(), 0x20))
                if iszero(ret) { fail(ERR_PRECOMPILE_FAILED) }
                // Compare against 1 rather than truncating to the low bit:
                // `and(ret, word)` would accept any odd result word. EIP-2537
                // only ever returns 0 or 1, so this matches the strict form
                // the constructor smoke test already uses.
                ret := eq(mload(scratch), 1)
                if iszero(ret) { fail(ERR_PROOF_REJECTED) }
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
                    // `and` here is bitwise, so it must not be fed the raw
                    // `first_adjust` (a radix base, i.e. a high power of two):
                    // `iszero(...)` is 0 or 1 and shares no bit with it, which
                    // would make the guard false for every call. Subtracting is
                    // already a no-op when `first_adjust` is zero, so gate on
                    // the word index alone.
                    if iszero(div(i, limbs_per_word)) {
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
                        //
                        // Unreachable by construction (audit I-2/I-3): the
                        // whole-point sentinel check above already accepted
                        // every encoding in which x carries the identity flag
                        // -- the packed codec is a bijection, so an x flagged
                        // as identity with a sentinel mismatch cannot decode
                        // here. Kept as defence in depth for future codec
                        // changes rather than as a live branch.
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
            // `r` is consumed only by the canonicality guards in the
            // carried-scalar and fixed-base-tail arms; renders whose
            // accumulator layout has neither (e.g. point_pair with no tail)
            // legally leave it unused.
            // MF-4: `precompile_failed` separates a G1MSM staticcall that
            // could not run (chain/gas fault) from a public-input point this
            // verifier decoded and rejected (bad packing, out-of-field
            // coordinate, non-canonical identity encoding, or a point the
            // precompile found off-curve/out-of-subgroup). Both fail closed at
            // the call site; only the second is a BadPointEncoding.
            function validate_public_accumulator(success, r) -> out, precompile_failed {
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
                let acc_instance_ptr := add(INSTANCE_CPTR, 0x80)

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
                let acc_scratch := 0xb140
                {
                    // Carried-scalar layout: the circuit exposes the scalar
                    // that multiplies the carried LHS point.
                    let lhs_scalar := calldataload(lhs_scalar_ptr)
                    // Canonicality is enforced here rather than relying on the
                    // later instance-absorption loop: G1MSM reduces scalars
                    // mod r implicitly, so s and s+r would be indistinguishable
                    // inside this helper.
                    out := and(out, lt(lhs_scalar, r))
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
                        out := staticcall(G1MSM_GAS_1PAIR, 0x0c, acc_scratch, 0xa0, ACC_LHS_MPTR, 0x80)
                        out := and(out, eq(returndatasize(), 0x80))
                        precompile_failed := iszero(out)
                    }
                }
                // RHS layout for this generated verifier is fully collapsed:
                // point limbs (x,y), scalar. There is no fixed-base scalar
                // tail; fixed-base contributions were already folded into
                // ACC_RHS by the circuit/native accumulator construction.
                let rhs_instance_ptr := add(lhs_scalar_ptr, 0x20)
                // RHS scalar, when present, immediately follows the RHS point
                // limbs. The fixed-base scalar tail starts after it.
                let rhs_scalar_ptr := add(rhs_instance_ptr, mul(mul(2, coord_words), 0x20))
                let rhs_ok, rhs_is_id := load_acc_point(ACC_RHS_MPTR, rhs_instance_ptr, bits, n, limb_base)
                out := and(out, rhs_ok)
                // acc_pair_ptr appends (G1, scalar) pairs into acc_scratch for
                // one final RHS MSM.
                let acc_pair_ptr := acc_scratch
                {
                    // Explicit carried RHS scalar.
                    let rhs_scalar := calldataload(rhs_scalar_ptr)
                    out := and(out, lt(rhs_scalar, r))
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
                        // ACC_RHS_MSM_GAS is the compile-time worst case
                        // (every tail scalar nonzero); acc_msm_len can only
                        // select a same-size-or-smaller MSM at runtime.
                        out := staticcall(
                            ACC_RHS_MSM_GAS,
                            0x0c,
                            acc_scratch,
                            acc_msm_len,
                            ACC_RHS_MPTR,
                            0x80
                        )
                        out := and(out, eq(returndatasize(), 0x80))
                        precompile_failed := iszero(out)
                    }
                }
                // The caller checks `out` and reverts before transcript work if
                // any decode, canonicality, or precompile validation failed.
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
                )) { fail(ERR_VK_MISMATCH) }
                // Runtime byte 0 is INVALID so direct calls cannot execute the
                // payload. Copy from byte 1 into VK_MPTR to reconstruct the
                // exact payload layout used by the embedded branch.
                extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)

                // Cross-check loaded VK header words against the verifier
                // constants used by later parser, domain, and accumulator
                // paths. Codehash pinning protects the external VK address;
                // these checks catch generator drift before calldata parsing
                // chooses a stale schema.
                success := and(success, eq(mload(NUM_INSTANCES_MPTR), 14))
                success := and(success, eq(mload(K_MPTR), 20))
                success := and(success, eq(mload(HAS_ACCUMULATOR_MPTR), 1))
                success := and(success, eq(mload(ACC_OFFSET_MPTR), 4))
                success := and(success, eq(mload(NUM_ACC_LIMBS_MPTR), 7))
                success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), 56))
                if iszero(success) { fail(ERR_VK_MISMATCH) }
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
                success := and(success, eq(14, calldataload(NUM_INSTANCE_CPTR)))
                // Calldata must contain exactly the ABI selector, proof bytes,
                // instance-array length, and generated number of instance
                // words. Any trailing bytes fail closed.
                success := and(
                    success,
                    eq(calldatasize(), add(INSTANCE_CPTR, 0x01c0))
                )
                // Stop before any transcript absorption if the ABI/proof shape
                // is not exactly the generated one.
                if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }
            }
            // __phase:accumulator_msm
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
            let acc_precompile_failed := 0
            success, acc_precompile_failed := validate_public_accumulator(success, r)
            if iszero(success) {
                // MF-4: a G1MSM that could not run at all is a chain fault,
                // not a malformed accumulator point.
                if acc_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
                fail(ERR_BAD_POINT_ENCODING)
            }

                // __phase:transcript
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
                buf_len := common_word(buf_len, 14)

                let instance_cptr := INSTANCE_CPTR
                for { let instance_cptr_end := add(instance_cptr, 0x01c0) }
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
                if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }
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
            for { let end := add(proof_cptr, 0x0780) }
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
            for { let end := add(proof_cptr, 0x0300) }
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
                for { let end := add(proof_cptr, 0x0cc0) }
                    lt(proof_cptr, end)
                    {} {
                    let eval := calldataload(proof_cptr)
                    // Proof evaluation scalars must be canonical Fr elements
                    // before they are absorbed or made available to quotient
                    // reconstruction.
                    if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
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
                if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
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
            if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }

            // `success` carries deferred canonicality failures from public
            // instance reads. G1/proof scalar helpers revert immediately.
            if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }

                // __phase:lagrange_batch_invert
            // ===============================================================
            // Lagrange & instance-evaluation block (pure Fr arithmetic).
            // ===============================================================
            // MF-4: hoisted so the section boundary below can tell a failed
            // modexp (chain fault) from a rejected denominator (x landed on a
            // domain point) instead of reporting both as PrecompileFailed.
            let lagrange_precompile_failed := 0
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
                // modexp call. The run lives in the dedicated planner-registered
                // LAGRANGE_DENOMS_MPTR scratch region; only the distilled
                // results below are persisted into the named theta slots.
                let mptr := LAGRANGE_DENOMS_MPTR
                let mptr_end := add(mptr, 0x0300)
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success, lagrange_precompile_failed := batch_invert(success, LAGRANGE_DENOMS_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)

                // Convert inverted denominators into Lagrange evaluations:
                // L_i(x) = (x^n - 1) * n^-1 * omega_i / (x - omega_i).
                mptr := LAGRANGE_DENOMS_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                // l_blind is the sum of the negative-rotation Lagrange terms
                // used by the midnight-proofs blinding identity.
                let l_blind := mload(add(LAGRANGE_DENOMS_MPTR, 0x20))
                let l_i_cptr := add(LAGRANGE_DENOMS_MPTR, 0x40)
                for { let l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, 0x0140) }
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
                        let instance_cptr_end := add(instance_cptr, 0x01c0)
                    }
                    lt(instance_cptr, instance_cptr_end)
                    { instance_cptr := add(instance_cptr, 0x20)
                      l_i_cptr := add(l_i_cptr, 0x20) } {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                // Persist the derived values into named memory slots consumed
                // by quotient reconstruction and PCS preparation.
                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(LAGRANGE_DENOMS_MPTR)
                let l_0 := mload(add(LAGRANGE_DENOMS_MPTR, 0x0140))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            if iszero(success) {
                // A zero or non-canonical denominator is a rejected input,
                // not a broken chain: the only way to reach it is a squeezed
                // x that coincides with a domain point (probability ~n/r).
                if lagrange_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
                fail(ERR_PROOF_REJECTED)
            }

    
            // ===============================================================
            // External batched identity numerator reconstruction.
            //
            // The quotient evaluator receives the verifier memory image from
            // QUOTIENT_FRAME_BASE..+QUOTIENT_FRAME_LEN, reconstructs the same
            // y-batched numerator, and returns:
            //   word 0: magic/version
            //   word 1: linearization expected eval
            //   word 2..: simple-selector accumulators
            // ===============================================================
            {
                let q_out := QUOTIENT_RETURN_MPTR
                // The quotient evaluator is as correctness-critical as the VK:
                // it reconstructs the y-batched identity numerator and
                // selector buckets. Re-check the pinned runtime before every
                // external call, mirroring the VK freshness guard above.
                if iszero(and(
                    eq(extcodesize(quotientEvaluator), EXPECTED_QUOTIENT_LENGTH),
                    eq(extcodehash(quotientEvaluator), EXPECTED_QUOTIENT_CODEHASH_WORD)
                )) { fail(ERR_VK_MISMATCH) }
                // gas() forwarding is deliberate here, unlike the precompile
                // call sites: this is a regular contract call, so a reverting
                // or failing callee refunds its unused gas -- only precompile
                // ERRORS burn everything forwarded (EIP-2537). The callee is
                // also pinned by codehash above, not attacker-supplied.
                if iszero(staticcall(gas(), quotientEvaluator, 0x3680, 0x6ac0, q_out, 0x0180)) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                if iszero(eq(returndatasize(), 0x0180)) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                if iszero(eq(mload(q_out), 0x00000000000000000000000000000000000000000000000051554556414c0001)) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                // Word 1 is the negated y-batched identity numerator, stored
                // in the same memory slot used by the monolithic path.
                mstore(QUOTIENT_EVAL_MPTR, mload(add(q_out, 0x20)))
                // Remaining return words are selector linearization buckets.
                // Copy them back into the canonical selector accumulator region
                // so the PCS code path is identical for split and monolithic
                // quotient renders.
                for { let q_i := 0 } lt(q_i, 10) { q_i := add(q_i, 1) } {
                    mstore(add(SELECTOR_ACC_MPTR, shl(5, q_i)), mload(add(q_out, add(0x40, shl(5, q_i)))))
                }
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
                // Generated PCS sub-block 3. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[0]: 43 evaluation term(s), 42 commitment term(s) (rolled, m>=4)
                    // __phase:pcs_q_eval_source_table
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xb280, 0x9980)
                    mstore(0xb2a0, 0x9480)
                    mstore(0xb2c0, 0xa020)
                    mstore(0xb2e0, 0xa040)
                    mstore(0xb300, 0xa0a0)
                    mstore(0xb320, 0xa0c0)
                    mstore(0xb340, 0xa120)
                    mstore(0xb360, 0x99a0)
                    mstore(0xb380, 0x99c0)
                    mstore(0xb3a0, 0x99e0)
                    mstore(0xb3c0, 0x9a00)
                    mstore(0xb3e0, 0x9a20)
                    mstore(0xb400, 0x9a40)
                    mstore(0xb420, 0x9a60)
                    mstore(0xb440, 0x9a80)
                    mstore(0xb460, 0x9aa0)
                    mstore(0xb480, 0x9ac0)
                    mstore(0xb4a0, 0x9ae0)
                    mstore(0xb4c0, 0x9b00)
                    mstore(0xb4e0, 0x9b20)
                    mstore(0xb500, 0x9b40)
                    mstore(0xb520, 0x9b60)
                    mstore(0xb540, 0x9b80)
                    mstore(0xb560, 0x9ba0)
                    mstore(0xb580, 0x9bc0)
                    mstore(0xb5a0, 0x9be0)
                    mstore(0xb5c0, 0x9c00)
                    mstore(0xb5e0, 0x9c20)
                    mstore(0xb600, 0x9c40)
                    mstore(0xb620, 0x9c60)
                    mstore(0xb640, 0x9c80)
                    mstore(0xb660, 0x9ca0)
                    mstore(0xb680, 0x9cc0)
                    mstore(0xb6a0, 0x9ce0)
                    mstore(0xb6c0, 0x9d00)
                    mstore(0xb6e0, 0x9d20)
                    mstore(0xb700, 0x9d40)
                    mstore(0xb720, 0x9d60)
                    mstore(0xb740, 0x9d80)
                    mstore(0xb760, 0x9da0)
                    mstore(0xb780, 0x9dc0)
                    mstore(0xb7a0, 0x9de0)
                    mstore(0xb7c0, QUOTIENT_EVAL_MPTR)
                    let q_eval_set_0 := mload(0x9980)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xb280, 0x20)
                    for { let i := 1 } lt(i, 0x2b) { i := add(i, 1) } {
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
                    // q_eval_set[1]: 3 evaluation term(s), 3 commitment term(s)
                    let q_eval_set_0 := mload(0x9660)
                    let q_eval_set_1 := mload(0x9920)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x9680), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x9940), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0x96a0), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0x9960), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0x20), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x40), q_eval_set_1)
                }
                // Generated PCS sub-block 5. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[2]: 3 evaluation term(s), 3 commitment term(s)
                    let q_eval_set_0 := mload(0x9fe0)
                    let q_eval_set_1 := mload(0xa000)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0xa060), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0xa080), mload(add(X1_POWERS_MPTR, 0x20)), r), r)
                    q_eval_set_0 := addmod(q_eval_set_0, mulmod(mload(0xa0e0), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    q_eval_set_1 := addmod(q_eval_set_1, mulmod(mload(0xa100), mload(add(X1_POWERS_MPTR, 0x40)), r), r)
                    mstore(add(Q_EVAL_SET_MPTR, 0x60), q_eval_set_0)
                    mstore(add(Q_EVAL_SET_MPTR, 0x80), q_eval_set_1)
                }
                // Generated PCS sub-block 6. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[3]: 11 evaluation term(s), 11 commitment term(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xb280, 0x94a0)
                    mstore(0xb2a0, 0x9540)
                    mstore(0xb2c0, 0x97c0)
                    mstore(0xb2e0, 0x94c0)
                    mstore(0xb300, 0x9560)
                    mstore(0xb320, 0x97e0)
                    mstore(0xb340, 0x94e0)
                    mstore(0xb360, 0x9580)
                    mstore(0xb380, 0x9800)
                    mstore(0xb3a0, 0x9500)
                    mstore(0xb3c0, 0x96c0)
                    mstore(0xb3e0, 0x9820)
                    mstore(0xb400, 0x9520)
                    mstore(0xb420, 0x96e0)
                    mstore(0xb440, 0x9840)
                    mstore(0xb460, 0x95a0)
                    mstore(0xb480, 0x9700)
                    mstore(0xb4a0, 0x9860)
                    mstore(0xb4c0, 0x95c0)
                    mstore(0xb4e0, 0x9720)
                    mstore(0xb500, 0x9880)
                    mstore(0xb520, 0x95e0)
                    mstore(0xb540, 0x9740)
                    mstore(0xb560, 0x98a0)
                    mstore(0xb580, 0x9600)
                    mstore(0xb5a0, 0x9760)
                    mstore(0xb5c0, 0x98c0)
                    mstore(0xb5e0, 0x9620)
                    mstore(0xb600, 0x9780)
                    mstore(0xb620, 0x98e0)
                    mstore(0xb640, 0x9640)
                    mstore(0xb660, 0x97a0)
                    mstore(0xb680, 0x9900)
                    let q_eval_set_0 := mload(0x94a0)
                    let q_eval_set_1 := mload(0x9540)
                    let q_eval_set_2 := mload(0x97c0)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xb280, 0x60)
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
                // Generated PCS sub-block 7. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // q_eval_set[4]: 5 evaluation term(s), 5 commitment term(s) (rolled, m>=4)
                    // stage per-(commit, rotation) eval source addresses
                    mstore(0xb280, 0x9e00)
                    mstore(0xb2a0, 0x9e20)
                    mstore(0xb2c0, 0x9e40)
                    mstore(0xb2e0, 0x9e60)
                    mstore(0xb300, 0x9e80)
                    mstore(0xb320, 0x9ea0)
                    mstore(0xb340, 0x9ec0)
                    mstore(0xb360, 0x9ee0)
                    mstore(0xb380, 0x9f00)
                    mstore(0xb3a0, 0x9f20)
                    mstore(0xb3c0, 0x9f40)
                    mstore(0xb3e0, 0x9f60)
                    mstore(0xb400, 0x9f80)
                    mstore(0xb420, 0x9fa0)
                    mstore(0xb440, 0x9fc0)
                    let q_eval_set_0 := mload(0x9e00)
                    let q_eval_set_1 := mload(0x9e20)
                    let q_eval_set_2 := mload(0x9e40)
                    let pow_p := add(X1_POWERS_MPTR, 0x20)
                    let eval_p := add(0xb280, 0x60)
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
                // Generated PCS sub-block 8. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // __phase:scalar_inv
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
                // Generated PCS sub-block 9. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // __phase:pcs_final_msm
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
                    mcopy(0xb280, 0xa840, 0x80)
                    mstore(0xb300, 1)
                    mcopy(0xb320, 0xa8c0, 0x80)
                    mstore(0xb3a0, mload(add(X1_POWERS_MPTR, 0x40)))
                    mcopy(0xb3c0, 0xacc0, 0x80)
                    mstore(0xb440, mload(add(X1_POWERS_MPTR, 0x60)))
                    mcopy(0xb460, 0xa940, 0x80)
                    mstore(0xb4e0, mload(add(X1_POWERS_MPTR, 0x80)))
                    mcopy(0xb500, 0xad40, 0x80)
                    mstore(0xb580, mload(add(X1_POWERS_MPTR, 0xa0)))
                    mcopy(0xb5a0, 0xaec0, 0x80)
                    mstore(0xb620, mload(add(X1_POWERS_MPTR, 0xc0)))
                    mcopy(0xb640, 0x6700, 0x80)
                    mstore(0xb6c0, mload(add(X1_POWERS_MPTR, 0xe0)))
                    mcopy(0xb6e0, 0x6480, 0x80)
                    mstore(0xb760, mload(add(X1_POWERS_MPTR, 0x100)))
                    mcopy(0xb780, 0x6500, 0x80)
                    mstore(0xb800, mload(add(X1_POWERS_MPTR, 0x120)))
                    mcopy(0xb820, 0x6580, 0x80)
                    mstore(0xb8a0, mload(add(X1_POWERS_MPTR, 0x140)))
                    mcopy(0xb8c0, 0x6600, 0x80)
                    mstore(0xb940, mload(add(X1_POWERS_MPTR, 0x160)))
                    mcopy(0xb960, 0x6680, 0x80)
                    mstore(0xb9e0, mload(add(X1_POWERS_MPTR, 0x180)))
                    mcopy(0xba00, 0x6280, 0x80)
                    mstore(0xba80, mload(add(X1_POWERS_MPTR, 0x1a0)))
                    mcopy(0xbaa0, 0x6300, 0x80)
                    mstore(0xbb20, mload(add(X1_POWERS_MPTR, 0x1c0)))
                    mcopy(0xbb40, 0x6380, 0x80)
                    mstore(0xbbc0, mload(add(X1_POWERS_MPTR, 0x1e0)))
                    mcopy(0xbbe0, 0x6400, 0x80)
                    mstore(0xbc60, mload(add(X1_POWERS_MPTR, 0x200)))
                    mcopy(0xbc80, 0x6780, 0x80)
                    mstore(0xbd00, mload(add(X1_POWERS_MPTR, 0x220)))
                    mcopy(0xbd20, 0x6800, 0x80)
                    mstore(0xbda0, mload(add(X1_POWERS_MPTR, 0x240)))
                    mcopy(0xbdc0, 0x6880, 0x80)
                    mstore(0xbe40, mload(add(X1_POWERS_MPTR, 0x260)))
                    mcopy(0xbe60, 0x6900, 0x80)
                    mstore(0xbee0, mload(add(X1_POWERS_MPTR, 0x280)))
                    mcopy(0xbf00, 0x6b00, 0x80)
                    mstore(0xbf80, mload(add(X1_POWERS_MPTR, 0x2a0)))
                    mcopy(0xbfa0, 0x6c00, 0x80)
                    mstore(0xc020, mload(add(X1_POWERS_MPTR, 0x2c0)))
                    mcopy(0xc040, 0x6f80, 0x80)
                    mstore(0xc0c0, mload(add(X1_POWERS_MPTR, 0x2e0)))
                    mcopy(0xc0e0, 0x7000, 0x80)
                    mstore(0xc160, mload(add(X1_POWERS_MPTR, 0x300)))
                    mcopy(0xc180, 0x7080, 0x80)
                    mstore(0xc200, mload(add(X1_POWERS_MPTR, 0x320)))
                    mcopy(0xc220, 0x7100, 0x80)
                    mstore(0xc2a0, mload(add(X1_POWERS_MPTR, 0x340)))
                    mcopy(0xc2c0, 0x7180, 0x80)
                    mstore(0xc340, mload(add(X1_POWERS_MPTR, 0x360)))
                    mcopy(0xc360, 0x7200, 0x80)
                    mstore(0xc3e0, mload(add(X1_POWERS_MPTR, 0x380)))
                    mcopy(0xc400, 0x7280, 0x80)
                    mstore(0xc480, mload(add(X1_POWERS_MPTR, 0x3a0)))
                    mcopy(0xc4a0, 0x7300, 0x80)
                    mstore(0xc520, mload(add(X1_POWERS_MPTR, 0x3c0)))
                    mcopy(0xc540, 0x7380, 0x80)
                    mstore(0xc5c0, mload(add(X1_POWERS_MPTR, 0x3e0)))
                    mcopy(0xc5e0, 0x7400, 0x80)
                    mstore(0xc660, mload(add(X1_POWERS_MPTR, 0x400)))
                    mcopy(0xc680, 0x7480, 0x80)
                    mstore(0xc700, mload(add(X1_POWERS_MPTR, 0x420)))
                    mcopy(0xc720, 0x7500, 0x80)
                    mstore(0xc7a0, mload(add(X1_POWERS_MPTR, 0x440)))
                    mcopy(0xc7c0, 0x7580, 0x80)
                    mstore(0xc840, mload(add(X1_POWERS_MPTR, 0x460)))
                    mcopy(0xc860, 0x7600, 0x80)
                    mstore(0xc8e0, mload(add(X1_POWERS_MPTR, 0x480)))
                    mcopy(0xc900, 0x7680, 0x80)
                    mstore(0xc980, mload(add(X1_POWERS_MPTR, 0x4a0)))
                    mcopy(0xc9a0, 0x7700, 0x80)
                    mstore(0xca20, mload(add(X1_POWERS_MPTR, 0x4c0)))
                    mcopy(0xca40, 0x7780, 0x80)
                    mstore(0xcac0, mload(add(X1_POWERS_MPTR, 0x4e0)))
                    mcopy(0xcae0, 0x7800, 0x80)
                    mstore(0xcb60, mload(add(X1_POWERS_MPTR, 0x500)))
                    mcopy(0xcb80, 0x7880, 0x80)
                    mstore(0xcc00, mload(add(X1_POWERS_MPTR, 0x520)))
                    let lin_query_scalar_41 := mload(add(X1_POWERS_MPTR, 0x540))
                    let lin_cur_scalar_41 := mulmod(lin_query_scalar_41, lin_one_minus_x_n, r)
                    mcopy(0xcc20, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x0), 0x80)
                    mstore(0xcca0, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xccc0, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x80), 0x80)
                    mstore(0xcd40, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xcd60, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x100), 0x80)
                    mstore(0xcde0, lin_cur_scalar_41)
                    lin_cur_scalar_41 := mulmod(lin_cur_scalar_41, lin_x_split, r)
                    mcopy(0xce00, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, 0x180), 0x80)
                    mstore(0xce80, lin_cur_scalar_41)
                    mcopy(0xcea0, 0x6980, 0x80)
                    mstore(0xcf20, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x0)), r))
                    mcopy(0xcf40, 0x6a00, 0x80)
                    mstore(0xcfc0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x20)), r))
                    mcopy(0xcfe0, 0x6a80, 0x80)
                    mstore(0xd060, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x40)), r))
                    mcopy(0xd080, 0x6b80, 0x80)
                    mstore(0xd100, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x60)), r))
                    mcopy(0xd120, 0x6c80, 0x80)
                    mstore(0xd1a0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x80)), r))
                    mcopy(0xd1c0, 0x6d00, 0x80)
                    mstore(0xd240, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xa0)), r))
                    mcopy(0xd260, 0x6d80, 0x80)
                    mstore(0xd2e0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xc0)), r))
                    mcopy(0xd300, 0x6e00, 0x80)
                    mstore(0xd380, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0xe0)), r))
                    mcopy(0xd3a0, 0x6e80, 0x80)
                    mstore(0xd420, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x100)), r))
                    mcopy(0xd440, 0x6f00, 0x80)
                    mstore(0xd4c0, mulmod(lin_query_scalar_41, mload(add(SELECTOR_ACC_MPTR, 0x120)), r))
                    mcopy(0xd4e0, 0xa6c0, 0x80)
                    mstore(0xd560, x4_pow_1)
                    mcopy(0xd580, 0xa740, 0x80)
                    mstore(0xd600, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_1, r))
                    mcopy(0xd620, 0xa7c0, 0x80)
                    mstore(0xd6a0, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_1, r))
                    mcopy(0xd6c0, 0xac40, 0x80)
                    mstore(0xd740, x4_pow_2)
                    mcopy(0xd760, 0xadc0, 0x80)
                    mstore(0xd7e0, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_2, r))
                    mcopy(0xd800, 0xae40, 0x80)
                    mstore(0xd880, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_2, r))
                    mcopy(0xd8a0, 0xa140, 0x80)
                    mstore(0xd920, x4_pow_3)
                    mcopy(0xd940, 0xa1c0, 0x80)
                    mstore(0xd9c0, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_3, r))
                    mcopy(0xd9e0, 0xa240, 0x80)
                    mstore(0xda60, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_3, r))
                    mcopy(0xda80, 0xa2c0, 0x80)
                    mstore(0xdb00, mulmod(mload(add(X1_POWERS_MPTR, 0x60)), x4_pow_3, r))
                    mcopy(0xdb20, 0xa340, 0x80)
                    mstore(0xdba0, mulmod(mload(add(X1_POWERS_MPTR, 0x80)), x4_pow_3, r))
                    mcopy(0xdbc0, 0xa3c0, 0x80)
                    mstore(0xdc40, mulmod(mload(add(X1_POWERS_MPTR, 0xa0)), x4_pow_3, r))
                    mcopy(0xdc60, 0xa440, 0x80)
                    mstore(0xdce0, mulmod(mload(add(X1_POWERS_MPTR, 0xc0)), x4_pow_3, r))
                    mcopy(0xdd00, 0xa4c0, 0x80)
                    mstore(0xdd80, mulmod(mload(add(X1_POWERS_MPTR, 0xe0)), x4_pow_3, r))
                    mcopy(0xdda0, 0xa540, 0x80)
                    mstore(0xde20, mulmod(mload(add(X1_POWERS_MPTR, 0x100)), x4_pow_3, r))
                    mcopy(0xde40, 0xa5c0, 0x80)
                    mstore(0xdec0, mulmod(mload(add(X1_POWERS_MPTR, 0x120)), x4_pow_3, r))
                    mcopy(0xdee0, 0xa640, 0x80)
                    mstore(0xdf60, mulmod(mload(add(X1_POWERS_MPTR, 0x140)), x4_pow_3, r))
                    mcopy(0xdf80, 0xa9c0, 0x80)
                    mstore(0xe000, x4_pow_4)
                    mcopy(0xe020, 0xaa40, 0x80)
                    mstore(0xe0a0, mulmod(mload(add(X1_POWERS_MPTR, 0x20)), x4_pow_4, r))
                    mcopy(0xe0c0, 0xaac0, 0x80)
                    mstore(0xe140, mulmod(mload(add(X1_POWERS_MPTR, 0x40)), x4_pow_4, r))
                    mcopy(0xe160, 0xab40, 0x80)
                    mstore(0xe1e0, mulmod(mload(add(X1_POWERS_MPTR, 0x60)), x4_pow_4, r))
                    mcopy(0xe200, 0xabc0, 0x80)
                    mstore(0xe280, mulmod(mload(add(X1_POWERS_MPTR, 0x80)), x4_pow_4, r))
                    mcopy(0xe2a0, F_COM_MPTR, 0x80)
                    mstore(0xe320, x4_pow_5)
                    if success {
                        // exact EIP-2537 G1MSM cost for 78 pair(s)
                        success := staticcall(525096, 0x0c, 0xb280, 0x30c0, FINAL_COM_MPTR, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mstore(V_MPTR, v)
                }
                // Generated PCS sub-block 10. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    // __phase:pcs_pairing
                    // Scale z*pi - vG before the final pairing check
                    // pairing inputs (LHS = pi; RHS = final_com - v*G + x3*pi)
                    mcopy(PAIRING_LHS_MPTR, PI_MPTR, 0x80)
                    mcopy(0x1000, G1_BASE_MPTR, 0x80)
                    mstore(0x1080, addmod(0, sub(r, mload(V_MPTR)), r))
                    if success {
                        success := staticcall(G1MSM_GAS_1PAIR, 0x0c, 0x1000, 0xa0, 0x1000, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x1080, FINAL_COM_MPTR, 0x80)
                    if success {
                        success := staticcall(G1ADD_GAS, 0x0b, 0x1000, 0x100, 0x1000, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(0x1080, PI_MPTR, 0x80)
                    mstore(0x1100, mload(X3_MPTR))
                    if success {
                        success := staticcall(G1MSM_GAS_1PAIR, 0x0c, 0x1080, 0xa0, 0x1080, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    if success {
                        success := staticcall(G1ADD_GAS, 0x0b, 0x1000, 0x100, 0x1000, 0x80)
                        success := and(success, eq(returndatasize(), 0x80))
                    }
                    mcopy(PAIRING_RHS_MPTR, 0x1000, 0x80)
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
            // __phase:accumulator_pairing_batch
            {
                let batch_ptr := 0x1000

                // Domain || vk_digest || KZG rhs/lhs || accumulator rhs/lhs.
                // vk_digest makes alpha's binding to the verifying key local
                // instead of transitive-through-the-points (audit I-7).
                mstore(batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
                mstore(add(batch_ptr, 0x20), mload(VK_DIGEST_MPTR))
                mcopy(add(batch_ptr, 0x40),  PAIRING_RHS_MPTR, 0x80)
                mcopy(add(batch_ptr, 0xc0),  PAIRING_LHS_MPTR, 0x80)
                mcopy(add(batch_ptr, 0x0140), ACC_RHS_MPTR,     0x80)
                mcopy(add(batch_ptr, 0x01c0), ACC_LHS_MPTR,     0x80)
                // alpha is Fiat-Shamir over the fully materialized pairing
                // inputs. Replace the negligible zero draw with one so the
                // accumulator equation cannot be accidentally dropped.
                let acc_pair_alpha := mod(keccak256(batch_ptr, 0x0240), r)
                if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }

                // PAIRING_RHS_MPTR += alpha * ACC_RHS_MPTR.
                // First compute alpha * ACC_RHS with a one-pair G1MSM, then
                // add it into the KZG RHS point.
                mcopy(batch_ptr, ACC_RHS_MPTR, 0x80)
                mstore(add(batch_ptr, 0x80), acc_pair_alpha)
                if success {
                    success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
                mcopy(add(batch_ptr, 0x80), PAIRING_RHS_MPTR, 0x80)
                if success {
                    success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_RHS_MPTR, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }

                // PAIRING_LHS_MPTR += alpha * ACC_LHS_MPTR.
                // Mirror the same randomized batching on the KZG LHS point.
                mcopy(batch_ptr, ACC_LHS_MPTR, 0x80)
                mstore(add(batch_ptr, 0x80), acc_pair_alpha)
                if success {
                    success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
                mcopy(add(batch_ptr, 0x80), PAIRING_LHS_MPTR, 0x80)
                if success {
                    success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_LHS_MPTR, 0x80)
                    success := and(success, eq(returndatasize(), 0x80))
                }
            }

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
            // __phase:final_pairing
            if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)

    

            // Success path is terminal. Invalid inputs have already reverted,
            // so the Solidity ABI observes `true`.
            //
            // The guard is redundant today -- every failure path above reverts
            // rather than clearing `success` -- but it keeps acceptance a local
            // property of this file instead of an invariant split across
            // FinalPairing.yul and ec_pairing.
            if iszero(success) { fail(ERR_PROOF_REJECTED) }
            // __phase:verifier_return
            mstore(RETURN_MPTR, 1)
            return(RETURN_MPTR, 0x20)
        }
    }
}