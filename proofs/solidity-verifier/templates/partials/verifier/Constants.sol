    {%- match self.expected_vk_codehash %}
    {%- when Some with (expected_vk_codehash) %}
    /// @notice Verifying-key contract address authorized for this verifier.
    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.
    address public immutable AUTHORIZED_VK;
    // Expected VK runtime metadata. The deployed VK runtime is
    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than
    // EXPECTED_VK_PAYLOAD_LENGTH.
    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = {{ vk_len }};
    uint256 internal constant EXPECTED_VK_LENGTH = {{ vk_len + 1 }};
    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = {{ expected_vk_codehash|hex_padded(64) }};
    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);
    {%- when None %}
    {%- endmatch %}
    {%- match quotient_external %}
    {%- when Some with (_) %}
    /// @notice Quotient evaluator contract authorized for split quotient reconstruction.
    /// @dev The evaluator returns the linearization expected scalar and selector buckets; its runtime may be pinned by generated constants.
    address public immutable AUTHORIZED_QUOTIENT;
    {%- match self.expected_quotient_codehash %}
    {%- when Some with (expected_quotient_codehash) %}
    // Expected split evaluator runtime metadata. It is checked at deployment
    // and again immediately before each external quotient reconstruction.
    uint256 internal constant EXPECTED_QUOTIENT_LENGTH = {{ self.expected_quotient_len.unwrap() }};
    uint256 internal constant EXPECTED_QUOTIENT_CODEHASH_WORD = {{ expected_quotient_codehash|hex_padded(64) }};
    bytes32 internal constant EXPECTED_QUOTIENT_CODEHASH = bytes32(EXPECTED_QUOTIENT_CODEHASH_WORD);
    {%- when None %}
    {%- endmatch %}
    {%- when None %}
    {%- endmatch %}

    // Solidity ABI calldata cursors. The generated verifier accepts exactly
    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`
    // bytes itself in the same order as the Rust verifier transcript.
    uint256 internal constant    PROOF_LEN_CPTR = {{ proof_cptr - 1 }};
    uint256 internal constant        PROOF_CPTR = {{ proof_cptr }};
    uint256 internal constant NUM_INSTANCE_CPTR = {{ num_instance_cptr|hex_padded(2) }};
    uint256 internal constant     INSTANCE_CPTR = {{ instance_cptr|hex_padded(2) }};
    // First general-purpose memory words reserved by the generated verifier.
    // RETURN_MPTR is a single word set to 1 on success.
    uint256 internal constant    TRANSCRIPT_MPTR = {{ memory.transcript_mptr|hex() }};
    uint256 internal constant        RETURN_MPTR = {{ memory.verifier_return_mptr|hex() }};

    // ----------------------------------------------------------------------
    // Verifying-key memory map. The VK header lives at VK_MPTR, followed
    // by the quotient VM payload and commitments. After the full VK
    // runtime comes the challenge slots (challenge_mptr..) and the
    // per-stage scratch (theta_mptr..).
    // ----------------------------------------------------------------------
    uint256 internal constant                VK_MPTR = {{ memory.vk_mptr }};
    uint256 internal constant         VK_DIGEST_MPTR = {{ memory.vk_mptr + vk_header.vk_digest }};
    uint256 internal constant     NUM_INSTANCES_MPTR = {{ memory.vk_mptr + vk_header.num_instances }};
    uint256 internal constant                 K_MPTR = {{ memory.vk_mptr + vk_header.k }};
    uint256 internal constant             N_INV_MPTR = {{ memory.vk_mptr + vk_header.n_inv }};
    uint256 internal constant             OMEGA_MPTR = {{ memory.vk_mptr + vk_header.omega }};
    uint256 internal constant         OMEGA_INV_MPTR = {{ memory.vk_mptr + vk_header.omega_inv }};
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = {{ memory.vk_mptr + vk_header.omega_inv_to_l }};
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = {{ memory.vk_mptr + vk_header.has_accumulator }};
    uint256 internal constant        ACC_OFFSET_MPTR = {{ memory.vk_mptr + vk_header.acc_offset }};
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = {{ memory.vk_mptr + vk_header.num_acc_limbs }};
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = {{ memory.vk_mptr + vk_header.num_acc_limb_bits }};
    uint256 internal constant            G1_BASE_MPTR = {{ memory.vk_mptr + vk_header.g1_base }};
    uint256 internal constant            G2_BASE_MPTR = {{ memory.vk_mptr + vk_header.g2_base }};
    uint256 internal constant      NEG_S_G2_BASE_MPTR = {{ memory.vk_mptr + vk_header.neg_s_g2_base }};

    uint256 internal constant CHALLENGE_MPTR = {{ memory.challenge_mptr }};

    // Challenge layout. Squeeze order in midnight-proofs:
    //   user_phase challenges (variable count)
    //   theta -> beta, gamma -> trash_challenge -> y -> x ->
    //   x1, x2 -> x3 -> x4
    uint256 internal constant            THETA_MPTR = {{ memory.theta_mptr }};
    uint256 internal constant             BETA_MPTR = {{ memory.beta_mptr }};
    uint256 internal constant            GAMMA_MPTR = {{ memory.gamma_mptr }};
    uint256 internal constant TRASH_CHALLENGE_MPTR = {{ memory.trash_challenge_mptr }};
    uint256 internal constant                Y_MPTR = {{ memory.y_mptr }};
    uint256 internal constant                X_MPTR = {{ memory.x_mptr }};
    uint256 internal constant               X1_MPTR = {{ memory.x1_mptr }};
    uint256 internal constant               X2_MPTR = {{ memory.x2_mptr }};
    uint256 internal constant               X3_MPTR = {{ memory.x3_mptr }};
    uint256 internal constant               X4_MPTR = {{ memory.x4_mptr }};

    // Batch-open commitments live in 4-word EIP-2537 padded slots.
    uint256 internal constant             F_COM_MPTR = {{ memory.f_com_mptr }};
    uint256 internal constant                PI_MPTR = {{ memory.pi_mptr }};

    // Accumulator (KZG IVC).
    uint256 internal constant          ACC_LHS_MPTR = {{ memory.acc_lhs_mptr }};
    uint256 internal constant          ACC_RHS_MPTR = {{ memory.acc_rhs_mptr }};

    // Lagrange / linearization scratch.
    uint256 internal constant              X_N_MPTR = {{ memory.x_n_mptr }};
    uint256 internal constant  X_N_MINUS_1_INV_MPTR = {{ memory.x_n_minus_1_inv_mptr }};
    uint256 internal constant           L_LAST_MPTR = {{ memory.l_last_mptr }};
    uint256 internal constant          L_BLIND_MPTR = {{ memory.l_blind_mptr }};
    uint256 internal constant              L_0_MPTR = {{ memory.l_0_mptr }};
    uint256 internal constant     INSTANCE_EVAL_MPTR = {{ memory.instance_eval_mptr }};
    // Legacy name: this is not h(x). It stores the expected opening
    // scalar for the linearized commitment, i.e. the negated y-batched
    // identity numerator reconstructed from the alleged evals at x.
    uint256 internal constant     QUOTIENT_EVAL_MPTR = {{ memory.quotient_eval_mptr }};
    uint256 internal constant         QUOTIENT_MPTR = {{ memory.quotient_mptr }};   // 4 words
    uint256 internal constant            F_EVAL_MPTR = {{ memory.f_eval_mptr }};
    uint256 internal constant                 V_MPTR = {{ memory.v_mptr }};
    uint256 internal constant         FINAL_COM_MPTR = {{ memory.final_com_mptr }};   // 4 words
    uint256 internal constant      PAIRING_LHS_MPTR = {{ memory.pairing_lhs_mptr }};   // 4 words
    uint256 internal constant      PAIRING_RHS_MPTR = {{ memory.pairing_rhs_mptr }};   // 4 words

    // Multi-prepare scratch (sized at codegen time).
    uint256 internal constant       ROT_POINTS_MPTR = {{ memory.rot_points_mptr }};
    uint256 internal constant       X1_POWERS_MPTR = {{ memory.x1_powers_mptr }};
    // Q_COM materialization is currently fused into the final MSM scratch,
    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero
    // reserved capacity until a future emitter starts writing Q_COM_MPTR.
    uint256 internal constant            Q_COM_MPTR = {{ memory.q_com_mptr }};
    uint256 internal constant      Q_EVAL_SET_MPTR = {{ memory.q_eval_set_mptr }};

    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals
    // block of the proof; we keep it as a memory slot for symmetry.
    uint256 internal constant         Q_EVAL_CPTR_MPTR = {{ memory.q_eval_cptr_mptr }};

    // Reserved 4-word slot for the G1 identity (point at infinity) in
    // EIP-2537 padded form. EVM memory is zero-initialised, and the verifier
    // never writes to this region, so any read of this slot (the PCS
    // emitters `mcopy` from it when staging identity commitments) yields
    // 0,0,0,0 -- exactly the identity encoding the EIP-2537 precompiles
    // accept. Artifacts whose PCS plan never stages an identity commitment
    // still emit the constant; it costs no runtime bytes beyond the
    // declaration and keeps the emitters' pointer model uniform.
    uint256 internal constant       G1_IDENTITY_MPTR = {{ memory.g1_identity_mptr }};

    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain
    // Solidity proof shim rewrites proof scalars into canonical BE words,
    // so `calldataload` gives the field element directly. The transcript-
    // side `evaluations` loop range-checks and spills that value here so
    // downstream eval references (gate evaluator + PCS q_eval Horner)
    // become 3-gas `mload(...)` instead of calldata reads.
    uint256 internal constant     REVERSED_EVALS_MPTR = {{ memory.reversed_evals_mptr }};
    uint256 internal constant      SELECTOR_ACC_MPTR = {{ memory.selector_acc_mptr|hex() }};
    uint256 internal constant   QUOTIENT_RETURN_MPTR = {{ memory.quotient_return_mptr|hex() }};
    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = {{ memory.batch_invert_scratch_mptr|hex() }};
    // Lagrange batch-inversion input run: denominators, in-place inverses,
    // then Lagrange values, consumed and distilled into the named theta
    // slots by the Lagrange block. Planner-registered phase scratch.
    uint256 internal constant    LAGRANGE_DENOMS_MPTR = {{ memory.lagrange_denoms_mptr|hex() }};
    uint256 internal constant        TRACE_U256_MPTR = {{ memory.trace_u256_mptr|hex() }};

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
    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = {{ memory.advice_comms_mptr_base }};
    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = {{ memory.lookup_m_comms_mptr_base }};
    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = {{ memory.perm_z_comms_mptr_base }};
    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = {{ memory.lookup_helper_comms_mptr_base }};
    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = {{ memory.lookup_z_comms_mptr_base }};
    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = {{ memory.trashcan_comms_mptr_base }};
    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = {{ memory.quotient_limb_comms_mptr_base }};

    // ----------------------------------------------------------------------
    // Precompile gas bounds: the exact EIP-2537 / EIP-2565 scheduled costs.
    //
    // A failing EIP-2537 or modexp call consumes ALL gas supplied to the
    // STATICCALL, so every generated call site forwards the exact scheduled
    // cost instead of gas(). A malformed proof point then burns at most the
    // scheduled cost of the single failing call instead of 63/64 of the
    // transaction budget. The schedule is the spec-guaranteed worst case
    // (EIP-2537 "DDoS protection" rationale), so these bounds are sufficient
    // by construction on any conformant chain.
    //
    // Liveness caveat: if a future fork reprices these precompiles UPWARD,
    // this verifier must be regenerated and redeployed. The constructor
    // smoke probes forward the same bounds, so deployment onto an
    // already-repriced chain fails fast instead of bricking at proof time.
    // ----------------------------------------------------------------------
    uint256 internal constant          G1ADD_GAS = {{ template_constants.gas.g1add }};
    uint256 internal constant   G1MSM_GAS_1PAIR = {{ template_constants.gas.g1msm_one_pair }};
    uint256 internal constant PAIRING_GAS_2PAIR = {{ template_constants.gas.pairing_two_pair }};
    uint256 internal constant        MODEXP_GAS = {{ template_constants.gas.modexp }};
    // Exact cost of the deployment-time worst-case G1MSM smoke probe.
    uint256 internal constant G1MSM_GAS_SMOKE = {{ constructor_g1msm_smoke_gas }};
    {%- if self.expected_has_accumulator %}
    // Worst-case accumulator RHS MSM: carried RHS point plus every generated
    // fixed-base tail scalar nonzero. Zero tail scalars are omitted at
    // runtime, which only lowers the actual cost below this bound.
    uint256 internal constant ACC_RHS_MSM_GAS = {{ acc_rhs_msm_gas }};
    {%- endif %}

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
    bytes32 public constant BUILD_ID = {{ build_id|hex_padded(64) }};

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
