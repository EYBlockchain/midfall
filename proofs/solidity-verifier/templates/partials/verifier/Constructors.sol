    {%- match self.expected_vk_codehash %}
    {%- when Some with (_) %}
    {%- match self.external_pinned() %}
    {%- when Some with (_) %}
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
    {%- when None %}
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
    {%- endmatch %}
    {%- when None %}
    {%- match self.external_pinned() %}
    {%- when Some with (_) %}
    /// @notice Create a verifier pinned to a quotient evaluator.
    /// @dev Used when the VK is embedded in the verifier but quotient reconstruction is split out.
    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.
    constructor(address authorizedQuotient) {
        // Embedded VK path: the verifier bytecode carries the VK payload, but
        // the runtime prerequisites and external quotient evaluator still
        // need to be checked before storing the dependency address.
        require_eip2537_precompiles();
        require(
            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH
                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,
            "invalid quotient"
        );
        AUTHORIZED_QUOTIENT = authorizedQuotient;
    }
    {%- when None %}
    /// @notice Create a verifier with embedded verifier data.
    /// @dev Checks MCOPY/EIP-2537 availability at deployment.
    constructor() {
        // Fully embedded verifier: no external generated dependency exists,
        // so deployment only checks runtime opcode/precompile availability.
        require_eip2537_precompiles();
    }
    {%- endmatch %}
    {%- endmatch %}
