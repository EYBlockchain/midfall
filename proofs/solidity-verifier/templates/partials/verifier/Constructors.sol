    {%- match self.expected_vk_codehash %}
    {%- when Some with (_) %}
    {%- match quotient_external %}
    {%- when Some with (_) %}
    /// @notice Create a verifier pinned to a verifying key and quotient evaluator.
    /// @dev Checks EIP-2537 availability and verifies both dependency runtimes before storing their addresses.
    /// @param authorizedVk Address of the generated `Halo2VerifyingKey` runtime.
    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.
    constructor(address authorizedVk, address authorizedQuotient) {
        // Verifier correctness depends on chain support for the BLS12-381
        // precompiles; fail deployment before pinning any dependency address.
        require_eip2537_precompiles();
        // Pin the generated VK runtime exactly. The verifier later repeats the
        // codehash/length check before copying the VK payload for a proof.
        require(
            authorizedVk.code.length == EXPECTED_VK_LENGTH
                && authorizedVk.codehash == EXPECTED_VK_CODEHASH,
            "invalid vk"
        );
        {%- match self.expected_quotient_codehash %}
        {%- when Some with (_) %}
        // The split evaluator contains generated verifier logic, not a generic
        // library. Pin it with the same strictness as the verifying key.
        require(
            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH
                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,
            "invalid quotient"
        );
        {%- when None %}
        {%- endmatch %}
        // Store the already-validated dependency addresses for proof-time
        // memory loading and quotient reconstruction.
        AUTHORIZED_VK = authorizedVk;
        AUTHORIZED_QUOTIENT = authorizedQuotient;
        {%- match self.expected_quotient_codehash %}
        {%- when Some with (_) %}
        {%- when None %}
        {%- endmatch %}
    }
    {%- when None %}
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
    {%- endmatch %}
    {%- when None %}
    {%- match quotient_external %}
    {%- when Some with (_) %}
    /// @notice Create a verifier pinned to a quotient evaluator.
    /// @dev Used when the VK is embedded in the verifier but quotient reconstruction is split out.
    /// @param authorizedQuotient Address of the generated `Halo2QuotientEvaluator` runtime.
    constructor(address authorizedQuotient) {
        // Embedded VK path: the verifier bytecode carries the VK payload, but
        // the external quotient evaluator remains a pinned dependency.
        require_eip2537_precompiles();
        {%- match self.expected_quotient_codehash %}
        {%- when Some with (_) %}
        require(
            authorizedQuotient.code.length == EXPECTED_QUOTIENT_LENGTH
                && authorizedQuotient.codehash == EXPECTED_QUOTIENT_CODEHASH,
            "invalid quotient"
        );
        {%- when None %}
        {%- endmatch %}
        AUTHORIZED_QUOTIENT = authorizedQuotient;
        {%- match self.expected_quotient_codehash %}
        {%- when Some with (_) %}
        {%- when None %}
        {%- endmatch %}
    }
    {%- when None %}
    /// @notice Create a verifier with embedded verifier data.
    /// @dev Checks EIP-2537 availability at deployment.
    constructor() {
        // Fully embedded verifier: no external generated dependency exists,
        // so deployment only checks precompile availability.
        require_eip2537_precompiles();
    }
    {%- endmatch %}
    {%- endmatch %}
