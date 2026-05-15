    /// @notice Smoke-check the BLS12-381 precompiles required by the verifier.
    /// @dev Uses identity inputs to catch absent EIP-2537 implementations, short return data, and incompatible pairing semantics at deployment.
    function require_eip2537_precompiles() private view {
        assembly ("memory-safe") {
            // Scratch is reused for every precompile probe. Start with the
            // EIP-2537 identity encoding for G1/G2: all-zero padded words.
            let scratch := {{ memory.constructor_smoke_scratch_mptr|hex() }}
            for { let off := 0 } lt(off, {{ template_constants.eip2537.smoke_scratch_bytes|hex() }}) { off := add(off, {{ template_constants.word_bytes|hex() }}) } {
                mstore(add(scratch, off), 0)
            }

            // G1ADD(identity, identity) -> identity, 128-byte return.
            // This catches chains where the precompile is missing or returns a
            // non-standard success shape.
            if iszero(staticcall({{ template_constants.eip2537.g1add_gas_cap }}, {{ template_constants.eip2537.g1add_address|hex() }}, scratch, {{ template_constants.g1add_input_bytes|hex() }}, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // G1MSM([(identity, 0)]) -> identity, 128-byte return.
            // The production verifier uses G1MSM both for commitments and as
            // the subgroup validator for absorbed proof points.
            if iszero(staticcall({{ template_constants.eip2537.g1msm_smoke_gas_cap }}, {{ template_constants.eip2537.g1msm_address|hex() }}, scratch, {{ template_constants.g1_msm_pair_bytes|hex() }}, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // PAIRING_CHECK([(identity_g1, identity_g2)]) -> true,
            // 32-byte return. This catches absent pairing precompiles,
            // short return data, and obviously incompatible semantics.
            if iszero(staticcall({{ template_constants.eip2537.pairing_smoke_gas_cap }}, {{ template_constants.eip2537.pairing_address|hex() }}, scratch, {{ template_constants.pairing_pair_bytes|hex() }}, scratch, {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
        }
    }
