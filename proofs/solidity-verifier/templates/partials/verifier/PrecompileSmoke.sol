    /// @notice Smoke-check the Cancun/EIP-2537 runtime features required by the verifier.
    /// @dev Exercises MCOPY and identity EIP-2537 inputs to catch incompatible chain/fork configurations at deployment.
    ///      The probes forward the same exact EIP-2537 gas bounds the runtime
    ///      uses (see the gas-bound constants block), so a chain whose
    ///      precompile schedule was repriced upward fails here, at deployment,
    ///      instead of bricking verifyProof later.
    function require_eip2537_precompiles() private view {
        assembly ("memory-safe") {
            // Same free-memory-pointer guard as verifyProof. This body runs in
            // the *creation* frame, which the generator's memoryguard test does
            // not inspect (it parses the runtime prologue only).
            if gt(mload(0x40), {{ memory.constructor_smoke_scratch_mptr|hex() }}) { revert(0, 0) }

            // Scratch is reused for every runtime-prerequisite probe.
            let scratch := {{ memory.constructor_smoke_scratch_mptr|hex() }}

            // MCOPY must be available because the verifier uses it for
            // proof-time point/scratch staging. Execute the opcode here so a
            // non-Cancun fork fails during deployment instead of later proofs.
            mstore(scratch, 0x1234)
            mcopy(add(scratch, {{ template_constants.word_bytes|hex() }}), scratch, {{ template_constants.word_bytes|hex() }})
            if iszero(eq(mload(add(scratch, {{ template_constants.word_bytes|hex() }})), 0x1234)) { revert(0, 0) }

            // Start the EIP-2537 probes with the identity encoding for G1/G2:
            // all-zero padded words.
            for { let off := 0 } lt(off, {{ template_constants.eip2537.smoke_scratch_bytes|hex() }}) { off := add(off, {{ template_constants.word_bytes|hex() }}) } {
                mstore(add(scratch, off), 0)
            }

            // G1ADD(identity, identity) -> identity, 128-byte return.
            // This catches chains where the precompile is missing or returns a
            // non-standard success shape.
            if iszero(staticcall(G1ADD_GAS, {{ template_constants.eip2537.g1add_address|hex() }}, scratch, {{ template_constants.g1add_input_bytes|hex() }}, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
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
            mstore(add(scratch, 0x00), {{ template_constants.eip2537.g1_generator.0|hex_padded(64) }})
            mstore(add(scratch, 0x20), {{ template_constants.eip2537.g1_generator.1|hex_padded(64) }})
            mstore(add(scratch, 0x40), {{ template_constants.eip2537.g1_generator.2|hex_padded(64) }})
            mstore(add(scratch, 0x60), {{ template_constants.eip2537.g1_generator.3|hex_padded(64) }})
            mcopy(add(scratch, {{ template_constants.g1_bytes|hex() }}), scratch, {{ template_constants.g1_bytes|hex() }})
            if iszero(staticcall(G1ADD_GAS, {{ template_constants.eip2537.g1add_address|hex() }}, scratch, {{ template_constants.g1add_input_bytes|hex() }}, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(and(
                and(
                    eq(mload(add(scratch, 0x00)), {{ template_constants.eip2537.g1_double_generator.0|hex_padded(64) }}),
                    eq(mload(add(scratch, 0x20)), {{ template_constants.eip2537.g1_double_generator.1|hex_padded(64) }})
                ),
                and(
                    eq(mload(add(scratch, 0x40)), {{ template_constants.eip2537.g1_double_generator.2|hex_padded(64) }}),
                    eq(mload(add(scratch, 0x60)), {{ template_constants.eip2537.g1_double_generator.3|hex_padded(64) }})
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
            if iszero(staticcall(G1MSM_GAS_1PAIR, {{ template_constants.eip2537.g1msm_address|hex() }}, scratch, 0xa0, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
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
            if staticcall(200000, {{ template_constants.eip2537.g1msm_address|hex() }}, scratch, 0xa0, scratch, {{ template_constants.g1_bytes|hex() }}) { revert(0, 0) }

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
            if iszero(staticcall(PAIRING_GAS_2PAIR, {{ template_constants.eip2537.pairing_address|hex() }}, scratch, {{ template_constants.pairing_two_pair_bytes|hex() }}, add(scratch, 0x300), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(mload(add(scratch, 0x300)), 1)) { revert(0, 0) }

            // (d) e(G, G2) * e(G, G2) != 1. Flip the second G1 back to +G.
            mstore(add(scratch, 0x1c0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
            mstore(add(scratch, 0x1e0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
            if iszero(staticcall(PAIRING_GAS_2PAIR, {{ template_constants.eip2537.pairing_address|hex() }}, scratch, {{ template_constants.pairing_two_pair_bytes|hex() }}, add(scratch, 0x300), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(iszero(mload(add(scratch, 0x300)))) { revert(0, 0) }

            // Restore the identity encoding for the probes below.
            for { let off := 0 } lt(off, {{ template_constants.eip2537.smoke_scratch_bytes|hex() }}) { off := add(off, {{ template_constants.word_bytes|hex() }}) } {
                mstore(add(scratch, off), 0)
            }

            // Worst-case generated G1MSM with all identity/zero terms ->
            // identity, 128-byte return. This exercises the largest MSM input
            // length rendered by this verifier instead of only a one-pair
            // smoke call.
            let msm_scratch := {{ memory.constructor_g1msm_smoke_scratch_mptr|hex() }}
            for { let off := 0 } lt(off, {{ constructor_g1msm_smoke_input_bytes|hex() }}) { off := add(off, {{ template_constants.word_bytes|hex() }}) } {
                mstore(add(msm_scratch, off), 0)
            }
            // The production verifier uses G1MSM both for commitments and as
            // the subgroup validator for absorbed proof points.
            if iszero(staticcall(G1MSM_GAS_SMOKE, {{ template_constants.eip2537.g1msm_address|hex() }}, msm_scratch, {{ constructor_g1msm_smoke_input_bytes|hex() }}, scratch, {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})) { revert(0, 0) }
            if or(or(mload(scratch), mload(add(scratch, 0x20))), or(mload(add(scratch, 0x40)), mload(add(scratch, 0x60)))) {
                revert(0, 0)
            }

            // PAIRING_CHECK([(identity_g1, identity_g2), (identity_g1, identity_g2)])
            // -> true, 32-byte return. This matches the runtime two-pair KZG
            // pairing input size and catches absent pairing precompiles,
            // short return data, and obviously incompatible semantics.
            if iszero(staticcall(PAIRING_GAS_2PAIR, {{ template_constants.eip2537.pairing_address|hex() }}, scratch, {{ template_constants.pairing_two_pair_bytes|hex() }}, scratch, {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(returndatasize(), {{ template_constants.word_bytes|hex() }})) { revert(0, 0) }
            if iszero(eq(mload(scratch), 1)) { revert(0, 0) }
        }
    }
