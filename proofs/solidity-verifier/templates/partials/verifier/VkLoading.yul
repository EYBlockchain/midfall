            {%- if self.gas_checkpoints %}
            gas_checkpoint(1) // entry: before VK loading
            {%- endif %}

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
                {%- match self.embedded_vk %}
                {%- when Some with (embedded_vk) %}
                // Embedded VK render: materialize the generated payload
                // directly into the same VK_MPTR memory layout that the
                // external-VK path obtains via extcodecopy.
                //
                // Embedded mode increases verifier bytecode size but avoids an
                // external VK deployment and proof-time extcodecopy. The
                // generated constants below are still organized as the same VK
                // payload words used by the separate contract.
                // The trailing inline names identify generated payload slots.
                {%- for (name, chunk) in embedded_vk.constants %}
                // Header/base/quotient-payload word {{ loop.index0 }}.
                mstore({{ vk_mptr + loop.index0 }}, {{ chunk|hex_padded(64) }}) // {{ name }}
                {%- endfor %}
                {%- for (x_hi, x_lo, y_hi, y_lo) in embedded_vk.fixed_comms %}
                {%- let offset = embedded_vk.constants.len() %}
                // Fixed-column commitment {{ loop.index0 }}.
                // Stored as EIP-2537 padded uncompressed G1:
                //   x_hi, x_lo, y_hi, y_lo.
                mstore({{ vk_mptr + offset + 4 * loop.index0 }}, {{ x_hi|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 1 }}, {{ x_lo|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 2 }}, {{ y_hi|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 3 }}, {{ y_lo|hex_padded(64) }})
                {%- endfor %}
                {%- for (x_hi, x_lo, y_hi, y_lo) in embedded_vk.permutation_comms %}
                {%- let offset = embedded_vk.constants.len() + 4 * embedded_vk.fixed_comms.len() %}
                // Permutation commitment {{ loop.index0 }}.
                // These follow fixed commitments contiguously in the generated
                // VK payload, also as 4-word EIP-2537 G1 slots.
                mstore({{ vk_mptr + offset + 4 * loop.index0 }}, {{ x_hi|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 1 }}, {{ x_lo|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 2 }}, {{ y_hi|hex_padded(64) }})
                mstore({{ vk_mptr + offset + 4 * loop.index0 + 3 }}, {{ y_lo|hex_padded(64) }})
                {%- endfor %}
                {%- when None %}
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
                {%- endmatch %}

                // Cross-check loaded VK header words against the verifier
                // constants used by later parser, domain, and accumulator
                // paths. Codehash pinning protects the external VK address;
                // these checks catch generator drift before calldata parsing
                // chooses a stale schema.
                success := and(success, eq(mload(NUM_INSTANCES_MPTR), {{ num_instances }}))
                success := and(success, eq(mload(K_MPTR), {{ k }}))
                success := and(success, eq(mload(HAS_ACCUMULATOR_MPTR), {{ expected_has_accumulator_word }}))
                success := and(success, eq(mload(ACC_OFFSET_MPTR), {{ expected_acc_offset }}))
                success := and(success, eq(mload(NUM_ACC_LIMBS_MPTR), {{ expected_num_acc_limbs }}))
                success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), {{ expected_num_acc_limb_bits }}))
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
                success := and(success, eq({{ proof_len|hex() }}, calldataload(PROOF_LEN_CPTR)))
                success := and(success, eq({{ num_instances }}, calldataload(NUM_INSTANCE_CPTR)))
                // Calldata must contain exactly the ABI selector, proof bytes,
                // instance-array length, and generated number of instance
                // words. Any trailing bytes fail closed.
                success := and(
                    success,
                    eq(calldatasize(), add(INSTANCE_CPTR, {{ (num_instances * 32)|hex() }}))
                )
                // Stop before any transcript absorption if the ABI/proof shape
                // is not exactly the generated one.
                if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }
            }

            {%- if self.expected_has_accumulator %}
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
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(2) // after VK loading + accumulator public-input precheck
            {%- endif %}
