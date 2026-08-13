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
            {%- if self.expected_has_accumulator %}
            {
                let batch_ptr := {{ memory.accumulator_pairing_batch_mptr|hex() }}

                // Domain || vk_digest || KZG rhs/lhs || accumulator rhs/lhs.
                // vk_digest makes alpha's binding to the verifying key local
                // instead of transitive-through-the-points (audit I-7).
                mstore(batch_ptr, {{ template_constants.accumulator.pairing_batch_domain_tag_hex }})
                mstore(add(batch_ptr, {{ template_constants.accumulator.pairing_batch_vk_digest_offset|hex() }}), mload(VK_DIGEST_MPTR))
                mcopy(add(batch_ptr, {{ template_constants.accumulator.pairing_batch_rhs_offset|hex() }}),  PAIRING_RHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                mcopy(add(batch_ptr, {{ template_constants.accumulator.pairing_batch_lhs_offset|hex() }}),  PAIRING_LHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                mcopy(add(batch_ptr, {{ template_constants.accumulator.pairing_batch_acc_rhs_offset|hex() }}), ACC_RHS_MPTR,     {{ template_constants.g1_bytes|hex() }})
                mcopy(add(batch_ptr, {{ template_constants.accumulator.pairing_batch_acc_lhs_offset|hex() }}), ACC_LHS_MPTR,     {{ template_constants.g1_bytes|hex() }})
                // alpha is Fiat-Shamir over the fully materialized pairing
                // inputs. Replace the negligible zero draw with one so the
                // accumulator equation cannot be accidentally dropped.
                let acc_pair_alpha := mod(keccak256(batch_ptr, {{ template_constants.accumulator.pairing_batch_hash_bytes|hex() }}), r)
                if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }

                // PAIRING_RHS_MPTR += alpha * ACC_RHS_MPTR.
                // First compute alpha * ACC_RHS with a one-pair G1MSM, then
                // add it into the KZG RHS point.
                mcopy(batch_ptr, ACC_RHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                mstore(add(batch_ptr, {{ template_constants.g1_bytes|hex() }}), acc_pair_alpha)
                if success {
                    success := staticcall(G1MSM_GAS_1PAIR, {{ template_constants.eip2537.g1msm_address|hex() }}, batch_ptr, {{ template_constants.g1_msm_pair_bytes|hex() }}, batch_ptr, {{ template_constants.g1_bytes|hex() }})
                    success := and(success, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                }
                mcopy(add(batch_ptr, {{ template_constants.g1_bytes|hex() }}), PAIRING_RHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                if success {
                    success := staticcall(G1ADD_GAS, {{ template_constants.eip2537.g1add_address|hex() }}, batch_ptr, {{ template_constants.g1add_input_bytes|hex() }}, PAIRING_RHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                    success := and(success, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                }

                // PAIRING_LHS_MPTR += alpha * ACC_LHS_MPTR.
                // Mirror the same randomized batching on the KZG LHS point.
                mcopy(batch_ptr, ACC_LHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                mstore(add(batch_ptr, {{ template_constants.g1_bytes|hex() }}), acc_pair_alpha)
                if success {
                    success := staticcall(G1MSM_GAS_1PAIR, {{ template_constants.eip2537.g1msm_address|hex() }}, batch_ptr, {{ template_constants.g1_msm_pair_bytes|hex() }}, batch_ptr, {{ template_constants.g1_bytes|hex() }})
                    success := and(success, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                }
                mcopy(add(batch_ptr, {{ template_constants.g1_bytes|hex() }}), PAIRING_LHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                if success {
                    success := staticcall(G1ADD_GAS, {{ template_constants.eip2537.g1add_address|hex() }}, batch_ptr, {{ template_constants.g1add_input_bytes|hex() }}, PAIRING_LHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                    success := and(success, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                }
            }
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(15) // after public accumulator pairing batch prep (omitted for no-accumulator VKs)
            {%- endif %}

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
            if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)

            {%- if self.gas_checkpoints %}
            gas_checkpoint(16) // after final ec_pairing
            {%- endif %}
