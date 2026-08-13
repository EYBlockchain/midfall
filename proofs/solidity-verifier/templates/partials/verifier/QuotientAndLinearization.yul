            {%- match quotient_external %}
            {%- when Some with (qext) %}
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
                {%- match self.expected_quotient_codehash %}
                {%- when Some with (_) %}
                // The quotient evaluator is as correctness-critical as the VK:
                // it reconstructs the y-batched identity numerator and
                // selector buckets. Re-check the pinned runtime before every
                // external call, mirroring the VK freshness guard above.
                if iszero(and(
                    eq(extcodesize(quotientEvaluator), EXPECTED_QUOTIENT_LENGTH),
                    eq(extcodehash(quotientEvaluator), EXPECTED_QUOTIENT_CODEHASH_WORD)
                )) { fail(ERR_VK_MISMATCH) }
                {%- when None %}
                {%- endmatch %}
                {%- if self.trace %}
                if iszero(call(gas(), quotientEvaluator, 0, {{ qext.frame_base|hex() }}, {{ qext.frame_len|hex() }}, q_out, {{ qext.output_len|hex() }})) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                {%- else %}
                // gas() forwarding is deliberate here, unlike the precompile
                // call sites: this is a regular contract call, so a reverting
                // or failing callee refunds its unused gas -- only precompile
                // ERRORS burn everything forwarded (EIP-2537). The callee is
                // also pinned by codehash above, not attacker-supplied.
                if iszero(staticcall(gas(), quotientEvaluator, {{ qext.frame_base|hex() }}, {{ qext.frame_len|hex() }}, q_out, {{ qext.output_len|hex() }})) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                {%- endif %}
                if iszero(eq(returndatasize(), {{ qext.output_len|hex() }})) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                if iszero(eq(mload(q_out), {{ qext.magic|hex_padded(64) }})) { fail(ERR_QUOTIENT_PROGRAM_INVALID) }
                // Word 1 is the negated y-batched identity numerator, stored
                // in the same memory slot used by the monolithic path.
                mstore(QUOTIENT_EVAL_MPTR, mload(add(q_out, 0x20)))
                {%- if simple_selector_cols.len() > 0 %}
                // Remaining return words are selector linearization buckets.
                // Copy them back into the canonical selector accumulator region
                // so the PCS code path is identical for split and monolithic
                // quotient renders.
                for { let q_i := 0 } lt(q_i, {{ simple_selector_cols.len() }}) { q_i := add(q_i, 1) } {
                    mstore(add(SELECTOR_ACC_MPTR, shl(5, q_i)), mload(add(q_out, add(0x40, shl(5, q_i)))))
                }
                {%- endif %}
            }
            {%- when None %}
            {%- include "partials/quotient_numerator/QuotientHelpers.yul" %}
            {%- include "partials/quotient_numerator/QuotientNumeratorBlock.yul" %}
            {%- endmatch %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(12) // after batched identity numerator reconstruction
            {%- endif %}

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
                let k := {{ k }}
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

            {%- if self.trace %}
            // Materialize the linearization commitment for trace comparison.
            // The production path expands the same terms directly into the
            // fused final PCS MSM below.
            {
                let lin_scratch := add(SELECTOR_ACC_MPTR, {{ (simple_selector_cols.len() * 0x20)|hex() }})
                let lin_pair := lin_scratch
                let lin_cur_scalar := mload(add(QUOTIENT_MPTR, 0x20))
                {%- for _ in 0..num_quotients %}
                // Trace-only quotient limb term: Q_i * ((1 - x^n) * x_split^i).
                mcopy(lin_pair, add(QUOTIENT_LIMB_COMMS_MPTR_BASE, {{ (loop.index0 * 0x80)|hex() }}), 0x80)
                mstore(add(lin_pair, 0x80), lin_cur_scalar)
                lin_pair := add(lin_pair, 0xa0)
                {%- if !loop.last %}
                lin_cur_scalar := mulmod(lin_cur_scalar, mload(QUOTIENT_MPTR), r)
                {%- endif %}
                {%- endfor %}
                {%- for col in simple_selector_cols %}
                // Trace-only selector term: fixed selector commitment times
                // the generated selector accumulator bucket.
                mcopy(lin_pair, {{ (fixed_comm_mptr + col * 0x80)|hex() }}, 0x80)
                mstore(add(lin_pair, 0x80), mload(add(SELECTOR_ACC_MPTR, {{ (loop.index0 * 0x20)|hex() }})))
                lin_pair := add(lin_pair, 0xa0)
                {%- endfor %}
                let lin_trace_ok := staticcall(gas(), {{ template_constants.eip2537.g1msm_address|hex() }}, lin_scratch, {{ ((num_quotients + simple_selector_cols.len()) * template_constants.g1_msm_pair_bytes)|hex() }}, lin_scratch, {{ template_constants.g1_bytes|hex() }})
                lin_trace_ok := and(lin_trace_ok, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                if iszero(lin_trace_ok) {
                    mstore(TRACE_U256_MPTR, 34)
                    revert(TRACE_U256_MPTR, 0x20)
                }
                trace_point(34, lin_scratch)
            }
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(13) // after linearization scalar prep
            {%- endif %}
