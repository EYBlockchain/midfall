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
                {%- for code_block in pcs_computations %}
                // Generated PCS sub-block {{ loop.index }}. These lines are
                // emitted by the multi-prepare lowering pass and are kept
                // grouped so gas checkpoints can attribute their cost.
                {
                    {%- for line in code_block %}
                    {{ line }}
                    {%- endfor %}
                }
                {%- if self.gas_checkpoints && !loop.last %}
                gas_checkpoint({{ 17 + loop.index0 }}) // after PCS sub-block {{ loop.index }}
                {%- endif %}
                {%- endfor %}
            }

            {%- if self.gas_checkpoints %}
            gas_checkpoint(14) // after PCS computation block (= sub-block 6)
            {%- endif %}

            {%- if self.trace %}
            // Trace the final pairing inputs and selector accumulator buckets
            // after PCS expansion, matching the Rust verifier trace labels.
            trace_point(27, PAIRING_LHS_MPTR)
            trace_point(28, PAIRING_RHS_MPTR)
            {%- for _ in simple_selector_cols %}
            trace_u256({{ selector_trace_base + loop.index0 }}, mload(add(SELECTOR_ACC_MPTR, {{ (loop.index0 * 32)|hex() }})))
            {%- endfor %}
            {%- endif %}
