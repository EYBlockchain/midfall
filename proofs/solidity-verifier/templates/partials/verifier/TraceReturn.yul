            {%- if self.trace %}
            // Terminal trace emission. IDs are intentionally stable across
            // generated verifiers so fixture tooling can diff Rust and
            // Solidity executions without understanding a particular circuit.
            trace_u256(1,  mload(VK_DIGEST_MPTR))
            trace_u256(2,  {{ num_instances }})
            trace_u256(3,  {{ k }})
            trace_u256(4,  mload(N_INV_MPTR))
            trace_u256(5,  mload(OMEGA_MPTR))
            trace_u256(6,  mload(OMEGA_INV_MPTR))
            {%- for phase in user_phases %}
            {%- for j in 0..phase.num_challenges %}
            trace_u256({{ 1000 + phase.challenge_offset + j }}, mload(add(CHALLENGE_MPTR, {{ ((phase.challenge_offset + j) * 32)|hex() }})))
            {%- endfor %}
            {%- endfor %}
            trace_u256(7,  mload(THETA_MPTR))
            trace_u256(8,  mload(BETA_MPTR))
            trace_u256(9,  mload(GAMMA_MPTR))
            trace_u256(10, mload(Y_MPTR))
            trace_u256(11, mload(X_MPTR))
            {%- if num_trashcans != 0 %}
            trace_u256(12, mload(TRASH_CHALLENGE_MPTR))
            {%- endif %}
            trace_u256(13, mload(X1_MPTR))
            trace_u256(14, mload(X2_MPTR))
            trace_u256(15, mload(X3_MPTR))
            trace_u256(16, mload(X4_MPTR))
            trace_u256(17, mload(X_N_MPTR))
            trace_u256(18, mload(X_N_MINUS_1_INV_MPTR))
            trace_u256(19, mload(L_LAST_MPTR))
            trace_u256(20, mload(L_BLIND_MPTR))
            trace_u256(21, mload(L_0_MPTR))
            trace_u256(22, mload(INSTANCE_EVAL_MPTR))
            trace_u256(23, mload(LINEARIZATION_EVAL_MPTR))
            // Rust traces often print the positive numerator; the verifier
            // stores the negated expected scalar for the linearized opening.
            trace_u256(36, addmod(0, sub(r, mload(LINEARIZATION_EVAL_MPTR)), r))
            // QUOTIENT_MPTR carries scalar metadata in the fused production
            // path. Zero the unused point words before tracing it as a G1 slot.
            mstore(add(QUOTIENT_MPTR, 0x40), 0)
            mstore(add(QUOTIENT_MPTR, 0x60), 0)
            trace_point(24, QUOTIENT_MPTR)
            trace_point(25, F_COM_MPTR)
            trace_point(26, PI_MPTR)
            trace_u256(31, mload(F_EVAL_MPTR))
            trace_u256(32, mload(V_MPTR))
            trace_point(33, FINAL_COM_MPTR)
            trace_u256(35, success)
            {%- if self.expected_has_accumulator %}
            trace_point(29, ACC_LHS_MPTR)
            trace_point(30, ACC_RHS_MPTR)
            {%- endif %}
            {%- endif %}

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
