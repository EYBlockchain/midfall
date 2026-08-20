            // __phase:lagrange_batch_invert
            // ===============================================================
            // Lagrange & instance-evaluation block (pure Fr arithmetic).
            // ===============================================================
            // MF-4: hoisted so the section boundary below can tell a failed
            // modexp (chain fault) from a rejected denominator (x landed on a
            // domain point) instead of reporting both as PrecompileFailed.
            let lagrange_precompile_failed := 0
            {
                let k := {{ k }}
                let x := mload(X_MPTR)
                // Compute x^n by repeated squaring, with n = 2^k.
                let x_n := x
                for { let idx := 0 } lt(idx, k) { idx := add(idx, 1) } {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                // First pass writes denominators (x - omega_i) for every
                // Lagrange value needed below, then appends x^n - 1. The
                // batch inversion pass turns all of them into inverses in one
                // modexp call. The run lives in the dedicated planner-registered
                // LAGRANGE_DENOMS_MPTR scratch region; only the distilled
                // results below are persisted into the named theta slots.
                let mptr := LAGRANGE_DENOMS_MPTR
                let mptr_end := add(mptr, {{ ((num_instances + num_neg_lagranges) * 32)|hex() }})
                {%- if num_instances == 0 %}
                // No public instances still need one denominator slot so
                // L_0 can be recovered for boundary identities.
                mptr_end := add(mptr_end, 0x20)
                {%- endif %}
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success, lagrange_precompile_failed := batch_invert(success, LAGRANGE_DENOMS_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)

                // Convert inverted denominators into Lagrange evaluations:
                // L_i(x) = (x^n - 1) * n^-1 * omega_i / (x - omega_i).
                mptr := LAGRANGE_DENOMS_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) } {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                // l_blind is the sum of the negative-rotation Lagrange terms
                // used by the midnight-proofs blinding identity.
                let l_blind := mload(add(LAGRANGE_DENOMS_MPTR, 0x20))
                let l_i_cptr := add(LAGRANGE_DENOMS_MPTR, 0x40)
                for { let l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, {{ (num_neg_lagranges * 32)|hex() }}) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) } {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                // Public instance polynomial evaluation at x. Instance words
                // have already been range-checked and absorbed in transcript
                // order; this loop only forms the linear combination.
                let instance_eval := 0
                for {
                        let instance_cptr := INSTANCE_CPTR
                        let instance_cptr_end := add(instance_cptr, {{ (num_instances * 32)|hex() }})
                    }
                    lt(instance_cptr, instance_cptr_end)
                    { instance_cptr := add(instance_cptr, 0x20)
                      l_i_cptr := add(l_i_cptr, 0x20) } {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                // Persist the derived values into named memory slots consumed
                // by quotient reconstruction and PCS preparation.
                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(LAGRANGE_DENOMS_MPTR)
                let l_0 := mload(add(LAGRANGE_DENOMS_MPTR, {{ (num_neg_lagranges * 32)|hex() }}))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            {%- if self.gas_checkpoints %}
            gas_checkpoint(11) // after Lagrange + instance evaluation block
            {%- endif %}

            if iszero(success) {
                // A zero or non-canonical denominator is a rejected input,
                // not a broken chain: the only way to reach it is a squeezed
                // x that coincides with a domain point (probability ~n/r).
                if lagrange_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
                fail(ERR_PROOF_REJECTED)
            }
