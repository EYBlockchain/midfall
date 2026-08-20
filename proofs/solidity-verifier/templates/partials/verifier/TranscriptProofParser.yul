            // __phase:transcript
            // ===============================================================
            // Transcript: VK digest + instances + proof.
            //
            // This block is the Solidity mirror of the native Midfall verifier
            // transcript schedule. It does three jobs at once:
            //
            //   1. Absorb public data and proof bytes into the streaming
            //      Keccak transcript in exactly the native order.
            //   2. Decode/range-check proof scalars and canonical G1 calldata.
            //   3. Copy proof commitments/evaluations into planned memory
            //      slots consumed by Lagrange, quotient, PCS, and pairing
            //      blocks later in the verifier.
            //
            // `buf_len` is a write cursor into the transcript buffer. The
            // helper functions append bytes and return the new cursor; squeeze
            // helpers hash memory[TRANSCRIPT_MPTR..buf_len), reseed the buffer
            // with the digest, and write the sampled Fr challenge to memory.
            // ===============================================================
            let buf_len := transcript_init()
            // VK_DIGEST_MPTR holds the digest as a BE 32-byte word (the
            // VK contract stores it via `mstore`, which matches the
            // Keccak Fq transcript input).
            //
            // This digest commits to the verifier key / constraint system
            // before any proof material is read.
            buf_len := common_word(buf_len, mload(VK_DIGEST_MPTR))

            // Absorb committed_pi = G1Affine::identity() when the
            // `committed-instances` feature is on in midnight-proofs.
            // Under the patched `Hashable<Keccak256>::to_input` (see
            // `midfall/proofs/src/transcript/implementors.rs`), the
            // identity hashes as 128 zero bytes (EIP-2537 (0,0)
            // convention), NOT the 48-byte ZCash compressed form
            // 0xc0||47*0x00 that the previous emitter produced.
            // Native verifier absorbs this BEFORE the instance count.
            {
                // 128 zero bytes: zero out 4 consecutive 32-byte words
                // at buf_len.
                // This is a raw transcript absorb, not a memory slot kept for
                // later elliptic-curve operations.
                mstore(buf_len, 0)
                mstore(add(buf_len, 0x20), 0)
                mstore(add(buf_len, 0x40), 0)
                mstore(add(buf_len, 0x60), 0)
                buf_len := add(buf_len, 0x80)
            }

            {
                // Native verifier absorbs a length scalar before instance
                // values; Keccak Fq transcript input is canonical BE.
                // The ABI length was already checked against this generated
                // constant in VkLoading.yul.
                buf_len := common_word(buf_len, {{ num_instances }})

                let instance_cptr := INSTANCE_CPTR
                for { let instance_cptr_end := add(instance_cptr, {{ (num_instances * 32)|hex() }}) }
                    lt(instance_cptr, instance_cptr_end)
                    { instance_cptr := add(instance_cptr, 0x20) } {
                    let inst_be := calldataload(instance_cptr)
                    // Public inputs are BLS12-381 scalar-field elements. They
                    // must be canonical before transcript absorption; accepting
                    // non-canonical encodings would admit transcript aliases.
                    success := and(success, lt(inst_be, r))
                    // Instances are passed BE in calldata, matching the
                    // Keccak Fq transcript input.
                    buf_len := common_word(buf_len, inst_be)
                }
                if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }
            }

            {%- if self.gas_checkpoints %}
            gas_checkpoint(3) // after VK digest + committed_pi + instance absorbs
            {%- endif %}

            // ===============================================================
            // Per-user-phase reads + challenge squeezes.
            //
            // Each proof G1 is already EIP-2537 padded in calldata. The
            // verifier validates and absorbs that 128-byte form, then copies
            // it into the corresponding per-category MPTR. The PCS /
            // quotient-fold blocks below dereference those MPTRs.
            //
            // All G1 reads follow the same pattern:
            //   - common_uncompressed_g1 canonicalizes/range-checks the two Fp
            //     coordinates and appends the exact 128 calldata bytes;
            //   - calldatacopy stores the same 4-word G1 slot in planned
            //     memory for later EIP-2537 precompile calls;
            //   - proof_cptr advances by one G1 byte length.
            // ===============================================================
            // proof_cptr walks the raw proof bytes inside the ABI `bytes`
            // payload. Every successful read advances it exactly once, and the
            // final equality check below proves the parser consumed the whole
            // generated proof layout.
            let proof_cptr := PROOF_CPTR
            // advice_walk mirrors proof commitment order into the contiguous
            // G1 commitment memory region used by PCS and quotient folding.
            let advice_walk := ADVICE_COMMS_MPTR_BASE
            {%- if self.trace %}
            // Trace IDs are monotonic across all commitments/evaluations in
            // transcript order, matching the Rust trace comparison harness.
            let proof_commit_trace_id := {{ proof_commit_trace_base }}
            let proof_eval_trace_id := {{ proof_eval_trace_base }}
            {%- endif %}

            {%- for phase in user_phases %}
            // ---- User phase {{ loop.index }} ----
            // Advice commitments for this phase are absorbed before the phase's
            // challenge squeezes. The number of commitments and challenges is
            // generated from the protocol plan.
            for { let end := add(proof_cptr, {{ phase.advice_bytes|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                // Store the commitment at its phase-ordered advice slot.
                calldatacopy(advice_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, advice_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                advice_walk := add(advice_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }
            {%- for j in 0..phase.num_challenges %}
            // User-phase challenge {{ j }} for phase {{ loop.index }}. The
            // challenge slots are contiguous under CHALLENGE_MPTR, but each
            // phase owns a generated offset.
            buf_len := squeeze_to(buf_len, add(CHALLENGE_MPTR, {{ ((phase.challenge_offset + j) * 32)|hex() }}))
            {%- endfor %}
            {%- endfor %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(4) // after user-phase advice reads + user challenge squeezes
            {%- endif %}

            // ---- theta ----
            // From this point onward the transcript alternates between
            // squeezed challenges and proof commitments exactly as
            // midnight-proofs does in `plonk/verifier.rs`.
            // theta batches lookup input expressions.
            buf_len := squeeze_to(buf_len, THETA_MPTR)

            {%- if num_lookups != 0 %}
            // ---- multiplicities (one G1 per lookup) ----
            // Lookup multiplicity commitments are absorbed after theta and
            // copied into their own contiguous G1 region.
            let lookup_m_walk := LOOKUP_M_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, {{ codegen_layout.proof.lookup_multiplicities.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(lookup_m_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, lookup_m_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                lookup_m_walk := add(lookup_m_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(5) // after theta squeeze + lookup multiplicities
            {%- endif %}

            // ---- beta, gamma ----
            // beta and gamma are the permutation/lookup randomizers. They are
            // squeezed after lookup multiplicities and before permutation
            // product commitments, matching the native verifier schedule.
            buf_len := squeeze_to(buf_len, BETA_MPTR)
            buf_len := squeeze_to(buf_len, GAMMA_MPTR)

            {%- if num_permutation_zs != 0 %}
            // ---- permutation Z products ----
            // Permutation product commitments are used by the permutation
            // identities in the quotient numerator and later by PCS openings.
            let perm_z_walk := PERM_Z_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, {{ codegen_layout.proof.permutation_products.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(perm_z_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, perm_z_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                perm_z_walk := add(perm_z_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(6) // after beta/gamma + permutation Z products
            {%- endif %}

            {%- if lookup_h_plus_acc != 0 %}
            // ---- lookup helpers + accumulators (per-lookup) ----
            // Each lookup contributes zero or more helper commitments followed
            // by its lookup accumulator Z commitment. The generated layout keeps
            // helper commitments and accumulator commitments in separate memory
            // regions because the quotient/PCS schedules address them
            // differently.
            let lookup_helper_walk := LOOKUP_HELPER_COMMS_MPTR_BASE
            let lookup_z_walk := LOOKUP_Z_COMMS_MPTR_BASE
            {%- for lookup in codegen_layout.proof.lookups %}
            // lookup {{ loop.index0 }}: {{ lookup.helpers.item_count }} helper(s) + 1 acc
            // Helper commitments for lookup {{ loop.index0 }}.
            for { let end := add(proof_cptr, {{ lookup.helpers.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(lookup_helper_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, lookup_helper_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                lookup_helper_walk := add(lookup_helper_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }
            // Accumulator commitment for lookup {{ loop.index0 }}. This is
            // always one G1 when the lookup section is present.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(lookup_z_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
            {%- if self.trace %}
            trace_point(proof_commit_trace_id, lookup_z_walk)
            proof_commit_trace_id := add(proof_commit_trace_id, 1)
            {%- endif %}
            lookup_z_walk := add(lookup_z_walk, {{ template_constants.g1_bytes|hex() }})
            proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            {%- endfor %}
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(7) // after lookup helpers + Z accumulators
            {%- endif %}

            // ---- trash_challenge ----
            // Midnight squeezes this challenge unconditionally, even when the
            // circuit has no trash arguments.
            // Keeping this squeeze unconditional preserves transcript
            // compatibility across circuits with and without trash columns.
            buf_len := squeeze_to(buf_len, TRASH_CHALLENGE_MPTR)
            {%- if num_trashcans != 0 %}
            // ---- trashcans ----
            // Trashcan commitments are optional, but when present they are
            // absorbed before y so the quotient batching challenge binds them.
            let trashcan_walk := TRASHCAN_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, {{ codegen_layout.proof.trash.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(trashcan_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, trashcan_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                trashcan_walk := add(trashcan_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }
            {%- endif %}

            {%- if self.gas_checkpoints %}
            gas_checkpoint(8) // after trash_challenge + trashcans
            {%- endif %}

            // ---- y ----
            // y batches all quotient identities. Quotient commitments are read
            // only after y is sampled, matching the Rust verifier flow.
            buf_len := squeeze_to(buf_len, Y_MPTR)

            // ---- quotient commitment(s) ----
            // Each uncompressed quotient commitment is calldatacopied directly to
            // QUOTIENT_LIMB_COMMS_MPTR_BASE; the Horner fold below reads
            // them back from memory. common_uncompressed_g1 absorbs the
            // 128-byte calldata form into the transcript verbatim.
            //
            // Multi-limb quotient mode reads several Q_i commitments; single-H
            // mode renders this loop with one limb.
            let quotient_walk := QUOTIENT_LIMB_COMMS_MPTR_BASE
            for { let end := add(proof_cptr, {{ codegen_layout.proof.quotient_limbs.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                buf_len := common_uncompressed_g1(buf_len, proof_cptr)
                calldatacopy(quotient_walk, proof_cptr, {{ template_constants.g1_bytes|hex() }})
                {%- if self.trace %}
                trace_point(proof_commit_trace_id, quotient_walk)
                proof_commit_trace_id := add(proof_commit_trace_id, 1)
                {%- endif %}
                quotient_walk := add(quotient_walk, {{ template_constants.g1_bytes|hex() }})
                proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})
            }

            {%- if self.gas_checkpoints %}
            gas_checkpoint(9) // after y squeeze + quotient-limb reads
            {%- endif %}

            // ---- x ----
            // x is the main evaluation point. Values read after this point are
            // alleged polynomial evaluations at x or derived PCS openings.
            buf_len := squeeze_to(buf_len, X_MPTR)

            // ---- evaluations ----
            // Optimisation H3: the off-chain Solidity proof shim rewrites
            // proof scalars into BE calldata words. Spill each decoded eval
            // into REVERSED_EVALS_MPTR in the same iteration we range-check
            // it, so downstream references can use cheap mload.
            //
            // The Rust verifier conceptually reads evaluations in query order.
            // The lowering plan arranges REVERSED_EVALS_MPTR in the order used
            // by the quotient VM/direct evaluator, hence the generated name.
            {
                let eval_buf := REVERSED_EVALS_MPTR
                for { let end := add(proof_cptr, {{ codegen_layout.proof.evals.byte_len|hex() }}) }
                    lt(proof_cptr, end)
                    {} {
                    let eval := calldataload(proof_cptr)
                    // Proof evaluation scalars must be canonical Fr elements
                    // before they are absorbed or made available to quotient
                    // reconstruction.
                    if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
                    // Spill for quotient numerator and PCS codegen.
                    mstore(eval_buf, eval)
                    eval_buf := add(eval_buf, {{ template_constants.word_bytes|hex() }})
                    // Absorb the exact BE field word used by the native
                    // Keccak transcript.
                    buf_len := common_word(buf_len, eval)
                    {%- if self.trace %}
                    trace_u256(proof_eval_trace_id, eval)
                    proof_eval_trace_id := add(proof_eval_trace_id, 1)
                    {%- endif %}
                    proof_cptr := add(proof_cptr, {{ template_constants.word_bytes|hex() }})
                }
            }

            // ---- x1, x2 ----
            // x1 and x2 batch the KZG multi-opening reduction. They are
            // squeezed after all polynomial evaluations are absorbed.
            buf_len := squeeze_to(buf_len, X1_MPTR)
            buf_len := squeeze_to(buf_len, X2_MPTR)

            // ---- f_com (1 uncompressed G1) ----
            // f_com is the commitment to the batched polynomial used by the PCS
            // multi-open protocol. It is both transcript material and later
            // pairing/MSM input.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(F_COM_MPTR, proof_cptr, {{ template_constants.g1_bytes|hex() }})
            {%- if self.trace %}
            trace_point(proof_commit_trace_id, F_COM_MPTR)
            proof_commit_trace_id := add(proof_commit_trace_id, 1)
            {%- endif %}
            proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})

            // ---- x3 ----
            // x3 is the PCS evaluation point for f_com.
            buf_len := squeeze_to(buf_len, X3_MPTR)
            {%- if truncated_challenges %}
            // truncated-challenges mirrors midnight-proofs
            // proofs/src/poly/kzg/mod.rs:
            //   - x3 is the f_com evaluation point and is truncated
            //     immediately after squeeze.
            //   - x1 and x4 remain full squeezed Fr words, but later PCS
            //     batching stores truncate(x1^i) and truncate(x4^i) while
            //     keeping the internal power accumulators full precision.
            // This direct x3 mask is therefore one part of the PCS truncation
            // rule, not the only truncated value used by the verifier.
            mstore(X3_MPTR, and(mload(X3_MPTR), 0xffffffffffffffffffffffffffffffff))
            {%- endif %}

            // ---- q_evals (one Fq per point set) ----
            // q_evals are not spilled into REVERSED_EVALS_MPTR because the PCS
            // emitter reads them as a contiguous calldata range from the saved
            // Q_EVAL_CPTR_MPTR cursor.
            //
            // Each q_eval is the claimed evaluation for one prepared point set
            // in the KZG multi-open reduction. They are still transcript
            // material and must be range-checked as Fr scalars.
            mstore(Q_EVAL_CPTR_MPTR, proof_cptr)
            for { let end := add(proof_cptr, {{ codegen_layout.proof.q_evals.byte_len|hex() }}) }
                lt(proof_cptr, end)
                {} {
                let eval := calldataload(proof_cptr)
                // Canonical Fr check before transcript absorption.
                if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
                buf_len := common_word(buf_len, eval)
                {%- if self.trace %}
                trace_u256(proof_eval_trace_id, eval)
                proof_eval_trace_id := add(proof_eval_trace_id, 1)
                {%- endif %}
                proof_cptr := add(proof_cptr, {{ template_constants.word_bytes|hex() }})
            }

            // ---- x4 ----
            // x4 is the final PCS batching challenge, sampled after q_evals
            // and before the opening proof point pi.
            buf_len := squeeze_to(buf_len, X4_MPTR)

            // ---- pi (1 uncompressed G1) ----
            // pi is the KZG opening proof commitment. It is the last proof
            // object absorbed into the transcript and later becomes one side of
            // the final pairing check.
            buf_len := common_uncompressed_g1(buf_len, proof_cptr)
            calldatacopy(PI_MPTR, proof_cptr, {{ template_constants.g1_bytes|hex() }})
            {%- if self.trace %}
            trace_point(proof_commit_trace_id, PI_MPTR)
            proof_commit_trace_id := add(proof_commit_trace_id, 1)
            {%- endif %}
            proof_cptr := add(proof_cptr, {{ template_constants.g1_bytes|hex() }})

            // The hand-rolled proof parser must consume exactly the ABI
            // `proof` bytes before the `instances` length word. This is
            // redundant with the generated proof length today, but makes
            // future proof-layout drift fail closed.
            //
            // NUM_INSTANCE_CPTR is the calldata word immediately after the
            // dynamic proof bytes payload. If proof_cptr lands anywhere else,
            // some section was under-read or over-read.
            if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }

            // `success` carries deferred canonicality failures from public
            // instance reads. G1/proof scalar helpers revert immediately.
            if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }

            {%- if self.gas_checkpoints %}
            gas_checkpoint(10) // after evaluations + x1/x2 + f_com + x3 + q_evals + x4 + pi (transcript done)
            {%- endif %}
