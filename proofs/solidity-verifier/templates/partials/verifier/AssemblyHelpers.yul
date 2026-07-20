            // Inverse of a Fr scalar via modexp(x, r-2, r). The verifier
            // calls this only after transcript absorption is complete, so it
            // reuses the dead transcript buffer just below VK_MPTR instead of
            // a fixed post-VK address that can collide with live PCS scratch
            // when the VK payload becomes smaller.
            function scalar_inv(x) -> inv {
                // Zero has no multiplicative inverse in Fr; callers rely on a
                // revert here rather than a bogus modexp result. Check the
                // full canonical range, not just the literal word 0: for any
                // x congruent to 0 mod r (x = r, say) modexp returns 0, which
                // downstream mulmod chains would silently absorb. Every
                // current call site feeds addmod/mulmod output, so this only
                // guards against a future emitter passing a raw scalar.
                if iszero(lt(x, FR_MODULUS)) { revert(0, 0) }
                if iszero(x) { revert(0, 0) }
                let p := {{ memory.scalar_inv_scratch_mptr|hex() }}
                // EIP-198 modexp frame:
                //   [base_len, exp_len, mod_len, base, exponent, modulus]
                mstore(add(p, {{ template_constants.modexp.base_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})        // base len
                mstore(add(p, {{ template_constants.modexp.exp_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})        // exp len
                mstore(add(p, {{ template_constants.modexp.mod_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})        // mod len
                mstore(add(p, {{ template_constants.modexp.base_offset|hex() }}), x)
                mstore(add(p, {{ template_constants.modexp.exp_offset|hex() }}), sub(FR_MODULUS, 2))
                mstore(add(p, {{ template_constants.modexp.mod_offset|hex() }}), FR_MODULUS)
                if iszero(staticcall(gas(), {{ template_constants.modexp.address|hex() }}, p, {{ template_constants.modexp.frame_bytes|hex() }}, p, {{ template_constants.modexp.output_bytes|hex() }})) { revert(0, 0) }
                if iszero(eq(returndatasize(), {{ template_constants.modexp.output_bytes|hex() }})) { revert(0, 0) }
                inv := mload(p)
            }

            // ---------- Streaming Keccak256 transcript helpers ----------
            //
            // The transcript buffer lives at
            // memory[TRANSCRIPT_MPTR..buf_len). On verifier entry it starts
            // empty. Each common(input) appends raw bytes. squeeze_*(buf_len)
            // computes one Keccak digest, reseeds the buffer with that
            // 32-byte digest, and samples a Fq element as
            // uint256(digest_be) mod r.

            function transcript_init() -> buf_len {
                // Empty transcript buffer starts exactly at TRANSCRIPT_MPTR.
                buf_len := TRANSCRIPT_MPTR
            }

            // Append one 32-byte big-endian field/transcript word at the
            // current end of the transcript buffer.
            function common_word(buf_len, word) -> ret {
                mstore(buf_len, word)
                ret := add(buf_len, 32)
            }

            // Absorb a BLS12-381 G1 point in EIP-2537 padded
            // uncompressed form (4 calldata words = 128 bytes:
            // x_hi || x_lo || y_hi || y_lo, each coord = 16 zero
            // pad bytes + 48 big-endian field bytes) into the
            // transcript buffer at `buf_len`.
            //
            // Matches the patched `Hashable<Keccak256> for
            // midnight_curves::G1Projective::to_input` in
            // midnight-proofs, which now emits the same 128-byte form
            // (`midfall/proofs/src/transcript/implementors.rs`). The
            // previous emitter hashed the 48-byte ZCash compressed
            // encoding instead and ran a 384-bit `lex(y) > lex(p − y)`
            // ladder + identity flag fixup to derive the sign bit on
            // the fly; switching to the uncompressed form drops that
            // ladder entirely.
            //
            // Canonicality: reject non-zero bytes in the top 16 bytes
            // of each `_hi` calldata word and reject coordinates
            // outside Fp. Normalizing those bytes before hashing would
            // make multiple calldata encodings share one transcript.
            //
            // This helper does not run an independent curve/subgroup
            // check. Instead, ProtocolPlan::validate rejects generated
            // plans where an absorbed proof commitment would not later be
            // consumed by an EIP-2537 G1MSM or pairing path, and those
            // precompiles perform the curve/subgroup validation.
            //
            // The point's uncompressed form remains in calldata; the
            // call site is responsible for `calldatacopy`-ing it into
            // memory afterwards if it needs the on-curve coordinates.
            function common_uncompressed_g1(buf_len, cptr) -> ret {
                let x_hi_word := calldataload(cptr)
                let x_lo := calldataload(add(cptr, 0x20))
                let y_hi_word := calldataload(add(cptr, 0x40))
                let y_lo := calldataload(add(cptr, 0x60))
                if shr(128, x_hi_word) { revert(0, 0) }
                if shr(128, y_hi_word) { revert(0, 0) }

                let x_hi := and(x_hi_word, 0xffffffffffffffffffffffffffffffff)
                let y_hi := and(y_hi_word, 0xffffffffffffffffffffffffffffffff)
                if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
                    revert(0, 0)
                }
                if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
                    revert(0, 0)
                }

                // Memcpy the 4 calldata words (128 bytes) verbatim
                // into the keccak buffer.
                calldatacopy(buf_len, cptr, 0x80)
                ret := add(buf_len, 0x80)
            }

            // One Keccak finalization + reseed. Returns the new buffer
            // cursor (= TRANSCRIPT_MPTR + 32) and stores the squeezed Fq at
            // `mptr`.
            function squeeze_to(buf_len, mptr) -> ret {
                let h0 := keccak256(TRANSCRIPT_MPTR, sub(buf_len, TRANSCRIPT_MPTR))
                // Reseed: write the 32-byte digest at start of buffer.
                mstore(TRANSCRIPT_MPTR, h0)
                let r := FR_MODULUS
                // Sample Fq as uint256(keccak_digest_be) mod r.
                mstore(mptr, mod(h0, r))
                ret := add(TRANSCRIPT_MPTR, 32)
            }

            // ---------- EC primitives (EIP-2537 wrappers) ----------
            //
            // These mirror the BN254 helpers but operate on 4-word G1
            // points. They use planned memory windows above Solidity's
            // reserved prefix; the streaming transcript buffer is no longer
            // needed once all challenges are squeezed.

            // Invert a contiguous run of Fr words in-place using Montgomery's
            // batch inversion trick:
            //   1. write prefix products to scratch;
            //   2. invert the total product once with modexp;
            //   3. walk backward to recover each individual inverse.
            //
            // The function returns a boolean instead of reverting so callers
            // can combine it with other `success` plumbing until a section
            // boundary decides whether to fail closed.
            function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret {
                ret := success
                if iszero(ret) { leave }
                // Memory ranges must be forward and word-aligned by
                // construction; a reversed range is always a codegen error.
                if lt(mptr_end, mptr_start) {
                    ret := 0
                    leave
                }

                let count_bytes := sub(mptr_end, mptr_start)
                // Empty batch is valid and leaves memory untouched.
                if iszero(count_bytes) { leave }

                // Fast path for a single denominator: avoid prefix scratch and
                // just run one modexp inverse in place.
                if eq(count_bytes, 0x20) {
                    let x := mload(mptr_start)
                    // Reject anything congruent to zero mod r, not just the
                    // literal word 0: modexp would return 0 for those too, and
                    // the caller would take it for a valid inverse.
                    if iszero(lt(x, r)) {
                        ret := 0
                        leave
                    }
                    if iszero(x) {
                        ret := 0
                        leave
                    }

                    let single_scratch := scratch_mptr
                    mstore(add(single_scratch, {{ template_constants.modexp.base_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                    mstore(add(single_scratch, {{ template_constants.modexp.exp_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                    mstore(add(single_scratch, {{ template_constants.modexp.mod_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                    mstore(add(single_scratch, {{ template_constants.modexp.base_offset|hex() }}), x)
                    mstore(add(single_scratch, {{ template_constants.modexp.exp_offset|hex() }}), sub(r, 2))
                    mstore(add(single_scratch, {{ template_constants.modexp.mod_offset|hex() }}), r)
                    ret := staticcall(gas(), {{ template_constants.modexp.address|hex() }}, single_scratch, {{ template_constants.modexp.frame_bytes|hex() }}, single_scratch, {{ template_constants.modexp.output_bytes|hex() }})
                    ret := and(ret, eq(returndatasize(), {{ template_constants.modexp.output_bytes|hex() }}))
                    if ret { mstore(mptr_start, mload(single_scratch)) }
                    leave
                }

                // Forward pass: scratch stores prefix products up to, but not
                // including, the final element. `gp` becomes the total product.
                //
                // Match the single-element path: reject non-canonical words
                // (x >= r) instead of letting mulmod reduce them silently, so
                // accept/reject semantics do not depend on batch length.
                let gp_mptr := scratch_mptr
                let gp := mload(mptr_start)
                if iszero(lt(gp, r)) {
                    ret := 0
                    leave
                }
                let mptr := add(mptr_start, 0x20)
                for {} lt(mptr, sub(mptr_end, 0x20)) {} {
                    let x := mload(mptr)
                    if iszero(lt(x, r)) {
                        ret := 0
                        leave
                    }
                    gp := mulmod(gp, x, r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                let x_last := mload(mptr)
                if iszero(lt(x_last, r)) {
                    ret := 0
                    leave
                }
                gp := mulmod(gp, x_last, r)
                // A zero total product means at least one denominator was
                // zero, so no batch inverse exists.
                if iszero(gp) {
                    ret := 0
                    leave
                }

                // Invert the total product once.
                mstore(add(gp_mptr, {{ template_constants.modexp.base_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                mstore(add(gp_mptr, {{ template_constants.modexp.exp_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                mstore(add(gp_mptr, {{ template_constants.modexp.mod_len_offset|hex() }}), {{ template_constants.word_bytes|hex() }})
                mstore(add(gp_mptr, {{ template_constants.modexp.base_offset|hex() }}), gp)
                mstore(add(gp_mptr, {{ template_constants.modexp.exp_offset|hex() }}), sub(r, 2))
                mstore(add(gp_mptr, {{ template_constants.modexp.mod_offset|hex() }}), r)
                ret := staticcall(gas(), {{ template_constants.modexp.address|hex() }}, gp_mptr, {{ template_constants.modexp.frame_bytes|hex() }}, gp_mptr, {{ template_constants.modexp.output_bytes|hex() }})
                ret := and(ret, eq(returndatasize(), {{ template_constants.modexp.output_bytes|hex() }}))
                // Leave before the backward pass on a failed modexp. A failed
                // staticcall writes no output, so `mload(gp_mptr)` would read
                // back the stale frame header and the pass below would
                // overwrite every denominator in [mptr_start, mptr_end) with
                // garbage products before returning ret = 0.
                if iszero(ret) { leave }
                let all_inv := mload(gp_mptr)

                // Backward pass: derive each inverse from the inverted total
                // product and the saved prefix products.
                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for {} lt(second_mptr, mptr) {} {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Final EIP-2537 pairing wrapper. `lhs_mptr` and `rhs_mptr` are
            // 4-word G1 slots; G2 bases are loaded from the pinned VK payload.
            function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret {
                ret := success
                // Every other exit from this function reverts, and the
                // terminal `return(RETURN_MPTR, 0x20)` in TraceReturn.yul
                // returns true without consulting `success`. Revert here too,
                // so this helper has no path that hands control back to a
                // caller that would report success for an unverified proof.
                if iszero(ret) { revert(0, 0) }
                // Lay out two (G1, G2) pairs at scratch..scratch+0x300:
                //   [lhs_g1 (0x80) | G2_BASE (0x100) | rhs_g1 (0x80) | NEG_S_G2_BASE (0x100)]
                // Cancun MCOPY (3 + 3·words gas) replaces what used to
                // be a 4-step mstore chain for each G1 (~60 gas) and an
                // 8-iter mstore loop for each G2 (~240 gas). Net saving
                // here is ~500 gas per ec_pairing call.
                let scratch := {{ memory.final_pairing_scratch_mptr|hex() }}
                mcopy(scratch,              lhs_mptr,                 0x80)
                mcopy(add(scratch, 0x80),   G2_BASE_MPTR,             0x100)
                mcopy(add(scratch, 0x180),  rhs_mptr,                 0x80)
                mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)
                ret := staticcall(gas(), {{ template_constants.eip2537.pairing_address|hex() }}, scratch, {{ template_constants.pairing_two_pair_bytes|hex() }}, scratch, {{ template_constants.word_bytes|hex() }})
                ret := and(ret, eq(returndatasize(), {{ template_constants.word_bytes|hex() }}))
                // Compare against 1 rather than truncating to the low bit:
                // `and(ret, word)` would accept any odd result word. EIP-2537
                // only ever returns 0 or 1, so this matches the strict form
                // the constructor smoke test already uses.
                ret := and(ret, eq(mload(scratch), 1))
                if iszero(ret) { revert(0, 0) }
                ret := 1
            }
