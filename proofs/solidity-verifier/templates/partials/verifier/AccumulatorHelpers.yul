            // ---------- IVC accumulator public-input decoding ----------
            //
            // `AssignedForeignPoint<BLS12-381>` exposes each base-field coordinate
            // through `AssignedField::as_public_input`: seven radix-2^56 limbs of
            // (coord - 1) are packed four-at-a-time into native field elements.
            // The x coordinate's first packed word carries the identity flag by
            // adding one raw radix base. Rebuild EIP-2537 padded
            // (x_hi, x_lo, y_hi, y_lo) words from that encoding.
            //
            // Public-input layout for one coordinate:
            //   word 0: limb_0 | limb_1 << bits | ... up to limbs_per_word
            //   word 1: next limbs, if any
            //
            // The limbs are little-endian in the represented integer even
            // though calldata words are loaded as big 256-bit values. The loop
            // below extracts each limb by shifting inside the packed word and
            // reconstructs the full coordinate into the two-word EIP-2537
            // representation expected by the BLS12-381 precompiles.
            function load_acc_coord_shifted(src, bits, n, base, limbs_per_word, first_adjust) -> hi, lo {
                // Mask for one radix limb, e.g. 2^56 - 1 for the current
                // BLS12-381 self-emulation parameters.
                let mask := sub(base, 1)
                for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                    // Limb words are little-endian packed inside each Fr
                    // public input. `first_adjust` removes the identity flag
                    // base from the first x word when present.
                    let packed := calldataload(add(src, mul(div(i, limbs_per_word), 0x20)))
                    if and(iszero(div(i, limbs_per_word)), first_adjust) {
                        packed := sub(packed, first_adjust)
                    }
                    // Select limb i from its packed field word. The mod/div
                    // pair maps a limb index to an intra-word limb slot and
                    // the calldata word containing it.
                    let limb := and(shr(mul(mod(i, limbs_per_word), bits), packed), mask)

                    let shift := mul(i, bits)
                    // Split the reconstructed 384-bit coordinate into the
                    // EIP-2537 high/low words expected by the precompiles.
                    if lt(shift, 256) {
                        lo := add(lo, shl(shift, limb))
                        if gt(add(shift, bits), 256) {
                            // A limb can straddle the 256-bit low/high split.
                            // Move the overflow bits into hi.
                            hi := add(hi, shr(sub(256, shift), limb))
                        }
                    }
                    if iszero(lt(shift, 256)) {
                        // Once shift >= 256 the whole limb belongs to hi.
                        hi := add(hi, shl(sub(shift, 256), limb))
                    }
                }
            }

            // The shifted coordinate codec represents zero as p-1 before the
            // final +1 below, so keep this sentinel explicit.
            function is_bls_p_minus_one(hi, lo) -> yes {
                yes := and(eq(hi, BLS_P_HI), eq(lo, BLS_P_MINUS_ONE_LO))
            }

            // Canonical encoded accumulator identity:
            //   x = p-1 plus the identity flag in the first packed word,
            //   y = p-1 with no identity flag.
            // It decodes to the EIP-2537 point-at-infinity slot (all zeros).
            //
            // This fast path is deliberately stricter than "decodes to zero":
            // the point at infinity has exactly one accepted public-input
            // encoding. Non-canonical zero-like encodings are rejected later.
            function is_acc_encoded_identity(src) -> yes {
                yes := and(
                    and(
                        eq(calldataload(src), BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG),
                        eq(calldataload(add(src, 0x20)), BLS_P_MINUS_ONE_PACKED_1)
                    ),
                    and(
                        eq(calldataload(add(src, 0x40)), BLS_P_MINUS_ONE_PACKED_0),
                        eq(calldataload(add(src, 0x60)), BLS_P_MINUS_ONE_PACKED_1)
                    )
                )
            }

            // Reject unused high bits in the packed public-input words. This
            // makes each accumulator point encoding canonical before it reaches
            // the precompile-based curve/subgroup validation.
            function check_acc_coord_packing(src, bits, n, limbs_per_word) -> ok {
                ok := 1
                // Number of packed native-field public-input words occupied by
                // one coordinate.
                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                for { let word_idx := 0 } lt(word_idx, coord_words) { word_idx := add(word_idx, 1) } {
                    // The final word may contain fewer than limbs_per_word
                    // limbs. Any unused high bits must be zero, otherwise the
                    // same coordinate would have multiple calldata encodings.
                    let remaining := sub(n, mul(word_idx, limbs_per_word))
                    let limbs_in_word := limbs_per_word
                    if lt(remaining, limbs_per_word) {
                        limbs_in_word := remaining
                    }
                    let used_bits := mul(limbs_in_word, bits)
                    if lt(used_bits, 256) {
                        // shl(used_bits, 1) == 2^used_bits. The packed word
                        // must be strictly less than that bound.
                        ok := and(ok, lt(calldataload(add(src, mul(word_idx, 0x20))), shl(used_bits, 1)))
                    }
                }
            }

            // Decode one shifted coordinate. `allow_id` is true only for x,
            // because the identity flag lives in x's first packed word.
            function load_acc_coord(src, allow_id, bits, n, base, limbs_per_word) -> ok, hi, lo, is_id {
                ok := check_acc_coord_packing(src, bits, n, limbs_per_word)
                if and(allow_id, iszero(lt(calldataload(src), base))) {
                    // Probe the x identity flag by removing one radix base and
                    // checking whether the adjusted coordinate is p-1.
                    //
                    // `calldataload(src) >= base` is a cheap prefilter: only x
                    // can carry this flag, and adding one radix base must make
                    // the first packed word at least base.
                    let adj_hi, adj_lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, base)
                    is_id := is_bls_p_minus_one(adj_hi, adj_lo)
                }

                // Decode again with the identity adjustment applied only when
                // the canonical identity flag was actually detected.
                hi, lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, mul(is_id, base))
                ok := and(
                    ok,
                    // Coordinate must be in the BLS12-381 base field, i.e.
                    // <= p - 1 in split hi/lo form.
                    or(lt(hi, BLS_P_HI), and(eq(hi, BLS_P_HI), iszero(gt(lo, BLS_P_MINUS_ONE_LO))))
                )

                let was_p_minus_one := is_bls_p_minus_one(hi, lo)
                if was_p_minus_one {
                    // Shifted encoding maps p-1 back to zero.
                    hi := 0
                    lo := 0
                }
                if iszero(was_p_minus_one) {
                    // All other coordinates are encoded as coord - 1, so add
                    // one back with carry into the high word.
                    let next_lo := add(lo, 1)
                    hi := add(hi, lt(next_lo, lo))
                    lo := next_lo
                }

                // EIP-2537 pads each 48-byte Fp coordinate to 64 bytes,
                // so the high word must fit in its low 128 bits.
                // This also catches impossible reconstructions above 384 bits.
                ok := and(ok, lt(hi, shl(128, 1)))
            }

            // Decode a public accumulator point into an EIP-2537 4-word G1
            // slot. Non-identity points are curve/subgroup checked later by
            // routing them through G1MSM.
            function load_acc_point(dst, src, bits, n, base) -> ok, is_id {
                // Prefer the canonical all-coordinate identity encoding before
                // attempting coordinate-level shifted decoding. This accepts
                // the point at infinity only in the exact form generated by the
                // circuit's public-input codec.
                is_id := is_acc_encoded_identity(src)
                if is_id {
                    ok := 1
                    // EIP-2537 encodes G1 identity as four zero words:
                    // x_hi = x_lo = y_hi = y_lo = 0.
                    mstore(dst, 0)
                    mstore(add(dst, 0x20), 0)
                    mstore(add(dst, 0x40), 0)
                    mstore(add(dst, 0x60), 0)
                }
                if iszero(is_id) {
                    // x occupies coord_words packed public-input words; y
                    // starts immediately after x.
                    let limbs_per_word := {{ template_constants.accumulator.limbs_per_word }}
                    let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                    // Only x may carry the identity flag. y must decode as a
                    // normal shifted coordinate.
                    let x_ok, x_hi, x_lo, x_is_id := load_acc_coord(src, 1, bits, n, base, limbs_per_word)
                    let y_ok, y_hi, y_lo, y_id := load_acc_coord(
                        add(src, mul(coord_words, 0x20)),
                        0,
                        bits,
                        n,
                        base,
                        limbs_per_word
                    )
                    // y_id is always zero because allow_id was false, but the
                    // tuple shape is shared with x decoding.
                    pop(y_id)
                    ok := and(x_ok, y_ok)
                    is_id := x_is_id

                    if is_id {
                        // If x carried the identity flag, both decoded
                        // coordinates must be zero after shifting. Any other y
                        // value would be a malformed infinity encoding.
                        ok := and(ok, iszero(or(or(x_hi, x_lo), or(y_hi, y_lo))))
                        mstore(dst, 0)
                        mstore(add(dst, 0x20), 0)
                        mstore(add(dst, 0x40), 0)
                        mstore(add(dst, 0x60), 0)
                    }
                    if iszero(is_id) {
                        // The coordinate codec maps encoded p-1 to decoded
                        // zero. EIP-2537 reserves affine (0,0) for the point
                        // at infinity, so a decoded infinity is only valid
                        // when the canonical accumulator identity encoding
                        // was used above.
                        let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))
                        ok := and(ok, iszero(decoded_zero))
                        // Store the affine point in the exact precompile input
                        // layout: x_hi, x_lo, y_hi, y_lo.
                        mstore(dst, x_hi)
                        mstore(add(dst, 0x20), x_lo)
                        mstore(add(dst, 0x40), y_hi)
                        mstore(add(dst, 0x60), y_lo)
                    }
                }
            }

            {%- if self.expected_has_accumulator %}
            // Validate and prepare the public accumulator equation before the
            // main transcript starts. This fails malformed public inputs early
            // and writes ACC_LHS_MPTR / ACC_RHS_MPTR for final pairing batching.
            //
            // The accumulator public input represents an equality of two G1
            // commitments used by the recursive KZG accumulator. This helper:
            //   1. decodes carried public G1 points from shifted limbs;
            //   2. forces every decoded point through EIP-2537 G1MSM so the
            //      precompile validates curve/subgroup membership;
            //   3. folds the RHS carried point and fixed-base scalar tail into
            //      ACC_RHS_MPTR, leaving ACC_LHS_MPTR / ACC_RHS_MPTR ready for
            //      randomized batching in FinalPairing.yul.
            function validate_public_accumulator(success, r) -> out {
                out := success
                let bits := {{ self.expected_num_acc_limb_bits }}
                let n := {{ self.expected_num_acc_limbs }}
                // The BLS12-381 self-emulation currently exposes Fp
                // coordinates as 7 radix-2^56 limbs.
                let limb_base := shl(bits, 1)
                let limbs_per_word := {{ template_constants.accumulator.limbs_per_word }}
                let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
                // acc_offset is generated from the VK/protocol shape and
                // points into the ABI `instances` array.
                let acc_instance_ptr := add(INSTANCE_CPTR, {{ (self.expected_acc_offset * 32)|hex() }})

                // LHS layout: point limbs (x,y), then either an explicit
                // scalar word or an implicit unit scalar for already-collapsed
                // point-pair public inputs.
                // The scalar pointer is computed unconditionally; the rendered
                // branch below decides whether to read it or use scalar 1.
                let lhs_scalar_ptr := add(acc_instance_ptr, mul(mul(2, coord_words), 0x20))
                let lhs_ok, lhs_is_id := load_acc_point(ACC_LHS_MPTR, acc_instance_ptr, bits, n, limb_base)
                out := and(out, lhs_ok)
                // Shared scratch for one-pair LHS validation and the later
                // variable-length RHS MSM.
                let acc_scratch := {{ memory.acc_msm_scratch|hex() }}
                {
                    {%- if self.expected_acc_has_carried_scalars %}
                    // Carried-scalar layout: the circuit exposes the scalar
                    // that multiplies the carried LHS point.
                    let lhs_scalar := calldataload(lhs_scalar_ptr)
                    {%- else %}
                    // Already-collapsed point-pair layout: carried scalars are
                    // implicit one.
                    let lhs_scalar := 1
                    {%- endif %}
                    // Identity status is useful for decoding checks above, but
                    // validation still goes through G1MSM for all points.
                    pop(lhs_is_id)
                    // Always route the decoded carried point through G1MSM,
                    // even for identity points and zero/one scalars. The
                    // precompile is the on-curve/subgroup validator for this
                    // public-input point; skipping it would let a malformed
                    // non-identity point hide behind scalar 0.
                    mcopy(acc_scratch, ACC_LHS_MPTR, 0x80)
                    mstore(add(acc_scratch, 0x80), lhs_scalar)
                    if out {
                        // Single-pair MSM output overwrites ACC_LHS_MPTR with
                        // lhs_scalar * decoded_lhs. If lhs_scalar is one, this
                        // is also a curve/subgroup validation round-trip.
                        out := staticcall({{ g1msm_single_gas_cap }}, {{ template_constants.eip2537.g1msm_address|hex() }}, acc_scratch, {{ template_constants.g1_msm_pair_bytes|hex() }}, ACC_LHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                        out := and(out, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                    }
                }

                {%- if acc_fixed_bases.len() == 0 %}
                    {%- if self.expected_acc_has_carried_scalars %}
                // RHS layout for this generated verifier is fully collapsed:
                // point limbs (x,y), scalar. There is no fixed-base scalar
                // tail; fixed-base contributions were already folded into
                // ACC_RHS by the circuit/native accumulator construction.
                    {%- else %}
                // RHS layout for this generated verifier is an already
                // collapsed point pair: lhs point, rhs point. Both carried
                // scalars are implicit one, and there is no fixed-base scalar
                // tail.
                    {%- endif %}
                {%- else %}
                // RHS layout for this generated verifier is partially
                // collapsed: point limbs (x,y), scalar, then fixed-base
                // scalars in BTreeMap key order (`-G`, fixed_i, perm_i
                // lexicographically by name). Each tail scalar is consumed
                // below and appended to the RHS MSM with its generated base.
                {%- endif %}
                {%- if self.expected_acc_has_carried_scalars %}
                let rhs_instance_ptr := add(lhs_scalar_ptr, 0x20)
                {%- else %}
                let rhs_instance_ptr := lhs_scalar_ptr
                {%- endif %}
                // RHS scalar, when present, immediately follows the RHS point
                // limbs. The fixed-base scalar tail starts after it.
                let rhs_scalar_ptr := add(rhs_instance_ptr, mul(mul(2, coord_words), 0x20))
                let rhs_ok, rhs_is_id := load_acc_point(ACC_RHS_MPTR, rhs_instance_ptr, bits, n, limb_base)
                out := and(out, rhs_ok)
                // acc_pair_ptr appends (G1, scalar) pairs into acc_scratch for
                // one final RHS MSM.
                let acc_pair_ptr := acc_scratch
                {
                    {%- if self.expected_acc_has_carried_scalars %}
                    // Explicit carried RHS scalar.
                    let rhs_scalar := calldataload(rhs_scalar_ptr)
                    {%- else %}
                    // Implicit unit scalar for already-collapsed point pairs.
                    let rhs_scalar := 1
                    {%- endif %}
                    pop(rhs_is_id)
                    // Keep the carried RHS point in the MSM input even when
                    // it is encoded as identity or has scalar 0/1, so EIP-2537
                    // validates every decoded public accumulator point before
                    // it can affect, or be erased from, the pairing batch.
                    mcopy(acc_pair_ptr, ACC_RHS_MPTR, {{ template_constants.g1_bytes|hex() }})
                    mstore(add(acc_pair_ptr, {{ template_constants.g1_bytes|hex() }}), rhs_scalar)
                    // Move to the next (G1, scalar) pair slot.
                    acc_pair_ptr := add(acc_pair_ptr, {{ template_constants.g1_msm_pair_bytes|hex() }})
                }
                {%- if acc_fixed_bases.len() > 0 %}
                {%- if self.expected_acc_has_carried_scalars %}
                // Fixed-base tail starts after the explicit RHS scalar.
                let fixed_scalar_ptr := add(rhs_scalar_ptr, 0x20)
                {%- else %}
                // Without carried scalars, the tail starts where an explicit
                // RHS scalar would otherwise have lived.
                let fixed_scalar_ptr := rhs_scalar_ptr
                {%- endif %}
                {%- for (base_mptr, negate_scalar) in acc_fixed_bases %}
                // Generated fixed-base scalar {{ loop.index0 }}. The
                // corresponding base point is embedded in verifier memory at
                // {{ base_mptr|hex() }}.
                let fixed_scalar_{{ loop.index0 }} := calldataload(fixed_scalar_ptr)
                {%- if negate_scalar %}
                // Some accumulator bases are represented with a negated scalar
                // so the MSM can reuse the generated positive base point.
                fixed_scalar_{{ loop.index0 }} := mod(sub(r, fixed_scalar_{{ loop.index0 }}), r)
                {%- endif %}
                if fixed_scalar_{{ loop.index0 }} {
                    // Zero scalars do not need a pair in the RHS MSM. Nonzero
                    // tail scalars append their generated fixed base.
                    mcopy(acc_pair_ptr, {{ base_mptr|hex() }}, {{ template_constants.g1_bytes|hex() }})
                    mstore(add(acc_pair_ptr, {{ template_constants.g1_bytes|hex() }}), fixed_scalar_{{ loop.index0 }})
                    acc_pair_ptr := add(acc_pair_ptr, {{ template_constants.g1_msm_pair_bytes|hex() }})
                }
                // Advance to the next public tail scalar regardless of whether
                // this one was zero and omitted from the MSM input.
                fixed_scalar_ptr := add(fixed_scalar_ptr, 0x20)
                {%- endfor %}
                {%- endif %}
                // Total byte length of the appended RHS MSM input pairs. This
                // is at least one pair because the carried RHS point is always
                // appended; keep the guard for synthetic render configurations.
                let acc_msm_len := sub(acc_pair_ptr, acc_scratch)
                if acc_msm_len {
                    // Fold the carried RHS point and any generated fixed-base
                    // tail into ACC_RHS_MPTR. The later final pairing block
                    // randomizes this equation together with the KZG pairing.
                    if out {
                        // Output overwrites ACC_RHS_MPTR with:
                        //   rhs_scalar * carried_rhs
                        // + sum_i fixed_scalar_i * fixed_base_i
                        //
                        // The precompile also validates every nonzero fixed
                        // base embedded by codegen and the carried RHS point.
                        out := staticcall(
                            {{ acc_rhs_g1msm_gas_cap }},
                            {{ template_constants.eip2537.g1msm_address|hex() }},
                            acc_scratch,
                            acc_msm_len,
                            ACC_RHS_MPTR,
                            {{ template_constants.g1_bytes|hex() }}
                        )
                        out := and(out, eq(returndatasize(), {{ template_constants.g1_bytes|hex() }}))
                    }
                }
                // The caller checks `out` and reverts before transcript work if
                // any decode, canonicality, or precompile validation failed.
            }
            {%- endif %}
