// GENERATED SNAPSHOT -- do not edit by hand.
//
// Canonical all-ops render of the quotient VM interpreter arms from
// src/lowering/quotient_numerator/vm/yul_arms.rs (every opcode and
// memory token enabled, trace instrumentation on, fixed placeholder
// program constants from `snapshot_program`, one placeholder body per
// native callback family). Regenerate with
//   HALO2_SOLIDITY_UPDATE_VM_ARMS_SNAPSHOT=1 cargo test -p
//     halo2_solidity_verifier --lib vm_arms_snapshot_is_current
// and re-pin tests/template_digest.rs. Reviewers diff this file to
// see interpreter-arm changes in readable Yul.
// ===== opcode summary =====
                //   0x01 push_const
                //   0x02 push_mem_literal
                //   0x03 push_mem_token
                //   0x04 push_mem_token_offset
                //   0x05 push_mem_u16
                //   0x06 add
                //   0x07 mul
                //   0x08 neg
                //   0x09 push_const_u8
                //   0x0a fold_main
                //   0x0b fold_selector
                //   0x0c add_const_u8
                //   0x0d mul_const_u8
                //   0x0e add_const
                //   0x0f mul_const
                //   0x10 add_mem_u16
                //   0x11 mul_mem_u16
                //   0x12 add_mul_mem_mem_const_u8
                //   0x13 add_mul_const_u8_mem_u16
                //   0x14 add_mul_mem_mem
                //   0x15 run_add_mul_mem_mem_const_u8
                //   0x16 run_add_mul_const_u8_mem_u16
                //   0x22 affine_sum
                //   0x19 native_permutation
                //   0x1f native_lookup
                //   0x1b native_identity
                //   0x1c lin7
                //   0x1d bilin7_row
                //   0x1e bilin7_pairwise
                //   0x21 modarith7
                //   0x20 pow5
// ===== switch arms =====
                    // VM 0x01 PUSH_CONST (bytes): next two bytes are a constant-table slot.
                    case 0x01 {
                        // Operand layout: u16 const_idx. Constants are 32-byte
                        // Fr words, so shl(5, const_idx) converts an index to
                        // a byte offset.
                        let qconst := shr(240, mload(q_pc))
                        if iszero(lt(qconst, 300)) { q_program_fail() }
                        // Push semantics: spill the old cached top, if any,
                        // then install the loaded constant as the new q_top.
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(add(q_const_mptr, shl(5, qconst)))
                        q_has_top := 1
                        q_pc := add(q_pc, 2)
                    }
                    // VM 0x02 PUSH_MEM_LITERAL (bytes): next four bytes are a memory pointer.
                    case 0x02 {
                        // Operand layout: u32 absolute memory pointer. This is
                        // emitted only for planned addresses that do not fit in
                        // the smaller u16 form or token map.
                        let q_ptr := shr(224, mload(q_pc))
                        q_pc := add(q_pc, 0x04)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        // Load one canonical Fr word from generated memory and
                        // push it through the cached-top stack discipline.
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    // VM 0x03 PUSH_MEM_TOKEN (bytes): next byte selects a symbolic memory pointer.
                    case 0x03 {
                        // Operand layout: u8 token. Tokens cover the hot
                        // global verifier scalars used in many identities.
                        let q_token := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        let q_ptr := 0
                        // Token cases decode generated symbolic memory addresses.
                        switch q_token
                        case 0x01 { q_ptr := L_0_MPTR }
                        case 0x02 { q_ptr := L_LAST_MPTR }
                        case 0x03 { q_ptr := L_BLIND_MPTR }
                        case 0x04 { q_ptr := BETA_MPTR }
                        case 0x05 { q_ptr := GAMMA_MPTR }
                        case 0x06 { q_ptr := X_MPTR }
                        case 0x07 { q_ptr := THETA_MPTR }
                        case 0x08 { q_ptr := TRASH_CHALLENGE_MPTR }
                        case 0x09 { q_ptr := INSTANCE_EVAL_MPTR }
                        // A token not advertised by the VM usage manifest is
                        // impossible for valid generated bytecode.
                        default { q_program_fail() }
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    // VM 0x04 PUSH_MEM_TOKEN_OFFSET (bytes): token byte plus u32 byte offset.
                    case 0x04 {
                        // Operand layout: u8 token, u32 byte offset. This is
                        // used when a symbolic base such as REVERSED_EVALS_MPTR
                        // is known, but the expression needs a specific word
                        // inside that generated region.
                        let q_word := mload(q_pc)
                        let q_token := byte(0, q_word)
                        let q_off := and(shr(216, q_word), 0xffffffff)
                        q_pc := add(q_pc, 5)
                        let q_ptr := 0
                        // Token-offset cases reuse the same token table, then add q_off.
                        switch q_token
                        case 0x01 { q_ptr := add(L_0_MPTR, q_off) }
                        case 0x02 { q_ptr := add(L_LAST_MPTR, q_off) }
                        case 0x03 { q_ptr := add(L_BLIND_MPTR, q_off) }
                        case 0x04 { q_ptr := add(BETA_MPTR, q_off) }
                        case 0x05 { q_ptr := add(GAMMA_MPTR, q_off) }
                        case 0x06 { q_ptr := add(X_MPTR, q_off) }
                        case 0x07 { q_ptr := add(THETA_MPTR, q_off) }
                        case 0x08 { q_ptr := add(TRASH_CHALLENGE_MPTR, q_off) }
                        case 0x09 { q_ptr := add(INSTANCE_EVAL_MPTR, q_off) }
                        default { q_program_fail() }
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.
                    case 0x05 {
                        // Operand layout: u16 absolute memory pointer. The
                        // memory planner keeps the hot quotient frame below
                        // 64 KiB when this compact form is emitted.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    // VM 0x06 ADD: pop one spilled stack word and add it to q_top.
                    case 0x06 {
                        // The safety validator guarantees a spilled operand
                        // exists before ADD. q_top is the right operand.
                        if eq(q_sp, 0x9000) { q_program_fail() }
                        q_sp := sub(q_sp, 0x20)
                        q_top := addmod(mload(q_sp), q_top, r)
                    }
                    // VM 0x07 MUL: pop one spilled stack word and multiply it by q_top.
                    case 0x07 {
                        // Same stack contract as ADD, with multiplication
                        // reduced directly modulo Fr.
                        if eq(q_sp, 0x9000) { q_program_fail() }
                        q_sp := sub(q_sp, 0x20)
                        q_top := mulmod(mload(q_sp), q_top, r)
                    }
                    // VM 0x08 NEG: replace q_top with its Fr negation.
                    case 0x08 {
                        // addmod(0, r - x, r) maps zero back to zero and every
                        // nonzero scalar to its canonical additive inverse.
                        q_top := addmod(0, sub(r, q_top), r)
                    }
                    // VM 0x20 POW5: replace q_top with q_top^5.
                    case 0x20 {
                        // Poseidon S-box shortcut: x^5 = x * (x^2)^2.
                        let q2 := mulmod(q_top, q_top, r)
                        q_top := mulmod(q_top, mulmod(q2, q2, r), r)
                    }
                    // VM 0x09 PUSH_CONST_U8 (bytes): next byte is a constant-table slot.
                    case 0x09 {
                        // One-byte variant for the common case where the
                        // constant table has fewer than 256 referenced slots.
                        let qconst := byte(0, mload(q_pc))
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(add(q_const_mptr, shl(5, qconst)))
                        q_has_top := 1
                        q_pc := add(q_pc, 1)
                    }
                    // VM 0x0c ADD_CONST_U8: add a small constant-table slot into q_top.
                    case 0x0c {
                        // Accumulator opcode: mutates q_top in place instead
                        // of pushing a new stack value.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.
                    case 0x0d {
                        // One-byte constant-index multiply, used by short
                        // affine chains after an initial PUSH.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    // VM 0x0e ADD_CONST: add a wider constant-table slot into q_top.
                    case 0x0e {
                        // Two-byte constant-index form for larger generated
                        // constant tables.
                        let qconst := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if iszero(lt(qconst, 300)) { q_program_fail() }
                        let q_const_ptr := add(q_const_mptr, shl(5, qconst))
                        if gt(sub(q_const_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := addmod(q_top, mload(q_const_ptr), r)
                    }
                    // VM 0x0f MUL_CONST: multiply q_top by a wider constant-table slot.
                    case 0x0f {
                        // Two-byte constant-index multiply.
                        let qconst := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if iszero(lt(qconst, 300)) { q_program_fail() }
                        let q_const_ptr := add(q_const_mptr, shl(5, qconst))
                        if gt(sub(q_const_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := mulmod(q_top, mload(q_const_ptr), r)
                    }
                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.
                    case 0x10 {
                        // Operand layout: u16 pointer. The pointed word is an
                        // already range-checked Fr scalar in verifier memory.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := addmod(q_top, mload(q_ptr), r)
                    }
                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.
                    case 0x11 {
                        // In-place multiply by a planned memory word.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := mulmod(q_top, mload(q_ptr), r)
                    }
                    // VM 0x12 ADD_MUL_MEM_MEM_CONST_U8: fused q_top += lhs * rhs * const.
                    case 0x12 {
                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr,
                        // u8 const_idx. This fuses a frequent affine-product
                        // term without spending opcodes on PUSH/MUL/MUL/ADD.
                        let q_word := mload(q_pc)
                        let q_lhs := shr(240, q_word)
                        let q_rhs := and(shr(224, q_word), 0xffff)
                        let qconst := byte(4, q_word)
                        q_pc := add(q_pc, 5)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := addmod(
                            q_top,
                            mulmod(
                                mulmod(mload(q_lhs), mload(q_rhs), r),
                                mload(add(q_const_mptr, shl(5, qconst))),
                                r
                            ),
                            r
                        )
                    }
                    // VM 0x13 ADD_MUL_CONST_U8_MEM_U16: fused q_top += mem * const.
                    case 0x13 {
                        // Operand layout: u16 ptr, u8 const_idx.
                        let q_word := mload(q_pc)
                        let q_ptr := shr(240, q_word)
                        let qconst := byte(2, q_word)
                        q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := addmod(
                            q_top,
                            mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                            r
                        )
                    }
                    // VM 0x14 ADD_MUL_MEM_MEM: fused q_top += lhs * rhs.
                    case 0x14 {
                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr. This is
                        // the unit-coefficient sibling of opcode 0x12.
                        let q_word := mload(q_pc)
                        let q_lhs := shr(240, q_word)
                        let q_rhs := and(shr(224, q_word), 0xffff)
                        q_pc := add(q_pc, 0x04)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                        q_top := addmod(q_top, mulmod(mload(q_lhs), mload(q_rhs), r), r)
                    }
                    // VM 0x15 RUN_ADD_MUL_MEM_MEM_CONST_U8: byte-only loop over fused 0x12 payloads.
                    case 0x15 {
                        // Operand layout: u16 count followed by `count`
                        // packed 0x12-style payloads. The run header saves a
                        // dispatch per term in long affine product chains.
                        let q_count := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        let q_run_end := add(q_pc, mul(q_count, 5))
                        for { } lt(q_pc, q_run_end) { } {
                            let q_word := mload(q_pc)
                            let q_lhs := shr(240, q_word)
                            let q_rhs := and(shr(224, q_word), 0xffff)
                            let qconst := byte(4, q_word)
                            q_pc := add(q_pc, 5)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                            q_top := addmod(
                                q_top,
                                mulmod(
                                    mulmod(mload(q_lhs), mload(q_rhs), r),
                                    mload(add(q_const_mptr, shl(5, qconst))),
                                    r
                                ),
                                r
                            )
                        }
                    }
                    // VM 0x16 RUN_ADD_MUL_CONST_U8_MEM_U16: byte-only loop over fused 0x13 payloads.
                    case 0x16 {
                        // Operand layout: u16 count followed by `count`
                        // packed 0x13-style payloads.
                        let q_count := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        let q_run_end := add(q_pc, mul(q_count, 3))
                        for { } lt(q_pc, q_run_end) { } {
                            let q_word := mload(q_pc)
                            let q_ptr := shr(240, q_word)
                            let qconst := byte(2, q_word)
                            q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                            q_top := addmod(
                                q_top,
                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                                r
                            )
                        }
                    }
                    // VM 0x22 AFFINE_SUM: mixed byte-only affine linear/product loop.
                    case 0x22 {
                        // Operand layout:
                        //   u16 lin_count, u16 product_count,
                        //   lin_count * {u16 ptr, u8 const_idx},
                        //   product_count * {u16 lhs, u16 rhs, u8 const_idx}.
                        // The opcode appends all terms into the existing
                        // q_top accumulator.
                        let q_lin_count := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        let q_product_count := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        // Linear part: q_top += c_i * mload(ptr_i).
                        let q_lin_end := add(q_pc, mul(q_lin_count, 3))
                        for { } lt(q_pc, q_lin_end) { } {
                            let q_word := mload(q_pc)
                            let q_ptr := shr(240, q_word)
                            let qconst := byte(2, q_word)
                            q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                            q_top := addmod(
                                q_top,
                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                                r
                            )
                        }
                        // Product part: q_top += c_i * mload(lhs_i) * mload(rhs_i).
                        let q_product_end := add(q_pc, mul(q_product_count, 5))
                        for { } lt(q_pc, q_product_end) { } {
                            let q_word := mload(q_pc)
                            let q_lhs := shr(240, q_word)
                            let q_rhs := and(shr(224, q_word), 0xffff)
                            let qconst := byte(4, q_word)
                            q_pc := add(q_pc, 5)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                            q_top := addmod(
                                q_top,
                                mulmod(
                                    mulmod(mload(q_lhs), mload(q_rhs), r),
                                    mload(add(q_const_mptr, shl(5, qconst))),
                                    r
                                ),
                                r
                            )
                        }
                    }
                    // Limb-aware opcodes are opt-in compact forms for
                    // structurally recognized non-SHA foreign-field shapes.
                    // Coefficients are indexes into q_const_mptr, which is
                    // generated from VK/program data, never from proof
                    // calldata.
                    //
                    // Rust source shape:
                    //   proofs/src/plonk/mod.rs::partially_evaluate_identities
                    //   circuits/src/field/foreign/util.rs::{sum_exprs,pair_wise_prod}
                    //   circuits/src/field/foreign/params.rs::{base_powers,double_base_powers}
                    //
                    // "Foreign field" means the circuit represents elements
                    // modulo another modulus m as 7 limbs in base
                    // 2^LOG2_BASE. The verifier does not switch fields; it
                    // evaluates the lowered identity over BLS12-381 Fr, using
                    // Fr coefficients equal to base^i mod m or base^(i+j) mod m.
                    // VM 0x1c LIN7: byte-only 7-term foreign-field linear form.
                    case 0x1c {
                        // LIN7: sum_i coeff[i] * value[i] over Fr.
                        // Typical Rust origin: foreign/gates/norm.rs
                        // normalization and foreign/gates/mul.rs base-power
                        // sums for x/y/z limbs.
                        //
                        // Operand layout: seven repeated {u8 const_idx,
                        // u16 ptr} pairs. The result is pushed as a fresh
                        // stack value.
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        // Accumulate exactly seven limbs, matching the
                        // generated foreign-field limb width.
                        for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_ptr := and(shr(232, q_word), 0xffff)
                            q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                            q_acc := addmod(
                                q_acc,
                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                r
                            )
                        }
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // VM 0x1d BILIN7_ROW: byte-only lhs times a 7-term weighted row.
                    case 0x1d {
                        // BILIN7_ROW: lhs * sum_i coeff[i] * rhs[i].
                        // Typical Rust origin: one row/slice of
                        // pair_wise_prod in foreign multiplication and EC
                        // on_curve/slope/tangent/lambda_squared gates.
                        //
                        // Operand layout: u16 lhs_ptr, then seven repeated
                        // {u8 const_idx, u16 rhs_ptr} pairs. The lhs value is
                        // loaded once and reused for all seven products.
                        let q_lhs := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        let q_lhs_value := mload(q_lhs)
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_rhs := and(shr(232, q_word), 0xffff)
                            q_pc := add(q_pc, 3)
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                            q_acc := addmod(
                                q_acc,
                                mulmod(
                                    mulmod(q_lhs_value, mload(q_rhs), r),
                                    mload(add(q_const_mptr, shl(5, qconst))),
                                    r
                                ),
                                r
                            )
                        }
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // VM 0x1e BILIN7_PAIRWISE: byte-only 7-by-7 weighted convolution.
                    case 0x1e {
                        // BILIN7_PAIRWISE:
                        //   sum_{i=0..6,j=0..6} coeff[i+j] * lhs[i] * rhs[j].
                        // Bases point to contiguous 7-word limb vectors.
                        // Typical Rust origin:
                        //   sum_exprs(double_base_powers,
                        //             pair_wise_prod(lhs, rhs))
                        // where double_base_powers[k] = base^k mod m.
                        //
                        // Operand layout: u16 lhs_base, u16 rhs_base, then 13
                        // one-byte coefficient indexes. Coefficients are
                        // addressed by i+j, so 7-by-7 products need 13 slots.
                        let q_word := mload(q_pc)
                        let q_lhs_base := shr(240, q_word)
                        let q_rhs_base := and(shr(224, q_word), 0xffff)
                        q_pc := add(q_pc, 0x04)
                            if gt(sub(q_lhs_base, 0x1000), 0x01ef40) { q_program_fail() }
                            if gt(sub(q_rhs_base, 0x1000), 0x01ef40) { q_program_fail() }
                        let q_coeff_pc := q_pc
                        q_pc := add(q_pc, 13)
                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        // Nested limb convolution over two contiguous
                        // 7-word vectors.
                        for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                            let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))
                            for { let q_j := 0 } lt(q_j, 7) { q_j := add(q_j, 1) } {
                                let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))
                                q_acc := addmod(
                                    q_acc,
                                    mulmod(
                                        mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),
                                        mload(add(q_const_mptr, shl(5, qconst))),
                                        r
                                    ),
                                    r
                                )
                            }
                        }
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // VM 0x21 MODARITH7: byte-only fused affine 7-limb foreign-field/ECC identity.
                    case 0x21 {
                        // MODARITH7:
                        //   maybe_cond * (
                        //       c
                        //     + sum LIN7 blocks
                        //     + sum BILIN7_ROW blocks
                        //     + sum BILIN7_PAIRWISE blocks
                        //     + sum coeff[k] * mload(ptr[k])
                        //     + sum coeff[k] * mload(lhs[k]) * mload(rhs[k])
                        //   )
                        // It is a dispatch/operand-load optimization only;
                        // all coefficients still come from the generated
                        // quotient constant table.
                        //
                        // Flags:
                        //   bit 0: multiply the final affine sum by a memory
                        //          condition word.
                        //   bit 1: seed q_acc from a constant-table word
                        //          before reading the counted term blocks.
                        let q_flags := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        let q_cond_ptr := 0
                        if and(q_flags, 0x01) {
                            // Optional condition pointer. When present, the
                            // whole identity is gated by mload(q_cond_ptr).
                            q_cond_ptr := shr(240, mload(q_pc))
                            q_pc := add(q_pc, 2)
                        if gt(sub(q_cond_ptr, 0x1000), 0x01f000) { q_program_fail() }
                        }

                        let q_acc := 0
                        if and(q_flags, 0x02) {
                            // Optional constant seed for affine identities
                            // with a standalone constant term.
                            let qconst := byte(0, mload(q_pc))
                            q_pc := add(q_pc, 1)
                            q_acc := mload(add(q_const_mptr, shl(5, qconst)))
                        }

                        // Five one-byte counters describe the blocks that
                        // follow. Each block has a fixed-width internal layout,
                        // so q_pc can advance without per-term tags.
                        let q_counts_word := mload(q_pc)
                        let q_lin_count := byte(0, q_counts_word)
                        let q_row_count := byte(1, q_counts_word)
                        let q_pairwise_count := byte(2, q_counts_word)
                        let q_mem_count := byte(3, q_counts_word)
                        let q_product_count := byte(4, q_counts_word)
                        q_pc := add(q_pc, 5)

                        if q_has_top {
                            if iszero(lt(q_sp, 0x9200)) { q_program_fail() }
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }

                        // LIN7 blocks: q_acc += sum_i c_i * limb_i.
                        for { let q_lin_block := 0 } lt(q_lin_block, q_lin_count) { q_lin_block := add(q_lin_block, 1) } {
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_word := mload(q_pc)
                                let qconst := byte(0, q_word)
                                let q_ptr := and(shr(232, q_word), 0xffff)
                                q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                                q_acc := addmod(
                                    q_acc,
                                    mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                    r
                                )
                            }
                        }

                        // BILIN7_ROW blocks: q_acc += lhs * sum_i c_i * rhs_i.
                        for { let q_row_block := 0 } lt(q_row_block, q_row_count) { q_row_block := add(q_row_block, 1) } {
                            let q_lhs := shr(240, mload(q_pc))
                            q_pc := add(q_pc, 2)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                            let q_lhs_value := mload(q_lhs)
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_word := mload(q_pc)
                                let qconst := byte(0, q_word)
                                let q_rhs := and(shr(232, q_word), 0xffff)
                                q_pc := add(q_pc, 3)
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                                q_acc := addmod(
                                    q_acc,
                                    mulmod(
                                        mulmod(q_lhs_value, mload(q_rhs), r),
                                        mload(add(q_const_mptr, shl(5, qconst))),
                                        r
                                    ),
                                    r
                                )
                            }
                        }

                        // BILIN7_PAIRWISE blocks: q_acc += weighted 7-by-7
                        // product convolution.
                        for { let q_pair_block := 0 } lt(q_pair_block, q_pairwise_count) { q_pair_block := add(q_pair_block, 1) } {
                            let q_pair_word := mload(q_pc)
                            let q_lhs_base := shr(240, q_pair_word)
                            let q_rhs_base := and(shr(224, q_pair_word), 0xffff)
                            q_pc := add(q_pc, 0x04)
                            if gt(sub(q_lhs_base, 0x1000), 0x01ef40) { q_program_fail() }
                            if gt(sub(q_rhs_base, 0x1000), 0x01ef40) { q_program_fail() }
                            let q_coeff_pc := q_pc
                            q_pc := add(q_pc, 13)
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))
                                for { let q_j := 0 } lt(q_j, 7) { q_j := add(q_j, 1) } {
                                    let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))
                                    q_acc := addmod(
                                        q_acc,
                                        mulmod(
                                            mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),
                                            mload(add(q_const_mptr, shl(5, qconst))),
                                            r
                                        ),
                                        r
                                    )
                                }
                            }
                        }

                        // Extra linear memory terms outside the 7-limb shapes.
                        for { let q_mem_block := 0 } lt(q_mem_block, q_mem_count) { q_mem_block := add(q_mem_block, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_ptr := and(shr(232, q_word), 0xffff)
                            q_pc := add(q_pc, 3)
                        if gt(sub(q_ptr, 0x1000), 0x01f000) { q_program_fail() }
                            q_acc := addmod(
                                q_acc,
                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),
                                r
                            )
                        }

                        // Extra binary product terms outside the 7-limb shapes.
                        for { let q_product_block := 0 } lt(q_product_block, q_product_count) { q_product_block := add(q_product_block, 1) } {
                            let q_word := mload(q_pc)
                            let qconst := byte(0, q_word)
                            let q_lhs := and(shr(232, q_word), 0xffff)
                            let q_rhs := and(shr(216, q_word), 0xffff)
                            q_pc := add(q_pc, 5)
                        if gt(sub(q_lhs, 0x1000), 0x01f000) { q_program_fail() }
                        if gt(sub(q_rhs, 0x1000), 0x01f000) { q_program_fail() }
                            q_acc := addmod(
                                q_acc,
                                mulmod(
                                    mulmod(mload(q_lhs), mload(q_rhs), r),
                                    mload(add(q_const_mptr, shl(5, qconst))),
                                    r
                                ),
                                r
                            )
                        }

                        if and(q_flags, 0x01) {
                            // Apply the optional gate condition last so every
                            // subterm shares the same selector/condition.
                            q_acc := mulmod(mload(q_cond_ptr), q_acc, r)
                        }
                        // MODARITH7 pushes its fused identity value.
                        q_top := q_acc
                        q_has_top := 1
                    }
                    // Native permutation callback. It evaluates the
                    // permutation identities from permutation.rs at this exact
                    // VM position, preserving the Rust identity order while
                    // avoiding a large interpreted product loop.
                    // VM 0x19 NATIVE_PERMUTATION: marker for the generated permutation callback.
                    case 0x19 {
                        // Native callbacks are identity-boundary opcodes. They
                        // must not inherit any partially evaluated VM stack
                        // state from the previous expression.
                        q_top := 0
                        q_has_top := 0
                        // The generated loop below uses program.stack_mptr as
                        // its scratch-table base, not as a conventional VM
                        // stack. The Rust memory planner must reserve enough
                        // words for structured_permutation_scratch_words(meta)
                        // whenever this opcode can appear.
                        if iszero(eq(q_sp, 0x9000)) { q_program_fail() }
                        // The generated lines below call the same fold snippets
                        // used by interpreted expressions, so trace IDs and
                        // y-batch positions remain contiguous.
                        // snapshot placeholder: generated permutation callback body
                    }
                    // Native lookup callback. This whole-family opcode
                    // evaluates the LogUp boundary, helper-chunk, and
                    // accumulator identities at this VM position, preserving
                    // the Rust y-batch order while avoiding many interpreted
                    // product-loop opcodes.
                    // VM 0x1f NATIVE_LOOKUP: marker for the generated LogUp lookup callback.
                    case 0x1f {
                        // Reset VM stack state before entering structured
                        // lookup Yul. Lookup callbacks own their scratch
                        // layout and perform all needed folds internally.
                        q_top := 0
                        q_has_top := 0
                        // The generated loop below uses program.stack_mptr as
                        // f+beta/prefix/suffix scratch rather than as a
                        // conventional VM stack. The Rust memory planner must
                        // reserve structured_lookup_scratch_words(meta).
                        if iszero(eq(q_sp, 0x9000)) { q_program_fail() }
                        // Generated LogUp code follows the same y-batch order
                        // as the Rust identity stream.
                        // snapshot placeholder: generated lookup callback body
                    }
                    // Native callbacks are generated only for the heaviest
                    // recognized Midfall gate identities. All other gate and
                    // non-native identity arithmetic remains in
                    // the compact q_program VM above, preserving the Rust
                    // `partially_evaluate_identities` order.
                    // VM 0x1b NATIVE_IDENTITY: marker for generated heavy-gate callbacks.
                    case 0x1b {
                        // Operand layout: u16 native callback index. The
                        // manifest validates that callback indexes appear in
                        // generated order and target existing switch cases.
                        let q_native_idx := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        // Heavy identities are whole expressions, so clear the
                        // interpreter stack before dispatching.
                        q_top := 0
                        q_has_top := 0
                        if iszero(eq(q_sp, 0x9000)) { q_program_fail() }
                        // Native identity sub-cases are generated from selected heavy gate identities.
                        switch q_native_idx
                        case 0 {
                            // snapshot placeholder: generated heavy-gate callback body
                        }
                        default { q_program_fail() }
                    }
                    // VM 0x0a FOLD_MAIN: consume q_top into the fully evaluated numerator fold.
                    case 0x0a {
                        // q_top is the complete value of one fully evaluated
                        // identity at x. It leaves the expression stack here.
                        if iszero(q_has_top) { q_program_fail() }
                        let q_eval := q_top
                        q_has_top := 0
                        trace_u256(mload(0x8020), q_eval)
                        mstore(0x8020, add(mload(0x8020), 1))
                        // Fully-evaluated identity: qn = qn*y + eval.
                        // This matches the reverse y-power fold in Rust
                        // linearization once all identities have been read.
                        mstore(0x8000, mulmod(mload(0x8000), y, r))
                        mstore(0x8000, addmod(mload(0x8000), q_eval, r))
                    }
                    // VM 0x0b FOLD_SELECTOR: consume q_top into one simple-selector bucket.
                    case 0x0b {
                        // Operand layout packed into three bytes:
                        //   high byte: selector bucket index;
                        //   low u16 : y-power gap since this selector's
                        //             previous contribution.
                        let q_selector_payload := shr(232, mload(q_pc))
                        q_pc := add(q_pc, 3)
                        let q_sel_idx := shr(16, q_selector_payload)
                        let q_sel_gap := and(q_selector_payload, 0xffff)
                        // P12: the bucket index addresses the SELECTOR_ACC
                        // region and the gap indexes the y-power table; both
                        // are codegen-known sizes, so clamp before the writes.
                        if iszero(lt(q_sel_idx, 2)) { q_program_fail() }
                        if gt(q_sel_gap, 0x03) { q_program_fail() }
                        if iszero(q_has_top) { q_program_fail() }
                        let q_eval := q_top
                        q_has_top := 0
                        trace_u256(mload(0x8020), q_eval)
                        mstore(0x8020, add(mload(0x8020), 1))
                        // Simple-selector identity: keep the same y-batch
                        // position as main identities, then advance only this
                        // selector bucket by its codegen-known gap.
                        //
                        // The global fully-evaluated accumulator is still
                        // multiplied by y so later main identities land at the
                        // same y powers as Rust's reverse fold.
                        mstore(0x8000, mulmod(mload(0x8000), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add(0x8040, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
                    }
