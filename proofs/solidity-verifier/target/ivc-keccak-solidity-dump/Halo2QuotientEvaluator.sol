// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.24;

/// @title Split Halo2 quotient numerator evaluator.
/// @notice Reconstructs the scalar side of the linearization query for a generated verifier.
/// @dev This is the split-out implementation of the expensive
/// `partially_evaluate_identities` / `compute_linearization_commitment` side
/// from the Midfall Rust verifier:
/// - `midfall/proofs/src/plonk/mod.rs::partially_evaluate_identities`
/// - `midfall/proofs/src/plonk/linearization/verifier.rs::compute_linearization_commitment`
/// - `midfall/proofs/src/plonk/{permutation,logup,trash}.rs`
/// @dev The main verifier has already parsed calldata, checked proof scalar
/// ranges, sampled Fiat-Shamir challenges, loaded the VK payload, and computed
/// local Lagrange/public-input values before making the staticcall.
///
/// Instead of receiving structured Solidity arguments, the evaluator receives
/// the verifier's memory frame as raw calldata:
///
///   calldata[0..QUOTIENT_FRAME_LEN)
///      == memory[QUOTIENT_FRAME_BASE..QUOTIENT_FRAME_BASE+QUOTIENT_FRAME_LEN)
///
/// The fallback copies that frame back into the same generated memory
/// addresses. All constants below are therefore memory addresses inside that
/// copied frame, not ABI offsets.
///
/// Output is a compact fixed frame consumed by Halo2Verifier:
///
///   word 0: QUOTIENT_MAGIC, a generated version/magic guard
///   word 1: linearization_expected_eval
///   word 2..: simple-selector accumulator scalars
///
/// This contract reconstructs the Rust verifier's y-batched identity numerator
/// nu_y(x) and returns the linearization expected scalar -nu_y(x). It does not
/// evaluate or trust a quotient scalar h(x).
///
/// The quotient limb commitments are handled by Halo2Verifier on the commitment
/// side as (1 - x^n) * sum_i x_split^i * Q_i. That is why this scalar side is
/// -nu_y(x), not h(x) = nu_y(x) / (x^n - 1).
///
/// See docs/QUOTIENT_NUMERATOR_EVALUATOR.md for the full Rust/Solidity mapping.
contract Halo2QuotientEvaluator {
    // BLS12-381 scalar field modulus. All arithmetic in this contract is over
    // Fr and uses addmod/mulmod with this modulus.
    uint256 internal constant FR_MODULUS =
        0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    // Start of the copied verifier-key payload in memory. The VK payload also
    // carries the compact quotient VM constant/program tables used by the
    // included numerator block.
    uint256 internal constant                VK_MPTR = 0x3680;

    // Fiat-Shamir challenge slots. Halo2Verifier sampled these in transcript
    // order before the external call. The evaluator only reads them.
    uint256 internal constant        CHALLENGE_MPTR = 0x7900;
    uint256 internal constant            THETA_MPTR = 0x7900;
    uint256 internal constant             BETA_MPTR = 0x7920;
    uint256 internal constant            GAMMA_MPTR = 0x7940;
    uint256 internal constant TRASH_CHALLENGE_MPTR = 0x7960;
    uint256 internal constant                Y_MPTR = 0x7980;
    uint256 internal constant                X_MPTR = 0x79a0;
    uint256 internal constant               X1_MPTR = 0x79c0;
    uint256 internal constant               X2_MPTR = 0x79e0;
    uint256 internal constant               X3_MPTR = 0x7a00;
    uint256 internal constant               X4_MPTR = 0x7a20;

    // Common polynomial values at x. Halo2Verifier computes these once after
    // sampling x and places them in the frame so the numerator block can share
    // the exact Rust verifier inputs.
    uint256 internal constant              X_N_MPTR = 0x7c40;
    uint256 internal constant  X_N_MINUS_1_INV_MPTR = 0x7c60;
    uint256 internal constant           L_LAST_MPTR = 0x7c80;
    uint256 internal constant          L_BLIND_MPTR = 0x7ca0;
    uint256 internal constant              L_0_MPTR = 0x7cc0;
    uint256 internal constant     INSTANCE_EVAL_MPTR = 0x7ce0;
    uint256 internal constant     QUOTIENT_EVAL_MPTR = 0x7d00;

    // Proof evaluation table. Values are already decoded as canonical Fr words
    // by Halo2Verifier. The generated numerator code indexes this table by the
    // same query order as the Rust verifier.
    uint256 internal constant     REVERSED_EVALS_MPTR = 0x9480;

    // Scratch/output region for simple-selector linearization accumulators.
    // The numerator block writes one bucket per simple selector, then the
    // fallback copies those buckets into the compact return frame.
    uint256 internal constant      SELECTOR_ACC_MPTR = 0xb140;
    // Callee-local scratch for trace hooks. Trace-enabled verifier builds call
    // this evaluator with CALL so quotient identity logs can be compared with
    // the native Rust trace. Production verifier builds keep using STATICCALL
    // and render this evaluator without trace hooks.
    uint256 internal constant        TRACE_U256_MPTR = 0x1000;
    uint256 internal constant    QUOTIENT_OUTPUT_MPTR = 0x1000;

    // External-call frame metadata. The main verifier calls this contract with
    // exactly QUOTIENT_FRAME_LEN bytes starting at
    // QUOTIENT_FRAME_BASE, then checks the return length and QUOTIENT_MAGIC.
    uint256 internal constant QUOTIENT_FRAME_BASE = 0x3680;
    uint256 internal constant QUOTIENT_FRAME_LEN = 0x6ac0;
    uint256 internal constant QUOTIENT_OUTPUT_LEN = 0x0180;
    uint256 internal constant QUOTIENT_MAGIC = 0x00000000000000000000000000000000000000000000000051554556414c0001;

    /// @notice Evaluate the generated quotient numerator block for one verifier memory frame.
    /// @dev Calldata is exactly the raw frame, not ABI-encoded arguments. Returns `QUOTIENT_MAGIC`, the linearization expected eval, and selector buckets.
    /// @dev This fallback also uses generated absolute memory addresses and
    /// returns directly from assembly. Its compact return frame starts at
    /// `0x80`, preserving Solidity's reserved memory words.
    fallback() external {
        assembly ("memory-safe") {
            // Reject malformed calls. This contract is not a general-purpose
            // ABI endpoint; accepting partial or shifted frames would make the
            // generated memory addresses point at the wrong data.
            if iszero(eq(calldatasize(), QUOTIENT_FRAME_LEN)) { revert(0, 0) }

            // Rehydrate the verifier memory image. From this point onward the
            // generated Yul can use the same MPTR constants as the monolithic
            // verifier path.
            calldatacopy(QUOTIENT_FRAME_BASE, 0, QUOTIENT_FRAME_LEN)

            let r := FR_MODULUS

            // This included block is the main body of the evaluator. It:
            //   1. evaluates gate/permutation/lookup/trash identities in the
            //      same order as Rust `partially_evaluate_identities`;
            //   2. y-batches fully evaluated identities into
            //      quotient_eval_numer;
            //   3. y-batches simple-selector identities into
            //      SELECTOR_ACC_MPTR buckets;
            //   4. writes -quotient_eval_numer to QUOTIENT_EVAL_MPTR.
            //
            // Depending on codegen settings, some identities are native Yul
            // callbacks and the rest are executed by the compact q_program VM
            // stored in the copied VK payload.
            //
            // The upstream Rust comments call out that simple multiplicative
            // selectors do not appear as normal proof eval scalars. The Yul
            // block mirrors that rule by accumulating those identities into
            // SELECTOR_ACC_MPTR buckets for later multiplication by fixed
            // selector commitments, while fully evaluated identities contribute
            // to the negated expected scalar.            // Optional quotient helper functions. Each one is rendered only
            // when the Rust lowering pass recognized the corresponding
            // expression shape in this generated verifier. They are pure Fr
            // helpers and share the same FR_MODULUS as the surrounding
            // numerator block.
            // VK-specialized identity helper for Poseidon S-box terms.
            //
            // Rust source shape:
            //   circuits/src/hash/poseidon/poseidon_chip.rs::sbox
            //   full_round_gate / partial_round_gate
            //   circuits/src/hash/poseidon/round_skips.rs::RoundId
            //
            // The Rust verifier only sees this as an Expression tree from
            // `vk.cs.gates`; the generator emits q_pow5 after recognizing five
            // equal multiplicative factors. It is a codegen shortcut for x^5,
            // not a separate verifier rule.
            function q_pow5(x) -> z {
                let q_r := FR_MODULUS
                let x2 := mulmod(x, x, q_r)
                z := mulmod(x, mulmod(x2, x2, q_r), q_r)
            }            // ===============================================================
            // Batched identity numerator / linearization target.
            //
            // This block does not evaluate the quotient polynomial h(x), and
            // the proof does not provide an h(x) scalar to trust. Instead it:
            //
            //   1. Reconstructs the y-batched constraint numerator nu_y(x)
            //      from the alleged polynomial evaluations read after the
            //      transcript sampled x.
            //   2. Stores -nu_y(x) as the expected opening scalar for the
            //      linearized commitment.
            //
            // The commitment side is built in the next block from the quotient
            // limb commitments as (1 - x^n) * Σ_i x_split^i * Q_i, plus any
            // simple-selector commitments. The PCS check later binds that
            // linearized commitment to this expected scalar at x.
            //
            // Rust source-of-truth:
            //   - verifier.rs reads quotient commitments, samples x, then
            //     reads/computes all evaluations used below.
            //   - mod.rs::partially_evaluate_identities returns identities in
            //     gate, permutation, lookup, trash order.
            //   - linearization/verifier.rs::compute_linearization_commitment
            //     reverse-folds those identities by powers of y, sends
            //     simple-selector identities to selector commitment scalars,
            //     and subtracts fully-evaluated identities into expected_eval.
            //
            // This template is shared by the monolithic and external quotient
            // paths. In the external path, Halo2QuotientEvaluator first copies
            // the verifier memory frame into the same generated addresses.
            //
            // Runtime inputs expected to exist before this block starts:
            //   - `r` is the BLS12-381 scalar-field modulus.
            //   - Y_MPTR holds the quotient batching challenge y.
            //   - X_MPTR, L_*_MPTR, INSTANCE_EVAL_MPTR, and
            //     REVERSED_EVALS_MPTR hold values parsed or derived by the
            //     main verifier after the transcript sampled x.
            //   - VK_MPTR holds the pinned VK payload; in compact mode that
            //     payload includes the quotient constant table and bytecode.
            //
            // Runtime outputs written by this block:
            //   - QUOTIENT_EVAL_MPTR receives the scalar expected opening for
            //     the linearized commitment, namely -nu_y(x).
            //   - SELECTOR_ACC_MPTR[0..num_simple_selectors) receives one
            //     linearization scalar per generated simple selector.
            //
            // Line-by-line reading conventions used below:
            //
            //   * Every runtime value is one canonical Fr element stored in a
            //     256-bit EVM memory word. The small integer operands decoded
            //     from q_program are never field values; they are pointers,
            //     constant-table slots, selector indexes, offsets, or counts.
            //
            //   * `mload(ptr)` is the only way the VM turns a small pointer
            //     operand into a real 255-bit field element. The value loaded
            //     from memory is then combined with `addmod(..., r)` or
            //     `mulmod(..., r)`, so every arithmetic line is reduced modulo
            //     the BLS12-381 scalar-field order.
            //
            //   * `q_top` is the cached top of the VM operand stack. When an
            //     opcode needs to push while `q_top` is already live, the old
            //     value is written to `q_sp` and `q_sp` is advanced by one
            //     word. Binary `ADD`/`MUL` move `q_sp` back by one word and
            //     combine that spilled value with `q_top`.
            //
            //   * Identity boundaries are explicit. Expression opcodes leave
            //     one value in `q_top`; `FOLD_MAIN` or `FOLD_SELECTOR` consumes
            //     it and advances the global y-batch position. Native callback
            //     opcodes are only emitted at empty-stack boundaries and run
            //     generated Yul that performs the same fold side effects.
            //
            //   * The generated Solidity source intentionally emits comments
            //     before opcode cases. Those comments are documentation only:
            //     they do not affect bytecode, but they make rendered verifier
            //     assembly readable without jumping back to Rust codegen.
            // ===============================================================
            {
                // Compact quotient-program mode.
                //
                // The largest identity expressions are not all emitted as
                // unrolled Yul. Instead, most arithmetic is encoded as a small
                // q_program bytecode stored in the VK payload. This block
                // interprets that program, while selected heavy identities may
                // still be emitted as native callbacks for gas.
                //
                // Compact mode is a code-size trade: short bytecode operands
                // name already-planned memory slots, and the interpreter turns
                // those names into Fr arithmetic. The opcode stream is fully
                // generated and pinned by the VK/runtime codehash; no proof
                // calldata can alter control flow.
                // Load the quotient batching challenge used by every fold.
                let y := mload(Y_MPTR)

                // q_const_mptr points to Fr constants used by the VM.
                // q_program_mptr points to the bytecode stream.
                // Constants are stored as consecutive 32-byte Fr words.
                let q_const_mptr := 0x3a60
                // Program bytes are also stored in the VK payload, packed into
                // 32-byte words by PackedProgramCodec.
                let q_program_mptr := 0x50a0
                // Running Horner accumulator for fully evaluated identities.
                // After all identities, this is nu_y(x) for the `None`
                // identity group.
                // Initialize A = 0 before scanning the identity stream.
                mstore(0xb280, 0)
                // Simple selectors are grouped into separate linearization
                // buckets. They start at zero for every proof.
                // q_sel_zero_off walks selector bucket byte offsets.
                for { let q_sel_zero_off := 0 } lt(q_sel_zero_off, 0x0140) { q_sel_zero_off := add(q_sel_zero_off, 0x20) } {
                    // B_s = 0 for each simple selector bucket.
                    mstore(add(SELECTOR_ACC_MPTR, q_sel_zero_off), 0)
                }
                // Codegen knows the selector identity positions. Precompute
                // the y^k powers needed for selector gap and tail updates,
                // avoiding a runtime y^-1 modexp and per-identity selector
                // scale maintenance.
                {
                    // q_y_power holds y^i at the current loop index.
                    let q_y_power := 1
                    // Slot 0 holds y^0 = 1. Codegen never emits a read of it
                    // (FOLD_SELECTOR guards on a nonzero gap, and
                    // selector_tail_updates drops zero tails), but the tail
                    // block multiplies by mload(selector_power_mptr + offset)
                    // unconditionally -- so initialize the slot rather than
                    // leaving correctness to two filters in another file.
                    mstore(0xb2c0, 1)
                    // Start at i=1 because y^0 = 1 is written above.
                    for { let q_y_power_i := 1 } lt(q_y_power_i, 49) { q_y_power_i := add(q_y_power_i, 1) } {
                        // Advance from y^(i-1) to y^i modulo Fr.
                        q_y_power := mulmod(q_y_power, y, r)
                        // Store y^i at selector_power_mptr + 32*i.
                        mstore(add(0xb2c0, shl(5, q_y_power_i)), q_y_power)
                    }
                }

                // Direct inline prefix. These identities are generated as Yul
                // before entering the VM. They use the same fold snippets as
                // VM/native identities, so they occupy the same y-batch order.
                {
                let var0 := 0x1
                let f_3 := mload(0x9ac0)
                let f_4 := mload(0x99c0)
                let a_0 := mload(0x94a0)
                let var1 := mulmod(f_4, a_0, r)
                let var2 := addmod(f_3, var1, r)
                let f_5 := mload(0x99e0)
                let a_1 := mload(0x94c0)
                let var3 := mulmod(f_5, a_1, r)
                let var4 := addmod(var2, var3, r)
                let f_6 := mload(0x9a00)
                let a_2 := mload(0x94e0)
                let var5 := mulmod(f_6, a_2, r)
                let var6 := addmod(var4, var5, r)
                let f_7 := mload(0x9a20)
                let a_3 := mload(0x9500)
                let var7 := mulmod(f_7, a_3, r)
                let var8 := addmod(var6, var7, r)
                let f_8 := mload(0x9a40)
                let a_4 := mload(0x9520)
                let var9 := mulmod(f_8, a_4, r)
                let var10 := addmod(var8, var9, r)
                let f_0 := mload(0x9a60)
                let a_0_next_1 := mload(0x9540)
                let var11 := mulmod(f_0, a_0_next_1, r)
                let var12 := addmod(var10, var11, r)
                let f_1 := mload(0x9a80)
                let var13 := mulmod(f_1, a_0, r)
                let var14 := mulmod(var13, a_1, r)
                let var15 := addmod(var12, var14, r)
                let f_2 := mload(0x9aa0)
                let var16 := mulmod(f_2, a_0, r)
                let var17 := mulmod(var16, a_2, r)
                let var18 := addmod(var15, var17, r)
                let var19 := mulmod(var0, var18, r)
                mstore(0xb8e0, var19)
                }
                mstore(0xb280, mulmod(mload(0xb280), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x0)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x94c0)
                let a_2 := mload(0x94e0)
                let var1 := addmod(a_1, a_2, r)
                let a_3 := mload(0x9500)
                let var2 := addmod(0, sub(r, a_3), r)
                let var3 := addmod(var1, var2, r)
                let a_4 := mload(0x9520)
                let var4 := addmod(0, sub(r, a_4), r)
                let var5 := addmod(var3, var4, r)
                let var6 := mulmod(var0, var5, r)
                mstore(0xb8e0, var6)
                }
                mstore(0xb280, mulmod(mload(0xb280), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                }
                {
                let var0 := 0x1
                let a_0 := mload(0x94a0)
                let f_4 := mload(0x99c0)
                let var1 := addmod(a_0, f_4, r)
                let a_0_next_1 := mload(0x9540)
                let var2 := addmod(0, sub(r, a_0_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0xb8e0, var4)
                }
                mstore(0xb280, mulmod(mload(0xb280), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                }
                {
                let var0 := 0x1
                let a_1 := mload(0x94c0)
                let f_5 := mload(0x99e0)
                let var1 := addmod(a_1, f_5, r)
                let a_1_next_1 := mload(0x9560)
                let var2 := addmod(0, sub(r, a_1_next_1), r)
                let var3 := addmod(var1, var2, r)
                let var4 := mulmod(var0, var3, r)
                mstore(0xb8e0, var4)
                }
                mstore(0xb280, mulmod(mload(0xb280), y, r))
                {
                let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                let q_selector_acc := mload(q_selector_ptr)
                q_selector_acc := mulmod(q_selector_acc, mload(add(0xb2c0, 0x20)), r)
                mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                }

                // VM registers:
                //   q_pc      current bytecode pointer
                //   q_end     end of bytecode stream
                //   q_sp      memory stack pointer for non-top stack values
                //   q_top     cached top-of-stack value
                //   q_has_top whether q_top currently holds a stack value
                //
                // The cached top reduces memory traffic in the interpreter.
                // q_sp's registered range must cover the interpreted operand
                // stack plus any native callback scratch that reuses this base
                // pointer. In particular, the native permutation callback
                // writes a structured scratch table at program.stack_mptr.
                // q_pc starts at the first encoded instruction.
                let q_pc := q_program_mptr
                // q_end is an exclusive byte pointer for the VM loop.
                let q_end := add(q_program_mptr, 0x11cf)
                // q_sp starts at the first free stack word.
                let q_sp := 0xb8e0
                // q_top is meaningless until q_has_top is set.
                let q_top := 0
                // q_has_top = 0 means the VM stack is empty.
                let q_has_top := 0

                // q_program opcode summary:
                //   0x01/0x09 push const       0x02/0x05 push memory
                //   0x03/0x04 push token ptr   0x06 add, 0x07 mul, 0x08 neg
                //   0x0a fold main identity    0x0b fold selector identity
                //   0x0c..0x11 add/mul const or memory into top
                //   0x12..0x16 fused add-mul runs
                //   0x17/0x18 reserved
                //   0x19 native permutation    0x1b native heavy identity
                //   0x1c LIN7                 0x1d BILIN7_ROW
                //   0x1e BILIN7_PAIRWISE      0x1f native lookup
                //   0x20 POW5                 0x21 MODARITH7
                //   0x22 AFFINE_SUM
                //
                // The default IVC verifier uses one physical encoding for the
                // logical VM: compact byte-oriented opcodes with variable-width
                // operands, dynamic runs, and limb-aware cases.
                
                // Byte-oriented encoding: opcodes are one byte followed by
                // variable-width operand bytes.
                for { } lt(q_pc, q_end) { } {
                    // The bytecode table is byte-addressed, but EVM memory
                    // loads whole words. `byte(0, mload(q_pc))` extracts the
                    // opcode at the current byte cursor; each case advances
                    // q_pc by exactly its operand width.
                    let q_op := byte(0, mload(q_pc))
                    q_pc := add(q_pc, 1)

                    switch q_op
                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.
                    case 0x05 {
                        // Operand layout: u16 absolute memory pointer. The
                        // memory planner keeps the hot quotient frame below
                        // 64 KiB when this compact form is emitted.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        if q_has_top {
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
                        q_sp := sub(q_sp, 0x20)
                        q_top := addmod(mload(q_sp), q_top, r)
                    }
                    // VM 0x08 NEG: replace q_top with its Fr negation.
                    case 0x08 {
                        // addmod(0, r - x, r) maps zero back to zero and every
                        // nonzero scalar to its canonical additive inverse.
                        q_top := addmod(0, sub(r, q_top), r)
                    }
                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.
                    case 0x0d {
                        // One-byte constant-index multiply, used by short
                        // affine chains after an initial PUSH.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.
                    case 0x10 {
                        // Operand layout: u16 pointer. The pointed word is an
                        // already range-checked Fr scalar in verifier memory.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := addmod(q_top, mload(q_ptr), r)
                    }
                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.
                    case 0x11 {
                        // In-place multiply by a planned memory word.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := mulmod(q_top, mload(q_ptr), r)
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
                            let q_lhs_value := mload(q_lhs)
                            for { let q_i := 0 } lt(q_i, 7) { q_i := add(q_i, 1) } {
                                let q_word := mload(q_pc)
                                let qconst := byte(0, q_word)
                                let q_rhs := and(shr(232, q_word), 0xffff)
                                q_pc := add(q_pc, 3)
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
                        q_sp := 0xb8e0
                        // The generated lines below call the same fold snippets
                        // used by interpreted expressions, so trace IDs and
                        // y-batch positions remain contiguous.
                        {
                        let delta := 0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
                        let q_perm_vals := 0xb8e0
                        let q_perm_sigmas := 0xbb20
                        let q_perm_z_cur := 0xbd60
                        let q_perm_z_next := 0xbe20
                        let q_perm_z_last := 0xbee0
                        let q_perm_delta_base_ptr := 0xbf80
                        let q_perm_num_cols := 18
                        let q_perm_num_sets := 6
                        let q_perm_chunk_len := 3
                        let q_perm_delta_chunk := 0x4285088329c399ea457a8ca1d30f8957e74c7f529842a1579b4fee55b3982923
                        mstore(add(q_perm_vals, 0x0), mload(0x99a0))
                        {
                        for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 5) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {
                        let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)
                        let q_perm_val_load_src_off := q_perm_val_load_dst_off
                        mstore(add(add(q_perm_vals, 0x20), q_perm_val_load_dst_off), mload(add(0x94a0, q_perm_val_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_vals, 0xc0), mload(0x9480))
                        mstore(add(q_perm_vals, 0xe0), mload(INSTANCE_EVAL_MPTR))
                        {
                        for { let q_perm_val_load_i := 0 } lt(q_perm_val_load_i, 9) { q_perm_val_load_i := add(q_perm_val_load_i, 1) } {
                        let q_perm_val_load_dst_off := shl(5, q_perm_val_load_i)
                        let q_perm_val_load_src_off := q_perm_val_load_dst_off
                        mstore(add(add(q_perm_vals, 0x100), q_perm_val_load_dst_off), mload(add(0x95a0, q_perm_val_load_src_off)))
                        }
                        }
                        mstore(add(q_perm_vals, 0x220), mload(0x9980))
                        {
                        for { let q_perm_sigma_load_i := 0 } lt(q_perm_sigma_load_i, 18) { q_perm_sigma_load_i := add(q_perm_sigma_load_i, 1) } {
                        let q_perm_sigma_load_dst_off := shl(5, q_perm_sigma_load_i)
                        let q_perm_sigma_load_src_off := q_perm_sigma_load_dst_off
                        mstore(add(add(q_perm_sigmas, 0x0), q_perm_sigma_load_dst_off), mload(add(0x9bc0, q_perm_sigma_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_cur_load_i := 0 } lt(q_perm_z_cur_load_i, 6) { q_perm_z_cur_load_i := add(q_perm_z_cur_load_i, 1) } {
                        let q_perm_z_cur_load_dst_off := shl(5, q_perm_z_cur_load_i)
                        let q_perm_z_cur_load_src_off := mul(q_perm_z_cur_load_i, 0x60)
                        mstore(add(add(q_perm_z_cur, 0x0), q_perm_z_cur_load_dst_off), mload(add(0x9e00, q_perm_z_cur_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_next_load_i := 0 } lt(q_perm_z_next_load_i, 6) { q_perm_z_next_load_i := add(q_perm_z_next_load_i, 1) } {
                        let q_perm_z_next_load_dst_off := shl(5, q_perm_z_next_load_i)
                        let q_perm_z_next_load_src_off := mul(q_perm_z_next_load_i, 0x60)
                        mstore(add(add(q_perm_z_next, 0x0), q_perm_z_next_load_dst_off), mload(add(0x9e20, q_perm_z_next_load_src_off)))
                        }
                        }
                        {
                        for { let q_perm_z_last_load_i := 0 } lt(q_perm_z_last_load_i, 5) { q_perm_z_last_load_i := add(q_perm_z_last_load_i, 1) } {
                        let q_perm_z_last_load_dst_off := shl(5, q_perm_z_last_load_i)
                        let q_perm_z_last_load_src_off := mul(q_perm_z_last_load_i, 0x60)
                        mstore(add(add(q_perm_z_last, 0x0), q_perm_z_last_load_dst_off), mload(add(0x9e40, q_perm_z_last_load_src_off)))
                        }
                        }
                        let q_perm_eval := 0
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_perm_eval, r))
                        let q_perm_zn := mload(add(q_perm_z_cur, 0xa0))
                        q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_perm_eval, r))
                        for { let q_perm_i := 1 } lt(q_perm_i, 6) { q_perm_i := add(q_perm_i, 1) } {
                        let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))
                        let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))
                        q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_perm_eval, r))
                        }
                        mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))
                        for { let q_perm_set := 0 } lt(q_perm_set, 6) { q_perm_set := add(q_perm_set, 1) } {
                        let q_perm_start := mul(q_perm_set, q_perm_chunk_len)
                        let q_perm_end := add(q_perm_start, q_perm_chunk_len)
                        if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }
                        let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))
                        let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))
                        let q_perm_delta_pow := mload(q_perm_delta_base_ptr)
                        for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {
                        let q_perm_off := shl(5, q_perm_j)
                        let q_perm_v := mload(add(q_perm_vals, q_perm_off))
                        let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))
                        q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)
                        q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)
                        q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)
                        }
                        q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_perm_eval, r))
                        mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))
                        }
                        }
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
                        q_sp := 0xb8e0
                        // Generated LogUp code follows the same y-batch order
                        // as the Rust identity stream.
                        {
                        let q_lookup_f := 0xb8e0
                        let q_lookup_prefix := 0xb960
                        let q_lookup_suffix := 0xb9e0
                        let q_lookup_l0 := mload(L_0_MPTR)
                        let q_lookup_llast := mload(L_LAST_MPTR)
                        let q_lookup_lblind := mload(L_BLIND_MPTR)
                        let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)
                        let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)
                        let q_lookup_beta := mload(BETA_MPTR)
                        let q_lookup_theta := mload(THETA_MPTR)
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0xa060), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        {
                        let f_10 := mload(0x9ae0)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_10, r)
                        let var1 := mulmod(var0, q_lookup_theta, r)
                        for { let q_lookup_shared_i := 0 } lt(q_lookup_shared_i, 4) { q_lookup_shared_i := add(q_lookup_shared_i, 1) } {
                        let q_lookup_shared_off := shl(5, q_lookup_shared_i)
                        let q_lookup_shared_tail := mload(add(0x94c0, q_lookup_shared_off))
                        let q_lookup_shared_compressed := addmod(var1, q_lookup_shared_tail, r)
                        mstore(add(q_lookup_f, q_lookup_shared_off), addmod(q_lookup_shared_compressed, q_lookup_beta, r))
                        }
                        let q_lookup_product := 1
                        for { let q_lookup_prod_i := 0 } lt(q_lookup_prod_i, 4) { q_lookup_prod_i := add(q_lookup_prod_i, 1) } {
                        q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)
                        }
                        mstore(q_lookup_prefix, 1)
                        for { let q_lookup_pref_i := 1 } lt(q_lookup_pref_i, 4) { q_lookup_pref_i := add(q_lookup_pref_i, 1) } {
                        let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)
                        mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))
                        }
                        mstore(add(q_lookup_suffix, 0x60), 1)
                        for { let q_lookup_suf_i := sub(4, 1) } gt(q_lookup_suf_i, 0) { q_lookup_suf_i := sub(q_lookup_suf_i, 1) } {
                        let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)
                        mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))
                        }
                        let q_lookup_sum := 0
                        for { let q_lookup_sum_i := 0 } lt(q_lookup_sum_i, 4) { q_lookup_sum_i := add(q_lookup_sum_i, 1) } {
                        q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)
                        }
                        let q_lookup_eval := addmod(mulmod(mload(0xa040), q_lookup_product, r), sub(r, q_lookup_sum), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0xa040)
                        let f_17 := mload(0x9b60)
                        let f_11 := mload(0x9b00)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), f_11, r)
                        let f_12 := mload(0x9b20)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), f_12, r)
                        let q_lookup_s_sum_h := mulmod(f_17, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0xa080), sub(r, addmod(mload(0xa060), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var1, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0xa020), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        }
                        {
                        {
                        let q_lookup_eval := mulmod(q_lookup_lsum, mload(0xa0e0), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        {
                        let a_14 := mload(0x9980)
                        let var0 := addmod(mulmod(0, q_lookup_theta, r), a_14, r)
                        let a_0 := mload(0x94a0)
                        let var1 := addmod(mulmod(var0, q_lookup_theta, r), a_0, r)
                        let a_1 := mload(0x94c0)
                        let var2 := addmod(mulmod(var1, q_lookup_theta, r), a_1, r)
                        let a_2 := mload(0x94e0)
                        let var3 := addmod(mulmod(var2, q_lookup_theta, r), a_2, r)
                        let a_3 := mload(0x9500)
                        let var4 := addmod(mulmod(var3, q_lookup_theta, r), a_3, r)
                        let a_4 := mload(0x9520)
                        let var5 := addmod(mulmod(var4, q_lookup_theta, r), a_4, r)
                        let a_5 := mload(0x95a0)
                        let var6 := addmod(mulmod(var5, q_lookup_theta, r), a_5, r)
                        let a_6 := mload(0x95c0)
                        let var7 := addmod(mulmod(var6, q_lookup_theta, r), a_6, r)
                        let a_7 := mload(0x95e0)
                        let var8 := addmod(mulmod(var7, q_lookup_theta, r), a_7, r)
                        let a_8 := mload(0x9600)
                        let var9 := addmod(mulmod(var8, q_lookup_theta, r), a_8, r)
                        let a_9 := mload(0x9620)
                        let var10 := addmod(mulmod(var9, q_lookup_theta, r), a_9, r)
                        let a_10 := mload(0x9640)
                        let var11 := addmod(mulmod(var10, q_lookup_theta, r), a_10, r)
                        let a_11 := mload(0x9660)
                        let var12 := addmod(mulmod(var11, q_lookup_theta, r), a_11, r)
                        let a_12 := mload(0x9680)
                        let var13 := addmod(mulmod(var12, q_lookup_theta, r), a_12, r)
                        let a_13 := mload(0x96a0)
                        let var14 := addmod(mulmod(var13, q_lookup_theta, r), a_13, r)
                        let f_13 := mload(0x9b40)
                        let var15 := addmod(mulmod(var14, q_lookup_theta, r), f_13, r)
                        let q_lookup_eval := addmod(mulmod(mload(0xa0c0), addmod(var15, q_lookup_beta, r), r), sub(r, 1), r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        {
                        let q_lookup_sum_h := mload(0xa0c0)
                        let var0 := 0x1
                        let f_26 := mload(0x9ba0)
                        let var1 := addmod(0, sub(r, f_26), r)
                        let var2 := addmod(var0, var1, r)
                        let a_14 := mload(0x9980)
                        let var3 := mulmod(var2, a_14, r)
                        let var4 := addmod(mulmod(0, q_lookup_theta, r), var3, r)
                        let a_0 := mload(0x94a0)
                        let var5 := mulmod(var2, a_0, r)
                        let var6 := addmod(mulmod(var4, q_lookup_theta, r), var5, r)
                        let a_1 := mload(0x94c0)
                        let var7 := mulmod(var2, a_1, r)
                        let var8 := addmod(mulmod(var6, q_lookup_theta, r), var7, r)
                        let a_2 := mload(0x94e0)
                        let var9 := mulmod(var2, a_2, r)
                        let var10 := addmod(mulmod(var8, q_lookup_theta, r), var9, r)
                        let a_3 := mload(0x9500)
                        let var11 := mulmod(var2, a_3, r)
                        let var12 := addmod(mulmod(var10, q_lookup_theta, r), var11, r)
                        let a_4 := mload(0x9520)
                        let var13 := mulmod(var2, a_4, r)
                        let var14 := addmod(mulmod(var12, q_lookup_theta, r), var13, r)
                        let a_5 := mload(0x95a0)
                        let var15 := mulmod(var2, a_5, r)
                        let var16 := addmod(mulmod(var14, q_lookup_theta, r), var15, r)
                        let a_6 := mload(0x95c0)
                        let var17 := mulmod(var2, a_6, r)
                        let var18 := addmod(mulmod(var16, q_lookup_theta, r), var17, r)
                        let a_7 := mload(0x95e0)
                        let var19 := mulmod(var2, a_7, r)
                        let var20 := addmod(mulmod(var18, q_lookup_theta, r), var19, r)
                        let a_8 := mload(0x9600)
                        let var21 := mulmod(var2, a_8, r)
                        let var22 := addmod(mulmod(var20, q_lookup_theta, r), var21, r)
                        let a_9 := mload(0x9620)
                        let var23 := mulmod(var2, a_9, r)
                        let var24 := addmod(mulmod(var22, q_lookup_theta, r), var23, r)
                        let a_10 := mload(0x9640)
                        let var25 := mulmod(var2, a_10, r)
                        let var26 := addmod(mulmod(var24, q_lookup_theta, r), var25, r)
                        let a_11 := mload(0x9660)
                        let var27 := mulmod(var2, a_11, r)
                        let var28 := addmod(mulmod(var26, q_lookup_theta, r), var27, r)
                        let a_12 := mload(0x9680)
                        let var29 := mulmod(var2, a_12, r)
                        let var30 := addmod(mulmod(var28, q_lookup_theta, r), var29, r)
                        let a_13 := mload(0x96a0)
                        let var31 := mulmod(var2, a_13, r)
                        let var32 := addmod(mulmod(var30, q_lookup_theta, r), var31, r)
                        let f_13 := mload(0x9b40)
                        let var33 := mulmod(var2, f_13, r)
                        let var34 := addmod(mulmod(var32, q_lookup_theta, r), var33, r)
                        let q_lookup_s_sum_h := mulmod(var0, q_lookup_sum_h, r)
                        let q_lookup_diff := addmod(mload(0xa100), sub(r, addmod(mload(0xa0e0), q_lookup_s_sum_h, r)), r)
                        let q_lookup_t_beta := addmod(var34, q_lookup_beta, r)
                        let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), mload(0xa0a0), r)
                        let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        mstore(0xb280, addmod(mload(0xb280), q_lookup_eval, r))
                        }
                        }
                        }
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
                        q_sp := 0xb8e0
                        // Native identity sub-cases are generated from selected heavy gate identities.
                        switch q_native_idx
                        case 0 {
                            {
                            let var0 := 0x1
                            let f_0 := mload(0x9a60)
                            let a_0_next_1 := mload(0x9540)
                            let var1 := addmod(0, sub(r, a_0_next_1), r)
                            let var2 := addmod(f_0, var1, r)
                            let var3 := 0x1b8114c381b922fd5d6d241210e2d8a68ad5744053ba9e776118de4107b51ace
                            let a_0 := mload(0x94a0)
                            let var4 := mulmod(a_0, a_0, r)
                            let a_3 := mload(0x9500)
                            let var5 := mulmod(var4, a_3, r)
                            let var6 := mulmod(var3, var5, r)
                            let var7 := addmod(var2, var6, r)
                            let var8 := 0x3df32e4cc4cb2ed20e5d21899cf5331775990ccaec4c09b4e3717213fcc0d763
                            let a_1 := mload(0x94c0)
                            let var9 := mulmod(a_1, a_1, r)
                            let a_4 := mload(0x9520)
                            let var10 := mulmod(var9, a_4, r)
                            let var11 := mulmod(var8, var10, r)
                            let var12 := addmod(var7, var11, r)
                            let var13 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                            let a_2 := mload(0x94e0)
                            let var14 := mulmod(a_2, a_2, r)
                            let a_5 := mload(0x95a0)
                            let var15 := mulmod(var14, a_5, r)
                            let var16 := mulmod(var13, var15, r)
                            let var17 := addmod(var12, var16, r)
                            let var18 := mulmod(var0, var17, r)
                            mstore(0xb8e0, var18)
                            }
                            mstore(0xb280, mulmod(mload(0xb280), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                            let q_selector_acc := mload(q_selector_ptr)
                            q_selector_acc := mulmod(q_selector_acc, mload(add(0xb2c0, 0x20)), r)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                            }
                        }
                        case 1 {
                            {
                            let var0 := 0x1
                            let f_1 := mload(0x9a80)
                            let a_1_next_1 := mload(0x9560)
                            let var1 := addmod(0, sub(r, a_1_next_1), r)
                            let var2 := addmod(f_1, var1, r)
                            let var3 := 0x404d21073985d14e432a4ad76d3fae06ca74314b950fe7b1d7f501cd31a8b374
                            let a_0 := mload(0x94a0)
                            let var4 := mulmod(a_0, a_0, r)
                            let a_3 := mload(0x9500)
                            let var5 := mulmod(var4, a_3, r)
                            let var6 := mulmod(var3, var5, r)
                            let var7 := addmod(var2, var6, r)
                            let var8 := 0xb2cc8704264c6bd81bc620e9e524d4b73e9b2317679422ff7fa1603955649f1
                            let a_1 := mload(0x94c0)
                            let var9 := mulmod(a_1, a_1, r)
                            let a_4 := mload(0x9520)
                            let var10 := mulmod(var9, a_4, r)
                            let var11 := mulmod(var8, var10, r)
                            let var12 := addmod(var7, var11, r)
                            let var13 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                            let a_2 := mload(0x94e0)
                            let var14 := mulmod(a_2, a_2, r)
                            let a_5 := mload(0x95a0)
                            let var15 := mulmod(var14, a_5, r)
                            let var16 := mulmod(var13, var15, r)
                            let var17 := addmod(var12, var16, r)
                            let var18 := mulmod(var0, var17, r)
                            mstore(0xb8e0, var18)
                            }
                            mstore(0xb280, mulmod(mload(0xb280), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                            let q_selector_acc := mload(q_selector_ptr)
                            q_selector_acc := mulmod(q_selector_acc, mload(add(0xb2c0, 0x20)), r)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                            }
                        }
                        case 2 {
                            {
                            let var0 := 0x1
                            let a_0 := mload(0x94a0)
                            let a_0_next_1 := mload(0x9540)
                            let var1 := mulmod(a_0, a_0_next_1, r)
                            let var2 := 0x100000000000000
                            let a_1_next_1 := mload(0x9560)
                            let var3 := mulmod(a_0, a_1_next_1, r)
                            let var4 := mulmod(var2, var3, r)
                            let var5 := addmod(var1, var4, r)
                            let var6 := 0x10000000000000000000000000000
                            let a_2_next_1 := mload(0x9580)
                            let var7 := mulmod(a_0, a_2_next_1, r)
                            let var8 := mulmod(var6, var7, r)
                            let var9 := addmod(var5, var8, r)
                            let a_1 := mload(0x94c0)
                            let var10 := mulmod(a_1, a_0_next_1, r)
                            let var11 := mulmod(var2, var10, r)
                            let var12 := addmod(var9, var11, r)
                            let var13 := mulmod(a_1, a_1_next_1, r)
                            let var14 := mulmod(var6, var13, r)
                            let var15 := addmod(var12, var14, r)
                            let var16 := 0x3212e00cde6d2002b119d800000347fcb8
                            let a_6_next_1 := mload(0x9720)
                            let var17 := mulmod(a_1, a_6_next_1, r)
                            let var18 := mulmod(var16, var17, r)
                            let var19 := addmod(var15, var18, r)
                            let a_2 := mload(0x94e0)
                            let var20 := mulmod(a_2, a_0_next_1, r)
                            let var21 := mulmod(var6, var20, r)
                            let var22 := addmod(var19, var21, r)
                            let a_5_next_1 := mload(0x9700)
                            let var23 := mulmod(a_2, a_5_next_1, r)
                            let var24 := mulmod(var16, var23, r)
                            let var25 := addmod(var22, var24, r)
                            let var26 := 0x297784894e27525bc342b7fde37dba9366
                            let var27 := mulmod(a_2, a_6_next_1, r)
                            let var28 := mulmod(var26, var27, r)
                            let var29 := addmod(var25, var28, r)
                            let a_3 := mload(0x9500)
                            let a_4_next_1 := mload(0x96e0)
                            let var30 := mulmod(a_3, a_4_next_1, r)
                            let var31 := mulmod(var16, var30, r)
                            let var32 := addmod(var29, var31, r)
                            let var33 := mulmod(a_3, a_5_next_1, r)
                            let var34 := mulmod(var26, var33, r)
                            let var35 := addmod(var32, var34, r)
                            let var36 := 0x340f2ebe380a0f5eff4360543988a61dc2
                            let var37 := mulmod(a_3, a_6_next_1, r)
                            let var38 := mulmod(var36, var37, r)
                            let var39 := addmod(var35, var38, r)
                            let a_4 := mload(0x9520)
                            let a_3_next_1 := mload(0x96c0)
                            let var40 := mulmod(a_4, a_3_next_1, r)
                            let var41 := mulmod(var16, var40, r)
                            let var42 := addmod(var39, var41, r)
                            let var43 := mulmod(a_4, a_4_next_1, r)
                            let var44 := mulmod(var26, var43, r)
                            let var45 := addmod(var42, var44, r)
                            let var46 := mulmod(a_4, a_5_next_1, r)
                            let var47 := mulmod(var36, var46, r)
                            let var48 := addmod(var45, var47, r)
                            let var49 := 0x13af65741744bd7bb2c6872df2b800320
                            let var50 := mulmod(a_4, a_6_next_1, r)
                            let var51 := mulmod(var49, var50, r)
                            let var52 := addmod(var48, var51, r)
                            let a_5 := mload(0x95a0)
                            let var53 := mulmod(a_5, a_2_next_1, r)
                            let var54 := mulmod(var16, var53, r)
                            let var55 := addmod(var52, var54, r)
                            let var56 := mulmod(a_5, a_3_next_1, r)
                            let var57 := mulmod(var26, var56, r)
                            let var58 := addmod(var55, var57, r)
                            let var59 := mulmod(a_5, a_4_next_1, r)
                            let var60 := mulmod(var36, var59, r)
                            let var61 := addmod(var58, var60, r)
                            let var62 := mulmod(a_5, a_5_next_1, r)
                            let var63 := mulmod(var49, var62, r)
                            let var64 := addmod(var61, var63, r)
                            let var65 := 0x2cb9b546d20373eaf85e8f53db883cb548
                            let var66 := mulmod(a_5, a_6_next_1, r)
                            let var67 := mulmod(var65, var66, r)
                            let var68 := addmod(var64, var67, r)
                            let a_6 := mload(0x95c0)
                            let var69 := mulmod(a_6, a_1_next_1, r)
                            let var70 := mulmod(var16, var69, r)
                            let var71 := addmod(var68, var70, r)
                            let var72 := mulmod(a_6, a_2_next_1, r)
                            let var73 := mulmod(var26, var72, r)
                            let var74 := addmod(var71, var73, r)
                            let var75 := mulmod(a_6, a_3_next_1, r)
                            let var76 := mulmod(var36, var75, r)
                            let var77 := addmod(var74, var76, r)
                            let var78 := mulmod(a_6, a_4_next_1, r)
                            let var79 := mulmod(var49, var78, r)
                            let var80 := addmod(var77, var79, r)
                            let var81 := mulmod(a_6, a_5_next_1, r)
                            let var82 := mulmod(var65, var81, r)
                            let var83 := addmod(var80, var82, r)
                            let var84 := 0xc8557e86f90d0d89eed6eb5349a0f8820
                            let var85 := mulmod(a_6, a_6_next_1, r)
                            let var86 := mulmod(var84, var85, r)
                            let var87 := addmod(var83, var86, r)
                            let var88 := mulmod(var2, a_1, r)
                            let var89 := addmod(a_0, var88, r)
                            let var90 := mulmod(var6, a_2, r)
                            let var91 := addmod(var89, var90, r)
                            let var92 := addmod(var87, var91, r)
                            let var93 := mulmod(var2, a_1_next_1, r)
                            let var94 := addmod(a_0_next_1, var93, r)
                            let var95 := mulmod(var6, a_2_next_1, r)
                            let var96 := addmod(var94, var95, r)
                            let var97 := addmod(var92, var96, r)
                            let a_7 := mload(0x95e0)
                            let a_8 := mload(0x9600)
                            let var98 := mulmod(var2, a_8, r)
                            let var99 := addmod(a_7, var98, r)
                            let a_9 := mload(0x9620)
                            let var100 := mulmod(var6, a_9, r)
                            let var101 := addmod(var99, var100, r)
                            let var102 := addmod(0, sub(r, var101), r)
                            let var103 := addmod(var97, var102, r)
                            let a_7_next_1 := mload(0x9740)
                            let var104 := 0x241eabfffeb153ffffb9feffffffffaaab
                            let var105 := mulmod(a_7_next_1, var104, r)
                            let var106 := addmod(0, sub(r, var105), r)
                            let var107 := addmod(var103, var106, r)
                            let var108 := addmod(0, sub(r, var16), r)
                            let var109 := addmod(var107, var108, r)
                            let a_8_next_1 := mload(0x9760)
                            let var110 := 0x73eda753299d7d483339d80809a1d80553b9202d7ffe85d4800008bb20000001
                            let var111 := addmod(a_8_next_1, var110, r)
                            let var112 := 0x4000000000000000000000000000000000
                            let var113 := mulmod(var111, var112, r)
                            let var114 := addmod(0, sub(r, var113), r)
                            let var115 := addmod(var109, var114, r)
                            let var116 := mulmod(var0, var115, r)
                            mstore(0xb8e0, var116)
                            }
                            mstore(0xb280, mulmod(mload(0xb280), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                            }
                        }
                        case 3 {
                            {
                            let var0 := 0x1
                            let a_0 := mload(0x94a0)
                            let var1 := 0x10000000000000000000000000000
                            let var2 := addmod(a_0, var1, r)
                            let var3 := 0x100000000000000
                            let a_1 := mload(0x94c0)
                            let var4 := addmod(a_1, var1, r)
                            let var5 := mulmod(var3, var4, r)
                            let var6 := addmod(var2, var5, r)
                            let a_2 := mload(0x94e0)
                            let var7 := addmod(a_2, var1, r)
                            let var8 := mulmod(var1, var7, r)
                            let var9 := addmod(var6, var8, r)
                            let a_7 := mload(0x95e0)
                            let a_8 := mload(0x9600)
                            let var10 := mulmod(var3, a_8, r)
                            let var11 := addmod(a_7, var10, r)
                            let a_9 := mload(0x9620)
                            let var12 := mulmod(var1, a_9, r)
                            let var13 := addmod(var11, var12, r)
                            let var14 := addmod(0, sub(r, var13), r)
                            let var15 := addmod(var9, var14, r)
                            let var16 := addmod(0, sub(r, var1), r)
                            let var17 := addmod(var15, var16, r)
                            let a_7_next_1 := mload(0x9740)
                            let var18 := 0x241eabfffeb153ffffb9feffffffffaaab
                            let var19 := mulmod(a_7_next_1, var18, r)
                            let var20 := addmod(0, sub(r, var19), r)
                            let var21 := addmod(var17, var20, r)
                            let var22 := 0xd9d44a30b019261257667fde3844a8cd6
                            let var23 := addmod(0, sub(r, var22), r)
                            let var24 := addmod(var21, var23, r)
                            let a_8_next_1 := mload(0x9760)
                            let var25 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5b6e855000003ab00002
                            let var26 := addmod(a_8_next_1, var25, r)
                            let var27 := 0x4000000000000000000000000000000000
                            let var28 := mulmod(var26, var27, r)
                            let var29 := addmod(0, sub(r, var28), r)
                            let var30 := addmod(var24, var29, r)
                            let var31 := mulmod(var0, var30, r)
                            mstore(0xb8e0, var31)
                            }
                            mstore(0xb280, mulmod(mload(0xb280), y, r))
                            {
                            let q_selector_ptr := add(SELECTOR_ACC_MPTR, 0xa0)
                            let q_selector_acc := mload(q_selector_ptr)
                            mstore(q_selector_ptr, addmod(q_selector_acc, mload(0xb8e0), r))
                            }
                        }
                        default { revert(0, 0) }
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
                        let q_eval := q_top
                        q_has_top := 0
                        // Simple-selector identity: keep the same y-batch
                        // position as main identities, then advance only this
                        // selector bucket by its codegen-known gap.
                        //
                        // The global fully-evaluated accumulator is still
                        // multiplied by y so later main identities land at the
                        // same y powers as Rust's reverse fold.
                        mstore(0xb280, mulmod(mload(0xb280), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add(0xb2c0, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
                    }
                    // Invalid generated bytecode should fail closed. 0x1a intentionally lands here.
                    default {
                        revert(0, 0)
                    }
                }
                // The VK-pinned bytecode must end exactly at q_end and every
                // identity must have been consumed by a fold/native callback.
                // This catches malformed generator output whose final opcode
                // over-reads operands or leaves a partial expression live.
                if iszero(eq(q_pc, q_end)) { revert(0, 0) }
                if q_has_top { revert(0, 0) }
                // The spilled stack must also be balanced. A FOLD executed
                // with more than one operand live consumes only the cached
                // top, leaving abandoned words below q_sp with q_has_top
                // clear -- so both checks above pass while an operand of the
                // identity has been silently dropped from nu_y(x).
                if iszero(eq(q_sp, 0xb8e0)) { revert(0, 0) }

                // Structured post-VM suffix. The current default uses this for
                // regular trash constraints: it is smaller than fully unrolled
                // Yul and cheaper than interpreting every trash operation.
                //
                // These generated blocks run after q_pc reaches q_end, but
                // they still participate in the same identity order and write
                // into the same numerator / selector accumulators.
                {
                let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)
                {
                let f_0 := mload(0x9a60)
                let a_0_next_1 := mload(0x9540)
                let var0 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
                let var1 := mulmod(a_0_next_1, var0, r)
                let var2 := addmod(f_0, var1, r)
                let var3 := 0x590ba402032e82eb1f660ef09796c5686345a5054ed96dae8e2d233633788771
                let a_0 := mload(0x94a0)
                let var4 := mulmod(var3, a_0, r)
                let var5 := addmod(var2, var4, r)
                let var6 := 0x52f789e4afc3801f7411102ee2f47cc5954a744e71cac98e75ea962a55a0a76f
                let a_1 := mload(0x94c0)
                let var7 := mulmod(var6, a_1, r)
                let var8 := addmod(var5, var7, r)
                let var9 := 0x3509dd2fe3aac0080783557fec090fb1cb4b2b0901253c55282024331d1fe1a8
                let a_2 := mload(0x94e0)
                let var10 := q_pow5(a_2)
                let var11 := mulmod(var9, var10, r)
                let var12 := addmod(var8, var11, r)
                let var13 := 0x333f8046ece5579cbd6872449c57f2703dfc8864cfadc06d587ff104a0d0c1f2
                let a_3 := mload(0x9500)
                let var14 := q_pow5(a_3)
                let var15 := mulmod(var13, var14, r)
                let var16 := addmod(var12, var15, r)
                let var17 := 0x412c98232b6ab8a47aa76ee814ef7ec6261987c9802f2cfc490e007951a60ca5
                let a_4 := mload(0x9520)
                let var18 := q_pow5(a_4)
                let var19 := mulmod(var17, var18, r)
                let var20 := addmod(var16, var19, r)
                let var21 := 0x53fded36d490ba6b05a5d10fd99ffe5456baec6a6a8753199d5ebdc33c99790e
                let a_5 := mload(0x95a0)
                let var22 := q_pow5(a_5)
                let var23 := mulmod(var21, var22, r)
                let var24 := addmod(var20, var23, r)
                let var25 := 0x6ccb1c7d87f3c12a2bde4e68ac7f1e8b03481ba15d7f88f9a7f9b8310dd6d34
                let a_6 := mload(0x95c0)
                let var26 := q_pow5(a_6)
                let var27 := mulmod(var25, var26, r)
                let var28 := addmod(var24, var27, r)
                let var29 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                let a_7 := mload(0x95e0)
                let var30 := q_pow5(a_7)
                let var31 := mulmod(var29, var30, r)
                let var32 := addmod(var28, var31, r)
                let var33 := addmod(mulmod(0, q_trash_tau, r), var32, r)
                let f_1 := mload(0x9a80)
                let a_1_next_1 := mload(0x9560)
                let var34 := mulmod(a_1_next_1, var0, r)
                let var35 := addmod(f_1, var34, r)
                let var36 := 0x5b1fc262a28cbb8bf75d9b1a6edaa74591ec24cd9a209512213cec3a3c0f1a5d
                let var37 := mulmod(var36, a_0, r)
                let var38 := addmod(var35, var37, r)
                let var39 := 0x4d0ea7f9c3fda06d9535b0fdafd8338bd47c2200b284fa71a325ff41ac358028
                let var40 := mulmod(var39, a_1, r)
                let var41 := addmod(var38, var40, r)
                let var42 := 0x26cc223e16f47c20e17cc6069605fa5a8af05ea4f6eb36029a641d23b818eb10
                let var43 := mulmod(var42, var10, r)
                let var44 := addmod(var41, var43, r)
                let var45 := 0x31e823a45e567484c1544e310c0fa5cd66547a8f0dde659ac61698c30e838d25
                let var46 := mulmod(var45, var14, r)
                let var47 := addmod(var44, var46, r)
                let var48 := 0x275a20361ea91992193920270d3e2d1f6361880ac0a439c64bef815d4469ba85
                let var49 := mulmod(var48, var18, r)
                let var50 := addmod(var47, var49, r)
                let var51 := 0x5f3a15bab4ce4097b1edc3a25002694b92395ce355a8a12fe557459d9633f701
                let var52 := mulmod(var51, var22, r)
                let var53 := addmod(var50, var52, r)
                let var54 := 0x301cf56f9b4577112cc4241cddf6484aaadedbf1bbd0f2351adf2e41c2fb2ecd
                let var55 := mulmod(var54, var26, r)
                let var56 := addmod(var53, var55, r)
                let var57 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                let var58 := mulmod(var57, var30, r)
                let var59 := addmod(var56, var58, r)
                let var60 := addmod(mulmod(var33, q_trash_tau, r), var59, r)
                let f_2 := mload(0x9aa0)
                let var61 := mulmod(a_3, var0, r)
                let var62 := addmod(f_2, var61, r)
                let var63 := 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140
                let var64 := mulmod(var63, a_0, r)
                let var65 := addmod(var62, var64, r)
                let var66 := 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a
                let var67 := mulmod(var66, a_1, r)
                let var68 := addmod(var65, var67, r)
                let var69 := 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db
                let var70 := mulmod(var69, var10, r)
                let var71 := addmod(var68, var70, r)
                let var72 := addmod(mulmod(var60, q_trash_tau, r), var71, r)
                let f_3 := mload(0x9ac0)
                let var73 := mulmod(a_4, var0, r)
                let var74 := addmod(f_3, var73, r)
                let var75 := 0x222e83e70453dfee19b402e9fa8dfe2c4987b034d0be3ceb478b3022e97934c1
                let var76 := mulmod(var75, a_0, r)
                let var77 := addmod(var74, var76, r)
                let var78 := 0x26c2cc87f95726b28f33ca03409a460ec987cfe12adae32769e3565865d07191
                let var79 := mulmod(var78, a_1, r)
                let var80 := addmod(var77, var79, r)
                let var81 := 0x4382d0938a760120dd6cef8f3b90a0c38abae475e3d21e39365472b76d780272
                let var82 := mulmod(var81, var10, r)
                let var83 := addmod(var80, var82, r)
                let var84 := mulmod(var69, var14, r)
                let var85 := addmod(var83, var84, r)
                let var86 := addmod(mulmod(var72, q_trash_tau, r), var85, r)
                let f_4 := mload(0x99c0)
                let var87 := mulmod(a_5, var0, r)
                let var88 := addmod(f_4, var87, r)
                let var89 := 0x726df1506749848155630b86ae25a82b281ecd050fe3a52d85a181fa87202e4b
                let var90 := mulmod(var89, a_0, r)
                let var91 := addmod(var88, var90, r)
                let var92 := 0x24822e1af9aa2887c912c87eb0f20bd332330e7e55cd784de67cb407a9f05520
                let var93 := mulmod(var92, a_1, r)
                let var94 := addmod(var91, var93, r)
                let var95 := 0x4e5280109d8f96b8bfb543a6b1af25fb56a9db616af85a90eedc558e3eb1ea29
                let var96 := mulmod(var95, var10, r)
                let var97 := addmod(var94, var96, r)
                let var98 := mulmod(var81, var14, r)
                let var99 := addmod(var97, var98, r)
                let var100 := mulmod(var69, var18, r)
                let var101 := addmod(var99, var100, r)
                let var102 := addmod(mulmod(var86, q_trash_tau, r), var101, r)
                let f_5 := mload(0x99e0)
                let var103 := mulmod(a_6, var0, r)
                let var104 := addmod(f_5, var103, r)
                let var105 := 0x2f5908b169c6cf1bd26dcf0f9e5105481f5164f3ece0582bf3098312167751a7
                let var106 := mulmod(var105, a_0, r)
                let var107 := addmod(var104, var106, r)
                let var108 := 0x23a6684b942d726a22e4d5b8d8ff83aeaa773f62600184efe5d033d7c7c6e827
                let var109 := mulmod(var108, a_1, r)
                let var110 := addmod(var107, var109, r)
                let var111 := 0x1981b4b33d6a9dab957b351d981d3323e65da39493af5bc01f7e8ffe17f98d4e
                let var112 := mulmod(var111, var10, r)
                let var113 := addmod(var110, var112, r)
                let var114 := mulmod(var95, var14, r)
                let var115 := addmod(var113, var114, r)
                let var116 := mulmod(var81, var18, r)
                let var117 := addmod(var115, var116, r)
                let var118 := mulmod(var69, var22, r)
                let var119 := addmod(var117, var118, r)
                let var120 := addmod(mulmod(var102, q_trash_tau, r), var119, r)
                let f_6 := mload(0x9a00)
                let var121 := mulmod(a_7, var0, r)
                let var122 := addmod(f_6, var121, r)
                let var123 := 0x6d05a41959f539a7fc9ec0972ea1e3dbb6fc67dd51daf3414f7fbbb091c7274a
                let var124 := mulmod(var123, a_0, r)
                let var125 := addmod(var122, var124, r)
                let var126 := 0x27e7119226c42a6d19c1541904b99ae40685511ed2e078964b74594d38340849
                let var127 := mulmod(var126, a_1, r)
                let var128 := addmod(var125, var127, r)
                let var129 := 0xd94c46a8456352aa44d7a885ab59e3a36664e6fb25e826f8a4cd79822f0533
                let var130 := mulmod(var129, var10, r)
                let var131 := addmod(var128, var130, r)
                let var132 := mulmod(var111, var14, r)
                let var133 := addmod(var131, var132, r)
                let var134 := mulmod(var95, var18, r)
                let var135 := addmod(var133, var134, r)
                let var136 := mulmod(var81, var22, r)
                let var137 := addmod(var135, var136, r)
                let var138 := mulmod(var69, var26, r)
                let var139 := addmod(var137, var138, r)
                let var140 := addmod(mulmod(var120, q_trash_tau, r), var139, r)
                let f_7 := mload(0x9a20)
                let a_2_next_1 := mload(0x9580)
                let var141 := mulmod(a_2_next_1, var0, r)
                let var142 := addmod(f_7, var141, r)
                let var143 := 0x70d8f2a733a64d650faccc9b1c2a766a9544bb3ff1a11ee73cb43947ef386633
                let var144 := mulmod(var143, a_0, r)
                let var145 := addmod(var142, var144, r)
                let var146 := 0x40fa389feb2522bb934881ac9ed749aee2296502af592418c6b5675c0f560261
                let var147 := mulmod(var146, a_1, r)
                let var148 := addmod(var145, var147, r)
                let var149 := 0x1f61345b652161410c5e29f51e301ae56342af824bc110649393d2b911c50d3e
                let var150 := mulmod(var149, var10, r)
                let var151 := addmod(var148, var150, r)
                let var152 := mulmod(var129, var14, r)
                let var153 := addmod(var151, var152, r)
                let var154 := mulmod(var111, var18, r)
                let var155 := addmod(var153, var154, r)
                let var156 := mulmod(var95, var22, r)
                let var157 := addmod(var155, var156, r)
                let var158 := mulmod(var81, var26, r)
                let var159 := addmod(var157, var158, r)
                let var160 := mulmod(var69, var30, r)
                let var161 := addmod(var159, var160, r)
                let var162 := addmod(mulmod(var140, q_trash_tau, r), var161, r)
                let f_19 := mload(0x9b80)
                let q_trash_one_minus_selector := addmod(1, sub(r, f_19), r)
                let q_trash_scaled := mulmod(q_trash_one_minus_selector, mload(0xa120), r)
                let q_trash_eval := addmod(var162, sub(r, q_trash_scaled), r)
                mstore(0xb280, mulmod(mload(0xb280), y, r))
                mstore(0xb280, addmod(mload(0xb280), q_trash_eval, r))
                }
                }
                // Finish selector buckets by applying the codegen-known tail
                // from each selector's last identity to the end of the global
                // y-batch.
                //
                // After this step, every selector bucket is aligned with the
                // final global y position and can be multiplied by its fixed
                // selector commitment in the linearized MSM.
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x00)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0600)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x20)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x05e0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x40)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0580)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x60)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x04c0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x80)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0460)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xa0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0400)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xc0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x03a0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0xe0)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0340)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0100)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x02e0)), r))
                }
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, 0x0120)
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add(0xb2c0, 0x0280)), r))
                }

                // Fully evaluated identities are the constant-polynomial side
                // of the linearization query. Rust subtracts that grouped
                // scalar into expected_eval, so Solidity stores -nu_y(x).
                let linearization_expected_eval := addmod(0, sub(r, mload(0xb280)), r)
                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)
                pop(y)
            }

            // Return the compact output frame. Halo2Verifier checks the magic,
            // stores word 1 as the linearization expected eval, then expands
            // selector buckets into the fused final PCS MSM.
            mstore(QUOTIENT_OUTPUT_MPTR, QUOTIENT_MAGIC)
            mstore(add(QUOTIENT_OUTPUT_MPTR, 0x20), mload(QUOTIENT_EVAL_MPTR))
            // Copy selector buckets from the generated absolute memory region
            // into the compact external-call return frame.
            for { let q_i := 0 } lt(q_i, 10) { q_i := add(q_i, 1) } {
                mstore(add(QUOTIENT_OUTPUT_MPTR, add(0x40, shl(5, q_i))), mload(add(SELECTOR_ACC_MPTR, shl(5, q_i))))
            }
            return(QUOTIENT_OUTPUT_MPTR, QUOTIENT_OUTPUT_LEN)
        }
    }
}