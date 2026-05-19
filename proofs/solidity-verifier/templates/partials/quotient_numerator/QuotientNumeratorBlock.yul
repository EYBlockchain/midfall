            // ===============================================================
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
                {%- match quotient_program %}
                {%- when Some with (program) %}
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
                let q_const_mptr := {{ program.const_mptr|hex() }}
                // Program bytes are also stored in the VK payload, packed into
                // 32-byte words by PackedProgramCodec.
                let q_program_mptr := {{ program.program_mptr|hex() }}
                // Running Horner accumulator for fully evaluated identities.
                // After all identities, this is nu_y(x) for the `None`
                // identity group.
                // Initialize A = 0 before scanning the identity stream.
                mstore({{ program.eval_numer_mptr|hex() }}, 0)
                {%- if self.trace %}
                // Trace builds label each emitted identity in y-batch order.
                mstore({{ program.trace_id_mptr|hex() }}, {{ quotient_identity_trace_base }})
                {%- endif %}
                {%- if simple_selector_cols.len() > 0 %}
                // Simple selectors are grouped into separate linearization
                // buckets. They start at zero for every proof.
                // q_sel_zero_off walks selector bucket byte offsets.
                for { let q_sel_zero_off := 0 } lt(q_sel_zero_off, {{ (simple_selector_cols.len() * 0x20)|hex() }}) { q_sel_zero_off := add(q_sel_zero_off, 0x20) } {
                    // B_s = 0 for each simple selector bucket.
                    mstore(add(SELECTOR_ACC_MPTR, q_sel_zero_off), 0)
                }

                {%- if program.selector_max_power > 0 %}
                // Codegen knows the selector identity positions. Precompute
                // the y^k powers needed for selector gap and tail updates,
                // avoiding a runtime y^-1 modexp and per-identity selector
                // scale maintenance.
                {
                    // q_y_power holds y^i at the current loop index.
                    let q_y_power := 1
                    // Start at i=1 because y^0 = 1 is implicit and never read.
                    for { let q_y_power_i := 1 } lt(q_y_power_i, {{ program.selector_max_power + 1 }}) { q_y_power_i := add(q_y_power_i, 1) } {
                        // Advance from y^(i-1) to y^i modulo Fr.
                        q_y_power := mulmod(q_y_power, y, r)
                        // Store y^i at selector_power_mptr + 32*i.
                        mstore(add({{ program.selector_power_mptr|hex() }}, shl(5, q_y_power_i)), q_y_power)
                    }
                }
                {%- endif %}
                {%- endif %}

                // Direct inline prefix. These identities are generated as Yul
                // before entering the VM. They use the same fold snippets as
                // VM/native identities, so they occupy the same y-batch order.
                {%- for code_block in quotient_inline_computations %}
                {%- for line in code_block %}
                {{ line }}
                {%- endfor %}
                {%- endfor %}

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
                let q_end := add(q_program_mptr, {{ program.len|hex() }})
                // q_sp starts at the first free stack word.
                let q_sp := {{ program.stack_mptr|hex() }}
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
                {#
                Template-only switch/case reference.

                This comment documents the interpreter source without being
                emitted into generated Solidity. Runtime behavior lives in the
                switch blocks below; opcode numbers and operand layouts are
                defined in src/codegen/quotient/mod.rs.

                Shared stack model:
                - q_top caches the top stack value.
                - q_has_top records whether q_top is live.
                - q_sp points just past spilled stack words.
                - push-like cases spill the old q_top when q_has_top is set.
                - ADD/MUL pop by moving q_sp back one word.
                - accumulator cases mutate q_top in place.
                - FOLD_* cases consume q_top and advance the y-batch state.
                - native callbacks reset q_top/q_sp and perform their own
                  fold calls inside generated callback code.

                Case map:
                0x01 push_const
                  bytes:    u16 const_idx
                  effect:   push q_const_mptr[const_idx]

                0x02 push_mem_literal
                  bytes:    u32 ptr
                  effect:   push mload(ptr)

                0x03 push_mem_token
                  bytes:    u8 token
                  effect:   resolve token to a generated pointer and push it

                0x04 push_mem_token_offset
                  bytes:    u8 token, u32 offset
                  effect:   resolve token, add byte offset, and push mload

                0x05 push_mem_u16
                  bytes:    u16 ptr
                  effect:   compact pointer load

                0x06 add
                  effect: q_top = stack_pop() + q_top mod Fr

                0x07 mul
                  effect: q_top = stack_pop() * q_top mod Fr

                0x08 neg
                  effect: q_top = -q_top mod Fr

                0x09 push_const_u8
                  bytes:    u8 const_idx
                  effect:   short form of push_const

                0x0a fold_main
                  effect: trace q_top, advance q_eval_numer = q_eval_numer*y
                          + q_top

                0x0b fold_selector
                  bytes:    u8 selector_idx, u16 selector_gap
                  effect: trace q_top, advance the global y position, and add
                          q_top into a selector bucket after applying its
                          codegen-known y^gap

                0x0c add_const_u8
                  effect: q_top += q_const_mptr[u8 const_idx]

                0x0d mul_const_u8
                  effect: q_top *= q_const_mptr[u8 const_idx]

                0x0e add_const
                  effect: q_top += q_const_mptr[u16 const_idx]

                0x0f mul_const
                  effect: q_top *= q_const_mptr[u16 const_idx]

                0x10 add_mem_u16
                  effect: q_top += mload(u16 ptr)

                0x11 mul_mem_u16
                  effect: q_top *= mload(u16 ptr)

                0x12 add_mul_mem_mem_const_u8
                  bytes:    u16 lhs, u16 rhs, u8 const_idx
                  effect:   q_top += mload(lhs) * mload(rhs) * const

                0x13 add_mul_const_u8_mem_u16
                  bytes:    u16 ptr, u8 const_idx
                  effect:   q_top += mload(ptr) * const

                0x14 add_mul_mem_mem
                  bytes:    u16 lhs, u16 rhs
                  effect:   q_top += mload(lhs) * mload(rhs)

                0x15 run_add_mul_mem_mem_const_u8
                  bytes: u16 count, then count * {u16 lhs, u16 rhs, u8 c}
                  effect: repeated 0x12 in one dispatch

                0x16 run_add_mul_const_u8_mem_u16
                  bytes: u16 count, then count * {u16 ptr, u8 c}
                  effect: repeated 0x13 in one dispatch

                0x22 affine_sum
                  bytes: u16 lin_count, u16 product_count,
                    lin_count * {u16 ptr, u8 c},
                    product_count * {u16 lhs, u16 rhs, u8 c}
                  effect: q_top += sum c_i * mload(p_i)
                    + sum c_i * mload(p_i) * mload(q_i)

                0x19 native_permutation
                  effect: evaluate and fold the generated permutation identity
                          family at this VM stream position

                0x1a reserved
                  effect: no switch case; default branch reverts

                0x1b native_identity
                  effect: dispatch to one generated heavy-gate callback by index

                0x1c lin7
                  bytes: seven {u8 const_idx, u16 ptr} pairs
                  effect: push sum_i const_i * mload(ptr_i)

                0x1d bilin7_row
                  bytes: u16 lhs, seven {u8 const_idx, u16 rhs} pairs
                  effect: push mload(lhs) * sum_i const_i * mload(rhs_i)

                0x1e bilin7_pairwise
                  bytes: u16 lhs_base, u16 rhs_base, 13 const indexes
                  effect: push sum_{i,j} const_{i+j} * lhs_i * rhs_j

                0x1f native_lookup
                  effect: evaluate and fold LogUp boundary/helper/accumulator
                          identities at this VM stream position

                0x20 pow5
                  effect: q_top = q_top^5

                0x21 modarith7
                  bytes: flags, optional cond/constant, count header,
                              then fused LIN7/BILIN7/mem/product blocks
                  effect: push one fused affine 7-limb identity value

                Memory token map used by 0x03/0x04:
                0x01 L_0_MPTR
                0x02 L_LAST_MPTR
                0x03 L_BLIND_MPTR
                0x04 BETA_MPTR
                0x05 GAMMA_MPTR
                0x06 X_MPTR
                0x07 THETA_MPTR
                0x08 TRASH_CHALLENGE_MPTR
                0x09 INSTANCE_EVAL_MPTR
                #}
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
                    {%- if program.op_usage.push_const %}
                    // VM 0x01 PUSH_CONST (bytes): next two bytes are a constant-table slot.
                    case {{ template_constants.quotient_vm.op.push_const|hex() }} {
                        // Operand layout: u16 const_idx. Constants are 32-byte
                        // Fr words, so shl(5, const_idx) converts an index to
                        // a byte offset.
                        let qconst := shr(240, mload(q_pc))
                        // Push semantics: spill the old cached top, if any,
                        // then install the loaded constant as the new q_top.
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(add(q_const_mptr, shl(5, qconst)))
                        q_has_top := 1
                        q_pc := add(q_pc, 2)
                    }
                    {%- endif %}
                    {%- if program.op_usage.push_mem_literal %}
                    // VM 0x02 PUSH_MEM_LITERAL (bytes): next four bytes are a memory pointer.
                    case {{ template_constants.quotient_vm.op.push_mem_literal|hex() }} {
                        // Operand layout: u32 absolute memory pointer. This is
                        // emitted only for planned addresses that do not fit in
                        // the smaller u16 form or token map.
                        let q_ptr := shr(224, mload(q_pc))
                        q_pc := add(q_pc, {{ template_constants.quotient_vm.byte_u32_bytes|hex() }})
                        // Load one canonical Fr word from generated memory and
                        // push it through the cached-top stack discipline.
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    {%- endif %}
                    {%- if program.op_usage.push_mem_token %}
                    // VM 0x03 PUSH_MEM_TOKEN (bytes): next byte selects a symbolic memory pointer.
                    case {{ template_constants.quotient_vm.op.push_mem_token|hex() }} {
                        // Operand layout: u8 token. Tokens cover the hot
                        // global verifier scalars used in many identities.
                        let q_token := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        let q_ptr := 0
                        // Token cases decode generated symbolic memory addresses.
                        switch q_token
                        {%- if program.mem_usage.l0 %}
                        case {{ template_constants.quotient_vm.mem.l0|hex() }} { q_ptr := L_0_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.l_last %}
                        case {{ template_constants.quotient_vm.mem.l_last|hex() }} { q_ptr := L_LAST_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.l_blind %}
                        case {{ template_constants.quotient_vm.mem.l_blind|hex() }} { q_ptr := L_BLIND_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.beta %}
                        case {{ template_constants.quotient_vm.mem.beta|hex() }} { q_ptr := BETA_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.gamma %}
                        case {{ template_constants.quotient_vm.mem.gamma|hex() }} { q_ptr := GAMMA_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.x %}
                        case {{ template_constants.quotient_vm.mem.x|hex() }} { q_ptr := X_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.theta %}
                        case {{ template_constants.quotient_vm.mem.theta|hex() }} { q_ptr := THETA_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.trash_challenge %}
                        case {{ template_constants.quotient_vm.mem.trash_challenge|hex() }} { q_ptr := TRASH_CHALLENGE_MPTR }
                        {%- endif %}
                        {%- if program.mem_usage.instance_eval %}
                        case {{ template_constants.quotient_vm.mem.instance_eval|hex() }} { q_ptr := INSTANCE_EVAL_MPTR }
                        {%- endif %}
                        // A token not advertised by the VM usage manifest is
                        // impossible for valid generated bytecode.
                        default { revert(0, 0) }
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    {%- endif %}
                    {%- if program.op_usage.push_mem_token_offset %}
                    // VM 0x04 PUSH_MEM_TOKEN_OFFSET (bytes): token byte plus u32 byte offset.
                    case {{ template_constants.quotient_vm.op.push_mem_token_offset|hex() }} {
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
                        {%- if program.mem_usage.l0 %}
                        case {{ template_constants.quotient_vm.mem.l0|hex() }} { q_ptr := add(L_0_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.l_last %}
                        case {{ template_constants.quotient_vm.mem.l_last|hex() }} { q_ptr := add(L_LAST_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.l_blind %}
                        case {{ template_constants.quotient_vm.mem.l_blind|hex() }} { q_ptr := add(L_BLIND_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.beta %}
                        case {{ template_constants.quotient_vm.mem.beta|hex() }} { q_ptr := add(BETA_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.gamma %}
                        case {{ template_constants.quotient_vm.mem.gamma|hex() }} { q_ptr := add(GAMMA_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.x %}
                        case {{ template_constants.quotient_vm.mem.x|hex() }} { q_ptr := add(X_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.theta %}
                        case {{ template_constants.quotient_vm.mem.theta|hex() }} { q_ptr := add(THETA_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.trash_challenge %}
                        case {{ template_constants.quotient_vm.mem.trash_challenge|hex() }} { q_ptr := add(TRASH_CHALLENGE_MPTR, q_off) }
                        {%- endif %}
                        {%- if program.mem_usage.instance_eval %}
                        case {{ template_constants.quotient_vm.mem.instance_eval|hex() }} { q_ptr := add(INSTANCE_EVAL_MPTR, q_off) }
                        {%- endif %}
                        default { revert(0, 0) }
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(q_ptr)
                        q_has_top := 1
                    }
                    {%- endif %}
                    {%- if program.op_usage.push_mem_u16 %}
                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.
                    case {{ template_constants.quotient_vm.op.push_mem_u16|hex() }} {
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
                    {%- endif %}
                    {%- if program.op_usage.add %}
                    // VM 0x06 ADD: pop one spilled stack word and add it to q_top.
                    case {{ template_constants.quotient_vm.op.add|hex() }} {
                        // The safety validator guarantees a spilled operand
                        // exists before ADD. q_top is the right operand.
                        q_sp := sub(q_sp, 0x20)
                        q_top := addmod(mload(q_sp), q_top, r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.mul %}
                    // VM 0x07 MUL: pop one spilled stack word and multiply it by q_top.
                    case {{ template_constants.quotient_vm.op.mul|hex() }} {
                        // Same stack contract as ADD, with multiplication
                        // reduced directly modulo Fr.
                        q_sp := sub(q_sp, 0x20)
                        q_top := mulmod(mload(q_sp), q_top, r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.neg %}
                    // VM 0x08 NEG: replace q_top with its Fr negation.
                    case {{ template_constants.quotient_vm.op.neg|hex() }} {
                        // addmod(0, r - x, r) maps zero back to zero and every
                        // nonzero scalar to its canonical additive inverse.
                        q_top := addmod(0, sub(r, q_top), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.pow5 %}
                    // VM 0x20 POW5: replace q_top with q_top^5.
                    case {{ template_constants.quotient_vm.op.pow5|hex() }} {
                        // Poseidon S-box shortcut: x^5 = x * (x^2)^2.
                        let q2 := mulmod(q_top, q_top, r)
                        q_top := mulmod(q_top, mulmod(q2, q2, r), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.push_const_u8 %}
                    // VM 0x09 PUSH_CONST_U8 (bytes): next byte is a constant-table slot.
                    case {{ template_constants.quotient_vm.op.push_const_u8|hex() }} {
                        // One-byte variant for the common case where the
                        // constant table has fewer than 256 referenced slots.
                        let qconst := byte(0, mload(q_pc))
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        q_top := mload(add(q_const_mptr, shl(5, qconst)))
                        q_has_top := 1
                        q_pc := add(q_pc, 1)
                    }
                    {%- endif %}
                    {%- if program.op_usage.add_const_u8 %}
                    // VM 0x0c ADD_CONST_U8: add a small constant-table slot into q_top.
                    case {{ template_constants.quotient_vm.op.add_const_u8|hex() }} {
                        // Accumulator opcode: mutates q_top in place instead
                        // of pushing a new stack value.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.mul_const_u8 %}
                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.
                    case {{ template_constants.quotient_vm.op.mul_const_u8|hex() }} {
                        // One-byte constant-index multiply, used by short
                        // affine chains after an initial PUSH.
                        let qconst := byte(0, mload(q_pc))
                        q_pc := add(q_pc, 1)
                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.add_const %}
                    // VM 0x0e ADD_CONST: add a wider constant-table slot into q_top.
                    case {{ template_constants.quotient_vm.op.add_const|hex() }} {
                        // Two-byte constant-index form for larger generated
                        // constant tables.
                        let qconst := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.mul_const %}
                    // VM 0x0f MUL_CONST: multiply q_top by a wider constant-table slot.
                    case {{ template_constants.quotient_vm.op.mul_const|hex() }} {
                        // Two-byte constant-index multiply.
                        let qconst := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.add_mem_u16 %}
                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.
                    case {{ template_constants.quotient_vm.op.add_mem_u16|hex() }} {
                        // Operand layout: u16 pointer. The pointed word is an
                        // already range-checked Fr scalar in verifier memory.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := addmod(q_top, mload(q_ptr), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.mul_mem_u16 %}
                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.
                    case {{ template_constants.quotient_vm.op.mul_mem_u16|hex() }} {
                        // In-place multiply by a planned memory word.
                        let q_ptr := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        q_top := mulmod(q_top, mload(q_ptr), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.add_mul_mem_mem_const_u8 %}
                    // VM 0x12 ADD_MUL_MEM_MEM_CONST_U8: fused q_top += lhs * rhs * const.
                    case {{ template_constants.quotient_vm.op.add_mul_mem_mem_const_u8|hex() }} {
                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr,
                        // u8 const_idx. This fuses a frequent affine-product
                        // term without spending opcodes on PUSH/MUL/MUL/ADD.
                        let q_word := mload(q_pc)
                        let q_lhs := shr(240, q_word)
                        let q_rhs := and(shr(224, q_word), 0xffff)
                        let qconst := byte(4, q_word)
                        q_pc := add(q_pc, 5)
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
                    {%- endif %}
                    {%- if program.op_usage.add_mul_const_u8_mem_u16 %}
                    // VM 0x13 ADD_MUL_CONST_U8_MEM_U16: fused q_top += mem * const.
                    case {{ template_constants.quotient_vm.op.add_mul_const_u8_mem_u16|hex() }} {
                        // Operand layout: u16 ptr, u8 const_idx.
                        let q_word := mload(q_pc)
                        let q_ptr := shr(240, q_word)
                        let qconst := byte(2, q_word)
                        q_pc := add(q_pc, 3)
                        q_top := addmod(
                            q_top,
                            mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                            r
                        )
                    }
                    {%- endif %}
                    {%- if program.op_usage.add_mul_mem_mem %}
                    // VM 0x14 ADD_MUL_MEM_MEM: fused q_top += lhs * rhs.
                    case {{ template_constants.quotient_vm.op.add_mul_mem_mem|hex() }} {
                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr. This is
                        // the unit-coefficient sibling of opcode 0x12.
                        let q_word := mload(q_pc)
                        let q_lhs := shr(240, q_word)
                        let q_rhs := and(shr(224, q_word), 0xffff)
                        q_pc := add(q_pc, {{ template_constants.quotient_vm.byte_u32_bytes|hex() }})
                        q_top := addmod(q_top, mulmod(mload(q_lhs), mload(q_rhs), r), r)
                    }
                    {%- endif %}
                    {%- if program.op_usage.run_add_mul_mem_mem_const_u8 %}
                    // VM 0x15 RUN_ADD_MUL_MEM_MEM_CONST_U8: byte-only loop over fused 0x12 payloads.
                    case {{ template_constants.quotient_vm.op.run_add_mul_mem_mem_const_u8|hex() }} {
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
                    {%- endif %}
                    {%- if program.op_usage.run_add_mul_const_u8_mem_u16 %}
                    // VM 0x16 RUN_ADD_MUL_CONST_U8_MEM_U16: byte-only loop over fused 0x13 payloads.
                    case {{ template_constants.quotient_vm.op.run_add_mul_const_u8_mem_u16|hex() }} {
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
                            q_top := addmod(
                                q_top,
                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),
                                r
                            )
                        }
                    }
                    {%- endif %}
                    {%- if program.op_usage.affine_sum %}
                    // VM 0x22 AFFINE_SUM: mixed byte-only affine linear/product loop.
                    case {{ template_constants.quotient_vm.op.affine_sum|hex() }} {
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
                    {%- endif %}
                    {%- if program.op_usage.lin7 || program.op_usage.bilin7_row || program.op_usage.bilin7_pairwise || program.op_usage.modarith7 %}
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
                    {%- endif %}
                    {%- if program.op_usage.lin7 %}
                    // VM 0x1c LIN7: byte-only 7-term foreign-field linear form.
                    case {{ template_constants.quotient_vm.op.lin7|hex() }} {
                        // LIN7: sum_i coeff[i] * value[i] over Fr.
                        // Typical Rust origin: foreign/gates/norm.rs
                        // normalization and foreign/gates/mul.rs base-power
                        // sums for x/y/z limbs.
                        //
                        // Operand layout: seven repeated {u8 const_idx,
                        // u16 ptr} pairs. The result is pushed as a fresh
                        // stack value.
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        // Accumulate exactly seven limbs, matching the
                        // generated foreign-field limb width.
                        for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
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
                        q_top := q_acc
                        q_has_top := 1
                    }
                    {%- endif %}
                    {%- if program.op_usage.bilin7_row %}
                    // VM 0x1d BILIN7_ROW: byte-only lhs times a 7-term weighted row.
                    case {{ template_constants.quotient_vm.op.bilin7_row|hex() }} {
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
                        let q_lhs_value := mload(q_lhs)
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
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
                        q_top := q_acc
                        q_has_top := 1
                    }
                    {%- endif %}
                    {%- if program.op_usage.bilin7_pairwise %}
                    // VM 0x1e BILIN7_PAIRWISE: byte-only 7-by-7 weighted convolution.
                    case {{ template_constants.quotient_vm.op.bilin7_pairwise|hex() }} {
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
                        q_pc := add(q_pc, {{ template_constants.quotient_vm.byte_u32_bytes|hex() }})
                        let q_coeff_pc := q_pc
                        q_pc := add(q_pc, {{ template_constants.quotient_vm.limb_pairwise_coeffs }})
                        if q_has_top {
                            mstore(q_sp, q_top)
                            q_sp := add(q_sp, 0x20)
                        }
                        let q_acc := 0
                        // Nested limb convolution over two contiguous
                        // 7-word vectors.
                        for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
                            let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))
                            for { let q_j := 0 } lt(q_j, {{ template_constants.quotient_vm.limb_count }}) { q_j := add(q_j, 1) } {
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
                    {%- endif %}
                    {%- if program.op_usage.modarith7 %}
                    // VM 0x21 MODARITH7: byte-only fused affine 7-limb foreign-field/ECC identity.
                    case {{ template_constants.quotient_vm.op.modarith7|hex() }} {
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
                            for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
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
                            for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
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
                            q_pc := add(q_pc, {{ template_constants.quotient_vm.byte_u32_bytes|hex() }})
                            let q_coeff_pc := q_pc
                            q_pc := add(q_pc, {{ template_constants.quotient_vm.limb_pairwise_coeffs }})
                            for { let q_i := 0 } lt(q_i, {{ template_constants.quotient_vm.limb_count }}) { q_i := add(q_i, 1) } {
                                let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))
                                for { let q_j := 0 } lt(q_j, {{ template_constants.quotient_vm.limb_count }}) { q_j := add(q_j, 1) } {
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
                    {%- endif %}
                    {%- if program.op_usage.native_permutation && quotient_native_permutation_computation.len() > 0 %}
                    // Native permutation callback. It evaluates the
                    // permutation identities from permutation.rs at this exact
                    // VM position, preserving the Rust identity order while
                    // avoiding a large interpreted product loop.
                    // VM 0x19 NATIVE_PERMUTATION: marker for the generated permutation callback.
                    case {{ template_constants.quotient_vm.op.native_permutation|hex() }} {
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
                        q_sp := {{ program.stack_mptr|hex() }}
                        // The generated lines below call the same fold snippets
                        // used by interpreted expressions, so trace IDs and
                        // y-batch positions remain contiguous.
                        {%- for line in quotient_native_permutation_computation %}
                        {{ line }}
                        {%- endfor %}
                    }
                    {%- endif %}
                    {%- if program.op_usage.native_lookup && quotient_native_lookup_computation.len() > 0 %}
                    // Native lookup callback. This whole-family opcode
                    // evaluates the LogUp boundary, helper-chunk, and
                    // accumulator identities at this VM position, preserving
                    // the Rust y-batch order while avoiding many interpreted
                    // product-loop opcodes.
                    // VM 0x1f NATIVE_LOOKUP: marker for the generated LogUp lookup callback.
                    case {{ template_constants.quotient_vm.op.native_lookup|hex() }} {
                        // Reset VM stack state before entering structured
                        // lookup Yul. Lookup callbacks own their scratch
                        // layout and perform all needed folds internally.
                        q_top := 0
                        q_has_top := 0
                        // The generated loop below uses program.stack_mptr as
                        // f+beta/prefix/suffix scratch rather than as a
                        // conventional VM stack. The Rust memory planner must
                        // reserve structured_lookup_scratch_words(meta).
                        q_sp := {{ program.stack_mptr|hex() }}
                        // Generated LogUp code follows the same y-batch order
                        // as the Rust identity stream.
                        {%- for line in quotient_native_lookup_computation %}
                        {{ line }}
                        {%- endfor %}
                    }
                    {%- endif %}
                    {%- if program.op_usage.native_identity && quotient_native_identity_computations.len() > 0 %}
                    // Native callbacks are generated only for the heaviest
                    // recognized Midfall gate identities. All other gate and
                    // non-native identity arithmetic remains in
                    // the compact q_program VM above, preserving the Rust
                    // `partially_evaluate_identities` order.
                    // VM 0x1b NATIVE_IDENTITY: marker for generated heavy-gate callbacks.
                    case {{ template_constants.quotient_vm.op.native_identity|hex() }} {
                        // Operand layout: u16 native callback index. The
                        // manifest validates that callback indexes appear in
                        // generated order and target existing switch cases.
                        let q_native_idx := shr(240, mload(q_pc))
                        q_pc := add(q_pc, 2)
                        // Heavy identities are whole expressions, so clear the
                        // interpreter stack before dispatching.
                        q_top := 0
                        q_has_top := 0
                        q_sp := {{ program.stack_mptr|hex() }}
                        // Native identity sub-cases are generated from selected heavy gate identities.
                        switch q_native_idx
                        {%- for code_block in quotient_native_identity_computations %}
                        case {{ loop.index0 }} {
                            {%- for line in code_block %}
                            {{ line }}
                            {%- endfor %}
                        }
                        {%- endfor %}
                        default { revert(0, 0) }
                    }
                    {%- endif %}
                    {%- if program.op_usage.fold_main %}
                    // VM 0x0a FOLD_MAIN: consume q_top into the fully evaluated numerator fold.
                    case {{ template_constants.quotient_vm.op.fold_main|hex() }} {
                        // q_top is the complete value of one fully evaluated
                        // identity at x. It leaves the expression stack here.
                        let q_eval := q_top
                        q_has_top := 0
                        {%- if self.trace %}
                        trace_u256(mload({{ program.trace_id_mptr|hex() }}), q_eval)
                        mstore({{ program.trace_id_mptr|hex() }}, add(mload({{ program.trace_id_mptr|hex() }}), 1))
                        {%- endif %}
                        // Fully-evaluated identity: qn = qn*y + eval.
                        // This matches the reverse y-power fold in Rust
                        // linearization once all identities have been read.
                        mstore({{ program.eval_numer_mptr|hex() }}, mulmod(mload({{ program.eval_numer_mptr|hex() }}), y, r))
                        mstore({{ program.eval_numer_mptr|hex() }}, addmod(mload({{ program.eval_numer_mptr|hex() }}), q_eval, r))
                    }
                    {%- endif %}
                    {%- if program.op_usage.fold_selector %}
                    // VM 0x0b FOLD_SELECTOR: consume q_top into one simple-selector bucket.
                    case {{ template_constants.quotient_vm.op.fold_selector|hex() }} {
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
                        {%- if self.trace %}
                        trace_u256(mload({{ program.trace_id_mptr|hex() }}), q_eval)
                        mstore({{ program.trace_id_mptr|hex() }}, add(mload({{ program.trace_id_mptr|hex() }}), 1))
                        {%- endif %}
                        // Simple-selector identity: keep the same y-batch
                        // position as main identities, then advance only this
                        // selector bucket by its codegen-known gap.
                        //
                        // The global fully-evaluated accumulator is still
                        // multiplied by y so later main identities land at the
                        // same y powers as Rust's reverse fold.
                        mstore({{ program.eval_numer_mptr|hex() }}, mulmod(mload({{ program.eval_numer_mptr|hex() }}), y, r))
                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))
                        let q_sel_acc := mload(q_target_ptr)
                        if q_sel_gap {
                            // Selector buckets are sparse in the global
                            // identity stream. Precomputed y^gap advances only
                            // this selector's local accumulator.
                            q_sel_acc := mulmod(q_sel_acc, mload(add({{ program.selector_power_mptr|hex() }}, shl(5, q_sel_gap))), r)
                        }
                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))
                    }
                    {%- endif %}
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

                // Structured post-VM suffix. The current default uses this for
                // regular trash constraints: it is smaller than fully unrolled
                // Yul and cheaper than interpreting every trash operation.
                //
                // These generated blocks run after q_pc reaches q_end, but
                // they still participate in the same identity order and write
                // into the same numerator / selector accumulators.
                {%- for code_block in quotient_post_vm_computations %}
                {%- for line in code_block %}
                {{ line }}
                {%- endfor %}
                {%- endfor %}

                {%- if simple_selector_cols.len() > 0 %}
                // Finish selector buckets by applying the codegen-known tail
                // from each selector's last identity to the end of the global
                // y-batch.
                //
                // After this step, every selector bucket is aligned with the
                // final global y position and can be multiplied by its fixed
                // selector commitment in the linearized MSM.
                {%- for tail in program.selector_tail_updates %}
                {
                    let q_sel_ptr := add(SELECTOR_ACC_MPTR, {{ tail.selector_offset|hex() }})
                    mstore(q_sel_ptr, mulmod(mload(q_sel_ptr), mload(add({{ program.selector_power_mptr|hex() }}, {{ tail.power_offset|hex() }})), r))
                }
                {%- endfor %}
                {%- endif %}

                // Fully evaluated identities are the constant-polynomial side
                // of the linearization query. Rust subtracts that grouped
                // scalar into expected_eval, so Solidity stores -nu_y(x).
                let linearization_expected_eval := addmod(0, sub(r, mload({{ program.eval_numer_mptr|hex() }})), r)
                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)
                pop(y)
                {%- when None %}
                // Legacy/direct mode. This path emits the numerator
                // reconstruction directly instead of interpreting q_program.
                // It is used by older monolithic/experimental generation
                // modes and remains available as a fallback for models that do
                // not carry compact quotient bytecode.
                //
                // The generated statements in quotient_eval_numer_computations
                // are already ordered and folded by the Rust renderer. They
                // must leave `quotient_eval_numer` as nu_y(x), matching the
                // compact VM accumulator in program.eval_numer_mptr.
                let delta := {{ fr_delta }} // BLS12-381 Fr::DELTA
                let y := mload(Y_MPTR)
                {%- if self.trace %}
                // Direct mode increments q_trace_id inside generated fold
                // snippets, mirroring compact-mode trace_id_mptr.
                let q_trace_id := {{ quotient_identity_trace_base }}
                {%- endif %}

                // Direct/generated numerator body. This may contain unrolled
                // gate, permutation, lookup, trash, and selector-fold code.
                {%- for code_block in quotient_eval_numer_computations %}
                {%- for line in code_block %}
                {{ line }}
                {%- endfor %}
                {%- endfor %}

                // Silence Yul unused-variable warnings in renders where the
                // direct body did not need one of these common constants.
                pop(y)
                pop(delta)

                // Store the expected opening scalar for the linearized
                // commitment at x: the negated sum of fully-evaluated
                // identities. See
                // `compute_linearization_commitment` in
                // midfall/proofs/src/plonk/linearization/verifier.rs:
                //
                //   expected_eval -= eval     (for col_idx == None)
                //
                // The commitment side already includes the quotient-limb
                // factor (1 - x^n), so this scalar is -nu_y(x), not
                // h(x) = nu_y(x) / (x^n - 1).
                let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)
                mstore(QUOTIENT_EVAL_MPTR, linearization_expected_eval)
                {%- endmatch %}
            }
