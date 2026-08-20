// SPDX-License-Identifier: CC0-1.0
//! Generated Yul interpreter arms for the compact quotient VM.
//!
//! P4 (roadmap): the 31 opcode `case` arms, the token sub-switches, and the
//! opcode summary comment used to be hand-written Askama template text in
//! `QuotientNumeratorBlock.yul`, gated by 31 `{% if program.op_usage.* %}`
//! predicates and cross-checked against the Rust opcode table only by a
//! string grep. This module generates those arms from the same `Q_OP_*` /
//! `Q_MEM_*` constants the encoder, the checked decoder, and the operand
//! visitor use, so opcode numbers, operand widths, and usage gating agree by
//! construction. `vm/reference.rs` deliberately does NOT use this module: it
//! stays the independent N-version interpreter.
//!
//! ## Runtime guard rationale (moved from the template's macro comments)
//!
//! P12 (L-6, docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md) runtime operand
//! clamps: the VM program is trusted only through the VK codehash pin;
//! build-time `validate_quotient_mem_ptrs` proves exact window membership,
//! but the deployed interpreter re-checks every decoded memory-pointer
//! operand against the coarse `[operand_lo, operand_hi]` union of the
//! planned read windows so a substituted or corrupted VK payload cannot read
//! arbitrary verifier state. Single-comparison form: unsigned wrap makes
//! `sub(ptr, lo) > (hi - lo)` cover both bounds (~6 gas per operand). u8
//! constant-table indexes stay unguarded: their drift is bounded to 0x1FE0
//! bytes inside the VK-reserved region and covered by build-time
//! `validate_quotient_const_slots`. MF-3: the u16 forms do NOT share that
//! argument -- an out-of-range u16 index reaches 0x1FFFE0 bytes past the
//! table, well outside the pinned payload -- so those sites are clamped
//! against the rendered table length.
//!
//! MF-3 interpreter fail-closed guards: none are reachable on-chain with a
//! well-formed artifact; they are containment for a future GENERATOR bug.
//!   - top guard: FOLD_MAIN/FOLD_SELECTOR consume the cached top; with
//!     `q_has_top` clear the fold would silently re-fold a STALE `q_top` while
//!     both terminal checks still pass.
//!   - stack-empty guard: native callbacks must not inherit spilled operands
//!     from a preceding partial expression.
//!   - const guard: constant-table indexes are decoded from program bytes;
//!     unclamped u16 forms would read past the table.
//!   - spill-ceiling check at every push site: `q_sp` walks upward with no
//!     ceiling of its own.

use crate::lowering::{
    quotient_numerator::vm::{
        QUOTIENT_OPCODE_TABLE, QUOTIENT_VM_BYTE_U32_BYTES, QUOTIENT_VM_LIMBS,
        QUOTIENT_VM_PAIRWISE_COEFFS, Q_MEM_BETA, Q_MEM_GAMMA, Q_MEM_INSTANCE_EVAL, Q_MEM_L0,
        Q_MEM_L_BLIND, Q_MEM_L_LAST, Q_MEM_THETA, Q_MEM_TRASH_CHALLENGE, Q_MEM_X, Q_OP_ADD,
        Q_OP_ADD_CONST, Q_OP_ADD_CONST_U8, Q_OP_ADD_MEM_U16, Q_OP_ADD_MUL_CONST_U8_MEM_U16,
        Q_OP_ADD_MUL_MEM_MEM, Q_OP_ADD_MUL_MEM_MEM_CONST_U8, Q_OP_AFFINE_SUM, Q_OP_BILIN7_PAIRWISE,
        Q_OP_BILIN7_ROW, Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_LIN7, Q_OP_MODARITH7, Q_OP_MUL,
        Q_OP_MUL_CONST, Q_OP_MUL_CONST_U8, Q_OP_MUL_MEM_U16, Q_OP_NATIVE_IDENTITY,
        Q_OP_NATIVE_LOOKUP, Q_OP_NATIVE_PERMUTATION, Q_OP_NEG, Q_OP_POW5, Q_OP_PUSH_CONST,
        Q_OP_PUSH_CONST_U8, Q_OP_PUSH_MEM_LITERAL, Q_OP_PUSH_MEM_TOKEN, Q_OP_PUSH_MEM_TOKEN_OFFSET,
        Q_OP_PUSH_MEM_U16,
    },
    render::QuotientProgram,
};

/// Reserved opcode byte with no interpreter arm; the dispatch `default`
/// reverts on it. Pinned here (and by the snapshot test) now that the arm
/// text is generated.
pub(crate) const Q_OP_RESERVED: u8 = 0x1a;

/// Inputs for one render's generated interpreter arms.
pub(crate) struct YulArmInputs<'a> {
    /// The finalized VK-backed program model (usage sets + numeric holes).
    pub(crate) program: &'a QuotientProgram,
    /// Whether the render emits trace instrumentation in the fold arms.
    pub(crate) trace: bool,
    /// Generated native permutation callback body.
    pub(crate) native_permutation: &'a [String],
    /// Generated native LogUp callback body.
    pub(crate) native_lookup: &'a [String],
    /// Generated heavy-gate callback bodies, dispatched by index.
    pub(crate) native_identities: &'a [Vec<String>],
}

/// Even-width lowercase hex literal, mirroring the Askama `hex()` filter.
fn hex(value: usize) -> String {
    let body = format!("{value:x}");
    if body.len() % 2 == 1 {
        format!("0x0{body}")
    } else {
        format!("0x{body}")
    }
}

/// Symbolic-memory-token arm order and Yul symbols, shared by the two token
/// sub-switches. Table order == template order.
const TOKEN_ARMS: [(u8, &str); 9] = [
    (Q_MEM_L0, "L_0_MPTR"),
    (Q_MEM_L_LAST, "L_LAST_MPTR"),
    (Q_MEM_L_BLIND, "L_BLIND_MPTR"),
    (Q_MEM_BETA, "BETA_MPTR"),
    (Q_MEM_GAMMA, "GAMMA_MPTR"),
    (Q_MEM_X, "X_MPTR"),
    (Q_MEM_THETA, "THETA_MPTR"),
    (Q_MEM_TRASH_CHALLENGE, "TRASH_CHALLENGE_MPTR"),
    (Q_MEM_INSTANCE_EVAL, "INSTANCE_EVAL_MPTR"),
];

/// Opcode summary listing order (historical template order; differs from the
/// switch-arm order below).
const SUMMARY_ORDER: [u8; 31] = [
    Q_OP_PUSH_CONST,
    Q_OP_PUSH_MEM_LITERAL,
    Q_OP_PUSH_MEM_TOKEN,
    Q_OP_PUSH_MEM_TOKEN_OFFSET,
    Q_OP_PUSH_MEM_U16,
    Q_OP_ADD,
    Q_OP_MUL,
    Q_OP_NEG,
    Q_OP_PUSH_CONST_U8,
    Q_OP_FOLD_MAIN,
    Q_OP_FOLD_SELECTOR,
    Q_OP_ADD_CONST_U8,
    Q_OP_MUL_CONST_U8,
    Q_OP_ADD_CONST,
    Q_OP_MUL_CONST,
    Q_OP_ADD_MEM_U16,
    Q_OP_MUL_MEM_U16,
    Q_OP_ADD_MUL_MEM_MEM_CONST_U8,
    Q_OP_ADD_MUL_CONST_U8_MEM_U16,
    Q_OP_ADD_MUL_MEM_MEM,
    Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
    Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
    Q_OP_AFFINE_SUM,
    Q_OP_NATIVE_PERMUTATION,
    Q_OP_NATIVE_LOOKUP,
    Q_OP_NATIVE_IDENTITY,
    Q_OP_LIN7,
    Q_OP_BILIN7_ROW,
    Q_OP_BILIN7_PAIRWISE,
    Q_OP_MODARITH7,
    Q_OP_POW5,
];

use crate::lowering::quotient_numerator::vm::{
    Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16, Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
};

/// Stable snake-case opcode name from the canonical table.
fn op_name(op: u8) -> &'static str {
    QUOTIENT_OPCODE_TABLE
        .iter()
        .find(|spec| spec.opcode == op)
        .map(|spec| spec.name)
        .unwrap_or_else(|| panic!("opcode {op:#x} missing from QUOTIENT_OPCODE_TABLE"))
}

/// Opcode summary comment lines (`//   0xNN name` per used opcode), rendered
/// between the VM register block and the dispatch loop.
pub(crate) fn quotient_vm_op_summary(program: &QuotientProgram) -> Vec<String> {
    let mut lines = Vec::new();
    for op in SUMMARY_ORDER {
        if program.uses_op(op) {
            lines.push(format!(
                "                //   {} {}",
                hex(op as usize),
                op_name(op)
            ));
        }
    }
    lines
}

/// Line emitter with the guard/spill building blocks shared by every arm.
struct Arms<'a> {
    inputs: &'a YulArmInputs<'a>,
    lines: Vec<String>,
}

impl<'a> Arms<'a> {
    fn push(&mut self, line: &str) {
        self.lines.push(line.to_string());
    }

    fn pushf(&mut self, line: String) {
        self.lines.push(line);
    }

    fn program(&self) -> &QuotientProgram {
        self.inputs.program
    }

    /// P12 operand clamp (template macro `q_ptr_guard`; fixed 24-space
    /// indent regardless of surrounding nesting, matching the macro body).
    fn ptr_guard(&mut self, ptr: &str) {
        let lo = self.program().operand_lo;
        let hi = self.program().operand_hi;
        self.pushf(format!(
            "                        if gt(sub({ptr}, {}), {}) {{ q_program_fail() }}",
            hex(lo),
            hex(hi - lo)
        ));
    }

    /// 7-word limb-vector clamp (template macro `q_vec7_guard`; 28 spaces).
    fn vec7_guard(&mut self, ptr: &str) {
        let lo = self.program().operand_lo;
        let hi = self.program().operand_hi;
        self.pushf(format!(
            "                            if gt(sub({ptr}, {}), {}) {{ q_program_fail() }}",
            hex(lo),
            hex(hi - lo - 0xc0)
        ));
    }

    /// Balanced-underflow pop guard (template macro `q_pop_guard`).
    fn pop_guard(&mut self) {
        self.pushf(format!(
            "                        if eq(q_sp, {}) {{ q_program_fail() }}",
            hex(self.program().stack_mptr)
        ));
    }

    /// Stale-top fold guard (template macro `q_top_guard`).
    fn top_guard(&mut self) {
        self.push("                        if iszero(q_has_top) { q_program_fail() }");
    }

    /// Native-callback empty-stack guard (template macro
    /// `q_stack_empty_guard`).
    fn stack_empty_guard(&mut self) {
        self.pushf(format!(
            "                        if iszero(eq(q_sp, {})) {{ q_program_fail() }}",
            hex(self.program().stack_mptr)
        ));
    }

    /// MF-3 u16 constant-table clamp (template macro `q_const_guard`).
    fn const_guard(&mut self, idx: &str) {
        self.pushf(format!(
            "                        if iszero(lt({idx}, {})) {{ q_program_fail() }}",
            self.program().num_consts
        ));
    }

    /// Cached-top spill with the MF-3 stack ceiling clamp.
    fn spill_top(&mut self) {
        self.push("                        if q_has_top {");
        self.pushf(format!(
            "                            if iszero(lt(q_sp, {})) {{ q_program_fail() }}",
            hex(self.program().stack_hi)
        ));
        self.push("                            mstore(q_sp, q_top)");
        self.push("                            q_sp := add(q_sp, 0x20)");
        self.push("                        }");
    }

    /// Fold-arm trace instrumentation, gated on the render's trace flag.
    fn fold_trace(&mut self) {
        if self.inputs.trace {
            let trace_id = hex(self.program().trace_id_mptr);
            self.pushf(format!(
                "                        trace_u256(mload({trace_id}), q_eval)"
            ));
            self.pushf(format!(
                "                        mstore({trace_id}, add(mload({trace_id}), 1))"
            ));
        }
    }

    /// One token sub-switch arm set. `body` maps a Yul symbol to the case
    /// body text after `{ q_ptr := ` and before ` }`.
    fn token_switch(&mut self, offset_form: bool) {
        for (token, symbol) in TOKEN_ARMS {
            if !self.inputs.program.uses_token(token) {
                continue;
            }
            let target = if offset_form {
                format!("add({symbol}, q_off)")
            } else {
                symbol.to_string()
            };
            self.pushf(format!(
                "                        case {} {{ q_ptr := {target} }}",
                hex(token as usize)
            ));
        }
    }
}

/// Generate the interpreter `case` arms for one render, in the historical
/// template order, gated by the program's used-opcode set exactly as the
/// deleted `{% if program.op_usage.* %}` predicates were.
pub(crate) fn quotient_vm_switch_arms(inputs: &YulArmInputs<'_>) -> Vec<String> {
    let program = inputs.program;
    assert!(
        !program.uses_op(Q_OP_RESERVED),
        "reserved opcode 0x1a must never appear in a generated program"
    );
    let mut arms = Arms {
        inputs,
        lines: Vec::new(),
    };

    if program.uses_op(Q_OP_PUSH_CONST) {
        push_const_arm(&mut arms);
    }
    if program.uses_op(Q_OP_PUSH_MEM_LITERAL) {
        push_mem_literal_arm(&mut arms);
    }
    if program.uses_op(Q_OP_PUSH_MEM_TOKEN) {
        push_mem_token_arm(&mut arms);
    }
    if program.uses_op(Q_OP_PUSH_MEM_TOKEN_OFFSET) {
        push_mem_token_offset_arm(&mut arms);
    }
    if program.uses_op(Q_OP_PUSH_MEM_U16) {
        push_mem_u16_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD) {
        add_arm(&mut arms);
    }
    if program.uses_op(Q_OP_MUL) {
        mul_arm(&mut arms);
    }
    if program.uses_op(Q_OP_NEG) {
        neg_arm(&mut arms);
    }
    if program.uses_op(Q_OP_POW5) {
        pow5_arm(&mut arms);
    }
    if program.uses_op(Q_OP_PUSH_CONST_U8) {
        push_const_u8_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_CONST_U8) {
        add_const_u8_arm(&mut arms);
    }
    if program.uses_op(Q_OP_MUL_CONST_U8) {
        mul_const_u8_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_CONST) {
        add_const_arm(&mut arms);
    }
    if program.uses_op(Q_OP_MUL_CONST) {
        mul_const_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_MEM_U16) {
        add_mem_u16_arm(&mut arms);
    }
    if program.uses_op(Q_OP_MUL_MEM_U16) {
        mul_mem_u16_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_MUL_MEM_MEM_CONST_U8) {
        add_mul_mem_mem_const_u8_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_MUL_CONST_U8_MEM_U16) {
        add_mul_const_u8_mem_u16_arm(&mut arms);
    }
    if program.uses_op(Q_OP_ADD_MUL_MEM_MEM) {
        add_mul_mem_mem_arm(&mut arms);
    }
    if program.uses_op(Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8) {
        run_add_mul_mem_mem_const_u8_arm(&mut arms);
    }
    if program.uses_op(Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16) {
        run_add_mul_const_u8_mem_u16_arm(&mut arms);
    }
    if program.uses_op(Q_OP_AFFINE_SUM) {
        affine_sum_arm(&mut arms);
    }
    if program.uses_op(Q_OP_LIN7)
        || program.uses_op(Q_OP_BILIN7_ROW)
        || program.uses_op(Q_OP_BILIN7_PAIRWISE)
        || program.uses_op(Q_OP_MODARITH7)
    {
        limb_section_comment(&mut arms);
    }
    if program.uses_op(Q_OP_LIN7) {
        lin7_arm(&mut arms);
    }
    if program.uses_op(Q_OP_BILIN7_ROW) {
        bilin7_row_arm(&mut arms);
    }
    if program.uses_op(Q_OP_BILIN7_PAIRWISE) {
        bilin7_pairwise_arm(&mut arms);
    }
    if program.uses_op(Q_OP_MODARITH7) {
        modarith7_arm(&mut arms);
    }
    if program.uses_op(Q_OP_NATIVE_PERMUTATION) && !inputs.native_permutation.is_empty() {
        native_permutation_arm(&mut arms);
    }
    if program.uses_op(Q_OP_NATIVE_LOOKUP) && !inputs.native_lookup.is_empty() {
        native_lookup_arm(&mut arms);
    }
    if program.uses_op(Q_OP_NATIVE_IDENTITY) && !inputs.native_identities.is_empty() {
        native_identity_arm(&mut arms);
    }
    if program.uses_op(Q_OP_FOLD_MAIN) {
        fold_main_arm(&mut arms);
    }
    if program.uses_op(Q_OP_FOLD_SELECTOR) {
        fold_selector_arm(&mut arms);
    }

    arms.lines
}

fn push_const_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x01 PUSH_CONST (bytes): next two bytes are a constant-table slot.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_CONST as usize)
    ));
    arms.push("                        // Operand layout: u16 const_idx. Constants are 32-byte");
    arms.push("                        // Fr words, so shl(5, const_idx) converts an index to");
    arms.push("                        // a byte offset.");
    arms.push("                        let qconst := shr(240, mload(q_pc))");
    arms.const_guard("qconst");
    arms.push("                        // Push semantics: spill the old cached top, if any,");
    arms.push("                        // then install the loaded constant as the new q_top.");
    arms.spill_top();
    arms.push("                        q_top := mload(add(q_const_mptr, shl(5, qconst)))");
    arms.push("                        q_has_top := 1");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                    }");
}

fn push_mem_literal_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x02 PUSH_MEM_LITERAL (bytes): next four bytes are a memory pointer.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_MEM_LITERAL as usize)
    ));
    arms.push("                        // Operand layout: u32 absolute memory pointer. This is");
    arms.push("                        // emitted only for planned addresses that do not fit in");
    arms.push("                        // the smaller u16 form or token map.");
    arms.push("                        let q_ptr := shr(224, mload(q_pc))");
    arms.pushf(format!(
        "                        q_pc := add(q_pc, {})",
        hex(QUOTIENT_VM_BYTE_U32_BYTES)
    ));
    arms.ptr_guard("q_ptr");
    arms.push("                        // Load one canonical Fr word from generated memory and");
    arms.push("                        // push it through the cached-top stack discipline.");
    arms.spill_top();
    arms.push("                        q_top := mload(q_ptr)");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn push_mem_token_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x03 PUSH_MEM_TOKEN (bytes): next byte selects a symbolic memory pointer.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_MEM_TOKEN as usize)
    ));
    arms.push("                        // Operand layout: u8 token. Tokens cover the hot");
    arms.push("                        // global verifier scalars used in many identities.");
    arms.push("                        let q_token := byte(0, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 1)");
    arms.push("                        let q_ptr := 0");
    arms.push("                        // Token cases decode generated symbolic memory addresses.");
    arms.push("                        switch q_token");
    arms.token_switch(false);
    arms.push("                        // A token not advertised by the VM usage manifest is");
    arms.push("                        // impossible for valid generated bytecode.");
    arms.push("                        default { q_program_fail() }");
    arms.spill_top();
    arms.push("                        q_top := mload(q_ptr)");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn push_mem_token_offset_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x04 PUSH_MEM_TOKEN_OFFSET (bytes): token byte plus u32 byte offset.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_MEM_TOKEN_OFFSET as usize)
    ));
    arms.push("                        // Operand layout: u8 token, u32 byte offset. This is");
    arms.push("                        // used when a symbolic base such as REVERSED_EVALS_MPTR");
    arms.push("                        // is known, but the expression needs a specific word");
    arms.push("                        // inside that generated region.");
    arms.push("                        let q_word := mload(q_pc)");
    arms.push("                        let q_token := byte(0, q_word)");
    arms.push("                        let q_off := and(shr(216, q_word), 0xffffffff)");
    arms.push("                        q_pc := add(q_pc, 5)");
    arms.push("                        let q_ptr := 0");
    arms.push(
        "                        // Token-offset cases reuse the same token table, then add q_off.",
    );
    arms.push("                        switch q_token");
    arms.token_switch(true);
    arms.push("                        default { q_program_fail() }");
    arms.ptr_guard("q_ptr");
    arms.spill_top();
    arms.push("                        q_top := mload(q_ptr)");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn push_mem_u16_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x05 PUSH_MEM_U16 (bytes): next two bytes are a short memory pointer.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_MEM_U16 as usize)
    ));
    arms.push("                        // Operand layout: u16 absolute memory pointer. The");
    arms.push("                        // memory planner keeps the hot quotient frame below");
    arms.push("                        // 64 KiB when this compact form is emitted.");
    arms.push("                        let q_ptr := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_ptr");
    arms.spill_top();
    arms.push("                        q_top := mload(q_ptr)");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn add_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x06 ADD: pop one spilled stack word and add it to q_top.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD as usize)
    ));
    arms.push("                        // The safety validator guarantees a spilled operand");
    arms.push("                        // exists before ADD. q_top is the right operand.");
    arms.pop_guard();
    arms.push("                        q_sp := sub(q_sp, 0x20)");
    arms.push("                        q_top := addmod(mload(q_sp), q_top, r)");
    arms.push("                    }");
}

fn mul_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x07 MUL: pop one spilled stack word and multiply it by q_top.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_MUL as usize)
    ));
    arms.push("                        // Same stack contract as ADD, with multiplication");
    arms.push("                        // reduced directly modulo Fr.");
    arms.pop_guard();
    arms.push("                        q_sp := sub(q_sp, 0x20)");
    arms.push("                        q_top := mulmod(mload(q_sp), q_top, r)");
    arms.push("                    }");
}

fn neg_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x08 NEG: replace q_top with its Fr negation.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_NEG as usize)
    ));
    arms.push("                        // addmod(0, r - x, r) maps zero back to zero and every");
    arms.push("                        // nonzero scalar to its canonical additive inverse.");
    arms.push("                        q_top := addmod(0, sub(r, q_top), r)");
    arms.push("                    }");
}

fn pow5_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x20 POW5: replace q_top with q_top^5.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_POW5 as usize)
    ));
    arms.push("                        // Poseidon S-box shortcut: x^5 = x * (x^2)^2.");
    arms.push("                        let q2 := mulmod(q_top, q_top, r)");
    arms.push("                        q_top := mulmod(q_top, mulmod(q2, q2, r), r)");
    arms.push("                    }");
}

fn push_const_u8_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x09 PUSH_CONST_U8 (bytes): next byte is a constant-table slot.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_PUSH_CONST_U8 as usize)
    ));
    arms.push("                        // One-byte variant for the common case where the");
    arms.push("                        // constant table has fewer than 256 referenced slots.");
    arms.push("                        let qconst := byte(0, mload(q_pc))");
    arms.spill_top();
    arms.push("                        q_top := mload(add(q_const_mptr, shl(5, qconst)))");
    arms.push("                        q_has_top := 1");
    arms.push("                        q_pc := add(q_pc, 1)");
    arms.push("                    }");
}

fn add_const_u8_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x0c ADD_CONST_U8: add a small constant-table slot into q_top.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_CONST_U8 as usize)
    ));
    arms.push("                        // Accumulator opcode: mutates q_top in place instead");
    arms.push("                        // of pushing a new stack value.");
    arms.push("                        let qconst := byte(0, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 1)");
    arms.push("                        q_top := addmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)");
    arms.push("                    }");
}

fn mul_const_u8_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x0d MUL_CONST_U8: multiply q_top by a small constant-table slot.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_MUL_CONST_U8 as usize)
    ));
    arms.push("                        // One-byte constant-index multiply, used by short");
    arms.push("                        // affine chains after an initial PUSH.");
    arms.push("                        let qconst := byte(0, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 1)");
    arms.push("                        q_top := mulmod(q_top, mload(add(q_const_mptr, shl(5, qconst))), r)");
    arms.push("                    }");
}

fn add_const_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x0e ADD_CONST: add a wider constant-table slot into q_top.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_CONST as usize)
    ));
    arms.push("                        // Two-byte constant-index form for larger generated");
    arms.push("                        // constant tables.");
    arms.push("                        let qconst := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.const_guard("qconst");
    arms.push("                        let q_const_ptr := add(q_const_mptr, shl(5, qconst))");
    arms.ptr_guard("q_const_ptr");
    arms.push("                        q_top := addmod(q_top, mload(q_const_ptr), r)");
    arms.push("                    }");
}

fn mul_const_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x0f MUL_CONST: multiply q_top by a wider constant-table slot.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_MUL_CONST as usize)
    ));
    arms.push("                        // Two-byte constant-index multiply.");
    arms.push("                        let qconst := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.const_guard("qconst");
    arms.push("                        let q_const_ptr := add(q_const_mptr, shl(5, qconst))");
    arms.ptr_guard("q_const_ptr");
    arms.push("                        q_top := mulmod(q_top, mload(q_const_ptr), r)");
    arms.push("                    }");
}

fn add_mem_u16_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x10 ADD_MEM_U16: add a short memory load into q_top.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_MEM_U16 as usize)
    ));
    arms.push("                        // Operand layout: u16 pointer. The pointed word is an");
    arms.push("                        // already range-checked Fr scalar in verifier memory.");
    arms.push("                        let q_ptr := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_ptr");
    arms.push("                        q_top := addmod(q_top, mload(q_ptr), r)");
    arms.push("                    }");
}

fn mul_mem_u16_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x11 MUL_MEM_U16: multiply q_top by a short memory load.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_MUL_MEM_U16 as usize)
    ));
    arms.push("                        // In-place multiply by a planned memory word.");
    arms.push("                        let q_ptr := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_ptr");
    arms.push("                        q_top := mulmod(q_top, mload(q_ptr), r)");
    arms.push("                    }");
}

/// The shared fused-product tail `q_top += mload(lhs) * mload(rhs) * const`.
fn fused_product_add(arms: &mut Arms<'_>, indent: &str) {
    arms.pushf(format!("{indent}q_top := addmod("));
    arms.pushf(format!("{indent}    q_top,"));
    arms.pushf(format!("{indent}    mulmod("));
    arms.pushf(format!(
        "{indent}        mulmod(mload(q_lhs), mload(q_rhs), r),"
    ));
    arms.pushf(format!(
        "{indent}        mload(add(q_const_mptr, shl(5, qconst))),"
    ));
    arms.pushf(format!("{indent}        r"));
    arms.pushf(format!("{indent}    ),"));
    arms.pushf(format!("{indent}    r"));
    arms.pushf(format!("{indent})"));
}

fn add_mul_mem_mem_const_u8_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x12 ADD_MUL_MEM_MEM_CONST_U8: fused q_top += lhs * rhs * const.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_MUL_MEM_MEM_CONST_U8 as usize)
    ));
    arms.push("                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr,");
    arms.push("                        // u8 const_idx. This fuses a frequent affine-product");
    arms.push("                        // term without spending opcodes on PUSH/MUL/MUL/ADD.");
    arms.push("                        let q_word := mload(q_pc)");
    arms.push("                        let q_lhs := shr(240, q_word)");
    arms.push("                        let q_rhs := and(shr(224, q_word), 0xffff)");
    arms.push("                        let qconst := byte(4, q_word)");
    arms.push("                        q_pc := add(q_pc, 5)");
    arms.ptr_guard("q_lhs");
    arms.ptr_guard("q_rhs");
    fused_product_add(arms, "                        ");
    arms.push("                    }");
}

fn add_mul_const_u8_mem_u16_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x13 ADD_MUL_CONST_U8_MEM_U16: fused q_top += mem * const.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_MUL_CONST_U8_MEM_U16 as usize)
    ));
    arms.push("                        // Operand layout: u16 ptr, u8 const_idx.");
    arms.push("                        let q_word := mload(q_pc)");
    arms.push("                        let q_ptr := shr(240, q_word)");
    arms.push("                        let qconst := byte(2, q_word)");
    arms.push("                        q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                        q_top := addmod(");
    arms.push("                            q_top,");
    arms.push("                            mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),");
    arms.push("                            r");
    arms.push("                        )");
    arms.push("                    }");
}

fn add_mul_mem_mem_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x14 ADD_MUL_MEM_MEM: fused q_top += lhs * rhs.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_ADD_MUL_MEM_MEM as usize)
    ));
    arms.push("                        // Operand layout: u16 lhs_ptr, u16 rhs_ptr. This is");
    arms.push("                        // the unit-coefficient sibling of opcode 0x12.");
    arms.push("                        let q_word := mload(q_pc)");
    arms.push("                        let q_lhs := shr(240, q_word)");
    arms.push("                        let q_rhs := and(shr(224, q_word), 0xffff)");
    arms.pushf(format!(
        "                        q_pc := add(q_pc, {})",
        hex(QUOTIENT_VM_BYTE_U32_BYTES)
    ));
    arms.ptr_guard("q_lhs");
    arms.ptr_guard("q_rhs");
    arms.push(
        "                        q_top := addmod(q_top, mulmod(mload(q_lhs), mload(q_rhs), r), r)",
    );
    arms.push("                    }");
}

fn run_add_mul_mem_mem_const_u8_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x15 RUN_ADD_MUL_MEM_MEM_CONST_U8: byte-only loop over fused 0x12 payloads.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 as usize)
    ));
    arms.push("                        // Operand layout: u16 count followed by `count`");
    arms.push("                        // packed 0x12-style payloads. The run header saves a");
    arms.push("                        // dispatch per term in long affine product chains.");
    arms.push("                        let q_count := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                        let q_run_end := add(q_pc, mul(q_count, 5))");
    arms.push("                        for { } lt(q_pc, q_run_end) { } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let q_lhs := shr(240, q_word)");
    arms.push("                            let q_rhs := and(shr(224, q_word), 0xffff)");
    arms.push("                            let qconst := byte(4, q_word)");
    arms.push("                            q_pc := add(q_pc, 5)");
    arms.ptr_guard("q_lhs");
    arms.ptr_guard("q_rhs");
    fused_product_add(arms, "                            ");
    arms.push("                        }");
    arms.push("                    }");
}

fn run_add_mul_const_u8_mem_u16_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x16 RUN_ADD_MUL_CONST_U8_MEM_U16: byte-only loop over fused 0x13 payloads.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 as usize)
    ));
    arms.push("                        // Operand layout: u16 count followed by `count`");
    arms.push("                        // packed 0x13-style payloads.");
    arms.push("                        let q_count := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                        let q_run_end := add(q_pc, mul(q_count, 3))");
    arms.push("                        for { } lt(q_pc, q_run_end) { } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let q_ptr := shr(240, q_word)");
    arms.push("                            let qconst := byte(2, q_word)");
    arms.push("                            q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                            q_top := addmod(");
    arms.push("                                q_top,");
    arms.push("                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),");
    arms.push("                                r");
    arms.push("                            )");
    arms.push("                        }");
    arms.push("                    }");
}

fn affine_sum_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x22 AFFINE_SUM: mixed byte-only affine linear/product loop.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_AFFINE_SUM as usize)
    ));
    arms.push("                        // Operand layout:");
    arms.push("                        //   u16 lin_count, u16 product_count,");
    arms.push("                        //   lin_count * {u16 ptr, u8 const_idx},");
    arms.push("                        //   product_count * {u16 lhs, u16 rhs, u8 const_idx}.");
    arms.push("                        // The opcode appends all terms into the existing");
    arms.push("                        // q_top accumulator.");
    arms.push("                        let q_lin_count := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                        let q_product_count := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                        // Linear part: q_top += c_i * mload(ptr_i).");
    arms.push("                        let q_lin_end := add(q_pc, mul(q_lin_count, 3))");
    arms.push("                        for { } lt(q_pc, q_lin_end) { } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let q_ptr := shr(240, q_word)");
    arms.push("                            let qconst := byte(2, q_word)");
    arms.push("                            q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                            q_top := addmod(");
    arms.push("                                q_top,");
    arms.push("                                mulmod(mload(q_ptr), mload(add(q_const_mptr, shl(5, qconst))), r),");
    arms.push("                                r");
    arms.push("                            )");
    arms.push("                        }");
    arms.push(
        "                        // Product part: q_top += c_i * mload(lhs_i) * mload(rhs_i).",
    );
    arms.push("                        let q_product_end := add(q_pc, mul(q_product_count, 5))");
    arms.push("                        for { } lt(q_pc, q_product_end) { } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let q_lhs := shr(240, q_word)");
    arms.push("                            let q_rhs := and(shr(224, q_word), 0xffff)");
    arms.push("                            let qconst := byte(4, q_word)");
    arms.push("                            q_pc := add(q_pc, 5)");
    arms.ptr_guard("q_lhs");
    arms.ptr_guard("q_rhs");
    fused_product_add(arms, "                            ");
    arms.push("                        }");
    arms.push("                    }");
}

fn limb_section_comment(arms: &mut Arms<'_>) {
    arms.push("                    // Limb-aware opcodes are opt-in compact forms for");
    arms.push("                    // structurally recognized non-SHA foreign-field shapes.");
    arms.push("                    // Coefficients are indexes into q_const_mptr, which is");
    arms.push("                    // generated from VK/program data, never from proof");
    arms.push("                    // calldata.");
    arms.push("                    //");
    arms.push("                    // Rust source shape:");
    arms.push("                    //   proofs/src/plonk/mod.rs::partially_evaluate_identities");
    arms.push(
        "                    //   circuits/src/field/foreign/util.rs::{sum_exprs,pair_wise_prod}",
    );
    arms.push("                    //   circuits/src/field/foreign/params.rs::{base_powers,double_base_powers}");
    arms.push("                    //");
    arms.push("                    // \"Foreign field\" means the circuit represents elements");
    arms.push("                    // modulo another modulus m as 7 limbs in base");
    arms.push("                    // 2^LOG2_BASE. The verifier does not switch fields; it");
    arms.push("                    // evaluates the lowered identity over BLS12-381 Fr, using");
    arms.push("                    // Fr coefficients equal to base^i mod m or base^(i+j) mod m.");
}

fn lin7_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x1c LIN7: byte-only 7-term foreign-field linear form.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_LIN7 as usize)
    ));
    arms.push("                        // LIN7: sum_i coeff[i] * value[i] over Fr.");
    arms.push("                        // Typical Rust origin: foreign/gates/norm.rs");
    arms.push("                        // normalization and foreign/gates/mul.rs base-power");
    arms.push("                        // sums for x/y/z limbs.");
    arms.push("                        //");
    arms.push("                        // Operand layout: seven repeated {u8 const_idx,");
    arms.push("                        // u16 ptr} pairs. The result is pushed as a fresh");
    arms.push("                        // stack value.");
    arms.spill_top();
    arms.push("                        let q_acc := 0");
    arms.push("                        // Accumulate exactly seven limbs, matching the");
    arms.push("                        // generated foreign-field limb width.");
    arms.pushf(format!(
        "                        for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let qconst := byte(0, q_word)");
    arms.push("                            let q_ptr := and(shr(232, q_word), 0xffff)");
    arms.push("                            q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                            q_acc := addmod(");
    arms.push("                                q_acc,");
    arms.push("                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),");
    arms.push("                                r");
    arms.push("                            )");
    arms.push("                        }");
    arms.push("                        q_top := q_acc");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn bilin7_row_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x1d BILIN7_ROW: byte-only lhs times a 7-term weighted row.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_BILIN7_ROW as usize)
    ));
    arms.push("                        // BILIN7_ROW: lhs * sum_i coeff[i] * rhs[i].");
    arms.push("                        // Typical Rust origin: one row/slice of");
    arms.push("                        // pair_wise_prod in foreign multiplication and EC");
    arms.push("                        // on_curve/slope/tangent/lambda_squared gates.");
    arms.push("                        //");
    arms.push("                        // Operand layout: u16 lhs_ptr, then seven repeated");
    arms.push("                        // {u8 const_idx, u16 rhs_ptr} pairs. The lhs value is");
    arms.push("                        // loaded once and reused for all seven products.");
    arms.push("                        let q_lhs := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_lhs");
    arms.push("                        let q_lhs_value := mload(q_lhs)");
    arms.spill_top();
    arms.push("                        let q_acc := 0");
    arms.pushf(format!(
        "                        for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let qconst := byte(0, q_word)");
    arms.push("                            let q_rhs := and(shr(232, q_word), 0xffff)");
    arms.push("                            q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_rhs");
    arms.push("                            q_acc := addmod(");
    arms.push("                                q_acc,");
    arms.push("                                mulmod(");
    arms.push("                                    mulmod(q_lhs_value, mload(q_rhs), r),");
    arms.push("                                    mload(add(q_const_mptr, shl(5, qconst))),");
    arms.push("                                    r");
    arms.push("                                ),");
    arms.push("                                r");
    arms.push("                            )");
    arms.push("                        }");
    arms.push("                        q_top := q_acc");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn bilin7_pairwise_arm(arms: &mut Arms<'_>) {
    arms.push(
        "                    // VM 0x1e BILIN7_PAIRWISE: byte-only 7-by-7 weighted convolution.",
    );
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_BILIN7_PAIRWISE as usize)
    ));
    arms.push("                        // BILIN7_PAIRWISE:");
    arms.push("                        //   sum_{i=0..6,j=0..6} coeff[i+j] * lhs[i] * rhs[j].");
    arms.push("                        // Bases point to contiguous 7-word limb vectors.");
    arms.push("                        // Typical Rust origin:");
    arms.push("                        //   sum_exprs(double_base_powers,");
    arms.push("                        //             pair_wise_prod(lhs, rhs))");
    arms.push("                        // where double_base_powers[k] = base^k mod m.");
    arms.push("                        //");
    arms.push("                        // Operand layout: u16 lhs_base, u16 rhs_base, then 13");
    arms.push("                        // one-byte coefficient indexes. Coefficients are");
    arms.push("                        // addressed by i+j, so 7-by-7 products need 13 slots.");
    arms.push("                        let q_word := mload(q_pc)");
    arms.push("                        let q_lhs_base := shr(240, q_word)");
    arms.push("                        let q_rhs_base := and(shr(224, q_word), 0xffff)");
    arms.pushf(format!(
        "                        q_pc := add(q_pc, {})",
        hex(QUOTIENT_VM_BYTE_U32_BYTES)
    ));
    arms.vec7_guard("q_lhs_base");
    arms.vec7_guard("q_rhs_base");
    arms.push("                        let q_coeff_pc := q_pc");
    arms.pushf(format!(
        "                        q_pc := add(q_pc, {QUOTIENT_VM_PAIRWISE_COEFFS})"
    ));
    arms.spill_top();
    arms.push("                        let q_acc := 0");
    arms.push("                        // Nested limb convolution over two contiguous");
    arms.push("                        // 7-word vectors.");
    arms.pushf(format!(
        "                        for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push("                            let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))");
    arms.pushf(format!(
        "                            for {{ let q_j := 0 }} lt(q_j, {QUOTIENT_VM_LIMBS}) {{ q_j := add(q_j, 1) }} {{"
    ));
    arms.push("                                let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))");
    arms.push("                                q_acc := addmod(");
    arms.push("                                    q_acc,");
    arms.push("                                    mulmod(");
    arms.push("                                        mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),");
    arms.push("                                        mload(add(q_const_mptr, shl(5, qconst))),");
    arms.push("                                        r");
    arms.push("                                    ),");
    arms.push("                                    r");
    arms.push("                                )");
    arms.push("                            }");
    arms.push("                        }");
    arms.push("                        q_top := q_acc");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

fn modarith7_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x21 MODARITH7: byte-only fused affine 7-limb foreign-field/ECC identity.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_MODARITH7 as usize)
    ));
    arms.push("                        // MODARITH7:");
    arms.push("                        //   maybe_cond * (");
    arms.push("                        //       c");
    arms.push("                        //     + sum LIN7 blocks");
    arms.push("                        //     + sum BILIN7_ROW blocks");
    arms.push("                        //     + sum BILIN7_PAIRWISE blocks");
    arms.push("                        //     + sum coeff[k] * mload(ptr[k])");
    arms.push("                        //     + sum coeff[k] * mload(lhs[k]) * mload(rhs[k])");
    arms.push("                        //   )");
    arms.push("                        // It is a dispatch/operand-load optimization only;");
    arms.push("                        // all coefficients still come from the generated");
    arms.push("                        // quotient constant table.");
    arms.push("                        //");
    arms.push("                        // Flags:");
    arms.push("                        //   bit 0: multiply the final affine sum by a memory");
    arms.push("                        //          condition word.");
    arms.push("                        //   bit 1: seed q_acc from a constant-table word");
    arms.push("                        //          before reading the counted term blocks.");
    arms.push("                        let q_flags := byte(0, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 1)");
    arms.push("                        let q_cond_ptr := 0");
    arms.push("                        if and(q_flags, 0x01) {");
    arms.push("                            // Optional condition pointer. When present, the");
    arms.push("                            // whole identity is gated by mload(q_cond_ptr).");
    arms.push("                            q_cond_ptr := shr(240, mload(q_pc))");
    arms.push("                            q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_cond_ptr");
    arms.push("                        }");
    arms.push("");
    arms.push("                        let q_acc := 0");
    arms.push("                        if and(q_flags, 0x02) {");
    arms.push("                            // Optional constant seed for affine identities");
    arms.push("                            // with a standalone constant term.");
    arms.push("                            let qconst := byte(0, mload(q_pc))");
    arms.push("                            q_pc := add(q_pc, 1)");
    arms.push("                            q_acc := mload(add(q_const_mptr, shl(5, qconst)))");
    arms.push("                        }");
    arms.push("");
    arms.push("                        // Five one-byte counters describe the blocks that");
    arms.push("                        // follow. Each block has a fixed-width internal layout,");
    arms.push("                        // so q_pc can advance without per-term tags.");
    arms.push("                        let q_counts_word := mload(q_pc)");
    arms.push("                        let q_lin_count := byte(0, q_counts_word)");
    arms.push("                        let q_row_count := byte(1, q_counts_word)");
    arms.push("                        let q_pairwise_count := byte(2, q_counts_word)");
    arms.push("                        let q_mem_count := byte(3, q_counts_word)");
    arms.push("                        let q_product_count := byte(4, q_counts_word)");
    arms.push("                        q_pc := add(q_pc, 5)");
    arms.push("");
    arms.spill_top();
    arms.push("");
    arms.push("                        // LIN7 blocks: q_acc += sum_i c_i * limb_i.");
    arms.push("                        for { let q_lin_block := 0 } lt(q_lin_block, q_lin_count) { q_lin_block := add(q_lin_block, 1) } {");
    arms.pushf(format!(
        "                            for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push("                                let q_word := mload(q_pc)");
    arms.push("                                let qconst := byte(0, q_word)");
    arms.push("                                let q_ptr := and(shr(232, q_word), 0xffff)");
    arms.push("                                q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                                q_acc := addmod(");
    arms.push("                                    q_acc,");
    arms.push("                                    mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),");
    arms.push("                                    r");
    arms.push("                                )");
    arms.push("                            }");
    arms.push("                        }");
    arms.push("");
    arms.push("                        // BILIN7_ROW blocks: q_acc += lhs * sum_i c_i * rhs_i.");
    arms.push("                        for { let q_row_block := 0 } lt(q_row_block, q_row_count) { q_row_block := add(q_row_block, 1) } {");
    arms.push("                            let q_lhs := shr(240, mload(q_pc))");
    arms.push("                            q_pc := add(q_pc, 2)");
    arms.ptr_guard("q_lhs");
    arms.push("                            let q_lhs_value := mload(q_lhs)");
    arms.pushf(format!(
        "                            for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push("                                let q_word := mload(q_pc)");
    arms.push("                                let qconst := byte(0, q_word)");
    arms.push("                                let q_rhs := and(shr(232, q_word), 0xffff)");
    arms.push("                                q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_rhs");
    arms.push("                                q_acc := addmod(");
    arms.push("                                    q_acc,");
    arms.push("                                    mulmod(");
    arms.push("                                        mulmod(q_lhs_value, mload(q_rhs), r),");
    arms.push("                                        mload(add(q_const_mptr, shl(5, qconst))),");
    arms.push("                                        r");
    arms.push("                                    ),");
    arms.push("                                    r");
    arms.push("                                )");
    arms.push("                            }");
    arms.push("                        }");
    arms.push("");
    arms.push("                        // BILIN7_PAIRWISE blocks: q_acc += weighted 7-by-7");
    arms.push("                        // product convolution.");
    arms.push("                        for { let q_pair_block := 0 } lt(q_pair_block, q_pairwise_count) { q_pair_block := add(q_pair_block, 1) } {");
    arms.push("                            let q_pair_word := mload(q_pc)");
    arms.push("                            let q_lhs_base := shr(240, q_pair_word)");
    arms.push("                            let q_rhs_base := and(shr(224, q_pair_word), 0xffff)");
    arms.pushf(format!(
        "                            q_pc := add(q_pc, {})",
        hex(QUOTIENT_VM_BYTE_U32_BYTES)
    ));
    arms.vec7_guard("q_lhs_base");
    arms.vec7_guard("q_rhs_base");
    arms.push("                            let q_coeff_pc := q_pc");
    arms.pushf(format!(
        "                            q_pc := add(q_pc, {QUOTIENT_VM_PAIRWISE_COEFFS})"
    ));
    arms.pushf(format!(
        "                            for {{ let q_i := 0 }} lt(q_i, {QUOTIENT_VM_LIMBS}) {{ q_i := add(q_i, 1) }} {{"
    ));
    arms.push(
        "                                let q_lhs_value := mload(add(q_lhs_base, shl(5, q_i)))",
    );
    arms.pushf(format!(
        "                                for {{ let q_j := 0 }} lt(q_j, {QUOTIENT_VM_LIMBS}) {{ q_j := add(q_j, 1) }} {{"
    ));
    arms.push("                                    let qconst := byte(0, mload(add(q_coeff_pc, add(q_i, q_j))))");
    arms.push("                                    q_acc := addmod(");
    arms.push("                                        q_acc,");
    arms.push("                                        mulmod(");
    arms.push("                                            mulmod(q_lhs_value, mload(add(q_rhs_base, shl(5, q_j))), r),");
    arms.push(
        "                                            mload(add(q_const_mptr, shl(5, qconst))),",
    );
    arms.push("                                            r");
    arms.push("                                        ),");
    arms.push("                                        r");
    arms.push("                                    )");
    arms.push("                                }");
    arms.push("                            }");
    arms.push("                        }");
    arms.push("");
    arms.push("                        // Extra linear memory terms outside the 7-limb shapes.");
    arms.push("                        for { let q_mem_block := 0 } lt(q_mem_block, q_mem_count) { q_mem_block := add(q_mem_block, 1) } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let qconst := byte(0, q_word)");
    arms.push("                            let q_ptr := and(shr(232, q_word), 0xffff)");
    arms.push("                            q_pc := add(q_pc, 3)");
    arms.ptr_guard("q_ptr");
    arms.push("                            q_acc := addmod(");
    arms.push("                                q_acc,");
    arms.push("                                mulmod(mload(add(q_const_mptr, shl(5, qconst))), mload(q_ptr), r),");
    arms.push("                                r");
    arms.push("                            )");
    arms.push("                        }");
    arms.push("");
    arms.push("                        // Extra binary product terms outside the 7-limb shapes.");
    arms.push("                        for { let q_product_block := 0 } lt(q_product_block, q_product_count) { q_product_block := add(q_product_block, 1) } {");
    arms.push("                            let q_word := mload(q_pc)");
    arms.push("                            let qconst := byte(0, q_word)");
    arms.push("                            let q_lhs := and(shr(232, q_word), 0xffff)");
    arms.push("                            let q_rhs := and(shr(216, q_word), 0xffff)");
    arms.push("                            q_pc := add(q_pc, 5)");
    arms.ptr_guard("q_lhs");
    arms.ptr_guard("q_rhs");
    fused_product_add_acc(arms);
    arms.push("                        }");
    arms.push("");
    arms.push("                        if and(q_flags, 0x01) {");
    arms.push("                            // Apply the optional gate condition last so every");
    arms.push("                            // subterm shares the same selector/condition.");
    arms.push("                            q_acc := mulmod(mload(q_cond_ptr), q_acc, r)");
    arms.push("                        }");
    arms.push("                        // MODARITH7 pushes its fused identity value.");
    arms.push("                        q_top := q_acc");
    arms.push("                        q_has_top := 1");
    arms.push("                    }");
}

/// MODARITH7's product-term accumulator body (targets `q_acc`, 28-space
/// indent).
fn fused_product_add_acc(arms: &mut Arms<'_>) {
    arms.push("                            q_acc := addmod(");
    arms.push("                                q_acc,");
    arms.push("                                mulmod(");
    arms.push("                                    mulmod(mload(q_lhs), mload(q_rhs), r),");
    arms.push("                                    mload(add(q_const_mptr, shl(5, qconst))),");
    arms.push("                                    r");
    arms.push("                                ),");
    arms.push("                                r");
    arms.push("                            )");
}

fn native_permutation_arm(arms: &mut Arms<'_>) {
    arms.push("                    // Native permutation callback. It evaluates the");
    arms.push("                    // permutation identities from permutation.rs at this exact");
    arms.push("                    // VM position, preserving the Rust identity order while");
    arms.push("                    // avoiding a large interpreted product loop.");
    arms.push("                    // VM 0x19 NATIVE_PERMUTATION: marker for the generated permutation callback.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_NATIVE_PERMUTATION as usize)
    ));
    arms.push("                        // Native callbacks are identity-boundary opcodes. They");
    arms.push("                        // must not inherit any partially evaluated VM stack");
    arms.push("                        // state from the previous expression.");
    arms.push("                        q_top := 0");
    arms.push("                        q_has_top := 0");
    arms.push("                        // The generated loop below uses program.stack_mptr as");
    arms.push("                        // its scratch-table base, not as a conventional VM");
    arms.push("                        // stack. The Rust memory planner must reserve enough");
    arms.push("                        // words for structured_permutation_scratch_words(meta)");
    arms.push("                        // whenever this opcode can appear.");
    arms.stack_empty_guard();
    arms.push("                        // The generated lines below call the same fold snippets");
    arms.push("                        // used by interpreted expressions, so trace IDs and");
    arms.push("                        // y-batch positions remain contiguous.");
    for line in arms.inputs.native_permutation {
        arms.pushf(format!("                        {line}"));
    }
    arms.push("                    }");
}

fn native_lookup_arm(arms: &mut Arms<'_>) {
    arms.push("                    // Native lookup callback. This whole-family opcode");
    arms.push("                    // evaluates the LogUp boundary, helper-chunk, and");
    arms.push("                    // accumulator identities at this VM position, preserving");
    arms.push("                    // the Rust y-batch order while avoiding many interpreted");
    arms.push("                    // product-loop opcodes.");
    arms.push("                    // VM 0x1f NATIVE_LOOKUP: marker for the generated LogUp lookup callback.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_NATIVE_LOOKUP as usize)
    ));
    arms.push("                        // Reset VM stack state before entering structured");
    arms.push("                        // lookup Yul. Lookup callbacks own their scratch");
    arms.push("                        // layout and perform all needed folds internally.");
    arms.push("                        q_top := 0");
    arms.push("                        q_has_top := 0");
    arms.push("                        // The generated loop below uses program.stack_mptr as");
    arms.push("                        // f+beta/prefix/suffix scratch rather than as a");
    arms.push("                        // conventional VM stack. The Rust memory planner must");
    arms.push("                        // reserve structured_lookup_scratch_words(meta).");
    arms.stack_empty_guard();
    arms.push("                        // Generated LogUp code follows the same y-batch order");
    arms.push("                        // as the Rust identity stream.");
    for line in arms.inputs.native_lookup {
        arms.pushf(format!("                        {line}"));
    }
    arms.push("                    }");
}

fn native_identity_arm(arms: &mut Arms<'_>) {
    arms.push("                    // Native callbacks are generated only for the heaviest");
    arms.push("                    // recognized Midfall gate identities. All other gate and");
    arms.push("                    // non-native identity arithmetic remains in");
    arms.push("                    // the compact q_program VM above, preserving the Rust");
    arms.push("                    // `partially_evaluate_identities` order.");
    arms.push("                    // VM 0x1b NATIVE_IDENTITY: marker for generated heavy-gate callbacks.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_NATIVE_IDENTITY as usize)
    ));
    arms.push("                        // Operand layout: u16 native callback index. The");
    arms.push("                        // manifest validates that callback indexes appear in");
    arms.push("                        // generated order and target existing switch cases.");
    arms.push("                        let q_native_idx := shr(240, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 2)");
    arms.push("                        // Heavy identities are whole expressions, so clear the");
    arms.push("                        // interpreter stack before dispatching.");
    arms.push("                        q_top := 0");
    arms.push("                        q_has_top := 0");
    arms.stack_empty_guard();
    arms.push("                        // Native identity sub-cases are generated from selected heavy gate identities.");
    arms.push("                        switch q_native_idx");
    for (index, block) in arms.inputs.native_identities.iter().enumerate() {
        arms.pushf(format!("                        case {index} {{"));
        for line in block {
            arms.pushf(format!("                            {line}"));
        }
        arms.push("                        }");
    }
    arms.push("                        default { q_program_fail() }");
    arms.push("                    }");
}

fn fold_main_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x0a FOLD_MAIN: consume q_top into the fully evaluated numerator fold.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_FOLD_MAIN as usize)
    ));
    arms.push("                        // q_top is the complete value of one fully evaluated");
    arms.push("                        // identity at x. It leaves the expression stack here.");
    arms.top_guard();
    arms.push("                        let q_eval := q_top");
    arms.push("                        q_has_top := 0");
    arms.fold_trace();
    let numer = hex(arms.program().eval_numer_mptr);
    arms.push("                        // Fully-evaluated identity: qn = qn*y + eval.");
    arms.push("                        // This matches the reverse y-power fold in Rust");
    arms.push("                        // linearization once all identities have been read.");
    arms.pushf(format!(
        "                        mstore({numer}, mulmod(mload({numer}), y, r))"
    ));
    arms.pushf(format!(
        "                        mstore({numer}, addmod(mload({numer}), q_eval, r))"
    ));
    arms.push("                    }");
}

fn fold_selector_arm(arms: &mut Arms<'_>) {
    arms.push("                    // VM 0x0b FOLD_SELECTOR: consume q_top into one simple-selector bucket.");
    arms.pushf(format!(
        "                    case {} {{",
        hex(Q_OP_FOLD_SELECTOR as usize)
    ));
    arms.push("                        // Operand layout packed into three bytes:");
    arms.push("                        //   high byte: selector bucket index;");
    arms.push("                        //   low u16 : y-power gap since this selector's");
    arms.push("                        //             previous contribution.");
    arms.push("                        let q_selector_payload := shr(232, mload(q_pc))");
    arms.push("                        q_pc := add(q_pc, 3)");
    arms.push("                        let q_sel_idx := shr(16, q_selector_payload)");
    arms.push("                        let q_sel_gap := and(q_selector_payload, 0xffff)");
    arms.push("                        // P12: the bucket index addresses the SELECTOR_ACC");
    arms.push("                        // region and the gap indexes the y-power table; both");
    arms.push("                        // are codegen-known sizes, so clamp before the writes.");
    arms.pushf(format!(
        "                        if iszero(lt(q_sel_idx, {})) {{ q_program_fail() }}",
        arms.program().num_selector_buckets
    ));
    arms.pushf(format!(
        "                        if gt(q_sel_gap, {}) {{ q_program_fail() }}",
        hex(arms.program().selector_max_power)
    ));
    arms.top_guard();
    arms.push("                        let q_eval := q_top");
    arms.push("                        q_has_top := 0");
    arms.fold_trace();
    let numer = hex(arms.program().eval_numer_mptr);
    let power = hex(arms.program().selector_power_mptr);
    arms.push("                        // Simple-selector identity: keep the same y-batch");
    arms.push("                        // position as main identities, then advance only this");
    arms.push("                        // selector bucket by its codegen-known gap.");
    arms.push("                        //");
    arms.push("                        // The global fully-evaluated accumulator is still");
    arms.push("                        // multiplied by y so later main identities land at the");
    arms.push("                        // same y powers as Rust's reverse fold.");
    arms.pushf(format!(
        "                        mstore({numer}, mulmod(mload({numer}), y, r))"
    ));
    arms.push(
        "                        let q_target_ptr := add(SELECTOR_ACC_MPTR, shl(5, q_sel_idx))",
    );
    arms.push("                        let q_sel_acc := mload(q_target_ptr)");
    arms.push("                        if q_sel_gap {");
    arms.push("                            // Selector buckets are sparse in the global");
    arms.push("                            // identity stream. Precomputed y^gap advances only");
    arms.push("                            // this selector's local accumulator.");
    arms.pushf(format!(
        "                            q_sel_acc := mulmod(q_sel_acc, mload(add({power}, shl(5, q_sel_gap))), r)"
    ));
    arms.push("                        }");
    arms.push("                        mstore(q_target_ptr, addmod(q_sel_acc, q_eval, r))");
    arms.push("                    }");
}

/// Placeholder native-callback bodies for the committed snapshot.
#[cfg(test)]
pub(crate) fn snapshot_native_lines(family: &str) -> Vec<String> {
    vec![format!(
        "// snapshot placeholder: generated {family} callback body"
    )]
}

/// Render the complete snapshot text: header, all-ops opcode summary, and
/// every switch arm with trace instrumentation on.
#[cfg(test)]
pub(crate) fn render_snapshot() -> String {
    let program = snapshot_program();
    let native_permutation = snapshot_native_lines("permutation");
    let native_lookup = snapshot_native_lines("lookup");
    let native_identities = vec![snapshot_native_lines("heavy-gate")];
    let summary = quotient_vm_op_summary(&program);
    let arms = quotient_vm_switch_arms(&YulArmInputs {
        program: &program,
        trace: true,
        native_permutation: &native_permutation,
        native_lookup: &native_lookup,
        native_identities: &native_identities,
    });
    let mut out = String::new();
    for header_line in [
        "// GENERATED SNAPSHOT -- do not edit by hand.",
        "//",
        "// Canonical all-ops render of the quotient VM interpreter arms from",
        "// src/lowering/quotient_numerator/vm/yul_arms.rs (every opcode and",
        "// memory token enabled, trace instrumentation on, fixed placeholder",
        "// program constants from `snapshot_program`, one placeholder body per",
        "// native callback family). Regenerate with",
        "//   HALO2_SOLIDITY_UPDATE_VM_ARMS_SNAPSHOT=1 cargo test -p",
        "//     halo2_solidity_verifier --lib vm_arms_snapshot_is_current",
        "// and re-pin tests/template_digest.rs. Reviewers diff this file to",
        "// see interpreter-arm changes in readable Yul.",
    ] {
        out.push_str(header_line);
        out.push('\n');
    }
    out.push_str("// ===== opcode summary =====\n");
    for line in &summary {
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("// ===== switch arms =====\n");
    for line in &arms {
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// Canonical all-enabled snapshot inputs. Fixed placeholder values,
/// documented so the committed `vm_arms.snapshot.yul` is reproducible and
/// reviewable: every opcode and token enabled, trace on, one native identity
/// placeholder body per native family.
#[cfg(test)]
pub(crate) fn snapshot_program() -> QuotientProgram {
    QuotientProgram {
        len: 0x0123,
        used_ops: QUOTIENT_OPCODE_TABLE.iter().map(|spec| spec.opcode).collect(),
        used_mem_tokens: crate::lowering::quotient_numerator::vm::QUOTIENT_MEM_TOKEN_TABLE
            .iter()
            .map(|spec| spec.token)
            .collect(),
        op_summary_lines: Vec::new(),
        vm_switch_arms: Vec::new(),
        const_mptr: 0x0001_0000,
        eval_numer_mptr: 0x8000,
        trace_id_mptr: 0x8020,
        selector_power_mptr: 0x8040,
        selector_max_power: 3,
        selector_tail_updates: Vec::new(),
        stack_mptr: 0x9000,
        stack_hi: 0x9200,
        num_consts: 300,
        program_mptr: 0x0001_1000,
        operand_lo: 0x1000,
        operand_hi: 0x0002_0000,
        num_selector_buckets: 2,
    }
}
