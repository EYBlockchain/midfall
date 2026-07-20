// SPDX-License-Identifier: CC0-1.0
//! Independent reference interpreter for finalized quotient VM bytecode.
//!
//! This is the second implementation of the quotient VM ABI. It exists so the
//! generator can certify its own output: for every render, the emitted bytecode
//! is executed here and compared against direct evaluation of the
//! [`QuotientExpr`] trees the bytecode was lowered from. A disagreement means
//! the emitter, one of its shape recognizers, or the run-compaction pass
//! miscompiled an identity, and the render is rejected before any artifact is
//! produced.
//!
//! Why a random-assignment check is sufficient: the certifier samples a
//! deterministic challenge from the finalized quotient bytecode, constant
//! table, oracle expression trees, and VK payload, then evaluates the fixed
//! program at that assignment. Any miscompilation therefore yields a wrong
//! polynomial that was fixed before the challenge was known, and it disagrees
//! with the correct one with probability `1 - deg/|Fr|`. One challenge-derived
//! evaluation is enough to catch it with overwhelming probability.
//!
//! Scope. This certifies the **emitter to reference-interpreter** leg, which is
//! where the shape recognizers in the parent module live. The
//! **reference-interpreter to Yul** leg is covered separately by the opcode and
//! memory-token table conformance tests and by the per-identity Rust/Solidity
//! trace differential on fixture circuits. Identities executed as inline Yul,
//! native callbacks, or the structured tail are not lowered to bytecode at all,
//! so this module evaluates them directly from their expression trees and they
//! remain covered only by those other two mechanisms.

use std::collections::HashMap;

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use ruint::aliases::U256;
use sha3::{Digest, Keccak256};

use super::{
    QuotientExpr, QuotientMem, QUOTIENT_VM_LIMBS, QUOTIENT_VM_PAIRWISE_COEFFS,
    Q_MODARITH7_FLAG_COND, Q_MODARITH7_FLAG_CONST, Q_OP_ADD, Q_OP_ADD_CONST, Q_OP_ADD_CONST_U8,
    Q_OP_ADD_MEM_U16, Q_OP_ADD_MUL_CONST_U8_MEM_U16, Q_OP_ADD_MUL_MEM_MEM,
    Q_OP_ADD_MUL_MEM_MEM_CONST_U8, Q_OP_AFFINE_SUM, Q_OP_BILIN7_PAIRWISE, Q_OP_BILIN7_ROW,
    Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_LIN7, Q_OP_MODARITH7, Q_OP_MUL, Q_OP_MUL_CONST,
    Q_OP_MUL_CONST_U8, Q_OP_MUL_MEM_U16, Q_OP_NATIVE_IDENTITY, Q_OP_NATIVE_LOOKUP,
    Q_OP_NATIVE_PERMUTATION, Q_OP_NEG, Q_OP_POW5, Q_OP_PUSH_CONST, Q_OP_PUSH_CONST_U8,
    Q_OP_PUSH_MEM_LITERAL, Q_OP_PUSH_MEM_TOKEN, Q_OP_PUSH_MEM_TOKEN_OFFSET, Q_OP_PUSH_MEM_U16,
    Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16, Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
};
use crate::lowering::layout::WORD_BYTES;

/// Deterministic pseudorandom assignment for every verifier memory slot.
///
/// The bytecode addresses memory by absolute pointer or by symbolic token, and
/// the expression trees address the exact same slots. Deriving each value from
/// its own address means both sides observe identical memory without the
/// certifier having to enumerate the live address set up front, which in turn
/// means a pointer-packing bug shows up as a value mismatch rather than as a
/// missing map key.
#[derive(Clone, Debug)]
pub(crate) struct QuotientRefMemory {
    seed: [u8; 32],
    cache: HashMap<(u8, u32), Fq>,
}

impl QuotientRefMemory {
    /// Build an assignment for one certification run.
    pub(crate) fn new(seed: [u8; 32]) -> Self {
        Self {
            seed,
            cache: HashMap::new(),
        }
    }

    /// Value at an absolute memory pointer.
    pub(crate) fn literal(&mut self, ptr: u32) -> Fq {
        self.derive(0, ptr)
    }

    /// Value behind a symbolic memory token, optionally offset.
    pub(crate) fn token(&mut self, token: u8, offset: u32) -> Fq {
        // Tokens resolve to generated addresses disjoint from the literal
        // pointer space, so they get their own domain tag.
        self.derive(1 + token, offset)
    }

    /// Derive one field element from a domain-separated address.
    fn derive(&mut self, domain: u8, address: u32) -> Fq {
        if let Some(value) = self.cache.get(&(domain, address)) {
            return *value;
        }
        let mut hasher = Keccak256::new();
        hasher.update(b"midfall/quotient-vm/reference-memory/v1");
        hasher.update(self.seed);
        hasher.update([domain]);
        hasher.update(address.to_be_bytes());
        let lo = hasher.finalize();

        let mut hasher = Keccak256::new();
        hasher.update(b"midfall/quotient-vm/reference-memory/v1/hi");
        hasher.update(lo);
        let hi = hasher.finalize();

        let mut wide = [0u8; 64];
        wide[..32].copy_from_slice(&lo);
        wide[32..].copy_from_slice(&hi);
        let value = <Fq as ff::FromUniformBytes<64>>::from_uniform_bytes(&wide);
        self.cache.insert((domain, address), value);
        value
    }
}

/// Evaluate a typed quotient expression directly, without going through the VM.
///
/// This is the oracle side of the certification: it follows the same shape as
/// `Expression::evaluate` in the native verifier and knows nothing about
/// opcodes, shape recognizers, or operand packing.
pub(crate) fn eval_quotient_expr(expr: &QuotientExpr, mem: &mut QuotientRefMemory) -> Fq {
    match expr {
        QuotientExpr::Const(value) => fq_from_u256(*value),
        QuotientExpr::Mem(QuotientMem::Literal(ptr)) => mem.literal(*ptr),
        QuotientExpr::Mem(QuotientMem::Token(token)) => mem.token(*token, 0),
        QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => mem.token(*token, *offset),
        QuotientExpr::Add(lhs, rhs) => eval_quotient_expr(lhs, mem) + eval_quotient_expr(rhs, mem),
        QuotientExpr::Mul(lhs, rhs) => eval_quotient_expr(lhs, mem) * eval_quotient_expr(rhs, mem),
        QuotientExpr::Neg(inner) => -eval_quotient_expr(inner, mem),
    }
}

/// Evaluate one identity expression subprogram, up to but excluding its fold.
///
/// Returns an error rather than panicking: this runs inside the generator, and
/// a malformed stream must surface as a `GeneratorError`, not a process abort.
pub(crate) fn eval_quotient_identity(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
) -> Result<Fq, String> {
    let mut stack: Vec<Fq> = Vec::new();
    let mut idx = 0usize;

    // Pop helpers keep the error path uniform; the offline validator has
    // already proven depth safety, so these only fire on validator drift.
    macro_rules! pop {
        () => {
            stack
                .pop()
                .ok_or_else(|| format!("reference VM stack underflow at byte {idx}"))?
        };
    }

    while idx < bytes.len() {
        let op = bytes[idx];
        match op {
            Q_OP_PUSH_CONST => {
                let slot = read_u16(bytes, idx + 1)? as usize;
                stack.push(const_at(consts, slot, idx)?);
                idx += 3;
            }
            Q_OP_PUSH_CONST_U8 => {
                let slot = byte_at(bytes, idx + 1)? as usize;
                stack.push(const_at(consts, slot, idx)?);
                idx += 2;
            }
            Q_OP_PUSH_MEM_LITERAL => {
                let ptr = read_u32(bytes, idx + 1)?;
                stack.push(mem.literal(ptr));
                idx += 5;
            }
            Q_OP_PUSH_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1)? as u32;
                stack.push(mem.literal(ptr));
                idx += 3;
            }
            Q_OP_PUSH_MEM_TOKEN => {
                let token = byte_at(bytes, idx + 1)?;
                stack.push(mem.token(token, 0));
                idx += 2;
            }
            Q_OP_PUSH_MEM_TOKEN_OFFSET => {
                let token = byte_at(bytes, idx + 1)?;
                let offset = read_u32(bytes, idx + 2)?;
                stack.push(mem.token(token, offset));
                idx += 6;
            }
            Q_OP_ADD => {
                let rhs = pop!();
                let lhs = pop!();
                stack.push(lhs + rhs);
                idx += 1;
            }
            Q_OP_MUL => {
                let rhs = pop!();
                let lhs = pop!();
                stack.push(lhs * rhs);
                idx += 1;
            }
            Q_OP_NEG => {
                let value = pop!();
                stack.push(-value);
                idx += 1;
            }
            Q_OP_POW5 => {
                let value = pop!();
                let squared = value * value;
                stack.push(value * squared * squared);
                idx += 1;
            }
            Q_OP_ADD_CONST_U8 | Q_OP_MUL_CONST_U8 => {
                let slot = byte_at(bytes, idx + 1)? as usize;
                let value = const_at(consts, slot, idx)?;
                let acc = pop!();
                stack.push(if op == Q_OP_ADD_CONST_U8 {
                    acc + value
                } else {
                    acc * value
                });
                idx += 2;
            }
            Q_OP_ADD_CONST | Q_OP_MUL_CONST => {
                let slot = read_u16(bytes, idx + 1)? as usize;
                let value = const_at(consts, slot, idx)?;
                let acc = pop!();
                stack.push(if op == Q_OP_ADD_CONST {
                    acc + value
                } else {
                    acc * value
                });
                idx += 3;
            }
            Q_OP_ADD_MEM_U16 | Q_OP_MUL_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1)? as u32;
                let value = mem.literal(ptr);
                let acc = pop!();
                stack.push(if op == Q_OP_ADD_MEM_U16 {
                    acc + value
                } else {
                    acc * value
                });
                idx += 3;
            }
            Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => {
                let acc = pop!();
                let (term, len) = affine_product_term(bytes, consts, mem, idx + 1)?;
                stack.push(acc + term);
                idx += 1 + len;
            }
            Q_OP_ADD_MUL_CONST_U8_MEM_U16 => {
                let acc = pop!();
                let (term, len) = affine_linear_term(bytes, consts, mem, idx + 1)?;
                stack.push(acc + term);
                idx += 1 + len;
            }
            Q_OP_ADD_MUL_MEM_MEM => {
                let lhs = read_u16(bytes, idx + 1)? as u32;
                let rhs = read_u16(bytes, idx + 3)? as u32;
                let acc = pop!();
                stack.push(acc + mem.literal(lhs) * mem.literal(rhs));
                idx += 5;
            }
            Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 | Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
                // Run compaction is a pure encoding change: the same terms in
                // the same order, with one shared count instead of repeated
                // opcode bytes.
                let count = read_u16(bytes, idx + 1)? as usize;
                if count == 0 {
                    return Err(format!("reference VM zero-length run at byte {idx}"));
                }
                let mut cursor = idx + 3;
                let mut acc = pop!();
                for _ in 0..count {
                    let (term, len) = if op == Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 {
                        affine_product_term(bytes, consts, mem, cursor)?
                    } else {
                        affine_linear_term(bytes, consts, mem, cursor)?
                    };
                    acc += term;
                    cursor += len;
                }
                stack.push(acc);
                idx = cursor;
            }
            Q_OP_AFFINE_SUM => {
                // Mixed run: all linear terms first, then all product terms,
                // matching `compact_quotient_runs`.
                let lin_count = read_u16(bytes, idx + 1)? as usize;
                let product_count = read_u16(bytes, idx + 3)? as usize;
                if lin_count == 0 || product_count == 0 {
                    return Err(format!(
                        "reference VM AFFINE_SUM at byte {idx} requires nonzero counts"
                    ));
                }
                let mut cursor = idx + 5;
                let mut acc = pop!();
                for _ in 0..lin_count {
                    let (term, len) = affine_linear_term(bytes, consts, mem, cursor)?;
                    acc += term;
                    cursor += len;
                }
                for _ in 0..product_count {
                    let (term, len) = affine_product_term(bytes, consts, mem, cursor)?;
                    acc += term;
                    cursor += len;
                }
                stack.push(acc);
                idx = cursor;
            }
            Q_OP_LIN7 => {
                let (value, len) = limb_linear_form(bytes, consts, mem, idx + 1)?;
                stack.push(value);
                idx += 1 + len;
            }
            Q_OP_BILIN7_ROW => {
                let (value, len) = limb_row_form(bytes, consts, mem, idx + 1)?;
                stack.push(value);
                idx += 1 + len;
            }
            Q_OP_BILIN7_PAIRWISE => {
                let (value, len) = limb_pairwise_form(bytes, consts, mem, idx + 1)?;
                stack.push(value);
                idx += 1 + len;
            }
            Q_OP_MODARITH7 => {
                let (value, len) = modarith7_form(bytes, consts, mem, idx + 1)?;
                stack.push(value);
                idx += 1 + len;
            }
            Q_OP_FOLD_MAIN
            | Q_OP_FOLD_SELECTOR
            | Q_OP_NATIVE_PERMUTATION
            | Q_OP_NATIVE_LOOKUP
            | Q_OP_NATIVE_IDENTITY => {
                return Err(format!(
                    "reference VM found stream opcode {op:#x} inside an identity expression at byte {idx}"
                ));
            }
            _ => {
                return Err(format!("reference VM unknown opcode {op:#x} at byte {idx}"));
            }
        }
    }

    if stack.len() != 1 {
        return Err(format!(
            "reference VM identity left {} value(s) on the stack, expected 1",
            stack.len()
        ));
    }
    Ok(stack.pop().expect("checked length"))
}

/// Decode one `const * mload(ptr)` term and return its byte length.
fn affine_linear_term(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let ptr = read_u16(bytes, idx)? as u32;
    let slot = byte_at(bytes, idx + 2)? as usize;
    Ok((const_at(consts, slot, idx)? * mem.literal(ptr), 3))
}

/// Decode one `mload(lhs) * mload(rhs) * const` term and return its byte length.
fn affine_product_term(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let lhs = read_u16(bytes, idx)? as u32;
    let rhs = read_u16(bytes, idx + 2)? as u32;
    let slot = byte_at(bytes, idx + 4)? as usize;
    Ok((
        mem.literal(lhs) * mem.literal(rhs) * const_at(consts, slot, idx)?,
        5,
    ))
}

/// Decode a seven-limb linear form `sum_i const_i * mload(ptr_i)`.
fn limb_linear_form(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let mut acc = Fq::ZERO;
    let mut cursor = idx;
    for _ in 0..QUOTIENT_VM_LIMBS {
        let slot = byte_at(bytes, cursor)? as usize;
        let ptr = read_u16(bytes, cursor + 1)? as u32;
        acc += const_at(consts, slot, cursor)? * mem.literal(ptr);
        cursor += 3;
    }
    Ok((acc, cursor - idx))
}

/// Decode `mload(lhs) * sum_i const_i * mload(rhs_i)`.
fn limb_row_form(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let lhs = read_u16(bytes, idx)? as u32;
    let lhs_value = mem.literal(lhs);
    let (inner, len) = limb_linear_form(bytes, consts, mem, idx + 2)?;
    Ok((lhs_value * inner, 2 + len))
}

/// Decode a 7x7 pairwise product with `i + j` indexed coefficients.
fn limb_pairwise_form(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let lhs_base = read_u16(bytes, idx)? as u32;
    let rhs_base = read_u16(bytes, idx + 2)? as u32;
    let coeff_idx = idx + 4;
    // Bounds-check the whole coefficient block once so the inner loop cannot
    // read past the program.
    byte_at(bytes, coeff_idx + QUOTIENT_VM_PAIRWISE_COEFFS - 1)?;

    let mut acc = Fq::ZERO;
    for i in 0..QUOTIENT_VM_LIMBS {
        let lhs = mem.literal(lhs_base + (i as u32) * WORD_BYTES as u32);
        for j in 0..QUOTIENT_VM_LIMBS {
            let rhs = mem.literal(rhs_base + (j as u32) * WORD_BYTES as u32);
            let slot = bytes[coeff_idx + i + j] as usize;
            acc += lhs * rhs * const_at(consts, slot, coeff_idx)?;
        }
    }
    Ok((acc, 4 + QUOTIENT_VM_PAIRWISE_COEFFS))
}

/// Decode the dynamic mixed seven-limb affine form.
fn modarith7_form(
    bytes: &[u8],
    consts: &[U256],
    mem: &mut QuotientRefMemory,
    idx: usize,
) -> Result<(Fq, usize), String> {
    let mut cursor = idx;
    let flags = byte_at(bytes, cursor)?;
    if flags & !(Q_MODARITH7_FLAG_COND | Q_MODARITH7_FLAG_CONST) != 0 {
        return Err(format!(
            "reference VM MODARITH7 unknown flag bits {flags:#x} at byte {idx}"
        ));
    }
    cursor += 1;

    let cond = if flags & Q_MODARITH7_FLAG_COND != 0 {
        let ptr = read_u16(bytes, cursor)? as u32;
        cursor += 2;
        Some(ptr)
    } else {
        None
    };

    let mut acc = Fq::ZERO;
    if flags & Q_MODARITH7_FLAG_CONST != 0 {
        let slot = byte_at(bytes, cursor)? as usize;
        acc += const_at(consts, slot, cursor)?;
        cursor += 1;
    }

    let lin_count = byte_at(bytes, cursor)? as usize;
    let row_count = byte_at(bytes, cursor + 1)? as usize;
    let pairwise_count = byte_at(bytes, cursor + 2)? as usize;
    let mem_count = byte_at(bytes, cursor + 3)? as usize;
    let product_count = byte_at(bytes, cursor + 4)? as usize;
    cursor += 5;

    for _ in 0..lin_count {
        let (value, len) = limb_linear_form(bytes, consts, mem, cursor)?;
        acc += value;
        cursor += len;
    }
    for _ in 0..row_count {
        let (value, len) = limb_row_form(bytes, consts, mem, cursor)?;
        acc += value;
        cursor += len;
    }
    for _ in 0..pairwise_count {
        let (value, len) = limb_pairwise_form(bytes, consts, mem, cursor)?;
        acc += value;
        cursor += len;
    }
    for _ in 0..mem_count {
        // Note the operand order here is const-slot first, unlike the standalone
        // `ADD_MUL_CONST_U8_MEM_U16` term, so this cannot reuse the helper.
        let slot = byte_at(bytes, cursor)? as usize;
        let ptr = read_u16(bytes, cursor + 1)? as u32;
        acc += const_at(consts, slot, cursor)? * mem.literal(ptr);
        cursor += 3;
    }
    for _ in 0..product_count {
        let slot = byte_at(bytes, cursor)? as usize;
        let lhs = read_u16(bytes, cursor + 1)? as u32;
        let rhs = read_u16(bytes, cursor + 3)? as u32;
        acc += const_at(consts, slot, cursor)? * mem.literal(lhs) * mem.literal(rhs);
        cursor += 5;
    }

    if let Some(cond) = cond {
        acc *= mem.literal(cond);
    }
    Ok((acc, cursor - idx))
}

/// Read one byte with an explicit bounds error.
fn byte_at(bytes: &[u8], idx: usize) -> Result<u8, String> {
    bytes
        .get(idx)
        .copied()
        .ok_or_else(|| format!("reference VM read past end of program at byte {idx}"))
}

/// Read a big-endian `u16` operand.
fn read_u16(bytes: &[u8], idx: usize) -> Result<u16, String> {
    Ok(u16::from_be_bytes([
        byte_at(bytes, idx)?,
        byte_at(bytes, idx + 1)?,
    ]))
}

/// Read a big-endian `u32` operand.
fn read_u32(bytes: &[u8], idx: usize) -> Result<u32, String> {
    Ok(u32::from_be_bytes([
        byte_at(bytes, idx)?,
        byte_at(bytes, idx + 1)?,
        byte_at(bytes, idx + 2)?,
        byte_at(bytes, idx + 3)?,
    ]))
}

/// Look up a constant-table slot with an explicit bounds error.
fn const_at(consts: &[U256], slot: usize, idx: usize) -> Result<Fq, String> {
    consts
        .get(slot)
        .copied()
        .map(fq_from_u256)
        .ok_or_else(|| format!("reference VM constant slot {slot} out of range at byte {idx}"))
}

/// Convert a canonical `U256` constant-table entry into Fr.
fn fq_from_u256(value: U256) -> Fq {
    let bytes = value.to_le_bytes::<32>();
    let repr = <Fq as PrimeField>::Repr::from(bytes);
    Option::<Fq>::from(Fq::from_repr(repr)).expect("constant table holds canonical field elements")
}
