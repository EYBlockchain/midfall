// SPDX-License-Identifier: CC0-1.0
//! Host-side decoder and reference interpreter for finalized quotient-VM
//! programs.
//!
//! The only runtime consumer of the program bytes is the Yul interpreter in
//! `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`. This
//! module is a second decoder of exactly the bytes that are pinned in the VK
//! payload (after run compaction and word packing), written against the Yul
//! operand layouts rather than against the Rust builder. It is used by the
//! quotient listing / manifest artifacts to:
//!
//! * print every instruction and every sub-term of the dynamic opcodes,
//! * re-evaluate each interpreted identity over a concrete memory image, and
//! * rebuild each interpreted identity as a symbolic polynomial.
//!
//! Both the numeric and the symbolic evaluation go through the same generic
//! [`eval_vm_identity`] routine, so the listing's polynomial and the
//! translation-validation check describe the same instruction semantics. The
//! decoder deliberately does not reuse `quotient_op_len` or the builder's
//! stack validator: the listing path is meant to fail closed if the builder
//! and this independent reading of the ABI ever disagree.
//!
//! What this module does not establish: that the Yul interpreter implements
//! these semantics. That property is covered by the EVM differential tests.

use ruint::aliases::U256;

use super::{
    QUOTIENT_MEM_TOKEN_TABLE, QUOTIENT_OPCODE_TABLE, Q_OP_ADD, Q_OP_ADD_CONST, Q_OP_ADD_CONST_U8,
    Q_OP_ADD_MEM_U16, Q_OP_ADD_MUL_CONST_U8_MEM_U16, Q_OP_ADD_MUL_MEM_MEM,
    Q_OP_ADD_MUL_MEM_MEM_CONST_U8, Q_OP_AFFINE_SUM, Q_OP_BILIN7_PAIRWISE, Q_OP_BILIN7_ROW,
    Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_LIN7, Q_OP_MODARITH7, Q_OP_MUL, Q_OP_MUL_CONST,
    Q_OP_MUL_CONST_U8, Q_OP_MUL_MEM_U16, Q_OP_NATIVE_IDENTITY, Q_OP_NATIVE_LOOKUP,
    Q_OP_NATIVE_PERMUTATION, Q_OP_NEG, Q_OP_POW5, Q_OP_PUSH_CONST, Q_OP_PUSH_CONST_U8,
    Q_OP_PUSH_MEM_LITERAL, Q_OP_PUSH_MEM_TOKEN, Q_OP_PUSH_MEM_TOKEN_OFFSET, Q_OP_PUSH_MEM_U16,
    Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16, Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
};

/// Number of limbs addressed by the seven-limb opcodes (fixed by the Yul
/// loops).
pub(crate) const VM_LIMBS: usize = 7;
/// Number of `i + j` coefficient slots of a 7x7 pairwise product.
pub(crate) const VM_PAIRWISE_COEFFS: usize = 2 * VM_LIMBS - 1;
/// Byte stride between consecutive limbs of a pairwise-product base.
pub(crate) const VM_LIMB_STRIDE: u32 = 0x20;

/// `MODARITH7` flag: the affine sum is multiplied by a memory condition.
pub(crate) const VM_MODARITH7_FLAG_COND: u8 = 0x01;
/// `MODARITH7` flag: the accumulator is seeded from a constant slot.
pub(crate) const VM_MODARITH7_FLAG_CONST: u8 = 0x02;

/// One `(constant slot, memory pointer)` limb term, in the byte order used by
/// `LIN7`, `BILIN7_ROW` and the `MODARITH7` blocks (`u8 const, u16 ptr`).
pub(crate) type VmLimbTerm = (u8, u16);

/// A memory operand as the Yul interpreter resolves it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VmMem {
    /// Absolute memory pointer (`PUSH_MEM_LITERAL` / `PUSH_MEM_U16`).
    Addr(u32),
    /// Generated Yul memory symbol selected by a token byte.
    Token(u8),
    /// Generated Yul memory symbol plus a byte offset.
    TokenOffset(u8, u32),
}

/// Decoded `MODARITH7` payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VmModarith7 {
    /// Raw flag byte.
    pub(crate) flags: u8,
    /// Optional condition pointer, applied last.
    pub(crate) cond: Option<u16>,
    /// Optional constant slot seeding the accumulator.
    pub(crate) constant: Option<u8>,
    /// `LIN7` blocks.
    pub(crate) lin: Vec<[VmLimbTerm; VM_LIMBS]>,
    /// `BILIN7_ROW` blocks: `(lhs pointer, seven rhs terms)`.
    pub(crate) rows: Vec<(u16, [VmLimbTerm; VM_LIMBS])>,
    /// `BILIN7_PAIRWISE` blocks: `(lhs base, rhs base, 13 coefficient slots)`.
    pub(crate) pairwise: Vec<(u16, u16, [u8; VM_PAIRWISE_COEFFS])>,
    /// Extra `const * mload(ptr)` terms.
    pub(crate) mem: Vec<VmLimbTerm>,
    /// Extra `const * mload(lhs) * mload(rhs)` terms.
    pub(crate) products: Vec<(u8, u16, u16)>,
}

/// One decoded opcode with all operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum VmOp {
    /// `0x01` (`wide`) / `0x09`: push a constant-table word.
    PushConst { slot: u16, wide: bool },
    /// `0x02` / `0x03` / `0x04` / `0x05`: push a memory word.
    PushMem { mem: VmMem },
    /// `0x06`: `top = next + top`.
    Add,
    /// `0x07`: `top = next * top`.
    Mul,
    /// `0x08`: `top = -top`.
    Neg,
    /// `0x20`: `top = top^5`.
    Pow5,
    /// `0x0c` / `0x0e` (`wide`): `top += const`.
    AddConst { slot: u16, wide: bool },
    /// `0x0d` / `0x0f` (`wide`): `top *= const`.
    MulConst { slot: u16, wide: bool },
    /// `0x10`: `top += mload(ptr)`.
    AddMem { ptr: u16 },
    /// `0x11`: `top *= mload(ptr)`.
    MulMem { ptr: u16 },
    /// `0x12`: `top += mload(lhs) * mload(rhs) * const`.
    AddMulMemMemConst { lhs: u16, rhs: u16, slot: u8 },
    /// `0x13`: `top += mload(ptr) * const`.
    AddMulConstMem { ptr: u16, slot: u8 },
    /// `0x14`: `top += mload(lhs) * mload(rhs)`.
    AddMulMemMem { lhs: u16, rhs: u16 },
    /// `0x15`: run of `0x12` payloads.
    RunMemMemConst { terms: Vec<(u16, u16, u8)> },
    /// `0x16`: run of `0x13` payloads.
    RunConstMem { terms: Vec<(u16, u8)> },
    /// `0x22`: linear terms `(ptr, const)` then product terms `(lhs, rhs,
    /// const)`.
    AffineSum {
        lin: Vec<(u16, u8)>,
        products: Vec<(u16, u16, u8)>,
    },
    /// `0x1c`: push `sum const_i * mload(ptr_i)`.
    Lin7 { terms: [VmLimbTerm; VM_LIMBS] },
    /// `0x1d`: push `mload(lhs) * sum const_i * mload(rhs_i)`.
    Bilin7Row {
        lhs: u16,
        terms: [VmLimbTerm; VM_LIMBS],
    },
    /// `0x1e`: push `sum_{i,j} const_{i+j} * lhs_i * rhs_j`.
    Bilin7Pairwise {
        lhs_base: u16,
        rhs_base: u16,
        coeffs: [u8; VM_PAIRWISE_COEFFS],
    },
    /// `0x21`: push a fused affine limb identity.
    Modarith7(Box<VmModarith7>),
    /// `0x0a`: fold `top` into the main accumulator.
    FoldMain,
    /// `0x0b`: fold `top` into a simple-selector bucket.
    FoldSelector { selector: u8, gap: u16 },
    /// `0x19`: generated permutation-family callback.
    NativePermutation,
    /// `0x1f`: generated lookup-family callback.
    NativeLookup,
    /// `0x1b`: generated heavy-gate callback.
    NativeIdentity { index: u16 },
}

/// One decoded instruction and its exact byte span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VmInstruction {
    /// Program byte offset of the opcode.
    pub(crate) offset: usize,
    /// Encoded byte length including the opcode.
    pub(crate) len: usize,
    /// Opcode byte.
    pub(crate) opcode: u8,
    /// Decoded operands.
    pub(crate) op: VmOp,
}

impl VmInstruction {
    /// Exclusive end offset.
    pub(crate) fn end(&self) -> usize {
        self.offset + self.len
    }
}

/// Upper-case mnemonic for an opcode byte, from the ABI opcode table.
pub(crate) fn vm_mnemonic(opcode: u8) -> String {
    QUOTIENT_OPCODE_TABLE
        .iter()
        .find(|spec| spec.opcode == opcode)
        .map(|spec| spec.name.to_ascii_uppercase())
        .unwrap_or_else(|| format!("UNKNOWN_{opcode:#04x}"))
}

/// Generated Yul symbol for a memory token, if the token is part of the ABI.
pub(crate) fn vm_token_symbol(token: u8) -> Option<&'static str> {
    QUOTIENT_MEM_TOKEN_TABLE
        .iter()
        .find(|spec| spec.token == token)
        .map(|spec| spec.name)
}

/// Bounds-checked big-endian reader over the program bytes.
struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
    start: usize,
    opcode: u8,
}

impl Cursor<'_> {
    /// Take `n` bytes or report a truncated instruction.
    fn take(&mut self, n: usize, what: &str) -> Result<&[u8], String> {
        let end = self.pos.checked_add(n).ok_or_else(|| {
            format!(
                "{} at program byte {:#06x}: operand length overflow",
                vm_mnemonic(self.opcode),
                self.start
            )
        })?;
        if end > self.bytes.len() {
            return Err(format!(
                "truncated {} at program byte {:#06x}: {what} needs {n} byte(s) at {:#06x}, program has {} byte(s)",
                vm_mnemonic(self.opcode),
                self.start,
                self.pos,
                self.bytes.len()
            ));
        }
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    /// Read one byte.
    fn u8(&mut self, what: &str) -> Result<u8, String> {
        Ok(self.take(1, what)?[0])
    }

    /// Read a big-endian `u16`.
    fn u16(&mut self, what: &str) -> Result<u16, String> {
        let bytes = self.take(2, what)?;
        Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
    }

    /// Read a big-endian `u32`.
    fn u32(&mut self, what: &str) -> Result<u32, String> {
        let bytes = self.take(4, what)?;
        Ok(u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// Read seven `{u8 const, u16 ptr}` limb terms.
    fn limb_terms(&mut self, what: &str) -> Result<[VmLimbTerm; VM_LIMBS], String> {
        let mut terms = [(0u8, 0u16); VM_LIMBS];
        for term in &mut terms {
            let slot = self.u8(what)?;
            let ptr = self.u16(what)?;
            *term = (slot, ptr);
        }
        Ok(terms)
    }

    /// Read the 13 pairwise coefficient slots.
    fn pairwise_coeffs(&mut self, what: &str) -> Result<[u8; VM_PAIRWISE_COEFFS], String> {
        let bytes = self.take(VM_PAIRWISE_COEFFS, what)?;
        let mut coeffs = [0u8; VM_PAIRWISE_COEFFS];
        coeffs.copy_from_slice(bytes);
        Ok(coeffs)
    }
}

/// Reject a token the Yul interpreter would send to its `revert` default.
fn check_token(token: u8, offset: usize) -> Result<(), String> {
    if vm_token_symbol(token).is_some() {
        Ok(())
    } else {
        Err(format!(
            "unknown memory token {token:#04x} at program byte {offset:#06x}"
        ))
    }
}

/// Decode one instruction starting at `offset`.
pub(crate) fn decode_vm_instruction(bytes: &[u8], offset: usize) -> Result<VmInstruction, String> {
    let opcode = *bytes
        .get(offset)
        .ok_or_else(|| format!("program byte {offset:#06x} is past the end"))?;
    let mut cur = Cursor {
        bytes,
        pos: offset + 1,
        start: offset,
        opcode,
    };
    let op = match opcode {
        Q_OP_PUSH_CONST => VmOp::PushConst {
            slot: cur.u16("constant slot")?,
            wide: true,
        },
        Q_OP_PUSH_CONST_U8 => VmOp::PushConst {
            slot: u16::from(cur.u8("constant slot")?),
            wide: false,
        },
        Q_OP_PUSH_MEM_LITERAL => VmOp::PushMem {
            mem: VmMem::Addr(cur.u32("pointer")?),
        },
        Q_OP_PUSH_MEM_U16 => VmOp::PushMem {
            mem: VmMem::Addr(u32::from(cur.u16("pointer")?)),
        },
        Q_OP_PUSH_MEM_TOKEN => {
            let token = cur.u8("token")?;
            check_token(token, offset)?;
            VmOp::PushMem {
                mem: VmMem::Token(token),
            }
        }
        Q_OP_PUSH_MEM_TOKEN_OFFSET => {
            let token = cur.u8("token")?;
            check_token(token, offset)?;
            let off = cur.u32("token offset")?;
            VmOp::PushMem {
                mem: VmMem::TokenOffset(token, off),
            }
        }
        Q_OP_ADD => VmOp::Add,
        Q_OP_MUL => VmOp::Mul,
        Q_OP_NEG => VmOp::Neg,
        Q_OP_POW5 => VmOp::Pow5,
        Q_OP_ADD_CONST_U8 => VmOp::AddConst {
            slot: u16::from(cur.u8("constant slot")?),
            wide: false,
        },
        Q_OP_MUL_CONST_U8 => VmOp::MulConst {
            slot: u16::from(cur.u8("constant slot")?),
            wide: false,
        },
        Q_OP_ADD_CONST => VmOp::AddConst {
            slot: cur.u16("constant slot")?,
            wide: true,
        },
        Q_OP_MUL_CONST => VmOp::MulConst {
            slot: cur.u16("constant slot")?,
            wide: true,
        },
        Q_OP_ADD_MEM_U16 => VmOp::AddMem {
            ptr: cur.u16("pointer")?,
        },
        Q_OP_MUL_MEM_U16 => VmOp::MulMem {
            ptr: cur.u16("pointer")?,
        },
        Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => VmOp::AddMulMemMemConst {
            lhs: cur.u16("lhs pointer")?,
            rhs: cur.u16("rhs pointer")?,
            slot: cur.u8("constant slot")?,
        },
        Q_OP_ADD_MUL_CONST_U8_MEM_U16 => VmOp::AddMulConstMem {
            ptr: cur.u16("pointer")?,
            slot: cur.u8("constant slot")?,
        },
        Q_OP_ADD_MUL_MEM_MEM => VmOp::AddMulMemMem {
            lhs: cur.u16("lhs pointer")?,
            rhs: cur.u16("rhs pointer")?,
        },
        Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
            let count = cur.u16("run count")?;
            if count == 0 {
                return Err(format!("zero-length run at program byte {offset:#06x}"));
            }
            let mut terms = Vec::with_capacity(count as usize);
            for _ in 0..count {
                terms.push((
                    cur.u16("lhs pointer")?,
                    cur.u16("rhs pointer")?,
                    cur.u8("constant slot")?,
                ));
            }
            VmOp::RunMemMemConst { terms }
        }
        Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
            let count = cur.u16("run count")?;
            if count == 0 {
                return Err(format!("zero-length run at program byte {offset:#06x}"));
            }
            let mut terms = Vec::with_capacity(count as usize);
            for _ in 0..count {
                terms.push((cur.u16("pointer")?, cur.u8("constant slot")?));
            }
            VmOp::RunConstMem { terms }
        }
        Q_OP_AFFINE_SUM => {
            let lin_count = cur.u16("linear count")?;
            let product_count = cur.u16("product count")?;
            if lin_count == 0 || product_count == 0 {
                return Err(format!(
                    "AFFINE_SUM at program byte {offset:#06x} has an empty side ({lin_count} linear, {product_count} product)"
                ));
            }
            let mut lin = Vec::with_capacity(lin_count as usize);
            for _ in 0..lin_count {
                lin.push((cur.u16("pointer")?, cur.u8("constant slot")?));
            }
            let mut products = Vec::with_capacity(product_count as usize);
            for _ in 0..product_count {
                products.push((
                    cur.u16("lhs pointer")?,
                    cur.u16("rhs pointer")?,
                    cur.u8("constant slot")?,
                ));
            }
            VmOp::AffineSum { lin, products }
        }
        Q_OP_LIN7 => VmOp::Lin7 {
            terms: cur.limb_terms("LIN7 term")?,
        },
        Q_OP_BILIN7_ROW => {
            let lhs = cur.u16("lhs pointer")?;
            VmOp::Bilin7Row {
                lhs,
                terms: cur.limb_terms("BILIN7_ROW term")?,
            }
        }
        Q_OP_BILIN7_PAIRWISE => {
            let lhs_base = cur.u16("lhs base")?;
            let rhs_base = cur.u16("rhs base")?;
            VmOp::Bilin7Pairwise {
                lhs_base,
                rhs_base,
                coeffs: cur.pairwise_coeffs("pairwise coefficients")?,
            }
        }
        Q_OP_MODARITH7 => {
            let flags = cur.u8("flags")?;
            if flags & !(VM_MODARITH7_FLAG_COND | VM_MODARITH7_FLAG_CONST) != 0 {
                return Err(format!(
                    "MODARITH7 at program byte {offset:#06x} has unknown flag bits {flags:#04x}"
                ));
            }
            let cond = if flags & VM_MODARITH7_FLAG_COND != 0 {
                Some(cur.u16("condition pointer")?)
            } else {
                None
            };
            let constant = if flags & VM_MODARITH7_FLAG_CONST != 0 {
                Some(cur.u8("constant slot")?)
            } else {
                None
            };
            let lin_count = cur.u8("lin count")?;
            let row_count = cur.u8("row count")?;
            let pairwise_count = cur.u8("pairwise count")?;
            let mem_count = cur.u8("mem count")?;
            let product_count = cur.u8("product count")?;
            let mut body = VmModarith7 {
                flags,
                cond,
                constant,
                lin: Vec::with_capacity(lin_count as usize),
                rows: Vec::with_capacity(row_count as usize),
                pairwise: Vec::with_capacity(pairwise_count as usize),
                mem: Vec::with_capacity(mem_count as usize),
                products: Vec::with_capacity(product_count as usize),
            };
            for _ in 0..lin_count {
                body.lin.push(cur.limb_terms("LIN7 block term")?);
            }
            for _ in 0..row_count {
                let lhs = cur.u16("row lhs pointer")?;
                body.rows.push((lhs, cur.limb_terms("row term")?));
            }
            for _ in 0..pairwise_count {
                let lhs_base = cur.u16("pairwise lhs base")?;
                let rhs_base = cur.u16("pairwise rhs base")?;
                body.pairwise.push((
                    lhs_base,
                    rhs_base,
                    cur.pairwise_coeffs("pairwise coefficients")?,
                ));
            }
            for _ in 0..mem_count {
                body.mem.push((cur.u8("constant slot")?, cur.u16("pointer")?));
            }
            for _ in 0..product_count {
                body.products.push((
                    cur.u8("constant slot")?,
                    cur.u16("lhs pointer")?,
                    cur.u16("rhs pointer")?,
                ));
            }
            VmOp::Modarith7(Box::new(body))
        }
        Q_OP_FOLD_MAIN => VmOp::FoldMain,
        Q_OP_FOLD_SELECTOR => {
            let selector = cur.u8("selector index")?;
            let gap = cur.u16("selector gap")?;
            VmOp::FoldSelector { selector, gap }
        }
        Q_OP_NATIVE_PERMUTATION => VmOp::NativePermutation,
        Q_OP_NATIVE_LOOKUP => VmOp::NativeLookup,
        Q_OP_NATIVE_IDENTITY => VmOp::NativeIdentity {
            index: cur.u16("native index")?,
        },
        other => {
            return Err(format!(
                "unknown quotient VM opcode {other:#04x} at program byte {offset:#06x}"
            ))
        }
    };
    Ok(VmInstruction {
        offset,
        len: cur.pos - offset,
        opcode,
        op,
    })
}

/// Decode a complete program. Every byte must belong to exactly one decoded
/// instruction.
pub(crate) fn decode_vm_program(bytes: &[u8]) -> Result<Vec<VmInstruction>, String> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    while offset < bytes.len() {
        let instruction = decode_vm_instruction(bytes, offset)?;
        offset = instruction.end();
        out.push(instruction);
    }
    Ok(out)
}

/// Stack effect of one instruction in the cached-top VM model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StackEffect {
    /// Pushes one value.
    Push,
    /// Pops two values and pushes one.
    Binary,
    /// Rewrites the top value.
    Unary,
    /// Consumes the single remaining value and ends an identity.
    Fold,
    /// Identity-boundary callback; requires an empty stack.
    Native,
}

/// Classify the stack discipline of an opcode.
fn stack_effect(op: &VmOp) -> StackEffect {
    match op {
        VmOp::PushConst { .. }
        | VmOp::PushMem { .. }
        | VmOp::Lin7 { .. }
        | VmOp::Bilin7Row { .. }
        | VmOp::Bilin7Pairwise { .. }
        | VmOp::Modarith7(_) => StackEffect::Push,
        VmOp::Add | VmOp::Mul => StackEffect::Binary,
        VmOp::Neg
        | VmOp::Pow5
        | VmOp::AddConst { .. }
        | VmOp::MulConst { .. }
        | VmOp::AddMem { .. }
        | VmOp::MulMem { .. }
        | VmOp::AddMulMemMemConst { .. }
        | VmOp::AddMulConstMem { .. }
        | VmOp::AddMulMemMem { .. }
        | VmOp::RunMemMemConst { .. }
        | VmOp::RunConstMem { .. }
        | VmOp::AffineSum { .. } => StackEffect::Unary,
        VmOp::FoldMain | VmOp::FoldSelector { .. } => StackEffect::Fold,
        VmOp::NativePermutation | VmOp::NativeLookup | VmOp::NativeIdentity { .. } => {
            StackEffect::Native
        }
    }
}

/// Kind of one identity-stream item in the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VmItemKind {
    /// One interpreted identity ending in a fold opcode.
    Identity,
    /// Heavy-gate callback marker.
    NativeIdentity(u16),
    /// Permutation-family callback marker.
    NativePermutation,
    /// Lookup-family callback marker.
    NativeLookup,
}

/// One identity-stream item: a run of instructions that either computes and
/// folds one identity, or is a single native-callback marker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VmItem {
    /// Item kind.
    pub(crate) kind: VmItemKind,
    /// Instructions of the item, including the final fold opcode.
    pub(crate) instructions: Vec<VmInstruction>,
    /// Maximum operand-stack depth reached inside the item.
    pub(crate) max_depth: usize,
}

impl VmItem {
    /// First program byte of the item.
    pub(crate) fn byte_start(&self) -> usize {
        self.instructions.first().map(|i| i.offset).unwrap_or(0)
    }

    /// Exclusive end byte of the item.
    pub(crate) fn byte_end(&self) -> usize {
        self.instructions.last().map(|i| i.end()).unwrap_or(0)
    }

    /// Fold opcode of an interpreted identity.
    pub(crate) fn fold(&self) -> Option<&VmOp> {
        match self.kind {
            VmItemKind::Identity => self.instructions.last().map(|i| &i.op),
            _ => None,
        }
    }

    /// Instructions that compute the identity value (everything but the fold).
    pub(crate) fn body(&self) -> &[VmInstruction] {
        match self.kind {
            VmItemKind::Identity => &self.instructions[..self.instructions.len() - 1],
            _ => &[],
        }
    }
}

/// Split decoded instructions into identity-stream items, enforcing the same
/// stack discipline the Yul interpreter relies on (binary ops need two
/// values, folds need exactly one, callbacks need an empty stack, and the
/// program must end on an identity boundary).
pub(crate) fn split_vm_items(instructions: &[VmInstruction]) -> Result<Vec<VmItem>, String> {
    let mut items = Vec::new();
    let mut current: Vec<VmInstruction> = Vec::new();
    let mut depth = 0usize;
    let mut max_depth = 0usize;
    for instruction in instructions {
        let at = instruction.offset;
        let name = vm_mnemonic(instruction.opcode);
        match stack_effect(&instruction.op) {
            StackEffect::Push => {
                depth += 1;
                max_depth = max_depth.max(depth);
                current.push(instruction.clone());
            }
            StackEffect::Binary => {
                if depth < 2 {
                    return Err(format!(
                        "{name} at program byte {at:#06x} needs two stack values, found {depth}"
                    ));
                }
                depth -= 1;
                current.push(instruction.clone());
            }
            StackEffect::Unary => {
                if depth < 1 {
                    return Err(format!(
                        "{name} at program byte {at:#06x} needs one stack value, found {depth}"
                    ));
                }
                current.push(instruction.clone());
            }
            StackEffect::Fold => {
                if depth != 1 {
                    return Err(format!(
                        "{name} at program byte {at:#06x} needs exactly one stack value, found {depth}"
                    ));
                }
                current.push(instruction.clone());
                items.push(VmItem {
                    kind: VmItemKind::Identity,
                    instructions: std::mem::take(&mut current),
                    max_depth,
                });
                depth = 0;
                max_depth = 0;
            }
            StackEffect::Native => {
                if depth != 0 || !current.is_empty() {
                    return Err(format!(
                        "{name} at program byte {at:#06x} requires an identity boundary, found {depth} stack value(s)"
                    ));
                }
                let kind = match instruction.op {
                    VmOp::NativePermutation => VmItemKind::NativePermutation,
                    VmOp::NativeLookup => VmItemKind::NativeLookup,
                    VmOp::NativeIdentity { index } => VmItemKind::NativeIdentity(index),
                    _ => unreachable!("native stack effect"),
                };
                items.push(VmItem {
                    kind,
                    instructions: vec![instruction.clone()],
                    max_depth: 0,
                });
            }
        }
    }
    if !current.is_empty() || depth != 0 {
        return Err(format!(
            "program ends inside an identity: {} instruction(s) after the last fold, {depth} stack value(s) live",
            current.len()
        ));
    }
    Ok(items)
}

/// Value domain for [`eval_vm_identity`].
///
/// Implemented numerically (over BLS12-381 Fr) for translation validation and
/// symbolically (over polynomials in the evaluation slots) for the listing.
pub(crate) trait VmValues {
    /// Value type held on the VM stack.
    type Value: Clone;
    /// Additive identity.
    fn zero(&self) -> Self::Value;
    /// Constant-table word `slot`.
    fn constant(&self, slot: u16) -> Result<Self::Value, String>;
    /// Memory word at an absolute address.
    fn load(&self, addr: u32) -> Result<Self::Value, String>;
    /// Absolute address of a memory token.
    fn token_addr(&self, token: u8) -> Result<u32, String>;
    /// Field addition.
    fn add(&self, lhs: Self::Value, rhs: Self::Value) -> Result<Self::Value, String>;
    /// Field multiplication.
    fn mul(&self, lhs: Self::Value, rhs: Self::Value) -> Result<Self::Value, String>;
    /// Field negation.
    fn neg(&self, value: Self::Value) -> Result<Self::Value, String>;
}

/// Load a memory operand, resolving tokens the way the Yul switch does.
fn load_mem<V: VmValues>(values: &V, mem: VmMem) -> Result<V::Value, String> {
    match mem {
        VmMem::Addr(addr) => values.load(addr),
        VmMem::Token(token) => values.load(values.token_addr(token)?),
        VmMem::TokenOffset(token, off) => {
            let base = values.token_addr(token)?;
            let addr = base
                .checked_add(off)
                .ok_or_else(|| format!("token {token:#04x} + {off:#x} overflows"))?;
            values.load(addr)
        }
    }
}

/// `acc + c * mload(ptr)` in the Yul operand order.
fn add_const_times_mem<V: VmValues>(
    values: &V,
    acc: V::Value,
    slot: u8,
    ptr: u16,
) -> Result<V::Value, String> {
    let term = values.mul(
        values.constant(u16::from(slot))?,
        values.load(u32::from(ptr))?,
    )?;
    values.add(acc, term)
}

/// `acc + (mload(lhs) * mload(rhs)) * c` in the Yul operand order.
fn add_product_times_const<V: VmValues>(
    values: &V,
    acc: V::Value,
    lhs: u32,
    rhs: u32,
    slot: u8,
) -> Result<V::Value, String> {
    let product = values.mul(values.load(lhs)?, values.load(rhs)?)?;
    let term = values.mul(product, values.constant(u16::from(slot))?)?;
    values.add(acc, term)
}

/// Seven-limb linear form `sum c_i * mload(ptr_i)`.
fn lin7<V: VmValues>(
    values: &V,
    mut acc: V::Value,
    terms: &[VmLimbTerm; VM_LIMBS],
) -> Result<V::Value, String> {
    for (slot, ptr) in terms {
        acc = add_const_times_mem(values, acc, *slot, *ptr)?;
    }
    Ok(acc)
}

/// Row form `sum (mload(lhs) * mload(rhs_i)) * c_i`.
fn bilin7_row<V: VmValues>(
    values: &V,
    mut acc: V::Value,
    lhs: u16,
    terms: &[VmLimbTerm; VM_LIMBS],
) -> Result<V::Value, String> {
    let lhs_value = values.load(u32::from(lhs))?;
    for (slot, rhs) in terms {
        let product = values.mul(lhs_value.clone(), values.load(u32::from(*rhs))?)?;
        let term = values.mul(product, values.constant(u16::from(*slot))?)?;
        acc = values.add(acc, term)?;
    }
    Ok(acc)
}

/// Pairwise form `sum_{i,j} (lhs_i * rhs_j) * c_{i+j}` over 32-byte strides.
fn bilin7_pairwise<V: VmValues>(
    values: &V,
    mut acc: V::Value,
    lhs_base: u16,
    rhs_base: u16,
    coeffs: &[u8; VM_PAIRWISE_COEFFS],
) -> Result<V::Value, String> {
    for i in 0..VM_LIMBS {
        let lhs_value = values.load(u32::from(lhs_base) + VM_LIMB_STRIDE * i as u32)?;
        for j in 0..VM_LIMBS {
            let rhs_value = values.load(u32::from(rhs_base) + VM_LIMB_STRIDE * j as u32)?;
            let product = values.mul(lhs_value.clone(), rhs_value)?;
            let term = values.mul(product, values.constant(u16::from(coeffs[i + j]))?)?;
            acc = values.add(acc, term)?;
        }
    }
    Ok(acc)
}

/// Pop the cached top value.
fn pop<T>(stack: &mut Vec<T>, at: usize, name: &str) -> Result<T, String> {
    stack
        .pop()
        .ok_or_else(|| format!("{name} at program byte {at:#06x}: stack underflow"))
}

/// Evaluate the body of one interpreted identity (everything before its fold
/// opcode) exactly as the Yul interpreter does, returning the value that the
/// fold opcode would consume.
pub(crate) fn eval_vm_identity<V: VmValues>(
    body: &[VmInstruction],
    values: &V,
) -> Result<V::Value, String> {
    let mut stack: Vec<V::Value> = Vec::new();
    for instruction in body {
        let at = instruction.offset;
        let name = vm_mnemonic(instruction.opcode);
        match &instruction.op {
            VmOp::PushConst { slot, .. } => stack.push(values.constant(*slot)?),
            VmOp::PushMem { mem } => stack.push(load_mem(values, *mem)?),
            VmOp::Add => {
                let top = pop(&mut stack, at, &name)?;
                let next = pop(&mut stack, at, &name)?;
                stack.push(values.add(next, top)?);
            }
            VmOp::Mul => {
                let top = pop(&mut stack, at, &name)?;
                let next = pop(&mut stack, at, &name)?;
                stack.push(values.mul(next, top)?);
            }
            VmOp::Neg => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(values.neg(top)?);
            }
            VmOp::Pow5 => {
                let top = pop(&mut stack, at, &name)?;
                let square = values.mul(top.clone(), top.clone())?;
                let fourth = values.mul(square.clone(), square)?;
                stack.push(values.mul(top, fourth)?);
            }
            VmOp::AddConst { slot, .. } => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(values.add(top, values.constant(*slot)?)?);
            }
            VmOp::MulConst { slot, .. } => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(values.mul(top, values.constant(*slot)?)?);
            }
            VmOp::AddMem { ptr } => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(values.add(top, values.load(u32::from(*ptr))?)?);
            }
            VmOp::MulMem { ptr } => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(values.mul(top, values.load(u32::from(*ptr))?)?);
            }
            VmOp::AddMulMemMemConst { lhs, rhs, slot } => {
                let top = pop(&mut stack, at, &name)?;
                stack.push(add_product_times_const(
                    values,
                    top,
                    u32::from(*lhs),
                    u32::from(*rhs),
                    *slot,
                )?);
            }
            VmOp::AddMulConstMem { ptr, slot } => {
                let top = pop(&mut stack, at, &name)?;
                // Yul: mulmod(mload(ptr), const, r); the product commutes.
                stack.push(add_const_times_mem(values, top, *slot, *ptr)?);
            }
            VmOp::AddMulMemMem { lhs, rhs } => {
                let top = pop(&mut stack, at, &name)?;
                let product =
                    values.mul(values.load(u32::from(*lhs))?, values.load(u32::from(*rhs))?)?;
                stack.push(values.add(top, product)?);
            }
            VmOp::RunMemMemConst { terms } => {
                let mut top = pop(&mut stack, at, &name)?;
                for (lhs, rhs, slot) in terms {
                    top = add_product_times_const(
                        values,
                        top,
                        u32::from(*lhs),
                        u32::from(*rhs),
                        *slot,
                    )?;
                }
                stack.push(top);
            }
            VmOp::RunConstMem { terms } => {
                let mut top = pop(&mut stack, at, &name)?;
                for (ptr, slot) in terms {
                    top = add_const_times_mem(values, top, *slot, *ptr)?;
                }
                stack.push(top);
            }
            VmOp::AffineSum { lin, products } => {
                let mut top = pop(&mut stack, at, &name)?;
                for (ptr, slot) in lin {
                    top = add_const_times_mem(values, top, *slot, *ptr)?;
                }
                for (lhs, rhs, slot) in products {
                    top = add_product_times_const(
                        values,
                        top,
                        u32::from(*lhs),
                        u32::from(*rhs),
                        *slot,
                    )?;
                }
                stack.push(top);
            }
            VmOp::Lin7 { terms } => stack.push(lin7(values, values.zero(), terms)?),
            VmOp::Bilin7Row { lhs, terms } => {
                stack.push(bilin7_row(values, values.zero(), *lhs, terms)?)
            }
            VmOp::Bilin7Pairwise {
                lhs_base,
                rhs_base,
                coeffs,
            } => stack.push(bilin7_pairwise(
                values,
                values.zero(),
                *lhs_base,
                *rhs_base,
                coeffs,
            )?),
            VmOp::Modarith7(body) => {
                let mut acc = match body.constant {
                    Some(slot) => values.constant(u16::from(slot))?,
                    None => values.zero(),
                };
                for terms in &body.lin {
                    acc = lin7(values, acc, terms)?;
                }
                for (lhs, terms) in &body.rows {
                    acc = bilin7_row(values, acc, *lhs, terms)?;
                }
                for (lhs_base, rhs_base, coeffs) in &body.pairwise {
                    acc = bilin7_pairwise(values, acc, *lhs_base, *rhs_base, coeffs)?;
                }
                for (slot, ptr) in &body.mem {
                    acc = add_const_times_mem(values, acc, *slot, *ptr)?;
                }
                for (slot, lhs, rhs) in &body.products {
                    acc = add_product_times_const(
                        values,
                        acc,
                        u32::from(*lhs),
                        u32::from(*rhs),
                        *slot,
                    )?;
                }
                if let Some(cond) = body.cond {
                    acc = values.mul(values.load(u32::from(cond))?, acc)?;
                }
                stack.push(acc);
            }
            VmOp::FoldMain
            | VmOp::FoldSelector { .. }
            | VmOp::NativePermutation
            | VmOp::NativeLookup
            | VmOp::NativeIdentity { .. } => {
                return Err(format!(
                    "{name} at program byte {at:#06x} is an identity boundary inside an identity body"
                ));
            }
        }
    }
    if stack.len() != 1 {
        return Err(format!(
            "identity body leaves {} stack value(s), expected exactly one",
            stack.len()
        ));
    }
    Ok(stack.pop().expect("one stack value"))
}

/// Constant-table slots referenced by one instruction, in operand order.
pub(crate) fn vm_constant_refs(op: &VmOp) -> Vec<u16> {
    let limbs = |terms: &[VmLimbTerm; VM_LIMBS]| {
        terms.iter().map(|(slot, _)| u16::from(*slot)).collect::<Vec<_>>()
    };
    match op {
        VmOp::PushConst { slot, .. }
        | VmOp::AddConst { slot, .. }
        | VmOp::MulConst { slot, .. } => {
            vec![*slot]
        }
        VmOp::AddMulMemMemConst { slot, .. } | VmOp::AddMulConstMem { slot, .. } => {
            vec![u16::from(*slot)]
        }
        VmOp::RunMemMemConst { terms } => terms.iter().map(|(_, _, s)| u16::from(*s)).collect(),
        VmOp::RunConstMem { terms } => terms.iter().map(|(_, s)| u16::from(*s)).collect(),
        VmOp::AffineSum { lin, products } => lin
            .iter()
            .map(|(_, s)| u16::from(*s))
            .chain(products.iter().map(|(_, _, s)| u16::from(*s)))
            .collect(),
        VmOp::Lin7 { terms } | VmOp::Bilin7Row { terms, .. } => limbs(terms),
        VmOp::Bilin7Pairwise { coeffs, .. } => coeffs.iter().map(|s| u16::from(*s)).collect(),
        VmOp::Modarith7(body) => {
            let mut out = Vec::new();
            out.extend(body.constant.map(u16::from));
            for terms in &body.lin {
                out.extend(limbs(terms));
            }
            for (_, terms) in &body.rows {
                out.extend(limbs(terms));
            }
            for (_, _, coeffs) in &body.pairwise {
                out.extend(coeffs.iter().map(|s| u16::from(*s)));
            }
            out.extend(body.mem.iter().map(|(s, _)| u16::from(*s)));
            out.extend(body.products.iter().map(|(s, _, _)| u16::from(*s)));
            out
        }
        VmOp::PushMem { .. }
        | VmOp::Add
        | VmOp::Mul
        | VmOp::Neg
        | VmOp::Pow5
        | VmOp::AddMem { .. }
        | VmOp::MulMem { .. }
        | VmOp::AddMulMemMem { .. }
        | VmOp::FoldMain
        | VmOp::FoldSelector { .. }
        | VmOp::NativePermutation
        | VmOp::NativeLookup
        | VmOp::NativeIdentity { .. } => Vec::new(),
    }
}

/// Absolute memory pointers read by one instruction (tokens excluded),
/// including every limb of a pairwise-product base.
pub(crate) fn vm_pointer_refs(op: &VmOp) -> Vec<u32> {
    let limbs = |terms: &[VmLimbTerm; VM_LIMBS]| {
        terms.iter().map(|(_, p)| u32::from(*p)).collect::<Vec<_>>()
    };
    let base = |b: u16| (0..VM_LIMBS as u32).map(move |i| u32::from(b) + VM_LIMB_STRIDE * i);
    match op {
        VmOp::PushMem {
            mem: VmMem::Addr(addr),
        } => vec![*addr],
        VmOp::AddMem { ptr } | VmOp::MulMem { ptr } | VmOp::AddMulConstMem { ptr, .. } => {
            vec![u32::from(*ptr)]
        }
        VmOp::AddMulMemMemConst { lhs, rhs, .. } | VmOp::AddMulMemMem { lhs, rhs } => {
            vec![u32::from(*lhs), u32::from(*rhs)]
        }
        VmOp::RunMemMemConst { terms } => {
            terms.iter().flat_map(|(l, r, _)| [u32::from(*l), u32::from(*r)]).collect()
        }
        VmOp::RunConstMem { terms } => terms.iter().map(|(p, _)| u32::from(*p)).collect(),
        VmOp::AffineSum { lin, products } => lin
            .iter()
            .map(|(p, _)| u32::from(*p))
            .chain(products.iter().flat_map(|(l, r, _)| [u32::from(*l), u32::from(*r)]))
            .collect(),
        VmOp::Lin7 { terms } => limbs(terms),
        VmOp::Bilin7Row { lhs, terms } => {
            std::iter::once(u32::from(*lhs)).chain(limbs(terms)).collect()
        }
        VmOp::Bilin7Pairwise {
            lhs_base, rhs_base, ..
        } => base(*lhs_base).chain(base(*rhs_base)).collect(),
        VmOp::Modarith7(body) => {
            let mut out = Vec::new();
            out.extend(body.cond.map(u32::from));
            for terms in &body.lin {
                out.extend(limbs(terms));
            }
            for (lhs, terms) in &body.rows {
                out.push(u32::from(*lhs));
                out.extend(limbs(terms));
            }
            for (lhs_base, rhs_base, _) in &body.pairwise {
                out.extend(base(*lhs_base));
                out.extend(base(*rhs_base));
            }
            out.extend(body.mem.iter().map(|(_, p)| u32::from(*p)));
            out.extend(body.products.iter().flat_map(|(_, l, r)| [u32::from(*l), u32::from(*r)]));
            out
        }
        VmOp::PushMem { .. }
        | VmOp::PushConst { .. }
        | VmOp::Add
        | VmOp::Mul
        | VmOp::Neg
        | VmOp::Pow5
        | VmOp::AddConst { .. }
        | VmOp::MulConst { .. }
        | VmOp::FoldMain
        | VmOp::FoldSelector { .. }
        | VmOp::NativePermutation
        | VmOp::NativeLookup
        | VmOp::NativeIdentity { .. } => Vec::new(),
    }
}

/// Rewrite every absolute memory-pointer operand `p >= min_addr` to
/// `p + delta`, leaving opcodes, constant slots, counts, flags, tokens, token
/// offsets, selector indices, gaps and callback indices untouched.
///
/// Returns the rewritten program and the number of rewritten operands. This
/// is used to compare two programs whose verifier memory layouts differ by a
/// uniform shift (for example a VK payload that is one header word longer).
pub(crate) fn relocate_vm_pointers(
    bytes: &[u8],
    min_addr: u32,
    delta: i64,
) -> Result<(Vec<u8>, usize), String> {
    let instructions = decode_vm_program(bytes)?;
    let mut out = bytes.to_vec();
    let mut rewritten = 0usize;
    let patch16 = |out: &mut Vec<u8>, pos: usize, rewritten: &mut usize| -> Result<(), String> {
        let value = u32::from(u16::from_be_bytes([out[pos], out[pos + 1]]));
        if value < min_addr {
            return Ok(());
        }
        let moved = i64::from(value) + delta;
        let moved = u16::try_from(moved).map_err(|_| {
            format!(
                "relocated u16 pointer {value:#x} at program byte {pos:#06x} leaves the u16 range"
            )
        })?;
        out[pos..pos + 2].copy_from_slice(&moved.to_be_bytes());
        *rewritten += 1;
        Ok(())
    };
    for instruction in &instructions {
        let at = instruction.offset;
        match &instruction.op {
            VmOp::PushMem {
                mem: VmMem::Addr(addr),
            } if instruction.opcode == Q_OP_PUSH_MEM_LITERAL => {
                if *addr >= min_addr {
                    let moved = u32::try_from(i64::from(*addr) + delta).map_err(|_| {
                        format!(
                            "relocated u32 pointer {addr:#x} at program byte {at:#06x} underflows"
                        )
                    })?;
                    out[at + 1..at + 5].copy_from_slice(&moved.to_be_bytes());
                    rewritten += 1;
                }
            }
            VmOp::PushMem {
                mem: VmMem::Addr(_),
            }
            | VmOp::AddMem { .. }
            | VmOp::MulMem { .. } => patch16(&mut out, at + 1, &mut rewritten)?,
            VmOp::AddMulMemMemConst { .. } | VmOp::AddMulMemMem { .. } => {
                patch16(&mut out, at + 1, &mut rewritten)?;
                patch16(&mut out, at + 3, &mut rewritten)?;
            }
            VmOp::AddMulConstMem { .. } => patch16(&mut out, at + 1, &mut rewritten)?,
            VmOp::RunMemMemConst { terms } => {
                for k in 0..terms.len() {
                    let pos = at + 3 + 5 * k;
                    patch16(&mut out, pos, &mut rewritten)?;
                    patch16(&mut out, pos + 2, &mut rewritten)?;
                }
            }
            VmOp::RunConstMem { terms } => {
                for k in 0..terms.len() {
                    patch16(&mut out, at + 3 + 3 * k, &mut rewritten)?;
                }
            }
            VmOp::AffineSum { lin, products } => {
                let mut pos = at + 5;
                for _ in lin {
                    patch16(&mut out, pos, &mut rewritten)?;
                    pos += 3;
                }
                for _ in products {
                    patch16(&mut out, pos, &mut rewritten)?;
                    patch16(&mut out, pos + 2, &mut rewritten)?;
                    pos += 5;
                }
            }
            VmOp::Lin7 { .. } => {
                for k in 0..VM_LIMBS {
                    patch16(&mut out, at + 2 + 3 * k, &mut rewritten)?;
                }
            }
            VmOp::Bilin7Row { .. } => {
                patch16(&mut out, at + 1, &mut rewritten)?;
                for k in 0..VM_LIMBS {
                    patch16(&mut out, at + 4 + 3 * k, &mut rewritten)?;
                }
            }
            VmOp::Bilin7Pairwise { .. } => {
                patch16(&mut out, at + 1, &mut rewritten)?;
                patch16(&mut out, at + 3, &mut rewritten)?;
            }
            VmOp::Modarith7(body) => {
                let mut pos = at + 2;
                if body.cond.is_some() {
                    patch16(&mut out, pos, &mut rewritten)?;
                    pos += 2;
                }
                if body.constant.is_some() {
                    pos += 1;
                }
                pos += 5;
                for _ in &body.lin {
                    for _ in 0..VM_LIMBS {
                        patch16(&mut out, pos + 1, &mut rewritten)?;
                        pos += 3;
                    }
                }
                for _ in &body.rows {
                    patch16(&mut out, pos, &mut rewritten)?;
                    pos += 2;
                    for _ in 0..VM_LIMBS {
                        patch16(&mut out, pos + 1, &mut rewritten)?;
                        pos += 3;
                    }
                }
                for _ in &body.pairwise {
                    patch16(&mut out, pos, &mut rewritten)?;
                    patch16(&mut out, pos + 2, &mut rewritten)?;
                    pos += 4 + VM_PAIRWISE_COEFFS;
                }
                for _ in &body.mem {
                    patch16(&mut out, pos + 1, &mut rewritten)?;
                    pos += 3;
                }
                for _ in &body.products {
                    patch16(&mut out, pos + 1, &mut rewritten)?;
                    patch16(&mut out, pos + 3, &mut rewritten)?;
                    pos += 5;
                }
                debug_assert_eq!(pos, instruction.end());
            }
            VmOp::PushMem { .. }
            | VmOp::PushConst { .. }
            | VmOp::Add
            | VmOp::Mul
            | VmOp::Neg
            | VmOp::Pow5
            | VmOp::AddConst { .. }
            | VmOp::MulConst { .. }
            | VmOp::FoldMain
            | VmOp::FoldSelector { .. }
            | VmOp::NativePermutation
            | VmOp::NativeLookup
            | VmOp::NativeIdentity { .. } => {}
        }
    }
    // The rewrite must not change the instruction structure.
    let check = decode_vm_program(&out)?;
    if check.len() != instructions.len()
        || check
            .iter()
            .zip(&instructions)
            .any(|(a, b)| a.offset != b.offset || a.len != b.len)
    {
        return Err("pointer relocation changed the instruction structure".to_string());
    }
    Ok((out, rewritten))
}

/// Reduce a 256-bit word modulo the BLS12-381 scalar field order, matching
/// how `addmod`/`mulmod` consume a constant-table word.
pub(crate) fn fr_from_word(value: U256) -> midnight_curves::Fq {
    use ff::PrimeField;
    let modulus = fr_modulus();
    let reduced = value.reduce_mod(modulus);
    let repr = <midnight_curves::Fq as PrimeField>::Repr::from(reduced.to_le_bytes::<32>());
    Option::<midnight_curves::Fq>::from(midnight_curves::Fq::from_repr(repr))
        .expect("reduced word is canonical")
}

/// BLS12-381 scalar field order `r`.
pub(crate) fn fr_modulus() -> U256 {
    U256::from_str_radix(
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
        16,
    )
    .expect("valid modulus literal")
}
