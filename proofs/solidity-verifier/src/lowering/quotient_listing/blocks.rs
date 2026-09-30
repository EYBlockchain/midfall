// SPDX-License-Identifier: CC0-1.0
//! Program-block rendering shared by the generator listing and the auditor
//! regeneration tool.
//!
//! A *program block* is the listing text for one identity-stream item of the
//! compact quotient VM program: either one interpreted identity (its
//! instructions, every sub-term of the dynamic opcodes, and the identity
//! polynomial rebuilt from those bytes), or one native-callback marker. The
//! text of every block depends only on
//!
//! * the program bytes and constant-table words stored in the VK payload,
//! * the memory address of the first program byte, and
//! * the slot names and identity indices published in the manifest,
//!
//! so `examples/quotient_listing.rs` can re-derive it from a deployed VK and
//! the manifest without the generator. Rendering fails if the decoded lines
//! do not tile the program bytes exactly once.

use std::collections::{BTreeMap, BTreeSet};

use midnight_curves::Fq;
use ruint::aliases::U256;

use super::poly::{compact_fr, polynomial_lines, Poly};
use crate::lowering::quotient_numerator::vm::disasm::{
    decode_vm_program, eval_vm_identity, fr_from_word, relocate_vm_pointers, split_vm_items,
    vm_constant_refs, vm_mnemonic, vm_token_symbol, VmInstruction, VmItem, VmItemKind, VmLimbTerm,
    VmMem, VmOp, VmValues, VM_LIMBS, VM_LIMB_STRIDE, VM_MODARITH7_FLAG_COND,
    VM_MODARITH7_FLAG_CONST,
};

/// First line of every program block.
pub const PROGRAM_BLOCK_BEGIN: &str = "  >>> program ";
/// Last line of every program block.
pub const PROGRAM_BLOCK_END: &str = "  <<< program ";

/// Names used to print memory operands.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ListingSymbols {
    /// Absolute verifier memory address to slot name (`a_3_next`, `f_4`, ...).
    pub slots: BTreeMap<u32, String>,
    /// VM memory token byte to `(Yul symbol, absolute address)`.
    pub tokens: BTreeMap<u8, (String, u32)>,
}

impl ListingSymbols {
    /// Name of an absolute address, or `mem[0x....]` when it is not a
    /// published slot.
    pub fn name(&self, addr: u32) -> String {
        self.slots.get(&addr).cloned().unwrap_or_else(|| format!("mem[{addr:#06x}]"))
    }
}

/// Kind of one program block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramBlockKind {
    /// One interpreted identity ending in `FOLD_MAIN` / `FOLD_SELECTOR`.
    VmIdentity,
    /// `NATIVE_IDENTITY` marker with its callback index.
    NativeIdentity {
        /// Callback index encoded in the marker.
        index: u16,
    },
    /// `NATIVE_PERMUTATION` marker.
    NativePermutation,
    /// `NATIVE_LOOKUP` marker.
    NativeLookup,
}

impl ProgramBlockKind {
    /// Stable manifest/listing label.
    pub fn label(self) -> &'static str {
        match self {
            Self::VmIdentity => "vm_bytecode",
            Self::NativeIdentity { .. } => "native_gate_callback",
            Self::NativePermutation => "native_permutation",
            Self::NativeLookup => "native_lookup",
        }
    }
}

/// Fold opcode that ends an interpreted identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramFold {
    /// `A <- A*y + e`.
    Main,
    /// `A <- A*y; B_selector <- B_selector*y^gap + e`.
    Selector {
        /// Bucket index in the sorted simple-selector list.
        selector: u8,
        /// Codegen-known `y` gap since the bucket's previous identity.
        gap: u16,
    },
}

/// Rendered listing text and facts for one identity-stream item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramBlock {
    /// Item kind.
    pub kind: ProgramBlockKind,
    /// First program byte.
    pub byte_start: usize,
    /// Exclusive end byte.
    pub byte_end: usize,
    /// Global identity indices `j` executed by this item.
    pub identities: Vec<usize>,
    /// Constant-table slots referenced, sorted and deduplicated.
    pub constants_used: Vec<u16>,
    /// Fold of an interpreted identity.
    pub fold: Option<ProgramFold>,
    /// Maximum operand-stack depth inside the item.
    pub max_stack: usize,
    /// Number of monomials of the rebuilt polynomial, when expanded.
    pub monomials: Option<usize>,
    /// Block text, from the begin marker to the end marker (inclusive).
    pub text: String,
}

/// Format `[j..]` identity labels.
fn identity_label(identities: &[usize]) -> String {
    match identities {
        [] => "j=?".to_string(),
        [one] => format!("j={one}"),
        [first, .., last] if identities.windows(2).all(|w| w[1] == w[0] + 1) => {
            format!("j={first}..{last}")
        }
        many => format!(
            "j={}",
            many.iter().map(ToString::to_string).collect::<Vec<_>>().join(",")
        ),
    }
}

/// Begin-marker line of a block.
fn begin_line(kind: ProgramBlockKind, start: usize, end: usize, identities: &[usize]) -> String {
    format!(
        "{PROGRAM_BLOCK_BEGIN}[{start:#06x}, {end:#06x}) {} {}",
        kind.label(),
        identity_label(identities)
    )
}

/// End-marker line of a block.
fn end_line(start: usize, end: usize) -> String {
    format!("{PROGRAM_BLOCK_END}[{start:#06x}, {end:#06x})")
}

/// Values available while rendering: constant words and symbols.
struct RenderEnv<'a> {
    consts: &'a [Fq],
    symbols: &'a ListingSymbols,
}

impl RenderEnv<'_> {
    /// `c[i](readable)` for one constant slot.
    fn constant(&self, slot: u16) -> String {
        match self.consts.get(slot as usize) {
            Some(value) => format!("c[{slot}]={}", compact_fr(*value)),
            None => format!("c[{slot}](missing)"),
        }
    }

    /// Name of a `u16` pointer operand.
    fn ptr(&self, ptr: u16) -> String {
        self.symbols.name(u32::from(ptr))
    }

    /// Name and resolution of a token operand.
    fn token(&self, token: u8, offset: u32) -> String {
        let symbol = vm_token_symbol(token).unwrap_or("UNKNOWN_TOKEN");
        match self.symbols.tokens.get(&token) {
            Some((_, base)) => {
                let addr = base.wrapping_add(offset);
                if offset == 0 {
                    format!("{} (token {token:#04x} {symbol})", self.symbols.name(addr))
                } else {
                    format!(
                        "{} (token {token:#04x} {symbol} + {offset:#x})",
                        self.symbols.name(addr)
                    )
                }
            }
            None => format!("token {token:#04x} {symbol} + {offset:#x} (unresolved)"),
        }
    }

    /// Names of the seven limbs of a pairwise base.
    fn limbs(&self, base: u16) -> String {
        (0..VM_LIMBS as u32)
            .map(|i| self.symbols.name(u32::from(base) + VM_LIMB_STRIDE * i))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Accumulates listing lines and the byte spans they cover.
struct LineSink<'a> {
    program: &'a [u8],
    program_mptr: u32,
    lines: Vec<String>,
    spans: Vec<(usize, usize)>,
}

impl LineSink<'_> {
    /// Emit one line covering `len` program bytes at `offset`, grouped as
    /// `fields` (big-endian widths in bytes).
    fn bytes_line(&mut self, offset: usize, fields: &[usize], text: String) {
        let len: usize = fields.iter().sum();
        let mut hex = Vec::with_capacity(fields.len());
        let mut pos = offset;
        for width in fields {
            let field = self.program.get(pos..pos + width).unwrap_or(&[]);
            hex.push(field.iter().map(|b| format!("{b:02x}")).collect::<String>());
            pos += width;
        }
        let mem = self.program_mptr as usize + offset;
        self.lines.push(format!(
            "  {offset:04x}  {mem:#06x}  {:<30} {text}",
            hex.join(" ")
        ));
        self.spans.push((offset, len));
    }

    /// Emit an explanatory line that covers no program bytes.
    fn note_line(&mut self, text: String) {
        self.lines.push(format!("  {:<4}  {:<6}  {:<30} {text}", "", "", ""));
    }

    /// Emit a raw line (polynomial / markers).
    fn raw_line(&mut self, text: String) {
        self.lines.push(text);
    }
}

/// Mnemonic padded for alignment.
fn mnemonic(opcode: u8) -> String {
    format!("{:<28}", vm_mnemonic(opcode))
}

/// Render seven limb-term lines `| c * mem`, three bytes each.
fn limb_term_lines(
    sink: &mut LineSink<'_>,
    env: &RenderEnv<'_>,
    mut pos: usize,
    terms: &[VmLimbTerm; VM_LIMBS],
    prefix: &str,
    lhs: Option<&str>,
) -> usize {
    for (slot, ptr) in terms {
        let text = match lhs {
            Some(lhs) => format!(
                "{prefix}{lhs} * {} * {}",
                env.ptr(*ptr),
                env.constant(u16::from(*slot))
            ),
            None => format!(
                "{prefix}{} * {}",
                env.constant(u16::from(*slot)),
                env.ptr(*ptr)
            ),
        };
        sink.bytes_line(pos, &[1, 2], text);
        pos += 3;
    }
    pos
}

/// Render one instruction (and its sub-terms) into the sink.
fn render_instruction(
    sink: &mut LineSink<'_>,
    env: &RenderEnv<'_>,
    instruction: &VmInstruction,
    identities: &[usize],
) {
    let at = instruction.offset;
    let op = instruction.opcode;
    let name = mnemonic(op);
    match &instruction.op {
        VmOp::PushConst { slot, wide } => {
            let width = if *wide { 2 } else { 1 };
            sink.bytes_line(at, &[1, width], format!("{name} {}", env.constant(*slot)));
        }
        VmOp::PushMem { mem } => match mem {
            VmMem::Addr(addr) => {
                let width = if instruction.len == 5 { 4 } else { 2 };
                sink.bytes_line(at, &[1, width], format!("{name} {}", env.symbols.name(*addr)));
            }
            VmMem::Token(token) => {
                sink.bytes_line(at, &[1, 1], format!("{name} {}", env.token(*token, 0)));
            }
            VmMem::TokenOffset(token, offset) => {
                sink.bytes_line(at, &[1, 1, 4], format!("{name} {}", env.token(*token, *offset)));
            }
        },
        VmOp::Add => sink.bytes_line(at, &[1], format!("{name} top = next + top")),
        VmOp::Mul => sink.bytes_line(at, &[1], format!("{name} top = next * top")),
        VmOp::Neg => sink.bytes_line(at, &[1], format!("{name} top = -top")),
        VmOp::Pow5 => sink.bytes_line(at, &[1], format!("{name} top = top^5")),
        VmOp::AddConst { slot, wide } => {
            let width = if *wide { 2 } else { 1 };
            sink.bytes_line(at, &[1, width], format!("{name} top += {}", env.constant(*slot)));
        }
        VmOp::MulConst { slot, wide } => {
            let width = if *wide { 2 } else { 1 };
            sink.bytes_line(at, &[1, width], format!("{name} top *= {}", env.constant(*slot)));
        }
        VmOp::AddMem { ptr } => {
            sink.bytes_line(at, &[1, 2], format!("{name} top += {}", env.ptr(*ptr)))
        }
        VmOp::MulMem { ptr } => {
            sink.bytes_line(at, &[1, 2], format!("{name} top *= {}", env.ptr(*ptr)))
        }
        VmOp::AddMulMemMemConst { lhs, rhs, slot } => sink.bytes_line(
            at,
            &[1, 2, 2, 1],
            format!(
                "{name} top += {} * {} * {}",
                env.ptr(*lhs),
                env.ptr(*rhs),
                env.constant(u16::from(*slot))
            ),
        ),
        VmOp::AddMulConstMem { ptr, slot } => sink.bytes_line(
            at,
            &[1, 2, 1],
            format!(
                "{name} top += {} * {}",
                env.constant(u16::from(*slot)),
                env.ptr(*ptr)
            ),
        ),
        VmOp::AddMulMemMem { lhs, rhs } => sink.bytes_line(
            at,
            &[1, 2, 2],
            format!("{name} top += {} * {}", env.ptr(*lhs), env.ptr(*rhs)),
        ),
        VmOp::RunMemMemConst { terms } => {
            sink.bytes_line(at, &[1, 2], format!("{name} {} terms:", terms.len()));
            let mut pos = at + 3;
            for (lhs, rhs, slot) in terms {
                sink.bytes_line(
                    pos,
                    &[2, 2, 1],
                    format!(
                        "  | top += {} * {} * {}",
                        env.ptr(*lhs),
                        env.ptr(*rhs),
                        env.constant(u16::from(*slot))
                    ),
                );
                pos += 5;
            }
        }
        VmOp::RunConstMem { terms } => {
            sink.bytes_line(at, &[1, 2], format!("{name} {} terms:", terms.len()));
            let mut pos = at + 3;
            for (ptr, slot) in terms {
                sink.bytes_line(
                    pos,
                    &[2, 1],
                    format!(
                        "  | top += {} * {}",
                        env.constant(u16::from(*slot)),
                        env.ptr(*ptr)
                    ),
                );
                pos += 3;
            }
        }
        VmOp::AffineSum { lin, products } => {
            sink.bytes_line(
                at,
                &[1, 2, 2],
                format!(
                    "{name} {} linear + {} product terms:",
                    lin.len(),
                    products.len()
                ),
            );
            let mut pos = at + 5;
            for (ptr, slot) in lin {
                sink.bytes_line(
                    pos,
                    &[2, 1],
                    format!(
                        "  | lin  top += {} * {}",
                        env.constant(u16::from(*slot)),
                        env.ptr(*ptr)
                    ),
                );
                pos += 3;
            }
            for (lhs, rhs, slot) in products {
                sink.bytes_line(
                    pos,
                    &[2, 2, 1],
                    format!(
                        "  | prod top += {} * {} * {}",
                        env.ptr(*lhs),
                        env.ptr(*rhs),
                        env.constant(u16::from(*slot))
                    ),
                );
                pos += 5;
            }
        }
        VmOp::Lin7 { terms } => {
            sink.bytes_line(at, &[1], format!("{name} push sum of 7 terms:"));
            limb_term_lines(sink, env, at + 1, terms, "  | + ", None);
        }
        VmOp::Bilin7Row { lhs, terms } => {
            let lhs_name = env.ptr(*lhs);
            sink.bytes_line(
                at,
                &[1, 2],
                format!("{name} push {lhs_name} * (sum of 7 terms):"),
            );
            limb_term_lines(sink, env, at + 3, terms, "  | + ", Some(&lhs_name));
        }
        VmOp::Bilin7Pairwise {
            lhs_base,
            rhs_base,
            coeffs,
        } => {
            sink.bytes_line(
                at,
                &[1, 2, 2],
                format!("{name} push sum_(i,j<7) L_i * R_j * k_(i+j):"),
            );
            sink.bytes_line(
                at + 5,
                &[1; 13],
                format!(
                    "  | k_0..k_12 = {}",
                    coeffs
                        .iter()
                        .map(|slot| env.constant(u16::from(*slot)))
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
            );
            sink.note_line(format!("  | L = [{}]", env.limbs(*lhs_base)));
            sink.note_line(format!("  | R = [{}]", env.limbs(*rhs_base)));
        }
        VmOp::Modarith7(body) => {
            let mut fields = vec![1usize, 1];
            let mut header = Vec::new();
            if body.flags & VM_MODARITH7_FLAG_COND != 0 {
                fields.push(2);
            }
            if body.flags & VM_MODARITH7_FLAG_CONST != 0 {
                fields.push(1);
            }
            fields.extend([1, 1, 1, 1, 1]);
            if let Some(cond) = body.cond {
                header.push(format!("cond {}", env.ptr(cond)));
            }
            if let Some(slot) = body.constant {
                header.push(format!("seed {}", env.constant(u16::from(slot))));
            }
            header.push(format!(
                "lin={} row={} pair={} mem={} prod={}",
                body.lin.len(),
                body.rows.len(),
                body.pairwise.len(),
                body.mem.len(),
                body.products.len()
            ));
            let shape = match body.cond {
                Some(cond) => format!("push {} * (sum of the terms below):", env.ptr(cond)),
                None => "push (sum of the terms below):".to_string(),
            };
            sink.bytes_line(
                at,
                &fields,
                format!("{name} {} ; {shape}", header.join(", ")),
            );
            let mut pos = at + fields.iter().sum::<usize>();
            if let Some(slot) = body.constant {
                sink.note_line(format!("  | seed + {}", env.constant(u16::from(slot))));
            }
            for (block, terms) in body.lin.iter().enumerate() {
                sink.note_line(format!("  | LIN7 block {block}:"));
                pos = limb_term_lines(sink, env, pos, terms, "  |   + ", None);
            }
            for (block, (lhs, terms)) in body.rows.iter().enumerate() {
                let lhs_name = env.ptr(*lhs);
                sink.bytes_line(pos, &[2], format!("  | ROW7 block {block}: {lhs_name} * (...)"));
                pos += 2;
                pos = limb_term_lines(sink, env, pos, terms, "  |   + ", Some(&lhs_name));
            }
            for (block, (lhs_base, rhs_base, coeffs)) in body.pairwise.iter().enumerate() {
                sink.bytes_line(
                    pos,
                    &[2, 2],
                    format!("  | PAIR7 block {block}: sum_(i,j<7) L_i * R_j * k_(i+j)"),
                );
                pos += 4;
                sink.bytes_line(
                    pos,
                    &[1; 13],
                    format!(
                        "  |   k_0..k_12 = {}",
                        coeffs
                            .iter()
                            .map(|slot| env.constant(u16::from(*slot)))
                            .collect::<Vec<_>>()
                            .join(" ")
                    ),
                );
                pos += 13;
                sink.note_line(format!("  |   L = [{}]", env.limbs(*lhs_base)));
                sink.note_line(format!("  |   R = [{}]", env.limbs(*rhs_base)));
            }
            for (slot, ptr) in &body.mem {
                sink.bytes_line(
                    pos,
                    &[1, 2],
                    format!(
                        "  | mem  + {} * {}",
                        env.constant(u16::from(*slot)),
                        env.ptr(*ptr)
                    ),
                );
                pos += 3;
            }
            for (slot, lhs, rhs) in &body.products {
                sink.bytes_line(
                    pos,
                    &[1, 2, 2],
                    format!(
                        "  | prod + {} * {} * {}",
                        env.constant(u16::from(*slot)),
                        env.ptr(*lhs),
                        env.ptr(*rhs)
                    ),
                );
                pos += 5;
            }
        }
        VmOp::FoldMain => sink.bytes_line(
            at,
            &[1],
            format!("{name} A = A*y + e  ({})", identity_label(identities)),
        ),
        VmOp::FoldSelector { selector, gap } => sink.bytes_line(
            at,
            &[1, 1, 2],
            format!(
                "{name} bucket B{selector}, gap {gap}: A = A*y; B{selector} = B{selector}*y^{gap} + e  ({})",
                identity_label(identities)
            ),
        ),
        VmOp::NativePermutation => sink.bytes_line(
            at,
            &[1],
            format!(
                "{name} generated Yul permutation callback folds {}",
                identity_label(identities)
            ),
        ),
        VmOp::NativeLookup => sink.bytes_line(
            at,
            &[1],
            format!(
                "{name} generated Yul lookup callback folds {}",
                identity_label(identities)
            ),
        ),
        VmOp::NativeIdentity { index } => sink.bytes_line(
            at,
            &[1, 2],
            format!(
                "{name} generated Yul callback case {index} folds {}",
                identity_label(identities)
            ),
        ),
    }
}

/// Symbolic value domain: constants from the table, memory as variables.
pub(crate) struct SymbolicValues<'a> {
    /// Constant-table words reduced into Fr.
    pub(crate) consts: &'a [Fq],
    /// Token byte to resolved address.
    pub(crate) tokens: &'a BTreeMap<u8, u32>,
}

impl VmValues for SymbolicValues<'_> {
    type Value = Poly;

    fn zero(&self) -> Poly {
        Poly::zero()
    }

    fn constant(&self, slot: u16) -> Result<Poly, String> {
        self.consts
            .get(slot as usize)
            .map(|value| Poly::constant(*value))
            .ok_or_else(|| format!("constant slot c[{slot}] is outside the constant table"))
    }

    fn load(&self, addr: u32) -> Result<Poly, String> {
        Ok(Poly::var(addr))
    }

    fn token_addr(&self, token: u8) -> Result<u32, String> {
        self.tokens
            .get(&token)
            .copied()
            .ok_or_else(|| format!("memory token {token:#04x} has no published address"))
    }

    fn add(&self, lhs: Poly, rhs: Poly) -> Result<Poly, String> {
        lhs.add(rhs)
    }

    fn mul(&self, lhs: Poly, rhs: Poly) -> Result<Poly, String> {
        lhs.mul(&rhs)
    }

    fn neg(&self, value: Poly) -> Result<Poly, String> {
        Ok(value.neg())
    }
}

/// Decode, split, and check an item count against the published identities.
pub(crate) fn decode_items(program: &[u8]) -> Result<Vec<VmItem>, String> {
    let instructions = decode_vm_program(program)?;
    split_vm_items(&instructions)
}

/// Reduce constant-table words into Fr as `addmod`/`mulmod` consume them.
pub(crate) fn consts_to_fr(consts: &[U256]) -> Vec<Fq> {
    consts.iter().copied().map(fr_from_word).collect()
}

/// Rebuild the identity polynomial of one interpreted item from its bytes.
pub(crate) fn item_polynomial(
    item: &VmItem,
    consts: &[Fq],
    symbols: &ListingSymbols,
) -> Result<Poly, String> {
    let tokens = symbols
        .tokens
        .iter()
        .map(|(token, (_, addr))| (*token, *addr))
        .collect::<BTreeMap<_, _>>();
    eval_vm_identity(
        item.body(),
        &SymbolicValues {
            consts,
            tokens: &tokens,
        },
    )
}

/// Render every program block of a finalized quotient-VM program.
///
/// `item_identities[i]` lists the global identity indices executed by the
/// `i`-th identity-stream item in program order: one index for an
/// interpreted identity or a `NATIVE_IDENTITY` marker, the family range for a
/// `NATIVE_PERMUTATION` / `NATIVE_LOOKUP` marker. The function fails if the
/// program does not decode, violates the VM stack discipline, has a
/// different number of items, or if the rendered byte lines do not cover
/// every program byte exactly once.
pub fn render_program_blocks(
    program: &[u8],
    consts: &[U256],
    program_mptr: u32,
    symbols: &ListingSymbols,
    item_identities: &[Vec<usize>],
) -> Result<Vec<ProgramBlock>, String> {
    let items = decode_items(program)?;
    if items.len() != item_identities.len() {
        return Err(format!(
            "program decodes to {} identity-stream items but {} were published",
            items.len(),
            item_identities.len()
        ));
    }
    let consts = consts_to_fr(consts);
    let env = RenderEnv {
        consts: &consts,
        symbols,
    };
    let mut blocks = Vec::with_capacity(items.len());
    let mut all_spans = Vec::new();
    for (item, identities) in items.iter().zip(item_identities) {
        let kind = match item.kind {
            VmItemKind::Identity => ProgramBlockKind::VmIdentity,
            VmItemKind::NativeIdentity(index) => ProgramBlockKind::NativeIdentity { index },
            VmItemKind::NativePermutation => ProgramBlockKind::NativePermutation,
            VmItemKind::NativeLookup => ProgramBlockKind::NativeLookup,
        };
        let single = matches!(
            kind,
            ProgramBlockKind::VmIdentity | ProgramBlockKind::NativeIdentity { .. }
        );
        if (single && identities.len() != 1) || identities.is_empty() {
            return Err(format!(
                "{} item at program byte {:#06x} was published with identities {:?}",
                kind.label(),
                item.byte_start(),
                identities
            ));
        }
        let (start, end) = (item.byte_start(), item.byte_end());
        let mut sink = LineSink {
            program,
            program_mptr,
            lines: Vec::new(),
            spans: Vec::new(),
        };
        sink.raw_line(begin_line(kind, start, end, identities));
        for instruction in &item.instructions {
            render_instruction(&mut sink, &env, instruction, identities);
            // Every byte line of this instruction must stay inside it.
            let covered: usize = sink
                .spans
                .iter()
                .filter(|(off, _)| *off >= instruction.offset && *off < instruction.end())
                .map(|(_, len)| *len)
                .sum();
            if covered != instruction.len {
                return Err(format!(
                    "listing lines for {} at program byte {:#06x} cover {covered} of {} bytes",
                    vm_mnemonic(instruction.opcode),
                    instruction.offset,
                    instruction.len
                ));
            }
        }
        let mut fold = None;
        let mut monomials = None;
        if kind == ProgramBlockKind::VmIdentity {
            fold = match item.fold() {
                Some(VmOp::FoldMain) => Some(ProgramFold::Main),
                Some(VmOp::FoldSelector { selector, gap }) => Some(ProgramFold::Selector {
                    selector: *selector,
                    gap: *gap,
                }),
                _ => None,
            };
            let name_of = |addr: u32| symbols.name(addr);
            match item_polynomial(item, &consts, symbols) {
                Ok(poly) => {
                    monomials = Some(poly.len());
                    sink.raw_line(format!(
                        "      = polynomial rebuilt from the bytes above ({} monomial(s), degree {}):",
                        poly.len(),
                        poly.degree()
                    ));
                    for line in polynomial_lines(&poly, &name_of) {
                        sink.raw_line(format!("        {line}"));
                    }
                }
                Err(err) => {
                    sink.raw_line(format!("      = polynomial not expanded: {err}"));
                }
            }
        }
        sink.raw_line(end_line(start, end));
        let constants_used = item
            .instructions
            .iter()
            .flat_map(|instruction| vm_constant_refs(&instruction.op))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        all_spans.extend(sink.spans.iter().copied());
        blocks.push(ProgramBlock {
            kind,
            byte_start: start,
            byte_end: end,
            identities: identities.clone(),
            constants_used,
            fold,
            max_stack: item.max_depth,
            monomials,
            text: sink.lines.join("\n"),
        });
    }
    check_tiling(&all_spans, program.len())?;
    Ok(blocks)
}

/// Check that byte spans cover `[0, len)` exactly once, in order.
pub(crate) fn check_tiling(spans: &[(usize, usize)], len: usize) -> Result<(), String> {
    let mut cursor = 0usize;
    for (offset, span_len) in spans {
        if *offset != cursor {
            return Err(format!(
                "listing byte lines are not contiguous: expected a line at {cursor:#06x}, found {offset:#06x}"
            ));
        }
        if *span_len == 0 {
            return Err(format!("empty listing byte line at {offset:#06x}"));
        }
        cursor += span_len;
    }
    if cursor != len {
        return Err(format!(
            "listing byte lines cover {cursor} of {len} program bytes"
        ));
    }
    Ok(())
}

/// Extract every program block (begin to end marker, inclusive) from a
/// listing, in order.
pub fn extract_program_blocks(listing: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current: Option<Vec<&str>> = None;
    for line in listing.lines() {
        if line.starts_with(PROGRAM_BLOCK_BEGIN) {
            current = Some(vec![line]);
        } else if let Some(lines) = current.as_mut() {
            lines.push(line);
            if line.starts_with(PROGRAM_BLOCK_END) {
                blocks.push(lines.join("\n"));
                current = None;
            }
        }
    }
    blocks
}

/// Shift every absolute memory-pointer operand `>= min_addr` by `delta`
/// bytes, leaving everything else unchanged. Returns the rewritten program
/// and the number of operands rewritten.
///
/// Two verifier renders whose memory layouts differ only by a uniform shift
/// above `min_addr` (for example a VK payload with one extra header word)
/// produce programs related by exactly this rewrite.
pub fn relocate_program_pointers(
    program: &[u8],
    min_addr: u32,
    delta: i64,
) -> Result<(Vec<u8>, usize), String> {
    relocate_vm_pointers(program, min_addr, delta)
}

/// Readable form of a 256-bit constant-table word (`1`, `2^56`, `-1`,
/// `r - 0x…`), after reduction modulo the BLS12-381 scalar field order.
pub fn readable_constant(value: U256) -> String {
    super::poly::readable_fr(fr_from_word(value))
}
