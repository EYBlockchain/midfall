// SPDX-License-Identifier: CC0-1.0
//! Annotated quotient-VM listing and machine-readable identity manifest.
//!
//! The compact quotient VM stores most gate arithmetic as bytecode in the VK
//! payload. An auditor who reviews only the generated contracts cannot tell
//! from the Solidity which bytes implement which Halo2 gate polynomial. This
//! module produces two artifacts next to `Halo2Verifier.sol` /
//! `Halo2VerifyingKey.sol`:
//!
//! * a text listing, organised by identity `j` in
//!   `partially_evaluate_identities` order, with every decoded instruction, the
//!   rebuilt identity polynomial, the verbatim Yul of inline / native
//!   identities, and the constant table;
//! * a JSON manifest with the artifact hashes, payload/memory offsets, the
//!   per-identity execution plan, the constant table and the evaluation-slot
//!   map.
//!
//! Both are built from the program bytes and constant words exactly as they
//! are embedded in the VK payload (after run compaction and word packing),
//! decoded by the independent decoder in
//! `quotient_numerator::vm::disasm`. Rendering fails closed when:
//!
//! * the payload bytes differ from the builder's finalized program,
//! * the decoded lines do not tile every program byte exactly once,
//! * the identity stream does not execute `0..m-1` exactly once in order,
//! * an interpreted identity folds into the wrong bucket or with the wrong
//!   selector gap, reads memory that is not a published slot, or evaluates
//!   differently from `Expression::evaluate` of its gate polynomial at
//!   [`LISTING_VALIDATION_POINTS`] pseudo-random points (or, when both sides
//!   expand within the cap, has a different symbolic expansion).
//!
//! Scope of the check: it compares the pinned bytes with the Rust gate
//! expressions through a Rust interpreter of the VM ABI. It says nothing
//! about the Yul interpreter itself, whose semantics are covered by the EVM
//! differential tests, and nothing about the inline / native Yul snippets,
//! which are printed verbatim for review.

pub(crate) mod blocks;
pub(crate) mod json;
pub(crate) mod poly;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ff::{Field, FromUniformBytes};
use midnight_curves::Fq;
use midnight_proofs::plonk::{Any, Column, Expression};
use ruint::aliases::U256;
use sha3::{Digest, Keccak256};

use self::{
    blocks::{
        consts_to_fr, decode_items, item_polynomial, render_program_blocks, ListingSymbols,
        ProgramBlock, ProgramBlockKind, ProgramFold,
    },
    json::Json,
    poly::{readable_fr, Poly},
};
use crate::{
    api::QuotientIdentitySource,
    lowering::{
        encoding::{fe_to_u256, ConstraintSystemMeta, Data, Ptr, Value, Word},
        layout::memory::{VerifierMemoryLayout, WORD_BYTES},
        plan::LoweringPlan,
        quotient::QuotientComputationBlocks,
        quotient_numerator::vm::{
            disasm::{eval_vm_identity, vm_pointer_refs, VmItem, VmItemKind, VmValues},
            QuotientExecutionKind, QuotientExpr, QuotientIdentity, QuotientMem,
            QuotientProgramItem, QuotientTarget, QUOTIENT_MEM_TOKEN_TABLE,
        },
        VerifierBuildInputs,
    },
};

/// Number of pseudo-random memory images each interpreted identity is
/// evaluated on during translation validation.
pub(crate) const LISTING_VALIDATION_POINTS: usize = 4;
/// Manifest `format` string.
pub(crate) const MANIFEST_FORMAT: &str = "halo2_solidity_verifier/quotient-vm-manifest";
/// Manifest `format_version`.
pub(crate) const MANIFEST_FORMAT_VERSION: usize = 1;
/// Domain separator for the validation points.
const VALIDATION_DOMAIN: &[u8] = b"halo2_solidity_verifier/quotient-listing/validation/v1";

/// Render facts that influence the listing text.
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuotientListingContext {
    /// Whether the VK is rendered as a separate, codehash-pinned contract.
    pub(crate) separate_vk: bool,
    /// Whether quotient reconstruction runs in the pinned external evaluator.
    pub(crate) external_quotient: bool,
    /// Whether trace instrumentation is rendered into the Yul snippets.
    pub(crate) trace: bool,
}

/// Rendered listing and manifest.
#[derive(Clone, Debug)]
pub(crate) struct QuotientListingArtifacts {
    /// Human-readable listing.
    pub(crate) listing: String,
    /// JSON manifest.
    pub(crate) manifest: String,
}

/// One published evaluation / challenge / Lagrange slot.
#[derive(Clone, Debug)]
struct SlotInfo {
    addr: u32,
    name: String,
    kind: &'static str,
    column: Option<usize>,
    rotation: Option<i32>,
    index: Option<usize>,
    eval_index: Option<usize>,
    detail: String,
}

/// Outcome of the symbolic comparison of one interpreted identity.
#[derive(Clone, Debug)]
enum SymbolicOutcome {
    /// Both expansions succeeded and are identical.
    Equal(usize),
    /// At least one side exceeded the expansion cap.
    Skipped(String),
}

/// Per-identity translation-validation result.
#[derive(Clone, Debug)]
struct VmCheck {
    points: usize,
    symbolic: SymbolicOutcome,
    reference: &'static str,
}

/// Everything known about one identity after planning and decoding.
#[derive(Clone, Debug)]
struct IdentityRow {
    j: usize,
    source: QuotientIdentitySource,
    target: QuotientTarget,
    execution: QuotientExecutionKind,
    /// Program item executing this identity, when it has program bytes.
    item: Option<usize>,
    /// Position inside an inline / native / family range.
    local: usize,
    /// Size of that range.
    family_size: usize,
    check: Option<VmCheck>,
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Build and validate the quotient listing and manifest for a converged
    /// lowering plan.
    pub(crate) fn quotient_listing_artifacts(
        &self,
        plan: &LoweringPlan,
        ctx: QuotientListingContext,
    ) -> Result<QuotientListingArtifacts, String> {
        let model = ListingModel::build(self, plan, ctx)?;
        let listing = model.render_listing();
        // The regeneration tool compares these blocks one by one, so the
        // listing must contain every program block exactly once, in order.
        let shipped = blocks::extract_program_blocks(&listing);
        if shipped.len() != model.blocks.len()
            || shipped.iter().zip(&model.blocks).any(|(text, block)| *text != block.text)
        {
            return Err(format!(
                "listing text holds {} program blocks, the program has {}",
                shipped.len(),
                model.blocks.len()
            ));
        }
        let manifest = model.render_manifest(&listing);
        Ok(QuotientListingArtifacts { listing, manifest })
    }
}

/// Keccak-256 as a `0x`-prefixed hex string.
fn keccak_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Keccak256::digest(bytes).into();
    format!("0x{}", hex::encode(digest))
}

/// 32-byte big-endian encoding of a constant table.
fn const_table_bytes(consts: &[U256]) -> Vec<u8> {
    consts.iter().flat_map(|value| value.to_be_bytes::<32>()).collect()
}

/// Lower-case field literal padded to 64 hex digits.
fn word_hex(value: U256) -> String {
    format!("0x{value:064x}")
}

/// Resolve a generated memory symbol to its planned absolute address.
fn token_symbol_addr(name: &str, memory: &VerifierMemoryLayout) -> Option<u32> {
    let ptr = match name {
        "L_0_MPTR" => memory.l_0_mptr,
        "L_LAST_MPTR" => memory.l_last_mptr,
        "L_BLIND_MPTR" => memory.l_blind_mptr,
        "BETA_MPTR" => memory.beta_mptr,
        "GAMMA_MPTR" => memory.gamma_mptr,
        "X_MPTR" => memory.x_mptr,
        "THETA_MPTR" => memory.theta_mptr,
        "TRASH_CHALLENGE_MPTR" => memory.trash_challenge_mptr,
        "INSTANCE_EVAL_MPTR" => memory.instance_eval_mptr,
        _ => return None,
    };
    match ptr.value() {
        Value::Integer(addr) if addr >= 0 => u32::try_from(addr).ok(),
        _ => None,
    }
}

/// Short slot name for a memory token (`L_0_MPTR` -> `l_0`).
fn token_slot_name(symbol: &str) -> String {
    symbol.trim_end_matches("_MPTR").to_ascii_lowercase()
}

/// Resolve a generated pointer to an absolute memory address.
fn resolve_ptr(ptr: Ptr, memory: &VerifierMemoryLayout) -> Result<u32, String> {
    match ptr.value() {
        Value::Integer(addr) => {
            u32::try_from(addr).map_err(|_| format!("negative memory pointer {addr}"))
        }
        Value::Identifier(name, offset) => {
            let base = token_symbol_addr(name, memory)
                .ok_or_else(|| format!("memory symbol {name} has no planned address"))?;
            let offset =
                u32::try_from(offset).map_err(|_| format!("negative offset from {name}"))?;
            Ok(base + offset)
        }
    }
}

/// Resolve a memory-backed word.
fn resolve_word(word: Word, memory: &VerifierMemoryLayout) -> Result<u32, String> {
    resolve_ptr(word.ptr(), memory)
}

/// `_next`, `_prev`, `_nextK`, `_prevK` rotation suffixes.
fn rotation_suffix(rotation: i32) -> String {
    match rotation {
        0 => String::new(),
        1 => "_next".to_string(),
        -1 => "_prev".to_string(),
        r if r > 1 => format!("_next{r}"),
        r => format!("_prev{}", -r),
    }
}

/// Human description of a permutation column.
fn any_column_text(column: &Column<Any>) -> (String, usize) {
    let kind = match column.column_type() {
        Any::Advice(_) => "advice",
        Any::Fixed => "fixed",
        Any::Instance => "instance",
    };
    (kind.to_string(), column.index())
}

/// Published slots plus the VM token table (`token -> (symbol, address)`).
type SlotTables = (Vec<SlotInfo>, BTreeMap<u8, (String, u32)>);

/// Build the evaluation-slot map and token table from the planned data.
fn build_slots(
    meta: &ConstraintSystemMeta,
    data: &Data,
    memory: &VerifierMemoryLayout,
) -> Result<SlotTables, String> {
    let evals_base = resolve_ptr(memory.reversed_evals_mptr, memory)?;
    let evals_end = evals_base + (meta.num_evals * WORD_BYTES) as u32;
    let eval_index = |addr: u32| {
        (addr >= evals_base && addr < evals_end)
            .then(|| ((addr - evals_base) as usize) / WORD_BYTES)
    };
    let mut slots = Vec::new();
    let mut push = |addr: u32,
                    name: String,
                    kind: &'static str,
                    column: Option<usize>,
                    rotation: Option<i32>,
                    index: Option<usize>,
                    detail: String| {
        slots.push(SlotInfo {
            addr,
            name,
            kind,
            column,
            rotation,
            index,
            eval_index: eval_index(addr),
            detail,
        });
    };

    let sorted = |map: &HashMap<(usize, i32), Word>| {
        let mut entries = map.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>();
        entries.sort_by_key(|(k, _)| *k);
        entries
    };
    for ((col, rot), word) in sorted(&data.committed_instance_evals) {
        push(
            resolve_word(word, memory)?,
            format!("ci_{col}{}", rotation_suffix(rot)),
            "committed_instance",
            Some(col),
            Some(rot),
            None,
            format!("committed instance column {col} at rotation {rot}"),
        );
    }
    for ((col, rot), word) in sorted(&data.advice_evals) {
        push(
            resolve_word(word, memory)?,
            format!("a_{col}{}", rotation_suffix(rot)),
            "advice",
            Some(col),
            Some(rot),
            None,
            format!("advice column {col} at rotation {rot}"),
        );
    }
    for ((col, rot), word) in sorted(&data.fixed_evals) {
        push(
            resolve_word(word, memory)?,
            format!("f_{col}{}", rotation_suffix(rot)),
            "fixed",
            Some(col),
            Some(rot),
            None,
            format!("fixed column {col} at rotation {rot}"),
        );
    }
    for (idx, column) in meta.permutation_columns.iter().enumerate() {
        let word = data
            .permutation_evals
            .get(column)
            .copied()
            .ok_or_else(|| format!("permutation column {idx} has no sigma eval slot"))?;
        let (kind, col) = any_column_text(column);
        push(
            resolve_word(word, memory)?,
            format!("sigma_{idx}"),
            "permutation_sigma",
            Some(col),
            Some(0),
            Some(idx),
            format!("permutation sigma {idx} for {kind} column {col}"),
        );
    }
    for (set, (cur, next, last)) in data.permutation_z_evals.iter().enumerate() {
        push(
            resolve_word(*cur, memory)?,
            format!("perm_z_{set}"),
            "permutation_z",
            None,
            Some(0),
            Some(set),
            format!("permutation product z_{set}(x)"),
        );
        push(
            resolve_word(*next, memory)?,
            format!("perm_z_{set}_next"),
            "permutation_z",
            None,
            Some(1),
            Some(set),
            format!("permutation product z_{set}(omega x)"),
        );
        if let Some(last) = last {
            push(
                resolve_word(*last, memory)?,
                format!("perm_z_{set}_last"),
                "permutation_z",
                None,
                Some(meta.rotation_last),
                Some(set),
                format!("permutation product z_{set}(omega^last x)"),
            );
        }
    }
    for (lookup, (m, helpers, z, z_next)) in data.lookup_evals.iter().enumerate() {
        push(
            resolve_word(*m, memory)?,
            format!("lk{lookup}_m"),
            "lookup_multiplicity",
            None,
            Some(0),
            Some(lookup),
            format!("lookup {lookup} multiplicity m(x)"),
        );
        for (chunk, helper) in helpers.iter().enumerate() {
            push(
                resolve_word(*helper, memory)?,
                format!("lk{lookup}_h{chunk}"),
                "lookup_helper",
                None,
                Some(0),
                Some(lookup),
                format!("lookup {lookup} helper h_{chunk}(x)"),
            );
        }
        push(
            resolve_word(*z, memory)?,
            format!("lk{lookup}_z"),
            "lookup_accumulator",
            None,
            Some(0),
            Some(lookup),
            format!("lookup {lookup} accumulator Z(x)"),
        );
        push(
            resolve_word(*z_next, memory)?,
            format!("lk{lookup}_z_next"),
            "lookup_accumulator",
            None,
            Some(1),
            Some(lookup),
            format!("lookup {lookup} accumulator Z(omega x)"),
        );
    }
    for (idx, word) in data.trashcan_evals.iter().enumerate() {
        push(
            resolve_word(*word, memory)?,
            format!("trash_{idx}"),
            "trash",
            None,
            Some(0),
            Some(idx),
            format!("trash argument {idx} eval"),
        );
    }
    for (idx, word) in data.dummy_eval_words.iter().enumerate() {
        push(
            resolve_word(*word, memory)?,
            format!("dummy_{idx}"),
            "dummy",
            None,
            None,
            Some(idx),
            format!("fewer-point-sets dummy eval {idx}"),
        );
    }
    for (idx, word) in data.challenges.iter().enumerate() {
        push(
            resolve_word(*word, memory)?,
            format!("ch_{idx}"),
            "user_challenge",
            None,
            None,
            Some(idx),
            format!("user challenge {idx}"),
        );
    }
    let mut tokens = BTreeMap::new();
    for spec in QUOTIENT_MEM_TOKEN_TABLE {
        let addr = token_symbol_addr(spec.name, memory)
            .ok_or_else(|| format!("memory token {} has no planned address", spec.name))?;
        let name = token_slot_name(spec.name);
        let (kind, detail) = match spec.name {
            "L_0_MPTR" | "L_LAST_MPTR" | "L_BLIND_MPTR" => {
                ("lagrange", format!("{} (verifier-computed)", spec.name))
            }
            "INSTANCE_EVAL_MPTR" => (
                "instance",
                "non-committed instance column evaluation computed from calldata".to_string(),
            ),
            _ => ("challenge", format!("transcript challenge {}", spec.name)),
        };
        push(addr, name.clone(), kind, None, None, None, detail);
        tokens.insert(spec.token, (spec.name.to_string(), addr));
    }
    slots.sort_by_key(|slot| slot.addr);
    for pair in slots.windows(2) {
        if pair[0].addr == pair[1].addr {
            return Err(format!(
                "memory {:#06x} is published twice ({} and {})",
                pair[0].addr, pair[0].name, pair[1].name
            ));
        }
    }
    Ok((slots, tokens))
}

/// Numeric value domain over a pseudo-random memory image.
struct NumericValues<'a> {
    consts: &'a [Fq],
    mem: &'a BTreeMap<u32, Fq>,
    tokens: &'a BTreeMap<u8, u32>,
}

impl VmValues for NumericValues<'_> {
    type Value = Fq;

    fn zero(&self) -> Fq {
        Fq::ZERO
    }

    fn constant(&self, slot: u16) -> Result<Fq, String> {
        self.consts
            .get(slot as usize)
            .copied()
            .ok_or_else(|| format!("constant slot c[{slot}] is outside the constant table"))
    }

    fn load(&self, addr: u32) -> Result<Fq, String> {
        self.mem.get(&addr).copied().ok_or_else(|| {
            format!("reads memory {addr:#06x}, which is not a published evaluation slot")
        })
    }

    fn token_addr(&self, token: u8) -> Result<u32, String> {
        self.tokens
            .get(&token)
            .copied()
            .ok_or_else(|| format!("memory token {token:#04x} has no planned address"))
    }

    fn add(&self, lhs: Fq, rhs: Fq) -> Result<Fq, String> {
        Ok(lhs + rhs)
    }

    fn mul(&self, lhs: Fq, rhs: Fq) -> Result<Fq, String> {
        Ok(lhs * rhs)
    }

    fn neg(&self, value: Fq) -> Result<Fq, String> {
        Ok(-value)
    }
}

/// Deterministic pseudo-random memory image for one validation point.
fn validation_image(seed: &[u8; 32], point: usize, addrs: &[u32]) -> BTreeMap<u32, Fq> {
    addrs
        .iter()
        .map(|addr| {
            let mut wide = [0u8; 64];
            for (half, chunk) in wide.chunks_mut(32).enumerate() {
                let mut hasher = Keccak256::new();
                hasher.update(seed);
                hasher.update((point as u64).to_be_bytes());
                hasher.update(addr.to_be_bytes());
                hasher.update([half as u8]);
                chunk.copy_from_slice(&hasher.finalize());
            }
            (*addr, Fq::from_uniform_bytes(&wide))
        })
        .collect()
}

/// How the generated verifier binds Halo2 query leaves to memory.
struct ExprEnv<'a> {
    meta: &'a ConstraintSystemMeta,
    data: &'a Data,
    memory: &'a VerifierMemoryLayout,
}

impl ExprEnv<'_> {
    /// Fixed query address, or `None` for a simple-selector column (which
    /// `partially_evaluate_identities` treats as the constant one).
    fn fixed(&self, col: usize, rot: i32) -> Result<Option<u32>, String> {
        if self.meta.simple_selector_cols.contains(&col) {
            return Ok(None);
        }
        let word = self
            .data
            .fixed_evals
            .get(&(col, rot))
            .ok_or_else(|| format!("fixed query ({col}, {rot}) has no eval slot"))?;
        resolve_word(*word, self.memory).map(Some)
    }

    /// Advice query address.
    fn advice(&self, col: usize, rot: i32) -> Result<u32, String> {
        let word = self
            .data
            .advice_evals
            .get(&(col, rot))
            .ok_or_else(|| format!("advice query ({col}, {rot}) has no eval slot"))?;
        resolve_word(*word, self.memory)
    }

    /// Instance query address (committed eval or the computed instance eval).
    fn instance(&self, col: usize, rot: i32) -> Result<u32, String> {
        if col < self.meta.num_committed_instances {
            let word =
                self.data.committed_instance_evals.get(&(col, rot)).ok_or_else(|| {
                    format!("committed instance query ({col}, {rot}) has no slot")
                })?;
            resolve_word(*word, self.memory)
        } else {
            resolve_word(self.data.instance_eval, self.memory)
        }
    }

    /// User challenge address.
    fn challenge(&self, idx: usize) -> Result<u32, String> {
        let word = self
            .data
            .challenges
            .get(idx)
            .ok_or_else(|| format!("challenge {idx} has no slot"))?;
        resolve_word(*word, self.memory)
    }
}

/// Evaluate a Halo2 expression with `Expression::evaluate`, binding leaves
/// through the generator's slot map. `leaf` maps a memory address (or `None`
/// for the constant one) into the value domain.
fn eval_expression<T: Clone>(
    expr: &Expression<Fq>,
    env: &ExprEnv<'_>,
    constant: &dyn Fn(Fq) -> Result<T, String>,
    leaf: &dyn Fn(u32) -> Result<T, String>,
    add: &dyn Fn(T, T) -> Result<T, String>,
    mul: &dyn Fn(T, T) -> Result<T, String>,
    neg: &dyn Fn(T) -> Result<T, String>,
) -> Result<T, String> {
    expr.evaluate(
        &|scalar| constant(scalar),
        &|_selector| Err("virtual selector left in a gate polynomial".to_string()),
        &|query| match env.fixed(query.column_index(), query.rotation().0)? {
            Some(addr) => leaf(addr),
            None => constant(Fq::ONE),
        },
        &|query| leaf(env.advice(query.column_index(), query.rotation().0)?),
        &|query| leaf(env.instance(query.column_index(), query.rotation().0)?),
        &|challenge| leaf(env.challenge(challenge.index())?),
        &|inner| neg(inner?),
        &|lhs, rhs| add(lhs?, rhs?),
        &|lhs, rhs| mul(lhs?, rhs?),
        &|inner, scalar| mul(inner?, constant(scalar)?),
    )
}

/// Evaluate the generator's typed expression (used only for non-gate
/// identities that are interpreted by the VM).
fn eval_quotient_expr<T: Clone>(
    expr: &QuotientExpr,
    tokens: &BTreeMap<u8, u32>,
    constant: &dyn Fn(Fq) -> Result<T, String>,
    leaf: &dyn Fn(u32) -> Result<T, String>,
    add: &dyn Fn(T, T) -> Result<T, String>,
    mul: &dyn Fn(T, T) -> Result<T, String>,
    neg: &dyn Fn(T) -> Result<T, String>,
) -> Result<T, String> {
    let rec = |e: &QuotientExpr| eval_quotient_expr(e, tokens, constant, leaf, add, mul, neg);
    match expr {
        QuotientExpr::Const(value) => {
            constant(crate::lowering::quotient_numerator::vm::disasm::fr_from_word(*value))
        }
        QuotientExpr::Mem(QuotientMem::Literal(addr)) => leaf(*addr),
        QuotientExpr::Mem(QuotientMem::Token(token)) => {
            leaf(*tokens.get(token).ok_or_else(|| format!("token {token:#04x} unresolved"))?)
        }
        QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => leaf(
            tokens.get(token).ok_or_else(|| format!("token {token:#04x} unresolved"))? + offset,
        ),
        QuotientExpr::Add(lhs, rhs) => add(rec(lhs)?, rec(rhs)?),
        QuotientExpr::Mul(lhs, rhs) => mul(rec(lhs)?, rec(rhs)?),
        QuotientExpr::Neg(inner) => neg(rec(inner)?),
    }
}

/// Human description of an identity source.
fn source_text(source: &QuotientIdentitySource) -> String {
    match source {
        QuotientIdentitySource::Gate {
            gate_index,
            gate_name,
            constraint_name,
            polynomial_index,
            ..
        } => {
            if constraint_name.is_empty() {
                format!("gate {gate_index} '{gate_name}' polynomial {polynomial_index}")
            } else {
                format!(
                    "gate {gate_index} '{gate_name}' polynomial {polynomial_index} (constraint '{constraint_name}')"
                )
            }
        }
        QuotientIdentitySource::Permutation { identity_index } => {
            format!("permutation identity {identity_index}")
        }
        QuotientIdentitySource::Lookup {
            identity_index,
            lookup_index,
            lookup_name,
        } => format!("lookup {lookup_index} ('{lookup_name}') identity {identity_index}"),
        QuotientIdentitySource::Trash {
            trash_index,
            trash_name,
        } => format!("trash {trash_index} ('{trash_name}')"),
    }
}

/// Stable execution-kind label (manifest `execution.kind`).
fn execution_label(kind: QuotientExecutionKind) -> &'static str {
    match kind {
        QuotientExecutionKind::Inline => "inline_direct_prefix",
        QuotientExecutionKind::Interpreted => "vm_bytecode",
        QuotientExecutionKind::NativeIdentity { .. } => "native_gate_callback",
        QuotientExecutionKind::NativePermutation => "native_permutation",
        QuotientExecutionKind::NativeLookup => "native_lookup",
        QuotientExecutionKind::StructuredTail => "trash_suffix",
    }
}

/// Human execution-kind description.
fn execution_text(kind: QuotientExecutionKind) -> String {
    match kind {
        QuotientExecutionKind::Inline => {
            "inline direct prefix (Yul before the VM loop)".to_string()
        }
        QuotientExecutionKind::Interpreted => "VM bytecode".to_string(),
        QuotientExecutionKind::NativeIdentity { native_index } => {
            format!("native gate callback #{native_index} (NATIVE_IDENTITY)")
        }
        QuotientExecutionKind::NativePermutation => {
            "native permutation callback (NATIVE_PERMUTATION)".to_string()
        }
        QuotientExecutionKind::NativeLookup => "native lookup callback (NATIVE_LOOKUP)".to_string(),
        QuotientExecutionKind::StructuredTail => {
            "trash suffix (structured Yul after the VM loop)".to_string()
        }
    }
}

/// Converged facts plus decoded program, ready for rendering.
struct ListingModel<'a> {
    ctx: QuotientListingContext,
    plan: &'a LoweringPlan,
    inputs: &'a VerifierBuildInputs<'a, 'a>,
    payload_len: usize,
    runtime_len: usize,
    codehash: String,
    payload_keccak: String,
    vk_mptr: usize,
    header_words: usize,
    const_offset_words: usize,
    const_reserved_words: usize,
    consts: Vec<U256>,
    consts_fr: Vec<Fq>,
    const_refs: Vec<usize>,
    program_offset_words: usize,
    program_words: usize,
    program: Vec<u8>,
    program_mptr: usize,
    const_mptr: usize,
    slots: Vec<SlotInfo>,
    symbols: ListingSymbols,
    rows: Vec<IdentityRow>,
    blocks: Vec<ProgramBlock>,
    yul: QuotientComputationBlocks,
    seed: [u8; 32],
    sorted_simple: Vec<usize>,
    expected_gaps: Vec<Option<usize>>,
    tails: Vec<usize>,
}

impl<'a> ListingModel<'a> {
    /// Extract, decode, cross-check and validate.
    fn build(
        inputs: &'a VerifierBuildInputs<'a, 'a>,
        plan: &'a LoweringPlan,
        ctx: QuotientListingContext,
    ) -> Result<Self, String> {
        let vk = &plan.vk;
        let payload = vk.bytes();
        let runtime = vk.runtime_bytes();
        let codehash = keccak_hex(&runtime);
        let payload_keccak = keccak_hex(&payload);
        let vk_mptr = vk_mptr_usize(plan)?;
        let const_offset_words =
            vk.quotient_const_offset_words.ok_or("VK carries no quotient constant table")?;
        let program_offset_words =
            vk.quotient_program_offset_words.ok_or("VK carries no quotient program")?;
        let const_reserved_words = vk.quotient_const_words;
        let program_words = vk.quotient_program_words;
        let program_len = plan.quotient.program.len;
        let const_count = plan.quotient.build.consts.len();

        // Constant table as embedded in the payload.
        let word_at = |word: usize| -> Result<U256, String> {
            let start = word * WORD_BYTES;
            payload
                .get(start..start + WORD_BYTES)
                .map(U256::from_be_slice)
                .ok_or_else(|| format!("VK payload word {word} is out of range"))
        };
        if const_count > const_reserved_words {
            return Err(format!(
                "{const_count} quotient constants exceed the {const_reserved_words} reserved VK words"
            ));
        }
        let consts = (0..const_count)
            .map(|i| word_at(const_offset_words + i))
            .collect::<Result<Vec<_>, _>>()?;
        for i in const_count..const_reserved_words {
            if word_at(const_offset_words + i)? != U256::ZERO {
                return Err(format!(
                    "reserved quotient constant word {i} is not zero in the VK payload"
                ));
            }
        }
        // Program bytes as embedded in the payload (strip zero padding only).
        let program_start = program_offset_words * WORD_BYTES;
        let program_capacity = program_words * WORD_BYTES;
        if program_len > program_capacity {
            return Err(format!(
                "program length {program_len} exceeds its {program_words} packed VK words"
            ));
        }
        let packed = payload
            .get(program_start..program_start + program_capacity)
            .ok_or("quotient program words are outside the VK payload")?;
        if packed[program_len..].iter().any(|byte| *byte != 0) {
            return Err(
                "quotient program padding bytes in the VK payload are not zero".to_string(),
            );
        }
        let program = packed[..program_len].to_vec();
        if program != plan.quotient.build.bytes {
            return Err(
                "quotient program bytes in the VK payload differ from the finalized build"
                    .to_string(),
            );
        }
        if consts != plan.quotient.build.consts {
            return Err(
                "quotient constant table in the VK payload differs from the finalized build"
                    .to_string(),
            );
        }
        let program_mptr = plan.quotient.program.program_mptr;
        let const_mptr = plan.quotient.program.const_mptr;
        if program_mptr != vk_mptr + program_start
            || const_mptr != vk_mptr + const_offset_words * WORD_BYTES
        {
            return Err(format!(
                "quotient memory pointers disagree with the VK layout: program {program_mptr:#x}, constants {const_mptr:#x}, VK_MPTR {vk_mptr:#x}"
            ));
        }
        let header_words = const_offset_words;

        // Identity stream from the existing execution manifest.
        let qplan = &plan.quotient.plan;
        let execution = qplan.execution_manifest()?;
        let m = execution.len();
        for (pos, entry) in execution.iter().enumerate() {
            if entry.global_index != pos {
                return Err(format!(
                    "identity stream position {pos} executes identity {} (expected each of 0..{} exactly once, in order)",
                    entry.global_index,
                    m.saturating_sub(1)
                ));
            }
        }
        let protocol = &plan.meta.protocol.quotient;
        let expected_m = protocol.gates + protocol.permutation + protocol.lookup + protocol.trash;
        if m != expected_m {
            return Err(format!(
                "identity stream has {m} identities, protocol plan expects {expected_m}"
            ));
        }

        // Decode the embedded bytes and match items with the plan.
        let items = decode_items(&program)?;
        if items.len() != qplan.items.len() {
            return Err(format!(
                "program decodes to {} identity-stream items, the execution plan has {}",
                items.len(),
                qplan.items.len()
            ));
        }
        let mut item_identities = Vec::with_capacity(items.len());
        let mut order = qplan
            .inline_identities
            .iter()
            .map(|identity| identity.meta.global_index)
            .collect::<Vec<_>>();
        for (idx, (item, planned)) in items.iter().zip(&qplan.items).enumerate() {
            let ids = match (item.kind, planned) {
                (VmItemKind::Identity, QuotientProgramItem::Identity(identity)) => {
                    vec![identity.meta.global_index]
                }
                (VmItemKind::NativeIdentity(index), QuotientProgramItem::NativeIdentity(planned))
                    if usize::from(index) == *planned =>
                {
                    vec![qplan
                        .native_identities
                        .get(*planned)
                        .ok_or_else(|| format!("native callback {planned} has no identity"))?
                        .meta
                        .global_index]
                }
                (VmItemKind::NativePermutation, QuotientProgramItem::NativePermutation) => qplan
                    .native_permutation_identities
                    .iter()
                    .map(|identity| identity.meta.global_index)
                    .collect(),
                (VmItemKind::NativeLookup, QuotientProgramItem::NativeLookup) => qplan
                    .native_lookup_identities
                    .iter()
                    .map(|identity| identity.meta.global_index)
                    .collect(),
                (decoded, _) => {
                    return Err(format!(
                        "program item {idx} at byte {:#06x} decodes as {decoded:?} but the execution plan has a different item there",
                        item.byte_start()
                    ))
                }
            };
            order.extend(ids.iter().copied());
            item_identities.push(ids);
        }
        order.extend(
            qplan
                .structured_tail_identities
                .iter()
                .map(|identity| identity.meta.global_index),
        );
        if order != (0..m).collect::<Vec<_>>() {
            return Err(format!(
                "decoded program plus inline/tail identities do not execute 0..{} exactly once in order: {order:?}",
                m.saturating_sub(1)
            ));
        }

        // Slots and symbols.
        let (slots, tokens) = build_slots(&plan.meta, &plan.data, &plan.memory)?;
        let symbols = ListingSymbols {
            slots: slots.iter().map(|slot| (slot.addr, slot.name.clone())).collect(),
            tokens: tokens.clone(),
        };
        let blocks = render_program_blocks(
            &program,
            &consts,
            u32::try_from(program_mptr).map_err(|_| "program pointer exceeds u32")?,
            &symbols,
            &item_identities,
        )?;
        let consts_fr = consts_to_fr(&consts);
        let mut const_refs = vec![0usize; consts.len()];
        for item in &items {
            for instruction in &item.instructions {
                for slot in crate::lowering::quotient_numerator::vm::disasm::vm_constant_refs(
                    &instruction.op,
                ) {
                    let entry = const_refs.get_mut(slot as usize).ok_or_else(|| {
                        format!(
                            "instruction at program byte {:#06x} references constant c[{slot}] outside the {}-entry table",
                            instruction.offset,
                            consts.len()
                        )
                    })?;
                    *entry += 1;
                }
            }
        }

        // Expected selector gaps and tails from the identity order alone.
        let sorted_simple = plan.quotient.sorted_simple.clone();
        let mut last_in_bucket: HashMap<usize, usize> = HashMap::new();
        let mut expected_gaps = vec![None; m];
        for entry in &execution {
            if let QuotientTarget::Selector(bucket) = entry.target {
                let gap = last_in_bucket.get(&bucket).map_or(0, |prev| entry.global_index - prev);
                expected_gaps[entry.global_index] = Some(gap);
                last_in_bucket.insert(bucket, entry.global_index);
            }
        }
        let tails = (0..sorted_simple.len())
            .map(|bucket| last_in_bucket.get(&bucket).map_or(0, |last| m - 1 - last))
            .collect::<Vec<_>>();

        // Rows.
        let mut item_of = HashMap::new();
        for (idx, ids) in item_identities.iter().enumerate() {
            for (local, j) in ids.iter().enumerate() {
                item_of.insert(*j, (idx, local, ids.len()));
            }
        }
        let family_len = |kind: QuotientExecutionKind| {
            execution.iter().filter(|entry| entry.execution == kind).count()
        };
        let mut rows = Vec::with_capacity(m);
        let mut family_seen: HashMap<&'static str, usize> = HashMap::new();
        for entry in &execution {
            let (item, local, family_size) = match entry.execution {
                QuotientExecutionKind::Inline | QuotientExecutionKind::StructuredTail => {
                    let label = execution_label(entry.execution);
                    let seen = family_seen.entry(label).or_insert(0);
                    let local = *seen;
                    *seen += 1;
                    (None, local, family_len(entry.execution))
                }
                _ => {
                    let (idx, local, size) =
                        item_of.get(&entry.global_index).copied().ok_or_else(|| {
                            format!("identity {} has no program item", entry.global_index)
                        })?;
                    (Some(idx), local, size)
                }
            };
            rows.push(IdentityRow {
                j: entry.global_index,
                source: entry.source.clone(),
                target: entry.target,
                execution: entry.execution,
                item,
                local,
                family_size,
                check: None,
            });
        }

        let seed: [u8; 32] = {
            let mut hasher = Keccak256::new();
            hasher.update(VALIDATION_DOMAIN);
            hasher.update(&program);
            hasher.update(const_table_bytes(&consts));
            hasher.finalize().into()
        };

        let yul = inputs.compact_quotient_computation_blocks(
            &plan.meta,
            &plan.data,
            qplan,
            plan.quotient.stack_mptr,
            plan.quotient.state_slots,
            ctx.trace,
        );

        let mut model = Self {
            ctx,
            plan,
            inputs,
            payload_len: payload.len(),
            runtime_len: runtime.len(),
            codehash,
            payload_keccak,
            vk_mptr,
            header_words,
            const_offset_words,
            const_reserved_words,
            consts,
            consts_fr,
            const_refs,
            program_offset_words,
            program_words,
            program,
            program_mptr,
            const_mptr,
            slots,
            symbols,
            rows,
            blocks,
            yul,
            seed,
            sorted_simple,
            expected_gaps,
            tails,
        };
        model.validate_vm_identities(&items)?;
        Ok(model)
    }

    /// Translation validation of every interpreted identity.
    fn validate_vm_identities(&mut self, items: &[VmItem]) -> Result<(), String> {
        let qplan = &self.plan.quotient.plan;
        let env = ExprEnv {
            meta: &self.plan.meta,
            data: &self.plan.data,
            memory: &self.plan.memory,
        };
        let tokens = self
            .symbols
            .tokens
            .iter()
            .map(|(token, (_, addr))| (*token, *addr))
            .collect::<BTreeMap<_, _>>();
        let addrs = self.slots.iter().map(|slot| slot.addr).collect::<Vec<_>>();
        let images = (0..LISTING_VALIDATION_POINTS)
            .map(|point| validation_image(&self.seed, point, &addrs))
            .collect::<Vec<_>>();
        let published = addrs.iter().copied().collect::<BTreeSet<_>>();
        let cs = self.inputs.vk.cs();

        for (idx, (item, planned)) in items.iter().zip(&qplan.items).enumerate() {
            let QuotientProgramItem::Identity(identity) = planned else {
                continue;
            };
            let j = identity.meta.global_index;
            let context = || {
                format!(
                    "quotient listing validation failed for identity j={j} ({}), VM bytes [{:#06x}, {:#06x})",
                    source_text(&identity.meta.source),
                    item.byte_start(),
                    item.byte_end()
                )
            };

            // Fold target and selector gap.
            let expected_fold = match identity.target {
                QuotientTarget::Main => ProgramFold::Main,
                QuotientTarget::Selector(bucket) => ProgramFold::Selector {
                    selector: u8::try_from(bucket)
                        .map_err(|_| format!("{}: bucket index {bucket} exceeds u8", context()))?,
                    gap: u16::try_from(self.expected_gaps[j].unwrap_or(0))
                        .map_err(|_| format!("{}: selector gap exceeds u16", context()))?,
                },
            };
            let actual_fold = self.blocks[idx].fold;
            if actual_fold != Some(expected_fold) {
                return Err(format!(
                    "{}: fold is {actual_fold:?}, expected {expected_fold:?} for bucket {:?}",
                    context(),
                    identity.target
                ));
            }
            // Every pointer read must be a published slot.
            for instruction in item.body() {
                for addr in vm_pointer_refs(&instruction.op) {
                    if !published.contains(&addr) {
                        return Err(format!(
                            "{}: instruction at {:#06x} reads memory {addr:#06x}, which is not a published evaluation slot",
                            context(),
                            instruction.offset
                        ));
                    }
                }
            }

            // Numeric check at pseudo-random points.
            let reference = VmReference::for_identity(identity, cs)?;
            for (point, image) in images.iter().enumerate() {
                let values = NumericValues {
                    consts: &self.consts_fr,
                    mem: image,
                    tokens: &tokens,
                };
                let vm = eval_vm_identity(item.body(), &values)
                    .map_err(|err| format!("{}: {err}", context()))?;
                let expected = reference
                    .numeric(&env, &tokens, image)
                    .map_err(|err| format!("{}: reference evaluation failed: {err}", context()))?;
                if vm != expected {
                    return Err(format!(
                        "{}: VM bytes evaluate to {} but {} gives {} at validation point {point}",
                        context(),
                        word_hex(fe_to_u256::<Fq>(&vm)),
                        reference.label(),
                        word_hex(fe_to_u256::<Fq>(&expected))
                    ));
                }
            }

            // Symbolic comparison when both sides expand within the cap.
            let vm_poly = item_polynomial(item, &self.consts_fr, &self.symbols);
            let ref_poly = reference.symbolic(&env, &tokens);
            let symbolic = match (vm_poly, ref_poly) {
                (Ok(vm_poly), Ok(ref_poly)) => {
                    if vm_poly != ref_poly {
                        return Err(format!(
                            "{}: symbolic expansion of the VM bytes ({} monomials) differs from {} ({} monomials)",
                            context(),
                            vm_poly.len(),
                            reference.label(),
                            ref_poly.len()
                        ));
                    }
                    SymbolicOutcome::Equal(vm_poly.len())
                }
                (Err(err), _) | (_, Err(err)) => SymbolicOutcome::Skipped(err),
            };
            if let Some(row) = self.rows.get_mut(j) {
                row.check = Some(VmCheck {
                    points: LISTING_VALIDATION_POINTS,
                    symbolic,
                    reference: reference.label(),
                });
            }
        }
        Ok(())
    }
}

/// Reference semantics of an interpreted identity.
enum VmReference<'a> {
    /// `vk.cs().gates()[g].polynomials()[p]`.
    Gate(&'a Expression<Fq>),
    /// Generator-parsed expression (non-gate identity routed through the VM).
    Generator(&'a QuotientExpr),
}

impl<'a> VmReference<'a> {
    /// Pick the reference for one identity.
    fn for_identity(
        identity: &'a QuotientIdentity,
        cs: &'a midnight_proofs::plonk::ConstraintSystem<Fq>,
    ) -> Result<Self, String> {
        match &identity.meta.source {
            QuotientIdentitySource::Gate {
                gate_index,
                polynomial_index,
                ..
            } => cs
                .gates()
                .get(*gate_index)
                .and_then(|gate| gate.polynomials().get(*polynomial_index))
                .map(VmReference::Gate)
                .ok_or_else(|| {
                    format!("gate {gate_index} polynomial {polynomial_index} is not in the constraint system")
                }),
            _ => Ok(VmReference::Generator(&identity.expr)),
        }
    }

    /// Label used in messages and in the listing.
    fn label(&self) -> &'static str {
        match self {
            Self::Gate(_) => "Expression::evaluate of the gate polynomial",
            Self::Generator(_) => "the generator's parsed Yul expression",
        }
    }

    /// Numeric evaluation over one memory image.
    fn numeric(
        &self,
        env: &ExprEnv<'_>,
        tokens: &BTreeMap<u8, u32>,
        image: &BTreeMap<u32, Fq>,
    ) -> Result<Fq, String> {
        let constant = |value: Fq| Ok(value);
        let leaf = |addr: u32| {
            image
                .get(&addr)
                .copied()
                .ok_or_else(|| format!("memory {addr:#06x} is not a published slot"))
        };
        let add = |a: Fq, b: Fq| Ok(a + b);
        let mul = |a: Fq, b: Fq| Ok(a * b);
        let neg = |a: Fq| Ok(-a);
        match self {
            Self::Gate(expr) => eval_expression(expr, env, &constant, &leaf, &add, &mul, &neg),
            Self::Generator(expr) => {
                eval_quotient_expr(expr, tokens, &constant, &leaf, &add, &mul, &neg)
            }
        }
    }

    /// Symbolic expansion.
    fn symbolic(&self, env: &ExprEnv<'_>, tokens: &BTreeMap<u8, u32>) -> Result<Poly, String> {
        let constant = |value: Fq| Ok(Poly::constant(value));
        let leaf = |addr: u32| Ok(Poly::var(addr));
        let add = |a: Poly, b: Poly| a.add(b);
        let mul = |a: Poly, b: Poly| a.mul(&b);
        let neg = |a: Poly| Ok(a.neg());
        match self {
            Self::Gate(expr) => eval_expression(expr, env, &constant, &leaf, &add, &mul, &neg),
            Self::Generator(expr) => {
                eval_quotient_expr(expr, tokens, &constant, &leaf, &add, &mul, &neg)
            }
        }
    }
}

/// `VK_MPTR` as a concrete address.
fn vk_mptr_usize(plan: &LoweringPlan) -> Result<usize, String> {
    match plan.vk_mptr.value() {
        Value::Integer(addr) if addr >= 0 => Ok(addr as usize),
        other => Err(format!("VK_MPTR is not a concrete address: {other}")),
    }
}

/// Listing section rule.
const RULE: &str = "--------------------------------------------------------------------------------------------------------";
/// Listing family rule.
const DOUBLE_RULE: &str = "========================================================================================================";

impl ListingModel<'_> {
    /// Number of identities.
    fn m(&self) -> usize {
        self.rows.len()
    }

    /// Bucket description.
    fn bucket_text(&self, target: QuotientTarget) -> String {
        match target {
            QuotientTarget::Main => "main".to_string(),
            QuotientTarget::Selector(bucket) => format!(
                "B{bucket} (simple selector f{})",
                self.sorted_simple.get(bucket).copied().unwrap_or(usize::MAX)
            ),
        }
    }

    /// Short bucket label for tables.
    fn bucket_short(&self, target: QuotientTarget) -> String {
        match target {
            QuotientTarget::Main => "main".to_string(),
            QuotientTarget::Selector(bucket) => format!(
                "B{bucket}(f{})",
                self.sorted_simple.get(bucket).copied().unwrap_or(usize::MAX)
            ),
        }
    }

    /// Program-byte range of a row, if any.
    fn row_range(&self, row: &IdentityRow) -> Option<(usize, usize)> {
        row.item.map(|idx| (self.blocks[idx].byte_start, self.blocks[idx].byte_end))
    }

    /// Meaning of a permutation / lookup / trash identity and where its fold
    /// happens inside the generated native block.
    fn family_meaning(&self, row: &IdentityRow) -> String {
        let meta = &self.plan.meta;
        match &row.source {
            QuotientIdentitySource::Permutation { identity_index } => {
                let sets = meta.num_permutation_zs;
                let chunk = meta.permutation_chunk_len.max(1);
                let cols = meta.permutation_columns.len();
                let k = *identity_index;
                if row.family_size != 2 * sets + 1 {
                    return format!("permutation identity {k}");
                }
                if k == 0 {
                    "straight-line fold: l_0 * (1 - perm_z_0)  [first-set boundary]".to_string()
                } else if k == 1 {
                    let last = sets - 1;
                    format!(
                        "straight-line fold: l_last * (perm_z_{last}^2 - perm_z_{last})  [last-set booleanity]"
                    )
                } else if k <= sets {
                    let i = k - 1;
                    format!(
                        "loop q_perm_i = {i}: l_0 * (perm_z_{i} - perm_z_{}_last)  [set continuity]",
                        i - 1
                    )
                } else {
                    let s = k - sets - 1;
                    let start = s * chunk;
                    let end = ((s + 1) * chunk).min(cols);
                    format!(
                        "loop q_perm_set = {s}: (1 - (l_last + l_blind)) * (perm_z_{s}_next * prod(v + beta*sigma + gamma) - perm_z_{s} * prod(v + beta*delta^i*x + gamma)) over sigma_{start}..sigma_{}  [set product]",
                        end.saturating_sub(1)
                    )
                }
            }
            QuotientIdentitySource::Lookup {
                identity_index,
                lookup_index,
                ..
            } => {
                let local = meta
                    .protocol
                    .lookup_identity_source(*identity_index)
                    .map(|(_, local)| local)
                    .unwrap_or(usize::MAX);
                let chunks = meta.lookup_chunks.get(*lookup_index).copied().unwrap_or(0);
                let l = lookup_index;
                if local == 0 {
                    format!("boundary: (l_0 + l_last) * lk{l}_z")
                } else if local <= chunks {
                    let c = local - 1;
                    let inputs = self.lookup_chunk_inputs(*lookup_index, c);
                    format!(
                        "helper chunk {c} ({inputs} input(s)): lk{l}_h{c} * prod_k(f_k + beta) - sum_k prod_(i!=k)(f_i + beta)"
                    )
                } else {
                    format!(
                        "accumulator: (1 - (l_last + l_blind)) * ((lk{l}_z_next - lk{l}_z - s * sum_c lk{l}_h_c) * (t + beta) + lk{l}_m)"
                    )
                }
            }
            QuotientIdentitySource::Trash { trash_index, .. } => {
                let constraints = self
                    .inputs
                    .vk
                    .cs()
                    .trashcans()
                    .get(*trash_index)
                    .map(|trash| trash.constraint_expressions().len())
                    .unwrap_or(0);
                format!(
                    "sum_i trash_challenge^i * c_i - (1 - q) * trash_{trash_index}  [{constraints} compressed constraint(s)]"
                )
            }
            QuotientIdentitySource::Gate { .. } => String::new(),
        }
    }

    /// Number of parallel inputs of one lookup chunk.
    fn lookup_chunk_inputs(&self, lookup: usize, chunk: usize) -> usize {
        let cs = self.inputs.vk.cs();
        cs.lookups()
            .get(lookup)
            .map(|argument| {
                argument
                    .chunk_by_degree(cs.degree())
                    .input_expression_chunks()
                    .get(chunk)
                    .map(|inputs| inputs.len())
                    .unwrap_or(0)
            })
            .unwrap_or(0)
    }

    /// Render the text listing.
    fn render_listing(&self) -> String {
        let mut out = Vec::<String>::new();
        let m = self.m();
        let meta = &self.plan.meta;
        let protocol = &meta.protocol.quotient;
        let vm_rows = self.rows.iter().filter(|row| row.check.is_some()).count();
        let symbolic_equal = self
            .rows
            .iter()
            .filter(|row| {
                matches!(
                    row.check.as_ref().map(|c| &c.symbolic),
                    Some(SymbolicOutcome::Equal(_))
                )
            })
            .count();
        let program_end = self.program_mptr + self.program.len();

        out.push("QUOTIENT VM LISTING".to_string());
        out.push(DOUBLE_RULE.to_string());
        out.push(format!(
            "generator            halo2_solidity_verifier {}",
            env!("CARGO_PKG_VERSION")
        ));
        out.push(format!(
            "render               vk={} quotient={} trace={}",
            if self.ctx.separate_vk {
                "separate"
            } else {
                "embedded"
            },
            if self.ctx.external_quotient {
                "external_pinned"
            } else {
                "inline"
            },
            self.ctx.trace
        ));
        out.push(format!(
            "vk runtime           {} bytes = 0xfe INVALID prefix + {}-byte payload ({} words)",
            self.runtime_len,
            self.payload_len,
            self.payload_len / WORD_BYTES
        ));
        out.push(format!(
            "vk runtime codehash  {}{}",
            self.codehash,
            if self.ctx.separate_vk {
                "  (EXPECTED_VK_CODEHASH pinned by the verifier)"
            } else {
                "  (embedded VK: not pinned by codehash)"
            }
        ));
        out.push(format!(
            "VK_MPTR              {:#06x}  (payload word w is copied to VK_MPTR + 32*w; runtime byte = 1 + payload byte)",
            self.vk_mptr
        ));
        out.push(format!(
            "constant table       {} used of {} reserved words, payload words [{}, {}) = payload bytes [{:#06x}, {:#06x}) = memory [{:#06x}, {:#06x}); keccak256 {}",
            self.consts.len(),
            self.const_reserved_words,
            self.const_offset_words,
            self.const_offset_words + self.const_reserved_words,
            self.const_offset_words * WORD_BYTES,
            (self.const_offset_words + self.const_reserved_words) * WORD_BYTES,
            self.const_mptr,
            self.const_mptr + self.const_reserved_words * WORD_BYTES,
            keccak_hex(&const_table_bytes(&self.consts))
        ));
        out.push(format!(
            "program              {} bytes packed in {} words, payload words [{}, {}) = payload bytes [{:#06x}, {:#06x}) = memory [{:#06x}, {:#06x}); keccak256 {}",
            self.program.len(),
            self.program_words,
            self.program_offset_words,
            self.program_offset_words + self.program_words,
            self.program_offset_words * WORD_BYTES,
            self.program_offset_words * WORD_BYTES + self.program.len(),
            self.program_mptr,
            program_end,
            keccak_hex(&self.program)
        ));
        out.push(format!(
            "identities (m)       {m} = {} gate + {} permutation + {} lookup + {} trash; identity j has weight y^(m-1-j)",
            protocol.gates, protocol.permutation, protocol.lookup, protocol.trash
        ));
        let buckets = self
            .sorted_simple
            .iter()
            .enumerate()
            .map(|(idx, col)| format!("B{idx}=f{col}(tail y^{})", self.tails[idx]))
            .collect::<Vec<_>>();
        out.push(format!(
            "simple selectors     {} bucket(s): {}",
            self.sorted_simple.len(),
            if buckets.is_empty() {
                "-".to_string()
            } else {
                buckets.join(" ")
            }
        ));
        out.push(String::new());
        out.push("Fold semantics (QuotientNumeratorBlock.yul)".to_string());
        out.push("  main identity:     A <- A*y + e_j".to_string());
        out.push(
            "  selector identity: A <- A*y;  B_k <- B_k*y^gap + e_j   (gap = j - previous j in bucket k, 0 for the first)"
                .to_string(),
        );
        out.push(
            "  after the stream:  B_k <- B_k*y^tail_k (tail_k = m-1-last j of bucket k);  QUOTIENT_EVAL <- -A".to_string(),
        );
        out.push(
            "  => QUOTIENT_EVAL = -sum_{main j} e_j*y^(m-1-j),  B_k = sum_{j in bucket k} e_j*y^(m-1-j)".to_string(),
        );
        out.push(String::new());
        out.push("Render-time checks (rendering fails if any of these fails)".to_string());
        out.push(format!(
            "  [ok] program bytes and constant words read back from the VK payload equal the finalized build ({} bytes, {} constants; padding zero)",
            self.program.len(),
            self.consts.len()
        ));
        let lines = self.blocks.iter().map(|block| block.text.lines().count()).sum::<usize>();
        out.push(format!(
            "  [ok] {} program blocks ({} listing lines) cover program bytes [0x0000, {:#06x}) exactly once",
            self.blocks.len(),
            lines,
            self.program.len()
        ));
        out.push(format!(
            "  [ok] identities 0..{} each executed exactly once, in order (inline prefix, program items, trash suffix)",
            m.saturating_sub(1)
        ));
        out.push(format!(
            "  [ok] {vm_rows} VM identities: fold opcode, bucket and selector gap match the identity; all memory reads are published slots"
        ));
        out.push(format!(
            "  [ok] {vm_rows} VM identities: bytes interpreted in Rust == Expression::evaluate of the gate polynomial at {} pseudo-random points",
            LISTING_VALIDATION_POINTS
        ));
        out.push(format!(
            "  [ok] {symbolic_equal} of {vm_rows} VM identities: symbolic expansion of the bytes == expansion of the gate polynomial ({} not expanded: > {} monomials)",
            vm_rows - symbolic_equal,
            poly::POLY_TERM_CAP
        ));
        out.push(
            "  scope: these checks tie the pinned VK bytes to the Rust gate expressions through a Rust interpreter of the"
                .to_string(),
        );
        out.push(
            "         VM ABI. They do not check the Yul interpreter (covered by the EVM tests) or the inline/native Yul"
                .to_string(),
        );
        out.push(
            "         snippets, which are printed verbatim below. Slot names come from the generator's evaluation plan."
                .to_string(),
        );
        out.push(String::new());

        out.push("Identity index".to_string());
        out.push(format!(
            "  {:<5} {:<6} {:<10} {:<22} {:<18} source",
            "j", "y^", "bucket", "execution", "program bytes"
        ));
        for row in &self.rows {
            let range = self
                .row_range(row)
                .map(|(s, e)| format!("[{s:#06x},{e:#06x})"))
                .unwrap_or_else(|| "-".to_string());
            out.push(format!(
                "  {:<5} {:<6} {:<10} {:<22} {:<18} {}",
                row.j,
                m - 1 - row.j,
                self.bucket_short(row.target),
                execution_label(row.execution),
                range,
                source_text(&row.source)
            ));
        }
        out.push(String::new());

        self.render_identity_sections(&mut out);
        self.render_slot_table(&mut out);
        self.render_constant_table(&mut out);
        let mut text = out.join("\n");
        text.push('\n');
        text
    }

    /// Per-identity sections, in `j` order.
    fn render_identity_sections(&self, out: &mut Vec<String>) {
        let m = self.m();
        let mut family_headers = BTreeSet::new();
        for row in &self.rows {
            let y = m - 1 - row.j;
            match row.execution {
                QuotientExecutionKind::Inline
                | QuotientExecutionKind::Interpreted
                | QuotientExecutionKind::NativeIdentity { .. } => {
                    out.push(RULE.to_string());
                    out.push(format!(
                        "j={} | {} | bucket {} | y^{y} | {}",
                        row.j,
                        source_text(&row.source),
                        self.bucket_text(row.target),
                        execution_text(row.execution)
                    ));
                    if let Some(gap) = self.expected_gaps[row.j] {
                        out.push(format!("    selector gap {gap} (y-distance to the previous identity of this bucket)"));
                    }
                    match row.execution {
                        QuotientExecutionKind::Inline => {
                            out.push(format!(
                                "    inline prefix block {} of {} (no program bytes); Yul verbatim from the verifier's quotient block (;; = slot names added by the listing):",
                                row.local, row.family_size
                            ));
                            if let Some(lines) = self.yul.inline_computations.get(row.local) {
                                push_yul(out, lines, &self.symbols);
                            }
                        }
                        QuotientExecutionKind::Interpreted => {
                            let block = &self.blocks[row.item.expect("VM row has an item")];
                            out.push(format!(
                                "    program bytes [{:#06x}, {:#06x}) = {} B at memory [{:#06x}, {:#06x}); max stack {}; constants {}",
                                block.byte_start,
                                block.byte_end,
                                block.byte_end - block.byte_start,
                                self.program_mptr + block.byte_start,
                                self.program_mptr + block.byte_end,
                                block.max_stack,
                                if block.constants_used.is_empty() {
                                    "-".to_string()
                                } else {
                                    block
                                        .constants_used
                                        .iter()
                                        .map(|slot| format!("c[{slot}]"))
                                        .collect::<Vec<_>>()
                                        .join(" ")
                                }
                            ));
                            if let Some(check) = &row.check {
                                let symbolic = match &check.symbolic {
                                    SymbolicOutcome::Equal(n) => {
                                        format!("symbolic expansions identical ({n} monomials)")
                                    }
                                    SymbolicOutcome::Skipped(why) => {
                                        format!("symbolic comparison skipped ({why})")
                                    }
                                };
                                out.push(format!(
                                    "    check: equals {} at {}/{} points; {symbolic}",
                                    check.reference, check.points, check.points
                                ));
                            }
                            out.push(block.text.clone());
                        }
                        QuotientExecutionKind::NativeIdentity { native_index } => {
                            let idx = row.item.expect("native row has an item");
                            out.push(self.blocks[idx].text.clone());
                            out.push(format!(
                                "    Yul verbatim (NATIVE_IDENTITY switch case {native_index}; ;; = slot names added by the listing):"
                            ));
                            if let Some(lines) =
                                self.yul.native_identity_computations.get(native_index)
                            {
                                push_yul(out, lines, &self.symbols);
                            }
                        }
                        _ => {}
                    }
                }
                QuotientExecutionKind::NativePermutation
                | QuotientExecutionKind::NativeLookup
                | QuotientExecutionKind::StructuredTail => {
                    let label = execution_label(row.execution);
                    if family_headers.insert(label) {
                        let members = self
                            .rows
                            .iter()
                            .filter(|other| other.execution == row.execution)
                            .map(|other| other.j)
                            .collect::<Vec<_>>();
                        out.push(DOUBLE_RULE.to_string());
                        let (first, last) = (members[0], members[members.len() - 1]);
                        let span = if first == last {
                            format!("j={first} (1 identity)")
                        } else {
                            format!("j={first}..{last} ({} identities)", members.len())
                        };
                        match row.execution {
                            QuotientExecutionKind::NativePermutation => {
                                let meta = &self.plan.meta;
                                out.push(format!(
                                    "permutation family: {span}, executed by the NATIVE_PERMUTATION callback"
                                ));
                                out.push(format!(
                                    "    {} set(s), {} permutation column(s), chunk_len {}; folds happen inside the callback in the order listed below",
                                    meta.num_permutation_zs,
                                    meta.permutation_columns.len(),
                                    meta.permutation_chunk_len
                                ));
                            }
                            QuotientExecutionKind::NativeLookup => {
                                out.push(format!(
                                    "lookup family: {span}, executed by the NATIVE_LOOKUP callback"
                                ));
                                out.push(
                                    "    per lookup, in cs.lookups() order: boundary, one helper identity per chunk, accumulator"
                                        .to_string(),
                                );
                            }
                            _ => {
                                out.push(format!(
                                    "trash family: {span}, executed by the structured trash suffix after the VM loop (no program bytes)"
                                ));
                            }
                        }
                        if let Some(idx) = row.item {
                            out.push(self.blocks[idx].text.clone());
                        }
                        let (title, lines): (&str, Vec<String>) = match row.execution {
                            QuotientExecutionKind::NativePermutation => (
                                "    Yul verbatim (NATIVE_PERMUTATION case body; ;; = slot names added by the listing):",
                                self.yul.native_permutation_computation.clone(),
                            ),
                            QuotientExecutionKind::NativeLookup => (
                                "    Yul verbatim (NATIVE_LOOKUP case body; ;; = slot names added by the listing):",
                                self.yul.native_lookup_computation.clone(),
                            ),
                            _ => (
                                "    Yul verbatim (post-VM trash suffix; ;; = slot names added by the listing):",
                                self.yul.post_vm_computations.concat(),
                            ),
                        };
                        out.push(title.to_string());
                        push_yul(out, &lines, &self.symbols);
                        out.push(format!(
                            "    identities of this family (fold k of {}):",
                            members.len()
                        ));
                    }
                    out.push(format!(
                        "  j={} | {} | bucket {} | y^{y} | fold {} of {}: {}",
                        row.j,
                        source_text(&row.source),
                        self.bucket_text(row.target),
                        row.local + 1,
                        row.family_size,
                        self.family_meaning(row)
                    ));
                }
            }
        }
        out.push(RULE.to_string());
        out.push(String::new());
    }

    /// Evaluation-slot table.
    fn render_slot_table(&self, out: &mut Vec<String>) {
        out.push(format!(
            "Evaluation-slot map ({} slots; REVERSED_EVALS_MPTR = {:#06x}, eval i at REVERSED_EVALS_MPTR + 32*i)",
            self.slots.len(),
            resolve_ptr(self.plan.memory.reversed_evals_mptr, &self.plan.memory).unwrap_or(0)
        ));
        out.push(format!(
            "  {:<8} {:<18} {:<20} {:<6} detail",
            "memory", "name", "kind", "eval#"
        ));
        for slot in &self.slots {
            out.push(format!(
                "  {:<#8x} {:<18} {:<20} {:<6} {}",
                slot.addr,
                slot.name,
                slot.kind,
                slot.eval_index.map(|i| i.to_string()).unwrap_or_else(|| "-".to_string()),
                slot.detail
            ));
        }
        out.push(String::new());
    }

    /// Constant table with reference counts.
    fn render_constant_table(&self, out: &mut Vec<String>) {
        out.push(format!(
            "Constant table ({} used, {} reserved; memory = {:#06x} + 32*idx; payload = VK payload byte offset, i.e. `mstore(add(payload, <payload>), ...)` in the VK source)",
            self.consts.len(),
            self.const_reserved_words,
            self.const_mptr
        ));
        out.push(format!(
            "  {:<5} {:<8} {:<8} {:<5} {:<66} readable",
            "idx", "memory", "payload", "refs", "value"
        ));
        for (idx, value) in self.consts.iter().enumerate() {
            out.push(format!(
                "  {:<5} {:<#8x} {:<8} {:<5} {:<66} {}",
                idx,
                self.const_mptr + idx * WORD_BYTES,
                format!("{:#06x}", (self.const_offset_words + idx) * WORD_BYTES),
                self.const_refs[idx],
                word_hex(*value),
                readable_fr(self.consts_fr[idx])
            ));
        }
    }

    /// Render the JSON manifest.
    fn render_manifest(&self, listing: &str) -> String {
        let m = self.m();
        let protocol = &self.plan.meta.protocol.quotient;
        let memory = &self.plan.memory;
        let addr = |ptr: Ptr| Json::hex(resolve_ptr(ptr, memory).unwrap_or(0) as usize);
        let vm_rows = self.rows.iter().filter(|row| row.check.is_some()).count();
        let symbolic_equal = self
            .rows
            .iter()
            .filter(|row| {
                matches!(
                    row.check.as_ref().map(|c| &c.symbolic),
                    Some(SymbolicOutcome::Equal(_))
                )
            })
            .count();

        let const_table = self
            .consts
            .iter()
            .enumerate()
            .map(|(idx, value)| {
                Json::obj([
                    ("index", Json::num(idx)),
                    ("value", Json::str(word_hex(*value))),
                    ("readable", Json::str(readable_fr(self.consts_fr[idx]))),
                    (
                        "vk_payload_offset",
                        Json::str(format!(
                            "{:#06x}",
                            (self.const_offset_words + idx) * WORD_BYTES
                        )),
                    ),
                    ("memory", Json::hex(self.const_mptr + idx * WORD_BYTES)),
                    ("refs", Json::num(self.const_refs[idx])),
                ])
            })
            .collect::<Vec<_>>();
        let slots = self
            .slots
            .iter()
            .map(|slot| {
                let mut pairs = vec![
                    ("memory".to_string(), Json::hex(slot.addr as usize)),
                    ("name".to_string(), Json::str(slot.name.clone())),
                    ("kind".to_string(), Json::str(slot.kind)),
                ];
                if let Some(column) = slot.column {
                    pairs.push(("column".to_string(), Json::num(column)));
                }
                if let Some(rotation) = slot.rotation {
                    pairs.push((
                        "rotation".to_string(),
                        Json::str(match rotation {
                            0 => "cur".to_string(),
                            1 => "next".to_string(),
                            r => r.to_string(),
                        }),
                    ));
                }
                if let Some(index) = slot.index {
                    pairs.push(("index".to_string(), Json::num(index)));
                }
                if let Some(eval_index) = slot.eval_index {
                    pairs.push(("eval_index".to_string(), Json::num(eval_index)));
                }
                pairs.push(("detail".to_string(), Json::str(slot.detail.clone())));
                Json::Obj(pairs)
            })
            .collect::<Vec<_>>();
        let tokens = self
            .symbols
            .tokens
            .iter()
            .map(|(token, (symbol, addr))| {
                Json::obj([
                    ("token", Json::num(usize::from(*token))),
                    ("symbol", Json::str(symbol.clone())),
                    ("name", Json::str(token_slot_name(symbol))),
                    ("memory", Json::hex(*addr as usize)),
                ])
            })
            .collect::<Vec<_>>();
        let buckets = self
            .sorted_simple
            .iter()
            .enumerate()
            .map(|(idx, col)| {
                Json::obj([
                    ("index", Json::num(idx)),
                    ("fixed_column", Json::num(*col)),
                    (
                        "identities",
                        Json::Arr(
                            self.rows
                                .iter()
                                .filter(|row| row.target == QuotientTarget::Selector(idx))
                                .map(|row| Json::num(row.j))
                                .collect(),
                        ),
                    ),
                    ("tail_exponent", Json::num(self.tails[idx])),
                ])
            })
            .collect::<Vec<_>>();
        let program_items = self
            .blocks
            .iter()
            .enumerate()
            .map(|(idx, block)| {
                let mut pairs = vec![
                    ("index".to_string(), Json::num(idx)),
                    ("kind".to_string(), Json::str(block.kind.label())),
                    ("byte_start".to_string(), Json::num(block.byte_start)),
                    ("byte_end".to_string(), Json::num(block.byte_end)),
                    (
                        "identities".to_string(),
                        Json::Arr(block.identities.iter().map(|j| Json::num(*j)).collect()),
                    ),
                ];
                if let ProgramBlockKind::NativeIdentity { index } = block.kind {
                    pairs.push(("native_index".to_string(), Json::num(usize::from(index))));
                }
                Json::Obj(pairs)
            })
            .collect::<Vec<_>>();
        let entries = self.rows.iter().map(|row| self.manifest_entry(row)).collect::<Vec<_>>();

        let manifest = Json::obj([
            ("format", Json::str(MANIFEST_FORMAT)),
            ("format_version", Json::num(MANIFEST_FORMAT_VERSION)),
            (
                "generator",
                Json::obj([
                    ("crate", Json::str("halo2_solidity_verifier")),
                    ("version", Json::str(env!("CARGO_PKG_VERSION"))),
                ]),
            ),
            (
                "render",
                Json::obj([
                    ("vk", Json::str(if self.ctx.separate_vk { "separate" } else { "embedded" })),
                    (
                        "quotient",
                        Json::str(if self.ctx.external_quotient { "external_pinned" } else { "inline" }),
                    ),
                    ("trace", Json::Bool(self.ctx.trace)),
                ]),
            ),
            (
                "vk",
                Json::obj([
                    ("runtime_codehash", Json::str(self.codehash.clone())),
                    ("codehash_pinned_by_verifier", Json::Bool(self.ctx.separate_vk)),
                    ("runtime_length", Json::num(self.runtime_len)),
                    ("runtime_prefix", Json::str("0xfe")),
                    ("payload_length", Json::num(self.payload_len)),
                    ("payload_words", Json::num(self.payload_len / WORD_BYTES)),
                    ("payload_keccak256", Json::str(self.payload_keccak.clone())),
                    ("header_words", Json::num(self.header_words)),
                    ("vk_mptr", Json::hex(self.vk_mptr)),
                ]),
            ),
            (
                "program",
                Json::obj([
                    ("keccak256", Json::str(keccak_hex(&self.program))),
                    ("length_bytes", Json::num(self.program.len())),
                    ("vk_payload_word_offset", Json::num(self.program_offset_words)),
                    ("vk_payload_word_count", Json::num(self.program_words)),
                    ("vk_payload_byte_offset", Json::hex(self.program_offset_words * WORD_BYTES)),
                    ("vk_runtime_byte_offset", Json::hex(1 + self.program_offset_words * WORD_BYTES)),
                    ("memory_start", Json::hex(self.program_mptr)),
                    ("memory_end", Json::hex(self.program_mptr + self.program.len())),
                    (
                        "padding_bytes",
                        Json::num(self.program_words * WORD_BYTES - self.program.len()),
                    ),
                ]),
            ),
            (
                "constants",
                Json::obj([
                    ("keccak256", Json::str(keccak_hex(&const_table_bytes(&self.consts)))),
                    ("count", Json::num(self.consts.len())),
                    ("reserved_words", Json::num(self.const_reserved_words)),
                    ("vk_payload_word_offset", Json::num(self.const_offset_words)),
                    ("vk_payload_byte_offset", Json::hex(self.const_offset_words * WORD_BYTES)),
                    ("memory_start", Json::hex(self.const_mptr)),
                    ("table", Json::Arr(const_table)),
                ]),
            ),
            (
                "memory",
                Json::obj([
                    ("VK_MPTR", Json::hex(self.vk_mptr)),
                    ("REVERSED_EVALS_MPTR", addr(memory.reversed_evals_mptr)),
                    ("num_evals", Json::num(self.plan.meta.num_evals)),
                    ("CHALLENGE_MPTR", addr(memory.challenge_mptr)),
                    ("SELECTOR_ACC_MPTR", Json::hex(memory.selector_acc_mptr)),
                    ("quotient_stack_mptr", Json::hex(self.plan.quotient.stack_mptr)),
                    ("quotient_eval_numer_mptr", Json::hex(self.plan.quotient.state_slots.eval_numer_mptr)),
                    (
                        "quotient_selector_power_mptr",
                        Json::hex(self.plan.quotient.state_slots.selector_power_mptr),
                    ),
                ]),
            ),
            ("tokens", Json::Arr(tokens)),
            ("slots", Json::Arr(slots)),
            (
                "identities",
                Json::obj([
                    ("m", Json::num(m)),
                    ("gate", Json::num(protocol.gates)),
                    ("permutation", Json::num(protocol.permutation)),
                    ("lookup", Json::num(protocol.lookup)),
                    ("trash", Json::num(protocol.trash)),
                    (
                        "simple_selector_fixed_columns",
                        Json::Arr(self.sorted_simple.iter().map(|c| Json::num(*c)).collect()),
                    ),
                    ("selector_buckets", Json::Arr(buckets)),
                ]),
            ),
            ("program_items", Json::Arr(program_items)),
            ("entries", Json::Arr(entries)),
            (
                "validation",
                Json::obj([
                    ("points", Json::num(LISTING_VALIDATION_POINTS)),
                    ("seed", Json::str(format!("0x{}", hex::encode(self.seed)))),
                    ("vm_identities", Json::num(vm_rows)),
                    ("numeric_agree", Json::num(vm_rows)),
                    ("symbolic_equal", Json::num(symbolic_equal)),
                    ("symbolic_skipped", Json::num(vm_rows - symbolic_equal)),
                    ("program_bytes_covered_once", Json::Bool(true)),
                    ("identities_executed_once_in_order", Json::Bool(true)),
                    (
                        "scope",
                        Json::str(
                            "VK program bytes vs Rust gate expressions through a Rust interpreter of the VM ABI; the Yul interpreter is covered by the EVM tests, not by this check",
                        ),
                    ),
                ]),
            ),
            (
                "listing",
                Json::obj([
                    ("keccak256", Json::str(keccak_hex(listing.as_bytes()))),
                    ("length_bytes", Json::num(listing.len())),
                ]),
            ),
        ]);
        manifest.pretty()
    }

    /// One manifest entry.
    fn manifest_entry(&self, row: &IdentityRow) -> Json {
        let m = self.m();
        let source = match &row.source {
            QuotientIdentitySource::Gate {
                gate_index,
                gate_name,
                constraint_index,
                constraint_name,
                polynomial_index,
            } => Json::obj([
                ("family", Json::str("gate")),
                ("gate_index", Json::num(*gate_index)),
                ("gate_name", Json::str(gate_name.clone())),
                ("constraint_index", Json::num(*constraint_index)),
                ("constraint_name", Json::str(constraint_name.clone())),
                ("polynomial_index", Json::num(*polynomial_index)),
            ]),
            QuotientIdentitySource::Permutation { identity_index } => Json::obj([
                ("family", Json::str("permutation")),
                ("local_index", Json::num(*identity_index)),
            ]),
            QuotientIdentitySource::Lookup {
                identity_index,
                lookup_index,
                lookup_name,
            } => Json::obj([
                ("family", Json::str("lookup")),
                ("local_index", Json::num(*identity_index)),
                ("lookup_index", Json::num(*lookup_index)),
                ("lookup_name", Json::str(lookup_name.clone())),
            ]),
            QuotientIdentitySource::Trash {
                trash_index,
                trash_name,
            } => Json::obj([
                ("family", Json::str("trash")),
                ("local_index", Json::num(*trash_index)),
                ("trash_name", Json::str(trash_name.clone())),
            ]),
        };
        let target = match row.target {
            QuotientTarget::Main => Json::obj([("bucket", Json::str("main"))]),
            QuotientTarget::Selector(bucket) => {
                let mut pairs = vec![
                    ("bucket".to_string(), Json::str("selector")),
                    ("selector_index".to_string(), Json::num(bucket)),
                    (
                        "fixed_column".to_string(),
                        Json::num(self.sorted_simple.get(bucket).copied().unwrap_or(usize::MAX)),
                    ),
                ];
                if let Some(gap) = self.expected_gaps[row.j] {
                    pairs.push(("gap".to_string(), Json::num(gap)));
                }
                Json::Obj(pairs)
            }
        };
        let mut execution = vec![(
            "kind".to_string(),
            Json::str(execution_label(row.execution)),
        )];
        match row.execution {
            QuotientExecutionKind::Inline => {
                execution.push(("inline_index".to_string(), Json::num(row.local)));
            }
            QuotientExecutionKind::StructuredTail => {
                execution.push(("fold_position".to_string(), Json::num(row.local + 1)));
                execution.push(("family_size".to_string(), Json::num(row.family_size)));
                execution.push(("meaning".to_string(), Json::str(self.family_meaning(row))));
            }
            _ => {}
        }
        if let Some(idx) = row.item {
            let block = &self.blocks[idx];
            execution.push(("program_item".to_string(), Json::num(idx)));
            execution.push(("byte_start".to_string(), Json::num(block.byte_start)));
            execution.push(("byte_end".to_string(), Json::num(block.byte_end)));
            execution.push((
                "byte_range_hex".to_string(),
                Json::str(format!(
                    "[{:#06x}, {:#06x})",
                    block.byte_start, block.byte_end
                )),
            ));
            execution.push((
                "memory_start".to_string(),
                Json::hex(self.program_mptr + block.byte_start),
            ));
            match row.execution {
                QuotientExecutionKind::Interpreted => {
                    execution.push((
                        "constants_used".to_string(),
                        Json::Arr(
                            block
                                .constants_used
                                .iter()
                                .map(|c| Json::num(usize::from(*c)))
                                .collect(),
                        ),
                    ));
                    execution.push((
                        "fold".to_string(),
                        match block.fold {
                            Some(ProgramFold::Main) => Json::obj([("op", Json::str("fold_main"))]),
                            Some(ProgramFold::Selector { selector, gap }) => Json::obj([
                                ("op", Json::str("fold_selector")),
                                ("selector_index", Json::num(usize::from(selector))),
                                ("gap", Json::num(usize::from(gap))),
                            ]),
                            None => Json::Null,
                        },
                    ));
                    execution.push(("max_stack".to_string(), Json::num(block.max_stack)));
                    execution.push((
                        "monomials".to_string(),
                        block.monomials.map(Json::num).unwrap_or(Json::Null),
                    ));
                }
                QuotientExecutionKind::NativeIdentity { native_index } => {
                    execution.push(("native_index".to_string(), Json::num(native_index)));
                }
                QuotientExecutionKind::NativePermutation | QuotientExecutionKind::NativeLookup => {
                    execution.push(("fold_position".to_string(), Json::num(row.local + 1)));
                    execution.push(("family_size".to_string(), Json::num(row.family_size)));
                    execution.push(("meaning".to_string(), Json::str(self.family_meaning(row))));
                }
                _ => {}
            }
        }
        let mut pairs = vec![
            ("j".to_string(), Json::num(row.j)),
            ("source".to_string(), source),
            ("target".to_string(), target),
            ("y_exponent".to_string(), Json::num(m - 1 - row.j)),
            ("execution".to_string(), Json::Obj(execution)),
        ];
        if let Some(check) = &row.check {
            pairs.push((
                "check".to_string(),
                Json::obj([
                    ("reference", Json::str(check.reference)),
                    ("random_points_agree", Json::num(check.points)),
                    (
                        "symbolic",
                        Json::str(match &check.symbolic {
                            SymbolicOutcome::Equal(n) => format!("equal ({n} monomials)"),
                            SymbolicOutcome::Skipped(why) => format!("skipped: {why}"),
                        }),
                    ),
                ]),
            ));
        }
        Json::Obj(pairs)
    }
}

/// Append verbatim Yul lines with a fixed indent.
///
/// Lines that load published slots by literal address get a trailing
/// `;; 0xADDR=name` annotation (added by the listing, not part of the Yul).
fn push_yul(out: &mut Vec<String>, lines: &[String], symbols: &ListingSymbols) {
    if lines.is_empty() {
        out.push("      (empty)".to_string());
    }
    for line in lines {
        let names = yul_literal_loads(line)
            .into_iter()
            .filter_map(|addr| symbols.slots.get(&addr).map(|name| format!("{addr:#06x}={name}")))
            .collect::<Vec<_>>();
        if names.is_empty() {
            out.push(format!("      {line}"));
        } else {
            out.push(format!("      {line}    ;; {}", names.join(", ")));
        }
    }
}

/// Literal addresses loaded by `mload(0x...)` in one Yul line, in order,
/// without duplicates.
fn yul_literal_loads(line: &str) -> Vec<u32> {
    let mut out = Vec::new();
    let mut rest = line;
    while let Some(pos) = rest.find("mload(0x") {
        rest = &rest[pos + "mload(0x".len()..];
        let digits = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect::<String>();
        if rest[digits.len()..].starts_with(')') {
            if let Ok(addr) = u32::from_str_radix(&digits, 16) {
                if !out.contains(&addr) {
                    out.push(addr);
                }
            }
        }
    }
    out
}
