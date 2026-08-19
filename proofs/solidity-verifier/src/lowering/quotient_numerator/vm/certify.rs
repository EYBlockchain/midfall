// SPDX-License-Identifier: CC0-1.0
//! Render-time self-certification of the emitted quotient VM program.
//!
//! The quotient lowering runs a peephole optimizer: shape recognizers rewrite
//! seven-limb foreign-field expressions into superinstructions, and a
//! run-compaction pass rewrites adjacent affine terms into counted opcodes.
//! Both are pure encoding choices that must preserve the evaluated polynomial
//! exactly. This module proves that they did, for the specific program this
//! render is about to emit, by executing the finalized bytecode with the
//! independent interpreter in [`super::reference`] and comparing each identity
//! against direct evaluation of the [`QuotientExpr`] tree it was lowered from.
//!
//! This is a generator-time gate, not a test: every artifact the generator
//! produces is certified before it can be pinned into a verifying key, so a
//! recognizer bug on a previously unseen gate shape fails the render instead of
//! shipping a wrong verifier.
//!
//! See [`super::reference`] for what this does and does not cover.

use ff::Field;
use midnight_curves::Fq;
use sha3::{Digest, Keccak256};

use super::{
    quotient_op_len,
    reference::{eval_quotient_expr, eval_quotient_identity, QuotientRefMemory},
    QuotientExpr, QuotientMem, QuotientProgramBuild, QuotientProgramItem, QuotientProgramPlan,
    QuotientTarget, Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_NATIVE_IDENTITY, Q_OP_NATIVE_LOOKUP,
    Q_OP_NATIVE_PERMUTATION,
};
use crate::lowering::render::Halo2VerifyingKey;

/// Seed for the certification assignment.
///
/// The seed is deterministic so failing renders reproduce exactly, but it is
/// derived from the finalized artifact rather than fixed globally. This keeps
/// the sampled assignment independent of any circuit author's pre-render view
/// of the quotient program while preserving reproducible diagnostics.
const QUOTIENT_CERTIFY_SEED_DOMAIN: &[u8] = b"midfall/quotient-vm/certify-seed/v3";

/// Derive the random-assignment seed from every compared artifact.
///
/// Binding the oracle expressions closes the case where a miscompile drops a
/// tunable constant before it reaches the emitted constant table. Binding both
/// builds makes the dual-build challenge depend on the optimized and baseline
/// representations. The VK payload is included after generator invariants have
/// checked that its quotient sections match the finalized build.
pub(crate) fn derive_certify_seed(
    builds: &[&QuotientProgramBuild],
    exprs: &[&QuotientExpr],
    vk_payload: &[u8],
) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(QUOTIENT_CERTIFY_SEED_DOMAIN);

    hasher.update((builds.len() as u64).to_be_bytes());
    for build in builds {
        hasher.update((build.bytes.len() as u64).to_be_bytes());
        hasher.update(&build.bytes);

        hasher.update((build.consts.len() as u64).to_be_bytes());
        for value in &build.consts {
            hasher.update(value.to_be_bytes::<32>());
        }
    }

    hasher.update((exprs.len() as u64).to_be_bytes());
    for expr in exprs {
        hash_quotient_expr(&mut hasher, expr);
    }

    hasher.update((vk_payload.len() as u64).to_be_bytes());
    hasher.update(vk_payload);

    hasher.finalize().into()
}

/// Hash one expression with explicit node and memory-address tags.
fn hash_quotient_expr(hasher: &mut Keccak256, expr: &QuotientExpr) {
    match expr {
        QuotientExpr::Const(value) => {
            hasher.update([0]);
            hasher.update(value.to_be_bytes::<32>());
        }
        QuotientExpr::Mem(QuotientMem::Literal(ptr)) => {
            hasher.update([1]);
            hasher.update(ptr.to_be_bytes());
        }
        QuotientExpr::Mem(QuotientMem::Token(token)) => {
            hasher.update([2, *token]);
        }
        QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => {
            hasher.update([3, *token]);
            hasher.update(offset.to_be_bytes());
        }
        QuotientExpr::Add(lhs, rhs) => {
            hasher.update([4]);
            hash_quotient_expr(hasher, lhs);
            hash_quotient_expr(hasher, rhs);
        }
        QuotientExpr::Mul(lhs, rhs) => {
            hasher.update([5]);
            hash_quotient_expr(hasher, lhs);
            hash_quotient_expr(hasher, rhs);
        }
        QuotientExpr::Neg(inner) => {
            hasher.update([6]);
            hash_quotient_expr(hasher, inner);
        }
    }
}

/// Expressions evaluated by the compact quotient program.
fn interpreted_exprs(plan: &QuotientProgramPlan) -> Vec<&QuotientExpr> {
    plan.items
        .iter()
        .filter_map(|item| match item {
            QuotientProgramItem::Identity(identity) => Some(&identity.expr),
            _ => None,
        })
        .collect()
}

/// Certify that the emitted bytecode evaluates the planned identities.
///
/// Runs after [`super::validate_quotient_program`], which has already proven
/// the stream decodes and is stack-safe; this pass assumes well-formedness and
/// checks *meaning*.
pub(crate) fn certify_quotient_program(
    plan: &QuotientProgramPlan,
    build: &QuotientProgramBuild,
    vk: &Halo2VerifyingKey,
) -> Result<(), String> {
    let exprs = interpreted_exprs(plan);
    let vk_payload = vk.bytes();
    let seed = derive_certify_seed(&[build], &exprs, &vk_payload);
    let mut mem = QuotientRefMemory::new(seed);
    let bytes = &build.bytes;
    let mut cursor = 0usize;

    for (item_idx, item) in plan.items.iter().enumerate() {
        match item {
            QuotientProgramItem::Identity(identity) => {
                let (expr_end, fold_op) = identity_segment(bytes, cursor)
                    .map_err(|err| format!("quotient item {item_idx}: {err}"))?;

                let actual =
                    eval_quotient_identity(&bytes[cursor..expr_end], &build.consts, &mut mem)
                        .map_err(|err| {
                            format!(
                                "quotient identity {} ({:?}): {err}",
                                identity.meta.global_index, identity.meta.source
                            )
                        })?;
                let expected = eval_quotient_expr(&identity.expr, &mut mem);

                if actual != expected {
                    return Err(format!(
                        "quotient VM miscompiled identity {} ({:?}): bytecode evaluates to {:?} \
                         but its expression evaluates to {:?}. This is a codegen bug in the \
                         quotient lowering (shape recognizer, operand packing, or run \
                         compaction), not a proof or verifying-key problem.",
                        identity.meta.global_index, identity.meta.source, actual, expected
                    ));
                }

                check_fold(bytes, expr_end, fold_op, identity, plan).map_err(|err| {
                    format!(
                        "quotient identity {} ({:?}): {err}",
                        identity.meta.global_index, identity.meta.source
                    )
                })?;

                cursor = expr_end + quotient_op_len(bytes, expr_end);
            }
            QuotientProgramItem::NativePermutation
            | QuotientProgramItem::NativeLookup
            | QuotientProgramItem::NativeIdentity(_) => {
                // Native markers carry no arithmetic here: the Yul template
                // substitutes generated straight-line kernels. Certify only
                // that the marker sits at the planned stream position.
                let expected_op = match item {
                    QuotientProgramItem::NativePermutation => Q_OP_NATIVE_PERMUTATION,
                    QuotientProgramItem::NativeLookup => Q_OP_NATIVE_LOOKUP,
                    _ => Q_OP_NATIVE_IDENTITY,
                };
                let actual_op = *bytes.get(cursor).ok_or_else(|| {
                    format!("quotient item {item_idx}: program ended before native marker")
                })?;
                if actual_op != expected_op {
                    return Err(format!(
                        "quotient item {item_idx}: expected native marker {expected_op:#x} at byte \
                         {cursor}, found {actual_op:#x}"
                    ));
                }
                if let QuotientProgramItem::NativeIdentity(native_idx) = item {
                    // The marker index is a big-endian u16, not a single byte.
                    let hi = *bytes.get(cursor + 1).ok_or_else(|| {
                        format!("quotient item {item_idx}: truncated native identity index")
                    })?;
                    let lo = *bytes.get(cursor + 2).ok_or_else(|| {
                        format!("quotient item {item_idx}: truncated native identity index")
                    })?;
                    let encoded = u16::from_be_bytes([hi, lo]) as usize;
                    if encoded != *native_idx {
                        return Err(format!(
                            "quotient item {item_idx}: native identity index {encoded} does not \
                             match planned index {native_idx}"
                        ));
                    }
                }
                cursor += quotient_op_len(bytes, cursor);
            }
        }
    }

    if cursor != bytes.len() {
        return Err(format!(
            "quotient program has {} trailing byte(s) after the planned item stream",
            bytes.len() - cursor
        ));
    }

    Ok(())
}

/// Find the end of one identity expression and the fold opcode that closes it.
fn identity_segment(bytes: &[u8], start: usize) -> Result<(usize, u8), String> {
    let mut idx = start;
    while idx < bytes.len() {
        let op = bytes[idx];
        match op {
            Q_OP_FOLD_MAIN | Q_OP_FOLD_SELECTOR => return Ok((idx, op)),
            Q_OP_NATIVE_PERMUTATION | Q_OP_NATIVE_LOOKUP | Q_OP_NATIVE_IDENTITY => {
                return Err(format!(
                    "native marker {op:#x} at byte {idx} interrupts an identity expression"
                ));
            }
            _ => idx += quotient_op_len(bytes, idx),
        }
    }
    Err(format!(
        "identity expression starting at byte {start} is never folded"
    ))
}

/// Check that the emitted fold matches the planned target and selector gap.
fn check_fold(
    bytes: &[u8],
    fold_idx: usize,
    fold_op: u8,
    identity: &super::QuotientIdentity,
    plan: &QuotientProgramPlan,
) -> Result<(), String> {
    match (fold_op, identity.target) {
        (Q_OP_FOLD_MAIN, QuotientTarget::Main) => Ok(()),
        (Q_OP_FOLD_SELECTOR, QuotientTarget::Selector(selector_idx)) => {
            let encoded_idx = *bytes
                .get(fold_idx + 1)
                .ok_or_else(|| "truncated selector fold index".to_string())?
                as usize;
            if encoded_idx != selector_idx {
                return Err(format!(
                    "selector fold targets bucket {encoded_idx} but the plan says {selector_idx}"
                ));
            }
            let hi = *bytes
                .get(fold_idx + 2)
                .ok_or_else(|| "truncated selector fold gap".to_string())?;
            let lo = *bytes
                .get(fold_idx + 3)
                .ok_or_else(|| "truncated selector fold gap".to_string())?;
            let encoded_gap = u16::from_be_bytes([hi, lo]) as usize;
            let planned_gap = plan
                .selector_fold
                .gap_for(identity)
                .ok_or_else(|| "selector identity has no planned fold gap".to_string())?;
            if encoded_gap != planned_gap {
                return Err(format!(
                    "selector fold gap {encoded_gap} does not match planned gap {planned_gap}"
                ));
            }
            Ok(())
        }
        (fold_op, target) => Err(format!(
            "fold opcode {fold_op:#x} does not match planned target {target:?}"
        )),
    }
}

/// Certify that two builds of the same identity stream agree.
///
/// The limb-aware superinstructions are the least principled part of the
/// lowering: they pattern-match algebraic shapes out of a commutative-ring
/// expression tree. Building the same stream with those recognizers disabled
/// yields a program using only `PUSH`/`ADD`/`MUL`/`NEG`, which is
/// straightforward to audit. Requiring the two to agree identity-by-identity
/// turns every recognizer from trusted code into a checked optimization.
pub(crate) fn certify_quotient_builds_agree(
    plan: &QuotientProgramPlan,
    optimized: &QuotientProgramBuild,
    baseline: &QuotientProgramBuild,
    vk: &Halo2VerifyingKey,
) -> Result<(), String> {
    let exprs = interpreted_exprs(plan);
    let vk_payload = vk.bytes();
    let seed = derive_certify_seed(&[optimized, baseline], &exprs, &vk_payload);
    let mut mem = QuotientRefMemory::new(seed);

    let optimized_values = identity_values(plan, optimized, &mut mem)?;
    let baseline_values = identity_values(plan, baseline, &mut mem)?;

    if optimized_values.len() != baseline_values.len() {
        return Err(format!(
            "quotient dual build disagrees on identity count: {} with limb opcodes, {} without",
            optimized_values.len(),
            baseline_values.len()
        ));
    }

    for (position, (lhs, rhs)) in optimized_values.iter().zip(baseline_values.iter()).enumerate() {
        if lhs != rhs {
            return Err(format!(
                "quotient limb superinstructions changed the value of interpreted identity at \
                 stream position {position}: {lhs:?} with limb opcodes, {rhs:?} without. One of \
                 the shape recognizers is unsound for this gate shape."
            ));
        }
    }

    Ok(())
}

/// Evaluate every interpreted identity in one build, in stream order.
fn identity_values(
    plan: &QuotientProgramPlan,
    build: &QuotientProgramBuild,
    mem: &mut QuotientRefMemory,
) -> Result<Vec<Fq>, String> {
    let bytes = &build.bytes;
    let mut values = Vec::new();
    let mut cursor = 0usize;

    for item in &plan.items {
        match item {
            QuotientProgramItem::Identity(_) => {
                let (expr_end, _) = identity_segment(bytes, cursor)?;
                values.push(eval_quotient_identity(
                    &bytes[cursor..expr_end],
                    &build.consts,
                    mem,
                )?);
                cursor = expr_end + quotient_op_len(bytes, expr_end);
            }
            _ => {
                // Native markers evaluate no bytecode; both builds emit the
                // same marker at the same stream position.
                values.push(Fq::ZERO);
                cursor += quotient_op_len(bytes, cursor);
            }
        }
    }

    Ok(values)
}
