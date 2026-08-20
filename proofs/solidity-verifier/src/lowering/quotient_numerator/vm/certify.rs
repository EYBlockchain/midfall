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
    quotient_expr_from_yul, quotient_op_len,
    reference::{eval_quotient_expr, eval_quotient_identity, QuotientRefMemory},
    QuotientExpr, QuotientMem, QuotientProgramBuild, QuotientProgramItem, QuotientProgramPlan,
    QuotientTarget, Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_NATIVE_IDENTITY, Q_OP_NATIVE_LOOKUP,
    Q_OP_NATIVE_PERMUTATION,
};
use crate::{api::QuotientIdentitySource, lowering::render::Halo2VerifyingKey};

/// Seed for the certification assignment.
///
/// The seed is deterministic so failing renders reproduce exactly, but it is
/// derived from the finalized artifact rather than fixed globally. This keeps
/// the sampled assignment independent of any circuit author's pre-render view
/// of the quotient program while preserving reproducible diagnostics.
/// v4: the seed binds EVERY execution surface's expression tree (inline,
/// interpreted, native gate, native permutation, native lookup, structured
/// trash tail), matching the frame differential's binding -- v3 bound only
/// the interpreted exprs, so the challenge was fixed before some compared
/// artifacts were.
const QUOTIENT_CERTIFY_SEED_DOMAIN: &[u8] = b"midfall/quotient-vm/certify-seed/v4";

/// Number of independent evaluation points each certification pass samples.
///
/// One point already bounds accidental-miscompile escape probability by
/// roughly `deg/2^255` (Schwartz-Zippel); three points cost microseconds and
/// cube it.
pub(crate) const QUOTIENT_CERTIFY_POINTS: u64 = 3;

/// Domain tag separating per-point certification assignments from the
/// artifact-bound base seed and from the frame differential's per-iteration
/// seeds (`oracle::frame_differential_seed` keeps its own domain on purpose:
/// the empirical leg must not sample the same assignments the structural leg
/// already passed).
const QUOTIENT_CERTIFY_POINT_DOMAIN: &[u8] = b"midfall/quotient-vm/certify-point/v1";

/// Derive one evaluation-point seed from the artifact-bound base seed.
pub(crate) fn certify_point_seed(base: [u8; 32], point: u64) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(QUOTIENT_CERTIFY_POINT_DOMAIN);
    hasher.update(base);
    hasher.update(point.to_be_bytes());
    hasher.finalize().into()
}

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

/// Expression trees for EVERY execution surface, in execution order.
///
/// The certification challenge must be fixed only after every compared
/// artifact is; binding all six surfaces (not just the interpreted ones)
/// matches what the frame differential binds in `src/test.rs`.
fn all_surface_exprs(plan: &QuotientProgramPlan) -> Result<Vec<&QuotientExpr>, String> {
    Ok(plan
        .identities_in_execution_order()
        .map_err(|err| format!("certification could not walk the execution stream: {err}"))?
        .into_iter()
        .map(|(identity, _)| &identity.expr)
        .collect())
}

/// Pin the property the whole certification independence argument rests on.
///
/// Gate expressions are lowered independently from `Expression<Fq>` by
/// `quotient_expr_from_plonk_expr`, so comparing bytecode against them is a
/// genuine N-version check. Permutation/lookup/trash expressions are
/// re-parsed from the emitter's own Yul (roadmap gap G1) and would certify
/// vacuously -- the planner must therefore never route them through the
/// typed-lowering surfaces. This was previously true by construction of
/// `quotient_program_plan` but asserted nowhere.
fn check_certification_independence(plan: &QuotientProgramPlan) -> Result<(), String> {
    let require_gate = |identity: &super::QuotientIdentity, surface: &str| {
        if matches!(identity.meta.source, QuotientIdentitySource::Gate { .. }) {
            Ok(())
        } else {
            Err(format!(
                "identity {} on the {surface} surface has non-gate source {:?}; the                  certification independence argument requires gate-only typed-lowering                  surfaces (non-gate expressions are parsed from the emitter's own Yul                  and would certify vacuously)",
                identity.meta.global_index, identity.meta.source
            ))
        }
    };
    for identity in &plan.inline_identities {
        require_gate(identity, "inline")?;
    }
    for identity in &plan.native_identities {
        require_gate(identity, "native-gate")?;
    }
    let mut permutation_markers = 0usize;
    let mut lookup_markers = 0usize;
    for item in &plan.items {
        match item {
            QuotientProgramItem::Identity(identity) => require_gate(identity, "interpreted")?,
            QuotientProgramItem::NativePermutation => permutation_markers += 1,
            QuotientProgramItem::NativeLookup => lookup_markers += 1,
            QuotientProgramItem::NativeIdentity(_) => {}
        }
    }
    if permutation_markers > 1 {
        return Err(format!(
            "quotient plan carries {permutation_markers} native permutation markers; at most one              is meaningful"
        ));
    }
    if lookup_markers > 1 {
        return Err(format!(
            "quotient plan carries {lookup_markers} native lookup markers; at most one is              meaningful"
        ));
    }
    for identity in &plan.structured_tail_identities {
        if !matches!(identity.meta.source, QuotientIdentitySource::Trash { .. }) {
            return Err(format!(
                "structured-tail identity {} has non-trash source {:?}",
                identity.meta.global_index, identity.meta.source
            ));
        }
    }
    Ok(())
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
    check_certification_independence(plan)?;
    let exprs = all_surface_exprs(plan)?;
    let vk_payload = vk.bytes();
    let seed = derive_certify_seed(&[build], &exprs, &vk_payload);
    for point in 0..QUOTIENT_CERTIFY_POINTS {
        let mut mem = QuotientRefMemory::new(certify_point_seed(seed, point));
        certify_program_at_point(plan, build, &mut mem)
            .map_err(|err| format!("certification point {point}: {err}"))?;
    }
    Ok(())
}

/// Value-check every interpreted identity and native marker at one sampled
/// assignment.
fn certify_program_at_point(
    plan: &QuotientProgramPlan,
    build: &QuotientProgramBuild,
    mem: &mut QuotientRefMemory,
) -> Result<(), String> {
    let bytes = &build.bytes;
    let mut cursor = 0usize;

    for (item_idx, item) in plan.items.iter().enumerate() {
        match item {
            QuotientProgramItem::Identity(identity) => {
                let (expr_end, fold_op) = identity_segment(bytes, cursor)
                    .map_err(|err| format!("quotient item {item_idx}: {err}"))?;

                let actual = eval_quotient_identity(&bytes[cursor..expr_end], &build.consts, mem)
                    .map_err(|err| {
                    format!(
                        "quotient identity {} ({:?}): {err}",
                        identity.meta.global_index, identity.meta.source
                    )
                })?;
                let expected = eval_quotient_expr(&identity.expr, mem);

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
///
/// `pub(crate)` so the quotient frame differential's negative controls can
/// target a program byte that provably sits inside a decoded identity
/// expression rather than guessing from window geometry.
pub(crate) fn identity_segment(bytes: &[u8], start: usize) -> Result<(usize, u8), String> {
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
    let exprs = all_surface_exprs(plan)?;
    let vk_payload = vk.bytes();
    let seed = derive_certify_seed(&[optimized, baseline], &exprs, &vk_payload);

    for point in 0..QUOTIENT_CERTIFY_POINTS {
        // One assignment per point, shared by both builds: `QuotientRefMemory`
        // is a pure function of (seed, address), so sharing is a cache, not a
        // sequencing dependency.
        let mut mem = QuotientRefMemory::new(certify_point_seed(seed, point));

        let optimized_values = identity_values(plan, optimized, &mut mem)?;
        let baseline_values = identity_values(plan, baseline, &mut mem)?;

        if optimized_values.len() != baseline_values.len() {
            return Err(format!(
                "quotient dual build disagrees on identity count: {} with limb opcodes, {} without",
                optimized_values.len(),
                baseline_values.len()
            ));
        }

        for (position, (lhs, rhs)) in
            optimized_values.iter().zip(baseline_values.iter()).enumerate()
        {
            if lhs != rhs {
                return Err(format!(
                    "quotient limb superinstructions changed the value of interpreted identity at \
                     stream position {position} (certification point {point}): {lhs:?} with limb \
                     opcodes, {rhs:?} without. One of the shape recognizers is unsound for this \
                     gate shape."
                ));
            }
        }
    }

    Ok(())
}

/// TRANSITIONAL (delete in roadmap phase P5): value-check the inline gate
/// prefix.
///
/// The inline prefix renders `identity.lines` -- Yul from the string-based
/// `Evaluator` -- while `identity.expr` is the independent typed lowering
/// from `Expression<Fq>`. Nothing else value-checks that pair: the inline
/// identities are absent from `plan.items`, so `certify_quotient_program`
/// never sees them. Parse the rendered lines back to an expression with the
/// same parser the structured families use and require value agreement at
/// every certification point.
///
/// This check is genuine only while gate Yul comes from the string emitter;
/// when phase P5 prints gate Yul from `.expr`, it becomes a tautology and
/// must be deleted -- the native trace anchor (ids 30_000+i) is the formula
/// oracle from then on. The `specialize_limb7_chains` string pass applied at
/// render time is NOT covered here; the per-PR frame differential covers it
/// empirically.
pub(crate) fn certify_inline_prefix(
    plan: &QuotientProgramPlan,
    build: &QuotientProgramBuild,
    vk: &Halo2VerifyingKey,
) -> Result<(), String> {
    if plan.inline_identities.is_empty() {
        return Ok(());
    }
    let exprs = all_surface_exprs(plan)?;
    let vk_payload = vk.bytes();
    let seed = derive_certify_seed(&[build], &exprs, &vk_payload);

    for point in 0..QUOTIENT_CERTIFY_POINTS {
        let mut mem = QuotientRefMemory::new(certify_point_seed(seed, point));
        for identity in &plan.inline_identities {
            let parsed = quotient_expr_from_yul(&identity.lines, &identity.var);
            let rendered = eval_quotient_expr(&parsed, &mut mem);
            let typed = eval_quotient_expr(&identity.expr, &mut mem);
            if rendered != typed {
                return Err(format!(
                    "inline gate identity {} ({:?}) diverges at certification point {point}: the \
                     rendered Yul evaluates to {rendered:?} but the typed lowering evaluates to \
                     {typed:?}. The string emitter and the typed gate lowering disagree on this \
                     gate shape.",
                    identity.meta.global_index, identity.meta.source
                ));
            }
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
