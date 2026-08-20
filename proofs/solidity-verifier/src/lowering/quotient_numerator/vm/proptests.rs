// SPDX-License-Identifier: CC0-1.0
//! Property tests for the compact quotient VM compiler, decoders, and rewrite
//! certificates (assurance gap G6, TESTING_STRATEGY.md section 14).
//!
//! The hand-written recognizer tests pin a dozen curated shapes; these
//! properties drive the same pipeline with generated expression trees:
//!
//!   * P1 compiler round-trip: random identity streams built with the limb
//!     recognizers ON and OFF must validate, re-encode byte-identically, and
//!     evaluate -- per identity, under the independent reference interpreter at
//!     several derived assignments -- to exactly the value of the typed
//!     expression they were lowered from, with both builds agreeing.
//!   * P2 encode/decode agreement: every finalized instruction re-encodes
//!     byte-identically through the single operand visitor, and the visitor's
//!     view of instruction extents matches the checked length decoder.
//!   * P3 decoder totality: the checked validation entry points never panic, on
//!     fully arbitrary bytes or on structured corruptions of valid programs;
//!     anything they accept must survive reference evaluation without a panic.
//!   * P4 run-compaction certificates: streams engineered to compact must
//!     produce a nonempty certificate that verifies, and corrupted certificates
//!     must be rejected.
//!
//! Case counts default low enough for tier-1 (`cargo test`) latency; the
//! release job can raise them with `PROPTEST_CASES`.

use midnight_curves::Fq;
use proptest::prelude::*;
use ruint::aliases::U256;

use super::{
    certify::identity_segment,
    check_run_compaction, compact_quotient_runs, quotient_byte_instruction_len_checked,
    reencode_quotient_instruction,
    reference::{eval_quotient_expr, eval_quotient_identity, QuotientRefMemory},
    validate_quotient_const_slots, validate_quotient_program, validate_quotient_reencode,
    QuotientExpr, QuotientIdentity, QuotientIdentityMetadata, QuotientMem, QuotientProgramBuild,
    QuotientProgramBuilder, QuotientTarget, RunRewriteKind, SelectorFoldPlan,
    QUOTIENT_MEM_TOKEN_TABLE, QUOTIENT_VM_LIMBS, QUOTIENT_VM_RUN_COMPACTION_MIN_LEN,
};
use crate::{api::QuotientIdentitySource, lowering::VerifierBuildInputs};

/// Proptest config with an overridable case count.
///
/// `ProptestConfig::with_cases` would shadow the `PROPTEST_CASES` environment
/// override the release job uses, so read the variable explicitly and treat
/// the argument as the tier-1 default.
fn config(default_cases: u32) -> ProptestConfig {
    let cases = std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default_cases);
    ProptestConfig {
        cases,
        ..ProptestConfig::default()
    }
}

// ---------------------------------------------------------------------------
// Expression constructors (local mirrors of the tests.rs helpers).
// ---------------------------------------------------------------------------

fn add(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Add(Box::new(lhs), Box::new(rhs))
}

fn mul(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Mul(Box::new(lhs), Box::new(rhs))
}

fn cnst(value: u64) -> QuotientExpr {
    QuotientExpr::Const(U256::from(value))
}

fn mem(ptr: u32) -> QuotientExpr {
    QuotientExpr::Mem(QuotientMem::Literal(ptr))
}

fn scale(coeff: u64, expr: QuotientExpr) -> QuotientExpr {
    mul(cnst(coeff), expr)
}

/// Synthetic gate-sourced identity around one generated expression.
fn synthetic_identity(
    global_index: usize,
    target: QuotientTarget,
    expr: QuotientExpr,
) -> QuotientIdentity {
    QuotientIdentity {
        meta: QuotientIdentityMetadata {
            global_index,
            source: QuotientIdentitySource::Gate {
                gate_index: global_index,
                gate_name: format!("proptest_gate_{global_index}"),
                constraint_index: 0,
                constraint_name: "proptest_constraint".to_string(),
                polynomial_index: 0,
            },
        },
        lines: Vec::new(),
        var: format!("eval_{global_index}"),
        target,
        expr,
    }
}

/// Lower an all-Identity stream exactly the way the production planner does
/// (`build_quotient_program_items_with_limb_ops` minus the native markers).
/// `finish()` runs every render-time gate: structure/stack validation,
/// const-slot validation, the run-compaction certificate check, and the
/// re-encode round trip.
fn build_stream(
    identities: &[QuotientIdentity],
    selector_count: usize,
    limb_vm_ops: bool,
) -> (QuotientProgramBuild, SelectorFoldPlan) {
    let fold = VerifierBuildInputs::selector_fold_plan(identities, selector_count);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(limb_vm_ops);
    for identity in identities {
        builder.identity_expr(&identity.expr, identity.target, fold.gap_for(identity));
    }
    (builder.finish(), fold)
}

/// Walk a finalized all-Identity program and evaluate each identity segment
/// under the reference interpreter, using only checked decoding.
fn reference_identity_values(
    build: &QuotientProgramBuild,
    identity_count: usize,
    seed: [u8; 32],
) -> Vec<Fq> {
    let bytes = &build.bytes;
    let mut mem = QuotientRefMemory::new(seed);
    let mut cursor = 0usize;
    let mut values = Vec::with_capacity(identity_count);
    for _ in 0..identity_count {
        let (expr_end, _fold_op) = identity_segment(bytes, cursor).expect("identity segment");
        values.push(
            eval_quotient_identity(&bytes[cursor..expr_end], &build.consts, &mut mem)
                .expect("reference evaluation of a validated segment"),
        );
        let fold_len = quotient_byte_instruction_len_checked(bytes, expr_end).expect("fold length");
        cursor = expr_end + fold_len;
    }
    assert_eq!(
        cursor,
        bytes.len(),
        "identity walk must consume the program"
    );
    values
}

/// Directly evaluate the typed expressions at the same derived assignment.
fn expected_identity_values(identities: &[QuotientIdentity], seed: [u8; 32]) -> Vec<Fq> {
    let mut mem = QuotientRefMemory::new(seed);
    identities
        .iter()
        .map(|identity| eval_quotient_expr(&identity.expr, &mut mem))
        .collect()
}

/// Per-instruction decode checks shared by several properties: checked length,
/// visitor re-encode byte identity, and whole-stream re-encode validation.
fn assert_stream_reencodes(bytes: &[u8]) {
    validate_quotient_reencode(bytes).expect("whole-stream re-encode");
    let mut idx = 0usize;
    while idx < bytes.len() {
        let len = quotient_byte_instruction_len_checked(bytes, idx).expect("checked length");
        let reencoded = reencode_quotient_instruction(bytes, idx).expect("re-encode");
        assert_eq!(
            reencoded,
            &bytes[idx..idx + len],
            "instruction at byte {idx} must re-encode byte-identically"
        );
        idx += len;
    }
}

// ---------------------------------------------------------------------------
// Generators.
// ---------------------------------------------------------------------------

/// Word-aligned memory leaves across the u16 and u32 pointer ranges, plus
/// symbolic tokens with and without offsets.
fn arb_quotient_mem() -> impl Strategy<Value = QuotientMem> {
    let tokens: Vec<u8> = QUOTIENT_MEM_TOKEN_TABLE.iter().map(|spec| spec.token).collect();
    prop_oneof![
        4 => (1u32..0x800).prop_map(|word| QuotientMem::Literal(word * 0x20)),
        2 => (0x800u32..0x4000).prop_map(|word| QuotientMem::Literal(word * 0x20)),
        1 => proptest::sample::select(tokens.clone()).prop_map(QuotientMem::Token),
        1 => (proptest::sample::select(tokens), 0u32..64)
            .prop_map(|(token, word)| QuotientMem::TokenOffset(token, word * 0x20)),
    ]
}

/// Free recursive expression mixtures over a small constant pool.
fn arb_quotient_expr() -> impl Strategy<Value = QuotientExpr> {
    let leaf = prop_oneof![
        2 => (1u64..48).prop_map(cnst),
        3 => arb_quotient_mem().prop_map(QuotientExpr::Mem),
    ];
    leaf.prop_recursive(5, 48, 3, |inner| {
        prop_oneof![
            (inner.clone(), inner.clone()).prop_map(|(a, b)| add(a, b)),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| mul(a, b)),
            inner.prop_map(|a| QuotientExpr::Neg(Box::new(a))),
        ]
    })
}

/// Seven-limb linear form over adjacent words (the LIN7 recognizer shape).
fn arb_lin7_expr() -> impl Strategy<Value = QuotientExpr> {
    (
        1u32..0x780,
        proptest::collection::vec(2u64..2000, QUOTIENT_VM_LIMBS),
        0u64..7,
    )
        .prop_map(|(base_word, coeffs, head)| {
            let base = base_word * 0x20;
            let mut expr = cnst(head + 1);
            for (i, coeff) in coeffs.into_iter().enumerate() {
                expr = add(expr, scale(coeff, mem(base + (i as u32) * 0x20)));
            }
            expr
        })
}

/// One limb times a seven-limb row (the BILIN7_ROW recognizer shape).
fn arb_bilin7_row_expr() -> impl Strategy<Value = QuotientExpr> {
    (
        1u32..0x380,
        0x400u32..0x780,
        proptest::collection::vec(2u64..2000, QUOTIENT_VM_LIMBS),
    )
        .prop_map(|(lhs_word, base_word, coeffs)| {
            let lhs = lhs_word * 0x20;
            let base = base_word * 0x20;
            let mut expr = cnst(1);
            for (i, coeff) in coeffs.into_iter().enumerate() {
                expr = add(
                    expr,
                    scale(coeff, mul(mem(lhs), mem(base + (i as u32) * 0x20))),
                );
            }
            expr
        })
}

/// 7x7 pairwise convolution with `i + j`-indexed coefficients (the
/// BILIN7_PAIRWISE recognizer shape).
fn arb_bilin7_pairwise_expr() -> impl Strategy<Value = QuotientExpr> {
    (1u32..0x300, 0x400u32..0x700, 2u64..500).prop_map(|(lhs_word, rhs_word, coeff_seed)| {
        let lhs_base = lhs_word * 0x20;
        let rhs_base = rhs_word * 0x20;
        let mut expr = cnst(1);
        for i in 0..QUOTIENT_VM_LIMBS as u32 {
            for j in 0..QUOTIENT_VM_LIMBS as u32 {
                expr = add(
                    expr,
                    scale(
                        coeff_seed + u64::from(i + j),
                        mul(mem(lhs_base + i * 0x20), mem(rhs_base + j * 0x20)),
                    ),
                );
            }
        }
        expr
    })
}

/// Conditionally gated mixed affine form (the MODARITH7 identity shape):
/// `cond * (c + lin7 + sum coeff*mem + sum coeff*mem*mem)`, optionally with a
/// residue tail outside the gate.
fn arb_modarith7_expr() -> impl Strategy<Value = QuotientExpr> {
    (
        1u32..0x100,
        arb_lin7_expr(),
        proptest::collection::vec((0x600u32..0x780, 2u64..900), 0..3),
        proptest::collection::vec((0x600u32..0x700, 0x700u32..0x780, 2u64..900), 0..3),
        proptest::option::of(2u64..50),
    )
        .prop_map(|(cond_word, lin, mems, prods, residue)| {
            let mut inner = lin;
            for (word, coeff) in mems {
                inner = add(inner, scale(coeff, mem(word * 0x20)));
            }
            for (lhs, rhs, coeff) in prods {
                inner = add(inner, scale(coeff, mul(mem(lhs * 0x20), mem(rhs * 0x20))));
            }
            let gated = mul(mem(cond_word * 0x20), inner);
            match residue {
                Some(extra) => add(gated, scale(extra, mem(0x7e0 * 0x20))),
                None => gated,
            }
        })
}

/// Fifth-power chains (the POW5 recognizer shape), optionally scaled.
fn arb_pow5_expr() -> impl Strategy<Value = QuotientExpr> {
    (1u32..0x780, proptest::option::of(2u64..900)).prop_map(|(word, coeff)| {
        let base = mem(word * 0x20);
        let pow5 = mul(
            mul(base.clone(), base.clone()),
            mul(base.clone(), mul(base.clone(), base)),
        );
        match coeff {
            Some(c) => scale(c, pow5),
            None => pow5,
        }
    })
}

/// One identity expression drawn from the free mixture or a recognizer shape.
fn arb_identity_expr() -> impl Strategy<Value = QuotientExpr> {
    prop_oneof![
        4 => arb_quotient_expr(),
        1 => arb_lin7_expr(),
        1 => arb_bilin7_row_expr(),
        1 => arb_bilin7_pairwise_expr(),
        1 => arb_modarith7_expr(),
        1 => arb_pow5_expr(),
    ]
}

const SELECTOR_BUCKETS: usize = 2;

/// A stream of identities with Main and selector-bucketed targets.
fn arb_identity_stream() -> impl Strategy<Value = Vec<QuotientIdentity>> {
    proptest::collection::vec((arb_identity_expr(), 0usize..=SELECTOR_BUCKETS), 1..6).prop_map(
        |entries| {
            entries
                .into_iter()
                .enumerate()
                .map(|(global_index, (expr, target_pick))| {
                    let target = match target_pick {
                        0 => QuotientTarget::Main,
                        bucket => QuotientTarget::Selector(bucket - 1),
                    };
                    synthetic_identity(global_index, target, expr)
                })
                .collect()
        },
    )
}

// ---------------------------------------------------------------------------
// P1 + P2: compiler round-trip and encode/decode agreement.
// ---------------------------------------------------------------------------

fn check_compiler_round_trip(identities: Vec<QuotientIdentity>) {
    let (optimized, _) = build_stream(&identities, SELECTOR_BUCKETS, true);
    let (baseline, _) = build_stream(&identities, SELECTOR_BUCKETS, false);

    for build in [&optimized, &baseline] {
        validate_quotient_program(&build.bytes).expect("structure validation");
        validate_quotient_const_slots(&build.bytes, build.consts.len())
            .expect("const-slot validation");
        assert_stream_reencodes(&build.bytes);
    }

    for point in 1u8..=4 {
        let seed = [point; 32];
        let expected = expected_identity_values(&identities, seed);
        let actual_optimized = reference_identity_values(&optimized, identities.len(), seed);
        let actual_baseline = reference_identity_values(&baseline, identities.len(), seed);
        assert_eq!(
            actual_optimized, expected,
            "limb-optimized build diverged from the typed expressions"
        );
        assert_eq!(
            actual_baseline, expected,
            "generic-opcode build diverged from the typed expressions"
        );
    }
}

proptest! {
    #![proptest_config(config(48))]

    /// P1/P2 over free expression mixtures and recognizer shapes.
    #[test]
    fn prop_compiler_round_trip(identities in arb_identity_stream()) {
        check_compiler_round_trip(identities);
    }
}

proptest! {
    #![proptest_config(config(4))]

    /// P1 with a constant pool wide enough to overflow u8 constant slots,
    /// exercising the post-residue slot re-check and the u16 slot forms.
    #[test]
    fn prop_compiler_round_trip_wide_const_pool(
        term_count in 260usize..320,
        coeff_base in 2u64..1000,
    ) {
        let mut expr = cnst(1);
        for k in 0..term_count {
            // Distinct coefficients force one constant-table slot per term;
            // stride 0x40 keeps the limb recognizers out of the way so the
            // fused-op and run-compaction paths carry the overflow.
            expr = add(
                expr,
                scale(coeff_base + k as u64, mem(0x1000 + (k as u32) * 0x40)),
            );
        }
        let identities = vec![synthetic_identity(0, QuotientTarget::Main, expr)];
        let (optimized, _) = build_stream(&identities, 0, true);
        prop_assert!(
            optimized.consts.len() > usize::from(u8::MAX),
            "wide pool must overflow the one-byte constant table"
        );
        check_compiler_round_trip(identities);
    }
}

// ---------------------------------------------------------------------------
// P3: decoder totality.
// ---------------------------------------------------------------------------

/// Run every checked validation gate; `Ok(consts_len)` when all accept.
fn checked_gates(bytes: &[u8], const_len: usize) -> Result<(), String> {
    validate_quotient_program(bytes)?;
    validate_quotient_const_slots(bytes, const_len)?;
    validate_quotient_reencode(bytes)?;
    Ok(())
}

/// Whatever the checked gates accept must survive reference evaluation
/// without panicking (errors are fine; aborts are not).
fn evaluate_accepted_stream(bytes: &[u8], consts: &[U256]) {
    let mut mem = QuotientRefMemory::new([0x5eu8; 32]);
    let mut cursor = 0usize;
    while cursor < bytes.len() {
        match identity_segment(bytes, cursor) {
            Ok((expr_end, _)) => {
                let _ = eval_quotient_identity(&bytes[cursor..expr_end], consts, &mut mem);
                match quotient_byte_instruction_len_checked(bytes, expr_end) {
                    Ok(fold_len) => cursor = expr_end + fold_len,
                    Err(_) => break,
                }
            }
            // Native markers or unterminated tails: skip one instruction.
            Err(_) => match quotient_byte_instruction_len_checked(bytes, cursor) {
                Ok(len) => cursor += len,
                Err(_) => break,
            },
        }
    }
}

proptest! {
    #![proptest_config(config(256))]

    /// P3a: fully arbitrary bytes never panic the checked entry points.
    #[test]
    fn prop_checked_decoders_are_total_on_arbitrary_bytes(
        bytes in proptest::collection::vec(any::<u8>(), 0..192),
    ) {
        if checked_gates(&bytes, 4).is_ok() {
            let consts = vec![U256::from(7u64); 4];
            evaluate_accepted_stream(&bytes, &consts);
        }
    }
}

proptest! {
    #![proptest_config(config(64))]

    /// P3b: structured corruptions of valid programs either fail validation
    /// or evaluate without panicking.
    #[test]
    fn prop_checked_decoders_survive_structured_corruption(
        identities in arb_identity_stream(),
        cut in any::<proptest::sample::Index>(),
        flip_at in any::<proptest::sample::Index>(),
        flip_with in 1u8..=255,
        splice in any::<proptest::sample::Index>(),
    ) {
        let (build, _) = build_stream(&identities, SELECTOR_BUCKETS, true);
        let valid = build.bytes.clone();
        prop_assume!(!valid.is_empty());

        let truncated = valid[..cut.index(valid.len())].to_vec();
        let mut flipped = valid.clone();
        let at = flip_at.index(flipped.len());
        flipped[at] ^= flip_with;
        let mut spliced = valid.clone();
        let split = splice.index(valid.len());
        spliced.extend_from_slice(&valid[split..]);

        for mutated in [truncated, flipped, spliced] {
            if checked_gates(&mutated, build.consts.len()).is_ok() {
                evaluate_accepted_stream(&mutated, &build.consts);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// P4: run-compaction certificates on generated shapes.
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(config(32))]

    /// P4: compactable streams produce nonempty, verifying certificates, and
    /// deterministic corruptions of those certificates are rejected.
    #[test]
    fn prop_run_compaction_certificates_verify_and_are_tamper_evident(
        lin_terms in 0usize..8,
        product_terms in 0usize..8,
        coeff in 2u64..200,
    ) {
        // Ensure at least one compactable run regardless of the draws.
        let lin_terms = lin_terms + QUOTIENT_VM_RUN_COMPACTION_MIN_LEN;

        // Non-adjacent strides keep the limb recognizers out; the generic
        // fused ops below are what run compaction rewrites.
        let mut expr = cnst(1);
        for k in 0..lin_terms {
            expr = add(expr, scale(coeff + k as u64, mem(0x2000 + (k as u32) * 0x40)));
        }
        for k in 0..product_terms {
            expr = add(
                expr,
                scale(
                    coeff + 100 + k as u64,
                    mul(mem(0x4000 + (k as u32) * 0x40), mem(0x6000 + (k as u32) * 0x40)),
                ),
            );
        }

        let mut builder = QuotientProgramBuilder::with_limb_vm_ops(false);
        builder.emit_expr(&expr);
        let raw = builder.bytes.clone();

        let (compacted, cert) = compact_quotient_runs(&raw);
        prop_assert!(
            !cert.rewrites.is_empty(),
            "a {lin_terms}-term affine chain must compact"
        );
        check_run_compaction(&raw, &compacted, &cert).expect("honest certificate verifies");

        // Dropping a rewrite is always detectable: the rewrite replaced its
        // input bytes with a strictly different encoding.
        let mut dropped = cert.clone();
        dropped.rewrites.pop();
        prop_assert!(check_run_compaction(&raw, &compacted, &dropped).is_err());

        // A wrong rewrite kind is always detectable.
        let mut wrong_kind = cert.clone();
        let kind = &mut wrong_kind.rewrites[0].kind;
        *kind = match *kind {
            RunRewriteKind::RunMemMemConst => RunRewriteKind::RunConstMem,
            RunRewriteKind::RunConstMem => RunRewriteKind::AffineSum,
            RunRewriteKind::AffineSum => RunRewriteKind::RunConstMem,
        };
        prop_assert!(check_run_compaction(&raw, &compacted, &wrong_kind).is_err());

        // Truncating a rewrite's input span by one whole instruction changes
        // the expanded term count and is always detectable.
        let mut short_input = cert.clone();
        let rewrite = &mut short_input.rewrites[0];
        let first_len = quotient_byte_instruction_len_checked(&raw, rewrite.input.start)
            .expect("first fused instruction length");
        rewrite.input.end -= first_len;
        prop_assert!(check_run_compaction(&raw, &compacted, &short_input).is_err());
    }
}
