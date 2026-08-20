// SPDX-License-Identifier: CC0-1.0
//! Typed permutation/LogUp/trash identity builders (roadmap P5.b).
//!
//! THE single in-crate statement of the three non-gate identity families,
//! transcribed from the native verifier
//! (`midfall/proofs/src/plonk/permutation.rs::expressions`,
//! `logup.rs::Evaluated::expressions`, `trash.rs::Evaluated::expressions`)
//! and pinned per-value against it by the `native_anchor` tier-1 test
//! (trace ids `30_000 + global_index`).
//!
//! Until this module existed, these formulas lived only as hand-written Yul
//! in `yul_emit.rs`, and the typed `QuotientExpr` trees the certifier, the
//! frame-differential oracle, and the compact VM consume were RE-PARSED from
//! that same Yul -- so a formula transcription error was invisible to every
//! structural check (audit gap G1). The builders below construct the trees
//! directly; the Yul round-trip for these families is gone.
//!
//! ## Tree-shape compatibility
//!
//! The trees deliberately reproduce, node for node, the shapes the deleted
//! flat emitters produced after Yul parsing (including historical warts such
//! as `Add(Mul(Const(0), theta), e0)` as the first Horner step and
//! `Add(Const(0), Neg(x))` for negation inside embedded gate expressions), so
//! the compiled VM bytecode -- and therefore every pinned VK payload and
//! fixture -- is byte-for-byte unchanged by the swap. A structural-equality
//! A/B test enforced this across the shape corpus while both paths existed.

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::plonk::{Any, Column, ConstraintSystem, Expression};
use ruint::aliases::U256;

use crate::lowering::{
    encoding::{fe_to_u256, ConstraintSystemMeta, Data},
    quotient_numerator::vm::{
        word_to_quotient_expr, QuotientExpr, QuotientMem, Q_MEM_BETA, Q_MEM_GAMMA, Q_MEM_L0,
        Q_MEM_L_BLIND, Q_MEM_L_LAST, Q_MEM_THETA, Q_MEM_TRASH_CHALLENGE, Q_MEM_X,
    },
};

/// Symbolic memory-token leaf.
fn tok(token: u8) -> QuotientExpr {
    QuotientExpr::Mem(QuotientMem::Token(token))
}

/// Constant leaf from a `U256`.
fn konst(value: U256) -> QuotientExpr {
    QuotientExpr::Const(value)
}

/// Constant one.
fn one() -> QuotientExpr {
    konst(U256::from(1u64))
}

/// Constant zero.
fn zero() -> QuotientExpr {
    konst(U256::ZERO)
}

/// Constant leaf from an Fr element.
fn fe(value: &Fq) -> QuotientExpr {
    konst(fe_to_u256::<Fq>(value))
}

/// Fr addition node.
fn add(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Add(Box::new(lhs), Box::new(rhs))
}

/// Fr multiplication node.
fn mul(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Mul(Box::new(lhs), Box::new(rhs))
}

/// Fr negation node.
fn neg(inner: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Neg(Box::new(inner))
}

/// Resolve a permutation-column evaluation at rotation 0, mirroring the
/// verifier semantics: simple selectors synthesize constant one; every other
/// column reads its decoded proof eval.
fn column_eval(meta: &ConstraintSystemMeta, data: &Data, column: &Column<Any>) -> QuotientExpr {
    let col_idx = column.index();
    match column.column_type() {
        Any::Advice(_) => word_to_quotient_expr(
            *data
                .advice_evals
                .get(&(col_idx, 0))
                .expect("advice eval present in permutation chunk"),
        ),
        Any::Fixed => {
            if meta.protocol.simple_selector_cols.contains(&col_idx) {
                one()
            } else {
                word_to_quotient_expr(
                    *data
                        .fixed_evals
                        .get(&(col_idx, 0))
                        .expect("fixed eval present in permutation chunk"),
                )
            }
        }
        Any::Instance => instance_eval(meta, data, col_idx, 0),
    }
}

/// Resolve an instance query from proof evals or the local interpolation.
fn instance_eval(
    meta: &ConstraintSystemMeta,
    data: &Data,
    column_index: usize,
    rotation: i32,
) -> QuotientExpr {
    if column_index < meta.protocol.num_committed_instances {
        word_to_quotient_expr(
            *data
                .committed_instance_evals
                .get(&(column_index, rotation))
                .expect("committed instance eval present"),
        )
    } else {
        // The constructor rejects rotated public-instance queries; fail closed
        // here too (see `DataQuotientExpressionEnv::instance`).
        assert_eq!(
            rotation, 0,
            "rotated public instance query reached identity lowering"
        );
        word_to_quotient_expr(data.instance_eval)
    }
}

// ----------------------------------------------------------------------
// Embedded-Expression lowering.
//
// LogUp inputs/tables/selectors and trash constraints embed full Halo2
// `Expression`s. These are lowered with the SAME top-level sum-fusion the
// gate Yul emitter applies (constants folded, negations absorbed into
// coefficients, sums flattened left-associatively), so the trees match what
// the Yul round-trip used to produce.
// ----------------------------------------------------------------------

/// Lower an embedded expression with top-level additive-term fusion.
fn lower_fused(
    meta: &ConstraintSystemMeta,
    data: &Data,
    expression: &Expression<Fq>,
) -> QuotientExpr {
    if let Some(tree) = lower_sum_fused(meta, data, expression) {
        return tree;
    }
    lower_basic(meta, data, expression)
}

/// Try to flatten a sum into a folded constant plus scaled terms.
fn lower_sum_fused(
    meta: &ConstraintSystemMeta,
    data: &Data,
    expression: &Expression<Fq>,
) -> Option<QuotientExpr> {
    let mut terms = Vec::new();
    let mut constant = Fq::ZERO;
    collect_sum_terms(expression, Fq::ONE, &mut constant, &mut terms);

    terms.retain(|(coeff, _)| !coeff.is_zero_vartime());
    let has_constant = !constant.is_zero_vartime();
    let should_fuse = has_constant
        || terms.len() > 1
        || terms.first().is_some_and(|(coeff, _)| *coeff != Fq::ONE);
    if !should_fuse {
        return None;
    }

    let mut acc = has_constant.then(|| fe(&constant));
    for (coeff, term) in terms {
        let tree = lower_scaled_term(meta, data, term, coeff);
        acc = Some(match acc {
            Some(acc_tree) => add(acc_tree, tree),
            None => tree,
        });
    }
    Some(acc.unwrap_or_else(zero))
}

/// Recursively collect additive terms with their accumulated coefficient.
fn collect_sum_terms<'b>(
    expression: &'b Expression<Fq>,
    coeff: Fq,
    constant: &mut Fq,
    terms: &mut Vec<(Fq, &'b Expression<Fq>)>,
) {
    match expression {
        Expression::Constant(value) => {
            *constant += coeff * value;
        }
        Expression::Negated(inner) => {
            collect_sum_terms(inner, -coeff, constant, terms);
        }
        Expression::Sum(lhs, rhs) => {
            collect_sum_terms(lhs, coeff, constant, terms);
            collect_sum_terms(rhs, coeff, constant, terms);
        }
        Expression::Scaled(inner, scale) => {
            collect_sum_terms(inner, coeff * scale, constant, terms);
        }
        _ => terms.push((coeff, expression)),
    }
}

/// Lower one fused term multiplied by a known Fr coefficient.
fn lower_scaled_term(
    meta: &ConstraintSystemMeta,
    data: &Data,
    term: &Expression<Fq>,
    coeff: Fq,
) -> QuotientExpr {
    let coeff_is_one = coeff == Fq::ONE;
    if let Expression::Product(lhs, rhs) = term {
        let product = mul(lower_basic(meta, data, lhs), lower_basic(meta, data, rhs));
        return if coeff_is_one {
            product
        } else {
            mul(product, fe(&coeff))
        };
    }
    let tree = lower_basic(meta, data, term);
    if coeff_is_one {
        tree
    } else {
        mul(tree, fe(&coeff))
    }
}

/// Plain syntax-directed lowering (the emitter's `evaluate_basic` shape).
fn lower_basic(
    meta: &ConstraintSystemMeta,
    data: &Data,
    expression: &Expression<Fq>,
) -> QuotientExpr {
    expression.evaluate(
        &|scalar| fe(&scalar),
        &|_| panic!("virtual selectors must be removed before identity lowering"),
        &|query| {
            let column_index = query.column_index();
            if meta.protocol.simple_selector_cols.contains(&column_index) {
                one()
            } else {
                word_to_quotient_expr(
                    *data
                        .fixed_evals
                        .get(&(column_index, query.rotation().0))
                        .expect("fixed eval present"),
                )
            }
        },
        &|query| {
            word_to_quotient_expr(
                *data
                    .advice_evals
                    .get(&(query.column_index(), query.rotation().0))
                    .expect("advice eval present"),
            )
        },
        &|query| instance_eval(meta, data, query.column_index(), query.rotation().0),
        &|challenge| word_to_quotient_expr(data.challenges[challenge.index()]),
        // Negation keeps the emitter's `addmod(0, sub(r, x), r)` shape.
        &|inner| add(zero(), neg(inner)),
        &|lhs, rhs| add(lhs, rhs),
        &|lhs, rhs| mul(lhs, rhs),
        &|inner, scalar| mul(inner, fe(&scalar)),
    )
}

/// Horner-fold a slice of embedded expressions over a challenge token:
/// `acc = acc * challenge + expr`, starting from constant zero.
fn horner_compress(
    meta: &ConstraintSystemMeta,
    data: &Data,
    expressions: &[Expression<Fq>],
    challenge: u8,
) -> QuotientExpr {
    if expressions.is_empty() {
        return zero();
    }
    let mut acc: Option<QuotientExpr> = None;
    for expression in expressions {
        let value = lower_fused(meta, data, expression);
        let prev = acc.unwrap_or_else(zero);
        acc = Some(add(mul(prev, tok(challenge)), value));
    }
    acc.expect("non-empty expression fold")
}

// ----------------------------------------------------------------------
// Permutation identities.
//
// Native order (permutation.rs::expressions):
//   l_0 * (1 - z_0)                             (first set)
//   l_last * (z_n^2 - z_n)                      (last set)
//   l_0 * (z_i - z_{i-1}@last)                  (each set i >= 1)
//   per chunk i of chunk_len columns:
//     (z_i@next * PROD_j (eval_j + beta * sigma_j + gamma)
//      - z_i * PROD_j (eval_j + delta^{i*chunk_len+j} * beta * x + gamma))
//     * (1 - (l_last + l_blind))
// ----------------------------------------------------------------------

/// Build the permutation-argument identities in native verifier order.
pub(crate) fn permutation_identity_exprs(
    meta: &ConstraintSystemMeta,
    data: &Data,
) -> Vec<QuotientExpr> {
    let num_sets = meta.protocol.num_permutation_zs;
    if num_sets == 0 {
        return Vec::new();
    }

    let chunk_len = meta.protocol.permutation_chunk_len;
    let columns = &meta.protocol.permutation_columns;
    let z_evals = &data.permutation_z_evals;
    let mut out = Vec::new();

    // 1. First-set boundary: l_0 * (1 - z_0).
    let z0 = word_to_quotient_expr(z_evals.first().expect("perm sets non-empty").0);
    out.push(mul(tok(Q_MEM_L0), add(one(), neg(z0))));

    // 2. Last-set boundary: l_last * (z_n^2 - z_n).
    let zn = word_to_quotient_expr(z_evals.last().expect("perm sets non-empty").0);
    out.push(mul(
        tok(Q_MEM_L_LAST),
        add(mul(zn.clone(), zn.clone()), neg(zn)),
    ));

    // 3. Set-to-set continuity: l_0 * (z_i - z_{i-1}@last).
    for i in 1..num_sets {
        let zi = word_to_quotient_expr(z_evals[i].0);
        let z_prev_last =
            word_to_quotient_expr(z_evals[i - 1].2.expect("non-last set has last eval"));
        out.push(mul(tok(Q_MEM_L0), add(zi, neg(z_prev_last))));
    }

    // 4. Per-set product equality.
    let delta = Fq::DELTA;
    for (set_idx, ((z_cur, z_next, _), chunk_cols)) in
        z_evals.iter().zip(columns.chunks(chunk_len)).enumerate()
    {
        let active = add(one(), neg(add(tok(Q_MEM_L_LAST), tok(Q_MEM_L_BLIND))));

        // left = z_next * PROD (eval + beta * sigma + gamma)
        let mut left = word_to_quotient_expr(*z_next);
        for col in chunk_cols {
            let sigma = word_to_quotient_expr(
                *data.permutation_evals.get(col).expect("permutation eval present"),
            );
            let term = add(
                add(column_eval(meta, data, col), mul(tok(Q_MEM_BETA), sigma)),
                tok(Q_MEM_GAMMA),
            );
            left = mul(left, term);
        }

        // right = z_cur * PROD (eval + delta_pow + gamma), where the delta
        // ladder starts at beta * x * delta^(set_idx * chunk_len) and each
        // later column multiplies one more delta in.
        let initial_delta = delta.pow_vartime([(set_idx * chunk_len) as u64]);
        let mut delta_pow = mul(mul(tok(Q_MEM_BETA), tok(Q_MEM_X)), fe(&initial_delta));
        let mut right = word_to_quotient_expr(*z_cur);
        let last_col_idx = chunk_cols.len().saturating_sub(1);
        for (col_pos, col) in chunk_cols.iter().enumerate() {
            let term = add(
                add(column_eval(meta, data, col), delta_pow.clone()),
                tok(Q_MEM_GAMMA),
            );
            right = mul(right, term);
            if col_pos != last_col_idx {
                delta_pow = mul(delta_pow, fe(&delta));
            }
        }

        out.push(mul(active, add(left, neg(right))));
    }

    out
}

// ----------------------------------------------------------------------
// LogUp identities.
//
// Native order (logup.rs::Evaluated::expressions), per lookup argument:
//   boundary = (l_0 + l_last) * Z
//   per chunk c (division-free form of the native inversion):
//     helper_c = h_c * PROD_j (f_j + beta) - SUM_j PROD_{k != j} (f_k + beta)
//   accumulator =
//     ((Z@next - Z - s * SUM h_i) * (t + beta) + m) * (1 - (l_last + l_blind))
// ----------------------------------------------------------------------

/// Build the LogUp identities in native verifier order.
pub(crate) fn lookup_identity_exprs(
    cs: &ConstraintSystem<Fq>,
    meta: &ConstraintSystemMeta,
    data: &Data,
) -> Vec<QuotientExpr> {
    if meta.protocol.num_lookups == 0 {
        return Vec::new();
    }

    let cs_degree = cs.degree();
    let mut out = Vec::new();

    for (lookup_idx, lookup) in cs.lookups().iter().enumerate() {
        let chunked = lookup.chunk_by_degree(cs_degree);
        let (m_eval, h_evals, z_eval, z_next_eval) = &data.lookup_evals[lookup_idx];

        // Boundary: (l_0 + l_last) * Z.
        out.push(mul(
            add(tok(Q_MEM_L0), tok(Q_MEM_L_LAST)),
            word_to_quotient_expr(*z_eval),
        ));

        // Fail closed on a chunk/helper-eval count mismatch: zip would
        // otherwise silently drop the excess chunks, removing helper
        // constraints from the numerator.
        assert_eq!(
            chunked.input_expression_chunks().len(),
            h_evals.len(),
            "lookup {lookup_idx}: input chunk count {} != helper eval count {}",
            chunked.input_expression_chunks().len(),
            h_evals.len(),
        );
        for (input_chunk, h_eval) in chunked.input_expression_chunks().iter().zip(h_evals.iter()) {
            // f_plus_beta[j] = theta-compress(input_j) + beta.
            let f_plus_beta: Vec<QuotientExpr> = input_chunk
                .iter()
                .map(|parallel_input| {
                    add(
                        horner_compress(meta, data, parallel_input, Q_MEM_THETA),
                        tok(Q_MEM_BETA),
                    )
                })
                .collect();

            let k = f_plus_beta.len();
            if k == 0 {
                // Unreachable today (BatchedArgument::new requires >= 1
                // parallel lookup and slice::chunks never yields an empty
                // chunk), but keep the reference-faithful value: the native
                // verifier computes h * (empty product = 1) - (empty sum = 0)
                // = h, enforcing h == 0.
                out.push(word_to_quotient_expr(*h_eval));
                continue;
            }

            // P = PROD_j f_plus_beta[j].
            let mut product = f_plus_beta[0].clone();
            for fb in &f_plus_beta[1..] {
                product = mul(product, fb.clone());
            }

            // partial[j] = prefix[j] * suffix[j] via shared prefix/suffix
            // products, exactly like the native inversion-free evaluation.
            let mut prefix = Vec::with_capacity(k);
            prefix.push(one());
            for j in 1..k {
                prefix.push(mul(prefix[j - 1].clone(), f_plus_beta[j - 1].clone()));
            }
            let mut suffix = vec![QuotientExpr::Const(U256::ZERO); k];
            suffix[k - 1] = one();
            for j in (0..k - 1).rev() {
                suffix[j] = mul(suffix[j + 1].clone(), f_plus_beta[j + 1].clone());
            }

            let mut sum = mul(prefix[0].clone(), suffix[0].clone());
            for j in 1..k {
                sum = add(sum, mul(prefix[j].clone(), suffix[j].clone()));
            }

            // helper = h * P - sum.
            out.push(add(mul(word_to_quotient_expr(*h_eval), product), neg(sum)));
        }

        // Accumulator: active * ((Z@next - Z - s * SUM h) * (t + beta) + m).
        let active = add(one(), neg(add(tok(Q_MEM_L_LAST), tok(Q_MEM_L_BLIND))));
        let sum_h = match h_evals.split_first() {
            Some((first, rest)) => {
                let mut sum = word_to_quotient_expr(*first);
                for h in rest {
                    sum = add(sum, word_to_quotient_expr(*h));
                }
                sum
            }
            None => zero(),
        };
        let selector = lower_fused(meta, data, chunked.selector_expression());
        let diff = add(
            word_to_quotient_expr(*z_next_eval),
            neg(add(word_to_quotient_expr(*z_eval), mul(selector, sum_h))),
        );
        let table = horner_compress(meta, data, chunked.table_expressions(), Q_MEM_THETA);
        let core = add(
            mul(diff, add(table, tok(Q_MEM_BETA))),
            word_to_quotient_expr(*m_eval),
        );
        out.push(mul(active, core));
    }

    out
}

// ----------------------------------------------------------------------
// Trash identities.
//
// Native form (trash.rs::Evaluated::expressions), per trashcan:
//   Horner_{trash_challenge}(constraint_exprs) - (1 - selector) * trash_eval
// ----------------------------------------------------------------------

/// Build the trash-argument identities in native verifier order.
pub(crate) fn trash_identity_exprs(
    cs: &ConstraintSystem<Fq>,
    meta: &ConstraintSystemMeta,
    data: &Data,
) -> Vec<QuotientExpr> {
    if meta.protocol.num_trashcans == 0 {
        return Vec::new();
    }

    let mut out = Vec::new();
    for (idx, argument) in cs.trashcans().iter().enumerate() {
        let compressed = horner_compress(
            meta,
            data,
            argument.constraint_expressions(),
            Q_MEM_TRASH_CHALLENGE,
        );
        let selector = lower_fused(meta, data, argument.selector());
        let scaled = mul(
            add(one(), neg(selector)),
            word_to_quotient_expr(data.trashcan_evals[idx]),
        );
        out.push(add(compressed, neg(scaled)));
    }

    out
}
