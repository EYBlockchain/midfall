// SPDX-License-Identifier: CC0-1.0
#![allow(clippy::useless_format)]

//! Batched identity numerator emitter.
//!
//! This module walks the gates / permutation / lookup / trash arguments
//! stored in a `midnight_proofs::plonk::ConstraintSystem` and emits the
//! Yul lines that compute their per-row contributions to
//! `quotient_eval_numer` at the evaluation challenge `x`.
//!
//! The name is historical: this is not an evaluator for the quotient
//! polynomial `h(x)`. It reconstructs the batched identity numerator
//! `nu_y(x)`. The generated verifier later stores `-nu_y(x)` as the
//! expected opening scalar for the linearized commitment; the commitment
//! side already includes the quotient-limb factor `(1 - x^n)`.
//!
//! ## Step 4 status (2026-04-26)
//!
//! All four emitters are now ported:
//!
//!   * [`Evaluator::gate_computations_tagged`] — per-gate `polynomials()`
//!   * [`Evaluator::permutation_computations`] — boundary + product equality
//!   * [`Evaluator::lookup_computations`]    — boundary + helper + accumulator
//!   * [`Evaluator::trashcan_computations`]  — `compressed - (1-q)*trash`
//!
//! Each returns a `Vec<(Vec<String>, String)>` where the inner pair is
//! `(yul_lines, final_var)`; the caller in `lowering/quotient.rs` folds the
//! final value into the compact quotient VM state or a native callback body.
//!
//! All emitters reference well-known Yul memory pointers that the
//! verifier prologue populates before invoking the quotient-numerator block.
//! Names follow the generated-verifier memory convention, including
//! `TRASH_CHALLENGE_MPTR` for the Midnight trash argument.

use std::{cell::RefCell, cmp::Ordering, collections::HashMap};

use ff::Field;
use midnight_curves::Fq;
use midnight_proofs::plonk::{Any, Column, ConstraintSystem, Expression};

use crate::lowering::{
    encoding::{fe_to_u256, ConstraintSystemMeta, Data, Location, Value, Word},
    quotient_numerator::vm::u256_string,
    yul_ir::YulValue,
};

#[derive(Debug)]
pub(crate) struct Evaluator<'a> {
    /// Source constraint system whose identities are emitted.
    cs: &'a ConstraintSystem<Fq>,
    /// Codegen metadata for query order and selector handling.
    meta: &'a ConstraintSystemMeta,
    /// Concrete memory/calldata handles for all queried values.
    data: &'a Data,
    /// Whether five repeated factors should be lowered through `q_pow5`.
    use_pow5_helper: bool,
    /// Local variable counter for the current emitted identity.
    var_counter: RefCell<usize>,
    /// Per-identity expression text to variable-name cache.
    var_cache: RefCell<HashMap<String, String>>,
}

/// Yul computation plus source metadata for one gate polynomial.
#[derive(Clone, Debug)]
pub(crate) struct GateComputation {
    pub(crate) lines: Vec<String>,
    pub(crate) var: String,
    pub(crate) simple_selector_index: Option<usize>,
    pub(crate) gate_index: usize,
    pub(crate) gate_name: String,
    pub(crate) constraint_index: usize,
    pub(crate) constraint_name: String,
    pub(crate) polynomial_index: usize,
}

impl<'a> Evaluator<'a> {
    /// Create an evaluator bound to a constraint system, metadata, and data
    /// map.
    pub(crate) fn new(
        cs: &'a ConstraintSystem<Fq>,
        meta: &'a ConstraintSystemMeta,
        data: &'a Data,
    ) -> Self {
        Self {
            cs,
            meta,
            data,
            use_pow5_helper: false,
            var_counter: Default::default(),
            var_cache: Default::default(),
        }
    }

    /// Enable or disable the optional `q_pow5` Yul helper peephole.
    pub(crate) fn with_pow5_helper(mut self, enabled: bool) -> Self {
        self.use_pow5_helper = enabled;
        self
    }

    /// Clear local variable and expression caches.
    pub(crate) fn reset_locals(&self) {
        self.reset();
    }

    /// Emit Yul for a single Halo2 expression without changing caller state.
    pub(crate) fn evaluate_expression(&self, expression: &Expression<Fq>) -> (Vec<String>, String) {
        self.evaluate(expression)
    }

    /// Compress expressions with a caller-provided challenge variable.
    ///
    /// This is used by structured lookup/trash paths that hoist theta or the
    /// trash challenge once and then reuse the variable across loop bodies.
    pub(crate) fn compress_expressions_with_challenge_var(
        &self,
        expressions: &[Expression<Fq>],
        challenge_var: &str,
    ) -> (Vec<String>, String) {
        self.compress_expressions(expressions, challenge_var)
    }

    /// Whether the shared-prefix parallel-lookup optimization applies to one
    /// chunk, returning the adjacent tail-eval base pointer when it does.
    ///
    /// This is the single dispatch rule shared by the emitter
    /// ([`Self::lookup_shared_prefix_f_plus_beta`]) and the shape-corpus
    /// lookup-arm census, so the census cannot drift from what the emitter
    /// actually generates.
    fn lookup_shared_prefix_base_ptr(&self, input_chunk: &[Vec<Expression<Fq>>]) -> Option<usize> {
        if input_chunk.len() < 3 {
            return None;
        }

        let first = input_chunk.first()?;
        if first.is_empty() {
            return None;
        }
        let prefix_len = first.len().checked_sub(1)?;
        if prefix_len == 0 {
            return None;
        }

        if input_chunk
            .iter()
            .any(|exprs| exprs.len() != first.len() || exprs[..prefix_len] != first[..prefix_len])
        {
            return None;
        }

        let base_ptr = self.expression_memory_ptr(first.last()?)?;
        for (idx, exprs) in input_chunk.iter().enumerate() {
            if self.expression_memory_ptr(exprs.last()?)? != base_ptr + idx * 0x20 {
                return None;
            }
        }
        Some(base_ptr)
    }

    /// Whether [`Self::lookup_shared_prefix_f_plus_beta`] would emit the
    /// shared-prefix loop for this chunk.
    #[cfg(test)]
    pub(crate) fn lookup_shared_prefix_applicable(
        &self,
        input_chunk: &[Vec<Expression<Fq>>],
    ) -> bool {
        self.lookup_shared_prefix_base_ptr(input_chunk).is_some()
    }

    /// Emit a shared-prefix optimization for parallel lookup inputs.
    ///
    /// When every parallel input has the same prefix and its final limb is laid
    /// out in adjacent memory words, the generated Yul evaluates the prefix
    /// once and loops over the tails. This mirrors LogUp's θ-compression while
    /// avoiding repeated arithmetic in wide range-check lookups.
    pub(crate) fn lookup_shared_prefix_f_plus_beta(
        &self,
        input_chunk: &[Vec<Expression<Fq>>],
        challenge_var: &str,
        beta_var: &str,
        f_plus_beta_mptr: &str,
    ) -> Option<Vec<String>> {
        let base_ptr = self.lookup_shared_prefix_base_ptr(input_chunk)?;
        let first = input_chunk.first()?;
        let prefix_len = first.len().checked_sub(1)?;

        let mut lines = Vec::new();
        let (mut prefix_lines, prefix_var) =
            self.compress_expressions(&first[..prefix_len], challenge_var);
        lines.append(&mut prefix_lines);
        let prefix_scaled = self.fresh_var();
        lines.push(format!(
            "let {prefix_scaled} := mulmod({prefix_var}, {challenge_var}, r)"
        ));
        lines.push(format!(
            "for {{ let q_lookup_shared_i := 0 }} lt(q_lookup_shared_i, {}) {{ q_lookup_shared_i := add(q_lookup_shared_i, 1) }} {{",
            input_chunk.len()
        ));
        lines.push("let q_lookup_shared_off := shl(5, q_lookup_shared_i)".to_string());
        lines.push(format!(
            "let q_lookup_shared_tail := mload(add({base_ptr:#x}, q_lookup_shared_off))"
        ));
        lines.push(format!(
            "let q_lookup_shared_compressed := addmod({prefix_scaled}, q_lookup_shared_tail, r)"
        ));
        lines.push(format!(
            "mstore(add({f_plus_beta_mptr}, q_lookup_shared_off), addmod(q_lookup_shared_compressed, {beta_var}, r))"
        ));
        lines.push("}".to_string());
        Some(lines)
    }

    // ----------------------------------------------------------------
    // Gate emitter: one constraint per gate-polynomial.
    // ----------------------------------------------------------------

    /// Emit each gate polynomial and tag it with its simple-selector
    /// fixed-column index (if any).
    /// Mirrors `partially_evaluate_identities` in
    /// `midfall/proofs/src/plonk/mod.rs`: for each gate, the simple
    /// selector index is `gate.queried_selectors().filter(|s|
    /// s.is_simple()).next().map(|s| s.index())`. After
    /// `directly_convert_selectors_to_fixed`, a simple selector's
    /// `index()` equals the fixed column index of its replacement
    /// (selector indices were shifted by `nr_fixed_columns`).
    pub(crate) fn gate_computations_tagged(&self) -> Vec<GateComputation> {
        self.cs
            .gates()
            .iter()
            .enumerate()
            .flat_map(|(gate_index, gate)| {
                let simple_idx =
                    gate.queried_selectors().iter().find(|s| s.is_simple()).map(|s| s.index());
                gate.polynomials()
                    .iter()
                    .enumerate()
                    .map(move |(polynomial_index, poly)| {
                        let (lines, var) = self.evaluate_and_reset(poly);
                        GateComputation {
                            lines,
                            var,
                            simple_selector_index: simple_idx,
                            gate_index,
                            gate_name: gate.name().to_string(),
                            constraint_index: polynomial_index,
                            constraint_name: gate.constraint_name(polynomial_index).to_string(),
                            polynomial_index,
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    // ----------------------------------------------------------------
    // Helpers
    // ----------------------------------------------------------------

    /// Fold expressions as `acc = acc * challenge + expr`.
    fn compress_expressions(
        &self,
        expressions: &[Expression<Fq>],
        challenge_var: &str,
    ) -> (Vec<String>, String) {
        let mut lines = Vec::new();
        let mut acc_var: Option<String> = None;
        for expr in expressions {
            let (mut e_lines, e_var) = self.evaluate(expr);
            lines.append(&mut e_lines);
            let next = self.fresh_var();
            let prev = acc_var.unwrap_or_else(|| "0".to_string());
            lines.push(format!(
                "let {next} := addmod(mulmod({prev}, {challenge_var}, r), {e_var}, r)"
            ));
            acc_var = Some(next);
        }
        let final_var = acc_var.unwrap_or_else(|| {
            let zero = self.fresh_var();
            lines.push(format!("let {zero} := 0"));
            zero
        });
        (lines, final_var)
    }

    /// Return the concrete memory pointer for a simple query expression.
    ///
    /// This is used only by loop optimizers that require adjacent memory-backed
    /// evals; non-query expressions or symbolic pointers return `None`.
    fn expression_memory_ptr(&self, expression: &Expression<Fq>) -> Option<usize> {
        let word = match expression {
            Expression::Advice(query) => self
                .data
                .advice_evals
                .get(&(query.column_index(), query.rotation().0))
                .copied()?,
            Expression::Fixed(query) => {
                let column_index = query.column_index();
                if self.meta.protocol.simple_selector_cols.contains(&column_index) {
                    return None;
                }
                self.data.fixed_evals.get(&(column_index, query.rotation().0)).copied()?
            }
            Expression::Instance(query) => {
                let column_index = query.column_index();
                if column_index < self.meta.protocol.num_committed_instances {
                    self.data
                        .committed_instance_evals
                        .get(&(column_index, query.rotation().0))
                        .copied()?
                } else {
                    // The non-committed public-input column only has its local
                    // Rotation::cur() interpolation at INSTANCE_EVAL_MPTR.
                    // Decline to treat a rotated query as a direct memory
                    // pointer; the constructor rejects rotated instance queries
                    // and instance_eval_at hard-asserts rotation == 0.
                    if query.rotation().0 != 0 {
                        return None;
                    }
                    self.data.instance_eval
                }
            }
            _ => return None,
        };

        if word.loc() != Location::Memory {
            return None;
        }

        match word.ptr().value() {
            Value::Integer(offset) if offset >= 0 => Some(offset as usize),
            _ => None,
        }
    }

    /// Recognize `a * a * a * a * a` when the Yul pow5 helper is enabled.
    fn pow5_base_expr<'b>(&self, expression: &'b Expression<Fq>) -> Option<&'b Expression<Fq>> {
        if !self.use_pow5_helper {
            return None;
        }

        let mut factors = Vec::new();
        collect_product_factors(expression, &mut factors);
        if factors.len() != 5 {
            return None;
        }

        let base = factors[0];
        if factors.iter().skip(1).all(|factor| *factor == base) {
            Some(base)
        } else {
            None
        }
    }

    /// Typed counterpart of [`Self::eval_at`]: the generated word handle a
    /// permutation column's evaluation loads from, or the constant a simple
    /// selector synthesizes. Staged-table emission needs the handle rather
    /// than its rendering so copy runs are found arithmetically.
    pub(crate) fn eval_source_at(&self, column: &Column<Any>, rotation: i32) -> YulValue {
        let col_idx = column.index();
        match column.column_type() {
            Any::Advice(_) => YulValue::Word(
                *self
                    .data
                    .advice_evals
                    .get(&(col_idx, rotation))
                    .expect("advice eval present in permutation chunk"),
            ),
            Any::Fixed => {
                if self.meta.protocol.simple_selector_cols.contains(&col_idx) {
                    YulValue::Literal("0x1".to_string())
                } else {
                    YulValue::Word(
                        *self
                            .data
                            .fixed_evals
                            .get(&(col_idx, rotation))
                            .expect("fixed eval present in permutation chunk"),
                    )
                }
            }
            Any::Instance => YulValue::Literal(self.instance_eval_at(col_idx, rotation)),
        }
    }

    /// Allocate the next local Yul variable name.
    fn fresh_var(&self) -> String {
        self.next_var()
    }

    /// Reset local-variable numbering and expression cache.
    fn reset(&self) {
        *self.var_counter.borrow_mut() = Default::default();
        *self.var_cache.borrow_mut() = Default::default();
    }

    /// Emit one expression from a clean local state.
    fn evaluate_and_reset(&self, expression: &Expression<Fq>) -> (Vec<String>, String) {
        self.reset();
        self.evaluate(expression)
    }

    /// Emit an expression, first trying additive-term fusion.
    fn evaluate(&self, expression: &Expression<Fq>) -> (Vec<String>, String) {
        if let Some(result) = self.evaluate_sum_with_coeff_and_const(expression) {
            return result;
        }

        self.evaluate_basic(expression)
    }

    /// Try to flatten a sum into constants and scaled terms before emission.
    ///
    /// This avoids nested `addmod` trees and lets product/constant terms use
    /// fewer temporary variables in generated Yul.
    fn evaluate_sum_with_coeff_and_const(
        &self,
        expression: &Expression<Fq>,
    ) -> Option<(Vec<String>, String)> {
        let mut terms = Vec::new();
        let mut constant = Fq::ZERO;
        Self::collect_sum_terms(expression, Fq::ONE, &mut constant, &mut terms);

        terms.retain(|(coeff, _)| !coeff.is_zero_vartime());
        let has_constant = !constant.is_zero_vartime();
        let should_fuse = has_constant
            || terms.len() > 1
            || terms.first().is_some_and(|(coeff, _)| *coeff != Fq::ONE);
        if !should_fuse {
            return None;
        }

        let mut lines = Vec::new();
        let mut acc = if has_constant {
            let (const_lines, const_var) =
                self.init_var(u256_string(fe_to_u256::<Fq>(&constant)), None);
            lines.extend(const_lines);
            Some(const_var)
        } else {
            None
        };

        for (coeff, term) in terms {
            let (mut term_lines, term_var) = self.evaluate_scaled_term(term, coeff);
            lines.append(&mut term_lines);
            acc = Some(match acc {
                Some(acc_var) => {
                    let (add_lines, add_var) =
                        self.init_var(format!("addmod({acc_var}, {term_var}, r)"), None);
                    lines.extend(add_lines);
                    add_var
                }
                None => term_var,
            });
        }

        Some(match acc {
            Some(var) => (lines, var),
            None => self.init_var("0x0", None),
        })
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
                Self::collect_sum_terms(inner, -coeff, constant, terms);
            }
            Expression::Sum(lhs, rhs) => {
                Self::collect_sum_terms(lhs, coeff, constant, terms);
                Self::collect_sum_terms(rhs, coeff, constant, terms);
            }
            Expression::Scaled(inner, scale) => {
                Self::collect_sum_terms(inner, coeff * scale, constant, terms);
            }
            _ => terms.push((coeff, expression)),
        }
    }

    /// Emit one term multiplied by a known Fr coefficient.
    fn evaluate_scaled_term(
        &self,
        expression: &Expression<Fq>,
        coeff: Fq,
    ) -> (Vec<String>, String) {
        let coeff_is_one = coeff == Fq::ONE;

        if let Some(base) = self.pow5_base_expr(expression) {
            let (mut lines, base_var) = self.evaluate_basic(base);
            let (pow_lines, pow_var) = self.init_var(format!("q_pow5({base_var})"), None);
            lines.extend(pow_lines);
            if coeff_is_one {
                return (lines, pow_var);
            }

            let (coeff_lines, coeff_var) =
                self.init_var(u256_string(fe_to_u256::<Fq>(&coeff)), None);
            lines.extend(coeff_lines);
            let (scale_lines, out_var) =
                self.init_var(format!("mulmod({pow_var}, {coeff_var}, r)"), None);
            lines.extend(scale_lines);
            return (lines, out_var);
        }

        if let Expression::Product(lhs, rhs) = expression {
            let (mut lines, lhs_var) = self.evaluate_basic(lhs);
            let (mut rhs_lines, rhs_var) = self.evaluate_basic(rhs);
            lines.append(&mut rhs_lines);
            let expr = if coeff_is_one {
                format!("mulmod({lhs_var}, {rhs_var}, r)")
            } else {
                let (coeff_lines, coeff_var) =
                    self.init_var(u256_string(fe_to_u256::<Fq>(&coeff)), None);
                lines.extend(coeff_lines);
                format!("mulmod(mulmod({lhs_var}, {rhs_var}, r), {coeff_var}, r)")
            };
            let (out_lines, out_var) = self.init_var(expr, None);
            lines.extend(out_lines);
            return (lines, out_var);
        }

        let (mut lines, var) = self.evaluate_basic(expression);
        if coeff_is_one {
            return (lines, var);
        }

        let (coeff_lines, coeff_var) = self.init_var(u256_string(fe_to_u256::<Fq>(&coeff)), None);
        lines.extend(coeff_lines);
        let (scale_lines, out_var) = self.init_var(format!("mulmod({var}, {coeff_var}, r)"), None);
        lines.extend(scale_lines);
        (lines, out_var)
    }

    /// Emit an expression through the native `Expression::evaluate` visitor.
    fn evaluate_basic(&self, expression: &Expression<Fq>) -> (Vec<String>, String) {
        if let Some(base) = self.pow5_base_expr(expression) {
            let (mut lines, base_var) = self.evaluate_basic(base);
            let (pow_lines, pow_var) = self.init_var(format!("q_pow5({base_var})"), None);
            lines.extend(pow_lines);
            return (lines, pow_var);
        }

        // midnight-proofs `Expression<F>` carries the full frontend
        // variants: Constant / Selector / Fixed / Advice / Instance /
        // Challenge / Negated / Sum / Product / Scaled. We do not expect
        // to see `Selector` here because virtual selectors are removed
        // during `directly_convert_selectors_to_fixed`.
        expression.evaluate(
            &|scalar| self.init_var(u256_string(fe_to_u256::<Fq>(&scalar)), None),
            &|_| panic!("virtual selectors must be removed before codegen"),
            &|query| {
                let column_index = query.column_index();
                let rotation = query.rotation().0;
                if self.meta.protocol.simple_selector_cols.contains(&column_index) {
                    // Simple selectors have no eval slot; the verifier
                    // semantics insert F::ONE.
                    self.init_var("0x1".to_string(), None)
                } else {
                    let eval: Word = *self
                        .data
                        .fixed_evals
                        .get(&(column_index, rotation))
                        .expect("fixed eval present");
                    let var_name = column_eval_var("f", column_index, rotation);
                    self.init_var(eval.to_string(), Some(var_name))
                }
            },
            &|query| {
                let column_index = query.column_index();
                let rotation = query.rotation().0;
                let eval: Word = *self
                    .data
                    .advice_evals
                    .get(&(column_index, rotation))
                    .expect("advice eval present");
                let var_name = column_eval_var("a", column_index, rotation);
                self.init_var(eval.to_string(), Some(var_name))
            },
            &|query| {
                let column_index = query.column_index();
                let rotation = query.rotation().0;
                let eval = self.instance_eval_at(column_index, rotation);
                self.init_var(eval, Some(column_eval_var("i", column_index, rotation)))
            },
            &|challenge| {
                self.init_var(
                    self.data.challenges[challenge.index()],
                    Some(format!("c_{}", challenge.index())),
                )
            },
            &|(mut acc, var)| {
                let (lines, var) = self.init_var(format!("addmod(0, sub(r, {var}), r)"), None);
                acc.extend(lines);
                (acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("addmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut lhs_acc, lhs_var), (rhs_acc, rhs_var)| {
                let (lines, var) = self.init_var(format!("mulmod({lhs_var}, {rhs_var}, r)"), None);
                lhs_acc.extend(rhs_acc);
                lhs_acc.extend(lines);
                (lhs_acc, var)
            },
            &|(mut acc, var), scalar| {
                let scalar_var = self.init_var(u256_string(fe_to_u256::<Fq>(&scalar)), None);
                acc.extend(scalar_var.0);
                let (lines, out) =
                    self.init_var(format!("mulmod({var}, {}, r)", scalar_var.1), None);
                acc.extend(lines);
                (acc, out)
            },
        )
    }

    /// Resolve an instance query either from proof evals or local
    /// interpolation.
    fn instance_eval_at(&self, column_index: usize, rotation: i32) -> String {
        if column_index < self.meta.protocol.num_committed_instances {
            self.data
                .committed_instance_evals
                .get(&(column_index, rotation))
                .expect("committed instance eval present")
                .to_string()
        } else {
            // The current public API supports one non-committed instance
            // column, whose Lagrange-combined evaluation is computed by the
            // template prologue and stored at INSTANCE_EVAL_MPTR for
            // Rotation::cur() only. Hard-assert (not debug_assert) so a
            // rotated query that ever bypasses the far-away constructor guard
            // (builder/api.rs) fails closed in release builds too, instead of
            // silently evaluating instance(x) in place of instance(x*omega^k)
            // and generating a verifier that checks a different identity than
            // the native Midfall verifier.
            assert_eq!(
                rotation, 0,
                "rotated public instance query reached Yul quotient emission"
            );
            self.data.instance_eval.to_string()
        }
    }

    /// Bind a Yul expression to a local variable, reusing cached variables.
    fn init_var(&self, value: impl ToString, var: Option<String>) -> (Vec<String>, String) {
        let value = value.to_string();
        if self.var_cache.borrow().contains_key(&value) {
            (vec![], self.var_cache.borrow()[&value].clone())
        } else {
            let var = var.unwrap_or_else(|| self.next_var());
            self.var_cache.borrow_mut().insert(value.clone(), var.clone());
            (vec![format!("let {var} := {value}")], var)
        }
    }

    /// Return the next `varN` local name.
    fn next_var(&self) -> String {
        let count = *self.var_counter.borrow();
        *self.var_counter.borrow_mut() += 1;
        format!("var{count}")
    }
}

/// Stable variable name for a column evaluation and rotation.
fn column_eval_var(prefix: &'static str, column_index: usize, rotation: i32) -> String {
    match rotation.cmp(&0) {
        Ordering::Less => format!("{prefix}_{column_index}_prev_{}", rotation.unsigned_abs()),
        Ordering::Equal => format!("{prefix}_{column_index}"),
        Ordering::Greater => format!("{prefix}_{column_index}_next_{rotation}"),
    }
}

/// Flatten a product tree into leaf expressions.
fn collect_product_factors<'a>(
    expression: &'a Expression<Fq>,
    factors: &mut Vec<&'a Expression<Fq>>,
) {
    if let Expression::Product(lhs, rhs) = expression {
        collect_product_factors(lhs, factors);
        collect_product_factors(rhs, factors);
    } else {
        factors.push(expression);
    }
}
