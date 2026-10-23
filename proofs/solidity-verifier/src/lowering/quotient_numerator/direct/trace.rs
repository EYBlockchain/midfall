// SPDX-License-Identifier: CC0-1.0
//! Trace variables of the direct quotient lowering.
//!
//! Trace renders (`RenderDiagnostics { trace: true, .. }`) of a direct
//! verifier emit, besides the identity values `30_000 + j` shared with the
//! compact VM, one `LOG1` per intermediate value of the direct lowering
//! (see `docs/reference/TRACE_VARIABLES.md`):
//!
//! ```text
//! 70_000 + k   result of the k-th helper call (sum_exprs / sum_exprs_by_degree),
//!              calls numbered in identity order, left-first inside an identity
//! 75_000 + k   product-table entries: table after table (program order), T[0..len)
//! 77_500 + k   limb-view words: vector after vector (program order), v[0..len)
//! ```
//!
//! The ids are a pure function of the lowered program, which is itself a pure
//! function of the constraint system. The native expected values are computed
//! here from the *original* gate sub-expressions (the chain the recogniser
//! replaced) and from the proof's evaluation scalars, never from the IR or the
//! emitted Yul, so a wrong run, table, view, or helper shows up as a named
//! mismatch.

use ff::Field;
use midnight_curves::Fq;
use midnight_proofs::plonk::Expression;

use super::{layout::visit_calls, DirectCall, DirectQuotientProgram, DirectSlot};

/// First trace id of the helper-call results.
pub(crate) const DIRECT_HELPER_TRACE_BASE: u64 = 70_000;
/// First trace id of the product-table entries.
pub(crate) const DIRECT_PRODUCT_TABLE_TRACE_BASE: u64 = 75_000;
/// First trace id of the limb-view words.
pub(crate) const DIRECT_LIMB_VIEW_TRACE_BASE: u64 = 77_500;
/// End (exclusive) of the direct trace range.
pub(crate) const DIRECT_TRACE_END: u64 = 80_000;

/// Trace ids of the direct lowering's intermediates.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct DirectTraceIds {
    /// Per gate identity (program order): ids of its helper calls, left-first.
    pub(crate) calls: Vec<Vec<u64>>,
    /// Per product table: id of `T[0]`.
    pub(crate) tables: Vec<u64>,
    /// Per vector: id of `v[0]`.
    pub(crate) vectors: Vec<u64>,
}

impl DirectQuotientProgram {
    /// Assign the direct trace ids, failing if a sub-range overflows.
    pub(crate) fn trace_ids(&self) -> Result<DirectTraceIds, String> {
        let mut ids = DirectTraceIds::default();
        let mut next = DIRECT_HELPER_TRACE_BASE;
        for identity in &self.gates {
            let mut calls = Vec::new();
            visit_calls(&identity.expr, &mut |_| {
                calls.push(next);
                next += 1;
            });
            ids.calls.push(calls);
        }
        if next > DIRECT_PRODUCT_TABLE_TRACE_BASE {
            return Err(format!(
                "{} helper calls overflow the trace range",
                next - DIRECT_HELPER_TRACE_BASE
            ));
        }
        let mut next = DIRECT_PRODUCT_TABLE_TRACE_BASE;
        for table in &self.tables {
            ids.tables.push(next);
            next += table.len as u64;
        }
        if next > DIRECT_LIMB_VIEW_TRACE_BASE {
            return Err("product-table entries overflow the trace range".to_string());
        }
        let mut next = DIRECT_LIMB_VIEW_TRACE_BASE;
        for vector in &self.vectors {
            ids.vectors.push(next);
            next += vector.len as u64;
        }
        if next > DIRECT_TRACE_END {
            return Err("limb-view words overflow the trace range".to_string());
        }
        Ok(ids)
    }

    /// Native expected value of every direct trace variable, as
    /// `(trace id, name, value)`, given the value of every evaluation slot.
    ///
    /// Helper results evaluate the original gate sub-expression the call
    /// replaced (`Expression::evaluate`); table entries are
    /// `Σ_{i+j=t} x_i y_j` over the limb evaluations; view words are the limb
    /// evaluations (plus the shift for shifted views).
    pub(crate) fn native_trace_values(
        &self,
        eval_of: &impl Fn(DirectSlot) -> Result<Fq, String>,
    ) -> Result<Vec<(u64, String, Fq)>, String> {
        let ids = self.trace_ids()?;
        let mut out = Vec::new();
        for (identity, call_ids) in self.gates.iter().zip(&ids.calls) {
            let mut calls = Vec::new();
            visit_calls(&identity.expr, &mut |call| calls.push(call));
            if calls.len() != identity.call_sources.len() || calls.len() != call_ids.len() {
                return Err(format!(
                    "identity {}: {} calls but {} recorded source sub-trees",
                    identity.global_index,
                    calls.len(),
                    identity.call_sources.len()
                ));
            }
            for (n, ((call, source), id)) in
                calls.iter().zip(&identity.call_sources).zip(call_ids).enumerate()
            {
                let value = evaluate(source, &self.sorted_simple, eval_of)?;
                out.push((*id, self.call_name(identity.global_index, n, *call), value));
            }
        }
        let limb = |vector: usize, i: usize| -> Result<Fq, String> {
            let v = &self.vectors[vector];
            let base = eval_of(v.slot(i))?;
            Ok(base + v.shift.map(|(_, s)| s).unwrap_or(Fq::ZERO))
        };
        for (t, (table, base_id)) in self.tables.iter().zip(&ids.tables).enumerate() {
            let (xs, ys) = (&self.vectors[table.xs], &self.vectors[table.ys]);
            let mut entries = vec![Fq::ZERO; table.len];
            for i in 0..xs.len {
                for j in 0..ys.len {
                    entries[i + j] += limb(table.xs, i)? * limb(table.ys, j)?;
                }
            }
            let _ = t;
            for (k, value) in entries.into_iter().enumerate() {
                out.push((
                    base_id + k as u64,
                    format!(
                        "{}[{k}] = sum_{{i+j={k}}} {}[i]*{}[j] (cs.gates()[{}])",
                        table.name, xs.name, ys.name, table.gate_index
                    ),
                    value,
                ));
            }
        }
        for (v, (vector, base_id)) in self.vectors.iter().zip(&ids.vectors).enumerate() {
            for i in 0..vector.len {
                let slot = vector.slot(i);
                let shift = match vector.shift {
                    Some((_, s)) => format!(" + {}", super::sym_const(&s)),
                    None => String::new(),
                };
                out.push((
                    base_id + i as u64,
                    format!("{}[{i}] = {}{shift}", vector.name, slot.short()),
                    limb(v, i)?,
                ));
            }
        }
        Ok(out)
    }

    /// Diagnostic name of the `n`-th call of identity `j`.
    pub(crate) fn call_name(&self, j: usize, n: usize, call: DirectCall) -> String {
        let identity = &self.gates[j];
        let text = match call {
            DirectCall::SumExprs { run, vector } => format!(
                "sum_exprs({}, {})",
                self.runs[run].name, self.vectors[vector].name
            ),
            DirectCall::SumExprsByDegree { run, table } => format!(
                "sum_exprs_by_degree({}, {})",
                self.runs[run].name, self.tables[table].name
            ),
        };
        format!(
            "q_identity_{j} (cs.gates()[{}] \"{}\" polynomial[{}]) call #{n}: {text}",
            identity.gate_index, identity.gate_name, identity.polynomial_index
        )
    }
}

/// `Expression::evaluate` of a gate sub-tree with slot values from `eval_of`.
fn evaluate(
    expr: &Expression<Fq>,
    simple: &[usize],
    eval_of: &impl Fn(DirectSlot) -> Result<Fq, String>,
) -> Result<Fq, String> {
    expr.evaluate(
        &|c| Ok(c),
        &|_| Err("virtual selector in a gate sub-expression".to_string()),
        &|q| {
            if simple.contains(&q.column_index()) {
                Ok(Fq::ONE)
            } else {
                eval_of(DirectSlot::Fixed {
                    column: q.column_index(),
                    rotation: q.rotation().0,
                })
            }
        },
        &|q| {
            eval_of(DirectSlot::Advice {
                column: q.column_index(),
                rotation: q.rotation().0,
            })
        },
        &|q| {
            eval_of(DirectSlot::Instance {
                column: q.column_index(),
                rotation: q.rotation().0,
            })
        },
        &|c| eval_of(DirectSlot::Challenge { index: c.index() }),
        &|a| a.map(|x| -x),
        &|a, b| Ok(a? + b?),
        &|a, b| Ok(a? * b?),
        &|a, c| Ok(a? * c),
    )
}
