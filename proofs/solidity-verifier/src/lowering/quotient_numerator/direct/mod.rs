// SPDX-License-Identifier: CC0-1.0
//! Direct ("hybrid") quotient-numerator lowering.
//!
//! This is the opt-in alternative to the compact quotient VM
//! (`QuotientLowering::Direct`). It lowers every gate identity of the
//! `y`-batched numerator to one Yul function whose body is the gate's
//! `Expression` tree written node by node, and folds every identity
//! explicitly:
//!
//! ```text
//! identity j of m (gates -> permutation -> lookups -> trash):
//!     bucket(j) += y^(m-1-j) * e_j
//! bucket(j) = selector bucket of the gate's simple selector, or the main
//!             accumulator (negated into expected_eval at the end)
//! ```
//!
//! which is literally `compute_linearization_commitment` in
//! `proofs/src/plonk/linearization/verifier.rs` (identity `j` of `m` carries
//! `y^(m-1-j)`). Two sub-tree shapes produced by the foreign-field helpers of
//! `midnight-circuits` are recognised structurally in the typed trees and
//! lowered to shared helper calls:
//!
//! * `sum_exprs(coeffs, v)` (circuits/src/field/foreign/util.rs): a left-deep
//!   chain `Σ Constant(c_i) * v_i` over a limb vector `v` (advice queries of
//!   consecutive columns at one rotation), possibly shifted (`v_i + s`,
//!   norm.rs `shifted_x`). Zero coefficients are absent from the Rust tree
//!   (`0 * x = 0`, `acc + 0 = acc` in `proofs/src/plonk/circuit.rs`) and are
//!   restored as zeros in the coefficient run.
//! * `sum_exprs(c, pair_wise_prod(xs, ys))`: a chain `Σ c_ij * xs_i * ys_j`
//!   where the generator checks, on the actual constants, that `c_ij` depends
//!   only on `i + j`; it is lowered to `pair_wise_prod_by_degree(T, xs, ys)`
//!   (computed once per gate and pair of vectors) and
//!   `sum_exprs_by_degree(c_by_degree, T)`.
//!
//! Limb vectors are discovered from the product shapes of the trees; nothing
//! about the limb count, base, or moduli is hard-coded.
//!
//! What is checked, and where:
//!
//! * Code generation, fails closed (`validate`): translation validation of
//!   the lowered *IR*. For several pseudo-random slot assignments, the bound
//!   gate-identity IR (`DirectExpr`, including helper calls, limb views,
//!   shifted views and product tables, reading the VK constant table exactly
//!   as deployed) is executed on a simulated memory and compared with
//!   `Expression::evaluate` of the original gate polynomial. This does not
//!   execute the emitted Yul: the Yul text of identity bodies and helpers
//!   (`emit`), the `Y_POW` table, the bucket zeroing, the final
//!   `-Q_MAIN_ACC`, and the permutation / lookup / trash bodies are not
//!   covered by it. Both sides use the same slot-address resolver.
//! * Code generation, fails closed (`folds`): a structural check of every
//!   emitted fold statement, gate functions and family loops alike (loops
//!   expanded iteration by iteration). Each identity `j` in `0..m` is folded
//!   exactly once, with `Y_POW[m-1-j]`, into the bucket of its manifest
//!   target; no weight is reused or unused. It checks where values are
//!   folded, not how they are computed.
//! * Tests (EVM tier, `tests/common::quotient_probe`): a test-only probe
//!   render returns `[expected_eval, selector_acc[0..n)]` after the quotient
//!   section; on random evaluation frames and changed challenges it is
//!   compared with a Rust reference (midnight-proofs' own identity values,
//!   gate identities re-evaluated with `Expression::evaluate`, folded with the
//!   linearization rule). This is the check of the emitted Yul.
//!
//! This module contains the pure program (IR + recognition), the layout
//! binder, the Yul emitter, the IR validator and the fold check; the
//! orchestration with the verifier plan lives in `lowering/quotient_direct.rs`.

pub(crate) mod emit;
pub(crate) mod folds;
pub(crate) mod layout;
pub(crate) mod trace;
pub(crate) mod validate;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::plonk::{ConstraintSystem, Expression};
use ruint::aliases::U256;

use crate::{
    api::{QuotientIdentityManifest, QuotientIdentityManifestTarget, QuotientIdentitySource},
    lowering::encoding::fe_to_u256,
};

/// Minimum number of `c * x_i * y_j` terms before a product chain is used to
/// discover limb vectors or lowered to the by-degree helpers.
pub(crate) const MIN_PAIR_TERMS: usize = 3;
/// Minimum number of `c * v_i` terms before a linear chain is used to
/// discover limb vectors or lowered to `sum_exprs` (shorter chains are
/// cheaper inline).
pub(crate) const MIN_LINEAR_TERMS: usize = 3;
/// Scalar constants whose canonical encoding needs at least this many bytes
/// are stored in the VK constant table (read by `mload(QC_i)`); smaller ones
/// are named Solidity literals (`QK_0x..`).
pub(crate) const POOL_MIN_BYTES: usize = 4;

/// One polynomial evaluation read by a gate identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum DirectSlot {
    /// Advice column query.
    Advice { column: usize, rotation: i32 },
    /// Non-simple-selector fixed column query.
    Fixed { column: usize, rotation: i32 },
    /// Instance column query.
    Instance { column: usize, rotation: i32 },
    /// User-phase challenge.
    Challenge { index: usize },
}

/// Rotation suffix used in slot and vector names.
pub(crate) fn rotation_suffix(rotation: i32) -> String {
    match rotation {
        0 => String::new(),
        1 => "_NEXT".to_string(),
        -1 => "_PREV".to_string(),
        r if r > 0 => format!("_NEXT{r}"),
        r => format!("_PREV{}", -r),
    }
}

impl DirectSlot {
    /// Solidity constant name of the evaluation slot, e.g. `EV_A0_NEXT`.
    pub(crate) fn name(&self) -> String {
        match *self {
            Self::Advice { column, rotation } => {
                format!("EV_A{column}{}", rotation_suffix(rotation))
            }
            Self::Fixed { column, rotation } => {
                format!("EV_F{column}{}", rotation_suffix(rotation))
            }
            Self::Instance { column, rotation } => {
                format!("EV_I{column}{}", rotation_suffix(rotation))
            }
            Self::Challenge { index } => format!("EV_CHALLENGE_{index}"),
        }
    }

    /// Human description, e.g. `advice column 0 @ rotation 1`.
    pub(crate) fn describe(&self) -> String {
        match *self {
            Self::Advice { column, rotation } => {
                format!("advice column {column} @ rotation {rotation}")
            }
            Self::Fixed { column, rotation } => {
                format!("fixed column {column} @ rotation {rotation}")
            }
            Self::Instance { column, rotation } => {
                format!("instance column {column} @ rotation {rotation}")
            }
            Self::Challenge { index } => format!("challenge {index}"),
        }
    }

    /// Short lower-case name used in symbolic comments, e.g. `a0_next`.
    pub(crate) fn short(&self) -> String {
        let name = self.name();
        name.trim_start_matches("EV_").to_ascii_lowercase()
    }
}

/// Typed identity IR: the gate `Expression` tree, node by node, with
/// recognised helper calls as atomic leaves.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum DirectExpr {
    /// Field constant.
    Constant(Fq),
    /// Simple selector query. The Rust verifier substitutes `F::ONE` and
    /// routes the identity to the selector's linearization bucket.
    SimpleSelector(usize),
    /// Evaluation slot.
    Slot(DirectSlot),
    /// `-a`.
    Negated(Box<DirectExpr>),
    /// `a + b`.
    Sum(Box<DirectExpr>, Box<DirectExpr>),
    /// `a * b` (`Scaled(a, c)` is lowered to `a * Constant(c)`).
    Product(Box<DirectExpr>, Box<DirectExpr>),
    /// Recognised helper call.
    Call(DirectCall),
}

/// Recognised helper call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum DirectCall {
    /// `sum_exprs(run, vector) = Σ_i run[i] * vector[i]`.
    SumExprs { run: usize, vector: usize },
    /// `sum_exprs_by_degree(run, table) = Σ_t run[t] * table[t]`.
    SumExprsByDegree { run: usize, table: usize },
}

/// Coefficient run kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RunKind {
    /// Coefficients of a `sum_exprs` over a limb vector.
    Linear,
    /// Coefficients of a `pair_wise_prod` sum, grouped by `i + j`.
    ByDegree,
}

/// One coefficient run stored in the VK constant table.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct CoeffRun {
    pub(crate) kind: RunKind,
    pub(crate) values: Vec<Fq>,
    /// Display name, e.g. `COEFF_RUN_0` / `COEFF_RUN_BY_DEGREE_1`.
    pub(crate) name: String,
}

/// A limb vector: `len` advice queries of consecutive columns at one
/// rotation, or a shifted view `base[i] + shift` of such a vector.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct LimbVector {
    pub(crate) rotation: i32,
    pub(crate) first_column: usize,
    pub(crate) len: usize,
    /// `Some((base_vector, shift))` for a shifted view.
    pub(crate) shift: Option<(usize, Fq)>,
    /// Solidity constant name (memory pointer).
    pub(crate) name: String,
}

impl LimbVector {
    /// Advice slot of limb `i` (of the base vector for shifted views).
    pub(crate) fn slot(&self, i: usize) -> DirectSlot {
        DirectSlot::Advice {
            column: self.first_column + i,
            rotation: self.rotation,
        }
    }

    /// Human description, e.g. `a0..a6 @ rotation 1`.
    pub(crate) fn describe(&self) -> String {
        let base = format!(
            "a{}..a{} @ rotation {}",
            self.first_column,
            self.first_column + self.len - 1,
            self.rotation
        );
        match self.shift {
            None => base,
            Some((_, shift)) => format!("({base}) + {}", sym_const(&shift)),
        }
    }
}

/// `T[t] = Σ_{i+j=t} xs[i] * ys[j]`, computed once per gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProductTable {
    pub(crate) gate_index: usize,
    pub(crate) xs: usize,
    pub(crate) ys: usize,
    pub(crate) len: usize,
    pub(crate) name: String,
}

/// Accumulation target of one identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DirectTarget {
    /// Fully evaluated identity (`None` bucket): main accumulator.
    Main,
    /// Simple-selector bucket.
    Selector { bucket: usize, fixed_column: usize },
}

/// One gate identity in the global stream.
#[derive(Clone, Debug)]
pub(crate) struct DirectGateIdentity {
    pub(crate) global_index: usize,
    pub(crate) gate_index: usize,
    pub(crate) gate_name: String,
    pub(crate) polynomial_index: usize,
    pub(crate) constraint_name: String,
    pub(crate) target: DirectTarget,
    /// Lowered IR (emitted and validated).
    pub(crate) expr: DirectExpr,
    /// Source tree from `vk.cs().gates()`, kept for translation validation.
    pub(crate) source: Expression<Fq>,
    /// Original gate sub-tree of every recognised helper call, in the
    /// left-first order of [`layout::visit_calls`] (the order of their trace
    /// ids). Used to compute the native expected value of each call.
    pub(crate) call_sources: Vec<Expression<Fq>>,
}

/// Contiguous range of identities in the global stream.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct IdentityRange {
    pub(crate) base: usize,
    pub(crate) count: usize,
}

/// Recognition switches (all on by default; tests turn them off to compare
/// against plain transliteration).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DirectOptions {
    /// Recognise `sum_exprs` / `pair_wise_prod` shapes.
    pub(crate) recognize_shapes: bool,
    /// Recognise shifted limb vectors (`v_i + s`).
    pub(crate) shifted_vectors: bool,
}

impl Default for DirectOptions {
    fn default() -> Self {
        Self {
            recognize_shapes: true,
            shifted_vectors: true,
        }
    }
}

/// Memory-independent part of the direct lowering: lowered identities, limb
/// vectors, coefficient runs, product tables, and the VK constant table.
#[derive(Clone, Debug)]
pub(crate) struct DirectQuotientProgram {
    /// Total number of identities `m` in the global stream.
    pub(crate) m: usize,
    pub(crate) gates: Vec<DirectGateIdentity>,
    pub(crate) permutation: IdentityRange,
    pub(crate) lookup: IdentityRange,
    pub(crate) trash: IdentityRange,
    /// Sorted simple-selector fixed columns (bucket index = position).
    pub(crate) sorted_simple: Vec<usize>,
    pub(crate) vectors: Vec<LimbVector>,
    pub(crate) runs: Vec<CoeffRun>,
    pub(crate) tables: Vec<ProductTable>,
    /// Scalar constants stored in the VK table (`QC_i`), by first use.
    pub(crate) pool: Vec<Fq>,
}

/// One word of the VK constant table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TableWord {
    pub(crate) value: U256,
    /// Trailing comment in the VK contract.
    pub(crate) label: String,
    /// Comment lines emitted before this word (coefficient run headers).
    pub(crate) headers: Vec<String>,
}

impl DirectQuotientProgram {
    /// Lower the gate identities of `cs` and collect the direct-mode data.
    ///
    /// `manifest` is the host-side identity manifest (gate / permutation /
    /// lookup / trash order and targets) built from the same constraint
    /// system; it is the single source of the identity metadata.
    pub(crate) fn build(
        cs: &ConstraintSystem<Fq>,
        advice_queries: &[(usize, i32)],
        manifest: &QuotientIdentityManifest,
        options: DirectOptions,
    ) -> Result<Self, String> {
        let polys: Vec<(usize, &str, usize, &Expression<Fq>)> = cs
            .gates()
            .iter()
            .enumerate()
            .flat_map(|(gate_index, gate)| {
                gate.polynomials()
                    .iter()
                    .enumerate()
                    .map(move |(poly_index, poly)| (gate_index, gate.name(), poly_index, poly))
            })
            .collect();
        Self::build_from_polys(&polys, advice_queries, manifest, options)
    }

    /// [`Self::build`] over an explicit list of
    /// `(gate_index, gate_name, polynomial_index, polynomial)` in stream order.
    pub(crate) fn build_from_polys(
        polys: &[(usize, &str, usize, &Expression<Fq>)],
        advice_queries: &[(usize, i32)],
        manifest: &QuotientIdentityManifest,
        options: DirectOptions,
    ) -> Result<Self, String> {
        let sorted_simple = manifest.simple_selector_cols.clone();
        let simple_set: BTreeSet<usize> = sorted_simple.iter().copied().collect();
        if polys.len() != manifest.gate_identities {
            return Err(format!(
                "gate polynomial count {} does not match the identity manifest ({})",
                polys.len(),
                manifest.gate_identities
            ));
        }

        let mut recognizer = Recognizer::new(advice_queries, &simple_set, options);
        if options.recognize_shapes {
            recognizer.discover_vectors(polys.iter().map(|(_, _, _, poly)| *poly));
        }

        let mut gates = Vec::with_capacity(polys.len());
        for (entry, (gate_index, gate_name, poly_index, poly)) in
            manifest.entries.iter().zip(polys.iter())
        {
            let QuotientIdentitySource::Gate {
                gate_index: m_gate,
                gate_name: m_name,
                polynomial_index: m_poly,
                constraint_name,
                ..
            } = &entry.source
            else {
                return Err(format!(
                    "identity {} is not a gate identity in the manifest",
                    entry.global_index
                ));
            };
            if m_gate != gate_index || m_poly != poly_index || m_name != gate_name {
                return Err(format!(
                    "manifest entry {} ({m_name}[{m_poly}]) does not match cs.gates()[{gate_index}] {gate_name}[{poly_index}]",
                    entry.global_index
                ));
            }
            let target = match entry.target {
                QuotientIdentityManifestTarget::Main => DirectTarget::Main,
                QuotientIdentityManifestTarget::Selector {
                    selector_index,
                    fixed_column,
                } => DirectTarget::Selector {
                    bucket: selector_index,
                    fixed_column,
                },
            };
            recognizer.current_gate = *gate_index;
            let expr = recognizer.lower(poly)?;
            let call_sources = std::mem::take(&mut recognizer.call_sources);
            gates.push(DirectGateIdentity {
                global_index: entry.global_index,
                gate_index: *gate_index,
                gate_name: gate_name.to_string(),
                polynomial_index: *poly_index,
                constraint_name: constraint_name.clone(),
                target,
                expr,
                source: (*poly).clone(),
                call_sources,
            });
        }

        let permutation = IdentityRange {
            base: manifest.gate_identities,
            count: manifest.permutation_identities,
        };
        let lookup = IdentityRange {
            base: permutation.base + permutation.count,
            count: manifest.lookup_identities,
        };
        let trash = IdentityRange {
            base: lookup.base + lookup.count,
            count: manifest.trash_identities,
        };
        let m = trash.base + trash.count;
        if manifest.entries.len() != m {
            return Err(format!(
                "identity manifest has {} entries, expected {m}",
                manifest.entries.len()
            ));
        }

        let Recognizer {
            vectors,
            runs,
            tables,
            ..
        } = recognizer;
        let mut program = Self {
            m,
            gates,
            permutation,
            lookup,
            trash,
            sorted_simple,
            vectors,
            runs,
            tables,
            pool: Vec::new(),
        };
        program.prune_vectors();
        program.name_objects();
        program.pool = program.collect_pool();
        Ok(program)
    }

    /// Drop discovered vectors that no helper call ended up using and
    /// renumber the remaining ones (order preserved).
    fn prune_vectors(&mut self) {
        let used = layout::used_vectors(self);
        let remap: HashMap<usize, usize> =
            used.iter().enumerate().map(|(new, old)| (*old, new)).collect();
        self.vectors = std::mem::take(&mut self.vectors)
            .into_iter()
            .enumerate()
            .filter(|(idx, _)| used.contains(idx))
            .map(|(_, mut v)| {
                if let Some((base, shift)) = v.shift {
                    v.shift = Some((remap[&base], shift));
                }
                v
            })
            .collect();
        for table in &mut self.tables {
            table.xs = remap[&table.xs];
            table.ys = remap[&table.ys];
        }
        fn rewrite(expr: &mut DirectExpr, remap: &HashMap<usize, usize>) {
            match expr {
                DirectExpr::Call(DirectCall::SumExprs { vector, .. }) => *vector = remap[vector],
                DirectExpr::Negated(inner) => rewrite(inner, remap),
                DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                    rewrite(lhs, remap);
                    rewrite(rhs, remap);
                }
                _ => {}
            }
        }
        for identity in &mut self.gates {
            rewrite(&mut identity.expr, &remap);
        }
    }

    /// Assign stable display names in first-use order.
    fn name_objects(&mut self) {
        // Runs: linear and by-degree runs are numbered separately in id
        // (first-use) order.
        let (mut linear, mut by_degree) = (0usize, 0usize);
        for run in &mut self.runs {
            run.name = match run.kind {
                RunKind::Linear => {
                    linear += 1;
                    format!("COEFF_RUN_{}", linear - 1)
                }
                RunKind::ByDegree => {
                    by_degree += 1;
                    format!("COEFF_RUN_BY_DEGREE_{}", by_degree - 1)
                }
            };
        }
        // Vectors: base vectors by columns/rotation, shifted views by base.
        let base_names: Vec<String> = self
            .vectors
            .iter()
            .map(|v| {
                format!(
                    "LIMBS_A{}_A{}{}",
                    v.first_column,
                    v.first_column + v.len - 1,
                    rotation_suffix(v.rotation)
                )
            })
            .collect();
        let mut shifted_per_base: HashMap<usize, usize> = HashMap::new();
        for v in &self.vectors {
            if let Some((base, _)) = v.shift {
                *shifted_per_base.entry(base).or_default() += 1;
            }
        }
        let mut shifted_seen: HashMap<usize, usize> = HashMap::new();
        for (idx, v) in self.vectors.iter_mut().enumerate() {
            v.name = match v.shift {
                None => base_names[idx].clone(),
                Some((base, _)) => {
                    let ordinal = shifted_seen.entry(base).or_default();
                    *ordinal += 1;
                    if shifted_per_base[&base] > 1 {
                        format!("SHIFTED_{}_{}", base_names[base], *ordinal - 1)
                    } else {
                        format!("SHIFTED_{}", base_names[base])
                    }
                }
            };
        }
        let short = |name: &str| name.trim_start_matches("LIMBS_").to_string();
        let names: Vec<String> = self.vectors.iter().map(|v| v.name.clone()).collect();
        for table in &mut self.tables {
            table.name = format!(
                "T_G{}_{}_X_{}",
                table.gate_index,
                short(&names[table.xs]),
                short(&names[table.ys])
            );
        }
    }

    /// Pooled constants in stream (first-use) order.
    fn collect_pool(&self) -> Vec<Fq> {
        let mut pool: Vec<Fq> = Vec::new();
        let mut seen: BTreeSet<[u8; 32]> = BTreeSet::new();
        let mut push = |value: &Fq, pool: &mut Vec<Fq>| {
            if is_pooled(value) && seen.insert(value.to_repr()) {
                pool.push(*value);
            }
        };
        let mut shifted_done: BTreeSet<usize> = BTreeSet::new();
        for identity in &self.gates {
            let mut stack = vec![&identity.expr];
            while let Some(expr) = stack.pop() {
                match expr {
                    DirectExpr::Constant(value) => push(value, &mut pool),
                    DirectExpr::Negated(inner) => stack.push(inner),
                    DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                        stack.push(rhs);
                        stack.push(lhs);
                    }
                    DirectExpr::Call(DirectCall::SumExprs { vector, .. }) => {
                        if let Some((_, shift)) = self.vectors[*vector].shift {
                            if shifted_done.insert(*vector) {
                                push(&shift, &mut pool);
                            }
                        }
                    }
                    DirectExpr::Call(DirectCall::SumExprsByDegree { .. })
                    | DirectExpr::SimpleSelector(_)
                    | DirectExpr::Slot(_) => {}
                }
            }
        }
        pool
    }

    /// Index of a pooled constant.
    pub(crate) fn pool_index(&self, value: &Fq) -> Option<usize> {
        self.pool.iter().position(|v| v == value)
    }

    /// Word offset of each run inside the constant table (runs first).
    pub(crate) fn run_offsets(&self) -> Vec<usize> {
        let mut offsets = Vec::with_capacity(self.runs.len());
        let mut cursor = 0usize;
        for run in &self.runs {
            offsets.push(cursor);
            cursor += run.values.len();
        }
        offsets
    }

    /// Total words of coefficient runs.
    pub(crate) fn run_words(&self) -> usize {
        self.runs.iter().map(|run| run.values.len()).sum()
    }

    /// Word offset of pooled constant `i`.
    pub(crate) fn pool_offset(&self, i: usize) -> usize {
        self.run_words() + i
    }

    /// Number of words of the VK constant table.
    pub(crate) fn table_len(&self) -> usize {
        self.run_words() + self.pool.len()
    }

    /// VK constant table: coefficient runs (all entries, zeros kept), then
    /// pooled scalar constants.
    pub(crate) fn table_words(&self) -> Vec<TableWord> {
        let mut words = Vec::with_capacity(self.table_len());
        for run in &self.runs {
            let what = match run.kind {
                RunKind::Linear => "sum_exprs coefficients c[i] (zeros kept)",
                RunKind::ByDegree => {
                    "pair_wise_prod coefficients grouped by degree: c[t] = c_ij for every i+j = t"
                }
            };
            let values = run.values.iter().map(sym_const).collect::<Vec<_>>().join(", ");
            let headers = vec![
                format!("{} ({} words): {what}", run.name, run.values.len()),
                format!("{} = [{values}]", run.name),
            ];
            for (i, value) in run.values.iter().enumerate() {
                words.push(TableWord {
                    value: fe_to_u256::<Fq>(value),
                    label: format!("{}[{i}] = {}", run.name, sym_const(value)),
                    headers: if i == 0 { headers.clone() } else { Vec::new() },
                });
            }
        }
        for (i, value) in self.pool.iter().enumerate() {
            words.push(TableWord {
                value: fe_to_u256::<Fq>(value),
                label: format!("QC_{i} = {}", sym_const(value)),
                headers: if i == 0 {
                    vec!["scalar constants QC_i of the identity trees, by first use".to_string()]
                } else {
                    Vec::new()
                },
            });
        }
        words
    }

    /// Identity `j`'s weight exponent `m - 1 - j`.
    pub(crate) fn y_exponent(&self, global_index: usize) -> usize {
        self.m - 1 - global_index
    }

    /// Distinct helper arities in use: (linear lengths, by-degree lengths,
    /// product shapes).
    pub(crate) fn helper_shapes(&self) -> HelperShapes {
        let mut shapes = HelperShapes::default();
        for identity in &self.gates {
            let mut stack = vec![&identity.expr];
            while let Some(expr) = stack.pop() {
                match expr {
                    DirectExpr::Negated(inner) => stack.push(inner),
                    DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                        stack.push(rhs);
                        stack.push(lhs);
                    }
                    DirectExpr::Call(DirectCall::SumExprs { run, .. }) => {
                        shapes.linear.insert(self.runs[*run].values.len());
                    }
                    DirectExpr::Call(DirectCall::SumExprsByDegree { run, table }) => {
                        shapes.by_degree.insert(self.runs[*run].values.len());
                        let t = &self.tables[*table];
                        shapes.products.insert((self.vectors[t.xs].len, self.vectors[t.ys].len));
                    }
                    _ => {}
                }
            }
        }
        shapes
    }
}

/// Helper arities used by a program.
#[derive(Clone, Debug, Default)]
pub(crate) struct HelperShapes {
    pub(crate) linear: BTreeSet<usize>,
    pub(crate) by_degree: BTreeSet<usize>,
    pub(crate) products: BTreeSet<(usize, usize)>,
}

impl HelperShapes {
    /// Name of the `sum_exprs` helper for `len` coefficients.
    pub(crate) fn sum_exprs_name(&self, len: usize) -> String {
        if self.linear.len() <= 1 {
            "sum_exprs".to_string()
        } else {
            format!("sum_exprs_{len}")
        }
    }

    /// Name of the `sum_exprs_by_degree` helper for `len` coefficients.
    pub(crate) fn sum_exprs_by_degree_name(&self, len: usize) -> String {
        if self.by_degree.len() <= 1 {
            "sum_exprs_by_degree".to_string()
        } else {
            format!("sum_exprs_by_degree_{len}")
        }
    }

    /// Name of the product-table helper for vectors of lengths `(nx, ny)`.
    pub(crate) fn pair_wise_prod_name(&self, shape: (usize, usize)) -> String {
        if self.products.len() <= 1 {
            "pair_wise_prod_by_degree".to_string()
        } else {
            format!("pair_wise_prod_by_degree_{}x{}", shape.0, shape.1)
        }
    }
}

/// Whether a constant is stored in the VK table.
pub(crate) fn is_pooled(value: &Fq) -> bool {
    fe_to_u256::<Fq>(value).bit_len() > 8 * (POOL_MIN_BYTES - 1)
}

/// Human-readable constant for comments: small values in decimal, powers of
/// two as `2^k`, values close to `r` as negatives.
pub(crate) fn sym_const(value: &Fq) -> String {
    let v = fe_to_u256::<Fq>(value);
    let neg = fe_to_u256::<Fq>(&-*value);
    let fmt = |x: U256| -> String {
        if x < U256::from(1024u64) {
            x.to_string()
        } else if x.count_ones() == 1 {
            format!("2^{}", x.bit_len() - 1)
        } else {
            format!("{x:#x}")
        }
    };
    if v.bit_len() > 160 && neg.bit_len() <= 160 {
        format!("(-{})", fmt(neg))
    } else {
        fmt(v)
    }
}

/// Term of a left-deep sum chain, classified by shape.
#[derive(Clone, Copy, Debug)]
enum Term {
    /// `c * a_(col, rot)`.
    Linear {
        coeff: Fq,
        column: usize,
        rotation: i32,
    },
    /// `c * (a_(col, rot) + shift)`.
    Shifted {
        coeff: Fq,
        column: usize,
        rotation: i32,
        shift: Fq,
    },
    /// `c * (a_x * a_y)`.
    Pair {
        coeff: Fq,
        x: (usize, i32),
        y: (usize, i32),
    },
}

/// `Sum(Advice, Constant)`, the norm.rs `x + shift` limb.
fn shifted_limb(expr: &Expression<Fq>) -> Option<(usize, i32, Fq)> {
    match expr {
        Expression::Sum(lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (Expression::Advice(q), Expression::Constant(s)) => {
                Some((q.column_index(), q.rotation().0, *s))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Terms of the left-deep sum chain rooted at `expr`, in fold order.
///
/// `fold(0, |acc, e| acc + e)` builds `Sum(Sum(t0, t1), t2)...`; the chain is
/// walked down the left spine until a non-`Sum` node (or a shifted limb,
/// which is a single term) is reached.
fn chain_terms(expr: &Expression<Fq>) -> Vec<&Expression<Fq>> {
    let mut terms = Vec::new();
    let mut node = expr;
    while let Expression::Sum(lhs, rhs) = node {
        if shifted_limb(node).is_some() {
            break;
        }
        terms.push(rhs.as_ref());
        node = lhs.as_ref();
    }
    terms.push(node);
    terms.reverse();
    terms
}

/// Classify one chain term.
fn classify(term: &Expression<Fq>) -> Option<Term> {
    let (coeff, inner) = match term {
        Expression::Product(lhs, rhs) => match lhs.as_ref() {
            Expression::Constant(c) => (*c, rhs.as_ref()),
            _ => (Fq::ONE, term),
        },
        _ => (Fq::ONE, term),
    };
    match inner {
        Expression::Advice(q) => Some(Term::Linear {
            coeff,
            column: q.column_index(),
            rotation: q.rotation().0,
        }),
        Expression::Sum(..) => shifted_limb(inner).map(|(column, rotation, shift)| Term::Shifted {
            coeff,
            column,
            rotation,
            shift,
        }),
        Expression::Product(lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (Expression::Advice(x), Expression::Advice(y)) => Some(Term::Pair {
                coeff,
                x: (x.column_index(), x.rotation().0),
                y: (y.column_index(), y.rotation().0),
            }),
            _ => None,
        },
        _ => None,
    }
}

/// Extent of a product chain: `(x rotation, x columns, y rotation, y columns)`.
type PairExtent = (i32, BTreeSet<usize>, i32, BTreeSet<usize>);

/// Return the vector extents of a product chain, if `expr` is one.
fn pair_chain_extent(expr: &Expression<Fq>) -> Option<PairExtent> {
    let terms = chain_terms(expr);
    if terms.len() < MIN_PAIR_TERMS {
        return None;
    }
    let mut extent: Option<PairExtent> = None;
    for term in terms {
        let Term::Pair { x, y, .. } = classify(term)? else {
            return None;
        };
        let e = extent.get_or_insert_with(|| (x.1, BTreeSet::new(), y.1, BTreeSet::new()));
        if e.0 != x.1 || e.2 != y.1 {
            return None;
        }
        e.1.insert(x.0);
        e.3.insert(y.0);
    }
    extent
}

/// Extent `(rotation, columns)` of a linear chain `Σ c * v_i` (plain or
/// shifted limbs), if `expr` is one.
fn linear_chain_extent(expr: &Expression<Fq>) -> Option<(i32, BTreeSet<usize>)> {
    let terms = chain_terms(expr);
    if terms.len() < MIN_LINEAR_TERMS {
        return None;
    }
    let mut extent: Option<(i32, BTreeSet<usize>)> = None;
    for term in terms {
        let (column, rotation) = match classify(term)? {
            Term::Linear {
                column, rotation, ..
            }
            | Term::Shifted {
                column, rotation, ..
            } => (column, rotation),
            Term::Pair { .. } => return None,
        };
        let e = extent.get_or_insert_with(|| (rotation, BTreeSet::new()));
        if e.0 != rotation {
            return None;
        }
        e.1.insert(column);
    }
    extent
}

/// Merge `[lo, hi]` column ranges that overlap.
fn merge_ranges(mut spans: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    spans.sort_unstable();
    let mut merged: Vec<(usize, usize)> = Vec::new();
    for (lo, hi) in spans {
        match merged.last_mut() {
            Some(last) if lo <= last.1 => last.1 = last.1.max(hi),
            _ => merged.push((lo, hi)),
        }
    }
    merged
}

/// Stateful recogniser shared across the gates of one constraint system.
struct Recognizer<'a> {
    advice_queries: BTreeSet<(usize, i32)>,
    simple: &'a BTreeSet<usize>,
    options: DirectOptions,
    vectors: Vec<LimbVector>,
    runs: Vec<CoeffRun>,
    tables: Vec<ProductTable>,
    current_gate: usize,
    /// Source sub-trees of the calls recognised in the current identity.
    call_sources: Vec<Expression<Fq>>,
}

impl<'a> Recognizer<'a> {
    fn new(
        advice_queries: &[(usize, i32)],
        simple: &'a BTreeSet<usize>,
        options: DirectOptions,
    ) -> Self {
        Self {
            advice_queries: advice_queries.iter().copied().collect(),
            simple,
            options,
            vectors: Vec::new(),
            runs: Vec::new(),
            tables: Vec::new(),
            current_gate: 0,
            call_sources: Vec::new(),
        }
    }

    /// Discover limb vectors from the chains of all gate trees.
    ///
    /// Product chains `Σ c * x_i * y_j` are the primary source: each
    /// contributes the column range of its `x` factors and of its `y` factors
    /// (each at one rotation), and overlapping ranges at the same rotation are
    /// merged. Linear chains `Σ c * v_i` (of at least `MIN_LINEAR_TERMS`
    /// terms) contribute ranges too, merged among themselves, but only where
    /// they do not overlap a product-derived vector (a linear chain inside a
    /// product vector is covered by it; one straddling it is ignored). This
    /// recovers the full width of vectors that only appear linearly, such as
    /// `zs` in a multiplication gate, from the chain with non-zero
    /// coefficients, while chains whose trailing coefficients vanish (terms
    /// absent from the Rust tree) inherit the full width and get zeros.
    ///
    /// A range becomes a vector only if every column in it is queried at that
    /// rotation (so every limb has an evaluation slot).
    fn discover_vectors<'e>(&mut self, polys: impl Iterator<Item = &'e Expression<Fq>>) {
        fn walk(
            expr: &Expression<Fq>,
            pairs: &mut Vec<(i32, usize, usize)>,
            linear: &mut Vec<(i32, usize, usize)>,
        ) {
            match expr {
                Expression::Sum(lhs, rhs) => {
                    if let Some((rx, xs, ry, ys)) = pair_chain_extent(expr) {
                        pairs.push((rx, *xs.first().unwrap(), *xs.last().unwrap()));
                        pairs.push((ry, *ys.first().unwrap(), *ys.last().unwrap()));
                        return;
                    }
                    if let Some((rot, cols)) = linear_chain_extent(expr) {
                        linear.push((rot, *cols.first().unwrap(), *cols.last().unwrap()));
                        return;
                    }
                    walk(lhs, pairs, linear);
                    walk(rhs, pairs, linear);
                }
                Expression::Product(lhs, rhs) => {
                    walk(lhs, pairs, linear);
                    walk(rhs, pairs, linear);
                }
                Expression::Negated(inner) | Expression::Scaled(inner, _) => {
                    walk(inner, pairs, linear)
                }
                _ => {}
            }
        }
        let (mut pairs, mut linear) = (Vec::new(), Vec::new());
        for poly in polys {
            walk(poly, &mut pairs, &mut linear);
        }
        let group = |ranges: Vec<(i32, usize, usize)>| {
            let mut by_rotation: BTreeMap<i32, Vec<(usize, usize)>> = BTreeMap::new();
            for (rotation, lo, hi) in ranges {
                by_rotation.entry(rotation).or_default().push((lo, hi));
            }
            by_rotation
                .into_iter()
                .map(|(rotation, spans)| (rotation, merge_ranges(spans)))
                .collect::<BTreeMap<_, _>>()
        };
        let product_ranges = group(pairs);
        let linear_ranges = group(linear);
        let mut accepted: Vec<(i32, usize, usize)> = Vec::new();
        for (rotation, spans) in &product_ranges {
            accepted.extend(spans.iter().map(|(lo, hi)| (*rotation, *lo, *hi)));
        }
        for (rotation, spans) in &linear_ranges {
            let products = product_ranges.get(rotation).cloned().unwrap_or_default();
            for (lo, hi) in spans {
                if products.iter().all(|(plo, phi)| hi < plo || lo > phi) {
                    accepted.push((*rotation, *lo, *hi));
                }
            }
        }
        accepted.sort_unstable();
        for (rotation, lo, hi) in accepted {
            let len = hi - lo + 1;
            if len < 2 || !(lo..=hi).all(|c| self.advice_queries.contains(&(c, rotation))) {
                continue;
            }
            self.vectors.push(LimbVector {
                rotation,
                first_column: lo,
                len,
                shift: None,
                name: String::new(),
            });
        }
    }

    /// Base vector containing all `columns` at `rotation`.
    fn find_vector(&self, rotation: i32, columns: &[usize]) -> Option<usize> {
        self.vectors.iter().position(|v| {
            v.shift.is_none()
                && v.rotation == rotation
                && columns.iter().all(|c| *c >= v.first_column && *c < v.first_column + v.len)
        })
    }

    fn intern_run(&mut self, kind: RunKind, values: Vec<Fq>) -> usize {
        if let Some(idx) = self.runs.iter().position(|run| run.kind == kind && run.values == values)
        {
            return idx;
        }
        self.runs.push(CoeffRun {
            kind,
            values,
            name: String::new(),
        });
        self.runs.len() - 1
    }

    fn intern_shifted(&mut self, base: usize, shift: Fq) -> usize {
        if let Some(idx) = self.vectors.iter().position(|v| v.shift == Some((base, shift))) {
            return idx;
        }
        let b = self.vectors[base].clone();
        self.vectors.push(LimbVector {
            rotation: b.rotation,
            first_column: b.first_column,
            len: b.len,
            shift: Some((base, shift)),
            name: String::new(),
        });
        self.vectors.len() - 1
    }

    fn intern_table(&mut self, xs: usize, ys: usize) -> usize {
        let gate_index = self.current_gate;
        if let Some(idx) = self
            .tables
            .iter()
            .position(|t| t.gate_index == gate_index && t.xs == xs && t.ys == ys)
        {
            return idx;
        }
        let len = self.vectors[xs].len + self.vectors[ys].len - 1;
        self.tables.push(ProductTable {
            gate_index,
            xs,
            ys,
            len,
            name: String::new(),
        });
        self.tables.len() - 1
    }

    /// Try to lower the chain rooted at a `Sum` node to a helper call.
    fn match_call(&mut self, expr: &Expression<Fq>) -> Option<DirectCall> {
        let terms = chain_terms(expr);
        if terms.len() < MIN_LINEAR_TERMS.min(MIN_PAIR_TERMS) {
            return None;
        }
        let classified: Vec<Term> = terms.iter().map(|t| classify(t)).collect::<Option<_>>()?;
        match classified[0] {
            Term::Linear { rotation, .. } => {
                let mut cols = Vec::with_capacity(classified.len());
                let mut coeffs = Vec::with_capacity(classified.len());
                for term in &classified {
                    let Term::Linear {
                        coeff,
                        column,
                        rotation: rot,
                    } = *term
                    else {
                        return None;
                    };
                    if rot != rotation {
                        return None;
                    }
                    cols.push(column);
                    coeffs.push(coeff);
                }
                let vector = self.find_vector(rotation, &cols)?;
                let values = self.linear_run(vector, &cols, &coeffs)?;
                let run = self.intern_run(RunKind::Linear, values);
                Some(DirectCall::SumExprs { run, vector })
            }
            Term::Shifted {
                rotation, shift, ..
            } => {
                if !self.options.shifted_vectors {
                    return None;
                }
                let mut cols = Vec::with_capacity(classified.len());
                let mut coeffs = Vec::with_capacity(classified.len());
                for term in &classified {
                    let Term::Shifted {
                        coeff,
                        column,
                        rotation: rot,
                        shift: s,
                    } = *term
                    else {
                        return None;
                    };
                    if rot != rotation || s != shift {
                        return None;
                    }
                    cols.push(column);
                    coeffs.push(coeff);
                }
                let base = self.find_vector(rotation, &cols)?;
                let values = self.linear_run(base, &cols, &coeffs)?;
                let vector = self.intern_shifted(base, shift);
                let run = self.intern_run(RunKind::Linear, values);
                Some(DirectCall::SumExprs { run, vector })
            }
            Term::Pair { x, y, .. } => {
                if classified.len() < MIN_PAIR_TERMS {
                    return None;
                }
                let mut xcols = Vec::with_capacity(classified.len());
                let mut ycols = Vec::with_capacity(classified.len());
                let mut coeffs = Vec::with_capacity(classified.len());
                for term in &classified {
                    let Term::Pair {
                        coeff,
                        x: tx,
                        y: ty,
                    } = *term
                    else {
                        return None;
                    };
                    if tx.1 != x.1 || ty.1 != y.1 {
                        return None;
                    }
                    xcols.push(tx.0);
                    ycols.push(ty.0);
                    coeffs.push(coeff);
                }
                let vx = self.find_vector(x.1, &xcols)?;
                let vy = self.find_vector(y.1, &ycols)?;
                let values = self.by_degree_run(vx, vy, &xcols, &ycols, &coeffs)?;
                let table = self.intern_table(vx, vy);
                let run = self.intern_run(RunKind::ByDegree, values);
                Some(DirectCall::SumExprsByDegree { run, table })
            }
        }
    }

    /// Coefficient run over `vector` for a linear chain, zero-padded.
    ///
    /// Requires strictly increasing limb indices (the `sum_exprs` fold order).
    fn linear_run(&self, vector: usize, cols: &[usize], coeffs: &[Fq]) -> Option<Vec<Fq>> {
        let v = &self.vectors[vector];
        let mut values = vec![Fq::ZERO; v.len];
        let mut last: Option<usize> = None;
        for (col, coeff) in cols.iter().zip(coeffs) {
            let i = col - v.first_column;
            if last.is_some_and(|l| i <= l) {
                return None;
            }
            last = Some(i);
            values[i] = *coeff;
        }
        Some(values)
    }

    /// By-degree run for a product chain, or `None` if `c_ij` is not a
    /// function of `i + j` (absent pairs count as zero coefficients).
    fn by_degree_run(
        &self,
        vx: usize,
        vy: usize,
        xcols: &[usize],
        ycols: &[usize],
        coeffs: &[Fq],
    ) -> Option<Vec<Fq>> {
        let (x, y) = (&self.vectors[vx], &self.vectors[vy]);
        let mut grid = vec![vec![None::<Fq>; y.len]; x.len];
        let mut last: Option<(usize, usize)> = None;
        for ((xc, yc), coeff) in xcols.iter().zip(ycols).zip(coeffs) {
            let (i, j) = (xc - x.first_column, yc - y.first_column);
            // `pair_wise_prod` enumerates (i, j) row-major.
            if last.is_some_and(|l| (i, j) <= l) {
                return None;
            }
            last = Some((i, j));
            grid[i][j] = Some(*coeff);
        }
        let mut by_degree = vec![None::<Fq>; x.len + y.len - 1];
        for (i, row) in grid.iter().enumerate() {
            for (j, cell) in row.iter().enumerate() {
                let c = cell.unwrap_or(Fq::ZERO);
                match by_degree[i + j] {
                    None => by_degree[i + j] = Some(c),
                    Some(d) if d == c => {}
                    Some(_) => return None,
                }
            }
        }
        Some(by_degree.into_iter().map(|c| c.unwrap_or(Fq::ZERO)).collect())
    }

    /// Lower one expression tree to the direct IR.
    fn lower(&mut self, expr: &Expression<Fq>) -> Result<DirectExpr, String> {
        Ok(match expr {
            Expression::Constant(c) => DirectExpr::Constant(*c),
            Expression::Selector(_) => {
                return Err("virtual selectors must be removed before codegen".to_string())
            }
            Expression::Fixed(q) => {
                let column = q.column_index();
                if self.simple.contains(&column) {
                    DirectExpr::SimpleSelector(column)
                } else {
                    DirectExpr::Slot(DirectSlot::Fixed {
                        column,
                        rotation: q.rotation().0,
                    })
                }
            }
            Expression::Advice(q) => DirectExpr::Slot(DirectSlot::Advice {
                column: q.column_index(),
                rotation: q.rotation().0,
            }),
            Expression::Instance(q) => DirectExpr::Slot(DirectSlot::Instance {
                column: q.column_index(),
                rotation: q.rotation().0,
            }),
            Expression::Challenge(c) => {
                DirectExpr::Slot(DirectSlot::Challenge { index: c.index() })
            }
            Expression::Negated(inner) => DirectExpr::Negated(Box::new(self.lower(inner)?)),
            Expression::Sum(lhs, rhs) => {
                if self.options.recognize_shapes {
                    if let Some(call) = self.match_call(expr) {
                        self.call_sources.push(expr.clone());
                        return Ok(DirectExpr::Call(call));
                    }
                }
                DirectExpr::Sum(Box::new(self.lower(lhs)?), Box::new(self.lower(rhs)?))
            }
            Expression::Product(lhs, rhs) => {
                DirectExpr::Product(Box::new(self.lower(lhs)?), Box::new(self.lower(rhs)?))
            }
            Expression::Scaled(inner, c) => DirectExpr::Product(
                Box::new(self.lower(inner)?),
                Box::new(DirectExpr::Constant(*c)),
            ),
        })
    }
}

/// Every slot read by the gate identities or the limb vectors, sorted.
pub(crate) fn used_slots(program: &DirectQuotientProgram) -> BTreeSet<DirectSlot> {
    let mut slots = BTreeSet::new();
    for identity in &program.gates {
        let mut stack = vec![&identity.expr];
        while let Some(expr) = stack.pop() {
            match expr {
                DirectExpr::Slot(slot) => {
                    slots.insert(*slot);
                }
                DirectExpr::Negated(inner) => stack.push(inner),
                DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
                    stack.push(rhs);
                    stack.push(lhs);
                }
                _ => {}
            }
        }
    }
    for v in &program.vectors {
        for i in 0..v.len {
            slots.insert(v.slot(i));
        }
    }
    slots
}
