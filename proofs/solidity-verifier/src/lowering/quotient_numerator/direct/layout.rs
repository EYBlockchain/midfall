// SPDX-License-Identifier: CC0-1.0
//! Memory binding of a direct quotient program.
//!
//! The program is memory independent; this module assigns absolute
//! addresses to every name the emitted Yul uses:
//!
//! ```text
//! SELECTOR_ACC_MPTR + 32 s        Q_BUCKET_s (selector buckets, read by the PCS)
//! quotient state  [0]             Q_MAIN_ACC (fully evaluated identities)
//!                 [1]             Q_R_MPTR   (r, stored once)
//!                 [2 .. 2+m)      Y_POW[k] = y^k
//! quotient stack  views           limb vectors whose limbs are not adjacent in
//!                                 the evaluation table (copied once)
//!                 shifted views   base[i] + shift
//!                 tables          T[t] = Σ_{i+j=t} xs[i] ys[j]
//!                 family scratch  permutation / lookup loop tables
//! VK table        runs, QC_i      copied with the VK payload
//! ```
//!
//! and the section schedule (views, per-gate tables, identity calls) shared by
//! the emitter and the validator.

use std::collections::{BTreeMap, BTreeSet};

use super::{used_slots, DirectCall, DirectExpr, DirectQuotientProgram, DirectSlot};
use crate::lowering::layout::WORD_BYTES;

/// One `mcopy` run of a limb view.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CopyRun {
    /// Destination word index inside the view.
    pub(crate) view_word: usize,
    /// Source address (first limb of the run).
    pub(crate) src: usize,
    /// Number of words.
    pub(crate) words: usize,
}

/// One statement of the quotient section after the preamble.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SectionOp {
    /// Compute a shifted view `vector[i] = base[i] + shift` before the first
    /// identity of `gate`.
    ShiftView { vector: usize, gate: usize },
    /// Compute a product table.
    ProductTable { table: usize },
    /// Call `q_identity_<j>` for `program.gates[index]`.
    Identity { index: usize },
}

/// Inputs from the verifier memory planner.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DirectMemory {
    pub(crate) selector_acc_mptr: usize,
    pub(crate) state_mptr: usize,
    pub(crate) state_words: usize,
    pub(crate) stack_mptr: usize,
    pub(crate) stack_words: usize,
    pub(crate) const_table_mptr: usize,
    pub(crate) family_scratch_words: usize,
}

/// Addresses of every name used by the direct quotient section.
#[derive(Clone, Debug)]
pub(crate) struct DirectLayout {
    pub(crate) slots: BTreeMap<DirectSlot, usize>,
    pub(crate) buckets: Vec<usize>,
    pub(crate) main_acc: usize,
    pub(crate) r_slot: usize,
    pub(crate) y_pow: usize,
    /// Memory pointer of every vector (the first limb for adjacent vectors).
    pub(crate) vector_addr: Vec<usize>,
    /// Copy runs of the views that must be materialised, `(vector, runs)`.
    pub(crate) view_copies: Vec<(usize, Vec<CopyRun>)>,
    pub(crate) table_addr: Vec<usize>,
    pub(crate) run_addr: Vec<usize>,
    pub(crate) pool_addr: Vec<usize>,
    pub(crate) const_table_mptr: usize,
    /// Scratch of the structured families (after the views and tables).
    pub(crate) family_scratch_mptr: usize,
    pub(crate) schedule: Vec<SectionOp>,
}

/// Persistent quotient-state words: main accumulator, `r`, `Y_POW[0..m)`.
pub(crate) fn state_words(program: &DirectQuotientProgram) -> usize {
    2 + program.m
}

/// Vectors referenced (directly or as a shifted view's base) by the calls.
pub(crate) fn used_vectors(program: &DirectQuotientProgram) -> BTreeSet<usize> {
    let mut used = BTreeSet::new();
    for identity in &program.gates {
        visit_calls(&identity.expr, &mut |call| match call {
            DirectCall::SumExprs { vector, .. } => {
                used.insert(vector);
            }
            DirectCall::SumExprsByDegree { table, .. } => {
                used.insert(program.tables[table].xs);
                used.insert(program.tables[table].ys);
            }
        });
    }
    let bases: Vec<usize> = used
        .iter()
        .filter_map(|v| program.vectors[*v].shift.map(|(base, _)| base))
        .collect();
    used.extend(bases);
    used
}

/// Visit every helper call of an expression in evaluation (left-first) order.
pub(crate) fn visit_calls(expr: &DirectExpr, f: &mut impl FnMut(DirectCall)) {
    match expr {
        DirectExpr::Call(call) => f(*call),
        DirectExpr::Negated(inner) => visit_calls(inner, f),
        DirectExpr::Sum(lhs, rhs) | DirectExpr::Product(lhs, rhs) => {
            visit_calls(lhs, f);
            visit_calls(rhs, f);
        }
        DirectExpr::Constant(_) | DirectExpr::SimpleSelector(_) | DirectExpr::Slot(_) => {}
    }
}

/// Copy runs of a base vector, or `None` if its limbs are already adjacent.
fn copy_runs(
    program: &DirectQuotientProgram,
    vector: usize,
    slot_addr: &impl Fn(DirectSlot) -> Result<usize, String>,
) -> Result<Option<Vec<CopyRun>>, String> {
    let v = &program.vectors[vector];
    let addrs = (0..v.len).map(|i| slot_addr(v.slot(i))).collect::<Result<Vec<_>, _>>()?;
    if addrs.windows(2).all(|w| w[1] == w[0] + WORD_BYTES) {
        return Ok(None);
    }
    let mut runs = Vec::new();
    let mut i = 0;
    while i < addrs.len() {
        let mut k = i;
        while k + 1 < addrs.len() && addrs[k + 1] == addrs[k] + WORD_BYTES {
            k += 1;
        }
        runs.push(CopyRun {
            view_word: i,
            src: addrs[i],
            words: k - i + 1,
        });
        i = k + 1;
    }
    Ok(Some(runs))
}

/// Gate scratch words (views, shifted views, tables) for this program.
pub(crate) fn gate_scratch_words(
    program: &DirectQuotientProgram,
    slot_addr: &impl Fn(DirectSlot) -> Result<usize, String>,
) -> Result<usize, String> {
    let mut words = 0usize;
    for v in used_vectors(program) {
        let vector = &program.vectors[v];
        if vector.shift.is_some() || copy_runs(program, v, slot_addr)?.is_some() {
            words += vector.len;
        }
    }
    words += program.tables.iter().map(|t| t.len).sum::<usize>();
    Ok(words)
}

/// Section schedule: at the first identity of every gate, the shifted views
/// first used by that gate and the gate's product tables, then the identity.
pub(crate) fn schedule(program: &DirectQuotientProgram) -> Vec<SectionOp> {
    let mut ops = Vec::new();
    let mut shifted_done: BTreeSet<usize> = BTreeSet::new();
    let mut last_gate: Option<usize> = None;
    for (index, identity) in program.gates.iter().enumerate() {
        if last_gate != Some(identity.gate_index) {
            last_gate = Some(identity.gate_index);
            // Shifted views first used by any polynomial of this gate.
            for other in program.gates.iter().filter(|g| g.gate_index == identity.gate_index) {
                visit_calls(&other.expr, &mut |call| {
                    if let DirectCall::SumExprs { vector, .. } = call {
                        if program.vectors[vector].shift.is_some() && shifted_done.insert(vector) {
                            ops.push(SectionOp::ShiftView {
                                vector,
                                gate: identity.gate_index,
                            });
                        }
                    }
                });
            }
            for (table, t) in program.tables.iter().enumerate() {
                if t.gate_index == identity.gate_index {
                    ops.push(SectionOp::ProductTable { table });
                }
            }
        }
        ops.push(SectionOp::Identity { index });
    }
    ops
}

impl DirectLayout {
    /// Bind a program to verifier memory.
    pub(crate) fn bind(
        program: &DirectQuotientProgram,
        memory: DirectMemory,
        slot_addr: impl Fn(DirectSlot) -> Result<usize, String>,
    ) -> Result<Self, String> {
        let word = WORD_BYTES;
        if memory.state_words < state_words(program) {
            return Err(format!(
                "quotient state region too small: {} words reserved, {} needed",
                memory.state_words,
                state_words(program)
            ));
        }
        let slots = used_slots(program)
            .into_iter()
            .map(|slot| slot_addr(slot).map(|addr| (slot, addr)))
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let buckets = (0..program.sorted_simple.len())
            .map(|s| memory.selector_acc_mptr + s * word)
            .collect::<Vec<_>>();
        let main_acc = memory.state_mptr;
        let r_slot = memory.state_mptr + word;
        let y_pow = memory.state_mptr + 2 * word;

        let used = used_vectors(program);
        let mut cursor = memory.stack_mptr;
        let mut vector_addr = vec![0usize; program.vectors.len()];
        let mut view_copies = Vec::new();
        // Base vectors first (views are copied in the preamble), then shifted
        // views (computed at their first gate).
        for (v, vector) in program.vectors.iter().enumerate() {
            if !used.contains(&v) || vector.shift.is_some() {
                continue;
            }
            match copy_runs(program, v, &slot_addr)? {
                None => vector_addr[v] = slot_addr(vector.slot(0))?,
                Some(runs) => {
                    vector_addr[v] = cursor;
                    cursor += vector.len * word;
                    view_copies.push((v, runs));
                }
            }
        }
        for (v, vector) in program.vectors.iter().enumerate() {
            if used.contains(&v) && vector.shift.is_some() {
                vector_addr[v] = cursor;
                cursor += vector.len * word;
            }
        }
        let mut table_addr = Vec::with_capacity(program.tables.len());
        for table in &program.tables {
            table_addr.push(cursor);
            cursor += table.len * word;
        }
        let family_scratch_mptr = cursor;
        cursor += memory.family_scratch_words * word;
        let stack_end = memory.stack_mptr + memory.stack_words * word;
        if cursor > stack_end {
            return Err(format!(
                "quotient scratch region too small: needs up to {cursor:#x}, reserved up to {stack_end:#x}"
            ));
        }
        let run_addr = program
            .run_offsets()
            .into_iter()
            .map(|off| memory.const_table_mptr + off * word)
            .collect();
        let pool_addr = (0..program.pool.len())
            .map(|i| memory.const_table_mptr + program.pool_offset(i) * word)
            .collect();

        // Scratch must not alias any slot read by the identities.
        let scratch = memory.stack_mptr..cursor;
        let state = memory.state_mptr..(memory.state_mptr + memory.state_words * word);
        for (slot, addr) in &slots {
            if scratch.contains(addr) || state.contains(addr) {
                return Err(format!(
                    "evaluation slot {} at {addr:#x} aliases quotient scratch",
                    slot.name()
                ));
            }
        }

        Ok(Self {
            slots,
            buckets,
            main_acc,
            r_slot,
            y_pow,
            vector_addr,
            view_copies,
            table_addr,
            run_addr,
            pool_addr,
            const_table_mptr: memory.const_table_mptr,
            family_scratch_mptr,
            schedule: schedule(program),
        })
    }

    /// Address of `Y_POW[k]`.
    pub(crate) fn y_pow_addr(&self, k: usize) -> usize {
        self.y_pow + k * WORD_BYTES
    }
}
