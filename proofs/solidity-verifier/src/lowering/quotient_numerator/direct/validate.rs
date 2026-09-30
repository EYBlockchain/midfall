// SPDX-License-Identifier: CC0-1.0
//! Code-generation-time translation validation of the direct lowering's IR.
//!
//! For several pseudo-random assignments of every evaluation slot, this
//! module executes the bound *IR* (`DirectExpr`, not the emitted Yul) on a
//! simulated memory holding the evaluation slots at their addresses and the
//! VK constant table at its address: limb-view copies, shifted views, product
//! tables, and every gate identity's IR including its helper calls (which
//! read coefficient runs from the table words and limbs from the vector
//! pointers). Each identity value is compared with `Expression::evaluate` of
//! the original gate polynomial on the same assignment (simple selectors
//! evaluate to one, as in `partially_evaluate_identities`). Any mismatch,
//! unwritten memory read, shape inconsistency, or non-canonical table word is
//! an error: the build fails closed.
//!
//! Scope: the simulated execution and the reference use the same slot
//! resolver, and the Yul text produced by `emit` (identity bodies, helper
//! functions, `Y_POW`, bucket zeroing, the final `-Q_MAIN_ACC`) as well as the
//! permutation / lookup / trash bodies are outside this check. The fold
//! structure (weights and buckets of every identity, families included) is
//! proven by `folds`; the emitted Yul is exercised by the EVM probe tests.

use std::collections::HashMap;

use ff::{Field, FromUniformBytes, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::plonk::Expression;
use ruint::aliases::U256;
use sha3::{Digest, Keccak256};

use super::{
    is_pooled,
    layout::{DirectLayout, SectionOp},
    DirectCall, DirectExpr, DirectQuotientProgram, DirectSlot,
};
use crate::lowering::layout::WORD_BYTES;

/// Number of random evaluation points.
pub(crate) const VALIDATION_POINTS: usize = 4;

/// Deterministic pseudo-random field element for `(seed, point, index)`.
fn sample(seed: &[u8], point: usize, index: usize) -> Fq {
    let mut wide = [0u8; 64];
    for (half, chunk) in wide.chunks_mut(32).enumerate() {
        let mut hasher = Keccak256::new();
        hasher.update(b"halo2-solidity-verifier/direct-quotient-validation");
        hasher.update(seed);
        hasher.update((point as u64).to_be_bytes());
        hasher.update((index as u64).to_be_bytes());
        hasher.update([half as u8]);
        chunk.copy_from_slice(&hasher.finalize());
    }
    Fq::from_uniform_bytes(&wide)
}

/// Canonical field element of a table word.
fn word_to_fq(word: &U256) -> Option<Fq> {
    let mut repr = <Fq as PrimeField>::Repr::default();
    repr.as_mut().copy_from_slice(&word.to_le_bytes::<32>());
    Option::<Fq>::from(Fq::from_repr(repr))
}

/// Simulated EVM memory of field words.
struct Memory {
    words: HashMap<usize, Fq>,
}

impl Memory {
    fn read(&self, addr: usize) -> Result<Fq, String> {
        self.words
            .get(&addr)
            .copied()
            .ok_or_else(|| format!("read of unwritten memory word {addr:#x}"))
    }

    fn write(&mut self, addr: usize, value: Fq) {
        self.words.insert(addr, value);
    }
}

/// Simulated executor of the bound program.
struct Executor<'a> {
    program: &'a DirectQuotientProgram,
    layout: &'a DirectLayout,
    mem: Memory,
}

impl Executor<'_> {
    fn constant(&self, value: &Fq) -> Result<Fq, String> {
        if is_pooled(value) {
            let idx = self
                .program
                .pool_index(value)
                .ok_or_else(|| format!("pooled constant {value:?} missing from the VK table"))?;
            self.mem.read(self.layout.pool_addr[idx])
        } else {
            Ok(*value)
        }
    }

    fn call(&self, call: DirectCall) -> Result<Fq, String> {
        match call {
            DirectCall::SumExprs { run, vector } => {
                let len = self.program.runs[run].values.len();
                if self.program.vectors[vector].len != len {
                    return Err(format!(
                        "sum_exprs run {} has {len} coefficients but vector {} has {} limbs",
                        self.program.runs[run].name,
                        self.program.vectors[vector].name,
                        self.program.vectors[vector].len
                    ));
                }
                let (coeffs, exprs) = (self.layout.run_addr[run], self.layout.vector_addr[vector]);
                let mut acc = Fq::ZERO;
                for i in 0..len {
                    acc += self.mem.read(coeffs + i * WORD_BYTES)?
                        * self.mem.read(exprs + i * WORD_BYTES)?;
                }
                Ok(acc)
            }
            DirectCall::SumExprsByDegree { run, table } => {
                let len = self.program.runs[run].values.len();
                if self.program.tables[table].len != len {
                    return Err(format!(
                        "sum_exprs_by_degree run {} has {len} coefficients but table {} has {} entries",
                        self.program.runs[run].name,
                        self.program.tables[table].name,
                        self.program.tables[table].len
                    ));
                }
                let (coeffs, t) = (self.layout.run_addr[run], self.layout.table_addr[table]);
                let mut acc = Fq::ZERO;
                for i in 0..len {
                    acc += self.mem.read(coeffs + i * WORD_BYTES)?
                        * self.mem.read(t + i * WORD_BYTES)?;
                }
                Ok(acc)
            }
        }
    }

    fn eval(&self, expr: &DirectExpr) -> Result<Fq, String> {
        Ok(match expr {
            DirectExpr::Constant(c) => self.constant(c)?,
            DirectExpr::SimpleSelector(_) => Fq::ONE,
            DirectExpr::Slot(slot) => {
                let addr = self
                    .layout
                    .slots
                    .get(slot)
                    .ok_or_else(|| format!("slot {} has no address", slot.name()))?;
                self.mem.read(*addr)?
            }
            DirectExpr::Negated(inner) => -self.eval(inner)?,
            DirectExpr::Sum(lhs, rhs) => self.eval(lhs)? + self.eval(rhs)?,
            DirectExpr::Product(lhs, rhs) => self.eval(lhs)? * self.eval(rhs)?,
            DirectExpr::Call(call) => self.call(*call)?,
        })
    }

    fn shift_view(&mut self, vector: usize) -> Result<(), String> {
        let v = &self.program.vectors[vector];
        let (base, shift) = v.shift.ok_or("shift view of an unshifted vector")?;
        let shift = self.constant(&shift)?;
        let (dst, src) = (
            self.layout.vector_addr[vector],
            self.layout.vector_addr[base],
        );
        for i in 0..v.len {
            let value = self.mem.read(src + i * WORD_BYTES)? + shift;
            self.mem.write(dst + i * WORD_BYTES, value);
        }
        Ok(())
    }

    fn product_table(&mut self, table: usize) -> Result<(), String> {
        let t = &self.program.tables[table];
        let (xs, ys) = (&self.program.vectors[t.xs], &self.program.vectors[t.ys]);
        if t.len != xs.len + ys.len - 1 {
            return Err(format!("table {} has inconsistent length", t.name));
        }
        let (xa, ya, ta) = (
            self.layout.vector_addr[t.xs],
            self.layout.vector_addr[t.ys],
            self.layout.table_addr[table],
        );
        let mut out = vec![Fq::ZERO; t.len];
        for i in 0..xs.len {
            for j in 0..ys.len {
                out[i + j] +=
                    self.mem.read(xa + i * WORD_BYTES)? * self.mem.read(ya + j * WORD_BYTES)?;
            }
        }
        for (k, value) in out.into_iter().enumerate() {
            self.mem.write(ta + k * WORD_BYTES, value);
        }
        Ok(())
    }
}

/// Reference value of a gate polynomial under a slot assignment.
fn reference(
    source: &Expression<Fq>,
    simple: &[usize],
    values: &HashMap<DirectSlot, Fq>,
) -> Result<Fq, String> {
    let get = |slot: DirectSlot| -> Result<Fq, String> {
        values.get(&slot).copied().ok_or_else(|| {
            format!(
                "reference evaluation reads {} which the lowering never binds",
                slot.name()
            )
        })
    };
    source.evaluate(
        &|c| Ok(c),
        &|_| Err("virtual selector in a gate polynomial".to_string()),
        &|q| {
            if simple.contains(&q.column_index()) {
                Ok(Fq::ONE)
            } else {
                get(DirectSlot::Fixed {
                    column: q.column_index(),
                    rotation: q.rotation().0,
                })
            }
        },
        &|q| {
            get(DirectSlot::Advice {
                column: q.column_index(),
                rotation: q.rotation().0,
            })
        },
        &|q| {
            get(DirectSlot::Instance {
                column: q.column_index(),
                rotation: q.rotation().0,
            })
        },
        &|c| get(DirectSlot::Challenge { index: c.index() }),
        &|a| a.map(|x| -x),
        &|a, b| Ok(a? + b?),
        &|a, b| Ok(a? * b?),
        &|a, c| Ok(a? * c),
    )
}

/// Validate a bound program against the source trees; `table` is the VK
/// constant table exactly as it will be deployed.
pub(crate) fn validate(
    program: &DirectQuotientProgram,
    layout: &DirectLayout,
    table: &[U256],
    seed: &[u8],
) -> Result<(), String> {
    if table.len() != program.table_len() {
        return Err(format!(
            "VK constant table has {} words, program expects {}",
            table.len(),
            program.table_len()
        ));
    }
    let mut seen_addr: HashMap<usize, DirectSlot> = HashMap::new();
    for (slot, addr) in &layout.slots {
        if let Some(other) = seen_addr.insert(*addr, *slot) {
            return Err(format!(
                "slots {} and {} share address {addr:#x}",
                other.name(),
                slot.name()
            ));
        }
    }
    for point in 0..VALIDATION_POINTS {
        let mut mem = Memory {
            words: HashMap::new(),
        };
        for (i, word) in table.iter().enumerate() {
            let value = word_to_fq(word).ok_or_else(|| {
                format!("VK constant table word {i} is not a canonical Fr element")
            })?;
            mem.write(layout.const_table_mptr + i * WORD_BYTES, value);
        }
        let mut values = HashMap::new();
        for (index, (slot, addr)) in layout.slots.iter().enumerate() {
            let value = sample(seed, point, index);
            values.insert(*slot, value);
            mem.write(*addr, value);
        }
        let mut exec = Executor {
            program,
            layout,
            mem,
        };
        for (vector, runs) in &layout.view_copies {
            let dst = layout.vector_addr[*vector];
            for run in runs {
                for w in 0..run.words {
                    let value = exec.mem.read(run.src + w * WORD_BYTES)?;
                    exec.mem.write(dst + (run.view_word + w) * WORD_BYTES, value);
                }
            }
        }
        for op in &layout.schedule {
            match *op {
                SectionOp::ShiftView { vector, .. } => exec.shift_view(vector)?,
                SectionOp::ProductTable { table } => exec.product_table(table)?,
                SectionOp::Identity { index } => {
                    let identity = &program.gates[index];
                    let lowered = exec.eval(&identity.expr).map_err(|err| {
                        format!(
                            "identity {} (cs.gates()[{}] \"{}\" polynomial[{}]): {err}",
                            identity.global_index,
                            identity.gate_index,
                            identity.gate_name,
                            identity.polynomial_index
                        )
                    })?;
                    let expected = reference(&identity.source, &program.sorted_simple, &values)?;
                    if lowered != expected {
                        return Err(format!(
                            "identity {} (cs.gates()[{}] \"{}\" polynomial[{}]) differs from Expression::evaluate at validation point {point}",
                            identity.global_index,
                            identity.gate_index,
                            identity.gate_name,
                            identity.polynomial_index
                        ));
                    }
                }
            }
        }
        // Every identity must have been scheduled exactly once, in order.
        let order: Vec<usize> = layout
            .schedule
            .iter()
            .filter_map(|op| match op {
                SectionOp::Identity { index } => Some(*index),
                _ => None,
            })
            .collect();
        if order != (0..program.gates.len()).collect::<Vec<_>>() {
            return Err("section schedule does not call every gate identity once in order".into());
        }
    }
    Ok(())
}
