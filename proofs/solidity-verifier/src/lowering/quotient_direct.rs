// SPDX-License-Identifier: CC0-1.0
//! Orchestration of the direct quotient lowering (`QuotientLowering::Direct`)
//! for one verifier build: program construction from the constraint system,
//! memory binding against the converged verifier layout, code-generation-time
//! IR translation validation, Yul rendering (identity functions plus the
//! generator's structured permutation / lookup / trash emitters with the
//! explicit `Y_POW[m-1-j]` fold) and the structural fold check of the
//! rendered sites. Both renders (production and trace) are produced and
//! checked when the plan is built; the plan carries exactly the checked Yul.

use std::cell::RefCell;

use ruint::aliases::U256;

use crate::lowering::{
    diagnostics,
    encoding::{ConstraintSystemMeta, Data, Location, Value, Word},
    layout::memory::VerifierMemoryLayout,
    quotient::StructuredFold,
    quotient_numerator::{
        direct::{
            emit::{self, DirectFamilies, FamilyBody},
            folds::{self, FoldContext, FoldRecord},
            layout::{self as direct_layout, DirectLayout, DirectMemory},
            validate, DirectOptions, DirectQuotientProgram, DirectSlot,
        },
        Evaluator,
    },
    VerifierBuildInputs,
};

/// Direct quotient program bound to the converged verifier memory,
/// validated against the source trees, rendered and fold-checked.
#[derive(Clone, Debug)]
pub(crate) struct DirectQuotientPlanned {
    pub(crate) program: DirectQuotientProgram,
    // Read by the plan tests and the fold-check tests.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) layout: DirectLayout,
    /// VK constant table words, as deployed.
    pub(crate) table: Vec<U256>,
    /// `SELECTOR_ACC_MPTR` of the verifier memory (bucket `s` is read by the
    /// PCS at `+ 32 s`).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) selector_acc_mptr: usize,
    /// Production render (fold-checked).
    pub(crate) rendering: DirectQuotientRendering,
    /// Trace render (fold-checked).
    pub(crate) trace_rendering: DirectQuotientRendering,
    /// Fold sites and section calls of the production render.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) folds: FoldRecord,
}

/// Direct quotient pieces consumed by the verifier templates.
#[derive(Clone, Debug, Default)]
pub(crate) struct DirectQuotientRendering {
    /// Contract-level Solidity constant declarations.
    pub(crate) constants: Vec<String>,
    /// Yul function definitions, emitted at the top of the verifier's
    /// assembly block (next to the other helpers).
    pub(crate) functions: Vec<String>,
    /// The quotient section block.
    pub(crate) block: Vec<String>,
}

/// Absolute memory address of a word handle.
fn word_addr(word: &Word, what: &str) -> Result<usize, String> {
    if word.loc() != Location::Memory {
        return Err(format!("{what} is not memory-resident"));
    }
    match word.ptr().value() {
        Value::Integer(offset) if offset >= 0 => Ok(offset as usize),
        _ => Err(format!("{what} has a symbolic address")),
    }
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Build the memory-independent direct program from the constraint
    /// system and the identity manifest.
    pub(crate) fn direct_quotient_program(&self) -> Result<DirectQuotientProgram, String> {
        let manifest = diagnostics::quotient_identity_manifest_for_meta(*self, self.meta);
        DirectQuotientProgram::build(
            self.vk.cs(),
            &self.meta.advice_queries,
            &manifest,
            DirectOptions::default(),
        )
    }

    /// Scratch words of the structured families (they run after all gate
    /// identities and get their own region after the gate scratch).
    pub(crate) fn direct_family_scratch_words(&self, meta: &ConstraintSystemMeta) -> usize {
        let permutation = if meta.num_permutation_zs > 0 {
            Self::structured_permutation_scratch_words(meta)
        } else {
            0
        };
        let lookup = if meta.num_lookups > 0 {
            self.structured_lookup_scratch_words(meta)
        } else {
            0
        };
        permutation.max(lookup)
    }

    /// Address resolver for evaluation slots.
    pub(crate) fn direct_slot_resolver<'a>(
        meta: &'a ConstraintSystemMeta,
        data: &'a Data,
        instance_eval_mptr: usize,
    ) -> impl Fn(DirectSlot) -> Result<usize, String> + 'a {
        move |slot| match slot {
            DirectSlot::Advice { column, rotation } => word_addr(
                data.advice_evals
                    .get(&(column, rotation))
                    .ok_or_else(|| format!("no advice eval for {}", slot.name()))?,
                &slot.name(),
            ),
            DirectSlot::Fixed { column, rotation } => word_addr(
                data.fixed_evals
                    .get(&(column, rotation))
                    .ok_or_else(|| format!("no fixed eval for {}", slot.name()))?,
                &slot.name(),
            ),
            DirectSlot::Instance { column, rotation } => {
                if column < meta.num_committed_instances {
                    word_addr(
                        data.committed_instance_evals
                            .get(&(column, rotation))
                            .ok_or_else(|| format!("no instance eval for {}", slot.name()))?,
                        &slot.name(),
                    )
                } else if rotation == 0 {
                    // The single non-committed instance column is
                    // Lagrange-interpolated into INSTANCE_EVAL_MPTR.
                    Ok(instance_eval_mptr)
                } else {
                    Err(format!(
                        "rotated non-committed instance query {}",
                        slot.name()
                    ))
                }
            }
            DirectSlot::Challenge { index } => word_addr(
                data.challenges
                    .get(index)
                    .ok_or_else(|| format!("no challenge slot for {}", slot.name()))?,
                &slot.name(),
            ),
        }
    }

    /// `(state words, stack words)` the memory planner must reserve.
    pub(crate) fn direct_scratch_requirements(
        &self,
        program: &DirectQuotientProgram,
        meta: &ConstraintSystemMeta,
        data: &Data,
        instance_eval_mptr: usize,
    ) -> Result<(usize, usize), String> {
        let resolve = Self::direct_slot_resolver(meta, data, instance_eval_mptr);
        let gate = direct_layout::gate_scratch_words(program, &resolve)?;
        Ok((
            direct_layout::state_words(program),
            gate + self.direct_family_scratch_words(meta),
        ))
    }

    /// Bind the program to the final memory layout and validate it.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn plan_direct_quotient(
        &self,
        program: DirectQuotientProgram,
        meta: &ConstraintSystemMeta,
        data: &Data,
        memory: &VerifierMemoryLayout,
        const_table_mptr: usize,
        state_words: usize,
        stack_words: usize,
    ) -> Result<DirectQuotientPlanned, String> {
        // The structured family emitters produce a block exactly when the
        // constraint system has the argument; an identity range without its
        // emitter would silently drop identities.
        for (name, count, present) in [
            (
                "permutation",
                program.permutation.count,
                meta.num_permutation_zs > 0,
            ),
            ("lookup", program.lookup.count, meta.num_lookups > 0),
            ("trash", program.trash.count, meta.num_trashcans > 0),
        ] {
            if (count > 0) != present {
                return Err(format!(
                    "{name} identity range ({count} identities) does not match the constraint system"
                ));
            }
        }
        program.trace_ids()?;
        let instance_eval_mptr = memory.instance_eval_mptr.value().as_usize();
        let resolve = Self::direct_slot_resolver(meta, data, instance_eval_mptr);
        let layout = DirectLayout::bind(
            &program,
            DirectMemory {
                selector_acc_mptr: memory.selector_acc_mptr,
                state_mptr: memory.quotient_tmp_mptr,
                state_words,
                stack_mptr: memory.quotient_stack_mptr,
                stack_words,
                const_table_mptr,
                family_scratch_words: self.direct_family_scratch_words(meta),
            },
            resolve,
        )?;
        let table: Vec<U256> = program.table_words().into_iter().map(|w| w.value).collect();
        let seed = crate::lowering::encoding::fe_to_u256::<midnight_curves::Fq>(
            &self.vk.transcript_repr(),
        )
        .to_be_bytes::<32>();
        validate::validate(&program, &layout, &table, &seed)?;
        let selector_acc_mptr = memory.selector_acc_mptr;
        let (rendering, folds) =
            self.direct_quotient_rendering(&program, &layout, meta, data, false);
        self.direct_fold_check(&program, &layout, selector_acc_mptr, meta, &folds)
            .map_err(|err| format!("y-batch fold check (production render): {err}"))?;
        let (trace_rendering, trace_folds) =
            self.direct_quotient_rendering(&program, &layout, meta, data, true);
        self.direct_fold_check(&program, &layout, selector_acc_mptr, meta, &trace_folds)
            .map_err(|err| format!("y-batch fold check (trace render): {err}"))?;
        Ok(DirectQuotientPlanned {
            program,
            layout,
            table,
            selector_acc_mptr,
            rendering,
            trace_rendering,
            folds,
        })
    }

    /// Structural check of the fold sites of one render against the identity
    /// manifest (`direct::folds`).
    pub(crate) fn direct_fold_check(
        &self,
        program: &DirectQuotientProgram,
        layout: &DirectLayout,
        selector_acc_mptr: usize,
        meta: &ConstraintSystemMeta,
        record: &FoldRecord,
    ) -> Result<(), String> {
        let manifest = diagnostics::quotient_identity_manifest_for_meta(*self, meta);
        folds::check(
            record,
            &FoldContext {
                manifest: &manifest,
                m: program.m,
                permutation_sets: meta.num_permutation_zs,
                lookup_chunks: &meta.protocol.lookup_chunks,
                y_pow: layout.y_pow,
                buckets: &layout.buckets,
                selector_acc_mptr,
                simple_selector_cols: &program.sorted_simple,
            },
        )
    }

    /// Native expected values of the direct lowering's intermediate trace
    /// variables for a proof whose main evaluation scalars (proof read order)
    /// are `evals`. See `quotient_numerator::direct::trace`.
    pub(crate) fn direct_quotient_trace_values(
        &self,
        evals: &[midnight_curves::Fq],
    ) -> Result<Vec<(u64, String, midnight_curves::Fq)>, String> {
        use crate::lowering::protocol::EvalRead;
        let program = self.direct_quotient_program()?;
        let mut index = std::collections::HashMap::new();
        for (i, read) in self.meta.protocol.proof.evals.iter().enumerate() {
            let slot = match read {
                EvalRead::Advice(q) => DirectSlot::Advice {
                    column: q.column,
                    rotation: q.rotation,
                },
                EvalRead::Fixed(q) => DirectSlot::Fixed {
                    column: q.column,
                    rotation: q.rotation,
                },
                EvalRead::CommittedInstance(q) => DirectSlot::Instance {
                    column: q.column,
                    rotation: q.rotation,
                },
                _ => continue,
            };
            index.insert(slot, i);
        }
        let eval_of = |slot: DirectSlot| -> Result<midnight_curves::Fq, String> {
            let i = index
                .get(&slot)
                .ok_or_else(|| format!("{} is not a proof evaluation", slot.name()))?;
            evals.get(*i).copied().ok_or_else(|| {
                format!(
                    "evaluation vector has {} entries, {} is entry {i}",
                    evals.len(),
                    slot.name()
                )
            })
        };
        program.native_trace_values(&eval_of)
    }

    /// Render the direct quotient block and constants, and return the fold
    /// sites of the render (checked by [`Self::direct_fold_check`]).
    pub(crate) fn direct_quotient_rendering(
        &self,
        program: &DirectQuotientProgram,
        layout: &DirectLayout,
        meta: &ConstraintSystemMeta,
        data: &Data,
        trace: bool,
    ) -> (DirectQuotientRendering, FoldRecord) {
        let evaluator = Evaluator::new(self.vk.cs(), meta, data).with_pow5_helper(true);
        // One site recorder per family: each body becomes its own function.
        let family = |emit: &dyn Fn(StructuredFold<'_>) -> Option<Vec<String>>| {
            let sites = RefCell::new(Vec::new());
            let lines = emit(StructuredFold::Weighted {
                m: program.m,
                trace,
                sites: &sites,
            })?;
            Some(FamilyBody {
                lines,
                sites: sites.into_inner(),
            })
        };
        let families = DirectFamilies {
            permutation: (program.permutation.count > 0)
                .then(|| {
                    family(&|fold| {
                        Self::structured_permutation_loop_block(
                            meta,
                            data,
                            &evaluator,
                            layout.family_scratch_mptr,
                            fold,
                            program.permutation.base,
                        )
                    })
                })
                .flatten(),
            lookup: (program.lookup.count > 0)
                .then(|| {
                    family(&|fold| {
                        self.structured_lookup_loop_block(
                            meta,
                            data,
                            &evaluator,
                            layout.family_scratch_mptr,
                            fold,
                            program.lookup.base,
                        )
                    })
                })
                .flatten(),
            trash: (program.trash.count > 0)
                .then(|| {
                    family(&|fold| {
                        self.structured_trash_loop_block(
                            meta,
                            data,
                            &evaluator,
                            fold,
                            program.trash.base,
                        )
                    })
                })
                .flatten(),
            pow5: false,
        };
        let families = DirectFamilies {
            pow5: evaluator.pow5_used(),
            ..families
        };
        let trace_base = trace.then_some(crate::lowering::layout::trace::QUOTIENT_IDENTITY_BASE);
        let yul = emit::quotient_block(program, layout, &families, trace_base);
        (
            DirectQuotientRendering {
                constants: emit::solidity_constants(program, layout),
                functions: yul.functions,
                block: yul.section,
            },
            yul.folds,
        )
    }
}
