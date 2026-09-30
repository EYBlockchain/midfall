// SPDX-License-Identifier: CC0-1.0
//! Converged lowering plan for one Solidity verifier build.
//!
//! Rendering, diagnostics, and proof repacking all need the same finalized
//! VK payload, proof layout, memory layout, and quotient program facts. This
//! module makes that post-convergence state explicit so call sites do not
//! independently rebuild small slices of the verifier shape.

use crate::{
    api::{GeneratorError, QuotientLowering},
    lowering::{
        abi::ProofCalldataLayout,
        encoding::{ConstraintSystemMeta, Data, Ptr},
        kzg, layout,
        layout::memory::{PcsMemoryRequirements, VerifierMemoryLayout, VerifierMemoryLayoutConfig},
        quotient::{QuotientComputationBlocks, QuotientHelperFlags, QuotientStateSlots},
        quotient_direct::{DirectQuotientPlanned, DirectQuotientRendering},
        quotient_numerator::vm::{
            QuotientProgramBuild, QuotientProgramPlan, RepackedProofLayoutPlan,
        },
        render::{Halo2VerifyingKey, QuotientExternal, QuotientProgram},
        VerifierBuildInputs,
    },
};

/// Finalized, reusable codegen facts for one verifier render/repack operation.
#[derive(Debug)]
pub(crate) struct LoweringPlan {
    pub(crate) vk: Halo2VerifyingKey,
    pub(crate) vk_mptr: Ptr,
    pub(crate) meta: ConstraintSystemMeta,
    pub(crate) data: Data,
    pub(crate) proof_layout: ProofCalldataLayout,
    /// Quotient numerator lowering this plan was built for.
    pub(crate) lowering: QuotientLowering,
    /// Sorted simple-selector fixed columns (selector bucket order).
    pub(crate) sorted_simple: Vec<usize>,
    /// Compact VM quotient plan (`QuotientLowering::Vm`).
    pub(crate) quotient: Option<PlannedQuotient>,
    /// Direct quotient plan (`QuotientLowering::Direct`).
    pub(crate) direct: Option<DirectQuotientPlanned>,
    pub(crate) pcs_memory_requirements: PcsMemoryRequirements,
    pub(crate) memory: VerifierMemoryLayout,
}

/// Quotient VM and rendering metadata tied to the finalized memory layout.
#[derive(Clone, Debug)]
pub(crate) struct PlannedQuotient {
    pub(crate) plan: QuotientProgramPlan,
    pub(crate) build: QuotientProgramBuild,
    pub(crate) program: QuotientProgram,
    pub(crate) stack_mptr: usize,
    pub(crate) state_slots: QuotientStateSlots,
}

/// Quotient rendering mode for the main verifier.
#[derive(Clone, Debug)]
pub(crate) enum QuotientRendering {
    /// The main verifier delegates quotient reconstruction to a pinned
    /// evaluator and therefore renders no local quotient VM program.
    External { external: QuotientExternal },
    /// The main verifier runs the compact quotient VM and any native callbacks
    /// locally.
    Compact {
        blocks: Box<QuotientComputationBlocks>,
        program: QuotientProgram,
    },
    /// The main verifier runs the direct per-identity Yul functions.
    Direct {
        rendering: Box<DirectQuotientRendering>,
    },
}

impl QuotientRendering {
    /// Helper flags needed by the Solidity/Yul templates.
    pub(crate) fn helper_flags(&self) -> QuotientHelperFlags {
        match self {
            Self::External { .. } | Self::Direct { .. } => {
                QuotientComputationBlocks::default().helper_flags()
            }
            Self::Compact { blocks, .. } => blocks.helper_flags(),
        }
    }

    /// Decompose into the legacy template fields from one coordinated value.
    pub(crate) fn into_template_parts(
        self,
    ) -> (
        Option<QuotientExternal>,
        QuotientComputationBlocks,
        Option<QuotientProgram>,
        Option<DirectQuotientRendering>,
    ) {
        match self {
            Self::External { external } => (
                Some(external),
                QuotientComputationBlocks::default(),
                None,
                None,
            ),
            Self::Compact { blocks, program } => (None, *blocks, Some(program), None),
            Self::Direct { rendering } => (
                None,
                QuotientComputationBlocks::default(),
                None,
                Some(*rendering),
            ),
        }
    }
}

/// Quotient rendering facts for the standalone evaluator artifact.
#[derive(Clone, Debug)]
pub(crate) struct QuotientEvaluatorRendering {
    pub(crate) external: QuotientExternal,
    pub(crate) blocks: QuotientComputationBlocks,
    pub(crate) program: QuotientProgram,
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Build the finalized (compact VM) lowering plan for this concrete
    /// verifier.
    pub(crate) fn lowering_plan(&self) -> LoweringPlan {
        LoweringPlan::new(self)
    }

    /// Build the finalized lowering plan for the requested quotient lowering.
    pub(crate) fn lowering_plan_for(
        &self,
        lowering: QuotientLowering,
    ) -> Result<LoweringPlan, GeneratorError> {
        match lowering {
            QuotientLowering::Vm => Ok(LoweringPlan::new(self)),
            QuotientLowering::Direct => LoweringPlan::new_direct(self),
        }
    }
}

impl LoweringPlan {
    /// Compact VM quotient plan.
    ///
    /// Panics for a direct-lowering plan; callers on VM-only paths (the
    /// external evaluator, VM diagnostics) only ever build VM plans.
    pub(crate) fn vm_quotient(&self) -> &PlannedQuotient {
        self.quotient.as_ref().expect("compact quotient VM plan (QuotientLowering::Vm)")
    }

    /// Build a finalized plan for the direct quotient lowering.
    ///
    /// The VK payload carries the direct constant table (coefficient runs and
    /// scalar constants) in the quotient-constants section and no program.
    /// The table depends only on the constraint system, so no convergence
    /// loop is needed; the memory planner reserves the direct quotient state
    /// (`Q_MAIN_ACC`, `r`, `Y_POW`) and scratch (limb views, product tables,
    /// family scratch), and the bound program is validated before any
    /// Solidity is rendered.
    pub(crate) fn new_direct(inputs: &VerifierBuildInputs<'_, '_>) -> Result<Self, GeneratorError> {
        let fail = |stage: &'static str| {
            move |message: String| GeneratorError::Planning { stage, message }
        };
        let proof_cptr = Ptr::calldata(layout::abi::VERIFY_PROOF_PROOF_CPTR);
        let program = inputs.direct_quotient_program().map_err(fail("direct quotient lowering"))?;
        let vk = inputs.generate_vk_direct(&program);
        let (vk_mptr, meta, data, pre_memory) = inputs.meta_data_for_stable_static_layout(&vk);
        let proof_layout = ProofCalldataLayout::from_protocol(
            &meta.protocol,
            proof_cptr.value().as_usize(),
            meta.num_evals,
            meta.num_point_sets,
        );
        let (state_words, stack_words) = inputs
            .direct_scratch_requirements(
                &program,
                &meta,
                &data,
                pre_memory.instance_eval_mptr.value().as_usize(),
            )
            .map_err(fail("direct quotient memory planning"))?;
        let pcs_memory_requirements = kzg::memory_requirements(&meta, &data);
        let memory = inputs.memory_layout_for(
            &meta,
            &vk,
            vk_mptr,
            VerifierMemoryLayoutConfig {
                quotient_state_words: state_words,
                quotient_stack_words: stack_words,
                acc_msm_terms: Self::acc_msm_terms(inputs),
                pcs: pcs_memory_requirements,
                ..VerifierMemoryLayoutConfig::default()
            },
        );
        let const_offset = vk
            .quotient_const_offset_words
            .ok_or_else(|| fail("direct quotient VK payload")("missing constant table".into()))?;
        let const_table_mptr = (vk_mptr + const_offset).value().as_usize();
        let direct = inputs
            .plan_direct_quotient(
                program,
                &meta,
                &data,
                &memory,
                const_table_mptr,
                state_words,
                stack_words,
            )
            .map_err(fail("direct quotient translation validation"))?;
        let sorted_simple = direct.program.sorted_simple.clone();
        let plan = Self {
            vk,
            vk_mptr,
            meta,
            data,
            proof_layout,
            lowering: QuotientLowering::Direct,
            sorted_simple,
            quotient: None,
            direct: Some(direct),
            pcs_memory_requirements,
            memory,
        };
        plan.validate_generator_invariants().map_err(fail("generator invariants"))?;
        Ok(plan)
    }

    /// Build a finalized plan, preserving the existing bounded convergence
    /// process while exposing the resulting facts as one value.
    pub(crate) fn new(inputs: &VerifierBuildInputs<'_, '_>) -> Self {
        let proof_cptr = Ptr::calldata(layout::abi::VERIFY_PROOF_PROOF_CPTR);
        let vk = inputs.generate_vk();
        let (vk_mptr, meta, data, _) = inputs.meta_data_for_stable_static_layout(&vk);
        let proof_layout = ProofCalldataLayout::from_protocol(
            &meta.protocol,
            proof_cptr.value().as_usize(),
            meta.num_evals,
            meta.num_point_sets,
        );

        let quotient_plan = inputs.quotient_program_plan(&meta, &data);
        let sorted_simple = quotient_plan.sorted_simple.clone();
        let quotient_program_build =
            inputs.build_quotient_program_items(&quotient_plan.items, &quotient_plan.selector_fold);
        let native_callback_scratch_words =
            inputs.native_callback_scratch_words(&meta, &quotient_plan);
        let quotient_stack_words = VerifierBuildInputs::quotient_stack_words_for_build(
            &quotient_program_build,
            native_callback_scratch_words,
        );
        let quotient_state_words =
            VerifierBuildInputs::quotient_state_words(&quotient_plan.selector_fold);
        let pcs_memory_requirements = kzg::memory_requirements(&meta, &data);
        let memory = inputs.memory_layout_for(
            &meta,
            &vk,
            vk_mptr,
            VerifierMemoryLayoutConfig {
                quotient_state_words,
                quotient_stack_words,
                acc_msm_terms: Self::acc_msm_terms(inputs),
                pcs: pcs_memory_requirements,
                ..VerifierMemoryLayoutConfig::default()
            },
        );
        let (quotient_program, quotient_stack_mptr, quotient_state_slots) = inputs
            .quotient_template_program(
                quotient_program_build.clone(),
                &vk,
                vk_mptr,
                &memory,
                &quotient_plan.selector_fold,
            );

        let plan = Self {
            vk,
            vk_mptr,
            meta,
            data,
            proof_layout,
            lowering: QuotientLowering::Vm,
            sorted_simple,
            quotient: Some(PlannedQuotient {
                plan: quotient_plan,
                build: quotient_program_build,
                program: quotient_program,
                stack_mptr: quotient_stack_mptr,
                state_slots: quotient_state_slots,
            }),
            direct: None,
            pcs_memory_requirements,
            memory,
        };
        plan.validate_generator_invariants()
            .unwrap_or_else(|err| panic!("generator invariant violation: {err}"));
        plan
    }

    /// Repacking plan derived from the same proof layout used for rendering.
    pub(crate) fn repacked_proof_layout_plan(&self) -> RepackedProofLayoutPlan {
        RepackedProofLayoutPlan::from_proof_layout(&self.proof_layout)
    }

    /// Build quotient rendering for the main verifier.
    pub(crate) fn quotient_rendering(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        trace: bool,
        external_quotient: bool,
    ) -> QuotientRendering {
        if external_quotient {
            return QuotientRendering::External {
                external: self.quotient_external_frame(),
            };
        }
        if let Some(direct) = &self.direct {
            // The renders were produced and fold-checked when the plan was
            // built; the verifier gets exactly the checked Yul.
            let rendering = if trace {
                &direct.trace_rendering
            } else {
                &direct.rendering
            };
            return QuotientRendering::Direct {
                rendering: Box::new(rendering.clone()),
            };
        }

        QuotientRendering::Compact {
            blocks: Box::new(self.compact_quotient_blocks(inputs, trace)),
            program: self.vm_quotient().program.clone(),
        }
    }

    /// Build quotient rendering for the standalone evaluator artifact.
    pub(crate) fn quotient_evaluator_rendering(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        trace: bool,
    ) -> QuotientEvaluatorRendering {
        QuotientEvaluatorRendering {
            external: self.quotient_external_frame(),
            blocks: self.compact_quotient_blocks(inputs, trace),
            program: self.vm_quotient().program.clone(),
        }
    }

    /// Expected external evaluator frame for this finalized layout.
    pub(crate) fn quotient_external_frame(&self) -> QuotientExternal {
        VerifierBuildInputs::quotient_external_frame(
            self.vk_mptr,
            self.vk.len(),
            &self.meta,
            &self.memory,
            self.sorted_simple.len(),
        )
    }

    /// Generate local compact-VM/native-callback Yul blocks for inline renders.
    fn compact_quotient_blocks(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        trace: bool,
    ) -> QuotientComputationBlocks {
        let quotient = self.vm_quotient();
        inputs.compact_quotient_computation_blocks(
            &self.meta,
            &self.data,
            &quotient.plan,
            quotient.stack_mptr,
            quotient.state_slots,
            trace,
        )
    }

    /// Re-check cross-module invariants after convergence.
    ///
    /// This catches drift between independently computed protocol, memory,
    /// quotient, and precompile-coverage facts before any Solidity template is
    /// rendered.
    fn validate_generator_invariants(&self) -> Result<(), String> {
        self.meta
            .validate_against_protocol()
            .map_err(|err| format!("protocol invariant failed: {err}"))?;
        self.memory
            .validate()
            .map_err(|err| format!("memory-region non-overlap invariant failed: {err}"))?;
        kzg::validate_absorbed_g1_precompile_coverage(
            &self.meta,
            &self.data,
            &self.memory,
            &self.proof_layout,
        )
        .map_err(|err| format!("absorbed-G1 precompile coverage invariant failed: {err}"))?;
        let planned_pcs = kzg::memory_requirements(&self.meta, &self.data);
        if self.pcs_memory_requirements != planned_pcs {
            return Err(format!(
                "PCS memory requirements drifted: planned {:?}, recomputed {:?}",
                self.pcs_memory_requirements, planned_pcs
            ));
        }
        if let Some(direct) = &self.direct {
            if self.quotient.is_some() || self.lowering != QuotientLowering::Direct {
                return Err("direct plan also carries a compact VM plan".to_string());
            }
            if self.vk.quotient_program_words != 0 {
                return Err(format!(
                    "direct lowering must not reserve VM program words (got {})",
                    self.vk.quotient_program_words
                ));
            }
            if self.vk.quotient_const_words != direct.table.len() {
                return Err(format!(
                    "direct constant table drifted: VK reserves {} words, program has {}",
                    self.vk.quotient_const_words,
                    direct.table.len()
                ));
            }
            let offset = self.vk.quotient_const_offset_words.unwrap_or(usize::MAX);
            for (i, word) in direct.table.iter().enumerate() {
                if self.vk.constants.get(offset + i).map(|(_, value)| value) != Some(word) {
                    return Err(format!(
                        "direct constant table word {i} differs from the VK payload"
                    ));
                }
            }
            return Ok(());
        }
        let quotient = self.vm_quotient();
        if quotient.program.len != quotient.build.bytes.len() {
            return Err(format!(
                "quotient program length drifted: model={} build={}",
                quotient.program.len,
                quotient.build.bytes.len()
            ));
        }
        if quotient.build.consts.len() > self.vk.quotient_const_words {
            return Err(format!(
                "quotient const table exceeds VK reservation: consts={} words={}",
                quotient.build.consts.len(),
                self.vk.quotient_const_words
            ));
        }
        let quotient_program_words =
            layout::vk_payload::PackedProgramCodec::word_len_for_bytes(quotient.build.bytes.len());
        if quotient_program_words > self.vk.quotient_program_words {
            return Err(format!(
                "quotient bytecode exceeds VK reservation: program_words={quotient_program_words} reserved={}",
                self.vk.quotient_program_words
            ));
        }
        if quotient.program.stack_mptr != quotient.stack_mptr {
            return Err(format!(
                "quotient stack pointer drifted: model={:#x} planned={:#x}",
                quotient.program.stack_mptr, quotient.stack_mptr
            ));
        }
        if quotient.program.eval_numer_mptr != quotient.state_slots.eval_numer_mptr {
            return Err(format!(
                "quotient state pointer drifted: model={:#x} planned={:#x}",
                quotient.program.eval_numer_mptr, quotient.state_slots.eval_numer_mptr
            ));
        }
        Ok(())
    }

    /// Number of `(G1, scalar)` terms required by the optional accumulator MSM.
    fn acc_msm_terms(inputs: &VerifierBuildInputs<'_, '_>) -> usize {
        inputs
            .acc_encoding
            .map(|acc_encoding| {
                let fixed_scalar_count = acc_encoding
                    .fixed_scalar_count(inputs.num_instances)
                    .expect("accumulator encoding validated by GeneratorConfig");
                fixed_scalar_count + 1
            })
            .unwrap_or(0)
    }
}
