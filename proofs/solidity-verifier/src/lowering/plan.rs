// SPDX-License-Identifier: CC0-1.0
//! Converged lowering plan for one Solidity verifier build.
//!
//! Rendering, diagnostics, and proof repacking all need the same finalized
//! VK payload, proof layout, memory layout, and quotient program facts. This
//! module makes that post-convergence state explicit so call sites do not
//! independently rebuild small slices of the verifier shape.

use crate::lowering::{
    abi::ProofCalldataLayout,
    encoding::{ConstraintSystemMeta, Data, Ptr},
    kzg, layout,
    layout::memory::{PcsMemoryRequirements, VerifierMemoryLayout, VerifierMemoryLayoutConfig},
    quotient::{QuotientComputationBlocks, QuotientHelperFlags, QuotientStateSlots},
    quotient_numerator::vm::{
        self as vm, certify, QuotientProgramBuild, QuotientProgramPlan, RepackedProofLayoutPlan,
    },
    render::{Halo2VerifyingKey, QuotientExternal, QuotientProgram},
    VerifierBuildInputs,
};

/// Finalized, reusable codegen facts for one verifier render/repack operation.
#[derive(Debug)]
pub(crate) struct LoweringPlan {
    pub(crate) vk: Halo2VerifyingKey,
    pub(crate) vk_mptr: Ptr,
    pub(crate) meta: ConstraintSystemMeta,
    pub(crate) data: Data,
    pub(crate) proof_layout: ProofCalldataLayout,
    pub(crate) quotient: PlannedQuotient,
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
    pub(crate) sorted_simple: Vec<usize>,
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
}

impl QuotientRendering {
    /// Helper flags needed by the Solidity/Yul templates.
    pub(crate) fn helper_flags(&self) -> QuotientHelperFlags {
        match self {
            Self::External { .. } => QuotientComputationBlocks::default().helper_flags(),
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
    ) {
        match self {
            Self::External { external } => {
                (Some(external), QuotientComputationBlocks::default(), None)
            }
            Self::Compact { blocks, program } => (None, *blocks, Some(program)),
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
    /// Build the finalized lowering plan for this concrete verifier.
    pub(crate) fn lowering_plan(&self) -> LoweringPlan {
        LoweringPlan::new(self)
    }
}

impl LoweringPlan {
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
                quotient_operand_bounds(&meta, &data, &vk, vk_mptr, &memory),
                meta.num_simple_selectors,
            );

        let plan = Self {
            vk,
            vk_mptr,
            meta,
            data,
            proof_layout,
            quotient: PlannedQuotient {
                plan: quotient_plan,
                build: quotient_program_build,
                program: quotient_program,
                stack_mptr: quotient_stack_mptr,
                state_slots: quotient_state_slots,
                sorted_simple,
            },
            pcs_memory_requirements,
            memory,
        };
        plan.validate_generator_invariants()
            .unwrap_or_else(|err| panic!("generator invariant violation: {err}"));

        // Certify the limb superinstructions against a generic-opcode build of
        // the same identity stream. This needs `inputs`, so it runs here rather
        // than inside `validate_generator_invariants`.
        let baseline_build = inputs.build_quotient_program_items_with_limb_ops(
            &plan.quotient.plan.items,
            &plan.quotient.plan.selector_fold,
            false,
        );
        certify::certify_quotient_builds_agree(
            &plan.quotient.plan,
            &plan.quotient.build,
            &baseline_build,
            &plan.vk,
        )
        .unwrap_or_else(|err| panic!("quotient dual-build certification failed: {err}"));

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

        QuotientRendering::Compact {
            blocks: Box::new(self.compact_quotient_blocks(inputs, trace)),
            program: self.quotient.program.clone(),
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
            program: self.quotient.program.clone(),
        }
    }

    /// Expected external evaluator frame for this finalized layout.
    pub(crate) fn quotient_external_frame(&self) -> QuotientExternal {
        VerifierBuildInputs::quotient_external_frame(
            self.vk_mptr,
            self.vk.len(),
            &self.meta,
            &self.memory,
            self.quotient.sorted_simple.len(),
        )
    }

    /// Generate local compact-VM/native-callback Yul blocks for inline renders.
    fn compact_quotient_blocks(
        &self,
        inputs: &VerifierBuildInputs<'_, '_>,
        trace: bool,
    ) -> QuotientComputationBlocks {
        inputs.compact_quotient_computation_blocks(
            &self.meta,
            &self.data,
            &self.quotient.plan,
            self.quotient.stack_mptr,
            self.quotient.state_slots,
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
        if self.quotient.program.len != self.quotient.build.bytes.len() {
            return Err(format!(
                "quotient program length drifted: model={} build={}",
                self.quotient.program.len,
                self.quotient.build.bytes.len()
            ));
        }
        if self.quotient.build.consts.len() > self.vk.quotient_const_words {
            return Err(format!(
                "quotient const table exceeds VK reservation: consts={} words={}",
                self.quotient.build.consts.len(),
                self.vk.quotient_const_words
            ));
        }
        let quotient_program_words = layout::vk_payload::PackedProgramCodec::word_len_for_bytes(
            self.quotient.build.bytes.len(),
        );
        if quotient_program_words > self.vk.quotient_program_words {
            return Err(format!(
                "quotient bytecode exceeds VK reservation: program_words={quotient_program_words} reserved={}",
                self.vk.quotient_program_words
            ));
        }
        // The VK payload embeds the const table and packed bytecode compiled
        // inside `generate_vk`, but the interpreter is rendered from this
        // independently recompiled `self.quotient.build`. Length checks alone
        // let a nondeterministic/order-dependent compile ship a pinned VK whose
        // bytecode disagrees with the rendered VM. Compare the embedded words
        // against the plan build word-for-word so any divergence fails codegen.
        if let Some(const_offset) = self.vk.quotient_const_offset_words {
            let build_consts = &self.quotient.build.consts;
            let embedded = &self.vk.constants[const_offset..const_offset + build_consts.len()];
            if embedded.iter().map(|(_, value)| value).ne(build_consts.iter()) {
                return Err(
                    "quotient const table embedded in the VK payload does not match the \
                     plan-rebuilt const table"
                        .to_string(),
                );
            }
        }
        if let Some(program_offset) = self.vk.quotient_program_offset_words {
            let build_words =
                layout::vk_payload::PackedProgramCodec::encode_words(&self.quotient.build.bytes);
            let embedded = &self.vk.constants[program_offset..program_offset + build_words.len()];
            if embedded.iter().map(|(_, value)| value).ne(build_words.iter()) {
                return Err(
                    "quotient program bytecode embedded in the VK payload does not match the \
                     plan-rebuilt bytecode"
                        .to_string(),
                );
            }
        }
        if self.quotient.program.stack_mptr != self.quotient.stack_mptr {
            return Err(format!(
                "quotient stack pointer drifted: model={:#x} planned={:#x}",
                self.quotient.program.stack_mptr, self.quotient.stack_mptr
            ));
        }
        if self.quotient.program.eval_numer_mptr != self.quotient.state_slots.eval_numer_mptr {
            return Err(format!(
                "quotient state pointer drifted: model={:#x} planned={:#x}",
                self.quotient.program.eval_numer_mptr, self.quotient.state_slots.eval_numer_mptr
            ));
        }
        // Bounds-check every address the emitted bytecode loads from against
        // the windows this layout actually populates before the VM runs.
        // Certification cannot do this: it compares the bytecode against the
        // expression tree, so a pointer that is wrong in both agrees with
        // itself.
        vm::validate_quotient_mem_ptrs(&self.quotient.build.bytes, &self.quotient_read_model())
            .map_err(|err| format!("quotient memory pointer validation failed: {err}"))?;
        // Prove the emitted bytecode still evaluates the identities it was
        // lowered from, before it can be pinned into a verifying key.
        certify::certify_quotient_program(&self.quotient.plan, &self.quotient.build, &self.vk)
            .map_err(|err| format!("quotient program certification failed: {err}"))?;
        Ok(())
    }

    /// Addresses the compact quotient VM is allowed to load from.
    ///
    /// These are exactly the ranges the verifier has populated by the time the
    /// VM runs, and they are the same ranges
    /// `Halo2QuotientEvaluator::validate_layout` requires the external frame to
    /// contain -- a read outside them is either uninitialized memory in the
    /// split path or live verifier state in the inline path.
    pub(crate) fn quotient_read_model(&self) -> vm::QuotientReadModel {
        vm::QuotientReadModel {
            windows: quotient_read_windows(
                &self.meta,
                &self.data,
                &self.vk,
                self.vk_mptr,
                &self.memory,
            ),
            token_bases: vec![
                (vm::Q_MEM_L0, self.memory.l_0_mptr.value().as_usize()),
                (vm::Q_MEM_L_LAST, self.memory.l_last_mptr.value().as_usize()),
                (
                    vm::Q_MEM_L_BLIND,
                    self.memory.l_blind_mptr.value().as_usize(),
                ),
                (vm::Q_MEM_BETA, self.memory.beta_mptr.value().as_usize()),
                (vm::Q_MEM_GAMMA, self.memory.gamma_mptr.value().as_usize()),
                (vm::Q_MEM_X, self.memory.x_mptr.value().as_usize()),
                (vm::Q_MEM_THETA, self.memory.theta_mptr.value().as_usize()),
                (
                    vm::Q_MEM_TRASH_CHALLENGE,
                    self.memory.trash_challenge_mptr.value().as_usize(),
                ),
                (
                    vm::Q_MEM_INSTANCE_EVAL,
                    self.memory.instance_eval_mptr.value().as_usize(),
                ),
            ],
        }
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

/// The memory windows the compact quotient VM is allowed to load from,
/// shared by the build-time pointer validator
/// ([`LoweringPlan::quotient_read_model`]) and the runtime operand clamps
/// rendered into the interpreter (P12/L-6,
/// docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md). One source of truth so the
/// two layers cannot drift.
pub(crate) fn quotient_read_windows(
    meta: &ConstraintSystemMeta,
    data: &Data,
    vk: &Halo2VerifyingKey,
    vk_mptr: Ptr,
    memory: &VerifierMemoryLayout,
) -> Vec<vm::QuotientReadWindow> {
    let theta = data.theta_mptr.value().as_usize();
    let instance_eval = memory.instance_eval_mptr.value().as_usize();
    vec![
        vm::QuotientReadWindow {
            name: "vk_payload",
            start: vk_mptr.value().as_usize(),
            len: vk.len(),
        },
        vm::QuotientReadWindow {
            name: "user_challenges",
            start: data.challenge_mptr.value().as_usize(),
            len: meta.num_user_challenges.iter().sum::<usize>() * layout::memory::WORD_BYTES,
        },
        vm::QuotientReadWindow {
            name: "challenge_and_common_slots",
            // Ends one word past `instance_eval`, matching the frame
            // window in `Halo2QuotientEvaluator::validate_layout`.
            // `quotient_eval` sits immediately above and is a write
            // target, not a VM input.
            start: theta,
            len: (instance_eval + layout::memory::WORD_BYTES).saturating_sub(theta),
        },
        vm::QuotientReadWindow {
            name: "decoded_proof_evals",
            start: memory.reversed_evals_mptr.value().as_usize(),
            len: meta.num_evals * layout::memory::WORD_BYTES,
        },
    ]
}

/// The coarse `[lo, hi]` bound over every non-empty read window, rendered
/// into the interpreter's operand clamps. `hi` is the last legally loadable
/// word address (inclusive). Build-time validation still enforces exact
/// per-window membership; the runtime clamp is defence in depth for a VM
/// whose program bytes are trusted only through the VK codehash pin.
pub(crate) fn quotient_operand_bounds(
    meta: &ConstraintSystemMeta,
    data: &Data,
    vk: &Halo2VerifyingKey,
    vk_mptr: Ptr,
    memory: &VerifierMemoryLayout,
) -> (usize, usize) {
    let windows = quotient_read_windows(meta, data, vk, vk_mptr, memory);
    let lo = windows
        .iter()
        .filter(|w| w.len > 0)
        .map(|w| w.start)
        .min()
        .expect("at least one non-empty quotient read window");
    let hi = windows
        .iter()
        .filter(|w| w.len > 0)
        .map(|w| w.start + w.len - layout::memory::WORD_BYTES)
        .max()
        .expect("at least one non-empty quotient read window");
    (lo, hi)
}
