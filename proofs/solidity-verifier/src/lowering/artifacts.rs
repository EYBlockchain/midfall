// SPDX-License-Identifier: CC0-1.0
//! Verifier artifact construction for a concrete verifier build.
//!
//! This slice assembles Askama models for the embedded verifier, split verifier
//! plus VK payload, and optional external quotient evaluator after all protocol
//! and layout planning has converged.

use ruint::aliases::U256;
use sha3::{Digest, Keccak256};

use crate::lowering::{
    encoding::Ptr,
    kzg, layout,
    layout::memory::{G1_BYTES, WORD_BYTES},
    plan::LoweringPlan,
    quotient_numerator::vm::{fr_delta_literal, LIMB7_YUL_COEFFS, WIDE_LIMB7_YUL_COEFFS},
    render::{Halo2QuotientEvaluator, Halo2Verifier, UserPhase, VerifierCodegenLayout},
    VerifierBuildInputs,
};

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Build the Askama model for the standalone quotient evaluator contract
    /// from an already-converged lowering plan.
    pub(crate) fn generate_quotient_evaluator_from_plan(
        &self,
        plan: &LoweringPlan,
        trace: bool,
    ) -> Halo2QuotientEvaluator {
        let quotient_rendering = plan.quotient_evaluator_rendering(self, trace);
        let quotient_helper_flags = quotient_rendering.blocks.helper_flags();

        let quotient_evaluator = Halo2QuotientEvaluator {
            template_constants: Default::default(),
            trace,
            quotient_pow5_helper: quotient_helper_flags.pow5,
            quotient_limb7_helper: quotient_helper_flags.limb7,
            quotient_wide_limb7_helper: quotient_helper_flags.wide_limb7,
            limb7_yul_coeffs: LIMB7_YUL_COEFFS,
            wide_limb7_yul_coeffs: WIDE_LIMB7_YUL_COEFFS,
            fr_delta: fr_delta_literal(),
            memory: plan.memory.clone(),
            vk_mptr: plan.vk_mptr,
            vk_len: plan.vk.len(),
            challenge_mptr: plan.data.challenge_mptr,
            num_user_challenges: plan.meta.num_user_challenges.iter().sum(),
            theta_mptr: plan.data.theta_mptr,
            reversed_evals_mptr: plan.data.reversed_evals_mptr,
            num_evals: plan.meta.num_evals,
            quotient_external: quotient_rendering.external,
            quotient_inline_computations: quotient_rendering.blocks.inline_computations,
            quotient_eval_numer_computations: quotient_rendering.blocks.eval_numer_computations,
            quotient_post_vm_computations: quotient_rendering.blocks.post_vm_computations,
            quotient_native_permutation_computation: quotient_rendering
                .blocks
                .native_permutation_computation,
            quotient_native_lookup_computation: quotient_rendering.blocks.native_lookup_computation,
            quotient_native_identity_computations: quotient_rendering
                .blocks
                .native_identity_computations,
            quotient_program: Some(quotient_rendering.program),
            simple_selector_cols: plan.quotient.sorted_simple.clone(),
            quotient_identity_trace_base: layout::trace::QUOTIENT_IDENTITY_BASE,
        };
        quotient_evaluator
            .validate_layout()
            .unwrap_or_else(|err| panic!("invalid generated quotient evaluator layout: {err}"));
        quotient_evaluator
    }

    /// Build the Askama model for the main Solidity verifier contract from an
    /// already-converged lowering plan.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn generate_verifier_from_plan(
        &self,
        plan: &LoweringPlan,
        separate: bool,
        trace: bool,
        gas_checkpoints: bool,
        external_quotient: bool,
        expected_quotient: Option<(usize, U256)>,
        provenance: Option<[u8; 32]>,
    ) -> Halo2Verifier {
        assert!(
            expected_quotient.is_none() || external_quotient,
            "quotient pinning requires an external quotient evaluator"
        );
        assert!(
            !external_quotient || expected_quotient.is_some(),
            "external quotient evaluator render requires a generated runtime length/codehash; \
             render the quotient evaluator first and use the pinned quotient render API"
        );
        let meta = &plan.meta;
        let data = &plan.data;
        let proof_layout = &plan.proof_layout;
        let proof_cptr = Ptr::calldata(proof_layout.proof_cptr);
        let memory = plan.memory.clone();
        let vk_mptr = plan.vk_mptr;
        let sorted_simple = &plan.quotient.sorted_simple;

        let selector_acc_mptr = plan.memory.selector_acc_mptr;
        let expected_vk_codehash = separate.then(|| {
            let digest: [u8; 32] = Keccak256::digest(plan.vk.runtime_bytes()).into();
            U256::from_be_bytes(digest)
        });
        let vk_len = plan.vk.len();
        // BUILD_ID (P10/L-8): one on-chain constant that identifies the build.
        // Preimage: domain tag, length-prefixed feature profile (from
        // build.rs), vk_digest, expected VK codehash (zero when embedded),
        // SRS fingerprint, and the optional deployment provenance tag.
        // Deployment records must publish these components so third parties
        // can recompute the id; see
        // docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md.
        let build_id = {
            let vk_digest = plan
                .vk
                .constants
                .iter()
                .find(|(name, _)| *name == "vk_digest")
                .expect("VK header always carries vk_digest")
                .1;
            let features = env!("SOLIDITY_VERIFIER_FEATURES");
            let mut hasher = Keccak256::new();
            hasher.update(b"halo2-solidity-verifier-build-v1");
            hasher.update((features.len() as u64).to_be_bytes());
            hasher.update(features.as_bytes());
            hasher.update(vk_digest.to_be_bytes::<32>());
            hasher.update(expected_vk_codehash.unwrap_or_default().to_be_bytes::<32>());
            hasher.update(self.srs_fingerprint());
            match provenance {
                Some(tag) => {
                    hasher.update([1u8]);
                    hasher.update(tag);
                }
                None => hasher.update([0u8]),
            }
            let digest: [u8; 32] = hasher.finalize().into();
            U256::from_be_bytes(digest)
        };
        let (expected_quotient_len, expected_quotient_codehash) = expected_quotient
            .map(|(len, codehash)| (Some(len), Some(codehash)))
            .unwrap_or((None, None));
        let quotient_rendering = plan.quotient_rendering(self, trace, external_quotient);
        let quotient_helper_flags = quotient_rendering.helper_flags();
        let (quotient_external, quotient_blocks, quotient_program) =
            quotient_rendering.into_template_parts();

        let pcs_computations = kzg::computations(
            &plan.meta,
            &plan.data,
            &plan.memory,
            cfg!(feature = "truncated-challenges"),
            trace,
        );

        // Per-user-phase breakdown (advices + user challenges).
        let user_phases: Vec<UserPhase> = meta
            .num_user_advices
            .iter()
            .zip(meta.num_user_challenges.iter())
            .enumerate()
            .map(|(idx, (_, &n_c))| UserPhase {
                advice_bytes: proof_layout.advice_phases[idx].byte_len,
                num_challenges: n_c,
                challenge_offset: meta.num_user_challenges.iter().take(idx).sum(),
            })
            .collect();
        let num_user_challenges: usize = meta.num_user_challenges.iter().sum();
        let lookup_h_plus_acc: usize = meta.lookup_chunks.iter().sum::<usize>() + meta.num_lookups;

        // Compute VK / accumulator layout helpers before moving vk into
        // the template struct.
        let fixed_comm_mptr_byte = (vk_mptr + plan.vk.constants.len()).value().as_usize();
        let permutation_comm_mptr_byte =
            fixed_comm_mptr_byte + plan.vk.fixed_comms.len() * G1_BYTES;
        let g1_base_mptr_byte = (vk_mptr + layout::VkHeaderSlot::G1Base.word()).value().as_usize();

        let mut acc_fixed_bases: Vec<(String, usize, bool)> = self
            .acc_encoding
            .map(|acc_encoding| {
                let fixed_scalar_count = acc_encoding
                    .fixed_scalar_count(self.num_instances)
                    .expect("accumulator encoding validated by GeneratorConfig");
                // A fully-collapsed public accumulator has no fixed-base scalar
                // tail: just (lhs point, lhs scalar=1, rhs point, rhs scalar=1).
                // Older partially-collapsed accumulators still expose the RHS
                // fixed scalars for -G, fixed commitments, and permutation
                // commitments in BTreeMap key order.
                let bases = if fixed_scalar_count == 0 {
                    Vec::new()
                } else {
                    let num_perm_bases = plan.vk.permutation_comms.len();
                    let num_fixed_bases = fixed_scalar_count
                        .checked_sub(1 + num_perm_bases)
                        .expect("accumulator fixed scalar count is smaller than -G + permutations");
                    // Each generated base below is `fixed_comm_mptr + i * 0x80`,
                    // so more bases than the VK has fixed commitments would
                    // point past the region into the permutation commitments
                    // and then the rest of the VK payload. SolidityGenerator::
                    // try_new rejects this shape with a typed error; fail
                    // closed here too, since this is where the out-of-region
                    // pointers would actually be emitted.
                    assert!(
                        num_fixed_bases <= plan.vk.fixed_comms.len(),
                        "accumulator fixed-base count {num_fixed_bases} exceeds the VK \
                         fixed-commitment region ({} commitments)",
                        plan.vk.fixed_comms.len()
                    );

                    std::iter::once(("-G".to_string(), g1_base_mptr_byte, true))
                        .chain((0..num_fixed_bases).map(|i| {
                            (
                                format!("self_vk_fixed_com_{i}"),
                                fixed_comm_mptr_byte + i * G1_BYTES,
                                false,
                            )
                        }))
                        .chain((0..num_perm_bases).map(|i| {
                            (
                                format!("self_vk_perm_com_{i}"),
                                permutation_comm_mptr_byte + i * G1_BYTES,
                                false,
                            )
                        }))
                        .collect::<Vec<_>>()
                };
                // Holds by construction of `bases` above; kept as a cheap
                // guard on the one-to-one correspondence with the scalars the
                // generated verifier reads from calldata.
                assert_eq!(
                    bases.len(),
                    fixed_scalar_count,
                    "accumulator fixed-base scalar tail must match generated bases"
                );
                bases
            })
            .unwrap_or_default();
        acc_fixed_bases.sort_by(|a, b| a.0.cmp(&b.0));
        let acc_fixed_bases: Vec<(usize, bool)> =
            acc_fixed_bases.into_iter().map(|(_, mptr, negate)| (mptr, negate)).collect();
        let (
            expected_has_accumulator,
            expected_acc_offset,
            expected_num_acc_limbs,
            expected_num_acc_limb_bits,
            expected_acc_has_carried_scalars,
        ) = self
            .acc_encoding
            .map(|acc_encoding| {
                (
                    true,
                    acc_encoding.offset,
                    acc_encoding.num_limbs,
                    acc_encoding.num_limb_bits,
                    acc_encoding.has_carried_scalars(),
                )
            })
            .unwrap_or((false, 0, 0, 0, false));

        let verifier = Halo2Verifier {
            template_constants: Default::default(),
            trace,
            gas_checkpoints,
            quotient_pow5_helper: quotient_helper_flags.pow5,
            quotient_limb7_helper: quotient_helper_flags.limb7,
            quotient_wide_limb7_helper: quotient_helper_flags.wide_limb7,
            constructor_g1msm_smoke_input_bytes: plan.memory.constructor_g1msm_smoke_input_bytes,
            constructor_g1msm_smoke_gas: {
                let smoke_bytes = plan.memory.constructor_g1msm_smoke_input_bytes;
                assert_eq!(
                    smoke_bytes % layout::G1_MSM_PAIR_BYTES,
                    0,
                    "constructor G1MSM smoke input is not a whole number of pairs"
                );
                layout::gas::g1msm_gas(smoke_bytes / layout::G1_MSM_PAIR_BYTES)
            },
            acc_rhs_msm_gas: if expected_has_accumulator {
                // Worst case: carried RHS point plus every fixed-base tail
                // scalar nonzero. Zero scalars are omitted at runtime, which
                // only shrinks the MSM below this bound.
                layout::gas::g1msm_gas(1 + acc_fixed_bases.len())
            } else {
                0
            },
            limb7_yul_coeffs: LIMB7_YUL_COEFFS,
            wide_limb7_yul_coeffs: WIDE_LIMB7_YUL_COEFFS,
            fr_delta: fr_delta_literal(),
            embedded_vk: (!separate).then(|| plan.vk.clone()),
            expected_vk_codehash,
            build_id,
            vk_len,
            num_instances: self.num_instances,
            k: self.vk.get_domain().k() as usize,
            codegen_layout: VerifierCodegenLayout {
                proof: plan.proof_layout.clone(),
            },
            memory,
            vk_header: Default::default(),
            vk_mptr,
            num_neg_lagranges: meta.rotation_last.unsigned_abs() as usize,
            user_phases,
            num_user_challenges,
            num_lookups: meta.num_lookups,
            num_permutation_zs: meta.num_permutation_zs,
            lookup_h_plus_acc,
            num_trashcans: meta.num_trashcans,
            num_quotients: meta.num_quotients,
            num_evals: meta.num_evals,
            comms_mptr_base: data.comms_mptr_base,
            reversed_evals_mptr: data.reversed_evals_mptr,
            selector_acc_mptr,
            quotient_external,
            expected_quotient_len,
            expected_quotient_codehash,
            proof_cptr,
            abi_selector_bytes: layout::abi::SELECTOR_BYTES,
            abi_proof_head_offset: layout::abi::VERIFY_PROOF_PROOF_HEAD_OFFSET,
            abi_instances_head_cptr: layout::abi::SELECTOR_BYTES + WORD_BYTES,
            num_instance_cptr: proof_layout.proof_end,
            instance_cptr: proof_layout.proof_end + WORD_BYTES,
            quotient_comm_cptr: Ptr::calldata(proof_layout.quotient_comm_cptr),
            proof_len: proof_layout.proof_len,
            challenge_mptr: data.challenge_mptr,
            theta_mptr: data.theta_mptr,
            quotient_inline_computations: quotient_blocks.inline_computations,
            quotient_eval_numer_computations: quotient_blocks.eval_numer_computations,
            quotient_post_vm_computations: quotient_blocks.post_vm_computations,
            quotient_native_permutation_computation: quotient_blocks.native_permutation_computation,
            quotient_native_lookup_computation: quotient_blocks.native_lookup_computation,
            quotient_native_identity_computations: quotient_blocks.native_identity_computations,
            quotient_program,
            pcs_computations,
            simple_selector_cols: sorted_simple.clone(),
            proof_commit_trace_base: layout::trace::PROOF_COMMIT_BASE,
            proof_eval_trace_base: layout::trace::PROOF_EVAL_BASE,
            quotient_identity_trace_base: layout::trace::QUOTIENT_IDENTITY_BASE,
            selector_trace_base: layout::trace::SELECTOR_FOLD_BASE,
            fixed_comm_mptr: fixed_comm_mptr_byte,
            truncated_challenges: cfg!(feature = "truncated-challenges"),
            expected_has_accumulator,
            expected_has_accumulator_word: expected_has_accumulator as usize,
            expected_acc_offset,
            expected_num_acc_limbs,
            expected_num_acc_limb_bits,
            expected_acc_has_carried_scalars,
            acc_fixed_bases,
        };
        verifier
            .validate_layout()
            .unwrap_or_else(|err| panic!("invalid generated verifier layout: {err}"));
        verifier
    }
}
