// SPDX-License-Identifier: CC0-1.0
//! Verifying-key payload generation for a concrete verifier build.
//!
//! This module serializes the concrete Halo2 verifying key, quotient constants,
//! compact VM program, selector tables, and payload section map consumed by the
//! generated verifier contracts.

use ff::Field;
use group::{prime::PrimeCurveAffine, Curve};
use itertools::chain;
use midnight_curves::{Fq, G1Affine, G1Projective, G2Affine};
use ruint::aliases::U256;

use crate::lowering::{
    abi::{ProofCalldataLayout, TranscriptBufferLayout},
    encoding::{fe_to_u256, g1_to_u256s, g2_to_u256s, ConstraintSystemMeta, Data, Ptr},
    kzg, layout,
    layout::{
        memory::{
            VerifierMemoryLayout, VerifierMemoryLayoutConfig, VkConstructorMemoryLayout, G1_BYTES,
            WORD_BYTES,
        },
        vk_payload::{PackedProgramCodec, PayloadSectionKind, VkPayloadLayout},
    },
    render::{Halo2VerifyingKey, VK_RUNTIME_PREFIX_LEN},
    VerifierBuildInputs,
};

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Generate the VK payload before compact quotient constants/program data.
    fn generate_base_vk(&self) -> Halo2VerifyingKey {
        let constants: Vec<(&'static str, U256)>;
        {
            use layout::VkHeaderSlot as Slot;

            let domain = self.vk.get_domain();
            // BLS12-381 scalar Fq is 32 bytes wide (256 bits) so the same
            // little-endian-to-u256 conversion that worked for BN254 Fr
            // also works here: the verifier reads each scalar from
            // calldata into a single 32-byte word.
            // `plonk/verifier.rs` hashes the verifying key into the
            // transcript before reading prover data. The Solidity template
            // absorbs this `transcript_repr` digest as its first transcript
            // word to preserve the Rust verifier's Fiat-Shamir prefix.
            let vk_digest = fe_to_u256::<Fq>(&self.vk.transcript_repr());
            let num_instances = U256::from(self.num_instances);
            let k = U256::from(domain.k());
            let n_inv = fe_to_u256::<Fq>(&Fq::from(1u64 << domain.k()).invert().unwrap());
            let omega = fe_to_u256::<Fq>(&domain.get_omega());
            let omega_inv = fe_to_u256::<Fq>(&domain.get_omega_inv());
            let omega_inv_to_l = {
                let l = self.meta.rotation_last.unsigned_abs() as u64;
                fe_to_u256::<Fq>(&domain.get_omega_inv().pow_vartime([l]))
            };
            let has_accumulator = U256::from(self.acc_encoding.is_some() as usize);
            let acc_offset = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.offset))
                .unwrap_or_default();
            let num_acc_limbs = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.num_limbs))
                .unwrap_or_default();
            let num_acc_limb_bits = self
                .acc_encoding
                .map(|acc_encoding| U256::from(acc_encoding.num_limb_bits))
                .unwrap_or_default();
            // EIP-2537 padded encodings come from `g1_to_u256s` / `g2_to_u256s`
            // (4 / 8 u256 words respectively). We cannot read `params.g[0]`
            // directly (the field is crate-private in midnight-proofs), so
            // we use the canonical BLS12-381 generator.
            let g1_pt: G1Affine = G1Affine::generator();
            let g2_pt: G2Affine = self.params.g2().to_affine();
            let neg_s_g2_pt: G2Affine = (-self.params.s_g2()).to_affine();
            let g1 = g1_to_u256s(g1_pt);
            let g2 = g2_to_u256s(g2_pt);
            let neg_s_g2 = g2_to_u256s(neg_s_g2_pt);

            let mut header = layout::VkHeaderLayout::builder();
            header.scalar(Slot::VkDigest, "vk_digest", vk_digest).unwrap();
            header.scalar(Slot::NumInstances, "num_instances", num_instances).unwrap();
            header.scalar(Slot::K, "k", k).unwrap();
            header.scalar(Slot::NInv, "n_inv", n_inv).unwrap();
            header.scalar(Slot::Omega, "omega", omega).unwrap();
            header.scalar(Slot::OmegaInv, "omega_inv", omega_inv).unwrap();
            header.scalar(Slot::OmegaInvToL, "omega_inv_to_l", omega_inv_to_l).unwrap();
            header.scalar(Slot::HasAccumulator, "has_accumulator", has_accumulator).unwrap();
            header.scalar(Slot::AccOffset, "acc_offset", acc_offset).unwrap();
            header.scalar(Slot::NumAccLimbs, "num_acc_limbs", num_acc_limbs).unwrap();
            header
                .scalar(Slot::NumAccLimbBits, "num_acc_limb_bits", num_acc_limb_bits)
                .unwrap();
            header
                .g1(
                    Slot::G1Base,
                    ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"],
                    g1,
                )
                .unwrap();
            header
                .g2(
                    Slot::G2Base,
                    [
                        "g2_x_c0_hi",
                        "g2_x_c0_lo",
                        "g2_x_c1_hi",
                        "g2_x_c1_lo",
                        "g2_y_c0_hi",
                        "g2_y_c0_lo",
                        "g2_y_c1_hi",
                        "g2_y_c1_lo",
                    ],
                    g2,
                )
                .unwrap();
            header
                .g2(
                    Slot::NegSG2Base,
                    [
                        "neg_s_g2_x_c0_hi",
                        "neg_s_g2_x_c0_lo",
                        "neg_s_g2_x_c1_hi",
                        "neg_s_g2_x_c1_lo",
                        "neg_s_g2_y_c0_hi",
                        "neg_s_g2_y_c0_lo",
                        "neg_s_g2_y_c1_hi",
                        "neg_s_g2_y_c1_lo",
                    ],
                    neg_s_g2,
                )
                .unwrap();
            constants =
                header.finish().unwrap_or_else(|err| panic!("invalid VK header layout: {err}"));
        }

        // Convert each commitment from G1Projective to G1Affine before
        // EIP-2537 packing.
        let to_affine = |g: &G1Projective| -> G1Affine { g.to_affine() };
        let fixed_comms: Vec<_> = chain![self.vk.fixed_commitments()]
            .map(to_affine)
            .map(g1_to_u256s)
            .map(|[a, b, c, d]| (a, b, c, d))
            .collect();
        let permutation_comms: Vec<_> = chain![self.vk.permutation().commitments()]
            .map(to_affine)
            .map(g1_to_u256s)
            .map(|[a, b, c, d]| (a, b, c, d))
            .collect();
        let constructor_payload_len =
            constants.len() * WORD_BYTES + (fixed_comms.len() + permutation_comms.len()) * G1_BYTES;
        let constructor_memory =
            VkConstructorMemoryLayout::new(constructor_payload_len + VK_RUNTIME_PREFIX_LEN);
        constructor_memory
            .validate()
            .unwrap_or_else(|err| panic!("invalid VK constructor memory layout: {err}"));
        Halo2VerifyingKey {
            constructor_payload_mptr: constructor_memory.payload_mptr,
            constants,
            fixed_comms,
            permutation_comms,
            quotient_const_offset_words: None,
            quotient_const_words: 0,
            quotient_program_offset_words: None,
            quotient_program_words: 0,
        }
    }

    /// Generate the final VK payload, including compact quotient VM data.
    ///
    /// The quotient program depends on memory addresses, and memory addresses
    /// depend on the final VK length. This method reserves zero-filled quotient
    /// sections first, rebuilds against the final layout, and then fills the
    /// sections. Assertions catch any non-convergent program size change.
    pub(crate) fn generate_vk(&self) -> Halo2VerifyingKey {
        let mut vk = self.generate_base_vk();

        let header_words = vk.constants.len();
        let mut quotient_const_words = 0usize;
        let mut quotient_program_words = 0usize;
        let mut quotient_program_build = None;

        for _ in 0..8 {
            vk.constants.truncate(header_words);
            vk.constants
                .extend((0..quotient_const_words).map(|_| ("quotient_const", U256::ZERO)));
            vk.constants
                .extend((0..quotient_program_words).map(|_| ("quotient_program", U256::ZERO)));
            vk.quotient_const_offset_words = None;
            vk.quotient_const_words = 0;
            vk.quotient_program_offset_words = None;
            vk.quotient_program_words = 0;

            let (_, meta, data, _) = self.meta_data_for_stable_static_layout(&vk);
            let (candidate, _) = self.compact_quotient_program_for(&meta, &data);
            let candidate_const_words = candidate.consts.len();
            let candidate_program_words =
                PackedProgramCodec::word_len_for_bytes(candidate.bytes.len());

            if candidate_const_words <= quotient_const_words
                && candidate_program_words <= quotient_program_words
            {
                quotient_program_build = Some(candidate);
                break;
            }

            quotient_const_words = quotient_const_words.max(candidate_const_words);
            quotient_program_words = quotient_program_words.max(candidate_program_words);
        }

        let quotient_program_build = quotient_program_build.unwrap_or_else(|| {
            panic!(
                "quotient VK payload reservation did not converge after 8 iterations: const_words={quotient_const_words}, program_words={quotient_program_words}"
            )
        });
        let payload_layout = VkPayloadLayout::for_vk(
            header_words,
            quotient_const_words,
            quotient_program_words,
            vk.fixed_comms.len(),
            vk.permutation_comms.len(),
        )
        .unwrap_or_else(|err| panic!("invalid VK payload layout reservation: {err}"));
        let quotient_const_offset_words = payload_layout
            .word_offset(PayloadSectionKind::QuotientConstants)
            .expect("quotient constants section");
        let quotient_program_offset_words = payload_layout
            .word_offset(PayloadSectionKind::QuotientProgram)
            .expect("quotient program section");
        assert_eq!(
            payload_layout
                .word_len(PayloadSectionKind::QuotientConstants)
                .expect("quotient constants section length"),
            quotient_const_words
        );
        assert_eq!(
            payload_layout
                .word_len(PayloadSectionKind::QuotientProgram)
                .expect("quotient program section length"),
            quotient_program_words
        );
        assert_eq!(
            payload_layout.total_bytes(),
            vk.len(),
            "typed VK payload layout must preserve the emitted byte length"
        );

        let quotient_program_chunks =
            PackedProgramCodec::encode_words(&quotient_program_build.bytes);
        assert!(
            quotient_program_build.consts.len() <= quotient_const_words,
            "quotient const table exceeded VK payload reservation"
        );
        assert!(
            quotient_program_chunks.len() <= quotient_program_words,
            "quotient program length exceeded VK payload reservation"
        );

        for (i, value) in quotient_program_build.consts.iter().copied().enumerate() {
            vk.constants[quotient_const_offset_words + i] = ("quotient_const", value);
        }
        for (i, value) in quotient_program_chunks.iter().copied().enumerate() {
            vk.constants[quotient_program_offset_words + i] = ("quotient_program", value);
        }

        vk.quotient_const_offset_words = Some(quotient_const_offset_words);
        vk.quotient_const_words = quotient_const_words;
        vk.quotient_program_offset_words = Some(quotient_program_offset_words);
        vk.quotient_program_words = quotient_program_words;
        vk.validate_payload_layout()
            .unwrap_or_else(|err| panic!("invalid generated VK payload layout: {err}"));
        vk
    }

    /// Build metadata, data handles, and memory layout for a candidate VK base.
    fn meta_data_for_vk(
        &self,
        vk: &Halo2VerifyingKey,
        vk_mptr: Ptr,
    ) -> (ConstraintSystemMeta, Data, VerifierMemoryLayout) {
        // ------------------------------------------------------------------
        // Phase 3 / outer-fewer-point-sets two-pass `Data` construction.
        //
        // Pass 1: build `Data` against the *raw* meta (no dummy evals).
        //   This gives us the raw query list whose commitment identity
        //   structure feeds `compute_dummy_queries`.
        //
        // Pass 2: bump meta.num_evals by the dummy count (so the
        //   memory layout - REVERSED_EVALS_MPTR buffer + downstream
        //   comms_mptr_base - grows to fit the dummies), rebuild Data,
        //   and populate the dummy eval Words.
        //
        // When the `outer-fewer-point-sets` Cargo feature is OFF, the dummy
        // count is forced to zero; pass 2 collapses to "rebuild Data
        // against unchanged meta", and the result is byte-identical
        // to the pre-Phase-3 single-pass path.
        // ------------------------------------------------------------------
        let raw_memory = self.memory_layout_for(
            self.meta,
            vk,
            vk_mptr,
            VerifierMemoryLayoutConfig::default(),
        );
        let raw_data = Data::new(self.meta, vk, &raw_memory);
        let mut meta = (*self.meta).clone();
        let n_dummy = if cfg!(feature = "outer-fewer-point-sets") {
            kzg::num_dummy_queries(&meta, &raw_data)
        } else {
            0
        };
        let main_evals = meta.num_evals;
        meta.set_num_dummy_evals(n_dummy);
        let memory =
            self.memory_layout_for(&meta, vk, vk_mptr, VerifierMemoryLayoutConfig::default());
        let mut data = Data::new(&meta, vk, &memory);
        if n_dummy > 0 {
            data.set_dummy_eval_words(main_evals, n_dummy);
        }

        meta.set_num_point_sets(kzg::num_point_sets(&meta, &data));
        let memory =
            self.memory_layout_for(&meta, vk, vk_mptr, VerifierMemoryLayoutConfig::default());
        (meta, data, memory)
    }

    /// Find a VK memory base that is stable after proof-shape planning.
    ///
    /// Transcript/PCS low-memory requirements can grow when dummy query
    /// planning discovers extra eval scalars. Iterate until the chosen
    /// `VK_MPTR` matches the requirements computed from the resulting
    /// metadata.
    pub(super) fn meta_data_for_stable_static_layout(
        &self,
        vk: &Halo2VerifyingKey,
    ) -> (Ptr, ConstraintSystemMeta, Data, VerifierMemoryLayout) {
        let mut vk_mptr = Ptr::memory(self.static_working_memory_size_for_meta(self.meta));

        for _ in 0..3 {
            let (meta, data, memory) = self.meta_data_for_vk(vk, vk_mptr);
            let planned_mptr = self.static_working_memory_size_for_meta(&meta);
            if planned_mptr == vk_mptr.value().as_usize() {
                return (vk_mptr, meta, data, memory);
            }
            vk_mptr = Ptr::memory(planned_mptr);
        }

        panic!("static verifier memory layout did not converge after proof-shape planning");
    }

    /// Build a verifier memory layout after filling derived config fields.
    pub(super) fn memory_layout_for(
        &self,
        meta: &ConstraintSystemMeta,
        vk: &Halo2VerifyingKey,
        vk_mptr: Ptr,
        mut config: VerifierMemoryLayoutConfig,
    ) -> VerifierMemoryLayout {
        config.transcript_words =
            Self::transcript_buffer_layout_for_meta(meta, self.num_instances).words;
        config.num_instances = self.num_instances;
        VerifierMemoryLayout::new(meta, vk, vk_mptr, config)
    }
    /// Low-memory working-set size that must stay below `VK_MPTR`.
    fn static_working_memory_size_for_meta(&self, meta: &ConstraintSystemMeta) -> usize {
        let pcs_computation = kzg::static_working_memory_size();
        let transcript_words =
            Self::transcript_buffer_layout_for_meta(meta, self.num_instances).words;
        let transcript_end = layout::TRANSCRIPT_BUFFER_START + transcript_words * WORD_BYTES;
        let pcs_end = layout::PCS_PAIRING_SCRATCH_START + pcs_computation * WORD_BYTES;
        let final_pairing_end =
            layout::FINAL_PAIRING_SCRATCH_START + layout::PAIRING_STATIC_WORKING_WORDS * WORD_BYTES;
        let verifier_return_end = layout::VERIFIER_RETURN_BUFFER_START + WORD_BYTES;
        let quotient_return_end =
            layout::QUOTIENT_RETURN_BUFFER_START + (2 + meta.num_simple_selectors) * WORD_BYTES;

        itertools::max([
            // Transcript buffer (streaming Keccak256). The buffer must
            // fit *below* `VK_MPTR` because every `mload(VK_MPTR + ...)`
            // assumes the VK contract bytes copied via `extcodecopy`
            // remain intact, and the buffer would otherwise overwrite
            // them as it grows past the start of the VK area.
            transcript_end,
            // PCS computation scratch
            pcs_end,
            // Pairing: two-pair input frame plus output word, rooted above
            // Solidity's reserved memory prefix.
            final_pairing_end,
            // Low-memory return frames. The quotient evaluator's output grows
            // with the number of simple selector buckets.
            verifier_return_end,
            quotient_return_end,
        ])
        .unwrap()
    }

    #[cfg(test)]
    /// Test helper exposing the transcript buffer word bound.
    pub(crate) fn transcript_buffer_words_bound(
        meta: &ConstraintSystemMeta,
        num_instances: usize,
    ) -> usize {
        Self::transcript_buffer_layout_for_meta(meta, num_instances).words
    }

    /// Compute the transcript buffer layout for a metadata snapshot.
    pub(super) fn transcript_buffer_layout_for_meta(
        meta: &ConstraintSystemMeta,
        num_instances: usize,
    ) -> TranscriptBufferLayout {
        // The Step 6 transcript model is a streaming Keccak256 buffer rooted
        // at TRANSCRIPT_BUFFER_START. The buffer monotonically grows between
        // two challenge squeezes and is reset to one seed word after each
        // squeeze. This function returns the number of words needed above
        // that root; the caller adds the 0x80 base when choosing VK_MPTR. For
        // midnight-proofs verifiers the dominating run is whichever of the
        // following is largest:
        //   (a) initial absorbs (vk_digest + committed_pi + num_instances
        //       + all instance scalars + all phase-1 advices) before the
        //       first user-phase challenge squeeze (`theta`), or
        //   (b) the evaluation block (all `num_evals` scalars) absorbed
        //       after the `y` squeeze and before the next squeeze.
        //
        // We compute a per-run conservative upper bound for each and
        // take the max, then add the 32-byte post-squeeze seed cushion.
        //
        // Per-absorb costs in the patched (uncompressed-G1) emitter:
        //   - word                         = 32 bytes  (`common_word`)
        //   - uncompressed G1              = 128 bytes (`common_uncompressed_g1`)
        //   - squeeze output               = 32 bytes  (post-squeeze seed)
        // The earlier (compressed-G1) emitter used 49 bytes per G1; the
        // 49 used here is wrong now that the verifier hashes the 128-byte
        // EIP-2537 padded form, so we use 128. Mismatching the bound
        // causes the keccak buffer to overrun `VK_MPTR` mid-verify and
        // silently corrupt `K_MPTR`, `OMEGA_MPTR`, etc., producing a
        // multi-billion-gas spin in the Lagrange block.
        let proof_layout = ProofCalldataLayout::from_protocol(
            &meta.protocol,
            0,
            meta.num_evals,
            meta.num_point_sets,
        );
        TranscriptBufferLayout::from_proof_layout(&proof_layout, num_instances)
    }
}
