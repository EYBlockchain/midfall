// SPDX-License-Identifier: CC0-1.0
//! Askama data models for the generated Solidity/Yul templates.
//!
//! The structs in this module are deliberately plain: they carry
//! already-planned calldata, memory, VK, quotient, and PCS facts into the
//! templates. Keeping the planning logic outside Askama makes generated
//! Solidity easier to audit and lets Rust tests validate layouts before
//! rendering.

use std::fmt;

use askama::{Error, Template};
use group::{prime::PrimeCurveAffine, Curve, Group};
use midnight_curves::{G1Affine, G1Projective};
use ruint::aliases::U256;

use crate::lowering::{
    abi::proof::ProofCalldataLayout,
    encoding::Ptr,
    layout,
    layout::{
        memory::{VerifierMemoryLayout, VkConstructorMemoryLayout, G1_BYTES, WORD_BYTES},
        vk_payload::{PayloadSectionKind, VkPayloadLayout},
    },
};

/// G1 point in EIP-2537 padded encoding: (x_hi, x_lo, y_hi, y_lo).
pub(crate) type G1Words = (U256, U256, U256, U256);

#[derive(Clone, Copy, Debug)]
pub(crate) struct TemplateConstants {
    /// EVM word byte width.
    pub(crate) word_bytes: usize,
    /// EIP-2537 padded G1 byte width.
    pub(crate) g1_bytes: usize,
    /// G1MSM input tuple byte width.
    pub(crate) g1_msm_pair_bytes: usize,
    /// G1ADD input byte width.
    pub(crate) g1add_input_bytes: usize,
    /// Pairing input byte width for two pairs.
    pub(crate) pairing_two_pair_bytes: usize,
    /// EIP-2537 precompile constants.
    pub(crate) eip2537: Eip2537TemplateConstants,
    /// Exact EIP-2537/EIP-2565 gas bounds forwarded to precompile calls.
    pub(crate) gas: GasTemplateConstants,
    /// EIP-198 modexp constants.
    pub(crate) modexp: ModexpTemplateConstants,
    /// Public accumulator layout constants.
    pub(crate) accumulator: AccumulatorTemplateConstants,
    /// Compact quotient VM constants.
    pub(crate) quotient_vm: QuotientVmTemplateConstants,
}

/// EIP-2537 precompile addresses rendered into templates.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Eip2537TemplateConstants {
    pub(crate) g1add_address: usize,
    pub(crate) g1msm_address: usize,
    pub(crate) pairing_address: usize,
    pub(crate) smoke_scratch_bytes: usize,
    /// BLS12-381 G1 generator in EIP-2537 padded encoding.
    ///
    /// Used with [`Self::g1_double_generator`] as a known-answer vector for the
    /// constructor smoke test: identity-only probes are satisfied by
    /// implementations that never do any real curve arithmetic.
    pub(crate) g1_generator: G1Words,
    /// Twice the BLS12-381 G1 generator, in EIP-2537 padded encoding.
    pub(crate) g1_double_generator: G1Words,
}

/// Exact precompile gas bounds rendered into templates.
///
/// These are the EIP-2537/EIP-2565 scheduled costs, forwarded verbatim so a
/// failing precompile call burns at most its scheduled cost instead of the
/// full 63/64 of the transaction budget. See [`layout::gas`] for the model
/// and the upward-repricing liveness caveat.
#[derive(Clone, Copy, Debug)]
pub(crate) struct GasTemplateConstants {
    /// EIP-2537 G1ADD flat cost.
    pub(crate) g1add: u64,
    /// EIP-2537 G1MSM cost for a single (point, scalar) pair.
    pub(crate) g1msm_one_pair: u64,
    /// EIP-2537 pairing cost for the verifier's two-pair check.
    pub(crate) pairing_two_pair: u64,
    /// EIP-2565 modexp cost for the 32-byte base/exp/mod frame.
    pub(crate) modexp: u64,
}

/// EIP-198 modexp frame constants rendered into templates.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ModexpTemplateConstants {
    pub(crate) address: usize,
    pub(crate) frame_bytes: usize,
    pub(crate) output_bytes: usize,
    pub(crate) base_len_offset: usize,
    pub(crate) exp_len_offset: usize,
    pub(crate) mod_len_offset: usize,
    pub(crate) base_offset: usize,
    pub(crate) exp_offset: usize,
    pub(crate) mod_offset: usize,
}

/// Public accumulator ABI and pairing-batch constants.
#[derive(Clone, Copy, Debug)]
pub(crate) struct AccumulatorTemplateConstants {
    pub(crate) limbs_per_word: usize,
    pub(crate) pairing_batch_domain_tag_hex: &'static str,
    pub(crate) pairing_batch_vk_digest_offset: usize,
    pub(crate) pairing_batch_rhs_offset: usize,
    pub(crate) pairing_batch_lhs_offset: usize,
    pub(crate) pairing_batch_acc_rhs_offset: usize,
    pub(crate) pairing_batch_acc_lhs_offset: usize,
    pub(crate) pairing_batch_hash_bytes: usize,
}

/// Compact quotient VM opcode constants rendered into Solidity/Yul.
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuotientVmOpcodeTemplateConstants {
    pub(crate) push_const: u8,
    pub(crate) push_mem_literal: u8,
    pub(crate) push_mem_token: u8,
    pub(crate) push_mem_token_offset: u8,
    pub(crate) push_mem_u16: u8,
    pub(crate) add: u8,
    pub(crate) mul: u8,
    pub(crate) neg: u8,
    pub(crate) push_const_u8: u8,
    pub(crate) fold_main: u8,
    pub(crate) fold_selector: u8,
    pub(crate) add_const_u8: u8,
    pub(crate) mul_const_u8: u8,
    pub(crate) add_const: u8,
    pub(crate) mul_const: u8,
    pub(crate) add_mem_u16: u8,
    pub(crate) mul_mem_u16: u8,
    pub(crate) add_mul_mem_mem_const_u8: u8,
    pub(crate) add_mul_const_u8_mem_u16: u8,
    pub(crate) add_mul_mem_mem: u8,
    pub(crate) run_add_mul_mem_mem_const_u8: u8,
    pub(crate) run_add_mul_const_u8_mem_u16: u8,
    pub(crate) affine_sum: u8,
    pub(crate) native_permutation: u8,
    pub(crate) native_lookup: u8,
    pub(crate) native_identity: u8,
    pub(crate) lin7: u8,
    pub(crate) bilin7_row: u8,
    pub(crate) bilin7_pairwise: u8,
    pub(crate) modarith7: u8,
    pub(crate) pow5: u8,
}

/// Compact quotient VM memory-token constants rendered into Solidity/Yul.
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuotientVmMemTokenTemplateConstants {
    pub(crate) l0: u8,
    pub(crate) l_last: u8,
    pub(crate) l_blind: u8,
    pub(crate) beta: u8,
    pub(crate) gamma: u8,
    pub(crate) x: u8,
    pub(crate) theta: u8,
    pub(crate) trash_challenge: u8,
    pub(crate) instance_eval: u8,
}

/// Compact quotient VM table-level constants rendered into templates.
#[derive(Clone, Copy, Debug)]
pub(crate) struct QuotientVmTemplateConstants {
    pub(crate) op: QuotientVmOpcodeTemplateConstants,
    pub(crate) mem: QuotientVmMemTokenTemplateConstants,
    pub(crate) byte_u32_bytes: usize,
    pub(crate) limb_count: usize,
    pub(crate) limb_pairwise_coeffs: usize,
}

/// Convert a G1 point into the tuple form the templates render.
fn g1_words(point: G1Affine) -> G1Words {
    let [x_hi, x_lo, y_hi, y_lo] = crate::lowering::encoding::g1_to_u256s(point);
    (x_hi, x_lo, y_hi, y_lo)
}

impl Default for TemplateConstants {
    /// Build template constants from the Rust-side layout and VM specs.
    fn default() -> Self {
        use crate::lowering::quotient_numerator::vm as q;

        Self {
            word_bytes: layout::WORD_BYTES,
            g1_bytes: layout::G1_BYTES,
            g1_msm_pair_bytes: layout::G1_MSM_PAIR_BYTES,
            g1add_input_bytes: layout::G1ADD_INPUT_BYTES,
            pairing_two_pair_bytes: layout::PAIRING_TWO_PAIR_BYTES,
            eip2537: Eip2537TemplateConstants {
                g1add_address: layout::precompile::G1ADD_ADDRESS,
                g1msm_address: layout::precompile::G1MSM_ADDRESS,
                pairing_address: layout::precompile::PAIRING_ADDRESS,
                smoke_scratch_bytes: layout::PAIRING_TWO_PAIR_BYTES,
                g1_generator: g1_words(G1Affine::generator()),
                g1_double_generator: {
                    let g = G1Projective::generator();
                    g1_words((g + g).to_affine())
                },
            },
            gas: GasTemplateConstants {
                g1add: layout::gas::G1ADD_GAS,
                g1msm_one_pair: layout::gas::g1msm_gas(1),
                pairing_two_pair: layout::gas::pairing_gas(2),
                modexp: layout::gas::modexp_gas_word_frame(),
            },
            modexp: ModexpTemplateConstants {
                address: layout::precompile::MODEXP_ADDRESS,
                frame_bytes: layout::MODEXP_FRAME_BYTES,
                output_bytes: layout::WORD_BYTES,
                base_len_offset: layout::modexp_frame::BASE_LEN_OFFSET,
                exp_len_offset: layout::modexp_frame::EXP_LEN_OFFSET,
                mod_len_offset: layout::modexp_frame::MOD_LEN_OFFSET,
                base_offset: layout::modexp_frame::BASE_OFFSET,
                exp_offset: layout::modexp_frame::EXP_OFFSET,
                mod_offset: layout::modexp_frame::MOD_OFFSET,
            },
            accumulator: AccumulatorTemplateConstants {
                limbs_per_word: layout::accumulator::LIMBS_PER_WORD,
                pairing_batch_domain_tag_hex: layout::accumulator::PAIRING_BATCH_DOMAIN_TAG_HEX,
                pairing_batch_vk_digest_offset: layout::accumulator::PAIRING_BATCH_VK_DIGEST_OFFSET,
                pairing_batch_rhs_offset: layout::accumulator::PAIRING_BATCH_RHS_OFFSET,
                pairing_batch_lhs_offset: layout::accumulator::PAIRING_BATCH_LHS_OFFSET,
                pairing_batch_acc_rhs_offset: layout::accumulator::PAIRING_BATCH_ACC_RHS_OFFSET,
                pairing_batch_acc_lhs_offset: layout::accumulator::PAIRING_BATCH_ACC_LHS_OFFSET,
                pairing_batch_hash_bytes: layout::accumulator::PAIRING_BATCH_HASH_BYTES,
            },
            quotient_vm: QuotientVmTemplateConstants {
                op: QuotientVmOpcodeTemplateConstants {
                    push_const: q::Q_OP_PUSH_CONST,
                    push_mem_literal: q::Q_OP_PUSH_MEM_LITERAL,
                    push_mem_token: q::Q_OP_PUSH_MEM_TOKEN,
                    push_mem_token_offset: q::Q_OP_PUSH_MEM_TOKEN_OFFSET,
                    push_mem_u16: q::Q_OP_PUSH_MEM_U16,
                    add: q::Q_OP_ADD,
                    mul: q::Q_OP_MUL,
                    neg: q::Q_OP_NEG,
                    push_const_u8: q::Q_OP_PUSH_CONST_U8,
                    fold_main: q::Q_OP_FOLD_MAIN,
                    fold_selector: q::Q_OP_FOLD_SELECTOR,
                    add_const_u8: q::Q_OP_ADD_CONST_U8,
                    mul_const_u8: q::Q_OP_MUL_CONST_U8,
                    add_const: q::Q_OP_ADD_CONST,
                    mul_const: q::Q_OP_MUL_CONST,
                    add_mem_u16: q::Q_OP_ADD_MEM_U16,
                    mul_mem_u16: q::Q_OP_MUL_MEM_U16,
                    add_mul_mem_mem_const_u8: q::Q_OP_ADD_MUL_MEM_MEM_CONST_U8,
                    add_mul_const_u8_mem_u16: q::Q_OP_ADD_MUL_CONST_U8_MEM_U16,
                    add_mul_mem_mem: q::Q_OP_ADD_MUL_MEM_MEM,
                    run_add_mul_mem_mem_const_u8: q::Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
                    run_add_mul_const_u8_mem_u16: q::Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
                    affine_sum: q::Q_OP_AFFINE_SUM,
                    native_permutation: q::Q_OP_NATIVE_PERMUTATION,
                    native_lookup: q::Q_OP_NATIVE_LOOKUP,
                    native_identity: q::Q_OP_NATIVE_IDENTITY,
                    lin7: q::Q_OP_LIN7,
                    bilin7_row: q::Q_OP_BILIN7_ROW,
                    bilin7_pairwise: q::Q_OP_BILIN7_PAIRWISE,
                    modarith7: q::Q_OP_MODARITH7,
                    pow5: q::Q_OP_POW5,
                },
                mem: QuotientVmMemTokenTemplateConstants {
                    l0: q::Q_MEM_L0,
                    l_last: q::Q_MEM_L_LAST,
                    l_blind: q::Q_MEM_L_BLIND,
                    beta: q::Q_MEM_BETA,
                    gamma: q::Q_MEM_GAMMA,
                    x: q::Q_MEM_X,
                    theta: q::Q_MEM_THETA,
                    trash_challenge: q::Q_MEM_TRASH_CHALLENGE,
                    instance_eval: q::Q_MEM_INSTANCE_EVAL,
                },
                byte_u32_bytes: q::QUOTIENT_VM_BYTE_U32_BYTES,
                limb_count: q::QUOTIENT_VM_LIMBS,
                limb_pairwise_coeffs: q::QUOTIENT_VM_PAIRWISE_COEFFS,
            },
        }
    }
}

#[derive(Clone, Debug, Template)]
#[template(path = "contracts/Halo2VerifyingKey.sol")]
pub(crate) struct Halo2VerifyingKey {
    /// Constructor memory base used while returning VK bytes.
    pub(crate) constructor_payload_mptr: usize,
    /// Header constants followed by optional quotient constants/program words.
    pub(crate) constants: Vec<(&'static str, U256)>,
    /// EIP-2537-padded fixed commitments.
    pub(crate) fixed_comms: Vec<G1Words>,
    /// EIP-2537-padded permutation commitments.
    pub(crate) permutation_comms: Vec<G1Words>,
    /// Word offset of quotient constants, when present.
    pub(crate) quotient_const_offset_words: Option<usize>,
    /// Number of quotient constant words.
    pub(crate) quotient_const_words: usize,
    /// Word offset of quotient program words, when present.
    pub(crate) quotient_program_offset_words: Option<usize>,
    /// Number of quotient program words.
    pub(crate) quotient_program_words: usize,
}

/// INVALID byte that prefixes the separate VK runtime payload.
pub(crate) const VK_RUNTIME_PREFIX: u8 = 0xfe;
/// Number of bytes skipped before copying the separate VK payload.
pub(crate) const VK_RUNTIME_PREFIX_LEN: usize = 1;
/// EIP-170 deployed-contract runtime code-size limit (24576 bytes). The VK is
/// shipped as its own data contract whose runtime is `[INVALID, ...payload]`,
/// so it must fit under this bound to be deployable on EIP-170 chains.
pub(crate) const EIP_170_MAX_RUNTIME_BYTES: usize = 0x6000;

impl Halo2VerifyingKey {
    /// Reconstruct and validate the typed VK payload layout.
    pub(crate) fn payload_layout(&self) -> Result<VkPayloadLayout, String> {
        let quotient_words = self.quotient_const_words + self.quotient_program_words;
        let header_words = self.constants.len().checked_sub(quotient_words).ok_or_else(|| {
            format!(
                "VK constant table too short: constants={} quotient_words={quotient_words}",
                self.constants.len()
            )
        })?;
        let layout = VkPayloadLayout::for_vk(
            header_words,
            self.quotient_const_words,
            self.quotient_program_words,
            self.fixed_comms.len(),
            self.permutation_comms.len(),
        )?;

        if let Some(offset) = self.quotient_const_offset_words {
            let expected = layout.word_offset(PayloadSectionKind::QuotientConstants)?;
            if offset != expected {
                return Err(format!(
                    "quotient const offset mismatch: got {offset:#x}, expected {expected:#x}"
                ));
            }
        }
        if let Some(offset) = self.quotient_program_offset_words {
            let expected = layout.word_offset(PayloadSectionKind::QuotientProgram)?;
            if offset != expected {
                return Err(format!(
                    "quotient program offset mismatch: got {offset:#x}, expected {expected:#x}"
                ));
            }
        }

        Ok(layout)
    }

    /// Validate that typed layout length equals rendered byte length.
    pub(crate) fn validate_payload_layout(&self) -> Result<(), String> {
        let layout = self.payload_layout()?;
        if layout.total_bytes() != self.len() {
            return Err(format!(
                "VK payload byte length mismatch: layout={} bytes rendered={} bytes",
                layout.total_bytes(),
                self.len()
            ));
        }
        let runtime_len = self.runtime_len();
        if runtime_len > EIP_170_MAX_RUNTIME_BYTES {
            return Err(format!(
                "VK runtime code size {runtime_len} bytes exceeds the EIP-170 limit of \
                 {EIP_170_MAX_RUNTIME_BYTES} bytes; the VK data contract would revert at \
                 deployment. Reduce the circuit's constant/commitment count."
            ));
        }
        let constructor_memory = VkConstructorMemoryLayout::new(runtime_len);
        constructor_memory.validate()?;
        if self.constructor_payload_mptr != constructor_memory.payload_mptr {
            return Err(format!(
                "VK constructor payload pointer mismatch: got {:#x}, expected {:#x}",
                self.constructor_payload_mptr, constructor_memory.payload_mptr
            ));
        }
        Ok(())
    }

    /// Rendered VK payload length in bytes.
    pub(crate) fn len(&self) -> usize {
        // 32 bytes per scalar constant + 128 bytes per G1 point (EIP-2537 padded).
        (self.constants.len() * WORD_BYTES)
            + (self.fixed_comms.len() + self.permutation_comms.len()) * G1_BYTES
    }

    /// Deployed VK runtime length in bytes.
    pub(crate) fn runtime_len(&self) -> usize {
        VK_RUNTIME_PREFIX_LEN + self.len()
    }

    /// Rendered VK payload bytes in the exact contract return order.
    pub(crate) fn bytes(&self) -> Vec<u8> {
        self.constants
            .iter()
            .map(|(_, value)| *value)
            .chain(self.fixed_comms.iter().flat_map(|(a, b, c, d)| [*a, *b, *c, *d]))
            .chain(self.permutation_comms.iter().flat_map(|(a, b, c, d)| [*a, *b, *c, *d]))
            .flat_map(|value| value.to_be_bytes::<32>())
            .collect()
    }

    /// Deployed VK runtime bytes. Byte 0 is an unconditional INVALID opcode;
    /// the payload copied by the verifier starts at byte 1.
    pub(crate) fn runtime_bytes(&self) -> Vec<u8> {
        let mut runtime = Vec::with_capacity(self.runtime_len());
        runtime.push(VK_RUNTIME_PREFIX);
        runtime.extend(self.bytes());
        runtime
    }
}

/// Per-user-phase summary: how many advice commitments to absorb in this
/// phase, how many challenges to squeeze afterwards, and the index of
/// the first challenge within `CHALLENGE_MPTR[..]`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct UserPhase {
    pub(crate) advice_bytes: usize,
    pub(crate) num_challenges: usize,
    /// Starting offset (in 32-byte words) into the CHALLENGE_MPTR area
    /// where this phase's challenges should be written.
    pub(crate) challenge_offset: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct VerifierCodegenLayout {
    /// Planned proof calldata layout.
    pub(crate) proof: ProofCalldataLayout,
}

/// Word offsets for VK header fields rendered as template constants.
#[derive(Clone, Copy, Debug)]
pub(crate) struct VkHeaderTemplateSlots {
    pub(crate) vk_digest: usize,
    pub(crate) num_instances: usize,
    pub(crate) k: usize,
    pub(crate) n_inv: usize,
    pub(crate) omega: usize,
    pub(crate) omega_inv: usize,
    pub(crate) omega_inv_to_l: usize,
    pub(crate) has_accumulator: usize,
    pub(crate) acc_offset: usize,
    pub(crate) num_acc_limbs: usize,
    pub(crate) num_acc_limb_bits: usize,
    pub(crate) g1_base: usize,
    pub(crate) g2_base: usize,
    pub(crate) neg_s_g2_base: usize,
}

impl Default for VkHeaderTemplateSlots {
    /// Build slot offsets from the typed VK header schema.
    fn default() -> Self {
        use crate::lowering::layout::{VkHeaderLayout, VkHeaderSlot as Slot};

        Self {
            vk_digest: VkHeaderLayout::field(Slot::VkDigest).slot.word(),
            num_instances: VkHeaderLayout::field(Slot::NumInstances).slot.word(),
            k: VkHeaderLayout::field(Slot::K).slot.word(),
            n_inv: VkHeaderLayout::field(Slot::NInv).slot.word(),
            omega: VkHeaderLayout::field(Slot::Omega).slot.word(),
            omega_inv: VkHeaderLayout::field(Slot::OmegaInv).slot.word(),
            omega_inv_to_l: VkHeaderLayout::field(Slot::OmegaInvToL).slot.word(),
            has_accumulator: VkHeaderLayout::field(Slot::HasAccumulator).slot.word(),
            acc_offset: VkHeaderLayout::field(Slot::AccOffset).slot.word(),
            num_acc_limbs: VkHeaderLayout::field(Slot::NumAccLimbs).slot.word(),
            num_acc_limb_bits: VkHeaderLayout::field(Slot::NumAccLimbBits).slot.word(),
            g1_base: VkHeaderLayout::field(Slot::G1Base).slot.word(),
            g2_base: VkHeaderLayout::field(Slot::G2Base).slot.word(),
            neg_s_g2_base: VkHeaderLayout::field(Slot::NegSG2Base).slot.word(),
        }
    }
}

#[derive(Template)]
#[template(path = "contracts/Halo2Verifier.sol")]
pub(crate) struct Halo2Verifier {
    pub(crate) template_constants: TemplateConstants,
    pub(crate) trace: bool,
    /// When true, the rendered verifier emits LOG1 gas() checkpoints at
    /// section boundaries. See SOLIDITY_GAS_CHECKPOINTS_ENABLED.
    pub(crate) gas_checkpoints: bool,
    pub(crate) quotient_pow5_helper: bool,
    pub(crate) quotient_limb7_helper: bool,
    pub(crate) quotient_wide_limb7_helper: bool,
    /// Largest generated G1MSM input length, smoke-tested at deployment.
    pub(crate) constructor_g1msm_smoke_input_bytes: usize,
    /// Exact EIP-2537 G1MSM cost for the deployment smoke probe over
    /// [`Self::constructor_g1msm_smoke_input_bytes`].
    pub(crate) constructor_g1msm_smoke_gas: u64,
    /// Exact EIP-2537 G1MSM cost bound for the accumulator RHS MSM, sized
    /// for its worst case: the carried RHS point plus every generated
    /// fixed-base tail scalar nonzero. Zero tail scalars are omitted at
    /// runtime, which only lowers the actual cost below this bound.
    /// Zero when the verifier has no public accumulator.
    pub(crate) acc_rhs_msm_gas: u64,
    pub(crate) limb7_yul_coeffs: [&'static str; layout::quotient_limb::LIN_COEFFS],
    pub(crate) wide_limb7_yul_coeffs: [&'static str; layout::quotient_limb::LIN_COEFFS],
    pub(crate) fr_delta: String,
    pub(crate) embedded_vk: Option<Halo2VerifyingKey>,
    pub(crate) expected_vk_codehash: Option<U256>,
    /// keccak over the build's identity components (P10/L-8): feature
    /// profile, vk_digest, VK codehash-or-zero, SRS fingerprint, optional
    /// deployment provenance tag. Emitted as the public BUILD_ID constant.
    pub(crate) build_id: U256,
    pub(crate) vk_len: usize,
    /// Generated public-instance count for this pinned VK/proof layout.
    pub(crate) num_instances: usize,
    /// Generated evaluation domain size exponent.
    pub(crate) k: usize,
    pub(crate) proof_len: usize,
    pub(crate) codegen_layout: VerifierCodegenLayout,
    pub(crate) memory: VerifierMemoryLayout,
    pub(crate) vk_header: VkHeaderTemplateSlots,
    pub(crate) vk_mptr: Ptr,
    pub(crate) challenge_mptr: Ptr,
    pub(crate) theta_mptr: Ptr,
    pub(crate) proof_cptr: Ptr,
    pub(crate) abi_selector_bytes: usize,
    pub(crate) abi_proof_head_offset: usize,
    pub(crate) abi_instances_head_cptr: usize,
    /// Calldata byte offset of the `num_instances` length-prefix word
    /// that ABI-encodes the `instances` array. Equals
    /// `proof_cptr + proof_len` (in bytes). Materialised as a separate
    /// field because this is an ABI byte offset used directly by the
    /// hand-rolled calldata parser, while `Ptr` values are word-oriented.
    pub(crate) num_instance_cptr: usize,
    /// Calldata byte offset of the first instance value (immediately
    /// after `num_instance_cptr`).
    pub(crate) instance_cptr: usize,
    pub(crate) quotient_comm_cptr: Ptr,
    pub(crate) num_neg_lagranges: usize,
    /// Per-user-phase advice + user-challenge counts (excludes theta).
    pub(crate) user_phases: Vec<UserPhase>,
    pub(crate) num_user_challenges: usize,
    pub(crate) num_lookups: usize,
    pub(crate) num_permutation_zs: usize,
    pub(crate) lookup_h_plus_acc: usize,
    pub(crate) num_trashcans: usize,
    pub(crate) num_quotients: usize,
    pub(crate) num_evals: usize,
    /// Word offset (relative to memory base) of the first EIP-2537-padded
    /// advice commitment. The remaining categories (lookup_m, perm_z,
    /// lookup_helper, lookup_z, trashcan, quotient_limb) are laid out
    /// contiguously after this base with a 4-word stride per G1.
    pub(crate) comms_mptr_base: Ptr,
    /// Memory base of the decoded-evals buffer (Optimisation H3).
    /// The transcript-side `evaluations` loop spills the decoded scalar value
    /// to this buffer so that every later eval reference renders as
    /// `mload(...)`.
    pub(crate) reversed_evals_mptr: Ptr,
    /// Scratch base for simple-selector linearization accumulators.
    /// These values are needed only between quotient-eval emission and
    /// the linearization MSM, so the region may be reused by later PCS
    /// scratch tables.
    pub(crate) selector_acc_mptr: usize,
    pub(crate) quotient_external: Option<QuotientExternal>,
    pub(crate) expected_quotient_len: Option<usize>,
    pub(crate) expected_quotient_codehash: Option<U256>,
    pub(crate) quotient_inline_computations: Vec<Vec<String>>,
    pub(crate) quotient_eval_numer_computations: Vec<Vec<String>>,
    pub(crate) quotient_post_vm_computations: Vec<Vec<String>>,
    pub(crate) quotient_native_permutation_computation: Vec<String>,
    pub(crate) quotient_native_lookup_computation: Vec<String>,
    pub(crate) quotient_native_identity_computations: Vec<Vec<String>>,
    pub(crate) quotient_program: Option<QuotientProgram>,
    pub(crate) pcs_computations: Vec<Vec<String>>,
    /// Sorted simple-selector fixed-column indices. Each is rendered
    /// into a Yul snippet that adds `S_i_com * sel_acc_i` to the
    /// linearization commitment after Q_folded is scaled by (1-x^n).
    pub(crate) simple_selector_cols: Vec<usize>,
    pub(crate) proof_commit_trace_base: usize,
    pub(crate) proof_eval_trace_base: usize,
    pub(crate) quotient_identity_trace_base: u64,
    pub(crate) selector_trace_base: usize,
    /// Memory pointer base for the embedded VK fixed commitments. Used
    /// to resolve per-column G1 offsets in the simple-selector MSM.
    pub(crate) fixed_comm_mptr: usize,
    /// When true, mirrors midnight-proofs/truncated-challenges:
    ///   - x3 is masked to 128 bits immediately after squeeze
    ///   - x1 / x4 powers are masked to 128 bits at use, with the internal
    ///     full-precision accumulator preserved
    ///
    /// Driven by `cfg!(feature = "truncated-challenges")` in
    /// `SolidityGenerator::generate_verifier`.
    pub(crate) truncated_challenges: bool,
    /// Accumulator metadata expected by this generated verifier. These
    /// constants mirror the generator-side `AccumulatorEncoding` and are
    /// checked against the VK header after `extcodecopy` / embedded VK
    /// materialization, so a stale or mismatched VK fails before public-input
    /// decoding chooses the wrong schema.
    pub(crate) expected_has_accumulator: bool,
    pub(crate) expected_has_accumulator_word: usize,
    pub(crate) expected_acc_offset: usize,
    pub(crate) expected_num_acc_limbs: usize,
    pub(crate) expected_num_acc_limb_bits: usize,
    /// Whether the public accumulator payload carries explicit LHS/RHS scalar
    /// words. Moonlight wrap proofs expose an already collapsed point pair and
    /// use implicit unit scalars instead.
    pub(crate) expected_acc_has_carried_scalars: bool,
    /// Fixed bases serialized by `AssignedAccumulator<S>::as_public_input`
    /// for the RHS accumulator MSM, in the exact lexicographic
    /// `BTreeMap` order used by midnight-circuits. This is the public
    /// accumulator's fixed-scalar width, not necessarily every fixed
    /// commitment stored in the VK contract. Each tuple is
    /// `(point_mptr, negate_scalar)`: `-G` is represented as the
    /// regular generator with the scalar negated modulo Fr.
    pub(crate) acc_fixed_bases: Vec<(usize, bool)>,
}

#[derive(Clone, Debug)]
pub(crate) struct QuotientExternal {
    /// Base of the copied frame supplied to the external evaluator.
    pub(crate) frame_base: usize,
    /// Length of the copied frame in bytes.
    pub(crate) frame_len: usize,
    /// Expected return payload length in bytes.
    pub(crate) output_len: usize,
    /// Magic version tag checked between verifier and evaluator.
    pub(crate) magic: u64,
}

impl QuotientExternal {
    /// End byte of the copied frame, exclusive.
    fn frame_end(&self) -> usize {
        self.frame_base + self.frame_len
    }

    /// Return whether a range is fully contained by the external frame.
    fn contains_range(&self, start: usize, len: usize) -> bool {
        let end = start.saturating_add(len);
        start >= self.frame_base && end <= self.frame_end()
    }

    /// Return whether a range is disjoint from the copied external frame.
    fn disjoint_range(&self, start: usize, len: usize) -> bool {
        let end = start.saturating_add(len);
        end <= self.frame_base || start >= self.frame_end()
    }

    /// Validate that a named range is fully copied into the external frame.
    fn validate_contains(&self, name: &str, start: usize, len: usize) -> Result<(), String> {
        if self.contains_range(start, len) {
            Ok(())
        } else {
            Err(format!(
                "external quotient frame does not contain {name}: range {start:#x}..{:#x}, frame {:#x}..{:#x}",
                start.saturating_add(len),
                self.frame_base,
                self.frame_end()
            ))
        }
    }
}

#[derive(Template)]
#[template(path = "contracts/Halo2QuotientEvaluator.sol")]
pub(crate) struct Halo2QuotientEvaluator {
    pub(crate) template_constants: TemplateConstants,
    pub(crate) trace: bool,
    pub(crate) quotient_pow5_helper: bool,
    pub(crate) quotient_limb7_helper: bool,
    pub(crate) quotient_wide_limb7_helper: bool,
    pub(crate) limb7_yul_coeffs: [&'static str; layout::quotient_limb::LIN_COEFFS],
    pub(crate) wide_limb7_yul_coeffs: [&'static str; layout::quotient_limb::LIN_COEFFS],
    pub(crate) fr_delta: String,
    pub(crate) memory: VerifierMemoryLayout,
    pub(crate) vk_mptr: Ptr,
    pub(crate) vk_len: usize,
    pub(crate) challenge_mptr: Ptr,
    pub(crate) num_user_challenges: usize,
    pub(crate) theta_mptr: Ptr,
    pub(crate) reversed_evals_mptr: Ptr,
    pub(crate) num_evals: usize,
    pub(crate) quotient_external: QuotientExternal,
    pub(crate) quotient_inline_computations: Vec<Vec<String>>,
    pub(crate) quotient_eval_numer_computations: Vec<Vec<String>>,
    pub(crate) quotient_post_vm_computations: Vec<Vec<String>>,
    pub(crate) quotient_native_permutation_computation: Vec<String>,
    pub(crate) quotient_native_lookup_computation: Vec<String>,
    pub(crate) quotient_native_identity_computations: Vec<Vec<String>>,
    pub(crate) quotient_program: Option<QuotientProgram>,
    pub(crate) simple_selector_cols: Vec<usize>,
    pub(crate) quotient_identity_trace_base: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct QuotientProgram {
    /// Program length in bytes before word padding.
    pub(crate) len: usize,
    /// Opcode switch arms required by this generated program.
    pub(crate) op_usage: QuotientVmOpcodeUsage,
    /// Memory-token switch arms required by this generated program.
    pub(crate) mem_usage: QuotientVmMemUsage,
    /// Memory pointer to the first constant word.
    pub(crate) const_mptr: usize,
    /// Persistent quotient numerator accumulator word.
    pub(crate) eval_numer_mptr: usize,
    /// Persistent trace-id word.
    pub(crate) trace_id_mptr: usize,
    /// First word of the optional selector `y^k` power table.
    pub(crate) selector_power_mptr: usize,
    /// Highest selector gap/tail exponent referenced by generated code.
    pub(crate) selector_max_power: usize,
    /// Non-zero final selector y-power tail updates.
    pub(crate) selector_tail_updates: Vec<QuotientSelectorTail>,
    /// Operand stack / callback scratch base.
    pub(crate) stack_mptr: usize,
    /// First address past the operand stack / callback scratch region.
    ///
    /// MF-3: spill sites clamp `q_sp` against this so a malformed program
    /// cannot walk the stack pointer out of its registered region.
    pub(crate) stack_hi: usize,
    /// Number of Fr words in the generated quotient constant table.
    ///
    /// MF-3: constant-table indexes decoded from program bytes are clamped
    /// against this so an out-of-range index cannot read program bytes (or
    /// commitment words) as field constants.
    pub(crate) num_consts: usize,
    /// Memory pointer to the first encoded program word.
    pub(crate) program_mptr: usize,
    /// Lowest word address a VM memory operand may load from (P12/L-6).
    ///
    /// Coarse `[operand_lo, operand_hi]` clamp over the union of the plan's
    /// quotient read windows, rendered into the interpreter's operand-decode
    /// arms. Build-time `validate_quotient_mem_ptrs` still enforces exact
    /// per-window membership; the runtime clamp is defence in depth for a
    /// program trusted only through the VK codehash pin.
    pub(crate) operand_lo: usize,
    /// Highest word address a VM memory operand may load from (inclusive).
    pub(crate) operand_hi: usize,
    /// Number of simple-selector accumulator buckets addressable by
    /// FOLD_SELECTOR's index operand (P12/L-6).
    pub(crate) num_selector_buckets: usize,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct QuotientSelectorTail {
    /// Byte offset of the selector bucket under `SELECTOR_ACC_MPTR`.
    pub(crate) selector_offset: usize,
    /// Byte offset of the tail power under `selector_power_mptr`.
    pub(crate) power_offset: usize,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct QuotientVmOpcodeUsage {
    pub(crate) push_const: bool,
    pub(crate) push_mem_literal: bool,
    pub(crate) push_mem_token: bool,
    pub(crate) push_mem_token_offset: bool,
    pub(crate) push_mem_u16: bool,
    pub(crate) add: bool,
    pub(crate) mul: bool,
    pub(crate) neg: bool,
    pub(crate) push_const_u8: bool,
    pub(crate) fold_main: bool,
    pub(crate) fold_selector: bool,
    pub(crate) add_const_u8: bool,
    pub(crate) mul_const_u8: bool,
    pub(crate) add_const: bool,
    pub(crate) mul_const: bool,
    pub(crate) add_mem_u16: bool,
    pub(crate) mul_mem_u16: bool,
    pub(crate) add_mul_mem_mem_const_u8: bool,
    pub(crate) add_mul_const_u8_mem_u16: bool,
    pub(crate) add_mul_mem_mem: bool,
    pub(crate) run_add_mul_mem_mem_const_u8: bool,
    pub(crate) run_add_mul_const_u8_mem_u16: bool,
    pub(crate) affine_sum: bool,
    pub(crate) native_permutation: bool,
    pub(crate) native_lookup: bool,
    pub(crate) native_identity: bool,
    pub(crate) lin7: bool,
    pub(crate) bilin7_row: bool,
    pub(crate) bilin7_pairwise: bool,
    pub(crate) modarith7: bool,
    pub(crate) pow5: bool,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct QuotientVmMemUsage {
    pub(crate) l0: bool,
    pub(crate) l_last: bool,
    pub(crate) l_blind: bool,
    pub(crate) beta: bool,
    pub(crate) gamma: bool,
    pub(crate) x: bool,
    pub(crate) theta: bool,
    pub(crate) trash_challenge: bool,
    pub(crate) instance_eval: bool,
}

impl Halo2VerifyingKey {
    /// Render the verifying-key contract.
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

impl Halo2Verifier {
    /// Validate template inputs against the typed proof and memory layouts.
    pub(crate) fn validate_layout(&self) -> Result<(), String> {
        self.memory.validate()?;

        let proof_cptr = self.proof_cptr.value().as_usize();
        let proof_layout = &self.codegen_layout.proof;
        if proof_layout.proof_cptr != proof_cptr {
            return Err(format!(
                "proof calldata layout mismatch: template proof_cptr({proof_cptr:#x}) != layout proof_cptr({:#x})",
                proof_layout.proof_cptr
            ));
        }
        if proof_layout.proof_len != self.proof_len {
            return Err(format!(
                "proof length mismatch: template {:#x} != layout {:#x}",
                self.proof_len, proof_layout.proof_len
            ));
        }
        if proof_layout.proof_end != self.num_instance_cptr {
            return Err(format!(
                "proof calldata layout mismatch: proof_end({:#x}) != num_instance_cptr({:#x})",
                proof_layout.proof_end, self.num_instance_cptr
            ));
        }
        if self.num_instance_cptr + WORD_BYTES != self.instance_cptr {
            return Err(format!(
                "instance calldata layout mismatch: num_instance_cptr({:#x}) + 0x20 != instance_cptr({:#x})",
                self.num_instance_cptr, self.instance_cptr
            ));
        }
        let vk_end = self.vk_mptr.value().as_usize() + self.vk_len;
        let challenge_mptr = self.challenge_mptr.value().as_usize();
        if vk_end > challenge_mptr {
            return Err(format!(
                "VK memory layout mismatch: VK_MPTR({:#x}) + vk_len({:#x}) overlaps challenge_mptr({challenge_mptr:#x})",
                self.vk_mptr.value().as_usize(),
                self.vk_len
            ));
        }

        let expected_quotient_cptr = proof_layout.quotient_comm_cptr;
        let quotient_cptr = self.quotient_comm_cptr.value().as_usize();
        if quotient_cptr != expected_quotient_cptr {
            return Err(format!(
                "quotient commitment calldata mismatch: got {quotient_cptr:#x}, expected {expected_quotient_cptr:#x}"
            ));
        }

        let expected_proof_len = proof_layout.proof_len;
        if self.proof_len != expected_proof_len {
            return Err(format!(
                "proof length mismatch: got {:#x}, expected {expected_proof_len:#x}",
                self.proof_len
            ));
        }

        let comms_base = self.comms_mptr_base.value().as_usize();
        let committed_g1s = proof_layout.commitment_g1_count();
        let expected_selector_acc =
            (comms_base + committed_g1s * G1_BYTES).next_multiple_of(WORD_BYTES);
        if self.selector_acc_mptr != expected_selector_acc {
            return Err(format!(
                "selector accumulator layout mismatch: got {:#x}, expected {expected_selector_acc:#x}",
                self.selector_acc_mptr
            ));
        }

        if self.quotient_external.is_none()
            && self.quotient_program.is_none()
            && self.quotient_eval_numer_computations.is_empty()
        {
            return Err(
                "non-external quotient rendering requires a compact quotient program or legacy direct quotient blocks"
                    .to_string(),
            );
        }

        if let Some(qext) = &self.quotient_external {
            qext.validate_contains("VK payload", self.vk_mptr.value().as_usize(), self.vk_len)?;
            qext.validate_contains(
                "user challenge block",
                self.challenge_mptr.value().as_usize(),
                self.num_user_challenges * WORD_BYTES,
            )?;
            let quotient_input_end = self.memory.instance_eval_mptr.value().as_usize() + WORD_BYTES;
            qext.validate_contains(
                "quotient challenge/common slots",
                self.theta_mptr.value().as_usize(),
                quotient_input_end.saturating_sub(self.theta_mptr.value().as_usize()),
            )?;
            qext.validate_contains(
                "decoded proof evaluations",
                self.reversed_evals_mptr.value().as_usize(),
                self.num_evals * WORD_BYTES,
            )?;

            let expected_output_len = 2 * WORD_BYTES + self.simple_selector_cols.len() * WORD_BYTES;
            if qext.output_len != expected_output_len {
                return Err(format!(
                    "external quotient output length mismatch: got {:#x}, expected {expected_output_len:#x}",
                    qext.output_len
                ));
            }
            if !qext.disjoint_range(self.memory.quotient_return_mptr, expected_output_len) {
                return Err(format!(
                    "external quotient output overlaps copied frame: output {:#x}..{:#x}, frame {:#x}..{:#x}",
                    self.memory.quotient_return_mptr,
                    self.memory.quotient_return_mptr + expected_output_len,
                    qext.frame_base,
                    qext.frame_end()
                ));
            }
        }
        Ok(())
    }

    /// Render the verifier contract.
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

impl Halo2QuotientEvaluator {
    /// Validate the standalone evaluator's copied frame and output memory.
    pub(crate) fn validate_layout(&self) -> Result<(), String> {
        self.memory.validate()?;

        let qext = &self.quotient_external;
        qext.validate_contains("VK payload", self.vk_mptr.value().as_usize(), self.vk_len)?;
        qext.validate_contains(
            "user challenge block",
            self.challenge_mptr.value().as_usize(),
            self.num_user_challenges * WORD_BYTES,
        )?;
        let quotient_input_end = self.memory.instance_eval_mptr.value().as_usize() + WORD_BYTES;
        qext.validate_contains(
            "quotient challenge/common slots",
            self.theta_mptr.value().as_usize(),
            quotient_input_end.saturating_sub(self.theta_mptr.value().as_usize()),
        )?;
        qext.validate_contains(
            "decoded proof evaluations",
            self.reversed_evals_mptr.value().as_usize(),
            self.num_evals * WORD_BYTES,
        )?;

        let expected_output_len = 2 * WORD_BYTES + self.simple_selector_cols.len() * WORD_BYTES;
        if qext.output_len != expected_output_len {
            return Err(format!(
                "external quotient output length mismatch: got {:#x}, expected {expected_output_len:#x}",
                qext.output_len
            ));
        }
        if !qext.disjoint_range(self.memory.quotient_return_mptr, expected_output_len) {
            return Err(format!(
                "external quotient output overlaps copied frame: output {:#x}..{:#x}, frame {:#x}..{:#x}",
                self.memory.quotient_return_mptr,
                self.memory.quotient_return_mptr + expected_output_len,
                qext.frame_base,
                qext.frame_end()
            ));
        }

        Ok(())
    }

    /// Render the standalone quotient evaluator contract.
    pub(crate) fn render(&self, writer: &mut impl fmt::Write) -> Result<(), fmt::Error> {
        self.render_into(writer).map_err(|err| match err {
            Error::Fmt(err) => err,
            _ => unreachable!(),
        })
    }
}

mod filters {
    use std::fmt::LowerHex;

    /// Askama filter that renders a lower-hex value as an even-width Yul
    /// literal.
    pub fn hex(value: impl LowerHex) -> ::askama::Result<String> {
        let value = format!("{value:x}");
        Ok(if value.len() % 2 == 1 {
            format!("0x0{value}")
        } else {
            format!("0x{value}")
        })
    }

    /// Askama filter that renders a lower-hex value padded to `pad` nibbles.
    pub fn hex_padded(value: impl LowerHex, pad: usize) -> ::askama::Result<String> {
        let string = format!("0x{value:0pad$x}");
        if string == "0x0" {
            Ok(format!("0x{}", "0".repeat(pad)))
        } else {
            Ok(string)
        }
    }
}

#[cfg(test)]
mod tests {
    use ruint::aliases::U256;

    use super::{G1Words, Halo2Verifier, Halo2VerifyingKey, QuotientProgram, VK_RUNTIME_PREFIX};
    use crate::lowering::{
        abi::proof::ProofCalldataLayout,
        encoding::{ConstraintSystemMeta, Ptr},
        layout::{
            memory::{
                VerifierMemoryLayout, VerifierMemoryLayoutConfig, VkConstructorMemoryLayout,
                G1_BYTES, WORD_BYTES,
            },
            vk_payload::PayloadSectionKind,
        },
        protocol::{CommitmentRead, ProofReadPlan, ProtocolPlan},
    };

    /// Synthetic VK model with configurable fixed/permutation commitment
    /// counts.
    fn synthetic_vk(num_fixed: usize, num_perm: usize) -> Halo2VerifyingKey {
        // 11 named scalars + 4 g1 + 8 g2 + 8 neg_s_g2 = 31 entries (the
        // exact layout the verifier expects for the Step 6 named
        // VK_DIGEST_MPTR / G1_BASE_MPTR / G2_BASE_MPTR / NEG_S_G2_BASE_MPTR
        // slots).
        let mut constants: Vec<(&'static str, U256)> = vec![
            ("vk_digest", U256::from(0xde_u64)),
            ("num_instances", U256::from(1u64)),
            ("k", U256::from(8u64)),
            ("n_inv", U256::from(0x1234u64)),
            ("omega", U256::from(0x5678u64)),
            ("omega_inv", U256::from(0x9abcu64)),
            ("omega_inv_to_l", U256::from(0xdef0u64)),
            ("has_accumulator", U256::from(0u64)),
            ("acc_offset", U256::from(0u64)),
            ("num_acc_limbs", U256::from(0u64)),
            ("num_acc_limb_bits", U256::from(0u64)),
        ];
        constants.extend([
            ("g1_x_hi", U256::from(0x10u64)),
            ("g1_x_lo", U256::from(0x11u64)),
            ("g1_y_hi", U256::from(0x12u64)),
            ("g1_y_lo", U256::from(0x13u64)),
        ]);
        constants.extend([
            ("g2_x_c0_hi", U256::from(0x20u64)),
            ("g2_x_c0_lo", U256::from(0x21u64)),
            ("g2_x_c1_hi", U256::from(0x22u64)),
            ("g2_x_c1_lo", U256::from(0x23u64)),
            ("g2_y_c0_hi", U256::from(0x24u64)),
            ("g2_y_c0_lo", U256::from(0x25u64)),
            ("g2_y_c1_hi", U256::from(0x26u64)),
            ("g2_y_c1_lo", U256::from(0x27u64)),
        ]);
        constants.extend([
            ("neg_s_g2_x_c0_hi", U256::from(0x30u64)),
            ("neg_s_g2_x_c0_lo", U256::from(0x31u64)),
            ("neg_s_g2_x_c1_hi", U256::from(0x32u64)),
            ("neg_s_g2_x_c1_lo", U256::from(0x33u64)),
            ("neg_s_g2_y_c0_hi", U256::from(0x34u64)),
            ("neg_s_g2_y_c0_lo", U256::from(0x35u64)),
            ("neg_s_g2_y_c1_hi", U256::from(0x36u64)),
            ("neg_s_g2_y_c1_lo", U256::from(0x37u64)),
        ]);

        let fixed_comms: Vec<G1Words> = (0..num_fixed)
            .map(|i| {
                let base = U256::from(0x40_u64 + i as u64 * 4);
                (
                    base,
                    base + U256::from(1u64),
                    base + U256::from(2u64),
                    base + U256::from(3u64),
                )
            })
            .collect();
        let permutation_comms: Vec<G1Words> = (0..num_perm)
            .map(|i| {
                let base = U256::from(0x80_u64 + i as u64 * 4);
                (
                    base,
                    base + U256::from(1u64),
                    base + U256::from(2u64),
                    base + U256::from(3u64),
                )
            })
            .collect();
        let constructor_memory = VkConstructorMemoryLayout::new(
            constants.len() * WORD_BYTES + (fixed_comms.len() + permutation_comms.len()) * G1_BYTES,
        );
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

    /// Synthetic verifier model used by template-layout validation tests.
    fn synthetic_verifier() -> Halo2Verifier {
        let proof_cptr = crate::lowering::layout::abi::VERIFY_PROOF_PROOF_CPTR;
        let total_advices = 2usize;
        let num_lookups = 1usize;
        let num_permutation_zs = 1usize;
        let lookup_helper_chunks_total = 2usize;
        let num_trashcans = 1usize;
        let num_quotients = 3usize;
        let num_evals = 5usize;
        let num_point_sets = 2usize;
        let non_quotient_g1s = total_advices
            + num_lookups
            + num_permutation_zs
            + lookup_helper_chunks_total
            + num_lookups
            + num_trashcans;
        let proof_len = (non_quotient_g1s + num_quotients + 2) * G1_BYTES
            + (num_evals + num_point_sets) * WORD_BYTES;
        let comms_mptr_base = 0x2000usize;
        let selector_acc_mptr = comms_mptr_base + (non_quotient_g1s + num_quotients) * G1_BYTES;
        let memory = VerifierMemoryLayout::new(
            &ConstraintSystemMeta::default(),
            &synthetic_vk(0, 0),
            Ptr::memory(0x2000),
            VerifierMemoryLayoutConfig::default(),
        );
        let mut proof = ProofReadPlan::default();
        proof.commitments.extend((0..total_advices).map(|_| CommitmentRead::Advice));
        proof
            .commitments
            .extend((0..num_lookups).map(|_| CommitmentRead::LookupMultiplicity));
        proof
            .commitments
            .extend((0..num_permutation_zs).map(|_| CommitmentRead::PermutationProduct));
        proof
            .commitments
            .extend((0..lookup_helper_chunks_total).map(|_| CommitmentRead::LookupHelper));
        proof
            .commitments
            .extend((0..num_lookups).map(|_| CommitmentRead::LookupAccumulator));
        proof.commitments.extend((0..num_trashcans).map(|_| CommitmentRead::Trash));
        proof.commitments.extend((0..num_quotients).map(|_| CommitmentRead::Quotient));
        let protocol = ProtocolPlan {
            num_user_advices: vec![total_advices],
            lookup_chunks: vec![lookup_helper_chunks_total],
            num_lookups,
            num_permutation_zs,
            num_trashcans,
            num_quotients,
            proof,
            ..ProtocolPlan::default()
        };
        let proof_layout =
            ProofCalldataLayout::from_protocol(&protocol, proof_cptr, num_evals, num_point_sets);

        Halo2Verifier {
            template_constants: Default::default(),
            trace: false,
            gas_checkpoints: false,
            quotient_pow5_helper: false,
            quotient_limb7_helper: false,
            quotient_wide_limb7_helper: false,
            constructor_g1msm_smoke_input_bytes: crate::lowering::layout::G1_MSM_PAIR_BYTES,
            constructor_g1msm_smoke_gas: crate::lowering::layout::gas::g1msm_gas(1),
            acc_rhs_msm_gas: 0,
            limb7_yul_coeffs: crate::lowering::quotient_numerator::vm::LIMB7_YUL_COEFFS,
            wide_limb7_yul_coeffs: crate::lowering::quotient_numerator::vm::WIDE_LIMB7_YUL_COEFFS,
            fr_delta: crate::lowering::quotient_numerator::vm::fr_delta_literal(),
            embedded_vk: None,
            expected_vk_codehash: Some(U256::from(1u64)),
            build_id: U256::ZERO,
            vk_len: 0,
            num_instances: 1,
            k: 8,
            proof_len,
            codegen_layout: super::VerifierCodegenLayout {
                proof: proof_layout,
            },
            memory,
            vk_header: Default::default(),
            vk_mptr: Ptr::memory(0x2000),
            challenge_mptr: Ptr::memory(0x2200),
            theta_mptr: Ptr::memory(0x2300),
            proof_cptr: Ptr::calldata(proof_cptr),
            abi_selector_bytes: crate::lowering::layout::abi::SELECTOR_BYTES,
            abi_proof_head_offset: crate::lowering::layout::abi::VERIFY_PROOF_PROOF_HEAD_OFFSET,
            abi_instances_head_cptr: crate::lowering::layout::abi::SELECTOR_BYTES + WORD_BYTES,
            num_instance_cptr: proof_cptr + proof_len,
            instance_cptr: proof_cptr + proof_len + WORD_BYTES,
            quotient_comm_cptr: Ptr::calldata(proof_cptr + non_quotient_g1s * G1_BYTES),
            num_neg_lagranges: 0,
            user_phases: vec![],
            num_user_challenges: 0,
            num_lookups,
            num_permutation_zs,
            lookup_h_plus_acc: lookup_helper_chunks_total + num_lookups,
            num_trashcans,
            num_quotients,
            num_evals,
            comms_mptr_base: Ptr::memory(comms_mptr_base),
            reversed_evals_mptr: Ptr::memory(0x3000),
            selector_acc_mptr,
            quotient_external: None,
            expected_quotient_len: None,
            expected_quotient_codehash: None,
            quotient_inline_computations: vec![],
            quotient_eval_numer_computations: vec![],
            quotient_post_vm_computations: vec![],
            quotient_native_permutation_computation: vec![],
            quotient_native_lookup_computation: vec![],
            quotient_native_identity_computations: vec![],
            quotient_program: Some(QuotientProgram {
                len: 0,
                op_usage: Default::default(),
                mem_usage: Default::default(),
                const_mptr: 0,
                eval_numer_mptr: 0,
                trace_id_mptr: 0,
                selector_power_mptr: 0,
                selector_max_power: 0,
                selector_tail_updates: vec![],
                stack_mptr: 0,
                stack_hi: usize::MAX,
                num_consts: usize::MAX,
                program_mptr: 0,
                // Synthetic model: a permissive clamp window keeps the
                // rendered guards inert for layout-shape tests.
                operand_lo: 0,
                operand_hi: usize::MAX,
                num_selector_buckets: 0,
            }),
            pcs_computations: vec![],
            simple_selector_cols: vec![],
            proof_commit_trace_base: crate::lowering::layout::trace::PROOF_COMMIT_BASE,
            proof_eval_trace_base: crate::lowering::layout::trace::PROOF_EVAL_BASE,
            quotient_identity_trace_base: crate::lowering::layout::trace::QUOTIENT_IDENTITY_BASE,
            selector_trace_base: crate::lowering::layout::trace::SELECTOR_FOLD_BASE,
            fixed_comm_mptr: 0,
            truncated_challenges: false,
            expected_has_accumulator: false,
            expected_has_accumulator_word: 0,
            expected_acc_offset: 0,
            expected_num_acc_limbs: 0,
            expected_num_acc_limb_bits: 0,
            expected_acc_has_carried_scalars: false,
            acc_fixed_bases: vec![],
        }
    }

    #[test]
    fn verifying_key_payload_layout_matches_rendered_byte_order() {
        let mut vk = synthetic_vk(2, 1);
        let header_words = vk.constants.len();
        vk.quotient_const_offset_words = Some(header_words);
        vk.quotient_const_words = 2;
        vk.quotient_program_offset_words = Some(header_words + 2);
        vk.quotient_program_words = 3;
        vk.constants.extend((0..2).map(|_| ("quotient_const", U256::ZERO)));
        vk.constants.extend((0..3).map(|_| ("quotient_program", U256::ZERO)));

        let layout = vk.payload_layout().unwrap();

        assert_eq!(
            layout.word_offset(PayloadSectionKind::QuotientConstants).unwrap(),
            header_words
        );
        assert_eq!(
            layout.word_offset(PayloadSectionKind::QuotientProgram).unwrap(),
            header_words + 2
        );
        assert_eq!(
            layout.word_offset(PayloadSectionKind::FixedCommitments).unwrap(),
            vk.constants.len()
        );
        assert_eq!(layout.total_bytes(), vk.len());
        vk.validate_payload_layout().unwrap();
    }

    #[test]
    fn verifying_key_payload_layout_rejects_stale_quotient_offsets() {
        let mut vk = synthetic_vk(1, 1);
        vk.quotient_const_offset_words = Some(vk.constants.len() + 1);
        vk.quotient_const_words = 1;
        vk.quotient_program_offset_words = Some(vk.constants.len() + 1);
        vk.quotient_program_words = 0;
        vk.constants.push(("quotient_const", U256::ZERO));

        let err = vk.validate_payload_layout().expect_err("stale quotient offset rejected");

        assert!(err.contains("quotient const offset mismatch"));
    }

    #[test]
    fn vk_layout_byte_consistency() {
        // For a synthetic VK with 31 named scalars + N=2 fixed + M=3
        // permutation commitments, expect:
        //   len() = 31*32 + (2+3)*4*32 = 31*32 + 20*32 = 51*32 = 1632 bytes
        //   bytes().len() == len()
        let vk = synthetic_vk(2, 3);
        let expected_len = 31 * 32 + (2 + 3) * 4 * 32;
        assert_eq!(vk.len(), expected_len);
        assert_eq!(vk.bytes().len(), expected_len);

        // The first 32 bytes of bytes() should encode `vk_digest`.
        let head = &vk.bytes()[..32];
        let mut buf = [0u8; 32];
        buf.copy_from_slice(head);
        let head_u256 = U256::from_be_bytes(buf);
        assert_eq!(head_u256, U256::from(0xde_u64));

        // Word index of NEG_S_G2_BASE_MPTR = 23 (vk_mptr + 23).
        // Verify the corresponding bytes match the synthetic value 0x30.
        let off = 23 * 32;
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&vk.bytes()[off..off + 32]);
        let neg_s_g2_x_c0_hi = U256::from_be_bytes(buf);
        assert_eq!(neg_s_g2_x_c0_hi, U256::from(0x30_u64));

        // First fixed_comm starts at word 31.
        let off = 31 * 32;
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&vk.bytes()[off..off + 32]);
        assert_eq!(U256::from_be_bytes(buf), U256::from(0x40_u64));

        // First permutation_comm starts at word 31 + 4*N_FIXED = 39.
        let off = 39 * 32;
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&vk.bytes()[off..off + 32]);
        assert_eq!(U256::from_be_bytes(buf), U256::from(0x80_u64));
    }

    #[test]
    fn verifier_layout_validation_checks_calldata_and_memory_cursors() {
        let verifier = synthetic_verifier();
        verifier.validate_layout().expect("synthetic layout");
    }

    #[test]
    fn verifier_layout_validation_rejects_cursor_drift() {
        let mut verifier = synthetic_verifier();
        verifier.num_instance_cptr += 0x20;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("proof calldata layout mismatch"),
            "unexpected layout error: {err}"
        );
    }

    #[test]
    fn verifier_layout_validation_rejects_vk_challenge_overlap() {
        let mut verifier = synthetic_verifier();
        verifier.vk_len = 0x220;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("VK memory layout mismatch"),
            "unexpected layout error: {err}"
        );
    }

    #[test]
    fn verifier_layout_validation_rejects_pcs_scratch_overflow() {
        let mut verifier = synthetic_verifier();
        verifier.memory.pcs.rot_points_words = 29;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("ROT_POINTS_MPTR needs 29 word"),
            "unexpected layout error: {err}"
        );

        let mut verifier = synthetic_verifier();
        verifier.memory.pcs.x1_powers_words = 66;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("X1_POWERS_MPTR needs 66 word"),
            "unexpected layout error: {err}"
        );

        let mut verifier = synthetic_verifier();
        verifier.memory.pcs.q_com_words = 1;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("Q_COM_MPTR needs 1 word"),
            "unexpected layout error: {err}"
        );

        let mut verifier = synthetic_verifier();
        verifier.memory.pcs.q_eval_set_words = 57;
        let err = verifier.validate_layout().unwrap_err();
        assert!(
            err.contains("Q_EVAL_SET_MPTR needs 57 word"),
            "unexpected layout error: {err}"
        );
    }

    #[test]
    fn vk_renders_and_returns_correct_length() {
        let vk = synthetic_vk(2, 3);
        let mut s = String::new();
        vk.render(&mut s).expect("VK render");
        // The constructor returns one INVALID byte followed by the payload. The
        // verifier pins that full runtime but copies only the payload from
        // byte offset 1. Our `hex` filter left-pads odd-length hex literals
        // with a leading zero, so 0x661 (3 hex digits) renders as "0x0661".
        let runtime = vk.runtime_bytes();
        assert_eq!(runtime.len(), vk.runtime_len());
        assert_eq!(runtime[0], VK_RUNTIME_PREFIX);
        assert_eq!(&runtime[1..], vk.bytes().as_slice());

        let raw_hex = format!("{:x}", vk.runtime_len());
        let padded_hex = if raw_hex.len() % 2 == 1 {
            format!("0{raw_hex}")
        } else {
            raw_hex
        };
        let expected_return = format!("return(runtime, 0x{padded_hex})");
        assert!(
            s.contains(&expected_return),
            "rendered VK missing expected return statement {expected_return} in:\n{s}"
        );
        assert!(
            s.contains("let runtime := 0x80"),
            "VK constructor runtime buffer must start after Solidity's reserved words"
        );
        assert!(
            s.contains("let payload := add(runtime, 0x01)"),
            "VK payload must start after the INVALID runtime prefix"
        );
        assert!(
            s.contains("mstore8(runtime, 0xfe)"),
            "VK runtime must start with an unconditional INVALID opcode"
        );
        // It should `mstore` the very first scalar (vk_digest) at payload + 0.
        assert!(
            s.contains("mstore(add(payload, 0x0000),"),
            "vk_digest mstore at payload offset 0"
        );
        // The first permutation commitment is at byte offset 0x4e0
        // (39 * 32 = 1248 = 0x4e0).
        assert!(
            s.contains("mstore(add(payload, 0x04e0),"),
            "permutation_comms[0].x_hi at byte offset 0x4e0"
        );
    }
}
