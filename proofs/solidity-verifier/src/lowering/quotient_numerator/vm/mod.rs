// SPDX-License-Identifier: CC0-1.0
//! Producer-side implementation of the compact quotient-numerator VM.
//!
//! The verifier reconstructs the batched numerator `nu_y(x)` from the
//! polynomial evaluations that were already read after the Fiat-Shamir
//! challenge `x`, and then opens the linearized commitment at the scalar
//! `-nu_y(x)`. The commitment side contributes `(1 - x^n) * sum_i x_split^i *
//! Q_i` for the quotient limbs, so the scalar stored in verifier memory is
//! deliberately the negated numerator, not `h(x) = nu_y(x) / (x^n - 1)`.
//!
//! This module is the Rust producer for that reconstruction. It lowers Halo2
//! quotient identities into a compact bytecode stream plus a constant table;
//! `templates/partials/quotient_numerator/QuotientNumeratorBlock.yul` is the
//! only runtime consumer. The VM is therefore an ABI between generated VK data
//! and generated Solidity: opcode numbers, operand widths, memory tokens, stack
//! discipline, fold order, and native callback markers must change in lockstep
//! with the Yul template and the tests that compare the tables.
//!
//! Correctness comes from preserving the same identity stream used by
//! `midnight_proofs::plonk::partially_evaluate_identities` and
//! `compute_linearization_commitment`:
//!
//! ```text
//! identities: e_0, e_1, ..., e_(m-1)
//! main accumulator scan: acc <- acc * y + e_i
//! final main scalar: sum_i e_i * y^(m - 1 - i)
//! ```
//!
//! The Rust linearization code computes the same scalar by reverse-folding
//! powers of `y`; the Yul VM scans forward with Horner's rule because that is
//! cheaper and streaming-friendly. A simple-selector identity still advances
//! the global `y` position, but its value is sent to the selector commitment
//! bucket instead of the fully evaluated numerator. The selector positions are
//! known at code generation time, so each selector bucket is advanced only by
//! the gap since the previous identity for the same selector, then by its final
//! tail. That preserves the same `y^(m-1-i)` powers without computing `y^-1`
//! or updating every selector bucket position on unrelated identities.
//!
//! The VM is intentionally small rather than general-purpose. It has only Fr
//! arithmetic, memory loads from generated verifier addresses, a deduplicated
//! VK-resident constant table, optional common-subexpression temporaries, and a
//! few fused opcodes for shapes that dominate Midfall quotient identities.
//! Whole-family native markers, such as permutation and lookup callbacks, are
//! domain-shaped superinstructions: they preserve identity order while moving
//! regular product-loop arithmetic out of the interpreter. The limb-aware
//! opcodes are justified as structural compression of foreign-field limb
//! expressions; they do not change the source of truth and they still evaluate
//! the resulting PLONK identity over BLS12-381 Fr.
//!
//! Finalized bytecode is decoded again after run compaction. That safety pass
//! rejects unknown opcodes, truncated operands, unknown memory tokens, stack
//! underflow, and identity-boundary stack leaks before the bytes can be pinned
//! into a VK runtime.

pub(crate) mod certify;
#[cfg(test)]
pub(crate) mod oracle;
pub(crate) mod reference;

use std::collections::{HashMap, HashSet};

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::plonk::{Expression, Selector};
use ruint::aliases::U256;

#[cfg(test)]
use crate::api::{
    QuotientIdentityManifest, QuotientIdentityManifestEntry, QuotientIdentityManifestTarget,
};
use crate::{
    api::QuotientIdentitySource,
    lowering::{
        config,
        encoding::{fe_to_u256, ConstraintSystemMeta, Data, Location, Ptr, Value, Word},
        layout::{self, WORD_BYTES},
    },
};

/// Destination of one evaluated quotient identity.
///
/// Each identity occupies exactly one position in the global `y` batch. The
/// target only decides where the evaluated scalar is accumulated after that
/// position has been consumed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum QuotientTarget {
    /// Fully evaluated identity.
    ///
    /// The value contributes to the reconstructed numerator scalar. After the
    /// whole stream has been consumed, the Yul runtime stores the negation in
    /// `QUOTIENT_EVAL_MPTR`.
    Main,
    /// Simple-selector identity.
    ///
    /// The `usize` is an index into the sorted simple-selector column list,
    /// not the fixed-column index itself. The value is accumulated into the
    /// matching selector commitment bucket while still advancing the global
    /// `y` batch.
    Selector(usize),
}

/// Source metadata for one internal quotient identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct QuotientIdentityMetadata {
    /// Position in the global `y`-batch.
    pub(crate) global_index: usize,
    /// Source family and source-local metadata.
    pub(crate) source: QuotientIdentitySource,
}

/// Complete VM artifact emitted into the generated verifying-key payload.
///
/// The generator memory planner uses this to reserve constant, bytecode, stack,
/// and scratch regions; the Yul template uses the same values to interpret
/// the program. The build is intentionally self-contained so the external
/// quotient evaluator can execute with only the copied verifier frame plus VK
/// payload data.
#[derive(Clone, Debug)]
pub(crate) struct QuotientProgramBuild {
    /// Encoded byte-oriented bytecode.
    pub(crate) bytes: Vec<u8>,
    /// Deduplicated Fr constants addressed by `PUSH_CONST` and fused opcodes.
    pub(crate) consts: Vec<U256>,
    /// Maximum operand-stack depth of the pure interpreted bytecode.
    ///
    /// Native callbacks may reuse the same stack base as structured scratch,
    /// so the generator folds their scratch requirement into the final
    /// allocation separately.
    pub(crate) max_stack: usize,
    /// Opcode bytes actually present in the finalized physical program.
    ///
    /// The template uses this to render only the interpreter cases reachable
    /// by this VK-specialized quotient program.
    pub(crate) used_ops: Vec<u8>,
    /// Memory-token operands actually present in the finalized physical
    /// program.
    pub(crate) used_mem_tokens: Vec<u8>,
}

/// One Halo2 quotient identity in both native-Yul and VM-ready forms.
///
/// The normal evaluator still emits assignment lines because direct inline
/// paths and native callbacks reuse them. `expr` is built once during quotient
/// planning and is the single source for compact VM bytecode emission.
#[derive(Clone, Debug)]
pub(crate) struct QuotientIdentity {
    /// Host-side diagnostic metadata for this identity.
    pub(crate) meta: QuotientIdentityMetadata,
    /// Yul assignment lines emitted by the existing evaluator.
    pub(crate) lines: Vec<String>,
    /// Name of the Yul variable holding the final identity evaluation.
    pub(crate) var: String,
    /// Accumulator target for this identity.
    pub(crate) target: QuotientTarget,
    /// Typed expression form used by the VM.
    pub(crate) expr: QuotientExpr,
}

#[cfg(all(test, feature = "evm"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RepackedProofScalarLayout {
    pub(crate) eval_offset: usize,
    pub(crate) num_evals: usize,
    pub(crate) q_eval_offset: usize,
    pub(crate) num_point_sets: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct RepackedProofLayoutPlan {
    /// Counts of compressed G1 commitments read before scalar evaluations.
    pub(crate) g1_groups: Vec<usize>,
    /// Number of ordinary evaluation scalars.
    pub(crate) num_evals: usize,
    /// Number of quotient-opening point-set scalars.
    pub(crate) num_point_sets: usize,
}

impl RepackedProofLayoutPlan {
    /// Build a proof repacking plan from the typed Solidity calldata layout.
    pub(crate) fn from_proof_layout(
        layout: &crate::lowering::abi::proof::ProofCalldataLayout,
    ) -> Self {
        Self {
            g1_groups: layout.commitment_read_groups(),
            num_evals: layout.evals.item_count,
            num_point_sets: layout.q_evals.item_count,
        }
    }

    /// Number of compressed G1 points before the scalar eval block.
    pub(crate) fn prefix_g1_count(&self) -> usize {
        self.g1_groups.iter().sum()
    }

    /// Native compressed proof byte length expected by the repacker.
    pub(crate) fn compressed_len(&self) -> usize {
        self.prefix_g1_count() * crate::lowering::layout::G1_COMPRESSED_BYTES
            + self.num_evals * crate::lowering::layout::WORD_BYTES
            + crate::lowering::layout::G1_COMPRESSED_BYTES
            + self.num_point_sets * crate::lowering::layout::WORD_BYTES
            + crate::lowering::layout::G1_COMPRESSED_BYTES
    }

    /// Solidity-facing EIP-2537-padded proof byte length after repacking.
    pub(crate) fn repacked_len(&self) -> usize {
        self.prefix_g1_count() * crate::lowering::layout::G1_BYTES
            + self.num_evals * crate::lowering::layout::WORD_BYTES
            + crate::lowering::layout::G1_BYTES
            + self.num_point_sets * crate::lowering::layout::WORD_BYTES
            + crate::lowering::layout::G1_BYTES
    }

    #[cfg(all(test, feature = "evm"))]
    /// Return scalar offsets within the repacked proof for tests.
    pub(crate) fn scalar_layout(&self) -> RepackedProofScalarLayout {
        let eval_offset = self.prefix_g1_count() * crate::lowering::layout::G1_BYTES;
        let q_eval_offset = eval_offset
            + self.num_evals * crate::lowering::layout::WORD_BYTES
            + crate::lowering::layout::G1_BYTES;
        RepackedProofScalarLayout {
            eval_offset,
            num_evals: self.num_evals,
            q_eval_offset,
            num_point_sets: self.num_point_sets,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct QuotientIdentityParts {
    /// Gate identities, in the order returned by the upstream constraint
    /// system.
    pub(crate) gates: Vec<QuotientIdentity>,
    /// Permutation identities, after gates.
    pub(crate) permutation: Vec<QuotientIdentity>,
    /// Lookup identities, after permutation.
    pub(crate) lookup: Vec<QuotientIdentity>,
    /// Trashcan identities, after lookup.
    pub(crate) trash: Vec<QuotientIdentity>,
    /// Sorted fixed-column indices for simple selectors.
    ///
    /// VM selector targets use positions in this vector so generated memory
    /// buckets are stable even if fixed-column numbers are sparse.
    pub(crate) sorted_simple: Vec<usize>,
}

impl QuotientIdentityParts {
    /// Return every identity in global y-batch order.
    pub(crate) fn all_identities(&self) -> Vec<QuotientIdentity> {
        self.gates
            .iter()
            .chain(self.permutation.iter())
            .chain(self.lookup.iter())
            .chain(self.trash.iter())
            .cloned()
            .collect()
    }

    /// Return the host-side manifest for these identities.
    #[cfg(test)]
    pub(crate) fn manifest(&self) -> QuotientIdentityManifest {
        let entries = self
            .gates
            .iter()
            .chain(self.permutation.iter())
            .chain(self.lookup.iter())
            .chain(self.trash.iter())
            .map(|identity| QuotientIdentityManifestEntry {
                global_index: identity.meta.global_index,
                source: identity.meta.source.clone(),
                target: quotient_manifest_target(identity.target, &self.sorted_simple),
            })
            .collect();

        QuotientIdentityManifest {
            entries,
            gate_identities: self.gates.len(),
            permutation_identities: self.permutation.len(),
            lookup_identities: self.lookup.len(),
            trash_identities: self.trash.len(),
            simple_selector_cols: self.sorted_simple.clone(),
        }
    }
}

#[cfg(test)]
fn quotient_manifest_target(
    target: QuotientTarget,
    sorted_simple: &[usize],
) -> QuotientIdentityManifestTarget {
    match target {
        QuotientTarget::Main => QuotientIdentityManifestTarget::Main,
        QuotientTarget::Selector(selector_index) => QuotientIdentityManifestTarget::Selector {
            selector_index,
            fixed_column: sorted_simple[selector_index],
        },
    }
}

/// Logical stream item before final bytecode lowering.
///
/// Native items are not arithmetic opcodes in the Rust builder. They are
/// identity-position markers; the Yul template replaces them with generated
/// callback blocks that perform their own evaluation and fold at exactly the
/// same point in the global `y` batch.
#[derive(Clone, Debug)]
pub(crate) enum QuotientProgramItem {
    /// Identity interpreted by the compact VM.
    Identity(QuotientIdentity),
    /// Generated callback for the whole permutation identity block.
    NativePermutation,
    /// Generated callback for the whole lookup identity block.
    NativeLookup,
    /// Generated callback for a selected heavy gate identity.
    NativeIdentity(usize),
}

/// Hybrid execution plan for quotient numerator reconstruction.
///
/// A small prefix may stay inline, most identities become VM bytecode, and
/// selected expensive shapes can become native callbacks. The plan is a
/// representation choice only: it must preserve the original identity order and
/// the target of every identity.
#[derive(Clone, Debug)]
pub(crate) struct QuotientProgramPlan {
    /// Gate prefix emitted directly before the VM loop.
    pub(crate) inline_identities: Vec<QuotientIdentity>,
    /// VM/native stream after the inline prefix.
    pub(crate) items: Vec<QuotientProgramItem>,
    /// Bodies for `NativeIdentity` markers, addressed by marker index.
    pub(crate) native_identities: Vec<QuotientIdentity>,
    /// Identity range expanded by a `NativePermutation` marker, if present.
    pub(crate) native_permutation_identities: Vec<QuotientIdentity>,
    /// Identity range expanded by a `NativeLookup` marker, if present.
    pub(crate) native_lookup_identities: Vec<QuotientIdentity>,
    /// Structured post-VM identity range, currently the optional trash suffix.
    pub(crate) structured_tail_identities: Vec<QuotientIdentity>,
    /// Shared selector-column ordering.
    pub(crate) sorted_simple: Vec<usize>,
    /// Whether the stream contains a native permutation callback marker.
    pub(crate) has_native_permutation: bool,
    /// Whether the stream contains a native lookup callback marker.
    pub(crate) has_native_lookup: bool,
    /// Gap exponents for simple-selector buckets in the global y-batch.
    pub(crate) selector_fold: SelectorFoldPlan,
}

/// Execution surface used to fold an identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum QuotientExecutionKind {
    /// Direct Yul emitted before the VM loop.
    Inline,
    /// Compact VM bytecode expression followed by a fold opcode.
    Interpreted,
    /// Native callback replacing the full permutation identity range.
    NativePermutation,
    /// Native callback replacing the full lookup identity range.
    NativeLookup,
    /// Native callback replacing one selected heavy gate identity.
    NativeIdentity {
        /// Index into `QuotientProgramPlan::native_identities`.
        native_index: usize,
    },
    /// Structured Yul emitted after the VM loop.
    StructuredTail,
}

/// One identity after representation choices have been applied.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct QuotientExecutionManifestEntry {
    /// Position in the original global y-batch.
    pub(crate) global_index: usize,
    /// Original source metadata.
    pub(crate) source: QuotientIdentitySource,
    /// Original fold target.
    pub(crate) target: QuotientTarget,
    /// How this identity is executed in the generated verifier.
    pub(crate) execution: QuotientExecutionKind,
}

impl QuotientProgramPlan {
    /// Walk every identity in generated execution order with the surface that
    /// folds it.
    ///
    /// Native markers and structured tails are expanded to the exact identity
    /// ranges they replace. This single walk backs both the public execution
    /// manifest and the frame-differential oracle, so the two cannot disagree
    /// about which surface executes an identity.
    pub(crate) fn identities_in_execution_order(
        &self,
    ) -> Result<Vec<(&QuotientIdentity, QuotientExecutionKind)>, String> {
        let mut out = Vec::new();
        for identity in &self.inline_identities {
            out.push((identity, QuotientExecutionKind::Inline));
        }

        for item in &self.items {
            match item {
                QuotientProgramItem::Identity(identity) => {
                    out.push((identity, QuotientExecutionKind::Interpreted))
                }
                QuotientProgramItem::NativePermutation => {
                    if self.native_permutation_identities.is_empty() {
                        return Err(
                            "native permutation marker has empty identity range".to_string()
                        );
                    }
                    out.extend(
                        self.native_permutation_identities
                            .iter()
                            .map(|identity| (identity, QuotientExecutionKind::NativePermutation)),
                    );
                }
                QuotientProgramItem::NativeLookup => {
                    if self.native_lookup_identities.is_empty() {
                        return Err("native lookup marker has empty identity range".to_string());
                    }
                    out.extend(
                        self.native_lookup_identities
                            .iter()
                            .map(|identity| (identity, QuotientExecutionKind::NativeLookup)),
                    );
                }
                QuotientProgramItem::NativeIdentity(native_index) => {
                    let identity = self.native_identities.get(*native_index).ok_or_else(|| {
                        format!("native identity marker {native_index} has no callback body")
                    })?;
                    out.push((
                        identity,
                        QuotientExecutionKind::NativeIdentity {
                            native_index: *native_index,
                        },
                    ));
                }
            }
        }

        out.extend(
            self.structured_tail_identities
                .iter()
                .map(|identity| (identity, QuotientExecutionKind::StructuredTail)),
        );
        Ok(out)
    }

    /// Reconstruct the generated execution stream back into per-identity folds.
    ///
    /// This is the compiler-correctness bridge between the source identity
    /// stream and the mixed VM/native/direct execution plan.
    pub(crate) fn execution_manifest(&self) -> Result<Vec<QuotientExecutionManifestEntry>, String> {
        Ok(self
            .identities_in_execution_order()?
            .into_iter()
            .map(|(identity, execution)| quotient_execution_entry(identity, execution))
            .collect())
    }

    /// Check that representation choices preserve the original identity stream.
    pub(crate) fn validate_execution_manifest(
        &self,
        expected: &[QuotientIdentity],
    ) -> Result<(), String> {
        let manifest = self.execution_manifest()?;
        if manifest.len() != expected.len() {
            return Err(format!(
                "quotient execution manifest length mismatch: got {}, expected {}",
                manifest.len(),
                expected.len()
            ));
        }

        for (pos, (actual, expected)) in manifest.iter().zip(expected).enumerate() {
            if actual.global_index != expected.meta.global_index
                || actual.source != expected.meta.source
                || actual.target != expected.target
            {
                return Err(format!(
                    "quotient execution manifest mismatch at position {pos}: got index {}, source {:?}, target {:?}; expected index {}, source {:?}, target {:?}",
                    actual.global_index,
                    actual.source,
                    actual.target,
                    expected.meta.global_index,
                    expected.meta.source,
                    expected.target
                ));
            }
        }

        Ok(())
    }
}

/// Convert one planned identity plus chosen execution mode into the public
/// execution manifest shape.
fn quotient_execution_entry(
    identity: &QuotientIdentity,
    execution: QuotientExecutionKind,
) -> QuotientExecutionManifestEntry {
    QuotientExecutionManifestEntry {
        global_index: identity.meta.global_index,
        source: identity.meta.source.clone(),
        target: identity.target,
        execution,
    }
}

/// Codegen-time selector-bucket schedule for gap-based forward folding.
///
/// Fully evaluated identities still use the ordinary Horner scan. Selector
/// identities are sparse in that global stream, so each selector bucket only
/// needs to be advanced across the gap since the previous identity for the same
/// selector and then across the final tail after the stream ends.
#[derive(Clone, Debug, Default)]
pub(crate) struct SelectorFoldPlan {
    /// `Some(gap)` for selector identities by global identity index.
    pub(crate) gaps_by_identity: Vec<Option<usize>>,
    /// Final y-power tail for each selector bucket.
    pub(crate) tail_exponents: Vec<usize>,
    /// Largest exponent referenced by either gaps or tails.
    pub(crate) max_power: usize,
}

impl SelectorFoldPlan {
    /// Gap from this selector identity to the previous identity in the same
    /// selector bucket.
    pub(crate) fn gap_for(&self, identity: &QuotientIdentity) -> Option<usize> {
        self.gaps_by_identity.get(identity.meta.global_index).copied().flatten()
    }
}

/// Magic/version word returned by a split quotient evaluator.
pub(crate) const QUOTIENT_EXTERNAL_MAGIC: u64 = 0x5155_4556_414c_0001;
// Coefficients used by generated limb helper snippets in direct/native Yul
// paths. The VM limb opcodes do not hard-code these values; they load the
// corresponding Fr constants from the VK payload so the bytecode remains a
// representation of the actual lowered expression.
pub(crate) const LIMB7_YUL_COEFFS: [&str; layout::quotient_limb::LIN_COEFFS] = [
    "0x100000000000000",
    "0x10000000000000000000000000000",
    "0x400000000",
    "0x40000000000000000000000",
    "0x1000",
    "0x100000000000000000",
];
/// Coefficients for seven-term windows in the wide pairwise-product limb basis.
pub(crate) const WIDE_LIMB7_YUL_COEFFS: [&str; layout::quotient_limb::LIN_COEFFS] = [
    "0x100000000000000",
    "0x10000000000000000000000000000",
    "0x1000000000000000000000000000000000000000000",
    "0x100000000000000000000000000000000000000000000000000000000",
    "0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c",
    "0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b",
];

/// Minimum adjacent fused-op run worth replacing with a run opcode.
pub(crate) const QUOTIENT_VM_RUN_COMPACTION_MIN_LEN: usize = 4;
/// Encoded byte width of a `u16` operand.
pub(crate) const QUOTIENT_VM_BYTE_U16_BYTES: usize = 2;
/// Encoded byte width of the selector-fold `(selector_index, gap)` operand.
pub(crate) const QUOTIENT_VM_BYTE_U24_BYTES: usize = 3;
/// Encoded byte width of absolute memory pointers and token offsets.
pub(crate) const QUOTIENT_VM_BYTE_U32_BYTES: usize = 4;
/// Number of limbs in a recognized foreign-field coordinate.
pub(crate) const QUOTIENT_VM_LIMBS: usize = layout::quotient_limb::LIMBS;
/// Number of pairwise products in a 7x7 limb multiplication grid.
pub(crate) const QUOTIENT_VM_PAIRWISE_TERMS: usize = layout::quotient_limb::PAIRWISE_TERMS;
/// Number of diagonal coefficients in that pairwise grid.
pub(crate) const QUOTIENT_VM_PAIRWISE_COEFFS: usize = layout::quotient_limb::PAIRWISE_COEFFS;

// Opcode assignments are part of the verifier/VK ABI.
//
// Stack convention:
//   * push opcodes place a value in q_top, spilling the previous top to the
//     memory stack when needed;
//   * generic ADD/MUL consume one spilled operand and q_top, leaving q_top;
//   * accumulator opcodes mutate q_top in place and have zero stack effect;
//   * FOLD_* consumes q_top and advances the quotient y-batch;
//   * native callback markers require an empty stack at identity boundaries.
//
// The numeric assignments are intentionally sparse. Keep 0x1a reserved:
// historical builds used it for an experimental native trash callback, but the
// current VM intentionally has no operation at that value.
pub(crate) const Q_OP_PUSH_CONST: u8 = 0x01; // push VK constant-table value
pub(crate) const Q_OP_PUSH_MEM_LITERAL: u8 = 0x02; // push mload(absolute_ptr)
pub(crate) const Q_OP_PUSH_MEM_TOKEN: u8 = 0x03; // push mload(symbolic_token)
pub(crate) const Q_OP_PUSH_MEM_TOKEN_OFFSET: u8 = 0x04; // push mload(token + offset)
pub(crate) const Q_OP_PUSH_MEM_U16: u8 = 0x05; // push mload(short absolute ptr)
pub(crate) const Q_OP_ADD: u8 = 0x06; // binary Fr addition
pub(crate) const Q_OP_MUL: u8 = 0x07; // binary Fr multiplication
pub(crate) const Q_OP_NEG: u8 = 0x08; // unary Fr negation
pub(crate) const Q_OP_PUSH_CONST_U8: u8 = 0x09; // push short constant-table slot
pub(crate) const Q_OP_FOLD_MAIN: u8 = 0x0a; // consume top into main y-fold
pub(crate) const Q_OP_FOLD_SELECTOR: u8 = 0x0b; // consume top into selector bucket
pub(crate) const Q_OP_ADD_CONST_U8: u8 = 0x0c; // top += short constant
pub(crate) const Q_OP_MUL_CONST_U8: u8 = 0x0d; // top *= short constant
pub(crate) const Q_OP_ADD_CONST: u8 = 0x0e; // top += constant-table value
pub(crate) const Q_OP_MUL_CONST: u8 = 0x0f; // top *= constant-table value
pub(crate) const Q_OP_ADD_MEM_U16: u8 = 0x10; // top += mload(ptr)
pub(crate) const Q_OP_MUL_MEM_U16: u8 = 0x11; // top *= mload(ptr)
pub(crate) const Q_OP_ADD_MUL_MEM_MEM_CONST_U8: u8 = 0x12; // top += lhs * rhs * const
pub(crate) const Q_OP_ADD_MUL_CONST_U8_MEM_U16: u8 = 0x13; // top += const * mload(ptr)
pub(crate) const Q_OP_ADD_MUL_MEM_MEM: u8 = 0x14; // top += lhs * rhs
pub(crate) const Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8: u8 = 0x15; // compact run of op 0x12
pub(crate) const Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16: u8 = 0x16; // compact run of op 0x13
pub(crate) const Q_OP_NATIVE_PERMUTATION: u8 = 0x19; // delegate permutation family
pub(crate) const Q_OP_NATIVE_IDENTITY: u8 = 0x1b; // delegate one selected gate identity
pub(crate) const Q_OP_LIN7: u8 = 0x1c; // evaluate seven-limb linear form
pub(crate) const Q_OP_BILIN7_ROW: u8 = 0x1d; // evaluate one limb times a seven-limb row
pub(crate) const Q_OP_BILIN7_PAIRWISE: u8 = 0x1e; // evaluate a 7x7 pairwise product
pub(crate) const Q_OP_NATIVE_LOOKUP: u8 = 0x1f; // delegate lookup family
pub(crate) const Q_OP_POW5: u8 = 0x20; // raise top to the fifth power
pub(crate) const Q_OP_MODARITH7: u8 = 0x21; // dynamic mixed seven-limb affine form
pub(crate) const Q_OP_AFFINE_SUM: u8 = 0x22; // dynamic affine sum over mem/products

/// MODARITH7 operand flag: first operand is a conditional memory factor.
const Q_MODARITH7_FLAG_COND: u8 = 0x01;
/// MODARITH7 operand flag: a nonzero constant term is encoded first.
const Q_MODARITH7_FLAG_CONST: u8 = 0x02;

// Memory tokens compress generated Yul symbols whose concrete addresses depend
// on the memory planner. Literal pointers are used for most proof/VK evals;
// tokens cover shared challenge/common-polynomial locations that are easier and
// safer to address symbolically in generated code.
pub(crate) const Q_MEM_L0: u8 = 0x01; // L_0(x)
pub(crate) const Q_MEM_L_LAST: u8 = 0x02; // L_last(x)
pub(crate) const Q_MEM_L_BLIND: u8 = 0x03; // L_blind(x)
pub(crate) const Q_MEM_BETA: u8 = 0x04; // permutation/lookup beta
pub(crate) const Q_MEM_GAMMA: u8 = 0x05; // permutation/lookup gamma
pub(crate) const Q_MEM_X: u8 = 0x06; // evaluation challenge x
pub(crate) const Q_MEM_THETA: u8 = 0x07; // lookup compression theta
pub(crate) const Q_MEM_TRASH_CHALLENGE: u8 = 0x08; // trash argument challenge
pub(crate) const Q_MEM_INSTANCE_EVAL: u8 = 0x09; // locally interpolated public input

/// Operand decoder classes shared by tests and docs.
///
/// The Yul template is the runtime decoder; this enum is the compile-time/spec
/// view of the same ABI. Encodings with zero fixed byte length are dynamic
/// byte-only forms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum QuotientOpcodeEncoding {
    None,
    U8,
    U16,
    U24,
    U32,
    TokenOffset,
    AddMulMemMemConstU8,
    AddMulConstU8MemU16,
    AddMulMemMem,
    RunAddMulMemMemConstU8,
    RunAddMulConstU8MemU16,
    LimbLin,
    LimbBilinRow,
    LimbBilinPairwise,
    LimbModarith7,
    AffineSum,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct QuotientOpcodeSpec {
    /// Stable snake-case name rendered into template constants.
    pub(crate) name: &'static str,
    /// Stable opcode byte.
    pub(crate) opcode: u8,
    /// Byte length in byte-oriented encoding, or zero for dynamic run forms.
    pub(crate) byte_len: usize,
    /// Operand decoding class.
    pub(crate) encoding: QuotientOpcodeEncoding,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct QuotientMemTokenSpec {
    /// Generated Yul memory symbol.
    pub(crate) name: &'static str,
    /// Stable compact token used by VM bytecode.
    pub(crate) token: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct QuotientVmSpec {
    /// Complete opcode table, used by template constants and ABI tests.
    pub(crate) opcodes: &'static [QuotientOpcodeSpec],
    /// Complete memory-token table, used by template constants and ABI tests.
    pub(crate) mem_tokens: &'static [QuotientMemTokenSpec],
    /// Minimum adjacent fused-op run length worth compacting.
    pub(crate) run_compaction_min_len: usize,
    /// Number of foreign-field limbs recognized by limb opcodes.
    pub(crate) limb_count: usize,
    /// Number of products in a 7-by-7 pairwise convolution.
    pub(crate) limb_pairwise_terms: usize,
    /// Number of distinct `i + j` coefficients in that convolution.
    pub(crate) limb_pairwise_coeffs: usize,
}

/// Canonical opcode table shared by Rust tests and rendered template constants.
pub(crate) const QUOTIENT_OPCODE_TABLE: &[QuotientOpcodeSpec] = &[
    QuotientOpcodeSpec {
        name: "push_const",
        opcode: Q_OP_PUSH_CONST,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "push_mem_literal",
        opcode: Q_OP_PUSH_MEM_LITERAL,
        byte_len: 1 + QUOTIENT_VM_BYTE_U32_BYTES,
        encoding: QuotientOpcodeEncoding::U32,
    },
    QuotientOpcodeSpec {
        name: "push_mem_token",
        opcode: Q_OP_PUSH_MEM_TOKEN,
        byte_len: 1 + 1,
        encoding: QuotientOpcodeEncoding::U8,
    },
    QuotientOpcodeSpec {
        name: "push_mem_token_offset",
        opcode: Q_OP_PUSH_MEM_TOKEN_OFFSET,
        byte_len: 1 + 1 + QUOTIENT_VM_BYTE_U32_BYTES,
        encoding: QuotientOpcodeEncoding::TokenOffset,
    },
    QuotientOpcodeSpec {
        name: "push_mem_u16",
        opcode: Q_OP_PUSH_MEM_U16,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "add",
        opcode: Q_OP_ADD,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "mul",
        opcode: Q_OP_MUL,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "neg",
        opcode: Q_OP_NEG,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "push_const_u8",
        opcode: Q_OP_PUSH_CONST_U8,
        byte_len: 1 + 1,
        encoding: QuotientOpcodeEncoding::U8,
    },
    QuotientOpcodeSpec {
        name: "fold_main",
        opcode: Q_OP_FOLD_MAIN,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "fold_selector",
        opcode: Q_OP_FOLD_SELECTOR,
        byte_len: 1 + QUOTIENT_VM_BYTE_U24_BYTES,
        encoding: QuotientOpcodeEncoding::U24,
    },
    QuotientOpcodeSpec {
        name: "add_const_u8",
        opcode: Q_OP_ADD_CONST_U8,
        byte_len: 1 + 1,
        encoding: QuotientOpcodeEncoding::U8,
    },
    QuotientOpcodeSpec {
        name: "mul_const_u8",
        opcode: Q_OP_MUL_CONST_U8,
        byte_len: 1 + 1,
        encoding: QuotientOpcodeEncoding::U8,
    },
    QuotientOpcodeSpec {
        name: "add_const",
        opcode: Q_OP_ADD_CONST,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "mul_const",
        opcode: Q_OP_MUL_CONST,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "add_mem_u16",
        opcode: Q_OP_ADD_MEM_U16,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "mul_mem_u16",
        opcode: Q_OP_MUL_MEM_U16,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "add_mul_mem_mem_const_u8",
        opcode: Q_OP_ADD_MUL_MEM_MEM_CONST_U8,
        byte_len: 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1,
        encoding: QuotientOpcodeEncoding::AddMulMemMemConstU8,
    },
    QuotientOpcodeSpec {
        name: "add_mul_const_u8_mem_u16",
        opcode: Q_OP_ADD_MUL_CONST_U8_MEM_U16,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES + 1,
        encoding: QuotientOpcodeEncoding::AddMulConstU8MemU16,
    },
    QuotientOpcodeSpec {
        name: "add_mul_mem_mem",
        opcode: Q_OP_ADD_MUL_MEM_MEM,
        byte_len: 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::AddMulMemMem,
    },
    QuotientOpcodeSpec {
        name: "run_add_mul_mem_mem_const_u8",
        opcode: Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
        byte_len: 0,
        encoding: QuotientOpcodeEncoding::RunAddMulMemMemConstU8,
    },
    QuotientOpcodeSpec {
        name: "run_add_mul_const_u8_mem_u16",
        opcode: Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
        byte_len: 0,
        encoding: QuotientOpcodeEncoding::RunAddMulConstU8MemU16,
    },
    QuotientOpcodeSpec {
        name: "native_permutation",
        opcode: Q_OP_NATIVE_PERMUTATION,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "native_lookup",
        opcode: Q_OP_NATIVE_LOOKUP,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "native_identity",
        opcode: Q_OP_NATIVE_IDENTITY,
        byte_len: 1 + QUOTIENT_VM_BYTE_U16_BYTES,
        encoding: QuotientOpcodeEncoding::U16,
    },
    QuotientOpcodeSpec {
        name: "lin7",
        opcode: Q_OP_LIN7,
        byte_len: 1 + QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES),
        encoding: QuotientOpcodeEncoding::LimbLin,
    },
    QuotientOpcodeSpec {
        name: "bilin7_row",
        opcode: Q_OP_BILIN7_ROW,
        byte_len: 1
            + QUOTIENT_VM_BYTE_U16_BYTES
            + QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES),
        encoding: QuotientOpcodeEncoding::LimbBilinRow,
    },
    QuotientOpcodeSpec {
        name: "bilin7_pairwise",
        opcode: Q_OP_BILIN7_PAIRWISE,
        byte_len: 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_PAIRWISE_COEFFS,
        encoding: QuotientOpcodeEncoding::LimbBilinPairwise,
    },
    QuotientOpcodeSpec {
        name: "modarith7",
        opcode: Q_OP_MODARITH7,
        byte_len: 0,
        encoding: QuotientOpcodeEncoding::LimbModarith7,
    },
    QuotientOpcodeSpec {
        name: "pow5",
        opcode: Q_OP_POW5,
        byte_len: 1,
        encoding: QuotientOpcodeEncoding::None,
    },
    QuotientOpcodeSpec {
        name: "affine_sum",
        opcode: Q_OP_AFFINE_SUM,
        byte_len: 0,
        encoding: QuotientOpcodeEncoding::AffineSum,
    },
];

/// Canonical symbolic-memory-token table shared with the Yul VM.
pub(crate) const QUOTIENT_MEM_TOKEN_TABLE: &[QuotientMemTokenSpec] = &[
    QuotientMemTokenSpec {
        name: "L_0_MPTR",
        token: Q_MEM_L0,
    },
    QuotientMemTokenSpec {
        name: "L_LAST_MPTR",
        token: Q_MEM_L_LAST,
    },
    QuotientMemTokenSpec {
        name: "L_BLIND_MPTR",
        token: Q_MEM_L_BLIND,
    },
    QuotientMemTokenSpec {
        name: "BETA_MPTR",
        token: Q_MEM_BETA,
    },
    QuotientMemTokenSpec {
        name: "GAMMA_MPTR",
        token: Q_MEM_GAMMA,
    },
    QuotientMemTokenSpec {
        name: "X_MPTR",
        token: Q_MEM_X,
    },
    QuotientMemTokenSpec {
        name: "THETA_MPTR",
        token: Q_MEM_THETA,
    },
    QuotientMemTokenSpec {
        name: "TRASH_CHALLENGE_MPTR",
        token: Q_MEM_TRASH_CHALLENGE,
    },
    QuotientMemTokenSpec {
        name: "INSTANCE_EVAL_MPTR",
        token: Q_MEM_INSTANCE_EVAL,
    },
];

/// Complete compact VM ABI description used by docs/tests/template rendering.
pub(crate) const QUOTIENT_VM_SPEC: QuotientVmSpec = QuotientVmSpec {
    opcodes: QUOTIENT_OPCODE_TABLE,
    mem_tokens: QUOTIENT_MEM_TOKEN_TABLE,
    run_compaction_min_len: QUOTIENT_VM_RUN_COMPACTION_MIN_LEN,
    limb_count: QUOTIENT_VM_LIMBS,
    limb_pairwise_terms: QUOTIENT_VM_PAIRWISE_TERMS,
    limb_pairwise_coeffs: QUOTIENT_VM_PAIRWISE_COEFFS,
};

/// Return the VM opcode spec for a stable opcode byte.
pub(crate) fn quotient_opcode_spec(opcode: u8) -> Option<&'static QuotientOpcodeSpec> {
    QUOTIENT_VM_SPEC.opcodes.iter().find(|spec| spec.opcode == opcode)
}

/// Return the fixed byte length of an opcode in byte-oriented encoding.
///
/// Dynamic run opcodes intentionally return `None`; callers that need to walk
/// bytecode containing those forms must decode the run count and operand width.
pub(crate) fn quotient_opcode_byte_len(opcode: u8) -> Option<usize> {
    quotient_opcode_spec(opcode).and_then(|spec| (spec.byte_len != 0).then_some(spec.byte_len))
}

/// Convert a little-endian proof scalar into the big-endian 32-byte EVM word.
///
/// Proof calldata uses scalar-byte order from the host encoding; EVM `mstore`
/// and arithmetic consume canonical big-endian words.
pub(crate) fn scalar_le_to_be_word(bytes: &[u8]) -> [u8; 32] {
    assert_eq!(bytes.len(), 32, "scalar proof element must be 32 bytes");
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(bytes);
    scalar.reverse();
    scalar
}

/// Field-expression AST accepted by the quotient VM builder.
///
/// This is a deliberately tiny subset of Halo2 expressions and generated Yul:
/// constants, verifier-memory loads, and Fr addition/multiplication/negation.
/// Keeping the tree this small makes bytecode lowering auditable and lets the
/// structural limb recognizers operate without depending on gate names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum QuotientExpr {
    /// Native Fr constant encoded as a `U256`.
    Const(U256),
    /// Memory-backed verifier value.
    Mem(QuotientMem),
    /// Fr addition modulo the scalar field.
    Add(Box<QuotientExpr>, Box<QuotientExpr>),
    /// Fr multiplication modulo the scalar field.
    Mul(Box<QuotientExpr>, Box<QuotientExpr>),
    /// Fr negation modulo the scalar field.
    Neg(Box<QuotientExpr>),
}

/// Structural foreign-field limb shapes compressed by dedicated opcodes.
///
/// These are recognized from the expression tree alone. That constraint is
/// important: adding a limb opcode must never make correctness depend on a
/// gate label or on a hand-maintained list of circuit gadgets. If a shape is
/// not recognized exactly, the builder falls back to ordinary Fr VM opcodes.
#[derive(Clone, Debug)]
pub(crate) enum QuotientLimbShape {
    // Structural forms from the Midfall foreign-field chips, not gate-name
    // dispatch. Rust source shapes:
    //   circuits/src/field/foreign/util.rs::sum_exprs
    //   circuits/src/field/foreign/util.rs::pair_wise_prod
    //   circuits/src/field/foreign/params.rs::base_powers
    //   circuits/src/field/foreign/params.rs::double_base_powers
    //
    // These expressions emulate arithmetic modulo a foreign modulus `m`
    // inside the circuit, but the verifier still evaluates the resulting
    // PLONK identity polynomial over the native BLS12-381 scalar field Fr.
    // The coefficients are Fr encodings of base^i mod m or base^(i+j) mod m.
    Lin7 {
        terms: Vec<(U256, u16)>,
    },
    Bilin7Row {
        lhs: u16,
        terms: Vec<(U256, u16)>,
    },
    Bilin7Pairwise {
        lhs_base: u16,
        rhs_base: u16,
        coeffs: Vec<U256>,
    },
}

/// One fused foreign-field/ECC affine identity.
///
/// This is a bundled version of the same structural limb blocks as
/// `QuotientLimbShape`, plus scalar memory terms and an optional outer
/// condition. It deliberately remains expression-shaped rather than
/// gate-name-shaped:
///
/// ```text
/// maybe_cond * (
///     c
///   + sum lin7 blocks
///   + sum row-bilinear blocks
///   + sum pairwise-bilinear blocks
///   + sum scalar_coeff_i * mload(ptr_i)
///   + sum product_coeff_i * mload(lhs_i) * mload(rhs_i)
/// )
/// ```
///
/// Some first-modulus residues reduce to sparse affine product identities with
/// no dense seven-limb block left. Those are still encoded here when they are
/// conditionally gated, which keeps the opcode tied to ModArith-style custom
/// gate checks rather than tiny generic arithmetic snippets.
#[derive(Clone, Debug)]
pub(crate) struct QuotientModarith7Shape {
    cond: Option<u16>,
    constant: U256,
    lin: Vec<Vec<(U256, u16)>>,
    rows: Vec<(u16, Vec<(U256, u16)>)>,
    pairwise: Vec<(u16, u16, Vec<U256>)>,
    mem_terms: Vec<(U256, u16)>,
    product_terms: Vec<(U256, u16, u16)>,
}

/// Compact reference to a verifier memory word.
///
/// Literal pointers are encoded directly when they fit. Tokens represent
/// generated Yul symbols whose concrete address can change with the memory
/// layout; token offsets support structured regions rooted at those symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum QuotientMem {
    /// Absolute memory pointer.
    Literal(u32),
    /// Generated memory symbol token.
    Token(u8),
    /// Generated memory symbol token plus byte offset.
    TokenOffset(u8, u32),
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum QuotientLeaf {
    /// Constant leaf.
    Const(U256),
    /// Memory leaf.
    Mem(QuotientMem),
}

/// Fused `top += product` forms recognized during expression emission.
///
/// These are the most common small arithmetic kernels after sum/product
/// flattening. Encoding them as accumulator operations avoids push/load/mul/add
/// sequences and is still easy to reason about because the VM stack effect is
/// exactly zero.
#[derive(Clone, Copy, Debug)]
pub(crate) enum QuotientProductAdd {
    /// `top += mload(lhs) * mload(rhs) * const`.
    MemMemConstU8 { lhs: u16, rhs: u16, scalar: U256 },
    /// `top += const * mload(ptr)`.
    ConstU8Mem { scalar: U256, ptr: u16 },
    /// `top += mload(lhs) * mload(rhs)`.
    MemMem { lhs: u16, rhs: u16 },
}

/// Lowers quotient identities into VM bytecode and a constant table.
///
/// The builder owns stack-depth accounting and all byte-level encoding. It
/// emits an expression as an isolated stack computation followed by exactly one
/// fold opcode, so identity boundaries are explicit and native callback markers
/// can be interleaved safely.
pub(crate) struct QuotientProgramBuilder {
    // Raw byte-oriented program before run compaction. All stack-depth
    // accounting happens against this stream.
    pub(crate) bytes: Vec<u8>,
    pub(crate) consts: Vec<U256>,
    pub(crate) const_slots: HashMap<U256, u16>,
    pub(crate) vars: HashMap<String, QuotientExpr>,
    pub(crate) stack_depth: usize,
    pub(crate) max_stack: usize,
    pub(crate) limb_vm_ops: bool,
}

impl Default for QuotientProgramBuilder {
    /// Start an empty VM program with the crate's default limb-opcode policy.
    fn default() -> Self {
        Self {
            bytes: Vec::new(),
            consts: Vec::new(),
            const_slots: HashMap::new(),
            vars: HashMap::new(),
            stack_depth: 0,
            max_stack: 0,
            limb_vm_ops: config::DEFAULT_QUOTIENT_LIMB_VM_OPS,
        }
    }
}

impl QuotientProgramBuilder {
    /// Create a builder, optionally enabling limb-specialized opcode emission.
    pub(crate) fn with_limb_vm_ops(enabled: bool) -> Self {
        Self {
            limb_vm_ops: enabled,
            ..Default::default()
        }
    }

    /// Emit one complete quotient identity and its fold target.
    ///
    /// The operand stack is reset at the start and must be empty at the end.
    /// That invariant is the reason callbacks can share the same stream: the
    /// Yul interpreter is allowed to clear `q_top` and reuse `q_sp` whenever a
    /// native marker appears between identities.
    pub(crate) fn identity_expr(
        &mut self,
        expr: &QuotientExpr,
        target: QuotientTarget,
        selector_gap: Option<usize>,
    ) {
        // Each identity is emitted as an isolated stack expression followed by
        // one fold opcode. Native callbacks assert the same empty-stack
        // boundary, which lets the Yul interpreter reset q_sp before them.
        self.vars.clear();
        self.stack_depth = 0;

        self.emit_expr(expr);
        self.fold_identity(target, selector_gap);

        assert_eq!(self.stack_depth, 0, "quotient VM stack leak");
    }

    /// Emit the fold opcode for the completed top-of-stack identity value.
    fn fold_identity(&mut self, target: QuotientTarget, selector_gap: Option<usize>) {
        // Mirrors the Rust `compute_linearization_commitment` y-batch:
        // every emitted identity is first absorbed into the same running
        // power of y, then either accumulated into the fully-evaluated
        // numerator or into the simple-selector bucket.
        match target {
            QuotientTarget::Main => self.op0(Q_OP_FOLD_MAIN),
            QuotientTarget::Selector(idx) => {
                let gap = selector_gap.expect("selector fold gap for selector identity");
                assert!(
                    idx <= u8::MAX as usize,
                    "selector fold selector index exceeds 8 bits"
                );
                assert!(
                    gap <= u16::MAX as usize,
                    "selector fold gap exceeds 16 bits"
                );
                self.bytes.push(Q_OP_FOLD_SELECTOR);
                self.u24((idx << 16) | gap);
                self.pop_stack();
            }
        }
        if matches!(target, QuotientTarget::Main) {
            self.pop_stack();
        }
    }

    /// Emit the native permutation marker.
    ///
    /// The generated Yul callback evaluates the whole permutation block and
    /// performs the same fold side effects that interpreted identities would
    /// have performed one by one at this position.
    pub(crate) fn native_permutation(&mut self) {
        assert_eq!(
            self.stack_depth, 0,
            "native permutation expects empty VM stack"
        );
        // The callback is not an arithmetic stack op: it is a placeholder in
        // the y-batched identity stream. The generated Yul block performs its
        // own scratch writes and fold calls at this exact program position.
        self.bytes.push(Q_OP_NATIVE_PERMUTATION);
    }

    /// Emit the native lookup marker.
    ///
    /// The generated Yul callback evaluates every LogUp lookup identity
    /// (boundary, helper chunks, accumulator) and folds each one in the same
    /// order as the interpreted identity stream.
    pub(crate) fn native_lookup(&mut self) {
        assert_eq!(self.stack_depth, 0, "native lookup expects empty VM stack");
        // Like native permutation, this is a domain-shaped superinstruction:
        // the opcode marks one family in the y-batched stream while the
        // generated callback performs all per-identity arithmetic and folds.
        self.bytes.push(Q_OP_NATIVE_LOOKUP);
    }

    /// Emit a native heavy-identity marker addressed by `native_idx`.
    ///
    /// The marker is an execution-plan choice, not a different identity. Its
    /// callback body is generated from the same `QuotientIdentity` and must
    /// trace and fold exactly once.
    pub(crate) fn native_identity(&mut self, native_idx: usize) {
        assert_eq!(
            self.stack_depth, 0,
            "native identity expects empty VM stack"
        );
        // Native identity callbacks are a bytecode/gas trade: recognized
        // heavy gates stay as generated Yul kernels while the remaining gates
        // fall back to the compact VM program stored in the VK payload.
        self.bytes.push(Q_OP_NATIVE_IDENTITY);
        self.u16(native_idx);
    }

    /// Finalize byte-oriented bytecode after compacting adjacent run opcodes.
    pub(crate) fn finish(self) -> QuotientProgramBuild {
        // `max_stack` is the pure VM operand-stack high-water mark. The memory
        // planner adds callback scratch requirements when callbacks share the
        // same base pointer.
        let bytes = compact_quotient_runs(&self.bytes);
        let validated_max_stack = validate_quotient_program(&bytes)
            .unwrap_or_else(|err| panic!("invalid finalized quotient VM program: {err}"));
        validate_quotient_const_slots(&bytes, self.consts.len())
            .unwrap_or_else(|err| panic!("invalid finalized quotient VM program: {err}"));
        assert_eq!(
            validated_max_stack, self.max_stack,
            "quotient VM physical program stack depth diverged from builder accounting"
        );
        let (used_ops, used_mem_tokens) = quotient_program_usage(&bytes);
        QuotientProgramBuild {
            bytes,
            consts: self.consts,
            max_stack: self.max_stack,
            used_ops,
            used_mem_tokens,
        }
    }

    /// Parse and remember one generated Yul assignment.
    ///
    /// This is the bridge for identities that do not yet have typed
    /// `Expression<Fq>` lowering. Only the evaluator's simple arithmetic subset
    /// is accepted; unsupported syntax is rejected during code generation.
    pub(crate) fn assignment(&mut self, line: &str) {
        let assignment = yul_assignment(line)
            .unwrap_or_else(|| panic!("unsupported quotient assignment: {}", line.trim()));
        let expr = self.parse_expr(&assignment.expr);
        self.vars.insert(assignment.dst, expr);
    }

    /// Parse a generated Yul expression into `QuotientExpr`.
    ///
    /// Supported operations are exactly the Fr operations emitted by
    /// `Evaluator`: `addmod(_, _, r)`, `mulmod(_, _, r)`, `sub(r, _)`,
    /// `mload(_)`, literals, and previously assigned variables.
    pub(crate) fn parse_expr(&self, expr: &str) -> QuotientExpr {
        let expr = expr.trim();
        if let Some(args) = call_args(expr, "addmod") {
            assert_eq!(args.len(), 3, "addmod arity");
            assert_eq!(args[2].trim(), "r", "addmod modulus");
            QuotientExpr::Add(
                Box::new(self.parse_expr(&args[0])),
                Box::new(self.parse_expr(&args[1])),
            )
        } else if let Some(args) = call_args(expr, "mulmod") {
            assert_eq!(args.len(), 3, "mulmod arity");
            assert_eq!(args[2].trim(), "r", "mulmod modulus");
            QuotientExpr::Mul(
                Box::new(self.parse_expr(&args[0])),
                Box::new(self.parse_expr(&args[1])),
            )
        } else if let Some(args) = call_args(expr, "sub") {
            assert_eq!(args.len(), 2, "sub arity");
            assert_eq!(args[0].trim(), "r", "only sub(r, x) is supported");
            QuotientExpr::Neg(Box::new(self.parse_expr(&args[1])))
        } else if let Some(args) = call_args(expr, "mload") {
            assert_eq!(args.len(), 1, "mload arity");
            QuotientExpr::Mem(parse_mem(&args[0]))
        } else if is_literal(expr) {
            QuotientExpr::Const(parse_u256(expr))
        } else {
            self.vars
                .get(expr)
                .cloned()
                .unwrap_or_else(|| panic!("unknown quotient variable: {expr}"))
        }
    }

    /// Emit a `QuotientExpr` using ordinary VM bytecode plus local peepholes.
    ///
    /// The method leaves the expression value on top of the VM stack. It first
    /// tries structural limb compression, then falls back to accumulator-leaf
    /// and fused product-add opcodes before using generic stack add/mul/neg.
    pub(crate) fn emit_expr(&mut self, expr: &QuotientExpr) {
        if self.try_emit_pow5(expr) {
            return;
        }
        if self.try_emit_modarith7_shape(expr) {
            return;
        }
        if self.try_emit_limb_shape(expr) {
            return;
        }
        if self.try_emit_limb_decomposition(expr) {
            return;
        }

        match expr {
            QuotientExpr::Const(value) => {
                self.emit_const(*value);
                self.push_stack();
            }
            QuotientExpr::Mem(QuotientMem::Literal(ptr)) => {
                self.emit_mem_literal(*ptr);
                self.push_stack();
            }
            QuotientExpr::Mem(QuotientMem::Token(token)) => {
                self.bytes.push(Q_OP_PUSH_MEM_TOKEN);
                self.bytes.push(*token);
                self.push_stack();
            }
            QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => {
                self.bytes.push(Q_OP_PUSH_MEM_TOKEN_OFFSET);
                self.bytes.push(*token);
                self.u32(*offset);
                self.push_stack();
            }
            QuotientExpr::Add(lhs, rhs) => {
                if !self.try_emit_add_product(lhs, rhs) && !self.try_emit_add_product(rhs, lhs) {
                    self.emit_binary_expr(
                        lhs,
                        rhs,
                        Q_OP_ADD,
                        Q_OP_ADD_CONST_U8,
                        Q_OP_ADD_CONST,
                        Q_OP_ADD_MEM_U16,
                    );
                }
            }
            QuotientExpr::Mul(lhs, rhs) => {
                self.emit_binary_expr(
                    lhs,
                    rhs,
                    Q_OP_MUL,
                    Q_OP_MUL_CONST_U8,
                    Q_OP_MUL_CONST,
                    Q_OP_MUL_MEM_U16,
                );
            }
            QuotientExpr::Neg(expr) => {
                self.emit_expr(expr);
                self.op0(Q_OP_NEG);
            }
        }
    }

    /// Try to replace a repeated-factor fifth power with one opcode.
    fn try_emit_pow5(&mut self, expr: &QuotientExpr) -> bool {
        let Some(base) = quotient_pow5_base(expr) else {
            return false;
        };
        self.emit_expr(base);
        self.bytes.push(Q_OP_POW5);
        true
    }

    /// Try to extract one limb-specialized subexpression from a larger sum.
    fn try_emit_limb_decomposition(&mut self, expr: &QuotientExpr) -> bool {
        if !self.limb_vm_ops {
            return false;
        }
        let Some((shape, residue, matched)) = quotient_limb_subshape(expr) else {
            return false;
        };
        if !self.limb_shape_has_u8_const_slots(&shape) {
            return false;
        }
        self.reserve_limb_shape_consts(&shape);
        self.emit_expr(&residue);
        // `limb_shape_has_u8_const_slots` was checked against the constant table
        // before `emit_expr(&residue)`. Emitting the residue can insert new
        // constants and push a shape coefficient past a one-byte constant slot,
        // which would panic in `emit_limb_shape`'s `u8::try_from(...).expect(...)`.
        // Re-check against the post-residue table: keep the fused limb opcode
        // only while every coefficient still fits, otherwise emit the matched
        // terms through the generic path (their sum equals the shape's value).
        if self.limb_shape_has_u8_const_slots(&shape) {
            self.emit_limb_shape(shape);
        } else {
            self.emit_affine_terms(&matched);
        }
        self.op_binary(Q_OP_ADD);
        true
    }

    /// Emit `Σ terms[i]` with generic stack ops, leaving one value on the
    /// stack.
    ///
    /// Each entry is one recognized affine/bilinear term (a scaled memory load
    /// or product), so emitting it cannot re-enter the limb-decomposition
    /// peephole, and its coefficients use `emit_const`'s u16-capable slots.
    /// This is the panic-free fallback for a recognized limb shape whose
    /// coefficients no longer fit one-byte constant slots after intervening
    /// emission. The slice is always non-empty (a recognized subshape uses
    /// at least one term).
    fn emit_affine_terms(&mut self, terms: &[QuotientExpr]) {
        for (idx, term) in terms.iter().enumerate() {
            self.emit_expr(term);
            if idx > 0 {
                self.op_binary(Q_OP_ADD);
            }
        }
    }

    /// Try to replace a full expression with one limb-specialized opcode.
    ///
    /// The const-slot preflight is part of the ABI justification: limb opcodes
    /// carry coefficient slots as single bytes, so either every coefficient can
    /// be addressed by `u8` after deterministic insertion or the expression
    /// must use the generic VM path.
    fn try_emit_limb_shape(&mut self, expr: &QuotientExpr) -> bool {
        if !self.limb_vm_ops {
            return false;
        }

        let Some(shape) = quotient_limb_shape(expr) else {
            return false;
        };
        if !self.limb_shape_has_u8_const_slots(&shape) {
            return false;
        }

        self.emit_limb_shape(shape);
        true
    }

    /// Try to replace a whole affine foreign-field/ECC identity with one
    /// dynamic byte-only opcode.
    fn try_emit_modarith7_shape(&mut self, expr: &QuotientExpr) -> bool {
        if !self.limb_vm_ops {
            return false;
        }

        let Some(shape) = quotient_modarith7_shape(expr) else {
            return false;
        };
        if !self.modarith7_shape_has_u8_const_slots(&shape) {
            return false;
        }

        self.emit_modarith7_shape(shape);
        true
    }

    /// Check whether all coefficients of a fused affine limb identity fit
    /// one-byte constant-table slots without mutating the builder.
    fn modarith7_shape_has_u8_const_slots(&self, shape: &QuotientModarith7Shape) -> bool {
        self.peek_u8_const_slots(&modarith7_coeffs(shape)).is_some()
    }

    /// Check whether all coefficients of a recognized limb shape fit `u8`
    /// constant slots without mutating the builder.
    fn limb_shape_has_u8_const_slots(&self, shape: &QuotientLimbShape) -> bool {
        let coeffs = match shape {
            QuotientLimbShape::Lin7 { terms } => terms.iter().map(|(coeff, _)| *coeff).collect(),
            QuotientLimbShape::Bilin7Row { terms, .. } => {
                terms.iter().map(|(coeff, _)| *coeff).collect()
            }
            QuotientLimbShape::Bilin7Pairwise { coeffs, .. } => coeffs.clone(),
        };
        self.peek_u8_const_slots(&coeffs).is_some()
    }

    /// Reserve coefficient slots before residue emission can grow the table.
    fn reserve_limb_shape_consts(&mut self, shape: &QuotientLimbShape) {
        match shape {
            QuotientLimbShape::Lin7 { terms } | QuotientLimbShape::Bilin7Row { terms, .. } => {
                for (coeff, _) in terms {
                    self.const_slot(*coeff);
                }
            }
            QuotientLimbShape::Bilin7Pairwise { coeffs, .. } => {
                for coeff in coeffs {
                    self.const_slot(*coeff);
                }
            }
        }
    }

    /// Emit the byte-level representation of a pre-validated limb shape.
    fn emit_limb_shape(&mut self, shape: QuotientLimbShape) {
        match shape {
            QuotientLimbShape::Lin7 { terms } => {
                // LIN7 is the VM encoding of:
                //   sum_exprs(base_powers, limbs)
                // from foreign-field normalization/multiplication and EC
                // gates. It packs seven limb-evaluation loads and their
                // generated Fr coefficients into one interpreter opcode.
                self.bytes.push(Q_OP_LIN7);
                for (coeff, ptr) in terms {
                    let slot = self.const_slot(coeff);
                    let slot = u8::try_from(slot).expect("lin7 const slot checked");
                    self.bytes.push(slot);
                    self.u16(ptr as usize);
                }
            }
            QuotientLimbShape::Bilin7Row { lhs, terms } => {
                // BILIN7_ROW captures the repeated row shape
                // lhs * sum_i coeff[i] * rhs[i]. It appears after lowering
                // pair_wise_prod slices in foreign-field multiplication and
                // EC slope/tangent/on-curve/lambda-squared identities.
                self.bytes.push(Q_OP_BILIN7_ROW);
                self.u16(lhs as usize);
                for (coeff, rhs) in terms {
                    let slot = self.const_slot(coeff);
                    let slot = u8::try_from(slot).expect("bilin7 row const slot checked");
                    self.bytes.push(slot);
                    self.u16(rhs as usize);
                }
            }
            QuotientLimbShape::Bilin7Pairwise {
                lhs_base,
                rhs_base,
                coeffs,
            } => {
                // BILIN7_PAIRWISE captures the full 7-by-7 convolution:
                //   sum_{i,j} coeff[i+j] * lhs[i] * rhs[j]
                // matching sum_exprs(double_base_powers,
                // pair_wise_prod(lhs, rhs)).
                self.bytes.push(Q_OP_BILIN7_PAIRWISE);
                self.u16(lhs_base as usize);
                self.u16(rhs_base as usize);
                for coeff in coeffs {
                    let slot = self.const_slot(coeff);
                    let slot = u8::try_from(slot).expect("bilin7 pairwise const slot checked");
                    self.bytes.push(slot);
                }
            }
        }
        self.push_stack();
    }

    /// Emit the dynamic byte-level representation of one fused affine
    /// foreign-field/ECC identity.
    fn emit_modarith7_shape(&mut self, shape: QuotientModarith7Shape) {
        self.bytes.push(Q_OP_MODARITH7);

        let mut flags = 0u8;
        if shape.cond.is_some() {
            flags |= Q_MODARITH7_FLAG_COND;
        }
        if shape.constant != U256::ZERO {
            flags |= Q_MODARITH7_FLAG_CONST;
        }
        self.bytes.push(flags);

        if let Some(cond) = shape.cond {
            self.u16(cond as usize);
        }
        if shape.constant != U256::ZERO {
            let slot = self.const_slot(shape.constant);
            let slot = u8::try_from(slot).expect("modarith7 const slot checked");
            self.bytes.push(slot);
        }

        let lin_count = u8::try_from(shape.lin.len()).expect("modarith7 lin count checked");
        let row_count = u8::try_from(shape.rows.len()).expect("modarith7 row count checked");
        let pairwise_count =
            u8::try_from(shape.pairwise.len()).expect("modarith7 pairwise count checked");
        let mem_count = u8::try_from(shape.mem_terms.len()).expect("modarith7 mem count checked");
        let product_count =
            u8::try_from(shape.product_terms.len()).expect("modarith7 product count checked");
        self.bytes.push(lin_count);
        self.bytes.push(row_count);
        self.bytes.push(pairwise_count);
        self.bytes.push(mem_count);
        self.bytes.push(product_count);

        for terms in shape.lin {
            for (coeff, ptr) in terms {
                let slot = self.const_slot(coeff);
                let slot = u8::try_from(slot).expect("modarith7 lin const slot checked");
                self.bytes.push(slot);
                self.u16(ptr as usize);
            }
        }
        for (lhs, terms) in shape.rows {
            self.u16(lhs as usize);
            for (coeff, rhs) in terms {
                let slot = self.const_slot(coeff);
                let slot = u8::try_from(slot).expect("modarith7 row const slot checked");
                self.bytes.push(slot);
                self.u16(rhs as usize);
            }
        }
        for (lhs_base, rhs_base, coeffs) in shape.pairwise {
            self.u16(lhs_base as usize);
            self.u16(rhs_base as usize);
            for coeff in coeffs {
                let slot = self.const_slot(coeff);
                let slot = u8::try_from(slot).expect("modarith7 pairwise const slot checked");
                self.bytes.push(slot);
            }
        }
        for (coeff, ptr) in shape.mem_terms {
            let slot = self.const_slot(coeff);
            let slot = u8::try_from(slot).expect("modarith7 mem const slot checked");
            self.bytes.push(slot);
            self.u16(ptr as usize);
        }
        for (coeff, lhs, rhs) in shape.product_terms {
            let slot = self.const_slot(coeff);
            let slot = u8::try_from(slot).expect("modarith7 product const slot checked");
            self.bytes.push(slot);
            self.u16(lhs as usize);
            self.u16(rhs as usize);
        }

        self.push_stack();
    }

    /// Emit a constant load, choosing the shortest constant-slot operand.
    fn emit_const(&mut self, value: U256) {
        let slot = self.const_slot(value);
        if let Ok(slot) = u8::try_from(slot) {
            self.bytes.push(Q_OP_PUSH_CONST_U8);
            self.bytes.push(slot);
        } else {
            self.bytes.push(Q_OP_PUSH_CONST);
            self.u16(slot as usize);
        }
    }

    /// Emit a memory load, choosing the shortest literal-pointer operand.
    fn emit_mem_literal(&mut self, ptr: u32) {
        if let Ok(ptr) = u16::try_from(ptr) {
            self.bytes.push(Q_OP_PUSH_MEM_U16);
            self.u16(ptr as usize);
        } else {
            self.bytes.push(Q_OP_PUSH_MEM_LITERAL);
            self.u32(ptr);
        }
    }

    /// Try to emit `base + product` as a fused accumulator opcode.
    fn try_emit_add_product(&mut self, base: &QuotientExpr, product: &QuotientExpr) -> bool {
        let mut leaves = Vec::new();
        if !collect_product_leaves(product, &mut leaves) {
            return false;
        }
        let Some(fused) = self.product_add_macro(&leaves) else {
            return false;
        };

        self.reserve_product_add_consts(fused);
        self.emit_expr(base);
        // `product_add_macro` checked the fused scalar against the constant
        // table as it stood *before* `emit_expr(base)`. Emitting `base` can
        // insert new constants and push that scalar past a one-byte constant
        // slot, which would panic in `emit_product_add`'s
        // `u8::try_from(...).expect(...)`. Re-check against the post-`base`
        // table: keep the fused opcode only while the scalar still fits,
        // otherwise add the product through the generic path (its lone scalar
        // goes through `emit_const`, which falls back to a u16 slot).
        if self.product_add_fits_u8_slot(&fused) {
            self.emit_product_add(fused);
        } else {
            self.emit_expr(product);
            self.op_binary(Q_OP_ADD);
        }
        true
    }

    /// Whether the fused product-add scalar (if any) still lands in a one-byte
    /// constant slot given the current constant table.
    fn product_add_fits_u8_slot(&self, product: &QuotientProductAdd) -> bool {
        match *product {
            QuotientProductAdd::MemMemConstU8 { scalar, .. }
            | QuotientProductAdd::ConstU8Mem { scalar, .. } => self.const_fits_u8_slot(scalar),
            QuotientProductAdd::MemMem { .. } => true,
        }
    }

    /// Recognize product leaves that can be encoded as one fused add-mul op.
    ///
    /// The fused forms require literal `u16` memory pointers and, where a
    /// constant is present, a coefficient that can fit a `u8` const slot. Token
    /// memory is kept on the generic path because the fused byte layout stores
    /// raw pointers only.
    fn product_add_macro(&self, leaves: &[QuotientLeaf]) -> Option<QuotientProductAdd> {
        let mut mems = Vec::new();
        let mut consts = Vec::new();
        for leaf in leaves {
            match *leaf {
                QuotientLeaf::Mem(QuotientMem::Literal(ptr)) => {
                    mems.push(u16::try_from(ptr).ok()?);
                }
                QuotientLeaf::Const(value) => {
                    if !self.const_fits_u8_slot(value) {
                        return None;
                    }
                    consts.push(value);
                }
                QuotientLeaf::Mem(QuotientMem::Token(_))
                | QuotientLeaf::Mem(QuotientMem::TokenOffset(_, _)) => return None,
            }
        }

        match (mems.as_slice(), consts.as_slice()) {
            ([lhs, rhs], [scalar]) => Some(QuotientProductAdd::MemMemConstU8 {
                lhs: *lhs,
                rhs: *rhs,
                scalar: *scalar,
            }),
            ([ptr], [scalar]) => Some(QuotientProductAdd::ConstU8Mem {
                scalar: *scalar,
                ptr: *ptr,
            }),
            ([lhs, rhs], []) => Some(QuotientProductAdd::MemMem {
                lhs: *lhs,
                rhs: *rhs,
            }),
            _ => None,
        }
    }

    /// Reserve coefficient slots before another expression can grow the table.
    fn reserve_product_add_consts(&mut self, product: QuotientProductAdd) {
        match product {
            QuotientProductAdd::MemMemConstU8 { scalar, .. }
            | QuotientProductAdd::ConstU8Mem { scalar, .. } => {
                self.const_slot(scalar);
            }
            QuotientProductAdd::MemMem { .. } => {}
        }
    }

    /// Emit one fused add-mul accumulator operation.
    fn emit_product_add(&mut self, product: QuotientProductAdd) {
        match product {
            QuotientProductAdd::MemMemConstU8 { lhs, rhs, scalar } => {
                let slot = self.const_slot(scalar);
                let slot = u8::try_from(slot).expect("const slot checked");
                self.bytes.push(Q_OP_ADD_MUL_MEM_MEM_CONST_U8);
                self.u16(lhs as usize);
                self.u16(rhs as usize);
                self.bytes.push(slot);
            }
            QuotientProductAdd::ConstU8Mem { scalar, ptr } => {
                let slot = self.const_slot(scalar);
                let slot = u8::try_from(slot).expect("const slot checked");
                self.bytes.push(Q_OP_ADD_MUL_CONST_U8_MEM_U16);
                self.u16(ptr as usize);
                self.bytes.push(slot);
            }
            QuotientProductAdd::MemMem { lhs, rhs } => {
                self.bytes.push(Q_OP_ADD_MUL_MEM_MEM);
                self.u16(lhs as usize);
                self.u16(rhs as usize);
            }
        }
    }

    /// Emit a binary expression with accumulator-leaf peepholes.
    ///
    /// If one side is a constant or short memory load, the VM can update the
    /// other side's top-of-stack directly with `ADD_CONST`, `MUL_MEM_U16`, and
    /// related opcodes. Otherwise both operands are pushed and a generic stack
    /// operation combines them.
    fn emit_binary_expr(
        &mut self,
        lhs: &QuotientExpr,
        rhs: &QuotientExpr,
        stack_op: u8,
        const_u8_op: u8,
        const_op: u8,
        mem_u16_op: u8,
    ) {
        if let Some(leaf) = quotient_leaf(rhs) {
            self.emit_expr(lhs);
            if self.emit_acc_leaf(leaf, const_u8_op, const_op, mem_u16_op) {
                return;
            }
            self.emit_expr(rhs);
            self.op_binary(stack_op);
            return;
        }
        if let Some(leaf) = quotient_leaf(lhs) {
            self.emit_expr(rhs);
            if self.emit_acc_leaf(leaf, const_u8_op, const_op, mem_u16_op) {
                return;
            }
            self.emit_expr(lhs);
            self.op_binary(stack_op);
            return;
        }

        self.emit_expr(lhs);
        self.emit_expr(rhs);
        self.op_binary(stack_op);
    }

    /// Try to apply a constant or short-memory accumulator opcode to `q_top`.
    fn emit_acc_leaf(
        &mut self,
        leaf: QuotientLeaf,
        const_u8_op: u8,
        const_op: u8,
        mem_u16_op: u8,
    ) -> bool {
        match leaf {
            QuotientLeaf::Const(value) => {
                let slot = self.const_slot(value);
                if let Ok(slot) = u8::try_from(slot) {
                    self.bytes.push(const_u8_op);
                    self.bytes.push(slot);
                } else {
                    self.bytes.push(const_op);
                    self.u16(slot as usize);
                }
                true
            }
            QuotientLeaf::Mem(QuotientMem::Literal(ptr)) => {
                if let Ok(ptr) = u16::try_from(ptr) {
                    self.bytes.push(mem_u16_op);
                    self.u16(ptr as usize);
                    true
                } else {
                    false
                }
            }
            QuotientLeaf::Mem(QuotientMem::Token(_))
            | QuotientLeaf::Mem(QuotientMem::TokenOffset(_, _)) => false,
        }
    }

    /// Emit a zero-operand opcode.
    fn op0(&mut self, op: u8) {
        self.bytes.push(op);
    }

    /// Emit a binary stack opcode and update stack-depth accounting.
    fn op_binary(&mut self, op: u8) {
        self.bytes.push(op);
        self.pop_stack();
    }

    /// Record one pushed stack value and update the high-water mark.
    fn push_stack(&mut self) {
        self.stack_depth += 1;
        self.max_stack = self.max_stack.max(self.stack_depth);
    }

    /// Record one consumed stack value.
    fn pop_stack(&mut self) {
        self.stack_depth = self.stack_depth.checked_sub(1).expect("quotient VM stack underflow");
    }

    /// Append a big-endian `u16` operand.
    fn u16(&mut self, value: usize) {
        assert!(value <= u16::MAX as usize, "quotient VM u16 overflow");
        self.bytes.extend_from_slice(&(value as u16).to_be_bytes());
    }

    /// Append a big-endian 24-bit operand.
    fn u24(&mut self, value: usize) {
        assert!(value <= 0x00ff_ffff, "quotient VM u24 overflow");
        self.bytes.extend_from_slice(&(value as u32).to_be_bytes()[1..]);
    }

    /// Append a big-endian `u32` operand.
    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    /// Return the stable constant-table slot for `value`, inserting if needed.
    fn const_slot(&mut self, value: U256) -> u16 {
        if let Some(slot) = self.const_slots.get(&value) {
            *slot
        } else {
            let slot = self.consts.len();
            assert!(slot <= u16::MAX as usize, "too many quotient constants");
            self.consts.push(value);
            self.const_slots.insert(value, slot as u16);
            slot as u16
        }
    }

    /// Check whether `value` can be addressed by a one-byte constant slot.
    fn const_fits_u8_slot(&self, value: U256) -> bool {
        self.const_slots.get(&value).is_some_and(|slot| u8::try_from(*slot).is_ok())
            || (!self.const_slots.contains_key(&value) && self.consts.len() <= u8::MAX as usize)
    }

    /// Predict one-byte constant slots for a batch of values without insertion.
    ///
    /// This lets limb opcode recognition fail cleanly before mutating the
    /// constant table, so fallback lowering sees the same builder state it
    /// would have seen if recognition had never been attempted.
    fn peek_u8_const_slots(&self, values: &[U256]) -> Option<Vec<u8>> {
        let mut next_slot = self.consts.len();
        let mut pending = HashMap::new();
        let mut slots = Vec::with_capacity(values.len());
        for value in values {
            let slot = if let Some(slot) = self.const_slots.get(value).copied() {
                slot as usize
            } else if let Some(slot) = pending.get(value).copied() {
                slot
            } else {
                let slot = next_slot;
                next_slot += 1;
                pending.insert(*value, slot);
                slot
            };
            slots.push(u8::try_from(slot).ok()?);
        }
        Some(slots)
    }
}

/// Compact long adjacent fused-op runs in byte-oriented VM encoding.
pub(crate) fn compact_quotient_runs(bytes: &[u8]) -> Vec<u8> {
    // Run compaction is only a byte-encoding optimization. It preserves the
    // logical operation stream by replacing long adjacent fused add-mul ops
    // with one counted opcode followed by the same operands. Mixed linear and
    // bilinear affine runs use a larger superinstruction because addition is
    // commutative and each term only mutates the same accumulator.
    let mut out = Vec::with_capacity(bytes.len());
    let mut idx = 0usize;
    while idx < bytes.len() {
        let op = bytes[idx];
        if is_affine_add_op(op) {
            let run_start = idx;
            let mut term_ops = Vec::new();
            let mut lin_count = 0usize;
            let mut product_count = 0usize;
            while idx < bytes.len() && is_affine_add_op(bytes[idx]) {
                let term_op = bytes[idx];
                let len = quotient_op_len(bytes, idx);
                term_ops.push((term_op, idx + 1, len - 1));
                match term_op {
                    Q_OP_ADD_MUL_CONST_U8_MEM_U16 => lin_count += 1,
                    Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => product_count += 1,
                    _ => {}
                }
                idx += len;
                if lin_count == u16::MAX as usize || product_count == u16::MAX as usize {
                    break;
                }
            }

            if lin_count > 0
                && product_count > 0
                && lin_count + product_count >= QUOTIENT_VM_SPEC.run_compaction_min_len
            {
                out.push(Q_OP_AFFINE_SUM);
                out.extend_from_slice(&(lin_count as u16).to_be_bytes());
                out.extend_from_slice(&(product_count as u16).to_be_bytes());
                for (term_op, term_start, term_len) in &term_ops {
                    if *term_op == Q_OP_ADD_MUL_CONST_U8_MEM_U16 {
                        out.extend_from_slice(&bytes[*term_start..*term_start + *term_len]);
                    }
                }
                for (term_op, term_start, term_len) in &term_ops {
                    if *term_op == Q_OP_ADD_MUL_MEM_MEM_CONST_U8 {
                        out.extend_from_slice(&bytes[*term_start..*term_start + *term_len]);
                    }
                }
            } else if term_ops.len() >= QUOTIENT_VM_SPEC.run_compaction_min_len
                && term_ops.iter().all(|(term_op, _, _)| *term_op == op)
                && matches!(
                    op,
                    Q_OP_ADD_MUL_MEM_MEM_CONST_U8 | Q_OP_ADD_MUL_CONST_U8_MEM_U16
                )
            {
                let run_operands_len = term_ops[0].2;
                let run_op = match op {
                    Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
                    Q_OP_ADD_MUL_CONST_U8_MEM_U16 => Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
                    _ => unreachable!(),
                };
                out.push(run_op);
                out.extend_from_slice(&(term_ops.len() as u16).to_be_bytes());
                for (_, term_start, _) in &term_ops {
                    out.extend_from_slice(&bytes[*term_start..*term_start + run_operands_len]);
                }
            } else {
                out.extend_from_slice(&bytes[run_start..idx]);
            }
        } else {
            let len = quotient_op_len(bytes, idx);
            out.extend_from_slice(&bytes[idx..idx + len]);
            idx += len;
        }
    }
    out
}

/// Whether an opcode contributes a fused affine-add term to the current top.
fn is_affine_add_op(op: u8) -> bool {
    matches!(
        op,
        Q_OP_ADD_MUL_MEM_MEM_CONST_U8 | Q_OP_ADD_MUL_CONST_U8_MEM_U16
    )
}

/// Return opcode and memory-token usage for a finalized quotient program.
///
/// This is a code-size optimization for the VK-specialized interpreter. The
/// generated evaluator only needs switch arms for opcodes that can actually
/// occur in its embedded program; malformed external frames still hit the
/// default revert branch.
pub(crate) fn quotient_program_usage(bytes: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let mut ops = Vec::new();
    let mut mem_tokens = Vec::new();

    for (idx, op, _) in quotient_bytecode_ops(bytes) {
        push_unique_u8(&mut ops, op);
        match op {
            Q_OP_PUSH_MEM_TOKEN => {
                push_unique_u8(&mut mem_tokens, bytes[idx + 1]);
            }
            Q_OP_PUSH_MEM_TOKEN_OFFSET => {
                push_unique_u8(&mut mem_tokens, bytes[idx + 1]);
            }
            _ => {}
        }
    }

    (ops, mem_tokens)
}

/// Insert a byte once and keep the set sorted for deterministic templates.
fn push_unique_u8(values: &mut Vec<u8>, value: u8) {
    if !values.contains(&value) {
        values.push(value);
        values.sort_unstable();
    }
}

/// Decode a finalized byte-oriented quotient program and verify stack safety.
///
/// This is an offline safety check for the VK-pinned program, not a runtime
/// verifier feature. The Yul VM stays lean and assumes codegen emitted a valid
/// stream; this pass proves that assumption before the program is embedded.
pub(crate) fn validate_quotient_program(bytes: &[u8]) -> Result<usize, String> {
    let mut idx = 0usize;
    let mut depth = 0usize;
    let mut max_stack = 0usize;

    while idx < bytes.len() {
        let (op, len) = decode_byte_quotient_instruction(bytes, idx)?;
        apply_quotient_stack_effect(op, idx, &mut depth, &mut max_stack)?;
        idx += len;
    }

    if depth != 0 {
        return Err(format!(
            "quotient VM stack leak at end of program: {depth} value(s) remain"
        ));
    }

    Ok(max_stack)
}

/// Bounds-check every constant-table slot referenced by a finalized program.
///
/// `validate_quotient_program` proves structural and stack safety but never
/// checks that decoded const-table indices fall inside the emitted table. An
/// encoder/planner regression that emits an out-of-range slot (this class has
/// already produced one real bug) would otherwise make the deployed verifier
/// load an arbitrary trailing VK word as a gate coefficient, silently flipping
/// accept/reject. Run this after `validate_quotient_program`, whose byte-length
/// validation guarantees the layout walked here is already in bounds.
pub(crate) fn validate_quotient_const_slots(bytes: &[u8], const_len: usize) -> Result<(), String> {
    let check = |slot: usize, idx: usize| -> Result<(), String> {
        if slot >= const_len {
            return Err(format!(
                "quotient VM const slot {slot} at byte {idx} is outside the {const_len}-entry constant table"
            ));
        }
        Ok(())
    };
    let limb_stride = 1 + QUOTIENT_VM_BYTE_U16_BYTES;

    for (idx, op, _len) in quotient_bytecode_ops(bytes) {
        match op {
            Q_OP_PUSH_CONST | Q_OP_ADD_CONST | Q_OP_MUL_CONST => {
                check(read_u16(bytes, idx + 1) as usize, idx)?;
            }
            Q_OP_PUSH_CONST_U8 | Q_OP_ADD_CONST_U8 | Q_OP_MUL_CONST_U8 => {
                check(bytes[idx + 1] as usize, idx)?;
            }
            Q_OP_ADD_MUL_CONST_U8_MEM_U16 => {
                check(bytes[idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES] as usize, idx)?;
            }
            Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => {
                check(
                    bytes[idx + 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES] as usize,
                    idx,
                )?;
            }
            Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
                let count = read_u16(bytes, idx + 1) as usize;
                let base = idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES;
                let stride = QUOTIENT_VM_BYTE_U16_BYTES + 1;
                for k in 0..count {
                    check(
                        bytes[base + k * stride + QUOTIENT_VM_BYTE_U16_BYTES] as usize,
                        idx,
                    )?;
                }
            }
            Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
                let count = read_u16(bytes, idx + 1) as usize;
                let base = idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES;
                let stride = 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1;
                for k in 0..count {
                    check(
                        bytes[base + k * stride + 2 * QUOTIENT_VM_BYTE_U16_BYTES] as usize,
                        idx,
                    )?;
                }
            }
            Q_OP_LIN7 => {
                for k in 0..QUOTIENT_VM_LIMBS {
                    check(bytes[idx + 1 + k * limb_stride] as usize, idx)?;
                }
            }
            Q_OP_BILIN7_ROW => {
                let base = idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES;
                for k in 0..QUOTIENT_VM_LIMBS {
                    check(bytes[base + k * limb_stride] as usize, idx)?;
                }
            }
            Q_OP_BILIN7_PAIRWISE => {
                let base = idx + 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES;
                for k in 0..QUOTIENT_VM_PAIRWISE_COEFFS {
                    check(bytes[base + k] as usize, idx)?;
                }
            }
            Q_OP_AFFINE_SUM => {
                let lin_count = read_u16(bytes, idx + 1) as usize;
                let product_count = read_u16(bytes, idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES) as usize;
                let mut cursor = idx + 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES;
                for _ in 0..lin_count {
                    check(bytes[cursor + QUOTIENT_VM_BYTE_U16_BYTES] as usize, idx)?;
                    cursor += QUOTIENT_VM_BYTE_U16_BYTES + 1;
                }
                for _ in 0..product_count {
                    check(bytes[cursor + 2 * QUOTIENT_VM_BYTE_U16_BYTES] as usize, idx)?;
                    cursor += 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1;
                }
            }
            Q_OP_MODARITH7 => {
                let mut cursor = idx + 1;
                let flags = bytes[cursor];
                cursor += 1;
                if flags & Q_MODARITH7_FLAG_COND != 0 {
                    cursor += QUOTIENT_VM_BYTE_U16_BYTES;
                }
                if flags & Q_MODARITH7_FLAG_CONST != 0 {
                    check(bytes[cursor] as usize, idx)?;
                    cursor += 1;
                }
                let lin_count = bytes[cursor] as usize;
                let row_count = bytes[cursor + 1] as usize;
                let pairwise_count = bytes[cursor + 2] as usize;
                let mem_count = bytes[cursor + 3] as usize;
                let product_count = bytes[cursor + 4] as usize;
                cursor += 5;
                for _ in 0..lin_count {
                    for _ in 0..QUOTIENT_VM_LIMBS {
                        check(bytes[cursor] as usize, idx)?;
                        cursor += limb_stride;
                    }
                }
                for _ in 0..row_count {
                    cursor += QUOTIENT_VM_BYTE_U16_BYTES;
                    for _ in 0..QUOTIENT_VM_LIMBS {
                        check(bytes[cursor] as usize, idx)?;
                        cursor += limb_stride;
                    }
                }
                for _ in 0..pairwise_count {
                    cursor += 2 * QUOTIENT_VM_BYTE_U16_BYTES;
                    for _ in 0..QUOTIENT_VM_PAIRWISE_COEFFS {
                        check(bytes[cursor] as usize, idx)?;
                        cursor += 1;
                    }
                }
                for _ in 0..mem_count {
                    check(bytes[cursor] as usize, idx)?;
                    cursor += limb_stride;
                }
                for _ in 0..product_count {
                    check(bytes[cursor] as usize, idx)?;
                    cursor += 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES;
                }
            }
            _ => {}
        }
    }

    Ok(())
}

/// One byte range the compact quotient VM is allowed to load from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct QuotientReadWindow {
    /// Stable name used in validation errors.
    pub(crate) name: &'static str,
    /// Start byte offset in verifier memory.
    pub(crate) start: usize,
    /// Length in bytes. Zero-length windows never accept a pointer.
    pub(crate) len: usize,
}

impl QuotientReadWindow {
    /// Whether a full 32-byte `mload` at `ptr` stays inside this window.
    fn contains_word(&self, ptr: usize) -> bool {
        self.len != 0
            && ptr >= self.start
            && ptr.saturating_add(WORD_BYTES) <= self.start.saturating_add(self.len)
    }
}

/// Legal read set for one finalized quotient program.
///
/// Built from the converged memory layout, so it describes the addresses this
/// concrete verifier actually populates before the VM runs.
#[derive(Clone, Debug, Default)]
pub(crate) struct QuotientReadModel {
    /// Ranges the VM may load from.
    pub(crate) windows: Vec<QuotientReadWindow>,
    /// Resolved base address for each symbolic memory token.
    pub(crate) token_bases: Vec<(u8, usize)>,
}

impl QuotientReadModel {
    /// Resolve a symbolic memory token to its generated base address.
    fn token_base(&self, token: u8) -> Option<usize> {
        self.token_bases
            .iter()
            .find_map(|(candidate, base)| (*candidate == token).then_some(*base))
    }

    /// Name the window covering a word-sized load, if any.
    fn window_for(&self, ptr: usize) -> Option<&'static str> {
        self.windows
            .iter()
            .find(|window| window.contains_word(ptr))
            .map(|window| window.name)
    }
}

/// Bounds-check every memory pointer a finalized program loads from.
///
/// `validate_quotient_const_slots` covers constant-table indices; this covers
/// the other half of the operand space. The pointers baked into the bytecode
/// are absolute generated addresses, so an emitter or planner regression that
/// computes one incorrectly makes the deployed verifier read a live challenge,
/// commitment word, or uninitialized scratch as a gate value -- silently
/// flipping accept/reject rather than reverting.
///
/// Note what the render-time certification in [`certify`] does *not*
/// cover here. It compares the bytecode against the `QuotientExpr` tree it was
/// lowered from, and [`reference::QuotientRefMemory`] derives a value
/// from whatever address it is handed, so a pointer that disagrees between the
/// two shows up as a value mismatch. A pointer that is already wrong *in the
/// tree* -- a `Data` or planner bug upstream of the VM -- makes both sides
/// agree on the wrong address and certifies cleanly. This check is what catches
/// that class.
///
/// Run after [`validate_quotient_program`], whose byte-length validation
/// guarantees the operand layout walked here is in bounds.
pub(crate) fn validate_quotient_mem_ptrs(
    bytes: &[u8],
    model: &QuotientReadModel,
) -> Result<(), String> {
    for (idx, op, _len) in quotient_bytecode_ops(bytes) {
        let mut check = |kind: &str, ptr: usize| -> Result<(), String> {
            if !ptr.is_multiple_of(WORD_BYTES) {
                return Err(format!(
                    "quotient VM {kind} pointer {ptr:#x} at byte {idx} is not 32-byte aligned"
                ));
            }
            if model.window_for(ptr).is_none() {
                return Err(format!(
                    "quotient VM {kind} pointer {ptr:#x} at byte {idx} is outside every window \
                     the verifier populates before the quotient VM runs ({})",
                    describe_read_windows(model)
                ));
            }
            Ok(())
        };
        quotient_read_pointers(bytes, idx, op, model, &mut check)?;
    }

    Ok(())
}

/// Render the legal read set for a validation error message.
fn describe_read_windows(model: &QuotientReadModel) -> String {
    model
        .windows
        .iter()
        .map(|window| {
            format!(
                "{}=[{:#x}..{:#x})",
                window.name,
                window.start,
                window.start + window.len
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Visit every memory address one instruction loads from.
///
/// Unlike [`validate_quotient_const_slots`], the fallback arm is an error
/// rather than a no-op: a new opcode with pointer operands that forgets to
/// extend this walker fails the render instead of silently losing its bounds
/// check. `quotient_pointer_walker_covers_every_opcode` pins that the walker is
/// total over `QUOTIENT_OPCODE_TABLE`.
pub(crate) fn quotient_read_pointers(
    bytes: &[u8],
    idx: usize,
    op: u8,
    model: &QuotientReadModel,
    check: &mut impl FnMut(&str, usize) -> Result<(), String>,
) -> Result<(), String> {
    let u16_at = |offset: usize| read_u16(bytes, offset) as usize;
    let u32_at = |offset: usize| {
        u32::from_be_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ]) as usize
    };
    // `const_slot, u16 ptr` -- the LIN7 limb operand and the MODARITH7 mem term.
    let limb_terms = |base: usize, check: &mut dyn FnMut(&str, usize) -> Result<(), String>| {
        for k in 0..QUOTIENT_VM_LIMBS {
            check(
                "limb",
                u16_at(base + k * (1 + QUOTIENT_VM_BYTE_U16_BYTES) + 1),
            )?;
        }
        Ok::<(), String>(())
    };
    // Both pairwise bases are indexed `base + i * 0x20` for seven limbs, so the
    // whole span has to be in range, not just the base word.
    let limb_span =
        |base_ptr: usize, kind: &str, check: &mut dyn FnMut(&str, usize) -> Result<(), String>| {
            for k in 0..QUOTIENT_VM_LIMBS {
                check(kind, base_ptr + k * WORD_BYTES)?;
            }
            Ok::<(), String>(())
        };

    match op {
        // No memory operands.
        Q_OP_PUSH_CONST
        | Q_OP_PUSH_CONST_U8
        | Q_OP_ADD
        | Q_OP_MUL
        | Q_OP_NEG
        | Q_OP_POW5
        | Q_OP_ADD_CONST
        | Q_OP_ADD_CONST_U8
        | Q_OP_MUL_CONST
        | Q_OP_MUL_CONST_U8
        | Q_OP_FOLD_MAIN
        | Q_OP_FOLD_SELECTOR
        | Q_OP_NATIVE_PERMUTATION
        | Q_OP_NATIVE_LOOKUP
        | Q_OP_NATIVE_IDENTITY => Ok(()),

        Q_OP_PUSH_MEM_LITERAL => check("literal", u32_at(idx + 1)),
        Q_OP_PUSH_MEM_U16 | Q_OP_ADD_MEM_U16 | Q_OP_MUL_MEM_U16 => check("u16", u16_at(idx + 1)),

        Q_OP_PUSH_MEM_TOKEN | Q_OP_PUSH_MEM_TOKEN_OFFSET => {
            let token = bytes[idx + 1];
            let base = model.token_base(token).ok_or_else(|| {
                format!(
                    "quotient VM memory token {token:#x} at byte {idx} has no generated base \
                     address in this layout"
                )
            })?;
            let offset = if op == Q_OP_PUSH_MEM_TOKEN_OFFSET {
                u32_at(idx + 2)
            } else {
                0
            };
            check("token", base + offset)
        }

        Q_OP_ADD_MUL_MEM_MEM => {
            check("u16", u16_at(idx + 1))?;
            check("u16", u16_at(idx + 3))
        }
        Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => {
            check("u16", u16_at(idx + 1))?;
            check("u16", u16_at(idx + 3))
        }
        Q_OP_ADD_MUL_CONST_U8_MEM_U16 => check("u16", u16_at(idx + 1)),

        Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
            let count = u16_at(idx + 1);
            let base = idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES;
            let stride = 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1;
            for k in 0..count {
                check("u16", u16_at(base + k * stride))?;
                check(
                    "u16",
                    u16_at(base + k * stride + QUOTIENT_VM_BYTE_U16_BYTES),
                )?;
            }
            Ok(())
        }
        Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
            let count = u16_at(idx + 1);
            let base = idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES;
            let stride = QUOTIENT_VM_BYTE_U16_BYTES + 1;
            for k in 0..count {
                check("u16", u16_at(base + k * stride))?;
            }
            Ok(())
        }
        Q_OP_AFFINE_SUM => {
            let lin_count = u16_at(idx + 1);
            let product_count = u16_at(idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES);
            let mut cursor = idx + 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES;
            for _ in 0..lin_count {
                check("u16", u16_at(cursor))?;
                cursor += QUOTIENT_VM_BYTE_U16_BYTES + 1;
            }
            for _ in 0..product_count {
                check("u16", u16_at(cursor))?;
                check("u16", u16_at(cursor + QUOTIENT_VM_BYTE_U16_BYTES))?;
                cursor += 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1;
            }
            Ok(())
        }

        Q_OP_LIN7 => limb_terms(idx + 1, check),
        Q_OP_BILIN7_ROW => {
            check("u16", u16_at(idx + 1))?;
            limb_terms(idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES, check)
        }
        Q_OP_BILIN7_PAIRWISE => {
            limb_span(u16_at(idx + 1), "pairwise_lhs", check)?;
            limb_span(
                u16_at(idx + 1 + QUOTIENT_VM_BYTE_U16_BYTES),
                "pairwise_rhs",
                check,
            )
        }
        Q_OP_MODARITH7 => {
            let mut cursor = idx + 1;
            let flags = bytes[cursor];
            cursor += 1;
            let cond = if flags & Q_MODARITH7_FLAG_COND != 0 {
                let ptr = u16_at(cursor);
                cursor += QUOTIENT_VM_BYTE_U16_BYTES;
                Some(ptr)
            } else {
                None
            };
            if flags & Q_MODARITH7_FLAG_CONST != 0 {
                cursor += 1;
            }
            let lin_count = bytes[cursor] as usize;
            let row_count = bytes[cursor + 1] as usize;
            let pairwise_count = bytes[cursor + 2] as usize;
            let mem_count = bytes[cursor + 3] as usize;
            let product_count = bytes[cursor + 4] as usize;
            cursor += 5;
            let limb_stride = QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES);
            for _ in 0..lin_count {
                limb_terms(cursor, check)?;
                cursor += limb_stride;
            }
            for _ in 0..row_count {
                check("u16", u16_at(cursor))?;
                cursor += QUOTIENT_VM_BYTE_U16_BYTES;
                limb_terms(cursor, check)?;
                cursor += limb_stride;
            }
            for _ in 0..pairwise_count {
                limb_span(u16_at(cursor), "pairwise_lhs", check)?;
                limb_span(
                    u16_at(cursor + QUOTIENT_VM_BYTE_U16_BYTES),
                    "pairwise_rhs",
                    check,
                )?;
                cursor += 2 * QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_PAIRWISE_COEFFS;
            }
            for _ in 0..mem_count {
                check("u16", u16_at(cursor + 1))?;
                cursor += 1 + QUOTIENT_VM_BYTE_U16_BYTES;
            }
            for _ in 0..product_count {
                check("u16", u16_at(cursor + 1))?;
                check("u16", u16_at(cursor + 1 + QUOTIENT_VM_BYTE_U16_BYTES))?;
                cursor += 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES;
            }
            if let Some(cond) = cond {
                check("modarith_cond", cond)?;
            }
            Ok(())
        }

        _ => Err(format!(
            "quotient VM pointer walker does not handle opcode {op:#x} at byte {idx}; extend \
             `quotient_read_pointers` so the new opcode's memory operands stay bounds-checked"
        )),
    }
}

/// Decode one instruction and validate token operands.
fn decode_byte_quotient_instruction(bytes: &[u8], idx: usize) -> Result<(u8, usize), String> {
    require_quotient_bytes(bytes, idx, 1, "opcode")?;
    let op = bytes[idx];
    let spec = quotient_opcode_spec(op)
        .ok_or_else(|| format!("unknown quotient VM opcode {op:#x} at byte {idx}"))?;
    let len = quotient_byte_instruction_len_checked(bytes, idx)?;

    match op {
        Q_OP_PUSH_MEM_TOKEN => {
            let token = bytes[idx + 1];
            validate_quotient_mem_token(token, idx)?;
        }
        Q_OP_PUSH_MEM_TOKEN_OFFSET => {
            let token = bytes[idx + 1];
            validate_quotient_mem_token(token, idx)?;
        }
        _ => {}
    }

    if len == 0 {
        return Err(format!(
            "quotient VM opcode {} ({op:#x}) decoded to zero length at byte {idx}",
            spec.name
        ));
    }
    Ok((op, len))
}

/// Return one instruction length while checking dynamic operand bounds.
fn quotient_byte_instruction_len_checked(bytes: &[u8], idx: usize) -> Result<usize, String> {
    let op = bytes[idx];
    let len = match op {
        Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
            require_quotient_bytes(bytes, idx, 1 + QUOTIENT_VM_BYTE_U16_BYTES, "run count")?;
            let count = read_u16(bytes, idx + 1) as usize;
            if count == 0 {
                return Err(format!("zero-length quotient VM run at byte {idx}"));
            }
            let payload_len =
                checked_quotient_len_mul(count, 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1, op, idx)?;
            checked_quotient_len_add(1 + QUOTIENT_VM_BYTE_U16_BYTES, payload_len, op, idx)?
        }
        Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
            require_quotient_bytes(bytes, idx, 1 + QUOTIENT_VM_BYTE_U16_BYTES, "run count")?;
            let count = read_u16(bytes, idx + 1) as usize;
            if count == 0 {
                return Err(format!("zero-length quotient VM run at byte {idx}"));
            }
            let payload_len =
                checked_quotient_len_mul(count, QUOTIENT_VM_BYTE_U16_BYTES + 1, op, idx)?;
            checked_quotient_len_add(1 + QUOTIENT_VM_BYTE_U16_BYTES, payload_len, op, idx)?
        }
        Q_OP_AFFINE_SUM => quotient_affine_sum_op_len_checked(bytes, idx)?,
        Q_OP_MODARITH7 => quotient_modarith7_op_len_checked(bytes, idx)?,
        _ => quotient_opcode_byte_len(op)
            .ok_or_else(|| format!("unknown quotient VM opcode {op:#x} at byte {idx}"))?,
    };
    require_quotient_bytes(bytes, idx, len, "instruction")?;
    Ok(len)
}

/// Decode the dynamic `AFFINE_SUM` payload header and byte length.
fn quotient_affine_sum_op_len_checked(bytes: &[u8], idx: usize) -> Result<usize, String> {
    let op = Q_OP_AFFINE_SUM;
    require_quotient_bytes(
        bytes,
        idx,
        1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES,
        "AFFINE_SUM count header",
    )?;
    let lin_count = read_u16(bytes, idx + 1) as usize;
    let product_count = read_u16(bytes, idx + 3) as usize;
    if lin_count == 0 || product_count == 0 {
        return Err(format!(
            "AFFINE_SUM at byte {idx} requires nonzero linear and product counts"
        ));
    }
    let lin_payload = checked_quotient_len_mul(lin_count, QUOTIENT_VM_BYTE_U16_BYTES + 1, op, idx)?;
    let product_payload =
        checked_quotient_len_mul(product_count, 2 * QUOTIENT_VM_BYTE_U16_BYTES + 1, op, idx)?;
    let payload = checked_quotient_len_add(lin_payload, product_payload, op, idx)?;
    checked_quotient_len_add(1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES, payload, op, idx)
}

/// Decode the dynamic `MODARITH7` payload and byte length.
fn quotient_modarith7_op_len_checked(bytes: &[u8], idx: usize) -> Result<usize, String> {
    let op = Q_OP_MODARITH7;
    let mut cursor = idx;
    advance_quotient_cursor(bytes, &mut cursor, 1, op, idx)?; // opcode
    require_quotient_bytes(bytes, cursor, 1, "MODARITH7 flags")?;
    let flags = bytes[cursor];
    if flags & !(Q_MODARITH7_FLAG_COND | Q_MODARITH7_FLAG_CONST) != 0 {
        return Err(format!(
            "MODARITH7 has unknown flag bits {flags:#x} at byte {idx}"
        ));
    }
    advance_quotient_cursor(bytes, &mut cursor, 1, op, idx)?;
    if flags & Q_MODARITH7_FLAG_COND != 0 {
        advance_quotient_cursor(bytes, &mut cursor, QUOTIENT_VM_BYTE_U16_BYTES, op, idx)?;
    }
    if flags & Q_MODARITH7_FLAG_CONST != 0 {
        advance_quotient_cursor(bytes, &mut cursor, 1, op, idx)?;
    }

    require_quotient_bytes(bytes, cursor, 5, "MODARITH7 count header")?;
    let lin_count = bytes[cursor] as usize;
    let row_count = bytes[cursor + 1] as usize;
    let pairwise_count = bytes[cursor + 2] as usize;
    let mem_count = bytes[cursor + 3] as usize;
    let product_count = bytes[cursor + 4] as usize;
    advance_quotient_cursor(bytes, &mut cursor, 5, op, idx)?;

    advance_quotient_cursor(
        bytes,
        &mut cursor,
        checked_quotient_len_mul(
            lin_count,
            QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES),
            op,
            idx,
        )?,
        op,
        idx,
    )?;
    advance_quotient_cursor(
        bytes,
        &mut cursor,
        checked_quotient_len_mul(
            row_count,
            QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES),
            op,
            idx,
        )?,
        op,
        idx,
    )?;
    advance_quotient_cursor(
        bytes,
        &mut cursor,
        checked_quotient_len_mul(
            pairwise_count,
            2 * QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_PAIRWISE_COEFFS,
            op,
            idx,
        )?,
        op,
        idx,
    )?;
    advance_quotient_cursor(
        bytes,
        &mut cursor,
        checked_quotient_len_mul(mem_count, 1 + QUOTIENT_VM_BYTE_U16_BYTES, op, idx)?,
        op,
        idx,
    )?;
    advance_quotient_cursor(
        bytes,
        &mut cursor,
        checked_quotient_len_mul(product_count, 1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES, op, idx)?,
        op,
        idx,
    )?;

    Ok(cursor - idx)
}

/// Apply one opcode's static stack effect during offline validation.
fn apply_quotient_stack_effect(
    op: u8,
    idx: usize,
    depth: &mut usize,
    max_stack: &mut usize,
) -> Result<(), String> {
    match op {
        Q_OP_PUSH_CONST
        | Q_OP_PUSH_MEM_LITERAL
        | Q_OP_PUSH_MEM_TOKEN
        | Q_OP_PUSH_MEM_TOKEN_OFFSET
        | Q_OP_PUSH_MEM_U16
        | Q_OP_PUSH_CONST_U8
        | Q_OP_LIN7
        | Q_OP_BILIN7_ROW
        | Q_OP_BILIN7_PAIRWISE
        | Q_OP_MODARITH7 => {
            *depth = depth
                .checked_add(1)
                .ok_or_else(|| format!("quotient VM stack depth overflow at byte {idx}"))?;
            *max_stack = (*max_stack).max(*depth);
        }
        Q_OP_ADD | Q_OP_MUL => {
            require_quotient_stack_depth(op, idx, *depth, 2)?;
            *depth -= 1;
        }
        Q_OP_NEG
        | Q_OP_ADD_CONST_U8
        | Q_OP_MUL_CONST_U8
        | Q_OP_ADD_CONST
        | Q_OP_MUL_CONST
        | Q_OP_ADD_MEM_U16
        | Q_OP_MUL_MEM_U16
        | Q_OP_ADD_MUL_MEM_MEM_CONST_U8
        | Q_OP_ADD_MUL_CONST_U8_MEM_U16
        | Q_OP_ADD_MUL_MEM_MEM
        | Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8
        | Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16
        | Q_OP_AFFINE_SUM
        | Q_OP_POW5 => {
            require_quotient_stack_depth(op, idx, *depth, 1)?;
        }
        Q_OP_FOLD_MAIN | Q_OP_FOLD_SELECTOR => {
            if *depth != 1 {
                return Err(format!(
                    "quotient VM stack boundary error at byte {idx}: opcode {op:#x} requires exactly 1 stack value, found {depth}"
                ));
            }
            *depth = 0;
        }
        Q_OP_NATIVE_PERMUTATION | Q_OP_NATIVE_LOOKUP | Q_OP_NATIVE_IDENTITY => {
            if *depth != 0 {
                return Err(format!(
                    "quotient VM native callback at byte {idx}: opcode {op:#x} requires an empty stack, found {depth}"
                ));
            }
        }
        _ => {
            return Err(format!(
                "unknown quotient VM opcode {op:#x} reached stack validator at byte {idx}"
            ));
        }
    }
    Ok(())
}

/// Require at least `required` stack values before consuming operands.
fn require_quotient_stack_depth(
    op: u8,
    idx: usize,
    depth: usize,
    required: usize,
) -> Result<(), String> {
    if depth < required {
        return Err(format!(
            "quotient VM stack underflow at byte {idx}: opcode {op:#x} requires {required} stack value(s), found {depth}"
        ));
    }
    Ok(())
}

/// Reject symbolic memory tokens unknown to this VM version.
fn validate_quotient_mem_token(token: u8, idx: usize) -> Result<(), String> {
    if QUOTIENT_VM_SPEC.mem_tokens.iter().any(|spec| spec.token == token) {
        Ok(())
    } else {
        Err(format!(
            "unknown quotient VM memory token {token:#x} at byte {idx}"
        ))
    }
}

/// Check that an instruction operand range fits inside the bytecode.
fn require_quotient_bytes(
    bytes: &[u8],
    idx: usize,
    len: usize,
    context: &str,
) -> Result<(), String> {
    let end = idx
        .checked_add(len)
        .ok_or_else(|| format!("quotient VM {context} length overflows at byte {idx}"))?;
    if end > bytes.len() {
        return Err(format!(
            "truncated quotient VM {context} at byte {idx}: need {len} byte(s), program has {} byte(s) remaining",
            bytes.len().saturating_sub(idx)
        ));
    }
    Ok(())
}

/// Advance a dynamic-instruction cursor after bounds-checking the range.
fn advance_quotient_cursor(
    bytes: &[u8],
    cursor: &mut usize,
    amount: usize,
    op: u8,
    op_idx: usize,
) -> Result<(), String> {
    require_quotient_bytes(bytes, *cursor, amount, "dynamic instruction operand")?;
    *cursor = cursor.checked_add(amount).ok_or_else(|| {
        format!("quotient VM opcode {op:#x} length overflows while decoding byte {op_idx}")
    })?;
    Ok(())
}

/// Checked multiplication for derived instruction lengths.
fn checked_quotient_len_mul(lhs: usize, rhs: usize, op: u8, idx: usize) -> Result<usize, String> {
    lhs.checked_mul(rhs).ok_or_else(|| {
        format!("quotient VM opcode {op:#x} length multiplication overflows at byte {idx}")
    })
}

/// Checked addition for derived instruction lengths.
fn checked_quotient_len_add(lhs: usize, rhs: usize, op: u8, idx: usize) -> Result<usize, String> {
    lhs.checked_add(rhs).ok_or_else(|| {
        format!("quotient VM opcode {op:#x} length addition overflows at byte {idx}")
    })
}

/// Read a big-endian `u16` operand from bytecode.
pub(crate) fn read_u16(bytes: &[u8], idx: usize) -> u16 {
    u16::from_be_bytes(bytes[idx..idx + 2].try_into().expect("u16 quotient operand"))
}

/// Read a big-endian `u32` operand from bytecode.
#[cfg(test)]
pub(crate) fn read_u32(bytes: &[u8], idx: usize) -> u32 {
    u32::from_be_bytes(bytes[idx..idx + 4].try_into().expect("u32 quotient operand"))
}

/// Canonical key for structural expression matching and deduplication.
///
/// Addition and multiplication are keyed commutatively because all arithmetic
/// is over Fr and these rewrites do not alter evaluation order side effects:
/// `QuotientExpr` has no side effects.
pub(crate) fn quotient_expr_key(expr: &QuotientExpr) -> String {
    match expr {
        QuotientExpr::Const(value) => format!("c:{value:x}"),
        QuotientExpr::Mem(QuotientMem::Literal(ptr)) => format!("m:{ptr:x}"),
        QuotientExpr::Mem(QuotientMem::Token(token)) => format!("t:{token:x}"),
        QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => {
            format!("to:{token:x}:{offset:x}")
        }
        QuotientExpr::Add(lhs, rhs) => quotient_commutative_expr_key("a", lhs, rhs),
        QuotientExpr::Mul(lhs, rhs) => quotient_commutative_expr_key("u", lhs, rhs),
        QuotientExpr::Neg(inner) => format!("n:{}", quotient_expr_key(inner)),
    }
}

/// Resolve a generated Yul memory symbol name to its compact token.
pub(crate) fn quotient_mem_token_from_name(name: &str) -> Option<u8> {
    QUOTIENT_MEM_TOKEN_TABLE
        .iter()
        .find_map(|spec| (spec.name == name).then_some(spec.token))
}

/// Environment needed to lower Halo2 `Expression<Fq>` leaves.
///
/// The VM lowerer is independent of the concrete verifier memory layout; this
/// trait supplies the memory-backed expression for each kind of query.
pub(crate) trait QuotientExpressionEnv {
    /// Lower a selector leaf.
    fn selector(&self, selector: Selector) -> QuotientExpr;
    /// Lower a fixed-column query leaf.
    fn fixed(&self, column_index: usize, rotation: i32) -> QuotientExpr;
    /// Lower an advice-column query leaf.
    fn advice(&self, column_index: usize, rotation: i32) -> QuotientExpr;
    /// Lower an instance-column query leaf.
    fn instance(&self, column_index: usize, rotation: i32) -> QuotientExpr;
    /// Lower a challenge leaf.
    fn challenge(&self, index: usize) -> QuotientExpr;
}

/// Lower a Halo2 expression into the compact quotient AST.
pub(crate) fn quotient_expr_from_expression<E: QuotientExpressionEnv>(
    env: &E,
    expression: &Expression<Fq>,
) -> QuotientExpr {
    expression.evaluate(
        &|scalar| QuotientExpr::Const(fe_to_u256::<Fq>(&scalar)),
        &|selector| env.selector(selector),
        &|query| env.fixed(query.column_index(), query.rotation().0),
        &|query| env.advice(query.column_index(), query.rotation().0),
        &|query| env.instance(query.column_index(), query.rotation().0),
        &|challenge| env.challenge(challenge.index()),
        &|inner| QuotientExpr::Neg(Box::new(inner)),
        &|lhs, rhs| QuotientExpr::Add(Box::new(lhs), Box::new(rhs)),
        &|lhs, rhs| QuotientExpr::Mul(Box::new(lhs), Box::new(rhs)),
        &|inner, scalar| {
            QuotientExpr::Mul(
                Box::new(inner),
                Box::new(QuotientExpr::Const(fe_to_u256::<Fq>(&scalar))),
            )
        },
    )
}

/// Production expression environment backed by generated verifier data.
pub(crate) struct DataQuotientExpressionEnv<'a> {
    /// Constraint-system metadata used to classify selectors and instances.
    pub(crate) meta: &'a ConstraintSystemMeta,
    /// Concrete generated memory locations for proof/VK/challenge values.
    pub(crate) data: &'a Data,
}

impl QuotientExpressionEnv for DataQuotientExpressionEnv<'_> {
    /// Reject virtual selectors after selector-to-fixed conversion.
    fn selector(&self, _selector: Selector) -> QuotientExpr {
        panic!("virtual selectors must be removed before quotient lowering")
    }

    /// Lower a fixed query, synthesizing simple selectors as constant one.
    fn fixed(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        if self.meta.simple_selector_cols.contains(&column_index) {
            QuotientExpr::Const(U256::from(1u64))
        } else {
            word_to_quotient_expr(
                *self
                    .data
                    .fixed_evals
                    .get(&(column_index, rotation))
                    .expect("fixed eval present"),
            )
        }
    }

    /// Lower an advice query to a memory-backed eval word.
    fn advice(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        word_to_quotient_expr(
            *self
                .data
                .advice_evals
                .get(&(column_index, rotation))
                .expect("advice eval present"),
        )
    }

    /// Lower an instance query from proof evals or local instance evaluation.
    fn instance(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        if column_index < self.meta.num_committed_instances {
            word_to_quotient_expr(
                *self
                    .data
                    .committed_instance_evals
                    .get(&(column_index, rotation))
                    .expect("committed instance eval present"),
            )
        } else {
            // The builder rejects rotated instance queries before lowering, so
            // the direct public-input column always uses the one local
            // Lagrange evaluation computed for `Rotation::cur()`.
            //
            // Hard assert (not debug_assert): `debug_assert` compiles out in
            // release, and this is the last line of defense far from the
            // constructor guard (builder/api.rs). Substituting the Rotation::cur
            // eval for a rotated query would silently emit a verifier that
            // evaluates the gate with instance(x) instead of instance(x*w^k),
            // enforcing a different quotient identity than the circuit. Fail
            // closed, matching word_to_quotient_expr / ptr_to_quotient_mem.
            assert_eq!(
                rotation, 0,
                "rotated public instance query reached lowering"
            );
            word_to_quotient_expr(self.data.instance_eval)
        }
    }

    /// Lower a user challenge to its memory-backed word.
    fn challenge(&self, index: usize) -> QuotientExpr {
        word_to_quotient_expr(self.data.challenges[index])
    }
}

/// Convert a memory-backed `Word` into a quotient memory load expression.
pub(crate) fn word_to_quotient_expr(word: Word) -> QuotientExpr {
    assert_eq!(
        word.loc(),
        Location::Memory,
        "quotient expressions can only load memory-backed words"
    );
    QuotientExpr::Mem(ptr_to_quotient_mem(word.ptr()))
}

/// Convert a generated memory pointer into the compact VM pointer form.
pub(crate) fn ptr_to_quotient_mem(ptr: Ptr) -> QuotientMem {
    assert_eq!(
        ptr.loc(),
        Location::Memory,
        "quotient expressions can only load memory-backed words"
    );
    match ptr.value() {
        Value::Integer(offset) => {
            // Checked conversion: Value offsets are isize, so `offset as u32`
            // would silently wrap for a negative or > u32::MAX offset and make
            // the VM mload an unrelated address (a verifier computing the
            // quotient numerator from the wrong memory word, with no build-time
            // diagnostic). Fail loudly instead, like the other narrowing casts
            // in this file (u16::try_from, u8::try_from).
            let offset = u32::try_from(offset)
                .expect("quotient memory pointer must be a non-negative offset that fits in u32");
            // Every address the quotient VM reads is a 32-byte word slot (the
            // layout allocates in WORD_BYTES units and all eval/challenge/VK/
            // scratch handles are word multiples). A non-word-aligned literal
            // pointer signals a truncated/mis-encoded address that would make
            // the VM mload a straddling window; reject it at the single
            // construction choke point rather than emit a corrupt verifier.
            assert!(
                (offset as usize).is_multiple_of(WORD_BYTES),
                "quotient memory pointer {offset:#x} is not 32-byte word aligned"
            );
            QuotientMem::Literal(offset)
        }
        Value::Identifier(name, offset) => {
            let offset = u32::try_from(offset).expect(
                "quotient memory token offset must be a non-negative offset that fits in u32",
            );
            assert!(
                (offset as usize).is_multiple_of(WORD_BYTES),
                "quotient memory token offset {offset:#x} is not 32-byte word aligned"
            );
            let token = quotient_mem_token_from_name(name)
                .unwrap_or_else(|| panic!("unsupported quotient memory token: {name}"));
            if offset == 0 {
                QuotientMem::Token(token)
            } else {
                QuotientMem::TokenOffset(token, offset)
            }
        }
    }
}

/// Canonical key helper for commutative binary operations.
pub(crate) fn quotient_commutative_expr_key(
    op: &str,
    lhs: &QuotientExpr,
    rhs: &QuotientExpr,
) -> String {
    let lhs = quotient_expr_key(lhs);
    let rhs = quotient_expr_key(rhs);
    if lhs <= rhs {
        format!("{op}:{lhs}:{rhs}")
    } else {
        format!("{op}:{rhs}:{lhs}")
    }
}

/// Byte length of the opcode at `idx`.
///
/// Fixed-width opcodes are read from the spec table; byte-only run and
/// MODARITH7 opcodes decode their embedded counts.
pub(crate) fn quotient_op_len(bytes: &[u8], idx: usize) -> usize {
    let op = bytes[idx];
    match op {
        Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
            1 + QUOTIENT_VM_BYTE_U16_BYTES
                + (read_u16(bytes, idx + 1) as usize) * (2 * QUOTIENT_VM_BYTE_U16_BYTES + 1)
        }
        Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
            1 + QUOTIENT_VM_BYTE_U16_BYTES
                + (read_u16(bytes, idx + 1) as usize) * (QUOTIENT_VM_BYTE_U16_BYTES + 1)
        }
        Q_OP_AFFINE_SUM => quotient_affine_sum_op_len(bytes, idx),
        Q_OP_MODARITH7 => quotient_modarith7_op_len(bytes, idx),
        _ => quotient_opcode_byte_len(op)
            .unwrap_or_else(|| panic!("unknown quotient op {op:#x} at byte {idx}")),
    }
}

/// Decode `AFFINE_SUM` length in trusted/internal bytecode walks.
fn quotient_affine_sum_op_len(bytes: &[u8], idx: usize) -> usize {
    let lin_count = read_u16(bytes, idx + 1) as usize;
    let product_count = read_u16(bytes, idx + 3) as usize;
    1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES
        + lin_count * (QUOTIENT_VM_BYTE_U16_BYTES + 1)
        + product_count * (2 * QUOTIENT_VM_BYTE_U16_BYTES + 1)
}

/// Decode `MODARITH7` length in trusted/internal bytecode walks.
fn quotient_modarith7_op_len(bytes: &[u8], idx: usize) -> usize {
    let mut cursor = idx + 1;
    let flags = bytes[cursor];
    cursor += 1;
    if flags & Q_MODARITH7_FLAG_COND != 0 {
        cursor += QUOTIENT_VM_BYTE_U16_BYTES;
    }
    if flags & Q_MODARITH7_FLAG_CONST != 0 {
        cursor += 1;
    }
    let lin_count = bytes[cursor] as usize;
    let row_count = bytes[cursor + 1] as usize;
    let pairwise_count = bytes[cursor + 2] as usize;
    let mem_count = bytes[cursor + 3] as usize;
    let product_count = bytes[cursor + 4] as usize;
    cursor += 5;
    cursor += lin_count * QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES);
    cursor += row_count
        * (QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_LIMBS * (1 + QUOTIENT_VM_BYTE_U16_BYTES));
    cursor += pairwise_count * (2 * QUOTIENT_VM_BYTE_U16_BYTES + QUOTIENT_VM_PAIRWISE_COEFFS);
    cursor += mem_count * (1 + QUOTIENT_VM_BYTE_U16_BYTES);
    cursor += product_count * (1 + 2 * QUOTIENT_VM_BYTE_U16_BYTES);
    cursor - idx
}

/// Iterate over decoded byte-oriented quotient instructions.
///
/// This is intentionally lightweight: safety validation still lives in
/// `validate_quotient_program`, while codegen-side metrics can share the same
/// offset walk instead of open-coding counters.
pub(crate) fn quotient_bytecode_ops(bytes: &[u8]) -> QuotientBytecodeOps<'_> {
    QuotientBytecodeOps { bytes, idx: 0 }
}

/// Iterator over `(offset, opcode, byte_len)` triples for a finalized program.
pub(crate) struct QuotientBytecodeOps<'a> {
    bytes: &'a [u8],
    idx: usize,
}

impl Iterator for QuotientBytecodeOps<'_> {
    /// Offset, opcode byte, and decoded byte length.
    type Item = (usize, u8, usize);

    /// Return the next decoded opcode span.
    fn next(&mut self) -> Option<Self::Item> {
        (self.idx < self.bytes.len()).then(|| {
            let idx = self.idx;
            let op = self.bytes[idx];
            let len = quotient_op_len(self.bytes, idx);
            self.idx += len;
            (idx, op, len)
        })
    }
}

/// Return the leaf form of an expression, if it has no arithmetic children.
pub(crate) fn quotient_leaf(expr: &QuotientExpr) -> Option<QuotientLeaf> {
    match expr {
        QuotientExpr::Const(value) => Some(QuotientLeaf::Const(*value)),
        QuotientExpr::Mem(mem) => Some(QuotientLeaf::Mem(*mem)),
        QuotientExpr::Add(_, _) | QuotientExpr::Mul(_, _) | QuotientExpr::Neg(_) => None,
    }
}

/// Flatten a pure multiplication tree into constant/memory leaves.
///
/// This intentionally rejects sums and negations. Additive structure is handled
/// by sum collection or by the generic emitter; fused product-add opcodes need
/// a product that can be encoded directly.
pub(crate) fn collect_product_leaves(expr: &QuotientExpr, leaves: &mut Vec<QuotientLeaf>) -> bool {
    match expr {
        QuotientExpr::Mul(lhs, rhs) => {
            collect_product_leaves(lhs, leaves) && collect_product_leaves(rhs, leaves)
        }
        QuotientExpr::Const(_) | QuotientExpr::Mem(_) => {
            if let Some(leaf) = quotient_leaf(expr) {
                leaves.push(leaf);
                true
            } else {
                false
            }
        }
        QuotientExpr::Add(_, _) | QuotientExpr::Neg(_) => false,
    }
}

/// Flatten multiplication nodes while keeping additive subexpressions whole.
fn collect_product_expr_factors<'a>(expr: &'a QuotientExpr, factors: &mut Vec<&'a QuotientExpr>) {
    match expr {
        QuotientExpr::Mul(lhs, rhs) => {
            collect_product_expr_factors(lhs, factors);
            collect_product_expr_factors(rhs, factors);
        }
        QuotientExpr::Const(_)
        | QuotientExpr::Mem(_)
        | QuotientExpr::Add(_, _)
        | QuotientExpr::Neg(_) => {
            factors.push(expr);
        }
    }
}

/// Construct an addition node without applying algebraic simplification.
fn quotient_sum_expr(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Add(Box::new(lhs), Box::new(rhs))
}

/// Attach a scalar coefficient to a term, eliding multiplication by one.
fn quotient_scaled_term_expr(coeff: Fq, expr: QuotientExpr) -> QuotientExpr {
    if coeff == Fq::ONE {
        expr
    } else {
        QuotientExpr::Mul(
            Box::new(QuotientExpr::Const(quotient_fq_to_u256(coeff))),
            Box::new(expr),
        )
    }
}

/// Recognize any supported seven-limb foreign-field quotient shape.
pub(crate) fn quotient_limb_shape(expr: &QuotientExpr) -> Option<QuotientLimbShape> {
    // Recover foreign-field limb algebra from the generic `QuotientExpr`
    // tree. This deliberately does not look at gate names: the Rust verifier
    // source of truth remains
    // proofs/src/plonk/mod.rs::partially_evaluate_identities, which evaluates
    // `vk.cs.gates` expression trees in order. The recognizer only changes how
    // obvious `sum_exprs` / `pair_wise_prod` shapes are encoded for Solidity.
    let mut terms = Vec::new();
    if !collect_quotient_sum_terms(expr, Fq::ONE, &mut terms) {
        return None;
    }
    terms.retain(|(coeff, _)| *coeff != Fq::ZERO);

    try_quotient_bilin7_pairwise_shape(&terms)
        .or_else(|| try_quotient_bilin7_row_shape(&terms))
        .or_else(|| try_quotient_lin7_shape(&terms))
}

/// Return the repeated base for a structural fifth power.
pub(crate) fn quotient_pow5_base(expr: &QuotientExpr) -> Option<&QuotientExpr> {
    let mut factors = Vec::with_capacity(5);
    collect_product_expr_factors(expr, &mut factors);
    if factors.len() != 5 {
        return None;
    }
    let first_key = quotient_expr_key(factors[0]);
    factors
        .iter()
        .all(|factor| quotient_expr_key(factor) == first_key)
        .then_some(factors[0])
}

/// Extract one limb shape from a larger affine sum and return the residue.
pub(crate) fn quotient_limb_subshape(
    expr: &QuotientExpr,
) -> Option<(QuotientLimbShape, QuotientExpr, Vec<QuotientExpr>)> {
    let mut terms = Vec::new();
    let mut constant = Fq::ZERO;
    if !collect_quotient_affine_terms(expr, Fq::ONE, &mut terms, &mut constant) {
        return None;
    }
    terms.retain(|(coeff, _)| *coeff != Fq::ZERO);
    if terms.len() <= QUOTIENT_VM_LIMBS && constant == Fq::ZERO {
        return None;
    }

    let (shape, used) = try_quotient_bilin7_pairwise_subshape(&terms)
        .or_else(|| try_quotient_bilin7_row_subshape(&terms))
        .or_else(|| try_quotient_lin7_subshape(&terms))?;
    if used.is_empty() || (used.len() == terms.len() && constant == Fq::ZERO) {
        return None;
    }

    // Split the affine terms into the residue (unused terms plus the constant)
    // and the matched terms that reconstruct `shape` as a plain sum. The matched
    // terms are the panic-free fallback for `emit_limb_shape`: their sum equals
    // the fused opcode's value, but each is a single scaled load/product that
    // uses u16-capable constant loads.
    let used = used.into_iter().collect::<HashSet<_>>();
    let mut residue = QuotientExpr::Const(quotient_fq_to_u256(constant));
    let mut matched = Vec::with_capacity(used.len());
    for (idx, (coeff, term)) in terms.into_iter().enumerate() {
        let scaled = quotient_scaled_term_expr(coeff, (*term).clone());
        if used.contains(&idx) {
            matched.push(scaled);
        } else {
            residue = quotient_sum_expr(residue, scaled);
        }
    }
    Some((shape, residue, matched))
}

/// Recognize a whole affine foreign-field/ECC identity that can be evaluated
/// by the dynamic `MODARITH7` opcode.
pub(crate) fn quotient_modarith7_shape(expr: &QuotientExpr) -> Option<QuotientModarith7Shape> {
    if let Some((cond, inner)) = quotient_condition_factor(expr) {
        if let Some(shape) = quotient_modarith7_affine_shape(Some(cond), &inner) {
            return Some(shape);
        }
    }
    quotient_modarith7_affine_shape(None, expr)
}

/// Split `cond * inner` when `cond` is a literal memory load, moving any scalar
/// factor attached to `cond` into `inner`.
fn quotient_condition_factor(expr: &QuotientExpr) -> Option<(u16, QuotientExpr)> {
    let QuotientExpr::Mul(lhs, rhs) = expr else {
        return None;
    };

    if let Some((coeff, ptr)) = quotient_mem_term(lhs) {
        return Some((ptr, quotient_scaled_term_expr(coeff, rhs.as_ref().clone())));
    }
    if let Some((coeff, ptr)) = quotient_mem_term(rhs) {
        return Some((ptr, quotient_scaled_term_expr(coeff, lhs.as_ref().clone())));
    }
    None
}

/// Recognize a mixed affine form after any outer condition factor has been
/// separated.
fn quotient_modarith7_affine_shape(
    cond: Option<u16>,
    expr: &QuotientExpr,
) -> Option<QuotientModarith7Shape> {
    let mut terms = Vec::new();
    let mut constant = Fq::ZERO;
    if !collect_quotient_affine_terms(expr, Fq::ONE, &mut terms, &mut constant) {
        return None;
    }
    terms.retain(|(coeff, _)| *coeff != Fq::ZERO);

    let mut lin = Vec::new();
    let mut rows = Vec::new();
    let mut pairwise = Vec::new();

    loop {
        if let Some((shape, used)) = try_quotient_bilin7_pairwise_subshape(&terms) {
            if used.is_empty() {
                break;
            }
            if let QuotientLimbShape::Bilin7Pairwise {
                lhs_base,
                rhs_base,
                coeffs,
            } = shape
            {
                pairwise.push((lhs_base, rhs_base, coeffs));
            } else {
                unreachable!("pairwise recognizer returned non-pairwise shape");
            }
            remove_quotient_terms(&mut terms, &used);
            continue;
        }
        if let Some((shape, used)) = try_quotient_factored_bilin7_row_subshape(&terms) {
            if used.is_empty() {
                break;
            }
            if let QuotientLimbShape::Bilin7Row { lhs, terms } = shape {
                rows.push((lhs, terms));
            } else {
                unreachable!("factored row recognizer returned non-row shape");
            }
            remove_quotient_terms(&mut terms, &used);
            continue;
        }
        if let Some((shape, used)) = try_quotient_bilin7_row_subshape(&terms) {
            if used.is_empty() {
                break;
            }
            if let QuotientLimbShape::Bilin7Row { lhs, terms } = shape {
                rows.push((lhs, terms));
            } else {
                unreachable!("row recognizer returned non-row shape");
            }
            remove_quotient_terms(&mut terms, &used);
            continue;
        }
        if let Some((shape, used)) = try_quotient_lin7_subshape(&terms) {
            if used.is_empty() {
                break;
            }
            if let QuotientLimbShape::Lin7 { terms } = shape {
                lin.push(terms);
            } else {
                unreachable!("linear recognizer returned non-linear shape");
            }
            remove_quotient_terms(&mut terms, &used);
            continue;
        }
        break;
    }

    if lin.len() > u8::MAX as usize
        || rows.len() > u8::MAX as usize
        || pairwise.len() > u8::MAX as usize
    {
        return None;
    }

    let mut grouped_mem = Vec::<(u16, Fq)>::new();
    let mut grouped_products = Vec::<(u16, u16, Fq)>::new();
    for (coeff, term) in terms {
        if let Some((inner_coeff, ptr)) = quotient_mem_term(term) {
            add_grouped_limb_coeff(&mut grouped_mem, ptr, coeff * inner_coeff);
        } else if let Some((inner_coeff, lhs, rhs)) = quotient_product_mem_pair(term) {
            add_grouped_product_coeff(&mut grouped_products, lhs, rhs, coeff * inner_coeff);
        } else if add_factored_affine_product_terms(
            &mut grouped_mem,
            &mut grouped_products,
            coeff,
            term,
        )
        .is_none()
        {
            return None;
        }
    }
    grouped_mem.retain(|(_, coeff)| *coeff != Fq::ZERO);
    grouped_mem.sort_by_key(|(ptr, _)| *ptr);
    grouped_products.retain(|(_, _, coeff)| *coeff != Fq::ZERO);
    grouped_products.sort_by_key(|(lhs, rhs, _)| (*lhs, *rhs));
    if grouped_mem.len() > u8::MAX as usize || grouped_products.len() > u8::MAX as usize {
        return None;
    }

    let nonzero_constant = usize::from(constant != Fq::ZERO);
    let component_count = lin.len()
        + rows.len()
        + pairwise.len()
        + grouped_mem.len()
        + grouped_products.len()
        + nonzero_constant;
    if component_count == 0 {
        return None;
    }
    let has_limb_component = !lin.is_empty() || !rows.is_empty() || !pairwise.is_empty();
    let has_sparse_conditional_products =
        cond.is_some() && !grouped_products.is_empty() && component_count >= 2;
    if !has_limb_component && !has_sparse_conditional_products {
        return None;
    }
    if cond.is_none() && component_count < 2 {
        return None;
    }

    Some(QuotientModarith7Shape {
        cond,
        constant: quotient_fq_to_u256(constant),
        lin,
        rows,
        pairwise,
        mem_terms: grouped_mem
            .into_iter()
            .map(|(ptr, coeff)| (quotient_fq_to_u256(coeff), ptr))
            .collect(),
        product_terms: grouped_products
            .into_iter()
            .map(|(lhs, rhs, coeff)| (quotient_fq_to_u256(coeff), lhs, rhs))
            .collect(),
    })
}

/// Remove recognized term indices from an affine term list.
fn remove_quotient_terms(terms: &mut Vec<(Fq, &QuotientExpr)>, used: &[usize]) {
    let used = used.iter().copied().collect::<HashSet<_>>();
    let mut idx = 0usize;
    terms.retain(|_| {
        let keep = !used.contains(&idx);
        idx += 1;
        keep
    });
}

/// Add a coefficient to an unordered memory-product pair.
fn add_grouped_product_coeff(grouped: &mut Vec<(u16, u16, Fq)>, lhs: u16, rhs: u16, coeff: Fq) {
    let (lhs, rhs) = if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) };
    if let Some((_, _, existing)) = grouped
        .iter_mut()
        .find(|(existing_lhs, existing_rhs, _)| *existing_lhs == lhs && *existing_rhs == rhs)
    {
        *existing += coeff;
    } else {
        grouped.push((lhs, rhs, coeff));
    }
}

/// Recognize `mem * (affine mem sum)` and fold it into sparse product/memory
/// buckets for `MODARITH7`.
fn add_factored_affine_product_terms(
    grouped_mem: &mut Vec<(u16, Fq)>,
    grouped_products: &mut Vec<(u16, u16, Fq)>,
    term_coeff: Fq,
    expr: &QuotientExpr,
) -> Option<()> {
    let mut factors = Vec::new();
    collect_product_expr_factors(expr, &mut factors);
    if factors.len() < 2 {
        return None;
    }

    let mut coeff = term_coeff;
    let mut lhs = None;
    let mut affine_expr = None;
    for factor in factors {
        match factor {
            QuotientExpr::Const(value) => coeff *= quotient_fq_from_u256(*value)?,
            QuotientExpr::Mem(QuotientMem::Literal(ptr)) => {
                if lhs.replace(u16::try_from(*ptr).ok()?).is_some() {
                    return None;
                }
            }
            QuotientExpr::Mem(QuotientMem::Token(_))
            | QuotientExpr::Mem(QuotientMem::TokenOffset(_, _)) => return None,
            QuotientExpr::Add(_, _) | QuotientExpr::Mul(_, _) | QuotientExpr::Neg(_) => {
                if affine_expr.replace(factor).is_some() {
                    return None;
                }
            }
        }
    }

    let lhs = lhs?;
    let affine_expr = affine_expr?;
    let mut terms = Vec::new();
    let mut constant = Fq::ZERO;
    if !collect_quotient_affine_terms(affine_expr, Fq::ONE, &mut terms, &mut constant) {
        return None;
    }
    if constant != Fq::ZERO {
        add_grouped_limb_coeff(grouped_mem, lhs, coeff * constant);
    }
    for (inner_coeff, term) in terms {
        let (mem_coeff, rhs) = quotient_mem_term(term)?;
        add_grouped_product_coeff(grouped_products, lhs, rhs, coeff * inner_coeff * mem_coeff);
    }
    Some(())
}

/// Find one factored row-shaped limb term inside a larger affine sum.
fn try_quotient_factored_bilin7_row_subshape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<(QuotientLimbShape, Vec<usize>)> {
    for (idx, (coeff, expr)) in terms.iter().enumerate() {
        if let Some(shape) = quotient_factored_bilin7_row_shape(*coeff, expr) {
            return Some((shape, vec![idx]));
        }
    }
    None
}

/// Recognize `lhs_limb * lin7(rhs_limbs)` as a row bilinear limb shape.
fn quotient_factored_bilin7_row_shape(
    term_coeff: Fq,
    expr: &QuotientExpr,
) -> Option<QuotientLimbShape> {
    let mut factors = Vec::new();
    collect_product_expr_factors(expr, &mut factors);
    if factors.len() < 2 {
        return None;
    }

    let mut coeff = term_coeff;
    let mut lhs = None;
    let mut lin_expr = None;
    for factor in factors {
        match factor {
            QuotientExpr::Const(value) => coeff *= quotient_fq_from_u256(*value)?,
            QuotientExpr::Mem(QuotientMem::Literal(ptr)) => {
                if lhs.replace(u16::try_from(*ptr).ok()?).is_some() {
                    return None;
                }
            }
            QuotientExpr::Mem(QuotientMem::Token(_))
            | QuotientExpr::Mem(QuotientMem::TokenOffset(_, _)) => return None,
            QuotientExpr::Add(_, _) | QuotientExpr::Mul(_, _) | QuotientExpr::Neg(_) => {
                if lin_expr.replace(factor).is_some() {
                    return None;
                }
            }
        }
    }

    let lhs = lhs?;
    let lin_expr = lin_expr?;
    let mut lin_terms = Vec::new();
    if !collect_quotient_sum_terms(lin_expr, coeff, &mut lin_terms) {
        return None;
    }
    match try_quotient_lin7_shape(&lin_terms)? {
        QuotientLimbShape::Lin7 { terms } => Some(QuotientLimbShape::Bilin7Row { lhs, terms }),
        QuotientLimbShape::Bilin7Row { .. } | QuotientLimbShape::Bilin7Pairwise { .. } => None,
    }
}

/// Return constant-table coefficients referenced by a `MODARITH7` shape.
fn modarith7_coeffs(shape: &QuotientModarith7Shape) -> Vec<U256> {
    let mut coeffs = Vec::new();
    if shape.constant != U256::ZERO {
        coeffs.push(shape.constant);
    }
    for terms in &shape.lin {
        coeffs.extend(terms.iter().map(|(coeff, _)| *coeff));
    }
    for (_, terms) in &shape.rows {
        coeffs.extend(terms.iter().map(|(coeff, _)| *coeff));
    }
    for (_, _, terms) in &shape.pairwise {
        coeffs.extend(terms.iter().copied());
    }
    coeffs.extend(shape.mem_terms.iter().map(|(coeff, _)| *coeff));
    coeffs.extend(shape.product_terms.iter().map(|(coeff, _, _)| *coeff));
    coeffs
}

/// Collect additive terms for subshape extraction, preserving constants as the
/// residue instead of rejecting the whole affine identity.
fn collect_quotient_affine_terms<'a>(
    expr: &'a QuotientExpr,
    coeff: Fq,
    terms: &mut Vec<(Fq, &'a QuotientExpr)>,
    constant: &mut Fq,
) -> bool {
    if coeff == Fq::ZERO {
        return true;
    }

    match expr {
        QuotientExpr::Add(lhs, rhs) => {
            collect_quotient_affine_terms(lhs, coeff, terms, constant)
                && collect_quotient_affine_terms(rhs, coeff, terms, constant)
        }
        QuotientExpr::Neg(inner) => collect_quotient_affine_terms(inner, -coeff, terms, constant),
        QuotientExpr::Mul(lhs, rhs) => {
            if let QuotientExpr::Const(value) = lhs.as_ref() {
                let Some(value) = quotient_fq_from_u256(*value) else {
                    return false;
                };
                collect_quotient_affine_terms(rhs, coeff * value, terms, constant)
            } else if let QuotientExpr::Const(value) = rhs.as_ref() {
                let Some(value) = quotient_fq_from_u256(*value) else {
                    return false;
                };
                collect_quotient_affine_terms(lhs, coeff * value, terms, constant)
            } else {
                terms.push((coeff, expr));
                true
            }
        }
        QuotientExpr::Const(value) => {
            let Some(value) = quotient_fq_from_u256(*value) else {
                return false;
            };
            *constant += coeff * value;
            true
        }
        QuotientExpr::Mem(_) => {
            terms.push((coeff, expr));
            true
        }
    }
}

/// Collect additive terms as `(coefficient, expression)` pairs over Fr.
///
/// Constant-only terms must reduce to zero for a limb shape to match; non-zero
/// standalone constants would require an additional VM add and therefore are
/// left to the generic emitter.
pub(crate) fn collect_quotient_sum_terms<'a>(
    expr: &'a QuotientExpr,
    coeff: Fq,
    terms: &mut Vec<(Fq, &'a QuotientExpr)>,
) -> bool {
    if coeff == Fq::ZERO {
        return true;
    }

    match expr {
        QuotientExpr::Add(lhs, rhs) => {
            collect_quotient_sum_terms(lhs, coeff, terms)
                && collect_quotient_sum_terms(rhs, coeff, terms)
        }
        QuotientExpr::Neg(inner) => collect_quotient_sum_terms(inner, -coeff, terms),
        QuotientExpr::Mul(lhs, rhs) => {
            if let QuotientExpr::Const(value) = lhs.as_ref() {
                let Some(value) = quotient_fq_from_u256(*value) else {
                    return false;
                };
                collect_quotient_sum_terms(rhs, coeff * value, terms)
            } else if let QuotientExpr::Const(value) = rhs.as_ref() {
                let Some(value) = quotient_fq_from_u256(*value) else {
                    return false;
                };
                collect_quotient_sum_terms(lhs, coeff * value, terms)
            } else {
                terms.push((coeff, expr));
                true
            }
        }
        QuotientExpr::Const(value) => {
            let Some(value) = quotient_fq_from_u256(*value) else {
                return false;
            };
            coeff * value == Fq::ZERO
        }
        QuotientExpr::Mem(_) => {
            terms.push((coeff, expr));
            true
        }
    }
}

/// Recognize a seven-limb linear combination.
///
/// The resulting terms are sorted by memory pointer so equivalent expressions
/// have deterministic bytecode even when the source expression tree orders
/// additions differently.
pub(crate) fn try_quotient_lin7_shape(terms: &[(Fq, &QuotientExpr)]) -> Option<QuotientLimbShape> {
    // Matches:
    //   circuits/src/field/foreign/gates/norm.rs
    //     sum_exprs(base_powers, shifted_x) - sum_exprs(base_powers, zs)
    //   circuits/src/field/foreign/gates/mul.rs
    //     sum_exprs(base_powers, xs/ys/zs)
    // and the same base-power sums reused by ECC foreign gates.
    let mut grouped = Vec::<(u16, Fq)>::new();
    for (coeff, expr) in terms {
        let (inner_coeff, ptr) = quotient_mem_term(expr)?;
        add_grouped_limb_coeff(&mut grouped, ptr, *coeff * inner_coeff);
    }
    grouped.retain(|(_, coeff)| *coeff != Fq::ZERO);
    if grouped.len() != QUOTIENT_VM_LIMBS {
        return None;
    }
    grouped.sort_by_key(|(ptr, _)| *ptr);
    Some(QuotientLimbShape::Lin7 {
        terms: grouped
            .into_iter()
            .map(|(ptr, coeff)| (quotient_fq_to_u256(coeff), ptr))
            .collect(),
    })
}

/// Recognize one limb multiplied across a seven-limb vector.
///
/// The recognizer tries both sides of the first pair as the repeated limb so it
/// is insensitive to multiplication commutativity in the lowered expression.
pub(crate) fn try_quotient_bilin7_row_shape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<QuotientLimbShape> {
    // Matches one fixed limb multiplied across a 7-limb vector. This is a
    // local slice of the `pair_wise_prod` formulas in:
    //   circuits/src/field/foreign/gates/mul.rs
    //   circuits/src/ecc/foreign/gates/{on_curve,slope,tangent,lambda_squared}.rs
    let mut pairs = Vec::with_capacity(terms.len());
    for (coeff, expr) in terms {
        let (inner_coeff, lhs, rhs) = quotient_product_mem_pair(expr)?;
        pairs.push((*coeff * inner_coeff, lhs, rhs));
    }
    if pairs.len() != QUOTIENT_VM_LIMBS {
        return None;
    }

    for candidate in [pairs[0].1, pairs[0].2] {
        let mut grouped = Vec::<(u16, Fq)>::new();
        let mut ok = true;
        for (coeff, lhs, rhs) in &pairs {
            let other = if *lhs == candidate {
                *rhs
            } else if *rhs == candidate {
                *lhs
            } else {
                ok = false;
                break;
            };
            add_grouped_limb_coeff(&mut grouped, other, *coeff);
        }
        grouped.retain(|(_, coeff)| *coeff != Fq::ZERO);
        if ok && grouped.len() == QUOTIENT_VM_LIMBS {
            grouped.sort_by_key(|(ptr, _)| *ptr);
            return Some(QuotientLimbShape::Bilin7Row {
                lhs: candidate,
                terms: grouped
                    .into_iter()
                    .map(|(ptr, coeff)| (quotient_fq_to_u256(coeff), ptr))
                    .collect(),
            });
        }
    }

    None
}

/// Recognize a full seven-by-seven foreign-field product convolution.
///
/// The memory pointers must contain two contiguous seven-word limb vectors. For
/// each product term the coefficient is accumulated into its row-major slot and
/// then checked to depend only on `i + j`, exactly matching the
/// `double_base_powers` shape. If any slot is missing or coefficients disagree,
/// the shape is rejected and the generic VM remains the source of truth.
pub(crate) fn try_quotient_bilin7_pairwise_shape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<QuotientLimbShape> {
    // Matches the full foreign-field product convolution:
    //   sum_exprs(double_base_powers, pair_wise_prod(lhs, rhs))
    // where double_base_powers[k] = base^k mod m. The Rust helper
    // pair_wise_prod emits 49 terms in row-major order; after collection we
    // require coefficients with the same i+j to agree, exactly the
    // base^(i+j) pattern documented in foreign/params.rs.
    let mut pairs = Vec::with_capacity(terms.len());
    let mut ptrs = HashSet::new();
    for (coeff, expr) in terms {
        let (inner_coeff, lhs, rhs) = quotient_product_mem_pair(expr)?;
        pairs.push((*coeff * inner_coeff, lhs, rhs));
        ptrs.insert(lhs);
        ptrs.insert(rhs);
    }
    if pairs.len() != QUOTIENT_VM_PAIRWISE_TERMS {
        return None;
    }

    let bases = limb7_base_candidates(&ptrs);
    for lhs_base in &bases {
        for rhs_base in &bases {
            let mut coeffs = vec![Fq::ZERO; QUOTIENT_VM_PAIRWISE_TERMS];
            let mut seen = [false; QUOTIENT_VM_PAIRWISE_TERMS];
            let mut ok = true;

            for (coeff, lhs, rhs) in &pairs {
                let direct = limb7_index(*lhs_base, *lhs).zip(limb7_index(*rhs_base, *rhs));
                let swapped = limb7_index(*lhs_base, *rhs).zip(limb7_index(*rhs_base, *lhs));
                let Some((i, j)) = direct.or(swapped) else {
                    ok = false;
                    break;
                };
                let idx = i * QUOTIENT_VM_LIMBS + j;
                coeffs[idx] += *coeff;
                seen[idx] = true;
            }

            if !ok || seen.iter().any(|seen| !seen) {
                continue;
            }

            let mut by_sum = vec![None; QUOTIENT_VM_PAIRWISE_COEFFS];
            for i in 0..QUOTIENT_VM_LIMBS {
                for j in 0..QUOTIENT_VM_LIMBS {
                    let coeff = coeffs[i * QUOTIENT_VM_LIMBS + j];
                    let slot = &mut by_sum[i + j];
                    if let Some(expected) = slot {
                        if *expected != coeff {
                            ok = false;
                            break;
                        }
                    } else {
                        *slot = Some(coeff);
                    }
                }
                if !ok {
                    break;
                }
            }

            if ok {
                return Some(QuotientLimbShape::Bilin7Pairwise {
                    lhs_base: *lhs_base,
                    rhs_base: *rhs_base,
                    coeffs: by_sum
                        .into_iter()
                        .map(|coeff| quotient_fq_to_u256(coeff.expect("pairwise sum coefficient")))
                        .collect(),
                });
            }
        }
    }

    None
}

/// Find a complete seven-limb linear subshape inside a larger affine sum.
fn try_quotient_lin7_subshape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<(QuotientLimbShape, Vec<usize>)> {
    let mut mem_terms = Vec::<(usize, u16, Fq)>::new();
    for (idx, (coeff, expr)) in terms.iter().enumerate() {
        if let Some((inner_coeff, ptr)) = quotient_mem_term(expr) {
            mem_terms.push((idx, ptr, *coeff * inner_coeff));
        }
    }

    let ptrs = mem_terms.iter().map(|(_, ptr, _)| *ptr).collect::<HashSet<_>>();
    for base in limb7_base_candidates(&ptrs) {
        let mut grouped = Vec::<(u16, Fq)>::new();
        let mut used = Vec::with_capacity(QUOTIENT_VM_LIMBS);
        for limb in 0..QUOTIENT_VM_LIMBS {
            let ptr = base + (limb as u16) * WORD_BYTES as u16;
            let mut coeff = Fq::ZERO;
            let mut found = false;
            for (idx, term_ptr, term_coeff) in &mem_terms {
                if *term_ptr == ptr {
                    coeff += *term_coeff;
                    used.push(*idx);
                    found = true;
                }
            }
            if !found {
                used.clear();
                break;
            }
            grouped.push((ptr, coeff));
        }
        grouped.retain(|(_, coeff)| *coeff != Fq::ZERO);
        if grouped.len() == QUOTIENT_VM_LIMBS && used.len() >= QUOTIENT_VM_LIMBS {
            grouped.sort_by_key(|(ptr, _)| *ptr);
            return Some((
                QuotientLimbShape::Lin7 {
                    terms: grouped
                        .into_iter()
                        .map(|(ptr, coeff)| (quotient_fq_to_u256(coeff), ptr))
                        .collect(),
                },
                used,
            ));
        }
    }
    None
}

/// Find terms sharing one multiplicand with a complete seven-limb row.
fn try_quotient_bilin7_row_subshape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<(QuotientLimbShape, Vec<usize>)> {
    let mut pairs = Vec::<(usize, Fq, u16, u16)>::new();
    let mut ptrs = HashSet::new();
    for (idx, (coeff, expr)) in terms.iter().enumerate() {
        if let Some((inner_coeff, lhs, rhs)) = quotient_product_mem_pair(expr) {
            pairs.push((idx, *coeff * inner_coeff, lhs, rhs));
            ptrs.insert(lhs);
            ptrs.insert(rhs);
        }
    }

    let mut candidates = ptrs.into_iter().collect::<Vec<_>>();
    candidates.sort_unstable();
    for candidate in candidates {
        let mut grouped = Vec::<(u16, Fq)>::new();
        let mut used = Vec::with_capacity(QUOTIENT_VM_LIMBS);
        for (idx, coeff, lhs, rhs) in &pairs {
            let other = if *lhs == candidate {
                Some(*rhs)
            } else if *rhs == candidate {
                Some(*lhs)
            } else {
                None
            };
            if let Some(other) = other {
                add_grouped_limb_coeff(&mut grouped, other, *coeff);
                used.push(*idx);
            }
        }
        grouped.retain(|(_, coeff)| *coeff != Fq::ZERO);
        if grouped.len() == QUOTIENT_VM_LIMBS && used.len() >= QUOTIENT_VM_LIMBS {
            grouped.sort_by_key(|(ptr, _)| *ptr);
            return Some((
                QuotientLimbShape::Bilin7Row {
                    lhs: candidate,
                    terms: grouped
                        .into_iter()
                        .map(|(ptr, coeff)| (quotient_fq_to_u256(coeff), ptr))
                        .collect(),
                },
                used,
            ));
        }
    }
    None
}

/// Find a full 7x7 pairwise product grid inside a larger affine sum.
fn try_quotient_bilin7_pairwise_subshape(
    terms: &[(Fq, &QuotientExpr)],
) -> Option<(QuotientLimbShape, Vec<usize>)> {
    let mut pairs = Vec::<(usize, Fq, u16, u16)>::new();
    let mut ptrs = HashSet::new();
    for (idx, (coeff, expr)) in terms.iter().enumerate() {
        if let Some((inner_coeff, lhs, rhs)) = quotient_product_mem_pair(expr) {
            pairs.push((idx, *coeff * inner_coeff, lhs, rhs));
            ptrs.insert(lhs);
            ptrs.insert(rhs);
        }
    }

    let bases = limb7_base_candidates(&ptrs);
    for lhs_base in &bases {
        for rhs_base in &bases {
            let mut coeffs = vec![Fq::ZERO; QUOTIENT_VM_PAIRWISE_TERMS];
            let mut seen = [false; QUOTIENT_VM_PAIRWISE_TERMS];
            let mut used = Vec::with_capacity(QUOTIENT_VM_PAIRWISE_TERMS);
            for (idx, coeff, lhs, rhs) in &pairs {
                let direct = limb7_index(*lhs_base, *lhs).zip(limb7_index(*rhs_base, *rhs));
                let swapped = limb7_index(*lhs_base, *rhs).zip(limb7_index(*rhs_base, *lhs));
                let Some((i, j)) = direct.or(swapped) else {
                    continue;
                };
                let term_idx = i * QUOTIENT_VM_LIMBS + j;
                coeffs[term_idx] += *coeff;
                seen[term_idx] = true;
                used.push(*idx);
            }
            if seen.iter().any(|seen| !seen) {
                continue;
            }

            let mut by_sum = vec![None; QUOTIENT_VM_PAIRWISE_COEFFS];
            let mut ok = true;
            for i in 0..QUOTIENT_VM_LIMBS {
                for j in 0..QUOTIENT_VM_LIMBS {
                    let coeff = coeffs[i * QUOTIENT_VM_LIMBS + j];
                    let slot = &mut by_sum[i + j];
                    if let Some(expected) = slot {
                        if *expected != coeff {
                            ok = false;
                            break;
                        }
                    } else {
                        *slot = Some(coeff);
                    }
                }
                if !ok {
                    break;
                }
            }
            if ok && used.len() >= QUOTIENT_VM_PAIRWISE_TERMS {
                return Some((
                    QuotientLimbShape::Bilin7Pairwise {
                        lhs_base: *lhs_base,
                        rhs_base: *rhs_base,
                        coeffs: by_sum
                            .into_iter()
                            .map(|coeff| {
                                quotient_fq_to_u256(coeff.expect("pairwise sum coefficient"))
                            })
                            .collect(),
                    },
                    used,
                ));
            }
        }
    }
    None
}

/// Return `(coefficient, ptr)` for a product with exactly one memory factor.
pub(crate) fn quotient_mem_term(expr: &QuotientExpr) -> Option<(Fq, u16)> {
    let (coeff, ptrs) = quotient_product_mem_factors(expr)?;
    if ptrs.len() == 1 {
        Some((coeff, ptrs[0]))
    } else {
        None
    }
}

/// Return `(coefficient, lhs_ptr, rhs_ptr)` for a product with two memory
/// factors.
pub(crate) fn quotient_product_mem_pair(expr: &QuotientExpr) -> Option<(Fq, u16, u16)> {
    let (coeff, ptrs) = quotient_product_mem_factors(expr)?;
    if ptrs.len() == 2 {
        Some((coeff, ptrs[0], ptrs[1]))
    } else {
        None
    }
}

/// Factor a product into its Fr coefficient and literal memory pointers.
///
/// Token memory references are rejected because limb opcodes and fused product
/// forms store compact literal `u16` pointers.
pub(crate) fn quotient_product_mem_factors(expr: &QuotientExpr) -> Option<(Fq, Vec<u16>)> {
    let mut leaves = Vec::new();
    if !collect_product_leaves(expr, &mut leaves) {
        return None;
    }

    let mut coeff = Fq::ONE;
    let mut ptrs = Vec::new();
    for leaf in leaves {
        match leaf {
            QuotientLeaf::Const(value) => coeff *= quotient_fq_from_u256(value)?,
            QuotientLeaf::Mem(QuotientMem::Literal(ptr)) => ptrs.push(u16::try_from(ptr).ok()?),
            QuotientLeaf::Mem(QuotientMem::Token(_))
            | QuotientLeaf::Mem(QuotientMem::TokenOffset(_, _)) => return None,
        }
    }
    Some((coeff, ptrs))
}

/// Add a coefficient into a grouped limb term.
pub(crate) fn add_grouped_limb_coeff(grouped: &mut Vec<(u16, Fq)>, ptr: u16, coeff: Fq) {
    if let Some((_, existing)) = grouped.iter_mut().find(|(existing, _)| *existing == ptr) {
        *existing += coeff;
    } else {
        grouped.push((ptr, coeff));
    }
}

/// Find all base pointers that cover a contiguous seven-limb vector.
pub(crate) fn limb7_base_candidates(ptrs: &HashSet<u16>) -> Vec<u16> {
    let mut bases = ptrs
        .iter()
        .copied()
        .filter(|base| {
            (0..QUOTIENT_VM_LIMBS).all(|idx| {
                base.checked_add((idx * layout::WORD_BYTES) as u16)
                    .is_some_and(|ptr| ptrs.contains(&ptr))
            })
        })
        .collect::<Vec<_>>();
    bases.sort_unstable();
    bases.dedup();
    bases
}

/// Return the limb index of `ptr` relative to `base`, if it is in the vector.
pub(crate) fn limb7_index(base: u16, ptr: u16) -> Option<usize> {
    let diff = ptr.checked_sub(base)?;
    let word_bytes = layout::WORD_BYTES as u16;
    if diff % word_bytes != 0 {
        return None;
    }
    let idx = (diff / word_bytes) as usize;
    (idx < QUOTIENT_VM_LIMBS).then_some(idx)
}

/// Interpret a `U256` as a canonical BLS12-381 scalar field element.
///
/// Values outside the field modulus are rejected; that is important when
/// folding parsed Yul literals back into Fr coefficients for shape recognition.
pub(crate) fn quotient_fq_from_u256(value: U256) -> Option<Fq> {
    let bytes = value.to_le_bytes::<32>();
    let repr = <Fq as PrimeField>::Repr::from(bytes);
    Option::<Fq>::from(Fq::from_repr(repr))
}

/// Encode a BLS12-381 scalar field element as a `U256`.
pub(crate) fn quotient_fq_to_u256(value: Fq) -> U256 {
    fe_to_u256::<Fq>(&value)
}

/// Parse a generated Yul memory pointer expression into a VM memory reference.
pub(crate) fn parse_mem(ptr: &str) -> QuotientMem {
    let ptr = ptr.trim();
    if let Some(value) = parse_u32_literal(ptr) {
        QuotientMem::Literal(value)
    } else if let Some(token) = mem_token(ptr) {
        QuotientMem::Token(token)
    } else if let Some(args) = call_args(ptr, "add") {
        assert_eq!(args.len(), 2, "add pointer arity");
        let token = mem_token(args[0].trim())
            .unwrap_or_else(|| panic!("unsupported quotient mload base: {}", args[0]));
        let offset = parse_u32_literal(args[1].trim())
            .unwrap_or_else(|| panic!("unsupported quotient mload offset: {}", args[1]));
        QuotientMem::TokenOffset(token, offset)
    } else {
        panic!("unsupported quotient mload pointer: {ptr}");
    }
}

/// Return whether a string is a decimal or hexadecimal integer literal.
pub(crate) fn is_literal(value: &str) -> bool {
    let value = value.trim();
    value.starts_with("0x") || value.as_bytes().first().is_some_and(|byte| byte.is_ascii_digit())
}

/// Parse a decimal or hexadecimal `U256` literal.
pub(crate) fn parse_u256(value: &str) -> U256 {
    let value = value.trim();
    if let Some(hex) = value.strip_prefix("0x") {
        U256::from_str_radix(hex, 16)
            .unwrap_or_else(|err| panic!("valid hex U256 `{value}`: {err:?}"))
    } else {
        U256::from_str_radix(value, 10)
            .unwrap_or_else(|err| panic!("valid decimal U256 `{value}`: {err:?}"))
    }
}

/// Render a `U256` as the shortest stable hexadecimal Yul literal.
pub(crate) fn u256_string(value: U256) -> String {
    if value.bit_len() < 64 {
        format!("0x{:x}", value.as_limbs()[0])
    } else {
        format!("0x{value:x}")
    }
}

/// Render BLS12-381 Fr `DELTA` for legacy/direct Yul paths.
pub(crate) fn fr_delta_literal() -> String {
    u256_string(fe_to_u256::<Fq>(&Fq::DELTA))
}

/// Parse a literal if it fits in `u32`.
pub(crate) fn parse_u32_literal(value: &str) -> Option<u32> {
    if !is_literal(value) {
        return None;
    }
    let parsed = parse_u256(value);
    parsed.try_into().ok()
}

/// Parse a literal if it fits in `usize`.
pub(crate) fn parse_usize_literal(value: &str) -> Option<usize> {
    if !is_literal(value) {
        return None;
    }
    let parsed = parse_u256(value);
    parsed.try_into().ok()
}

/// Resolve a generated Yul memory symbol to a VM token.
pub(crate) fn mem_token(name: &str) -> Option<u8> {
    quotient_mem_token_from_name(name)
}

/// Parsed form of the simple Yul assignments emitted by `Evaluator`.
///
/// The parser is deliberately shallow. It is not a Yul parser; it accepts only
/// assignment syntax that this generator emits, which makes unsupported changes
/// fail loudly during code generation instead of silently changing verifier
/// semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct YulAssignment {
    /// Destination variable name.
    pub(crate) dst: String,
    /// Right-hand expression as source text.
    pub(crate) expr: String,
    /// Whether the assignment was introduced with `let`.
    pub(crate) has_let: bool,
}

/// Parse a generated Yul assignment line.
pub(crate) fn yul_assignment(line: &str) -> Option<YulAssignment> {
    let line = line.trim();
    let (has_let, rest) = if let Some(rest) = line.strip_prefix("let") {
        if !rest.starts_with(char::is_whitespace) {
            return None;
        }
        (true, rest.trim_start())
    } else {
        (false, line)
    };
    let (dst, expr) = rest.split_once(":=")?;
    let dst = dst.trim();
    let expr = expr.trim();
    if dst.is_empty() || expr.is_empty() {
        return None;
    }
    Some(YulAssignment {
        dst: dst.to_string(),
        expr: expr.to_string(),
        has_let,
    })
}

/// Parse a generated `let dst := expr` assignment.
pub(crate) fn yul_let_assignment(line: &str) -> Option<(String, String)> {
    let assignment = yul_assignment(line)?;
    assignment.has_let.then_some((assignment.dst, assignment.expr))
}

/// Resolve a literal or previously bound constant variable to canonical text.
pub(crate) fn yul_const_value(value: &str, const_vars: &HashMap<String, String>) -> Option<String> {
    let value = value.trim();
    if is_literal(value) {
        Some(u256_string(parse_u256(value)))
    } else {
        const_vars.get(value).cloned()
    }
}

/// Parse `let dst := mulmod(lhs, rhs, r)`.
pub(crate) fn yul_mulmod_assignment(line: &str) -> Option<(String, String, String)> {
    let (dst, expr) = yul_let_assignment(line)?;
    let args = call_args(&expr, "mulmod")?;
    if args.len() == 3 && args[2].trim() == "r" {
        Some((dst, args[0].trim().to_string(), args[1].trim().to_string()))
    } else {
        None
    }
}

/// Parse `let dst := addmod(lhs, rhs, r)`.
pub(crate) fn yul_addmod_assignment(line: &str) -> Option<(String, String, String)> {
    let (dst, expr) = yul_let_assignment(line)?;
    let args = call_args(&expr, "addmod")?;
    if args.len() == 3 && args[2].trim() == "r" {
        Some((dst, args[0].trim().to_string(), args[1].trim().to_string()))
    } else {
        None
    }
}

/// Parse `mload(literal_ptr)`.
pub(crate) fn yul_mload_literal_expr(expr: &str) -> Option<usize> {
    let args = call_args(expr.trim(), "mload")?;
    if args.len() == 1 {
        parse_usize_literal(args[0].trim())
    } else {
        None
    }
}

/// Return top-level comma-separated call arguments for `name(...)`.
pub(crate) fn call_args(expr: &str, name: &str) -> Option<Vec<String>> {
    let expr = expr.trim();
    let rest = expr.strip_prefix(name)?.trim_start();
    let rest = rest.strip_prefix('(')?;
    if !rest.ends_with(')') {
        return None;
    }
    Some(split_top_level(&rest[..rest.len() - 1]))
}

/// Split a comma-separated argument list while respecting nested calls.
pub(crate) fn split_top_level(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.checked_sub(1).expect("balanced quotient expression"),
            ',' if depth == 0 => {
                args.push(input[start..idx].trim().to_string());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    args.push(input[start..].trim().to_string());
    args
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_compaction_groups_mixed_affine_sum_terms() {
        let mut bytes = Vec::new();
        bytes.push(Q_OP_PUSH_CONST_U8);
        bytes.push(0);
        bytes.push(Q_OP_ADD_MUL_CONST_U8_MEM_U16);
        bytes.extend_from_slice(&0x120u16.to_be_bytes());
        bytes.push(1);
        bytes.push(Q_OP_ADD_MUL_MEM_MEM_CONST_U8);
        bytes.extend_from_slice(&0x140u16.to_be_bytes());
        bytes.extend_from_slice(&0x160u16.to_be_bytes());
        bytes.push(2);
        bytes.push(Q_OP_ADD_MUL_CONST_U8_MEM_U16);
        bytes.extend_from_slice(&0x180u16.to_be_bytes());
        bytes.push(3);
        bytes.push(Q_OP_ADD_MUL_MEM_MEM_CONST_U8);
        bytes.extend_from_slice(&0x1a0u16.to_be_bytes());
        bytes.extend_from_slice(&0x1c0u16.to_be_bytes());
        bytes.push(4);
        bytes.push(Q_OP_FOLD_MAIN);

        let compacted = compact_quotient_runs(&bytes);
        assert_eq!(compacted[2], Q_OP_AFFINE_SUM);
        assert_eq!(read_u16(&compacted, 3), 2);
        assert_eq!(read_u16(&compacted, 5), 2);
        assert_eq!(read_u16(&compacted, 7), 0x120);
        assert_eq!(compacted[9], 1);
        assert_eq!(read_u16(&compacted, 10), 0x180);
        assert_eq!(compacted[12], 3);
        assert_eq!(read_u16(&compacted, 13), 0x140);
        assert_eq!(read_u16(&compacted, 15), 0x160);
        assert_eq!(compacted[17], 2);
        assert_eq!(read_u16(&compacted, 18), 0x1a0);
        assert_eq!(read_u16(&compacted, 20), 0x1c0);
        assert_eq!(compacted[22], 4);

        let max_stack = validate_quotient_program(&compacted)
            .expect("mixed affine sum program should pass validation");
        assert_eq!(max_stack, 1);
    }

    #[test]
    fn byte_validator_rejects_empty_affine_sum_sides() {
        for (lin_count, product_count) in [(0u16, 1u16), (1, 0)] {
            let mut bytes = Vec::new();
            bytes.push(Q_OP_PUSH_CONST_U8);
            bytes.push(0);
            bytes.push(Q_OP_AFFINE_SUM);
            bytes.extend_from_slice(&lin_count.to_be_bytes());
            bytes.extend_from_slice(&product_count.to_be_bytes());
            let err = validate_quotient_program(&bytes)
                .expect_err("empty affine sum side should be rejected");
            assert!(err.contains("requires nonzero linear and product counts"));
        }
    }
}
