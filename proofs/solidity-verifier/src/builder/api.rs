// SPDX-License-Identifier: CC0-1.0
//! Public and crate-local constructor/configuration methods for
//! `SolidityGenerator`.
//!
//! This slice owns validation of the supported proof shape and exposes the
//! stable caller-facing knobs before lower-level generation starts.

use super::*;
use crate::lowering::layout::{memory::batch_invert_input_words, theta_window};

impl<'a> SolidityGenerator<'a> {
    /// Number of committed instance columns supported by the generated ABI.
    pub(super) const SUPPORTED_COMMITTED_INSTANCE_COLUMNS: usize = 1;
    /// Number of non-committed instance columns supported by the generated ABI.
    pub(super) const SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS: usize = 1;
    /// Committed-instance commitment policy hard-coded by the generated
    /// verifier ABI.
    pub const SUPPORTED_COMMITTED_INSTANCE_COMMITMENT: CommittedInstanceCommitmentKind =
        CommittedInstanceCommitmentKind::Identity;

    /// Return a new `SolidityGenerator`.
    pub fn new(
        params: &'a ParamsKZG<Bls12>,
        vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        config: GeneratorConfig,
    ) -> Self {
        Self::try_new(params, vk, config)
            .unwrap_or_else(|err| panic!("unsupported Solidity verifier shape: {err}"))
    }

    /// Try to construct a new `SolidityGenerator`, returning a typed error
    /// when the supplied constraint system is outside the currently supported
    /// Midfall verifier shape.
    pub fn try_new(
        params: &'a ParamsKZG<Bls12>,
        vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        config: GeneratorConfig,
    ) -> Result<Self, GeneratorError> {
        if vk.cs().num_advice_columns() == 0 {
            return Err(GeneratorError::NoAdviceColumns);
        }
        // Midfall's Rust verifier receives instances in two arguments:
        // committed instances and normal (non-committed) instances. The
        // total number of instance columns is their sum, with committed
        // columns first in verifier order (`plonk/verifier.rs::verify_proof`).
        Self::validate_instance_column_shape(
            vk.cs().num_instance_columns(),
            config.num_committed_instances,
        )?;
        if let Some(acc_encoding) = config.accumulator {
            acc_encoding.validate_for_num_instances(config.num_instances)?;
            // The fixed-base scalar tail is derived from the *instance* length,
            // but the bases it multiplies come from this verifying key: `-G`,
            // then `fixed_comm_mptr + i * G1_BYTES` per fixed base, then the
            // permutation commitments. Two tail lengths break that mapping:
            //
            //   * Too long: the generated fixed-base pointers run past the end
            //     of the fixed-commitment region, silently aliasing permutation
            //     commitments and then arbitrary VK payload words as G1 bases.
            //   * Shorter than `-G` plus the permutation commitments: the base
            //     count underflows in the artifact emitter.
            //
            // A tail inside the range is left alone -- it covers a prefix of
            // the fixed commitments, which keeps every pointer in region.
            let fixed_scalar_count = acc_encoding.fixed_scalar_count(config.num_instances)?;
            let num_fixed_comms = vk.fixed_commitments().len();
            let num_permutation_comms = vk.permutation().commitments().len();
            let min_fixed_scalar_count = 1 + num_permutation_comms;
            let max_fixed_scalar_count = min_fixed_scalar_count + num_fixed_comms;
            if fixed_scalar_count != 0
                && !(min_fixed_scalar_count..=max_fixed_scalar_count).contains(&fixed_scalar_count)
            {
                return Err(GeneratorError::AccumulatorFixedBaseTailMismatch {
                    fixed_scalar_count,
                    min_fixed_scalar_count,
                    max_fixed_scalar_count,
                    num_fixed_comms,
                    num_permutation_comms,
                });
            }
        }
        // Non-committed instance evaluations are reconstructed once from the
        // public-input polynomial at the current rotation. Reject rotated
        // instance queries until that path is keyed by `(column, rotation)`.
        if let Some((column, rotation)) = vk
            .cs()
            .instance_queries()
            .iter()
            .find(|(_, rotation)| *rotation != Rotation::cur())
        {
            return Err(GeneratorError::RotatedInstanceQuery {
                column: column.index(),
                rotation: rotation.0,
            });
        }

        // Fallible: `ProtocolPlan::validate` rejects a range of unsupported
        // constraint-system shapes -- an advice column that is absorbed but
        // never opened by a PCS query being the most reachable authoring
        // mistake. Panicking here would break this constructor's contract of
        // reporting such shapes as a typed error.
        let meta = ConstraintSystemMeta::try_new(vk.cs(), config.num_committed_instances).map_err(
            |message| GeneratorError::Planning {
                stage: "constraint system",
                message,
            },
        )?;

        // Bound the public instance count here rather than leaving it to
        // `VerifierMemoryLayout::validate`. The Lagrange block writes its
        // batch-inversion input run in place from `X_N_MPTR`, and that run
        // grows with `num_instances`; the layout does catch an overrun, but
        // only much later and phrased in theta-word offsets. `rotation_last`
        // is only known once `meta` is built, hence the position of this check.
        let run_words = batch_invert_input_words(&meta, config.num_instances);
        if run_words > theta_window::LAGRANGE_RUN_CAP_WORDS {
            let rotation_last_words = meta.rotation_last.unsigned_abs() as usize;
            return Err(GeneratorError::TooManyInstances {
                num_instances: config.num_instances,
                max_num_instances: theta_window::LAGRANGE_RUN_CAP_WORDS
                    .saturating_sub(rotation_last_words + 1),
                rotation_last_words,
            });
        }

        Ok(Self {
            params,
            vk,
            num_instances: config.num_instances,
            acc_encoding: config.accumulator,
            meta,
        })
    }

    /// Return the committed-instance commitment policy for this generator.
    pub fn committed_instance_commitment_kind(&self) -> CommittedInstanceCommitmentKind {
        Self::SUPPORTED_COMMITTED_INSTANCE_COMMITMENT
    }

    /// Validate the currently supported committed/non-committed instance split.
    pub(super) fn validate_instance_column_shape(
        total_instance_columns: usize,
        num_committed_instances: usize,
    ) -> Result<(), GeneratorError> {
        // The Rust verifier accepts committed and normal instance arguments
        // separately, with committed instance columns first. The current
        // Solidity calldata ABI supports exactly one identity-committed column
        // and one direct public-input column, so every instance query can be
        // classified without an extra column-routing table or supplied
        // committed-instance commitment.
        let supported_committed = Self::SUPPORTED_COMMITTED_INSTANCE_COLUMNS;
        let supported_non_committed = Self::SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS;
        let non_committed = total_instance_columns
            .checked_sub(num_committed_instances)
            .unwrap_or(usize::MAX);

        if num_committed_instances != supported_committed
            || non_committed != supported_non_committed
        {
            return Err(GeneratorError::UnsupportedInstanceColumnShape {
                total: total_instance_columns,
                committed: num_committed_instances,
                expected_committed: supported_committed,
                expected_non_committed: supported_non_committed,
            });
        }

        Ok(())
    }

    /// Return the exact field-evaluation counts for the proof layout consumed
    /// by the generated Solidity verifier.
    pub fn proof_evaluation_counts(&self) -> ProofEvaluationCounts {
        crate::lowering::diagnostics::proof_evaluation_counts(self.inputs())
    }

    /// Return a stable host-side manifest of quotient numerator identities.
    ///
    /// This diagnostic API follows the same source ordering as the generated
    /// quotient evaluator: normal gates, permutation, lookup, then trash.
    pub fn quotient_identity_manifest(&self) -> QuotientIdentityManifest {
        crate::lowering::diagnostics::quotient_identity_manifest(self.inputs())
    }
}
