// SPDX-License-Identifier: CC0-1.0
//! Thin public facade for rendering a concrete Solidity verifier.
//!
//! `builder` owns the public `SolidityGenerator` type, supported-shape
//! validation, and caller-facing wrappers. The actual lowering pipeline lives
//! in `lowering`, which receives read-only verifier build inputs.

use std::fmt::Debug;

use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    plonk::VerifyingKey,
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};

use crate::{
    api::{
        AccumulatorEncoding, CommittedInstanceCommitmentKind, GeneratorConfig, GeneratorError,
        ProofEvaluationCounts, QuotientIdentityManifest, RenderDiagnostics, RenderOptions,
        RenderedArtifacts, RepackError,
    },
    lowering::{encoding::ConstraintSystemMeta, VerifierBuildInputs},
};

mod api;
mod render;
mod repack;

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests;

/// Solidity verifier generator for midnight-proofs (logup + trash + KZG
/// multi-prepare PCS) on BLS12-381 EIP-2537.
///
/// The supported protocol shape is intentionally narrow: Midfall/Midnight
/// KZG proofs with one committed identity instance column and one
/// non-committed public-input column.
#[derive(Debug)]
pub struct SolidityGenerator<'a> {
    params: &'a ParamsKZG<Bls12>,
    vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    num_instances: usize,
    /// Optional accumulator layout encoded at the tail of the public instances.
    acc_encoding: Option<AccumulatorEncoding>,
    meta: ConstraintSystemMeta,
}

impl<'a> SolidityGenerator<'a> {
    /// Package immutable generator state for the private lowering pipeline.
    ///
    /// The returned value borrows the constructor inputs and the cached
    /// constraint-system metadata; each render/repack path then builds its own
    /// converged lowering plan from the same facts.
    pub(crate) fn inputs(&self) -> VerifierBuildInputs<'a, '_> {
        VerifierBuildInputs {
            params: self.params,
            vk: self.vk,
            num_instances: self.num_instances,
            num_committed_instances: self.meta.num_committed_instances,
            acc_encoding: self.acc_encoding,
            meta: &self.meta,
        }
    }
}
