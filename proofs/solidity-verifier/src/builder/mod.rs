// SPDX-License-Identifier: CC0-1.0
//! Thin public facade for rendering a concrete Solidity verifier.
//!
//! `builder` owns the public `SolidityGenerator` type, supported-shape
//! validation, and caller-facing wrappers. The actual lowering pipeline lives
//! in `lowering`, which receives read-only verifier build inputs.

use std::{fmt::Debug, sync::OnceLock};

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
    lowering::{encoding::ConstraintSystemMeta, plan::LoweringPlan, VerifierBuildInputs},
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
    /// One converged lowering plan per generator. Render, repack, and
    /// diagnostics all share this cached build; `LoweringPlan::try_new` is
    /// deterministic in the constructor inputs, so a failure is cached too.
    plan: OnceLock<Result<Box<LoweringPlan>, GeneratorError>>,
}

impl<'a> SolidityGenerator<'a> {
    /// The single converged lowering plan for this generator.
    ///
    /// Built lazily on first use (plan construction includes an O(2^k)
    /// SRS tau-commitment MSM, so the constructor must stay cheap) and shared
    /// by every render/repack/diagnostics call.
    pub(crate) fn plan(&self) -> Result<&LoweringPlan, GeneratorError> {
        match self.plan.get_or_init(|| LoweringPlan::try_new(&self.inputs()).map(Box::new)) {
            Ok(plan) => Ok(plan),
            Err(err) => Err(err.clone()),
        }
    }
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
