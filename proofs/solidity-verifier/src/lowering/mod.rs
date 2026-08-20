// SPDX-License-Identifier: CC0-1.0
//! Private lowering pipeline for Solidity verifier artifact construction.
//!
//! `lowering` owns the reusable planning and emission machinery: protocol
//! planning, ABI/layout facts, proof encoders, VK payload generation, KZG and
//! quotient-numerator emitters, calldata repacking, artifact assembly, and
//! Askama render models. The public `SolidityGenerator` facade in `builder`
//! delegates here with a concrete, read-only [`VerifierBuildInputs`] value.

use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    plonk::VerifyingKey,
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
};

use crate::api::AccumulatorEncoding;

pub(crate) mod abi;
pub(crate) mod artifacts;
pub(crate) mod calldata;
pub(crate) mod config;
pub(crate) mod diagnostics;
pub(crate) mod encoding;
pub(crate) mod kzg;
pub(crate) mod layout;
pub(crate) mod plan;
pub(crate) mod protocol;
pub(crate) mod quotient;
pub(crate) mod quotient_numerator;
pub(crate) mod render;
pub(crate) mod vk;
pub(crate) mod yul_ir;

use encoding::ConstraintSystemMeta;

#[derive(Clone, Copy, Debug)]
pub(crate) struct VerifierBuildInputs<'params, 'meta> {
    pub(crate) params: &'params ParamsKZG<Bls12>,
    pub(crate) vk: &'params VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    pub(crate) num_instances: usize,
    pub(crate) num_committed_instances: usize,
    pub(crate) acc_encoding: Option<AccumulatorEncoding>,
    pub(crate) meta: &'meta ConstraintSystemMeta,
}

#[cfg(all(test, feature = "evm"))]
pub(crate) use quotient_numerator::vm::RepackedProofScalarLayout;

#[cfg(test)]
pub(crate) mod test_circuits;

#[cfg(test)]
mod transcript_anchor;

#[cfg(test)]
mod tests;
