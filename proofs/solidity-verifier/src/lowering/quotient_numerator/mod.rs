// SPDX-License-Identifier: CC0-1.0
//! Quotient-numerator planning and emission.
//!
//! This namespace contains the compact VM producer plus the Yul emitter that
//! reconstructs the batched Halo2 identity numerator inside generated
//! Solidity.

pub(crate) mod vm;
pub(crate) mod yul_emit;

pub(crate) use yul_emit::Evaluator;
