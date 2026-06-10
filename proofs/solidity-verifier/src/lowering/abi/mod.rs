// SPDX-License-Identifier: CC0-1.0
//! ABI planning for generated verifier calldata and transcript buffers.
//!
//! The submodules here describe byte offsets and proof sections consumed by
//! both the generator and the generated Yul.

pub(crate) mod proof;

pub(crate) use proof::{ProofCalldataLayout, TranscriptBufferLayout};
