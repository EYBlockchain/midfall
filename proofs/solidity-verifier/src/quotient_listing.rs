// SPDX-License-Identifier: CC0-1.0
//! Auditor-facing decoder for the compact quotient-VM program.
//!
//! [`SolidityGenerator::render`](crate::SolidityGenerator::render) emits, next
//! to the Solidity sources, a text listing
//! ([`RenderedArtifacts::quotient_listing`](crate::RenderedArtifacts::quotient_listing))
//! and a JSON manifest
//! ([`RenderedArtifacts::quotient_manifest`](crate::RenderedArtifacts::quotient_manifest))
//! of the quotient-VM program stored in the VK payload.
//!
//! This module exposes the part of the listing that depends only on the
//! deployed VK bytes and on the names published in the manifest, so the
//! `quotient_listing` example can regenerate it from a deployed
//! `Halo2VerifyingKey` without running the generator:
//!
//! * [`render_program_blocks`] decodes the program, checks the VM stack
//!   discipline, renders one [`ProgramBlock`] per identity-stream item
//!   (instructions, every sub-term of the dynamic opcodes, and the identity
//!   polynomial rebuilt from the bytes), and fails unless the rendered lines
//!   cover every program byte exactly once;
//! * [`extract_program_blocks`] pulls the same blocks out of a shipped listing
//!   for a textual comparison;
//! * [`relocate_program_pointers`] maps a program between two memory layouts
//!   that differ by a uniform shift (for example a VK with one extra header
//!   word).
//!
//! See `docs/reference/QUOTIENT_LISTING.md` for the file formats and the
//! auditor workflow.

pub use crate::lowering::quotient_listing::blocks::{
    extract_program_blocks, readable_constant, relocate_program_pointers, render_program_blocks,
    ListingSymbols, ProgramBlock, ProgramBlockKind, ProgramFold, PROGRAM_BLOCK_BEGIN,
    PROGRAM_BLOCK_END,
};

/// `format` field of the JSON manifest.
pub const MANIFEST_FORMAT: &str = crate::lowering::quotient_listing::MANIFEST_FORMAT;
/// `format_version` field of the JSON manifest.
pub const MANIFEST_FORMAT_VERSION: usize =
    crate::lowering::quotient_listing::MANIFEST_FORMAT_VERSION;
