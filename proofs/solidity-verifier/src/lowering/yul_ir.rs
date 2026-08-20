// SPDX-License-Identifier: CC0-1.0
//! Typed building blocks for generated Yul (roadmap P5.c).
//!
//! The generated verifier's staged lookup/permutation tables used to be
//! emitted as `mstore(...)` TEXT and then re-scanned by a string pass that
//! parsed `mload(0x...)` back out of each line to discover copy runs. This
//! module carries the source of each table entry as a typed value instead, so
//! run detection is arithmetic over addresses the planner already knows.
//!
//! Scope note: this deliberately starts with the one construct that has a
//! production consumer today ([`TableFill`]). A general `YulStmt`/`Scope`
//! statement IR is only worth introducing when a second emitter (the PCS
//! block) migrates onto it; until then it would be an unused abstraction.

use crate::lowering::encoding::{Location, Value, Word};

/// Source of one staged-table entry.
#[derive(Clone, Debug)]
pub(crate) enum YulValue {
    /// A generated word handle. Memory-backed words at literal addresses can
    /// participate in copy-run compression; calldata or symbolic handles
    /// render as individual stores.
    Word(Word),
    /// A pre-rendered Yul expression, such as the constant `0x1` synthesized
    /// for a simple-selector column that has no proof evaluation.
    Literal(String),
}

impl YulValue {
    /// Absolute memory address this value loads from, when it is a
    /// memory-backed word at a known literal address.
    fn mem_literal(&self) -> Option<usize> {
        match self {
            Self::Word(word) if word.loc() == Location::Memory => match word.ptr().value() {
                Value::Integer(offset) if offset >= 0 => Some(offset as usize),
                _ => None,
            },
            _ => None,
        }
    }
}

impl std::fmt::Display for YulValue {
    /// Render the load expression.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Word(word) => write!(f, "{word}"),
            Self::Literal(text) => f.write_str(text),
        }
    }
}

impl From<Word> for YulValue {
    /// Treat a generated word handle as a table source.
    fn from(word: Word) -> Self {
        Self::Word(word)
    }
}

/// A staged table written into one destination base pointer.
///
/// Entries are `(destination byte offset, source)`; adjacent entries whose
/// destinations advance by one word and whose sources advance by a constant
/// stride are emitted as a copy loop instead of individual stores.
#[derive(Debug)]
pub(crate) struct TableFill<'a> {
    /// Yul expression for the destination base pointer.
    dst: &'a str,
    /// Prefix for the generated loop's local variables.
    loop_prefix: &'a str,
    /// Table entries in destination order.
    entries: Vec<(usize, YulValue)>,
}

/// Minimum run length worth turning into a copy loop. Shorter runs stay as
/// straight-line stores, where the loop's own setup would cost more than it
/// saves.
const MIN_RUN_LEN: usize = 3;

/// Word size of the staged tables, in bytes.
const WORD_BYTES: usize = 0x20;

impl<'a> TableFill<'a> {
    /// Start a table fill for `dst`, naming loop locals from `loop_prefix`.
    pub(crate) fn new(dst: &'a str, loop_prefix: &'a str) -> Self {
        Self {
            dst,
            loop_prefix,
            entries: Vec::new(),
        }
    }

    /// Append one entry at `dst_offset` bytes past the destination base.
    pub(crate) fn push(&mut self, dst_offset: usize, value: impl Into<YulValue>) {
        self.entries.push((dst_offset, value.into()));
    }

    /// Emit the table fill, compressing regular copy runs into loops.
    pub(crate) fn render_into(self, block: &mut Vec<String>) {
        let Self {
            dst,
            loop_prefix,
            entries,
        } = self;

        let mut idx = 0usize;
        while idx < entries.len() {
            let (dst_base, value) = &entries[idx];
            match Self::run_length(&entries, idx) {
                Some((src_base, src_stride, count)) => {
                    block.push("{".to_string());
                    block.push(format!(
                        "for {{ let {loop_prefix}_i := 0 }} lt({loop_prefix}_i, {count}) {{ {loop_prefix}_i := add({loop_prefix}_i, 1) }} {{"
                    ));
                    block.push(format!(
                        "let {loop_prefix}_dst_off := shl(5, {loop_prefix}_i)"
                    ));
                    if src_stride == WORD_BYTES {
                        block.push(format!(
                            "let {loop_prefix}_src_off := {loop_prefix}_dst_off"
                        ));
                    } else {
                        block.push(format!(
                            "let {loop_prefix}_src_off := mul({loop_prefix}_i, {src_stride:#x})"
                        ));
                    }
                    block.push(format!(
                        "mstore(add(add({dst}, {dst_base:#x}), {loop_prefix}_dst_off), mload(add({src_base:#x}, {loop_prefix}_src_off)))"
                    ));
                    block.push("}".to_string());
                    block.push("}".to_string());
                    idx += count;
                }
                None => {
                    block.push(format!("mstore(add({dst}, {dst_base:#x}), {value})"));
                    idx += 1;
                }
            }
        }
    }

    /// Length of the compressible copy run starting at `idx`, with its source
    /// base and stride, when one exists.
    ///
    /// A run needs at least [`MIN_RUN_LEN`] entries whose destinations advance
    /// by exactly one word and whose memory-literal sources advance by a
    /// constant nonzero stride.
    fn run_length(entries: &[(usize, YulValue)], idx: usize) -> Option<(usize, usize, usize)> {
        let (dst_base, value) = entries.get(idx)?;
        let src_base = value.mem_literal()?;
        let (next_dst, next_value) = entries.get(idx + 1)?;
        if *next_dst != dst_base + WORD_BYTES {
            return None;
        }
        let src_stride = next_value.mem_literal()?.checked_sub(src_base)?;
        if src_stride == 0 {
            return None;
        }

        let mut count = 2usize;
        while let Some((candidate_dst, candidate_value)) = entries.get(idx + count) {
            let Some(candidate_src) = candidate_value.mem_literal() else {
                break;
            };
            if *candidate_dst != dst_base + count * WORD_BYTES
                || candidate_src != src_base + count * src_stride
            {
                break;
            }
            count += 1;
        }

        (count >= MIN_RUN_LEN).then_some((src_base, src_stride, count))
    }
}
