//! Trace hooks for differential testing of generated Solidity verifiers.
//!
//! This module is intentionally small and byte-oriented: the Rust verifier
//! records the exact scalar/G1 bytes that correspond to generated Solidity
//! trace logs, and downstream harnesses can compare those bytes without
//! reimplementing verifier algebra.

use std::cell::RefCell;

use crate::transcript::{Hashable, TranscriptHash, TranscriptInputBytes};

thread_local! {
    static EVENTS: RefCell<Option<Vec<SolidityTraceEvent>>> = const { RefCell::new(None) };
}

/// One Rust verifier trace item, keyed by the generated Solidity trace ID.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolidityTraceEvent {
    /// Solidity trace topic ID.
    pub id: u64,
    /// Stable human-readable name for diagnostics.
    pub name: &'static str,
    /// Trace payload bytes. Scalars are 32 bytes; G1 points are the
    /// transcript's EIP-2537 padded 128-byte representation.
    pub data: Vec<u8>,
}

/// Start collecting trace events on the current thread.
pub fn start() {
    EVENTS.with(|events| {
        *events.borrow_mut() = Some(Vec::new());
    });
}

/// Stop collecting and return all events collected on the current thread.
pub fn take() -> Vec<SolidityTraceEvent> {
    EVENTS.with(|events| events.borrow_mut().take().unwrap_or_default())
}

pub(crate) fn record_bytes(id: u64, name: &'static str, data: impl Into<Vec<u8>>) {
    EVENTS.with(|events| {
        if let Some(events) = events.borrow_mut().as_mut() {
            events.push(SolidityTraceEvent {
                id,
                name,
                data: data.into(),
            });
        }
    });
}

pub(crate) fn record_u64(id: u64, name: &'static str, value: u64) {
    let mut data = vec![0u8; 32];
    data[24..32].copy_from_slice(&value.to_be_bytes());
    record_bytes(id, name, data);
}

pub(crate) fn record_hashable<H, T>(id: u64, name: &'static str, value: &T)
where
    H: TranscriptHash,
    H::Input: TranscriptInputBytes,
    T: Hashable<H>,
{
    record_bytes(id, name, value.to_input().into_trace_bytes());
}
