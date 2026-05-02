//! Trace hooks for differential testing of generated Solidity verifiers.
//!
//! This module is intentionally small and byte-oriented: the Rust verifier
//! records the exact scalar/G1 bytes that correspond to generated Solidity
//! trace logs, and downstream harnesses can compare those bytes without
//! reimplementing verifier algebra.

use std::cell::RefCell;

use crate::transcript::{Hashable, TranscriptHash, TranscriptInputBytes};

/// First trace topic used for proof G1 commitments, in proof-read order.
pub const PROOF_COMMITMENT_TRACE_BASE: u64 = 10_000;
/// First trace topic used for proof scalar evaluations, in proof-read order.
pub const PROOF_EVAL_TRACE_BASE: u64 = 20_000;
/// First trace topic used for raw quotient identity evaluations.
pub const QUOTIENT_IDENTITY_TRACE_BASE: u64 = 30_000;
/// First trace topic used for per-point-set PCS `q_com` commitments.
pub const PCS_Q_COM_TRACE_BASE: u64 = 40_000;
/// Trace topic used for the materialized linearization commitment.
pub const LINEARIZATION_COMMITMENT_TRACE_ID: u64 = 34;

#[derive(Debug, Default)]
struct SolidityTraceState {
    events: Vec<SolidityTraceEvent>,
    proof_commitments: u64,
    proof_evals: u64,
}

thread_local! {
    static EVENTS: RefCell<Option<SolidityTraceState>> = const { RefCell::new(None) };
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
        *events.borrow_mut() = Some(SolidityTraceState {
            events: Vec::new(),
            proof_commitments: 0,
            proof_evals: 0,
        });
    });
}

/// Stop collecting and return all events collected on the current thread.
pub fn take() -> Vec<SolidityTraceEvent> {
    EVENTS.with(|events| events.borrow_mut().take().map(|state| state.events).unwrap_or_default())
}

/// Record an already-rendered byte payload under a Solidity trace topic ID.
pub fn record_bytes(id: u64, name: &'static str, data: impl Into<Vec<u8>>) {
    EVENTS.with(|events| {
        if let Some(state) = events.borrow_mut().as_mut() {
            state.events.push(SolidityTraceEvent {
                id,
                name,
                data: data.into(),
            });
        }
    });
}

/// Record a `u64` as a 32-byte big-endian Solidity word.
pub fn record_u64(id: u64, name: &'static str, value: u64) {
    let mut data = vec![0u8; 32];
    data[24..32].copy_from_slice(&value.to_be_bytes());
    record_bytes(id, name, data);
}

/// Record a transcript-hashable value using its diagnostic trace bytes.
pub fn record_hashable<H, T>(id: u64, name: &'static str, value: &T)
where
    H: TranscriptHash,
    H::Input: TranscriptInputBytes,
    T: Hashable<H>,
{
    record_bytes(id, name, value.to_input().into_trace_bytes());
}

/// Record the next proof commitment read from the transcript.
pub fn record_proof_commitment<H, T>(name: &'static str, value: &T)
where
    H: TranscriptHash,
    H::Input: TranscriptInputBytes,
    T: Hashable<H>,
{
    EVENTS.with(|events| {
        if let Some(state) = events.borrow_mut().as_mut() {
            let id = PROOF_COMMITMENT_TRACE_BASE + state.proof_commitments;
            state.proof_commitments += 1;
            state.events.push(SolidityTraceEvent {
                id,
                name,
                data: value.to_input().into_trace_bytes(),
            });
        }
    });
}

/// Record the next proof scalar evaluation read from the transcript.
pub fn record_proof_eval<H, T>(name: &'static str, value: &T)
where
    H: TranscriptHash,
    H::Input: TranscriptInputBytes,
    T: Hashable<H>,
{
    EVENTS.with(|events| {
        if let Some(state) = events.borrow_mut().as_mut() {
            let id = PROOF_EVAL_TRACE_BASE + state.proof_evals;
            state.proof_evals += 1;
            state.events.push(SolidityTraceEvent {
                id,
                name,
                data: value.to_input().into_trace_bytes(),
            });
        }
    });
}
