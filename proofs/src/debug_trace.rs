//! Thread-local trace recorder for intermediate verifier values.
//!
//! This module provides a minimal, always-present instrumentation surface
//! used by the PLONK verifier pipeline to emit intermediate scalars /
//! commitments / shape parameters at canonical points:
//!
//! * [`crate::plonk::partially_evaluate_identities`] — per-identity
//!   `(selector_column, scalar)` pairs and the aggregated Lagrange
//!   helpers `l_0`, `l_last`, `l_blind`.
//! * [`crate::plonk::linearization::verifier::compute_linearization_commitment`]
//!   — the quotient-limb scalars, the grouped identity points/scalars,
//!   and the negated constant term.
//! * [`crate::plonk::permutation::expressions`] — each of the produced
//!   permutation-argument expressions, in emission order.
//! * [`crate::plonk::logup::Evaluated::expressions`] — the boundary,
//!   helper-chunk, and accumulator expressions, in emission order.
//! * [`crate::plonk::trash::Evaluated::expressions`] — one expression
//!   per trashcan argument.
//! * [`crate::poly::kzg::KZGCommitmentScheme::multi_prepare`] — the
//!   challenges `x1`, `x2`, `x3`, `x4`, the sorted-set shapes, and the
//!   `f_eval` scalar resulting from the reverse-Horner Lagrange fold.
//!
//! When the `debug-trace-hooks` feature is disabled, every emission site
//! compiles to a no-op and this module exposes stubs only. When enabled,
//! [`start`] begins capture on the current thread and [`stop`] returns
//! the accumulated [`Event`] list in emission order.
//!
//! # Threading
//!
//! Capture is thread-local. If verification runs across multiple threads
//! (it currently does not), each thread records independently. The
//! callers in `proofs/solidity-verifier/src/bin/generate.rs` drive this
//! from a single thread.
//!
//! # Not a soundness surface
//!
//! Events here are purely observational. Enabling the feature must not
//! alter any value produced by the verifier; the instrumentation only
//! copies intermediates out of the hot path. If a caller observes a
//! divergence between enabled-feature and disabled-feature builds on
//! the same input, that is a bug in this module, not in the verifier.

#[cfg(feature = "debug-trace-hooks")]
use std::cell::RefCell;

use ff::PrimeField;

/// A single trace event emitted by an instrumented verifier function.
#[derive(Debug, Clone)]
pub struct Event {
    /// Short, stable human-readable tag identifying the emission site,
    /// e.g. `"partial_eval.x"`, `"permutation.expr"`, or
    /// `"multi_prepare.x1"`.
    pub tag: String,
    /// Raw payload bytes. For scalars this is the big-endian canonical
    /// 32-byte representation. For group elements this is the concrete
    /// payload chosen at the emission site (typically the `to_repr()`
    /// of the compressed encoding). For u64/i32 shape parameters this
    /// is the big-endian integer bytes.
    pub payload: Vec<u8>,
}

#[cfg(feature = "debug-trace-hooks")]
thread_local! {
    static TRACE: RefCell<Option<Vec<Event>>> = const { RefCell::new(None) };
}

/// Begin recording trace events on the current thread.
///
/// Any previously-recorded events are discarded. After this call, every
/// call to [`emit`] / [`emit_scalar`] / [`emit_u64`] / [`emit_i32`] /
/// [`emit_usize`] / [`emit_bytes`] will push into a per-thread buffer
/// until [`stop`] is called.
#[cfg(feature = "debug-trace-hooks")]
pub fn start() {
    TRACE.with(|t| *t.borrow_mut() = Some(Vec::new()));
}

/// Stop recording and return the captured events in emission order.
///
/// If recording was not active, returns an empty vector.
#[cfg(feature = "debug-trace-hooks")]
pub fn stop() -> Vec<Event> {
    TRACE.with(|t| t.borrow_mut().take().unwrap_or_default())
}

/// Returns `true` if a trace is currently being recorded on this thread.
#[inline]
pub fn is_enabled() -> bool {
    #[cfg(feature = "debug-trace-hooks")]
    {
        TRACE.with(|t| t.borrow().is_some())
    }
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        false
    }
}

/// Emit an event with raw bytes payload.
///
/// No-op if recording is not active or the feature is disabled.
#[inline]
pub fn emit(tag: &str, bytes: Vec<u8>) {
    #[cfg(feature = "debug-trace-hooks")]
    TRACE.with(|t| {
        if let Some(events) = t.borrow_mut().as_mut() {
            events.push(Event {
                tag: tag.to_string(),
                payload: bytes,
            });
        }
    });
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        let _ = (tag, bytes);
    }
}

/// Emit a scalar field element as its canonical 32-byte big-endian
/// representation. Uses `PrimeField::to_repr()` (little-endian by
/// convention) and reverses to big-endian so downstream consumers
/// can load the bytes directly with `mload` / uint256 readers.
#[inline]
pub fn emit_scalar<F: PrimeField>(tag: &str, v: &F) {
    #[cfg(feature = "debug-trace-hooks")]
    {
        if is_enabled() {
            let repr = v.to_repr();
            let mut bytes = repr.as_ref().to_vec();
            bytes.reverse();
            emit(tag, bytes);
        }
    }
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        let _ = (tag, v);
    }
}

/// Emit a `u64` value as 8 big-endian bytes.
#[inline]
pub fn emit_u64(tag: &str, v: u64) {
    #[cfg(feature = "debug-trace-hooks")]
    emit(tag, v.to_be_bytes().to_vec());
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        let _ = (tag, v);
    }
}

/// Emit an `i32` value as 4 big-endian bytes.
#[inline]
pub fn emit_i32(tag: &str, v: i32) {
    #[cfg(feature = "debug-trace-hooks")]
    emit(tag, v.to_be_bytes().to_vec());
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        let _ = (tag, v);
    }
}

/// Emit a `usize` value as 8 big-endian bytes (truncated to u64).
#[inline]
pub fn emit_usize(tag: &str, v: usize) {
    emit_u64(tag, v as u64);
}

/// Emit a borrowed byte slice as the payload.
#[inline]
pub fn emit_bytes(tag: &str, bytes: &[u8]) {
    #[cfg(feature = "debug-trace-hooks")]
    emit(tag, bytes.to_vec());
    #[cfg(not(feature = "debug-trace-hooks"))]
    {
        let _ = (tag, bytes);
    }
}
