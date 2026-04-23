//! A thin wrapper around `midnight_proofs::transcript::CircuitTranscript<Keccak256>`
//! that records every operation performed on it in a [`Trace`]. The wrapped
//! transcript behaves *exactly* like the canonical one, so proofs produced
//! for the vanilla `CircuitTranscript<Keccak256>` can be verified with it.
//!
//! Instead of trying to intercept generically inside the `Transcript` impl,
//! we expose explicit helpers (`read_fq`, `read_g1`, `squeeze_fq`, …) that
//! record on behalf of the caller. The caller should use these in place of
//! the generic `read()` / `squeeze_challenge()` calls to participate in the
//! trace; all arithmetic operations that do not touch the transcript are
//! recorded separately via [`Trace::intermediate`].

use std::{cell::RefCell, io, rc::Rc};

use group::GroupEncoding;
use midnight_curves::{Fq, G1Projective};
use midnight_proofs::transcript::{CircuitTranscript, Transcript};
use sha3::Keccak256;

use crate::{eip2537, trace::Trace};

#[derive(Clone)]
pub struct TracingTranscript {
    inner: CircuitTranscript<Keccak256>,
    pub trace: Rc<RefCell<Trace>>,
}

impl TracingTranscript {
    pub fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::<Keccak256>::init_from_bytes(bytes),
            trace: Rc::new(RefCell::new(Trace::new())),
        }
    }

    pub fn trace(&self) -> Trace {
        self.trace.borrow().clone()
    }

    /// Squeeze a Fq challenge and record it.
    pub fn squeeze_fq(&mut self, name: &str) -> Fq {
        let out: Fq = self.inner.squeeze_challenge();
        self.trace.borrow_mut().challenge(name, eip2537::fq_to_be_hex(&out));
        out
    }

    /// Read a Fq scalar and record it.
    pub fn read_fq(&mut self, tag: &str) -> io::Result<Fq> {
        let v: Fq = self.inner.read()?;
        self.trace.borrow_mut().read_scalar(tag, eip2537::fq_to_be_hex(&v));
        Ok(v)
    }

    /// Returns the current position in the proof buffer (for diagnostics).
    pub fn pos(&mut self) -> u64 {
        self.inner.buffer().position()
    }



    /// Read a G1 point and record it.
    pub fn read_g1(&mut self, tag: &str) -> io::Result<G1Projective> {
        let pos_before = self.inner.buffer().position();
        let v: G1Projective = self.inner.read().map_err(|e| {
            let buf = self.inner.buffer();
            let data = buf.get_ref();
            let peek: String = data
                .iter()
                .skip(pos_before as usize)
                .take(48)
                .map(|b| format!("{:02x}", b))
                .collect();
            io::Error::other(format!(
                "read_g1(tag={tag}) at pos {pos_before} bytes={peek}: {e}"
            ))
        })?;
        // Record the *compressed* 48-byte encoding — this is what ends up
        // in the proof and on the wire. The trace comparison uses this
        // canonical representation on both sides.
        let compressed = <G1Projective as GroupEncoding>::to_bytes(&v);
        self.trace
            .borrow_mut()
            .read_point(tag, hex::encode(compressed.as_ref()));
        let _ = eip2537::g1_projective_to_eip2537(&v); // retained for later callers
        Ok(v)
    }

    pub fn common_fq(&mut self, v: &Fq) -> io::Result<()> {
        self.inner.common(v)
    }

    pub fn common_g1(&mut self, v: &G1Projective) -> io::Result<()> {
        self.inner.common(v)
    }

    /// Borrow the inner transcript mutably so we can pass it through to the
    /// canonical verifier (e.g. `vk.hash_into`).
    pub fn inner_mut(&mut self) -> &mut CircuitTranscript<Keccak256> {
        &mut self.inner
    }
}
