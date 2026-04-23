//! Execution trace recorder. Both the Rust and Solidity verifiers emit
//! ordered `(tag, value)` records as they execute. Comparing the two traces
//! proves that the Solidity verifier faithfully replays the algebraic
//! execution of the Rust verifier.

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "data")]
pub enum TraceEntry {
    /// A challenge squeezed from the transcript.
    Challenge { name: String, fe_be_hex: String },
    /// A field element read from the proof stream.
    ReadScalar { tag: String, fe_be_hex: String },
    /// A G1 point read from the proof stream (EIP-2537 encoded, 128 bytes).
    ReadPoint { tag: String, eip2537_hex: String },
    /// An intermediate scalar value computed by the verifier.
    Intermediate { tag: String, fe_be_hex: String },
    /// The final pairing check result (0x01 on success, 0x00 on failure).
    PairingResult { ok: bool },
}

#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct Trace {
    pub entries: Vec<TraceEntry>,
}

impl Trace {
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    pub fn challenge(&mut self, name: impl Into<String>, fe_be_hex: impl Into<String>) {
        self.entries.push(TraceEntry::Challenge {
            name: name.into(),
            fe_be_hex: fe_be_hex.into(),
        });
    }

    pub fn read_scalar(&mut self, tag: impl Into<String>, fe_be_hex: impl Into<String>) {
        self.entries.push(TraceEntry::ReadScalar {
            tag: tag.into(),
            fe_be_hex: fe_be_hex.into(),
        });
    }

    pub fn read_point(&mut self, tag: impl Into<String>, eip2537_hex: impl Into<String>) {
        self.entries.push(TraceEntry::ReadPoint {
            tag: tag.into(),
            eip2537_hex: eip2537_hex.into(),
        });
    }

    pub fn intermediate(&mut self, tag: impl Into<String>, fe_be_hex: impl Into<String>) {
        self.entries.push(TraceEntry::Intermediate {
            tag: tag.into(),
            fe_be_hex: fe_be_hex.into(),
        });
    }

    pub fn pairing(&mut self, ok: bool) {
        self.entries.push(TraceEntry::PairingResult { ok });
    }

    pub fn to_json_pretty(&self) -> String {
        serde_json::to_string_pretty(self).expect("serde can serialise Trace")
    }
}
