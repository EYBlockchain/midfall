//! Solidity port of the [`midnight_proofs::plonk::verifier`] KZG/PLONK
//! verifier, specialised for the poseidon example from
//! [`zk_stdlib/examples/poseidon.rs`]. This crate provides a runtime
//! code generator that, given a `VerifyingKey` and a proof built with the
//! Keccak256 Fiat-Shamir transcript, produces:
//!
//! * `PoseidonVerifyingKey.sol` — a tiny constants-only contract
//!   (constructor that returns a concatenated bytes blob with all the
//!   circuit-specific fields).
//! * `PoseidonVerifier.sol` — the verifier logic, using EIP-2537
//!   (Prague) BLS12-381 precompiles and Keccak256 transcript.
//!
//! The Rust side of this crate also exposes a [`TracingTranscript`] that
//! records every challenge/read so that we can compare its execution with
//! the Solidity verifier's and verify both implementations agree.

pub mod trace;
pub mod codegen;
pub mod transcript;
pub mod eip2537;
pub mod poseidon_fixture;
pub mod expr_bytecode;
