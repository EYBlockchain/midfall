//! Per-circuit Rust fixtures consumed by `bin/generate.rs` and the
//! test harness. Each submodule exposes a circuit-specific
//! `Relation` implementation plus a `*Fixture` struct that bundles
//! (SRS, VK, PK, instance, witness, proof) so the codegen + test
//! pipelines can treat each supported circuit uniformly.
//!
//! The generic verifier logic (transcript, identity evaluation,
//! linearization, multi_prepare, pairing) lives one level up in
//! `proofs/solidity-verifier/src/{codegen,expr_bytecode,transcript,eip2537,trace}.rs`
//! and is intended to be circuit-agnostic. Circuit specialisations
//! that still remain in `contracts/Verifier.sol` are tracked in
//! ARCHITECTURE.md §7.2.

pub mod ivc;
pub mod poseidon;
pub mod rsa_signature;
