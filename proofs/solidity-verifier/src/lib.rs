// SPDX-License-Identifier: CC0-1.0
//! Solidity verifier generator for midnight-proofs with KZG polynomial
//! commitment scheme on BLS12-381 / EIP-2537.
//!
//! Historical migration notes live in `docs/architecture/MIGRATION.md`.

#![deny(missing_debug_implementations)]
#![deny(rustdoc::broken_intra_doc_links)]

mod api;
mod builder;
mod evm;
mod lowering;

#[cfg(all(test, feature = "evm"))]
mod test;

#[cfg(feature = "evm")]
#[doc(hidden)]
pub use api::QuotientProbeArtifacts;
pub use api::{
    AccumulatorEncoding, AccumulatorEncodingKind, GeneratorConfig, GeneratorError,
    ProofEvaluationCounts, QuotientIdentityManifest, QuotientIdentityManifestEntry,
    QuotientIdentityManifestTarget, QuotientIdentitySource, QuotientLowering, RenderDiagnostics,
    RenderOptions, RenderQuotient, RenderVk, RenderedArtifacts, RepackError,
};
pub use builder::SolidityGenerator;
pub use evm::{encode_calldata, FN_SIG_VERIFY_PROOF};

/// First trace id of the direct quotient lowering's helper-call results
/// (`sum_exprs` / `sum_exprs_by_degree`), numbered in identity order,
/// left-first inside an identity. See `docs/reference/TRACE_VARIABLES.md`.
pub const DIRECT_TRACE_HELPER_BASE: u64 =
    lowering::quotient_numerator::direct::trace::DIRECT_HELPER_TRACE_BASE;
/// First trace id of the direct lowering's product-table entries `T[t]`.
pub const DIRECT_TRACE_PRODUCT_TABLE_BASE: u64 =
    lowering::quotient_numerator::direct::trace::DIRECT_PRODUCT_TABLE_TRACE_BASE;
/// First trace id of the direct lowering's limb-view words.
pub const DIRECT_TRACE_LIMB_VIEW_BASE: u64 =
    lowering::quotient_numerator::direct::trace::DIRECT_LIMB_VIEW_TRACE_BASE;
/// End (exclusive) of the direct lowering's trace id range.
pub const DIRECT_TRACE_END: u64 = lowering::quotient_numerator::direct::trace::DIRECT_TRACE_END;

/// Whether the default Solidity renderer emits trace logs.
///
/// Enable with `--features solidity-trace`. `RenderDiagnostics { trace: true,
/// .. }` still forces trace output regardless of this flag.
pub const SOLIDITY_TRACE_ENABLED: bool = cfg!(feature = "solidity-trace");

/// Whether the default Solidity renderer emits LOG1 gas() checkpoints at
/// section boundaries. The host-side test parses these into per-section gas
/// deltas (see `dump_gas_checkpoints` in `tests/poseidon_fixture.rs`).
///
/// Default render paths honor `solidity-gas-checkpoints` independently from
/// `solidity-trace`, so gas attribution can be measured without trace-only
/// verifier work. `RenderDiagnostics { gas_checkpoints: true, .. }` still
/// forces checkpoint emission for profiling artifacts regardless of this flag.
pub const SOLIDITY_GAS_CHECKPOINTS_ENABLED: bool = cfg!(feature = "solidity-gas-checkpoints");

/// Whether the generated Solidity verifier expects the outer proof to use
/// the fewer-point-sets dummy-query PCS layout.
///
/// This is intentionally separate from recursive/in-circuit verifier proofs:
/// the IVC benchmark can keep fewer point sets for proofs checked inside the
/// decider circuit while emitting the final Solidity-facing proof without the
/// extra dummy eval scalars.
pub const OUTER_FEWER_POINT_SETS_ENABLED: bool = cfg!(feature = "outer-fewer-point-sets");

/// Whether the generated Solidity verifier expects the outer proof to use
/// Midnight's single-H quotient commitment layout.
///
/// This is intentionally outer-only. Recursive proofs checked inside the IVC
/// decider circuit remain on the multi-limb layout from `midnight-circuits`.
pub const OUTER_SINGLE_H_COMMITMENT_ENABLED: bool = cfg!(feature = "outer-single-h-commitment");

#[cfg(feature = "evm")]
pub use evm::test::{
    compile_solidity, compile_solidity_with_runs, pinned_solc_available, revm, solc_version,
    CallOutcome, Evm, ALLOW_UNPINNED_SOLC_ENV, DEFAULT_OPTIMIZE_RUNS, PINNED_SOLC_VERSION,
};

/// Test-only helper that exposes the internal BLS12-381 G1 to EIP-2537
/// hi/lo encoder so debugging examples can re-encode host-computed
/// points using the exact same pipeline the Solidity verifier consumes.
#[doc(hidden)]
pub fn __test_only_g1_to_u256s(point: &midnight_curves::G1Affine) -> [ruint::aliases::U256; 4] {
    crate::lowering::encoding::g1_to_u256s(point)
}

#[doc(hidden)]
pub fn __test_only_g2_to_u256s(point: &midnight_curves::G2Affine) -> [ruint::aliases::U256; 8] {
    crate::lowering::encoding::g2_to_u256s(point)
}
