// SPDX-License-Identifier: CC0-1.0
//! Public API surface for the Solidity verifier crate.
//!
//! This module contains caller-facing configuration, diagnostics, and error
//! types. Keeping them outside the private codegen tree preserves stable
//! crate-root exports while letting the implementation modules move around.

use std::fmt;

use ruint::aliases::U256;

use crate::lowering::layout;

/// KZG accumulator encoding information.
///
/// Accumulator verification is opt-in. A generated verifier only batches a
/// public accumulator pairing equation into the final PLONK/KZG pairing when
/// [`GeneratorConfig::with_accumulator`] is used before constructing the
/// generator.
///
/// The accumulator is encoded as a tail of the non-committed public-input
/// vector, starting at [`Self::offset`]. The default Solidity decoder supports
/// Midnight's fully-collapsed BLS12-381 accumulator layout:
///
/// ```text
/// lhs point coordinates, lhs scalar, rhs point coordinates, rhs scalar
/// ```
///
/// with each BLS12-381 base-field coordinate represented as seven radix-2^56
/// limbs, packed four limbs per public-input field element. Any public-input
/// words after the fixed accumulator payload are interpreted as the optional
/// RHS fixed-base scalar tail for partially collapsed accumulators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AccumulatorEncoding {
    /// Offset of accumulator limbs in instances.
    pub offset: usize,
    /// Number of limbs per base field element.
    pub num_limbs: usize,
    /// Number of bits per limb.
    pub num_limb_bits: usize,
    /// Public-input accumulator layout.
    pub kind: AccumulatorEncodingKind,
}

/// Public-input layouts supported by the generated accumulator checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccumulatorEncodingKind {
    /// `AssignedAccumulator<S>::as_public_input`: lhs point, lhs scalar, rhs
    /// point, rhs scalar, followed by an optional fixed-base scalar tail.
    PointAndScalar,
    /// Already collapsed point-pair layout: lhs point, rhs point. The generated
    /// verifier treats both carried scalars as one and does not accept a
    /// fixed-base scalar tail.
    PointPair,
}

/// Committed-instance commitment policy supported by this generator.
///
/// The current Solidity verifier shape mirrors the Midfall/zk-stdlib path
/// where the committed-instance commitment absorbed into the transcript is the
/// G1 identity. It is not a generic committed-instance-column verifier for
/// caller-supplied commitments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommittedInstanceCommitmentKind {
    /// Absorb and use `G1::identity()` for every committed instance column.
    Identity,
}

impl AccumulatorEncoding {
    /// Supported limb count for one BLS12-381 base-field coordinate.
    pub const SUPPORTED_NUM_LIMBS: usize = layout::accumulator::LIMBS;
    /// Supported bits per accumulator limb.
    pub const SUPPORTED_NUM_LIMB_BITS: usize = layout::accumulator::LIMB_BITS;
    /// Public-input words required by the fully collapsed accumulator form.
    pub const FULLY_COLLAPSED_PUBLIC_INPUT_WORDS: usize = 10;
    /// Public-input words required by an already collapsed `(lhs, rhs)` point
    /// pair.
    pub const POINT_PAIR_PUBLIC_INPUT_WORDS: usize = 8;

    /// Return a new `AccumulatorEncoding`.
    pub fn new(offset: usize, num_limbs: usize, num_limb_bits: usize) -> Self {
        Self {
            offset,
            num_limbs,
            num_limb_bits,
            kind: AccumulatorEncodingKind::PointAndScalar,
        }
    }

    /// Return a point-pair accumulator encoding with implicit unit scalars.
    pub fn point_pair(offset: usize, num_limbs: usize, num_limb_bits: usize) -> Self {
        Self {
            offset,
            num_limbs,
            num_limb_bits,
            kind: AccumulatorEncodingKind::PointPair,
        }
    }

    /// Number of public-input words needed for one base-field coordinate.
    fn coordinate_words(self) -> usize {
        let limbs_per_instance = (254 / self.num_limb_bits).max(1);
        self.num_limbs.div_ceil(limbs_per_instance)
    }

    /// Number of public-input words for two G1 coordinates.
    fn point_pair_words(self) -> usize {
        4 * self.coordinate_words()
    }

    /// Whether this public-input layout carries explicit lhs/rhs scalars.
    pub(crate) fn has_carried_scalars(self) -> bool {
        matches!(self.kind, AccumulatorEncodingKind::PointAndScalar)
    }

    /// Number of public-input words occupied by the fixed accumulator payload.
    fn fixed_payload_words(self) -> usize {
        self.point_pair_words()
            + if self.has_carried_scalars() {
                layout::accumulator::CARRIED_SCALARS
            } else {
                0
            }
    }

    /// Minimum number of public-input words occupied by the accumulator tail,
    /// excluding any optional fixed-base scalar tail.
    pub fn fully_collapsed_public_input_words(self) -> Result<usize, GeneratorError> {
        self.validate_for_num_instances(usize::MAX)?;
        Ok(self.fixed_payload_words())
    }

    /// Validate this encoding against the generated verifier's supported
    /// schema.
    pub(crate) fn validate_for_num_instances(
        self,
        num_instances: usize,
    ) -> Result<(), GeneratorError> {
        if self.num_limbs != Self::SUPPORTED_NUM_LIMBS
            || self.num_limb_bits != Self::SUPPORTED_NUM_LIMB_BITS
        {
            return Err(GeneratorError::UnsupportedAccumulatorEncoding {
                offset: self.offset,
                num_limbs: self.num_limbs,
                num_limb_bits: self.num_limb_bits,
                num_instances,
                reason: "expected 7 radix-2^56 limbs per BLS12-381 base-field coordinate",
            });
        }

        let required_words = self.fixed_payload_words();
        if self.offset.saturating_add(required_words) > num_instances {
            return Err(GeneratorError::UnsupportedAccumulatorEncoding {
                offset: self.offset,
                num_limbs: self.num_limbs,
                num_limb_bits: self.num_limb_bits,
                num_instances,
                reason: "accumulator public-input tail exceeds num_instances",
            });
        }

        Ok(())
    }

    /// Number of optional fixed-base accumulator scalars after the fixed
    /// payload.
    pub(crate) fn fixed_scalar_count(self, num_instances: usize) -> Result<usize, GeneratorError> {
        self.validate_for_num_instances(num_instances)?;
        let tail = num_instances - (self.offset + self.fixed_payload_words());
        if self.kind == AccumulatorEncodingKind::PointPair && tail != 0 {
            return Err(GeneratorError::UnsupportedAccumulatorEncoding {
                offset: self.offset,
                num_limbs: self.num_limbs,
                num_limb_bits: self.num_limb_bits,
                num_instances,
                reason: "point-pair accumulator encoding does not support a fixed-base scalar tail",
            });
        }
        Ok(tail)
    }
}

/// Stable diagnostic view of the identities folded into the quotient numerator.
///
/// This is not part of the Solidity verifier ABI. It is a host-side inspection
/// API for confirming which custom gates and argument identities a generated
/// verifier will evaluate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuotientIdentityManifest {
    /// Identities in the exact global `y`-batch order used by the verifier.
    pub entries: Vec<QuotientIdentityManifestEntry>,
    /// Number of normal custom-gate polynomial identities.
    pub gate_identities: usize,
    /// Number of permutation identities.
    pub permutation_identities: usize,
    /// Number of lookup identities.
    pub lookup_identities: usize,
    /// Number of trash argument identities.
    pub trash_identities: usize,
    /// Fixed-column indices for simple selector buckets, sorted by column.
    pub simple_selector_cols: Vec<usize>,
}

/// One identity in the quotient numerator manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuotientIdentityManifestEntry {
    /// Position in the global `y`-batch.
    pub global_index: usize,
    /// Source family and source-local metadata.
    pub source: QuotientIdentitySource,
    /// Accumulation target for this identity.
    pub target: QuotientIdentityManifestTarget,
}

/// Source family for a quotient numerator identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QuotientIdentitySource {
    /// A normal custom-gate polynomial from `vk.cs().gates()`.
    Gate {
        /// Index in `ConstraintSystem::gates()`.
        gate_index: usize,
        /// Gate name recorded by `create_gate`.
        gate_name: String,
        /// Constraint/polynomial index inside the gate.
        constraint_index: usize,
        /// Constraint name recorded by the gate builder.
        constraint_name: String,
        /// Polynomial index inside the gate.
        polynomial_index: usize,
    },
    /// A permutation argument identity.
    Permutation {
        /// Identity index inside the permutation family.
        identity_index: usize,
    },
    /// A LogUp lookup argument identity.
    Lookup {
        /// Identity index inside the lookup family.
        identity_index: usize,
        /// Lookup argument index.
        lookup_index: usize,
        /// Lookup name recorded by the constraint system.
        lookup_name: String,
    },
    /// A trash argument identity.
    Trash {
        /// Trash argument index.
        trash_index: usize,
        /// Trash argument name, usually the source additive-selector gate name.
        trash_name: String,
    },
}

/// Destination of one manifest identity after its `y` position is consumed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuotientIdentityManifestTarget {
    /// Fully evaluated identity accumulated into the quotient numerator scalar.
    Main,
    /// Simple-selector identity accumulated into a selector commitment bucket.
    Selector {
        /// Bucket index in the sorted simple-selector list.
        selector_index: usize,
        /// Fixed column backing that simple selector.
        fixed_column: usize,
    },
}

/// Immutable generator configuration.
///
/// The constructor validates this entire shape up front. Post-construction
/// mutation is intentionally not supported, so render/repack paths always use
/// the same public-instance and accumulator schema.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GeneratorConfig {
    /// Number of non-committed public-input values expected by `verifyProof`.
    pub num_instances: usize,
    /// Number of instance columns committed to in the proof transcript.
    pub num_committed_instances: usize,
    /// Optional public accumulator pairing-batch encoding.
    pub accumulator: Option<AccumulatorEncoding>,
}

impl GeneratorConfig {
    /// Construct a generator config without accumulator verification.
    pub fn new(num_instances: usize, num_committed_instances: usize) -> Self {
        Self {
            num_instances,
            num_committed_instances,
            accumulator: None,
        }
    }

    /// Enable accumulator verification for this config.
    pub fn with_accumulator(mut self, accumulator: AccumulatorEncoding) -> Self {
        self.accumulator = Some(accumulator);
        self
    }
}

/// Whether the generated verifier embeds the VK or links to a separate VK
/// contract.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RenderVk {
    /// Embed the generated VK payload directly in `Halo2Verifier.sol`.
    #[default]
    Embedded,
    /// Render `Halo2Verifier.sol` plus `Halo2VerifyingKey.sol`.
    Separate,
}

/// Quotient numerator rendering strategy.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RenderQuotient {
    /// Render quotient reconstruction inside the verifier.
    #[default]
    Inline,
    /// Link to a separately deployed, hard-pinned quotient evaluator.
    ExternalPinned {
        /// Expected deployed runtime byte length.
        runtime_len: usize,
        /// Expected deployed runtime codehash.
        codehash: U256,
    },
}

/// Diagnostic render knobs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RenderDiagnostics {
    /// Emit trace logs.
    pub trace: bool,
    /// Emit section gas checkpoints.
    pub gas_checkpoints: bool,
}

impl Default for RenderDiagnostics {
    /// Default diagnostics are feature-gated so normal library callers get the
    /// same render shape as the crate was compiled for.
    fn default() -> Self {
        Self {
            trace: crate::SOLIDITY_TRACE_ENABLED,
            gas_checkpoints: crate::SOLIDITY_GAS_CHECKPOINTS_ENABLED,
        }
    }
}

/// Main render options for generated Solidity artifacts.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RenderOptions {
    /// VK artifact mode.
    pub vk: RenderVk,
    /// Quotient numerator artifact mode.
    pub quotient: RenderQuotient,
    /// Trace/gas diagnostic knobs.
    pub diagnostics: RenderDiagnostics,
    /// Optional 32-byte provenance tag folded into the emitted `BUILD_ID`
    /// constant (P10/L-8) — typically a hash of the generator git commit and
    /// build context, e.g. `keccak256("commit=<sha>,dirty=<bool>")`.
    ///
    /// `None` (the default) keeps `BUILD_ID` a pure function of the feature
    /// profile, VK, and SRS, so repository fixtures stay byte-stable across
    /// commits. Deployment builds SHOULD set it and publish the preimage in
    /// the deployment record; see
    /// `docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md`.
    pub provenance: Option<[u8; 32]>,
}

/// Rendered Solidity artifacts.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RenderedArtifacts {
    /// Always-rendered verifier source.
    pub verifier: String,
    /// Separate VK source when [`RenderVk::Separate`] is selected.
    pub verifying_key: Option<String>,
    /// Quotient evaluator source when [`RenderQuotient::ExternalPinned`] is
    /// selected.
    pub quotient_evaluator: Option<String>,
}

/// Errors from native-proof to Solidity-proof repacking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepackError {
    /// The native compressed proof does not match the generated proof schema.
    LengthMismatch {
        /// Expected native compressed proof byte length.
        expected: usize,
        /// Actual input byte length.
        actual: usize,
        /// Number of prefix compressed G1 commitments before scalar evals.
        prefix_g1: usize,
        /// Number of main evaluation scalars.
        num_evals: usize,
        /// Number of PCS point-set evaluation scalars.
        num_point_sets: usize,
    },
    /// One compressed G1 commitment failed host-side decompression.
    InvalidCompressedG1 {
        /// Byte offset of the failing compressed G1 in the native proof.
        offset: usize,
        /// Hex encoding of the failing 48-byte compressed G1.
        bytes_hex: String,
    },
    /// One proof scalar is not a canonical Fr element (`>= r`).
    NonCanonicalScalar {
        /// Byte offset of the failing scalar in the native proof.
        offset: usize,
        /// Big-endian hex encoding of the failing 32-byte scalar.
        bytes_hex: String,
    },
}

impl fmt::Display for RepackError {
    /// Format repack failures with byte-level context useful to callers.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LengthMismatch {
                expected,
                actual,
                prefix_g1,
                num_evals,
                num_point_sets,
            } => write!(
                f,
                "compressed proof length mismatch: expected {expected} bytes (prefix_g1={prefix_g1}, num_evals={num_evals}, num_point_sets={num_point_sets}, +f_com+pi), got {actual}"
            ),
            Self::InvalidCompressedG1 { offset, bytes_hex } => write!(
                f,
                "invalid compressed G1 at compressed[{offset}..{}]: bytes = 0x{bytes_hex}",
                offset + layout::G1_COMPRESSED_BYTES
            ),
            Self::NonCanonicalScalar { offset, bytes_hex } => write!(
                f,
                "non-canonical Fr scalar at compressed[{offset}..{}]: bytes = 0x{bytes_hex}",
                offset + layout::WORD_BYTES
            ),
        }
    }
}

impl std::error::Error for RepackError {}

/// Errors returned when a constraint system is outside the currently
/// supported Midfall Solidity verifier shape, or when generation/repacking
/// fails for the configured shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GeneratorError {
    /// A verifier with no advice commitments has no proof commitment phase to
    /// bind into the Fiat-Shamir transcript.
    NoAdviceColumns,
    /// The generated transcript and instance-evaluation path currently
    /// supports exactly one committed identity column and one non-committed
    /// public-input column.
    UnsupportedInstanceColumnShape {
        total: usize,
        committed: usize,
        expected_committed: usize,
        expected_non_committed: usize,
    },
    /// Instance columns are read as direct public inputs and locally
    /// Lagrange-interpolated only at the current row.
    RotatedInstanceQuery { column: usize, rotation: i32 },
    /// The optional public accumulator pairing batch currently supports only
    /// the Midnight BLS12-381 public-input encoding used by the IVC decider
    /// fixtures.
    UnsupportedAccumulatorEncoding {
        offset: usize,
        num_limbs: usize,
        num_limb_bits: usize,
        num_instances: usize,
        reason: &'static str,
    },
    /// The accumulator's fixed-base scalar tail asks for more bases than this
    /// verifying key can supply.
    ///
    /// The tail must be empty (fully collapsed accumulator), or cover `-G` plus
    /// every permutation commitment plus at most one scalar per fixed
    /// commitment.
    AccumulatorFixedBaseTailMismatch {
        /// Tail scalars implied by `num_instances` and the encoding.
        fixed_scalar_count: usize,
        /// Smallest non-empty tail this verifying key supports (`-G` plus every
        /// permutation commitment).
        min_fixed_scalar_count: usize,
        /// Largest tail this verifying key supports.
        max_fixed_scalar_count: usize,
        /// Fixed commitments in the verifying key.
        num_fixed_comms: usize,
        /// Permutation commitments in the verifying key.
        num_permutation_comms: usize,
    },
    /// Internal render/layout planning failed before Solidity was emitted.
    Planning {
        /// Planning stage.
        stage: &'static str,
        /// Human-readable error.
        message: String,
    },
    /// Formatting the Askama model into a Solidity string failed.
    Render {
        /// Artifact being rendered.
        artifact: &'static str,
    },
    /// Repacking a native proof into the Solidity ABI failed.
    Repack(RepackError),
}

impl fmt::Display for GeneratorError {
    /// Format typed generator errors as caller-facing diagnostics.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoAdviceColumns => {
                write!(f, "at least one advice column is required")
            }
            Self::UnsupportedInstanceColumnShape {
                total,
                committed,
                expected_committed,
                expected_non_committed,
            } => {
                let non_committed = total.checked_sub(*committed).map_or_else(
                    || format!("invalid: committed {committed} exceeds total {total}"),
                    |n| n.to_string(),
                );
                write!(
                    f,
                    "unsupported instance column shape: got total={total}, committed={committed}, non_committed={non_committed}; expected exactly {expected_committed} identity-committed and {expected_non_committed} non-committed"
                )
            }
            Self::RotatedInstanceQuery { column, rotation } => write!(
                f,
                "rotated instance query is not supported: column {column}, rotation {rotation}"
            ),
            Self::UnsupportedAccumulatorEncoding {
                offset,
                num_limbs,
                num_limb_bits,
                num_instances,
                reason,
            } => write!(
                f,
                "unsupported accumulator encoding: offset={offset}, num_limbs={num_limbs}, num_limb_bits={num_limb_bits}, num_instances={num_instances}; {reason}"
            ),
            Self::AccumulatorFixedBaseTailMismatch {
                fixed_scalar_count,
                min_fixed_scalar_count,
                max_fixed_scalar_count,
                num_fixed_comms,
                num_permutation_comms,
            } => write!(
                f,
                "accumulator fixed-base scalar tail of {fixed_scalar_count} is not supported by \
                 this verifying key ({num_fixed_comms} fixed, {num_permutation_comms} permutation \
                 commitments): expected 0 (fully collapsed) or \
                 {min_fixed_scalar_count}..={max_fixed_scalar_count}; adjust num_instances or the \
                 accumulator offset"
            ),
            Self::Planning { stage, message } => {
                write!(f, "generator planning failed during {stage}: {message}")
            }
            Self::Render { artifact } => write!(f, "failed to render {artifact}"),
            Self::Repack(err) => write!(f, "{err}"),
        }
    }
}

impl std::error::Error for GeneratorError {}

impl From<RepackError> for GeneratorError {
    /// Promote repacking failures into the generator's public error type.
    fn from(err: RepackError) -> Self {
        Self::Repack(err)
    }
}

/// Field-evaluation counts for the proof layout consumed by the generated
/// Solidity verifier.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ProofEvaluationCounts {
    /// Committed instance-query evaluations read from the proof.
    pub committed_instance: usize,
    /// Non-committed instance-query evaluations reconstructed from calldata
    /// public inputs, not read from the proof.
    pub computed_instance: usize,
    /// Advice-query evaluations read from the proof.
    pub advice: usize,
    /// Non-simple fixed-column evaluations read from the proof.
    pub fixed: usize,
    /// Simple selector fixed columns synthesized/handled via selector
    /// commitments instead of proof eval scalars.
    pub simple_selector_fixed: usize,
    /// Permutation common/sigma evaluations read from the proof.
    pub permutation_common: usize,
    /// Permutation product evaluations (`z_cur`, `z_next`, and non-final
    /// `z_last`) read from the proof.
    pub permutation_product: usize,
    /// Number of permutation product sets.
    pub permutation_sets: usize,
    /// Lookup multiplicity evaluations read from the proof.
    pub lookup_multiplicity: usize,
    /// Lookup helper evaluations read from the proof.
    pub lookup_helper: usize,
    /// Lookup accumulator evaluations (`z`, `z_next`) read from the proof.
    pub lookup_accumulator: usize,
    /// Trash argument evaluations read from the proof.
    pub trash: usize,
    /// Dummy eval scalars appended for the `fewer-point-sets` PCS layout.
    pub dummy: usize,
}

impl ProofEvaluationCounts {
    /// Main proof eval scalars, excluding dummy PCS evals.
    pub fn proof_main_total(&self) -> usize {
        self.committed_instance
            + self.advice
            + self.fixed
            + self.permutation_common
            + self.permutation_product
            + self.lookup_multiplicity
            + self.lookup_helper
            + self.lookup_accumulator
            + self.trash
    }

    /// All proof eval scalars consumed by the generated Solidity verifier.
    pub fn proof_total(&self) -> usize {
        self.proof_main_total() + self.dummy
    }

    /// Instance evals available to identity reconstruction, including those
    /// computed locally from public inputs.
    pub fn instance_total_for_identities(&self) -> usize {
        self.committed_instance + self.computed_instance
    }

    /// Total permutation eval scalars read from the proof.
    pub fn permutation_total(&self) -> usize {
        self.permutation_common + self.permutation_product
    }

    /// Total lookup eval scalars read from the proof.
    pub fn lookup_total(&self) -> usize {
        self.lookup_multiplicity + self.lookup_helper + self.lookup_accumulator
    }
}
