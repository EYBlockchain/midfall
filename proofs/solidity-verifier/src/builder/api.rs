// SPDX-License-Identifier: CC0-1.0
//! Public and crate-local constructor/configuration methods for
//! `SolidityGenerator`.
//!
//! This slice owns validation of the supported proof shape and exposes the
//! stable caller-facing knobs before lower-level generation starts.

use sha3::{Digest, Keccak256};

use super::*;

impl<'a> SolidityGenerator<'a> {
    /// Number of committed instance columns supported by the generated ABI.
    pub(super) const SUPPORTED_COMMITTED_INSTANCE_COLUMNS: usize = 1;
    /// Number of non-committed instance columns supported by the generated ABI.
    pub(super) const SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS: usize = 1;
    /// Committed-instance commitment policy hard-coded by the generated
    /// verifier ABI.
    pub const SUPPORTED_COMMITTED_INSTANCE_COMMITMENT: CommittedInstanceCommitmentKind =
        CommittedInstanceCommitmentKind::Identity;

    /// Return a new `SolidityGenerator`.
    pub fn new(
        params: &'a ParamsKZG<Bls12>,
        vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        config: GeneratorConfig,
    ) -> Self {
        Self::try_new(params, vk, config)
            .unwrap_or_else(|err| panic!("unsupported Solidity verifier shape: {err}"))
    }

    /// Try to construct a new `SolidityGenerator`, returning a typed error
    /// when the supplied constraint system is outside the currently supported
    /// Midfall verifier shape.
    pub fn try_new(
        params: &'a ParamsKZG<Bls12>,
        vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
        config: GeneratorConfig,
    ) -> Result<Self, GeneratorError> {
        if vk.cs().num_advice_columns() == 0 {
            return Err(GeneratorError::NoAdviceColumns);
        }
        // Midfall's Rust verifier receives instances in two arguments:
        // committed instances and normal (non-committed) instances. The
        // total number of instance columns is their sum, with committed
        // columns first in verifier order (`plonk/verifier.rs::verify_proof`).
        Self::validate_instance_column_shape(
            vk.cs().num_instance_columns(),
            config.num_committed_instances,
        )?;
        if let Some(acc_encoding) = config.accumulator {
            acc_encoding.validate_for_num_instances(config.num_instances)?;
        }
        if let Some((column, rotation)) = vk
            .cs()
            .instance_queries()
            .iter()
            .find(|(_, rotation)| *rotation != Rotation::cur())
        {
            return Err(GeneratorError::RotatedInstanceQuery {
                column: column.index(),
                rotation: rotation.0,
            });
        }

        let meta = ConstraintSystemMeta::new(vk.cs(), config.num_committed_instances);

        Ok(Self {
            params,
            vk,
            num_instances: config.num_instances,
            acc_encoding: config.accumulator,
            meta,
        })
    }

    /// Return the committed-instance commitment policy for this generator.
    pub fn committed_instance_commitment_kind(&self) -> CommittedInstanceCommitmentKind {
        Self::SUPPORTED_COMMITTED_INSTANCE_COMMITMENT
    }

    /// Validate the currently supported committed/non-committed instance split.
    pub(super) fn validate_instance_column_shape(
        total_instance_columns: usize,
        num_committed_instances: usize,
    ) -> Result<(), GeneratorError> {
        // The Rust verifier accepts committed and normal instance arguments
        // separately, with committed instance columns first. The current
        // Solidity calldata ABI supports exactly one identity-committed column
        // and one direct public-input column, so every instance query can be
        // classified without an extra column-routing table or supplied
        // committed-instance commitment.
        let supported_committed = Self::SUPPORTED_COMMITTED_INSTANCE_COLUMNS;
        let supported_non_committed = Self::SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS;
        let non_committed = total_instance_columns
            .checked_sub(num_committed_instances)
            .unwrap_or(usize::MAX);

        if num_committed_instances != supported_committed
            || non_committed != supported_non_committed
        {
            return Err(GeneratorError::UnsupportedInstanceColumnShape {
                total: total_instance_columns,
                committed: num_committed_instances,
                expected_committed: supported_committed,
                expected_non_committed: supported_non_committed,
            });
        }

        Ok(())
    }

    /// Return the exact field-evaluation counts for the proof layout consumed
    /// by the generated Solidity verifier.
    pub fn proof_evaluation_counts(&self) -> ProofEvaluationCounts {
        crate::lowering::diagnostics::proof_evaluation_counts(self.inputs())
    }

    /// Return a stable host-side manifest of quotient numerator identities.
    ///
    /// This diagnostic API follows the same source ordering as the generated
    /// quotient evaluator: normal gates, permutation, lookup, then trash.
    pub fn quotient_identity_manifest(&self) -> QuotientIdentityManifest {
        crate::lowering::diagnostics::quotient_identity_manifest(self.inputs())
    }

    /// Return the artifact-bound quotient certificate for this generator.
    ///
    /// The certificate is derived from the same finalized lowering plan used by
    /// rendering and proof repacking. Its canonical hash is stored in the
    /// generated VK payload and checked by the verifier, but it is not absorbed
    /// into the Fiat-Shamir transcript.
    pub fn quotient_certificate(&self) -> QuotientCertificate {
        crate::lowering::diagnostics::quotient_certificate(self.inputs())
    }

    /// Return the canonical quotient certificate hash.
    pub fn quotient_certificate_hash(&self) -> U256 {
        crate::lowering::diagnostics::quotient_certificate_hash(self.inputs())
    }

    /// Emit a release assurance report for already-rendered artifacts.
    ///
    /// The report is JSON text containing source hashes, feature flags, render
    /// mode, quotient certificate hashes, and caller-supplied heavy-gate
    /// summaries. It fails closed when required heavy EVM/trace or mutation
    /// evidence is skipped or missing.
    pub fn release_assurance_report(
        &self,
        options: RenderOptions,
        artifacts: &RenderedArtifacts,
        evidence: ReleaseAssuranceEvidence,
    ) -> Result<String, GeneratorError> {
        if !evidence.heavy_evm_trace_gates_passed {
            return Err(GeneratorError::ReleaseAssuranceGateMissing {
                gate: "heavy_evm_trace",
            });
        }
        if evidence.trace_coverage_summary.trim().is_empty() {
            return Err(GeneratorError::ReleaseAssuranceGateMissing {
                gate: "trace_coverage_summary",
            });
        }
        if !evidence.mutation_tests_passed {
            return Err(GeneratorError::ReleaseAssuranceGateMissing {
                gate: "mutation_tests",
            });
        }
        if evidence.mutation_test_summary.trim().is_empty() {
            return Err(GeneratorError::ReleaseAssuranceGateMissing {
                gate: "mutation_test_summary",
            });
        }

        let certificate = self.quotient_certificate();
        let quotient_pin = match options.quotient {
            RenderQuotient::Inline => {
                r#"{"mode":"inline","expected_runtime_len":null,"expected_codehash":null}"#
                    .to_string()
            }
            RenderQuotient::ExternalPinned {
                runtime_len,
                codehash,
            } => format!(
                r#"{{"mode":"external_pinned","expected_runtime_len":{runtime_len},"expected_codehash":{}}}"#,
                json_string(&u256_hex(codehash))
            ),
        };
        let report = format!(
            concat!(
                "{{\n",
                r#"  "schema": "midfall.solidity-verifier.release-assurance.v1","#,
                "\n",
                r#"  "render_mode": {{"vk": {}, "quotient": {}, "trace": {}, "gas_checkpoints": {}}},"#,
                "\n",
                r#"  "feature_flags": {{"evm": {}, "solidity_trace": {}, "solidity_gas_checkpoints": {}, "truncated_challenges": {}, "in_circuit_fewer_point_sets": {}, "outer_fewer_point_sets": {}, "outer_single_h_commitment": {}, "fewer_point_sets": {}, "rust_verifier_trace": {}}},"#,
                "\n",
                r#"  "artifacts": {{"verifier": {}, "verifying_key": {}, "quotient_evaluator": {}}},"#,
                "\n",
                r#"  "quotient": {{"certificate_hash": {}, "vm_bytecode_hash": {}, "constants_hash": {}, "identity_count": {}, "selector_bucket_count": {}, "gate_identities": {}, "permutation_identities": {}, "lookup_identities": {}, "trash_identities": {}}},"#,
                "\n",
                r#"  "external_quotient_pin": {},"#,
                "\n",
                r#"  "gates": {{"heavy_evm_trace": {{"passed": true, "summary": {}}}, "mutation_tests": {{"passed": true, "summary": {}}}}}"#,
                "\n",
                "}}\n"
            ),
            json_string(match options.vk {
                RenderVk::Embedded => "embedded",
                RenderVk::Separate => "separate",
            }),
            json_string(match options.quotient {
                RenderQuotient::Inline => "inline",
                RenderQuotient::ExternalPinned { .. } => "external_pinned",
            }),
            options.diagnostics.trace,
            options.diagnostics.gas_checkpoints,
            cfg!(feature = "evm"),
            cfg!(feature = "solidity-trace"),
            cfg!(feature = "solidity-gas-checkpoints"),
            cfg!(feature = "truncated-challenges"),
            cfg!(feature = "in-circuit-fewer-point-sets"),
            cfg!(feature = "outer-fewer-point-sets"),
            cfg!(feature = "outer-single-h-commitment"),
            cfg!(feature = "fewer-point-sets"),
            cfg!(feature = "rust-verifier-trace"),
            artifact_json(Some(&artifacts.verifier)),
            artifact_json(artifacts.verifying_key.as_deref()),
            artifact_json(artifacts.quotient_evaluator.as_deref()),
            json_string(&u256_hex(certificate.certificate_hash)),
            json_string(&u256_hex(certificate.vm_bytecode_hash)),
            json_string(&u256_hex(certificate.quotient_constants_hash)),
            certificate.entries.len(),
            certificate.simple_selector_cols.len(),
            certificate.gate_identities,
            certificate.permutation_identities,
            certificate.lookup_identities,
            certificate.trash_identities,
            quotient_pin,
            json_string(&evidence.trace_coverage_summary),
            json_string(&evidence.mutation_test_summary),
        );
        Ok(report)
    }
}

fn artifact_json(source: Option<&str>) -> String {
    match source {
        Some(source) => format!(
            r#"{{"present":true,"source_len_bytes":{},"source_keccak256":{}}}"#,
            source.len(),
            json_string(&u256_hex(keccak_u256(source.as_bytes())))
        ),
        None => r#"{"present":false,"source_len_bytes":0,"source_keccak256":null}"#.to_string(),
    }
}

fn keccak_u256(bytes: &[u8]) -> U256 {
    let mut hasher = Keccak256::new();
    hasher.update(bytes);
    let digest: [u8; 32] = hasher.finalize().into();
    U256::from_be_bytes(digest)
}

fn u256_hex(value: U256) -> String {
    format!("{value:#066x}")
}

fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}
