// SPDX-License-Identifier: CC0-1.0
//! Host-side diagnostics derived from the same lowering plan used for
//! rendering.

use ruint::aliases::U256;
use sha3::{Digest, Keccak256};

use crate::{
    api::{
        ProofEvaluationCounts, QuotientCertificate, QuotientCertificateEntry,
        QuotientIdentityExecution, QuotientIdentityManifest, QuotientIdentityManifestEntry,
        QuotientIdentityManifestTarget, QuotientIdentitySource,
    },
    lowering::{
        protocol,
        quotient_numerator::vm::{
            QuotientExecutionKind, QuotientExecutionManifestEntry, QuotientExpr, QuotientMem,
            QuotientProgramBuild, QuotientProgramPlan, QuotientTarget,
        },
        VerifierBuildInputs,
    },
};

/// Count proof-evaluation scalars in the same categories used by calldata
/// parsing and transcript absorption.
pub(crate) fn proof_evaluation_counts(
    inputs: VerifierBuildInputs<'_, '_>,
) -> ProofEvaluationCounts {
    debug_assert_eq!(
        inputs.num_committed_instances,
        inputs.meta.num_committed_instances
    );
    let plan = inputs.lowering_plan();
    let meta = &plan.meta;

    let committed_instance = meta
        .instance_queries
        .iter()
        .filter(|(col, _)| *col < meta.num_committed_instances)
        .count();
    let computed_instance = meta.instance_queries.len() - committed_instance;
    let permutation_product = if meta.num_permutation_zs == 0 {
        0
    } else {
        3 * meta.num_permutation_zs - 1
    };
    let lookup_helper = meta.lookup_chunks.iter().sum();

    let counts = ProofEvaluationCounts {
        committed_instance,
        computed_instance,
        advice: meta.advice_queries.len(),
        // Fixed evals are query-based proof reads. The Rust verifier
        // reads the non-simple fixed queries that appear in
        // `protocol.proof.evals`; simple selector columns are synthesized
        // locally and feed selector buckets instead of proof scalars.
        fixed: meta
            .protocol
            .proof
            .evals
            .iter()
            .filter(|eval| matches!(eval, protocol::EvalRead::Fixed(_)))
            .count(),
        simple_selector_fixed: meta.num_simple_selectors,
        permutation_common: meta.permutation_columns.len(),
        permutation_product,
        permutation_sets: meta.num_permutation_zs,
        lookup_multiplicity: meta.num_lookups,
        lookup_helper,
        lookup_accumulator: 2 * meta.num_lookups,
        trash: meta.num_trashcans,
        dummy: meta.num_dummy_evals,
    };

    assert_eq!(
        counts.proof_total(),
        meta.num_evals,
        "proof evaluation count accounting must match verifier proof layout"
    );
    counts
}

/// Build a stable source-indexed manifest for the generated quotient identity
/// stream.
pub(crate) fn quotient_identity_manifest(
    inputs: VerifierBuildInputs<'_, '_>,
) -> QuotientIdentityManifest {
    let certificate = quotient_certificate(inputs);
    QuotientIdentityManifest {
        entries: certificate
            .entries
            .iter()
            .map(|entry| QuotientIdentityManifestEntry {
                global_index: entry.global_index,
                source: entry.source.clone(),
                target: entry.target,
            })
            .collect(),
        gate_identities: certificate.gate_identities,
        permutation_identities: certificate.permutation_identities,
        lookup_identities: certificate.lookup_identities,
        trash_identities: certificate.trash_identities,
        simple_selector_cols: certificate.simple_selector_cols,
    }
}

/// Build the artifact-bound quotient certificate from the finalized lowering
/// plan used by render/repack paths.
pub(crate) fn quotient_certificate(inputs: VerifierBuildInputs<'_, '_>) -> QuotientCertificate {
    let plan = inputs.lowering_plan();

    quotient_certificate_from_parts(
        &plan.meta.protocol.quotient,
        &plan.quotient.plan,
        &plan.quotient.build,
        &plan.quotient.sorted_simple,
    )
}

/// Return the canonical quotient certificate hash.
pub(crate) fn quotient_certificate_hash(inputs: VerifierBuildInputs<'_, '_>) -> U256 {
    quotient_certificate(inputs).certificate_hash
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Best-effort human label for a trash identity.
    ///
    /// Empty-polynomial gates are the usual source because trash arguments are
    /// created from additive selectors. If the gate metadata is unavailable,
    /// fall back to the constraint-system trash list and finally to a stable
    /// synthetic name.
    pub(crate) fn trash_manifest_name(&self, trash_index: usize) -> String {
        if let Some(gate) = self
            .vk
            .cs()
            .gates()
            .iter()
            .filter(|gate| gate.polynomials().is_empty())
            .nth(trash_index)
        {
            return gate.name().to_string();
        }

        self.vk
            .cs()
            .trashcans()
            .get(trash_index)
            .map(|trash| trash.name().to_string())
            .unwrap_or_else(|| format!("trash_{trash_index}"))
    }
}

pub(crate) fn quotient_certificate_hash_for_plan(
    plan: &crate::lowering::plan::LoweringPlan,
) -> U256 {
    quotient_certificate_hash_from_parts(
        &plan.meta.protocol.quotient,
        &plan.quotient.plan,
        &plan.quotient.build,
        &plan.quotient.sorted_simple,
    )
}

pub(crate) fn quotient_certificate_hash_from_parts(
    quotient_counts: &protocol::QuotientIdentityPlan,
    quotient_plan: &QuotientProgramPlan,
    quotient_build: &QuotientProgramBuild,
    sorted_simple: &[usize],
) -> U256 {
    quotient_certificate_from_parts(
        quotient_counts,
        quotient_plan,
        quotient_build,
        sorted_simple,
    )
    .certificate_hash
}

pub(crate) fn quotient_certificate_from_parts(
    quotient_counts: &protocol::QuotientIdentityPlan,
    quotient_plan: &QuotientProgramPlan,
    quotient_build: &QuotientProgramBuild,
    sorted_simple: &[usize],
) -> QuotientCertificate {
    let execution_entries = quotient_plan
        .execution_manifest()
        .expect("validated quotient execution manifest");
    let vm_bytecode_hash = hash_bytes(b"midfall.qcert.bytecode.v1", &quotient_build.bytes);
    let quotient_constants_hash =
        hash_u256_words(b"midfall.qcert.constants.v1", &quotient_build.consts);
    let entries = execution_entries
        .iter()
        .map(|entry| {
            let expression_encoding = canonical_expr_encoding(&entry.expr);
            QuotientCertificateEntry {
                global_index: entry.global_index,
                source: entry.source.clone(),
                target: quotient_manifest_target(entry.target, sorted_simple),
                selector_gap: quotient_plan
                    .selector_fold
                    .gaps_by_identity
                    .get(entry.global_index)
                    .copied()
                    .flatten(),
                execution: quotient_execution_kind(entry.execution),
                expression_hash: hash_bytes(b"midfall.qcert.expr.v1", &expression_encoding),
                expression_encoding_len: expression_encoding.len(),
            }
        })
        .collect::<Vec<_>>();
    let mut certificate = QuotientCertificate {
        version: 1,
        entries,
        gate_identities: quotient_counts.gates,
        permutation_identities: quotient_counts.permutation,
        lookup_identities: quotient_counts.lookup,
        trash_identities: quotient_counts.trash,
        simple_selector_cols: sorted_simple.to_vec(),
        selector_tail_exponents: quotient_plan.selector_fold.tail_exponents.clone(),
        vm_bytecode_hash,
        quotient_constants_hash,
        certificate_hash: U256::ZERO,
    };
    certificate.certificate_hash = quotient_certificate_hash_for(&certificate, &execution_entries);
    certificate
}

fn quotient_certificate_hash_for(
    certificate: &QuotientCertificate,
    execution_entries: &[QuotientExecutionManifestEntry],
) -> U256 {
    let mut out = Vec::new();
    put_bytes(&mut out, b"midfall.quotient.certificate.v1");
    put_u64(&mut out, certificate.version as u64);
    put_usize(&mut out, certificate.gate_identities);
    put_usize(&mut out, certificate.permutation_identities);
    put_usize(&mut out, certificate.lookup_identities);
    put_usize(&mut out, certificate.trash_identities);
    put_usize_vec(&mut out, &certificate.simple_selector_cols);
    put_usize_vec(&mut out, &certificate.selector_tail_exponents);
    put_u256(&mut out, certificate.vm_bytecode_hash);
    put_u256(&mut out, certificate.quotient_constants_hash);
    put_usize(&mut out, execution_entries.len());
    for (pos, entry) in execution_entries.iter().enumerate() {
        put_usize(&mut out, entry.global_index);
        encode_source(&mut out, &entry.source);
        encode_target(&mut out, entry.target);
        match entry
            .target
            .selector_index()
            .and_then(|_| certificate.entries[pos].selector_gap)
        {
            Some(gap) => {
                out.push(1);
                put_usize(&mut out, gap);
            }
            None => out.push(0),
        }
        encode_execution(&mut out, certificate.entries[pos].execution);
        let expr = canonical_expr_encoding(&entry.expr);
        put_bytes(&mut out, &expr);
    }
    hash_bytes(b"midfall.qcert.root.v1", &out)
}

trait QuotientTargetExt {
    fn selector_index(self) -> Option<usize>;
}

impl QuotientTargetExt for QuotientTarget {
    fn selector_index(self) -> Option<usize> {
        match self {
            QuotientTarget::Main => None,
            QuotientTarget::Selector(idx) => Some(idx),
        }
    }
}

fn quotient_manifest_target(
    target: QuotientTarget,
    sorted_simple: &[usize],
) -> QuotientIdentityManifestTarget {
    match target {
        QuotientTarget::Main => QuotientIdentityManifestTarget::Main,
        QuotientTarget::Selector(selector_index) => QuotientIdentityManifestTarget::Selector {
            selector_index,
            fixed_column: sorted_simple[selector_index],
        },
    }
}

fn quotient_execution_kind(execution: QuotientExecutionKind) -> QuotientIdentityExecution {
    match execution {
        QuotientExecutionKind::Inline => QuotientIdentityExecution::Inline,
        QuotientExecutionKind::Interpreted => QuotientIdentityExecution::Interpreted,
        QuotientExecutionKind::NativePermutation => QuotientIdentityExecution::NativePermutation,
        QuotientExecutionKind::NativeLookup => QuotientIdentityExecution::NativeLookup,
        QuotientExecutionKind::NativeIdentity { native_index } => {
            QuotientIdentityExecution::NativeIdentity { native_index }
        }
        QuotientExecutionKind::StructuredTail => QuotientIdentityExecution::StructuredTail,
    }
}

fn canonical_expr_encoding(expr: &QuotientExpr) -> Vec<u8> {
    let mut out = Vec::new();
    encode_expr(&mut out, expr);
    out
}

fn encode_expr(out: &mut Vec<u8>, expr: &QuotientExpr) {
    match expr {
        QuotientExpr::Const(value) => {
            out.push(1);
            put_u256(out, *value);
        }
        QuotientExpr::Mem(mem) => {
            out.push(2);
            encode_mem(out, *mem);
        }
        QuotientExpr::Add(lhs, rhs) => {
            out.push(3);
            encode_expr(out, lhs);
            encode_expr(out, rhs);
        }
        QuotientExpr::Mul(lhs, rhs) => {
            out.push(4);
            encode_expr(out, lhs);
            encode_expr(out, rhs);
        }
        QuotientExpr::Neg(inner) => {
            out.push(5);
            encode_expr(out, inner);
        }
    }
}

fn encode_mem(out: &mut Vec<u8>, mem: QuotientMem) {
    match mem {
        QuotientMem::Literal(ptr) => {
            out.push(1);
            put_u64(out, ptr as u64);
        }
        QuotientMem::Token(token) => {
            out.push(2);
            out.push(token);
        }
        QuotientMem::TokenOffset(token, offset) => {
            out.push(3);
            out.push(token);
            put_u64(out, offset as u64);
        }
    }
}

fn encode_source(out: &mut Vec<u8>, source: &QuotientIdentitySource) {
    match source {
        QuotientIdentitySource::Gate {
            gate_index,
            constraint_index,
            polynomial_index,
            ..
        } => {
            out.push(1);
            put_usize(out, *gate_index);
            put_usize(out, *constraint_index);
            put_usize(out, *polynomial_index);
        }
        QuotientIdentitySource::Permutation { identity_index } => {
            out.push(2);
            put_usize(out, *identity_index);
        }
        QuotientIdentitySource::Lookup {
            identity_index,
            lookup_index,
            ..
        } => {
            out.push(3);
            put_usize(out, *identity_index);
            put_usize(out, *lookup_index);
        }
        QuotientIdentitySource::Trash { trash_index, .. } => {
            out.push(4);
            put_usize(out, *trash_index);
        }
    }
}

fn encode_target(out: &mut Vec<u8>, target: QuotientTarget) {
    match target {
        QuotientTarget::Main => out.push(1),
        QuotientTarget::Selector(selector_index) => {
            out.push(2);
            put_usize(out, selector_index);
        }
    }
}

fn encode_execution(out: &mut Vec<u8>, execution: QuotientIdentityExecution) {
    match execution {
        QuotientIdentityExecution::Inline => out.push(1),
        QuotientIdentityExecution::Interpreted => out.push(2),
        QuotientIdentityExecution::NativePermutation => out.push(3),
        QuotientIdentityExecution::NativeLookup => out.push(4),
        QuotientIdentityExecution::NativeIdentity { native_index } => {
            out.push(5);
            put_usize(out, native_index);
        }
        QuotientIdentityExecution::StructuredTail => out.push(6),
    }
}

fn hash_u256_words(domain: &[u8], words: &[U256]) -> U256 {
    let mut out = Vec::new();
    put_usize(&mut out, words.len());
    for word in words {
        put_u256(&mut out, *word);
    }
    hash_bytes(domain, &out)
}

fn hash_bytes(domain: &[u8], bytes: &[u8]) -> U256 {
    let mut hasher = Keccak256::new();
    hasher.update(domain);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    let digest: [u8; 32] = hasher.finalize().into();
    U256::from_be_bytes(digest)
}

fn put_usize_vec(out: &mut Vec<u8>, values: &[usize]) {
    put_usize(out, values.len());
    for value in values {
        put_usize(out, *value);
    }
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_usize(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn put_usize(out: &mut Vec<u8>, value: usize) {
    put_u64(
        out,
        u64::try_from(value).expect("certificate usize fits u64"),
    );
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

fn put_u256(out: &mut Vec<u8>, value: U256) {
    out.extend_from_slice(&value.to_be_bytes::<32>());
}
