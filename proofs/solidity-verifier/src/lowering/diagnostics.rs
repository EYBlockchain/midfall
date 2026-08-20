// SPDX-License-Identifier: CC0-1.0
//! Host-side diagnostics derived from the same lowering plan used for
//! rendering.

use crate::{
    api::{
        ProofEvaluationCounts, QuotientIdentityManifest, QuotientIdentityManifestEntry,
        QuotientIdentityManifestTarget,
    },
    lowering::{plan::LoweringPlan, protocol, VerifierBuildInputs},
};

/// Count proof-evaluation scalars in the same categories used by calldata
/// parsing and transcript absorption.
pub(crate) fn proof_evaluation_counts(
    inputs: VerifierBuildInputs<'_, '_>,
    plan: &LoweringPlan,
) -> ProofEvaluationCounts {
    debug_assert_eq!(
        inputs.num_committed_instances,
        inputs.meta.protocol.num_committed_instances
    );
    let meta = &plan.meta;

    // E5/E6/E7: a single pass over the executed proof-read schedule, instead
    // of twelve hand-maintained per-category formulas that could drift from
    // it. Fixed evals are query-based proof reads: the Rust verifier reads
    // the non-simple fixed queries that appear in `protocol.proof.evals`,
    // while simple selector columns are synthesized locally and feed selector
    // buckets instead of proof scalars. The categories not read from the
    // proof (locally interpolated instances, synthesized simple selectors,
    // set counts, dummy slots) come from the same protocol plan.
    let mut counts = ProofEvaluationCounts::default();
    for eval in &meta.protocol.proof.evals {
        match eval {
            protocol::EvalRead::CommittedInstance(_) => counts.committed_instance += 1,
            protocol::EvalRead::Advice(_) => counts.advice += 1,
            protocol::EvalRead::Fixed(_) => counts.fixed += 1,
            protocol::EvalRead::PermutationCommon { .. } => counts.permutation_common += 1,
            protocol::EvalRead::PermutationZ { .. } => counts.permutation_product += 1,
            protocol::EvalRead::LookupMultiplicity { .. } => counts.lookup_multiplicity += 1,
            protocol::EvalRead::LookupHelper { .. } => counts.lookup_helper += 1,
            protocol::EvalRead::LookupAccumulator { .. } => counts.lookup_accumulator += 1,
            protocol::EvalRead::Trash { .. } => counts.trash += 1,
        }
    }
    counts.computed_instance = meta.protocol.instance_queries.len() - counts.committed_instance;
    counts.simple_selector_fixed = meta.protocol.num_simple_selectors;
    counts.permutation_sets = meta.protocol.num_permutation_zs;
    counts.dummy = meta.num_dummy_evals();

    assert_eq!(
        counts.proof_total(),
        meta.num_evals(),
        "proof evaluation count accounting must match verifier proof layout"
    );
    counts
}

/// Build a stable source-indexed manifest for the generated quotient identity
/// stream.
pub(crate) fn quotient_identity_manifest(
    _inputs: VerifierBuildInputs<'_, '_>,
    plan: &LoweringPlan,
) -> QuotientIdentityManifest {
    let mut simple_selector_cols: Vec<usize> =
        plan.meta.protocol.simple_selector_cols.iter().copied().collect();
    simple_selector_cols.sort_unstable();

    // E8/G2: derived from the SAME execution walk that backs the frame
    // differential and `validate_execution_manifest` (a mandatory render
    // gate), instead of a second, independent re-walk of `vk.cs().gates()`
    // that could silently drift from the executed stream. Entries are
    // re-sorted into global (source) order for the public API.
    let mut entries: Vec<QuotientIdentityManifestEntry> = plan
        .quotient
        .plan
        .identities_in_execution_order()
        .expect("finalized plan walks its execution stream")
        .into_iter()
        .map(|(identity, _kind)| {
            let target = match identity.target {
                crate::lowering::quotient_numerator::vm::QuotientTarget::Main => {
                    QuotientIdentityManifestTarget::Main
                }
                crate::lowering::quotient_numerator::vm::QuotientTarget::Selector(
                    selector_index,
                ) => QuotientIdentityManifestTarget::Selector {
                    selector_index,
                    fixed_column: simple_selector_cols[selector_index],
                },
            };
            QuotientIdentityManifestEntry {
                global_index: identity.meta.global_index,
                source: identity.meta.source.clone(),
                target,
            }
        })
        .collect();
    entries.sort_by_key(|entry| entry.global_index);

    QuotientIdentityManifest {
        entries,
        gate_identities: plan.meta.protocol.quotient.gates,
        permutation_identities: plan.meta.protocol.quotient.permutation,
        lookup_identities: plan.meta.protocol.quotient.lookup,
        trash_identities: plan.meta.protocol.quotient.trash,
        simple_selector_cols,
    }
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Best-effort human label for a trash identity, consumed when
    /// `quotient_identity_parts` builds each identity's source metadata (the
    /// manifest inherits it from there).
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
