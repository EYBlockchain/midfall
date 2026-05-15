// SPDX-License-Identifier: CC0-1.0
//! Host-side diagnostics derived from the same lowering plan used for
//! rendering.

use crate::{
    api::{
        ProofEvaluationCounts, QuotientIdentityManifest, QuotientIdentityManifestEntry,
        QuotientIdentityManifestTarget, QuotientIdentitySource,
    },
    lowering::{protocol, VerifierBuildInputs},
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
    let plan = inputs.lowering_plan();
    let mut simple_selector_cols: Vec<usize> =
        plan.meta.simple_selector_cols.iter().copied().collect();
    simple_selector_cols.sort_unstable();

    let gate_entries = inputs
        .vk
        .cs()
        .gates()
        .iter()
        .enumerate()
        .flat_map(|(gate_index, gate)| {
            let target = gate
                .queried_selectors()
                .iter()
                .find(|selector| selector.is_simple())
                .map(|selector| {
                    let selector_index = simple_selector_cols
                        .iter()
                        .position(|fixed| *fixed == selector.index())
                        .expect("simple selector fixed column present");
                    QuotientIdentityManifestTarget::Selector {
                        selector_index,
                        fixed_column: selector.index(),
                    }
                })
                .unwrap_or(QuotientIdentityManifestTarget::Main);

            (0..gate.polynomials().len()).map(move |polynomial_index| {
                (
                    gate_index,
                    gate.name().to_string(),
                    polynomial_index,
                    gate.constraint_name(polynomial_index).to_string(),
                    target,
                )
            })
        })
        .enumerate()
        .map(
            |(global_index, (gate_index, gate_name, polynomial_index, constraint_name, target))| {
                QuotientIdentityManifestEntry {
                    global_index,
                    source: QuotientIdentitySource::Gate {
                        gate_index,
                        gate_name,
                        constraint_index: polynomial_index,
                        constraint_name,
                        polynomial_index,
                    },
                    target,
                }
            },
        )
        .collect::<Vec<_>>();
    let permutation_base = gate_entries.len();
    let lookup_base = permutation_base + plan.meta.protocol.quotient.permutation;
    let trash_base = lookup_base + plan.meta.protocol.quotient.lookup;

    let entries = gate_entries
        .into_iter()
        .chain(
            (0..plan.meta.protocol.quotient.permutation).map(|identity_index| {
                QuotientIdentityManifestEntry {
                    global_index: permutation_base + identity_index,
                    source: QuotientIdentitySource::Permutation { identity_index },
                    target: QuotientIdentityManifestTarget::Main,
                }
            }),
        )
        .chain(
            (0..plan.meta.protocol.quotient.lookup).map(|identity_index| {
                let (lookup_index, _) = plan
                    .meta
                    .protocol
                    .lookup_identity_source(identity_index)
                    .expect("lookup identity index covered by protocol lookup chunks");
                let lookup_name = format!("lookup_{lookup_index}");
                QuotientIdentityManifestEntry {
                    global_index: lookup_base + identity_index,
                    source: QuotientIdentitySource::Lookup {
                        identity_index,
                        lookup_index,
                        lookup_name,
                    },
                    target: QuotientIdentityManifestTarget::Main,
                }
            }),
        )
        .chain((0..plan.meta.protocol.quotient.trash).map(|trash_index| {
            let trash_name = inputs.trash_manifest_name(trash_index);
            QuotientIdentityManifestEntry {
                global_index: trash_base + trash_index,
                source: QuotientIdentitySource::Trash {
                    trash_index,
                    trash_name,
                },
                target: QuotientIdentityManifestTarget::Main,
            }
        }))
        .collect();

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
