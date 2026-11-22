//! Shared conformance-bundle serialisers (WID.3).
//!
//! Extracted verbatim from `tests/conformance_export.rs` so that the F1
//! (poseidon) exporter and the F2 (IVC decider) exporter write the SAME
//! schema for a key and its constraint system. Nothing here computes a new
//! value: every field goes through a public accessor of `VerifyingKey`,
//! `ConstraintSystem` or `Expression`.
//!
//! The F1 exporter's output must stay byte-identical apart from added keys
//! (REF.11's additive-schema rule), so this module is a move and not a
//! rewrite.

#![allow(dead_code)]

use group::Curve;
use midnight_curves::{Bls12, Fq, G1Projective};
use midnight_proofs::{
    plonk::{Any, ConstraintSystem, Expression, VerifyingKey},
    poly::kzg::KZGCommitmentScheme,
    transcript::Hashable,
};
use serde_json::json;
use sha3::Keccak256;

pub type F = Fq;
pub type Vk = VerifyingKey<F, KZGCommitmentScheme<Bls12>>;

/// A field element as big-endian hex, through the transcript's own encoder.
pub fn be_hex(x: &F) -> String {
    hex::encode(<F as Hashable<Keccak256>>::to_input(x))
}

/// A compressed G1 point, through the transcript's own encoder.
pub fn point_hex(p: &G1Projective) -> String {
    hex::encode(<G1Projective as Hashable<Keccak256>>::to_bytes(p))
}

/// A compressed G2 point (affine compressed form).
pub fn g2_hex(p: &midnight_curves::G2Projective) -> String {
    use group::GroupEncoding;
    hex::encode(p.to_affine().to_bytes().as_ref())
}

/// One `Expression<F>` as data. The variant set mirrors
/// `proofs/src/plonk/circuit.rs:824-849` one for one and every payload is read
/// through a PUBLIC accessor. `degree` is carried on every node because it is
/// the only thing the plan path reads of an expression.
pub fn expr_json(e: &Expression<F>) -> serde_json::Value {
    let deg = e.degree();
    match e {
        Expression::Constant(c) => json!({"k": "constant", "f": be_hex(c), "degree": deg}),
        Expression::Selector(s) => json!({
            "k": "selector", "index": s.index(), "is_simple": s.is_simple(), "degree": deg
        }),
        Expression::Fixed(q) => json!({
            "k": "fixed", "index": q.index(), "col": q.column_index(),
            "rot": q.rotation().0, "degree": deg
        }),
        Expression::Advice(q) => json!({
            "k": "advice", "index": q.index, "col": q.column_index(),
            "rot": q.rotation().0, "phase": q.phase(), "degree": deg
        }),
        Expression::Instance(q) => json!({
            "k": "instance", "index": q.index, "col": q.column_index(),
            "rot": q.rotation().0, "degree": deg
        }),
        Expression::Challenge(c) => json!({
            "k": "challenge", "index": c.index(), "phase": c.phase(), "degree": deg
        }),
        Expression::Negated(a) => json!({"k": "negated", "a": expr_json(a), "degree": deg}),
        Expression::Sum(a, b) => json!({
            "k": "sum", "a": expr_json(a), "b": expr_json(b), "degree": deg
        }),
        Expression::Product(a, b) => json!({
            "k": "product", "a": expr_json(a), "b": expr_json(b), "degree": deg
        }),
        Expression::Scaled(a, s) => json!({
            "k": "scaled", "a": expr_json(a), "f": be_hex(s), "degree": deg
        }),
    }
}

/// `vk.json` for ANY verifying key and any public-input count. The F1 call is
/// `verifying_key_json(vk, pi.len(), 1)`; the F2 call is the same function on
/// the decider key with its own 16-word instance.
pub fn verifying_key_json(vk: &Vk, num_public_inputs: usize, num_committed_instances: usize)
    -> serde_json::Value
{
    let cs = vk.cs();
    let domain = vk.get_domain();
    let selector_flags: Vec<_> = (0..cs.num_fixed_columns())
        .map(|i| json!({"is_simple": cs.has_simple_selector_col(i), "col_idx": i}))
        .collect();
    let instance_queries: Vec<_> =
        cs.instance_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();
    let advice_queries: Vec<_> =
        cs.advice_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();
    let fixed_queries: Vec<_> =
        cs.fixed_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();

    json!({
        "schema": 1,
        "k": domain.k(),
        "n": vk.n(),
        "omega_be_hex": be_hex(&domain.get_omega()),
        "omega_inv_be_hex": be_hex(&domain.get_omega_inv()),
        "cs_degree": cs.degree(),
        "quotient_poly_degree": domain.get_quotient_poly_degree(),
        "transcript_repr_be_hex": be_hex(&vk.transcript_repr()),
        "num_advice_columns": cs.num_advice_columns(),
        "num_fixed_columns": cs.num_fixed_columns(),
        "num_instance_columns": cs.num_instance_columns(),
        "num_challenges": cs.num_challenges(),
        "nb_public_inputs": num_public_inputs,
        "num_committed_instances": num_committed_instances,
        "fixed_commitments_compressed_hex": vk.fixed_commitments().iter().map(point_hex).collect::<Vec<_>>(),
        "permutation_commitments_compressed_hex": vk.permutation().commitments().iter().map(point_hex).collect::<Vec<_>>(),
        "advice_column_phase": cs.advice_column_phase(),
        "selector_flags": selector_flags,
        "instance_queries": instance_queries,
        "advice_queries": advice_queries,
        "fixed_queries": fixed_queries,
        "blinding_factors": cs.blinding_factors(),
        "num_lookups": cs.lookups().len(),
        "num_trashcans": cs.trashcans().len(),
        "truncated_challenges": true,
        "scalar_num_bits": <F as ff::PrimeField>::NUM_BITS,
        "extended_k": domain.extended_k(),
    })
}

/// `cs.json` for ANY constraint system. `source` names the exporter that wrote
/// it, so the two bundles are distinguishable without a second file.
pub fn constraint_system_json(cs: &ConstraintSystem<F>, source: &str) -> serde_json::Value {
    let cs_degree = cs.degree();
    let perm_cols = cs.permutation().get_columns();
    let permutation_columns: Vec<_> = perm_cols
        .iter()
        .map(|c| match c.column_type() {
            Any::Advice(a) => json!({"type": "advice", "index": c.index(), "phase": a.phase()}),
            Any::Fixed => json!({"type": "fixed", "index": c.index(), "phase": null}),
            Any::Instance => json!({"type": "instance", "index": c.index(), "phase": null}),
        })
        .collect();
    let gates: Vec<_> = cs
        .gates()
        .iter()
        .map(|g| {
            json!({
                "name": g.name(),
                "constraint_names": (0..g.polynomials().len())
                    .map(|i| g.constraint_name(i).to_string())
                    .collect::<Vec<_>>(),
                "polys": g.polynomials().iter().map(expr_json).collect::<Vec<_>>(),
                "queried_selectors": g.queried_selectors().iter()
                    .map(|s| json!({"index": s.index(), "is_simple": s.is_simple()}))
                    .collect::<Vec<_>>(),
            })
        })
        .collect();
    // `chunk_by_degree(cs_degree)` is the exact call PM:344 makes, so the
    // exported num_chunks is the reference's own answer and the Lean importer
    // can KAT its port of `LogupBatchedArgument::num_chunks` against it.
    let lookups: Vec<_> = cs
        .lookups()
        .iter()
        .map(|l| {
            let chunked = l.chunk_by_degree(cs_degree);
            let chunks = chunked.input_expression_chunks();
            json!({
                "selector": expr_json(l.selector_expression()),
                "table_expressions": l.table_expressions().iter().map(expr_json).collect::<Vec<_>>(),
                "input_expressions": chunks.iter().flatten()
                    .map(|pl| pl.iter().map(expr_json).collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
                "num_parallel_lookups": chunks.iter().flatten().count(),
                "num_chunks_at_cs_degree": chunked.num_chunks(),
            })
        })
        .collect();
    let trashcans: Vec<_> = cs
        .trashcans()
        .iter()
        .map(|t| {
            json!({
                "name": t.name(),
                "selector": expr_json(t.selector()),
                "constraint_expressions": t.constraint_expressions().iter().map(expr_json).collect::<Vec<_>>(),
            })
        })
        .collect();
    json!({
        "schema": 1,
        "source": source,
        "cs_degree": cs_degree,
        "blinding_factors": cs.blinding_factors(),
        "num_simple_selectors": cs.num_simple_selectors(),
        "challenge_phase": cs.challenge_phase(),
        "permutation_columns": permutation_columns,
        "gates": gates,
        "lookups": lookups,
        "trashcans": trashcans,
        "summary": {
            "num_gates": gates.len(),
            "gate_poly_total": cs.gates().iter().map(|g| g.polynomials().len()).sum::<usize>(),
            "num_lookups": cs.lookups().len(),
            "num_trashcans": cs.trashcans().len(),
            "num_permutation_columns": perm_cols.len(),
        },
        "not_exported": [
            "gate.queried_cells (circuit.rs:1627, pub(crate))",
            "lookup name (logup.rs:172, pub(crate), no accessor)",
            "minimum_degree (circuit.rs:1726, pub(crate), no accessor)",
            "unblinded_advice_columns (circuit.rs:1687, pub(crate), no accessor)",
            "general_column_annotations (circuit.rs:1720, pub(crate), no accessor)"
        ],
    })
}
