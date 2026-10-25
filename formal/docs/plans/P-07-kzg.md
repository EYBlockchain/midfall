# P-07 - Midfall.Generator.Kzg (port of lowering/kzg/mod.rs)

Status: DRAFT - hazards below are from reading the source; the item table needs
completing against the file before firing.
Depends on: P-05 (encoding: Data, Ptr, Word, EcPoint, ConstraintSystemMeta), P-04
(protocol: PcsQuerySource). Blocks: P-08 (vk imports kzg), P-11 (plan), and the Phase 4
lemma "correctness of construct_intermediate_sets" from PLAN section 6.

Reference: `proofs/solidity-verifier/src/lowering/kzg/mod.rs`, 2,226 lines, 32
top-level items. Lean target: `formal/Midfall/Generator/Kzg.lean`, registered in
`formal/Midfall.lean`.

## What this module is

It is the codegen-time simulation of the verifier's KZG multi-open: it builds the
query list, groups commitments into point sets, and emits the Yul that computes
`q_com[s]`, `q_eval_set[s]`, `f_eval` (Horner over reverse(point_sets) with Lagrange
interpolation at x3) and the final MSM with x4 powers. Its header states the structure
in six steps; the port must preserve that order because PLAN 6 lists
`construct_intermediate_sets` correctness as a required lemma and the lemma will be
stated over exactly this shape.

## Item map (TO COMPLETE)

| range | item |
|---|---|
| 69-94 | `Query` + impl |
| 96-134 | `queries(meta, data)` |
| 136-224 | `assert_permutation_query_order_is_upstream_equivalent` |
| 226-300 | `query_from_plan(source, meta, data)` |
| 302-320 | `DummyQuery` |
| 322-370 | `compute_dummy_queries` |
| 372-396 | `augment_queries_with_dummies` |
| 398-407 | `CommitmentEntry` |
| 409-417 | `IntermediateSets` |
| 421-516 | `construct_intermediate_sets_impl` |
| 518-543 | `sort_sets` |
| 545-556 | `intermediate_sets` |
| 558-566 | `num_point_sets` |
| 569-578 | `TrackedG1` + impl |
| 580-586 | `quotient_limb_comms` |
| 587-648 | `proof_absorbed_g1s` |
| 650-688 | `precompile_validated_g1s` |
| 690-721 | `validate_g1_precompile_coverage` |
| 723-741 | `validate_absorbed_g1_precompile_coverage` |
| 743-750 | `commitments_by_set` |
| 752-763 | `linearization_term_count` |
| 765-787 | `q_com_terms_for_set` |
| 789-800 | `q_com_trace_terms` |
  above is 24 of 32 and must not be fired from an incomplete map).

## Hazards - each must be answered in the report

1. **The BTreeMap insertion-order trap** (`construct_intermediate_sets_impl` step 2,
   ~line 470). The Rust does `point_idx_sets.entry(sorted).or_insert(point_idx_sets.len())`.
   The *value* is insertion order; the *key* is a `Vec<usize>` and BTreeMap iterates keys
   in sorted order. If anything downstream iterates the map instead of looking keys up,
   the set numbering it sees is sorted-key order, and the two differ. Trace every use of
   `point_idx_sets` after that loop and state per use whether it is a lookup or an
   iteration. Model it insertion-ordered (the R6 `IndexMap` rule) and gate a case where
   the two orders disagree.
2. **`EcPoint` equality is memory-pointer equality, deliberately** (doc at 418-420: "same
   memory location = same commitment"). In the port `EcPoint` wraps a `Ptr` (a Nat), so
   value equality *is* pointer equality - faithful by construction. Say so explicitly:
   this is the same hazard R-7 flagged in the verifier (`CommitmentReference` uses
   `std::ptr::eq`) and a reviewer will look for it. The difference: here the pointer is a
   planned memory address, there it is a Rust allocation.
3. **The duplicate-query `assert_eq!`** (~445). Two queries may share
   `(commitment, rotation)` legally when several columns point at one slot; the assert
   fires only when their evals *conflict*. Port as a `Fault.panic` site and gate BOTH
   arms: same comm + same rotation + same eval collapses silently; conflicting evals
   abort. Getting this wrong changes the point-set partition, which changes the x1/x2/x3
   batching structure of §9.4.
4. **`sort_sets` key is `(len, original_index)`** - ascending cardinality, tiebreak by
   original index, and the doc says the verifier relies on it so the first point set
   holds the fixed commitments opened at x. Gate a case with two equal-cardinality sets:
   that is the only case where the tiebreak is observable.
5. **`remap[c.set_index]`** indexes a `vec![0usize; len]`. If `set_index` could ever be
   out of range this is a release-mode panic (indexing, not wrapping). Argue totality at
   the site or port the panic per R4.
6. **`validate_absorbed_g1_precompile_coverage` is the PLAN 13 `points_subgroup_checked`
   risk.** It decides which absorbed G1 points reach a validating precompile. PLAN 9.5
   states `points_subgroup_checked` as a theorem - every proof G1 point reaches
   G1MSM/PAIRING or an explicit check. If this function shows an absorbed point reaches
   neither, that is a counterexample to a normative statement: STOP and report.
7. **Feature branches.** `DummyQuery`, `compute_dummy_queries`,
   `augment_queries_with_dummies` and the `data.dummy_eval_words.is_empty()` branch in
   `intermediate_sets` are the `fewer-point-sets` path. R8: both branches ported, and the
   branch taken under `Features.solidity` identified and gated.

## Acceptance

Standard: PLAN section 4 rules as applied by Protocol.lean; `lake build` and
`scripts/checks.sh` green; at least 12 `#eval` gates; per-gate perturbation actually run
and reported; non-vacuity shown for every boolean gate.

Extra for this module: build one hand-made query list exercising hazards 1, 3 and 4
together - equal-cardinality sets, a legal duplicate, an insertion order that differs
from sorted order - and pin the whole `IntermediateSets` shape (commitments with their
set indices, plus the point-set list). That single gate is the anchor the Phase 4
`construct_intermediate_sets` lemma will be stated against, so it is worth more than all
the small ones.

