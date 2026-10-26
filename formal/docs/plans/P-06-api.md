# P-06 - Midfall.Generator.Api (port of api.rs)

Status: READY. Fire when P-05 (Abi + Encoding) is committed.
Depends on: layout (done), abi + encoding (P-05). Blocks: vm, quotient, plan, calldata,
diagnostics, quotient_listing - six modules import `crate::api`, so nothing after this
one can proceed without it. See PLAN 14.7.

The Rust reference is **git HEAD**, not the working tree. **Correction after the fact
(this plan was wrong about its own numbers and the implementing agent caught it):** HEAD
is **761 lines**, not 818; the working copy is 818, not 875. The 57-line uncommitted
addition is `RenderedArtifacts::named_bytes` plus a test module, and it is NOT part of
the baseline. Because the item table below was written from the working copy, every
range after 527 is 57 lines high and the `RenderedArtifacts + impl` row straddles the
uncommitted item. The port was done against HEAD and its R11 table is the authoritative
one. Rule extracted for all future plans: **derive line numbers from
`git show HEAD:<path>`, never from `wc -l` on a dirty working tree**, and state which
one a table uses.**

Read the reference with:

    git show HEAD:proofs/solidity-verifier/src/api.rs

    git show HEAD:proofs/solidity-verifier/src/api.rs

or verify the committed line count first (`git show HEAD:... | wc -l` = 818). If your
working copy says 875, you are reading the uncommitted version. Do not edit it either:
Rust is read-only for this project.

## Deliverable

One new module `formal/Midfall/Generator/Api.lean`, registered in
`formal/Midfall.lean`, porting `proofs/solidity-verifier/src/api.rs` (818 lines at
HEAD) in full and in source order. Every top-level item, including private helpers and
the `impl` blocks:

| range | item |
|---|---|
| 36-46 | `AccumulatorEncoding` (offset, num_limbs, num_limb_bits, kind) |
| 49-64 | `AccumulatorEncodingKind` (PointAndScalar, PointPair) |
| 66-70 | `CommittedInstanceCommitmentKind` (Identity only) |
| 71-196 | `impl AccumulatorEncoding`: SUPPORTED_NUM_LIMBS, SUPPORTED_NUM_LIMB_BITS, FULLY_COLLAPSED_PUBLIC_INPUT_WORDS, POINT_PAIR_PUBLIC_INPUT_WORDS, new, point_pair, coordinate_words (private), point_words, point_pair_words, has_carried_scalars, fixed_payload_words, fully_collapsed_public_input_words, validate_for_num_instances, fixed_scalar_count |
| 200-214 | `QuotientProbeArtifacts` (#[cfg(feature = "evm")], doc(hidden)) |
| 216-373 | the manifest / certificate types: QuotientIdentityManifest, QuotientCertificate, QuotientCertificateEntry, QuotientIdentityExecution, QuotientIdentityManifestEntry, QuotientIdentitySource, QuotientIdentityManifestTarget |
| 375-402 | `GeneratorConfig` + impl (including `with_accumulator`) |
| 404-463 | `RenderVk`, `RenderQuotient`, `QuotientLowering` (Vm, Direct - **Vm is the default**, the Phase 0 merge requirement) |
| 465-506 | `RenderDiagnostics` + Default, `RenderOptions` |
| 508-587 | `RenderedArtifacts` + impl |
| 589-651 | `RepackError` + Display + std::error::Error impl |
| 653-750 | `GeneratorError` + Display + Error + From<RepackError> |
| 752-818 | `ProofEvaluationCounts` + impl |

## Why this module is load-bearing, not clerical

Three of the four `Supported` fields that PLAN 9.5 lists as "arrive with the Phase 6
port" are named after types in this file: `acc` quantifies over
`AccumulatorEncoding` and its `validFor`, `production` reads `RenderDiagnostics`, and
`g.cfg.accumulator` is `GeneratorConfig`. `Midfall/Lowering/Types.lean` is a
placeholder precisely because these did not exist. Landing this module is what lets the
frozen §9.5 statements stop being sketches. Do not treat it as a bag of enums.

## Hazards - address each one explicitly in your report

1. **Division by zero in `coordinate_words`.** It computes
   `(254 / self.num_limb_bits).max(1)`. Integer division by zero panics in Rust even in
   release - it is not wrapping arithmetic - so `num_limb_bits = 0` is a panic site per
   R4, not an unreachable one. Check the call graph: `validate_for_num_instances`
   rejects any `num_limb_bits != SUPPORTED_NUM_LIMB_BITS` (56), and both
   `fully_collapsed_public_input_words` and `fixed_scalar_count` validate first. But
   `point_words` is `pub(crate)` and may be reachable from a caller that does not
   validate. Enumerate the callers in the crate (`grep -rn 'point_words\|coordinate_words' proofs/solidity-verifier/src`) and state, per caller, whether validation precedes it. Where a path reaches it unvalidated, port the panic as `throw (.panic "api.rs:<line>")`; where every path validates, say so at the site.

2. **`usize::MAX` as a sentinel.** `fully_collapsed_public_input_words` calls
   `validate_for_num_instances(usize::MAX)` specifically so the tail bound
   `offset.saturating_add(required_words) > num_instances` cannot fire. Port it exactly
   - do not "simplify" it into a separate unvalidated path. Gate it: an encoding with a
   huge offset must still return Ok from `fullyCollapsedPublicInputWords` and Err from
   `validateForNumInstances` at a realistic num_instances.

3. **`saturating_add` is deliberate.** In the same bound, `offset + required_words`
   would wrap in release; the Rust uses `saturating_add` so overflow yields the
   saturation value and the comparison then fires. Reproduce the saturation, not a Nat
   addition, and gate the saturating case.

4. **Limb arithmetic is the §9.5 `decodeAcc_encode` claim.** PLAN 9.5 says the
   accumulator encoding is "7x56 limbs, coord-1, sentinel, identity flag". Check that
   the constants here agree with `layout::accumulator::{LIMBS, LIMB_BITS,
   IDENTITY_FLAG_WORDS, CARRIED_SCALARS}` as ported in Generator/Layout.lean, and gate
   the derived numbers: with the supported constants, `coordinate_words` must be 2 (so
   4 limbs per public-input word, as the doc comment claims), `point_words` must be
   2*2 + IDENTITY_FLAG_WORDS, `point_pair_words` twice that, and
   `fixed_payload_words` must equal FULLY_COLLAPSED_PUBLIC_INPUT_WORDS (12) for
   PointAndScalar and POINT_PAIR_PUBLIC_INPUT_WORDS (10) for PointPair. **If those
   equalities do not hold, STOP and report it**: the doc constants and the derived
   arithmetic disagreeing is a reference bug of the R-40 class, and PLAN 13 lists the
   accumulator composition as exactly the place where a false statement must be
   reported rather than worked around.

5. **`PointPair` rejects a tail; `PointAndScalar` accepts one.** `fixed_scalar_count`
   returns Err for a non-zero tail under PointPair. Both arms are reachable and both
   must be gated (R8-style: exercise both, do not assume one is dead).

6. **Error types are Display-formatted strings.** `RepackError` and `GeneratorError`
   have `fmt::Display` impls whose text is user-visible and, in the case of
   `UnsupportedAccumulatorEncoding`, carries a `reason: &'static str` that the
   validation logic compares against nothing but which a later gate might. Port the
   Display strings verbatim, including punctuation, and gate at least one rendering of
   each variant that has a payload. `From<RepackError> for GeneratorError` must be
   ported too - `Except` chains will want it.

7. **`QuotientProbeArtifacts` is `#[cfg(feature = "evm")]` and `doc(hidden)`.** It is a
   test-only probe type ("not a verifier"). Decide explicitly: port it marked test-only,
   or record that it is not ported and why. The repo convention (Layout.lean header,
   Protocol.lean R8 section) is to port what a ported test needs and say out loud what
   you skipped.

8. **`QuotientLowering::Vm` is the default.** Phase 0 step 4 requires Vm as the
   default lowering, and R-36/D-P13 mean the golden target is a VM-path render. If the
   Rust `Default` or any constructor picks Direct, that is a finding. Gate the default.

## Rules

Binding rules are PLAN section 4 (R1-R11) as applied by
`formal/Midfall/Generator/Protocol.lean` - read that file's header first and copy its
discipline: citation prefix naming its file and line count, an explicit "what this file
does NOT port and why" section, TEST-ONLY markers, and per-gate perturbation evidence.

- R1 provenance comment on every def: `-- rust: proofs/solidity-verifier/src/api.rs:<lines> @formal-baseline`.
- R2 names: snake_case -> lowerCamelCase, type names kept.
- R4: the reference profile is RELEASE (BASELINE.md), so overflow does not panic and
  `debug_assert!` is compiled out; division by zero DOES panic. Record which is which.
- R6: `Vec` -> `List` (Generator-row precedent; PLAN's literal "Vec becomes Array"
  diverges - follow the row, as Protocol.lean did, and note it if relevant here).
- R10: computable, never `partial`. No proofs in this file beyond `#eval` gates.
- Do NOT edit any Rust file, Statements.lean, or SORRY.md. Do NOT git add or commit.
- Register the module in `formal/Midfall.lean`.

## Acceptance

1. `cd /Users/julian/midfall/formal && lake build` green (currently 3375 jobs + P-05).
2. `bash scripts/checks.sh` green: sorry register unchanged, golden provenance green,
   every `#eval ... -- expect true` gate passing (kat_gate counts them - report the
   before/after numbers).
3. At least 10 `#eval` gates, each pinning a real behaviour, and for each one you claim
   is load-bearing, the single-token perturbation you ACTUALLY RAN and what reddened.
   R-41's rule: a gate's stated scope must be justified by a perturbation inside that
   scope. Do not write a claim about what a gate would catch that you did not test.
4. Non-vacuity: for every boolean gate, show it can be false. A gate over a constant
   `true` is the R-30/R-32 pattern and Protocol.lean's F6 is the most recent instance.

## Report format

1. Status: build + checks tails, line count, gate count.
2. R11 table: Rust range -> Lean def (the table above is the starting point; correct it
   against what you actually found).
3. Answers to hazards 1-8, each with what you did and what you tested.
4. Perturbation evidence, per gate.
5. Findings: faithfulness risks, plan-level problems, reference defects. Plainly stated,
   not rounded up. A vacuous test found in the reference is worth more than a clean
   report - Protocol.lean's F1 found one and it was confirmed independently.
