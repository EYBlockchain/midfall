# Instrumentation model & residual risks — TODO

> Companion to [`ARCHITECTURE.md`](./ARCHITECTURE.md) and
> [`OPTIMISATIONS.md`](./OPTIMISATIONS.md). Captures the open question
> "could we have instrumented the real Rust verifier directly instead
> of writing `generate.rs`, and how do we know `generate.rs` doesn't
> miss checks the real verifier performs?"

## 1. Fixture taxonomy

The fixtures produced by `src/bin/generate.rs` now **all** come from
real verifier code; the replica-divergence risk that Category B used
to carry has been eliminated by landing Option 1 below
(`debug-trace-hooks` feature on `midnight-proofs`).

### Category A — real-library traces (no replica risk)

These call the **actual** `midnight-proofs` library end-to-end via
its public API, or via the `debug_trace` instrumentation inside it.
There is no re-implementation to drift.

| Fixture | Source of truth |
|---|---|
| `proof.bin`, `instance.be`, `vk.bin` | Real prover + real `VerifyingKey` via `zk_stdlib` |
| `pairing_fixture.bin` | Real `midnight_proofs::plonk::prepare` → real `DualMSM`, split and serialised |
| `verifier_trace.bin` | Events emitted by real `prepare()` under the `debug-trace-hooks` feature (canonical intermediate scalars for `partial_eval.*`, `linearization.*`, `permutation.*`, `logup.*`, `trash.*`, `multi_prepare.*`) |
| `right_g1_fixture.bin`, `right_msm_inputs_digest_fixture.bin`, `right_msm_terms_fixture.bin` | Derived from real `DualMSM.right` (not a replica) |
| `query_schedule_fixture.bin`, `lagrange_aux_fixture.bin` | Produced via real `VerifyingKey`/domain helpers (`get_omega`, `l_i_range`) |
| `evals_signature_fixture.bin` | Real `CircuitTranscript<Keccak256>` parse of the real proof |
| `gate_eval_fixture.bin`, `algebra_fixtures.bin`, `decomp_pairs.bin` | Public `Expression::evaluate`, public algebra / encoding APIs (not a replica of any `pub(in crate::plonk)` function) |

### Category B — synthetic replicas (historical; now empty)

No fixtures in this category remain. The six Category-B replicas
listed in the original version of this document (perm / lookup /
trash expressions, `partially_evaluate_identities`,
`compute_linearization_commitment`, `multi_prepare` Horner fold)
plus four extended replicas (`construct_intermediate_sets`,
per-set x1 evals fold, x4 outer fold) and five D3-D7 "signature"
fixtures have been removed from `generate.rs` and replaced by
observation tags inside `verifier_trace.bin`. Their Solidity
component-level tests were replaced by a single
`test_verifier_trace_instrumented_tags` structural assertion
plus the already-existing end-to-end soundness tests
(`test_verify_poseidon_proof`, trace-diff harness, adversarial
matrix).

## 2. What actually catches divergence today

All soundness checks now use the real prover/verifier. No replica
exists.

1. **`test_verify_poseidon_proof`** (forge, end-to-end): runs
   Solidity `verify()` on a real proof and **requires `ok == true`**.
   Any missing check / miscomputation on the Solidity side makes the
   final pairing non-identity → this test fails.
2. **`tests/forge.rs::rust_and_solidity_traces_match`** (trace-diff
   harness): replays the Fiat-Shamir sequence through the *real*
   `CircuitTranscript<Keccak256>` and diffs the resulting
   challenge / scalar-read / point-read trace byte-for-byte against
   the Solidity `Trace*` events. Any divergence at the transcript
   level surfaces here.
3. **`test_verifier_trace_instrumented_tags`** (forge): parses
   `verifier_trace.bin` (produced by the real `prepare()` under
   the `debug-trace-hooks` feature) and asserts the expected
   instrumentation tag families are present with non-trivial
   cardinality. Guards against silent removal of a
   `debug_trace::emit_*` call inside the real verifier.
4. **Adversarial matrix + PBT suite**: exercise the rejection paths
   against the real prover's output (see
   `ARCHITECTURE.md` §3 bullets 5-6, §5.6).

For a Solidity divergence to slip past (1)-(4), the Solidity
implementation would need to mirror the same mistake as the real
Rust verifier — a rather unlikely coincidence since we are not
implementing the same thing (Solidity is a fresh port against the
Rust trace, not a translation of a Rust copy).

## 3. Upgrade options (in order of preference)

### Option 1 — `debug-trace-hooks` Cargo feature upstreamed to `midnight-proofs` [**LANDED**]
Best long-term design and the one that shipped. A conditional
`debug_trace::emit_*(tag, value)` API at every intermediate step
inside `prepare` / `partially_evaluate_identities` /
`compute_linearization_commitment` / `permutation::expressions` /
`logup::Evaluated::expressions` / `trash::Evaluated::expressions` /
`multi_prepare`, gated on `#[cfg(feature = "debug-trace-hooks")]`.
`generate.rs` enables the feature, records the intermediates via a
thread-local event buffer, and writes them to
`fixtures/verifier_trace.bin`. **No replica, no divergence risk.**

Status: shipped on branch `verifier-contract`
(`proofs/src/debug_trace.rs`). Replica Category B + extended
replicas + D3-D7 signatures are all removed.

### Option 2 — fork `midnight-proofs` with the hooks in a local patch
Not taken — instead the hooks are in-tree under a feature flag
that is off by default (zero-cost when the feature is absent).

### Option 3 — widen visibility behind a feature flag
Not taken — Option 1 (trace hooks) subsumes this; callers no
longer need direct access to `pub(in crate::plonk)` helpers because
the real verifier emits every scalar they would have computed.

## 4. Realistic residual gaps today

Things the current test matrix might still miss:

1. **Rust-verifier check with no Solidity counterpart AND no trace
   event.** If `midnight-proofs::verify` does something that doesn't
   touch the transcript and doesn't feed the final pairing MSM
   (structural `assert!`s on query-schedule shape, `debug_assert!`s
   on intermediate ranges), neither the trace-diff nor the
   pairing-identity test notices. Typically defense-in-depth, but
   risk is not zero.
2. **Poseidon-specific shortcuts the Solidity side takes.**
   Enumerated in `ARCHITECTURE.md` §7.2.  The original poseidon-only
   shortcuts (`instance · l_0` collapse, `fixed_queries[i].column_idx
   == i`, `numLookups == 1`) were lifted in Phases 2-4; the
   remaining narrowings (G1-identity committed instance,
   `num_challenges == 0`, `num_proofs == 1`) are deliberate scope
   restrictions that are algebraically correct for every example
   circuit (poseidon, RSA-signature, IVC aggregation) but wrong for a
   future circuit that opts into one of those features.
3. **Feature-gated paths.** `truncated-challenges`,
   `single-h-commitment`, `fewer-point-sets` enabled on the prover
   produce a proof stream Solidity cannot parse. Documented as "not
   supported" in `ARCHITECTURE.md` §7.3 — deliberate scope
   restriction, not a missed check.

Options 1 or 3 in §3 above close gap (1) entirely and reduce the
reliance on human both-sides-read review for gaps (2)-(3).

## 5. Actionable follow-ups

Prioritised (highest-payoff first):

- [x] **Option 1 landed.** `debug-trace-hooks` feature added to
      `midnight-proofs`; `generate.rs` drives real `prepare()` and
      dumps `verifier_trace.bin`. See
      `proofs/src/debug_trace.rs` + per-site instrumentation in
      `plonk/mod.rs`, `plonk/linearization/verifier.rs`,
      `plonk/permutation.rs`, `plonk/logup.rs`, `plonk/trash.rs`,
      `poly/kzg/mod.rs`.
- [x] **Replicas removed.** All Category B + extended replicas +
      D3-D7 signatures deleted from `generate.rs` and
      `test/PoseidonVerifier.t.sol`; replaced by
      `test_verifier_trace_instrumented_tags`.
- [ ] **Enumerate all `assert!` / `debug_assert!` / `return Err`
      sites in `proofs/src/plonk/verifier.rs`** and its callees.
      For each one, document whether the Solidity side has an
      equivalent check (by line reference). This is a manual audit
      that closes §4 gap (1) without any code change.
- [ ] **Add more emit points if audit gap (1) finds any.** If the
      audit above surfaces a verifier check that doesn't touch the
      transcript and isn't observable in the trace, extend
      `debug_trace::emit_*` at that site so Solidity can cross-check
      it too.
- [ ] **Revisit this TODO after any `midnight-proofs` bump.** The
      instrumentation-site file-line references are bump-sensitive
      and should be kept in sync.

## 6. Short answer (if someone asks the same question again)

- All `generate.rs` fixtures are now produced by the real
  `midnight-proofs` verifier — either through its public API or
  through the `debug-trace-hooks` instrumentation
  (`verifier_trace.bin`). There is no replica to drift.
- Soundness is carried by `test_verify_poseidon_proof` + the
  trace-diff harness + the adversarial matrix / PBT suite + the
  new `test_verifier_trace_instrumented_tags` structural guard,
  **all of which use the real prover/verifier** and would surface
  a Solidity omission or miscomputation end-to-end.
