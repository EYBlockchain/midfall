# Instrumentation model & residual risks — TODO

> Companion to [`ARCHITECTURE.md`](./ARCHITECTURE.md) and
> [`OPTIMISATIONS.md`](./OPTIMISATIONS.md). Captures the open question
> "could we have instrumented the real Rust verifier directly instead
> of writing `generate.rs`, and how do we know `generate.rs` doesn't
> miss checks the real verifier performs?"

## 1. Fixture taxonomy

The fixtures produced by `src/bin/generate.rs` split into two
categories with different trust characteristics.

### Category A — real-library traces (no replica risk)

These call the **actual** `midnight-proofs` library end-to-end via its
public API. There is no re-implementation to drift.

| Fixture | Source of truth |
|---|---|
| `proof.bin`, `instance.be`, `vk.bin` | Real prover + real `VerifyingKey` via `zk_stdlib` |
| `pairing_fixture.bin` | Real `midnight_proofs::plonk::prepare` → real `DualMSM`, split and serialised |

### Category B — synthetic replicas of `pub(in crate::plonk)` functions

These re-implement algorithms that are not reachable from `generate.rs`
because they are crate-private. If a replica drifts from the real
algorithm, the Solidity test validates two consistently-wrong
implementations.

| Fixture | Replica of | Reference |
|---|---|---|
| `perm_expressions_fixture.bin` | `permutation::expressions` | `proofs/src/plonk/permutation.rs:180+` |
| `lookup_expressions_fixture.bin` | `logup::Evaluated::expressions` | `proofs/src/plonk/logup.rs:400+` |
| `trashcan_expressions_fixture.bin` | `trash::Evaluated::expressions` | `proofs/src/plonk/trash.rs:57+` |
| `partial_eval_fixture.bin` | `partially_evaluate_identities` | `proofs/src/plonk/verifier.rs` |
| `linearization_fixture.bin` | `compute_linearization_commitment` | `proofs/src/plonk/linearization/verifier.rs:45+` |
| `feval_fold_fixture.bin` | `multi_prepare` Horner fold | `proofs/src/poly/kzg/mod.rs:330-340` |

## 2. What actually catches divergence today

Two end-to-end tests do **not** use any replica. They are the
load-bearing soundness checks; the component-level Category B
replicas are a fault-localisation aid, not a primary soundness
guarantee.

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
3. **Adversarial matrix + PBT suite**: exercise the rejection paths
   against the real prover's output (see
   `ARCHITECTURE.md` §3 bullets 5-6, §5.6).

For a divergence to slip past (1)+(2), the Solidity implementation
would need to mirror **exactly the same mistake** as our Rust
replica — possible in principle, but unlikely for the specific
replicas we have because the Rust reference is cited next to every
replica and diff-review of 5-40 line algorithms is tractable.

## 3. Upgrade options (in order of preference)

### Option 1 — `debug-trace-hooks` Cargo feature upstreamed to `midnight-proofs`
Best long-term design. A conditional `trace_emit!(tag, value)` macro
at every intermediate step inside `prepare` /
`partially_evaluate_identities` / `compute_linearization_commitment`,
gated on `#[cfg(feature = "debug-trace-hooks")]`. `generate.rs`
enables the feature, records the intermediates into a channel, and
writes them to disk. **No replica, no divergence risk.**

Cost:
- Coordinate with `midnight-proofs` maintainers.
- API-stability commitment for the hook surface (even though it's
  feature-gated).
- Build-time cost of threading a trace sink through the verifier
  call stack.

Worth doing if this port keeps being extended (e.g. to generalise
beyond poseidon per `ARCHITECTURE.md` §9).

### Option 2 — fork `midnight-proofs` with the hooks in a local patch
Same effect without upstream coordination. Cost: maintain a diff
against `midnight-proofs` across every bump. The project currently
uses `path = ".."` to avoid forking; a patched fork would be a new
pain point.

### Option 3 — widen visibility behind a feature flag
Minimal surface change: `pub(in crate::plonk)` → `pub` inside a
`pub mod testing { ... }` gated on `#[cfg(feature = "testing-api")]`.
Every Category B replica in `generate.rs` collapses to a direct
call into the real `midnight-proofs` function. **Cheapest path to
full replica elimination** if maintainers agree.

### Why none of the above are landed yet
- `midnight-proofs` is pinned via `path = ".."`; changes become
  cross-crate edits with their own review burden.
- The end-to-end tests give >99% of the assurance (a replica bug
  that happens to coincide exactly with a Solidity bug is a small-
  probability event; everything else fails `test_verify_poseidon_proof`
  or the trace-diff harness).
- Replicas keep `generate.rs` self-contained — it runs without
  building `midnight-proofs` with special flags.

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
   Enumerated in `ARCHITECTURE.md` §7.2 (six rows:
   `numLookups == 1`, `instance · l_0` collapse, G1-identity
   committed instance, `num_challenges == 0`,
   `fixed_queries[i].column_idx == i`, `num_proofs == 1`). These
   are not missed checks — they are deliberate narrowings that are
   algebraically correct for poseidon but wrong for a general circuit.
3. **Feature-gated paths.** `truncated-challenges`,
   `single-h-commitment`, `fewer-point-sets` enabled on the prover
   produce a proof stream Solidity cannot parse. Documented as "not
   supported" in `ARCHITECTURE.md` §7.3 — deliberate scope
   restriction, not a missed check.

Options 1 or 3 in §3 above close gap (1) entirely and reduce the
reliance on human both-sides-read review for gaps (2)-(3).

## 5. Actionable follow-ups

Prioritised (highest-payoff first):

- [ ] **Propose Option 3 to the `midnight-proofs` maintainers.**
      Widening visibility behind a `testing-api` feature is the
      smallest upstream change and entirely removes Category B
      replica-divergence risk. Estimated upstream diff: < 200 LOC
      across `plonk::permutation`, `plonk::logup`, `plonk::trash`,
      `plonk::verifier`, `plonk::linearization`, `poly::kzg`.
- [ ] **Draft Option 1 as a design doc.** If Option 3 is accepted,
      the same hook points become natural candidates for trace
      emission. Design doc should specify:
      - The trace-sink trait (probably `TraceSink: FnMut(&str, &[u8])`
        or similar).
      - The gating feature name (`debug-trace-hooks`).
      - Hook placement: every `squeeze_challenge` call, every
        `read_*` transcript op, every intermediate ~10 LOC algebra
        section.
- [ ] **Enumerate all `assert!` / `debug_assert!` / `return Err`
      sites in `proofs/src/plonk/verifier.rs`** and its callees.
      For each one, document whether the Solidity side has an
      equivalent check (by line reference). This is a manual audit
      that closes gap (1) without any code change. Output: a table
      appended to `ARCHITECTURE.md` §10 or a new §11.
- [ ] **Revisit this TODO after any `midnight-proofs` bump.** The
      replica file-line references in §1 table are bump-sensitive
      and should be kept in sync.

## 6. Short answer (if someone asks the same question again)

- Category A fixtures use the real verifier via its public API — no
  replica risk.
- Category B fixtures re-implement `pub(in crate::plonk)` algorithms;
  divergence between our replica and the real algorithm is a possible
  failure mode.
- Soundness today is carried by `test_verify_poseidon_proof` + the
  trace-diff harness + the adversarial matrix / PBT suite, **all of
  which use the real prover/verifier** and would surface a Solidity
  omission or miscomputation end-to-end. The Category B replicas are
  a fault-localisation aid, not the load-bearing soundness check.
- The cleanest long-term fix is widened visibility (Option 3) or
  feature-gated trace hooks (Option 1) in `midnight-proofs`. Both
  are tracked in §5 above.
