# P-M0 - execute D-P28: regenerate the poseidon fixtures, re-pin BASELINE, cut the tag.

Status: **AUTHORISED and unblocked.** The human took the recommended option on D-P28, which
reads: regenerate the six live poseidon artefacts under the profile `BASELINE.md` already
records, re-pin its SHA-256 table, and delete the 12 unread fixture files. R-57 settled the
provenance - the committed fixture was **stale on arrival** and fails the current verifier -
so this is execution, not investigation.

## Steps, in order

1. **Confirm the profile.** `BASELINE.md` records `outerFewerPointSets = false`, which R-57
   measured corresponds to the **2,640-byte / 72-read** proof. State the profile explicitly
   in the output so G0 and `BASELINE.md` name the same one.
2. **Regenerate the six live artefacts** - `proof.bin`, `vk.bin`, `instance.be`,
   `rust_trace.json`, `solidity_trace.json`, `verifier_trace.bin` - into a scratch location
   FIRST, diff against the committed ones, and report the diff before replacing anything.
   The generator path is `tests/poseidon_fixture.rs` (k=6, witness seed 42, prover rng
   `0xdebd`).
3. **Verify the regenerated fixture actually passes.** Replay the new `proof.bin` through the
   real verifier and confirm it is accepted - the committed one returns `Error::Opening`,
   which is the whole reason this package exists. **A regenerated fixture that also fails is
   a finding, not a step to skip.**
4. **Replace the six files and re-pin** the SHA-256 rows at `BASELINE.md:211-228`.
5. **Delete the 12 orphan files** in `fixtures/poseidon/` with zero code references
   (`adversarial_fixtures`, `algebra_fixtures`, `decomp_pairs`, `evals_signature_fixture`,
   `gate_eval_fixture`, `identity_g1_compressed`, `lagrange_aux_fixture`, `pairing_fixture`,
   `query_schedule_fixture`, `right_g1_fixture`, `right_msm_inputs_digest_fixture`,
   `right_msm_terms_fixture`). Verified: they appear only in `BASELINE.md`. **List every
   deletion explicitly in your report** - these are baseline artefacts and the human should
   be able to see exactly what went.
6. **Run G0**: `cargo test -p midnight-proofs`, `cargo test -p halo2_solidity_verifier
   --features evm` plus the CI feature matrix, and the revm PRAGMA fixtures on both quotient
   lowerings. Report pass/fail per item.
7. **Update `BASELINE.md`** from DRAFT to final for Phase 0 steps 6-8, and state whether the
   `formal-baseline-v1` tag is now safe to cut. **Do not create the tag yourself** - report
   readiness and the orchestrator cuts it.

## Environment and traps

* **`cargo` is NOT on PATH.** Use
  `PATH=$HOME/.rustup/toolchains/1.90.0-aarch64-apple-darwin/bin`. And **do not pipe cargo
  through `tail`** - it masks the exit code; use `set -o pipefail`. An earlier agent reported
  a green build that was actually `cargo: command not found`.
* **Do not touch the Lean tree.** This is a Rust-side and documentation package. If
  regeneration changes bytes that a Lean gate reads, **stop and report** - do not edit the
  Lean gate. (`formal/fixtures/conformance/` is the regenerated bundle and is separate from
  `proofs/solidity-verifier/fixtures/poseidon/`; do not conflate them.)
* **Never perturb the working tree in place** for any mutation testing (R-54).
* Do NOT edit `Statements.lean`, `vendor/`, or any Lean file. Do NOT git add or commit.
* Existing gate must stay green: `cargo test -p halo2_solidity_verifier` is 203 passed / 0
  failed; `lake build` green at 5154 jobs; `checks.sh` green with 1257 KATs.

## Acceptance

- Six artefacts regenerated, **verified to pass the verifier**, and committed values replaced.
- SHA-256 table re-pinned; 12 orphans deleted with an explicit list.
- G0 results reported per item, pass or fail.
- **Required finding**: is `formal-baseline-v1` safe to cut? If not, name precisely which G0
  item fails and what it would take. Also state whether any Lean gate read a byte that
  changed - if so, which, since that is the cross-cutting risk this package carries.
