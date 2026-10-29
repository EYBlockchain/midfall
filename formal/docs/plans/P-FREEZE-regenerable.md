# P-FREEZE - make the baseline regenerable, and fix the stale SHA rows.

Status: READY. Small package that protects what `formal-baseline-v1` just froze.

## 1. Land the regeneration harness (F-3 from P-M0)

**Nothing in the tree can currently re-emit the poseidon fixture set.** The harness was a
temporary test file and was deleted; the recipe is prose in `BASELINE.md`. A baseline you
cannot regenerate is fragile - the next time a transcript change stales the fixture, whoever
fixes it starts from scratch again.

* Land it as `proofs/solidity-verifier/tests/m0_poseidon_regen.rs`, **env-gated on `M0_OUT`**
  so it is inert without the variable. P-M0 warned explicitly: *"it must stay inert without
  M0_OUT or it reddens `--all-targets`"* - and `--all-targets` is already failing 39 tests
  for an unrelated reason, so do not add noise there.
* It must reproduce the recorded profile exactly: features `evm,rust-verifier-trace`,
  `PoseidonExample` k=6, witness seed 42, prover rng `0xdebd`, SRS `bls_filecoin_2p6`.
* **It cannot reproduce `proof.bin` byte-for-byte** - `blind_quotient_limbs`
  (`proofs/src/plonk/prover.rs:126`) draws from `OsRng`, so runs agree for 720 bytes then
  diverge. The test should assert **structural** invariants instead: proof length 2,640, 72
  transcript reads, and that the regenerated proof **verifies**. Say that in the test name or
  a comment so nobody later "fixes" it into a byte comparison that flakes.

## 2. Fix the stale SHA rows

P-M0 found, and deliberately did not touch: **2 tracked rows were already stale before that
package** - `target/ivc-keccak-solidity-dump/Halo2Verifier.sol` and
`Halo2QuotientEvaluator.sol` (table `c4a04c1b`/`27a60d29` vs HEAD `c9347fde`/`4086ef35`).

* Re-derive them and update the table, or move them out of the pinned set with a stated
  reason. `BASELINE.md` now has a "Which rows of this table are stable pins" subsection -
  use it.
* The table also mixes 30 tracked with 25 untracked rows; **untracked rows cannot be pinned
  at all**. State which are which rather than leaving a table that half-checks.

## Constraints

* **Do not touch the Lean tree.** If a Lean gate reads anything you change, stop and report.
* **Never perturb the working tree in place** (R-54). Use an APFS clone under /tmp.
* `cargo` is not on PATH: `PATH=$HOME/.rustup/toolchains/1.90.0-aarch64-apple-darwin/bin`,
  and **do not pipe cargo through `tail`** - use `set -o pipefail`.
* Do NOT edit `Statements.lean`, `vendor/`, or any Lean file. Do NOT git add or commit.
* Do NOT move or amend the `formal-baseline-v1` tag.
* Existing gates must stay green: `cargo test -p halo2_solidity_verifier` 203/0; the EVM gate
  `evm,rust-verifier-trace` 249/0; `lake build` 5154 jobs; `checks.sh` 1257 KATs.

## Acceptance

- The regen harness exists, is env-gated, is inert by default, and regenerates a **verifying**
  2,640-byte proof when `M0_OUT` is set.
- The 2 stale tracked SHA rows are resolved (re-pinned or excluded with a reason).
- **Required finding**: does the harness, run today, reproduce the committed `vk.bin`,
  `instance.be` and the three traces byte-for-byte - or only structurally? If only
  structurally, name which artefacts are non-reproducible and why, since that decides
  whether the SHA pins on them mean anything.
