# P-FIX - why does the committed poseidon fixture fail the current verifier?

Status: gates **M0**. Recorded as R-56. A committed fixture that current code rejects
cannot be a faithful record of current code, and PLAN Phase 0 steps 6-7 (regenerate
fixtures, run G0) cannot honestly pass until this is resolved.

## The measured facts

| | bytes | reads | shape |
|---|---:|---:|---|
| committed `fixtures/poseidon/proof.bin` | 4,752 | 138 | 69 `dummy_eval`, 1 `q_eval` |
| regenerated, default features | 2,640 | 72 | no dummies, 3 `q_eval`s |
| regenerated, `rust-verifier-trace,fewer-point-sets` | 4,848 | 141 | closer, unequal |

The **VK matches** - same `transcript_repr` (`4cc2e5ac…494`), same 10 challenge names, same
21 point reads. Only the proof differs. Replaying the committed `proof.bin` through the
real verifier returns `Error::Opening`.

## Questions, in priority order

1. **Which feature profile produces the committed fixture?** Search the repo's own records:
   `formal/BASELINE.md` toolchain table, `docs/DEPLOYMENT_AND_INCIDENT_RESPONSE.md`, gas
   snapshots, CI workflow files, and the git history of `fixtures/poseidon/`.
   `fewer-point-sets` gets closest - is there a fourth flag, or a different `k`, or a
   prover version change?
2. **Is `Error::Opening` expected for that fixture under the current verifier, or is it a
   regression?** This is the important one. If the committed proof was valid when written
   and the verifier changed, something in the port's reference moved. If the fixture was
   always stale, say so and identify when.
3. **Can the fixtures be regenerated cleanly?** `poseidon_fixture.rs` writes them - run it
   and diff. If regeneration produces the 2,640-byte proof, then the committed 4,752-byte
   one is simply old and should be replaced, with the diff reviewed.
4. **`instance.be` endianness** (R-56 consequence 2): the committed file is big-endian
   while `poseidon_fixture.rs` writes LE `to_repr`. Which is correct, and does anything
   read it?

## Constraints

* **You may NOT modify the Lean port.** This is a Rust-side and provenance investigation.
  If the answer is that the port is wrong, **stop and report** - that is a different
  package.
* **Do not silently replace committed fixtures.** Regenerate into a scratch location, diff,
  and report. Replacing a baseline artefact is the human's call.
* `cargo` is **not on PATH** in this session. Use
  `PATH=$HOME/.rustup/toolchains/1.90.0-aarch64-apple-darwin/bin`. And **do not pipe cargo
  through `tail`** - it masks the exit code; use `set -o pipefail`. An earlier agent
  reported a green build that was actually `cargo: command not found`.
* Existing gate: `cargo test -p halo2_solidity_verifier` must stay at 203 passed / 0 failed.
* Do NOT edit `Statements.lean`, `vendor/`, or any Lean file. Do NOT git add or commit.

## Acceptance

- A named answer to question 1 (the profile), or a proof that no profile in this tree
  reproduces it.
- Question 2 answered: regression or stale artefact, with evidence.
- **Required finding**: is M0 taggable? If not, exactly what must change first, and is it
  a fixture regeneration or a code change?
