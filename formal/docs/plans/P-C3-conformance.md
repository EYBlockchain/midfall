# P-C3 - Phase 3 thin conformance slice. The largest remaining risk to verified.

Status: APPROVED by the human (round 51, decision 8). **Phase 3 is ~0%** and it is the
only thing that validates the Exec port (M2). Everything - stages 1-6, the lowering
theorems, the security claims - rests on `Midfall.Halo2.Exec` being a faithful port, and
that claim currently rests on KATs and review. Three real bugs (R-20, R-30, R-32) were
found by other means and two survived sign-off.

## Scope: the THIN slice only. Do not build the full harness.

PLAN section 5 describes a large harness. This package delivers the minimum that proves
the machinery works end to end:

1. **Rust exporter** (`conformance-rs/` or a new test binary in `halo2_solidity_verifier`):
   emit canonical `vk.json`, `params.json`, `proof.bin`, `instances.json`, and
   `trace.json` (every absorb/squeeze, the challenges, all evaluations, MSM terms, the
   DualMSM left/right points, the result) for **one** fixture - poseidon.
   **Decision already taken:** the exporter emits canonical JSON; Lean does NOT read
   Rust serde binary `vk.bin`. Reason, recorded so nobody re-litigates: `vk.bin` is not
   self-contained - `read_from_cs` takes the `ConstraintSystem` as an argument - and the
   coordinates are Montgomery-form raw bytes.
2. **Lean runner** (`Conformance/`): parse with `Common/Json.lean` (already landed,
   strict typed accessors - `jNat` rejects `12.5`), run `verifyNative` and `decodeRust`,
   compare accept/reject, error class, and every trace value.
3. **One end-to-end replay** against `rust_trace.json`, green.

Mutations, coverage, and the 10k bit-flip corpus are **explicitly out of scope** - they
come after the thin slice proves the plumbing.

## Hazards

1. **The exporter is Rust code.** You may ADD files under `conformance-rs/` or a new test
   binary; you may NOT modify existing Rust verifier code, `Statements.lean`, or fixtures.
   If exporting requires changing the verifier to expose internals, **stop and report** -
   that is a baseline question, not a harness question.
2. **`Common/Json.lean` exists but is unproven at scale.** If it cannot parse the
   exporter real output, report precisely what fails rather than bending the exporter to
   fit the parser. The parser is the thing being tested too.
3. **Numbers from `lake build` and `scripts/checks.sh` only** - `lake env lean` does not
   apply lakefile options.
4. **Register any new Lean module** (R-50, hard failure). A runner binary is not a module;
   say how CI will invoke it.
5. **Never perturb the working tree in place** (R-54). Verify existence with `#check`, not
   grep piped through `head`.
6. **The comparison must be able to fail.** A runner that prints agreed without a non-zero
   exit on mismatch is worse than no harness - it manufactures confidence. Perturb one
   trace value in the JSON and show the runner reddens.

## Rules

Read first: `docs/plans/README.md` standing notes; `docs/conformance-schema.md` (the
schema already exists - follow it); `Common/Json.lean`; `Exec/Native.lean` and
`Exec/Transcript.lean` (the read log that makes `decodeRust` derivable); PLAN section 5.

Do NOT edit existing Rust verifier files, `Statements.lean`, `vendor/`, or another
package Lean file. Do NOT git add or commit.

**No idle builds.** Background every cargo and lake build.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- One fixture replays end to end with a **non-zero exit on any mismatch**, and a
  perturbation demonstrates that.
- **Required finding**: does the replay agree on every trace value? If not, list every
  divergence - each one is either a port bug or an exporter bug, and both are the reason
  this package exists.
