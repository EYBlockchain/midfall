# Work package plans

Detailed handover briefs for implementing agents. One file per package: `P-NN-<slug>.md`.

A plan file is written by the orchestrator (planner) and consumed by exactly one
implementation agent. Plans are refined incrementally as the port advances - a plan that
was written before its dependencies landed is a guess, so the sections marked
`TO CONFIRM` must be resolved against the actual tree before the package is fired.

## Conventions

- **Status:** `READY` (fire now), `BLOCKED` (naming the blocker), `DRAFT` (hazards not
  yet verified against source), `DONE` (committed, with the commit hash).
- Every plan names its Rust file(s) with line counts **at HEAD**, the Lean file(s) it
  creates, the packages it depends on, and the packages it unblocks.
- Hazards are numbered and each one must be answered in the agent's report. A hazard is
  only allowed in a plan if the planner actually looked at the source and found it.
- Acceptance always includes: `lake build` green, `bash scripts/checks.sh` green, a
  per-gate perturbation actually run (PLAN 12, R-41's rule), and non-vacuity evidence.
- Plans do not repeat PLAN section 4's R1-R11 rules; they point at them and record only
  the file-specific application.

## Queue

See PLAN 14.7 for the dependency-correct order. Current board:

| pkg | plan | status |
|---|---|---|
| P-05 | abi + encoding | in flight |
| P-06 | [P-06-api.md](P-06-api.md) | READY |
| P-07 | kzg | DRAFT |
| P-08 | vk | DRAFT |
