# P-AST3b - extend `PlanView` with the accumulator fields, then convert `vkLoading`.

Status: READY. P-AST3a measured this as **the cheapest remaining placeholder** - blocked on
`PlanView`, not on text machinery. Two steps, one package, in this order.

## Step 1 - `PlanView` gains four accumulator fields

`renderVkLoading` interpolates 7 ctx values; `PlanView` (`Inv.lean:110`) carries `k`,
`numInstances`, `proofLayout` - and **not** the four accumulator words:
`expectedAccOffset`, `expectedNumAccLimbs`, `expectedNumAccLimbBits`,
`expectedHasAccumulatorWord`.

* **Derive them from `cfg.accumulator`; do NOT hard-code zeros.** P-AST3a measured all four
  are 0 in the deployed profile and explicitly declined to hard-code them: *"hard-coding the
  four zeros would reproduce the deployed bytes and lie for any accumulator plan."* That
  refusal stands - a fixture that matches by accident is the vacuity class.
* `proofLen` is already derivable (measured `poseidonCtx.proofLen == poseidonProofLayout.proofLen
  == 4320`, `Abi.lean:249`) - reuse it, do not add a fifth copy.
* **The duplicate-facts gate will react.** These four fields are copies of facts the Rust
  derives from `cfg.accumulator`. Either derive them in the `PlanView` constructor so there
  is one carrier, or add named pins and register the family in
  `scripts/check_duplicate_facts.py`. Do not bypass the gate.
* `Surface.plan_hasAccumulator` already pins `plan.hasAccumulator` to
  `cfg.accumulator.isSome` - follow that pattern if a pin is the right shape here.

## Step 2 - convert `vkLoading` with the established template

`emitVkLoading (pv : PlanView) : Block Op`, added to `emittedPartials` (4 -> 5), with:

* **Both gate relations.** `stmtsBeq` against a `yul%` quotation of the render as the
  record; `yulTokens` against `renderVkLoading poseidonCtx` as the tripwire. P-AST3a
  reproduced the blindness a third time - a builtin mis-spelled as a user call left every
  token gate green while `stmtsBeq` reddened. Both are required.
* **A `yul%` snapshot** of the deployed slice, generated the way `qalLinearization_ast` was.
  Measured: `renderVkLoading poseidonCtx` is 4,494 B / 74 lines, occurring exactly once.
* **The plant gate** in the `blkPinBites*` style: a `blk .vkLoading` set to the emitter's own
  placeholder must be rejected by `BlkIsEmitter` while `SupportedS` still holds of it.
* Update `placeholderPartials` (two remain: `transcriptParser`, `pcs`), `mainConcatKats_ok`
  and `lowerPinKats_ok` for the new `main` length, and any stale count comments.

## Constraints

* **No DSL extension, no fork edit.** Constructor helpers sufficed for four slices.
* **Numeric spelling is invisible to every AST relation** (standing note) - use a
  string-containment gate if this slice has hex-vs-decimal divergence.
* **Watch the `/-! ---- -/` trap** (standing note): a dash run right after `/-!` turns the
  rest of the file into an unterminated comment, reported only at EOF.
* **`vkLoading` is the partial whose `Inv .vk` clauses are the payload-image pin** - check
  that `Inv`'s existing `.vk` clauses still discharge after the `PlanView` change.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh` only.
* **D-P23 / R-41**: every new claim needs a witness AND a demonstrated failure mode.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5151 jobs**;
`checks.sh` green: 64 tracked sorries all owned, **1197 KATs across 80 files**, 107 statement
fragments, 9 fact families, 8 bundles (7 exhibited, 3 gaps, 2 joint refutations), 104
modules, Statements hash OK.

Read first: `Midfall/Lowering/Inv.lean` (`PlanView`, `EnvAgrees`), `Midfall/Lowering/GenAst.lean`
(copy `emitQuotientLin` exactly - same shape: one plan parameter, existing helpers),
`Midfall/Generator/VerifierPartials.lean` (`renderVkLoading`, and how `qalLinearization_ast`
was made), `Midfall/Instances/SurfaceFixture.lean` (`plantSurfaceWith`, the `blkPinBites*`
family), `docs/design.md` D-P30, `docs/REVIEW.md` R-62.

**No idle builds.** Re-read what you changed after every edit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1197.
- `PlanView` carries the four fields **derived from `cfg.accumulator`**, with the duplicate-
  facts gate satisfied by derivation or by named pins.
- `vkLoading` emits a real AST, gated by both relations, with a biting plant gate.
- **Required finding**: with two placeholders left, what does `transcriptParser` need beyond
  the four AssemblyHelpers callees and six plan values P-AST3a named - is the helper
  conversion (`Quotient/Evaluator.lean`, 18 string sites) now the critical path for the
  generator, ahead of `pcs`?
