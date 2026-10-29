# P-AST4 - `transcriptParser` to AST emission. Largest slice yet; split if needed.

Status: READY. P-AST3b measured this as **cheaper than I had assumed** and NOT blocked on
the `Quotient/Evaluator.lean` helper conversion. It is also **3.8x the size of vkLoading**
(318 lines / 17,140 B), so scale is the risk here, not capability.

## What is already available - measured by P-AST3b, re-verify before relying on it

* **The four callees are already sliceable**: `renderFunction` finds `transcript_init` (4
  lines), `common_word` (4), `common_uncompressed_g1` (13), `squeeze_to` (9) inside
  `renderAssemblyHelpers`. Same job P-AST did for `fail`/`ec_pairing`, machinery exists.
* **Seven `proofLayout` section accessors are already on `PlanView`** (`evals`,
  `lookupMultiplicities`, `lookups`, `permutationProducts`, `qEvals`, `quotientLimbs`,
  `trash`).
* **Six plan values are NOT on `PlanView`**: `userPhases` (a List the render loops over),
  `numLookups`, `numPermutationZs`, `lookupHPlusAcc`, `numTrashcans`,
  `truncatedChallenges`. These must be added - see the duplicate-facts warning below.
* **The 12 trace arms and 8 gas-checkpoint arms zero-render** under `SupportedS.production`
  - not blockers, but see the standing note about zero-valued data.

## Suggested split - take it if the size warrants

Given the interruption pattern has cost this project two truncated packages, **split if you
judge one session is too long**:

* **4a**: the four helper slices (`emitTranscriptInit`, `emitCommonWord`,
  `emitCommonUncompressedG1`, `emitSqueezeTo`) + the six `PlanView` fields + pins.
* **4b**: `emitTranscriptParser` itself + snapshot + plant gate.

Each sub-package must leave the tree compiling and all gates green. Do not half-register.

## The gate rule that changed since the last slice - READ THIS

**Standing note, earned by P-AST3b:** hard-coding four accumulator words to zero reddened
**neither** `yulTokens` **nor** `stmtsBeq`, because the deployed profile values ARE zero.
Only a **plan-dependence gate** - perturb the plan, require the output to move - caught it.

`transcriptParser` is full of exactly this hazard: the trace and gas arms render nothing, and
several counts are small or zero at the fixture. So **every interpolated value needs a
plan-dependence check**, not just the two relations. `emitVkLoadingDetectsPerturbation_ok`
is the template - extend it to all six new fields and the seven accessors.

## Standard requirements (unchanged from P-AST3b)

* **Both relations**: `stmtsBeq` against a `yul%` snapshot as the record, `yulTokens` against
  `renderTranscriptProofParser` as the tripwire. The blindness has been reproduced four
  times now - a builtin mis-spelled as a user call leaves token gates green.
* **Snapshot re-read from the artifact** at `#eval` time, with size/occurrence pinned, the way
  gate 90 does for `vkLoading_ast`. Measured: 17,136 B / 318 lines, occurs once.
* **Plant gate**: `blkPinBitesTranscriptParserPlaceholder` + a **direct** `SupportedS` exhibit
  (the transport does not typecheck - P-AST3a and P-AST3b both measured this).
* **Six new `PlanView` fields must be DERIVED, not hard-coded**, and the duplicate-facts gate
  satisfied by derivation or named pins. Note P-AST3b's honest finding: the discovery rule
  uses **prefix** stem matching, so fields sharing a stem are not auto-caught - register the
  family by hand and say so in the comment.
* **`userPhases` is a List the render loops over** - that is the first list-valued `PlanView`
  field. If it forces a shape the helpers do not support, **stop and report** rather than
  flattening it into scalars, which would lose the loop structure the snapshot checks.

## Constraints

* **No DSL extension, no fork edit.** If `userPhases` cannot be built with helpers, report it.
* **Numeric spelling is invisible to every AST relation** - string-containment gate.
* **Watch the `/-! ---- -/` trap** - a dash run after `/-!` makes the rest of the file an
  unterminated comment, reported only at EOF.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54) - P-AST3b used an APFS clone under /tmp, which worked well.
* Register modules (R-50). Numbers from `lake build` and `scripts/checks.sh` only.
* **D-P23 / R-41**: witness AND failure mode for everything; report failures to redden.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5151 jobs**;
`checks.sh` green: 64 tracked sorries, **1209 KATs across 80 files**, 110 statement
fragments, 10 fact families (8 pins), 8 bundles (7 exhibited, 2 joint refutations), 104
modules, Statements hash OK.

Read first: `Midfall/Lowering/GenAst.lean` (copy `emitVkLoading` - closest precedent,
including the acc-arm pattern), `Midfall/Generator/VerifierPartials.lean`
(`renderTranscriptProofParser`, `renderFunction`, gate 90's snapshot pattern),
`Midfall/Lowering/Inv.lean` (`PlanView`, `accWordsOfEncoding` as the derivation model),
`Midfall/Instances/SurfaceFixture.lean` (`plantSurfaceWith`, `blkPinBites*`),
`docs/plans/README.md` standing notes (two new ones since P-AST3a).

**No idle builds.** Re-read what you changed after every edit; this is the largest slice and
the one most likely to need the split.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1209.
- `transcriptParser` real, or 4a landed cleanly with 4b scoped and reported.
- **Required finding**: with only `pcs` left, confirm P-AST3b's verdict that it needs a
  deployed `LoweringPlan` (P-11-shaped work) rather than text conversion - and say whether
  that `LoweringPlan` package should come before or after the `Quotient/Evaluator.lean`
  string-machinery conversion, since both are now unblocked by different things.
