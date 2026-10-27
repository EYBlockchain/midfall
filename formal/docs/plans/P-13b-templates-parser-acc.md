# P-13b - `TranscriptProofParser.yul` + `AccumulatorHelpers.yul`

Status: READY. P-13a (`9532dea`) landed the plumbing: `PartialCtx`, `jinjaFor`,
`poseidonCtx`, `occ`/`artifactMatch`/`includeBoundary`, `readDump`. **Reuse it - do not
build a parallel render layer.**

Reference: `templates/partials/verifier/TranscriptProofParser.yul` (424 lines) and
`AccumulatorHelpers.yul` (372). Lean target: extend or add alongside
`formal/Midfall/Generator/VerifierPartials.lean` - your call, say which and why.

**Re-measure every line count before you start.** P-13a's brief was off by 211 lines and
described a 13-file directory as 7 files. My numbers are the worst part of my briefs.

## What P-13a says you need that it did not supply

`PartialCtx` currently carries the 26 expressions these five read. You need to extend it:

* **TranscriptProofParser**: `abiSelectorBytes`, `abiProofHeadOffset`,
  `abiInstancesHeadCptr`, `numInstanceCptr`, `instanceCptr`, `proofCptr`,
  `commsMptrBase`, `reversedEvalsMptr`, `numEvals`, `numPointSets`.
* **AccumulatorHelpers**: `accumulator.limbs_per_word`, `identity_flag_words`,
  `expectedAccHasCarriedScalars`, `accFixedBases`, `accRhsMsmGas`, `gas.*`.

Each new field must be cited to its Rust source (`RenderModels`/`layout/memory.rs`), not
guessed - P-13a set that standard and its `poseidonCtx` cites each field.

## Hazards

1. **`TranscriptProofParser.yul:416` is load-bearing for a settled normative claim.**
   `if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }` is
   half of what P-12 used to prove the calldata decoder is **EXACT** (the other half,
   `AssemblyHelpers.yul:94-104`, is already ported and re-verified by P-13a). Your render
   of that region must satisfy P-12's gate-22 shape. If it disagrees, **stop and report**
   - it would reopen a finding that corrected PLAN 13.
2. **`AccumulatorHelpers` may largely zero-render.** The deployed profile has
   `expected_has_accumulator = false` (P-13a proved this: zero `acc_pair_alpha` or
   `batch_ptr` anywhere in the dump). So a byte-exactness gate against the tracked
   artifact may pin an *empty* render - which is a vacuous gate. **Check before promising
   a byte gate.** If the deployed artifact exercises little of it, say so plainly and gate
   the untaken arms by structure or by a synthetic context instead, labelled as such.
   This interacts with R-25 (the accumulator decoder ignores coordinate words of
   identity-flagged points) - do not reintroduce that malleability in the render.
3. **`TranscriptProofParser.yul:63` and `:319`/`:382` are the canonicity guards** P-12
   cited (`lt(inst_be, r)`, `iszero(lt(eval, r))`, exactly two of the latter). Gate the
   *count* - "exactly two" was part of the evidence, so a third appearing somewhere is a
   finding.
4. **The trailing-newline rule P-13a discovered**: Askama does not emit an included
   file's final newline. Applies to you.
5. **None of the five P-13a partials used `-%}` right-trim; you may.** If you hit it,
   pin the rule - P-13d will need it too.
6. **D-P17**: no `Generator.Vk`, no `Midfall/Instances/`. **`List.range'` takes a count;
   `List.zipIdx` yields `(element, index)`.** Verify inherited claims in both directions
   - one package's "live unpinned defect" was false, the next's brace finding was true.

## Rules

Read first: `docs/plans/README.md` standing notes; `VerifierPartials.lean` (the plumbing
you must reuse); `Calldata.lean` (P-12's gates 21-22, whose shape you must satisfy);
`P-SE-evidence/attack.md` FIX lines (binding).

**R-41** (perturbations actually run; report failures to redden - P-13a reported three
honest non-bites with reasons), **R-48**, **D-P19**, **D-P13** (structural for theorems,
textual for golden tests - never substitute one for the other).

Binding: PLAN section 4; `Vec` -> `List`; R4 release profile.

**No idle builds.** Multi-line anchored edits have cost the orchestrator eight swallowed
lines across two repairs - re-read what you changed, rebuild after every edit.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 873 across 50 files.
- At least 12 gates, with byte-exactness against the tracked artifact where the deployed
  profile exercises the template, and an explicit statement of what it does not.
- **Required finding**: does `TranscriptProofParser.yul:416` render satisfy P-12's
  gate-22 shape, and how much of `AccumulatorHelpers` does the deployed profile actually
  render?
