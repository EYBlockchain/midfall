# P-AST3a - `quotientLin` to AST emission. Same template as P-AST2.

Status: READY. P-AST2 measured this one generalises now: `qalLinearization_ast` already
exists as a `yul%` snapshot, the render is 1,898 bytes / 42 lines occurring exactly once in
the tracked artifact, and **the only plan value it interpolates is `k`**.

## Scope decision, taken here so it is not drifted into

`blk .quotientLin` is **the template's own body**, not the artifact's whole quotient region.

**Why:** P-AST2 measured that feeding the real `quotient_numerator` includes into the render
makes it occur **0 times** in the artifact, while the empty-parameter render occurs once -
i.e. **the text port itself treats the includes as a separate region.** Adopting the same
decomposition is therefore consistent with the port, not a shortcut around it. Converting
the two includes (`renderQuotientHelpers` 826 B, `renderQuotientNumeratorBlock` 6,682 B,
both text) is the separate `Quotient/Evaluator.lean` string-machinery job - 18 sites - and
is **out of scope here**.

Say this in the `emitQuotientLin` doc comment, with the measurement, so a later package does
not silently redefine the boundary.

## Deliverable

1. `emitQuotientLinAt (k : Nat) : Block Op` and `emitQuotientLin (pv : PlanView) : Block Op`,
   constructor helpers only - no DSL extension, no fork edit.
2. Add to `GenAst.emittedPartials` (currently 3 entries; this makes 4).
3. **Gate with `stmtsBeq` against `qalLinearization_ast`** (the record) *and* the token
   comparator against `renderQuotientAndLinearization` (the tripwire). P-AST2 reproduced the
   blindness on its own slices: mis-spelling a builtin as a user call left token gates green
   while `stmtsBeq` reddened. Both relations required.
4. **Add the plant gate** in the `blkPinBites*` style: a `blk .quotientLin` set to the
   emitter's own placeholder must be rejected by `BlkIsEmitter` while `SupportedS` still
   holds of it. P-AST2 found this plant class is created *by* each conversion - before it,
   the placeholder was the emitter's answer, so the pin passed.
5. Update `placeholderPartials` (three remain: `vkLoading`, `transcriptParser`, `pcs`),
   `mainConcatKats_ok` / `lowerPinKats_ok` for the new `main` length, and any stale doc
   comments asserting counts.

## Constraints

* **Numeric spelling cannot be pinned by any AST relation** - P-AST2 measured that hex and
  decimal literals are equal under both `yulTokens` and `stmtsBeq`. If this slice has
  numeric divergences, use a string-containment gate like `numericSpellingDivergence_ok`.
* **Watch the `/-! ---- -/` trap** (standing note): a dash run right after `/-!` makes the
  rest of the file an unterminated comment, reported only at EOF.
* **No `yul%` DSL extension, no fork edit.** If a construct cannot be built with helpers,
  stop and report.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh`.
* **R-41 / D-P23**: every gate needs a demonstrated failure mode; report failures to redden.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5149 jobs**;
`checks.sh` green: 64 tracked sorries all owned, **1185 KATs across 78 files**, 84 statement
fragments, 9 fact families, 8 bundles (7 jointly exhibited), 102 modules, Statements hash OK.

Read first: `Midfall/Lowering/GenAst.lean` (copy `emitLagrange` / `emitTraceReturn` exactly
- same gate shapes), `Midfall/Generator/VerifierPartials.lean` (the text port and
`qalLinearization_ast`), `Midfall/Instances/SurfaceFixture.lean` (the `blkPinBites*` family
and `plantSurfaceWith`), `docs/design.md` D-P30.

**No idle builds.** Re-read what you changed after every edit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1185.
- `emitQuotientLin` gated by **both** relations; plant gate added and shown to bite.
- `emittedPartials` has 4 entries; 3 placeholders remain and are named.
- **Required finding**: of the three remaining placeholders, which can proceed with the same
  template and which are genuinely blocked? P-AST2 said `pcs` needs `Kzg.computations`
  converted first - say the same for `vkLoading` and `transcriptParser`, with evidence.
