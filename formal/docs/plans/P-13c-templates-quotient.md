# P-13c - `QuotientHelpers.yul` + `QuotientNumeratorBlock.yul`: the last named gap

Status: READY. 81 + 1,442 = 1,523 template lines. **This package contains the thing
D-P20 says is modelled nowhere**: `QuotientNumeratorBlock.yul:1439`,
`let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)` - the
`-nu_y(x)` negation. Confirming it is ported and gated closes a normative gap.

Reuse P-13a/P-13b's plumbing in `VerifierPartials.lean`: `PartialCtx` (now 34 fields),
`jinjaFor`, `poseidonCtx`, `occ`/`artifactMatch`/`includeBoundary`, `readDump`. Extend
`PartialCtx` in place if needed; do not build a parallel layer.

## The free gate P-13a left you

Their rendered bytes occupy **D:1588-2538** (QuotientHelpers' first rendered line is
D:1588; QuotientAndLinearization's own tail starts D:2539), and they are exactly the two
arguments `renderQuotientAndLinearization` already takes. So you can gate by feeding your
output into that function and re-running `quotientAndLinearization_ownBytes_ok`'s
boundary. **Use that** - it is a real end-to-end check the earlier packages set up.

Inputs you will need, all already ported in `Models.lean`: `quotientPow5Helper`,
`quotientLimb7Helper`, `quotientWideLimb7Helper`, `limb7YulCoeffs`, `wideLimb7YulCoeffs`,
`frDelta`, and the QVM opcode / mem-token tables.

## Hazards

1. **Re-measure everything.** My briefs have been wrong about line counts in four
   consecutive packages (most recently by 211 lines, and about which file a line lived
   in). Verify against `git show HEAD:` before relying on any number here.
2. **The negation is a normative object, not just a line.** D-P20 item 1 says the
   `Output` of the QVM includes "the negation written to `QUOTIENT_EVAL_MPTR`" and that
   it is "Yul-side and modelled NOWHERE". P-09h confirmed it is not in `yul_emit.rs`.
   **Required finding**: after your port, is the negation now represented in Lean? If
   yes, say precisely what represents it and whether D-P20 can be amended. If your port
   renders the line but nothing *models* its meaning, say that too - rendering text is
   not modelling arithmetic, and conflating the two would be exactly the vacuity the P-SE
   attack pass is hunting.
3. **1,442 lines is the largest template in the tree and it is where the QVM's emitted
   program text lives.** It will have the most `{% for %}` nesting and the most
   zero-render cases. Where a loop renders zero times in the deployed profile, a
   byte-exact gate pins nothing - say which regions are actually exercised, as P-13b did,
   and gate the rest structurally or synthetically with a label.
4. **Do not claim the QVM cross-check extends to this file without running it.** P-09h
   built a genuine second-implementation check (Emitter->Yul->interpret vs
   `evalQuotientExpr`). If your render plus that reader can be composed, that is
   high-value; if not, say what is missing rather than asserting agreement.
5. **D-P17**: no `Generator.Vk`, no `Midfall/Instances/`. **`List.range'` takes a count;
   `List.zipIdx` yields `(element, index)`.** Verify inherited claims in both directions.
6. **The trailing-newline rule** (Askama drops an included file's final newline) applies.
   Neither of P-13a's nor P-13b's templates used `-%}` right-trim; if this one does, pin
   the rule - P-13d needs it.

## Rules

Read first: `docs/plans/README.md` standing notes; `VerifierPartials.lean` (the plumbing
and the 46 gates whose style to match); `FoldCompute.lean`/`QuotientBlocks.lean` (the QVM
side you may be able to cross-check against); `P-SE-evidence/attack.md` FIX lines
(binding).

**R-41** (perturbations actually run; report failures to redden - P-13b ran a source-level
negative control and reported seven honest non-bites), **R-48**, **D-P19**, **D-P13**.

Binding: PLAN section 4; `Vec` -> `List`; R4 release profile.

**No idle builds.** Multi-line anchored edits have cost the orchestrator eight swallowed
lines across two repairs. Re-read what you changed; rebuild after every edit.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 891 across 50 files.
- At least 14 gates, including the D:1588-2538 boundary check described above and a
  byte-exact gate for each of the two templates where the deployed profile exercises them.
- **Required finding**: is the `-nu_y(x)` negation now modelled in Lean, or only
  rendered? Answer in those terms, not by pointing at the gate.
