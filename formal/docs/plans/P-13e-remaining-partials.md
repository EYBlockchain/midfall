# P-13e - the six partials my P-13 split missed. This closes gap A.

Status: READY. **This package exists because of an orchestrator planning error**: the P-13
split enumerated 7 verifier files when `templates/partials/verifier/` holds 13. P-13d
measured the damage - six partials, 698 Askama lines, **52,894 of the deployed artifact's
175,908 bytes (30.1%) have no render function anywhere**.

| template | lines | note |
|---|---:|---|
| `Constants.sol` | 255 | the biggest gap; `DVK:68`/`DVK:99` are already used as evidence by P-13b/P-13c - do not disturb those |
| `PrecompileSmoke.sol` | 216 | |
| `Constructors.sol` | 92 | opens with a `match` tag whose arm bodies start on the next line - one of the two whitespace-only lines gate 10 attributes to the shell's own holes |
| `TraceReturn.yul` | 73 | **P-SE step P5 needs `traceReturn_spec`**, whose subject this is |
| `Pcs.yul` | 39 | **P-SE step P5's `pcs_spec`** subject |
| `TraceAndGasHelpers.yul` | 23 | gate 9 already proves its deployed render is the empty string - so a byte gate here pins nothing; label it |

Reuse `VerifierPartials.lean`'s layer and `Contracts.lean`'s `RootCtx`. **Extend
`PartialCtx` in place if it needs fields; do not build a parallel renderer.**

## The gate that tells you when you are done

`Contracts.lean` gate 10 tiles the artifact and prints gap sizes:
`[0, 29032, 0, 6, 6, 0, 6, 6, 6, 23323, 569, 0]`. **Your success condition is that the
non-zero gaps shrink to zero** as each partial gains a render. Re-run that gate after each
one and report the tile vector each time - it is an objective measure of completeness and
it is the thing I got wrong.

## Hazards

1. **Every byte gate must assert length.** P-13c found `occursOnce` + prefix boundary is
   satisfied by a truncated render; P-13d demonstrated it in gate 20. Do not reintroduce it.
2. **Zero-render regions need labelling, not gating.** `TraceAndGasHelpers` renders empty
   in the deployed profile. A byte gate on an empty string is vacuous - say so and gate
   structurally or synthetically with a label, as P-13b/P-13d did.
3. **`Pcs.yul` and `TraceReturn.yul` are the subjects of two P-SE per-partial theorems**
   (`pcs_spec`, `traceReturn_spec`). Port them with those consumers in mind: name the
   regions a later proof would induct over, and say whether the render is expressible as a
   `Yul.Block` (D-P13's structural identity) or only as text.
4. **`Constants.sol` interacts with settled evidence.** `DVK:68` (hex_padded) and `DVK:99`
   (const_max) are cited by P-13b and P-13c gates. If your port changes how those values
   are produced, verify those gates still pass - do not just check your own.
5. **Re-measure.** My briefs have been wrong about counts in six consecutive packages,
   including this split.
6. **D-P17**: no `Generator.Vk`, no `Midfall/Instances/`. `List.range'` takes a count;
   `List.zipIdx` yields `(element, index)`.

## Rules

Read first: `docs/plans/README.md` standing notes; `VerifierPartials.lean` (68 gates);
`Contracts.lean` (28 gates, `RootCtx`, and gate 10's tiling); `P-SE-evidence/attack.md`
FIX lines (binding). **R-41**, **R-48**, **D-P19**, **D-P13**.

Binding: PLAN section 4; `Vec` -> `List`; R4 release profile.

**No idle builds.** Anchored multi-line edits have cost the orchestrator ten swallowed
lines across three repairs - re-read what you changed, rebuild after each edit.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 941 across 51 files.
- At least 12 gates, one per partial minimum plus the tiling re-measurement.
- **Required finding**: the final gate-10 tile vector, and an explicit statement of
  whether gap A is now closed - i.e. does every byte of the deployed artifact now come
  from a Lean render function or a labelled synthetic/structural gate?
