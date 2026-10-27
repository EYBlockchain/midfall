# P-13 - the Askama templates: 3,261 lines of `.yul` + 500 of `.sol` shells

Status: READY. **The last port package.** Measured, not taken from the earlier estimate
of 4,324: `templates/partials/verifier/*` 1,738 lines (7 files),
`templates/partials/quotient_numerator/*` 1,523 (2 files), `templates/contracts/*` 500
(3 `.sol` shells).

## Split - by file, three packages

| pkg | files | lines | why this grouping |
|---|---|---:|---|
| **P-13a** | `verifier/{AssemblyHelpers,VkLoading,Lagrange,QuotientAndLinearization,FinalPairing}.yul` | 1,018 | the smallest five, and `FinalPairing.yul` (92) is what P-SE proof step **P5** needs first |
| P-13b | `verifier/{TranscriptProofParser,AccumulatorHelpers}.yul` | 796 | the two big remaining verifier partials; `AccumulatorHelpers` is the acc-mode row and interacts with R-25 |
| P-13c | `quotient_numerator/{QuotientHelpers,QuotientNumeratorBlock}.yul` | 1,523 | `QuotientNumeratorBlock.yul:1439` is the `-nu_y(x)` negation D-P20 says is modelled nowhere - the last named gap |
| P-13d | `contracts/*.sol` shells + renderer glue | 500 | needs the above |

Do P-13a only. Report what the others need.

## What "porting a template" means here - read this before starting

These are **Askama templates**, not Yul. A `.yul` file is a Jinja-ish text program with
`{% for %}`, `{% if %}`, `{{ expr|hex }}` and `{% include %}`. Porting one means writing
a Lean function that renders the same bytes - PLAN section 8's requirement is "one Lean
fn per template/partial producing a `Yul.Block`; Jinja filters such as `hex()` ported
exactly".

**Two targets, and they are not the same.** PLAN D-P13 settled that the generator
identity is **structural** (`YulSemantics.SyntaxEq.stmtsBeq`), not textual - but M3's
acceptance is "golden byte-equality on corpus + Moonlight". So a template port must
produce text that is byte-identical to Askama's output AND parse to the AST the theorem
will use. Say explicitly which of the two your gates pin, and do not let a structural
gate stand in for a textual one.

## Hazards

1. **Whitespace and newlines are the whole difficulty.** Askama emits a line per
   `{% %}`-free source line; a `{% for %}` that renders zero times must remove its
   newline, an `{% if %}` else-branch changes indentation. Byte-equality lives or dies
   here. Gate against the **tracked rendered artifacts**
   (`target/poseidon-fixture-dump/Halo2Verifier.sol` is tracked; the dump's
   `proof.bin`/`calldata.bin` are NOT - see R-53/P-12 F-1), reading them at `#eval` time
   per D-P19, not against pasted strings.
2. **`hex()` and friends are filters with exact semantics.** `{{ (num_instances*32)|hex() }}`
   renders `0x20`. Port each filter as a named Lean function and gate it against the
   rendered artifact, not against your reading of Askama.
3. **`FinalPairing.yul` is the object of P-SE P5** (`finalPairing_spec`, the first
   semantic equivalence in the recommended order). Its `{% if %}` arms select between the
   accumulator-batched and plain pairing checks. Get the exact line ranges of both arms
   and say which one the deployed profile takes.
4. **`AssemblyHelpers.yul:94-104` and `:416` are load-bearing for a normative claim.**
   P-12 just used them to prove the calldata decoder is EXACT (correcting PLAN 13). If
   your port of that region disagrees with what P-12 measured, **stop and report** - that
   would reopen a settled finding.
5. **Do not import `Generator.Vk` or `Midfall/Instances/`** (D-P17). `LoweringPlan.lean`
   and `Calldata.lean` both established the pattern and the reason.
6. **`List.range'` takes a COUNT, not an inclusive end; `List.zipIdx` yields
   `(element, index)`.** Both are in plans/README.md standing notes; one of them was the
   basis of a false defect claim. Verify inherited claims in both directions.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`; **register your module** -
R-50), `Render.lean`/`RenderModels.lean`/`YulGolden.lean` (the existing render layer -
extend it, do not parallel it), and `P-SE-evidence/attack.md` FIX lines (binding).

**R-41** (perturbations actually run; report failures to redden - P-12 got 30/31 and
explained the one that could not bite), **R-48**, **D-P19**, **D-P13** (structural
identity for theorems, textual for golden tests).

Binding: PLAN section 4; `Vec` -> `List`; R4 release profile.

**No idle builds.** Multi-line edits in big Lean files have cost the orchestrator four
retries twice running - re-read what you changed and rebuild after every edit.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 845 across 49 files.
- At least 10 gates, including at least one **byte-exact** gate against a tracked
  rendered artifact (hazard 1) and one per Jinja filter used (hazard 2).
- **Required finding**: for each of the five templates, whether the port reproduces the
  tracked artifact byte for byte, and if not, exactly where it diverges. A near miss
  stated precisely is worth more than a claim of success that hides whitespace drift.
