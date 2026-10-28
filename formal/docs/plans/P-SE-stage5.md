# P-SE stage 5 - `Lowering/{Qvm,QvmFold}`: the QVM valuation and the fold

Status: READY. Stages 0-4 landed (`83313c9`, `01c71a3`, `bcf653d`, `04adea7`).
Tree: 3417 jobs, 1090 KATs across 69 files, 91 modules, 51 tracked sorries all owned.

## Files (P-SE architecture index sections 15 and 16, both M6)

| file | content |
|---|---|
| `Lowering/Qvm.lean` | `QVMFr` <-> `Fr` bridge, the valuation layer, `RecognizersSound`, per-identity compile correctness |
| `Lowering/QvmFold.lean` | `expandItem`/`globalIdentities`/`qvmFrPow`/`FoldState`/`foldStep`/`quotientFold`, `SelectorFoldConsistent`, `IdentityCorrespondence` as a **def**, and `quotientFold_matches_linearization (hcons) (hvals) (hcorr) (hq)` as a theorem hole |

## The finding that may change what is dischargeable here

P-11 reported that `IdentityCorrespondence` **cannot be discharged** for a real plan
because `quotient_expr_from_expression` (QVM:2870) was unported. **P-09h and P-10c have
since ported the Evaluator and `quotientExprFromPlonkExpr`.** So re-check that claim
before inheriting it: if the bridge now exists, `IdentityCorrespondence` may be provable
for a real plan rather than only asserted as a hypothesis bundle. That would be the
difference between a fold statement with an assumption and one with a derivation.

## D-P20's restatement is the shape to follow

D-P20 (amended `514c808`) says `qvm_compile_correct` should be **two claims**, not one:
1. a **per-stream fold-agreement** claim over `evalQuotientProgramArtifacts` vs
   `expectedLinearizationArtifacts` - statable modulo `L.plan.qprog`;
2. a **per-identity compile-correctness** claim over `evalQuotientIdentity` - statable
   since P-09d.

The gap between them is named: the segment-evaluator seam (the test module's third
interpreter uses a `HashMap` memory where P-09b's uses a PRNG - a real mismatch, not
plumbing) and the native markers plus inline prefix, which enter no Lean fold at all.
**Do not paper over that gap with a fixture.** If a claim is only statable per-identity,
say so; the exclusion must be recorded, not implied.

## Rules from the human - binding

Read `P-SE-evidence/attack.md` and the matching `design*.md` before each file; **FIX lines
are binding**; verify every `-- SKETCH` name against `survey.md` or `#check` (stages 1-4
found **38** that do not resolve - report, never invent); doc comments in the style of
`Exec/Accumulator.lean`; register every hole via `scripts/gen_sorry.sh`; **never edit
`Statements.lean`**; **false as written: stop and report** - five such defects in five
stages, so assume there is a sixth.

## Hazards

1. **`stmtsBeq` does not exist.** D-P13 names `YulSemantics.SyntaxEq.stmtsBeq` as the
   authoritative structural equality, and stage 4 confirmed by grep that **no declaration
   exists anywhere** - only prose references. If any stage-5 statement needs structural
   equality of Yul, say what you used instead and why. Do not cite a phantom identifier.
2. **`Fr 17` is too small** for magnitude/width/truncation gates (R-55). Stage 3's witness
   collapsed there. Use `Fr 1009` or larger, or the real modulus.
3. **Never perturb the working tree in place** (R-54). A killed harness once left
   `.reverse` deleted from `MultiPrepare.fEval`, building clean and passing KATs. Use
   copies outside the repo, or verify `git diff --numstat` after every run.
4. **`Instances/` confinement greps DIRECT imports only** (R-55). Gates needing a concrete
   model go in `Instances/`, as `ChallengeStream`/`InvFixture`/`SurfaceFixture` do.
5. **`qvm_validated_noOOB` and the validator**: P-09e's validator is abstract over the
   operand model. `Supported.qvm` is now constructible end to end (P-11), so check whether
   the no-OOB statement can be written against the real predicate rather than a stand-in.
6. **Register your modules** (R-50). `lake env lean` does not apply lakefile options.

**No idle builds.** Multi-line anchored edits have broken files repeatedly this session,
including the orchestrator's own. Re-read what you changed; rebuild after each edit.

Do NOT edit Rust files, `Statements.lean`, `vendor/`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 1090 across 69 files.
- Both files registered; holes registered with owners.
- **Required finding**: (a) is `IdentityCorrespondence` now dischargeable, given the
  Evaluator and `quotientExprFromPlonkExpr` exist? (b) of D-P20's two claims, which are
  statable today and what exactly blocks the other. (c) can stage 6 (`Obligations`) start?
