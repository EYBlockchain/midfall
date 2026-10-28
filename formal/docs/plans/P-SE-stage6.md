# P-SE stage 6 - `Lowering/Obligations.lean`: the headline, and a warning first

Status: **BLOCKED ON A DECISION, not on work.** Sketch section **Q, lines 2164-2378**. Read
section **R (2379+)** too - it is the authoritative diff against PLAN 9.5.

## The warning

Section Q is the `LoweringCorrect` structure - the thing the whole programme is for. **Eight
of its ~15 fields reference identifiers that do not exist in the tree.** They are not typos
in my transcription; I read the sketch directly:

| identifier | used by | state |
| ~~`YulSemantics.SyntaxEq.stmtsBeq`~~ | `render_eq_print` | **EXISTS** - `vendor/yul-semantics/YulSemantics/Ast.lean:147`, `#check` resolves, six passing gates use it. The earlier "no declaration anywhere" was a `head -5` truncation error in the orchestrator's own grep | copy the field verbatim |
| `EvaluatorFrame` | `qvm_yul_refines` | 0 occurrences (stage 4 reported) |
| `FrameWellFormed` | `qvm_yul_refines` | 0 occurrences |
| `S.plan.qext` | `qvm_yul_refines` | stage 3's `PlanView` has no `qext` field |
| `outputBytes`, `yOf`, `perIdentityValues` | `qvm_yul_refines` | marked SKETCH in the plan |
| `List.Sorted` | `accFixedBases_producer` | Mathlib order theory not in the built surface |
| `OperandModel` (as sketched), `segmentsOf` | `qvm_validated_noBoundsFault` | types marked SKETCH; verify against P-09e's real validator signature |
| `IsAlignedSubslice` | `points_subgroup_checked` | marked SKETCH |

`qvm_yul_refines` alone needs five of these. So **section Q cannot be copied verbatim**,
and the honest options are:

* **(a)** define the missing pieces as part of stage 6 - `EvaluatorFrame` and
  `FrameWellFormed` are genuinely new definitions the plan always owed, and stage 5's
  `QvmFold` should supply `perIdentityValues`/`yOf`/`outputBytes`. Then Q is copyable.
* **(b)** state `LoweringCorrect` with the fields that ARE expressible now, and leave the
  rest as named holes with the missing dependency recorded - the pattern stages 1-5 used.
* **(c)** do not silently restate them differently. That is the failure mode PLAN 12 forbids.

**My recommendation: (a) for `EvaluatorFrame`/`FrameWellFormed`/`perIdentityValues`** (they
are real objects the programme needs, and stage 5 is producing their inputs), **(b) for
`stmtsBeq`** (that is a decision about D-P13, not a definition to invent here), and **(b)
for `S.plan.qext`** until P-11's `LoweringPlan::new` blocker clears.

## What stage 6 should do

1. Copy every field of `LoweringCorrect` from section Q verbatim where the identifiers
   resolve. **Do not paraphrase.** Where they do not, apply the (a)/(b) split above and
   record each deviation at the site.
2. `SideConditions`/`SoundSide`/`CompleteSide` (lines 2184-2192) resolve - they are built
   from stage 2's `decodeCalldata`/`instOfWords?` and stage 3's `GenericX`/`NoLogupPanic`.
3. The non-vacuity gates the plan requires next to the structure (lines ~2350):
   `example : realSurface.Supported realSurface.o₀`,
   `#eval (realSurface.astOfMain o₀).isSome -- expect true`, and the trace-render
   refutation for `only_two_outcomes`. Stage 4 already proved `supportedInhabited` and
   `supportedRefutedForTraceRender` in `Instances/SurfaceFixture.lean` - reuse, do not
   duplicate.
4. Derived theorems listed in section 17: `lowering_equivalence`,
   `lowering_equivalence_noAcc`, `end_to_end_acc_complete`,
   `contractRef_noAcc_of_semanticEquivalence` (**rfl** - it reuses the already-proved
   `Lowering.contractRefAccepts_iff_verifyMsgs`), `verifyNative_iff_msgs_codec`.
5. Regenerate `SORRY.md` via `scripts/gen_sorry.sh`.

## Hard constraints

* **`ir_refines` and `lowering_equivalence` cannot be *proved*** while `RunContractIR` is
  uninhabited - the vendored dialect lacks `memoryguard`/`setimmutable` (D-P15). Stage 4
  declined to state them for exactly this reason. Stating a field is fine; stating a
  theorem whose only hypothesis is unsatisfiable is the vacuity class. **Say which you are
  doing.**
* **Never edit `Statements.lean`** - frozen, hash-checked.
* **False as written: stop and report.** Five such defects in five stages.
* Doc comments in the style of `Exec/Accumulator.lean`. Verify every `-- SKETCH` name
  against `survey.md` or `#check`; see `P-SE-statements.md` for the dead list.
* **Never perturb the working tree in place** (R-54). `Fr 17` too small for magnitude
  gates (R-55). Model-dependent gates go in `Instances/` (R-55).
* Register the module (R-50). Numbers from `lake build` and `scripts/checks.sh` only.

Do NOT edit Rust files, `Statements.lean`, `vendor/`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from stage 5's.
- `LoweringCorrect` stated with every field either copied from Q or a recorded deviation.
- **Required finding**: per field, one of {copied verbatim, defined new (name it),
  deferred with blocker}. Plus whether `lowering_equivalence` can be STATED at all today,
  and if not, precisely what the vendored dialect must gain.
