# P-SE stage 4 - `Lowering/{Surface,Partials}`: the thing that unblocks the seven specs

Status: READY. Stage 3's headline finding is that **all seven `*_spec` theorems have their
`Inv` hypotheses but none can be written completely**, because
`blk : Partial -> PlanView -> Block Op` does not exist. P-13 ported the templates as
**text renders**, not Yul ASTs. `Partials.lean` is where `blk` comes from, so this stage
converts seven unwriteable theorems into seven statable ones.

## Files

| file | content |
|---|---|
| `Lowering/Surface.lean` | the real `Lowered`/`Supported`/`Deployment` under **new names** (P-SE keeps `Lowering/Types.lean` placeholders so the frozen file keeps elaborating); the fixture Surface; non-vacuity gates |
| `Lowering/Partials.lean` | `blk`, `PartialSound`/`PartialProgress`, `PartialSpecs`, `finalPairing_*`, `traceReturn_spec` |

## The blocker you must decide about, not work around

`DeploymentW` needs `memoryguard <= 0x1000` (attack FIX 32) and the VK-immutable pins.
**Stage 1 measured that `memoryguard` and `setimmutable` are absent from the vendored
dialect - 0 occurrences in `EVMOp.lean`.** That is the D-P15 prerequisite, still owed.
So either: (a) state `memguard` as a named gap with the vendor dependency recorded, or
(b) report that the vendor edit is needed and stop. **Do NOT edit `vendor/`** - it is a
pinned fork and the edit is a separate decision. Choose (a) unless you find it makes
something unsatisfiable, and say which.

## Non-vacuity is the point, not a formality

attack FIX 44 and P-SE decision D2 both require it. The fixture Surface must come with
gates proving `realSurface.Supported realSurface.o₀` **is inhabited** and
`realSurface.irCheck ir₀ = true` is reachable - not merely well-typed. Stage 3 set the
standard: `Inv` was made a decidable Bool specifically so satisfiability could be
exhibited, and `invSatKats_ok` shows a witness at all seven checkpoints. A `Supported`
nothing satisfies would make every theorem above it vacuously true - the fourth instance
of the F1 class if it happens.

## Decisions this stage must honour

* **D-P18**: `Supported.layout` is `WellFormed && validate = .ok ()` (adopted as D3).
* **Review F1, already applied to PLAN 9.5**: run existence must be an explicit
  conjunct, never implied by a `forall` over an empty set of runs.
* **attack FIX 36**: world-local call relations - stage 1 proved
  `honestCalls_worldLocal`/`permissive_worldLocal`; use them, don't restate them.
* **attack FIX 32**: `callvalue = 0`, `AUTHORIZED_VK` immutable = `vkAddr` plus the
  quotient twin, `memoryguard <= 0x1000`.
* **D-P16**: PLAN 9.5's accumulator statements mean the **Generator** `AccumulatorEncoding`.
* **Stage 3's arity note**: `Bridge.Dialect` is `@[reducible]`, so `calls`/`gas` are
  erased from `VEnv` and cannot be recovered from `Inv`'s own argument - **quantify them
  at the theorem level**.

## Rules from the human - binding

Read `P-SE-evidence/attack.md` and the matching `design*.md` before each file; **FIX lines
are binding**; verify every `-- SKETCH` name against `survey.md` or `#check` (stages 1-3
found **28** that do not resolve - report, never invent); doc comments in the style of
`Exec/Accumulator.lean`; register every hole via `scripts/gen_sorry.sh`; **never edit
`Statements.lean`**; **if a statement is false as written, stop and report** - four such
defects have been found in four stages, so assume there is a fifth.

## Hazards

1. **Never perturb the working tree in place** (R-54). Apply source mutations to a copy
   outside the repo, or verify `git diff --numstat` after every harness run.
2. **`Fr 17` is too small** for magnitude/width/truncation gates (R-55). Stage 3 hit this
   for real: its witness `x4 = 51 = 0 mod 17` made a dropped write invisible.
3. **`Instances/` confinement greps DIRECT imports only** (R-55). Gates needing a concrete
   model go in `Instances/`, as `ChallengeStream.lean` and `InvFixture.lean` do.
4. **`linCom` is nameable as `queries.back?`** (`Verifier.lean:802`) without widening
   `linearize`. Stage 3 deliberately declined - it is a positional pin on another
   package's ordering. If you need it, choose that trade-off explicitly and say so, or
   widen `linearize` properly. Do not do it silently.
5. **Register your modules** (R-50). `lake env lean` does not apply lakefile options.
6. **Re-measure inherited claims in both directions.**

**No idle builds.** If you run short on room, leave files compiling or unregistered.

Do NOT edit Rust files, `Statements.lean`, `vendor/`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 1075 across 66 files.
- Both files registered; holes registered with owners.
- **Required finding**: how many of the seven `*_spec` theorems are now STATED (even if
  proved with `sorry`), and for each, what is still missing. If fewer than seven, name the
  blocker per theorem.
