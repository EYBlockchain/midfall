# P-SE stage 3 - `Lowering/{Checkpoint,Snapshot,Inv}`

Status: READY. **D6 landed** (`9d0b94c`), which was this stage's blocker. The Exec
refactor made the intermediate values nameable from outside the do-blocks:
`alg.x`, `alg.xn`, `alg.splittingFactor`, `alg.minRot/maxRot/maxInstanceLen/rotations/lIS`,
the six evaluation arrays, `lagrangeTriple -> (lLast, lBlind, l0)`, and `PhaseA/B/C`
giving `x1..x4`, `fEval`, `v`, `pi`, `finalCom`, with `PAIRING_LHS/RHS =`
`c.dual.left.eval / c.dual.right.eval`. `readAlgebra`, `phaseB` and `lagrangeTriple` are
**group-free**, so they can be exercised with a hand-built key and no curve.

## Files

| file | content |
|---|---|
| `Lowering/Checkpoint.lean` | `Checkpoint`, `Partial`, `liveAt` |
| `Lowering/Snapshot.lean` | `snapshotOf` over the now-nameable Exec values |
| `Lowering/Inv.lean` | `Inv k` relating memory to the L0 state after phase k |

## Two attack findings that bind this stage directly

* **Finding 11**: `X_N_MINUS_1_INV_MPTR` has **no production consumer** (grep of
  `kzg/mod.rs`, `quotient.rs`, `QuotientNumeratorBlock.yul`, `quotient_numerator/*.rs`).
  So `Inv` must leave it **unconstrained** - do not invent a relation for a slot nothing
  reads, and do not silently constrain it either.
* **Finding 12**: `selector_accumulators` is phase-scoped
  (`LayoutMemory.lean:268-270`, lifetime `.phase .pcsFinalMsm`) but is **written by the
  quotient phase and read by PCS block 5**. So `Checkpoint.liveAt` must be
  checkpoint-aware for that region, not phase-scoped. Get this wrong and `Inv` will
  declare a live slot dead at exactly the checkpoint a later proof needs.

## What D6 left unnameable - do not fake it

1. **`expressions` and `linCom`**: `linearize` returns only the query array. Widening it
   to `{ expressions, linCom, queries }` is one mechanical change, deliberately not done
   because D6's decomposition ended at the multi-open queries. **If `Snapshot` needs
   them, say so and leave the field as a named hole** - do not reconstruct them by
   replaying the transcript, which is the R-30/R-32 drift hazard D6 exists to avoid.
2. **The faulting phase's partial output**: a phase that faults returns `.error` and loses
   what it computed. Per-phase prefix snapshots can name every COMPLETED phase but not the
   faulting one. State that as a limit of the design, not a bug.
3. **`acc : Option KzgAcc`** - the accumulator path is untouched by D6.

## Rules from the human - binding

1. Before each file read `P-SE-evidence/attack.md` and the matching `design*.md`.
   **FIX lines are binding.**
2. **Verify every `-- SKETCH` name** against `survey.md` or `#check`. Stages 1-2 found
   **fourteen** that do not resolve; report rather than invent.
3. **Doc comments in the style of `Exec/Accumulator.lean`.**
4. **Register every hole in `SORRY.md` via `scripts/gen_sorry.sh`.**
5. **NEVER edit `Statements.lean`.**
6. **False as written: stop and report.** Three such defects have been found in three
   stages now (`countdown_or_halt`, `decodeAcc_encode_pointPair`, and the vacuous
   `end_to_end_noAcc` right-hand side). Assume there is another.

## Hazards

1. **`Inv` must be satisfiable, not merely stated.** A vacuity gate: exhibit a concrete
   memory satisfying `Inv k` for each checkpoint you claim, and show a perturbation that
   breaks it. An `Inv` no state satisfies would make every per-partial theorem vacuously
   true - the exact failure mode review F1 caught in `end_to_end_noAcc`.
2. **R-47 / P-4a**: several closed forms need a root-of-unity hypothesis that is not yet
   discharged (`FieldConsts.IsWellFormed`, unblocked for `fc17` only). If `Inv` or
   `Snapshot` needs it, state the dependency rather than assuming it.
3. **NEVER PERTURB THE WORKING TREE IN PLACE** (R-54). A killed D6 harness left
   `.reverse` deleted from `MultiPrepare.fEval` - a semantic change that built clean and
   passed KATs. Apply source mutations to a copy outside the repo, or verify
   `git diff --numstat` after every harness run.
4. **`Fr 17` is too small for magnitude, width or truncation gates** (R-55): `truncate`
   is the identity there. Use `Fr 1009` or larger for anything sensitive to size.
5. **`Instances/` confinement greps DIRECT imports only** (R-55). If you need a concrete
   model to run a gate, put the gate in `Instances/`, as `ChallengeStream.lean` does -
   never in a file that `Statements.lean` or `Lowering/*` transitively imports.
6. **Register your modules** (R-50, hard failure). `lake env lean` does not apply
   lakefile options - numbers from `lake build` and `scripts/checks.sh` only.

**No idle builds.** Multi-line anchored edits have cost this project a broken unregistered
file and ten swallowed orchestrator lines. Re-read what you changed; rebuild after each.

Do NOT edit Rust files, `Statements.lean`, or another package's Lean file. Do NOT git add
or commit. `SORRY.md` only via `gen_sorry.sh`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 1054 across 62 files.
- All three files registered; every hole registered with an owner.
- The `Inv` satisfiability gates above (hazard 1) present and shown to be able to fail.
- **Required finding**: (a) can the seven per-partial `*_spec` theorems now be STATED
  (not proved) from `Snapshot`/`Inv`? List each with the values it needs and whether they
  are nameable. (b) does anything still force the transcript-replay approach D6 rejected?
