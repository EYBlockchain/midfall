# P-FRAME - is the emitted program actually frame-insensitive? Measure before assuming the crux.

Status: READY, and **cheap**. P-CODECLAWS found that `L.main`'s opacity **is not the wall it
looked like**: `BlkIsEmitter S` pins `S.L.main = GenAst.emitMain S.plan`, `curveBlk` discharges
it at the curve Surface **by `rfl`**, and the emitted AST is already walked in-tree by the
P-BUNDLE machinery (`bundleWalkSs`, `callClosure`, `eip2537TargetsIn`).

## Why this is the right next step

`lowering_equivalence` is **proved** and its bundle is **fully inhabited** except `hc :
LoweringCorrect S product`. The open leg is `ir_refines` at `ShellModel.modelIr S`, which R-66
showed is **false for a general program** — the dispatcher prologue leaves `activeWords = 3` and
writes word `0x40`, while `initState` has `activeWords = 0`.

> **But it can hold for the actual program.** So: **measure whether the emitted program reads
> either of the two things that differ.** If it doesn't, the crux is not the frame problem.

## Step 1 (do this FIRST — it is a measurement, not a proof)

**Syntactic walk of `GenAst.emitMain S.plan` proving:**
- no `msize` occurs anywhere in the emitted AST (nor in any emitted partial reachable from it);
- no read of word `0x40` **except** `headGuard`'s bound test `gt(mload 0x40, 0x1000)`.

**With a negative control**: plant such a read into a clone and show the walk rejects it.
A walk that accepts everything is decoration — this project has measured 28 blind spots.

## Step 2 — the frame-insensitivity lemma

If Step 1 passes: two runs from states differing **only** in `activeWords` and word `0x40`
agree in `ObsView`, for any program with the Step-1 syntactic property.

Note `0` and `128` both fail `gt(·, 0x1000)`, so `headGuard` cannot distinguish the frames —
that is already provable and worth landing regardless.

## Step 3 — only if 1 and 2 hold

Discharge `ir_refines` at `modelIr S` for the curve Surface, or report precisely why not.
**Do not fake it**: if it needs the run leg (`gap_runLeg_unexhibited`), say so and stop.

## If Step 1 FAILS

**That is a major finding, and the better outcome than a false positive.** If the emitted
program *does* read `msize` or `0x40` load-bearingly, then `ir_refines` at `modelIr S` is
**refutable**, not merely unprovable — the same class as the original `ir_refines` and the
`Holds` unsatisfiability. Report it with the specific statement and address.

## Constraints

* **Never weaken a statement to make it provable.** If `ir_refines` cannot be discharged, say so.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **28 times**; a
  gutted conjunct of a joint exhibit is now also partly covered (conclusion-scoped matching),
  but `(P -> True)` still passes. Claim no coverage you do not have.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.** A splice left
  three orphan lines that the size check missed; only reading the file caught it.
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work** — a
  checkout silently reverted 241 lines of proof last session. Use content saves.
* **`lean_grep.py` is now fixed** for primed identifiers — do not re-break it, and note the
  string-literal `sorry` trap is deliberately preserved.
* **SORRY.md traps**: comment edits shift `file:line` pins. Regenerate with
  `scripts/gen_sorry.sh`; three-way agreement.
* **Method rule**: before claiming a name is missing, try the unprefixed spelling, check for a
  project definition shadowing a Mathlib one, and remember `import Midfall` resolution ≠
  this file's import closure.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~9–10 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5215 jobs**, 125 modules; `checks.sh` green: **41 tracked sorries**, 1318 KATs,
245 fragments, 6 gap defs, 30 pins, Statements hash OK.

Read first: `Midfall/Lowering/GenAst*.lean` (`emitMain`, the walker machinery),
`Midfall/Lowering/Partials.lean:268` (`BlkIsEmitter`), `Midfall/Instances/CurveSurface.lean`
(`curveBlk`, `loweqBundleCore` — now 8 conjuncts), `Midfall/Yul/ShellModel.lean` (`modelIr`,
`wrap`, `prologue_write_is_observable`, `no_mem0_reaches_the_arm_frame`,
`arm_frame_reads_a_different_head_word`), `Midfall/Lowering/Obligations.lean:665`
(`lowering_equivalence`), `Midfall/Yul/Bridge.lean` (`ObsView`, `msize` readers at
`EVMExec.lean:375/:765`), `docs/REVIEW.md` R-66 and R-67.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Step 1 measured, **with its negative control**.
- **Required finding**: is the emitted program frame-insensitive? If yes, land Step 2 and say
  what remains for Step 3. If no, name the exact statement that breaks `ir_refines` — that
  would be the third refuted headline hypothesis in this project and worth more than a proof.