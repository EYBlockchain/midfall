# P-RUNSHELL - settle the free-identifier inversion. Cheap, and a REFUTATION if it holds.

Status: **HIGHEST VALUE, and bounded.** P-FRAME found the frame is **not** the crux of
`ir_refines` — and surfaced a **different** obstruction it deliberately did not claim:
> `gap_runShell_uninhabited_candidate` — the arm at the curve Surface has **61 free identifiers**
> (`vk` among them) and `curveSurface.bindLocals = []`, while `wrap` **is** inhabited
> (`unroutable_calldata_reverts`). If `RunShell` has **no runs at all**, `ObsEquiv` fails with
> one side inhabited and the other empty.

**P-FRAME's own words: "cheap to finish and it is a refutation, not a gap."**

## Step 1 — the inversion (bounded, do this first)

Prove: **there is no `obs` with `RunShell curveSurface W H [] c g obs`** — or produce one.

The mechanism is already named: `YulSemantics.Run` starts the environment at `[]
(`BigStep.lean:366`) and `Step.var` requires `VEnv.get V x = some v`. The first non-definition
statement of `main` evaluates `extcodesize(vk)` unconditionally, and `vk` is free.

**If it goes: `ir_refines` at `modelIr curveSurface` is REFUTED**, and
`LoweringCorrect curveSurface product` is **false for every `product`**. That is the fourth
refuted headline hypothesis in this project and it changes what the curve Surface can be used
for. **Say so loudly.**

## Step 2 — if refuted: is this a Surface bug or a spec bug?

**This is the important question, and it decides what happens next.**
- `RunEmitted.lean:67-76` already records the emitted program as a **fragment** whose free
  names are the contract-level `uint256 internal constant` declarations, and `RunEmitted`
  binds them with `shellLets` **to run it**.
- So: does `Surface.shell` / `RunShell` need the same binding? If `bindLocals` is supposed to
  bind them and `curveSurface.bindLocals = []` is simply **wrong**, this is a **fixture bug** —
  fix the Surface, do not touch the spec.
- If the spec genuinely has no place for contract-level constants, **that is a spec question**
  — report it, do not patch `RunShell`.

**Do not fix this by weakening `ir_refines` or by making `wrap` uninhabited.** The honest fix
is whichever one makes the two sides comparable for the right reason.

## Step 3 — the entry-path difference (independent of the above)

P-FRAME: `wrap` runs the callvalue guard, thirteen ABI bounds tests and
`bindLocalsFromImmutables`; `RunShell` runs the arm alone. **The two programs differ wherever a
guard fires or a bound local is read**, even with a frame-blind body. Assess whether this is a
second independent refutation or just part of the same binding problem.

## Constraints

* **A refutation is a SUCCESS here.** Do not soften it. Do not make `RunShell` inhabited by
  fiat. If the inversion goes, the finding is that the curve Surface cannot discharge
  `LoweringCorrect`, and that must reach the headline of your report.
* **Never weaken a statement to make it provable.** Standing human instruction.
* **D-P23 both halves.** Falsification-deletion gap measured **29 times**. And note P-FRAME's
  new finding: gutting `shellConsts_matches_artifact_ok` to constant `true` leaves the KAT
  printing true — **that pin is decorative as written**. If you rely on it, fix it first.
* **`freeNames` verdicts are `native_decide`, not `decide`** (mutual recursion through
  `WellFounded.fix`) — compiler-trusted. If the inversion depends on them, say so at the site.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore with `git checkout` on a file holding uncommitted work** — 241 lines lost once.
* **SORRY.md traps**: string-literal `sorry` counts; comment edits shift pins.
* **`lean_grep.py` is fixed** for primed identifiers — do not re-break it.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~9–10 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5217 jobs**, 127 modules; `checks.sh` green: **41 tracked sorries**, 1324 KATs
across 95 files, 245 fragments, 6 gap defs, 30 pins, Statements hash OK.

Read first: `Midfall/Instances/FrameWalkWitness.lean` (**`gap_runShell_uninhabited_candidate`
at :292, `armHasFreeIdentifiers` at :269, `bindLocals_binds_nothing`**),
`Midfall/Lowering/FrameWalk.lean` (`freeNames`), `Midfall/Lowering/RunEmitted.lean:67-76`
(the fragment problem, already recorded) and its `shellLets`, `Midfall/Yul/ShellModel.lean`
(`unroutable_calldata_reverts`, `wrap`), `Midfall/Lowering/Surface.lean` (`RunShell`,
`bindLocals`), `vendor/.../BigStep.lean:366` (`Run` starts at `[]`), `docs/REVIEW.md` R-68.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- **The inversion settled**: `RunShell curveSurface` proved uninhabited, or a run exhibited.
- If refuted: `gap_runShell_uninhabited_candidate` upgraded to a theorem, and the fixture-vs-spec
  question answered with a concrete recommendation.
- **Required finding**: can the curve Surface discharge `LoweringCorrect` at all? If not, which
  Surface can, and what does that cost?