# P-SPEC1 - prove ONE Partials spec end-to-end. The calibration datum the ledger is asking for.

Status: READY, and **the single most valuable unblocked item.** Ledger R8: proving one
`Partials` spec anchors **both** M-B (4-6 sessions, still pure extrapolation) and M8's
re-derive-preconditions-against-dispatcher-memory step — **the same unknown counted twice.**

## Which spec

Six of the ten do **not** bind `Holds` and so need no curve Surface: `vkLoading_spec`,
`transcriptParser_spec`, `lagrange_spec`, `lagrange_progress_spec`, `quotientLin_spec`,
`traceReturn_spec`. **Pick the cheapest that exercises the run leg**, and say why you chose
it. `traceReturn_spec` is likely smallest (a terminal arm); `lagrange_spec` exercises more
machinery (batch inversion, the Lagrange loops) and so calibrates more.

**Do not pick one of the four `Holds`-binding specs** — P-CSURFACE-M8 recorded they still
need `hcd`/`hinst`/`hsnap`, the run leg, named in `curveSpecResidualBinders`. That is M8 work.

## Deliverable

1. **Prove the spec.** Replace one registered `sorry` with a real proof. Register: 57 -> 56.
2. **Record the wall-clock honestly** — this is the datum. Time from first attempt to green
   build, and count compile iterations.
3. **Write down what the proof actually needed** that the sketch did not name. Every package
   so far found the sketch under-specified; that finding is worth as much as the proof.
4. **Note which Bridge lemmas you needed and which existed.** `staticcall_failure_reverts` is
   proved; `dialect_deterministic` is not, and M-D depends on it.

## Constraints

* **D-P23 both halves as theorems** for any new lemma the proof needs. Falsification-deletion
  gap measured **fifteen** times — claim no coverage for falsifications.
* **Do not weaken a spec to make it provable.** If the statement is unprovable as written,
  **stop and report** — that is finding class 16, and it has happened sixteen times.
* **`BlkIsEmitter` is a hypothesis of all ten** (P-AST). Check your spec's binder list before
  assuming what you may use.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps, both measured**: the word `sorry` inside a Lean **string literal** counts
  as a proof hole, and a **comment-only** edit shifts `file:line` pins. Regenerate with
  `scripts/gen_sorry.sh`; budget a full `checks.sh` run (~8.5 min) after line-shifting edits.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
* **`lake env lean`**: pass `-DautoImplicit=false`. No unused `simp` args in `#eval` files.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5212 jobs**, 122 modules; `checks.sh` green: **57 tracked sorries**, 1304
KATs across 91 files, 158 fragments, 12 fact families, 8 bundles with 5 gap defs, 30 pins.
**D-P32**: Rust pinned to `2d52f24`. **D-P36a** pairing axioms are installed and gate-pinned.

Read first: `Midfall/Lowering/Partials.lean` (the ten specs, their binders, and the
`BlkIsEmitter` pin), `Midfall/Instances/CurveSurface.lean` (`curveSpecResidualBinders` — what
the run leg still needs), `Midfall/Yul/Bridge.lean` (`staticcall_failure_reverts`, the five
remaining Bridge sorries), `docs/plans/P-SE-semantic-equivalence.md` section N (lines
1794-1931) — **the sketch is the authority** — and `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **56**.
- **Required finding**: the measured wall-clock and iteration count for one spec, and what it
  implies for M-B's 4-6 estimate — is it confirmed, too low, or too high?