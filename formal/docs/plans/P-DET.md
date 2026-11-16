# P-DET - `dialect_deterministic`: the named blocker for `ir_refines`. M-D, now critical path.

Status: **ON THE CRITICAL PATH.** P-INLINE reduced `ir_refines` at `modelIr curveSurface` to
**one missing lemma**: `Bridge.RunCommitted.det`, which inherits the registered hole
`Bridge.dialect_deterministic` (`Bridge.lean:186`). The field is now **open with a named
obstacle** — not refuted, not provable. **This package closes that obstacle or proves it cannot
be closed.**

## What is needed

**Uniqueness of the committed run at the OPEN dialect** — i.e. if `RunCommitted c g rt s V' st'
out` and `RunCommitted c g rt s V'' st'' out'` then the views agree. `P-INLINE` proved the two
sides **disagree** (`shell_run_is_not_the_wrap_run`); what's missing is turning disagreement into
`¬ ObsEquiv`, which needs uniqueness.

## Before spending a day: check whether it is even true

**`gas()` stays nondeterministic** per PLAN §7, and `ExternalGas` is an arbitrary oracle. So
literal determinism of runs is **probably false** — two runs with different gas oracles can take
different paths. The honest target is likely **determinism of the `ObsView` given a FIXED call
relation and gas oracle**, not determinism simpliciter.

**Establish which before proving.** If `dialect_deterministic` as registered is false, say so —
this project has refuted five statements that way and each saved a later package. And note the
history: `dialect_deterministic` has been cited as a prerequisite **twice and both times it
wasn't one** (P-SPEC1 for local-only specs; P-M8-IRCHECK for `ObsEquiv`). **Verify it is
genuinely needed for this specific reduction before attacking it.**

## Deliverable

1. **Confirm the reduction is real**: does `ir_refines_refuted_at_curveSurface_of_unique_wrap`
   actually need it, or is there another route to `¬ ObsEquiv`? P-INLINE said uniqueness is the
   only available route — re-check that claim rather than inheriting it.
2. **State the right form** — view-level determinism given fixed `c` and `g`, if that is what's
   true. **Do not weaken the registered hole to a triviality to close it**; if the correct
   statement differs from the registered one, record the difference as a deviation.
3. **Prove it, or prove a counterexample.** Either closes the question.
4. **Then discharge or complete the refutation of `ir_refines`** at the curve Surface.

## Also: record the fork decision

P-INLINE concluded the evidence supports **F2** — `RunShell` and `wrap` differ **by construction**
(the shell has no entry path), and **F1 is not even expressible** because `ShellModel` imports
`Surface` — the cycle is structural. **Add this to `docs/design.md` as D-P42** with the
consequence: `ir_refines`'s right-hand side should have been `wrap` all along, which is what
P-LOWEQ already did to the headline. `ir_refines` itself was **not** edited.

## Constraints

* **`lake build` green ≠ KAT gates passed** — always run `python3 scripts/kat_gate.py`. (R-71)
* **Do NOT round-trip files over ~1500 lines through `read`** — it truncated a 1967-line file and
  a splice dropped 612 lines. `Bridge.lean` size: check first.
* **NEW, and it governs any fuel work: fuel per LIST ELEMENT is pathological** — one `rfl` cost
  18+ min and 8.7 GB and was killed. **Fuel per NESTING LEVEL completes in ~4 s.** Any walk over
  GenAst output must use the second shape.
* **Never weaken a statement to make it provable.**
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **35 times**; and
  gates are independent measurements that never call the lemmas.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore with `git checkout` on a file holding uncommitted work** — use hash-verified copies.
* **KAT pins asserted** (`EXPECTED_KAT_TOTAL = 1346`, `EXPECTED_KAT_FILES = 97`). Move deliberately.
* **`gen_sorry.sh` locale-fixed**; `sha256sum` at `/sbin/sha256sum` — no shim.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Qvm.lean`, `InlineConstants.lean`.
  Do NOT git add or commit. Leave no scratch.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5220 jobs**, 130
modules; `checks.sh` green: **40 tracked sorries**, 1346 KATs across 97 files, 375 fragments.

Read first: `Midfall/Yul/Bridge.lean:186` (the hole and its docstring), `Midfall/Instances/
RunShellInhabited.lean` (`ir_refines_refuted_at_curveSurface_of_unique_wrap`,
`shell_run_is_not_the_wrap_run`), `Midfall/Instances/RunShellInversion.lean` section 12 (the
retraction record), `Midfall/Lowering/Surface.lean` (`RunShell`, `armProgram`, `shell_unfolds`),
`docs/design.md` D-P39, `docs/ETA.md`.

## Acceptance

- `lake build`, `checks.sh` **and** `kat_gate.py` green.
- D-P42 recorded (fork F2).
- **Either** `dialect_deterministic` closed **or** a counterexample proving the registered form
  false **or** a proof that `ir_refines` does not need it.
- **Required finding**: is `dialect_deterministic` true as registered, true in a weaker
  view-level form, or false? Third time this hole has been cited as a prerequisite — settle it.