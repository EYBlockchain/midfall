# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `3235d17` (2026-11-16 20:45Z). v1 frozen at tag `formal/v1-final` (`a680b5c`).
Every number here is from a command the orchestrator ran after the merge.

**Plan:** `docs/plans/PLAN-V2.md` (what) · `docs/plans/EXECUTION-V2.md` (how) · `docs/QUEUE.md`.
Scope decision **D-P44** in `docs/design.md`. `docs/PLAN.md` points at V2.

**Headline:** `lowering_equivalence_poseidon` — **not yet stated** (C.1). Status word: *not stated*.

**Cone roots** — first real numbers, printed by `Midfall/Tools/ConeReport.lean` (Q0.2 baseline):

- `cone_avoids lowering_equivalence_of_blocks: ok (14 modules)` · `cone_sorries …: **1**`
- `cone_avoids end_to_end: ok (14 modules)` · `cone_sorries …: **1**`
- `imports_avoid: ok (14 modules)` — **the V2 closure contains 0 of the 14 retired modules** (was 6).
- Axioms of the roots: not yet printed (Q0.3 wires `verify.sh`).
- Each cone holds exactly one sorried declaration: the root itself. The other four V2 obligations are
  not yet in either cone — they are the parts later cards wire in.

**Register** (not a progress measure): **45** — `ok: 45 tracked sorries`. Zero `UNOWNED` rows.
**KAT totals** (not a progress measure): **1352 across 99 files**, both pinned.
**Modules:** 137 reachable. `checks.sh` exit **0**, 13 sections green.

**Proved and in the tree (not just landed):** `LegacyVacuity` — zero sorries; `not_LoweringCorrect` and
`ir_refines_field_is_false` on `[propext, Classical.choice, Quot.sound]`, `stuck_satisfies_every_post`
on `[propext]`. `ConeSorriesTest.lean` exits 0 with all 8 `#guard_msgs` passing.

**In flight:** none. Next READY: **Q0.3** (freeze the V2 surface; land `verify.sh`, one command that
runs build + cone report + register and prints root axioms).

**Last ticket:** Q0.2 · INFRA · PORT. Outcome **DONE**, squash-merged `3235d17`.
**Cone delta: baseline established (1 and 1).** Files: `Shared.lean` 195 ln + `ConeReport` 29 +
`ConeSorries` 78; `Program.lean`/`Statements.lean` edited to drop 4 retired imports. No v1, frozen or
vendor file touched; no deletions.

**Waiting on human:** none.

**Calibration (sample size 2):** Q0.1 box 1.5 h → ~26 min. Q0.2 box 2 h → ~35 min. Both under box.
Cost driver is the gate, not the Lean: a full `checks.sh` is ~14 min and it re-runs `kat_gate.py`, which
cards also require separately. **Q0.3 should collapse this** by making `verify.sh` the single entry.

**Blockers:** none. Environment quirk recorded: this toolchain rejects a `/-!` module docstring before
the `import` header — use `/-`. Every repo file already does.
