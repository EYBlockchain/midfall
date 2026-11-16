# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `96910d3` (2026-11-16 21:10Z). v1 frozen at `formal/v1-final` (`a680b5c`).
All numbers from the orchestrator's own full `scripts/verify.sh` run after the merge.

**Plan:** `docs/plans/PLAN-V2.md` · `docs/plans/EXECUTION-V2.md` · queue `docs/QUEUE.md`.
Scope decision **D-P44**. `docs/PLAN.md` points at V2.

**Headline:** `lowering_equivalence_poseidon` — **not yet stated** (C.1). Status word: *not stated*.

**Cone roots** (`Midfall/Tools/ConeReport.lean`, printed by `verify.sh`):
- `imports_avoid: ok (14 modules)`
- `cone_avoids lowering_equivalence_of_blocks: ok` · `cone_sorries …: **1**`
- `cone_avoids end_to_end: ok` · `cone_sorries …: **1**`
- Axioms of the roots: not yet printed by `verify.sh` (Q0.3 recorded the `native_decide` name shape;
  printing root axioms is a later card).
- Each cone holds exactly one sorried declaration: the root itself.

**Frozen surface (Q0.3):** `Program.lean` §1–§4, `Shared.lean`, `Statements.lean` §1–§5 +
`HypothesesInhabited` + `calldataOf` + the two wrapper Props, hashed in
`Midfall/LoweringV2/Frozen.sha256`; `checks.sh` verifies it. **Pin demonstrated**: appending one
character to a copy gives `Statements.lean: FAILED`, exit 1.

**`native_decide` axiom shape (PLAN-V2 §2.5 requirement, now recorded):** on Lean 4.35.0 it adds
**exactly one axiom per declaration**, named `<declName>._native.native_decide.ax_1_1`; no
`Lean.ofReduceBool`, no `propext`, no `Classical.choice`, no `Quot.sound`. Confirmed on three decls.

**Register** (not progress): **45**, zero `UNOWNED`. **KAT** (not progress): 1352 / 99 files, pinned.
**Modules:** 137+ reachable. `verify.sh` exit **0**.

**In flight:** none. Next READY: **Q0.4** (adversarial review of the frozen surface, read-only, 1 h)
and **D.1** (deployment generator inputs as pure terms, GEN, 2.5 h box).

**Last ticket:** Q0.3 · INFRA · KAT. Outcome **DONE**, merged `96910d3`. **Cone delta: none (1 and 1,
unchanged)** — Q0.3 is infrastructure; it changes what can be trusted, not the cone.

**Waiting on human:** none.

**Calibration (sample size 3):** Q0.1 26 min / box 1.5 h; Q0.2 35 min / box 2 h; Q0.3 19 min / box
1.5 h. All under box. Gate time, not Lean, dominates.

**False premises in cards so far: 2** (Q0.1's predicted `check_duplicate_facts` reddening, which did
not happen; Q0.3's `EndToEnd`/`EntryFrameInhabited`, which did not exist). Both caught by VERIFY FIRST
before or during the card; neither caused damage. Below the ask-the-human threshold (2 of 5).

**Blockers:** none. Quirks recorded: `/-!` before `import` is rejected by this toolchain (use `/-`);
`native_decide` adds one named axiom per declaration.
