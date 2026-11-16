# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `b688a85` + cut-over (2026-11-16 19:12Z). v1 frozen at tag **`formal/v1-final`**
(`a680b5c`). All numbers below are from tool output, not from prose.

**Plan:**

- `docs/plans/PLAN-V2.md` (what) and `docs/plans/EXECUTION-V2.md` (how).
- Live queue: `docs/QUEUE.md`.
- v1 is frozen at tag `formal/v1-final`. `docs/PLAN.md` carries a superseded header pointing here.
- Scope decision recorded as **D-P44** in `docs/design.md` (PLAN-V2 expected D-P43; that number was
  already taken by the `armBody` decision at `daf2243`, so D-V2 took the next free one).

**Headline:** `lowering_equivalence_poseidon` — **not yet stated** (C.1). Status word: *not stated*.

**Cone roots** (printed by `verify.sh` after Q0.2):

- `Midfall.LoweringV2.lowering_equivalence_of_blocks`: — (tool not landed)
- `Midfall.LoweringV2.end_to_end`: — (tool not landed)
- Axioms of the roots: —

**Register** (all sorries, incl. legacy; **not a progress measure**): **39**, measured by
`scripts/checks.sh` at `formal/v1-final` — `ok: 39 tracked sorries`.

**KAT totals** (not a progress measure): **1352 checks across 99 files**, both pinned in
`scripts/kat_gate.py`. Gate `checks.sh` exit **0**, all 13 sections green, at the tag.

**In flight:** none. P-ARMCLOSE (v1, brief `daf2243`) was stopped before it finished and left **no
tracked changes** — the working tree was clean, so T0.1 required no `v1/p-runleg-wip` branch.

**Last ticket:** T0.1–T0.4 (cut-over, orchestrator). Outcome: v1 tagged, D-V2 recorded as D-P44,
PLAN.md header pointed at PLAN-V2, V2 docs landed in `formal/docs/`. Cone delta: n/a.

**Next READY:** **Q0.1** (land the three V2 Lean files unchanged). Then Q0.2, Q0.3.

**Waiting on human:** none. D-V2 is pre-approved through the `/goal` prompt.

**Calibration:** none yet. The first point is C.5.

**Blockers** (each with a reproducer: example + error, at a commit): none.
