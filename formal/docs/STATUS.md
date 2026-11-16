# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `b8ca493` (2026-11-16 19:55Z). v1 frozen at tag `formal/v1-final` (`a680b5c`).
Numbers below are from tool output the orchestrator ran itself, not from a subagent report.

**Plan:** `docs/plans/PLAN-V2.md` (what) · `docs/plans/EXECUTION-V2.md` (how) · live queue
`docs/QUEUE.md`. Scope decision recorded as **D-P44** in `docs/design.md`. `docs/PLAN.md` carries a
superseded header pointing at V2.

**Headline:** `lowering_equivalence_poseidon` — **not yet stated** (C.1). Status word: *not stated*.

**Cone roots** (cone tool lands in Q0.2, so not yet measurable):

- `Midfall.LoweringV2.lowering_equivalence_of_blocks`: — (stated with `sorry` at Statements.lean:388)
- `Midfall.LoweringV2.end_to_end`: — (stated with `sorry` at Statements.lean:450)
- Axioms of the roots: —

**Register** (not a progress measure): **45** — `ok: 45 tracked sorries`, up from 39 at the tag. The
+6 are the V2 obligations, exactly the six names the card predicted.

**KAT totals** (not a progress measure): **1352 across 99 files**, both pinned. `checks.sh` exit **0**,
13 sections green, 134 modules reachable, measured by the orchestrator after the merge.

**Proved this card (not just landed):** `LegacyVacuity` carries **zero sorries** — `not_LoweringCorrect`
and `ir_refines_field_is_false` on `[propext, Classical.choice, Quot.sound]`, and
`stuck_satisfies_every_post` on `[propext]` alone. **This is the formal basis for retiring v1**, now
kernel-checked inside the tree rather than asserted in a plan.

**In flight:** none. Next READY: **Q0.2** (cut V2 off the retired modules; land the cone tool) and new
**Q0.1b** (one line: give `gen_sorry.sh` an owner case for `Midfall/LoweringV2/*`).

**Last ticket:** Q0.1 · INFRA · KAT. Outcome **DONE**, squash-merged at `b8ca493`. Cone delta: n/a (no
cone tool yet). Files: 874 insertions, 0 deletions, no v1 or frozen file touched.

**Waiting on human:** none.

**Calibration:** none yet — first point is C.5. Note for it: Q0.1's box was 1.5 h and it took ~26 min of
subagent wall, of which ~20 min was two full KAT passes (the card requires `kat_gate.py` once and
`checks.sh` once, and `checks.sh` itself runs `kat_gate.py`). **Sample size 1.**

**Blockers:** none. One false premise in the card, harmless and recorded: it predicted
`check_duplicate_facts.py` would redden on `Render`'s fields; it stayed green, so no gate-narrowing was
needed.
