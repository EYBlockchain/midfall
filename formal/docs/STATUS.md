# STATUS — overwritten by every ticket (≤ 1 page)

**As of:** `aeba06b` (2026-11-17), after the PLAN-V3 cut-over (card PL.0, tag `formal/v2-cutover`).
Everything before this overwrite is in git history (`git show formal/v2-cutover:formal/docs/STATUS.md`).

**Plan:** `docs/plans/PLAN-V3.md` (D-P60) · cards `docs/plans/PLAN-V3-cards.md` · rules
`docs/plans/EXECUTION-V2.md` + PLAN-V3 §4 (W12–W15) · queue `docs/QUEUE.md` — **the V3 table at its
top is the order**. Decisions D-P60–D-P69 are signed (`design.md`); their recorded conditions still
gate the cards that name them. PLAN-V2 is kept for its rules and its V2 cards. `PLAN.md` points at V3.

**The goal prompt.** `v2-bundle/docs/GOAL-PROMPT.md` is now the **V3 version** (PLAN-V3 §10.3, with the
V2 prompt's loop and rules adjusted). Until the human pastes it, a session running the V2 prompt
reads its references this way:
- "read PLAN-V2 §0–§4" → read **PLAN-V3 §0–§4 and §10** (PLAN-V2's banner says so).
- "DONE means PLAN-V2 §6" → DONE is **PLAN-V3 §6**, the Lean term `Done` (PLAN-V2 §6's note).
- The headline name `lowering_equivalence_poseidon`: card PL.1 deletes today's theorem of that
  name (its cone holds a refuted sorry, W13); M7's PL.H restates it as the V3 headline.
- "FIRST: THE CUT-OVER (T0.1–T0.4)" and "expected D-P43" are V2 history: done (D-V2 is D-P44).
- W6 ("no new gates") does not apply to the gates D-P69 approves (EXECUTION-V2's V3 note).

**Cone report** at `4e18c65`, whose Lean sources are this tip's (`lake build` green, 5240 jobs):
`imports_avoid: ok` · `lowering_equivalence_poseidon: 9` (`blockContracts_of_valid`,
`noWriters_prog`, `prefix_run_clean`, `rejects_of_not_accepts`, `runBody_iff_slices`,
`poseidon_quotient_block`, `poseidon_rejects`, `poseidon_valid`, `Run_worldEq_of_noWriters`) ·
`lowering_equivalence_of_blocks: 5` · `end_to_end: 1` · `fp_finalPairing_contracts: 3` ·
`tr_blockSound: 0` · `tr_blockProgress: 0` · `vk_blockRow: 3` · `vk_slice: 0`.
**The headline cone is UNREACHABLE, not a distance**: `poseidon_valid` is refuted in the tree
(`poseidonRender_notValid`) and `rejects_of_not_accepts` is false as stated (REVIEW-V3 RV-02, RV-10).
Headline axioms (measured at `f2fe99b`): standard three, `sorryAx`, the five D-P36a constants, one
`native_decide` axiom.

**Gates at the tip:** `checks.sh` is **red** at the KAT gate (1397 annotated checks against a pinned
1393; two annotations spelled `-- expect TRUE`). The sorry register is in sync. Card DG.0 fixes it.

**Last outcomes:** F.1 merged `f588ba2` (sequencing glue proved; headline cone 11 → 9). PL.0 done
`aeba06b` (the V3 table; every V2 card marked CONTINUES, MERGED INTO, SUPERSEDED or DONE).

**Next READY, top of the V3 table:** **DG.0** (gates green), then **ST.1** (land the V3 staging module,
no frozen edit), **OBJ.17** (name the target "fixture F1"), **Q0.5** (V2 card, continues).

**In force, applied by condition:** D-P65 — the G1.1–G1.3 batch carries the block-scope repair and
re-hashes `Program.lean` and `Statements.lean` together, or it does not merge G1.2. W14 — no Yul
PROOF card is READY before T3.11's exhibit, whatever the table's status column says.

**Waiting on human:** nothing blocks the queue. Recommended: paste the V3 goal prompt
(`v2-bundle/docs/GOAL-PROMPT.md`, everything below its line) as the orchestrator's `/goal`.
