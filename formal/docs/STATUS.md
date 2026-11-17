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

**THE GOAL CHANGED ON 2026-11-17 (D-P71, D-P72; `design.md`).** The deliverable is the generator
theorem `lowering_correct (R) (product) (hR : ValidV3 R) : LoweringEquivalenceV3 R product` — for
EVERY render — and its widening to the IVC verifier, `lowering_correctW` (accumulator mode with
the batched final pairing; external evaluator). **No block row, totality lemma or headline is
proved at a fixture; fixtures are tests** (F1 Poseidon; F2 the IVC decider circuit). Card PL.G has
run: PLAN-V3 §0, §2.2, §5 M5–M9, §6, §7, §9, §10.3, the cards, the V3 table and the goal prompt
are the restated text. Lines above that speak of `lowering_equivalence_poseidon` as the headline
describe the tree before D-P71; card PL.1 still deletes that theorem.

**What changed for the queue.**
- M0–M4 cards are unchanged (needed on either route).
- M5–M8: T3.4 DROPPED; T3.6 REPLACED BY GEN.1; T3.3 and T3.11 are tests only. T3.9, T3.10, SIM.6,
  HLP.1, TOT.1, ROW.TP, ROW.Q, ROW.PCS, ROW.FP, PL.H, PL.E, DG.4, DG.9 are RESTATED in place for
  every render; their children are area GEN-ROWS of `PLAN-V3-cards.md`. New: T3.1b (lands
  `wp_run`), GEN.0 (lands parametric execution; measured in the design pass: 7 leaves, kernel
  0.24 s), GEN.1, GEN.3 (loop rule, proved in the design pass), GEN.4, GEN.5, RECON.1b, RECON.3.
  T3.7 is dropped; T3.0 is optional.
- M9 (D-P72): area WID, 20 cards. WID.2 depends on nothing. M10 (D-P73): area CERT, 10 cards.
- Evidence: `docs/plans/V3-evidence/lean/statements/GeneratorTheorem.lean` (the headline; its
  falsifier is proved), `lean/soundness/GeneratorRows.lean` (40 named open row obligations; the
  composition is proved), `lean/widening/*.lean`. `bash docs/plans/V3-evidence/check.sh` has two
  new areas' worth of files (`soundness` grew; `widening` is new).
- **A missed threshold of PLAN-V3 §5 M5 (points P, B, L, C, D) goes to the human. Per-fixture
  rows are not a fallback.**

**D-P73 (signed 2026-11-17): the generator itself is certified.** The final theorem is
`generator_correct`: hypotheses on the generator's input only (`Generates gi o`, `SupportedInput
gi`); `lowering_correct` is its main lemma. Milestone M10, area CERT (10 cards; evidence
`lean/object/GeneratorCertified.lean`, 33 named lemmas). It is not provable before the tree
emitter is complete: at F1 the port's text and the emitted tree disagree today (6,761 tokens
against 14,054). CERT.1 probes two suspect lemmas first; a refuted one goes to the human.

**Waiting on human:** paste the goal prompt (`v2-bundle/docs/GOAL-PROMPT.md`, everything below its
line) as the orchestrator's `/goal`: **the prompt changed with D-P71 and D-P72.** D-P72 clause 9
asks the generator's owner for a free-memory guard in the evaluator template.

## ⚠ WAITING ON HUMAN — a REFUTED node is in the cone, and DG.6 cannot clear it

**Found while checking DG.6's preconditions at `9a3d619` (not by briefing it blindly).**

- `theorem poseidon_valid : poseidonRender.Valid := by sorry` is **still in the tree**
  (`Instances/PoseidonV2.lean:190`).
- Its **negation is proved**: `poseidonRender_notValid : ¬ poseidonRender.Valid`
  (`PoseidonValid.lean:468`).
- **DG.2's own gate reports it**: `ok: 58 sorried declarations, 9 in the headline cone, 1 REFUTED`.

**This is a live W13 violation.** W13 requires a sorry whose negation is proved to be **deleted in the
same commit as the refutation** — the refutation landed two rounds ago (C.4) and the sorry is still
there. And W13's other clause: **a cone containing a refuted leaf is reported as UNREACHABLE, never as
a number.** We are reporting `9`.

**Why DG.6 cannot fix it.** DG.6's NEEDS names *"the ticket (statements area) that deletes
`poseidon_valid` or turns `Valid` into a hypothesis"* — **that ticket has not run and I cannot identify
it from the V3 table.** DG.6's step 1 is literally `After poseidon_valid is gone, add…`. Its `after`
column says only `DG.2`, which is merged, so **the table says READY while the NEEDS say otherwise.**
**The tool itself already exists** (`Done.lean:410`, `#assert_no_refuted_sorry`), so DG.6 is one line —
but only once the statements ticket lands.

**Three questions:**
1. **Which V3 card deletes or re-hypotheses `poseidon_valid`?** Is it ST.4 (D-P45's `HypothesesInhabited`
   work) or an M3 statements card? The table does not say, and DG.6 depends on it.
2. **Under D-P71, `poseidon_valid` is a proof at a fixture** — `poseidonRender.Valid` names a fixture.
   **Should it simply be deleted as V2 residue rather than repaired?** Under the restatement the
   theorem is `lowering_correct` over every render with `ValidV3`; a fixture-level `Valid` sorry may
   have no consumer at all in V3.
3. **Should the report print UNREACHABLE rather than 9** while a refuted leaf sits in the cone, per
   W13's final clause? If so that is a DG.2/DG.6 gate change, and I would rather you say so than have
   me reinterpret my own gate.

**Until answered I am starting no PROOF or SKELETON card** (the loop's rule for an open question of
this kind). INFRA cards that do not depend on it — **DG.7** (CI that runs and can pass, after DG.0+DG.2,
both merged) and **DG.8** (STATUS generated from the report, after DG.2) — are READY and are the next
things I will brief.
