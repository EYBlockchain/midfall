# A6 / ROW.TP — worker report (transcriptParser, t/A6)

**Branch** `t/A6`, **base** `formal/baseline` @ `cc5b5ad`, **worktree** `/Users/julian/midfall-f`.
**HEAD** is this commit: `git log -1` in `/Users/julian/midfall-f`; the Lean work is `a3f7a06`,
`e0bc81f`, `b9d1568` and `d2823ca`. No push. `formal/baseline` and `/Users/julian/midfall`
untouched.

## What landed

New module `formal/Midfall/LoweringV3/TranscriptRows.lean` (801 lines, final), imported from
`formal/Midfall.lean` (line 203; `check_orphans.py`: `ok: all 224 modules are reachable`).

PROVED:

| declaration | lines | time (measured) |
|---|---|---|
| `tp_slice` — the parser slice is the inlined `emitTranscriptParserAt` | 184–193 | `rfl` (< 0.2 s) |
| `shadowed_append_right` / `shadowed_append_self` | 195–219 | < 0.2 s each |
| `tpVars_*` (5 concrete `tpExprVars` shapes) | 227–241 | < 0.1 s each |
| `tp_inExpr_eq_of_shadowed`, `tp_inExpr_args_eq` (mutual) | 246–282 | < 0.5 s |
| `inlineStmtStep_{assign,expr,let}_shadowed`, `inlineScan_single` | 287–329 | < 0.5 s |
| **`inline_g1WalkLoop` (ROW.TP.1)** — statement verbatim, now sorry-free | 331–491 (161) | one `simp` reported at **4.43 s**; declaration < 10 s |
| **`tp_blockSim` (ROW.TP row glue)** — the evidence's 12-line proof, verbatim | 576–593 | < 0.2 s |
| 2 W12 witnesses + 8 W12 falsifiers | 608–771 | `wp_run` in the ROW.TP.10 falsifier reported at **4.38 s**; rest < 1 s |
| `#assert_axioms inline_g1WalkLoop` traversal | — | **3.91 s** |

Module fresh build measured at **10 s** (`✔ [2151/2151] Built Midfall.LoweringV3.TranscriptRows (10s)`).
Plain `lake build` does not print per-declaration times; the figures above are Lean's `--profile`
and `set_option profiler true` prints (only >200 ms events are printed).

Every proved declaration is on `[propext, Classical.choice, Quot.sound]`, no `native_decide`, no
`maxHeartbeats`/`maxRecDepth` raise. `#assert_axioms` prints in the build log are `ok (n named, 0
native)`.

## The six remaining named leaves (statements ported verbatim, V3 reading)

All six are `sorry`; each has a PROVED W12 witness/falsifier. `#cone_sorries tp_blockSim` prints
exactly `tp_agrees`, `tp_computes`, `tp_poison` — i.e. the row glue cites its leaves.

1. `tp_events_slots` (493): `R.tpEvents.filterMap TEv.slot? = (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots`.
   **Exact dependency: PG-PARSER.** Nothing in `ValidV3` equates the MODEL's parser facts
   (`R.model.userPhases`, `.lookupHPlusAcc`, the three meta counts, `truncatedChallenges`) with
   `R.plan.proofLayout`; the only join is `generateVerifierFromPlan`, which no landed lemma unfolds
   at this shape. The card's instruction (stop, state the lemma, do not add a hypothesis) is
   followed: the statement is landed, the F1 witness is
   `GeneratorRowsWitness.lean:124/129`, and the generic W12 pair is
   `tp_events_slots_witness_nonempty` / `tp_events_slots_falsifier_not_every_event_reads_a_slot`.
2. `g1walk_loop_sem` (506): statement verbatim. **Exact dependency: ROW.TP.3's
   `common_uncompressed_g1` helper summary** (QUEUE 95h, "ISSUED BY ROW.TP: no card until ROW.TP
   merges") **and T3.5's `cdSlice` arithmetic.** Neither exists in the tree.
3. `tp_computes` (533): `StageInv .vk` → every run reverts or exits normally in `TpPost`.
   **Exact dependency: ROW.TP.3 (four helper summaries), ROW.TP.4 (instance run / evals spill /
   q_evals run), ROW.TP.5 (the `tpEvents` fold), ROW.TP.2 and ROW.TP.6** — all unissued
   (QUEUE 95h/95i/95j; 95b/95c).
4. `tp_agrees` (550): `TpPost → StageInv .transcript`. **Exact dependency: SIM.10's `xcript_total`,
   which is NOT IN THE TREE** (`grep -rn xcript_total formal/Midfall` prints only
   `WideningStages.lean` prose), plus `tp_events_slots`' `MirrorAt` half. The card's own VERIFY
   FIRST is "SIM.10 closed"; it is not.
5. `tp_poison` (563): `Poisoned → every run reverts`. **Exact dependency: ROW.TP.4's three scalar
   loops and ROW.TP.2's walk loops** (their preconditions do not read the loops' computed values),
   both unissued. No HLP.1 / A5 dependency was hit; A5 is untouched.
6. `tp_blockProgS` (595): ROW.TP.10, statement verbatim. **Exact dependency: every child above plus
   the existence half of the walk loops.**

No false/vacuous statement was found; no counterexample was needed. The ported `tp_events_slots` is
the one *unproved premise gap* (PG-PARSER), not a refuted statement.

## Movement

**None.** `Rows.lean`'s tp `sorry`s are untouched, so:

- `verify.sh --quick`: `ok (--quick)`, exit 0.
- `cone_sorries Midfall.LoweringV3.lowering_correct`: **11** (unchanged; the list still contains
  `Midfall.LoweringV3.tp_blockSim` and `tp_blockProgS`).
- `cone_sorries Midfall.LoweringV3.lowering_sound`: **5** (unchanged).
- `assert_axioms lowering_correct` / `lowering_sound`: `ok (4 named, 0 native)`.
- Register delta: **+6 non-ROOT sorried declarations** (the six leaves above); no ROOT row changed.
  `python3 scripts/lean_grep.py sorry formal/Midfall/LoweringV3/TranscriptRows.lean` prints six
  lines (497, 526, 541, 556, 569, 601). `gen_sorry.sh` was NOT run (worker rule W9/DG.2: the
  orchestrator regenerates).

`tp_blockSim` is proved and ready to wire. The one-line insertion in `Rows.lean` is

```lean
theorem tp_blockSim ... :=
  TranscriptRows.tp_blockSim R product hR hcodec hpc H vkAddr cd g
```

It is deliberately **not** inserted: doing so would replace one bare-sorry root leaf by the three
named leaves today (root cone 11 → 13), and the card's expected movement is none until the leaves
close. When ROW.TP.3/4/5/6 and SIM.10 land, `Rows.lean`'s two tp proofs become applications of
`TranscriptRows.tp_blockSim` / `TranscriptRows.tp_blockProgS`, and root 11 → 9.

## Gates run (printed, not inferred)

- `lake build` (plain, in `formal/`): `Build completed successfully (5314 jobs)`, exit 0.
- `bash scripts/verify.sh --quick`: `verify.sh: ok (--quick)`, exit 0 (log: `/tmp/a6-verify2.log`).
- `python3 scripts/check_orphans.py`: `ok: all 224 modules are reachable from Midfall.lean`.
- `python3 scripts/lean_grep.py sorry Midfall/LoweringV3/TranscriptRows.lean`: 6 lines, all six
  named leaves; ROW.TP.1 and the glue are sorry-free.
- KAT: **not run** (17–28 min, outside this box's budget; claiming neither way).
