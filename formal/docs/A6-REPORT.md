# A6 / ROW.TP — worker report (transcriptParser, t/A6)

**Branch** `t/A6`, rebased onto **`origin/formal/baseline` = `5dbdd94`** (13 new baseline commits;
the previous base was `8916dc0`). Worktree `/Users/julian/midfall-f`. **HEAD** is this commit
(`git log -1`). No push. `formal/baseline` and `/Users/julian/midfall` untouched; no
frozen/vendor/QVM/Quotient edit.

## TP leaves: 5 left (was 6); ROW.TP.6 is now PROVED

`Rows.lean` is still untouched, so the ROOT cones are unchanged: `lowering_correct` **11**,
`lowering_sound` **5**, both `assert_axioms` `ok (4 named, 0 native)`.
`lean_grep.py sorry TranscriptRows.lean` prints **5** lines (1572, 1587, 1602, 1615, 1647) — the
five named leaves below. Register delta vs the previous A6 head: **−1 non-ROOT sorry**.
`gen_sorry.sh` was not run (zero-sorry precondition not met; worker rule W9/DG.2).

## What `tp_events_slots` (ROW.TP.6) now rests on — all PROVED

| declaration | line | role |
|---|---|---|
| `tp_events_slots` | 1417 | the leaf; sorry-free |
| `tp_planFacts` | 706 | PG-PARSER bridge: plan meta/layout are the generator's, model parser facts are computed from them |
| `tp_fromProtocol` / `TpLayoutFacts` | 946 / 916 | every section's count, width, byte length |
| `userPhasesOf_advice` | 1098 | the phase table index for index |
| `fromConstraintSystem_phase_lengths` | 1116 | the two `remapping` lists have equal length (the structural inversion: five `match_ok_iff` peels, then `dsimp only []` zeta-reduces the record's `have` chain, then two `split`/`cases` rounds) |
| `ConstraintSystemMeta.new_phase_lengths`, `new_numLookups`, `new_protocol_fields` | 1134–1263 | the meta-level projections |
| `remapping_nums_length`, `bumpAt_length`, `foldlM_bumpAt_length` | 790–872 | `remapping`'s read-index vector has length `numPhase` |
| `takeCommitmentSection_shape`, `foldlM_take_length`, `foldlM_lookups_length`, `foldlM_lookups_accOne` | 800–915 | the `fromProtocol` section/fold facts |
| `tpEvents_filterMap_eq` | 1373 | the schedule's filtered slot list, segment by segment |
| `flatMap_advice_replicate`, `flatMap_lookups_byteLen`, `flatMap_replicate_eq`, `sumNat_filter_ne_zero`, `sumNat_trash_if`, `sumNat_cons_guard`, `tp_guard_replicate*` | 1146–1360 | the `slots` sum algebra |

Still proved from before: `inline_g1WalkLoop` (ROW.TP.1), `tp_slice`, `tp_blockSim` (cone exactly
`tp_agrees`, `tp_computes`, `tp_poison`), the W12 falsifiers. Everything is on
`[propext, Classical.choice, Quot.sound]`; no `native_decide`, no heartbeat/recursion raise.

## The five remaining leaves — all blocked by an UNISSUED card

1. **`g1walk_loop_sem`** (1553). Needs **ROW.TP.3's `common_uncompressed_g1` summary** (QUEUE 95h:
   "ISSUED BY ROW.TP (step 1): no card until ROW.TP merges") **and T3.5** (QUEUE row 78, "after
   T3.1", not run). Exact missing fact: an `EvalExpr` contract for the call
   `common_uncompressed_g1(buf_len, proof_cptr)` over the 13-statement helper body
   (`GenAst.emitCommonUncompressedG1`, `GenAst.lean:358`): from `st.env.calldata = cd.data.toList`
   and the two bound words, every run either (a) halts reverted (a `fail` arm), or (b) returns
   `buf_len + 128` with `bytesAt st' buf_len 128 = cdSlice cd proof_cptr 128`,
   `g1WordsOk cd proof_cptr = true`, env/halted preserved and memory equal outside the 128-byte
   window. The loop then needs the `cdSlice` append/`bytesAt` layer (T3.5) to carry the window over
   `j` frames. Neither is in the tree.
2. **`tp_computes`** (1580). Needs ROW.TP.3/4/5/2 (`common_word`, `transcript_init`, `squeeze_to`
   summaries; the three scalar loops; the `tpEvents` fold; the walk loop) — unissued. ROW.TP.6
   (this file) is now discharged and is no longer a blocker.
3. **`tp_agrees`** (1597). Needs **SIM.10 `xcript_total`**, still absent (`grep -rn xcript_total
   formal/Midfall` prints only `WideningStages.lean` prose). ROW.TP.6 is now discharged; the
   `MirrorAt` half of `TpPost` maps to `StageInv`'s `Mirror .transcript` by `rfl`.
4. **`tp_poison`** (1610). Needs ROW.TP.4's three scalar loops and ROW.TP.2's walk loops
   (end-normally/revert lemmas whose preconditions do not read the loops' computed values) —
   unissued.
5. **`tp_blockProgS`** (1642). Needs every child above plus the walk-loop normal arm.

No row/bundle/root/`ValidV3` hypothesis was added; no false/vacuous statement was found.

## Gates (printed)

- `lake build`: `Build completed successfully (5316 jobs)`, exit 0.
- `bash scripts/verify.sh --quick`: `verify.sh: ok (--quick)`, exit 0;
  `cone_sorries lowering_correct: 11`, `lowering_sound: 5`; both `assert_axioms … ok (4 named, 0 native)`.
- `python3 scripts/check_orphans.py`: `ok: all 226 modules are reachable from Midfall.lean`.
- `python3 scripts/lean_grep.py sorry Midfall/LoweringV3/TranscriptRows.lean`: five lines, the five
  named leaves.
- KAT: not run (claimed neither way).
