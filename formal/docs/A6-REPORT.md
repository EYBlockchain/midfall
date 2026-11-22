# A6 / ROW.TP — worker report (transcriptParser, t/A6)

**Branch** `t/A6`, rebased onto **`origin/formal/baseline` = `8916dc0`** (base `cc5b5ad` before the
rebase). Worktree `/Users/julian/midfall-f`. **HEAD** is this commit (`git log -1`). No push.
`formal/baseline` and `/Users/julian/midfall` untouched; no frozen/vendor/QVM/Quotient edit.

## State: WIP, six named leaves remain (no wiring, no gen_sorry)

`Rows.lean`'s two tp `sorry`s are still untouched, so the ROOT cones are unchanged:
`lowering_correct` **11**, `lowering_sound` **5**, `assert_axioms` both `ok (4 named, 0 native)`.
The file has **6 sorries**, all six original named leaves. `gen_sorry.sh` was **not** run (worker
rule W9/DG.2: it regenerates at merge time; also the "zero sorries" precondition is not met).

Rebase: clean (`git rebase origin/formal/baseline`), then the three Lean builds and
`verify.sh --quick` re-run green. The rebase changed nothing in this file; the new baseline added
`BatchInvert`, `LagrangeRows`/`PcsRows` and the QVM emitter, none of which the tp rows read
(A5 `batch_invert_summary` is NOT a TP dependency; it was not touched).

## What is now PROVED (beyond the previous report)

All added in `formal/Midfall/LoweringV3/TranscriptRows.lean` (1492 lines; `lake build` green):

| declaration | line | what it is |
|---|---|---|
| `tpEvents_filterMap_eq` | 1139 | the schedule's filtered slot list, segment by segment (with one internal hypothesis: accumulator sections are one frame) |
| `tp_planFacts` | 706 | **the PG-PARSER bridge, PROVED from `ValidV3.generated`**: plan meta/layout are the generator's, model parser facts are computed from them, seven meta fields are the protocol's |
| `tp_fromProtocol` | 946 | **every `fromProtocol` section's count, width and byte length** (`TpLayoutFacts`, line 916) |
| `userPhasesOf_advice` | 1098 | **the phase table index for index**: `userPhases[i].adviceBytes = L.advicePhases[i].byteLen` |
| `tp_newFromVk_facts` | 674 | the `newFromVk` peel: `plan.meta_`, `plan.proofLayout = L`, `fromProtocol … = ok L`, seven meta fields conserved |
| `metaDataForVk_conserves` | 523 | the stable-layout loop changes only `numEvals`/`numDummyEvals`/`numPointSets` |
| `remapping_nums_length` | 790 | `ProtocolPlan.remapping`'s read-index vector has length `numPhase` |
| `takeCommitmentSection_shape`, `foldlM_take_length`, `foldlM_lookups_length`, `foldlM_lookups_accOne` | 800–915 | the section/fold facts the `fromProtocol` peel spends |
| `mapM_length`, `listNth_eq_getElem?`, `userPhasesOf_aux` | 1019–1096 | the `userPhasesOf` index proof |
| `replicate_append_replicate_assoc`, `flatMap_lookup_replicate`, `filterMap_squeeze_eq_nil`, `TEv.filterMap_cons_*`, `TEv.slot?_*` | 146–215, 1145–1180 | the list algebra the schedule reduction needs |

Also still proved from the previous session: `inline_g1WalkLoop` (ROW.TP.1), `tp_slice`,
`tp_blockSim` (from the three leaves; `#cone_sorries` still prints exactly `tp_agrees`,
`tp_computes`, `tp_poison`), the shadow/inExpr/`inlineScan_single` inliner lemmas, and all W12
falsifiers. Every proved declaration is on `[propext, Classical.choice, Quot.sound]`; no
`native_decide`, no heartbeat/recursion raise.

## `tp_events_slots` — EXACT remaining goal state

PROVED: `tp_planFacts`, `tp_fromProtocol`, `userPhasesOf_advice`, `tpEvents_filterMap_eq`.
**Remaining, exactly two things:**

1. **The per-phase length equality.** `userPhasesOf meta_ L`'s length is
   `min meta_.numUserAdvices.length meta_.numUserChallenges.length`, and
   `L.advicePhases.length = meta_.protocol.numUserAdvices.length`
   (`TpLayoutFacts.adviceLen`). The two meta lists are both
   `(ProtocolPlan.remapping numPhase _).1` at the same `numPhase` in
   `ProtocolPlan.fromConstraintSystem`, so they have equal length — `remapping_nums_length`
   (line 790) proves the per-call length, but the `fromConstraintSystem` peel that extracts the two
   `remapping` equations is not landed. The obstacle measured: `fromConstraintSystem` is a
   `mutual`-block do-block whose binds are `match` forms, so `except_bind_ok` does not peel them;
   `match_ok_iff` peels the first five, but the final `match plan.validate with …` sits under
   `have`-binders, and `dsimp`/`split` there unfold `ProtocolPlan.validate`'s own `if` chain
   instead of the outer match. The exact goal at that point is
   `p.numUserAdvices.length = p.numUserChallenges.length` with
   `hAdv : ProtocolPlan.remapping numPhase cs.adviceColumnPhaseNats.toList = .ok adv` and
   `hCh : ProtocolPlan.remapping numPhase cs.challengePhaseNats.toList = .ok ch`.
2. **The `slots` sum algebra.** Once (1) holds, the canonical form from
   `tpEvents_filterMap_eq` is `replicate (sum of the group counts) g1 ++ …`; the group-sum
   equalities are:
   - `flatMap (fun ph => replicate (adviceBytes/128) g1) userPhases`
     `= replicate (sumNat (L.advicePhases.map itemCount)) g1`
     `= replicate (sumNat meta_.protocol.numUserAdvices) g1` (uses `userPhasesOf_advice`,
     `adviceByteLen`, `List.mul_div_cancel`);
   - `sumNat (l.filter (· != 0)) = sumNat l` for the three filtered scalar groups;
   - `(if n != 0 then replicate n x else []) = replicate n x`, and the lookup guard is
     irrelevant when `lookupChunks = []` (from `lookupHPlusAccOf = sum + numLookups`);
   - `fromProofLayout L`/`commitmentReadGroups`/`slots` unfold and `omega` closes the sum.

No hypothesis was added to any row, bundle, root or `ValidV3`; the only hypotheses are on the
internal algebra lemmas (`tpEvents_filterMap_eq`'s `hAcc`, which `TpLayoutFacts.lookupsAcc`
supplies at the use site).

## Other leaves — exact blockers (unchanged by the rebase)

| leaf | blocker |
|---|---|
| `g1walk_loop_sem` | ROW.TP.3's `common_uncompressed_g1` helper summary + T3.5 `cdSlice` arithmetic — unissued (QUEUE 95h) |
| `tp_computes` | ROW.TP.3/4/5 + ROW.TP.2/6 — unissued (QUUEUE 95b/95c/95h/95i/95j) |
| `tp_agrees` | SIM.10 `xcript_total` — still not in the tree (`grep -rn xcript_total formal/Midfall` prints only `WideningStages.lean` prose) |
| `tp_poison` | ROW.TP.4 scalar loops + ROW.TP.2 walk loops — unissued |
| `tp_blockProgS` | every child above + the walk-loop normal arm |

## Gates run on the rebased tree (printed, not inferred)

- `lake build`: `Build completed successfully (5316 jobs)`, exit 0.
- `bash scripts/verify.sh --quick`: `verify.sh: ok (--quick)`, exit 0;
  `cone_sorries lowering_correct: 11`, `lowering_sound: 5`; both `assert_axioms … ok (4 named, 0 native)`.
- `python3 scripts/check_orphans.py`: `ok: all 226 modules are reachable from Midfall.lean`.
- `python3 scripts/lean_grep.py sorry Midfall/LoweringV3/TranscriptRows.lean`: six lines
  (1188, 1217, 1232, 1247, 1260, 1292), all six named leaves.
- KAT: not run (claimed neither way).
