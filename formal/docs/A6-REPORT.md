# A6 / ROW.TP — worker report (transcriptParser, t/A6)

**Branch** `t/A6`, rebased onto **`origin/formal/baseline` = `79f2de3`** (the previous base was
`2c6789b`). Worktree `/Users/julian/midfall-f`. **HEAD** is this commit
(`git log -1`). No push. `formal/baseline` and `/Users/julian/midfall` untouched; no
frozen/vendor/QVM/Quotient edit.

## TP leaves: 5 left (was 6); ROW.TP.6 is now PROVED

`Rows.lean` is still untouched, so the ROOT cones are unchanged: `lowering_correct` **11**,
`lowering_sound` **5**, both `assert_axioms` `ok (4 named, 0 native)`.
`lean_grep.py sorry TranscriptRows.lean` prints **5** lines (2142, 2157, 2172, 2185, 2217) — the
five named leaves below. Register delta vs the previous A6 head: **−1 non-ROOT sorry**.
`gen_sorry.sh` was not run (zero-sorry precondition not met; worker rule W9/DG.2).

## What `tp_events_slots` (ROW.TP.6) now rests on — all PROVED

| declaration | line | role |
|---|---|---|
| `tp_events_slots` | 1440 | the leaf; sorry-free |
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

## SIM.10: obligation 2 IS PROVED; obligation 1 remains

All PROVED in `TranscriptRows.lean` (module green, no new holes):

| declaration | role |
|---|---|
| `wireOf` / `wireOf_cons` / `wireOf_size` | the `Msg.fr` arm of `msgWire` as a byte fold; `(wireOf qs).size = 32 * qs.length` |
| `bytesTake_whole` | reading the whole buffer is the identity |
| `squeeze_pos` / `squeeze_buffer` / `squeezeChallenge_pos` / `squeezeChallenge_buffer` | `Transcript.squeeze` rewrites only `state`; a challenge moves neither cursor nor buffer |
| `tmSqueezeChallenge_run_eq` / `tmSqueezeChallenge_run_spec` / `tmSqueezeChallenge_run` | the squeeze's exact run, and its success + frame facts |
| `tmRead_run_eq` / `tmRead_run_ok` | `tmRead.run` is `Transcript.read`; a present, decodable repr succeeds and advances `pos` by `width` |
| `hashableFr_readRepr?` / `hashableG1_readRepr?` / `hashableFr_width` / `hashableG1_width` | projection peels, stated at a variable byte string so `frToRepr` is never reduced |
| `tmRead_list_run` | the scalar run: `idx.mapM (tmRead hashableFr)` over `idx.length = qs.length` reads `wireOf qs`, advances by `32 * qs.length`, leaves the buffer |
| `tmRead_g1_run` | one G1 read from `pref ++ toCompressed Q ++ rest` |
| **`pcsReads_run_ok`** | **SIM.10 obligation 2**: from `t.buffer = pref ++ toCompressed fCom ++ wireOf qs ++ toCompressed pi`, `t.pos = pref.size`, `qs.length = nSets`, encoder-first and compressed-width laws, `p ≤ 2^256`, the `pcsReads.run` succeeds with `r.fCom = fCom`, `r.pi = pi`, `r.qEvalsOnX3 = qs`, `t'.pos = t.buffer.size`, `t'.buffer = t.buffer` |
| `assertEmpty_run_ok` | `assertEmpty` succeeds when `pos = buffer.size` |
| **`snapshotXcriptRun_of_algebra`** | **obligation 3, composed**: algebra success on that exact tail + the `pcsReads` hypotheses gives `∃ x, snapshotXcriptRun ... = .ok x` |
| `decodeSlots_map_slot` | the decoder's messages have exactly the layout's slots (`ms.map Msg.slot = slots`) |

The `pcsReads_run_ok` proof is the assembly the earlier report outlined: the two G1 reads
(`tmRead_g1_run`), the q-eval fold (`tmRead_list_run` over `List.range nSets`), the three
squeezes (`tmSqueezeChallenge_run_spec`), the `StateT.run_bind` chain, and the final cursor
arithmetic `pref.size + 48 + 32*nSets + 48 = t.buffer.size` using `wireOf_size` and
`frToRepr_size`. It also returns buffer preservation, which is what `assertEmpty` consumes.

## Parser-side read-schedule progress (D1's `prepare_logSlots` is NOT yet landed)

D1 (`t/D1`, merged at `702aebd`/`79f2de3`) has proved the reduction
`decodeRust_slots_eq_logWidths` and itemised the residual `prepare_logSlots`; it has NOT landed the
width sequence. I did not duplicate it. The parser-side facts that do not depend on it are now
PROVED in `TranscriptRows.lean`:

| declaration | role |
|---|---|
| `wireMsgs` / `wireMsgs_eq_fold` / `wireMsgs_cons` / `wireMsgs_size` | the `msgWire` fold `transcriptOf` runs, with its byte length as the sum of the per-message wire lengths |
| `transcriptOf_buffer` | `(transcriptOf E H ms).buffer = wireMsgs E ms` and `.pos = 0` |
| `tmReadMsg` / `tmRead_msg_run` | one mixed message read from the wired tail: succeeds, advances by `msgWire`'s length, leaves the buffer |
| **`tmRead_msgs_run`** | **the message-wire engine**: reading a whole `List (Msg …)` one message at a time from `pref ++ wireMsgs E ms ++ rest` succeeds, consumes the list in order, advances by the sum of wire lengths, and leaves the buffer |
| **`decodeCalldata_slots`** | **the `Decoded` linkage**: `Decoded R cd ms instW inst` gives `ms.map Msg.slot = plan.slots` (via `decodeSlots_map_slot`) |

These are exactly the buffer-tail/decode halves of `snapshotAlgebraRun_total`. The missing half is
the monadic schedule walk itself: `parseTrace`/`readAlgebra` must be shown to *call the reads in
the order of `ms`*. That is the parser-side counterpart of D1's residual, and its exact shared
statement (for D1's common module, not yet in the tree) is:

```
/-- D1's `prepare_logSlots`, the width sequence of a successful `Verifier.prepare` run. -/
theorem prepare_logSlots … (hrun : (prepare …).run t0 = .ok (d, t)) :
  (t.log.toList.drop t0.log.size).map Prod.fst =
    ((RepackedProofLayoutPlan.fromProofLayout L).slots.map WireSlot.slotWidth)
```

with the A6-side strengthening needed for totality (the `prepare_logSlots` analogue that also
tracks success and the cursor):

```
theorem snapshotAlgebraRun_wire … (hslots : ms.map Msg.slot = plan.slots) :
  ∃ s2 t2, snapshotAlgebraRun R.E H R.vk inst ms = .ok (s2, t2) ∧
    t2.buffer = wireMsgs R.E ms ∧ t2.pos = (wireMsgs R.E ms).size
```

`snapshotAlgebraRun_wire` is strictly stronger than the width half (it includes the run and the
buffer tail), which is why `snapshotAlgebraRun_total` cannot be derived from `prepare_logSlots`
alone; D1 and A6 need the same schedule walk, tracked once at widths and once at consumption.

## SIM.10 obligation 1 — exact residual (NOT landed)

The only missing input to `snapshotXcriptRun_of_algebra` is `snapshotAlgebraRun` totality on
`transcriptOf E H ms` with the tail facts. Stated exactly (this is the residual goal, not a
declaration in the tree because it is not yet proved):

```
theorem snapshotAlgebraRun_total
    (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (hdec : Decoded R cd ms instW inst) :
    ∃ (s2 : SnapAlgebra p G₁) (t2 : Transcript) (pref : Bytes) (fCom pi : G₁)
      (qs : List (Fr p)),
      snapshotAlgebraRun R.E H R.vk inst ms = .ok (s2, t2) ∧
      t2.buffer = pref ++ R.E.g1.toCompressed fCom ++ wireOf qs ++
        R.E.g1.toCompressed pi ∧
      t2.pos = pref.size ∧ qs.length = R.nSets
```

With it, `xcript_total` is immediate: `hR.env.modulus` gives `p = frModulusConstant`
(`< 2^256`), `hcodec.compressedEncoderFirst`/`.compressedWidth` supply `henc`/`hwidth`, and
`snapshotXcriptRun_of_algebra` returns the witness. `tp_agrees` then only needs the
`Inv .transcript` assembly (`XcriptSlots` + `MirrorAt` + `BaseInv`), which is ROW.TP.8's own
content.

What `snapshotAlgebraRun_total` still needs, in house vocabulary:

1. `parseTrace`/`readAlgebra` READ-SCHEDULE totality: the `tmReadN`/`tmRead` calls of
   `parseTrace` (advice phases, logup multiplicities and commitments, permutation products,
   trashcans) and of `readAlgebra` (the commitment read, instance queries, evals, qEvals, pi)
   must succeed on `transcriptOf E H ms`. This is the byte-consumption analogue of
   `tp_events_slots`: `decodeSlots_map_slot` gives `ms.map Msg.slot = plan.slots`, and
   `tp_events_slots` gives `plan.slots = R.tpEvents.filterMap TEv.slot?`; the remaining work is
   the monadic walk over the ~20 parser steps and `readAlgebra`, matching each loop's counts to
   `tp_planFacts` (`tp_fromProtocol`, `userPhasesOf_advice`,
   `fromConstraintSystem_phase_lengths`).
2. The `scatterIndexed` arms are already total at this profile (`committedShape` nonempty,
   the filtered indices in range), as recorded before.
3. `qs.length = R.nSets` and the tail split follow from the `readAlgebra` q-eval count; the
   parser's `nSets` is `R.plan.proofLayout.qEvals.itemCount`.

This is the SAME project-level refinement the D1 lane names: `gap_readScheduleAgrees`
(`Midfall/LoweringV3/EndToEnd.lean:674-685`) records that no theorem relates the WIDTH SEQUENCE
of `Verifier.prepare` to the protocol plan, and that the smallest true bridge is
`prepare_logSlots`. The D1 lane has now proved the reduction half
`decodeRust_slots_eq_logWidths` (`EndToEnd.lean:650`: `ms.map Msg.slot` IS the log width list of a
successful run). `decodeSlots_map_slot` here is the calldata-side slot shape; the parser-side
width list of `snapshotAlgebraRun` — `prepare_logSlots`'s analogue — is NOT in the tree, and
`snapshotAlgebraRun_total` needs both that width list and the existence of the run. This is why
`xcript_total` is reported rather than sorried: its residual is a registered cross-lane blocker,
not an A6 omission, and stating it as a `sorry` would grow the register.

The existing wire toolbox the user pointed at — `msgWire` (`Native.lean:164`), the
`mapM`/wire roundtrip (`list_mapM_roundtrip_snd`, `TranscriptLog.lean:1603`) and the recorded
fold (`recorded_fold_of_mapM`, `TranscriptLog.lean:1686`) — is what the parser walk should
consume; `wireOf` here is exactly `msgWire`'s `Msg.fr` arm, and `tmRead_list_run` is the
buffer-tail form of that fold.

## ROW.TP.3's call resolution

`commonG1_lookup` (line 523) is PROVED by `rfl`: `R.scope` resolves
`common_uncompressed_g1` to the emitted helper with `params = ["buf_len", "cptr"]` and
`rets = ["ret"]`. This is the lookup both the helper summary and the walk-loop body start from.
The helper body in `R.scope` is the INLINED body (the const table substitutes `BLS_P_HI` /
`BLS_P_MINUS_ONE_LO`), so the summary's range-check bridge is over literals.

## SIM.10 `xcript_total` — reduced to obligation 1

`pcsReads`/`assertEmpty` are PROVED (above). The composition
`snapshotXcriptRun_of_algebra` turns any `snapshotAlgebraRun` success with the exact wire tail into
`∃ x, snapshotXcriptRun ... = .ok x`; the residual is `snapshotAlgebraRun_total` stated in the
SIM.10 section. Nothing is sorried for it: the file's five holes are still the five SEM/ALG
leaves below.

## The five remaining leaves — all blocked by an UNISSUED card

1. **`g1walk_loop_sem`** (2123). Needs **ROW.TP.3's `common_uncompressed_g1` summary** (QUEUE 95h:
   "ISSUED BY ROW.TP (step 1): no card until ROW.TP merges") **and T3.5** (QUEUE row 78, "after
   T3.1", not run). Exact missing fact: an `EvalExpr` contract for the call
   `common_uncompressed_g1(buf_len, proof_cptr)` over the 13-statement helper body
   (`GenAst.emitCommonUncompressedG1`, `GenAst.lean:358`): from `st.env.calldata = cd.data.toList`
   and the two bound words, every run either (a) halts reverted (a `fail` arm), or (b) returns
   `buf_len + 128` with `bytesAt st' buf_len 128 = cdSlice cd proof_cptr 128`,
   `g1WordsOk cd proof_cptr = true`, env/halted preserved and memory equal outside the 128-byte
   window. The loop then needs the `cdSlice` append/`bytesAt` layer (T3.5) to carry the window over
   `j` frames. Neither is in the tree.
2. **`tp_computes`** (2150). Needs ROW.TP.3/4/5/2 (`common_word`, `transcript_init`, `squeeze_to`
   summaries; the three scalar loops; the `tpEvents` fold; the walk loop) — unissued. ROW.TP.6
   (this file) is now discharged and is no longer a blocker.
3. **`tp_agrees`** (2167). Needs **SIM.10 `xcript_total`**, still absent (`grep -rn xcript_total
   formal/Midfall` prints only `WideningStages.lean` prose). ROW.TP.6 is now discharged; the
   `MirrorAt` half of `TpPost` maps to `StageInv`'s `Mirror .transcript` by `rfl`.
4. **`tp_poison`** (2180). Needs ROW.TP.4's three scalar loops and ROW.TP.2's walk loops
   (end-normally/revert lemmas whose preconditions do not read the loops' computed values) —
   unissued.
5. **`tp_blockProgS`** (2212). Needs every child above plus the walk-loop normal arm.

No row/bundle/root/`ValidV3` hypothesis was added; no false/vacuous statement was found.

## Gates (printed)

- `lake build`: `Build completed successfully (5841 jobs)`, exit 0.
- `bash scripts/verify.sh --quick`: `verify.sh: ok (--quick)`, exit 0;
  `cone_sorries lowering_correct: 11`, `lowering_sound: 5`; both `assert_axioms … ok (4 named, 0 native)`.
- `python3 scripts/check_orphans.py`: `ok: all 231 modules are reachable from Midfall.lean`.
- `python3 scripts/lean_grep.py sorry Midfall/LoweringV3/TranscriptRows.lean`: five lines, the five
  named leaves.
- KAT: not run (claimed neither way).
