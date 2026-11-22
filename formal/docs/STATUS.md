# STATUS - midfall

**As of:** `8d22be0` (2026-11-22). **FULL GATE GREEN at `d0bf226`:** `verify.sh: ok (full)`,
EXIT=0, KAT 1648/119, `axiom_sweep: ok`, closure fingerprint 4823 declarations / 526 external
leaves / `bd27cd298a04fc1a`. The later A3/QVM commits are quick-gate green. Current report:
root **11 / sound 5**, register **73 / 11 ROOT**, 0 REFUTED, exhibits **4 / 4**.

## 1. Verified - PROGRESS

    root lowering_correct .... 11 OPEN sorried leaves (q_blockProgS, q_blockSim, block_live,
                               fp_blockProgS, fp_blockSim, lag_blockProgS, lag_blockSim,
                               pcs_blockProgS, pcs_blockSim, tp_blockProgS, tp_blockSim)
    root lowering_sound ...... 5 OPEN sorried leaves (q_blockSim, fp_blockSim, lag_blockSim,
                               pcs_blockSim, tp_blockSim)
    block rows ............... 1 INTEGRATED of 7 (traceReturn); 2 SORRY, 4 NONE
    exhibits ................. 4 PRESENT, 0 MISSING of 4
    ValidV3 at F1 ............ `poseidonRender` REFUTED (data defect); a re-sourced
                               `f1GeneratedRender` has `generated` PROVED; full inhabitant in flight
    root lowering_correctW ... C0 in flight (three CompositionW glue holes)
    root generator_correct ... D2 in flight (certified statement port)
    register ................. 73 rows / 11 ROOT; 0 REFUTED, 1 VACUOUS
    KAT ...................... 1648/119 (full gate at d0bf226; quick since)
    axiom roots .............. standard three + sorryAx, native []

**Pending green branch increments:** A4 `79907b1` (`lag_agrees_lLast_l0`), A5 `5a0e874`
(output-word round trip), A9 `e405fb8` (`eval_add_var_lit`), D1 `73c8e3a`
(`gap_readScheduleAgrees`). They merge as soon as the full gate finishes.
**Merged since the last full gate:** D1's `EndToEnd.lean` (both directions; one remaining
`readScheduleAgrees_of_validV3` projection), A4's `LagrangeAlg` + `lag_agrees_xn` (D-GATE2
exponent), A5's staticcall segment form, A9's scalar-inv store plumbing; QVMHDR `modarith7Form_shift`/`step_shift_modarith7` and the
PAIRWISE fold transport; B1's DG.3 closure pin (`bd27cd298a04fc1a`) + DG.7 CI; C1's F2 IVC bundle;
B5's artifact gate (VK exact, verifier except `BUILD_ID`); A11's `fp_pairing_algebra`,
`fp_stmt_steps`, `fpG2Slots_of_valid` (register 75 -> 73); A5's modexp memory bridge; A9's
`ScalarInv` six-store frame.
**This session (since `e7f3107`):** A3 complete (`vk_blockSim`/`vk_blockProgS`), A4's four
lagrange loops (a/b/c/d/e) proved, A5's `bi_forward_loop` **and `bi_backward_loop`** proved, A9's
both PCS truncation arms and the 32-byte store/read bridge proved, A6's `tp_events_slots` and
`commonG1_lookup` proved, QVM's MODSHIFT block/fold shifts and the four compaction arm-value
lemmas merged, and the B4 refutation/inhabitation split landed. All quick gates green; the full
gate last ran at `d0bf226`.

## 2. In flight (6-agent cap; critical path only)

- **ACTIVE 1 — A5/helpers** (`t/A5`): `bi_forward_loop` and `bi_backward_loop` PROVED;
  `batch_invert_summary` in flight.
- **ACTIVE 2 — A6/transcriptParser** (`t/A6`): SIM.10 `xcript_total` first, then ROW.TP.3/T3.5.
- **ACTIVE 3 — A9/PCS** (`t/A9`): six-store `modexpInvFrame` equality and the `scalar_inv`
  summary.
- **ACTIVE 4 — A11/finalPairing** (`t/A11`): the three groups + `fpG2Slots_of_valid`, then the two
  rows.
- **ACTIVE 5 — A4/lagrange** (`t/A4`): `powVartime_eq_pow` + the Lean `batchInvert` spec +
  `lag_agrees` at the corrected exponent, then T3.9.h.
- **ACTIVE 6 — D1/end-to-end** (`t/D1`): `end_to_end : EndToEndV3 ...` from `lowering_correct`.
- **PAUSED until a slot frees** (in this order): QVMHDR (`go_drop_ok`; the shift is already proved
  at `7225a47`), QVMGREEN (compaction), B1 (DG.3/DG.7 finish), B5 (artifact gate/T3.3), A12
  (per-block liveness), C0 (W glue; re-carded per its finding), D2 (certified generator), B4
  (F1 inhabitant), B3 (codec laws), C1 (F2), B6 (`Done`).
- **B5 (MERGED):** `artifact_gate.sh` and the Rust exporter are in `formal/baseline`; the measured
  VK artifact is byte-identical and the verifier differs only at `BUILD_ID`. Evidence: the VK artifact is byte-identical; the verifier differs only at the
  `BUILD_ID` line. D-B5 pins the VK exactly and the verifier except that named input.
- **C1/F2 (MERGED):** the IVC decider bundle is committed at `514781f` — `Halo2Verifier.sol`
  150,888 B (`c9347fde…`), `Halo2VerifyingKey.sol` 78,333 B (`f7585874…`), evaluator 97,477 B
  (`4086ef35…`), k=19/20, midnight SRS, solc 0.8.30, 279 s. The Lean F2 importer/clause table is
  the remaining C1 work.
- **B1/pinned zone (MERGED):** `gen_closure.sh`, `Closure.manifest` (4823 DECL / 526 leaves /
  `bd27cd298a04fc1a`) and the `checks.sh` gate are in `formal/baseline`; the manifest re-checks green
  after the new V3 modules.
- **QVMHDR (green on branch):** `modarith7Form_shift` + `step_shift_modarith7` proved at `7225a47`
  (D-QVM3's exception was not needed); `go_drop_ok`/`runBlocks` remain.
- **A9 (green on branch):** `bytesToNatBE_readBytes_32`/`fold_byte_lt` at `43da46c`; the six-store
  frame and `scalar_inv` summary remain.
- **A4/lagrange** (`t/A4`): `lag_agrees_xn` and `LagrangeAlg` merged; the exact residual is the
  `lLast`/`l0`/`lBlind`/instance projections plus the documented `hinst` leaf premise; T3.9.h and
  the lag rows then follow.
- **QVMHDR / QVMGREEN**: the MODARITH7 header is PROVED (`7225a47`); both paused, the existing
  QVM agent keeps the `q_blockSim`/`q_blockProgS` lane.
- **A12/totality** (`t/A12`): per-block liveness from the proved vk/tr progress rows; the root
  `block_live` stays the single registered hole until the other five progress rows land.
- **QVM** (`t/MODELF`, `t/TERMFOLD`, other agent): fixed-segment/spill/validator lane.
- **QVM compile-correctness** (`t/QVMIDGREEN`): LIN7/ROW decoder ties, MODSHIFT block/fold shifts,
  four compaction arm-value lemmas merged. `PG_identity_emitterValue`/`compactionValue` remain;
  `compactGo` induction in flight with the header shift as an internal-lemma hypothesis.
- **QVM header** (`t/QVMHDR`): `modarith7Form_shift`; D-QVM3 signs one local heartbeat exception.
- **B1/gates** (`t/B1N`): DG.3 closure manifest/gate at `bd27cd298a04fc1a` (4823 decls / 526
  leaves), DG.7 CI on `formal/baseline` with `ubuntu-latest`, local negative control; OBJ.17/S.10.
- **B4/F1 inhabitant** (`t/B4`): `ValidV3 f1GeneratedRender`; `generated` is proved, the five
  payload point fields are the remaining half.
- **B5/artifacts** (`t/B5`): byte-for-byte `.sol` gates with the local Rust toolchain and the
  downloaded SRS; no hand-edited artifacts.
- **C0/widening glue** (`t/C0`): `rejectsW_of_sims`, `completeAnyGasW_of_progs`,
  `totalW_of_stages` through `blockSimW_iff_blockSim`.
- **C1/F2** (`t/C1N`): IVC fixture export with the SRS, then the widened clause table.
- **D1/end-to-end** (`t/D1`): both directions of `EndToEndV3` proved in `EndToEnd.lean`; the one
  missing premise is `readScheduleAgrees_of_validV3` (`decodeRust` message slots vs the generator's
  repacked layout). This is the current D1 leaf.
- **D2/certified generator** (`t/D2`): CERT.0 statement port/rebase, CERT.1 suspects, CERT.3
  constants, CERT.8 `generate` on the real F1 key.

## 3. Next READY / critical path

The conditional e2e theorem stays: **A4/A5 -> lagrange rows -> A6/A9 -> A11 -> A12 -> A13 -> D1**,
with QVM `q_blockSim`/`q_blockProgS` in parallel. B4/B5/C0/C1/D2 are DONE/non-vacuity and widening
work, not prerequisites of `lowering_correct` itself.

## 4. Resolved this session (was "waiting on human")

1. **DG.3** signed as **D-GATE4**: pin the measured closure (4823 declarations / 526 external
   leaves / `bd27cd298a04fc1a`), not the stale 972. `B1` implements the manifest/gate.
2. **DG.7** unblocked: CI targets `formal/baseline` on `ubuntu-latest`; the negative control is the
   local `gate_negctl.py`, no throwaway branch on `origin`.
3. **B5/C1** unblocked: Rust 1.98.1 is present under `~/.rustup/toolchains`; the SRS assets are
   fetched by `proofs/solidity-verifier/scripts/ensure_srs_assets.sh` into `.srs` (2p19/2p20).
4. **OBJ.17** signed under D-P60: the target is "fixture F1"; F2 is the IVC fixture.
5. **D-QVM3** signed: one local `maxHeartbeats`/`maxRecDepth` exception for the `modarith7Form_shift`
   header only; no global change, no statement change, no `VmReference` edit.
6. **PG-LAGAGREE/T3.9.g** D-GATE2 corrected exponent is being proved by A4.
7. **A4/A5 order inversion** recorded: `batch_invert_summary` is the lagrange prerequisite.

## 5. Last three merges

- `e7f3107` SPILL2 - all six push arms chain across their spill; new window gap recorded
- `127cfe7` A3 - `vk_blockProgS` proved; root 11, register 75/11
- `7349592` PLSEG - builder_segments_total still open; precise handoff
- `d0bf226` SNAPSHOT - `snapshotOf_prepareMsgs` retired; root 12, sound 5, register 76/12
- `8b72779` PG-VKHEADER - frozen `PayloadAgrees.constantsLength` + six header-window equations

## 6. QVM — exact remaining milestones

The QVM rows are `q_blockSim` (`LoweringV3/QuotientRows.lean:236`) and `q_blockProgS` (`:249`).
They consume the following named facts, in dependency order:

1. `qvm_compile_correct_identity` (`Lowering/Qvm.lean:635`) — reduced by
   `qvm_compile_correct_identity_of_two_parts` to
   `PG_identity_emitterValue` (`:5270`) + `PG_identity_compactionValue` (`:5286`);
   `PG_identity_preFold` is PROVED. The PAIRWISE fold transport and
   `modarith7Form_shift`/`step_shift_modarith7` are merged. Remaining: `go_drop_ok`/`go_fuel_mono`/
   `runBlocks` over the full 31-arm step, the `compactGo` scan/walk induction, and the nine
   emitter-value paths (pow5, MODARITH7 shape, limb shape, decomposition residue split, generic
   const/mem/token, add-product macro incl. swapped-operand retry, binary accumulator leaves,
   affine term).
2. `qvm_compile_correct_certifier` (`:693`) — the `certifyItemWalk`/`itemStarts` induction;
   consumes (1).
3. `qvm_compile_correct_program` (`:709`) — the certifier entry point plus the trailing-byte check.
4. `builder_segments_total` (`:996`) — builder-side totality for every segment shape.
5. `qvm_validated_noBoundsFault` — the second per-arm fact (operand/no-bounds; `:1856`, `:2173`).
6. `quotientFold_matches_linearization` (`QvmFold.lean:364`) — Horner reverse, bucket gaps,
   grouped add.
7. `QInterpRefinesSegment` (`QuotientInterp.lean` §11; `QuotientRows.lean:170`) and its
   `qvmLoop` instantiation; the caller supplies D-QVM2's window, table agreement, stack safety and
   start state.
8. The segment/spill/validator lane (existing QVM agent): `QvmSegmentReal`, `QuotientSpill`,
   `QuotientInterp`, `MemoryPairs`, `QvmNoBounds`, fixed-segment window/fit, and `q_blockRow`.
9. Widening QVM arms (C5/C6): external quotient arm (`WID.16`), evaluator body (`WID.17`),
   widened totality (`WID.19`); the M9 evaluator remains trusted via `EvaluatorTrust`.
10. Certified generator QVM streams (D3–D5): the QVM program/certifier/stream facts consumed by
    `generator_correct`.

The first three are the compiler-correctness tranche; (1) is the only one that still has a
mathematical gap (the emitter/compaction values). (2)–(7) are inductions/compositions over
already-landed per-arm facts. (8) is the external agent's lane; (9)–(10) follow the row and
widening integrations.
