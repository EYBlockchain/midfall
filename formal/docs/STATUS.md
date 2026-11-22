# STATUS - midfall

**As of:** `e7f3107` (2026-11-22). **FULL GATE GREEN at `d0bf226`:** `verify.sh: ok (full)`,
EXIT=0, KAT 1648/119, `axiom_sweep: ok`, closure fingerprint 4823 declarations / 526 external
leaves / `bd27cd298a04fc1a`. The later A3/QVM commits are quick-gate green. Current report:
root **11 / sound 5**, register **75 / 11 ROOT**, 0 REFUTED, exhibits **4 / 4**.

## 1. Verified - PROGRESS

    root lowering_correct .... 11 OPEN sorried leaves (q_blockProgS, q_blockSim, block_live,
                               fp_blockProgS, fp_blockSim, lag_blockProgS, lag_blockSim,
                               pcs_blockProgS, pcs_blockSim, tp_blockProgS, tp_blockSim)
    root lowering_sound ...... 5 OPEN sorried leaves (q_blockSim, fp_blockSim, lag_blockSim,
                               pcs_blockSim, tp_blockSim)
    block rows ............... 1 INTEGRATED of 7 (traceReturn); 2 SORRY, 4 NONE
    exhibits ................. 4 PRESENT, 0 MISSING of 4
    ValidV3 at F1 ............ NOT INHABITED; blocking clause = generated (REFUTED at F1);
                               payload point half OPEN (B3)
    root lowering_correctW ... not reported (C0 not started)
    root generator_correct ... not reported (D2 not started)
    register ................. 75 rows / 11 ROOT; 0 REFUTED, 1 VACUOUS
    KAT ...................... 1648/119 (full gate)
    axiom roots .............. standard three + sorryAx, native []

**This session:** root 18 -> 12, sound 8 -> 5, register 85 -> 76, exhibits 2/4 -> 4/4, and the
registered REFUTED row is gone. Proved/landed: `prefix_live`, `runBody_gas_oblivious`,
`Run_worldEq_of_noWriters`, `twoOutcomes_of_exitDiscipline`, `vk_blockSim`, the two Poseidon
exhibits, C1/WID.2 IVC KATs, the D-QVM1 `programFits` fit clause (VKFIT bounds), D-QVM2 retirement,
`gasFree_of_valid` (programOk `GasFree` clause), PG-VKHEADER (`PayloadAgrees.constantsLength`),
and the `snapshotOf_prepareMsgs` retirement.

## 2. In flight

- **A3 COMPLETE** (`127cfe7`): `vk_blockSim` and `vk_blockProgS` both PROVED; the vkLoading pair
  is closed. Root 12 -> 11, register 76/12 -> 75/11.
- **A4/lagrange** (`55862a0`): `LagrangeRows.lean` has **T3.9.a `lag_sq_loop`**, **T3.9.d
  `lag_lblind_loop`** and **T3.9.e `lag_instance_loop`** PROVED, plus the semantic inversions and
  no-halt lemmas for the second-pass body. T3.9.c is one block-state equation + window invariant
  from green; T3.9.b guard-TRUE remains on the semantic route. A5/`batch_invert_summary` is the
  row prerequisite.
- **A5** (`36f034f`): `BatchInvert.lean` vocabulary/forms, **`bi_forward_loop`**, the `wMulmodAt`
  associativity, and the backward-pass algebra (`bwdAll`/`bwdInvVal`/`bwdEnv`) are merged. The
  `bwdMem` store-chain arithmetic and `batch_invert_summary` (memory-level modexp bridge) are in
  flight.
- **A6 transcriptParser** (`t/A6`): `tp_blockSim` glue and `inline_g1WalkLoop` green, six named
  TP leaves remain; the branch is WIP (not merged — it would add six non-ROOT rows).
- **A9 PCS** (`8916dc0`): `decode_exists` and the PCS-local inliner/loop infrastructure merged
  (zero sorries). Confirmed the queue's A8/QVM dependency is schedule-only; block 2 and the
  `scalar_inv` summary are next.
- **A4 continuation** (`midfall-g`, `t/A4`): T3.9.c/e and the b guard-TRUE semantic loop.

**Shortest path to the conditional e2e theorem:** A4/A5 -> A6/A9 -> A11 -> A12 -> A13 -> D1
(`end_to_end`), with QVM `q_blockSim`/`q_blockProgS` in parallel. B4 (ValidV3 at F1), B5 and the
M9/M10 C/D tracks are DONE/non-vacuity work, not prerequisites of `lowering_correct` itself.
- **QVM** (`midfall-c/d`): D-QVM2 executed; `QInterpRefinesSegment` stated; QIDENT/BINDINV/PLSEG/
  SPILL2/CURFACT landed. `q_blockSim`/`q_blockProgS` remain.
- **QVM compile-correctness** (`t/QVMBUILD`): the 26/26 arm table and reduction are merged; then
  `PG_identity_preFold` and `PG_termFold_structure` were PROVED and merged (`25459b2`/`3ff837d`).
  The worker then PROVED `qvm_compile_correct_identity` FALSE as stated (selector gap low byte
  `0x0a` collides with `FOLD_MAIN` in `finalizedIdentitySegment`). **D-GATE3 is signed:** make the
  segment target-aware (strip `FOLD_SELECTOR` by 4 / `FOLD_MAIN` by 1); that repair is in flight.
  It owns `Qvm.lean`/`QvmShift`/`QvmEmit`; the segment/spill/Quotient files stay with the QVM agent.

## 3. Next READY

- **A3** to completion, then **A4/lagrange** (after A3), **A6/transcriptParser** (after A2/A3/A5),
  **A9/PCS** (after A2/A8/B2), **A11/finalPairing**. The QVM row is the other track.

## 4. Waiting on human

1. **DG.3 pinned zone** — sign the current five-root closure (4823 declarations / 526 external
   leaves / `bd27cd298a04fc1a`) before it joins `Frozen.sha256`; the card's 972 is stale.
2. **DG.7 CI** — permission to push/delete a throwaway branch on `origin`; the local
   `gate_negctl.py` is not wired into `checks.sh`.
3. **B5/OBJ.11** — cargo and authorization to re-export the tracked `.sol` fixtures; OBJ.10/
   OBJ.12/T3.3 remain absent.
4. **C1/WID.3/WID.4** — `cargo` is not on PATH and the `midnight-srs-2p19`/`-2p20` assets are
   absent; the exporter is shared with B5/OBJ.11.
5. **QVM** — the fixed-segment proof is the agent's lane; no human item unless the fold output
   predicate needs a ruling.
6. **PG-LAGAGREE / T3.9.g — SIGNED by D-GATE2; A4 correcting the exponent.** Its `hW` uses
   `omegaInv ^ (numNegLagranges - 1)`; `PayloadAgrees.omegaInvToL`, `Protocol.lean:675` and
   `Vk.lean:777-780` all give `omegaInv ^ numNegLagranges`. The rest of the conclusion is
   consistent at the corrected exponent. A4's lag rows cannot close until this statement is
   restated (one exponent, or a general `w0` parameter); do not edit `LagRel` silently.
7. **A4/A5 order inversion.** `batch_invert_summary` (HLP.1.b/c) is a prerequisite of the lagrange
   row, not a successor; the queue lists A5 after A4. The A4 loop tranche is render-free and can
   proceed now (in flight on `t/A4`); the row integration needs A5 first.

**Signed and landed this session:** D-QVM1 (address fit), D-QVM2 (fixed-segment restatement),
D-GATE1 (PG-VKHEADER `constantsLength`, programOk `GasFree`, snapshot retirement).

## 5. Last three merges

- `e7f3107` SPILL2 - all six push arms chain across their spill; new window gap recorded
- `127cfe7` A3 - `vk_blockProgS` proved; root 11, register 75/11
- `7349592` PLSEG - builder_segments_total still open; precise handoff
- `d0bf226` SNAPSHOT - `snapshotOf_prepareMsgs` retired; root 12, sound 5, register 76/12
- `8b72779` PG-VKHEADER - frozen `PayloadAgrees.constantsLength` + six header-window equations
