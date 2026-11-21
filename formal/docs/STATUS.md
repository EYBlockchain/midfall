# STATUS - midfall

**As of:** `76ccfe5` (2026-11-21). Report copied from the last full `verify.sh --quick`; the full
`verify.sh` has not been run on this branch.

## 1. Verified - PROGRESS

    root lowering_correct .... 17 OPEN sorried leaves (snapshotOf_prepareMsgs, q_blockProgS,
                               q_blockSim, block_live, fp_*, gasFree_of_valid, lag_*, pcs_*,
                               runBody_gas_oblivious, tp_*, twoOutcomes_of_exitDiscipline, vk_*)
    root lowering_sound ...... 8 OPEN sorried leaves (the sim rows, prefix_sim, run_split,
                               twoOutcomes_of_exitDiscipline, snapshotOf_prepareMsgs)
    block rows ............... 1 INTEGRATED of 7 (traceReturn); 2 SORRY, 4 NONE
    exhibits ................. 2 PRESENT, 2 MISSING of 4
    ValidV3 at F1 ............ NOT INHABITED; blocking clause = generated (REFUTED at F1);
                               payload point half OPEN (B3)
    root lowering_correctW ... not reported (C0 not started)
    root generator_correct ... not reported (D2 not started)
    register ................. 84 rows / 17 ROOT; 1 REFUTED (poseidon_valid), 1 VACUOUS
    KAT ...................... 1640/118 pinned (last known; not run on this branch)
    frozen axioms ............ 5 named + 159 native_decide; roots are standard three + sorryAx,
                               native []

**PREFIXLIVE (this session):** `Midfall.LoweringV3.prefix_live` is PROVED - cone 0, standard
three - and the root cone moved 18 -> 17 (register 85 -> 84). The proof covers the three prefix
cases: both guards silent (the PROVED `prefix_prog_core`), the ABI guard fires, or the memory guard
fires; the two firing cases are new `Step` constructions, `pfxRevertBody_exists` plus the two head
lemmas. `totalV3_correct`'s cone moved 6 -> 3.

**D-QVM1 (signed 2026-11-21, design.md):** `programOk` now carries `programFits` - the VK payload
windows and, when the model has a `QuotientProgram`, the interpreter's program/const/stack windows
must lie below `2^256`. `MemoryPairs.fit1_of_valid` and `fit2_of_valid` are now theorems of
`ValidV3` (standard three, cone 0), so VKFIT's missing bound is closed. `programFitB` is the Bool
face for the clause table. No `ValidV3` field, bundle or root gained a hypothesis beyond this
conjunct; the headline signature is unchanged.

## 2. In flight / QVM

- **QVM agent (ROW.Q.3, `qinterpRefines_qvmLoop`).** The row is **FALSE as stated**, not merely
  unprovable. `t/BOXd`'s two PROVED refutations are now on `formal/baseline` via ROWFALSE (`0955bac`): (i) `qBadSegment` at base
  `2^256 - 1` wraps `q_pc`/`q_end`, the loop exits normally, the reference errors
  (`qinterpRefines_qvmLoop_row_is_false`); (ii) at an ordinary window the `neg` arm runs with
  `q_has_top = 0` while the reference returns `stackUnderflow`
  (`..._row_is_false_at_a_valid_label`). QLOOP's third axis is table disagreement: only 1 of 31
  arms composes unconditionally (the list head); the other 30 need `selectSwitch` to reject every
  preceding label, so full table agreement is required. The count of arms genuinely tied to the
  reference is still **0** (`armcount`'s 23 is a name intersection only).
- **What the row needs next, in order:** (1) D-QVM1's window fit (landed); (2) full template-table
  agreement (`tcq` = the emitted table, one structure equality); (3) a segment-level stack/operand
  validity hypothesis, the row counterpart of `qvm_validated_noBoundsFault` (the validator rejects
  `[NEG]` at depth 0, so the emitted loop and the reference agree only on validated segments).
  **D-QVM2, signed 2026-11-21, authorizes the fixed-segment restatement** (design.md): the old
  universal row is retired under W13, and the QVM agent states the replacement over a fixed
  `QSegment` with the fit, table agreement, validation, and the prologue's start stack. The fold
  output predicate is the agent's statement to design. The alternative - fixing the `neg`/`pow5`
  emitter arms - is a generated-contract change (Rust + Lean artifacts) and is not authorized.
- **`qvm_validated_noBoundsFault`** also has SEGLEG's exact cursor-alignment hypothesis
  (`PG_segleg_shiftAligned` + `PG_segleg_readsAligned`, and `segleg_repaired_suffices` proves it
  sufficient). The remaining SEGLEG obstacle is the MODARITH7 arm of
  `PG_segleg_opLenShift`: a normalisation problem on a `do` block, measured not guessed.

## 3. Next READY

- **B1** gates (4 h Sonnet) - READY.
- **C1** F2/IVC fixture (8 h strongest) - READY.
- **A3** vkLoading - the D-QVM1 fit blocker is closed; the VkRow branch (`t/A3`) is WIP and can
  resume at `vk_blockSim`'s reassembly.
- **A2** shared leaves - ST.11 and GEN.4 merged; ST.13 is still broken (do not trust its
  `PROVED (ST.13)` comment), `twoOutcomes_of_exitDiscipline` and `Run_worldEq_of_noWriters` are
  the long Step-induction pair.
- **A8** QVM row - blocked on the two statement changes above, not on the fit.

## 4. Waiting on human

1. **QVM row repair, remaining axes.** Authorize (a) full template-table agreement and (b) a
   segment validation/stack hypothesis on `qinterpRefines_qvmLoop`; or authorize a generator fix
   for the `neg`/`pow5` arms. Without one, A8 cannot start and `q_blockSim` cannot use the row.
2. **`snapshotOf_prepareMsgs`** - accept the replay gate as the evidence and retire the row, or
   port `prepare`'s schedule onto the phase records. Blocks 1 ROOT row of both roots.
3. **REF.5 Do step 2 / gate pairing** - still blocks B2 completeness and B3.
4. **REF.6 Do 2 vs `PoseidonCoherence`** - setting `poseidonE := <g1CodecC, ...>` falsifies three
   existing pins; a D.2 coherence change, not a silent absorption. Blocks B4.
5. **R.6 re-hash** - PLAN-V3 marks it subsumed at ST.6; confirm it is closed.

## 5. Last three merges

- `76ccfe5` PREFIXLIVE - `prefix_live` PROVED; root 18 -> 17, register 85 -> 84
- `88ea7a3` D-QVM2 - ROW.Q.3 restated over a fixed validated segment (signed)
- `7044b5a` QVMFIT - address-fit clause; VKFIT bounds are theorems (D-QVM1)
