# STATUS - midfall

**As of:** `fec9822` (2026-11-22). **FULL GATE GREEN at `29be14f`:** `verify.sh: ok (full)`,
EXIT=0, KAT 1640/118. After the B1/GASFREE/EXITSOUND merges the combined tree reports
`lowering_correct` **15** OPEN leaves, `lowering_sound` **7**, register **80 / 15 ROOT**,
**0 REFUTED**, `assert_no_refuted_sorry: ok`; `verify.sh --quick` and `--report` are green.
The QVM lane stays with its existing agent (midfall-c/d).

## 1. Verified - PROGRESS

    root lowering_correct .... 15 OPEN sorried leaves (snapshotOf_prepareMsgs, q_blockProgS,
                               q_blockSim, block_live, fp_*, gasFree_of_valid, lag_*, pcs_*,
                               tp_*, vk_*)
    root lowering_sound ...... 7 OPEN sorried leaves (the sim rows, prefix_sim, run_split,
                               snapshotOf_prepareMsgs)
    block rows ............... 1 INTEGRATED of 7 (traceReturn); 2 SORRY, 4 NONE
    exhibits ................. 2 PRESENT, 2 MISSING of 4
    ValidV3 at F1 ............ NOT INHABITED; blocking clause = generated (REFUTED at F1);
                               payload point half OPEN (B3)
    root lowering_correctW ... not reported (C0 not started)
    root generator_correct ... not reported (D2 not started)
    register ................. 80 rows / 15 ROOT; 0 REFUTED, 1 VACUOUS
    KAT ...................... 1640/118 pinned (last known; not run on this branch)
    frozen axioms ............ 5 named + 159 native_decide; roots are standard three + sorryAx,
                               native []

**TOT.1.a / ST.10 (this session):** `runBody_gas_oblivious` (GASFREE) and
`twoOutcomes_of_exitDiscipline` + `Run_worldEq_of_noWriters` (EXITSOUND) are PROVED; the root
moved 17 -> 15 and sound 8 -> 7. The `Run_worldEq` proof is the 41-constructor `Step.stepWorld`
induction over the `ScanClean`/`ScanCleanFuns` invariants; `twoOutcomes` uses it plus the exit
classification. All standard three, no `sorryAx`/`native_decide`.

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

- **ROW.Q.3 IS RETIRED, NOT OPEN (D-QVM2 signed; executed at `ddcb9cb`).** The universal row
  `qinterpRefines_qvmLoop` was PROVED FALSE by ROWFALSE (`0955bac`) on two independent grounds - a
  wrapping window and a default-table `neg` arm that runs while the reference underflows - and D-QVM2
  authorised restating it over a FIXED validated segment with the caller supplying table agreement and
  segment validation. **The replacement `QInterpRefinesSegment` is now landed, the refuted row's sorry
  and its register row were deleted in the same commit per W13, the retired text is retained as a
  sorry-free def with a type-level proof it is the refuted one, and ROWFALSE's refutations are kept as
  the W12 falsifiers.** G1 (window no-wrap) is DERIVED from `ValidV3` by D-QVM1's
  `windowFit_of_programWindow` (`qdvm2_G1_of_valid`), so it is a theorem, not an assumption;
  `QSegmentStackSafe` is built from the validator's OWN decode + stack-effect walk with end depth 1,
  so certificate and reference agree by construction. **`qinterpSegment_of_committed` proves the
  committed contract implies the replacement - a relaxation, not an extension.** **OPEN FINDING ABOUT
  THE SIGNED DECISION ITSELF: D-QVM2 asks the replacement to state the fold arms against the
  reference's `evalQuotientIdentity` value, which is IMPOSSIBLE - the reference refuses all five stream
  opcodes inside an identity (`qdvm2_foldSegment_refused`) and `evalNumerMptr` does not exist in the
  read-only reference. `qinterpFoldTop` is stated for the record; the clause needs a human amendment.**

- **QVM composition status.** QLOOP landed the first reduction of `selectSwitch` on the emitter's own
  31-entry list at a symbolic table, and QFIX landed the first REFERENCE-TIED arm fact
  (`qfix_reference_pushConst`) - so the count of arms tied to the reference is 1, not 0. 25 of 31 arms
  have emitted-side triples (`armcount.py`).
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

1. **D-QVM2 contains one unsatisfiable clause.** It asks the replacement to state the fold arms
   against the reference evalQuotientIdentity value, but the reference REFUSES all five stream
   opcodes inside an identity (qdvm2_foldSegment_refused) and evalNumerMptr does not exist in
   the read-only reference. **Amend D-QVM2 to drop that clause or point it at qinterpFoldTop.**
   The rest of D-QVM2 is executed at ddcb9cb; A8 can proceed against the replacement.
2. **`snapshotOf_prepareMsgs`** - accept the replay gate as the evidence and retire the row, or
   port `prepare`'s schedule onto the phase records. Blocks 1 ROOT row of both roots.
3. **REF.5 Do step 2 / gate pairing** - still blocks B2 completeness and B3.
4. **REF.6 Do 2 vs `PoseidonCoherence`** - setting `poseidonE := <g1CodecC, ...>` falsifies three
   existing pins; a D.2 coherence change, not a silent absorption. Blocks B4.
5. **R.6 re-hash** - PLAN-V3 marks it subsumed at ST.6; confirm it is closed.

## 4b. Parallel workers (2026-11-21/22)

- **EXITSOUND** (`midfall-f`, `t/EXITSOUND`): `Run_worldEq_of_noWriters` Step induction, then
  `twoOutcomes_of_exitDiscipline`. Per-op/WorldEq table and `ScanClean` infrastructure landed at
  `1460013`; the Step induction is the remaining work.
- **GASFREE** (`midfall-g`, `t/GASFREE`): `gasFree_of_valid` / `runBody_gas_oblivious`.
- **EXHIBITS** (`midfall-h`, `t/EXHIBITS`): the two missing Poseidon exhibits.
- **C1/WID.2** (`midfall-i`, `t/C1`): port the IVC partial KATs; WID.3/WID.4 depend on cargo.
- **B1/B5 audit** (read-only): the full B1/B5 state is in the worker report; the short version is
  below. B1 is not met: `poseidon_valid` is still a registered REFUTED row, DG.6 is not wired,
  DG.3's pinned zone is unsigned (the card's 972 is stale; current fingerprint 4823 decls / 526
  external leaves / `5d8c45843135d536`), DG.7 needs the human's branch permission, and S.10's
  stale "11 clauses"/"1792" prose remains. B5 is not met: OBJ.10/OBJ.12/T3.3 are absent, OBJ.11
  needs cargo and a human/Rust re-export decision.

## 5. Last three merges

- `1460013` EXITSOUND - per-op `WorldEq` table + `ScanClean` infrastructure (root unchanged)
- `29be14f` STATUS/QUEUE - PREFIXLIVE landed; D-QVM2 signed
- `76ccfe5` PREFIXLIVE - `prefix_live` PROVED; root 18 -> 17, register 85 -> 84
