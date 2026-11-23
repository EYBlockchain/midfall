# STATUS - midfall

**As of:** `72e5534` (2026-11-22). **FULL GATE GREEN at `d0bf226`:** `verify.sh: ok (full)`,
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

**Port audit (F1–F10):** the audit lane's `PORT-AUDIT.md` reports F1 (the two KZG point-set
constructions are independent ports; the rotation-collision case is the exact missing bridge),
F2 (raw-meta `numPointSets = 0`; known V3 repair), F3 (`scatterIndexed` faults where Rust uses
defaults), F4–F7 (stale prose, being fixed), F8 (params/SRS provenance pin), F9–F10 (not
mismatches). **D-GATE6** adds the rotation-distinctness clause to the supported profile;
**D-GATE7** adds the VK advice/challenge phase-length interface. Both are signed.
**D-GATE5 (signed):** D1's `kzgPartitionBridge_false_at_x0` proves the unconditional KZG
partition count false at challenge `x = 0` (generator 2 sets vs Halo2 1). `ChallengesGood` gains
`xNonzero : S.alg.x ≠ 0`, exactly parallel to `xNotRoot`; `CompleteSide` already quantifies over it.
This is a statement repair, not a row/`ValidV3`/root hypothesis; D1 is implementing the clause and
regenerating the closure manifest/`Frozen.sha256`.
**Merged at `4c920bd`:** A4 `lag_agrees_lLast_l0` + projections (202 lines), A5 output-word
round trip, A9 `eval_add_var_lit` + six-store plumbing, D1's named `readScheduleAgrees`/
`prepare_logSlots` gap.
**Merged since the last full gate:** D1's `EndToEnd.lean` (both directions; one remaining
`readScheduleAgrees_of_validV3` projection), A4's `LagrangeAlg` + `lag_agrees_xn` (D-GATE2
exponent), A5's staticcall segment form, A9's scalar-inv store plumbing; QVMHDR `modarith7Form_shift`/`step_shift_modarith7` and the
PAIRWISE fold transport; B1's DG.3 closure pin (`bd27cd298a04fc1a`) + DG.7 CI; C1's F2 IVC bundle;
B5's artifact gate (VK exact, verifier except `BUILD_ID`); A11's `fp_pairing_algebra`,
`fp_stmt_steps`, `fpG2Slots_of_valid` (register 75 -> 73); A5's modexp memory bridge; A9's
`ScalarInv` six-store frame.
**Full gate status:** at `4c920bd` the frozen hashes, closure (4823 pinned), sorry register
(73/11), native-decide confinement, reachability (229 modules), golden provenance and
import confinement are all green. The KAT replay was terminated by the orchestrator (not a
failure) and is re-running standalone; the last complete total was 1648/119 at `d0bf226`.
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
- **A4/lagrange** (`t/A4`): **`lag_agrees` and `lag_agrees_lBlind` PROVED** via the authorized
  leaf premises (`hE`/`hval`/`hBlindW`/`hInstEval`); the remaining work is to discharge those
  leaves where possible and T3.9.h/lag-row glue. `lBlind_fold` and `wAddmodAt_zero_left` are
  merged.
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
- **D1/end-to-end** (`t/D1`): `end_to_end_of_prepareLogSlots` is MERGED — the full `EndToEndV3`
  signature conditional only on `PrepareLogSlots`. D-GATE5's `xNonzero` is being implemented; then
  the four `PrepareLogSlots` sub-facts. Both `EndToEndV3` directions and
  `decodeRust_slots_eq_logWidths` are green. `prepare_logSlots` now has four explicit sub-facts:
  the `parseTrace`/`readAlgebra`/`multiPrepare` width sequences (`PresWidthSeq`), and the
  KZG-partition bridge
  `Halo2.constructIntermediateSets ... .pointSets.size = Generator.intermediateSets ... .pointSets.length`.
  The latter has no query-list/commitment/partition correspondence in the tree; the port-fidelity
  lane is checking it against Rust. `runBody_mono` (ST.13) is the other shared leaf; its direct
  induction needs a transport/bisimulation because `FunEnv`/`VEnv` are not defeq across dialects.
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

## 7. Lane snapshot

At `formal/baseline` `913f19a` (quick-gated; full-gate kernel checks green, KAT replay running):

- **A4 — PAUSED.** `lag_agrees` + `lag_agrees_lBlind` proved; `lagList`/`hE` discharged.
  `hval`/`hInstEval`, T3.9.h and the lag rows wait on A5's `batch_invert_summary` and the
  snapshot/query linkage.
- **A5 — staticcall walk tail lets** (`a3d1438`): `mload`/`first_mptr`/`second_mptr`/`gp_mptr`
  from the bundle pre; the head/guard composition and `BatchInvertPost` remain.
- **A6 — parser schedule.** SIM.10 obligation 2 and `tp_agrees_of_agree` are green;
  `snapshotAlgebraRun_wire`/`xcript_total` need the shared `PresWidthSeq` bridge.
- **A9 — scalar-inv/PCS.** `exec_mstore_state`, `mxMemFr`/literal bridge and the staticcall
  guard contract are green; the six-step `StmtsContractAll` and `emitScalarInvAt` summary remain.
- **A11 — finalPairing.** `EcPairing` helper/frame, product lemma and length/bit-AND guards are
  green; the `wp_run` normal leaf then G1/G2 wire, `.pcs → .pairing`, `fp_blockSim`/`fp_blockProgS`.
- **D1 — end-to-end.** `end_to_end_of_prepareLogSlots` is merged; D-GATE5 `xNonzero` and the
  `PresWidthSeq`/KZG query-map bridge are in flight. `runBody_mono` is the other shared leaf.
- **D2 — certified generator.** CERT.0 resumed under D-CERT1 (33 + 8 named obligations); the
  module port, `CertMeasure`, CERT.1 probes and the real-key generation are the deliverables.
- **Port-fidelity audit** (`t/PORTFIDELITY`): F1–F10 in `PORT-AUDIT.md`; D-GATE6 rotation
  distinctness and D-GATE7 VK phase-length interface signed; then the calldata codec component
  (`calldata_roundtrip`, `calldata_canonical`, `repack_spec_of_decodeRust`).

Register **73/11**, root **11/5**; the D2 CERT leaves will grow the register when merged, but not
the `lowering_correct` cone. No row, bundle, `ValidV3` or root hypothesis was added by any lane.

## 8. Integration notes (D-GATE5/6/7, CERT.0, calldata)

- **D1** has committed `9645f6d` — `ChallengesGood.xNonzero` (D-GATE5). The `Closure.manifest` /
  `Frozen.sha256` refresh is staged; merge only together with the gate update. D1 is now on the
  `PresWidthSeq`/KZG query-map bridge.
- **Audit** has D-GATE6 (rotation-distinctness) and D-GATE7 (VK phase lengths) edits in flight across
  `VerifyingKey.lean`/`CurveSurface.lean`/`PoseidonValid.lean`/`Kzg`/`Degrees`; it will commit each
  finding separately. Its F1 bridge is the same query-map bridge D1 is proving; do not duplicate.
- **D2** has `Midfall/Generator/Certified.lean` and `Instances/CertMeasure.lean` staged with the
  `gen_sorry.sh`/`kat_gate.py` changes; CERT.0 is the target, with the 33+8 named obligations.
- **Calldata:** `calldata_roundtrip` is an independent encode/decode proof, but
  `repack_spec_of_decodeRust` is **not** independent — `decodeRust` is defined from `prepare`'s
  transcript log, while `decodeWire` parses the slot schedule, so the bridge needs the same
  `PresWidthSeq`/`PrepareLogSlots` work. The calldata lane is therefore queued behind D1/A6 rather
  than treated as a shortcut.
- **D-GATE5/6/7 are statement repairs**, all signed: no row, bundle, `ValidV3` or root hypothesis was
  added. The closure manifest will be regenerated once after the three repairs merge; until then the
  only valid global gate is `verify.sh --quick` (KAT replay deferred).

## 9. Calldata ownership

The calldata codec component (`calldata_roundtrip`, `calldata_canonical`,
`repack_spec_of_decodeRust`) remains with the port-audit lane, after its D-GATE6/7/F4–F7 fixes.
`calldata_roundtrip`/`calldata_canonical` are independent encode/decode proofs; `repack_spec_of_decodeRust`
depends on D1's `prepare_logSlots`/`decodeRust` log schedule and should not be claimed as a shortcut.

## 11. Current integration

At `ec33847`: D2 is merged and the next generation peels are closed (`env_nG2`, `prog_noDirect`,
`env_vkDigest`, `v3_payload`); the register is **105 sorried declarations / 11 ROOT / 32 CERT /
0 REFUTED** (105 rows in `SORRY.md`); D1A's exact `readAlgebra` width sequence and `multiPrepare`
phase A/B/C widths are merged. A4's
`runBody_mono` (ST.13), lag statements 0–6, and the `litValue_number_nat` helper are merged; A5's
8-statement walk, tail, prelude 2–9, `wMulmodAt` inverse link, bridge modulus arithmetic, six-store
frame composition, and bridge 11–20 form are merged; A9's PCS block-1/block-2/block-3-seed
semantics, generator Word bridge, complete block-1 ROT_POINTS table spec, block-3 straight-line
list folds, and rolled-arm nested-mload inversions are merged; A11's guard helpers, trim, normal leaf, call inversion/VK wire, `FpWire`, selector-bucket
monotonicity, and the full `Inv .pcs → Inv .pairing` transfer are merged; A6's `GroupsMatch` split,
state-threaded fold, and `phaseCols` are in its branch; A12's `block_live` traceReturn/vkLoading
cases, finalPairing poison arm, and loop-existence rule are merged (3 of 7 block-cases). B4's `ValidV3InhabitationF1Completion` proves `f1GeneratedRender_notValidV3` and the
exact reduction `ValidV3 R ↔ ValidV3ExceptPayload R ∧ PayloadPointHalf R`; B4's
`ValidV3SyntheticInhabitant.exists_validV3` proves `∃ R, ValidV3 R` at a synthetic render, so the
**generic root is non-vacuous**, and B4's DG.4 `GeneratorDone`/`Done`/`not_done_today` card is merged.
B3's `PayloadPointsF1` supplies the resourced 19/8 commitments and the point half; the test-SRS
exponent is `n = blsR - sTest`, but the production F1 NEG_S_G2 scalar is in no tracked file. The
F1-real `ValidV3` at `f1PointRenderCN n` is therefore conditional on
`hpay : vkG2Words f1Pv vkNegSG2BaseSlot = g2foldToEip (g2foldExp n)`; `ValidV3F1Real` proves it from
that data input. B4's DG.4 `Done` card is merged; a positive F1 `Done` remains blocked on a concrete
codec law, a render-correct `Done` statement, `TotalV3`, and `ArtifactEq`. The D2 KAT is green
(**1648 annotated checks / 120 files**), quick gate and `checks.sh` are green, and the
`ChallengesGood.xNonzero` statement pin is in place.

**Generator-layout finding (`PG-FPSCRATCH`).** `VerifierMemoryLayout.validate`'s
`memoryLifetimeIntersects` returns true only for equal phases (or `permanent`), so the finalPairing
phase scratch and the `pcsQEvalSourceTable`/theta block are never compared. The current safety of
the finalPairing normal path rests on the fixed low-memory scratch start plus the
`vk_payload`/`challenge_slots` permanence chain; a plan with a small enough `vk.len` would pass
`validate` and break `Inv .pcs` on that path. A12 is constructing the falsifier and the exact
repair (a generator layout assertion or a `programOk` projection); no hypothesis is being added to
`block_live` or `ValidV3`.

The vacuity report is the non-vacuity ledger: the generic V3 root is now **NON-VACUOUS (synthetic)**
via `exists_validV3`, but **VACUOUS at F1** (`f1_ValidV3_false`), and `0 REFUTED / 1 VACUOUS` is not
a non-vacuity certificate. The F1-real `ValidV3` is conditional on the production SRS `hpay`; the
shortest path to the fully verified **generic** verifier is the root rows plus `EndToEnd`/generator,
with the F1-specific `Done` recorded as data-blocked.

### Six-lane critical path (user cap)

Phase 1 (live now):
- **A5** bridge 11–14 composition + `count_bytes = 32` + `BatchInvertPost`.
- **A9** PCS rolled `forLoop` + block 4–6.
- **A4** lag fixed segments 4–6, 11–12, 14–15, 17, 19–21, 22–27, then whole-block/rows.
- **A12** `block_live` clean arm + `PG-FPSCRATCH` falsifier/repair.
- **D1A** `EndToEndAlgebra` readAlgebra/multiPrepare widths.
- **D2** CERT derivable leaves.
Paused: A6 TP accessor, A11 finalPairing clean arm (layout disjointness), B3/B4 F1-real/Done residual,
port audit D-GATE6/7, calldata, CERT2.

Phase 2, as A5/A11 close: **A4** lag fixed segments/rows, **D1P/D1A** `EndToEnd` widths,
then **A12** `block_live` (2/7 done) and the port audit D-GATE6 bridge.

Phase 3, as rows/ValidV3 close: **D2** CERT (`env_nG2` + remaining 36), **DG.4** `Done`/`ArtifactEq`,
**calldata** and the final full gate.

Paused, resumable from their worktrees/sessions: D2 (env_nG2), A4 (lag), A12 (`block_live`),
D1P/D1A (`EndToEnd`), port audit D-GATE6/7, calldata, CERT2, DG.4. QVM is with the separate external
agent.

The root remains **11 / 5**. No row, bundle, `ValidV3`, `ValidW`, or root hypothesis was added.
