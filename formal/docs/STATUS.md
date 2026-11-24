# STATUS - midfall

**As of:** `35544b4d` + final-assembly merge (2026-11-24). **Quick gate GREEN at `35544b4d`**; the
last full gate is `7e1e7a29` (`verify.sh: ok (full)`, KAT 1648/119) and a final full gate is owed.
The final assembly moved `block_live` and `totalV3_correct` to
`Midfall/LoweringV3/BlockLive.lean` with a seven-block case table: three cases are closed
(`vkLoading`, `finalPairing`, `traceReturn`) and the four open inputs are
`block_live_case_transcriptParser`, `block_live_case_lagrange`, `block_live_case_quotientLin`,
`block_live_case_pcs`. The generic claim surface is `Midfall/LoweringV3/FinalClaims.lean`; the
F1-real `DoneAt` stays in `Midfall/Instances/GeneratorDoneAt.lean` with its index in
`Instances/FinalClaimsF1.lean`. Register after this merge is regenerated in `SORRY.md`; the
remaining CERT leaves are unchanged. The targeted
`lake build Midfall.LoweringV3.BlockLive Midfall` is green.

**CERT leaves closed since the prior status:** `prog_transcriptFloor` (CERT.4, from the generated
layout), `supported_layout` (CERT.4, from `validateGeneratorInvariants` + `MemoryMap.validate`
implies `WellFormed`), and `v3_pins_of_valid` (CERT.6, from `ValidV3`/`GeneratedBy`).

## 1. Verified - PROGRESS

    root lowering_correct .... 14 OPEN sorried leaves (q_blockProgS, q_blockSim,
                               block_live_case_{lagrange,pcs,quotientLin,transcriptParser},
                               lag_blockProgS, lag_blockSim, pcs_blockProgS, pcs_blockSim,
                               tp_blockProgS, TranscriptRows.{tp_agrees,tp_computes,tp_poison})
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
- **A12/totality** (`t/A12`): per-block liveness from the proved vk/tr progress rows. The root
  `block_live` now lives in `BlockLive.lean` as a seven-way table: vkLoading/finalPairing/traceReturn
  are CLOSED, the four conditional progress rows are the exact remaining case inputs.
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
- **D-GATE8 (signed 2026-11-23).** A11 proved the pairing-slot pointer-fit is not derivable from
  `programFits`: the VK bounds cover only `vkMptr + vk.len`/`runtimeLen`, while `pairingLhsMptr`/
  `pairingRhsMptr` and the G2 header pointers are post-payload `allocAfter` blocks that can cross
  `2^256`; the emitted `BitVec.ofNat 256` literal then wraps (A11's `PG-PAIRINGFIT` falsifier).
  The repair adds `staticWorkingSetFits pv` — `pv.memory.traceU256Mptr + wordBytes < 2^256`, where
  `traceU256Mptr` is the aligned maximum of all twenty-three static region ends — as a conjunct of
  `programFits` and `programFitB`, with `staticWorkingSetFits_of_valid` as the projection. No row,
  bundle or root hypothesis was added; the producers re-decided with no proof changes. A11 now
  derives `PG_PAIRINGFIT` from the new clause by unfolding `traceU256Bound`'s candidate list.

## 9. Calldata ownership

The calldata codec component (`calldata_roundtrip`, `calldata_canonical`,
`repack_spec_of_decodeRust`) remains with the port-audit lane, after its D-GATE6/7/F4–F7 fixes.
`calldata_roundtrip`/`calldata_canonical` are independent encode/decode proofs; `repack_spec_of_decodeRust`
depends on D1's `prepare_logSlots`/`decodeRust` log schedule and should not be claimed as a shortcut.

## 11. Current integration

At `7a55dc8d` (2026-11-23): register **96 rows / 11 ROOT / 22 CERT**, 0 REFUTED, 1 legacy VACUOUS
(`end_to_end_acc_complete`); 102 sorried declarations; 252 modules; closure **5250 declarations /
620 external leaves / digest 209cde2f48115a76**; quick gate green.

**D-GATE16 (signed, 2026-11-23)**: generator-build stack clause (the QVM:1217-1222 validator
interface) added to the generator input shape so `build.maxStack ≤ build.bytes.size` is available
for `prog_programFits`; not a row/root hypothesis.

**D-GATE17 (signed, 2026-11-23)**: the D-B5 artifact variant `ArtifactEqV3` supplies the modeled
`BUILD_ID` input line; raw `ArtifactEq` at the tracked dump is refuted only by that line
(machine-checked). The positive gates and VK byte-exactness are proved at the model with the input.

**D-GATE18 (signed, 2026-11-24)**: `VerifyingKey.WellFormed` gains
`advicePhaseColumnOrder : vk.cs.phases.flatMap (fun ph => phaseCols vk.cs ph) =
List.range vk.cs.numAdviceColumns`. `advicePhaseTotal` only fixes the phase vector's LENGTH;
the parser's advice block is phase-indexed while the trace's advice commitments are
column-indexed (`scatterIndexed`), so the phase-to-column order is a separate decidable
key-side clause. It is not a row, bundle or `ValidV3` field; `advicePhaseTotal_not_columnOrder`
is the falsifier showing it is not derivable from the old fields. `AdvicePhasesColumnOrder`
is now a theorem of `WellFormed` (`advicePhaseColumnOrder_of_wellFormed`), so the closed
`tp` consumer takes only the calldata bound.

**D-GATE19 (decision, 2026-11-24)**: the calldata predicate needed for `hnum`
(`R.cfg.numInstances < 2^31`) is `cd.size < 2^36` (`numInstances_lt_of_cd_size`: `Decoded`
fixes `cd.size = proofEnd + 32 + 32 * numInstances`). It is exposed at the consumer
`tp_agrees_of_valid_closed_cdSize`, NOT added to `EntryFrameV3`/`Frame`/`TpPost` or `ValidV3`:
`tp_agrees` has no entry-frame parameter, and adding the bound to `Frame` would be a bundle
field. `EntryFrameV3.cdSize` remains the existing `< 2^256` length bound; adding `< 2^36`
there would not reach `TpPost`. The exact minimal alternative is therefore the single
consumer predicate `cd.size < 2^36` (or, if the entry frame must carry it, a `Frame.cdSize36`
field, which is the bundle change this decision declines).

**D-GATE15 (signed, 2026-11-23)**: `WellFormed` gains the `readAlgebra` totality bundle: fixed
insert bound (`fixedQueries.size ≤ numFixedColumns` + simple-selector coverage), rotation-not-`i32::MIN`,
and the instance slice-window bound. VK sanity clauses, not row/root hypotheses.

**D-GATE16 (signed, 2026-11-23)**: `SupportedInput` gains `stackBound`, the generated-build
stack clause: for every successful output, the plan's quotient build satisfies
`build.maxStack ≤ build.bytes.size`. The QVM:1217-1222 validator is not ported
(`finishValidatorLeg`), and `finish` records `maxStack` from the pre-compaction stream while
`build.bytes` is compacted, so this is not a builder-state invariant (`pushStackAcct` emits no
byte). The clause is an input predicate over the generator's own outputs; F1 witnesses its
concrete content (`CertMeasure.f1StackOk_true`, `native_decide`). The quotient byte size is
already proved from `vkCarriesBuild` (`build_bytes_size_le`), and
`generated_build_stack_words_le` combines it with the stack clause:
`build.maxStack ≤ 32 * vk.quotientProgramWords` for the generated plan.

**D-GATE14 (signed, 2026-11-23)**: `WellFormed` gains `fixedSelectorBound :
numSimpleSelectors ≤ numFixedColumns`, the `readFixedEvals` no-throw precondition needed by the
`readAlgebra` walk. VK well-formedness clause, not a row/root hypothesis.

**D-GATE13 (signed, 2026-11-23)**: `calldata_roundtrip` carries the size bound
`proofEnd + 32 + 32*numInstances < 2^256`, supplied from the entry frame's `cdBoundB`/`cdSize`
(ABI length words are `u256`). It is a calldata/entry-frame bound, not a row/root hypothesis; the
roundtrip is proved at `Midfall.Lowering.calldata_roundtrip` with standard axioms.

**D-GATE12 (signed, 2026-11-23)**: `WellFormed` gains `lookupChunkable` — every lookup's
`nbParallelLookupsPerChunk vk.csDegree` succeeds and is positive, so `chunkByDegree`/`rustChunks` is
total on the verifier's lookups. This is the missing static fact the parseTrace multiplicity walk
needs; it is a VK well-formedness clause, not a row/root hypothesis.

**D-GATE11 (signed, 2026-11-23)**: `SupportedInput` gains a count bound (CS/lookup/
commitment/point-set counts and VK payload length) so the generated layout's
`staticWorkingSetFits`/`batchInvertScratchFits` and `proofEnd` bounds follow from the input. The
`v3_cdBound` CERT leaf is PROVED; `prog_programFits` remains OPEN with the exact quotient-build/
config-sizing residual recorded in the detailed D-GATE11 bullet below. It is a generator
input-predicate strengthening, not a `ValidV3`/row/root hypothesis.

**D-GATE8 (signed, 2026-11-23)**: `programFits`/`programFitB` carry `staticWorkingSetFits pv`
(`traceU256Mptr + wordBytes < 2^256`), the full static-region fit. A11 derived `PG_PAIRINGFIT`,
`pairingLhsMptr_toNat_of_valid` and `pairingRhsMptr_toNat_of_valid` from it;
`block_live_finalPairing_of_body_fit` discharges the finalPairing fit premises. The closure manifest
was regenerated after D-GATE8 and again after D2's generator refactor (5250 decls, digest
`209cde2f48115a76`) and `Frozen.sha256` re-pinned.

**Merged this wave**:
- A5: bridge head/full success+reject, stores env/halt frame, canonical/nonzero `BridgeSucc`,
  forward-loop leave arm and staticcall walk carrying `mptr`; `BatchInvertPost` is defined.
- A9: m1 no-halt/exec contracts, `finishCall`/`copyReturn` outside-window frames, `storesLit`
  output memory and the guard memory frame.
- A12: `FpBodyRun` actual-source post, `.vk` payload projection, `ec_pairing` prefix/tail/body phases.
- A11: clean `ec_pairing` call contract at the boundary state (`ecPairing_call_clean_at`) and
  `block_live_finalPairing_of_body_fit`.
- A6: `TranscriptRows` merged (`tp_events_slots` and `tp_blockSim` proved; five TP leaves registered),
  and the lane resumed on the Lean-side `parseTrace` widths plus those leaves.
- D1A: protocol eval decomposition, `PrepareLogSlots` from the parsed trace, and
  `end_to_end_of_A6_KZG`/`end_to_end_of_tpEvents` with exactly two named Props:
  `ParseTraceSchedule` (A6) and `KzgMultiPrepareWidths` (D-GATE5/KZG).
- D2: `generateBaseVkHeader_slots` (slots 0-10), reservation/fill `getD` prefix lemmas, the five
  payload CERT leaves (`payload_header`/`g1Base`/`g2Base`/`negSG2`/`payload_comms`), and the
  generator refactor (closure re-pinned at 5250 decls, digest `209cde2f48115a76`).
- A11: `fp_blockSim` CLOSED, `fpBodyRun_clean`, `fp_slice_det`, `callsOf_functional`, and
  **`fp_blockProgS` CLOSED** — no finalPairing ROOT row remains (ROOT 12 -> 11 after the TP leaves
  enter the cone).
- A12: REF.9/REF.10 CLOSED (`g1CodecC_compressedEncoderFirst`, `g1CodecC_lawsV3`; register 102 rows).
- A9: PCS block-4 m1 set contract, `dxLines`/`lbasisLines`/`bpLines`/`bq`/`bqLines`,
  `denInv`/`eval`/`termLines`/`f_eval` line folds, and the general-arm AST/name/no-shadow bundle
  (1790 lines); `block_live_pcs`. The set-block/block composition is the remaining PCS unit.
- A9: `pcsGenPrefix_contract` state threading, `pcsGenBody_contract` (prefix+batch+tail), and
  `pcsSetBlockAst_eq_gen` are proved; `pcsSetBlock_contract`'s restore-env facts remain.
- A11: `runsAllP_fixed_fold` and `readFixedEvals` proved; the remaining `readAlgebra` blocks are
  logup/permutation/advice/instance/minRot/lIS, then the parseTrace cover.
- A5: `fromConstraintSystem_pcsQueries`, `perProofQueries_parts`, the permutationZ upstream
  reordering, the upstream z-slice, `KzgQueryMapData.ofPairQueries`, and the quotient
  freshness/`hclass` classification are proved; the per-pair instantiation and concrete render
  freshness are the remaining datum inputs.
- A4: `LagrangeBlock` vocabulary + statement-4 contract; per-phase representation and group-4
  denominator-loop proof.
- A5: `bi_front`, `bi_back_tail`, prelude main, and **`batch_invert_summary` PROVED** (with the
  first-word-canonicality and `32 ≤ s` preconditions the lag pre supplies).
- A12: REF.9/REF.10 **CLOSED** (`g1CodecC_compressedEncoderFirst`, `g1CodecC_lawsV3`), and the
  resourced-codec F1 render `f1PointRenderCCN` with `ValidV3` under `hpay` and the gate's codec
  conjunct discharged (`f1PointRenderCCN_gateAtV3_of`); `DoneAt` now has the F1-resourced instance
  `f1PointRenderCCN_doneAt`, reducing to the gate data, `ArtifactEq` and `hpay`.
- A6: `TranscriptRows` merged, `fromProtocol_advice_itemCount`, the `parseTrace` width walk, and
  `parseTraceSchedule : ValidV3 R → ParseTraceSchedule R` (D-GATE7's `advicePhaseTotal` closes the
  phase-count pin); `Rows.tp_blockSim` is closed. The five TP leaves remain, blocked on the
  `common_uncompressed_g1` call summary and SIM.10's `xcript_total`.
- A11b: `xcript_total` is NOT derivable from the current facts; landed the exact clause
  `XcriptAlgebraRun` + `tp_agrees_of_xcript`, reducing `tp_agrees` to the parser/`readAlgebra` run
  existence and the `Inv .transcript` assembly. `tp_agrees`/the TP leaves remain the five registered
  holes.
- A12: the resourced-codec F1 render `f1PointRenderCCN` and the fixture gate inputs
  (`decode`/`snapshot`/`SoundSide`/`CompleteSide`/deployment/entry) are proved; `LeanAccepts` is
  REFUTED for the tracked test-SRS calldata at the production key, so a positive F1 `DoneAt` needs a
  production calldata/proof (documented in `VACUITY.md` §10c).
- D-GATE9: `programFits` carries the batch-invert scratch floor (`32 ≤ batchInvertScratchMptr`);
  A4's lag call uses it.
- D-GATE10: the old `KzgMultiPrepareWidths` (`∀ queries`) is false for positive `numPointSets`;
  the consumer is repaired to the per-query obligation at `linearize`'s query vector.
- **D-GATE11 (signed 2026-11-23): the generator's count budget.** `prog_programFits` and
  `v3_cdBound` were not derivable from the pre-D-GATE11 `SupportedInput`: the layout arithmetic
  multiplies unbounded `Nat` counts by `G1_BYTES`/`WORD_BYTES`, and no clause bounded `proofEnd` or
  the static working set. `SupportedInput` now carries `countBound : CountBound gi` (a computation on
  `gi`, so it remains an input predicate):
  * every raw-meta protocol count is `< 2 ^ 32` (`numLookups`, `numPermutationZs`, `numTrashcans`,
    `numQuotients`, `numUserAdvices` entries, `lookupChunks` entries, `pcsQueries.length`) —
    `MetaCountsBound`;
  * `numSimpleSelectors`, `numEvals` and `challengeIndices.length` are `< 2 ^ 32`;
  * the generated payload (`payloadOf gi`, `generate`'s first two binds) has `len < 2 ^ 200`;
  * `numInstances < 2 ^ 32`.
  The point-set count is NOT a meta field (it is computed by `intermediateSets`), so it is bounded
  indirectly: `pcsQueries.length < 2 ^ 32` plus the PROVED `numPointSets_le_pcsQueries` (the
  partition has at most one set per PCS query). The new module lemmas
  `step1Fold_length_le`/`constructIntermediateSetsImpl_pointSets_length_le` are the length walk.
  **`v3_cdBound` is now PROVED** from `proofLen_eq_repackedLen`, `tp_fromProtocol`,
  `newFromVk_meta_numEvals`, `newFromVk_numPointSets_le` and the count budget
  (`commitmentG1Count < 2 ^ 66`, `proofEnd < 2 ^ 80`, hence `< 2 ^ 256`). The F1 concrete-count
  witness is `Instances/CertMeasure.f1CountsOk_true`, a `native_decide` on the raw meta, the
  payload length and the proof-end bound.
  **Residual (CERT.6/D4), stated exactly.** `prog_programFits` itself is still OPEN, but its
  `batchInvertScratchFits` conjunct is PROVED
  (`Midfall.Generator.Certified.batchInvertScratchFits_of_generated`, from the exported
  `new_selectorAccMptr_ge` four-step arena chain and `generated_vkMptr_floor` + `0x1560`), the
  quotient program's byte size is proved (`build_bytes_size_le`:
  `build.bytes.size ≤ 32 * vk.quotientProgramWords`, from `vkCarriesBuild`), and D-GATE16's
  `SupportedInput.stackBound` supplies `build.maxStack ≤ build.bytes.size` for every successful
  output. The residual is now the LAYOUT ARITHMETIC: bound `staticWorkingMemorySizeForMeta`'s
  transcript words, the six `VerifierMemoryLayoutConfig` overrides (`quotientStateWords`,
  `quotientStackWords`, `accMsmTerms`, `rotPointsWords`, `x1PowersWords`, `qEvalSetWords`,
  `qEvalSourceTableWords`, `qComTraceMsm`, `finalMsm`), and the selector-fold `maxPower`, then
  bound the twenty-three `traceU256Bound` candidates; `quotientProgramFits` uses the same
  config/selector bounds. No `ValidV3`, row, bundle or root hypothesis was added, and
  `SupportedInput` was strengthened.

### `block_live` assembly - **LANDED** (`Midfall/LoweringV3/BlockLive.lean`)

The move is done. `BlockLive.lean` imports `Totality` + the case modules (`FpFit`,
`LagrangeBlock`, `PcsBlock4`) and sits below `Composition`, which now imports it for
`totalV3_correct`. The statements of `block_live` and `totalV3_correct` are `Totality`'s,
verbatim; no hypothesis was added. `Totality` keeps the per-case reductions
(`block_live_of_blockProgS`, `block_live_pcs`, `block_live_transcriptParser_of_prog`,
`block_live_quotientLin_of_prog`) and `prefix_live`/`slices_live`.

`block_live` is a seven-way named case table (`cases q` only), not a hole:

| block | case theorem | state |
|---|---|---|
| vkLoading | `block_live_case_vkLoading` | CLOSED - wires `Totality.block_live_vkLoading` |
| transcriptParser | `block_live_case_transcriptParser` | **OPEN** |
| lagrange | `block_live_case_lagrange` | **OPEN** |
| quotientLin | `block_live_case_quotientLin` | **OPEN** |
| pcs | `block_live_case_pcs` | **OPEN** |
| finalPairing | `block_live_case_finalPairing` | CLOSED - wires `FpFit.block_live_finalPairing` |
| traceReturn | `block_live_case_traceReturn` | CLOSED - wires `Totality.block_live_traceReturn` |

The four open rows are the exact remaining case inputs (`#cone_sorries block_live: 4`).
`totalV3_correct` is PROVED from the table plus `prefix_live`/`slices_live` and the two gas leaves;
its cone is the same four rows.

**Statement mismatch, measured (the reason the rows are not wired directly).** The generic
packers close a case from a `BlockProgS` over `StageInv` with NO acceptance premise. The landed
row statements are stronger: `TranscriptRows.tp_blockProgS`, `Rows.tp_blockProgS`,
`Rows.lag_blockProgS`, `Rows.pcs_blockProgS` and `QuotientRows.q_blockProgS` all take
`hacc : LeanAccepts R H cd` and `hcomp : CompleteSide R H cd`. `block_live` is unconditional in the
calldata, so it cannot supply either; wiring the rows as stated would require adding those two
facts to `block_live` (forbidden: it weakens the statement). The residual is therefore the
**unconditional progress row** for each of the four blocks, not the landed row verbatim. The
PCS/lagrange low-level contracts (`PcsBlock4.pcsBlock_contract`, `LagrangeBlock`'s
`LagInnerContract`/`LagBlockContract` definitions) sit below the row and do not by themselves state
`BlockLive`; no `block_live_lagrange`/`block_live_pcs_running` theorem exists to wire today.

### Final claim surface - generic vs F1-real

* `Midfall/LoweringV3/FinalClaims.lean` - the GENERIC surface: `lowering_correct`,
  `generator_correct_V3`, and `end_to_end_of_lowering_correct` (`EndToEndV3` with the headline's
  `hEq` discharged by `lowering_correct`, conditional on the named `PrepareLogSlots` bridge). Its
  gates assert `native []`; `sorryAx` is named only because the four BlockLive rows are still open.
* `Midfall/Instances/GeneratorDoneAt.lean` - the F1-REAL `DoneAt` wiring
  (`f1PointRenderCN_doneAt`, `f1PointRenderCCN_doneAt`), conditional on `hpay`, the gate data,
  `ArtifactEqV3` and the execution data. It consumes `totalV3_correct` from `BlockLive`.
* `Midfall/Instances/FinalClaimsF1.lean` - the index for that F1-real claim and the record of its
  native/data trust boundary. checks.sh's import-confinement rule keeps it out of every generic
  theorem-bearing file; the generic module does not import it.

### Six-lane critical path (user cap)

Nine-lane wave (2026-11-23): A9b PCS `pcsGenBody`/set-block/block; A4 lag group 13 + inner contract;
A6 `common_uncompressed_g1` scope/body contract; A11c `XcriptAlgebraRun`/`tp_agrees`; A5 KZG
same-order query shape/`hclass`; D2 CERT.5 gas scans; calldata `calldata_roundtrip`; PlanMeta/CERT.1;
D-GATE11 generator input-fit. A12's F1 gate is data-blocked on `LeanAccepts` (test-SRS proof vs
production key).

Phase 2: `block_live` - 3/7 CLOSED (traceReturn, vkLoading, finalPairing) and the seven-way table
LANDED in `BlockLive.lean`; then the four open TP/PCS/lag/quotient case rows (as unconditional
progress rows, not the `LeanAccepts`-guarded row statements), `TotalV3`, and the `Rows` glue.

Phase 3: D2 CERT payload; `Done`/`ArtifactEq`; port audit D-GATE6/KZG; calldata; final full gate.
QVM is with the separate external agent.

The root remains **11 / 5**. No row, bundle, `ValidV3`, `ValidW`, or root hypothesis was added.
