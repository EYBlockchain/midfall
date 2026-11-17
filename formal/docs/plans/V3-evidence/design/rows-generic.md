# The block rows for every render: what each emitter prints, and what the proof must induct over

> **After review (2026-11-17).** `GeneratorRows.lean` was repaired: `simPins_of_valid` is deleted and `rows_correct` no longer has the `SimPins` conjunct (`rows_total` is separate and needs `hasMultiPointSet`); `lag_lblind_loop` and `lag_instance_loop` conclude `SameUpToActive st st'` instead of `st' = st` (their bodies run `mload`). 40 open obligations. Where this memo differs, the Lean file is right.


HEAD `cf00592`. Evidence: `GeneratorRows.lean` (rows, children, premise gaps), `GeneratorRowsWitness.lean`
(tests at F1), `check-rows.sh` (the `check.sh` olean mechanism with a private `V3_OUT`).
Marking: **[M]** measured or typechecked in this pass; **[R]** read in the source at the line given;
**[I]** inferred, not checked by a machine.

## 0. What "for every R" quantifies over

- **[R]** `R.slice q = Inline.inlineContractConstants (constTableOf R.model) (GenAst.emitPartial R.pv q)`
  (`Program.lean:125`, `Statements.lean:102`). So a row for every `R` is a statement about an emitter of
  `GenAst*.lean` at every `PlanView`, composed with the inliner at every constant table.
- **[R]** The inliner (`InlineConstants.lean:287-389`) leaves a stuck `match consts.lookup x` at each
  unshadowed variable site; `Blocks/VkLoading.lean:94` names that site `vkSite`. A slice is inlined on
  its own, with an empty shadow list.
- **[M]** The kernel reduces the inliner on a symbolic table and a symbolic layout: `lagInner_length`
  (28 statements), `qlinInner_length` (9), `lag_sq_loop_form`, `helpers_eq` are proved by `kernel_rfl`
  (six lines of meta code: `Eq.refl` assigned without the elaborator's check; the kernel checks it).
  The elaborator's `rfl` on `lagInner_length` hit the default 200000 heartbeats at `whnf`. A false
  equation is refused: `(kernel) declaration type mismatch`.
- **[M]** `GeneratorRows.lean`: 21 s, 0 errors, 41 `sorry`, each a named theorem. Witness file: 15 s.

## 1. Composition (nothing to do)

- **[M]** `sim_rows`, `prog_rows`: `R.SimContracts product` and `R.ProgContracts product` from the 14
  per-block rows, proved. `rows_correct` as specified, `lowering_correct_of_rows` and `lowering_correct`
  proved through `lowering_equivalence_of_stages`. `#cone_sorries rows_correct`: 16 leaves.
- **[M]** `rejectsV3_of_rows`: `RejectsV3` from the same rows. `total_correct : TotalV3 R product` from
  four named leaves plus the tree's `prog_slices_decomp`.
- **[M] Finding.** `simPins_not_of_valid`: if any render is valid, some valid render fails
  `SimPins.compressedEnc` (`breakCompressed`). The conjunct `SimPins R` of `rows_correct` is not a
  consequence of validity; `simPins_of_laws` derives it from `G1CodecHeadlineLaws` and
  `hasMultiPointSet`, which is where RECON.2 step 4 puts it.
- **[I]** No inhabitant of `Render.Valid` is known at HEAD (`poseidonRender_notValid`,
  `Instances/PoseidonValid.lean:519`; `CodegenAgrees` is false until OBJ.2). Every row is vacuous at F1
  until `ValidV3` lands (OBJ.8, OBJ.9). W12 witnesses below are therefore at the level of children.

## 2. Per block

### Prefix (SIM.6) — `Program.lean:66-116`, `Blocks.lean:191-198`

| part | kind |
|---|---|
| `abiGuardBlock m` | fixed text, three model numerals, two table names **[R]** |
| `wrapperLocals` | one `let vk` under `separateVk`, `embeddedQuotient` **[R]**; needs `model_flags_of_valid` |
| `mainGuardBlock`, `mainLocals` | fixed text, two table names **[R]** |
| `R.helpers` | eight function definitions; a no-op to execute. **[M]** `helpers_eq`, `helpers_funDefs` |

- Invariant: none (no loop, no list). Post: `StageInv .start`.
- Risk: none in the semantics. The row waits on facts about the generator: `layout_static_of_valid`,
  `model_flags_of_valid`, PG-FRMOD, PG-G1ID, and RECON.2's `Frame.cdSize`.
- Cards: 5.

### Lagrange (T3.9) — `GenAst.lean:681-761`

| statement of the inner scope | kind | bound |
|---|---|---|
| 0–2, 4–6, 8–9, 11–12, 14–15, 17, 19–27 | fixed text, 13 table names | |
| 3 squarings | loop | `k` |
| 7 denominators, 13 second pass | loop | `n + m` (literal `(n+m)*32`) |
| 10 `batch_invert` | helper call: two loops, bound = batch words; one demonic `staticcall` | `n + m + 1` |
| 16 `l_blind` | loop | `m − 2` |
| 18 instance polynomial | loop, two cursors | `n` |

(`n = numInstances`, `m = numNegLagranges`.)

- Invariants: per loop, a word-level closed form (`wPow2`, `omegaPows`, `wSum`). Interface between SEM
  and ALG: `LagRel` (relation on five words, inverses existentially quantified).
- **[M]** At F1 `k = 6, n = 1, m = 9`; every hypothesis of the five loop lemmas holds together
  (`lagChildrenHyps_ok`).
- Risk 1 **[I]**: `m < 2`. `l_blind` is read from word 1 and the instance walk starts at word
  `max 2 m`, so for `m = 1` the block computes values the Lean verifier does not. `EnvAgrees.negLagranges`
  gives `m = blindingFactors.toOption.getD 0 + 1`. If `WellFormed` does not give `blindingFactors = .ok b`
  with `1 ≤ b`, the row is false for such a render (PG-NEGLAG).
- Risk 2: the loop rule (GEN.3) has not closed a loop yet. `lag_sq_loop` is the first.
- Cards: 9, plus 3 for `batch_invert` (HLP.1.b–d).

### TranscriptParser (ROW.TP) — `GenAst.lean:1073-1178`, helpers `:320-389`

| part | kind | induct over / bound |
|---|---|---|
| head (5 statements), tail guards, `g1AbsorbCopy` ×2, x3 mask | fixed text | |
| instance run | loop | `numInstances` |
| advice | list induction, then a loop per phase, then a list | `userPhases`; `adviceBytes/128`; `List.range numChallenges` |
| lookup-m, perm-z, trashcan, quotient walks | optional; loop | section `byteLen / 128` |
| lookups | list induction; loop + one body per lookup | `L.lookups`; `helpers.byteLen/128` |
| evals spill, q_evals run | loop | `evals.byteLen/32`, `qEvals.byteLen/32` |
| 11 squeezes | fixed text | |
| four helpers | fixed text, loop-free | |

- **[M]** The schedule is data: `tpEvents`. At F1 its read projection equals the layout's slot list
  (72 slots: 21 G1, 51 scalars; `tp_events_slots_F1`); with `numLookups := 0` it does not, and the
  emitter prints 42 statements instead of 44 (`tp_events_slots_falsifier`).
- Invariant: one, shared by all walks (`g1walk_loop_sem`): the transcript buffer and the walk window
  both hold the calldata bytes read so far, each frame passed `g1WordsOk`, three cursors advanced.
  Post of the block: `TpPost` = `Frame`, `success = 1`, `BaseInv`, `rawDecode … isSome`, `MirrorAt`,
  `XcriptSlots`. **[M]** `tp_blockSim` is proved from `tp_computes`, `tp_agrees`, `tp_poison`.
- Risk 1: the inliner over a symbolic list. `inlineScan_append` (GEN.4) is needed before any group can
  be isolated; `inline_append` (`ProgramLemmas.lean:27`) is a sorry.
- Risk 2 **[I]**: the transcript buffer. Nothing read so far bounds the longest absorb run by the size of
  the transcript region, or separates that region from the commitment windows (PG-TPBUF).
- Risk 3: the emitter's inputs come from the model (`parserFactsOfPlan`), `rawSlots` from the plan
  (PG-PARSER).
- Cards: 10.

### QuotientLin (ROW.Q) — `GenAst.lean:840-864` today

| part | kind | status |
|---|---|---|
| linearization scope | fixed text; one loop, bound `k` | **[M]** `qlin_split_loop` stated |
| `q_program_fail`, `q_pow5` | fixed text (helpers under three flags) | no AST emitter (OBJ.14) **[R]** |
| interpreter template (953 tokens at F1) | **interpreted**: a loop whose guard and `switch` read the program bytes in memory | no AST emitter (OBJ.15) **[R]** |
| six generated-line families (5,431 tokens at F1) | list inductions over `R.qblocks` | no AST twin of the block producers; not carded **[R]** `design/object.md:70` |

- Invariant (route B): the Yul operand stack and program counter refine the reference VM's state on a
  memory related by the frame valuation; contract shape `QInterpRefines`.
- Builder correctness in scope: `Qvm.lean:631, :698, :713, :768, :995`; `QvmFold.lean:338` (refuted by
  the file; **[M]** `identityCorrespondence_of_bridge_fixed` proved with the missing hypothesis),
  `:376`, `:434`.
- Risk: the largest of the plan. The object does not exist as an emitter; `qvm_compile_correct_stream`
  assumes `streamIsInterpretedOnly`, which F1 fails (it has inline and native items **[R]**
  `object/Quot1.lean`).
- Cards: 25–35 **[I]**.

### PCS (ROW.PCS) — `GenAstDispatch.lean:131`, `GenAstPcs.lean:131-611`

| block | kind | induct over / bound |
|---|---|---|
| 1 rotation walk | two list inductions, straight-line | `intRangeInclusive 1 maxRot`; reversed `intRange minRot 0` |
| 2 x1 powers | loop | `nbX1Powers − 1` |
| 3 per point set | list induction; rolled arm has a loop | sets; commitments in the set |
| 4 `f_eval` | list induction over reversed sets; lists over points; `scalar_inv` per set | sets; points |
| 5 fused MSM | nested `foldlM` with one pair counter; `pcsLinExpansion`; one `staticcall` | sets × commitments; limbs; selectors |
| 6 pairing inputs | fixed text, four scratch numerals, four `staticcall`s | |

- **[M]** `pcs_slice_of_ok`, `pcs_slice_of_fault`: the slice is the flattened blocks, or empty when the
  emitter faults. **[M]** At F1 today the emitter returns 8 blocks, 225 statements (the remark "pcs is
  EMPTY at the plan level", `Blocks.lean:181`, is stale).
- Invariant: for the MSM staging, the pair counter and the scratch image; the coverage invariant
  (every G1 window `MirrorAt` names is an operand of a G1MSM on every path that exits with
  `success = 1`), from which `decode_exists` gives the decoding.
- Risk: the coverage invariant is a fact about `finalMsmShape` and `commitmentsBySet`, not about Yul; it
  is not stated anywhere **[I]**. `x = 0` needs `hasMultiPointSet`.
- Cards: 12–14 **[I]**.

### FinalPairing (ROW.FP) — `GenAst.lean:649-654`, helper `:265-292`

- Fixed text. No loop, no list. Already written for every `R` in `Blocks/FinalPairing.lean`.
- **[M]** `fp_poison` proved from the tree's `fp_stmt_steps` (a registered sorry).
- Risk: `ec_pairing_contract` (`:314`) is false as stated (RV-23); `ec_pairing_sem` restates it over the
  bytes in memory. PG-G2SLOTS.
- Cards: 3.

### Helpers (HLP.1)

- **[M]** For every render the scope defines the eight helpers with the bodies their emitters print,
  inlined on their own: `helpers_eq`, `fail_is`, `batch_invert_is`, `helpers_are`. No premise.
- `batch_invert` (`GenAst.lean:465-542`): 34 statements, two loops, bound = batch words. Summary
  `batch_invert_summary`; forward pass `bi_forward_loop`.

### Totality (TOT.1)

- Step 1 for every `R`: a `GasFree` clause (`gasFreeScan`, not vacuous: two `decide` examples) and
  `runBody_gas_oblivious`. **[R]** No emitter prints `Op.gas`; no clause of `Valid` says so (PG-GAS).
- **[I]** Liveness is asked from `LivePre`: clean up to `.quotient`, clean-or-poisoned from `.pcs`. The
  quotient interpreter's loop is driven by memory, and a poisoned boundary says nothing about memory.
- **[M]** `live_append`, `stmts_append_stop`, `slices_live`, `total_correct` proved.
- Cards: 9.

## 3. Premise gaps (typechecked `def`s in `GeneratorRows.lean` §2; never a hypothesis of a row)

| id | missing fact | rows | supplied by |
|---|---|---|---|
| PG-SIMPINS | codec laws and `hasMultiPointSet` | all | headline laws + `programOk` (**[M]** refuted from `Valid`) |
| PG-EXIT | `R.ExitOk` | conjunct 3 | `ValidV3.exitDiscipline` |
| PG-NOSHADOW | `R.consts.lookup "r" = none` | all arithmetic | `noShadowB` |
| PG-CONSTS-LAG / -TP | table = plan-view addresses (6 + 23 names stated; more not `PlanView` fields) | lagrange, parser, prefix | `constsCoherent` (OBJ.4) |
| PG-FRMOD | `R.consts.lookup "FR_MODULUS" = some p` | all arithmetic | `constsCoherent` |
| PG-PARSER | `parserFactsOfPlan` agrees with the layout (`tp_events_slots`) | parser | lemma about `generateVerifierFromPlan`, or a clause |
| PG-TPBUF | transcript region large enough and disjoint | parser | layout lemma (not stated) |
| PG-NEGLAG | `2 ≤ R.pv.numNegLagranges` | lagrange | `WellFormed`? to be checked |
| PG-PCS-EMIT | `computationsAst … = .ok blocks`, `blocks ≠ []` | pcs | lemma, or a clause |
| PG-G2SLOTS | `fpG2Slots R` | finalPairing | `PayloadAgrees` |
| PG-G1ID | `0x80 ≤ ptrAddr g1IdentityMptr` | prefix | `g1IdentityAbove` |
| PG-GAS | `GasFree (R.prog vkAddr 0)` | totality | new `programOk` clause, or emitter lemma |
| PG-Q-OBJECT | AST emitters for the quotient region | quotientLin | OBJ.14, OBJ.15, block-producer twins |
| (RECON.2) | `cd.size < 2^256` in `Frame` | vkLoading, prefix | `EntryFrameV3.cdSize` |

**[M]** At F1 every table gap holds (`pgLagRows`, `pgTpRows` print `[]`; PG-NOSHADOW, PG-NEGLAG,
PG-G1ID, PG-FRMOD print `true`), so each is a real clause and not an impossibility.

## 4. Rows believed false as stated today

1. `rows_correct`'s first conjunct (`SimPins R`): **[M]** refuted whenever `Valid` is inhabited.
2. `pcs_blockSim` for a render whose PCS emitter faults: **[M]** the slice is `[]`; **[I]** the exit then
   claims a decoding the run never established.
3. `lag_blockSim` for `numNegLagranges < 2`: **[I]**.
4. `vk_blockSim` on calldata padded to `2^256` bytes: **[R]** RECON.2 step 1 (not re-derived here).

## 5. Not done

- No child is proved beyond normal forms and compositions. No loop has been closed with GEN.3.
- No Lean statement for: the four parser helper summaries, the instance and evals loops, the two
  parser list inductions, PCS blocks 1, 3, 4, 5, 6, the coverage invariant, `scalar_inv`, the backward
  pass of `batch_invert`, the frame card of lagrange, the per-block liveness lemmas. Their cards are
  STATEMENT cards.
- The quotient numerator: only the contract shape and the linearization loop are stated.
