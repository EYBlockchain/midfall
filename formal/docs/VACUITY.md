# VACUITY — non-inhabitation audit

**Branch:** `t/VACUITY` (from `formal/baseline` `881f780`).
**Scope:** the V3 root and its bundles/rows, the V3 statement surface and `EndToEndV3`, the
generator/certified path (D2), QVM, and widening C0–C7 — plus the one `VACUOUS` row in
`formal/SORRY.md`.
**Question:** a proof only reveals a bug if its statement is non-vacuous and its hypotheses are
inhabited. The register's `0 REFUTED / 1 VACUOUS` is a statement about *negations found by the
kernel*, not about inhabitancy. This report audits the second property.

Status vocabulary (the brief's):

| status | meaning |
|---|---|
| `INHABITED` | a term/theorem/KAT witness of the statement or of its hypothesis bundle exists |
| `CONDITIONAL` | no known witness, but the statement/hypothesis is not refuted |
| `VACUOUS` | a hypothesis is refuted/uninhabited for every instance, so the statement is true ex falso |
| `FALSE` | the negation is proved (a falsifier exists or was landed by this audit) |
| `UNKNOWN` | not enough evidence either way |

**Method.** `#check`, `#print axioms`, `#leaf_status`, `#cone_avoids_decls`, `#cone_sorries`,
the existing KATs (`#eval`/`decide`/`native_decide`) and the W12 witnesses/falsifiers already in
`Instances/`. The new witnesses of this audit are in
`formal/Midfall/Instances/VacuityWitnesses.lean`; they are not in the root cone.

---

## 0. Summary

**The headline is now non-vacuous in the generic sense, but still vacuous at F1.** B4's
`exists_validV3` (`Instances/ValidV3SyntheticInhabitant.lean`) proves `∃ R, ValidV3 R` at a
synthetic render built from a real `generateAll` run; the two codec fields are chosen from the
payload words and the payload is normalized. F1 (`poseidonRender`) still *refutes* `ValidV3`
through `generated`, and the re-sourced `f1GeneratedRender` is now proved **not** `ValidV3`
(`f1GeneratedRender_notValidV3`); its exact residual is `PayloadPointHalf` (real commitments and
`sG2gen`). Therefore:

| headline | status | one-line reason |
|---|---|---|
| `lowering_correct` (generic) | **NON-VACUOUS (synthetic) / CONDITIONAL** | `exists_validV3` inhabits the hypothesis at a synthetic render; the F1-real instance still needs `PayloadPointHalf` |
| `lowering_correct` at F1 | **VACUOUS** | `¬ ValidV3 poseidonRender`, proved (`f1_ValidV3_false`) |
| `lowering_sound` (generic / F1) | **CONDITIONAL / VACUOUS** | same hypothesis; the synthetic `ValidV3` is available |
| `EndToEndV3` (generic / F1) | **CONDITIONAL / VACUOUS** | synthetic `ValidV3` exists, but `PrepareLogSlots`/`hside` are still missing; at F1 `hcodec : G1CodecLawsV3 g1CodecZ` is false |
| `lowering_correctW` (C0–C7) | **CONDITIONAL** | no `ValidW`/`EvalContracts` witness; F2 importer absent; `model_quotientMode` still sorry |
| `generator_correct_V3` (D2) | **CONDITIONAL** | `SupportedInput`/`Generates` have no witness; 36 CERT leaves |
| `end_to_end_acc_complete` (V1) | **VACUOUS** | `hc : LoweringCorrect S product` is refuted by `not_LoweringCorrect` |

The root's 11 sorried leaves are `OPEN`, not `VACUOUS`, in the register because the register only
looks for a *proved negation of a hypothesis*. A hypothesis with no inhabitant at all is invisible
to that scan. That is the central gap this report records.

---

## 1. Root, composition, and bundles

| statement | file:line | hypotheses it needs | status | evidence / minimal witness or repair |
|---|---|---|---|---|
| `lowering_correct` | `LoweringV3/GeneratorTheorem.lean:70` | `hR : ValidV3 R` | **CONDITIONAL** (F1 **VACUOUS**) | `gap_lowering_correct_witness_unexhibited` (`:100`) names the gap; `lowering_correct_needs_valid` (`Instances/StatementsV3Falsifiers.lean:526`) proves `hR` is load-bearing by dropping it and refuting the result at `bumpInst R`; `f1_ValidV3_false` (new) refutes F1; `exists_validV3` (new) inhabits the hypothesis at a synthetic render, so the generic root is non-vacuous. The F1-real instance still needs `PayloadPointHalf`: `f1GeneratedRender` is now proved not valid (`f1GeneratedRender_notValidV3`), and B3 must re-source the 19/8 commitments and `sG2gen`. Owner: B4 + B3. |
| `lowering_sound` | `LoweringV3/GeneratorTheorem.lean:78` | `hR : ValidV3 R` | **CONDITIONAL** (F1 **VACUOUS**) | same `hR`; its row cone is `sim_rows`, so the witness is the same missing `ValidV3`. |
| `LoweringEquivalenceV3` | `LoweringV3/Statements.lean:3863` | `hdep`, `hentry`, `hpc`, `hcodec` hidden under the definition | **CONDITIONAL** | `EndToEndV3`'s four conjuncts are real (see `returns_of_inhabited`); no joint inhabitant of the world/frame/codec set exists. At F1 `hcodec` is false (`f1_codecLawsV3_false`). |
| `lowering_equivalenceV3_of_rows` | `LoweringV3/Composition.lean:260` | `hR : ValidV3 R`, `SimRowsV3`, `ProgRowsV3` | **CONDITIONAL** | proved glue; the two bundles below are the missing inhabitancy. |
| `sim_rows` | `LoweringV3/Rows.lean:254` | `ValidV3`, `G1CodecHeadlineLaws`, `Eip2537.Holds`, `SoundSide` | **CONDITIONAL** | proved glue over 7 rows; `BlockSim` leaves (see §2). W12 family witness is the named gap, not a term. |
| `prog_rows` | `LoweringV3/Rows.lean:268` | `ValidV3`, codec, `Holds`, `LeanAccepts`, `CompleteSide` | **CONDITIONAL** | same; 7 `BlockProgS` leaves. |
| `twoOutcomesV3_of_valid` | `LoweringV3/Composition.lean:192` | `ValidV3` | **CONDITIONAL** (F1 **VACUOUS**) | proved from `NoWriters` + `ExitDiscipline`; `twoOutcomes_hypotheses_together` (`Composition.lean:318`) is a toy witness, not a render witness. |
| `rejectsV3_of_sims` | `LoweringV3/Composition.lean:205` | `ValidV3`, `SimRowsV3` | **CONDITIONAL** | glue proved; depends on `prefix_simV3` and the rows. |
| `completeV3_of_progs` | `LoweringV3/Composition.lean:226` | `ValidV3`, `ProgRowsV3` | **CONDITIONAL** | glue proved; depends on `prefix_progV3` and the rows. |
| `totalV3_correct` | `LoweringV3/Totality.lean:1028` | `ValidV3` | **CONDITIONAL** | proved from `prefix_live` and four `block_live` leaves; no `ValidV3` witness. |

**Root at F1.** `f1_ValidV3_false` (`Instances/VacuityWitnesses.lean`) proves
`¬ ValidV3 poseidonRender` from `f1_generated_obstruction_at_F1` (`Instances/ValidV3InhabitationF1.lean:323`),
which is `poseidonValid_generated_not` (`Instances/PoseidonValid.lean:935`). `f1_root_has_no_witness`
(new) states the consequence. So every theorem with `hR : ValidV3 poseidonRender` is true at F1
*for the wrong reason*: its hypothesis is false, not its conclusion established.

**Root is not *universally* vacuous.** `lowering_correct_needs_valid` proves the root without `hR`
is false at `bumpInst R`; this is the W12 falsifier that makes `hR` load-bearing. It does not
exhibit a `ValidV3` render. The exact missing term is `ValidV3 f1GeneratedRender` (or any other
render); the contract is not to add a hypothesis, so the only repair is a real witness, not a
statement change.

---

## 2. Rows, prefixes, and totality

### 2.1 The fourteen row statements

The row shape is `BlockSim`/`BlockProgS` over `StageInv` (`LoweringV2/Stages.lean:171,222,243`).
Every row is an implication from a `StageInv` pre, and every row's *statement* is non-vacuous only
if some state satisfies that pre. The table distinguishes the proof status from the pre-inhabitation
status.

| row | file:line | top-level hypotheses | proof | pre-inhabitation | status |
|---|---|---|---|---|---|
| `vk_blockSim` | `LoweringV3/Rows.lean:56` | `ValidV3`, `G1CodecHeadlineLaws`, `Holds`, `Hash`, address, cd, gas | **PROVED** (`VkClean.vk_blockSimV3`) | no `StageInv .start`/`.vk` term at a real render | **CONDITIONAL** |
| `vk_blockProgS` | `LoweringV3/Rows.lean:95` | same + `LeanAccepts`, `CompleteSide` | **PROVED** (`VkClean.vk_exists_run` + `vk_all_normal`) | same | **CONDITIONAL** |
| `tp_blockSim` | `LoweringV3/Rows.lean:110` | `ValidV3`, codec, `Holds`, H, addr, cd, g | sorry | no `StageInv .transcript` term | **CONDITIONAL** |
| `tp_blockProgS` | `LoweringV3/Rows.lean:118` | same + acceptance | sorry | same | **CONDITIONAL** |
| `lag_blockSim` | `LoweringV3/Rows.lean:129` | `ValidV3`, codec, `Holds`, H, addr, cd, g | sorry | no `StageInv .lagrange` term; **in accumulator mode `StageInv` at `.lagrange` is unsatisfiable** (`WideningStages.stageInv_false_of_acc`) | **CONDITIONAL** (and **VACUOUS** on accumulator renders) |
| `lag_blockProgS` | `LoweringV3/Rows.lean:138` | same + acceptance | sorry | same | **CONDITIONAL** |
| `pcs_blockSim` | `LoweringV3/Rows.lean:148` | same | sorry | no `StageInv .pcs` term | **CONDITIONAL** |
| `pcs_blockProgS` | `LoweringV3/Rows.lean:157` | same + acceptance | sorry | same | **CONDITIONAL** |
| `fp_blockSim` | `LoweringV3/Rows.lean:168` | same | sorry | no `StageInv .pairing` term | **CONDITIONAL** |
| `fp_blockProgS` | `LoweringV3/Rows.lean:177` | same + acceptance | sorry | same | **CONDITIONAL** |
| `q_blockSim` | `LoweringV3/QuotientRows.lean:236` | `ValidV3`, codec, `Holds`, `SoundSide` | sorry | no `StageInv .quotient` term | **CONDITIONAL** |
| `q_blockProgS` | `LoweringV3/QuotientRows.lean:249` | `ValidV3`, codec, `Holds`, `LeanAccepts`, `CompleteSide` | sorry | same | **CONDITIONAL** |
| `tr_blockSim` | `LoweringV3/Rows.lean:207` | no `ValidV3`; only R/H/addr/g/cd | **PROVED** (`tr_sound_clean_noarm`) | pre is `StageInv .pairing`; no term | **CONDITIONAL** |
| `tr_blockProgS` | `LoweringV3/Rows.lean:229` | `ValidV3`, H, addr, cd | **PROVED** (`tr_blockProgress` + `returnMptr_of_valid`) | same | **CONDITIONAL** |

`qlin_split_loop` (`LoweringV3/QuotientRows.lean:296`) has a concrete pre (k, x, r locals) and a
proved base case (`qlin_split_loop_witness_base_case`, `:618`); its pre is **INHABITED** and its
pre-clause is load-bearing (`qlin_split_loop_falsifier_pre_pins_x_pow_2i`, `:654`). The inductive
step is the remaining leaf; status **CONDITIONAL** for the full loop, **INHABITED** for the pre.

### 2.2 What the W12 witnesses actually prove

| witness/falsifier | file:line | what it establishes | what it does **not** establish |
|---|---|---|---|
| `stageInv_start_not_vacuous` | `LoweringV2/Stages.lean:1861` | `StageInv .start` is not `True`: empty env fails `success = 1`. | no state satisfying `StageInv .start`; only a failure at the empty env |
| `mid_start_not_vacuous` | `LoweringV2/Stages.lean:1870` | neither arm of `Mid .start` is trivial at the empty env | same |
| `mirror_start` | `LoweringV2/Stages.lean:1882` | `Mirror .start = True`, so the mirror conjunct does not block the prefix | it does not supply the other five conjuncts of `StageInv` |
| `stageInv_start_conjuncts` | `LoweringV2/Stages.lean:1923` | the five live conjuncts at `.start` from `StageInv` | no inhabitant |
| `invSat_start` | `Instances/InvFixture.lean:215` | `Inv .start` at the toy `bigS`/`bigV`/`honestSt` | not `StageInv`: no `Frame`, `LeanRaw`, `Agree`; different render/model |
| `invSatKats_ok` | `Instances/InvFixture.lean:205` | `Inv` at every checkpoint, plus `.quotient`/`.pcs`/`.pairing` at the filled toy snapshot | a KAT, not a `StageInv` witness |
| `finSim_refutes_empty` | `LoweringV2/Stages.lean:1890` | `FinSim` is not "any outcome" | only a falsifier of a weakening |
| `exitSim_refutes_normal_traceReturn` | `LoweringV2/Stages.lean:1902` | the terminal sim arm rejects `.normal` | only a falsifier |
| `exitProg_refutes_normal_traceReturn` | `LoweringV2/Stages.lean:1912` | the terminal prog arm rejects `.normal` | only a falsifier |
| `q_blockSim_witness_reverting_block_satisfies_the_post` | `LoweringV3/QuotientRows.lean:569` | the row post is consistent with a real reverting block | its pre is `StageInv`; no pre inhabitant |
| `q_blockProgS_witness_empty_block_reaches_the_post` | `LoweringV3/QuotientRows.lean:600` | the progress post is reachable at `.normal` | pre is `True` in this witness, not `StageInv` |
| `q_blockSim_falsifier_return_is_not_a_halt_arm` | `LoweringV3/QuotientRows.lean:690` | the revert disjunct is load-bearing | no pre inhabitant |
| `q_blockProgS_falsifier_reverting_block_is_not_total` | `LoweringV3/QuotientRows.lean:725` | totality is not the revert arm | no pre inhabitant |

**Finding:** no row has a proved *empty* `StageInv`, and no row has a proved *inhabited* `StageInv`
at a real render either. The W12 family currently establishes non-triviality and falsifiability,
not non-vacuity. `stageInv_false_of_acc` (`WideningStages.lean:362`) proves `StageInv` is empty at
every checkpoint after `.start` for accumulator renders, so the four accumulator-eligible base rows
are **VACUOUS on that class** unless restated over `StageInvW` (which is what C0–C7 do). At V3's
non-accumulator class, `stageInvW_iff_V3` (`WideningStages.lean`) says the two invariants agree,
but it does not create an inhabitant.

**Minimal missing witness (owner A2/A7/A12):** one term
`StageInv R H vkAddr cd k V st` at a render and checkpoint, built from the existing
`poseidonValid_*` clauses plus `Frame`/`LeanRaw`/`Agree`. `f1_deploymentV2` and `f1_entryFrameV3`
(new) supply the `DeploymentV2` and `EntryFrameV3` halves at F1; what remains is the `Inv` +
`LeanRaw` + `Agree` package at the same frame.

### 2.3 Prefix and totality rows

| statement | file:line | hypotheses | status | evidence |
|---|---|---|---|---|
| `prefix_simV3` | `LoweringV3/Composition.lean:118` | `ValidV3`, `DeploymentV2`, `EntryFrame`, calls, gas | **CONDITIONAL** (F1 **VACUOUS**) | proved glue; `hR` missing; `EntryFrame` inhabited (`entryFrame_inhabitedV3`). |
| `prefix_progV3` | `LoweringV3/Composition.lean:138` | `ValidV3`, `DeploymentV2`, `EntryFrame`, `LeanAccepts` | **CONDITIONAL** | same; no `LeanAccepts` at F1 because the codec decodes nothing. |
| `block_live` | `LoweringV3/Totality.lean:853` | `ValidV3` | **CONDITIONAL** | `LivePre` pre; no inhabitant; owner A12. |
| `prefix_live` | `LoweringV3/Totality.lean:980` | `ValidV3`, `EntryFrameV3` | **CONDITIONAL** | `EntryFrameV3` inhabited at F1; `hR` not. |
| `totalV3_correct` | `LoweringV3/Totality.lean:1028` | `ValidV3` | **CONDITIONAL** | glue proved; depends on `block_live` and `prefix_live`. |

`LivePre` (`Totality.lean:833`) is a **new** pre, not `StageInv`; no witness is in the tree. This is
a second row-shape whose inhabitancy is not covered by `InvFixture`.

---

## 3. F1, `ValidV3`, payload, codec, `EndToEndV3`

### 3.1 The F1 facts (the only named render)

| proposition | file:line | status | evidence |
|---|---|---|---|
| `SupportedV2 poseidonRender` | `Instances/PoseidonValid.lean:574` | **INHABITED** | theorem, no sorry; 12 fields. |
| `programOk poseidonRender` | `Instances/PoseidonValid.lean:676` | **INHABITED** | theorem (native-decide axiom). |
| `NoWriters`, `EnvAgrees`, `inputs` | `Instances/PoseidonValid.lean:600,456,327` | **INHABITED** | theorems. |
| `PayloadAgrees poseidonRender` | `LoweringV3/Statements.lean:647` (structure); `PoseidonValid.lean:695` | **FALSE** | 8 of 14 fields proved; `fixedComms`/`permutationComms` are **REFUTED** (`f1_fixedComms_false`, `f1_permutationComms_false`), `g1Base`/`g2Base`/`negSG2` are open/opaque at the placeholder codec. Owner B3. |
| `GeneratedBy poseidonRender` | `LoweringV3/Statements.lean:3549` | **FALSE** | `f1_generated_obstruction_at_F1` (`Instances/ValidV3InhabitationF1.lean:323`); the generator refuses at `quotient.rs:202`. |
| `GeneratedBy f1GeneratedRender` | `Instances/ValidV3InhabitationF1.lean:260` | **INHABITED** | `f1GeneratedRender_generated`; re-sourced plan/qblocks/model from a successful `generateAll`. |
| `ValidV3 poseidonRender` | `LoweringV3/Statements.lean:3587` | **FALSE** | new `f1_ValidV3_false` (`Instances/VacuityWitnesses.lean`), from the `generated` refutation. |
| `ValidV3 f1GeneratedRender` | `Instances/ValidV3InhabitationF1Completion.lean` | **FALSE** | `f1GeneratedRender_notValidV3`; `f1GeneratedRender_validV3_iff_points` reduces it to `PayloadPointHalf`, whose `fixedComms`/`permutationComms` are refuted and whose `g1Base`/`g2Base`/`negSG2` are open. |
| `∃ R, ValidV3 R` (synthetic) | `Instances/ValidV3SyntheticInhabitant.lean:413` | **INHABITED** | `exists_validV3`; real `generateAll` run, synthetic codec fields (`g1zToEip 1`, slot-15 image) and normalized payload. Generic non-vacuity only, not F1 `Done`. |
| `HypothesesInhabitedV3 poseidonRender product` | `LoweringV3/Statements.lean:3968` | **FALSE** | `poseidon_notInhabitedV3` (`Instances/StatementsV3Deploy.lean:532`) via `g1CodecZ_not_headlineLaws`; the non-vacuity gate itself is refuted at F1. |
| `G1CodecHeadlineLaws g1CodecZ` | `LoweringV3/Statements.lean:72` | **FALSE** | `g1CodecZ_not_headlineLaws` (`StatementsV3Deploy.lean:523`); new `f1_codec_headline_false`. |
| `G1CodecLawsV3 g1CodecZ` | `LoweringV3/Statements.lean:83` | **FALSE** | new `f1_codecLawsV3_false`, from the headline law. |
| `G1CodecLawsV3 (withCompressed g1CodecZ comp)` | `LoweringV3/Statements.lean:104` | **INHABITED** | `withCompressed_lawsV3` + an injective 48-byte map; `lawsV3_satisfiable_at_G1z` (`StatementsV3Deploy.lean:558`) is the closed term. |
| `calldataOfV3` returns `.ok` on some data | `LoweringV3/Statements.lean:141` | **INHABITED** | `calldataOfV3_witness_ok` (`Statements.lean:169`, KAT) at the toy `katPlan`/`toyCodec`. |
| `DeploymentV2 poseidonRender f1W keccak256 0` | `LoweringV2/Statements.lean:1119` | **INHABITED** | new `f1_deploymentV2`. |
| `EntryFrameV3 poseidonRender f1W f1Lyt keccak256 fnSigVerifyProof st` | `LoweringV3/Statements.lean:3703` | **INHABITED** | new `f1_entryFrameV3`, via `entryFrame_inhabitedV3` and `poseidonValid_transcriptMptr`. |

The two `ValidV3`-blocker facts are also positive theorems, not prose:

| fact | file:line | status | evidence |
|---|---|---|---|
| `f1_plan_isNotTheGeneratorsPlan` | `Instances/ValidV3InhabitationF1.lean:315` | **INHABITED** | `genFilledOut.plan ≠ poseidonRender.plan`; the generator's `numPointSets = 3` against the raw `0`. It shows a payload-only repair cannot close `generated`. |
| `poseidonValid_decidableHalf` | `Instances/PoseidonValid.lean:782` | **INHABITED** | the five decidable clauses plus the eight scalar payload fields at F1; the remaining blockers are named in its conclusion, not hidden. |
| `poseidonValid_payload_scalars` | `Instances/PoseidonValid.lean:695` | **INHABITED** | 8 of 14 `PayloadAgrees` fields; `poseidonValid_payload_scalars_are_fields` (`:741`) ties them to the structure. |
| `g1CodecZ.ofCompressed? = none` | `Instances/CurveSurface.lean` (`g1CodecZ_laws` vicinity) | **INHABITED** | `rfl`/`simp [g1CodecZ]`; the reason the compressed half is a placeholder and the headline law fails. |
| `withCompressed_lawsV3` | `LoweringV3/Statements.lean:104` | **INHABITED** | the generic positive witness: any frozen-law codec plus an injective 48-byte map satisfies all eight V3 laws. |

**The two frame facts are real.** `f1_deploymentV2` and `f1_entryFrameV3` are standard-three plus
the D-P36a constants and the F1 native axioms named at the foot of
`VacuityWitnesses.lean` (`poseidonModel_isOk`; `f1_entryFrameV3` also
`poseidonValid_transcriptMptr`). They are witnesses for `hdep`/`hc v`/`EntryFrameV3`, not for
`ValidV3` or `hcodec`.

### 3.2 `EndToEndV3` and its premises

`EndToEndV3` is a definition (`LoweringV3/Statements.lean:3991`), not a theorem. The proved
end-to-end results are conditional:

| statement | file:line | hypotheses | status |
|---|---|---|---|
| `end_to_end_forward_of_readSchedule` | `LoweringV3/EndToEnd.lean:109` | `ValidV3`, `LoweringEquivalenceV3`, `DeploymentV2`, `hcv`, `Holds`, `G1CodecLawsV3`, `hn`, `hside`, `hsched` | **CONDITIONAL** |
| `end_to_end_backward` | `LoweringV3/EndToEnd.lean:449` | same minus `hsched` | **CONDITIONAL** |
| `end_to_end_of_readSchedule` | `LoweringV3/EndToEnd.lean:554` | the two above | **CONDITIONAL** |
| `readScheduleAgrees_of_prepareLogSlots` | `LoweringV3/EndToEnd.lean:702` | `PrepareLogSlots R` | **CONDITIONAL** |
| `end_to_end_of_prepareLogSlots` | `LoweringV3/EndToEnd.lean:720` | `PrepareLogSlots R` + the full `EndToEndV3` premise set | **CONDITIONAL** |
| `PrepareLogSlots` | `LoweringV3/EndToEnd.lean:678` | — (a `def : Prop`) | **CONDITIONAL**; no proof and no witness; `gap_readScheduleAgrees` (`:785`) names the exact residual. |
| `hside` (the `∀ cd` side-condition) | `LoweringV3/Statements.lean:3991` | — | **CONDITIONAL**; no term. `calldataOfV3_witness_ok` gives `.ok`, but not `SoundSide`/`CompleteSide`. |
| `hcodec` at F1 | — | `G1CodecLawsV3 poseidonRender.E.g1` | **FALSE** (`f1_codecLawsV3_false`) |
| `hpc` at F1 | `Instances/HoldsFinal.lean:57` | `Eip2537.Holds` | **INHABITED** for a product (`holds_exhibited`), but the `EndToEndV3` instance still fails on `hR`/`hcodec` |

`EndToEndV3` at F1 is **VACUOUS** (two independent false hypotheses, `hR` and `hcodec`), not merely
conditional. There is **no V3 consumer of `end_to_end_acc_complete`**: `#cone_avoids_decls
Midfall.LoweringV3.lowering_correct [Midfall.Lowering.end_to_end_acc_complete, ...]` prints
`ok (2 constants)`, and a repository grep finds only docs. The V3 root also avoids
`EndToEndV3`/`end_to_end_of_readSchedule` (`#cone_avoids_decls ...` prints `ok (2 constants)`), so
the conditional end-to-end layer is a D1 deliverable, not something the root's vacuity depends on.

---

## 4. Leaf premises

### 4.1 Lagrange

`lag_agrees` (`LoweringV3/LagrangeRows.lean:3515`) takes:

* `hR : ValidV3 R`; `hm : 2 ≤ R.pv.numNegLagranges`; `hn : 1 ≤ R.pv.numInstances`;
* `hl : snapshotLagrangeStep ... = .ok l`; `hxn`; `hinst : s2.alg.instanceEvals.getD 0 #[] = inst`;
* `hW : LagRel ...`; `bf`, `hbf`; `Lw`; `hval`; `hBlindW`; `hInstEval`.

`lag_agrees_hval` (`:3565`) removes `hval`/`hBlindW`. The `xn`/`lLast`/`l0` projections are proved
from `hR`/`hW` (`lag_agrees_xn` `:3111`, `lag_agrees_lLast_l0` `:3242`), and `lBlind` from the
opaque-list leaves (`lag_agrees_lBlind` `:3477`). Remaining inhabitancy problems:

* `hR : ValidV3 R` — no witness (root blocker).
* `hinst` — the snapshot/query linkage `s2.alg.instanceEvals.getD 0 #[] = inst` is **not a
  theorem**; the header at `:3203` calls it a missing leaf premise, not a row hypothesis.
* `hInstEval` — `∀ e, l.instanceEval = some e → W.instEval = frWord e`; no term. It is an
  implication, so it is satisfiable if `l.instanceEval = none`, but at an actual `.lagrange`
  snapshot with an instance evaluation it is the load-bearing instance conjunct.
* `hm`, `hn` — both true at F1 (`negLagranges = 9`, `numInstances = 1`), but F1 has no `ValidV3`.
* At an accumulator render, `StageInv .lagrange` is empty (`stageInv_false_of_acc`), so a row using
  this leaf there is vacuous until C4/C5 restate it over `StageInvW`.

**Status:** `CONDITIONAL`; **missing exact terms:** `hinst` and `hInstEval` at a real row, plus a
`ValidV3` render. Owner A4/A5 (and B4 for `hR`).

### 4.2 `PrepareLogSlots` / `PresWidthSeq` / KZG partition

* `PresWidthSeq` (`EndToEnd.lean:671`) is a `def : Prop`; `presWidths_prepare` supplies the
  `PresWidths` fact, but no `PresWidthSeq` term is in the tree. **CONDITIONAL.**
* `PrepareLogSlots` (`:678`) is the exact missing bridge. It is **CONDITIONAL**; no proof, no
  witness. `decodeRust_slots_eq_logWidths` and `readScheduleAgrees_of_prepareLogSlots` reduce it to
  `decodeRust`, but the protocol refinement itself is absent.
* `KzgPartitionBridge` (`:691`) is **FALSE as stated**: `kzgPartitionBridge_false_at_x0`
  (`:762`) proves at `x = 0` the Halo2 partition has 1 point set while the generator's has 2.
  `ChallengesGood.xNonzero` (`Lowering/Inv.lean:704`) is the added clause that excludes the
  collapse, but `KzgPartitionBridge` itself does not carry it. Minimal repair: add
  `xNonzero`/`rotationDistinct` to the bridge's hypotheses (a statement repair, not a row
  hypothesis); owner D1/audit. The existing falsifier is a W12 computation, so this is a `FALSE`
  row rather than a missing witness.
* `ChallengesGood` (`Lowering/Inv.lean:692`) is **CONDITIONAL**: `xNotRoot` and `xNonzero` have no
  witness at a real snapshot. `CompleteSide` (`LoweringV2/Statements.lean:1186`) quantifies over it;
  at F1 no snapshot is produced because `LeanAccepts` is false at the placeholder codec.
* `rotationDistinct` — D-GATE6 is signed but **not landed** in this tree (grep finds no
  `rotationDistinct` declaration). **UNKNOWN**; when it lands it belongs in `ChallengesGood`, not
  in a row.

### 4.3 Semantic leaves

| statement | file:line | status | evidence |
|---|---|---|---|
| `runBody_mono` | `LoweringV3/Statements.lean:3824` | **CONDITIONAL** | sorry; the statement is not vacuous: the identity call relation and any run inhabit its `hcc`/`h`, but no proof. Owner A2/ST.13. |
| `BodyTotal` | `LoweringV3/Statements.lean:3803` | **CONDITIONAL** | `GasTotal` is inhabited (`gasTotal_ofFun`, `:3794`), but no `BodyTotal` term at a render. |
| `TotalV3` | `LoweringV3/Statements.lean:3917` | **CONDITIONAL** | inherited from `ValidV3`/`EntryFrameV3`/`hcodec`; `totalV3_correct` is only conditional on `ValidV3`. |
| `SoundSide` | `LoweringV2/Statements.lean:1177` | **CONDITIONAL** | `soundSide_of_leanAccepts` (`LoweringV3/Statements.lean:3946`) gives it from `LeanAccepts`; at F1 `LeanAccepts` is false because `ofCompressed? = none`, so the only F1 route is the vacuous "no decode" one. |
| `CompleteSide` | `LoweringV2/Statements.lean:1186` | **CONDITIONAL** | no witness; `ChallengesGood` is its only live clause. |
| `GasFree` | `LoweringV3/Statements.lean:3164` | **CONDITIONAL** | `gasFree_of_valid` (`Totality.lean:756`) proves it from `ValidV3`; no `ValidV3` witness. At F1 the `CertMeasure` report is a KAT, not a theorem. |
| `GasTotal` | `LoweringV3/Statements.lean:3792` | **INHABITED** | `gasTotal_ofFun` (`:3794`) and `gasTotal_any`; `not_gasTotal_none` is the falsifier. |

---

## 5. Generator / certified path (D2)

The D2 tree is `t/D2` at `3253c5c` (not this baseline). It adds
`Midfall/Generator/Certified.lean`, `Instances/CertMeasure.lean`, `Instances/CertProbes.lean`, and
42 registered sorries; the register there is **115 declarations / 11 ROOT**, not 73/11. This audit
reads those files but does not claim their 42 leaves are proved.

| statement | file:line on `t/D2` | status | evidence / missing term |
|---|---|---|---|
| `GenInput` (structure) | `Generator/Certified.lean:66` | **UNKNOWN at F1** | the type is inhabited in principle (SRS, codecs, config can be supplied), but no `GenInput` term for F1 exists in either tree. The `srs : ParamsKZG` and `VkPointCodecs` fields are not read from the F1 bundle by any landed term. |
| `SupportedInput` | `Generator/Certified.lean:182` | **CONDITIONAL** | input-only, not refuted; no term. Its `g1Codec`/`g2Codec` fields require an encoder-agreement law, and `CertProbes` says `v3_planMeta` and `v3_cdBound` are **output** obligations, not consequences of `SupportedInput`. Owner D2. |
| `Generates` / `generate` | `Certified.lean:139,128` | **UNKNOWN** | no run of `generate` returning `.ok` on a real key. The only positive run in the tree, `genFilledRun_isOk` (`ValidV3InhabitationF1.lean`), is `generateAll` at the filled payload — not the whole `generate`, and not a real SRS. |
| `generate_spec` | `Certified.lean:157` | **INHABITED (conditional)** | proved with no sorry, but its `Generates gi o` hypothesis has no witness. |
| `generator_certified` | `Certified.lean:540` | **CONDITIONAL** | body has no sorry of its own; depends on the 42 section-3 leaves (`v3_planMeta`, `v3_cdBound`, `payload_g1Base`, ...). No `#cone_sorries` green claim in this baseline. |
| `generator_correct` | `Certified.lean:612` | **CONDITIONAL** | hypothetical-root form; the root is a binder. |
| `generator_correct_V3` | `Certified.lean:622` | **CONDITIONAL** | uses the real `lowering_correct`, which is `CONDITIONAL` at F1, plus `generator_certified`. |
| `v3_planMeta` | `Certified.lean:388` | **CONDITIONAL** | CERT.1 suspect: final vs intermediate memory layout; `PlanMetaStable` is a candidate clause, not an edit; owner CERT.1/CERT.4. |
| `v3_cdBound` | `Certified.lean:423` | **CONDITIONAL** | CERT.1 suspect: no generator check bounds `proofEnd`; `CdBoundCandidate` is a candidate output clause; owner CERT.1/CERT.6. |
| `Done` | evidence `T7.lean:756`; **no V3 `Done` in tree** | **VACUOUS at F1** (the evidence shape) / **UNKNOWN** (V3) | `not_done_today` (`T7.lean:766`) refutes `Done` because `valid : poseidonRender.Valid` is `poseidonRender_notValid`; `not_done_today'` (`:813`) refutes it independently through `artifact.whole`. A V3 `Done` must use `ValidV3`, and `f1_ValidV3_false` gives the same refutation; landing it without changing `Done` would be a vacuous definition, not a witness. Owner DG.4/D2. |

**CERT.1 probes.** `CertProbes.planMeta_of_stable` and `cdBoundB_of_candidate` are
**INHABITED** conditional lemmas: they show the candidate clauses are sufficient, not that the
candidate clauses hold. `PlanMetaStable` and `CdBoundCandidate` are **CONDITIONAL** statements
with no term. `CertMeasure.report` is a `#eval` measurement (not a gate, and it has no `-- expect`
annotation); its output is evidence only, not a theorem. The two CERT.1 suspects
(`v3_planMeta`, `v3_cdBound`) remain **CONDITIONAL** and are the exact reason `generator_certified`
cannot yet be non-vacuous.

**The exact D2 question.** `SupportedInput` is *not known to be inhabited at F1*, and `generate` is
*not known to return `.ok` on any real key*. The code sets `SupportedInput`'s field list, but the
only executable generator run in the tree is `generateAll` on `vkFilled`/`genFilledOut`
(`ValidV3InhabitationF1.lean`), which skips `generateVk` and the SRS. The minimal witness to land
is `f1GenInput` + `f1SupportedInput` + a proof `generate f1GenInput = .ok f1CertOut`; the first two
are D2's statement work, the last is the real-key run D2 asks for.

---

## 6. QVM

| statement | file:line | hypotheses | status | evidence / missing term |
|---|---|---|---|---|
| `qvm_compile_correct_identity` | `Lowering/Qvm.lean:623` | `RecognizersSound`, `exprBounded`, `hemit`, `hconsts`, `hcompact`, `hseg` | **CONDITIONAL** | the corrected segment `[9, 0]` and its value are exhibited (`identityRefutation_corrected_conclusion`); `hseg`/`hcompact` at a builder plan have no term. |
| `qvm_compile_correct_certifier` | `Qvm.lean:693` | `hbounded`, `hconsts`, `hbuild`, `CacheConsistent` | **CONDITIONAL** | `itemStarts_matchesCertifierWalk_ok` (`:4153`) is a KAT for `threeIdentityPlan`; no theorem. |
| `qvm_compile_correct_program` | `Qvm.lean:709` | same + `vk` | **CONDITIONAL** | same; seed/entry point is not inhabited by a term. |
| `builder_segments_total` | `Qvm.lean:996` | `hbuild`, `hbounded`, `hconsts`, `hstart`, `hseg`, `mem` | **CONDITIONAL** | `hstart` is nonempty at the three-identity KAT (`itemStarts_matchesCertifierWalk_ok`), but `hseg` and the no-fault conclusion are unproved. |
| `qvm_validated_noBoundsFault` | `QvmNoBounds.lean:102` | `hvm`, `hq`, `hmodel`, `hvalidated`, `hconsts`, `hstart`, `hseg`, `hf` | **CONDITIONAL — and potentially VACUOUS** | `validator_noOOB_onTheRealPlan_ok` (`Qvm.lean:4174`) is a KAT that every segment of the real plan evaluates without fault. If `builder_segments_total` lands, `hf : eval = .error f` is empty for every builder segment, so the theorem is true ex falso. The row should either quantify over an actual validator rejection or name the no-fault fact as its content; do not weaken the statement to hide this. Owner QVM/A8. |
| `QInterpRefinesSegment` | `QuotientInterp.lean:1183` | `s.inWindow`, `QWindowNoWrap`, `QTableAgrees`, `QSegmentStackSafe`, `QPrologueStart` | **CONDITIONAL** | it is the replacement for the refuted `QInterpRefines`; `qinterpRefines_qvmLoop_row_is_false` (`QuotientRows.lean:1037`), `qBadSegment`, `qNegSegment` are the falsifiers. The four caller clauses are individually satisfiable (`qBadSegment_inWindow`, `QTableAgrees_default`, `qfix_witness2_*`), but not jointly at a real compiled segment. |
| `q_blockSim` / `q_blockProgS` | `LoweringV3/QuotientRows.lean:236,249` | `ValidV3`, codec, `Holds`, `SoundSide`/acceptance | **CONDITIONAL** | same `StageInv` problem as all rows; `qlin_split_loop` is the only leaf whose pre is concretely inhabited. |
| `QInterpRefinesSegment_qvmLoop` | `QuotientRows.lean:1570` | — | **UNKNOWN** | a `def : Prop`; no witness. |

**Verdict:** the QVM rows are statement-conditional, not vacuous, *provided* the builder/segment
hypotheses are inhabited. `validator_noOOB_onTheRealPlan_ok` is the KAT that says the intended
fixture is non-degenerate; `qvm_validated_noBoundsFault`'s `hf` is the one hypothesis that may
become empty once the builder totality lands. That is a finding, not a proof hole.

---

## 7. Widening (C0–C7)

| statement | file:line | status | evidence / missing term |
|---|---|---|---|
| `SupportedCore` | `LoweringV3/Widening.lean:64` | **CONDITIONAL** | no term; it is the six non-scope clauses of `ValidV3`, so it inherits the missing `ValidV3` witness. |
| `SupportedW` | `Widening.lean:119` | **CONDITIONAL** | `SupportedW.ofV3` needs `ValidV3`; no `AccShape`/`ExternalPinned` term. |
| `ValidCore` | `Widening.lean:812` | **CONDITIONAL** | same as `SupportedCore`. |
| `ValidW` | `Widening.lean:845` | **CONDITIONAL** | `ValidW.ofV3` only conditional on `ValidV3`; F2 (`ivcRender`) is absent. |
| `EvalPins` | `Widening.lean:830` | **CONDITIONAL** | no term; `pin`/`frame` are render facts and `evalClosed` is not proved at a real evaluator. |
| `EvalBodyTotal` | `WideningStages.lean:597` | **CONDITIONAL** | no term; `evalModel_emptyBody` only proves the *empty* body's `evalModel`, not totality of a real evaluator. |
| `EvalContracts` | `WideningStages.lean:605` | **CONDITIONAL** | no term; `evalBodyShape_emptyBody_false` (`:970`) shows the empty body refutes row 1, so the only easy body is not a witness. |
| `SimContractsW` | `WideningStages.lean:863` | **CONDITIONAL** | an implication bundle; `ValidW`/`EvalContracts` hypotheses; no witness. |
| `ProgContractsW` | `WideningStages.lean:897` | **CONDITIONAL** | same. |
| `BlockSimW` | `WideningStages.lean:841` | **CONDITIONAL** | `StageInvW`; at V3's corner `stageInvW_iff_V3` (`:474`) but no inhabitant. |
| `BlockProgSW` | `WideningStages.lean:882` | **CONDITIONAL** | same. |
| `blockSimW_iff_blockSim` | `CompositionW.lean:228` | **INHABITED** | proved equivalence at noAcc/noExt; it is the reduction, not the widened root. |
| `blockProgSW_iff_blockProgS` | `CompositionW.lean:280` | **INHABITED** | same. |
| `model_quotientMode` | `Widening.lean:853` | **CONDITIONAL** | registered sorry; the generator fact has a W12 KAT at embedded/external renders but no proof. Owner WID.H. |
| `HypothesesInhabitedW` | `Widening.lean:720` | **CONDITIONAL** | no F2 witness; `WorldW`/`EvalContracts` absent. |
| `lowering_correctW` (target) | `WideningStages.lean:948` | **CONDITIONAL** | `hR : ValidW R Q`, `hQ : isExternal R → EvalContracts R Q`; no `ValidW`/`EvalContracts` witness, F2 absent. |
| `lowering_correctW_needs_evalContracts` | `WideningStages.lean:959` | **INHABITED** | proved: without `hQ` the empty body is a counterexample shape; it is a conditional implication, not a falsifier of the target. |
| `evalBodyShape_emptyBody_false` | `WideningStages.lean:970` | **INHABITED** | proved falsifier of the empty body; shows `hQ` is not decoration. |
| `lowering_correct_of_W` | `WideningStages.lean:994` | **CONDITIONAL** | depends on `lowering_correctW` and `model_quotientMode` (sorry). |
| `lowering_correctW` at F1 | — | **VACUOUS** | `ValidW R Q` needs `ValidCore`/`ValidV3`; F1's is false. |
| `lowering_correctW` at F2 | — | **UNKNOWN** | `ivcRender` is not imported; C1's bundle is a Rust fixture, not a Lean render. |

**Is the W root vacuous today?** It is **not refuted** and not proved vacuous; it is
**CONDITIONAL with no named F2 render**. At the only named F1 render it is vacuously true
(`ValidV3` false). The W-specific `hQ` guard is meaningful at an external render, but no external
`ValidW` render is in the tree. `ValidW.emptyBody` and `evalModel_emptyBody` show exactly why the
guard is needed; they do not provide a positive W witness.

---

## 8. `end_to_end_acc_complete`: the register's one VACUOUS row

### 8.1 Why the scan marks it VACUOUS

`end_to_end_acc_complete` is `Lowering/Obligations.lean:781`. Its binders include
`(hc : LoweringCorrect S product)` (hypothesis #17 in `#leaf_status`'s numbering).
`LegacyVacuity.not_LoweringCorrect` (`Lowering/LegacyVacuity.lean:106`) is

```lean
theorem not_LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) :
    ¬ LoweringCorrect S product
```

and its axiom print is `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no native axiom.
`#leaf_status Midfall.Lowering.end_to_end_acc_complete under [Midfall]` prints:

```
VACUOUS  Midfall.Lowering.end_to_end_acc_complete
  (hypothesis #17 is refuted for every instance by Midfall.Lowering.LegacyVacuity.not_LoweringCorrect)
```

The mechanism is `LoweringCorrect.ir_refines`: it quantifies over every object passing
`Surface.irCheck`, and both the empty runtime and the stuck runtime pass that check, so the
`ObsEquiv` requirement is inconsistent. This is a *legacy V1/V2* theorem; it is not in the V3 root
cone and has no V3 consumer.

### 8.2 Is it cited by a V3 consumer?

No.

* `#cone_avoids_decls Midfall.LoweringV3.lowering_correct
  [Midfall.Lowering.end_to_end_acc_complete, Midfall.Lowering.LegacyVacuity.not_LoweringCorrect]`
  prints `ok (2 constants)`; the root does not even use the refuter.
* A repository grep finds no `LoweringV3`/`LoweringV2` file that imports or cites
  `end_to_end_acc_complete`; the references are the V1/V2 design docs, `P-SE-semantic-equivalence.md`,
  and the registry row itself.
* The V3 end-to-end layer is `LoweringV3.EndToEndV3`/`end_to_end_of_readSchedule`/
  `end_to_end_of_prepareLogSlots`, and the V3 root **also avoids those** (the second
  `#cone_avoids_decls` prints `ok (2 constants)`). They are D1's conditional deliverable, not a
  consumer of the V1 row.

### 8.3 Correct action

**W13 retirement, with a pointer — do not restate or weaken.** The theorem proves `True` from a
false hypothesis; deleting it removes one VACUOUS row and does not touch any V3 theorem. Concretely:

1. W13 deletes `end_to_end_acc_complete` (and its doc comment) from `Lowering/Obligations.lean`.
2. Regenerate `SORRY.md`/`gen_sorry.sh`: the register drops from 73 to 72 declarations and from
   1 VACUOUS to 0 (D2's merge later restores its own 42 rows; the root count is unchanged).
3. The pointer left in the doc/queue is the V3 replacement: `EndToEndV3`
   (`LoweringV3/Statements.lean:3991`), with `end_to_end_of_prepareLogSlots`
   (`LoweringV3/EndToEnd.lean:720`) and the exact residual `PrepareLogSlots R`
   (`:678`) / `readScheduleAgrees_of_validV3` (`:20` header), plus `ValidV3 R`, `hcodec`, and
   `hside`. Those are **not** proved by the V1 row either; the replacement is conditional, and
   saying so is the point.

If a V3 document ever cites `end_to_end_acc_complete`, the residual is the same `LoweringCorrect`
hypothesis and the consumer is unsound; none does today.

---

## 9. Register, gate, and the `0 REFUTED / 1 VACUOUS` claim

Baseline (`881f780`):

* `formal/SORRY.md`: **73 rows / 11 ROOT**, `0 REFUTED`, `1 VACUOUS`.
* `#assert_no_refuted_sorry [Midfall]` scans sorried theorems, but **only `.refuted` is an error**
  (`Tools/Done.lean:412-429`); a `.vacuous` row is reported, not failed. So the gate passes with
  `end_to_end_acc_complete` VACUOUS and says nothing about the root's missing `ValidV3` inhabitant.
* `#leaf_status Midfall.LoweringV3.lowering_correct under [Midfall]` prints `OPEN`, not `VACUOUS`:
  the scan's `VACUOUS` test is "a *hypothesis* has a proved negation for every instance"
  (`Tools/Done.lean:327`), and `ValidV3 R` has no universal negation. The root is **CONDITIONAL**
  in this report's vocabulary, but the register has no status for "no inhabitant known".
* D2 (`t/D2` `3253c5c`) reports **115 sorried declarations / 11 ROOT**, `0 REFUTED`, no UNOWNED
  root row, root cone unchanged at 11. The 42 new CERT rows are not in the V3 root cone.

**The claim "0 REFUTED / 1 VACUOUS" is factually true and is not a non-vacuity certificate.** It
means (a) no sorried theorem has a proved negation, and (b) one sorried theorem has a refuted
hypothesis. It does not mean the root is inhabited, that the W root is inhabited, or that the D2
`SupportedInput`/`Generates` bundle is inhabited. The audit's central recommendation is to add a
**hypothesis-inhabitation gate** for the V3 root and the W root (joint witness or named gap), of
the same shape as `check_hypothesis_bundles.py` but keyed to `ValidV3`/`ValidW`; the existing gate
only covers the retired V1 `LoweringCorrect` fields.

---

## 10. Top blockers and exact next steps

| # | blocker | exact missing term / writer | owner |
|---|---|---|---|
| 1 | F1-real `ValidV3` is still blocked | `PayloadPointHalf f1GeneratedRender`: re-source the 19/8 commitments and `sG2gen` into `poseidonVkExec`; `exists_validV3` gives generic non-vacuity only, not F1 `Done` | B3 + B4 |
| 2 | Row pres are not inhabited | one `StageInv R H vkAddr cd k V st` at a real render/checkpoint, built from `Frame`, `Inv`, `LeanRaw`, `Agree`; `f1_deploymentV2`/`f1_entryFrameV3` supply only `DeploymentV2`/`EntryFrameV3` | A2/A7/A12 |
| 3 | `EndToEndV3` is conditional on a missing refinement | `PrepareLogSlots R` / `readScheduleAgrees_of_validV3`; also `hside`; at F1 `hcodec` is FALSE (`f1_codecLawsV3_false`) | D1 |
| 4 | KZG partition bridge is false without `x = 0` exclusion | `KzgPartitionBridge` needs `ChallengesGood.xNonzero`/`rotationDistinct`; `kzgPartitionBridge_false_at_x0` is the falsifier | D1/audit |
| 5 | W root has no F2 render or evaluator contract | `ValidW ivcRender`, `EvalContracts R Q`, `EvalBodyTotal Q`; `model_quotientMode` still sorry; F2 Lean importer absent | C1/C2 + WID.H |
| 6 | D2 has no input witness or real-key run | `SupportedInput f1GenInput`, `generate f1GenInput = .ok o`; 42 CERT leaves including `v3_planMeta`/`v3_cdBound` | D2 |
| 7 | `qvm_validated_noBoundsFault` may be vacuous | if `builder_segments_total` lands, `hf` has no instance; restate the no-fault claim or prove the validator faults are reachable; do not weaken | QVM/A8 |
| 8 | V1 `end_to_end_acc_complete` is VACUOUS | W13 retirement + pointer to `EndToEndV3`/`end_to_end_of_prepareLogSlots`; regenerate register | W13/B1 |

**Already landed by this audit (non-vacuity evidence, no statement weakened):**

* `Instances/VacuityWitnesses.lean`:
  * `f1_ValidV3_false : ¬ ValidV3 poseidonRender`;
  * `f1_root_has_no_witness : ¬ ∃ hR : ValidV3 poseidonRender, LoweringEquivalenceV3 ...`;
  * `f1_codec_headline_false`, `f1_codecLawsV3_false` (false at the deployment codec);
  * `f1_deploymentV2` (D-P36a + `poseidonModel_isOk` native) and `f1_entryFrameV3` (`DeploymentV2` + `EntryFrameV3`
    inhabited at F1).
* `formal/Midfall.lean` imports the new module so `check_orphans` and the build see it.

**No row, bundle, `ValidV3`, `ValidW`, or root gained a hypothesis; no statement was weakened.**

---

## 11. Reproduce

```sh
cd formal
lake env lean Midfall/Instances/VacuityWitnesses.lean
lake env lean /path/to/leaf_status_scratch.lean   # #leaf_status end_to_end_acc_complete ...
# #cone_avoids_decls Midfall.LoweringV3.lowering_correct [ ... ]
lake build
bash scripts/verify.sh --quick
python3 scripts/check_orphans.py
python3 scripts/lean_grep.py --help   # or the gate's own invocation
```

The `#leaf_status` output quoted above is from `Tools/Done.lean`; `#cone_avoids_decls` and
`#print axioms` are the same tool's commands. The new witnesses are standard-three plus the
documented D-P36a constants and the two F1 native-decide axioms printed at the foot of
`VacuityWitnesses.lean`; none is in `lowering_correct`'s cone.
