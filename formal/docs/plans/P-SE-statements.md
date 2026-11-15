# P-SE statement map - where the normative Lean statements actually live

**Rule this file exists to enforce:** the proof statements to prove are the **Lean sketches
in `P-SE-semantic-equivalence.md` sections A-R** - not the one-line index entries at lines
140-160, and not any orchestrator summary of them. Every P-SE stage brief must cite the
exact line range of its sketch section. Any deviation from a sketched statement is
reported, never silent.

Stage 5 was briefed from the index entries only and the ranges had to be sent mid-flight
as an addendum. That is the failure this map prevents.

## Section map

| section | lines | target file | stage | status |
|---|---|---|---|---|
| A | 407-535 | `Yul/Contracts.lean` | 1 | done `83313c9` - 10/10 lemmas proved, zero holes |
| B | 536-763 | `Yul/Bridge.lean` | 1 | done - 8 named holes, Y-3 resolved |
| C | 764-798 | `Assumptions/Codec.lean` | 1 (+2) | done - 1 hole (`frOfRepr_frToRepr`) |
| D | 799-851 | `Assumptions/Eip2537.lean` | 1 | done - 1 hole (`modexpInv_correct`, a theorem per D14) |
| E | 852-903 | `Lowering/AccEncoding.lean` | 2 | done - 3 holes, one shared cause |
| F | 904-1091 | `Lowering/Accumulator.lean` | 2 | done - 12 holes |
| G | 1092-1110 | `Lowering/VkDigest.lean` | 2 | done - 1 hole |
| H | 1111-1314 | `Lowering/Calldata.lean` | 2 | done - 7 holes |
| I | 1315-1357 | `Lowering/Checkpoint.lean` | 3 | done `bcf653d` - zero holes |
| J | 1358-1399 | Exec refactor (signatures only) | 3 (D6) | done `9d0b94c` |
| K | 1400-1470 | `Lowering/Snapshot.lean` | 3 | done - 1 hole |
| L | 1471-1617 | `Lowering/Inv.lean` | 3 | done - satisfiable at all 7 checkpoints |
| M | 1618-1793 | `Lowering/Surface.lean` | 4 | done `04adea7` - 1 hole |
| N | 1794-1931 | `Lowering/Partials.lean` | 4 | done - 12 holes, all 7 specs STATED |
| ~~`stmtsBeq`~~ | Q (`render_eq_print`) | **EXISTS - earlier claim was wrong.** Declared at `vendor/yul-semantics/YulSemantics/Ast.lean:147`; `#check @YulSemantics.SyntaxEq.stmtsBeq` resolves and six passing gates in `YulGolden.lean` already use it | nothing needed; D-P13 is sound and `render_eq_print`'s conjunct IS writable |
| Q | 2164-2378 | `Lowering/Obligations.lean` | 6 | queued - the headline |
| R | 2379-end | (diff vs PLAN 9.5, not code) | all | read before deviating from any sketch |

## Sketched identifiers known NOT to resolve

Collected from the stage 1-4 reports. Each is a statement that cannot be copied verbatim;
the stage that needs it must define it, substitute it, or report the gap - not silently
invent a different statement.

| name | section | status | what was done instead |
|---|---|---|---|
| `stmtsBeq` | Q (`render_eq_print`) | **no declaration anywhere** (grep `Midfall/` + `vendor/`) | conjunct unwritable; D-P13 names it authoritative - needs a decision |
| `Midfall.Halo2.Verifier.lagrangeTriple`, `MultiPrepare.phaseA/B/C` | J/K | declared **outside** those namespaces | use `Midfall.Halo2.lagrangeTriple`, `Midfall.Halo2.phaseA` |
| `S.repackProof`, `S.encodeCalldata` | Q (`end_to_end_noAcc`, the two `_faithful` fields) | stage 4 deliberately removed the codec fields from `Surface`, so there is no LHS | the two `_faithful` fields DEFERRED; `end_to_end_noAcc` restated against the spec functions |
| `EnvAgrees` 7-arg form | L, Q | landed arity is **5** (`E vk plan params sG2gen`) - confirmed by `#check` | use the landed arity |
| `tblOf S.plan S.accFixedBases` | Q | landed `tblOf` takes the table alone | use the landed arity |
| untyped `(gas)` binder | Q (`points_subgroup_checked`) | `autoImplicit = false` rejects it | type it: `(gas : ExternalGas)` |
| `frameValuation` | Q (`qvm_yul_refines`) | absent | field deferred rather than invented |
| `(exprs[i]'(by omega))` inside a conjunction | P | **does not elaborate** - the length equalities are conjuncts, not hypotheses in scope | Option indexing, equivalent under the length conjuncts |
| `List.modify` argument order | P | 4.35 is `List.modify : List α → Nat → (α → α) → List α`, index BEFORE function | swapped at the site |
| `Except.getD`, `List.zip3`, `ZMod.eq_iff_modEq_nat`, `∃ i (h : i < n), …` binder | O/P | absent or invalid syntax | substituted, each recorded in the file header |
| `List.Sorted` | P (`SelectorFoldConsistent`), Q (`accFixedBases_producer`) | Mathlib order theory not in the built surface | stage 2 used a local `namesAscending`; same fix |
| `memLeaves` | O (`leafKeys`) | marked SKETCH | verify against landed `QuotientExpr` |
| `nativePermutationIdentities`, `nativeLookupIdentities`, `nativeIdentities` | P (`expandItem`) | marked SKETCH | verify against `QuotientProgramPlan` |
| `outputBytes`, `yOf`, `perIdentityValues` | Q (`qvm_yul_refines`) | marked SKETCH | stage 5/6 must define or report |
| `ZMod.pow_card_sub_two_eq_inv` | D sketch | not a constant in pinned Mathlib | real form is `ZMod.pow_card_sub_one_eq_one` |
| `Bridge.honestResponds` | Q (`PermissiveFor`) | 0 occurrences | stage 4 used `PermissiveFor` over `S.calls` |
| `Fault` stage tag (`snapshotOf = .error (.pcs, f)`) | K/N | `Fault` has two constructors; no phase recoverable | `PartialRejects` stated over an untyped fault |
| `tokenBase : VerifierMemoryLayout -> Nat -> Nat` | M | signature does not exist | QVM area has `tokenBases` over `QuotientMem` - different object |
| `blsDeltaLiteral`, `vkG1Words`, `vkG2Words` | L (`EnvAgrees`) | do not exist | those `EnvAgrees` fields dropped, reason at the site |
| `Midfall.Halo2.Verifier.lagrangeTriple`, `MultiPrepare.phaseA/B/C` | J/K | declared **outside** those namespaces | use `Midfall.Halo2.lagrangeTriple`, `Midfall.Halo2.phaseA` |
| `Inv` 7-arg / `EnvAgrees` 7-arg forms | L, Q | do not typecheck against stage 3's landed arities | use the landed arities (`Inv E params k PV Snap V st`) |

## Stale notes found inside the sketches themselves

* **Line 2002-2003** documents `RecognizersSound` as "the recognizer hooks (P-09f
  unported)". **P-09f landed** (`d2ff30f`, `VmRecognizers.lean`, 39 ported defs). The
  substantive warning - "compile correctness is false for arbitrary hooks" - still stands;
  the blocker note does not.
* **`PLAN.md` line 183 and 223** named `--ir-ast-json`; corrected in `1f4fba5` for section
  7, but **section 5's exporter bullet still names the superseded artifact**.
* **PLAN 13's calldata-canonicity risk note** said trailing bytes and words >= r may be
  accepted. P-12 measured the decoder is **EXACT**; corrected in `28c1e8d`.

## Required reading order for a stage brief

1. This map - your section's line range.
2. The sketch itself (copy the statements from here).
3. Section **R (2379+)** - the authoritative diff against PLAN 9.5, so a deviation can be
   checked against what the plan already decided rather than reinvented.
4. `P-SE-evidence/attack.md` FIX lines (binding) and the matching `design*.md`.
5. The dead-identifier table above, so a sketched name is verified rather than trusted.

## P-RESTORE2 - the sketch-vs-implementation record for sections K, L, M, N

Added by P-RESTORE2, whose whole subject is drops that were never written down. The rule
this package adds, and which the four packages before it did not have:

> **A rename, an arity change, or a dropped field on a sketched statement requires a line
> in this file, in the same commit.** Not in a doc comment in the Lean file, not in a
> plan brief that gets archived: here, where the next auditor looks. The reason is
> measured: `EnvAgrees.accBasesInVk` was dropped and recorded nowhere, and the only
> reason anyone noticed is that a human happened to diff the sketch by hand. Everything
> below was found the same way - mechanically, by listing every declaration and every
> structure field the sketch writes in sections A-R and grepping the tree for it - so
> none of it is a judgement call about intent.

### The audit: every sketched obligation absent from the tree without a record

404 declarations and structure fields appear in the sketch's code blocks (sections A-R).
25 of them have no counterpart in `Midfall/`. 17 of those 25 are named in a Lean comment,
in `docs/ETA.md`, or in this file - i.e. they are annotated gaps, which is the acceptable
state. **Eight are named nowhere.** That is the class this package exists to eliminate.

| sketched name | section | what it actually is | status after P-RESTORE2 |
|---|---|---|---|
| `EnvAgrees.accBasesInVk` | L:1551 | every fixed-base table entry is a point a VK header slot encodes | **RESTORED** as `VkSlotsAgree.accBasesInVk`, exhibited at the fixture (`fxVkSlotsAgree`) and consumed by `finalPairing_acc_spec` as `hvks` |
| `Inv`'s reversed-evals clause (`reversedEvalsOf`) | L:1585 | pins the parser's main output window | **RECORDED** in Inv.lean's DROPPED list with the measured blocker, plus `gap_reversedEvalsWindow`. It WAS annotated - at Inv.lean:66-71, in the header's prose, which is not the register anyone greps - so the brief's "recorded nowhere" is half right and is corrected here |
| `publicInstanceEval` | K:1434 | the instance evaluation the Lagrange partial reads | **RENAMED, never recorded**: the tree has `instanceEvalOf` (Snapshot.lean), same job, same attack fix about `getD 0`. Recorded now |
| `finalPairing_sound_noAcc` | N:1882 | the no-accumulator pairing soundness theorem | **RENAMED, never recorded**: landed as `finalPairing_spec`. Recorded now |
| `finalPairing_progress_noAcc` | N:1895 | its progress twin | **RENAMED, never recorded**: landed as `finalPairing_progress_spec`. Recorded now |
| `finalPairing_sound_acc` | N:1906 | the accumulator arm | **RENAMED, never recorded**: landed as `finalPairing_acc_spec`. Recorded now |
| `EnvAgrees.accConsistent` | L:1547 | `hasAccumulator = accEncoding.isSome` | **RELOCATED, never recorded**: the two siblings accHeader/accNoHeader are named in docs/ETA.md:383; this one is not named anywhere. Its content lives as the `pv.expectedHasAccumulatorWord == if pv.hasAccumulator then 1 else 0` line of `planAccWords_derive_ok` (Inv.lean:857-860). Recorded now |
| `PlanView.qplan`, `PlanView.qbuild` | L:1495-1496 | the quotient plan and its build, carried on the plan view | **REPLACED, never recorded by name**: the landed PlanView carries `meta_` and `dat` instead, and `gap_planview_carries_the_plan` (Inv.lean) describes the plan-projection decision without naming these two fields. Recorded now |
| `Surface.modulusPinned` | M:1674 | `p = Midfall.Assumptions.r` as a Surface pin | **RELOCATED, never recorded**: the same fact is `EnvAgrees.modulus` (`p = frModulusConstant`), and `fxEnvAgreesKats_ok` asserts `rp == frModulusConstant`, so the obligation is carried - just not under this name and not in this structure. Recorded now |

### Other P-RESTORE2 deviations

* `EnvAgrees` arity. The sketch's is seven (E, vk, PV, params, sG2gen, encG2, fb); the
  landed one stayed at five and the two extra arguments moved to a sibling structure
  `VkSlotsAgree (E) (PV) (sG2gen) (encG2) (fb)`. The reason is measured and is in that
  structure's doc comment: folding them in makes `curveEnvAgrees` - and with it
  `curveBundle` and `curveBundleCore`, the only exhibit of `Eip2537.Holds` at a Surface -
  undischargeable, because curveSurface reuses the fixture's payload image and its G1
  codec is noncomputable. The conjunction of the two structures IS the sketch's
  seven-argument hypothesis, field for field.
* `g1BaseWords` / `g2BaseWords` / `negSG2Words` **restored** after the recorded reason for
  dropping them was checked and found false (see Inv.lean's dropped list: the .vk clause
  pins the payload COPY and never mentions a codec, so the clauses were not redundant).
  The sketch's literal slot indices 11/15/23 are the derived `vkG1BaseSlot` /
  `vkG2BaseSlot` / `vkNegSG2BaseSlot`, which `Models.lean:1159-1160` computes to 11/15/23.
* `finalPairing_progress_spec` **strengthened against the sketch**: the sketch (N:1873)
  gives it no `success` hypothesis, but the emitted slice reads the local before writing
  it (GenAst.lean:651-654), so the sketch's form is false for a run entering with
  success = 0. The entry condition is now on the pre. Deviation on the strong side.
* `PartialSpecs.transcript_rejects` and `PartialSpecs.pcs_rejects` **landed** (sketch
  N:1860-1865), which is what `PartialRejects` was defined for and which ends its status
  as a definition nothing consumes. The sketch's stage-tagged fault key does not
  typecheck (Fault carries no stage); the landed key is the fault itself, with the stage
  named by which field it is - the workaround PartialRejects' own doc comment promised.
* `delta` (sketch L:1526) stays dropped, with a MEASURED reason now. The literal the
  contract emits is `let delta := {{ fr_delta }} // BLS12-381 Fr::DELTA`
  (QuotientNumeratorBlock.yul:1407), and `fr_delta_literal()` is COMPUTED as
  `fe_to_u256::<Fq>(&Fq::DELTA)` (quotient_numerator/yul_emit.rs:330). The Rust test
  `permutation_delta_literal_is_computed_from_field_constant` (tests.rs:3467-3475)
  asserts the codegen source must NOT contain that literal. A Lean `blsDeltaLiteral`
  would therefore be a hard-coded transcription in the one place the reference has a
  test against hard-coding - and it is a BASE-field constant (Fq::DELTA) cast into
  `Fr p`, the cross-field move R-26.7 refuses to lose. Third: the fixture sets
  `VerifierEnv.delta := 2`, a placeholder nothing ties to the artifact, so the clause
  would be false at the only Surface able to check it. Recorded in the Inv.lean
  dropped list; docs/plans/P-DELTA-GAP.md stays open.

## P-RESTORE3 - the 17 annotated-but-absent obligations, triaged with the reason checked

P-RESTORE2 swept 404 sketched declarations and found 25 absent: 8 unannotated (fixed there)
and **17 annotated**. Annotation makes a gap visible; it does not make it correct, and R11 had
just proved an annotated reason could be false. Every one of the 17 was re-derived and its
reason re-measured. The list was re-derived mechanically (sketch code blocks A-R, declarations
plus structure fields, matched against comment-stripped declarations in `Midfall/`): 400
sketched names, 23 absent, which is P-RESTORE2's 25 minus the two it restored and plus
`Inv_mono` (annotated at Inv.lean:37 and :892, where the sketch's statement is proved FALSE -
Inv is not monotone - and the monotone fragment is stated instead). The brief's table names 15;
the sweep's 17 are those plus `tokenBase` and `frameValuation`.

| sketched name | sketch line | verdict | evidence |
|---|---|---|---|
| `hProofLayout` | M:1676 | **RESTORED** as a `Surface` pin | **Its recorded reason was FALSE.** Surface.lean deviation 2 lists it with `hRepack`/`hEncode` as codec pins with no left-hand side; it names no codec, and its LHS `plan.proofLayout` is a field the record has always carried. Landed verbatim (Surface.lean:452) and exhibited: `fxProofProtocol = AbiKats.protocolShape [8] [1] 3 1 4` with 48 evals and 3 point sets gives `fromProtocol ... = .ok poseidonProofLayout` by `rfl` at BOTH Surfaces. Not a self-round-trip: the RHS is transcribed from the deployed dump's `add(proof_cptr, 0x..)` lines, the LHS is the ported generator's output from the counts. `hProofLayoutKats_ok` perturbs all nine inputs (advice count, permZ, trashcans, quotients, lookup chunks, numEvals, numPointSets) and each perturbation breaks the equation. |
| `encodeCalldata_faithful` | Q:2285 | **RESTORED IN SUBSTANCE**; literal pin unstatable | The reason (no `Surface.encodeCalldata` field) is TRUE - checked against the record's field list. But the annotation's second sentence, "the content moved into `end_to_end_noAcc`", is **FALSE**: that field applies the *encoder* to the Surface's layout and never says encoder and decoder agree. The agreement is stated only by `calldata_roundtrip`/`calldata_canonical` (Calldata.lean:404/:428), both still `sorry`, both KATed only at the 4-slot `katLayout`. Now exhibited at the DEPLOYMENT's layout: `encodeCalldata_faithful_at_layout` - 72-slot schedule, 4484-byte calldata (the artifact's own size, Generator/Calldata.lean:844), `decodeCalldata` reads it back, head words 0x40/proofLen/numInstances where the guards look. Refuted by `faithfulnessRefutations_ok`: one byte short or one byte long and the decoder refuses. |
| `repackProof_faithful` | Q:2283 | **RESTORED IN SUBSTANCE**; same treatment | Same reason, same correction. `repackProof_faithful_at_layout`: the 2640-byte compressed stream repacks to exactly `encodeContractProof` of the 72 messages `decodeWire` reads, at the poseidon plan; `compressedLen`/`repackedLen` agree with the layout. Refutation: a 2608-byte stream errors on the exact-length guard. |
| `hEncode` | M:1680 | **DEFERRED, reason verified** | The twin of `encodeCalldata_faithful` at the deleted Surface field; no LHS exists. Carried by the exhibit above. |
| `hRepack` | M:1678 | **DEFERRED, reason verified** | Twin of `repackProof_faithful`. |
| `repackProof` | H:1163 | **PRESENT verbatim** | `Midfall.Lowering.repackProof`, Calldata.lean:186, sketch shape intact including the exact-length guard first. The sweep's "absent" for this name was about `S.repackProof`, the deleted Surface field, not the spec function. |
| `encodeCalldata` | H:1195 | **PRESENT verbatim** | `Midfall.Lowering.encodeCalldata`, Calldata.lean:241. One recorded substitution: `encodeCalldataRaw` is an ALIAS of `Midfall.Generator.encodeCalldata` (Calldata.lean:230) rather than a second copy of the byte shape - the anti-duplicate rule the plans README states. |
| `irCheck` | M:1666 | **PRESENT, and stronger than the sketch** | `Surface.irCheck` (Surface.lean:771) is a PROJECTION of `runtimeName`, not a free field - R-60 S1's repair. The sketch's free field is what let the fixture's check disagree with the run relation. |
| `hoisted` | M:1656 | **ALREADY PRESENT under another name** (rename recorded here for the first time) | The tree's carrier is `Partials.mainScope` (Partials.lean:125), which DERIVES `hoist S.L.main :: outer`. A Surface field carrying a `FunEnv` beside a derived scope is the R-58 copy class: two names for one scope with nothing relating them. Every one of the ten spec theorems runs in `mainScope`, so the obligation is consumed - under the other name. |
| `qvm_yul_refines` | Q:2258 | **DEFERRED, reason verified in substance, one line STALE** | The recorded blocker said the missing artifact was `QuotientNumeratorBlock.yul` as a `Block Op`. That is now out of date: P-STR2AST landed `Midfall/Lowering/GenAstQuotient.lean`, the batched-identity numerator Evaluator as a real Yul AST, gated token-for-token against the text port. The deferral still holds for two reasons that were re-measured, not inherited: (i) no function assembles those blocks into a whole evaluator runtime object, and (ii) BOTH Surfaces in the tree carry `evaluatorRuntime := none`, so the field's hypothesis has no witness at any Surface - unsatisfiable-hypothesis class. |
| `EvaluatorFrame` | M:1778 | **DEFERRED with it** | Stating a frame record while no Surface has an evaluator runtime is a definition nothing consumes - the `PartialRejects` failure. Its four clauses are otherwise statable today except `qext.frameLen`. |
| `FrameWellFormed` | M:1786 | **DEFERRED with it** | Same. Three of its four clauses are statable on landed data (`plan.vkMptr`, `plan.vk.bytes`, the modulus bound); the fourth needs the frame length below. |
| `qext` (a `PlanView` field) | L:1497 | **DEFERRED, reason re-measured and TRUE** | Re-checked by projection rather than by grep: `PlanView` has no quotient frame and `VerifierMemoryLayout` has **no** `quotientExternal` field either (Lean rejects the projection). The frame quadruple lives on `QuotientExternal` (Models.lean:531) and reaches a plan through `PlannedQuotient.external` (LoweringPlan.lean:291), so P-11's `LoweringPlan::new` remains the blocker. |
| `tokenBase` | M:1784 | **DEFERRED, reason verified** | The sketch's own `sorry` marks it undefined. The tree has `tokenBases : List (Nat x Nat)` on the VM operand model (VmValidator.lean:473) - a different object over `QuotientMem`, not `VerifierMemoryLayout -> Nat -> Nat`. Recorded at Surface.lean deviation 3 and re-confirmed here. |
| `frameValuation` | Q:2262 | **DEFERRED with `qvm_yul_refines`** | A valuation read out of a live `EvmState` frame; nothing in Exec exposes one, and the frame itself is the deferred object. |
| `points_subgroup_checked` | Q:2274 | **DEFERRED, reason RE-VERIFIED** | The deferral rests on `points_subgroup_checked_conclusion_is_unconditional` (Obligations.lean), a PROOF and not an argument, so the build re-verifies it every run. Re-checked the premises the brief asked about: `permissive` (Bridge.lean:594) still admits any request to any target whenever the response fails with an unchanged world, and `failResp` (Bridge.lean:557) still supplies one for any state. Neither the `Holds` exhibit nor the G1-codec work touched either definition. The deferral stands, and the witness objects (`isAlignedSubslice` + KAT) stay defined and gated. |
| `vkDigest_slot0` | Q:2281 | **DROPPED, reason now PROVED** | R-58 F5 said it follows from `Surface.vkDigest_spec` + `EnvAgrees.vkDigestWord`. That is a premise, so it is now a theorem: `vkDigest_slot0_of_the_stated_pins` (Obligations.lean) is one `trans`, and both hypotheses are in the bundle of every field that needs the digest. Re-adding the field would be the decoration F5 named. |

**How many were genuinely missing obligations: two.** `hProofLayout` (a pin the record should
have carried since stage 4, dropped behind a reason that belonged to its neighbours) and the
`*_faithful` obligation (one claim, two halves: the encoder's bytes are the decoder's bytes,
which was stated only for an arbitrary layout and only at a 4-slot KAT plan, and is now
exhibited at the deployment's own layout). Everything else was present verbatim, present under
another name (`hoisted` -> `mainScope`, now recorded), or deferred behind a reason that
survived re-measurement - with two annotations corrected in place: the `*_faithful` claim that
the content had moved into `end_to_end_noAcc`, and the `qvm_yul_refines` claim that no AST of
the numerator evaluator exists.

**Does a restored obligation make an existing hypothesis load-bearing?** Yes, and this is the
one that matters. `hcd : decodeCalldata S.plan.proofLayout S.cfg.numInstances S.E.g1 cd =
some (ms, instW)` is a hypothesis of every one of the ten partial specs, of `LeanAccepts`, and
of all three side conditions - and until now nothing anywhere said the Surface's layout is one
the decoder's own guards can be satisfied by. `hProofLayout` supplies exactly the two facts
(`proofCptr = 0x64`, `proofEnd = proofCptr + proofLen`) that `proofLen_eq_repackedLen` is
needed for and that `calldata_roundtrip` takes as hypotheses `hL`/`hlen`/`hend`. So the chain
`hProofLayout -> proofLen_eq_repackedLen -> calldata_roundtrip -> hcd satisfiable` now exists,
and the two theorems `decodeCalldata_none_of_pointer_mismatch` and
`decodeCalldata_none_of_len_skew` prove the other direction: break either guard and `hcd` is
unsatisfiable for EVERY calldata, i.e. all ten specs become true because nothing decodes. That
is the vacuity the restoration was driving at, and it was reachable through an unpinned layout
until this package.

**D-P23 coverage claimed, and the limit.** `hProofLayout`: witness at both Surfaces (`rfl` on
`fxProofProtocol`) + nine-input sensitivity perturbation set + two proved consequence
theorems. The `*_faithful` exhibits: witness (decode-back, sizes, head words) + refutation
(truncated, extended, short-stream). **NOT claimed:** no Surface that FAILS `hProofLayout` is
exhibited. Refuting the existential needs an inversion lemma for `fromProtocol` (its output's
`proofCptr` is the pointer argument); four attempts at `split at h` over the do-block's match
tower did not close it and the lemma was not proved. The gate for the class is
`scripts/check_statement_fingerprints.py` `SURFACE_PINS`, which now carries `hProofLayout`
(235 fragments, up from 231) and reddens if the pin is paraphrased or gutted.


---

## P-MC-CALLDATA - the seven `Calldata.lean` holes, checked against section H

Statement authority: `docs/plans/P-SE-semantic-equivalence.md` section H, lines 1111-1314.
Each of the seven holes was read against its sketch BEFORE being proved. Result: **six of the
seven matched the sketch verbatim** (modulo the recorded `hexOf` -> `hexEncodeLower` and
`encodeCalldataRaw`-as-alias substitutions, which predate this package and are annotated at
their sites). **One had drifted, and it had drifted WEAKER.**

| hole | sketch | implemented form found | verdict |
|---|---|---|---|
| `sum_commitmentReadGroups` | H:1258 | identical | proved as stated |
| `proofLen_eq_repackedLen` | H:1261 | identical | proved as stated |
| `calldata_roundtrip` | H:1267 | identical, incl. `hp : p <= 2^256` | NOT proved (out of room); statement unchanged |
| `calldata_canonical` | H:1280 | **carried an extra binder** `hend : L.proofEnd = L.proofCptr + L.proofLen` | **RESTORED to the sketch, then left as a hole** |
| `repack_spec_wire` | H:1287 | identical | proved as stated |
| `repack_spec_of_decodeRust` | H:1294 | identical | NOT proved (out of room); statement unchanged |
| `points_subgroup_checked_generator` | H:1305 | identical | proved as stated |

**The `calldata_canonical` drift, and why the sketch form is the right one.** The implemented
statement took the layout-consistency equation as a hypothesis. Section H does not, and cannot
need it: `decodeCalldata` itself contains `guard (L.proofEnd == L.proofCptr + L.proofLen)`,
so any successful decode already implies it. The file's own docstring even justified the binder
as "necessary for hand-built layouts", which is false for the same reason - it is necessary for
hand-built layouts to *decode at all*, which is the hypothesis. Carrying it as a binder made
the claim strictly weaker than the sketch, which is the drift class this package was told to
look for. Restored: `hend` is gone from the statement, and `decodeCalldata_hend_of_some`
(Calldata.lean, section 6) proves the equation from `h` so the restoration costs the next
package nothing. One honest caveat, because the authority document disagrees with ITSELF and the next
package should not have to rediscover it: section H (lines 1280-1284, the designated
authority for this package) states `calldata_canonical` WITHOUT `hend`, while the same
document's index row at line 233 reads
`calldata_canonical (hc : eipRoundtrip) (hend)`. So the binder in the tree may be a
transcription of the index rather than a drift from the sketch. The restoration follows
section H because that is what the brief names as authority, and the choice is cheap either
way: `decodeCalldata_hend_of_some` proves the equation from `h`, so a future proof of the
sketched form can recover `hend` in one line, and a future decision to keep the index's
shape is a one-line re-addition rather than a re-proof. **A human should pick one and
delete the other from the authority document.**
The two generic refutations `decodeCalldata_none_of_layout_skew` and
`decodeCalldata_none_of_pointer_skew` moved from the KAT namespace to section 6 as part of the
same edit, because they are the contrapositive of exactly this fact and are stated over an
arbitrary codec, not the toy.

**Does the `hProofLayout -> proofLen_eq_repackedLen -> calldata_roundtrip -> hcd` chain
close?** **Partly, and the part that did not is the last link.** `proofLen_eq_repackedLen` is
now a theorem, so the first arrow is proved: for EVERY layout the generator produces at the ABI
pointer - not just the transcribed poseidon one - the two guards `decodeCalldata` insists on
hold, and `proofLen` really is the repacked length. The anti-vacuity claim itself is now a
theorem at the deployment's own layout: `SurfaceFixture.hcd_satisfiable_at_deployment` proves
`(decodeCalldata\ rp\ fxPlan.proofLayout\ numInstances\ E.g1\ fxLayoutCalldata).isSome` -
4484 bytes, 72 slots, the real codec - so `hcd` is satisfiable and the ten specs are not true
because nothing decodes. What is still missing is the *symbolic* `calldata_roundtrip`: the
statement that for an ARBITRARY message list with the layout's slot shape, `calldataOf` round
trips. That needs byte-level window lemmas for `cdWord` over an unbounded buffer (the decoder
reads 32-byte words at symbolic offsets), which is a larger piece than the room left. It is
registered at Calldata.lean:743 unchanged.

**D-P23 for the four claims proved here.** Witness and refutation, both as theorems, all in
`Calldata.lean` section 8 (`CdKats` except where noted:
`sum_commitmentReadGroups` - `sum_groups_witness` + `sum_groups_filter_bites` (a layout whose
group list is NOT the list of phase counts, so the lemma is about a filter and not
`List.sum_map_id`). `proofLen_eq_repackedLen` - `proofLen_witness` + `proofLen_skew_falsifies`
+ `SurfaceFixture.fixtureLayout_guards_from_theorem` (the guards derived from the theorem
rather than checked against the transcription). `repack_spec_wire` - `repack_wire_witness` +
`repack_wire_refuted_length` + `SurfaceFixture.repackProof_faithful_at_layout_is_ok` and
`decodeWire_faithful_at_layout_is_ok` (the 72-slot deployment plan, as theorems).
`points_subgroup_checked_generator` - witness is the pre-existing
`validateAbsorbedCoverage_fixture_ok` gate over the real plan; refutation is
`psc_hypothesis_is_a_real_constraint`, which proves the hypothesis fails whenever the layout's
`totalG1Count` disagrees with what the generator tracked.

**The limit, stated because it has now been measured eighteen times.** Deleting a falsification
theorem leaves the build green: with `repack_wire_refuted_length` removed, `lake build`
completed successfully (2119 jobs) and nothing anywhere noticed. No gate in `checks.sh`
distinguishes a refutation from a comment. The five perturbations run for this package all
behaved - deleting the layout-consistency guard reddened, dropping `decodeWire`'s exact-length
guard reddened (and `native_decide` caught the resulting falsehood), falsifying the second
conjunct of `proofLen_eq_repackedLen` reddened, and changing `sum_commitmentReadGroups`'s
right-hand side to `totalG1Count` reddened - but none of those is a *deletion* of a
refutation, and that gap is not closed here.

## P-M8-IRCHECK - the two signature changes 'IRCheck.lean' owes

Fable's sketch (docs/PLAN.md line 228) is 'irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)',
one hypothesis. 'Midfall/Yul/IRCheck.lean' lands a theorem of that shape - 'irCheck_sound' - and it
needs **one extra hypothesis**, recorded here rather than hidden:

* 'hlyt : irLyt = S.shellLayout'. 'RunContractIR' runs the artifact in 'callState W irLyt H cd' and
  'wrap' runs the model in 'callState W S.shellLayout H cd'. 'datacopy', 'datasize' and
  'loadimmutable' read 'code', 'dataOffset', 'dataSize' and 'immutable' out of the frame, and
  'ObsView' carries the bytes those produce, so no theorem of Fable's shape can avoid tying the two
  layouts. The tie is a Prop about a function field ('immutable : U256 -> U256'), so it cannot be
  folded into the checker's Bool; it is a named hypothesis instead. Nothing else about the sketch's
  shape changed: the conclusion is still 'ObsEquiv', not a one-sided simulation.

**The determinism dependency was NOT taken, because it does not exist.** The brief offered "prove
'dialect_deterministic' first" or "land a weaker one-sided simulation". Neither:
'ObsEquiv' is a bi-implication between two existential statements, so a per-run matching discharges
it, and a per-run matching never asks a run to be unique. 'obsEquiv_iff_runsMatch' proves the
characterisation and 'irCheck_sound' uses it. 'Bridge.dialect_deterministic' (Bridge.lean:186)
stays a registered hole and stays irrelevant to this theorem - the second time this tree has found
that hole cited as a blocker where it was not one (the first is recorded at Bridge.lean's R-60 S6
note).

**Where the checker is weaker than the sketch, and by how much.** P11 defines 'irCheck' as
"alpha-equivalence modulo constant substitution and solc renames, fuel-based". The checker
'irAlphaCheck' implements exactly that - fuel-bounded, descends into every function body and nested
block, names its legal constant substitutions in 'constSubst', names its renames in 'solcRenames',
requires the rename to be a bijection whose call sites moved with it - and its **soundness is not
proved**. What is proved is 'irCheck', the same shape with the relaxation tables forced to the
identity, i.e. literal AST equality plus the creation check. The reason is mechanical and is written
out in the file header: making the alpha layer sound needs a transport lemma over the vendored 'Step'
that carries the function environment, and Lean 4.35 will not do structural recursion or mutual
induction through 'Stmt.switch' (R-37, re-measured twice this session). So the tree has a sound
checker that is conservative and a Fable-shaped checker that is not yet proved sound, and
'ir_refines' cannot cite the second until the transport lands.

**One convention this file had to adopt.** 'SyntaxEq.stmtsBeq' does not reduce in the kernel on these
blocks - 'theorem t : stmtsBeq sample alphaRename = false := by decide' fails with "failed to
reduce" even though the interpreter evaluates it to 'false' - which is the recorded reason artifact
cross-checks in this tree are 'Bool' gates read by 'kat_gate' rather than theorems. The falsifications
that could be stated as theorems (everything through the file's own matcher, which does reduce) are
theorems; the two that hinge on 'stmtsBeq' ('irCheckCore_witness_gate', 'witness_creation_ok_gate')
are gates with '#eval' lines.
