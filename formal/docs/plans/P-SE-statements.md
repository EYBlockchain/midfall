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
