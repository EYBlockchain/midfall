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
| `EvaluatorFrame`, `FrameWellFormed` | Q (`qvm_yul_refines`) | 0 occurrences (stage 4) | field unstated; needs defining in stage 5/6 |
| `S.plan.qext` | Q (`qvm_yul_refines`) | stage 3's `PlanView` has no such field | add to `PlanView` or restate the clause |
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
