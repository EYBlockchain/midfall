# Midfall formal - progress log

**Standing practice (D-P23 + human instruction, round 61): update this file every time a
work package lands.** Normative plan is `PLAN.md`; proof programme is
`docs/plans/P-SE-semantic-equivalence.md`; findings are `REVIEW.md`; decisions are
`design.md`; estimates and velocity are `ROADMAP.md`. This file is the running narrative of
**where we actually are**, newest first.

## Round 62 - the repairs landed, and two of them did better than repair

`P-REV-FIX` applied all ten R-58 findings plus G2 (`8ed429d`). Tree: 5143 jobs green, 100
modules, **1147 KATs**, 64 sorries all owned, **58 statement fragments across 9 fields and
5 Surface pins**, **7 fact families single-copy or pinned**.

* **Five new Surface pins**: `shell_unfolds`, `plan_hasAccumulator`, `plan_numInstances`,
  `evaluator_agrees`, `encG2_eip`. `shell_unfolds` is the important one - with it,
  `RunShell`'s program *is* `RunVerifier`'s program, so `verifier_sound + shell_unfolds`
  gives shell soundness **by unfolding** rather than by hope.
* **Two did better than repair.** F1 was **deferred, not patched**: the field was removed
  *and the vacuity proved in the file* (`points_subgroup_checked_conclusion_is_unconditional`)
  so it cannot silently return. F4 **deleted** `qvmValidated`/`SupportedS.qvm` outright - the
  fixture discharged it with `trivial`, so it could not fail.
* **A new pin immediately caught a real bug.** Restating `render_eq_print` as a pin over
  *every* option failed the old `astOfMain`, which keyed on `trace` only and answered
  `some` for a gas-checkpoint render the render refuses. The previous formulation hid it.
* **Honest half on G2:** fixing `encG2` did **not** make `Eip2537.Holds` satisfiable - the
  blocker is `g1Valid` over the exponent codec, i.e. the missing BLS12-381 model
  (D-P1/R-28), not a pin. Proved in the tree rather than asserted.
* **New gate** `check_duplicate_facts.py`: parses the records with comments stripped so
  prose cannot fake a field, requires a pin whose *type names both sides*, rejects
  self-equality. Credible because **run before the fixes it reddened with exactly the five
  real defects**, and it rejects `shell_unfolds` weakened to a self-equality. One honest
  non-bite: the old `astOfMain` shape reddens a KAT, not the build, because no `Surface`
  instance is constructed anywhere.

**Where the headline stands:** `lowering_equivalence` is still only **stated**, but half the
distance closed. The remaining gap is entirely IR-side - `ObsEquiv` view transport,
`dialect_deterministic`/`noWritersFuel`, `irCheck` not being alpha-equivalence, and the
dispatcher the shell model does not have until M8 restates the pin per-arm.

**In flight:** `P-REV2`, the second statement review pass required by D-P23 after a repair
round. It is told to attack the five new pins for ways to satisfy them while the defect
survives, to test whether the restated `render_eq_print` is now *too easy*, and to try to
defeat the duplicate-fact gate - a text-parsing gate over Lean source is usually beatable.

| Theorems and lemmas | **189** (was ~20 at the start of the port stretch) |
| Known-answer gates | 1142 across 76 files, plus 42 statement fingerprints |
| Tracked sorries | **64**, every one registered with a named owning stage |
| Frozen statements | hash OK; axioms `[propext, sorryAx, Classical.choice, Quot.sound]`, unchanged since M1 |
| Rust gate | `cargo test -p halo2_solidity_verifier` 203 passed / 0 failed |
| Commits in the last day | 46 |
| Findings logged | 60 `R-` entries |

## Round 60-61 - the statement review and its aftermath

**The single most productive review of the project.** A statement-only adversarial review of
P-SE stages 1-6 (read-only) found **ten defects, six demonstrated in Lean** (R-58). None
was findable by a port package, and all ten passed every mechanical gate that existed.

* **F1** `points_subgroup_checked`'s conclusion holds with **no hypotheses at all** - the
  existential call is not tied to the run, and `permissive` admits any failed call to any
  target.
* **F2** `PlanView.hasAccumulator` is a free Bool - nothing compares it to
  `cfg.accumulator`, so **11 of 13 `PartialSpecs` fields discharge on a one-Bool lie**.
* **F3** `S.shell.codeBlock` occurs at exactly **one** site, so the three run relations are
  about three unrelated programs - and **`lowering_equivalence`'s own sketch proof hint is
  false as written**: nothing links shell to verifier.
* **F7** `accFixedBases_producer` holds for the empty table. **F8** a Surface with
  `irCheck := fun _ => false` satisfies `ir_refines` trivially. **G2** the fixture sets
  `encG2` to empty bytes, so **no `Eip2537.Holds` is satisfiable at the only Surface in the
  tree** and every field carrying `Holds` is unexhibited.

**Root cause, generalised:** `PlanView`, `Surface` and `LoweringPlan` each carry a *copy* of
a fact the Rust derives once - `hasAccumulator`, `numInstances`, `evaluator`, `encG2`, the
`quotient`/`direct` pair. Every copy without a pin is a vacuity. The `supportedQvmBool` bug
was this same class, introduced by the orchestrator while fixing a different vacuity.

**Adopted as D-P23:** every stated theorem and every consumed structure field must carry
both a **satisfiability witness** and a **falsifiability demonstration**. No witness means
vacuous; no breaking perturbation means decorative - defer it with a named blocker rather
than ship it. Statement reviews now repeat indefinitely, including after each repair round.

**Also recorded honestly:** the statement-fingerprint gate I built (42 text fragments)
cannot see any of F1, F7, F8. A gate over fragments is not a gate over meaning.

**In flight:** `P-REV-FIX` applying all ten repairs plus a duplicate-fact gate.

## Round 51-59 - the port finished and the proof programme ran

* **Generator port complete except three named gaps.** The deployed verifier contract
  renders **byte-exactly from a derived context** - 175,908 bytes, 3,024 lines, differing
  only in `BUILD_ID` (`Instances/DeployedProfile.lean:533`). Remaining: the circuit as data
  (`Data.new` refuses a default `ProtocolPlan`), templates are text not ASTs, and the
  `quotient_direct` arms need the untracked `.direct.sol` files.
* **My P-13 split missed six whole files** - 698 Askama lines, 30.1% of the deployed
  artifact, unassigned for four packages. Caught by a package measuring its own coverage
  gap; `gate 70` now makes a 14th template file a build failure.
* **Phase 3 delivered its first real result:** 327 values compared between live Rust and
  Lean, **zero divergences** - the Exec port finally has conformance evidence. The exporter
  delegates to the real transcript rather than re-implementing the schedule, and needed zero
  verifier edits.
* **Fixture provenance closed (R-56, R-57):** the committed poseidon fixture was **stale on
  arrival** - published 2026-04-29, transcript changed 05-01 and 05-02 - and no profile in
  this tree reproduces it. Not a port bug. **M0 is blocked on a fixture regeneration plus a
  profile decision plus a ruling on 12 orphan fixture files**, all awaiting the human.
* **The vendored dialect grew `memoryguard` and `setimmutable`** (authorised fork edit), so
  `RunContractIR` is inhabited: the deployed runtime object elaborates with no `sorryAx`.
* **P-SE stages 0-6 all landed.** `lowering_equivalence` is **stated** with a live
  hypothesis; `contractRef_noAcc_of_semanticEquivalence` is **proved**; stage 5 found an
  inherited blocker claim was false and turned `IdentityCorrespondence` into a derivation.

## Five false-as-written statements found, and one vacuity introduced

`end_to_end_noAcc`'s vacuous RHS (review F1) · `countdown_or_halt` · `decodeAcc_encode_-
pointPair` · `Inv_mono` · `main_concat` - each corrected by **strengthening** or by
restricting with the falsity recorded, never by silent weakening. Plus `supportedQvmBool`,
which I introduced while fixing one of those. Six statement defects in six stages is the
base rate, so every future brief assumes there is another.

## Recurring process failures, written down so they are not repeated

* **My grep produced a false defect claim that reached the human as a blocking decision.**
  `stmtsBeq` was reported as having no declaration; the grep was piped through `head -5`,
  which cut off before `vendor/`. Rule now: verify existence with `#check`, never grep.
* **Multi-line anchored edits deleted neighbouring lines five separate times** (a `case`
  `esac`, a `def` signature, a `match` arm, a `let` binding, and a threefold duplicate
  insertion). Every catch came from running the tool, not trusting the edit. The reliable
  pattern is a deterministic script with an assert on anchor uniqueness.
* **A killed perturbation harness left a semantic change in the tree** (`.reverse` deleted
  from `MultiPrepare.fEval`) that built clean and passed KATs (R-54). Rule: perturb copies
  outside the repo, or verify `git diff --numstat` after every run.
* **`Fr 17` is too small** for magnitude, width or truncation gates (R-55) - `truncate` is
  the identity there. Bit twice for real.
* **`Instances/` confinement greps direct imports only** (R-55), so a concrete model in a
  transitively-imported file stays invisible.

## Decisions - all taken (round 68)

The human took the recommended option on all six open decisions. Recorded as **D-P24 to
D-P29** in `docs/design.md`; `PLAN` section 0 amended for D-P24 (`4817b16`).

| # | decision | record |
|---|---|---|
| 1 | **Per-deployment first**, generic theorem as a stated follow-on | D-P24 |
| 2 | **Re-pin `Statements.lean`** - a hash freeze is not a licence to keep a known falsehood frozen | D-P27 |
| 3 | **M0: regenerate** the six live poseidon artefacts under the recorded profile, re-pin `BASELINE.md`, **delete the 12 unread fixtures** | D-P28 |
| 4 | **Constructor helpers first**; extend the vendored DSL for splicing only if that proves painful | D-P26 |
| 5 | **Security moves to ArkLib `Interaction`**; D-P21 finally implemented; deployed KS stays a named parameterised assumption | D-P29 |
| 6 | **`PROOF-PLAN` is NOT retired** - re-pointed at `Interaction`, with an explicit owner for the S7 bridge | D-P29 |

Plus **D-P25**: the generator emits Yul ASTs; `stmtsBeq` is the check of record for M3,
token comparison is the CI tripwire for Yul, line-based normalisation only for the Solidity
wrapper. **Checked while amending: PLAN section 11 already said AST equality** (`:556`), so
the plan was right and `VerifierPartials.lean` drifted - a narrower finding than R-62
recorded, and D-P25 confirms the plan rather than changing it.

### Still owed, not decisions

* **`fixedBases` "-G" defect** - still stores the identity (P-SE finding 7). Mine to schedule.
* **F-IR-1** - `extract_ir_builtins.py` basename collision; 28 of 42 manifest rows measured
  from the wrong artifact. One-line fix plus regeneration.
* **`Common/Bytes.lean` lemma** - `Array.foldl` is not defeq to `List.foldl` in 4.35.
* **Correction to an earlier claim here:** "nothing is pushed" was **false**. The work is on
  `origin/formal/baseline`; I asserted it twice before checking.

## Next

Refreshed round 72 - the previous list predated P-AST, P-4a2 and P-ENV entirely.

1. **D-P30 conversion, split per partial** (the current critical path): six remaining
   `Partial`s get real AST emitters, then `Quotient/Evaluator.lean` (18 string sites), then
   `VerifierPartials`/`Contracts`. Each slice gated by `stmtsBeq` against the text port, not
   token comparison alone. Gates P7, P9, P10.
2. **P-CURVE** - real-curve G1 model. Now the *only* remaining blocker to P5
   (`finalPairing_spec`), since P-4a2 closed the `EnvAgrees` blocker and P-ENV made the
   structure strong enough to reject a degenerate generator.
3. **P5** can proceed in parallel with (1) - FinalPairing's AST is real.
4. **M0 execution** (D-P28): regenerate poseidon artefacts, re-pin `BASELINE.md`, delete the
   12 unread fixtures.
5. **`Statements.lean` re-pin** (D-P27) - it still freezes a known-false statement.
6. **D-P21 implementation** - per-round `chalMass`; adopted round 51, still not done.
7. Small owed items: F-IR-1 basename collision, `Common/Bytes.lean` `Array.foldl` lemma,
   `fixedBases` "-G" defect, gate schema gap (two of three gates cannot see theorem-binder
   hypotheses).

**Blocked on nothing external.** All six round-68 decisions are recorded as D-P24..D-P29 and
D-P30; nothing is waiting on the human.
