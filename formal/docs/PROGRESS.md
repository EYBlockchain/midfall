# Midfall formal - progress log

**Standing practice (D-P23 + human instruction, round 61): update this file every time a
work package lands.** Normative plan is `PLAN.md`; proof programme is
`docs/plans/P-SE-semantic-equivalence.md`; findings are `REVIEW.md`; decisions are
`design.md`; estimates and velocity are `ROADMAP.md`. This file is the running narrative of
**where we actually are**, newest first.

## Measured state - round 61

| | value |
|---|---|
| `lake build` | green, 5143 jobs (cached rebuild 2.3 s) |
| Lean | **99 modules, 82,492 lines**, all reachable (orphan gate) |
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

## Open with the human

1. **M0 tag** - blocked on the fixture regeneration decision above. Recommendation given.
2. **Vendor dialect** - done for the two builtins; `irOptimized` vs `ir` pinned to `ir`.
3. **`Common/Bytes.lean` lemma** - `Array.foldl` is not defeq to `List.foldl` in 4.35;
   gates two holes. Authorised, queued.
4. **F-IR-1** - `extract_ir_builtins.py` keys by basename, so 28 of 42 manifest rows were
   measured from the wrong artifact. One-line fix plus regeneration.
5. **F5 / D-P21** and **F6 / D-P22** - recorded as decisions; both are paper-proof work.
6. **Nothing is pushed.** ~30 commits ahead of `origin/formal/baseline`, all local-only.

## Next

1. `P-REV-FIX` lands -> **second statement review pass** (D-P23 requires repeating after
   repairs, because repairs can introduce new vacuities).
2. F-IR-1 fix, `Common/Bytes.lean` lemma.
3. M0 once the fixture decision is made.
4. M5-M8 proving work - the long pole now that the statements exist.

