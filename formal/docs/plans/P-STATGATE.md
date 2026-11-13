# P-STATGATE - give the frozen normative file semantic coverage, and clear the stale claims.

Status: READY, and **urgent in a specific sense**: P-REPIN just spent a whole package removing a
known-false theorem from `Midfall/Statements.lean`, and **nothing prevents a future re-pin from
silently putting it back.**

## The gap, independently confirmed by the orchestrator

All three structural gates - `check_statement_fingerprints.py`, `check_duplicate_facts.py`,
`check_hypothesis_bundles.py` - have **zero mentions of `Statements`**. Deleting the
`compressedRoundtrip` hypothesis from the frozen statement leaves the build and every semantic
gate green. **The hash detects any change but validates none** - it proves the file is the
file, not that the file is correct.

This is the fourth structural gate blind spot found this session (after theorem-binder
hypotheses, `EnvAgrees` clause types, and the `Holds` clause texts), and it is the most
important one, because `Statements.lean` is the normative surface.

## Deliverable

1. **A `STATEMENTS` section in `check_statement_fingerprints.py`** pinning, at minimum:
   * `E.g1.compressedRoundtrip` present in `verifyNative_iff_msgs`'s binders;
   * `Spec.accepts E` - the environment threading;
   * `contractRef_noAcc` marked superseded;
   * and a **`must_not`** clause rejecting the old E-free `Spec.accepts H` form and a
     `verifyNative_iff_msgs` without the codec law, so the refuted shapes cannot return.
   **Show each reddens** by reverting the corresponding repair on a clone.
2. **Make the axiom probe a gate, not a print.** It currently exits 0 while all three frozen
   statements carry `sorryAx`. Decide and record the rule: `sorryAx` is *expected* for
   unproved spec statements, so the gate should assert the axiom set is **exactly** the
   expected four and **reject `native_decide` or `Lean.ofReduceBool`** - a change in shape,
   not mere presence.
3. **Clear the stale claims** that now contradict the repaired file - each still says the defect
   is live: `Assumptions/Codec.lean:35-42`, `Lowering/Obligations.lean:645` and `:652`,
   `Halo2/Exec/Native.lean:84` and `:99-112`, `Instances/NativeE2E.lean:48` and `:406`,
   `Lowering/SemanticEquivalence.lean:27`. Update the docs recording the old digest or old
   line numbers (`survey.md`, `critic.md:84`, `REVIEW.md:676`, `PLAN.md:291-293`), and mark
   **D-P27 EXECUTED** in `design.md` with the new digest.
4. **Fix the misleading KAT docstring** from audit finding 6: `NativeE2E` KAT (8) is documented
   as the executable shadow of the frozen statement, but `repair1_law_is_not_free` proves the
   only runnable codec **fails** the new hypothesis - so it shadows the OLD shape. Correct the
   docstring to say what it actually shadows.

## Explicitly NOT in scope

* **Do not edit the three frozen statements themselves.** They were just repaired; this package
  protects them.
* **Do not remove the two dead imports** (`Security.SRS`, `Security.Challenges`) without a
  separate decision - they widen the trusted surface for no reason, but that is a statement-
  surface change and D-P27 was narrow.
* **Do not fill `contractRef_noAcc`'s `sorry`** even though `repair3_rederived` shows it is
  provable - the spec surface deliberately holds statements, not proofs. Record it as a
  decision for the human instead.
* **`hwf` load-bearing question** (audit finding 4) is Phase 4 work - flag, do not fix.

## Constraints

* **`checks.sh` hazard**: anchored edits have broken this file repeatedly. Insert with a script
  asserting the anchor appears exactly once, then `bash -n`, then a full run, then grep the
  occurrence count. **Never blind-retry a call you think failed - inspect first.**
* **RAM (D-P31)**: state an expected peak before VM work and run under `ram_guard.sh`.
  Baselines: warm build ~4 GiB tree, cold build 16.86 GiB tree / 4.28 GiB largest proc,
  `checks.sh` 4.94 GiB. Use `--proc-limit` for parallel builds.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Verify existence with `#check`. **Never perturb the working tree in place.**
* Numbers from `lake build` and `scripts/checks.sh` only. `SORRY.md` delta should be zero.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5155 jobs**, 109 modules; `checks.sh` green, 13 sections: 64 tracked sorries,
**1286 KATs across 85 files**, 111 fragments, 12 fact families, 8 + 23 bundles, 30 baseline
pins, Statements hash `40d97dc7…dc6e` OK.

Read first: `Midfall/Statements.lean`, `Midfall/Instances/StatementsRepair.lean` (the
witnesses and retained refutations to pin against), `scripts/check_statement_fingerprints.py`
(its existing section structure), `scripts/checks.sh` (the axiom probe), `docs/design.md`
D-P27 and D-P30.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- **The new gate reddens when each repair is reverted** - one demonstration per pinned clause.
- All stale claims cleared; D-P27 marked EXECUTED with the digest.
- **Required finding**: is there now any statement in the frozen file that a gate cannot
  detect being weakened? Enumerate what remains unprotected after this package.
