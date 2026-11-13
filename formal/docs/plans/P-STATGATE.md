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

## RESULT (executed by P-STATGATE)

**Status: DONE.** `lake build` green at 5155 jobs; `bash scripts/checks.sh` green, 13
sections; 64 tracked sorries unchanged (two rows moved line numbers because comment edits
shifted them, regenerated with `scripts/gen_sorry.sh`); Statements hash
`40d97dc7…dc6e` OK.

### What was added

1. **`STATEMENTS` section in `scripts/check_statement_fingerprints.py`**, eight kinds of
   clause, every one of them two-sided:
   * `STATEMENTS_EXACT` - the whole statement, binders and type, modulo whitespace;
   * `STATEMENTS_PINS` - `must` the repaired shape (`hc : E.g1.compressedRoundtrip`,
     `Spec.accepts E …`, the SUPERSEDED text) and `must_not` the refuted shape (the
     binder-free `verifyNative_iff_msgs :`, the E-free `Spec.accepts H F …`, the
     `p ≤ 2^256` pile-up the repair deliberately declined, `↔ True`);
   * `PLACEHOLDER_BINDER` - a frozen hypothesis hollowed to `(hc : True)`;
   * `STATEMENTS_DECLS` - the COMPLETE declaration set, so a fourth statement cannot arrive
     unpinned;
   * `STATEMENTS_BINDERS` - the four `variable` blocks, because a Lean theorem's statement is
     its variable context plus its binders plus its type;
   * `STATEMENTS_IMPORTS` - the trusted surface, pinned exactly (this makes the two dead
     imports visible instead of merely noted);
   * `STATEMENTS_DOCS` - the doc-string provenance, which is the only way "marked superseded"
     can mean anything to a gate;
   * `REPAIR_PINS` + the hollow-citation check - the D-P23 witnesses the frozen file cites must
     exist, keep their shape, and (for the retained OLD texts) must NOT be upgraded to the
     repaired shape, or they refute nothing.
   * `FROZEN_CITED_DEFS` - `G1Codec.compressedRoundtrip` and `Spec.accepts` themselves, the two
     cited definitions through which the repair could be undone WITHOUT touching the frozen
     file at all.
2. **`scripts/check_frozen_axioms.py`**, wired into `checks.sh` in place of the old two-line
   print. The rule: the declaration list is read FROM the file (the old print named three by
   hand); each of the three pinned statements must depend on EXACTLY
   `propext, sorryAx, Classical.choice, Quot.sound`; any further declaration must stay inside
   those four and must still carry `sorryAx`; `native_decide` and `ofReduceBool` are named and
   rejected (matched as substrings, because Lean mangles the generated axiom name after the
   declaration); a declaration the probe did not report is a failure, so silence is not a
   pass; and the eight D-P23 witnesses must carry NO `sorryAx` - they are proofs, and a
   re-sorrified witness keeps every text pin green while the obligation goes undemonstrated.
   `sorryAx` on the frozen statements is EXPECTED and asserted present: a gate that failed on
   it would be red on every honest version of this file.
3. **Stale claims cleared** (all comment-only, no statement touched): `Assumptions/Codec.lean`,
   `Lowering/Obligations.lean` ×2, `Halo2/Exec/Native.lean` ×2, `Instances/NativeE2E.lean` ×2,
   `Lowering/SemanticEquivalence.lean`. **Docs**: `design.md` D-P27 marked EXECUTED with the
   digest and the two open human decisions; `PLAN.md` §9.2 sketch annotated; `REVIEW.md` line
   reference corrected 43 → 65; `survey.md` and `critic.md` given corrigenda that annotate
   rather than rewrite, because they are dated evidence of what was frozen.
4. **NativeE2E KAT (8) docstring corrected**: it is the executable shadow of the PRE-D-P27
   shape, because `repair1_law_is_not_free` proves `expG1Codec` - the codec this fixture runs
   on - FAILS `compressedRoundtrip`. The computation is unchanged and still true.

### Demonstrated red

14 fingerprint controls and 3 axiom controls, all on an APFS clone under `/tmp`, each restoring
byte-identically: D1 drop the codec law · D2 `(hc : True)` · D3 re-add `p ≤ 2^256` · D4 E-free
`Spec.accepts` · D5 un-mark SUPERSEDED · D6 weaken a `variable` block · D7 add an import ·
D8 rename a frozen statement · D9 delete a cited witness · D10 upgrade a retained OLD text ·
D11 `compressedRoundtrip := True` · D12 revert it to the rejected encoder-first form ·
D13 `Spec.accepts := True` · D14 revert `accepts` to the E-free arity. A1 a new frozen
statement proved by `native_decide` · A2 a new frozen statement with no `sorry` · A3 FILL
`contractRef_noAcc`'s sorry from the proved lemma. In A1-A3 the OLD print exited 0 on the same
build the NEW gate reddened - the demonstration that the probe was a report.

### REQUIRED FINDING: what still cannot be detected being weakened

* **The other cited definitions.** `verifyNative`, `decodeRust`, `verifyMsgs`, `prepareMsgs`,
  `Lowering.ContractRefAccepts`, `VerifierEnv` and its four fields, `vk.WellFormed`,
  `Features.solidity`, `keccak256`. The frozen text names all of these and stays byte-identical
  if any of them is relaxed. `ContractRefAccepts` is the sharpest: it is Bool-valued, so the
  left arm of statement 3 silently means `= true`, and a version that stopped consulting the
  verifier would keep the frozen text whole. Pinning this surface is a package of its own;
  `FROZEN_CITED_DEFS` is the mechanism and takes two entries today.
* **Meaning, not shape.** Every clause here is a text or axiom-set pin. Only a proof is a
  meaning check. The repaired statement 1 is no longer known false; it is also not known true -
  it has no executable instance at all, since `repair1_law_is_not_free` shows the tree's only
  runnable codec fails its hypothesis and `canonEnv` has no KAT.
* **Witness-to-statement linkage.** `repair1_satisfiable` is pinned as `∃ E, E.g1.compressedRoundtrip`
  and the frozen doc string is pinned as citing it, but nothing in Lean says the witness is a
  witness TO `verifyNative_iff_msgs`. Change the statement's hypothesis to a different
  satisfiable law and both pins stay green while the D-P23 half no longer supports the claim.
  Closing it needs a proof-file change, which this package was told not to make.
* **Docstring English.** The gate pins keywords and cross-file existence, not that the prose
  about them is true.
* **`SORRY.md` is positional.** It records `file:line`, so a registered hole is not tied to a
  named declaration. This package's own comment edits shifted two rows - the fragility is real
  and visible.
* **`hwf` load-bearing** (statement 2) and the **scalar half** of the codec repair
  (`frOfRepr?`/`frToRepr`, still a registered sorry) are pinned as they stand and not
  protected from being insufficient. `hwf` is Phase 4 per the brief: flagged, not fixed.
* **The dead imports are pinned as PRESENT.** Deliberate - the gate records the surface rather
  than taking the decision - but it does mean a green gate currently defends two imports the
  project has called undesirable. The decision is recorded in D-P27.
* **And the point of all of it:** `Midfall/Statements.sha256` is not itself gated. A re-pin can
  make the hash gate green for ANY text. The fingerprint pin is now the only thing that survives
  such a re-pin and asks why.

