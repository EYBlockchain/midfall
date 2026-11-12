# P-REPIN - execute D-P27: re-pin `Statements.lean`. A freeze must not protect a false statement.

Status: **ADOPTED round 68, still not executed.** The normative statements file currently
contains a theorem that is **known false**. That is worse than an unproved theorem, and it
has been sitting there for 24 rounds.

## The three actions D-P27 authorises

| theorem | line | problem | action |
|---|---|---|---|
| `verifyNative_iff_msgs` | 43 | **false** for a degenerate codec | add the codec-law hypothesis |
| `verifyMsgs_iff_spec` | 57 | cannot hold for every verifier environment | make it environment-dependent or scope it |
| `contractRef_noAcc` | 73 | superseded | mark superseded by the proved `contractRef_noAcc_of_semanticEquivalence` |

## Deliverable

1. **Amend the three statements** as above. Keep them *statements* - this file is the spec
   surface, not a proof file. Proofs stay elsewhere.
2. **Re-pin the SHA-256** the frozen-hash gate checks. Find the mechanism first: `checks.sh`
   section `== frozen statements hash ==` prints `Midfall/Statements.lean: OK`, so there is a
   stored digest somewhere under `formal/` - locate it, update it, and **show the gate reddens
   if the file changes without a re-pin** (edit a comment on a clone, confirm `OK` becomes a
   failure).
3. **D-P23 both halves for each amended statement:**
   * **satisfiability** - exhibit an object meeting the new hypotheses, so the repaired
     theorem is not vacuous;
   * **falsifiability of the OLD text** - keep or add a refutation showing the original
     statement was genuinely false, exactly as `g1DecodesOld_unsatisfiable` does for R-63.
     **Do not silently delete the false version.**
4. **Update every consumer** of the changed signatures, and re-check the axiom probe - the
   frozen statements currently depend on `[propext, sorryAx, Classical.choice, Quot.sound]`
   and that must not gain `native_decide` or anything worse.

## Constraints

* **This is the ONE authorised edit to `Statements.lean`.** It is normally frozen and
  hash-checked; D-P27 is the exception, and it is narrow - three statements, no others.
* **Do not weaken a statement into triviality to make it true.** A theorem with so many
  hypotheses that nothing satisfies them is the vacuity class this project has found ten
  times. Exhibit the witness.
* **RAM (D-P31):** state an expected peak before any VM evaluation and run it under
  `scripts/ram_guard.sh`. Baselines measured last package: warm build 0.74 GiB tree, cold
  build **16.86 GiB tree / 4.28 GiB largest process**, `checks.sh` 4.94 GiB. Use
  `--proc-limit` for parallel builds and `--limit` for a single heavy eval.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp.
* **`checks.sh` warning:** anchored edits have broken this file repeatedly. If you must touch
  it, insert with a script asserting the anchor appears exactly once, then `bash -n`, then a
  full run.
* Numbers from `lake build` and `scripts/checks.sh` only. `SORRY.md` delta should be zero
  unless a statement change legitimately moves a line - then regenerate and verify.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5154 jobs**, 108 modules; `checks.sh` green with **13 sections**: 64 tracked
sorries, **1286 KATs across 85 files**, 111 statement fragments, 12 fact families, 8 + 23
bundles, 30 baseline pins, Statements hash OK, memory report clean.

Read first: `Midfall/Statements.lean` (all 79 lines), `docs/design.md` D-P27 (the decision),
`docs/REVIEW.md` R-58 and R-63 (where the falsity was established and the retain-the-old-text
pattern), the hash mechanism `checks.sh` uses, and `docs/plans/README.md` standing notes.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green, including the frozen-hash section.
- All three statements amended, each with a satisfiability witness and a retained refutation
  of the old text.
- The hash gate is **shown to redden** on an un-re-pinned change.
- **Required finding**: after the re-pin, does any *other* statement in the frozen file have
  a known or suspected defect? Audit all of them - the point of this package is that the
  freeze had stopped being reviewed.
