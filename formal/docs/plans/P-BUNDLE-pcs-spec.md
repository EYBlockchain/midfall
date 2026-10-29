# P-BUNDLE - fix `pcs_spec`'s hypothesis bundle. Small, statement-layer, unblocked.

Status: READY. Found and confirmed by P-PLANVIEW. **The generator work is finished** (7 of 7
partials emit real ASTs, `emitPlaceholder` unreachable), so this is the next-highest-value
unblocked package - it needs no human decision, unlike the curve model.

## The hole

`pcs_spec` (`Partials.lean:599`) binds `hblk`, `hsup`, `henv`, `hperm`, `hcd`, `hinst`,
`hsnap` - and **no `hh : Eip2537.Holds`**. But its proof needs `g1Msm1` and `g1Add`:
Block 5 is a G1MSM staticcall and Block 6 is two G1MSM-1s and two G1ADDs.
`finalPairing_acc_spec` names those clauses for exactly the same reason; `pcs_spec` does not.

So `pcs_spec` currently asserts something about precompile behaviour with no hypothesis about
precompile behaviour. It is not false - it is **unprovable as stated**, and the bundle gate
did not catch it because `pcs_spec` is not a `LoweringCorrect` field.

## Deliverable

1. **Add the missing hypothesis** to `pcs_spec` (and check the other nine `*_spec` theorems
   for the same class - does each name every precompile behaviour its conclusion depends on?).
2. **Extend the bundle gate** to cover the ten `*_spec` theorems, not just
   `LoweringCorrect` fields. P-PLANVIEW's finding is that a theorem-binder hypothesis is
   outside `check_duplicate_facts` and `check_hypothesis_bundles` schemas - so a hole in a
   spec theorem's bundle is invisible to every gate. Close that: a spec theorem whose
   conclusion mentions a precompile address must bind `Holds`.
3. **Do not weaken any conclusion** to avoid the new hypothesis. If adding `Holds` makes the
   statement unprovable at the fixture, that is expected - `Holds` is unexhibited pending the
   pairing/torsion decision. Record it as such rather than leaving the hole.

## Constraints

* **Keep `SORRY.md` line numbers stable** where possible - P-PLANVIEW made its `Partials.lean`
  edits line-count-neutral so 12 registered sorries kept their numbers. If your edit shifts
  them, regenerate with `scripts/gen_sorry.sh` and verify.
* **D-P23 / R-41**: the new hypothesis needs a demonstration that it is load-bearing - show
  that without it the statement cannot express what the proof needs, or that a weakened
  bundle reddens a gate.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp, verify `git diff --numstat`.
* **Structure-update layout rule** (new standing note): a multi-field `{ x with ... }` must
  be on ONE line and the base must be a plain identifier - the error message points elsewhere.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Numbers from `lake build` and `scripts/checks.sh` only.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5154 jobs**;
`checks.sh` green: 64 tracked sorries, **1253 KATs across 83 files**, 111 statement
fragments, 12 fact families (9 pins, 2 derived, 2 declared gaps), 8 bundles (7 exhibited, 2
joint refutations), 107 modules, Statements hash OK.

Read first: `Midfall/Lowering/Partials.lean` (the ten theorems and their binders),
`Midfall/Assumptions/Eip2537.lean` (`Holds` and its clauses),
`Midfall/Lowering/GenAstPcs.lean` (`PcsBlockRole`, and what Blocks 5-6 actually emit),
`scripts/check_hypothesis_bundles.py`, `docs/REVIEW.md` R-62 and R-64.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1253.
- `pcs_spec` binds `Holds`; the other nine audited.
- The bundle gate covers spec-theorem binders, and is shown to redden on a weakened bundle.
- **Required finding**: after this, is every spec theorem's bundle complete relative to its
  conclusion - i.e. is the only remaining blocker for all ten the external pairing/torsion
  decision and the Exec widenings?
