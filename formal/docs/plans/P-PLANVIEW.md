# P-PLANVIEW - give `PlanView` the `ConstraintSystemMeta` + `Data` it lacks. Last AST gap.

Status: READY. P-STR2AST made `emitPcs` writable and wrote it, but it **cannot be wired**
because `PlanView` (`Inv.lean:111-171`) carries neither `ConstraintSystemMeta` nor `Data` -
exactly the two inputs `computationsAst` needs. This package closes that, and with it
`emitPlaceholder` becomes unreachable: **seven of seven partials real**.

## Deliverable

1. **`PlanView` gains the two fields** - either `meta_ : ConstraintSystemMeta` and
   `dat : Data` directly, or a reference to the assembled plan. **Decide and justify**:
   `ObligationsGates:514` already notes that `S.plan` arguably *should be* a `LoweringPlan`,
   so carrying two fields may be the wrong shape. If `LoweringPlan` is the right carrier,
   say why and do that instead.
2. **Derive, never hard-code.** `DeployedProfile` already assembles `poseidonMeta` /
   `poseidonInputs` and reproduces the artifact byte-exactly, but it lives in `Instances/`
   and its counts are **observations of the dump, not circuit derivations** - the circuit
   gap its own header names. Do not launder observed constants into derived ones.
3. **Wire `.pcs`** into `GenAst.emitPartial`; `placeholderPartials` must become empty, and
   `emitPlaceholder` either unreachable or total-with-an-emptiness-proof (D-P30 clause 4).
4. **Both gate relations + plan-dependence** for the pcs slice, reusing
   `computationsAst_beq_ok` / `_tokens_ok` / `pcsTaggedBlocks`. The `PcsBlockRole` tagging is
   what makes the partition inductable - the AST has **no comment node**, so positional
   identity alone loses the values the leading comments carried.
5. **Plant gate** in the `blkPinBites*` style, with a **direct** `SupportedS` exhibit (the
   transport does not typecheck - measured three times).

## Constraints

* **The duplicate-facts gate will react.** `meta_`/`dat` may duplicate facts already carried
  by `PlanView` (`numLookups`, `numTrashcans`, `numPermutationZs` are *derived from* the
  meta). If they do, either **delete the derived copies and compute them from the meta** -
  preferred, it removes copies rather than adding pins - or register the family with named
  pins. **Do not leave both a copy and its source unpinned.**
* **`data` is a Lean keyword** and cannot even be a parameter binder (P-STR2AST finding);
  `meta` collides with R2's `meta_` convention. Choose names deliberately.
* **Confinement**: a theorem-bearing file must not import `Instances/`. If the only source
  of real meta/Data is `DeployedProfile`, then `PlanView` gains the *fields* and the
  **exhibit** stays in `Instances/`. Say which is which.
* **No DSL extension, no fork edit.**
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - use an APFS clone under /tmp, verify `git diff --numstat`.
* **D-P23 / R-41**: witness AND failure mode for everything; report failures to redden.
* Correct the now-stale claim in `GenAst.lean`'s header that an AST emitter for pcs cannot
  exist - it does now (P-STR2AST finding 2).

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5153 jobs**;
`checks.sh` green: 64 tracked sorries, **1243 KATs across 82 files**, 11 fact families (9
pins), 8 bundles (7 exhibited, 2 joint refutations), 106 modules, Statements hash OK.

Read first: `Midfall/Lowering/Inv.lean` (`PlanView`, `parserFactsOfPlan` as the derivation
model), `Midfall/Lowering/GenAstPcs.lean` (`computationsAst`, `PcsBlockRole`,
`pcsTaggedBlocks`), `Midfall/Instances/DeployedProfile.lean` (the observed meta/Data and its
circuit-gap header), `Midfall/Generator/Encoding.lean` (`ConstraintSystemMeta:364`,
`Data:551`), `docs/design.md` D-P30.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1243.
- `placeholderPartials` is empty; `emitPlaceholder` unreachable or proved empty.
- The duplicate-facts gate is satisfied by **removing copies** where possible.
- **Required finding**: with all seven partials real, what is the state of the ten `*_spec`
  theorems - are their hypotheses now all nameable, and which remain blocked by the
  pairing/torsion decisions rather than by anything in the generator?
