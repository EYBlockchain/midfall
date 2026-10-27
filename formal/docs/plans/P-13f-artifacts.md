# P-13f - `artifacts.rs`: gap B, the last thing between the port and P-SE

Status: READY. `src/lowering/artifacts.rs` (342 lines). P-13d named this as gap B:
**nothing in `Midfall/` constructs a `Halo2Verifier` record** - the ~60 template inputs
are computed only in Rust. Until it lands there is no Lean path from a `VerifyingKey` plus
plan to a template model, and therefore no `deployed_equivalence`.

## Why this is the highest-value remaining port work

Gap A is closed (`dc9a552`): the deployed contract renders byte-exactly from Lean -
**but from a hand-transcribed context.** `poseidonCtx` and `poseidonMemoryLayout` are
readings of the artifact, with the residual self-fulfilment stated on the def (P-13e F2).
This package replaces transcription with derivation: compute the same fields from the VK
and plan, then check they reproduce the artifact. **That is the difference between a
golden test and evidence.**

## What it must produce

The `Halo2Verifier` / `Halo2VerifyingKey` / `Halo2QuotientEvaluator` template models -
i.e. fill `PartialCtx`'s 63 fields and `RootCtx` from a `LoweringPlan` + `VerifyingKey`
rather than from the artifact. Every field currently in `poseidonCtx` should become a
derived value with a `M:`/`ART:` cite.

## Hazards

1. **The known blockers.** P-11 reported that no Lean term can produce a `LoweringPlan`
   because `quotient_template_program` (QRS:189-238) is unported and the Direct row is
   M10. P-09h unblocked several `quotient.rs` items and P-10c more. **Re-derive the
   current blocker list from the tree before assuming any of it still holds** - three
   consecutive packages have found inherited blocker claims stale, and one found a
   blocker claim that was simply false.
2. **Do not fake derivation by reading the artifact.** If a field cannot be derived yet,
   leave it as an explicit input with a named blocker. A gate that reads the answer from
   the artifact and then checks the render against the artifact is circular - P-13e
   flagged exactly this risk on `poseidonMemoryLayout` and stated it rather than hiding
   it. **Say which fields are derived and which are still transcribed, as a table.**
3. **`VerifierMemoryLayout::new` IS ported** (`LayoutMemory.lean:140`) - a prior package
   claimed otherwise and was wrong. `ConstraintSystemMeta` and `Data` are ported
   (`Encoding.lean:364`, `:551`). Use them.
4. **D-P17 is the binding constraint on the shape of this module.** No `Generator.Vk`, no
   `Midfall/Instances/`. But the concrete VK is what makes the deployed profile
   checkable - so split: derivation functions in a theorem-safe file, concrete instantiation
   in `Instances/`. `LoweringPlan.lean` and `Calldata.lean` both established this pattern.
5. **Re-measure everything.** My briefs have been wrong about counts in seven consecutive
   packages, including one that missed six whole files.
6. **Every byte gate asserts length AND line count.** `occursOnce` plus a prefix boundary
   is satisfied by a truncated render, and a strict SUFFIX also occurs once (P-13e gate 82).

## Rules

Read first: `docs/plans/README.md` standing notes; `VerifierPartials.lean` (`PartialCtx`,
`poseidonCtx`, gates 69-89); `Contracts.lean` (`RootCtx`, `poseidonParts`, gate 29's
whole-file equality - **that is your target to reproduce by derivation**);
`LoweringPlan.lean`; `P-SE-evidence/attack.md` FIX lines (binding).

**R-41**, **R-48**, **D-P19**, **D-P13**, **D-P17**. Binding: PLAN section 4;
`Vec` -> `List`; R4 release profile.

**No idle builds.** Anchored multi-line edits have cost the orchestrator ten swallowed
lines across three repairs - re-read what you changed, rebuild after each.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 965 across 51 files.
- At least 12 gates.
- **Required finding**: a table of `PartialCtx`/`RootCtx` fields marked derived vs
  transcribed, and a statement of whether gate 29's whole-file equality can now be
  reached from a `VerifyingKey` rather than from the artifact. If it cannot, name the
  precise remaining blocker - that is the gate on starting P-SE stage 2.
