# P-07R - RECOVER AND COMPLETE Midfall/Generator/Kzg.lean

Status: READY. This is a salvage task, not a fresh port.

## What happened

The P-07 agent was stopped mid-write. `formal/Midfall/Generator/Kzg.lean` exists at
**1,493 lines, 59 top-level decls, 0 gates**, and it is **truncated inside a function
body**: `lake build` with the module registered fails at Kzg.lean:1404 with
`unexpected token 'else'; expected ')', ',' or ':'`. It was never registered in
`formal/Midfall.lean`, so the tree is currently green and the file is inert.

The precise stop point: the last Rust cite in the file is around **KZ:1569-1576**, and
the last top-level def is `computations` (Kzg.lean:1232). In the reference,
`pub(crate) fn computations` spans **kzg/mod.rs:930-1927** - a single ~1,000-line
function. So the port died roughly 60% through that one function.

## What is left

1. Finish `computations` from about KZ:1576 to KZ:1927 (~350 Rust lines).
2. The `#[cfg(test)] mod tests` at KZ:1929-2226 (~300 lines) - reproduce its assertions
   as `#eval` gates, in the style Protocol.lean uses (a per-test mapping table in the
   header naming anything not reproduced and why).
3. **Audit the 1,493 lines that exist.** They have never been gated, never been reviewed,
   and their author was killed before it could write a single `#eval`. Treat every claim
   in them - including the header's "in full and in source order", which is currently
   false - as unverified until you have checked it against the Rust.
4. Answer the seven hazards in `P-07-kzg.md`, which the dead agent never reported on.
5. Register the module in `formal/Midfall.lean` **only once it compiles**.

## The two hazards that matter most, repeated here because they are load-bearing

- **Hazard 1, the BTreeMap insertion-order trap** (`construct_intermediate_sets_impl`,
  ~KZ:470): `point_idx_sets.entry(sorted).or_insert(point_idx_sets.len())` assigns
  insertion-order values under a sorted-key map. Trace every later use and say per use
  whether it is a lookup or an iteration. Check what the dead agent did here - it is the
  kind of thing that parses fine and is wrong.
- **Hazard 6, `validate_absorbed_g1_precompile_coverage`** is where PLAN 13's
  `points_subgroup_checked` risk lives. PLAN 9.5 states it as a theorem. If the code
  shows an absorbed G1 point reaching neither G1MSM/PAIRING nor an explicit check, STOP
  and report the counterexample.

## Rules

Read first: `docs/plans/P-07-kzg.md` (the original brief, item map and hazards),
`docs/plans/README.md` (standing notes - especially that `lake env lean` does NOT apply
lakefile options, so it accepts code `lake build` rejects; and that line numbers come
from `git show HEAD:<path>`, never `wc -l` on a dirty tree), and
`Midfall/Generator/Protocol.lean` for house style.

Binding: PLAN section 4 (R1-R11). `Vec` -> `List` in the Generator row. Reserved words
get a trailing underscore with the deviation recorded (`meta_` is already the convention
in this tree). R4: the reference profile is release, so overflow does not panic and
`debug_assert!` is compiled out, but indexing and division-by-zero do panic.

**No idle builds.** Run `lake build` in the background and keep working while it runs.

Reviews are deferred until the generator's semantic-equivalence results are done, so
your own perturbation evidence is the only second check this file will get before it is
committed. Report perturbations that fail to redden anything, plainly - that is what
made the P-05 and P-06 reports trustworthy.

Do NOT edit any Rust file, `Statements.lean`, or `SORRY.md`. Do NOT git add or commit.

## Acceptance

- `lake build` green with the module registered (currently 3378 jobs without it).
- `bash scripts/checks.sh` green; KAT count must rise from 354 across 32 files.
- At least 12 `#eval` gates, each with a perturbation actually run, plus non-vacuity
  evidence for every boolean gate.
- The header corrected so it states what the file actually contains, including any item
  not ported and why.
- A report with: status tails, the completed R11 line-range -> def table for the whole
  file (not just your additions), answers to hazards 1-7, perturbation evidence, and
  findings - including anything you find wrong in the 1,493 lines you inherited.
