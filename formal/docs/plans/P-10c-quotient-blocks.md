# P-10c - the `quotient.rs` items P-09h just unblocked

Status: READY. P-09h (Evaluator, `6337060`) reported these as FULLY UNBLOCKED or
WRITABLE. Doing them now is the shortest path to a producible `LoweringPlan`, which is
what `L.plan.qprog` and therefore PLAN 9.5's §9.5 statements need.

Reference: `lowering/quotient.rs`. Items, with what P-09h said about each:

| range | item | state per P-09h |
|---|---|---|
| 1471-1680 | `structured_permutation_loop_block` | fully unblocked |
| 1688-1934 | `structured_lookup_loop_block` | fully unblocked |
| 1941-1993 | `structured_trash_loop_block` | fully unblocked |
| 2000-2099 | `compact_quotient_computation_blocks` | unblocked transitively |
| 971-973, 975-983, 985-993 | `quotient_identity_expr`, `quotient_yul_expr`, `quotient_expr_from_plonk_expr` | re-filed / unblocked |
| 804-969 | `quotient_identity_parts` | writable, needs the bridge above |
| 1401-1417, 1419-1464 | the scratch-words and max-parallel items | re-filed as memory-layout, not Evaluator |

Lean target: extend `formal/Midfall/Generator/Quotient/FoldCompute.lean` **only if it is
yours to extend - it is not.** Put new items in `formal/Midfall/Generator/Quotient/
QuotientBlocks.lean` and report what FoldCompute's stale notes should say.

## Hazards

1. **Verify P-09h's unblocking claims before relying on them.** It reported four items
  fully unblocked and six re-filed as never-blocked. It also reported a defect in
  `FoldTypes.lean:504` that turned out to be **false** - `List.range'` takes a count, not
  an inclusive end, so the port was correct (see plans/README.md standing notes). Treat
  every inherited claim, including this package's own brief, as unverified until you
  check it against `git show HEAD:`.
2. **`List.zipIdx` yields `(element, index)`**, the reverse of Rust's `.enumerate()`. P-09h
  hit this at seven sites. Check every loop you port.
3. **The three loop blocks are the fold's producers.** P-10 could record and check a
  `FoldRecord` but could not produce a non-degenerate one, because `push_structured_fold`
  creates `Weighted` sites with an empty function name and `direct/emit.rs` fills in the
  names - deferred to M10. If these loop blocks are what actually populate the names,
  say so: it would mean the M10 deferral is narrower than PLAN 14.8 recorded. If they do
  not, state precisely what still blocks it.
4. **`compact_quotient_computation_blocks` was declined by P-10 as Evaluator-blocked.** If
  it now ports, that is the clearest signal the unblock is real. Gate it against the
  reference's own expectations, not just against your port.
5. **Do not pull in `direct/{mod,emit,layout,validate}.rs`** (M10) or the VK/template row.
  If an item needs one, report it as a scope error rather than importing around it.
6. **`quotient_template_program` (QRS:189) and the Direct row remain the blockers for
  `LoweringPlan::new`.** Do not claim P-11's blocker is cleared unless you have actually
  made a `LoweringPlan` constructible, and say plainly if you have.

## Rules

Read first: `docs/plans/README.md` standing notes - especially the two new entries on
`List.range'` and `List.zipIdx`, and the lesson about re-measuring inherited defect
claims. Also `lake env lean` does not apply lakefile options; line numbers from
`git show HEAD:<path>`; **register your module** (R-50).

Read the six `Quotient/` files, especially `Evaluator.lean` (the new dependency) and
`FoldCompute.lean`/`FoldTypes.lean` (whose notes you may make stale).

**R-41** (perturbations actually run inside each gate's scope; report failures to redden),
**R-48** (own fixture or assert distinctness), **D-P19** (read artifacts at `#eval` time),
**D-P17** (no theorems in a file importing Instances/; do not import `Generator.Vk`).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 767 across 45 files.
- At least 12 gates, including exact-line gates on the emitted Yul for each of the three
  loop blocks (the P-09h standard, not a smoke test).
- **Required finding**: state whether a non-degenerate `FoldRecord` can now be produced
  by shipped code rather than hand-built, and whether anything moved on the path to a
  constructible `LoweringPlan`.
