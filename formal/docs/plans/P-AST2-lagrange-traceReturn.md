# P-AST2 - convert `lagrange` + `traceReturn` to AST emission. First D-P30 slice.

Status: READY under **D-P30**. Split per partial (or per pair) as the decision directs -
each slice is independently checkable, and the interruption pattern punishes large packages.

## Why these two first

They are the two partials that **already have `yul%` AST snapshots** in the tree
(`lagrange_ast`, `traceReturn_ast`, both in `VerifierPartials.lean`), so the target shape is
known-good and the gate template is already written. This slice establishes the pattern and
the per-slice gate shape cheaply, before the harder pairs (`pcs`, `quotientLin`) that need
`Kzg.computations` converted from text.

## Deliverable

For each of `lagrange` and `traceReturn`:

1. `emitLagrange (pv : PlanView) : Block Op` and `emitTraceReturn (pv : PlanView) : Block Op`,
   built with **constructor helpers** - no `yul%` splicing, no DSL extension, no fork edit.
2. Add to `GenAst.emittedPartials` (currently `[.finalPairing]`).
3. **Gate with `stmtsBeq` against the text port parsed output**, not token comparison alone.
   P-AST measured that an `mcopy`-as-user-call mis-spelling left all four token gates green
   while `stmtsBeq` reddened. Token comparison is the tripwire; `stmtsBeq` is the record.
4. **Re-check the `blkPinBites*` family** and add the equivalent non-vacuity gate for each
   newly real slice. `BlkIsEmitter` pins `blk` and `L.main` to the emitter; once these are
   real, a plant previously excluded because it differed from a placeholder must still be
   excluded by the real emitter.
5. Keep the text port and its byte-exact gates in place - each converted slice is validated
   against something the converter does not control.

## Numeric spelling

The AST stores `Literal.number (n : Nat)` and prints decimal; the Rust emits hex. **Pin the
mapping explicitly** as a documented divergence - do not normalise it away. This is one of
the two reasons comparing modulo comments reports differences on identical code.

## Out of scope - say so in the header

The **Solidity** wrapper (`Constructors.sol`, `Constants.sol`, `PrecompileSmoke.sol`, the
three contract shells) is not Yul, has no AST, and stays text with the line-based
normaliser. Write that in the header of any file you touch so a later package does not
fix it.

## Constraints

* **No `yul%` DSL extension, no fork edit.** If a slice genuinely cannot be built without
  splicing values into `yul%`, **stop and report it** as a tooling finding.
* **`emitPlaceholder` must shrink toward unreachable.** A `Partial` silently yielding a
  placeholder is the R-62 defect class. After this slice, five remain; state which.
* **D-P23 non-vacuity** on everything you state: witness AND falsifiability.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** (R-54). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh` only.
* Keep the three structural gates green and **accurate**. Note two of them cannot see
  theorem-binder hypotheses (P-ENV confirmed) - do not claim coverage you do not have.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5149 jobs**;
`checks.sh` green: 64 tracked sorries all owned, **1174 KATs across 78 files**, 84 statement
fragments, 9 fact families, 8 bundles (7 jointly exhibited), 102 modules, Statements hash OK.

Read first: `docs/design.md` D-P30 (the decision), `Midfall/Lowering/GenAst.lean` (copy the
`emitFinalPairing` pattern), `Midfall/Generator/VerifierPartials.lean` (the text port and the
existing `lagrange_ast` / `traceReturn_ast` snapshots), `Midfall/Generator/YulGolden.lean`
(`yulTokens`, `stmtsBeq` usage), and `Midfall/Instances/SurfaceFixture.lean` (the
`blkPinBites*` family).

**No idle builds.** Re-read what you changed after every edit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1174.
- Both slices emit real ASTs, gated by `stmtsBeq` against the text port.
- `emittedPartials` has three entries; the remaining four are named.
- **Required finding**: does the per-slice gate template generalise to `pcs` and
  `quotientLin`, or do those need `Kzg.computations` converted first? That decides the next
  package scope.
