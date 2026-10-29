# P-STR2AST - convert the remaining text emitters to AST: `Quotient/Evaluator.lean` + `Kzg.computations`.

Status: READY. Per P-AST4's required finding, these are **one package** - same representation,
one consumer chain - and this conversion is what unblocks `pcs`, the last placeholder.

## Why one package, and why before the plan relocation

`Kzg.computations` (`Kzg.lean:1320`) returns `Except Fault (List (List String))` - the same
string machinery as `Quotient/Evaluator.lean`'s 18 sites. **There is no runtime Yul parser in
the vendored tree**, so an AST emitter for `pcs` cannot exist until the computations emitter
produces AST. Converting them together is one representation change, not two.

The `LoweringPlan` relocation delivers **no gate on its own** - it only becomes checkable once
the text is AST. Doing it first buys a blocked package.

## Scope

1. **`Quotient/Evaluator.lean`** - the `yul_emit.rs` port. Today: `abbrev Lines := List
   String`, `letLine v rhs := "let " ++ v ++ " := " ++ rhs`, `assignLine`, `u256String`,
   `columnEvalVar : String`, builders returning `E F (Option (List String))` that
   concatenate loop headers and `0x` pointer renderings. **Expressions must not be
   string-concatenated** (D-P30): numbers become `Literal.number`, variables
   `Expr.ident`/`Stmt.assign`, calls `Stmt` forms.
2. **`Kzg.computations`** - same conversion, preserving its block *partition* (the eight
   blocks and their boundaries are what `pcs_spec` will induct over).

## The cross-check problem, and how to solve it

D-P30 clause 2 says keep the text port as the reference. Here the text port **is** the thing
being converted, so the cross-check must be: **render the new AST through the vendored
printer and compare tokens against the old string output**, with the numeric-spelling
divergence pinned as a string-containment gate (hex vs decimal is invisible to every AST
relation - standing note). If that is not achievable for some construct, **stop and report**
rather than dropping the old path.

## Constraints

* **No DSL extension, no fork edit.** Five slices have been built with constructor helpers
  alone, including five for-loops with init/cond/post, nested scopes, multi-target
  assignment, and a List-valued plan field. If something genuinely needs splicing, report it.
* **`yul%` cannot write `end`** - use Lean's guillemet escape (P-AST4 found this).
* **Numeric spelling is invisible to every AST relation** - string-containment gate.
* **Watch the `/-! ---- -/` trap** - a dash run after `/-!` makes the rest of the file an
  unterminated comment, reported only at EOF.
* **Plan-dependence gates are required, not optional.** P-AST4 reproduced the finding: a
  hard-code against a profile whose values match reddens neither AST relation. Every
  interpolated value needs a gate that perturbs the plan and requires the output to move.
* **The quotient-region boundary question must be settled here or explicitly deferred.**
  `blk .quotientLin` currently excludes the two `quotient_numerator` includes (826 B +
  6,682 B). Converting them is this package's work if you take it; if you do not, say so and
  leave the boundary as recorded.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - use an APFS clone under /tmp and verify `git diff --numstat` (P-AST4's
  method worked well). Register modules (R-50). Numbers from `lake build` and
  `scripts/checks.sh`.
* **D-P23 / R-41**: witness AND failure mode for everything; report failures to redden.

## Sizing - split if needed

This is large. **Split by file if one session is too long**: `Evaluator.lean` first (it gates
the quotient region), then `Kzg.computations` (it gates `pcs`). Each sub-package must leave
the tree compiling and all gates green. Do not half-register.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5151 jobs**;
`checks.sh` green: 64 tracked sorries, **1221 KATs across 80 files**, 110 statement
fragments, 11 fact families (9 pins), 8 bundles (7 exhibited, 2 joint refutations), 104
modules, Statements hash OK.

Read first: `docs/design.md` D-P30 (the no-raw-strings rule and its acceptance clauses),
`Midfall/Lowering/GenAst.lean` (the constructor-helper vocabulary you must reuse -
`yfor`, `ysetN`, `ylet`, `yblock`), `Midfall/Generator/Quotient/Evaluator.lean` (the 18
sites), `Midfall/Generator/Kzg.lean:1320` (`computations`), `Midfall/Generator/YulGolden.lean`
(`yulTokens`, `stmtsBeq`), and `docs/plans/README.md` standing notes.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1221.
- Both files emit AST, cross-checked against their own prior text output via the printer.
- Plan-dependence gates for every interpolated value.
- **Required finding**: with the text converted, can `emitPcs` now be written, and does the
  eight-block partition survive as an inductable structure for `pcs_spec`?
