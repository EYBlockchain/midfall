# P-10 - `quotient.rs` + `direct/folds.rs`: where the fold actually lives

Status: READY. P-09a..f landed the whole QVM block (types, interpreter, builder,
certifier, validator, recognizers). ~2,644 Rust lines; split into two packages.

**Why this package now rather than `yul_emit`.** `yul_emit.rs:27` says its own output is
`(yul_lines, final_var)` and "the caller in `lowering/quotient.rs` folds" them. So the
y-batch fold and the assembly of quotient contributions live in `quotient.rs`, which is
exactly the object D-P20 item 1 says is modelled nowhere. Answering the fold question
requires this file, not the emitter.

**Hard dependency:** `quotient.rs` imports `quotient_numerator::direct::folds::{
FoldBucket, FoldLabel, FoldLoop, FoldSite, FoldWeight, SiteLabel}`. So `direct/folds.rs`
(497 lines) ports with it even though the rest of `direct/*` is deferred to M10 (PLAN
14.8). Do not defer `folds.rs`.

## Split

| pkg | range | ~lines |
|---|---|---:|
| P-10a | `direct/folds.rs` + `quotient.rs` records (`QuotientStateSlots`, `QuotientComputationBlocks`, `QuotientHelperFlags`, `NativeGateCandidate`, `NativeGateSelectionState`) and their impls | ~900 |
| P-10b | `quotient.rs` computation: the block builders, the native-gate knapsack selection, the fold assembly | ~1,750 |

Enumerate the real items against `git show HEAD:` first and correct this table - every
plan range this session has been a few lines off, and P-09f found four substantive errors
in its brief including a whole missing u16 guard.

## The required finding: does the fold become statable?

D-P20 item 1 says `QVM.run(prog, frame) : Except Fault Output` has no reference
counterpart, and that `frameOf`/`outputOf`/`quotientParts` are "Yul-side and modelled
NOWHERE". Three packages have since touched the fold without executing it (P-09c emits
`FOLD_MAIN`/`FOLD_SELECTOR`, P-09b rejects them inside an identity, P-09d inspects their
bytes positionally). This package is where the y-batch accumulation and the negation
written to `QUOTIENT_EVAL_MPTR` should become representable. Report explicitly:

1. Does `quotient.rs` contain a Lean-portable model of the fold, or is the fold purely a
   Yul-emission concern that no Rust function computes?
2. If it is portable: can `qvm_compile_correct` now be stated in a whole-stream form,
   or is per-identity still the only honest shape? Name every remaining missing object.
3. If it is not portable: say so plainly, because then PLAN 9.5's `qvm_compile_correct`
   must be restated per identity and the exclusion recorded rather than implied. That is
   a decision for the orchestrator, not something to paper over with a fixture.

## Hazards

1. **`NativeGateSelectionState` is a gas/byte knapsack** (`config.rs`:
   `DEFAULT_QUOTIENT_NATIVE_GATES = 4`, "selection is a gas/byte knapsack under an
   estimated native callback byte budget"). Knapsacks are order-dependent and tie-
   sensitive. Mirror the greedy selection exactly, including tie-breaks, and gate that a
   different selection order would give a different answer - otherwise the port silently
   normalises a choice the reference makes.
2. **`QuotientComputationBlocks::default()` is load-bearing.** `QuotientRendering::
   helper_flags` calls `default().helper_flags()` for the External and Direct arms. If
   the Lean default differs, the Direct path (deferred to M10) inherits a wrong shape.
   Pin the default field by field.
3. **The `outerSingleHCommitment` / `fewerPointSets` feature interactions.** `quotient.rs`
   is where `num_quotients` meets the block builders. R8: both branches, deployed one
   identified against `Features.solidity`.
4. **Do not pull in `direct/{mod,emit,layout,validate}.rs`** - deferred to M10 (PLAN
   14.8). `folds.rs` only. If something in `quotient.rs` needs a deferred item, report it
   as a scope error in the cut rather than importing around it.
5. **Retire what you make stale, by report not by edit.** P-09f left a list: VmBuilder
   notes at :39-47, :215-229, :805-809, and the "P-09e" mislabels; VmTypes :510 and :406;
   VmCertify :211-215, :1034-1036, :1860-1862. Add yours. Also fix the package-label drift
   (F-d) if you touch those files' claims.
6. **`Supported.qvm` still lacks the one-argument bridge** (`plan.rs:626-643`, P-11). If
   this package produces the pieces it needs, say so; do not build it sideways.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`; **register your module** -
R-50), and the six `Quotient/` files. REVIEW.md R-30, R-38, R-40, R-41, R-48, R-50,
R-51, R-52, plus D-P17, D-P19, D-P20.

**R-41** (perturbations actually run; report failures to redden - P-09f found five
reference guards that cannot bind and said so), **R-48** (own fixture or assert
distinctness), **D-P19** (read artifacts at `#eval` time), **D-P17** (no theorems in a
file importing Instances/).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file compiling or
unregistered - never half-written and registered. P-09f disclosed a mid-session truncation
and re-ran everything against the final bytes; that is the standard.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 656 across 41 files.
- At least 14 gates across the two halves, including the knapsack order-sensitivity gate
  (hazard 1) and the default-blocks pin (hazard 2).
- **The required finding on the fold**, answered in all three parts above.
