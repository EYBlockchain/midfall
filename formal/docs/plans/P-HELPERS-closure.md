# P-HELPERS - close the undefined-function gap: `batch_invert`, `scalar_inv`, `validate_public_accumulator`.

Status: READY. Found by P-AST3a, narrowed by P-BUNDLE, **still open**. This is a defect in the
generator's output, not a missing feature.

## The defect, and why it is invisible

`GenAst.emitHelpers` defines `fail`, `transcript_init`, `common_word`, `common_uncompressed_g1`,
`squeeze_to`, `ec_pairing`. But the **real** emitted slices call:

| callee | called by | status |
|---|---|---|
| `batch_invert` | `lagrange` (real since P-AST2) | **undefined** |
| `scalar_inv` | `pcs` (real since P-PLANVIEW) | **undefined** |
| `validate_public_accumulator` | `vkLoading` acc arm (untaken in this profile) | **undefined** |

**`BlkIsEmitter` is still SATISFIED** - it pins `main` to `emitMain`, and `emitMain` really does
contain what the emitter produces. So the pin passes while the emitted program references
functions that are never defined and therefore **cannot run**. A satisfied pin over an
unrunnable program is invisible to every gate we have - P-AST3a said so when it found this,
and four packages have gone past it.

## Deliverable

1. **Emit the missing helpers** as ASTs, in template order, each gated the standard way:
   `stmtsBeq` against a `yul%` quotation of the text port's slice as the record, `yulTokens`
   as the tripwire, **plus a plan-dependence gate** where the helper interpolates plan values.
   `renderFunction` can slice them from `renderAssemblyHelpers` - P-BUNDLE measured it finds
   `transcript_init`/`common_word`/`squeeze_to` correctly after the brace-depth repair.
   **Verify the slicer gets `batch_invert` and `scalar_inv` right** - the brace-depth bug that
   truncated `common_uncompressed_g1` could bite these too.
2. **Add a closure gate**: a decidable check that **every user call in every emitted slice has
   a matching `funDef` in `emitMain`**. That is the general fix - it catches the next missing
   helper automatically instead of relying on someone noticing. `emittedUnresolvedCalls`
   already exists from P-BUNDLE; make it the thing a gate requires to be empty.
3. **`validate_public_accumulator`** lives in `AccumulatorHelpers.yul:190` (165 lines), which
   `renderFunction` **cannot** slice from the AssemblyHelpers render - P-AST3b measured it
   returns `""`. If converting that file is too big for this package, **emit the first two
   helpers, land the closure gate with the acc-arm call recorded as a named exception, and
   say so.** Do not fake it.

## Why this matters for the spec theorems

`lagrange_spec` and `pcs_spec` are pinned to programs that cannot execute. Any proof about
their run would be a proof about a program the EVM rejects at validation. Closing this is a
precondition for those theorems meaning what they appear to say.

## Constraints

* **No DSL extension, no fork edit.** Seven slices have been built with constructor helpers.
* **Numeric spelling is invisible to every AST relation** - string-containment gate.
* **`/-! ---- -/` does not close** - a dash run after `/-!` makes the rest of the file an
  unterminated comment, reported only at EOF.
* **`yul%` cannot write `end`** - use the guillemet escape.
* **Plan-dependence gates are required**, not optional: a hard-code matching the deployed
  profile reddens neither AST relation (standing note, measured three times).
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp, verify `git diff --numstat`.
* **D-P23 / R-41**: witness AND failure mode; report failures to redden.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5153 jobs**; `checks.sh` green: 64 tracked sorries, **1259 KATs across 84
files**, 111 statement fragments, 12 fact families, 23 spec-theorem bundles, 30 baseline
pins, Statements hash OK.

Read first: `Midfall/Lowering/GenAst.lean` (`emitHelpers`, `emitMain`, and the
`emitTranscriptInit` family as the closest precedent), `Midfall/Lowering/GenAstPcs.lean`
(`emittedUnresolvedCalls` is in `Partials.lean`), `Midfall/Generator/VerifierPartials.lean`
(`renderFunction`, the helper renders), `docs/plans/README.md` standing notes.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count above 1259.
- **The closure gate exists and is shown to bite** - delete a helper definition and it reddens.
- `batch_invert` and `scalar_inv` emitted and gated, or a precise report of why not.
- **Required finding**: with the closure gate in place, is `emitMain` now guaranteed to
  produce a link-complete program for every profile - or are there other call sites the gate
  still cannot see (precompile addresses, `loadimmutable`, external jumps)?
