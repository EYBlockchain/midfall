# P-VEND - add `memoryguard` and `setimmutable` to the vendored dialect. Critical path.

Status: APPROVED by the human (round 51, decision 2). **This is the only thing between
stage 6 and a stated `lowering_equivalence`** - `ir_refines`'s sole run hypothesis
`RunContractIR` is uninhabited today because the imported via-IR contains builtins the
dialect cannot parse, so stage 4 correctly declined to state the headline theorem rather
than ship a vacuously satisfiable one.

## The measured problem

`vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean`:
* `parse : Ident -> Option Op` (from ~line 173) returns `none` for an unknown name, and a
  `none` call elaborates to a **user function call** (`mkCall`, ~line 216) with no Step
  derivation. So `memoryguard(..)` and `setimmutable(..)` parse, elaborate, and then
  cannot make progress - any run reaching them is stuck.
* Confirmed absent: 0 occurrences of either name in the dialect.

## What to do

1. **Measure first.** Import the actual pinned artifact (solc 0.8.30, `viaIR: true`,
   optimizer runs 200 - the triple `BASELINE.md` records) and list every builtin the
   deployed IR calls that `parse` does not resolve. Do not assume the answer is exactly
   two. D-P15 settled the artifact is the **textual via-ir IR**, imported via generated
   `yul%` quotations - the elaborator is the checker.
2. **Add the missing builtins to `Op`, `parse`, and the Step relation**, with semantics
   matching solc's documented behaviour:
   * `memoryguard(n)` is a **compile-time** construct - solc lowers
     `mstore(0x40, memoryguard(n))` to a constant free-memory-pointer initialiser. If the
     imported IR has already folded it, say so and record that no dialect change is needed
     for it. Stage 4 already recovered the *bound* from the runtime bytes
     (`Generator/Evm.lean:129`), so the question is only the AST-level form.
   * `setimmutable(slot, offset, value)` writes into the deployed code's immutable section
     at constructor end; `loadimmutable(slot, offset)` reads it. Both need a memory/
     immutable model - `EVMExec.lean:793` already models immutables as a layout map, so
     the representation exists.
3. **Keep it upstreamable.** Changes go in the vendored fork with a clear commit, and any
   Midfall-side additions stay under `Midfall/Yul/` per PLAN section 7.
4. **Gate it.** A `yul%` quotation using each new builtin must elaborate AND step. Show a
   perturbation that breaks each Step rule. **Apply source mutations to copies, never the
   working tree (R-54).**

## Constraints

* **`vendor/` is a pinned fork - this package is the authorisation to edit it.** No other
  package may. Keep the diff minimal and documented; record the upstream commit it is
  based on.
* Do NOT edit Rust files, `Statements.lean`, or another package's Lean file.
* Register any new module (R-50). Numbers from `lake build` and `scripts/checks.sh` only -
  `lake env lean` does not apply lakefile options.
* **Verify existence claims with `#check`, not grep.** The orchestrator recorded that
  `stmtsBeq` had no declaration anywhere, and a stage agreed; both were wrong, because a
  `head -5` truncated the grep before it reached `vendor/`. Use `#check` for every
  existence question in this package.

**No idle builds.** If you run short on room, leave the tree compiling.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Every builtin the deployed IR actually calls is resolvable by `parse` and has a Step rule.
- **Required finding**: state whether `RunContractIR` is now **inhabited** - can a run of
  the imported IR be constructed at all? That is the gate on stage 6 stating `ir_refines`
  and `lowering_equivalence`. If another obstacle remains, name it.
