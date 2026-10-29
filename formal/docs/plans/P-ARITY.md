# P-ARITY - check call arity and statement placement. The cheapest open link holes.

Status: READY. P-HELPERS enumerated six dimensions the closure gate cannot see and named this
one as **the most obvious remaining hole and the cheapest to close**. It is still open.

## Hole 1 - call arity is checked nowhere

The closure gate matches **names only**. So:

* a call `batch_invert(a, b, c, d)` where the definition takes 2 arguments satisfies the
  closure gate and is **rejected by the Yul validator**;
* binding 1 result where the definition returns 2 (`success, failed := batch_invert(...)`)
  likewise passes the gate and fails validation.

**Deliverable:** a decidable gate asserting, for every user call in every emitted slice and
helper body, that the **argument count equals the definition's parameter count** and the
**bound-variable count equals the return count**. `emittedProgramClosure_ok` already walks
the program and resolves names - extend it to carry arity, or add a sibling gate. Then
**demonstrate it bites**: mutate an emitted call to pass one extra argument on a clone and
confirm the gate reddens; mutate a binding to drop one result and confirm it reddens.

## Hole 2 - `leave` / `break` / `continue` placement is unchecked

The emitted program has **6 `leave`s** (4 in `batch_invert`, 2 in `ec_pairing`), all
correctly nested inside `funDef`s - and **nothing checks that**. Same class: `break`/
`continue` outside a loop. Yul has no jumps, so this is the whole of that dimension.

**Deliverable:** a decidable gate asserting every `leave` occurs inside a `funDef` and every
`break`/`continue` inside a `forLoop`. Demonstrate it bites by hoisting a `leave` into a
top-level slice on a clone.

## Why these matter more than they look

The generator's whole claim is that the emitted AST **is** the deployed program. A program
that fails Yul validation is not a program at all - so every unchecked well-formedness
dimension is a place where the claim could be false while every gate stays green. That is the
same failure mode as the unhoisted-helper class P-HELPERS found, and the same one the scratch
address revealed: **the gates check what they check, and silence is not evidence.**

## Optional, if room allows - the externals dimension

`datasize`/`datacopy`/`dataoffset`/`loadimmutable` are in the dialect, used by neither the
emitted program nor the artifact (measured 0 each), so the dimension is **vacuous today and
invisible if it stops being so**. A cheap guard: assert the emitted program uses none, so an
embedded-VK arm or sub-object reference reddens rather than silently link-failing. Note
`setimmutable`/`memoryguard` are **not in the dialect at all** - if you touch this, record
that as the known dialect gap rather than working around it.

## Constraints

* **No DSL extension, no fork edit.**
* **D-P23 / R-41**: every new gate needs a demonstrated failure mode. **A gate that cannot
  be made to fail is decoration** - this project has found ten vacuous statements that way.
* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place** - APFS clone under /tmp, verify `git diff --numstat`.
* **`/-! ---- -/` does not close**; **`yul%` cannot write `end`** (standing notes).
* Numbers from `lake build` and `scripts/checks.sh` only. `SORRY.md` delta should be zero.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5153 jobs**; `checks.sh` green: 64 tracked sorries, **1274 KATs across 84
files**, 111 statement fragments, 12 fact families, 23 spec-theorem bundles, 30 baseline
pins, 107 modules, Statements hash OK.

Read first: `Midfall/Lowering/Partials.lean` (`emittedProgramClosure_ok`,
`closureHoldsUnder`, `emittedMainUnresolvedCalls` - the walker to extend),
`vendor/yul-semantics/YulSemantics/Ast.lean` (the `Stmt` forms: `funDef` carries params and
returns; `assign` carries targets and a value; `call` carries the function name and args),
`Midfall/Lowering/GenAst.lean` (`emitBatchInvert`, `emitEcPairingAt` - the `leave` sites).

## Acceptance

- Both gates exist, are `decide`/`#eval` gated, and are **shown to redden** by the mutations
  named above.
- **Required finding**: after arity and placement, is there any remaining well-formedness
  dimension of the vendored `Stmt` grammar that the gates do not check? Enumerate the `Stmt`
  constructors and say which are covered - that turns a list of surprises into a checklist.
