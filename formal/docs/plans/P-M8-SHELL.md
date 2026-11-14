# P-M8-SHELL - build `ShellModel.lean` per Fable's spec. First half of the corrected M8.

Status: **AUTHORIZED (D-P38: follow Fable's plan).** M8 was mis-framed as a trusted-base decision;
R-65 showed Fable named two files as required deliverables and neither exists. **This is the first.**

## Fable's spec, verbatim (`docs/PLAN.md` §7 line 224)

> `ShellModel.lean`: a Yul model of solc's dispatcher for `verifyProof(bytes,uint256[])`, covering
> selector `0x1e8e1e13`, the callvalue check, ABI bounds checks, and binding the locals `vk` and
> `quotientEvaluator` from immutables.

## Why this file, first

* **It is a prerequisite of `IRCheck.lean`**, whose specified property is
  `irCheck ir L = true → ObsEquiv ir (ShellModel.wrap L)`. You cannot state the checker's theorem
  without the thing it checks against.
* **It also closes the `shell_unfolds` gap** identified in `M8-SCOPE.md`: the model's entry is a head
  guard `if gt(mload 0x40, 0x1000) revert`, while the artifact's is `memoryguard` prologue →
  callvalue/calldatasize tests → **selector switch** → ABI decode → fall-through revert. **A
  wrong-selector calldata reverts in the artifact and runs the verifier in the model.** One file
  fixes both.

## What to build

1. **`Midfall/Yul/ShellModel.lean`** — a Yul model (via the vendored AST, **D-P30: no raw string
   emission**) of the dispatcher, with the four specified behaviours:
   - selector `0x1e8e1e13` dispatch,
   - the callvalue check,
   - ABI bounds checks (offset/length of the `bytes` and `uint256[]` args),
   - binding locals `vk` and `quotientEvaluator` from immutables (`getimmutable`).
2. **`ShellModel.wrap`** — the function `IRCheck`'s theorem will cite. Design its signature against
   `RunContractIR`/`RunShell` in `Surface.lean` so `ObsEquiv` is statable.
3. **Replace the current shell model** where it is wrong: find what `Surface.shell` / `fxShell`
   currently pins and state precisely how the new model differs. **Do not delete the old one until
   the difference is written down** — `shell_unfolds` is a registered pin.

## Required cross-check

**Compare your model against the real artifact's dispatcher.** The deployed runtime block is in the
pinned `ir` (`ImportSolcIR.lean` / `Instances/ImportedIR.lean`). Your model must reproduce:
- the selector test and the fall-through revert,
- the callvalue guard,
- the ABI offset/length validation,
- the two `getimmutable` loads.
**Falsification, as theorems (D-P23):** a calldata with a wrong selector must **revert** in your
model (it currently runs the verifier in ours — that is the bug); a non-zero callvalue must revert;
a truncated `bytes` argument must revert. Each of those is a statement about your model, and each
must be proved, not asserted.

## Constraints

* **D-P30: all Yul emission goes through the vendored AST. No raw string expressions.** The text
  port is a reference, not the deliverable.
* **Never weaken a statement to make it provable.** Report instead.
* **D-P23 both halves as theorems** for every claim, including the falsifications above.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts as a hole; comment edits shift `file:line`
  pins → regenerate with `scripts/gen_sorry.sh`, verify three-way agreement, budget a full
  `checks.sh` run (~8.5 min).
* **Elaborator walls**: `decide` reduces exponentiation at 255-bit `r` but not inversion; `rw
  [ZMod.card]` on a `Fintype.card (ZMod blsP)` goal costs ~4 GiB — pre-prove cardinalities as
  `have`s; generalise over literals rather than raising `maxRecDepth`.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Full-gate actual 5.09 GiB tree / 4.41 GiB largest.
* **`checks.sh` is ~8.5 min**; heavy `decide`s go in a file with no `#eval` (the `G2Kernel.lean`
  pattern); no unused `simp` args in `#eval` files.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5212 jobs**, 122 modules; `checks.sh` green: **56 tracked sorries**, 1309 KATs
across 91 files, 235 fragments, 12 fact families, 8 bundles with 5 gap defs, 30 pins.
**D-P32**: Rust pinned to `2d52f24`. **Note**: another agent is working in
`Midfall/Lowering/Calldata.lean` — **do not touch that file.**

Read first: `docs/PLAN.md` §7 (lines 219-235) — **the spec** — `docs/REVIEW.md` R-65, `docs/design.md`
D-P38, `docs/plans/M8-SCOPE.md` (the `shell_unfolds` analysis and the three options, now superseded
by D-P38), `Midfall/Lowering/Surface.lean` (`shell`, `RunShell`, `shell_unfolds`, `Surface.irCheck`
at :771), `Midfall/Yul/ImportSolcIR.lean` (DECISION 1 and the pinned dispatcher), and
`Midfall/Instances/IrCheckBlindness.lean` (what the current check cannot see).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `ShellModel.lean` exists with the four specified behaviours and a `wrap` suitable for `IRCheck`'s
  theorem.
- The three falsifications (wrong selector, non-zero callvalue, truncated bytes) are **theorems**
  about the new model.
- The difference between old shell model and new is written down, with `shell_unfolds` updated or
  retired in the same change.
- **Required finding**: does `ObsEquiv (RunContractIR … ir …) (ShellModel.wrap …)` now STATE
  correctly for the pinned `ir`? If yes, `ir_refines` is no longer refutable and `IRCheck.lean` can
  be briefed. If no, say precisely what is still missing.
