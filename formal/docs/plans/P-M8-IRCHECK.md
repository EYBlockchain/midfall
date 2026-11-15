# P-M8-IRCHECK - build `IRCheck.lean`, Fable's verified checker. Second half of corrected M8.

Status: **AUTHORIZED (D-P38)** and **now statable** — P-M8-SHELL landed `ShellModel.wrap` and
exhibited `ObsEquiv` at the pinned `ir`. This is the file Fable's §7 called a **required**
deliverable and which never existed.

## Fable's spec, verbatim

> `IRCheck.lean` is a **verified checker**: `irCheck ir L = true → ObsEquiv ir (ShellModel.wrap L)`.

P11 index row: `irCheck` = **"α-equivalence modulo constant substitution and solc renames,
fuel-based"**; `ir_refines` = **"view-level simulation"**; falsification = **"planted rename
must fail `irCheck`"**.

## Constraints M8a derived — these are the design, not suggestions

1. **It must descend into function bodies.** `mutDeleteInside` (first statement of every
   helper body deleted) and `mutRevertLen` (`revert(p,0)`→`revert(p,32)` inside helpers) both
   pass the current check because `unresolvedTop` never enters a body.
2. **It must look at the creation object.** `mutCreation` (codecopy size) passes today.
3. **"Modulo constant substitution" must NAME the legal substitutions** — the render's own
   declared constants. If it means "any literal may be substituted", `mutRevertLen` is
   re-admitted and the checker is blind in exactly the place it was proved blind.
4. **`mutFold` (`add x 0`) is the interesting edge**: observationally equivalent, not an
   alpha-rename. A conservative checker that REJECTS it is **incomplete, not wrong**. Prefer
   incomplete-and-sound over the reverse, and say which you built.
5. **Fuel-bounded**, per the spec — the artifact has 76 user functions and 2,898 lines.

## A dependency you must check before promising the theorem

M8a's required finding: **`dialect_deterministic` (`Bridge.lean:186`) is a registered hole, so
one agreeing pair does not give `ObsEquiv`'s forall.** `ObsEquiv` needs every run on each side
matched, and `Run.det` is unavailable.

**So `IRCheck`'s main theorem may require M-D.** Decide early and say which you chose:
- **(i)** prove `dialect_deterministic` first (M-D, estimated 2–5 sessions) and state the
  full `ObsEquiv`; or
- **(ii)** state the checker's property as a **one-sided simulation** (every artifact run
  matches a shell run) which may not need determinism, and record that it is weaker than
  Fable's `ObsEquiv` until M-D lands.

**Do not silently substitute (ii) for (i).** Fable wrote `ObsEquiv`. If you land the weaker
form, that is a signature change to a sketched statement and needs a line in
`P-SE-statements.md` in the same commit — the standing rule.

## Also in scope: the one hole M8a could not close

**Swapping the two immutable key CONSTANTS' definitions is invisible to every gate** — the
model and its gates read the same constant, so the tie between `vkImmutableKey` and
`DeploymentW.vkImm` is prose, not a decidable fact. M8a called it "a copy-without-a-pin of
exactly the R-58 class" and handed it here. **Make it decidable** — e.g. a pin relating the
model's key strings to the `DeploymentW` fields, shown to redden when swapped.

## Constraints

* **D-P30: vendored AST only. No raw string Yul.**
* **Never weaken a statement to make it provable.** Report instead.
* **D-P23 both halves as theorems.** The falsification Fable named — **planted rename must
  fail** — must be a theorem, not a KAT. Falsification-deletion gap measured **twenty** times.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement; budget a full gate run.
* **Elaborator walls, newest first**: structure-update notation `{ e with f := v }` needs a
  VARIABLE head or you get a misleading parse error; `n - n` is not `rfl` for symbolic `n`, so
  `restore` needs an explicit `restore_self`/`restore_nil` lemma; builtin combinators need
  SEPARATE input and output state variables; the `rfl` TACTIC uses reducible transparency where
  term-mode `rfl` does not; `Step` constructor implicits must be pinned at every use site; the
  kernel cannot `rfl` a `SyntaxEq` over the 2,898-line import, so artifact cross-checks are
  `Bool` gates read by `kat_gate`, not theorems.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`. Gate peak
  5.10 GiB tree / 4.43 GiB largest; a TIGHT tree-total verdict is normal.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5213 jobs**, 123
modules; `checks.sh` green: **52 tracked sorries**, 1311 KATs across 92 files, 235 fragments,
30 pins, Statements hash OK.

Read first: `docs/PLAN.md` §7 line 228 (**the spec**) and the P11 row at line 356,
`Midfall/Yul/ShellModel.lean` (`wrap`, `dispatcherCode`, the three falsifications),
`Midfall/Instances/IrCheckBlindness.lean` (the mutants, re-read against Fable's definition),
`Midfall/Lowering/Surface.lean:771` (`Surface.irCheck`, the placeholder being replaced),
`Midfall/Yul/Bridge.lean:186` (`dialect_deterministic`), `docs/design.md` D-P38,
`docs/REVIEW.md` R-65, `docs/plans/M8-SCOPE.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `IRCheck.lean` exists with a decidable, fuel-bounded checker that descends into bodies and
  names its legal constant substitutions.
- **Planted rename fails it, as a theorem.**
- The immutable-key tie is decidable and shown to redden on a swap.
- The `dialect_deterministic` dependency is decided and stated, not worked around.
- **Required finding**: with `IRCheck` landed, is `ir_refines` provable, and what is the
  honest remaining distance to `lowering_equivalence`?