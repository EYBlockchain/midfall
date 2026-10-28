# P-REV-FIX2 - repair round 3. S1 is blocking; both gates are currently theatre.

Status: READY. Read **docs/REVIEW.md R-60** first. Priority is explicit: **S1 then S2** -
the review's own bottom line, and I agree.

## 1. S1 - the headline hypothesis is not inhabited (blocking)

`fixtureIrCheck` hard-codes `fxRuntimeName ir.name` (`n ++ "_1_deployed"`) instead of
reading `S.runtimeName`. The imported runtime sub-object is `Halo2Verifier_292_deployed`,
so the lookup misses and `irCheck` returns `false` on the real artifact.

* Make the check read the field it belongs to: `S.runtimeName ir.name`.
* **Add the joint exhibit that was missing**: `exists ir irLyt obs, S.irCheck ir = true /\
  RunContractIR S W H ir irLyt cd c g obs`. Gate 6 checks `RunContractIR` alone, which is
  why this survived - **a hypothesis bundle can be individually inhabited and jointly
  empty.** Add a gate for every multi-hypothesis headline conjunction, not just this one.
* Correct `Obligations.lean:36-41` and `:458-462`, which currently assert the hypothesis is
  inhabited. **They are false as written.** Fix the prose with the code.
* `runtimeName` is itself an unpinned free field - add it to the gate families.

## 2. S2 - harden both text gates, or delete them

A gate that cannot fail is worse than no gate. Demonstrated defeats to close:

1. **Strip block-comment bodies.** Today the parser invents a phantom `SupportedS` field
   named `rust` from an `-- rust:` R1 provenance comment - the gate was defeated by the
   project's own provenance convention. Fix the 3-line `strip_comments` bug and its
   docstring, which currently claims the opposite of what the code does.
2. **Self-equality check**: normalise away binder annotations before comparing sides, and
   reject any pin whose type is trivially decidable (`(h : X = X) -> ...` passes today).
3. **Conjunctions of self-equalities** must fail too (`<rfl, rfl>`).
4. **Word-boundary token matching.** `encG2` currently matches inside `encG2IsEip`.
5. **Discovery, not regression.** Scan all structure bodies for carrier-like fields so a NEW
   copy (`hasAccumulator2 : Bool`) is caught. A hand-written family list cannot catch the
   arrival of a new copy, which is the actual root cause.
6. **`enforced_at` must parse stripped code**, not raw text - deleting the real
   `quotient`/`direct` validation stays green today because the same English sentences
   survive in a KAT string.
7. **Fingerprint gate**: strip comments before fingerprinting and require fragments inside
   the *type*, not the line. `render_eq_print : True := trivial -- <real text>` passes today.

For each fix, **demonstrate the gate reddens on the specific defeat it closes** - the review
gave you all seven as working exploits.

## 3. S3-S5, S7, S9 - the residual pins

* `evaluator_agrees`: strengthen to `L.evaluator.map Object.codeBlock =
  evaluatorRuntime.map Prod.fst`. The comment claiming isSome is "the half nameable today"
  is **false** - `Object.codeBlock` exists and `Surface.irRuntime` already uses it.
* `encG2_eip`: a constant function satisfies it, and the fixture uses one. Either add
  `Function.Injective encG2` (the fixture cannot meet it - so record it as a **named gap
  with that blocker**, not a satisfied pin) or rename to `encG2_shape` and say what it does
  not claim.
* `render_eq_print`: satisfied by `rfl` because the fixture defines `astOfMain` from
  `lower`. Either defer it like F1, or add `forall o, o.diagnostics.trace = true ->
  S.astOfMain o = none` - nameable today, refuted by the review's counterexample, met by
  the fixture.
* **S7**: `shell.codeBlock` vs `shellLayout.code` is an unpinned copy, and `memguard` is
  satisfiable by shipping **no prologue at all** (`memoryguardValue [] = none`). Make
  `none` a failure, or pin it to the threshold the head guard tests.
* **S9**: fix the stale "eleven fields / qvm" fixture comment (it is 10, verified by
  `#check @SupportedS.mk`); note that `Types.lean`'s frozen placeholder still carries the
  deleted `qvm` field; and record that `qvm_validated_noBoundsFault` does not mention the
  Surface at all - the F3 class one level up.

## 4. S6 - correct the gap list

`ObsEquiv` view transport does **not** need `dialect_deterministic`: land the four lemmas
(`halted_of_view_eq`, `returnData_of_view_eq`, `isReturn_of_view_eq`,
`isRevertOrHalt_of_view_eq`) in `Bridge.lean` - they shrink the M8 gap. Then correct the
`lowering_equivalence` note: the real blocker for the third conjunct is that `ObsView`
omits `selfBalance` and `extCodeHashOf`, so `worldUnchanged` is not view-determined. Add
them to `ObsView` or restate the conjunct view-level.

## Constraints

* Do NOT edit `Statements.lean`, Rust, or `vendor/`. Do NOT git add or commit.
* **Never perturb the working tree in place** (R-54). Verify existence with `#check`, not
  grep piped through `head`.
* **R-41**: every new pin and every gate fix needs a demonstration it can fail.
* Do not weaken a pin to make the fixture pass - report which pin the fixture cannot meet.
* Update `check_statement_fingerprints.py` fragments and keep `checks.sh` green.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- S1 fixed with a **joint** exhibit, and the false prose corrected.
- Each of the seven S2 exploits closed and demonstrated closed.
- **Required finding**: after S1, is `lowering_equivalence`'s hypothesis genuinely
  inhabited at the real artifact - show the conjunction, not the halves.
