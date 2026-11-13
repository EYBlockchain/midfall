# P-CODEC-B - the fold lemma, the two do-block walks, and the codec discharge.

Status: READY. **Land in this exact order** - each step is independently useful, so a partial
finish still moves the project. Two previous agents on this chain ran out of room; do not
repeat that by working out of order.

## Step 1 (do this FIRST) - the fold lemma: `decodeRust` output vs `Transcript.recorded`

P-CODEC-A found this as a **fifth obstacle nobody had listed**. Needed shape:

```
decodeRust E F vk inst pi = some ms ->
  ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (msgWire E m))
    = t.recorded        -- equivalently pi.extract 0 t.pos once assertEmpty fires
```

* It follows **record by record** from `frOfRepr_frToRepr_bytes` (Fr arm),
  `hc.compressedRoundtrip` (G1 arm), and `widthDispatch_exhaustive` (dead third arm).
* The gap is the **fold shape**: `List.mapM` versus the `Array.foldl` inside
  `Transcript.recordedList` is stated nowhere.
* **The fact is already computed** at `Instances/NativeE2E.lean:347` - but that file is
  confined by D-P17 and **no theorem may cite it**. So it has gate evidence and no proof.
  Reproduce the statement as a theorem; do not import the instance file.
* P-CODEC-A estimated **hours**. Do it first because everything downstream is easier with it.

## Step 2 - `Pres.congr_of_run_eq`, and its `PresWidths` twin

P-LOGCONCAT characterised the fix for `verifyAlgebraicConstraints`: the match arms are **state
values**, so the elaborated term is `(match ... with ...).run s`, and `cases h : m.run s`
refuses to abstract a scrutinee there. The fix is pointwise run equality proved by
`intro s; cases h : m.run s` - where the **goal** carries the scrutinee - then transferred.

**P-CODEC-A added a warning you must honour: `PresWidths.set` is FALSE in general** (set
installs an arbitrary transcript). So the widths predicate needs the same `congr_of_run_eq`
treatment, and a naive `set` closure lemma will not exist. Plan for that before starting the
walks.

## Step 3 - the two do-block walks, `Pres` **and** `PresWidths`

* `Verifier.parseTrace` - 3 `throw`-guards (linearised by `guardWhen`) plus ~20 bind/fold/
  squeeze steps. **Every construct already has a closure lemma** in `TranscriptLog.lean`.
* `Verifier.verifyAlgebraicConstraints` - the `StateT.set t2 >> pure guard` tail, using step 2.
* P-CODEC-A says each is now **~5-15 lines**. If it is materially more, report that rather
  than grinding.

## Step 4 - discharge `verifyNative_iff_msgs_codec` at `Obligations.lean:668`

**SORRY.md should go 63 -> 62** - the second sorry removal of the session and the first of a
headline statement. Also verified-but-unlanded by P-CODEC-A, one line when you get here:
`Transcript.initWithHash keccak256 bytes = Transcript.initFromBytes bytes` **is `rfl`**.

## If you run out of room

**Stop at a step boundary, leave the tree compiling, and report which steps landed.** A partial
result in this order is strictly more useful than a complete attempt at all four out of order.
Do not leave a half-written registered file - two sessions have had to be recovered from that.

## Constraints

* **Read `TranscriptLog.lean`'s headers first.** Landmines recorded there: `whnf` on
  `natToBytesLowFirst` with a symbolic argument does not terminate (use `replaceState`, new
  state as a VARIABLE); the working `StateT` delta set; `pure` resolving to `Pres.pure` inside
  `Pres.foo`; anonymous-structure updates must stay on one line.
* **Perturbation testing must use `lake build`, not `lake env lean`** - P-CODEC-A measured that
  `lake env lean` reads the stale `.olean` and will not see an upstream source edit. Every
  cheap perturbation test before that has been under-reporting.
* **D-P23**: witness AND falsification, as **theorems**. Deleting a whole falsification theorem
  leaves the build green - only weakening reddens - so state them so a false version cannot
  elaborate, and note the deletion gap rather than claiming coverage.
* **Do not edit `Statements.lean` or `Statements.sha256`.** The frozen `sorry` at line 68 is a
  deliberate D-P27 hold-out.
* **RAM (D-P31)**: `--proc-limit 6G --limit 24G` for builds; state expected peak first.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. Verify with `#check`.
  **Never perturb the working tree in place.** Numbers from `lake build`/`scripts/checks.sh`.
* Regenerate `SORRY.md` with `scripts/gen_sorry.sh`; verify register, `scripts/sorries.sh` and
  `checks.sh` all agree.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green: **63 tracked sorries**, **1290
KATs across 86 files**, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK, frozen axioms exactly the expected four.

Read first: `Midfall/Halo2/Exec/TranscriptLog.lean` (headers, `Pres`, `PresWidths`, the
closure lemmas), `Midfall/Assumptions/Codec.lean:440-530` (the new byte lemmas),
`Midfall/Lowering/Obligations.lean:640-690`, `Midfall/Halo2/Exec/Native.lean` (`decodeRust`,
`msgWire`), and `docs/plans/P-CODEC.md` plus `P-CODEC-A.md` for the full picture.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Steps landed in order; register **62** if step 4 completes, else 63 with a precise report.
- **Required finding**: with the codec lemma discharged, what exactly stands between the frozen
  `verifyNative_iff_msgs` and a proof - is it now only the deliberate `Statements.lean:68`
  hold-out, and is that worth putting to the human?
