# P-CODEC - discharge `verifyNative_iff_msgs_codec`. Four named items, no decisions needed.

Status: READY. P-LOGCONCAT proved the general transcript lemma and named **exactly four**
remaining obstacles, all ordinary work. This is the closest the project has come to a real
proof of a frozen normative statement.

## The four items, in the order that makes dependency sense

### 1. The decoder-first **byte-level** Fr repr round trip (P-LOGCONCAT says ~1 day)

Needed: `frOfRepr? b = some x -> frToRepr x = b`. P-BYTES landed the **encoder-first
**value-level** `frOfRepr_frToRepr`; the direction needed here is the other way and at byte
level. P-LOGCONCAT identified the missing step precisely:

> `natToBytesLE (bytesToNatLE b) b.size = b` for `b.size = 32` - provable from `lowDigits_go`
> plus a digits lemma.

**Re-verify that claim rather than trusting it** - P-BYTES's recorded blocker was half-wrong,
and P-LOGCONCAT's premise that the log lemma was the *only* obstacle was also half-wrong.

### 2. The width condition: every verifier-path read logs width 48 or 32

`decodeRust` maps each log entry by `if rec.1 == wG1 then ... else if rec.1 == wFr then ...
else none`. If **any** verifier-path read had another width, `verifyNative` could accept while
`decodeRust = none` and the `iff` is **false**. `critic.md:81` asserts `hashableU32` is only
read by KATs - **prove it, do not cite it**. This is a second do-block walk.

### 3. `Pres (Verifier.verifyAlgebraicConstraints)` - the fix is already characterised

P-LOGCONCAT tried four ways and stopped. The problem: the match's arms are **state values**, so
the elaborated term is `(match ... with ...).run s`, and `cases h : m.run s` refuses to
abstract a scrutinee in that position. **The stated fix**: a `Pres.congr_of_run_eq` (pointwise
run equality transfers `Pres`) plus proving the pointwise equality by `intro s; cases h :
m.run s`, where the **goal** carries the scrutinee. Use that; it is diagnosed, not open.

### 4. `Pres (Verifier.parseTrace)` - "writing, not thinking"

3 `throw`-guards (linearised by `guardWhen`, not exponential) plus ~20 bind/fold/squeeze
steps, **every construct of which already has a closure lemma** in `TranscriptLog.lean`.

### Then: discharge `verifyNative_iff_msgs_codec` at `Obligations.lean:668`

**SORRY.md should go 63 -> 62.** That would be the second sorry removal of the session and the
first of a **headline** statement rather than a helper lemma.

## Constraints

* **Read `TranscriptLog.lean`'s header first** - it records two kernel landmines that will
  cost hours if rediscovered: `whnf` on `natToBytesLowFirst` with a **symbolic** value argument
  does not terminate in the default heartbeat budget (case-split the transcript before any
  `rfl` that must reduce), and core's `StateT.run_get`/`run_set` equation lemmas do **not**
  match elaborated do-blocks (the working delta set is written out). Also: inside a theorem
  named `Pres.foo`, `pure` resolves to `Pres.pure` - use `StateT.pure`.
* **Split if needed.** Items 1-2 are self-contained; 3-4 are the bulk. Each sub-step must leave
  the tree compiling. Landing 1-2 and one do-block walk is real progress; do not half-write all
  four.
* **D-P23 both halves** for each new lemma. And **state falsifications as theorems, not only
  KAT conjuncts** - the gate compares only a KAT def's whole Bool, so deleting conjuncts stays
  green. This has now been measured twice.
* **Do not edit `Statements.lean` or `Statements.sha256`.** The frozen statement's own `sorry`
  at line 68 is a deliberate D-P27 hold-out.
* **RAM (D-P31)**: `--proc-limit 6G --limit 24G` for builds; a naive tree budget kills
  legitimate builds (measured 17.91 GiB tree, 2.97 GiB largest process).
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. Verify with `#check`, not
  `grep | head`. **Never perturb the working tree in place.** Numbers from `lake build` and
  `scripts/checks.sh` only. Regenerate `SORRY.md` with `scripts/gen_sorry.sh`, never by hand.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green, 13 sections: **63 tracked
sorries**, 1288 KATs across 86 files, 158 statement fragments, 12 fact families, 8 + 23
bundles, 30 baseline pins, Statements hash OK, frozen axioms exactly the expected four.

Read first: `Midfall/Halo2/Exec/TranscriptLog.lean` (header + `Pres` + the closure lemmas),
`Midfall/Lowering/Obligations.lean:640-680` (the gated sorry and its sketch hint),
`Midfall/Common/Bytes.lean` (P-BYTES's lemmas), `Midfall/Assumptions/Codec.lean:150-240`,
`docs/plans/P-SE-semantic-equivalence.md` section Q, and the matching `design2.md` /
`attack.md` in `docs/plans/P-SE-evidence/` - **`attack.md` FIX lines are binding**.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- As many of the four items as fit, each left compiling; **register 62 if the codec lemma
  closes**, otherwise a precise statement of which item remains.
- **Required finding**: with the codec lemma discharged, what would it take to fill the frozen
  `Statements.lean:68` sorry - and is that now a decision worth putting to the human, since
  the statement would be provable rather than merely not-false?
