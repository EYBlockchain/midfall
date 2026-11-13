# P-CODEC-A - items 1 and 2 ONLY. The self-contained prerequisites.

**Scope was reduced deliberately.** The parent brief (`P-CODEC.md`) listed four items and the
agent assigned to it **ran out of room before producing any durable work at all** - the tree
came back clean with nothing committed. That is my planning error, not the agent's. This
package takes **two of the four items** and explicitly defers the rest.

## In scope - exactly two items

### Item 1: the decoder-first **byte-level** Fr repr round trip

Prove `frOfRepr? b = some x -> frToRepr x = b`. P-BYTES landed the **encoder-first
**value-level** `frOfRepr_frToRepr`; this is the other direction, at byte level.
P-LOGCONCAT identified the missing step as
`natToBytesLE (bytesToNatLE b) b.size = b` for `b.size = 32`, "provable from `lowDigits_go`
plus a digits lemma, roughly a day." **Re-verify that** - two packages running, a recorded
premise here has been half-wrong.

### Item 2: the width condition

Prove every verifier-path read logs width **48 or 32**. Without it the `iff` in
`verifyNative_iff_msgs_codec` is **false**: `decodeRust` maps each log entry by
`if rec.1 == wG1 then ... else if rec.1 == wFr then ... else none`, so another width means
`verifyNative` accepts while `decodeRust = none`. `critic.md:81` asserts `hashableU32` is
only read by KATs - **prove it, do not cite it**.

## Explicitly OUT of scope - do not start these

* `Pres (Verifier.verifyAlgebraicConstraints)` - the do-block walk with the characterised
  `Pres.congr_of_run_eq` fix.
* `Pres (Verifier.parseTrace)` - the ~20-step walk.
* Discharging `verifyNative_iff_msgs_codec` itself.

If you finish both in-scope items quickly, **stop and report** rather than starting a third.
The next package gets the do-block walks with a fresh budget.

## Constraints

* **Read `Midfall/Halo2/Exec/TranscriptLog.lean`'s header first** - two kernel landmines are
  recorded there that cost hours if rediscovered: `whnf` on `natToBytesLowFirst` with a
  **symbolic** value argument does not terminate in the default heartbeat budget (case-split
  the transcript before any `rfl` that must reduce), and core's `StateT.run_get`/`run_set`
  equation lemmas do not match elaborated do-blocks (working delta set is written out).
* **D-P23 both halves** per new lemma: witness AND falsification, stated as **theorems** not
  only KAT conjuncts - the gate compares only a KAT def's whole Bool, measured twice.
* **Do not edit `Statements.lean` or `Statements.sha256`.**
* **RAM (D-P31)**: state an expected peak; `--proc-limit 6G --limit 24G` for builds.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit.
* Verify with `#check`, not `grep | head`. **Never perturb the working tree in place.**
* Numbers from `lake build` and `scripts/checks.sh` only. `SORRY.md` should stay at **63** -
  no sorry is expected to close in this package.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green: **63 tracked sorries**, 1288
KATs across 86 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK.

Read first: `Midfall/Common/Bytes.lean` (P-BYTES lemmas), `Midfall/Assumptions/Codec.lean
lines 150-240`, `Midfall/Halo2/Exec/TranscriptLog.lean` header, `Midfall/Lowering/
Obligations.lean:640-680`, `docs/plans/P-CODEC.md` (the full four-item picture).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register still 63.
- Both lemmas proved, each with D-P23 witness and falsification.
- **Required finding**: with items 1-2 done, is the remaining distance to the codec lemma
  *only* the two do-block walks - or did you find a fifth obstacle? Name it if so.
