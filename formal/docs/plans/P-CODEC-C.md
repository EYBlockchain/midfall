# P-CODEC-C - the decodability predicate, then discharge the codec lemma. Register 63 -> 62.

Status: READY, and **narrow by design.** P-CODEC-B landed steps 1-3 and named exactly what
remains. Two prior agents on this chain ran out of room; this package has **two** steps, not
four.

## Step 1 - the sixth obstacle: `Hashable.Dispatchable` / `Transcript.LogDecoded`

P-CODEC-B's finding: **the log records a read's width and bytes but not *which* `Hashable`
produced it**, while `decodeRust` dispatches **by width**. `LogWidths` buys that the third arm
is unreachable; it does **not** buy that the arm reached accepts the bytes. A width-32 record
logged by some hypothetical 32-wide hashable whose `readRepr?` is not `frOfRepr?` would make
`decodeRust = none` while the read succeeded.

The fix, as characterised by the agent who found it - **"mechanically identical to
`PresWidths`; no invention required"**:

1. `Hashable.Dispatchable E h` - for the hashables the verifier path actually uses,
   `readRepr?` **is** the decoder the dispatch reaches for.
2. `Transcript.LogDecoded E t` - every logged record is decodable by `logDispatch`.
3. Per-primitive step lemmas (`read`, `readN`, `common`, `squeeze`, `squeezeChallenge`, init).
4. A **third** copy of the closure + transfer walks, hypotheses discharged by
   `hashableFr_dispatchable` / `hashableG1_dispatchable` exactly as the `_allowed` ones are
   now. Reuse `congr_of_run_eq` - both twins already exist.
5. Then the forward direction the codec lemma needs:
   `∃ ms, t.log.toList.mapM (logDispatch E) = some ms`.

**Note the `Pcs` obligation P-CODEC-B discovered**: `Pcs` is a *record* whose `multiPrepare`
field is an arbitrary function, so the pipeline predicates are not provable for a general
`pcs`. Both existing walks carry `∀ queries, Pres (pcs.multiPrepare queries)`, discharged at
the call site for `Pcs.kzg`. **Do the same here** - do not try to prove it for arbitrary `pcs`.

## Step 2 - discharge `verifyNative_iff_msgs_codec` at `Obligations.lean:668`

P-CODEC-B says this is now **just chaining**: `pres_prepare` + `presWidths_prepare` +
`transcript_log_concat` + `decodeRust_recorded` + `initWithHash_keccak` + `assertEmpty`, plus
the new `LogDecoded` walk.

**SORRY.md must go 63 -> 62** - the second sorry removal of the session and the **first of a
headline statement**. Regenerate with `scripts/gen_sorry.sh`; verify the register,
`scripts/sorries.sh`, and `checks.sh` all agree three ways.

**Also correct the stale sketch hint** at `Obligations.lean:669`, which names
`transcript_log_concat` as the *only* substantive obstacle - P-CODEC-B reports that is now
false in both directions.

## If you run out of room

**Land step 1 and stop at the boundary.** A complete `LogDecoded` walk with the codec lemma
still open is worth more than half of each. Report which landed.

## Constraints

* **Read `TranscriptLog.lean`'s headers first** - the landmines are recorded there (`whnf` on
  symbolic `natToBytesLowFirst` does not terminate, use the `replaceState` pattern; the
  working `StateT` delta set; `pure` resolving to `Pres.pure`; one-line structure updates).
* **Perturbation tests MUST use `lake build`, never `lake env lean`** - the latter reads the
  stale `.olean` and silently under-reports. Measured twice now.
* **D-P23**: witness AND falsification, as **theorems**. Known gaps to respect rather than
  claim past: deleting a KAT conjunct, deleting a whole falsification theorem, and corrupting
  `Pres` to `True` all leave the build green.
* **Do not edit `Statements.lean` or `Statements.sha256`.** The frozen `sorry` at line 68 is a
  deliberate D-P27 hold-out.
* **RAM (D-P31)**: `--proc-limit 6G --limit 24G`; state expected peak first; `--selftest`.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. Verify with `#check`.
  **Never perturb the working tree in place.** Leave **no scratch files in the repo** - the
  last agent left 13 of them in `formal/`; use `/tmp`.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green: **63 tracked sorries**, **1291
KATs across 86 files**, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK, frozen axioms exactly the expected four.

`TranscriptLog.lean` is now **2230 lines** - read its structure before adding to it.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Register **62** if step 2 lands; otherwise 63 with a precise report.
- **Required finding**: with the codec lemma discharged, is the frozen `verifyNative_iff_msgs`
  now provable modulo only the deliberate `Statements.lean:68` hold-out? If so, state exactly
  what filling it would take - the re-pin, the fingerprint-gate updates, and the axiom-shape
  gate consequence - so the human decision can be made with the full picture.
