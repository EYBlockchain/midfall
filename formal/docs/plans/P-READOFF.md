# P-READOFF - the second per-arm pass: operand reads fit inside the stride.

Status: READY, **bounded**. P-QVMARMS landed the stride agreement and measured that
`qvm_validated_noBoundsFault` needs a **second, different** per-arm fact — that every operand
**read** fits inside the stride — putting it at ~40% done, the closest of the six.

## The hole

`Qvm.lean:768` — `qvm_validated_noBoundsFault`, **restored to sketch strength by P-QVM**
(universal `∀ i, f ≠ readPastEnd i`, section Q at plan:2268-2271). **Do not re-narrow it.**

## What exists to build on — reuse it, don't rebuild

Section 7 of `Qvm.lean` now has: `evalQuotientIdentityStep_consumed_agrees` (22-arm case split),
`arms_enumeration_is_exhaustive`, `foldRangeIdxM_ok_advance`, five shape-helper length lemmas,
`evalQuotientIdentityLoop_fuelNeverBinds`, and **two differential gates** that re-run the
enumeration inside the build.

P-QVMARMS already verified the property holds on probes by a **truncation ladder**
(`BILIN7_PAIRWISE` on an 18-byte instruction fails with `readPastEnd 17`, so byte 17 really is
read; coefficient guard is `coeffIdx+12` with `coeffIdx = idx+4`). **Start from that.**

## Deliverable

1. **Enumerate read extents per arm** — for each of the 22 static arms, the max offset read as a
   function of the stride. Use **differential enumeration before induction** (R-70): run the real
   interpreter over engineered payloads and compare read extents to strides, **before** proving.
   **Watch the payload trap**: an all-zero payload makes dynamic arms short-circuit on their own
   guards, so the sweep silently measures only the easy arms.
2. **Prove the read-within-stride lemma** per arm (or one case split, as section 7 did).
3. **Phase-2 const-slot wiring** — the other half of the hole.
4. **Close `qvm_validated_noBoundsFault`** at its restored strength.

## Also: record a coverage gap in the audit instruction

**`qvm_compile_correct_stream` and `identityCorrespondence_of_bridge` appear ZERO times in
`P-SE-semantic-equivalence.md`** — orchestrator-confirmed. They come from D-P20 claim 1 /
design1. So the standing rule *audit every proof statement against the sketches in sections
A–R* **cannot cover them**, and has been silently assuming coverage it doesn't have.

Add a section to `docs/plans/P-SE-statements.md` listing **every theorem with a `sorry` that has
no sketch in A–R**, with its actual source. That is a real audit hole and it should be named
rather than worked around.

## Constraints

* **Never weaken a statement.** `noBoundsFault` is at sketch strength; keep it there.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **33 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **KAT pins are asserted** (`EXPECTED_KAT_TOTAL = 1336`, `EXPECTED_KAT_FILES = 96`). If you add
  gates, move the pins deliberately and say why — do not work around them.
* **`gen_sorry.sh` is locale-fixed**; `sha256sum` exists at `/sbin/sha256sum` — no shim.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate ~14 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Surface.lean`, `RunShell`,
  `ir_refines`, or `readScheduleAgrees`. Do NOT git add or commit. Leave no scratch.
* **Durability**: interim report after step 1 (the enumeration), land incrementally, revert-and
  report rather than carrying broken work forward.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5218 jobs**, 128
modules; `checks.sh` green: **40 tracked sorries**, 1336 KATs across 96 files (both pinned),
374 fragments across parsed structures, 30 pins, Statements hash OK.

Read first: `Midfall/Lowering/Qvm.lean` **section 7** (the machinery to reuse) and the
`qvm_validated_noBoundsFault` hole at :768, `Midfall/Generator/Quotient/VmCertify.lean`
(`identitySegment`, the validator), `Midfall/Generator/Quotient/VmReference.lean` (the
interpreter step), plan section Q lines 2268-2271 (the sketch), `docs/REVIEW.md` R-70 (the
technique), `docs/plans/P-SE-statements.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 40**.
- The read-extent enumeration landed with its negative controls.
- `qvm_validated_noBoundsFault` closed **at sketch strength**, or the exact remaining obstacle.
- The no-sketch audit section added.
- **Required finding**: does the read-within-stride property hold for all 22 arms, and do the
  four dynamic arms behave differently — P-QVMARMS could not prove them, only measure them.