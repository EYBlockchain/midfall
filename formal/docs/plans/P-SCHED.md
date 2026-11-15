# P-SCHED - `readScheduleAgrees`: one `LoweringCorrect` field, three blocked holes.

Status: READY and **high leverage**. It is a standalone `LoweringCorrect` field
(`Obligations.lean:443`) — so proving it is a step toward discharging the bundle **and** it
unblocks holes in three different files.

## The field

```lean
readScheduleAgrees : ∀ inst π ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
  ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout).slots
```

**Cited by three files**: `Partials.lean`, `Obligations.lean`, `Calldata.lean`.

## What it unblocks (all named by earlier packages as the blocker)

| hole | file | why it needs this |
|---|---|---|
| `calldata_roundtrip` | `Calldata.lean:743` | its `hshape` **is** this content (P-MC-CALLDATA) |
| `repack_spec_of_decodeRust` | `Calldata.lean:1288` | its `hsched` **is** this content |
| `transcriptParser_spec` | `Partials.lean` | blocked on `readScheduleAgrees` + the reversed-evals clause |

P-MC-CALLDATA's stated cheapest ordering was: **`readScheduleAgrees` first**, then
`calldata_roundtrip`, then `calldata_canonical`, then `repack_spec_of_decodeRust`. Follow it.

## Deliverable

1. **Prove `readScheduleAgrees`** as a standalone theorem (not just as a bundle field). If it
   can only be proved under a hypothesis the bundle already carries, say which.
2. **Then `calldata_roundtrip`** — P-MC-CALLDATA said it needs `cdWord`/`bytesTake` window
   lemmas over an unbounded buffer plus the `G1CodecLaws` frame leg. **`G1CodecLaws` is now
   exhibited at `g1CodecZ` (P-CODECLAWS)**, so that leg exists — check whether it is the right
   one for this use.
3. **Then `repack_spec_of_decodeRust`** if room.

## Before you start — check for vacuity, and do not trust this brief

**Three premises in orchestrator briefs have been wrong this session** (a fake
`dialect_deterministic` prerequisite, a module path causing a layering inversion, an impossible
`decide` conversion). **Five plan statements have been false as written.** So:
- Verify `readScheduleAgrees` is **satisfiable** — exhibit a case where `decodeRust` returns
  `some ms` and the slot equation holds. If `decodeRust` never returns `some`, the field is
  vacuously true and proving it buys nothing. **Check that first**; P-RUNSHELL just proved
  `RunShell` has no runs at all, so 'the hypothesis is empty' is a live failure mode here.
- Verify each claimed blocker actually blocks. P-MC-ACC found a 'structural impossibility' that
  was a four-line lemma.

## Constraints

* **Never weaken a statement to make it provable.** Restore from the sketch if it drifted.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **31 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore a perturbed file with `git checkout` if it holds uncommitted work.**
* **`gen_sorry.sh` is now fixed** (BSD `cut -c` counted bytes under non-UTF-8 locales) — do not
  revert it. String-literal `sorry` still counts as a hole; comment edits shift pins.
* **Method rule**: before claiming a name is missing, try the unprefixed spelling, check for a
  project definition shadowing a Mathlib one, and remember `import Midfall` ≠ file closure.
* **`sha256sum` exists at `/sbin/sha256sum`** — do not add a shim.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited.** Gate 9–17 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Surface.lean`, `RunShell`, or
  `ir_refines` — the binding question is an open human decision. Do NOT git add or commit.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5218 jobs**, 128 modules; `checks.sh` green: **40 tracked sorries**, 1330 KATs,
245 fragments, 6 gap defs, 30 pins, Statements hash OK.

Read first: `Midfall/Lowering/Obligations.lean:443` (the field), `Midfall/Lowering/Calldata.lean`
(the two holes and their `hshape`/`hsched` binders), `Midfall/Halo2/Exec/Decode.lean` or wherever
`decodeRust` lives, `Midfall/Generator/Abi.lean` (`RepackedProofLayoutPlan`), sketch sections H
and R, `docs/plans/P-SE-statements.md`, `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 40**.
- `readScheduleAgrees` proved **and shown non-vacuous**, or reported vacuous.
- `calldata_roundtrip` closed if the vacuity check passes.
- **Required finding**: is `readScheduleAgrees` vacuous? And does `decodeRust` ever return
  `some ms` at a real Surface — the same question that just refuted `RunShell` inhabitation?