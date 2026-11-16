# P-RUNLEG - the run leg. This is the live attack on D-P42, and it is needed either way.

Status: **CRITICAL PATH, and it tests my own decision.** D-P42 says `RunShell` and `wrap` differ
**by construction** on unroutable calldata, and it carries a falsifiability paragraph:
**the attack is a routed-calldata comparison showing the disagreement is an artefact of the EMPTY
calldata rather than of the entry path.** This package runs that attack.

## Why it must be done even if D-P42 survives

`gap_runLeg_unexhibited` — **no accepted calldata exists at any model in the tree.** It blocks:
- the D-P42 attack (above);
- `hside`, which is only ever exhibited vacuously without it;
- the four `*_spec` theorems that need a run;
- `lowering_correct` at any Surface, since a bundle with no inhabited input is a hollow exhibit.

## Deliverable

1. **Construct a routed calldata** — `bytesTake cd 0 4 = some fnSigVerifyProof`, callvalue 0, and
   the 13 ABI bounds tests passing, so the dispatcher actually enters the arm. `ShellModel` already
   has `dispatcherAccepts` and `cdWellFormed` (228 B, offset `0x40`) — **start from those**, and
   `armPrefix_passes` already proves the 16-statement prefix runs to `.normal`.
2. **Compare the two sides on it.** Does `wrap` on a routed calldata agree with `RunShell` on the
   same input, now that both are inhabited? **If yes, D-P42 is wrong and says so.** If no, name
   the mechanism precisely — is it still the prologue, or the immutables, or the return encoding?
3. **`ir_refines_refuted_at_the_imported_artifact` is still not re-established** after P-INLINE
   retracted it. If the routed comparison settles it at `irSurface` with the real solc artifact,
   do that too — it is the stronger claim.

## Constraints — several are new and specific

* **`Bridge.lean` is 1592 lines — past the read-tool truncation threshold.** It silently
  truncated a 1967-line file and a splice dropped 612 lines. **Use direct file access.**
* **`lake build` green ≠ KAT gates passed** — always run `python3 scripts/kat_gate.py`. (R-71)
* **Fuel per NESTING LEVEL, never per list element** — per-element made one `rfl` cost 18+ min
  and 8.7 GB and it was killed; per-level completes in ~4 s. (P-INLINE)
* **Do NOT edit `ir_refines` or restate its right-hand side.** D-P42 is recorded; the edit needs
  a separate authorised decision (D-P43) informed by this package's result.
* **Never weaken a statement to make it provable.**
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **36 times**; gates
  never call the lemmas.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW — AND READ THE BOUNDARY.**
* **NEVER restore with `git checkout` on a file holding uncommitted work** — hash-verified copies.
* **KAT pins asserted** (`EXPECTED_KAT_TOTAL = 1348`, `EXPECTED_KAT_FILES = 98`). Move deliberately.
* **`gen_sorry.sh` locale-fixed**; `sha256sum` at `/sbin`. **RAM (D-P31)**: `--selftest` first;
  `--proc-limit 6G --limit 24G`. Never run `checks.sh` during an edit; gate ~14 min.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, `vendor/`, `Qvm.lean`, `InlineConstants.lean`.
  Do NOT git add or commit. Leave no scratch.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`. Build green at **5220 jobs**, 130
modules; `checks.sh` green: **39 tracked sorries**, 1348 KATs across 98 files, 375 fragments.
`Bridge.lean` has 4 remaining sorries (`keccakOf_invariant`, `RunCommitted_keccakOf`, +2).

Read first: `Midfall/Instances/RunShellInhabited.lean` (the unconditional refutation,
`shell_run_is_not_the_wrap_run`, `ir_refines_hypotheses_hold_at_the_refuted_instantiation`),
`Midfall/Yul/ShellModel.lean` (`dispatcherAccepts`, `armPrefix_passes`, `cdWellFormed`, `wrap`,
`modelIr`), `Midfall/Instances/RunShellInversion.lean` section 12 (the retraction record),
`docs/design.md` **D-P42 including its falsifiability paragraph**, `docs/ETA.md` R24.

## Acceptance

- `lake build`, `checks.sh` **and** `kat_gate.py` green.
- A routed calldata constructed and both sides evaluated on it.
- **Required finding: does D-P42 survive?** If the disagreement is empty-calldata-specific, say
  so plainly — that is the falsifiability test working and it is a good outcome. If it survives,
  name the mechanism that makes it structural.