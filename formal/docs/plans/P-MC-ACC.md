# P-MC-ACC - M-C second tranche: the 12 `Accumulator.lean` holes.

Status: READY, **fully unblocked** — independent of M8, of the pending spec question, and of
`Eip2537.Holds`. Largest remaining sorry-reducing tranche on the board.

## Statement authority: section F, `docs/plans/P-SE-semantic-equivalence.md:904+`

**Check each implemented statement against its sketch BEFORE proving it.** Three consecutive
packages found drift — `calldata_canonical` had drifted **weaker** and was restored;
`finalPairing_progress_spec` was **false as written**; `EnvAgrees` clauses had been dropped.
If a statement here is weaker or false relative to the sketch, **restore it first, then prove
the restored form.** Never weaken to make it provable.

## The holes (`SORRY.md`, `Accumulator.lean`)

| line | theorem (verify by reading the file — this list was extracted mechanically) |
|---|---|
| 141 | `decodeAcc_injective` |
| 249 | `decodeAcc_encode` |
| 275 | `decodeAcc_encode_noNeg` |
| 339 | `decodeAcc_encode_pointPair` |
| 364, 372 | the two `MSMKZG.eval_*` holes (`eval_scale`, `eval_addMsm`) |
| 395 | `batched_complete` |
| 409 | `batched_atMostOneRoot` |
| 436 | `dualMsm_check_iff_contract` |
| 443, 460, 475 | `exists_zmod_smul_generator` and its neighbours |

**Read the file for the real names and docstrings** — the docstrings name their Rust sources,
which is where the mathematics lives.

## Suggested ordering

1. **`exists_zmod_smul_generator` first** if it is a standalone algebra fact — likely the
   cheapest and it may be a prerequisite for the MSM lemmas.
2. **The `decodeAcc_*` family** — four related lemmas about the accumulator decoding. P-SE
   index notes the `-s` elaboration was a known obstacle; if so, say which of the four are
   blocked on it rather than burning a session discovering it.
3. **`batched_complete` / `batched_atMostOneRoot`** — the batched-check completeness pair.
4. **`dualMsm_check_iff_contract`** last: it is the one that connects to the contract, so it
   may need the run leg.

**Stop at a boundary.** Four proved with eight compiling beats twelve half-attempted.

## Constraints

* **Never weaken a statement to make it provable or to make an exhibit pass.** Report instead.
* **D-P23 both halves as theorems** for every claim: satisfiability witness AND falsification.
  Falsification-deletion gap measured **twenty** times — claim no coverage for falsifications.
* **`Instances/` confinement (D-P17)**: `Accumulator.lean` is theorem-bearing, no `Instances/`
  import. Concrete-byte witnesses go in `Instances/`, statements stay portable.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.** Five silent losses caught this way.
* **SORRY.md traps**: `sorry` inside a Lean **string literal** counts as a proof hole
  (`lean_grep` strips comments, not strings); a **comment-only** edit shifts `file:line` pins
  and reddens the register, costing a full 8.5-minute gate run. Regenerate with
  `scripts/gen_sorry.sh`; verify three-way agreement.
* **Elaborator walls, all previously hit in this area**: `decide` reduces exponentiation at
  255-bit `r` but **not** inversion; `rw [ZMod.card]` on a `Fintype.card (ZMod blsP)` goal
  costs ~4 GiB and gets killed — **pre-prove cardinalities as `have`s**; `n - n` is not `rfl`
  for symbolic `n`; the `rfl` **tactic** uses reducible transparency where term-mode `rfl`
  uses default, so a bind-on-error equation needs `exact rfl`; `rw` cannot cross a match
  binder without `dsimp` first; `Midfall.Bytes.empty` vs `ByteArray.empty` are defeq but block
  `rw`; `rcases` Option patterns are `(none | some)`, not source order; structure-update
  notation `{ e with f := v }` needs a VARIABLE head.
* **`Nat.Prime` by `decide` is hopeless at 29 bits** — use the Pratt certificates in
  `Assumptions/BasePrime.lean` rather than re-attempting `decide`.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Gate peak 5.11 GiB tree / 4.44 GiB largest; a TIGHT tree-total verdict is normal.
* **`kat_gate` trap**: an unused `simp` arg in an `#eval` file emits an `[apply]` hint that
  matches the value regex and fails the gate on a green build.
* Do NOT edit `Statements.lean`, `.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5214 jobs**, 124 modules; `checks.sh` green: **52 tracked sorries**, 1316 KATs
across 93 files, 235 fragments, 12 fact families, 8 bundles with 5 gap defs, 30 pins.
**D-P32**: Rust pinned to `2d52f24`. **D-P36a** pairing axioms installed and gate-pinned.
`ShellModel.lean` and `IRCheck.lean` both exist now (D-P38) — do not disturb them.

Read first: `Midfall/Lowering/Accumulator.lean` (the 12 holes, their docstrings and Rust
citations), `docs/plans/P-SE-semantic-equivalence.md` **section F from line 904** (the
authority), `docs/plans/P-SE-statements.md` (the deviation log and the same-commit rule),
`Midfall/Assumptions/Eip2537.lean` (`Holds`, the modexp machinery), `docs/ETA.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 52**.
- Each proved claim has a witness and a falsification as theorems.
- Any statement restored from the sketch is recorded in `P-SE-statements.md` in the same change.
- **Required finding**: of the 12, how many were provable as stated, how many needed
  restoration, and which are blocked behind a named missing bridge — specifically, does
  `dualMsm_check_iff_contract` need the run leg, and is the `decodeAcc_*` family blocked on
  the `-s` elaboration as the index claims?