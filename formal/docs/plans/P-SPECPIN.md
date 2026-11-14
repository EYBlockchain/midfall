# P-SPECPIN - close the conclusion-weakening hole, then prove the next approachable spec.

Status: READY. Two steps. **Step 1 first** — it protects a theorem we just spent a session
proving, and it is small.

## Step 1 - the hole P-SPEC1 found and reported rather than repaired

**Weakening `traceReturn_spec`'s conclusion from the halt record to `o = .halt ∧ True`, with
the proof trivially repaired, leaves `lake build` GREEN and all three text gates at rc=0.**
`PARTIAL_SPEC_PINS` (`check_statement_fingerprints.py:128`) carries only
`["hblk : BlkIsEmitter S"]` per theorem — **the binder, never the conclusion**. So the only
thing protecting a proved spec from silent gutting is its proof, and a package under pressure
edits both.

**Deliverable:** add **conclusion fragments** to `PARTIAL_SPEC_PINS` for all ten specs — the
postcondition shape each must retain. For `traceReturn_spec` that is
`some (.ret, abiTrue)`; for the checkpoint-advancing specs, the target `Inv` checkpoint
(`.pcs`, `.pairing`, etc.). Mirror the mechanism `STATEMENTS_*` uses for the frozen file,
including a **`must_not`** direction so a trivialised post (`True`, `o = .halt`) is rejected,
not merely a missing one.

**Show it bites:** weaken a conclusion on a clone and confirm the gate reddens. That is the
acceptance test, not the code.

## Step 2 - which specs are actually approachable? Answer this, then prove one

P-SPEC1's finding was that M-B's **item list** was wrong, not its rate: of the twelve, four
bind `Eip2537.Holds` (M8's), `vkLoading_spec` is unprovable as stated
(`gap_vkLoading_world_reads`), and three need bridges that do not exist. **That leaves very
few.** So:

1. **Enumerate the remaining 11 specs and classify each**: approachable now / needs bridge X
   / binds Holds / unprovable as stated. Cite the specific missing thing.
2. **Prove the cheapest approachable one**, if any exists. The fixed machinery from
   `traceReturn_spec` (per-op `Step` inversion, the `Inv` projection, the memory lemma) is
   already in `Partials.lean` — reuse it, don't rebuild it.
3. **If none is approachable, say so plainly.** That is a real result: it means M-B is
   effectively blocked behind M8 and the bridges, and the ETA should say so rather than
   carrying 4-6 sessions of work that cannot start.

## Constraints

* **Do not weaken any spec to make it provable.** Sixteen headline statements have been found
  false or vacuous as written; report, don't repair by relaxation. Step 1 is the opposite of
  relaxation — it makes statements harder to gut.
* **D-P23 both halves as theorems** for anything new. Falsification-deletion gap measured
  **sixteen** times — claim no coverage for falsifications.
* **`BlkIsEmitter` is a hypothesis of all ten specs.** Check binder lists before assuming.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` inside a Lean **string literal** counts as a proof hole; a
  **comment-only** edit shifts `file:line` pins. Regenerate with `scripts/gen_sorry.sh`;
  budget a full `checks.sh` run (~8.5 min) after any line-shifting edit.
* **Gate changes must keep all 13 sections green** and must be shown to redden — a gate that
  has never been observed to fail is decoration (R-41).
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
  Recent: 5.09 GiB tree / 4.42 GiB largest for a full gate run.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5212 jobs**, 122 modules; `checks.sh` green: **56 tracked sorries**, 1304
KATs across 91 files, 158 fragments, 12 fact families, 8 bundles with 5 gap defs, 30 pins.
**D-P32**: Rust pinned to `2d52f24`. **D-P36a** pairing axioms installed and gate-pinned.

Read first: `scripts/check_statement_fingerprints.py` (`PARTIAL_SPEC_PINS` at :128, the
`STATEMENTS_*` mechanism at :358 as the model), `Midfall/Lowering/Partials.lean` (the ten
specs, the proved `traceReturn_spec` at :1177 and its reusable machinery at :786-1224),
`docs/plans/P-SE-semantic-equivalence.md` section N (lines 1794-1931) — **the sketch
authority** — and `docs/plans/P-SE-statements.md` for the section map and the
known-not-to-resolve table.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- The conclusion pin is in place **and shown to redden** on a weakened conclusion.
- The spec classification table, and one more spec proved **or** a plain statement that none
  is approachable before M8.
- **Required finding**: the honest size of M-B given the classification — is it 2-3 sessions,
  or is it effectively blocked behind M8?