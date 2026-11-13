# P-BRIDGE - the EVM step lemmas. The substrate under every run-related theorem.

Status: READY, unblocked, no human decision needed.

## Why this now

`Yul/Bridge.lean` carries **8 tracked sorries**, including **`noWritersFuel`, which is literally
`fun _ _ => sorry`** - so `NoWriters` can never be established for anything. P-CODEC's own cost
estimate for `finalPairing_spec` said the work is **dominated by the MF-4 staticcall-failure
mapping through the vendored EVM step lemmas, not by the pairing**. That mapping is Bridge work,
and it is needed regardless of how the pairing decision lands.

## Deliverable

1. **`noWritersFuel`** - replace `fun _ _ => sorry` with the real fuel function and prove the
   `NoWriters` property it is supposed to yield. This is the mechanical walker P-SE flagged.
2. **The staticcall-failure step lemmas (MF-4).** A failed precompile call must produce a
   revert carrying the *pinned* selector. State and prove: given a `staticcall` whose external
   response is a failure, the big-step relation yields `HaltKind.revert` with the expected
   bytes. **This is the lemma `finalPairing_spec` cannot be proved without.**
3. **Audit the remaining 6 Bridge sorries** and close whichever are mechanical; report the ones
   that are not.

## Constraints

* **`Bridge.lean` must not import `Midfall.Halo2.Exec`** (P-SE stage 1 rule). Keep the layering.
* **D-P23 both halves per new lemma**: witness AND falsification, as **theorems**. Known gaps
  to respect, not claim past: deleting a falsification theorem leaves the build green; deleting
  a KAT conjunct is invisible to `kat_gate.py`; corrupting a predicate to `True` reddens only
  what cites it.
* **`kat_gate.py` trap, newly found**: it counts stdout lines matching a value regex and
  requires exactly one per `#eval`. A linter hint shaped `[apply] simp [h2]` **matches that
  regex**, so a single unused `simp` argument in a `#eval`-bearing file fails the gate on an
  otherwise green build. Keep new proofs free of unused-simp warnings.
* **Perturbation tests must use `lake build`, never `lake env lean`** - the latter reads stale
  `.olean` and silently under-reports. Use an APFS clone of the **whole** repo.
* **RAM (D-P31)**: state expected peak; `--proc-limit 6G --limit 24G` for builds; run
  `ram_guard.sh --selftest` first. A naive tree budget kills legitimate builds.
* **Do not edit `Statements.lean` or `Statements.sha256`.**
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit. Verify with `#check`.
* Regenerate `SORRY.md` with `scripts/gen_sorry.sh`; the count should go **down** - report the
  new number and verify three-way agreement.
* **Leave no scratch in the repo.** Report back even if you run out of room; land in order and
  stop at a step boundary rather than half-finishing all three.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5156 jobs**, 110 modules; `checks.sh` green: **62 tracked sorries**, 1292
KATs across 86 files, 158 fragments, 12 fact families, 8 + 23 bundles, 30 pins, Statements
hash OK.

**Baseline note (D-P32):** the Rust reference is pinned to `2d52f24`; `origin/main` has moved
25 commits and all ten `.yul` templates changed. Work against the **pinned** templates and
phrase results as verifying the `2d52f24` contract.

Read first: `Midfall/Yul/Bridge.lean` (all 8 sorries, `noWritersFuel`, the four view lemmas,
`ObsView`), `vendor/yul-semantics/YulSemantics/BigStep/Step.lean` (the step rules),
`docs/plans/P-SE-semantic-equivalence.md` section B (lines 536-763 - **the sketches are the
authority, not the index entries**), and `docs/plans/P-SE-statements.md`.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; register **below 62**.
- `noWritersFuel` real, and the MF-4 staticcall-failure lemma stated and proved or its
  obstruction named precisely.
- **Required finding**: with the Bridge sorries reduced, what is the shortest remaining path
  to a *non-vacuous* run-related theorem - and which of the 62 remaining holes are now
  reachable that were not before?
