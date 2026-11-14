# P-CSURFACE + M8-SCOPE - the certain plumbing first, then scope the real remaining difficulty.

Status: READY. P-HOLDS-FINAL closed the model track and identified two residues. **Do them in this
order** — Step 1 is certain and cheap; Step 2 is the largest unknown in the project.

## Step 1 - build a `Surface` over the curve codecs (certain value, ~1 session of plumbing)

P-HOLDS-FINAL: the four `Holds`-binding spec theorems bind `Holds S.E.g1 ⟨S.encG2⟩ product` — the
**Surface's own** codec — so `holds_exhibited` advances none of their proofs. And
`VerifierEnv.g1` is typed over the Surface's own `AdmissiblePairing`, so installing the curve codec
means **building a Surface over `blsGT`**, not editing the fixture.

* Build `curveSurface` (or similar) over `G₁z` / `G2fold` / `blsGT` with `g1CodecZ` / `g2CodecFold`.
* **Then `bundle_holds_empty` should become an exhibit, not a refutation** — but only at the *new*
  Surface. The fixture refutation stays true and must not be deleted.
* Show the four spec theorems now **instantiate** at the curve Surface (their `Holds` binder is
  satisfiable there). Instantiating is not proving — say which is which.
* This is instance plumbing, not a theorem. If it turns out to need real work, report why.

## Step 2 - scope M8 precisely (the largest open estimate in the project)

P-HOLDS-FINAL's required finding: **M8 is where `lowering_equivalence`'s remaining difficulty
actually lives**, and nothing on the model track touched it. Three named items:

1. **`irCheck` is a decidable fragment, not alpha-equivalence.** What does it actually verify?
   What does it NOT check? Is the gap exploitable — could a non-equivalent IR pass `irCheck`?
2. **`shell_unfolds` pins the shell model, not the deployed entry path.** What is the difference,
   concretely, between the model and the artifact?
3. **`ir_refines` — the IR-to-shell simulation.** This is the substance of M8.

**Deliverable: a written scoping note** in `docs/plans/` answering: what each item requires, what
mathlib/vendored support exists, what the honest session estimate is, and whether `ir_refines` is
even the right formulation or whether the trusted hop should be stated differently. **Do not
attempt the full proof in this package** — scope it so the ETA stops being a guess.

### A concrete probe worth running

`ir` (not `irOptimized`) is pinned, so the deployed bytecode differs from the model by the solc
optimizer. **Check whether `irCheck` can distinguish a mutated IR that the optimizer would have
collapsed anyway** — if not, that bounds what M8 can ever prove and the trusted base needs a
stronger statement. This is the kind of question the ledger says I should ask before estimating.

## Constraints

* **`Instances/` confinement (D-P17)**: a concrete curve Surface lives in `Instances/`.
* **D-P23 both halves as theorems** for anything proved here. Falsification-deletion gap measured
  **fourteen** times; claim no coverage for falsifications.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **NEW traps, both found by running**: the word `sorry` inside a Lean **string literal** counts as
  a proof hole (`lean_grep` strips comments, not strings); and a **comment-only** edit shifts
  `SORRY.md`'s `file:line` pins — budget a full gate run (~8.5 min) after any line-shifting edit.
* **`checks.sh` is ~511 s.** Do not add heavy `#eval`s to `#eval`-bearing files; heavy `decide`s go
  in a file with no `#eval` (the `G2Kernel.lean` pattern).
* **Label prescriptions tried or guessed** (R6). Do not record a fix you have not tested.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first and read it; `--proc-limit 6G --limit 24G`.
* Do NOT edit `Statements.lean`, `Statements.sha256`, Rust, or `vendor/`. Do NOT git add or commit.
  Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5210 jobs**, 120 modules; `checks.sh` green: **57 tracked sorries**, 1303 KATs
across 90 files, 158 fragments, 12 fact families, 8 bundles with **5 named gap defs**, 30 pins,
Statements hash OK. **D-P32**: Rust pinned to `2d52f24`.

Read first: `Midfall/Instances/HoldsFinal.lean`, `Midfall/Assumptions/CurvePairing.lean`,
`Midfall/Lowering/Surface.lean` (`Surface`, `irCheck`, `shell_unfolds`, `RunContractIR`,
`DeploymentW`), `Midfall/Instances/SurfaceFixture.lean` (the fixture Surface as a template),
`Midfall/Yul/ImportSolcIR.lean`, `docs/PLAN.md` M8.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- Step 1 landed, or its hidden difficulty named.
- Step 2: a written scoping note with an honest session estimate for M8.
- **Required finding**: with M8 scoped, give the first **non-guessed** total for
  `lowering_equivalence`. If M8 turns out to be large, say so plainly — the ledger's whole purpose
  is to stop me from quoting numbers I have not earned.
