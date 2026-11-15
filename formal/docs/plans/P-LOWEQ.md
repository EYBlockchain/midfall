# P-LOWEQ - restate `lowering_equivalence` about the GENERATED Yul. Scope correction.

Status: **HUMAN-DIRECTED.** The deliverable is the generator's Yul/Solidity lowering, not
solc's output. `lowering_equivalence` currently quantifies over `(ir : YulObject)
(hir : S.irCheck ir = true)` and calls `RunContractIR` — i.e. **solc's IR**. Restate it about
`RunShell`/`RunVerifier` and **drop the `ir`/`irCheck` quantification entirely**.

## Why this is a scope change, not a weakening

**`RunVerifier` already runs the generator's own Yul** (`Surface.lean:797`):
```lean
∃ V', RunCommitted c g (S.L.headGuard ++ S.bindLocals ++ S.L.main)
    (initState W S.shellLayout H cd mem₀) V' obs.state obs.outcome
```
and `LoweringCorrect`'s headline fields are stated over `RunVerifier`. **The substance was
always generator-scoped** — only the headline theorem's *shape* reached into solc.

**`shell_unfolds` is the bridge**: its own comment says it is "the pin that makes `RunShell`
and `RunVerifier` be about the same thing… a shell run is a verifier run at zeroed memory",
stated as a real **equality**, not the sketch's `True`. So the restated theorem should be
provable from `LoweringCorrect` + `shell_unfolds` — **the transport the sketch always claimed.**

## What to do

1. **Restate `lowering_equivalence`** (`Obligations.lean:649`) with `RunShell` in place of
   `RunContractIR`, dropping `(ir)`, `(irLyt)` and `(hir)`. Keep all three conjuncts and their
   **asymmetry** exactly: soundness over `permissive (S.calls W product qAddr)` and ANY gas;
   completeness over `S.calls` honest and `ofFun _ => 0`; the third conjunct's two-outcome
   read-only claim. Keep `DeploymentW`, `Holds`, `EnvAgrees`, `G1CodecLaws`, `SupportedS`,
   `hsel`, `hside`.
   - **`RunShell` not `RunVerifier`** is the closer analogue: `RunContractIR` used
     `callState W irLyt H cd`, and `RunShell` uses `callState W S.shellLayout H cd` — same
     shape, no `mem₀`. If you prefer `RunVerifier`, say why and handle `mem₀`.
2. **Prove it, or state precisely what is missing.** The sketch's own note says it is a
   transport through `hc : LoweringCorrect S product`. If it does not go through, report the
   exact gap — do not weaken a conjunct to make it close.
3. **NON-VACUITY IS MANDATORY (D-P23).** Exhibit that the hypothesis bundle is **jointly
   inhabited** at a real Surface: `DeploymentW ∧ Holds ∧ EnvAgrees ∧ G1CodecLaws ∧ SupportedS
   ∧ hsel ∧ hside`. Note `curveSurface` now exhibits `Holds` at its own codecs, but the
   `Holds` here is `S.E.g1`'s — check whether the fixture or the curve Surface can witness
   the whole bundle. **If it cannot, that is the finding**, and it is the same vacuity class
   as `hcd`. Also give a falsification: a calldata failing `hsel`, and a run that is neither
   return nor revert.
4. **Record the deviation** in `docs/plans/P-SE-statements.md` **in the same change** — the
   standing rule. State plainly: the sketched theorem quantified over solc's IR; the landed
   one quantifies over the generated Yul; the deployed-contract claim is **out of scope by
   human decision**, not weakened.
5. **Update the gates that pin the old shape.** `check_statement_fingerprints` and
   `check_hypothesis_bundles` have entries citing `RunContractIR`/`irCheck` for this theorem;
   they must move in the same commit or the register reddens.
6. **Do NOT delete `ShellModel.lean` or `IRCheck.lean`.** They are real, proved work (
   `irCheck_sound` proves Fable's conclusion unchanged); they simply leave the critical path.
   Mark them `/-- Off the critical path since P-LOWEQ: about solc's IR, which is out of
   scope. -/` rather than removing.

## Also worth checking while you are in `Obligations.lean`

**Does `LoweringCorrect` itself need any `ir`/`irCheck` field?** 14 mentions of
`RunContractIR` exist in that file. If any of the 48 fields is stated over the IR rather than
the shell, that field is also mis-scoped — list them and say which need the same treatment.

## Constraints

* **This is a scope change authorised by the human. Do not use it as licence to weaken
  anything else.** Every other statement stays as sketched.
* **Never weaken a conjunct to make the proof close.** Report the gap instead.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **25 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement.
* **`Statements.lean` is FROZEN** — do not touch it or its `.sha256`. If the frozen text
  mentions the IR, that is a separate question to report, not to edit.
* **Gate changes must keep all 13 sections green and be shown to redden** (R-41).
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Never run `checks.sh` while a file is being edited** — stale oleans produce bogus KAT
  failures. Gate is ~9–10 min.
* Do NOT edit Rust, `vendor/`, `ShellModel.lean` or `IRCheck.lean` bodies. Do NOT git add or
  commit. Leave no scratch. **Report back even if stuck.**

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5215 jobs**, 125 modules; `checks.sh` green: **44 tracked sorries**, 1317 KATs
across 93 files, 235 fragments, 30 pins, Statements hash OK.
**Another agent is working in `Halo2/Exec/Accumulator.lean`, `Lowering/Accumulator.lean` and
`scripts/kat_gate.py` — do not touch those three files.**

Read first: `Midfall/Lowering/Obligations.lean:600-700` (the current statement and its long
docstring, which enumerates exactly why it is not yet provable), `Midfall/Lowering/Surface.lean
` (`RunVerifier` :797, `RunShell` :742, `RunContractIR` :735, `shell_unfolds`, `DeploymentW`),
`Midfall/Instances/SurfaceFixture.lean` (what the fixture exhibits), sketch section R,
`docs/plans/P-SE-statements.md`, `docs/PLAN.md` lines 17 and 70 (the trusted-base split).

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- `lowering_equivalence` restated over the generated Yul with no `ir`/`irCheck` quantifier.
- **Proved, or the exact remaining gap named.**
- Non-vacuity exhibit + falsification for the new hypothesis bundle.
- Deviation recorded in `P-SE-statements.md` in the same change; gates updated.
- **Required finding**: with the solc hop descoped, what is the honest remaining distance to a
  *proved* `lowering_equivalence` about the generator? The prior estimate was 6–12 sessions of
  M8; if the answer is now single-digit, say so plainly.