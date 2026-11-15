# P-LOWEQ - restate `lowering_equivalence` over `ShellModel.wrap` and PROVE it. Tier 2.

Status: **HUMAN-DIRECTED, option A.** The deliverable is the generator's lowering; the entry
path must be modelled (it comes from Solidity), but **solc itself is not**. So restate over
`ShellModel.wrap` — the in-tree Yul model of solc's dispatcher — and **prove the theorem**.

## Why `ShellModel.wrap` and not plain `RunShell`

The generator emits **Solidity with inline `assembly` blocks** (`Halo2Verifier.sol`, 2665
lines, `pragma solidity 0.8.30`, four `assembly ("memory-safe")` blocks). The Yul partials
are the *body*; the selector dispatch, callvalue guard, ABI bounds and `loadimmutable` bindings
come from Solidity. `RunVerifier` runs `headGuard ++ bindLocals ++ main` — **body only, no
entry path** — so restating over it would prove a narrower claim than the objective wants.
`ShellModel.wrap` (P-M8-SHELL) models the entry path **in Yul, in this tree**, with the three
falsifications proved as theorems. That is Tier 2: real entry-path semantics, no solc.

## The key lemma this needs

`LoweringCorrect`'s fields are stated over `RunVerifier`. `ShellModel.wrap` runs the dispatcher
whose `verifyProof` arm body is `armBody S = S.L.headGuard ++ S.bindLocals ++ S.L.main` —
**the same program `RunVerifier` runs.** So the bridge is:

> **for calldata that routes to `verifyProof` and passes the dispatcher's own ABI bounds, a
> `wrap` run is a `RunVerifier` run** (up to the layout tie).

**Prove that first.** It is the whole transport. Note `ShellModel.lean` already has
`runOn`, `dispatcherCode`, `armBody` and the wrap-level corollaries to build on.

## Then restate and prove

1. **Restate `lowering_equivalence`** (`Obligations.lean:649`) over `ShellModel.wrap`, dropping
   `(ir)`, `(irLyt)` and `(hir : S.irCheck ir = true)`. Keep all three conjuncts and the
   **soundness/completeness asymmetry exactly**: soundness over `permissive` calls and ANY
   gas; completeness over honest calls and `ofFun _ => 0`; the two-outcome read-only conjunct.
   Keep `DeploymentW`, `Holds`, `EnvAgrees`, `G1CodecLaws`, `SupportedS`, `hside`.
2. **Check whether `hsel` is still needed.** The selector check now lives INSIDE the modelled
   dispatcher, so `bytesTake cd 0 4 = some fnSigVerifyProof` may be derivable from the run
   rather than hypothesised. **If it can be derived, derive it** — fewer hypotheses is
   stronger. If dropping it changes the claim's meaning, keep it and say why.
3. **PROVE it.** The sketch calls it a transport through `hc : LoweringCorrect S product`. If
   it does not close, name the exact gap — **do not weaken a conjunct to make it close.**

## Non-vacuity is mandatory (D-P23), and this is the risk

**Exhibit the hypothesis bundle as jointly inhabited** at a real Surface: `DeploymentW ∧ Holds
∧ EnvAgrees ∧ G1CodecLaws ∧ SupportedS ∧ hside`. Note the trap: `curveSurface` exhibits `Holds`
at *its* codecs, but the theorem needs it at `S.E.g1`. **If no Surface witnesses the whole
bundle, that is the finding** — same class as the `hcd` vacuity and the `ir_refines`
refutation. Also give falsifications: a calldata failing the selector, and a run that is
neither return nor revert.

## Record the scope decision

* **`P-SE-statements.md`, same change**: the sketch quantified over solc's IR; the landed
  theorem quantifies over the generated Yul plus an in-tree model of the Solidity entry path.
  The link to solc's actual output is **out of scope by human decision (option A)**, not
  weakened. Name Tier 3 explicitly so nobody thinks it was forgotten.
* **Update the gates** pinning the old shape — `check_statement_fingerprints` and
  `check_hypothesis_bundles` cite `RunContractIR`/`irCheck` for this theorem.
* **Do NOT delete `ShellModel.lean` or `IRCheck.lean`.** `ShellModel` is now load-bearing;
  `IRCheck` is the Tier-3 bridge, keep it and note it is off the headline path.
* **Check the other 13 `RunContractIR` mentions in `Obligations.lean`** — if any of the 48
  `LoweringCorrect` fields is stated over the IR rather than the shell, list it.

## Constraints

* **Never weaken any statement other than the authorised restatement.** Every other spec stays
  as sketched.
* **D-P23 both halves as theorems.** Falsification-deletion gap measured **25 times**.
* **AFTER ANY SCRIPTED INSERT, ASSERT THE FILE GREW.**
* **SORRY.md traps**: `sorry` in a string literal counts; comment edits shift `file:line`
  pins. Regenerate with `scripts/gen_sorry.sh`; three-way agreement.
* **`Statements.lean` is FROZEN** — do not touch it or its `.sha256`.
* **Gate changes must keep all 13 sections green and be shown to redden** (R-41).
* **Never run `checks.sh` while a file is being edited** — stale oleans give bogus KAT
  failures. Gate ~9–10 min.
* **RAM (D-P31)**: `ram_guard.sh --selftest` first; `--proc-limit 6G --limit 24G`.
* **Durability**: land incrementally, keep the tree green, interim report after the key lemma.
* Do NOT edit Rust, `vendor/`, `ShellModel.lean` or `IRCheck.lean` **bodies** (adding lemmas is
  fine), and do NOT touch `Halo2/Exec/Accumulator.lean`, `Lowering/Accumulator.lean` or
  `scripts/kat_gate.py` — another agent owns those. Do NOT git add or commit. No scratch.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5215 jobs**; register **42** (another agent is mid-flight, so expect it to
move again). `checks.sh` sections: 235 fragments, 1317 KATs, 30 pins, Statements hash OK.

Read first: `Midfall/Yul/ShellModel.lean` (**`wrap`, `armBody`, `runOn`, `dispatcherCode`, the
three falsifications**), `Midfall/Lowering/Obligations.lean:600-700` (the current statement
and its long docstring enumerating why it is not yet provable), `Midfall/Lowering/Surface.lean`
(`RunVerifier` :797, `RunShell` :742, `RunContractIR` :735, `shell_unfolds`, `DeploymentW`),
`Midfall/Instances/SurfaceFixture.lean`, sketch section R, `docs/PLAN.md` lines 17 and 70.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green.
- The key lemma (`wrap` run ≡ `RunVerifier` run on routed, bounds-passing calldata) landed.
- **`lowering_equivalence` restated over `ShellModel.wrap` and PROVED**, or the exact
  remaining gap named with the same precision as the `ir_refines` refutation.
- Non-vacuity exhibit + falsifications, or a plain statement that the bundle is uninhabited.
- Deviation recorded; gates updated.
- **Required finding**: is the headline theorem now closed? If yes, what does the project
  still owe before `lowering_correct` can be stated for a real Surface?