# V3-evidence — what backs REVIEW-V3 and PLAN-V3

Everything here is **evidence and specification, not landed code**. The directory is under `docs/`:
`lake build` does not compile it and no gate scans it (`sorries.sh`, `kat_gate.py` and
`check_orphans.py` walk `Midfall/` only), so a `sorry` in a proposed statement here is not a
registered hole. Each file is landed in the tree by the PLAN-V3 card named in PLAN-V3 §3.

## Check it

From `formal/`, after `lake build`:

```bash
bash docs/plans/V3-evidence/check.sh
```

That typechecks every Lean file below against the built tree, one process at a time, in about six
minutes, and prints `ok` or `FAIL` per file with its sorry-warning count. Compiled interfaces and
logs go to a temporary directory; nothing is written into the repository. One area only:
`bash docs/plans/V3-evidence/check.sh reference` (areas: `probes`, `statements`, `soundness`,
`prooftech`, `reference`, `object`, `tooling`, `widening`).

The measurements cited in PLAN-V3 §3 are the `#eval` output in those logs: for example
`reference/RunABC.log` is the staged run of the Lean verifier on the Rust proof, and
`statements/StatementsV3Deploy.log` is the clause table at the fixture.

## Contents

| path | what it is |
|---|---|
| `ReviewProbes.lean` | The review's machine-checked findings. Self-checking: it elaborates with no output exactly while the recorded facts hold. When a repair lands, the probe for the repaired fact stops elaborating; delete or flip it in the same commit. |
| `findings-full.md` | Every raw finding of the review (115 from the reviewers, 37 from the skeptics) with evidence, counterexample, verdict and proposed fix. Generated; not edited by hand. |
| `design/*.md` | The six design memos behind PLAN-V3, as delivered: `statements`, `soundness`, `prooftech`, `reference`, `object`, `tooling`. They hold the measurements, the options that were rejected and the implementer pitfalls. Where a memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text (two known cases: the block scope, where the statements memo's measured choice was taken over the object memo's; and decision numbers, which follow PLAN-V3 §2). |
| `lean/statements/` | The repaired statement surface (`StatementsV3.lean`), its evaluation at the fixture and the falsifiers of the frozen text. |
| `lean/soundness/` | The staged simulation architecture with all composition proved (`SoundnessV3.lean`), the raw-decode lemma, the exit scan and the point-set measurement. |
| `lean/prooftech/` | The verified `wp` engine, its Bridge instance and driver, the lawful executable dialect, generated slice literals, and three block prototypes. `GenLits.lean` is the generator of `Lits.lean` and is not run by `check.sh`. |
| `lean/reference/` | The two verifier repairs as patched copies, the computable codec and constructed pairing, real key data, and the staged runs of the Lean verifier on the Rust proof with their falsifiers. `RunLib.lean` reads `fixtures/conformance/poseidon/` relative to `formal/`. |
| `lean/object/` | The token parser, the glue port of `LoweringPlan::new`, `generateAll`, `ValidV3`, the constants clause, and the coverage measurements. |
| `lean/tooling/` | `#assert_axioms`, the cone and sorry reports, the closure fingerprint, and `structure Done` with `not_done_today`. `Report.lean` (the full report, about 20 s and 400 kB of output) is shipped but not run by `check.sh`. |

## Added on 2026-11-17 for D-P71, D-P72 and D-P73 (the generator theorem)

| path | what it is |
|---|---|
| `lean/statements/GeneratorTheorem.lean` | D-P71's headline `lowering_correct` for every render, proved from four obligations (three open); `GateAtV3`, `GeneratorDone`; the falsifier `lowering_correct_needs_valid` (proved). |
| `lean/soundness/GeneratorRows.lean`, `GeneratorRowsWitness.lean` | Every block row stated for every render, with its children as named open obligations; the composition proved; the helper scope proved for every render; premise gaps as `PG_*` definitions. The witness file holds the tests at F1 (`native_decide` only there). |
| `lean/prooftech/VKP.lean` | The vkLoading block with its layout constants as free variables: `vk_all_param`, proved for every constant table and scope (7 leaves). One open statement, `wpSS_exists_C`. |
| `lean/prooftech/LoopRule.lean` | An invariant rule for a `for` loop with a symbolic bound, proved, with a witness and two falsifiers. |
| `lean/widening/*.lean` | D-P72: the supported class widened to accumulator mode and the external evaluator (`SupportedW`, `LeanAcceptsAcc` and its two Rust corollaries, `EvaluatorTrust`, `LoweringEquivalenceW`, the staged invariants). `IvcPartials.lean` renders seven template partials and finds each once in the tracked IVC `Halo2Verifier.sol`. |
| `lean/object/GeneratorCertified.lean`, `CertMeasure.lean` | D-P73: `generator_certified` and `generator_correct`, with hypotheses on the generator's input only, proved from 33 named open lemmas; their decidable conclusions evaluated at F1. |
| `design/rows-generic.md`, `prooftech-generic.md`, `ivc-widening.md`, `ivc-object-reference.md`, `generator-certified.md` | The five design memos behind those files: measurements, rejected options, pitfalls. Where a memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. |

These files state theorems over three different texts of validity (the tree's `R.Valid`, the
18-clause `ValidV3` of `StatementsV3.lean`, the 7-clause `Render.ValidV3` of `ObjectV3Full.lean`).
Cards RECON.1 and RECON.1b make them one.

## Limits

- Measured at `f2fe99b` … `4b525ef`; the 2026-11-17 additions at `cf00592`. Re-run `check.sh` at
  the commit you rely on. `check.sh` checks that each file elaborates; it does not compare the
  `#eval` outputs a card's VERIFY FIRST line quotes: read those in the log.
- `lean/widening/IvcPartials.lean` reads the tracked
  `proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol`.
- `lean/soundness/RawDecode.lean` reads
  `proofs/solidity-verifier/target/poseidon-fixture-dump/calldata.bin`, which is not tracked; on a
  checkout without it that one measurement prints a read error and the proofs still check.
- The reference runs use two shims for repairs the tree does not have yet (canonical rotations,
  slot grouping). `reference/RunG.lean` shows what the tree's own `prepare` returns today.
- A file that typechecks states what it states. Whether a proposed statement is the *right*
  statement is the subject of PLAN-V3 §2's decisions and of rule W12 (a witness and a falsifier
  before any brief).
