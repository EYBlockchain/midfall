# P-SE stage 1 - `Yul/Bridge`, `Yul/Contracts`, `Assumptions/{Codec,Eip2537}`

Status: READY. **Stage 0 is complete and verified**: `lake build` green at 3401 jobs;
`#check @Midfall.Halo2.decodeAcc` resolves; `Lowering/SemanticEquivalence.lean` is
committed (`8e80ca1`) with one real proved theorem; the `checks.sh` numeric-sort fix and
the `gen_sorry.sh` owner arms for `Yul/`, `Lowering/`, `Assumptions/` both landed
(`880733d`).

**Tree now**: 3401 jobs, 989 KATs across 53 files, 75 modules, 4 tracked sorries. The
generator port is effectively complete - `derivedRender_bytesExact_ok`
(`Instances/DeployedProfile.lean:533`) renders the deployed contract byte-exactly from a
derived context, differing only in `BUILD_ID`.

## Files to create

| file | content (P-SE architecture index) | |
|---|---|---|
| `Midfall/Yul/Bridge.lean` | open-dialect `Run`/`RunCommitted`, `det`, the keccak hook, `Obs`, honest/permissive calls | resolves **Y-3** |
| `Midfall/Yul/Contracts.lean` | the forall-runs partial-correctness layer, dialect-generic | |
| `Midfall/Assumptions/Codec.lean` | `G1CodecLaws` (hypothesis structure) + `frOfRepr_frToRepr` | |
| `Midfall/Assumptions/Eip2537.lean` | `G2Enc`, `Eip2537.Holds`, `modexpInv_correct` | |

Also read `docs/plans/P-BR-bridge-run.md` - it planned this same object earlier and
located Y-3 concretely: `BigStep.Run` is generic but `RunCommitted` at
`Observation.lean:39` is hard-wired to `EVM.Op`/`VEnv EVM.evm`.

## The decisions this stage must honour, not relitigate

* **D-P10 / the review's recommendation**: parameterise the committed-run layer **with
  explicit conditions that preserve determinism** - do not assume a generic external-call
  relation is deterministic.
* **attack.md FIX line 36 (binding)**: `ir_refines` needs **world-local** call relations.
  `WorldLocal c := forall req st st' r, CallWorld.ofState st = CallWorld.ofState st' ->
  (c.Call req st r <-> c.Call req st' r)`, with `gas := ExternalGas.ofFun (fun _ => g0)`.
  A relation reading `st.memory 0x40` separates IR from shell. Build this in from the
  start; retrofitting it is what the FIX line exists to prevent.
* **attack.md FIX line 32 (binding)**: `DeploymentW` needs `callvalue = 0`, the
  `AUTHORIZED_VK` immutable equal to `vkAddr` (and the quotient twin), and
  `memoryguard <= 0x1000`. Plus the codec laws `toEip 1 = zeros` and `eipRoundtrip` as
  hypotheses of every headline field.
* **Review F1 (already applied to PLAN 9.5)**: run existence must be explicit, never
  implied by a forall over an empty set of runs.

## Rules from the user's directive - these are binding

1. **Before each file, read `P-SE-evidence/attack.md` and the matching `design*.md`**
   (`design0/1/2.md` are in `P-SE-evidence/`). **attack FIX lines are binding.**
2. **Verify every `-- SKETCH` name against `P-SE-evidence/survey.md` or `#check`.** A
   sketched identifier that does not resolve is a finding, not something to invent.
3. **Doc comments in the style of `Exec/Accumulator.lean`** - read it first. That file's
   headers state what each object is for, which plan section cites it, and where a known
   falsehood lives (it carries the R-25 note).
4. **Register every proof hole in `SORRY.md` via `scripts/gen_sorry.sh`.** The owner arms
   for `Yul/`, `Lowering/`, `Assumptions/` already exist. Run the script and confirm
   `SORRY.md` is regenerated, not hand-edited.
5. **NEVER edit `Statements.lean`.** It is frozen and CI checks its hash. Findings about
   it are reported for a re-pin.
6. **If a statement is false as written, STOP AND REPORT** (PLAN 12). Do not weaken a
   statement silently. Two precedents this session: `decodeAcc_injective` was listed
   unchanged despite a known counterexample, and `end_to_end_noAcc` was vacuous.

## Hazards

1. **`lake env lean` does not apply lakefile options** - it accepts code `lake build
   rejects`. Every number from `lake build` and `scripts/checks.sh`.
2. **Register your modules** in `Midfall.lean`. The orphan gate is a hard failure and it
   caught the orchestrator's own scratch file today.
3. **The vendored dialect lacks `memoryguard` and `setimmutable`** (D-P15 prerequisite).
   If stage 1 needs them, report that rather than editing `vendor/` - it is a pinned fork.
4. **`Eip2537.Holds` shape**: D14 says 2-pair `pairing2` (P2) with the `G2Enc` wrapper
   (P1), and `Modexp.Holds` is a THEOREM (`modexpInv_correct`), not an assumption. Do not
   state as a hypothesis something the plan says to prove.
5. **D-P17**: no theorem-bearing file may import `Midfall/Instances/`. `checks.sh`
   enforces this.
6. **Re-measure inherited claims in both directions.** This session has produced one
   false 'live defect' claim, one false blocker claim, and one missed-file planning error
   that cost a whole package.

**No idle builds.** Anchored multi-line edits have cost the orchestrator ten swallowed
lines across three repairs - re-read what you changed, rebuild after each edit.

Do NOT edit Rust files, `Statements.lean`, or another package's Lean file. Do NOT git add
or commit. Editing `SORRY.md` only via `gen_sorry.sh` is allowed.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 989 across 53 files.
- All four files exist, registered, with doc comments in the `Accumulator.lean` style.
- Every `sorry` in them registered in `SORRY.md` with an owner, via the script.
- **Required finding**: (a) is Y-3 resolved such that `RunContractIR` from PLAN 9.5 can
  now be written? (b) list every `-- SKETCH` name from the plan that did NOT resolve
  against `survey.md` or `#check`. (c) state whether stage 2 can start.
