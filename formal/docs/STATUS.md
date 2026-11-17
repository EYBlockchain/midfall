```
imports_avoid: ok (14 modules)
cone_avoids Midfall.LoweringV2.lowering_equivalence_of_blocks: ok (14 modules)
cone_avoids Midfall.LoweringV2.end_to_end: ok (14 modules)
cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks: 5
Midfall.LoweringV2.noWriters_prog
Midfall.LoweringV2.prefix_run_clean
Midfall.LoweringV2.rejects_of_not_accepts
Midfall.LoweringV2.runBody_iff_slices
Midfall.Yul.Bridge.Run_worldEq_of_noWriters
cone_sorries Midfall.LoweringV2.end_to_end: 1
Midfall.LoweringV2.end_to_end
cone_avoids Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok (14 modules)
cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: 9
Midfall.LoweringV2.blockContracts_of_valid
Midfall.LoweringV2.noWriters_prog
Midfall.LoweringV2.prefix_run_clean
Midfall.LoweringV2.rejects_of_not_accepts
Midfall.LoweringV2.runBody_iff_slices
Midfall.Instances.PoseidonV2.poseidon_quotient_block
Midfall.Instances.PoseidonV2.poseidon_rejects
Midfall.Instances.PoseidonV2.poseidon_valid
Midfall.Yul.Bridge.Run_worldEq_of_noWriters
cone_sorries Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts: 3
Midfall.LoweringV2.Blocks.FinalPairing.ec_pairing_contract
Midfall.LoweringV2.Blocks.FinalPairing.fp_pairing_algebra
Midfall.LoweringV2.Blocks.FinalPairing.fp_stmt_steps
cone_sorries Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress: 0
cone_avoids Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress: ok (14 modules)
cone_avoids Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts: ok (14 modules)
cone_sorries Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound: 0
cone_avoids Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound: ok (14 modules)
cone_sorries Midfall.LoweringV2.Blocks.VkLoading.vk_blockRow: 3
Midfall.LoweringV2.Blocks.VkLoading.vk_poison_walk
Midfall.LoweringV2.Blocks.VkLoading.vk_progress
Midfall.LoweringV2.Blocks.VkLoading.vk_sound_clean
cone_sorries Midfall.LoweringV2.Blocks.VkLoading.vk_slice: 0
cone_avoids Midfall.LoweringV2.Blocks.VkLoading.vk_blockRow: ok (14 modules)
assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok (9 named, 1 native)
assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound: ok (3 named, 0 native)
assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockProgress: ok (3 named, 0 native)
cone_report Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: 9 sorried leaves = 8 OPEN + 1 REFUTED + 0 VACUOUS  [UNREACHABLE (a leaf is refuted: False is derivable, the count is not a distance)]
  OPEN     Midfall.Instances.PoseidonV2.poseidon_quotient_block
  OPEN     Midfall.Instances.PoseidonV2.poseidon_rejects
  REFUTED  Midfall.Instances.PoseidonV2.poseidon_valid   (negation proved: Midfall.Instances.PoseidonValid.poseidonRender_notValid)
  OPEN     Midfall.LoweringV2.blockContracts_of_valid
  OPEN     Midfall.LoweringV2.noWriters_prog
  OPEN     Midfall.LoweringV2.prefix_run_clean
  OPEN     Midfall.LoweringV2.rejects_of_not_accepts
  OPEN     Midfall.LoweringV2.runBody_iff_slices
  OPEN     Midfall.Yul.Bridge.Run_worldEq_of_noWriters
  axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Midfall.Assumptions.bls12_381Pairing,
 Midfall.Assumptions.blsGT,
 Midfall.Assumptions.blsGT_group,
 Midfall.Assumptions.blsGT_module,
 Midfall.Assumptions.blsGT_primeOrder]
  native axioms: 1 [Midfall.Instances.PoseidonV2.poseidonModel_isOk._native.native_decide.ax_1_1]
exhibits: 0 PRESENT, 4 MISSING of 4
  MISSING  Midfall.Instances.PoseidonExhibit.fixture_returns_abiTrue_ok
  MISSING  Midfall.Instances.PoseidonExhibit.fixture_leanAccepts_ok
  MISSING  Midfall.Instances.PoseidonExhibit.mutants_revert_ok
  MISSING  Midfall.Instances.PoseidonExhibit.mutants_leanRejects_ok
block_coverage Midfall.LoweringV2.BlockRow at Midfall.Instances.PoseidonV2.poseidonRender: 0 INTEGRATED, 1 CONDITIONAL, 2 SORRY, 4 NONE of 7
  SORRY       Midfall.Lowering.Partial.vkLoading  Midfall.LoweringV2.Blocks.VkLoading.vk_blockRow
  NONE        Midfall.Lowering.Partial.transcriptParser  
  NONE        Midfall.Lowering.Partial.lagrange  
  NONE        Midfall.Lowering.Partial.quotientLin  
  NONE        Midfall.Lowering.Partial.pcs  
  SORRY       Midfall.Lowering.Partial.finalPairing  Midfall.LoweringV2.Blocks.fp_blockRow
  CONDITIONAL Midfall.Lowering.Partial.traceReturn  Midfall.LoweringV2.Blocks.tr_blockRow (1 undischarged hypothesis/es, 18 binders)
slice_tokens [(Midfall.Lowering.Partial.vkLoading, 225), (Midfall.Lowering.Partial.transcriptParser, 925), (Midfall.Lowering.Partial.lagrange, 503), (Midfall.Lowering.Partial.quotientLin, 122), (Midfall.Lowering.Partial.pcs, 3625), (Midfall.Lowering.Partial.finalPairing, 24), (Midfall.Lowering.Partial.traceReturn, 25)]
program_tokens ast_main 6779 generator_text_main 14054 codegenAgrees false
axiom_sweep: ok (5 named axioms [Midfall.Assumptions.bls12_381Pairing,
 Midfall.Assumptions.blsGT,
 Midfall.Assumptions.blsGT_group,
 Midfall.Assumptions.blsGT_module,
 Midfall.Assumptions.blsGT_primeOrder], 126 native_decide axioms)
opaque / extern / implemented_by / unsafe constants of the project (39):
sorry_sweep: 58 declarations use sorryAx directly (1 REFUTED, 1 VACUOUS); 9 in the cone of Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon; 71 of 22468 project constants depend on it
closure_fingerprint [Midfall.LoweringV2.LoweringEquivalence,
 Midfall.LoweringV2.Render.Valid,
 Midfall.LoweringV2.HypothesesInhabited,
 Midfall.LoweringV2.EndToEnd,
 Midfall.LoweringV2.EntryFrameInhabited]: 3449 project declarations, 477 external leaves, digest a6ddb51ce1dae8bd
verify.sh: ok (--report)
```

## State at `13dd7a5` (card DG.8 — the block above is tool output; nothing in it is hand-transcribed)

- **Plan:** `docs/plans/PLAN-V3.md` (D-P60–D-P69, D-P71–D-P73 signed in `design.md`) · cards `PLAN-V3-cards.md` · rules `EXECUTION-V2.md` + PLAN-V3 §4 (W12–W15) · **order = the V3 table at the top of `docs/QUEUE.md`**.
- **The headline cone is UNREACHABLE, not a distance** (report above: `9 sorried leaves = 8 OPEN + 1 REFUTED`): `poseidon_valid` is refuted in the tree. That is a **live W13 violation** — the three questions at the foot of this file.
- **Gates:** `checks.sh` green at `13dd7a5` (run by this card); sorry register in sync — 58 sorried declarations, 9 in the cone, 1 REFUTED, 1 VACUOUS.
- **The goal changed 2026-11-17 (D-P71/72/73).** The deliverable is the generator theorem `lowering_correct` — for EVERY render with `ValidV3 R` — widened to the IVC verifier (`lowering_correctW`) and certified at the generator (`generator_correct`). **No block row, totality lemma or headline is proved at a fixture; fixtures are tests** (F1 Poseidon, F2 the IVC decider). A missed threshold of PLAN-V3 §5 M5 goes to the human; per-fixture rows are not a fallback.
- **D-P73 blocker, measured above:** `codegenAgrees false` — 6,779 AST tokens against 14,054 of generator text. CERT.1 probes two suspect lemmas first; a refuted one goes to the human.
- **First READY rows:** DG.6 in the table, held by the questions below; then ST.1, OBJ.17, Q0.5, S.10. **W14:** no Yul PROOF card is READY before T3.11's exhibit — the report shows **0 of 4 exhibits PRESENT**.
- **Waiting on human:** paste `v2-bundle/docs/GOAL-PROMPT.md` (everything below its line) as the orchestrator's `/goal` — **the prompt changed with D-P71 and D-P72.** D-P72 clause 9 asks the generator's owner for a free-memory guard in the evaluator template.

## The English statement (PLAN-V3 §6) — skeleton, trusted base itemised

- **The claim:** for every program the Lean port of the generator emits for a circuit in the supported class — `lowering_correct (R) (product) (hR : ValidV3 R) : LoweringEquivalenceV3 R product`. Before M10 that is conditional on `ValidV3 R`, checked by computation for each circuit; after M10 (D-P73) the only hypotheses are on the generator's input (`SupportedInput`: the scope clauses, a size bound, two codec laws) and the Lean printer is trusted. **UNTESTED** — `ValidV3 poseidonRender` is refuted today.
- **About the Lean generator's output:** the Rust generator is tested against it byte for byte on the test circuits, **not proved equal**. **UNTESTED** (`codegenAgrees false` above).
- **Test circuits** F1, and F2 after M9; **no on-chain contract is covered**.
- **The test SRS trapdoor is public** (D-P63): no soundness of the proof system is claimed for it.
- **The two side conditions** and what each excludes, saying that `SoundSide` is a predicate on prover-supplied calldata (RV-20).
- **In accumulator mode (M9):** the right-hand side is the contract's own batched check; against the Rust verifier the theorem is complete, and sound up to one value of `alpha` per input; the IVC and decider SRS are assumed to share one `[s]₂`.
- **The trusted base** — assumed, not proved away: the yul-semantics EVM dialect and the Bridge; `EntryFrame` (selector routing, zero call value, the free-memory prologue, zero memory from `0x80`, calldata shorter than 2²⁵⁶, the `memory-safe` footprint, the ABI decoder not reverting on decodable calldata); with the external evaluator, `EvaluatorTrust` (an account that passes the code-hash pin behaves as the generated evaluator body); the precompile assumption `Eip2537.Holds` in its two real-world halves, and that the chain implements EIP-2537 and modexp.
- **The Lean Yul token parser and `EVM.mkCall`** — they decide what tree a parsed region is. **UNTESTED** until OBJ.1's round-trip KATs land.
- **The axioms:** the standard three for `lowering_correct`; for `generator_done`, each `native_decide` axiom by owner declaration. Measured above: 9 named + 1 native at the headline; tree-wide `axiom_sweep: ok`, 5 named + 126 native_decide.
- **Port fidelity, and how each side is tested:** the generator by the artifact gates; the verifier by the reference gate and the mutation corpus. **UNTESTED** — 0 of 4 exhibits PRESENT.
- **Not modelled:** gas, including the forwarded-gas constants; solc.

## ⚠ WAITING ON HUMAN — a REFUTED node is in the cone, and DG.6 cannot clear it

**Found while checking DG.6's preconditions at `9a3d619` (not by briefing it blindly).**

- `theorem poseidon_valid : poseidonRender.Valid := by sorry` is **still in the tree**
  (`Instances/PoseidonV2.lean:190`).
- Its **negation is proved**: `poseidonRender_notValid : ¬ poseidonRender.Valid`
  (`PoseidonValid.lean:468`).
- **DG.2's own gate reports it**: `ok: 58 sorried declarations, 9 in the headline cone, 1 REFUTED`.

**This is a live W13 violation.** W13 requires a sorry whose negation is proved to be **deleted in the
same commit as the refutation** — the refutation landed two rounds ago (C.4) and the sorry is still
there. And W13's other clause: **a cone containing a refuted leaf is reported as UNREACHABLE, never as
a number.** We are reporting `9`.

**Why DG.6 cannot fix it.** DG.6's NEEDS names *"the ticket (statements area) that deletes
`poseidon_valid` or turns `Valid` into a hypothesis"* — **that ticket has not run and I cannot identify
it from the V3 table.** DG.6's step 1 is literally `After poseidon_valid is gone, add…`. Its `after`
column says only `DG.2`, which is merged, so **the table says READY while the NEEDS say otherwise.**
**The tool itself already exists** (`Done.lean:410`, `#assert_no_refuted_sorry`), so DG.6 is one line —
but only once the statements ticket lands.

**Three questions:**
1. **Which V3 card deletes or re-hypotheses `poseidon_valid`?** Is it ST.4 (D-P45's `HypothesesInhabited`
   work) or an M3 statements card? The table does not say, and DG.6 depends on it.
2. **Under D-P71, `poseidon_valid` is a proof at a fixture** — `poseidonRender.Valid` names a fixture.
   **Should it simply be deleted as V2 residue rather than repaired?** Under the restatement the
   theorem is `lowering_correct` over every render with `ValidV3`; a fixture-level `Valid` sorry may
   have no consumer at all in V3.
3. **Should the report print UNREACHABLE rather than 9** while a refuted leaf sits in the cone, per
   W13's final clause? If so that is a DG.2/DG.6 gate change, and I would rather you say so than have
   me reinterpret my own gate.

**Until answered I am starting no PROOF or SKELETON card** (the loop's rule for an open question of
this kind). INFRA cards that do not depend on it — **DG.7** (CI that runs and can pass, after DG.0+DG.2,
both merged) and **DG.8** (STATUS generated from the report, after DG.2) — are READY and are the next
things I will brief.

## ⚠ DG.7 HELD — question 4 for the human

**Question 4 for the human:** may a card push and delete `formal/ci-negctl` on `origin` to prove CI can go red — or should the CI negative control be done on a fork, or skipped with the gate's red-capability argued some other way?

**Context, checked at `d6cef1e`:** DG.7's step 4 is that create-and-delete on the shared `EYBlockchain/midfall` remote, and `.github/workflows/formal.yml` does not exist yet, so it must be created. Verified good news: the runner label `ubuntu-latest-16-core-x64` is already used by `ci.yaml` at `:47`, `:65`, `:92`. DG.7's own Guidance declares its premises untested (*“Nothing here was run in this session”*) — per the loop that is a probe to run, not a brief to issue blind. **The session before this one ended at round 46 by context exhaustion; four questions await the human: the W13 trio above, plus question 4.**
