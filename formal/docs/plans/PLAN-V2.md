# PLAN-V2 — prove the Lean verifier equivalent to the Solidity/Yul emitted by the Lean codegen

> **HAND-OVER TO PLAN-V3 — CONDITIONAL ON D-P60 (added 2026-11-17).**
> A review (`docs/plans/REVIEW-V3.md`) and a revised plan (`docs/plans/PLAN-V3.md`) are in the tree.
> **Until `design.md` holds a signed D-P60, this file is the plan and nothing below changes.** The
> orchestrator's goal prompt is unchanged in both cases; this banner is how it finds the new plan.
>
> - **D-P60 not signed** (check `grep -n '^## D-P60' formal/docs/design.md`): PLAN-V3 is PROPOSED.
>   Work `QUEUE.md` as usual. Its PLAN-V3 banner flags several READY cards; each flag is a *lead*
>   to verify, never a fact and never an instruction.
> - **D-P60 signed**: wherever the goal prompt says "PLAN-V2 §0–§4", read
>   **`PLAN-V3.md` §0–§4 and §10**; wherever it says "DONE means PLAN-V2 §6", DONE is
>   **PLAN-V3 §6**; the headline named in the goal is PLAN-V3 §5 M7's. §4 rules 1–12 of this file
>   and EXECUTION-V2 stay binding, with PLAN-V3 §4's W12–W15 added. The first card is **PL.0**
>   (in `QUEUE.md`), which performs the cut-over — **done 2026-11-17** (tag `formal/v2-cutover`). Each other PLAN-V3 decision (D-P61–D-P69) gates
>   only the cards that name it: an unsigned one leaves those cards BLOCKED, as W2 requires.

Handover brief for the implementing agent (Sonnet 5.5). Self-contained: read §0–§3 before
touching anything. Paths are relative to the repository root (`midfall/`).

> **For the human, before handing over.** The setup is **one orchestrator agent that delegates one
> ticket at a time to one subagent**.
>
> 1. **Push the V2 bundle on its own branch.** Push `v2-bundle/` (all files of §3 plus the docs) to
>    branch `v2/bundle` from a separate worktree. This does not disturb the agent's working tree or
>    `formal/baseline`.
> 2. **Give the orchestrator `GOAL-PROMPT.md` as its `/goal`.**
>    - It starts with the **cut-over** (EXECUTION-V2 §1) at the next package boundary: it drains the
>      in-flight P-RUNLEG, tags `formal/v1-final`, records D-V2, and fetches the bundle.
>    - It then works through `QUEUE.md`.
>    - Nothing proved is deleted.
> 3. **Read `EXECUTION-V2.md` once.** It covers the orchestrator loop, the subagent contract, rules
>    W1–W11, the cone-based progress measure, and why each rule exists.

---

## 0. Objective, in one sentence

Prove, in Lean 4, that for the deployed render, **the body of `verifyProof` emitted by the Lean port
of the Rust generator** (`formal/Midfall/Generator/*`, golden-tested against
`proofs/solidity-verifier`), run in the yul-semantics EVM dialect from the state Solidity hands it,
**returns ABI `true` iff the Rust-faithful Lean verifier accepts the decoded calldata, and otherwise
reverts without touching the world** — with **solc out of scope** (trusted) and **no free fields and
no obligation bundles** in the claimed theorem.

## 1. Why v1 is retired (proved, not argued)

`formal/Midfall/Lowering/LegacyVacuity.lean` (provided, kernel-checked, standard axioms only):

| theorem | meaning |
|---|---|
| `not_LoweringCorrect : ∀ S product, ¬ LoweringCorrect S product` | v1's headline `Lowering.lowering_equivalence` has an **unsatisfiable** hypothesis at every Surface. `ir_refines` quantifies over every object passing `Surface.irCheck`, which accepts arbitrary programs; an empty and a stuck object cannot both be `ObsEquiv` to one `RunShell`. No determinism lemma needed. |
| `ir_refines_field_is_false` | the same field refuted with a `revert(0,0)` object |
| `stuck_satisfies_every_post` | a ∀-runs contract over code that reads an unbound name holds for **every** postcondition; v1's per-partial specs are over **un-inlined** fragments whose helpers (6 of 8) read contract constants they cannot see, so they are vacuous on the paths that matter |

Other v1 defects V2 fixes by construction:

- **Free fields.** `Surface.L`, `lower`, `plan`, `blk`, `shell`, `bindLocals`, … were free. As a result the fixture's plan (poseidon, 72 slots) and VK (8 reads) described different circuits with every pin green (`ObligationsGates.readScheduleAgrees_refuted_at_deployment`).
- **Progress contracts asserted no existence** (partial correctness).
- **`ShellModel.wrap` ran the un-inlined arm**, which is stuck.
- **Over-claims in the log.** P-LOWEQ reported "the headline theorem of the project is PROVED" for a conditional whose bundle was empty.

## 2. Scope decision D-V2 (record verbatim in `formal/docs/design.md` as the next free D-P number — expected D-P43: P-DET took D-P42 at `af46ef9`, and P-RUNLEG reserved D-P43 for an `ir_refines` edit that D-V2 makes moot. Pre-approved by the human through the `/goal` prompt; supersedes D-P38, Q-OPEN-1)

1. **Object of the theorem:** the Yul of the two `verifyProof` assembly blocks as printed by the Lean
   text port (`Generator/Contracts.renderHalo2Verifier`), parsed by construction through the
   `GenAst` emitter and tied to the text by token equality (`CodegenAgrees`), with contract-level
   constants substituted (`Inline.inlineContractConstants`) — Solidity's own constant semantics.
2. **Trusted base:** delete the two solc rows of PLAN §1 (the "checked Solidity→IR" row and the
   "trusted optimizer" row) and add ONE row: *"Solidity entry semantics of the generated wrapper:
   `EntryFrame` (`LoweringV2/Statements.lean` §3) — selector routing, `view` ⇒ zero call value, ABI
   decoding only reads calldata, solc's free-memory prologue leaves `mload(0x40) ≤ TRANSCRIPT_MPTR`,
   fresh frame. Trusted; validated by the revm differential (M4), not in Lean."* Everything solc
   adds before the assembly can only revert, so soundness and two-outcomes do not depend on it.
3. **Retired** (stop work; keep building until WP-X6 deletes them): `LoweringCorrect`,
   `Lowering.lowering_equivalence`, `end_to_end_noAcc`/`end_to_end_acc_complete` (v1),
   `RunContractIR`, `Surface.irCheck`, `ir_refines`, `Yul/ImportSolcIR.lean`, `Yul/IRCheck.lean`,
   `Instances/ImportedIR.lean`, `Instances/IrCheckBlindness.lean`, `Instances/RunShellInversion.lean`,
   `Instances/RunShellInhabited.lean`, `scripts/gen_import_solc_ir.py`,
   `scripts/perturb_import_ir.py`, `Yul/solc-ir-*.yul`, milestone M8, P-DET. `Yul/ShellModel.lean`
   is kept only as raw material for optional WP-X5.
4. **Per-deployment first** (D-P24 stands). The claimed headline is
   `lowering_equivalence_poseidon (product : PairingProduct) : LoweringEquivalence poseidonRender product`.
   - It is stated for **every** pairing product. `LoweringEquivalence` already takes
     `Eip2537.Holds … product` as a hypothesis, so no pairing implementation is ever needed.
   - The one concrete product, `HoldsFinal`'s exhibited `poseidonProduct`, is used only for
     non-vacuity (`HypothesesInhabited`).
   - The ∀-render theorem is WP-X4.
5. **Trusted evaluation.** Decidable facts about the deployment (`poseidon_valid` clauses, codegen
   agreement, fixture KATs) may be closed by `native_decide`, only in `Instances/` (D-P17).
   - The headline's axiom list may therefore contain the compiler-trust axiom(s) `native_decide`
     adds. Q0.3 records their exact names in this toolchain. **Measured at `96910d3` on Lean 4.35.0: `native_decide` adds exactly one axiom per declaration, named `<declName>._native.native_decide.ax_1_1`; it adds no `Lean.ofReduceBool`, no `propext`, no `Classical.choice` and no `Quot.sound`. Confirmed on three declarations.**
   - A kernel-only re-check is optional, as WP-X8.

## 3. Starting point: four files provided (all compile against `979f358`, verified out of tree)

| file (repo path) | content | `sorry`s |
|---|---|---|
| `formal/Midfall/LoweringV2/Program.lean` | the program as a function of `(plan, model)`: `planViewOf`, `constTableOf`, `abiGuardBlock`, `mainGuardBlock`, `mainLocals`, `mainAsmRaw`, `wrapperLocals`, `asmOf`, `helpersOf`, `sliceOf`, `mainClosed`, the codegen text (`partsOf`, `mainAssemblyText`, `abiGuardText`) and **`CodegenAgrees`**; `emitSlices_eq` (proved) | `inline_append` |
| `formal/Midfall/LoweringV2/Statements.lean` | §1 `Render`; §2 `SupportedV2`, **`Render.Valid`**; §3 `DeploymentV2`, **`EntryFrame`** (trusted), `callsOf`, `RunBody`; §4 `LeanAccepts`, `SoundSide`, `CompleteSide`; §5 **`LoweringEquivalence`** (the headline); §6 block-contract layer (`Frame`, `Clean`, `Poisoned`, `exitOk`, `BlockSound`, total `BlockProgress`, `BlockContractsAt`, `Rejects`); §7–§9 obligations, non-vacuity, `end_to_end`. **Known defect, fixed by Q0.2:** it imports the retired `Surface`/`Partials` and the parked `Accumulator`, for 7 small definitions; `Program.lean` reaches them through `FrameWalk → RunEmitted` | `hoist_prog_addr_indep`, `blockContracts_of_valid`, `lowering_equivalence_of_blocks`, `entryFrame_inhabited`, `end_to_end` |
| `formal/Midfall/Lowering/LegacyVacuity.lean` | the three refutations of §1 | none |
| `probe/CodegenProbe.lean`, `probe/CoverageProbe.lean` (scratch) | evaluate `CodegenAgrees` at the deployed poseidon profile; become KATs in WP-A1 | — |
| `formal/Midfall/Tools/ConeSorries.lean` (+ `tools/ConeSorriesTest.lean`, kept outside `Midfall/`) | `#cone_sorries foo`: the sorried declarations in `foo`'s dependency cone, i.e. the progress measure. Tested on v4.35.0: 3 `#guard_msgs` cases; on this repo's build `traceReturn_spec` → 0 and `transcriptParser_spec` → 1, in about 30 s | none |
| docs: `EXECUTION-V2.md`, `QUEUE.md`, `STATUS.md`, `GOAL-PROMPT.md` | how to run this plan with one orchestrator and one subagent; the live queue; the initial status; the orchestrator's main prompt | — |

All of these ship in `v2-bundle/` on branch `v2/bundle`, outside `formal/`, so no gate scans them
before Q0.1 lands them.

**Frozen surface** (changes need human sign-off and a fingerprint re-pin, D-P27 procedure):
`Statements.lean` §1–§5 and `Program.lean` §2–§4. **Refinable**: `Statements.lean` §6 under the
four invariants stated in its header (closed slices, total progress, poisoned `success`, facts via
`Frame`).

**Measured at `979f358`, deployed poseidon profile** (probes):

| region of the main block | AST tokens | codegen tokens | agrees |
|---|---|---|---|
| ABI-shape guard block (first `assembly`) | — | — | **yes** |
| MF-2 guard + AssemblyHelpers | 1303 | 1303 | yes |
| AccumulatorHelpers (emitted even without accumulator) | 0 | 823 | **no** |
| VkLoading / TranscriptParser / Lagrange | 223 / 923 / 501 | same | yes |
| QuotientAndLinearization (numerator region) | 120 | 6572 | **no** |
| PCS | 0 | 2 | **no — both sides empty**: the typed-in `poseidonMeta` yields no PCS code; fixed by deriving the meta from the real VK (WP-I1/WP-G4) |
| FinalPairing / TraceReturn | 22 / 23 | same | yes |
| `constTableOf` vs the pinned 90-constant poseidon table | | | identical; `TRANSCRIPT_MPTR = 0x1000` |

## 4. Ground rules (each one is a v1 failure)

1. **No free fields or free functions in a statement.** A record may hold *inputs*. Anything the
   generator produces is either a function or a field checked by a decidable clause of `Render.Valid`.
2. **Obligations are theorems** (with `sorry`, registered), never hypotheses of the claimed headline.
   The headline's hypotheses may only mention: world, hash, calldata, entry frame, precompile
   semantics (`Eip2537.Holds`), codec laws, and the two negligible side conditions.
3. **Never quantify over programs/objects inside a hypothesis** (the `ir_refines` lesson).
4. **Whole-bundle non-vacuity.** A theorem with a bundle hypothesis (e.g.
   `lowering_equivalence_of_blocks`) is a lemma; it is never reported as a result until the bundle
   is *proved* at the deployment. D-P23 applies to the hypothesis set **jointly**, including the
   bundle, not leg by leg.
5. **Contracts are about the program that runs:** `R.slice q` in `R.scope` (inlined, closed).
   Completeness-side contracts are **total** (`StmtsTotal`: a run exists ∧ every run is good).
6. **Measure, then estimate; evidence is current-commit output.** A fact in a brief or a report is a
   command output or a kernel-checked theorem *at the current commit*. Comments, docstrings, ledger
   prose and earlier diagnoses are leads to re-check. A blocker is a minimal reproducer (an
   `example` plus the error text). Before sizing anything, write a probe (`#eval`) that measures it;
   the coverage table above took 10 minutes and replaced guesses. Verify names with `#check`, not
   grep.
7. **`lake build` green does not mean KATs passed** (ETA R23). Run `python3 formal/scripts/kat_gate.py`
   and `bash formal/scripts/checks.sh` too. `lake env lean` ignores `autoImplicit = false`; never
   report numbers from it.
8. **Resources** (D-P31): run heavy work under `bash formal/scripts/ram_guard.sh --limit 6G -- …`;
   one build at a time; check `ps` for other `lake`/`lean` processes first.
9. `native_decide` only under `formal/Midfall/Instances/` (D-P17). Keccak is `@[extern]`, so anything
   that squeezes a challenge needs it; everything else should be kernel-checked.
10. Do not edit `formal/vendor/`, the frozen `formal/Midfall/Statements.lean`, or the frozen V2
    surface without a written decision and sign-off.
11. Lean 4.35 traps: `meta` and `at` are keywords; multi-field structure updates on one line;
    `List.range' s n` takes a count; `List.zipIdx` yields `(x, i)`; fuel per **nesting level** not
    per list element (P-INLINE perf finding); `yulTokens` splits `"memory-safe"` into three tokens.
12. **Report in four categories only:** *stated*, *proved* (`#print axioms` = standard three [+ the five
    D-P36a curve axioms where a curve instance is used]), *proved conditionally on X*, *exhibited*.
    Docs follow the EXECUTION-V2 W8 budget.
    - Every ticket: `formal/SORRY.md` (via `scripts/gen_sorry.sh`), an overwritten one-page
      `docs/STATUS.md`, one `docs/ETA.md` row, and a ≤ 15-line report as the commit body.
    - `REVIEW.md` only for real defects; `design.md` only for human decisions.
    - `PROGRESS.md` is retired (stale since P-M8-SHELL).

## 5. Work packages

The WPs below describe **what** each area needs. **`QUEUE.md` cards are what the agent executes**,
and they supersede the WP text wherever the two differ:

- Phase 0 → T0.1–T0.4 and Q0.1–Q0.4;
- WP-I1 and the deployment parts of WP-I2 → D.1–D.3;
- WP-M0 → M0.1, C.2, C.3;
- WP-A1 → G.1;
- WP-G1 → G.2–G.4;
- WP-G3/G4 inventories → G.5/G.6.

Later WPs become cards when their SKELETON ticket runs.

**Execution:** do not hand a WP to the agent whole.

- **Tickets.** Each card has one layer, one deliverable, NEEDS / DOES NOT NEED, and a ≤ 2.5 h box.
- **Consumer first.** The headline is stated at the deployment early (C.1). Its composition (C.2)
  and validity (C.4) are skeletoned with named, `sorry`'d lemmas. Tickets are issued only for nodes
  in that cone (W1, W3).
- **When a proof ticket is done.** The lemma is used by its consumer and `#cone_sorries` of the root
  drops.
- **Families** get one shared case-split lemma and a complete requirements table first.

### Phase 0 — cut-over, land V2, retire the solc track (EXECUTION-V2 §1; QUEUE T0.1–T0.4, Q0.1–Q0.4)

**WP-0.1 Land, cut, freeze** (three cards).

- **Q0.1** lands the files unchanged.
- **Q0.2** cuts V2 off the retired modules.
  - It copies the 7 definitions and the `freeNames` walker into `LoweringV2/Shared.lean`; v1 files
    are untouched.
  - It lands the cone tool, with `#imports_avoid`/`#cone_avoids` guards over 14 modules.
- **Q0.3** splits frozen from refinable.
  - **Frozen:** `Program.lean` §1–§4, `Shared.lean`, and `Statements.lean` §1–§5, plus
    `HypothesesInhabited`, `calldataOf`, and the statements of `end_to_end` and
    `entryFrame_inhabited` as `Prop` defs.
  - **Refinable:** `ProgramLemmas.lean` and `Blocks.lean`.
  - It pins the frozen files with `Frozen.sha256`, through one line in `checks.sh`, and writes
    `scripts/verify.sh` (`--quick` for subagents; full, once per ticket, for the orchestrator).
  - There is no falsifier registry, and the token gates are not extended to V2 (W6).

*Accept:*

- `verify.sh` green;
- `#print axioms Midfall.Lowering.LegacyVacuity.not_LoweringCorrect` =
  `[propext, Classical.choice, Quot.sound]`;
- `SORRY.md` lists exactly the 6 new V2 holes;
- the `ConeReport` guards pass;
- editing a frozen file reddens `checks.sh`.

**WP-0.2 Decisions and plan** (orchestrator, docs only; T0.2–T0.4).

- Tag `formal/v1-final`.
- Record D-V2 (§2) in `design.md` as the next free D-P number (pre-approved).
- Close Q-OPEN-1 and supersede D-P38.
- Point `PLAN.md`'s header to this file.

**Do not edit any v1 `.lean` file.** V2 copies what it needs (Q0.2): `Statements.lean` is
sha256-pinned, v1 gates read `Surface.lean` and `Partials.lean`, and header edits shift the line
numbers `SORRY.md` records. Old briefs are not moved; `QUEUE.md` is the only live queue.

**WP-0.3 Adversarial statement review of V2** (1, fresh session, read-only). For each frozen statement
try to make it vacuous, trivially true, or false. In particular: is `Render.Valid` jointly
satisfiable? Can `EntryFrame` be empty? Does any clause hold for a degenerate model (cf. the PCS row)?
Is anything quantified over programs? Output: findings in `REVIEW.md`, each with a witness or a
counterexample term. Repairs go through sign-off.

### Phase A/G/I — the program IS the Lean codegen's output, for the real circuit

**WP-A1 Codegen-agreement KATs** (1). Turn the two probes into KATs in
`Instances/CodegenAgreement.lean`: token-offset pins (`mainAssemblyTokens` drops exactly
`assembly ( "memory - safe" )`; `abiGuardTokens` drops `{` plus those six), `abiGuard_agrees_ok`,
the per-region coverage table (expected values as measured), `constTableOf` = pinned table.
*Accept:* KATs green with the measured verdicts; a perturbation of `abiGuardBlock` (one literal)
reddens.

**WP-A2 Inliner lemmas** (1–2). Prove `inline_append` and `hoist_prog_addr_indep`; add
`mainClosed_poseidon_ok` (after WP-G1).

**WP-G1 Emit the missing regions as AST** (3–6). `GenAst` emitters for `AccumulatorHelpers.yul`
(823 tokens) and the quotient-numerator region of `QuotientAndLinearization` (6452 tokens:
`QuotientHelpers` + `QuotientNumeratorBlock`, i.e. the QVM interpreter and the model's compact
blocks; reuse `Lowering/GenAstQuotient.lean`). Extend `mainAsmRaw` accordingly.
*Accept:* coverage table all-equal except PCS; `codegenAgrees` false only because of PCS; a mutated
statement in each new region reddens.

**WP-I1 The poseidon Exec VK as a Lean term** (1–3). Generate `Instances/PoseidonVk.lean` from
`formal/fixtures/conformance/poseidon/vk.json` (script under `formal/scripts/`, generated file
committed, like the old IR import but for the VK). Validate it with the conformance replay
(`Conformance/Replay.lean`: challenges and evaluations of `trace.json` reproduced). Then compute
`ConstraintSystemMeta.new Features.solidity vk.cs 1` and compare with `DeployedProfile.poseidonMeta`.
*Accept:* replay agreement KAT; meta comparison KAT (a mismatch is a finding, not a fix-up).

**WP-G4 Port `LoweringPlan::new`** (3–6). `proofs/solidity-verifier/src/lowering/plan.rs:235-329`.
First inventory which callees exist (`generate_vk`, `meta_data_for_stable_static_layout`,
`quotient_program_plan`, `build_quotient_program_items`, `native_callback_scratch_words`,
`quotient_stack_words_for_build`, `quotient_state_words`, `kzg::memory_requirements`,
`memory_layout_for`, `quotient_operand_model`, `quotient_template_program` (QRS:189-238),
`certify_quotient_builds_agree`); port the missing ones under rules R1–R11. Then restate
`Valid.circuitMeta/layout/invariants` as lemmas of the constructor.
*Accept:* `LoweringPlan.new` on the WP-I1 VK equals `DeployedProfile`'s plan field by field (KAT), and
the PCS region becomes non-empty and agrees.

**WP-G3 Port QRS:2000 `compact_quotient_computation_blocks`** (2–4). Removes the artifact-derived
`poseidonBlocks`. *Accept:* equals `poseidonBlocks qctx` at the deployment (KAT); add the generator
fact `R.qblocks = compactBlocks R.plan` to `Render.Valid` (sign-off: frozen surface).

**WP-I2 The deployment instance** (1–2). In `Instances/PoseidonV2.lean`: `poseidonRender` over the
curve model (`G₁z`, `G2fold`, `blsGT`; `E.g1 := g1CodecZ`, `encG2 := ` the G2 fold codec used by
`HoldsFinal.holds_exhibited`); prove `poseidon_valid : poseidonRender.Valid` (by computation),
`entryFrame_inhabited` (generic), and `HypothesesInhabited poseidonRender poseidonProduct` (reuse
`holds_exhibited`). Depends on G1, I1, G4 (or an interim plan that passes `Valid`), G3 (or interim).
*Accept:* all three proved; `#print axioms` = standard + D-P36a.

### Phase M — the semantics

**WP-T Yul proof automation** (4–12, BEFORE M1; added after measurement). The only completed block
proof (`traceReturn_spec`) cost 412 Lean lines for a 23-token block, about 18 lines per Yul token.
The remaining blocks total about 13,200 tokens, so hand proofs at that density are infeasible. Build:
1. A symbolic-execution tactic (or a verified VC generator) for the vendored big-step semantics. It should discharge `Step` derivations for straight-line code, builtins and `if` on concrete conditions, apply loop rules with user invariants, and step `staticcall` through the `permissive`/honest relations.
2. A `simp` set connecting `mulmod`/`addmod` on `U256` to `ZMod p` under `< r` bounds.
3. Memory read-over-write lemmas at the layout's addresses.
4. For closed-dialect fragments, proof by evaluation through the sorry-free `YulSemantics.EVM.run_adequacy`.

Fuel must be consumed per nesting level, never per list element (P-INLINE: one per-element `rfl` cost 18 min and 8.7 GB).
*Accept:* re-prove `traceReturn_spec` on the closed slice in under 100 lines, and prove VkLoading's
straight-line prefix with the tactic. Record lines per token; it drives the §9 re-estimate.

**WP-M0 Contract design** (1–2, statements only). Make §6 precise against the real code:
1. Check each `Inv` clause and the `Frame`/`Clean`/`Poisoned` split against what each slice reads and writes.
2. Design **staged rejection**: invariants over `snapshotOfTrace … snapshotOfPcs`, with the fault class each block is responsible for, so that `Render.Rejects` decomposes per block. Exclude only the `logup.rs:460` panic (the `SoundSide` bad set).
3. State the prefix lemma: ABI guard + wrapper lets + MF-2 guard + helper definitions + `mainLocals`, from an `EntryFrame`, either reverts or reaches `Clean .start`.
4. Give one falsifier per contract (a mutated slice that breaks it).

Fresh-session review afterwards. *Accept:* every new statement has a satisfiability witness and a falsifier; no new hypothesis quantifies over programs.

**WP-M1 Prefix + VkLoading** (2–4). Generic in `R`. Reuse `Bridge` step lemmas and
`ShellModel`-style inversion; the VK gate uses `Frame.vkCode/vkHash/keccak` (this is what made v1's
`vkLoading_spec` "unprovable as stated").

**WP-M2 TranscriptParser** (5–10, largest). Squeezes must equal Lean's `Transcript` under the frame's
`H` (D-P10: hash-agnostic); canonical-scalar and EIP-2537 padding rejection; `x1..x4` and the x3
truncation (D-P14).

**WP-M3 Lagrange and QuotientLin** (4–8). Lagrange: `lIRange`, batch inversion (the contract is
stricter: `ChallengesGood`). QuotientLin: the QVM interpreter refines `vm/reference.rs`
(`Lowering/Qvm*.lean` lemmas), and the program computes the Lean numerator. This is the one block
proved **per deployment** until WP-G3.

**WP-M4 PCS, FinalPairing, TraceReturn** (3–6). Port the existing `traceReturn_spec` proof and
`finalPairing_spec` work to the closed slices. FinalPairing progress uses `Eip2537.Holds` and the
`DualMSM.check` premise; note the deferred `success` check (poisoned case).

**WP-M5 Composition** (2–4). Prove `lowering_equivalence_of_blocks` and `poseidonRender.Rejects` from
the staged contracts, `emitSlices_eq`, `inline_append`, `hoist_prog_addr_indep`, `NoWriters` +
`Bridge.Run_worldEq_of_noWriters` (currently `sorry` in Bridge — prove it), and the `Bridge` view lemmas.

**WP-H The claimed headline** (1).
`theorem lowering_equivalence_poseidon (product : PairingProduct) : LoweringEquivalence poseidonRender product`,
with no other hypotheses (stated in C.1, closed in H.1). *Accept:* §6. That means
`#cone_sorries` = 0, `#cone_avoids` ok, and the axioms are standard + D-P36a + the recorded
compiler-trust axiom(s).

### Phase E — end to end

**WP-E1** (2–4). Prove `end_to_end`.

- **Copy, don't move,** the proved `Lowering.verifyNative_iff_msgs_codec` into a V2 module, together
  with whatever it needs from `Obligations.lean` (measure it with `#cone_in`). `Obligations.lean` is
  v1 and gated; leave it untouched.
- Prove `calldata_roundtrip`, `calldata_canonical` and `repack_spec_of_decodeRust` (declarations at
  `Lowering/Calldata.lean:731, :790, :1276`, currently `sorry`), at least at
the deployed layout.

### Phase X — later, each a separate decision

- **X1 accumulator mode:** the contract batches with keccak-α; compare to `ContractRefAcceptsAcc`, one-directional w.r.t. Rust (R-10).
- **X2 externalised quotient evaluator:** needs world-locality of `Evaluator.rel`.
- **X3 embedded-VK render.**
- **X4 the ∀-render theorem:** after G3/G4 and generic block proofs.
- **X5 (optional) the Solidity wrapper as an in-tree Yul spec:** `ShellModel.dispatcher` with the *closed* program behind it, plus a decomposition lemma `wrap ↔ earlyRevert ∨ (prefix ; RunBody)`. A specification of Solidity, never compared to solc output.
- **X6 delete the retired solc track** (§2.3).
- **X7 security (S1–S7):** `Spec.accepts` is a `sorry` *definition* today, so `verifyMsgs_iff_spec` has no content until it is defined.

## 6. Definition of done (V2 headline)

> If `design.md` holds a signed D-P60, the definition of done is `PLAN-V3.md` §6 (the Lean term
> `Done`), not this section. Until then this section stands.

```bash
cd formal
bash scripts/verify.sh   # ram_guard + lake build + checks.sh (incl. kat_gate) + ConeReport
# ConeReport must print:
#   imports_avoid: ok (14 modules)
#   cone_avoids Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok (14 modules)
#   cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: 0
# and #print axioms on it must list only propext, Classical.choice, Quot.sound, the five D-P36a
# axioms (blsGT, blsGT_group, blsGT_primeOrder, blsGT_module, bls12_381Pairing) and the
# compiler-trust axiom(s) of native_decide recorded by Q0.3 (D-V2 clause 5) - no sorryAx.
```

- `lowering_equivalence_poseidon (product)` holds for every product, with no other hypotheses and an
  empty sorry cone.
- `poseidon_valid` includes `codegen` (AST = Lean codegen text), `circuitMeta` (plan derived from the
  verifier's own VK), `closed`, `noWriters`.
- `HypothesesInhabited` and `entryFrame_inhabited` are proved.
- The English statement in `docs/STATUS.md` names: the two side conditions (`SoundSide`, `CompleteSide`,
  negligible bad sets), the trusted `EntryFrame`, the D-P36a curve axioms, `Eip2537.Holds`, the
  first-headline scope (no accumulator, embedded quotient, separate VK, production), and that gas is
  not modelled.

## 7. Brief template — superseded by `EXECUTION-V2.md` §3

Use the one-page ticket brief in EXECUTION-V2 §3, one per ticket, never one per WP. Prefix every
brief with:

```
You are executing ticket <ID> of formal/docs/plans/EXECUTION-V2.md (part of WP-<id> of PLAN-V2.md).
PLAN-V2 §0–§4 and EXECUTION-V2 §5 (W1–W11) are binding. Repository: midfall/formal (Lean 4.35,
lake). Work on branch t/<ID>; do not commit to formal/baseline. The frozen files are sha256-pinned;
do not edit them or vendor/. Your output is ONE deliverable, ≤ 2.5 h; at 1 h, if less than a third is
done, commit WIP to t/<ID>, report PARTIAL and stop.
```

## 8. Reuse map

- **Keep and build on:**
  - `Halo2/Exec/*` and the conformance replay.
  - `Lowering/GenAst*.lean` (the core of the program) and `Lowering/InlineConstants.lean` (with its shadowing lemmas).
  - `Lowering/Inv.lean`, `Snapshot.lean`, `Checkpoint.lean`.
  - `Yul/Bridge.lean` and `Yul/Contracts.lean` (step and contract layers).
  - The `traceReturn_spec` proof technique, `Lowering/Calldata.lean`, `Lowering/Qvm*.lean`.
  - `verifyNative_iff_msgs_codec` and the `Exec/TranscriptLog` chain.
  - `Instances/DeployedProfile.lean`, `HoldsFinal`, `CurveSurface`, and the G1/G2 agreement files.
- **Retire:** §2.3.
- **Do not port forward:**
  - `Surface` as a statement carrier.
  - The pin-gate machinery whose only purpose was policing free fields (`check_duplicate_facts.py` families tied to Surface pins). Review each gate; keep the ones that test generator facts.

## 9. Effort: a prior, then calibration (not a forecast)

An external review of this plan cautioned that its earlier "on-path share" percentages and
token-to-proof-size extrapolations were **estimates presented with the precision of
measurements**. This section separates the two.

### 9.1 Facts (measured; each with its source)

| fact | value | source |
|---|---|---|
| package duration, plan commit → feat commit (includes orchestrator time) | median ≈ 2.3 h; 44 packages and 88 h in Nov 12–16 | `git log` timestamps |
| turnaround from feat commit to the next brief | 0–7 min, median 1 | `git log` |
| completed V2-shaped block proofs | one: `traceReturn_spec`, 412 Lean lines for 23 Yul tokens. `#cone_sorries` = 0 | the repo; the cone tool |
| Yul still to verify, by region | quotient numerator 6,384 tokens; PCS 3,623; AssemblyHelpers 1,303; TranscriptParser 923; Lagrange 501; VkLoading 223; FinalPairing + TraceReturn 45 | size probe |
| AST emission still missing | AccumulatorHelpers 823; QuotientHelpers 68; numerator 6,384 | coverage probe |
| the v1 ledger's own estimates | landmark 16–35 sessions, revised 6×; after about 40 more packages the landmark was vacuous | `docs/ETA.md` |

**Token counts are a size proxy, not a difficulty measure.** One proved block is a sample of one.
Neither supports an extrapolation to a schedule.

### 9.2 Prior (judgment, wide on purpose)

| work | prior, in tickets of ≤ 2.5 h |
|---|---|
| cut-over + Q0 | 4–6 |
| CORE to calibration point 1 (D.1–D.3, C.1–C.5, FP.0, P.1, T.1–T.5, M0.1) | 15–30 |
| everything after calibration point 1 | unknown until measured; the v1 plan's 50–200 range is not evidence |

The calendar depends on throughput in this setup. One orchestrator and one subagent ran about 10
packages/day when running continuously. So the first two rows are roughly **2–4 days of continuous
operation**. **No completion date is given before calibration point 1.**

### 9.3 Calibration points (the only basis for re-estimating)

At each point the orchestrator records, from ETA rows:

- tickets and hours since the previous point;
- cone nodes closed;
- block contracts integrated (proved **and** used by the composition);
- Yul statements covered by those contracts.

It then re-estimates the remaining cone by analogy to the measured tickets, **stating the sample
size**. No percentages are derived from classifications.

1. **C.5:** FinalPairing ; TraceReturn composed, with the automation (T.2–T.5) in use. The first
   real measure of contracts per ticket with tactics.
2. **End of TranscriptParser (B2):** the first loop-heavy, hash-heavy block.
3. **After the QVM interpreter refinement (B4):** the largest single risk.

### 9.4 Risks (qualitative; each can move the schedule by weeks)

- **Automation.** If WP-T does not make block proofs substantially cheaper than hand proofs, the work
  after calibration point 1 grows accordingly. Point 1 measures this directly.
- **QVM.** The interpreter refinement and per-program correctness (6.4k tokens of numerator).
- **PCS ↔ `multi_prepare`.** Point-set order, truncated `x1`/`x4` powers (R-22), MSM collapse.
- **Generator ports of unknown size.** The P-11 callee inventory and QRS:2000 (G.5, G.6 measure them).
- **Real mismatches.** A contract/Lean mismatch found by a proof needs a human decision.
- **Kernel and elaboration performance on generated code** (W9's 60 s rule bounds the waste).
- **Fixture coherence.** D.3 exists to surface this on day one, not week three.
