# QUEUE — the only live queue

**How to use it.** The orchestrator takes the **first READY card from the top**. A card is READY
when its `after` tickets are merged.

- **Cards are prescriptive.** If a card is wrong, the subagent stops and reports. It does not work
  around the card.
- **Layers.** INFRA = landing and tooling. GEN = facts about the generator or deployment, by
  computation. ALG = Lean mathematics on the verifier side, with no Yul. SEM = Yul semantics of the
  program. A ticket never investigates another layer's machinery.
- **Verification.** The subagent runs `verify.sh --quick` (once Q0.3 has landed). The orchestrator
  runs the full `verify.sh` **once**, before merging.
- **Facts.** "Measured" facts below were measured at `15c0b3a` (2026-11-16). The orchestrator
  re-checks them at the current commit before briefing (EXECUTION-V2 §2.3).

## CUT-OVER — the orchestrator does these itself (EXECUTION-V2 §1)

| ID | deliverable | after |
|---|---|---|
| T0.1 | Drain P-RUNLEG: merge it if green and complete, otherwise commit it to `v1/p-runleg-wip`. Start no new v1 package | — |
| T0.2 | Tag `formal/v1-final`. Run `checks.sh` once and write the measured register and KAT totals into `STATUS.md` | T0.1 |
| T0.3 | Record D-V2 (PLAN-V2 §2, pre-approved) verbatim as the next free D-P (expected D-P43); point `PLAN.md`'s header to PLAN-V2. Docs only | T0.2 |
| T0.4 | `git fetch origin v2/bundle && git checkout origin/v2/bundle -- v2-bundle/`; copy `v2-bundle/docs/{QUEUE,STATUS}.md` to `formal/docs/` and `{PLAN-V2,EXECUTION-V2}.md` to `formal/docs/plans/`; commit | T0.3 |

---

## Q0 — land V2 cleanly

### Q0.1 — Land the V2 files unchanged  **[MERGED b8ca493]**
INFRA · KAT · box 1.5 h · Sonnet · after T0.4

- **Goal.** The three provided files build inside the tree, unchanged.
- **Needs.**
  - `v2-bundle/lean/Midfall/LoweringV2/{Program,Statements}.lean`
  - `v2-bundle/lean/Midfall/Lowering/LegacyVacuity.lean`
  - `formal/Midfall.lean` (root imports)
  - `scripts/gen_sorry.sh`
- **Does NOT need.** Any v1 edit, any proof, any new gate.
- **Do.**
  1. Copy the files to `formal/Midfall/…`.
  2. Add three lines to `Midfall.lean`: `import Midfall.LoweringV2.Program`,
     `import Midfall.LoweringV2.Statements`, `import Midfall.Lowering.LegacyVacuity`.
  3. Run `scripts/gen_sorry.sh`.
  4. Run `lake build` once, under `ram_guard`.
- **Deliverable.** The three files, the imports, and `SORRY.md` with exactly 6 new rows: `inline_append`,
  `hoist_prog_addr_indep`, `blockContracts_of_valid`, `lowering_equivalence_of_blocks`,
  `entryFrame_inhabited`, `end_to_end`.
- **Accept.** Build green; the orchestrator's single `checks.sh` run is green;
  `#print axioms Midfall.Lowering.LegacyVacuity.not_LoweringCorrect` = `[propext, Classical.choice, Quot.sound]`.
- **Stop if.** A provided file fails to compile: report its first error and do not change its
  statements.
- **For the orchestrator.** If `checks.sh` reddens *only* because a v1 gate scans the new files (the
  likeliest is `check_duplicate_facts.py` discovering `Render`'s fields), merge Q0.1 and issue card
  **Q0.1b**: narrow that gate's scan to its v1 paths (one line, no V2 entries).

### Q0.1b — Give gen_sorry.sh an owner case for Midfall/LoweringV2/*  **[MERGED b035cf1]**

INFRA · KAT · box 0.25 h · Sonnet · after Q0.1

- **Goal.** The six V2 rows in SORRY.md name an owning work package instead of UNOWNED.
- **Needs.** scripts/gen_sorry.sh owner(); the six rows at LoweringV2/Program.lean:201 and
  Statements.lean:371/377/388/417/450.
- **Does NOT need.** Any .lean edit; any proof; any new gate.
- **Do.** Add the case; regenerate SORRY.md; confirm the row count stays 45.
- **Deliverable.** owner() handles Midfall/LoweringV2/*; 6 rows updated.
- **Accept.** bash scripts/sorries.sh | wc -l = 45; no LoweringV2 row says UNOWNED.
- **Stop if.** The register count moves off 45.

---
### Q0.2 — Cut V2 off the retired modules; land the cone tool  **[MERGED 3235d17]**
INFRA · PORT · box 2 h · Sonnet · after Q0.1

- **Goal.** Nothing V2 imports, directly or transitively, is retired or parked, and the cone report
  runs.
- **Needs (measured).**
  - **The only retired chain V2 reaches.** `Program.lean → Lowering.FrameWalk → RunEmitted → Partials
    → Surface → Accumulator → AccEncoding`, plus `Statements.lean`'s direct imports of `Surface`,
    `Partials` and `Accumulator`. Without those imports the closure has no retired module.
  - **What V2 uses from them** (measured by `#cone_in`; none needs anything else from its module):
    - `Surface`: `ZeroAbove` (:757), `initState` (:728), `ptReadable` (:512);
    - `Partials`: `Reverted` (:99), `revertedOf`;
    - `Accumulator`: `frOfWord?`, `instOfWords?` (:1407);
    - `FrameWalk`: `freeNames` (:586) with `boundE`, `boundS`, `boundSC`, `boundSs`, `refE`, `refSs`.
  - **The tool.** `v2-bundle/lean/Midfall/Tools/ConeSorries.lean`, tested on v4.35.0:
    `#cone_sorries`, `#cone_in`, `#cone_avoids`, `#imports_avoid`; 8 `#guard_msgs` tests.
- **Does NOT need.** Editing or moving anything in v1 files: **copy** instead, because v1 gates read
  those files. No proof.
- **Do.**
  1. Create `Midfall/LoweringV2/Shared.lean` (namespace `Midfall.LoweringV2`) with verbatim copies
     of the definitions above.
  2. In `Program.lean`, drop `import Midfall.Lowering.FrameWalk` and use the copies.
  3. In `Statements.lean`, drop the imports of `Surface`, `Partials` and `Accumulator`, and use the
     copies.
  4. Land `Midfall/Tools/ConeSorries.lean`. Create `Midfall/Tools/ConeReport.lean`, which imports
     only V2 modules and the tool, containing:
     - `#imports_avoid [AVOID]`;
     - `#cone_avoids R [AVOID]` and `#cone_sorries R` for R = `Midfall.LoweringV2.lowering_equivalence_of_blocks`
       and `Midfall.LoweringV2.end_to_end`.

     Add `import Midfall.Tools.ConeReport` to `Midfall.lean`; the orphan gate requires every file
     under `Midfall/` to be reachable.
  5. From `formal/`, run `lake env lean ../v2-bundle/tools/ConeSorriesTest.lean` once. It lives
     outside `Midfall/` because it contains deliberate sorries.
- **AVOID (14 modules).**
  - `Midfall.Lowering.{Surface, Partials, Obligations, Accumulator, AccEncoding, RunEmitted, FrameWalk}`
  - `Midfall.Yul.{ShellModel, ImportSolcIR, IRCheck}`
  - `Midfall.Instances.{ImportedIR, IrCheckBlindness, RunShellInversion, RunShellInhabited}`
- **Deliverable.** `Shared.lean`, the two edited V2 files, `ConeSorries.lean`, `ConeReport.lean`.
- **Accept.** Build green. `ConeReport` prints `imports_avoid: ok (14 modules)`, then
  `cone_avoids …: ok` twice, then two `cone_sorries` counts. The self-test exits 0.
- **Stop if.** A copied definition needs something not listed. Report the error; do not chase it
  into v1 files.

### Q0.3 — Freeze the surface; one verify command  **[MERGED 96910d3]**
INFRA · KAT · box 1.5 h · Sonnet · after Q0.2

- **Goal.** The frozen V2 surface cannot change silently, and one command verifies a ticket.
- **Needs.** `checks.sh` line 26 (`sha256sum -c Midfall/Statements.sha256`, measured).
- **Does NOT need.** New gates, registries, or edits to other gates.
- **Do.**
  1. **Split.**
     - Frozen: `Program.lean` §1–§4; `Shared.lean`; `Statements.lean` §1–§5; `HypothesesInhabited`;
       `calldataOf`; and `def EndToEnd`, `def EntryFrameInhabited` (the two theorem statements as
       Props).
     - Refinable: `ProgramLemmas.lean` (`topBinders`, `inline_append`, `emitSlices_eq`) and
       `Blocks.lean` (§6; §7; `entryFrame_inhabited : EntryFrameInhabited …`;
       `end_to_end : EndToEnd …`).
  2. Hash the frozen files into `Midfall/LoweringV2/Frozen.sha256`, and add one `sha256sum -c` line
     next to line 26.
  3. Write `scripts/verify.sh`. `--quick` runs build plus `ConeReport` (≤ 10 lines). The default runs
     `ram_guard` + build + `checks.sh` + `ConeReport`. Exit non-zero on any failure.
  4. In a scratch file, run `#print axioms` on a one-line `native_decide` example and put the axiom
     names in the report.
  5. Make `ConeReport` import `Midfall.LoweringV2.Blocks`. The root names are unchanged; their
     theorems now live there.
- **Deliverable.** The split files, `Frozen.sha256`, the `checks.sh` line, `verify.sh`.
- **Accept.**
  - `verify.sh --quick` is green and prints the cone lines.
  - The pin works, shown on a copy so the tree is not touched. Copy the frozen files plus
    `Frozen.sha256` into a temp dir with the same relative paths, append one character to one copy,
    and run `sha256sum -c` there: it fails. The commands go in the report.
  - The orchestrator's single full `verify.sh` run is green.
- **Stop if.** The split would change the text of any frozen statement.

### Q0.4 — Adversarial review of the frozen surface  **[DONE (read-only probe) - HIT: R-72, recorded in 3034c6a; the `70f8111` cited here before is not a commit in this repo]**
INFRA · PROBE · box 1 h · fresh subagent, read-only · after Q0.3

- **Goal.** For each frozen statement, give a sketch of a joint witness for all its hypotheses, or a
  counterexample.
- **Does NOT need.** Proofs or edits.
- **Deliverable.** The report. Add REVIEW.md entries only for real defects. Any repair is a DECISION
  for the human.

---

### Q0.4b — Land the probe's generic inhabitation proofs  **[MERGED 3034c6a - cone did NOT move]**

INFRA · PROOF · box 0.75 h · Sonnet · after Q0.4

- **Goal.** The probe proved `entryFrame_inhabited` generically in scratch; land it and close the sorry.
- **Needs.** `/tmp/q04/probe1.lean` — `entryFrame_witness` (:45), `probeW`/`probeW0` (:60,:67),
  `probeW_wf` (:72), `probeW_vkCode` (:75), `deployment_witness` (:81). Target: `Blocks.lean:185`
  (`entryFrame_inhabited`) and `Blocks.lean:148` if `blockContracts_of_valid` can reuse them.
- **Does NOT need.** R-72 repair (frozen file, human decision); any edit to `Statements.lean`.
- **Do.** Move the proofs into `Blocks.lean` (REFINABLE), discharge the `entryFrame_inhabited` sorry,
  regenerate `SORRY.md`, run `verify.sh --quick`.
- **Deliverable.** `entryFrame_inhabited` proved; register 45 → 44.
- **Accept.** `verify.sh --quick` green; `#print axioms` of `entryFrame_inhabited` clean; report the
  cone counts before and after — **if `cone_sorries end_to_end` does not move, say so**: progress is
  the root's cone, not the register.
- **Stop if.** The probe proof does not transplant unchanged.

### Q0.5 — Repair the non-vacuity gate (R-72)  [BLOCKED: human sign-off of D-P45, which is PROPOSED — draft in `docs/DECISIONS-PENDING.md` §3]

INFRA · PORT · box 1 h · after human sign-off of D-P45

- **Goal.** Make `HypothesesInhabited` gate the vacuity it exists to gate.
- **Needs.** D-P45 signed off, with the exact conjunct text it approves.
- **Verify first.** R-72's reproducer is **not in the tree**: it lived in `/tmp/q04/probe1.lean`,
  which is gone, and survives only as prose (REVIEW.md:2991-3005: `sel_nondecode`, `gate_weak`,
  `no_accept_at_gate_cd`).
- **Do.** 1. Re-create the three reproducer theorems from REVIEW.md:2991-3005 and confirm `gate_weak`
  type-checks against the CURRENT gate (the falsifier must fail before the fix). 2. Apply the
  signed-off text to `Statements.lean` §8 and re-hash `Frozen.sha256` in the same commit. 3. Update
  PLAN-V2:355 wording if the gate's meaning changes.
- **Not this card, whatever is decided.** Adding `hR : R.Valid` to `LoweringEquivalence` (R-72's
  second question; `docs/DECISIONS-PENDING.md` §2 recommends rejecting it: with
  `poseidonRender_notValid` proved it would make the headline provable by contradiction, and PLAN-V2
  §6 requires the headline "with no other hypotheses"). Also not this card: discharging the new gate
  at the deployment. REVIEW.md:3019 records "no accepted calldata at any model in the tree" and the
  deployment's G1 decoder is `Classical.choose` (G1Agreement.lean:1995), so that witness must be
  proved, not evaluated, by a later card.
- **Accept.** `gate_weak` type-checks before step 2 and NO LONGER type-checks after it (commands and
  output in the report), and the new gate needs a real accepting calldata. **The repair must be
  demonstrated to have teeth, not just to compile.**
- **Stop if.** Any change would alter a statement other than the gate.

---
## CORE — consumer first, to calibration point 1

### D.1 — The deployment's generator inputs as pure terms  **[MERGED d18424b - cone did NOT move]**
GEN · PORT · box 2.5 h (split at 1 h into VK/plan · qblocks/model) · Sonnet · after Q0.3

- **Goal.** Every generator-side input of `poseidonRender` is a pure term (no IO) derived from one
  fixture set.
- **Needs (measured, `Instances/DeployedProfile.lean`).**
  - Pure: `poseidonInputs` (:122), `poseidonFlags` (:132), `poseidonPlan (vk : Halo2VerifyingKey)
    (mem)` (:177), `poseidonDerivedMemory` (:192), `poseidonBlocks (qctx : PartialCtx)` (:197).
  - IO-only, to be replaced: `poseidonDerived` (:207), `poseidonDerivedCtx` (:219).
  - Pure parsers in `Conformance/Bundle.lean`: `parseVk`, `parseTrace`, `parseInstances`
    (`JValue → Except String _`).
- **Verify first.**
  - (a) `include_str` elaborates in this toolchain. If not, write a script under `formal/scripts/`
    that emits the Lean file.
  - (b) Find the path `poseidonDerived` reads.
  - (c) `poseidonPlan`'s result type fits `Render.plan : LoweringPlan Unit Unit`.
- **Does NOT need.** Yul semantics, the curve model, or ports of `LoweringPlan::new`/QRS:2000. Those
  later replace these terms (G.5, G.6).
- **Do.** Write `Instances/PoseidonInputs.lean` with:
  - `poseidonVkGen : Halo2VerifyingKey`;
  - `poseidonPlanV2`;
  - `poseidonCtx : PartialCtx`;
  - `poseidonQBlocks := poseidonBlocks poseidonCtx`;
  - `poseidonModel`, the `.ok` value of
    `generateVerifierFromPlan (fun _ _ => poseidonQBlocks) poseidonInputs poseidonFlags poseidonPlanV2`.
- **Accept.**
  - KATs: each pure term equals its IO-derived counterpart (`#eval` against `poseidonDerived` and
    `poseidonDerivedCtx`).
  - `generateVerifierFromPlan …` returns `.ok`.
- **Stop if.** After (a)–(c), a term is still only obtainable through IO.

### D.2 — The Lean verifier's side of the deployment  **[MERGED 8e43ac8 - cone did NOT move; exposes the ofCompressed blocker]**
ALG · PORT · box 2.5 h · strongest · after Q0.3

- **Goal.** Pure terms `poseidonE`, `poseidonParams`, `poseidonVkExec : VerifyingKey (Fr p) G₁`,
  `poseidonSG2` and `poseidonEncG2`, from `vk.json` and `params.json`, in the curve model that
  `HoldsFinal.holds_exhibited` uses.
- **Needs.**
  - `HoldsFinal.holds_exhibited`: its group instances, `E.g1 := g1CodecZ`, and `encG2`.
  - `vk.json` keys (measured): `k`, `n`, `omega_be_hex`, `fixed_commitments_compressed_hex`,
    `permutation_commitments_compressed_hex`, column counts, queries.
  - `params.json`.
- **Verify first.** Is decoding a compressed point into the model computable? Test with `#eval` on one
  commitment. If not, the terms are still definable through the codec, and the KATs drop point
  fields.
- **Does NOT need.** Yul, the generator, or a pairing implementation (the headline quantifies over
  `product`).
- **Deliverable.** `Instances/PoseidonEnv.lean`.
- **Accept.**
  - KATs: `k`, `n`, `omega`, column counts and query lists equal `vk.json`.
  - If points are computable: the first fixed commitment re-encodes to its hex.
- **Stop if.** The VK type needs data that `vk.json` does not contain. Report the field.

### D.3 — Coherent success path, before any proof uses the deployment  **[MERGED db4b2e6 - NEGATIVE: checks 1,2 false, check 3 blocked; C.1 BLOCKED]**
GEN · KAT · box 2 h · Sonnet · after D.1, D.2

- **Goal.** Show by computation that the fixture proof goes through the Lean side at the render's own
  layout, and that a corrupted proof fails at the right place.
- **Needs.**
  - D.1 and D.2 terms.
  - `proof.bin`, `instances.json`, `trace.json` (keys measured: `transcript_log`, `dual_msm`,
    `pairing_check`, `verdict`, `proof_len`).
  - `Conformance/Replay.lean`.
- **Does NOT need.** Yul semantics or the pairing. The verdict in `trace.json` is the Rust side's.
- **Checks.** Each is a KAT in `Instances/PoseidonCoherence.lean`.
  1. **Layout.** The `Valid.layout` computation on `poseidonPlanV2.meta_` gives
     `poseidonPlanV2.proofLayout`, and its proof length equals `proof_len`.
  2. **Meta.** `ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 = .ok
     poseidonPlanV2.meta_`. `DeployedProfile`'s meta is typed in, so a mismatch is a finding.
  3. **Decode.** `decodeCalldata` at that layout accepts the fixture calldata. Build the calldata from
     `proof.bin` + `instances.json` with `repackProof` then `encodeCalldata` at
     `poseidonPlanV2.proofLayout`, using `poseidonE.g1`. This is the body of `calldataOf`
     (`Statements` §9); the render itself does not exist yet.
  4. **Transcript.** The replay's challenges equal `transcript_log`.
  5. **Negative control.** Flipping one byte of `proof.bin` changes check 4 from the first challenge
     after that byte onward, and not before.
- **Accept.** Checks 1–4 are true and check 5 behaves as stated.
- **Stop if.** Any of checks 1–4 is false. Report NEGATIVE with the first differing value. Do not edit
  the fixtures or the typed-in profile.

### C.1 — State the headline at the deployment; fix the cone  **[MERGED 1009658 - headline stated, cone=5]**
SEM · SKELETON · box 2 h · strongest · after D.3

- **Goal.** `lowering_equivalence_poseidon` exists, is proved from named sorried lemmas, and becomes
  the cone root.
- **Needs.** All in namespace `Midfall.LoweringV2`, in `Blocks.lean` after Q0.3:
  - `lowering_equivalence_of_blocks (R) (product) (hR : R.Valid)
    (hB : R.BlockContractsAt product (fun _ => True)) (hrej : R.Rejects product)`.
  - `blockContracts_of_valid … : R.BlockContractsAt product (· ≠ .quotientLin)`.
  - `LoweringEquivalence R product` takes `Eip2537.Holds … product` as a hypothesis (`Statements` §5).
- **Does NOT need.** Any block proof, Yul tactics, or a concrete pairing product.
- **Do.** In `Instances/PoseidonV2.lean`:
  1. Build `poseidonRender` from the D.1 and D.2 terms.
  2. State `theorem lowering_equivalence_poseidon (product : PairingProduct) :
     LoweringEquivalence poseidonRender product`. **Every** product, not a fixed one.
  3. Prove it from three named, sorried lemmas:
     - `poseidon_valid`;
     - `poseidon_quotient_block`, the one block not covered generically;
     - `poseidon_rejects`.
  4. Point `ConeReport` at the new root.
- **Accept.** Build green. The report lists `#cone_sorries lowering_equivalence_poseidon`.
  `#cone_avoids` is still ok.
- **Stop if.** `poseidonRender` cannot be formed from the D.1/D.2 terms. Report the missing field.

### M0.1 — Measure the blocks' frames  **[DONE 252ea1d - table landed below]**
SEM · PROBE · box 1 h · Sonnet · after C.1

- **Goal.** Produce one table row per `Partial` with these columns:
  - locals read and written;
  - memory ranges written;
  - whether it can set `success := 0`;
  - whether it calls a helper with a loop.
- **Do.** Run `#eval` over `poseidonRender.slice q`, using the copied walkers (`freeNames`, …).
- **Does NOT need.** Proofs.
- **Deliverable.** The table, in the report, with the commands that produced it.


**M0.1 RESULT — the table (re-run and reproduced by the orchestrator at 252ea1d; full verbatim
output preserved at `/tmp/m01/OUTPUT.txt`). Route: `sliceOf (planViewOf poseidonPlanV2
poseidonModelVal poseidonConfig.accumulator) poseidonModelVal q` — `planViewOf` takes THREE explicit
args `(L) (m) (acc)`; `acc = poseidonConfig.accumulator = none`, pinned by the frozen
`Statements.lean:93` `Render.pv` definition. `poseidonRender` was NOT made computable.**

| Partial | C1 locals read / written | C2 memory written | C3 sets `success:=0` | C4 helper with a loop |
|---|---|---|---|---|
| vkLoading | W: success · R: vk, success | 0x2900..0x3ae0 (4576B) {vk_payload}; +0x0..0x20 via fail | **YES** — 9 assigns, all `and(success, eq(…))` | NO (calls `fail` only); 0 own loops |
| transcriptParser | W: 16 locals · R: 17 · ext-in: r | 4 static ranges + 11 dynamic sites (buf_len walks, calldatacopy of advice/lookup/perm/trashcan/quotient walks) | **YES** — `and(success, lt(inst_be, r))` | NO; 9 own for-loops |
| lagrange | W: 21 locals · R: 22 · ext-in: r | static 0x3e20..0x3ee0, 0x6900..0x6920; dynamic `mstore(mptr)` loop 0x67c0..0x6900 step 32 | **YES** — `success := batch_invert(…)` | **YES — via `batch_invert`, the ONLY looping helper (direct and transitive)**; 5 own loops |
| quotientLin | W: 7 locals · R: 8 · ext-in: r | static 0x3f00..0x3f40 (64B) = QUOTIENT_MPTR payload; no dynamic | **NO** — 0 success assigns | NO (calls nothing); 1 own loop |
| pcs | **EMPTY — 0 stmts, 0 names** | none | NO | NO |
| finalPairing | W: success · R: success | none in slice; via `ec_pairing` 0x1240..0x1540 (768B) + fail 0x0..0x20 | **YES** — `success := ec_pairing(…)` | NO (`ec_pairing` has no for); 0 own loops |
| traceReturn | W: none · R: success · ext-in: success | static 0x1000..0x1020 (`mstore(4096,1)` then `return(4096,32)`) | **NO** — reverts via fail or returns abiTrue | NO; 0 own loops |

**Five things C.2 must know that the table cannot express:**
1. **Cross-slice shared locals are exactly `{vk, r, success}`** — the union of read-and-not-written-here
   over all 7 slices. `r`/`success` are declared by `mainLocals` (Program.lean:88-90) OUTSIDE every
   slice; `vk` by `wrapperLocals`. `quotientEvaluator` never appears (`mA.quotientExternal = none`).
2. **`fail()` does NOT set `success := 0`** — it mstores the selector at 0x0 and `revert(0,4)`. 5 of 7
   slices call it (all but quotientLin and pcs). **Revert path and success path are distinct
   requirements.**
3. **Route validated:** sum of slice stmt counts = 54 = `(GenAst.emitSlices pvA).length`; slice token
   count = text-region count + 2 (block braces) for 5 of 7. Only quotientLin and pcs break the pattern.
4. **quotientLin emits only 122 of 6572 tokens** — 98% of the quotient region is not emitted (WP-G1:
   the two quotient_numerator includes + accumulator/trace helper includes). **This is exactly the
   block C.1 sorried separately as `poseidon_quotient_block`.**
5. **pcs is empty at the plan/model level, not an emitter omission** — `computationsAst = ok, 0
   blocks`, `mA.pcsComputations.length = 0`, and the rendered text region is also empty (2/2).
   **C.2 must not read the pcs row as "pcs needs nothing"** — every cell is vacuous.

### C.2 — Composition skeleton with a requirements table  **[MERGED 9401f1a - cone 5 to 11; Rejects decision needed]**
SEM · SKELETON · box 2 h · strongest · after M0.1

- **Goal.** Prove `lowering_equivalence_of_blocks` modulo named lemmas.
- **Needs.**
  - The M0.1 table.
  - `Statements`/`Blocks` §6: `Frame`, `Clean`, `Poisoned`, `exitOk`, `BlockSound`,
    `BlockProgress`, `BlockContractsAt`, `Rejects`.
  - `emitSlices_eq` (proved).
  - `inline_append` and `hoist_prog_addr_indep` (sorried).
  - `Bridge.Run_worldEq_of_noWriters` (a registered sorry, reused).
- **Verify first.** The Bridge view-lemma names, e.g. `halted_of_view_eq` and `worldEq_of_view_eq`.
- **Does NOT need.** Any block contract proof, or the deployment.
- **Deliverable.**
  - The proof in `Blocks.lean`, with named sorried lemmas: the prefix lemma, per-block sequencing,
    and rejection composition.
  - **A requirements table in the report.** One row per named lemma: its statement, the composition
    step that uses it, and the size estimate with its evidence.
- **Accept.** Build green. Every new name appears in the cone report (the count may rise) and in the
  table.
- **Stop if.** Composition needs a block fact not expressible with the §6 shapes. Report the exact
  goal state. Refining §6 is allowed only by adding fields to `Frame`/`Clean`, and each change is
  listed.

**C.2 RESULT — composition landed on t/C.2: the requirements table.**

`lowering_equivalence_of_blocks` is now a THEOREM with no `sorry`: 113 proof lines that wire the §6
contracts to the frozen `LoweringEquivalence`. Everything semantic sits in 7 named sorried lemmas in
`Blocks.lean` §7.1 plus 11 proved transport facts. CONE: `lowering_equivalence_of_blocks` 1 → 7;
headline `lowering_equivalence_poseidon` **5 → 11** (it moved; see the note at the end).

| Lemma (Blocks.lean unless noted) | What it must deliver | Composition step that uses it | Size estimate, with evidence |
|---|---|---|---|
| `prog_slices_decomp` :220 (SORRY) | `R.prog a b = preSlice ++ helpers ++ mainLocals ++ slices` AND `hoist (prog a b) = hoist helpers` — the second conjunct IS the `hoist_prog_eq_helpers` that Statements.lean:108 advertises and that does not exist in the tree | Structural premise of `runBody_iff_slices` and `prefix_run_clean`. NOT cited by the composition itself, so it is **not in the cone report** | `20-40 lines, LOW CONFIDENCE`. Evidence: `emitSlices_eq` is 2 proof lines (n=1); the 4 proved `Inline` lemmas are 1-11 lines each (n=4) but none is about `++`. The real cost is `inline_append`'s (sorried, ProgramLemmas.lean:27): **no basis yet** (n=0 proved lemmas in the tree about `inlineContractConstants` distributing over concatenation). |
| `prefix_run_clean` :246 (SORRY) | From `EntryFrame` + `DeploymentV2` + `LeanAccepts`: the calldata decodes, `snapshotOf = .ok Snap`, `DualMSM.check = true`, and the prefix run exists and ends `Clean R .start` | STEP 1, in all three conjuncts — the only route from `LeanAccepts` to `hB`'s hypothesis set | **No basis yet.** Bundles three kinds of work: (a) `snapshotOf_prepareMsgs` (registered sorry, Snapshot.lean:387) for the `Snap` witness and the `DualMSM` clause; (b) discharging `Inv .start` + `Frame` (`LocalsOk`, the g1-identity window from `zeroAbove`, `let vk`, `let r := FR_MODULUS`); (c) a `Step` construction of the prefix run. Closest proved sample: `entryFrame_inhabited` at 9 proof lines (n=1) — but it builds a state, not a run. |
| `runBody_iff_slices` :276 (SORRY) | `RunBody R vkAddr 0 c g st₀ obs ↔ ∃ V' st' o, obs = ⟨committedState st₀ st', o⟩ ∧ ExecStmts (R.scope c g) V₁ st₁ R.slices V' st' o`, given the prefix run `hp` to the SAME `V₁ st₁` | STEP 1: forward direction spends a per-slice contract on a `RunBody` hypothesis (conjuncts 1, 3); backward direction turns `StmtsContract`'s witness into the headline's existence claim (conjunct 2) | `30-60 lines`. Evidence: `Step.stmts_append_inv` 10 proof lines and `StmtsContractAll.append` 9 (n=2 proved reassociation lemmas); the rest is `Step.block` / `Step.funDef` bookkeeping (BigStep.lean:222-227). No semantic content. |
| `slices_seq_sound` :307 (SORRY) | 7 × `BlockSound` → one `StmtsContractAll` over `R.slices`: pre `Clean R .start`, post `(o = .halt ∧ Reverted) ∨ exitOk .traceReturn` | STEP 2 in conjuncts 1 and 3 | `60-100 lines`. Evidence: `StmtsContractAll.append` is 9 proof lines (n=1) applied 6 times, each with a `mid` predicate `Clean R k ∨ Poisoned` and a 3-way split of `BlockSound`'s post (`3-4` lines each) → 6 × `13 ≈ 78. **The table's most important cell:** the post stated here has NO `o = .normal ∧ Poisoned` arm, and 7 copies of `BlockSound` do NOT give that — `BlockSound R .traceReturn` permits a poisoned fall-through on paper. The missing fact ("`traceReturn` reverts on `iszero(success)`") is a per-block requirement for FP.0/T.1 and its size is **no basis yet**. |
| `slices_seq_progress` :325 (SORRY) | 7 × `BlockProgress` → `StmtsTotal` over `R.slices` (a run exists + every run exits `exitOk .traceReturn`) | STEP 2 in conjunct 2 (both the `∃ obs` and the `∀ obs` halves) | `90-130 lines`. Evidence: the same 6 handoffs twice (`StmtsContract` and `StmtsContractAll`), n=1 sample of the combinator, plus `ExecLoopAll.countdown_or_halt` at 50 proof lines (n=1) as the only proved multi-constructor inversion in the tree — the relevant one for the `lagrange`/`batch_invert` link, which per M0.1 is the ONLY looping helper. |
| `noWriters_prog` :340 (SORRY) | `NoWriters (R.prog vkAddr qAddr)` from `hR.noWriters : NoWriters (R.prog 0 0)` | TRANSPORT: the `hn` argument of `Bridge.Run_worldEq_of_noWriters`, via `worldEq_of_runBody` | **No basis yet.** Evidence: the two proved `NoWriters` exhibits in Bridge are `⟨30, by decide⟩`-style on ≤3-statement blocks (n=2); the program is 54 statements / 6572 tokens (M0.1), so `decide` scaling is untested and may not fit the ≤60 s budget. The honest shape is a substitution lemma on `noWritersScan` about `lit` values, cost unknown. |
| `rejects_of_not_accepts` :356 (SORRY) | `Render.Rejects` WITHOUT `SoundSide`: `¬ LeanAccepts` → every permissive run reverts | STEP 3 in conjunct 3 ONLY (conjunct 1 uses `hrej` directly, where `SoundSide` IS available) | **Not estimable here, by construction.** It is `Rejects` with one hypothesis deleted, so its cost IS the cost of WP-M0's staged rejection contracts (card C.3), not a new obligation of this card. See premise finding 2. |

**PROVED IN THIS CARD (0 sorries; 11 names, all cited by the composition):** `worldEq_symm`,
`exists_revert_of_Reverted`, `halted_committedState`, `worldEq_committedState`,
`worldEq_of_runBody`, `not_isRevertOrHalt_of_isReturn`, `isRevertOrHalt_of_Reverted`,
`obs_view_eq_returnView`, `view_eq_returnView_of_committed`, `exitOk_traceReturn_apply`,
`returnData_of_committed_ret`. 59 proof lines total (n=11, median 4 lines).

**REUSED, NOT NEW:** `emitSlices_eq` (proved, 2 lines) · `inline_append` (sorried,
ProgramLemmas.lean:27) · `hoist_prog_addr_indep` (sorried, Blocks.lean:145 — cited by nothing in
this composition, so NOT in the cone) · `Bridge.Run_worldEq_of_noWriters` (registered sorry,
Bridge.lean:1221 — **now IN the headline cone**; it was not before) ·
`Bridge.view_eq_of_worldEq_and_halt` (proved, 3 lines) · `StmtsContractAll.append` (proved) ·
`Snapshot.snapshotOf_prepareMsgs` (registered sorry, folded into `prefix_run_clean`).
The brief also listed `halted_of_view_eq` and `worldEq_of_view_eq` as needed: the composition does
NOT cite them. It needs the CONVERSE transport (world + halt → view), which is
`view_eq_of_worldEq_and_halt`. Both are proved, so nothing is blocked — the brief named the wrong
direction.

**TWO PREMISE FINDINGS (both were NEEDS items on this card).**
1. `Bridge.Run_worldEq_of_noWriters` **DOES EXIST**: `Midfall/Yul/Bridge.lean:1221`, a real `theorem`
   with a `sorry` at :1223, registered in SORRY.md as `Midfall/Yul/Bridge.lean | 1223`. The
   orchestrator's grep missed it because the declaration is `Run_worldEq_of_noWriters` (no `Bridge.`
   prefix on the declaration; the prefix appears only in prose). NOT a premise gap. It is cited, via
   `worldEq_of_runBody`, exactly as the brief asked.
2. `Render.Rejects` is NOT sufficient for the composition, and this IS a gap: `Rejects` demands
   `SoundSide R H cd`, but the third conjunct of the frozen `LoweringEquivalence`
   (Statements.lean:250-262) carries no `SoundSide`. Conjunct 3's `¬ LeanAccepts` branch is
   therefore unreachable from `hrej`. `SoundSide` excludes the logup-panic bad set, a COMPLETENESS
   side condition, and is spurious in the "Lean rejects ⇒ contract reverts" direction. Deleting it
   from `Rejects` would strengthen a §6 shape by REMOVING a hypothesis, which this card was not
   authorised to do (authorisation was add-fields-to-`Frame`/`Clean` only), so it is named as
   `rejects_of_not_accepts` instead. **Decision needed:** delete `SoundSide` from `Render.Rejects`
   (then `rejects_of_not_accepts` collapses to a one-line `exact` and the cone drops by 1), or keep
   the split and let C.3 own both.

**§6 FIELD CHANGES: NONE.** `Frame` and `Clean` are untouched — no field added, none removed. The
composition is expressible with the §6 shapes as they stand, with two recorded limits: the
`traceReturn` poisoned fall-through (a POST-condition limit, not a boundary-predicate limit) and the
`Rejects`/`SoundSide` hypothesis mismatch (a §6 hypothesis-set limit in `Rejects`, not in
`Frame`/`Clean`).

**M0.1 CAVEATS CARRIED INTO THIS TABLE (do not read the sequencing rows as "cheap, therefore done").**
`slices_seq_sound` and `slices_seq_progress` chain over all SEVEN slices, and two of those seven
links are vacuous or near-vacuous at the plan level:
* `quotientLin` emits **122 of 6572 tokens** (M0.1 finding 4: the two `quotient_numerator` includes
  and the accumulator/trace helper includes are not emitted). Its `BlockSound`/`BlockProgress` are
  therefore about 2% of the region the contract is supposed to cover, and it is the block C.1 sorried
  separately as `poseidon_quotient_block`. `hB` is asked for `fun _ => True`, i.e. it INCLUDES
  `quotientLin`: the composition cannot skip it, and closing the other six does not close this one.
* `pcs` is **EMPTY at the plan level** (M0.1 finding 5: `computationsAst = ok, 0 blocks`,
  `mA.pcsComputations.length = 0`, rendered text region empty too). Its two contracts are vacuously
  satisfiable, so a green `slices_seq_*` proves NOTHING about the PCS stage. The row is not "needs
  nothing"; it is "needs a plan-level fix upstream of every card in this queue".
Consequence for the cone: the sequencing lemmas are the CHEAP part (est. 150-230 lines together, n=1
combinator sample each) and the `hB` hypothesis they consume is the expensive part — 7 block
contracts, 2 of which are currently about an empty or 2%-emitted region.

**CONE, BEFORE AND AFTER (measured, not projected).**
`#cone_sorries Midfall.LoweringV2.lowering_equivalence_of_blocks`: **1 → 7**.
`#cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon`: **5 → 11**.
It moved UP by 6. That is not progress on the headline and is not presented as any: the headline
still has `poseidon_valid`, `poseidon_quotient_block`, `poseidon_rejects` and
`blockContracts_of_valid` in its cone, and now also 6 new LoweringV2 names plus
`Bridge.Run_worldEq_of_noWriters`. What changed is that one unnamed hole (the body of
`lowering_equivalence_of_blocks`) became 7 named ones with pinned interfaces. The count goes down
only when the rows above close; `prog_slices_decomp` is the one new sorry NOT in the cone (nothing
cites it yet), so the table has 7 rows and the cone shows 6 of them plus `Run_worldEq_of_noWriters`.

### C.4 — Validity skeleton, clause by clause  **[MERGED aee4f69 - NEGATIVE: 6 of 11 clauses REFUTED; not Valid is PROVED]**
GEN · SKELETON · box 2 h · Sonnet · after C.1

- **Goal.** `poseidon_valid` built from one lemma per `Render.Valid` clause. The 11 clauses are
  `circuitMeta`, `layout`, `invariants`, `model`, `inputs`, `codegen`, `closed`, `slots`, `supported`,
  `noWriters` and `transcriptMptr`.
- **Do.** Close the clauses that are decidable now; `native_decide` is allowed only in `Instances/`,
  and the axioms are reported. Reuse D.3 checks 1–2. Name the rest.
- **Does NOT need.** Yul semantics.
- **Deliverable.** `Instances/PoseidonValid.lean`.
- **Accept.** Each clause is either proved, with its axioms printed, or a named sorry. The cone count
  is reported.
- **Stop if.** A clause evaluates to `false`. Report NEGATIVE with the values.

### FP.0 — FinalPairing contract skeleton  **[MERGED ff7d145 - 1st block contract; needs R.Valid which is REFUTED]**
SEM · SKELETON · box 2 h · strongest · after C.2

- **Goal.** FinalPairing's `BlockSound` ∧ `BlockProgress`, proved from named sorried lemmas:
  - `fp_pairing_algebra`, the algebra (closed by P.1);
  - `ec_pairing_contract`, the helper's contract (closed by T.4);
  - the per-statement arithmetic and memory steps (closed by T.5).
- **Needs.**
  - the §6 shapes in `Blocks.lean`;
  - `poseidonRender.slice .finalPairing` and the `ec_pairing` helper in `poseidonRender.helpers`;
  - C.2's names for the FinalPairing nodes.
- **Does NOT need.** A pairing implementation (`product` is a parameter, related to the pairing only
  by `Holds`), any other block, or proofs of the three lemmas.
- **Deliverable.** The skeleton in `Blocks.lean` or a new `Blocks/FinalPairing.lean`, plus a
  requirements table (one row per lemma: statement, use site, evidence).
- **Accept.** Build green, and the cone lists the three lemma groups.
- **Stop if.** The contract needs a fact about the pairing beyond `Holds`. Report the exact goal
  state; do not open the curve model.

**FP.0 RESULT — FinalPairing contract skeleton (landed in `Midfall/LoweringV2/Blocks/FinalPairing.lean`, a new module imported from `Midfall.lean` and from `Tools/ConeReport.lean`).**

**THE THREE GROUPS.** `fp_pairing_algebra` (P.1), `ec_pairing_contract` (T.4), `fp_stmt_steps` (T.5). The contract `fp_finalPairing_contracts : R.BlockContractsAt product (· = Partial.finalPairing)` IS `BlockSound R .finalPairing ∧ BlockProgress R .finalPairing` under §6's own quantifiers, and its proof contains **no `sorry`** — it composes the three groups against §6's shapes. `fp_blockSound` / `fp_blockProgress` project each half.

| Lemma | Statement (shape) | Use site | Evidence | Size estimate |
|---|---|---|---|---|
| `fp_pairing_algebra` :281 (SORRY, **P.1**) | `fpAnsBit R product Snap = true ↔ DualMSM.check Snap.c.dual R.params = true`, with `fpAnsBit = product (fpFrame R Snap)` and `fpFrame` the two-pair EIP-2537 frame the slice lays out: `(dual.right.eval, nG2Prepared⁻¹)` then `(dual.left.eval, sG2Prepared⁻¹)` — the call-site swap of `ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)` is inside the definition, so no transport lemma is needed | glue, twice, both in the `BlockProgress` halves (backwards: §6's `DualMSM.check = true` gate → the honest answer bit); the forwards direction is consumed inside `ec_pairing_contract`'s conditional `.pairing` clause | `Eip2537.Holds.pairing2` (Eip2537.lean:137) IS this equation for a two-pair `pairingFrame`; `DualMSM.check` (Msm.lean:222-232) is `decideBool (toMul (e(left,sG2)+e(right,nG2)) = 1)`; the gap is `map_neg` twice plus a `decideBool` inversion. Width pinned by `pairingTwoPairBytes == 0x300` (Externals.lean:887-889) = 128+256+128+256 | **no basis yet** (n=0: no algebra lemma of this shape is in the tree). Nearest sample `Inv.pairing_decision` (Inv.lean:865, 5 proof lines, n=1), the same `.pairing` arm read the other way |
| `ec_pairing_contract` :328 (SORRY, **T.4**) | three conjuncts: permissive `StmtsContractAll` over `R.slice .finalPairing`, pre `fpPre` (`Frame ∧ Inv .pcs`), post `fpPost` (revert ∨ normal ∧ `Frame` ∧ `success = fpWord (fpOutBit …)` ∧ `Inv .pcs` ∧ `(success = 1 → Inv .pairing)`); then for `c = callsOf product` the same forall-runs contract with pre `Clean .pcs` and post `fpPostHonest`, plus the `StmtsContract` existence half | glue, three times: `.1` for `BlockSound` conjunct 1, `.2.1` for `BlockProgress`'s forall-runs half, `.2.2` for its existence half | the helper body is in the tree (`Generator/VerifierPartials.lean:555`, AssemblyHelpers.yul:269-301): four `mcopy`s to `scratch+0/+0x80/+0x180/+0x200`, one `staticcall` to PAIRING_CHECK (0x300 in, 0x20 out), `fail(ERR_PRECOMPILE_FAILED)` on a failed or short call, `ret := and(ret, eq(mload scratch, 1))`. M0.1: 0 own loops and no looping helper → no fuel, no invariant. Needs `fpG2Slots` (below) for the G2 half of the frame, `Inv .pcs`'s two `holdsG1` clauses (Inv.lean:811-812) for the G1 half, and `Holds.g1Valid`/`g2Valid` to show `pairingValidInput = true` | **no basis yet** (n=0 — no `staticcall` contract is proved anywhere in the tree; `traceReturn_spec` and the `fail` selector equation are the nearest and neither calls a precompile). T.4's own box is 2.5 h with T.2's tactic as a prerequisite |
| `fp_stmt_steps` :358 (SORRY, **T.5**) | `StmtsContractAll` over the same slice, pre `Frame ∧ success = 0`, post `(halt ∧ Reverted) ∨ (normal ∧ Poisoned)` — exactly `BlockSound`'s second conjunct: a poison already present is never laundered | glue, once, by `exact`, as `BlockSound` conjunct 2 | the slice's FIRST statement is the guard `if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }` (GenAst.lean:651-652), so the call is never reached; `fail` = `mstore(0, shl 224 sel); revert(0,4)` → `Reverted` via `revertedOf` (Shared.lean:48). T.5 also owns the `U256`/`BitVec` identities (`iszero`, `and`, `eq … 1`) and the read-over-write facts that let `ec_pairing_contract` claim `Frame`/`Inv` survive a 768-byte scratch write | **no basis yet** (n=0). The revert-arm part is 2-3 statements deep; the arithmetic/memory table T.5 is charged with is shared with every other block card, not FinalPairing-specific |

**§6 FIELD CHANGES: NONE.** `Frame`, `Clean`, `Poisoned`, `exitOk`, `BlockSound`, `BlockProgress`, `BlockContractsAt` untouched — no field added, none removed.

**DOES C.2'S POISONED-NORMAL GAP BITE FINALPAIRING? NO.** C.2's finding (a) is that `BlockSound R .traceReturn` admits `o = .normal ∧ Poisoned` and the program-level post cannot. At `.finalPairing` that arm is not a defect but the point: FinalPairing is the block that TAKES the decision, so a normal exit with `success = 0` is the intended handoff, and §6's `.pairing` mid predicate `Clean .pairing ∨ Poisoned` (Blocks.lean:294) consumes it exactly. Checked, not assumed: the only thing FinalPairing must not do is launder an EXISTING poison, and that is `BlockSound`'s second conjunct (T.5), not a missing field.

**PREMISE GAP FOUND (a fact beyond `Holds`, and it is NOT about the pairing).** `ec_pairing` copies its two G2 arguments from the VK payload (`G2_BASE_MPTR`, `NEG_S_G2_BASE_MPTR`). For the frame on the wire to be the frame `DualMSM.check` states, those bytes must be `encG2 (params.nG2Prepared)⁻¹` and `encG2 (params.sG2Prepared)⁻¹`. Nothing in §6 says it: `Frame` carries the VK *runtime code*, not the payload's G2 header slots; `Inv` pins the G1 pairing slots at `.pcs` and the payload image at `.vk` but has NO clause naming either G2 slot; `Render.Valid.slots` is `EnvAgrees` (params ↔ generators), not the payload bytes. v1 carried exactly these two clauses as `VkSlotsAgree.g2BaseWords` / `negSG2Words` (Inv.lean:623-624, whose own docstring says "these two slots are half of the pairing input and nothing else in the tree says what they hold") — **V2's `Valid` has no `VkSlotsAgree` field.** Named here as `fpG2Slots R` and carried as an explicit hypothesis of `fp_finalPairing_contracts`. **DECISION NEEDED:** (a) add `VkSlotsAgree`'s two G2 clauses to `Render.Valid` — a change to the FROZEN §2, so not this card's to make; or (b) exhibit `fpG2Slots` at the deployment by computation (the payload is `R.pv.vk.constants`, so it is checkable) and let a later card own it. Consequence for C.2: `blockContracts_of_valid` cannot cover `.finalPairing` either, so the FinalPairing row of `h7` needs `fpG2Slots` from somewhere.

**COST FINDING (heartbeat — reported, not raised).** The card first stated the `Inv` transfer (`Inv .pcs → (success = 1 → DualMSM.check → Inv .pairing)`) as a sorry-free theorem. It does not check: `InvAt` is a thirty-clause `&&` chain of `holdsFr`/`holdsG1`/`bytesAt`, and `simp`+`tauto` normalisation of it exceeds the 200 000-heartbeat default (`(deterministic) timeout at whnf` on the declaration). Heartbeats were NOT raised. The transfer is folded into `ec_pairing_contract`'s post as the conditional clause `(success = 1 → Inv .pairing)`, which the glue applies instead of deriving. **T.4/T.5 note: a tactic that discharges `Inv`-chain steps cheaply is worth more than it looks** — this is the third card to hit `InvAt`'s width.

**CONE, BEFORE AND AFTER (measured).** `#cone_sorries Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon`: **11 → 11. It did not move, and it could not**: the headline reaches the per-block contracts only through the generic sorried `blockContracts_of_valid`, so nothing in its cone cites a per-block row. A skeleton raising the cone was acceptable; this one neither raises it nor lowers it. What changed is that the three groups are now **in a cone at all**, under a new fourth root: `#cone_sorries Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts` = **3**, listing `fp_pairing_algebra`, `ec_pairing_contract`, `fp_stmt_steps` — that is the acceptance criterion. Tracked sorries 11 → 14 (SORRY.md regenerated). When `blockContracts_of_valid` is replaced by per-block rows, this root's 3 move into the headline's cone.

**FALSE PREMISES IN THE CARD, both confirmed as the brief stated.** (1) C.2 has no FinalPairing names — none existed anywhere in the tree before this file; the names are this card's output. (2) `poseidonRender.slice .finalPairing` cannot be `#eval`'d (`poseidonRender` is `noncomputable`, PoseidonV2.lean:152) — nothing here computes, no `#eval`/`native_decide` is used, and the C.4 computable-proxy pattern was not needed because the slice's shape was read off `GenAst.emitFinalPairingArms` rather than evaluated.

### T.1 — Automation design from real cone nodes  **[MERGED a432de6 - tr_blockProgress PROVED, cone 0; headline cone unchanged]**
SEM · SKELETON · box 2 h · strongest · after FP.0

- **Goal.** One tactic interface that will close three named cone nodes:
  - TraceReturn `BlockSound`/`BlockProgress`;
  - `ec_pairing_contract`;
  - one loop-bearing node from the M0.1 table.
- **Needs.** Those three nodes; the vendored semantics (`EVM.run_adequacy` is sorry-free); the
  `Bridge` step lemmas; the existing `traceReturn_spec` proof as a pattern.
- **Does NOT need.** Other blocks, the generator, or the pairing.
- **Do.**
  1. Hand-prove the smallest node, under the 60 s rule.
  2. List the proof steps that recur.
  3. Write each step's tactic signature into the existing T.2–T.5 cards (the exact node each one
     must close). Add a card only if a step fits none of them.
- **Deliverable.** The hand proof (it closes one node) and the updated T.2–T.5 cards.
- **RESULT (T.1, landed).** New file `Midfall/LoweringV2/Blocks/TraceReturn.lean`, no `sorry`, axioms
  `[propext, Classical.choice, Quot.sound]`. **Closed: `BlockProgress R .traceReturn`** (§6's TOTAL
  contract, Blocks.lean:106) as `tr_blockProgress`; `#cone_sorries` on it prints **0**, and a
  `#cone_avoids` line for it is added to `Tools/ConeReport.lean`. `BlockSound`'s **conjunct 1** is
  closed as `tr_sound_clean`; conjunct 2 is one step short (the `fail` inversion, S6) and is written
  into T.5 and T.2 above. The interface is six named step lemmas S1–S6 (§2–§3 of that file), reused
  verbatim by T.2/T.3/T.4/T.5 per the cards.
  **PREMISE GAP FOUND:** the existence half needs the render's constant table to bind `RETURN_MPTR`
  (named `trRetMptr`), because `BlockProgress` must EXHIBIT a run and nothing in
  `Frame`/`Clean`/`Inv` binds the return window — v1's own note at Partials.lean:1251 says the same,
  and V2's `Valid` pins only `TRANSCRIPT_MPTR`. Soundness needs no such pin: there the binding is a
  CONSEQUENCE of the run (`trAddr`). Dischargeable at the deployment by computation
  (`pinnedConstants` has `("RETURN_MPTR", 4096)`).
  **CONE: headline 11 → 11, `fp_finalPairing_contracts` 3 → 3 — neither moved, and neither could:**
  nothing in either cone cites TraceReturn.lean (the headline reaches per-block contracts only through
  the sorried `blockContracts_of_valid`). `verify.sh --quick` green.
  **FALSE PREMISES IN THE CARD:** (i) the `Bridge` view-direction problem does not arise at this node
  — no view lemma is cited or needed, every step is a `Step` inversion on a run hypothesis, which is
  already the direction §6 states; (ii) the card's "pick the smallest such node" for the loop node is
  `lagrange`, and it is NOT the smallest of the three — TraceReturn is, by a wide margin, and that is
  what got closed; (iii) `traceReturn_spec` was READ as a pattern only (Partials.lean:1256, v1,
  retired) and nothing was imported from it — three of its pieces are copied by value
  (`readBytes_storeWord_one`, `map_congr_range`, the `iszero` inversion) and restated for V2's shapes;
  (iv) `EVM.run_adequacy` was not needed, not cited, and `vendor/` is untouched.

---
**CRITICAL PATH — make the deployment render valid** *(added in review, 2026-11-17)*. Every route to
the headline goes through `poseidon_valid`, and `¬ poseidonRender.Valid` is PROVED (C.4,
PoseidonValid.lean:468; 6 of 11 clauses refuted). Until the render is valid, block rows (S.3–S.7)
are generic progress only. F.2 and R.2 are READY now. R.1 is DONE (`2041977`, run as "F.1" ahead of
D-P47 sign-off). R.3, R.4 and R.5 wait on decisions drafted in `docs/DECISIONS-PENDING.md` (R.5: below).

### F.2 — The deployment table: every hypothesis of the headline route, decided once  **[READY — RUN FIRST]**
GEN · PROBE · box 1 h · Sonnet · after nothing

- **Goal.** One table at `poseidonRender` of everything the headline route needs, so the remaining
  gaps surface in one card rather than one per card (EXECUTION-V2 §4: "nothing is discovered one pass
  at a time"; C.2, C.4, FP.0, T.1, M.1 and S.1 each found one more).
- **Rows.** The 11 `Render.Valid` clauses (re-run C.4's table at the current commit); the proposed
  pins `fpG2Slots` (D-P46), `trRetMptr` (D-P48) and v1's `g1BaseWords` (Inv.lean:617); the
  `Rejects`/`SoundSide` gap (C.2); `G1CodecLaws poseidonE.g1`; the D-P45 witness (an accepting
  calldata).
- **Columns.** Verdict — PROVED · REFUTED · OPEN · NOT-COMPUTABLE (depends on an axiom or on
  `Classical.choose`) — then the exact command or theorem that decided it, and the root cause.
- **Verify first.** `fpG2Slots` at the deployment: `poseidonSG2 := bls12_381Pairing.g₂`
  (PoseidonEnv.lean:386) and `poseidonParams.sG2Prepared := poseidonSG2`, so its second conjunct reads
  `NEG_S_G2_BASE = encG2 g₂⁻¹` (−G₂) while the payload holds −s·G₂ (Gap B, R.4). Expect REFUTED or
  NOT-COMPUTABLE; record which.
- **Does NOT need.** Proofs of any clause; edits to `Statements.lean`, the fixtures or the profile.
- **Deliverable.** The table in the report; one QUEUE line per new gap, with its reproducer.
- **Accept.** Every row cites a command output or theorem at the card's commit.

### R.2 — WP-G1 region inventory (`Valid.codegen`)  **[READY]**
GEN · PROBE · box 1 h · Sonnet · after nothing

- **Goal.** The list of regions the `GenAst` emitter does not produce yet, so WP-G1 (PLAN-V2:232) can
  be cut into EMIT cards. C.4 measured 3156 AST tokens against 10433 printed, first difference at
  index 1333.
- **Does NOT need.** Writing any emitter; Yul semantics.
- **Deliverable.** One row per missing region: its name, printed token count (`#eval`) and WP-G1 item;
  one EMIT child card per region in QUEUE.md (EXECUTION-V2 §4 EMIT row).
- **Accept.** The token counts account for the measured gap (10433 − 3156), or the residue is
  explained.

### ~~R.1~~ (review draft) — Re-export the fixture with the constraint-system data (D-P47)  **[SUPERSEDED — executed as R.1 below (`2041977`); do not run]**
INFRA · PROBE · box 1 h · Sonnet · after D-P47 sign-off

- **Goal.** A refreshed `fixtures/conformance/poseidon/` whose `vk.json` (or a sibling file) carries
  `gates`, `lookups`, `trashcans` and `permutation.columns`, with `proof.bin`/`instances.json` from
  the same export (D.3: committed proof 4752 B vs exported 2640 B).
- **Verify first.** Locate the Rust exporter that wrote the fixture (path:line). The refreshed VK must
  still reproduce the deployed contract byte for byte (D.1's gate).
- **Does NOT need.** Porting `LoweringPlan::new` (WP-G4); any proof.
- **Deliverable.** The refreshed fixture files, or NEGATIVE with the reason (then WP-G4 becomes the
  plan, per D-P47). Child card: GEN · KAT — re-run D.3 checks 1–2 (`Valid.layout`,
  `Valid.circuitMeta`) and C.4's `circuitMeta`, `layout`, `invariants`, `slots` and `supported`
  clauses on the refreshed fixture, one verdict each.
- **Accept.** D.1's byte-for-byte gate still passes on the refreshed fixture.
- **Stop if.** The refreshed fixture describes a different circuit or VK from the deployed contract:
  that is a scope question for the human.

### R.3 — Make `Valid.model` dischargeable  **[BLOCKED: human decision — `docs/DECISIONS-PENDING.md` §9]**
DECISION · ≤ 1 page

- C.4: `model` is true but blocked twice — `poseidonModelVal`'s error arm mentions `poseidonModel` in
  its own proof type, so `cases`/`rw`/`simp` fail on the motive. Both routes C.4 measured need the
  human: `deriving Inhabited` on `Halo2Verifier` (a v1 edit) plus a `getD` restatement, or a frozen
  change to `Render.Valid.model`.

### R.4 — Gap B: how s·G₂ is modelled at the deployment  **[BLOCKED: human decision — `docs/DECISIONS-PENDING.md` §8]**
DECISION · ≤ 1 page

- The model's s·G₂ is the generator: `poseidonSG2 := bls12_381Pairing.g₂`, "NOT checked against that
  hex" (PoseidonEnv.lean:386). So the deployment's Lean verifier pairs with g₂ where the contract pairs
  with s·G₂, and neither D-P46's slot pin nor FP.0's `fpG2Slots` hypothesis can hold at this render as
  modelled. Same discrete-log class as `g1CodecZ.ofCompressed?`. Blocks D-P46 and the FinalPairing
  route at the deployment.

### R.5 — The committed fixture is not reproducible  **[BLOCKED: human decision]**
DECISION · ≤ 1 page · raised by R.1 (`2041977`)

- R.1 found that `proof.bin` and `trace.json` differ from run to run (the prover's blinding is
  non-deterministic), and the committed bundle matches neither of its two runs. Every other output is
  byte-stable. The regenerated `Halo2Verifier.sol` differs from the committed one only in `BUILD_ID`
  (a stale tracked dump).
- R.1 kept the committed `proof.bin`/`trace.json`, because D.3 checks 4–5 pin the transcript to
  `trace.json`. Its regenerated copies were left in `/tmp/f1-regen/`, which is not in the tree
  (EXECUTION-V2 forbids `/tmp`-only evidence); treat them as lost.
- Decide: keep the committed proof as the pinned ground truth with unknown provenance, or make the
  export deterministic (seeded RNG in the test exporter), regenerate once, and re-pin D.3 checks 4–5
  in the same commit. Either way, refresh or untrack the stale `Halo2Verifier.sol` dump.

---
**BLOCK ROWS — generic progress.** Rows are stated for every `R`; none can move the headline cone
while `poseidon_valid` is refuted (see CRITICAL PATH above).

### S.3 — Apply the D-P49 §6 gate and repair the rows  **[MERGED d0aabba — DONE; D-P49 signed off 2026-11-17]**

SEM · PROOF · box 1.5 h · strongest · after S.1, D-P49 sign-off

- **Goal.** Gate `BlockSound`'s two poisoned arms on `q ≠ .traceReturn` and repair every dependent.
- **Needs (present at `7bf0497`).** `Blocks.lean:96-97`, `:100-101`; `tr_blockRow`/`fp_blockRow`/
  `blockContractsAt_twoRows` in `Blocks/Compose.lean`; `tr_sound_clean` (TraceReturn.lean:741) and
  `tr_poison_walk` (:853).
- **(Landed in `d0aabba` as `tr_sound_clean_noarm`/`tr_poison_walk_noarm`, no `sorryAx`.)** Original card text: the arm-free restatements `tr_sound_clean'` and `tr_poison_walk'` that D-P49
  cites as its evidence: S.1 elaborated them in scratch and merged no code. They are step 1 here, not
  a premise.
- **NEEDS snippet** (the orchestrator runs it before briefing; every line must elaborate):
  `#check @Midfall.LoweringV2.Blocks.TraceReturn.tr_sound_clean`,
  `#check @Midfall.LoweringV2.Blocks.TraceReturn.tr_poison_walk`,
  `#check @Midfall.LoweringV2.Blocks.tr_blockRow`, `#check @Midfall.LoweringV2.Blocks.fp_blockRow`.
- **Do.** 1. Land `tr_sound_clean'` (clean → revert ∨ exitOk) and `tr_poison_walk'` (poisoned →
  revert) in `Blocks/TraceReturn.lean`, sorry-free. 2. Apply the gate exactly as D-P49 states.
  3. Rebuild `tr_blockRow` from step 1's lemmas — **the landed one cites the armed version and will
  break.** 4. Confirm `fp_blockRow` still type-checks (finalPairing ≠ traceReturn — verify, do not
  assume).
- **Deliverable.** The two restatements, the gate and the repaired rows, all sorry-free.
- **Accept.** `verify.sh --quick` green; **`cone_sorries` unchanged at every root** (headline 11,
  `tr_blockSound` 0, `tr_blockProgress` 0, `fp_finalPairing_contracts` 3); `#print axioms` of every
  new or repaired lemma with **`sorryAx` grep = 0**; `Frozen.sha256` verifies.
- **Stop if.** Step 1 does not elaborate sorry-free — D-P49's premise is then false: report NEGATIVE
  with the goal state · any root's cone moves unexpectedly.

### F.1 — Prove the sequencing glue (`slices_seq_sound`, `slices_seq_progress`)  **[READY — S.3 merged d0aabba]**
SEM · PROOF · box 2.5 h (split at 1 h: sound / progress) · strongest · after S.3

- **Goal.** Both sequencing lemmas proved sorry-free from their seven per-block hypotheses, with
  D-P49's gate in place. C.2 left this glue sorried, which hid the sequencing ceiling until S.1, six
  cards later. Proving it now finds any further ceiling BEFORE four row cards are spent.
- **Needs.** S.3 merged; `slices_seq_sound` (Blocks.lean:307) and `slices_seq_progress` (:325), their
  mid predicate `Clean R k ∨ Poisoned` (docstring at :287); `StmtsTotal` (:49); C.2's size estimates
  (QUEUE C.2 table: 60–100 and 90–130 lines).
- **Does NOT need.** Any block row; the deployment; `Statements.lean`.
- **Also.** Fix the stale docstring at `Blocks.lean:301-303` (it still says §6 has the poisoned arm;
  S.3 left it for the next card that touches `slices_seq_sound`).
- **Deliverable.** Both lemmas, sorry-free.
- **Accept.** `#print axioms` of both with `sorryAx` grep = 0. **Expected: `cone_sorries
  lowering_equivalence_poseidon` 11 → 9 and `lowering_equivalence_of_blocks` 7 → 5** — the first
  headline-cone drop since C.2.
- **Stop if.** A handoff needs a fact no `BlockSound`/`BlockProgress` supplies: report the exact goal
  state. That is the next ceiling, and finding it here is the point of this card.

### S.4 — `BlockRow` for `vkLoading`  **[READY after F.1]**  **[MERGED 93c0d4c - PARTIAL: row NOT closed, 15 sorry-free lemmas + 6 pin gaps]**
SEM · PROOF · box 2 h · strongest · after S.3, F.1
- **Goal.** `BlockRow R product .vkLoading`. **Shape from S.1:** pre `Clean R .start`, post `(halt ∧
  Reverted) ∨ Clean R .vk ∨ (normal ∧ Poisoned)`; honest `StmtsTotal` gated on `G1CodecLaws ∧
  ChallengesGood ∧ DualMSM.check`.
- **Needs.** M0.1's vkLoading row (1 stmt; writes 0x2900..0x3ae0 {vk_payload} + 0x0..0x20 via fail;
  **9 `success := and(…)` guards ⇒ the poisoned arm is LIVE**); `extcodecopy` vs `Frame.vkCode`.
- **Does NOT need.** Other blocks; the deployment; the pairing.
- **Accept (S.4–S.6).** The row proved with `#print axioms` `sorryAx` grep = 0, or PARTIAL with each
  gap a named sorried lemma. Consumer: `blockContracts_of_valid_of_rows` (Blocks.lean:713).
  **Expected headline cone: unchanged** — a row reaches the headline only when all seven rows exist
  and `blockContracts_of_valid` is re-proved from `_of_rows`. Every `BlockRow` opens with
  `(R.Valid) →` (Blocks.lean:688) and `¬ poseidonRender.Valid` is proved, so a row stated AT
  `poseidonRender` is vacuous (PLAN-V2 §4.4): state rows for every `R`, and never report one as
  headline progress.

### S.8 — Verify the six `vkLoading` pins at the deployment  **[READY — RUN BEFORE ANY `Valid` CHANGE]**  **[DONE 89e9c0a - all six pins TRUE and PROVED at the deployment; see D-P50/S.9]**

GEN · KAT · box 1 h · Sonnet · after S.4

- **Goal.** Establish computationally whether S.4's six pins are TRUE at the deployment, before any of
  them enters frozen `Valid`. **D-P46/D-P48 each added one pin whose value was already known; six at
  once, unverified, is a guess about the frozen surface and is refused.**
- **Needs.** S.4's `vkPins` (1 table `VK_MPTR` = `ptrAddr pv.memory.vkMptr`; 2
  `EXPECTED_VK_PAYLOAD_LENGTH` = `pv.vk.len`; 3 `pv.numInstances` = `cfg.numInstances`; 4 VK/g1Identity
  window disjointness) and `vkProgressPins` (5 `EXPECTED_VK_LENGTH` = `runtimeBytes.size`; 6
  `EXPECTED_VK_CODEHASH_WORD` = `keccak256 runtimeBytes`). Computable proxies `poseidonPv`/`poseidonM`
  (C.4's pattern, pinned to `poseidonRender` by `rfl`); `poseidonRender` is noncomputable.
- **Do.** Evaluate each at the deployment. **All six are decidable equalities over `consts.lookup` and
  lengths — no proof needed, just computation.** Report TRUE / FALSE / UNDECIDABLE per pin, with the
  printed value.
- **Deliverable.** The verdict table + a recommendation: which pins (if any) are safe to add to
  `Render.Valid` as a follow-up decision, and which must stay row-level hypotheses.
- **Accept.** Six printed values. **If any pin is FALSE at the deployment, say so loudly** — that means
  `BlockSound R .vkLoading` is false at the deployment even with the pins, and the §6 shape problem is
  deeper than under-pinning.
- **Stop if.** A pin is not decidable by computation (report which and why).
- **Does NOT need.** Editing `Valid`; any block row; the pairing.

---
### S.9 — Land the six pins: `Valid` fields + the proved deployment discharge  **[READY]**  **[MERGED fece4c7 - Valid now 13 clauses; vk_blockRow pin-free; cone unchanged]**

INFRA · PORT · box 1.5 h · Sonnet · after S.8

- **Goal.** Execute D-P50: add `vkPins`/`vkProgressPins` as `Render.Valid` fields and land S.8's proved
  structure terms so `vk_blockRow` can be discharged from facts rather than hypotheses.
- **Needs.** `/tmp/s8/` probes — **if missing, STOP**: the proved `pins_at_render` /
  `progress_at_render` terms and the six `native_decide` lemmas must be transplanted, not re-derived.
  `Blocks/VkLoading.lean:668`/`:684` (the structures); `Instances/PoseidonValid.lean:87-88` (proxies);
  the defeq transfer lemmas `poseidonConsts_eq`/`poseidonPv_eq`/`poseidonPlan_eq`/`poseidonCfg_eq`.
- **Do.** 1. Add the two structures as fields of `Render.Valid` (`Statements.lean` §2 — **frozen, so
  re-hash `Frozen.sha256` in the same commit and say so in the message**). 2. Land the six decided
  lemmas + two structure terms in `Instances/PoseidonPins.lean`. 3. Feed them to `vk_blockRow` so the
  pins are no longer free hypotheses. 4. Regenerate `SORRY.md`.
- **Accept.** `verify.sh --quick` green; **`cone_sorries` at every root before and after — `vk_blockRow`
  is expected to STAY at 3** (the pins were never the sorried part). `#print axioms` of the two
  structure terms, with `sorryAx` grep = 0. **List all `native_decide` axioms now in the deployment
  path — the count should go from 1 to 7.** Frozen re-hash shown as a deliberate diff.
- **Stop if.** `/tmp/s8/` is gone · adding the fields breaks any existing `Valid` construction site
  (report it — that means something already builds a `Valid`) · a re-derived pin fails where S.8 proved
  it (that contradicts S.8 and must be reported, not fixed silently).
- **Does NOT need.** Proving `vk_sound_clean`/`vk_progress`/`vk_poison_walk`; any other block row;
  the pairing; v1 files; `vendor/`.

---
### R.1 (ran as "F.1") — Re-export the poseidon fixture WITH the constraint-system data (D-P47)  **[DONE 2041977 — ran ahead of D-P47 sign-off as a measurement card; `Valid` clauses 6/6/1 → 8 proved / 4 refuted / 1 sorry; reproducibility → R.5; do not re-run]**

GEN · PORT · box 2.5 h · strongest · **split at 1 h into (export) and (re-derive)** · after S.9

- **Goal.** Make the deployment's real `ProtocolPlan` available as data, so C.4's four
  protocol-caused refutations (`circuitMeta`, `layout`, `invariants`, `slots`) can close from facts
  rather than from a port of `LoweringPlan::new`. **D-P47 mandates this BEFORE any such port.**
- **Why this is the critical path.** C.4 PROVED `¬ poseidonRender.Valid`: 6 of 13 clauses refuted, and
  clauses 1/2/3/8 are ONE root cause — `planM.protocol = protocolPlanDefault`, a typed-in placeholder.
  **No Lean card can fix that. Until it is fixed, the cone cannot reach 0 however many block rows land.**
- **Needs (orchestrator-measured at 3e15e9f).**
  - Export source: **`proofs/solidity-verifier/tests/poseidon_fixture.rs`** — it writes
    `proofs/solidity-verifier/target/poseidon-fixture-dump/{Halo2VerifyingKey.sol, Halo2Verifier.sol,`
    `calldata.bin, instance.be, …}`.
  - `formal/fixtures/conformance/poseidon/vk.json` currently has: `advice_column_phase`,
    `advice_queries`, `blinding_factors`, `cs_degree`, `extended_k`, `fixed_commitments_compressed_hex`,
    `fixed_queries`, `instance_queries`, `k`, `n`, `nb_public_inputs`, `num_advice_columns`,
    `num_challenges`, `num_committed_instances`, `omega_be_hex`, `permutation_commitments_compressed_hex`,
    `proof_len`, … **and NOT: `gates`, `lookups` (only `num_lookups`), `trashcans` (only
    `num_trashcans`), `permutation.columns`.** Those four are exactly what D.2 gap A and C.4 need.
  - `Instances/PoseidonInputs.lean` (`poseidonVkGen`, `poseidonPlanV2`), `Instances/PoseidonEnv.lean`,
    `Instances/PoseidonV2.lean` (`poseidonRender`), `Instances/PoseidonCoherence.lean` (D.3 checks 1-2).
- **Do — HALF 1 (export, ≤1 h).** Extend `poseidon_fixture.rs` to emit the four missing structures
  into `vk.json` (or a sibling `cs.json` if the shape is awkward). **Re-run the fixture; do not hand-edit
  JSON.** If the Rust side cannot expose them, **that is the NEGATIVE D-P47 asked for — report it with
  the exact Rust error and stop; it makes `LoweringPlan::new` the plan.**
- **Do — HALF 2 (re-derive, only if half 1 lands).** Rebuild `poseidonVkGen`/`poseidonPlanV2` so
  `poseidonMeta.protocol` is the real `ProtocolPlan`, then re-run **D.3 checks 1-2 and C.4's clause
  table**. **Expect some to flip from REFUTED to PROVED — report each with its printed value.**
- **Does NOT need.** Porting `LoweringPlan::new` (that is the fallback, not this card); any block row;
  the pairing; §6/§7 changes; `Frozen.sha256` edits.
- **Deliverable.** The export change + (if half 2 runs) the re-derived terms and a before/after clause
  table. **Also: D.3 found the bundle is NOT the committed fixture (`committed_proof_len 4752` vs
  `exported 2640`, `proof=false`) — if the re-export can fix that too, do it here; one refresh, not two.**
- **Accept.** **`cone_sorries lowering_equivalence_poseidon` before and after — it is 11.** **This is the
  first card with a realistic chance of moving it: if `poseidon_valid`'s four protocol clauses close,
  the `poseidon_valid` sorry may become dischargeable.** Report the C.4 clause table re-measured, not
  asserted. `verify.sh --quick` green; `git diff --stat` shows no frozen `.lean` touched.
- **Stop if.** The Rust side cannot expose the data (NEGATIVE — a deliverable) · half 1 exceeds 1 h ·
  re-deriving changes a frozen statement · any evaluation >60 s · the fixture regenerates with
  DIFFERENT bytes for things that should be stable (that means the export is not reproducible — stop).

---
### S.10 — Fix the stale `Valid` clause-count prose  **[READY — small]**

INFRA · DOCS · box 0.5 h · Sonnet · after S.9

- **Goal.** `Render.Valid` now has **13** clauses (S.9 appended `vkPins`, `vkProgressPins`). Several
  comments still say 11 and actively misdescribe the frozen surface.
- **Needs.** `Instances/PoseidonValid.lean` 'CLAUSE n OF 11' headers; `Instances/PoseidonV2.lean:173`
  'the eleven computation clauses'; any other '11 clauses' mention (`grep -rn 'OF 11\|eleven'
  Midfall/Instances/`).
- **Do.** Update the counts and clause numbering. **Comment text only — no proof changes.**
- **Accept.** `grep` shows no stale '11 clauses'/'OF 11' referring to `Valid`; `verify.sh --quick` green;
  `Frozen.sha256` verifies (these files are NOT frozen, so no re-hash).
- **Note for whoever runs it:** rebuilding `PoseidonValid.lean` re-runs ~20 `native_decide`s — budget
  for it; S.9 left this out of scope for exactly that reason.
- **Does NOT need.** Any proof change; the pins; any block row.

---
### S.5 — `BlockRow` for `transcriptParser`  **[READY after F.1; see the WP-T stop below]**
SEM · PROOF · box 2.5 h · strongest · after S.3, F.1
- **Goal.** `BlockRow R product .transcriptParser`. **The big one: 44 stmts, 9 own loops ⇒ fuel + 9
  invariants.** Pre `Clean R .vk`, post `… ∨ Clean R .transcript ∨ …`.
- **Needs.** M0.1's transcriptParser row (16 locals written; 4 static ranges + **11 dynamic write
  sites**; helpers `transcript_init, common_word, fail, common_uncompressed_g1, squeeze_to`, none
  loops); `Yul/Contracts.lean` loop rules.
- **Split at 1 h** into (loops) and (guards) if needed.
- **Accept.** As S.4. **If the 9 invariants do not close, deliver the ones that do and name the rest.**
- **Stop if.** The first loop invariant is not closed at 1 h. PLAN-V2:269 puts automation (WP-T)
  BEFORE block proofs because "hand proofs at that density are infeasible", and TraceReturn took 988
  lines by hand. Report lines per Yul token so the WP-T decision (`docs/DECISIONS-PENDING.md` §10) is
  taken on data.

### S.6 — `BlockRow` for `lagrange`  **[READY after F.1]**
SEM · PROOF · box 2 h · strongest · after S.3, F.1
- **Goal.** `BlockRow R product .lagrange`. **The only loop-bearing helper is `batch_invert`.** Pre
  `Clean R .transcript`, post `… ∨ Clean R .lagrange ∨ …`.
- **Needs.** M0.1's lagrange row (3 stmts, 21 locals written, 5 own loops, `success :=
  batch_invert(…)`); `Yul/Contracts.lean` loop inversion; **FP.0's cost finding: the `Inv`-chain
  transfer blows the heartbeat default — do NOT raise heartbeats, fold the clause as FP.0 did.**
- **Accept.** As S.4.

### S.7 — The `quotientLin` contract (GAP G3)  **[BLOCKED: WP-G1 not merged (see R.2) · S.2 may move five `Inv` clauses into this post]**
SEM · PROOF · box 1.5 h · strongest (W10: Quotient) · after R.2's WP-G1 children, S.2
- **Goal.** Discharge C.1's `poseidon_quotient_block` (PoseidonV2.lean:207). **S.1 established six
  rows are NOT enough;** `.quotientLin` needs its contract too.
- **Not a `BlockRow`.** `poseidon_quotient_block` has no `R.Valid` hypothesis; `BlockRow` opens with
  `(R.Valid) →` (Blocks.lean:688), and `¬ poseidonRender.Valid` is proved (PoseidonValid.lean:468). A
  row stated at `poseidonRender` is therefore vacuous and cannot discharge it (PLAN-V2 §4.4). A
  generic row would also need `R.qblocks = compactBlocks R.plan` in `Valid` (WP-G3, PLAN-V2:258,
  frozen-surface sign-off).
- **Needs.** M0.1's quotientLin row (1 stmt, **122 of 6572 tokens emitted**, writes only the 2-word
  QUOTIENT_MPTR payload, **0 `success` assigns**); WP-G1 merged; S.2's verdict.
- **Stop if.** The unemitted region means the contract cannot be stated at all — report, do not pad.
- **Accept.** `poseidon_quotient_block` proved, `sorryAx` grep = 0, headline cone down by 1; or
  PARTIAL with each gap a named lemma.

### ~~pcs row~~  **[HELD — blocked by S.2]**
S.1 showed (in scratch; nothing landed) that an empty slice's `BlockSound` forces `Inv .quotient → Inv .pcs`, and the
`.pcs` arm adds five clauses `.quotient` lacks (fEval 16288, v 16320, finalCom 16352, pairingLhs 16480,
pairingRhs 16608). **The `pcs` row is REFUTABLE, not merely hard, until S.2 lands.** Do not write it.

---
### S.1 — Resolve the `slices_seq_sound` ceiling  **[DONE (read-only probe, no code merged) - verdict (b), a §6 shape problem; records in 7bf0497 (not `3963aa3`, which is M.1's ETA row); see D-P49 (signed off 2026-11-17) and S.3]**

SEM · PROBE · box 1 h · strongest · after M.1

- **Goal.** Determine whether the four missing block rows can close `slices_seq_sound` at all.
- **Why first.** M.1 established that **even 6/6 rows plus the quotient row do NOT close
  `slices_seq_sound`** — its post has no `normal ∧ Poisoned` arm (`Blocks.lean:299-305`) and no
  per-block contract supplies it. **Writing four block-row cards against a known ceiling would waste
  them.** This card decides whether they are worth writing.
- **Do.** State precisely what `slices_seq_sound`'s post asserts vs what `BlockRow` supplies; determine
  whether the gap is (a) a missing arm in the sequencing lemma's post, (b) a §6 shape problem, or
  (c) genuinely unprovable as stated. Report which, with the goal state.
- **Deliverable.** The verdict + the minimal change that would close it, if any.
- **Accept.** A clear answer to: *can per-block rows ever reach the headline?* If no, say so — that
  reshapes the plan and is worth more than four cards of work.
- **Does NOT need.** Proving any block row. Editing §6.

### S.2 — Resolve the `pcs` / `Inv` boundary misalignment  **[READY]**

GEN · PROBE · box 1 h · Sonnet · after M.1

- **Goal.** Decide where the five `.pcs`-arm `Inv` clauses belong.
- **Why.** M.1 measured `sliceOf poseidonPv poseidonM .pcs = []`, so the `pcs` row collapses to
  `Clean .quotient → Clean .pcs`, asserting fEval 16288, v 16320, finalCom 16352, pairingLhs 16480,
  pairingRhs 16608 — **all outside the lagrange/quotient arms 15904-16192 — at a boundary nothing
  before it writes.** Not fixable by adding `Frame`/`Clean` fields.
- **Verify first (10 min).** PLAN-V2:108 already attributes the empty PCS to the typed-in
  `poseidonMeta` ("fixed by deriving the meta from the real VK (WP-I1/WP-G4)"). If that holds at the
  current commit, the verdict is (a) and this card closes into R.1.
- **Do.** Determine which of: (a) the plan must emit the PCS computations (ties to D-P47's fixture
  re-export — the CS data may include them); or (b) those clauses belong to the `quotientLin` row's
  post. Report with evidence from the plan/Inv definitions.
- **Deliverable.** The verdict and which card it becomes. **If (a), it is part of D-P47, not separate
  work — say so.**
- **Does NOT need.** Proving anything; editing the plan.

---
### M.1 — Prove `blockContracts_of_valid` generically  **[READY — THE HINGE]**  **[MERGED 126c99e - OUTCOME (B): needs ALL 7 rows; narrowing moves nothing]**

SEM · PROOF · box 2.5 h · strongest · after T.2

- **Goal.** `R.BlockContractsAt product (· ≠ .quotientLin)` from `R.Valid` — the lemma C.1 sorried as
  `blockContracts_of_valid` at `Blocks.lean:152`.
- **Why this card exists / why it is first.** **Six roots have been reported and none has moved since
  C.2**, because the only route from a per-block lemma to the headline is this generic lemma. T.1 and
  T.2 proved TraceReturn's contract sorry-free (`tr_blockProgress: 0`, `tr_blockSound: 0`) and **it
  cannot reach the headline until M.1 lands.** Every per-block card is currently dead weight without
  it. This was added by the orchestrator after T.2; it was not in the original queue.
- **Needs.** §6 `BlockContractsAt` (`Blocks.lean:125`), `BlockSound`/`BlockProgress` (:92/:106);
  `T.2`'s TraceReturn pair as the one fully-proved exemplar; FP.0's `fp_finalPairing_contracts`
  (**note: it requires `R.Valid` AND `fpG2Slots R` — see the pending decision**); the M0.1 table.
- **Does NOT need.** Proving any new block contract; the deployment; the pairing; `Statements.lean`.
- **Do.** 1. State it and attempt the composition from the per-block contracts that exist. 2. **Report
  exactly which blocks it can close from what is already proved, and which it cannot** — M0.1 shows
  `pcs` is empty and `quotientLin` emits 122 of 6572 tokens, so `(· ≠ .quotientLin)` still demands
  `pcs`, which is vacuous, and `transcriptParser`/`lagrange`/`vkLoading` have no contract yet.
  3. If it cannot be closed, **narrow the predicate honestly** (e.g. to blocks with proved contracts)
  and report the cone delta — a narrower lemma that moves the headline cone beats a general one that
  stays sorried.
- **Accept.** **`cone_sorries lowering_equivalence_poseidon` measured before and after — it is 11.**
  **This is the first card since C.2 that can move it.** If it does not move, say so plainly and
  explain what still blocks it.
- **Stop if.** It needs a per-block contract that no card has proved — list the blocks and hand them
  back as cards. · `fpG2Slots` is required for the finalPairing row and no decision has landed.

---
### P.1 — Pairing-check algebra
ALG · PROOF · box 2 h · strongest · after FP.0

- **Goal.** Prove `fp_pairing_algebra`: under `Eip2537.Holds g1 g2codec product`, the precompile
  answer on the encoded final pair is `true` iff Lean's final check (`DualMSM.check`) holds.
- **Needs.** `DualMSM.check` (Msm.lean ~:222); `Eip2537.Holds` (`Assumptions/Eip2537.lean`);
  `E.g1.toEip`; `encG2`.
- **Verify first.** The exact names, with `#check`.
- **Does NOT need.** Yul, `Bridge`, runs, a pairing implementation, or the deployment. This is pure
  algebra.
- **Accept.** The lemma replaces FP.0's sorry, the cone count falls, and the axioms are printed.
- **Stop if.** The equivalence needs a property of `product` that `Holds` does not give. Report it as
  a PREMISE GAP.

### T.2 — `yul_step`, accepted by TraceReturn  **[MERGED e54fc7d - TraceReturn FULLY closed, both contracts sorry-free]**
SEM · PROOF · box 2.5 h · strongest · after T.1

- **Goal.** A tactic for straight-line code, builtins and `if` on concrete conditions.
- **Needs.** T.1's interface, the TraceReturn nodes, and the `Bridge` step lemmas.
- **Does NOT need.** Other blocks, `staticcall`, or field arithmetic.
- **Accept.** It closes TraceReturn `BlockSound` ∧ `BlockProgress` and the cone falls. A tactic that
  closes no node is not done.
- **T.1 RESULT + THE EXACT NODE LEFT.** `BlockProgress R .traceReturn` is **CLOSED**, sorry-free, in
  the new `Midfall/LoweringV2/Blocks/TraceReturn.lean` (`tr_blockProgress`; axioms
  `[propext, Classical.choice, Quot.sound]`, `#cone_sorries` on it = **0**). `BlockSound`'s
  **conjunct 1** is proved there as `tr_sound_clean`. So **T.2's remaining target is exactly
  `BlockSound R .traceReturn Snap H vkAddr (permissive (callsOf product)) g cd` conjunct 2** (the
  poisoned walk), and the only thing in it is step S6 below — hand it to T.5's `fail` step and wrap:
  `⟨fun V st a V' st' o => tr_sound_clean …, fun V st a V' st' o => S6 …⟩`.
  THE RECURRING STEPS, all in that file, reuse verbatim:
  **S1** `tr_slice` — the slice as a statement list; **S2** `tr_iszero_val` — invert a local builtin's
  `EvalExpr` through `stepOp` with `simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w]`, never
  through `dialect_deterministic`; **S3** `tr_guard_skip` + `Step.stmts_cons_inv` at every boundary
  (general in the `if` body — the clean path never enters it); **S4** `tr_mstore_step` / `tr_mstore_o`;
  **S5** `ret_step` / `tr_ret_o` + `readBytes_storeWord_one`; **S6** `fail_lookup` (proved, `rfl`) +
  `revertedOf_revert` — the hoisted-helper call, NOT yet composed into a walk (the open piece).
  TWO TRAPS, both measured, save T.2 the hour: (i) **the slice does not reduce by `simp`/`unfold`** —
  `unfold Inline.inlineScan` lands in the equation compiler's `brecOn` and `simp only [inlineScan.eq_1,
  eq_2]` cannot touch the partially-applied recursive argument; the route is `show` the inlined form →
  `rfl` against defs that NAME each stuck site (`trRetExpr`/`trErrExpr`/`trSuccExpr`) → rewrite the one
  lookup that must reduce (`consts_succ_none`); (ii) **do not put `classical` before a forward `Step`
  construction** — it swaps `DecidableEq D.Value` for `Classical.propDecidable` and the index
  unification fails with an opaque "type mismatch" on `Step.seqCons`; case-split only inside the
  inversion lemmas. THIRD: the `Bridge` view lemmas (`halted_of_view_eq`, `worldEq_of_view_eq`,
  `view_eq_of_worldEq_and_halt`) are NOT needed at this node — every step is a `Step` inversion on a
  run hypothesis, i.e. already the direction §6 states. C.2's wrong-direction finding does not bite
  a run-level walk; it bites only when an `Obs` has to be transported.

### T.4 — `staticcall` stepping, accepted by `ec_pairing_contract`
SEM · PROOF · box 2.5 h · strongest · after T.2

- **Goal.** Stepping through `permissive (callsOf product)` (`Bridge.lean:731`; `Statements` §3),
  plus `Holds` rewriting.
- **Needs.** `ec_pairing_contract` (FP.0), `Eip2537.Holds`, and T.2's tactic.
- **Does NOT need.** P.1's proof, a pairing implementation, or field-arithmetic simp sets.
- **Accept.** It closes `ec_pairing_contract`.
- **T.1 SIGNATURE — exact node: `ec_pairing_contract`** (FinalPairing.lean:314, sorry at :328). T.1
  closed TraceReturn instead (smaller), so this node is untouched, but the interface is now fixed and
  T.4 must be written against it. Steps to reuse: **S1** `tr_slice`'s three moves at
  `R.slice Partial.finalPairing` — the stuck-site defs must be added for FOUR more names
  (`PAIRING_RHS_MPTR`, `PAIRING_LHS_MPTR`, `G2_BASE_MPTR`, `NEG_S_G2_BASE_MPTR`) and each is read
  through an `trAddr`-shaped absorber (`trRet_eval_inv`) so the walk treats the site as opaque and
  the case split on `R.consts.lookup` happens once, in a lemma, not at every use. **S3** the
  `stmts_cons_inv` split. **S4/S5** the store/load inversions plus the INDEX TRICK: state the outcome
  IN the hypothesis (`… V' st' .normal`) so `cases` prunes the impossible `Step` rule for free —
  this is what makes a `staticcall` tractable, because `callOk` and `callHalt` are the same
  constructor family and naming the outcome picks one. **S6** `fail_lookup` is proved by `rfl`:
  `hoist` is a top-level `filterMap` and `lookupFun` short-circuits, so the FP.0 warning about an
  18-minute reduction over the inlined helper block does NOT apply to a function lookup — measured,
  the whole of `TraceReturn.lean` elaborates in 5 s. **THE Inv CHAIN, per FP.0's cost finding: do
  not try to derive `Inv .pcs → Inv .pairing`.** `fpPost`'s conditional clause is the budget; the
  glue applies it. What T.4 must actually produce inside that clause is
  `success = 1 → Inv .pairing`. **NOT MEASURED BY T.1 — the first route to try:** FP.0's timeout
  came from normalising the whole thirty-clause `&&` chain at once. Building `Inv .pairing` clause by
  clause from `Inv .pcs` (so only the two NEW clauses are ever elaborated) never asks the kernel to
  whnf the chain as a unit. T.1 has no measurement either way and promises nothing; try it under the
  60 s rule, and if it also times out report it as a PREMISE GAP rather than raising heartbeats.

### T.5 — Arithmetic and memory, accepted by FinalPairing
SEM · PROOF · box 2.5 h · strongest · after T.2, P.1

- **Goal.** `U256` `mulmod`/`addmod` ↔ `ZMod p` under `< r`, and memory read-over-write at layout
  addresses.
- **Needs.** FP.0's arithmetic and memory nodes, P.1, and T.4.
- **Does NOT need.** Other blocks.
- **Accept.** It closes FinalPairing `BlockSound` ∧ `BlockProgress`.
- **T.1 SIGNATURE — TWO exact nodes, and one of them is now shared with T.2.**
  (a) `fp_stmt_steps` (FinalPairing.lean:352, sorry at :358). Its whole content is ONE step: the
  guard `if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }` fires on `success = 0` and the hoisted
  `fail` reverts. T.1 proved the two facts it needs and nothing else is missing:
  `fail_lookup` (`lookupFun (R.scope c g) "fail" = some ⟨["sel"], [], [mstore(0, shl(224, sel)),
  revert(0,4)]⟩`, proved by `rfl`, TraceReturn.lean:396) and `revertedOf_revert` (:407). What T.1
  did NOT finish, and what blocks T.2's TraceReturn conjunct 2 identically, is the INVERSION of the
  call: `Step.callHalt` destructuring needs `cases hlookup` after `rw [fail_lookup R]`, then
  `Step.block` → `Step.stmts_cons_inv` over the two-statement body, then `tr_revert_halts`-style
  inversion of `revert(0,4)` (`simp only [Bridge.Dialect, builtinWithExternal, stepOp]` then
  `Option.some.injEq` / `BuiltinResult.halt.injEq`). The exact goal state T.1 stopped at, so the
  next card does not rediscover it: after `cases h with | exprStmtHalt hex | callHalt hargs hlookup
  hlen hbody` and the two `cases hargs`, `rw [fail_lookup R] at hlookup; cases hlookup` succeeds and
  `hbody : Step (R.scope c g) ((["sel"] := [e]) ++ bindZeros …) st (.stmt (.block failBody))
  (.sres V' st' .halt)`; the remaining work is `cases hbody with | block hstmts` and the two-statement
  split, where the seqCons branch needs `shl` proved non-halting (`trShl_ne_halts`-style: `cases` on
  `builtinHalt` then `simp [Bridge.Dialect, builtinWithExternal, stepOp]`). Three mechanical
  case-name iterations, no content. **T.2 and T.5 want the same lemma — write it once, name it
  `tr_fail_reverts`, and have both cite it.**
  (b) the arithmetic/memory table itself: `U256` ↔ `ZMod p` under `< r` and read-over-write at the
  layout addresses. T.1 measured nothing here, but it did settle the SHAPE of a memory-preservation
  lemma: `tr_mstore_step` returns the new state as an explicit record
  (`{ touchMemory st a.toNat 32 with memory := storeWord st.memory a.toNat 1 }`), so a
  read-over-write fact is a `readBytes`/`loadWord` equation over THAT term, and
  `readBytes_storeWord_one` (TraceReturn.lean:368, copied from v1 Partials.lean:1080 because V2 may
  not import it) is the template: reduce to `List.range` maps, `map_congr_range`, then `decide` the
  32-byte tail. Do NOT reach for `simp [storeWord]` on the whole thing — the `if p ≤ i ∧ i < p + 32`
  guard is what needs the per-index `hi : i < 32` fact.

### C.5 — Compose FinalPairing ; TraceReturn (calibration point 1)
SEM · PROOF · box 2 h · strongest · after T.4, T.5, C.2

- **Goal.** C.2's sequencing node for FinalPairing ; TraceReturn, starting from `Clean` at `.pcs`.
- **Needs.** The two block contracts (T.2, T.5) and C.2's sequencing lemma.
- **Does NOT need.** Other blocks, or deployment facts beyond the sorried `poseidon_valid`.
- **Accept.** The cone falls. Then the orchestrator runs **calibration point 1** (EXECUTION-V2 §6;
  PLAN-V2 §9.3).

### C.3 — Staged rejection skeleton
SEM · SKELETON · box 2 h · strongest · after C.2

- **Goal.** `Render.Rejects` from per-block rejection lemmas, modulo sorries, with each block's
  invariant and fault class.
- **Needs.** C.2's rejection step and the M0.1 table. The only excluded bad set is the
  `logup.rs:460` panic (`SoundSide`).
- **Does NOT need.** Block soundness or progress proofs.
- **Accept.** The cone lists the per-block lemmas, and the report has a requirements table.

### T.3 — Symbolic branches and loops
SEM · PROOF · box 2.5 h · strongest · after T.2

- **Goal.** Symbolic `if`/`switch` splits and loops with user invariants.
- **Needs.** The loop node T.1 named, and T.2's tactic.
- **Does NOT need.** The pairing or other blocks.
- **Accept.** It closes that loop node.
- **T.1 SIGNATURE — THE LOOP NODE IS `lagrange`, VIA `batch_invert`.** M0.1 measured it the only
  helper reaching a `for`-loop, direct or transitively; `lagrange` has 5 own loops and the call is
  `success := batch_invert(success, 26560, add(mptr_end,32), 26080, r)`. So T.3's exact target is
  `BlockSound R .lagrange` ∧ `BlockProgress R .lagrange` (the §6 shapes, Blocks.lean:92 / :106) at
  `R.slice Partial.lagrange` — NOT a helper-local statement, because §6 quantifies over slices of the
  CLOSED program and `batch_invert` is inside `R.helpers`, reached from the slice only as a
  `Step.callOk`/`callHalt` whose body runs in `R.scope`.
  What T.1 hands over unchanged: **S1** the slice-shape route (`show` + `rfl` against stuck-site defs
  + rewrite the lookups that must reduce) — at `lagrange` the stuck sites are the `mptr` constants
  and `26560`/`26080` arrive as literals already, so the inlining is the cheap part; **S2/S3** the
  local-builtin inversion and the `stmts_cons_inv` split; **S4/S5** the store/load inversions with the
  INDEX TRICK (state the outcome in the hypothesis so `cases` prunes); **S6** the hoisted-helper
  lookup, which is `rfl` and fast.
  What T.3 must ADD, and T.1 deliberately did not attempt: the loop rules. `Midfall/Yul/Contracts.lean`
  already inverts all seven loop constructors (`loopDone`, `loopCondHalt`, `loopStep`,
  `loopPostHalt`, `loopBreak`, `loopLeave`, `loopBodyHalt`) and its header records that
  `ExecLoopAll.countdown_or_halt` as sketched is NOT derivable — the extra arms are stated there
  instead, so the rule to use is the one in that file, not a two-hypothesis sketch. `batch_invert`'s
  two loops are a forward prefix pass and a backward recovery pass with `mptr`/`gp_mptr` cursors, and
  its `leave` statements are the arms the sketch could not discharge. Fuel: `lagrange` is the ONLY
  slice that needs it (M0.1), so the fuel argument belongs in T.3's per-slice contract and NOT in
  C.2's `slices_seq_*` (Blocks.lean:185-187 says exactly that).
  ONE MEASUREMENT THAT SAVES T.3 A WRONG TURN: the loop counter arithmetic is over `U256`
  (`BitVec 256`), and `lt(mptr, sub(mptr_end, 0x20))` cannot be discharged by `omega` — it needs
  `BitVec.ult_lemma`/`toNat` transport. T.1 hit the same wall one level down at
  `readBytes_storeWord_one` and solved it by reducing to `Nat` with a per-index `i < 32` fact rather
  than by deciding the whole vector expression.

---

## GEN — issued for the clause nodes C.4 names (when CORE is blocked; after C.5)

| ID | layer · type · box | deliverable | accept | after |
|---|---|---|---|---|
| G.1 | GEN · KAT · 1 h | `Instances/CodegenAgreement.lean` from `v2-bundle/probe/{CodegenProbe,CoverageProbe}.lean`: token offsets, per-region coverage, `constTableOf` = the pinned table. Update `kat_gate.py`'s `EXPECTED_KAT_*` deliberately | KATs green; a one-literal mutation of `abiGuardBlock` reddens | C.4 |
| G.2 | GEN · EMIT · 2.5 h | AccumulatorHelpers: 5 functions, 823 tokens. Dead code without an accumulator, so emit only, no contracts | the coverage row is equal | G.1 |
| G.3 | GEN · EMIT · 1 h | QuotientHelpers: `q_program_fail`, `q_pow5` (68 tokens) | the coverage row is equal | G.1 |
| G.4 | GEN · SKELETON · 2 h | The numerator region (6,384 tokens) split into template / model fields / compact-block lines; one EMIT child per part | children in QUEUE | G.1 |
| G.5 | GEN · PROBE · 1 h | Callee inventory of `plan.rs:235-329` (`#check` each Lean name; Rust LOC); one PORT child per missing callee | table plus children | C.4 |
| G.6 | GEN · PROBE · 1 h | The same for QRS:2000 `compact_quotient_computation_blocks` | table plus children | C.4 |

## Later epics — each starts with the SKELETON shown

**Family rule** (EXECUTION-V2 W3). When an epic has many similar cases (opcodes, gates, MSM terms),
its SKELETON delivers:

- **(a)** ONE shared case-split lemma, whose hypotheses are the per-case facts;
- **(b)** the complete per-case requirements table, computed by `#eval` on the deployed object.

PROOF tickets then fill table rows. Nothing is discovered one pass at a time.

| first ticket | epic | reuse candidates the SKELETON decides on |
|---|---|---|
| H.0 | AssemblyHelpers (contracts only for helpers called at the deployment) | — |
| B1.0 | Prefix + VkLoading. Includes the outcome KAT "fixture calldata passes the ABI guard and reaches the main block", reusing P-RUNLEG item 1's technique | `feToU256_frToRepr`; `extcodehash_of_deployment` (restate) |
| B2.0 | TranscriptParser. **Calibration point 2** after it | `keccakOf_invariant`, `RunCommitted_keccakOf` |
| B3.0 | Lagrange | — |
| B4.0 | Quotient, family rule. Table columns per opcode: instruction length, read bounds, constant-slot membership, write footprint, stack effect. **Calibration point 3** after the interpreter | the Qvm/QvmFold holes; the QVMARMS/READOFF/CONTSLOT results fill table cells |
| B5.0 | PCS (per MSM / batching section) | — |
| — | Children of C.3 (rejection), C.4 (clauses), G.5/G.6 (ports) | — |
| I.6 / I.7 | `entryFrame_inhabited`; `HypothesesInhabited poseidonRender poseidonProduct`, where `poseidonProduct` is `HoldsFinal`'s exhibited product | `HoldsFinal.holds_exhibited` |
| H.1 / E.1–E.4 | Close the headline (cone 0); the three Calldata holes; then `end_to_end` at the deployment | `calldata_roundtrip`, `calldata_canonical`, `repack_spec_of_decodeRust` |

## Legacy register map (39 entries at `15c0b3a`)

A reuse candidate gets a ticket only when a SKELETON puts it in the cone.

| class | entries | owner |
|---|---|---|
| **Reuse (17)** | `Calldata.lean`: `calldata_roundtrip`, `calldata_canonical`, `repack_spec_of_decodeRust` | E.1–E.3 |
| | `Snapshot.lean`: `snapshotOf_prepareMsgs`. `Bridge.lean`: `Run_worldEq_of_noWriters`, `rel_worldLocal` | C.2 decides |
| | `Bridge.lean`: `keccakOf_invariant`, `RunCommitted_keccakOf`. `VkDigest.lean`: `feToU256_frToRepr` | B2.0 / B1.0 decide |
| | `Qvm.lean`: `qvm_compile_correct_identity`, `qvm_compile_correct_certifier`, `qvm_compile_correct_program`, `qvm_validated_noBoundsFault`, `builder_segments_total` | B4.0 |
| | `QvmFold.lean`: `identityCorrespondence_of_bridge`, `quotientFold_matches_linearization`, `qvm_compile_correct_stream` | B4.0. Re-check D-P40's fourth hypothesis under W2 |
| **Retired with v1 (14)** — never ticketed | `Obligations.lean`: `lowering_equivalence_noAcc`, `end_to_end_acc_complete` | — |
| | `Partials.lean` ×11, stated over `Surface`: `vkLoading_spec`, `transcriptParser_spec`, `lagrange_spec`, `lagrange_progress_spec`, `quotientLin_spec`, `pcs_spec`, `finalPairing_spec`, `finalPairing_progress_spec`, `finalPairing_acc_spec`, `partialSound_of_alwaysReverts`, `partialProgress_not_of_alwaysReverts` | proof ideas only |
| | `Surface.lean`: `extcodehash_of_deployment` | B1.0 restates it if needed |
| **Parked (8)** | `AccEncoding.lean`: `toExec_fullyCollapsed`, `toExec_validFor`, `toExec_fixedScalarCount`. `Accumulator.lean`: `decodeAcc_injective`, `decodeAcc_encode_pointPair` | X-phase |
| | `Halo2/Spec/Piop.lean`: `accepts` (a sorried def). `Statements.lean`: `verifyMsgs_iff_spec`, `contractRef_noAcc` | X7 |
