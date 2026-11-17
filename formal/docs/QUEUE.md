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
- **Since PL.0 (2026-11-17) the plan is PLAN-V3** (D-P60). The order is the **V3 table** directly
  below: take its first READY row. A V2 card further down runs only where that table lists it;
  every other V2 card is marked MERGED INTO, SUPERSEDED or DONE.

## V3 — THE LIVE ORDER (PLAN-V3 §5; cut over by PL.0, 2026-11-17)

**How to use this table.** It is the queue: take the **first row whose status is READY**. A row is
READY when every card in its `after` column is merged, and the decision it names is signed (all of
D-P60–D-P69 are, `design.md`; their recorded **conditions** still gate the cards that name them).
When a card merges, change its status to `MERGED <hash>` and re-evaluate the rows that wait for it.

- **Card text.** Rows marked `PLAN-V3-cards` are briefed from `docs/plans/PLAN-V3-cards.md` (the
  heading `### <ID> —`); rows marked `V2 card below` from the card of that ID further down this
  file. Copy the card into the EXECUTION-V2 §3 brief, adding PLAN-V3 §7's EVIDENCE line.
- **Before briefing any card:** `bash docs/plans/V3-evidence/check.sh <area>` at the tip, then the
  card's NEEDS (EXECUTION-V2 §2.3). The evidence is a lead until it re-checks.
- **Milestone exit gates** are PLAN-V3 §5; a milestone is done when its gate prints the expected
  output at the tip. Rules W1–W15 bind (EXECUTION-V2 §5 and PLAN-V3 §4).
- **Statuses are set from `after` only.** A `PROOF` card about Yul is additionally not READY until
  W14's exhibit exists (T3.11), whatever this column says.
- **D-P71, D-P72 and D-P73 (signed 2026-11-17, `design.md`).** The goal is the generator theorem
  `lowering_correct`, for every render with `ValidV3`, widened to the IVC verifier
  (`lowering_correctW`); fixtures are tests. Card PL.G has run: rows marked "restated for every
  render" carry the new text in `PLAN-V3-cards.md`, their children are the lettered rows under
  them (area GEN-ROWS), and area WID is milestone M9. T3.4 is dropped, T3.6 is replaced by GEN.1,
  T3.3 and T3.11 are tests. D-P73 (signed the same day): the generator itself is certified —
  area CERT, milestone M10. **No PROOF card may state or prove anything at a fixture.** A missed
  threshold of PLAN-V3 §5 M5 goes to the human; per-fixture rows are not a fallback.

| # | ID | card | M | layer · type · box · model | after | status | source / note |
|---|---|---|---|---|---|---|---|
| 1 | **DG.0** | Make the gates green at the tip | M0 | INFRA · KAT · 1 h · Sonnet | — | **MERGED b4fd751** | PLAN-V3-cards |
| 2 | **DG.1** | Land the axiom gate | M0 | INFRA · PORT · 2 h · strongest | DG.0 | **MERGED 3a7c017** | PLAN-V3-cards |
| 3 | **DG.2** | Sorry register by declaration, from the environment | M0 | INFRA · PORT · 2.5 h · strongest | DG.1 | **MERGED 2a8ded8** | PLAN-V3-cards |
| 4 | **DG.6** | No registered sorry may be refuted | M0 | INFRA · KAT · 0.5 h · Sonnet | DG.2 | **READY** | PLAN-V3-cards |
| 5 | **PL.1** | W13: take the refuted sorries out of the tree | M0 | INFRA · PORT · 1.5 h · Sonnet | DG.6 | after DG.6 | PLAN-V3-cards; deletes poseidon_valid and its consumers (W13) |
| 6 | **DG.7** | CI that runs and can pass | M0 | INFRA · PROBE · 2 h · Sonnet | DG.0, DG.2 | **HELD - needs human OK to push/delete a branch on origin** | PLAN-V3-cards |
| 7 | **DG.8** | STATUS generated from the report | M0 | INFRA · PORT · 1 h · Sonnet | DG.2 | **MERGED e5516db** | PLAN-V3-cards |
| 8 | **ST.1** | Land the V3 staging module, its deployment file and the falsifiers (no frozen edit) | M0 | INFRA · STATEMENT · 1.5 h · Sonnet | — | READY | PLAN-V3-cards |
| 9 | **PL.0** | Cut over to PLAN-V3 | M0 | INFRA · DECISION · 0.5 h · orchestrator, no subagent | D-P60 is signed | DONE (this cut-over) | PLAN-V3-cards |
| 10 | **OBJ.17** | Name the target: fixture F1 | M0 | DECISION · DECISION · 0.5 h · orchestrator + human | — | READY | PLAN-V3-cards; docs edit applying D-P60's naming clause |
| 10a | **PL.G** | Restate the plan for the generator theorem (D-P71) | M0 | INFRA · DECISION · 2.5 h · the plan session with the human, no subagent | D-P71 is signed | DONE 2026-11-17 (plan session) | PLAN-V3-cards (area GEN) |
| 11 | **Q0.5** | Repair the non-vacuity gate + the RETURN_MPTR pin (one `Statements.lean` re-hash) | M0 | INFRA · PORT · strongest | F.1 | READY | V2 card below; D-P66 later strengthens it at ST.4 |
| 12 | **S.10** | Fix the stale `Valid` clause-count prose | M0 | INFRA · KAT · Sonnet | — | READY | V2 card below |
| 13 | **REF.D** | Reference-side decisions | M1 | DECISION · DECISION · 0.5 h · orchestrator + human | PL.0 or earlier | DONE — D-P61–63 signed | PLAN-V3-cards |
| 14 | **REF.11** | Exporter schema 2: test SRS with trapdoor, calldata, mutations, manifest | M1 | INFRA · PORT · 2.5 h · Sonnet | — | READY | PLAN-V3-cards |
| 15 | **OBJ.11** | Export the remaining generator inputs from Rust and re-export the dump | M1 | INFRA · PORT · 2 h · Sonnet | — (one Rust run with REF.11) | READY | PLAN-V3-cards |
| 16 | **REF.2** | Semantic equality on Rotation | M1 | ALG · PORT · 1 h · Sonnet | REF.D | READY | PLAN-V3-cards |
| 17 | **REF.1** | Multi-open grouping by allocation slot | M1 | ALG · PORT · 2.5 h · strongest | REF.D | READY | PLAN-V3-cards |
| 18 | **R.7** | = REF.3: fix `WellFormed.permutationCommitmentsMatch` (D-P59) | M1 | GEN · PORT · strongest | F.1 | READY | V2 card below |
| 19 | **REF.4** | A real, computable G1 codec on G₁z | M1 | ALG · PORT · 2 h · Sonnet | REF.D | READY | PLAN-V3-cards |
| 20 | **REF.5** | The deployment pairing by construction; retire the five D-P36a axioms | M1 | ALG · PORT · 1.5 h · Sonnet | REF.D | READY | PLAN-V3-cards |
| 21 | **REF.5g** | Gates follow the axiom removal | M1 | INFRA · KAT · 0.5 h · Sonnet | REF.5 | after REF.5 | PLAN-V3-cards |
| 22 | **REF.6** | Real key data at the deployment | M1 | ALG · PORT · 2 h · Sonnet | REF.4, REF.5 | after REF.4, REF.5 | PLAN-V3-cards |
| 23 | **R.6** | D-P46's three VK base pins (second `Statements.lean` re-hash); subsumed at ST.6 | M1 | INFRA · PORT · strongest | REF.6, Q0.5 | after REF.6, Q0.5 | V2 card below; R.4 is merged into REF.5–REF.6 |
| 24 | **REF.8** | The reference gate: Lean prepare reproduces Rust's final MSM | M1 | ALG · KAT · 2 h · Sonnet | REF.1, REF.2, REF.6 | after REF.1, REF.2, REF.6 | PLAN-V3-cards |
| 25 | **ST.18** | The real compressed codec on G1z | M1 | ALG · PROBE · 2 h · Sonnet | REF.4 | after REF.4 | PLAN-V3-cards |
| 26 | **REF.9** | fpSqrt recovers y from x and the sign bit | M1 | ALG · PROOF · 2.5 h · strongest | REF.4 | after REF.4 | PLAN-V3-cards |
| 27 | **REF.10** | The encoder-first compressed law | M1 | ALG · PROOF · 2.5 h · strongest | REF.9 | after REF.9 | PLAN-V3-cards |
| 28 | **REF.12** | Acceptance gate at the known trapdoor | M1 | ALG · KAT · 1.5 h · Sonnet | REF.8, REF.11 | after REF.8, REF.11 | PLAN-V3-cards |
| 29 | **OBJ.0** | Object decisions: the scope, and `ValidV3` | M2 | DECISION · DECISION · 0.5 h · orchestrator + human | PL.0 or earlier | DONE — D-P65, D-P67 signed | PLAN-V3-cards |
| 30 | **G1.4b** | Land the pcs block scopes + the 5 gate updates (D-P51) | M2 | GEN · EMIT · Sonnet | F.1 | READY | V2 card below; needs `t/G1.4` on origin (see its Needs) |
| 31 | **OBJ.1** | Land the Yul token parser with its round-trip KATs | M2 | INFRA · KAT · 1.5 h · Sonnet | — | READY | PLAN-V3-cards |
| 32 | **G1.1** | EMIT `AccumulatorHelpers` (823 tokens) — in the D-P65 batch | M2 | GEN · EMIT · Sonnet | G1.4b, OBJ.1 | after G1.4b, OBJ.1 | V2 card below; one commit with G1.2, OBJ.2, ST.3 (D-P65) |
| 33 | **G1.2** | EMIT `QuotientHelpers` (68 tokens) — in the D-P65 batch | M2 | GEN · EMIT · Sonnet | G1.4b, OBJ.1 | after G1.4b, OBJ.1 | V2 card below; one commit with G1.1, OBJ.2, ST.3 (D-P65) |
| 34 | **OBJ.2** | Complete the program: accumulator helpers, quotient region, pcs scopes | M2 | GEN · EMIT · 2.5 h · strongest | G1.4b, OBJ.1 | after G1.4b, OBJ.1 | PLAN-V3-cards; replaces G1.3; one commit with G1.1, G1.2, ST.3 (D-P65) |
| 35 | **ST.3** | Cut-over A: the block scope and the slices move | M2 | INFRA · PORT · 1.5 h · Sonnet | G1.4b, OBJ.1 | after G1.4b, OBJ.1 | PLAN-V3-cards; one commit with G1.1, G1.2, OBJ.2 (D-P65) |
| 36 | **ST.11** | prog_slices_decompV3 | M2 | GEN · PROOF · 2.5 h · strongest | ST.3, ST.6 | after ST.3, ST.6 | PLAN-V3-cards |
| 37 | **ST.12** | scans_prog_addr_indep | M2 | GEN · PROOF · 2 h · Sonnet | ST.5 | after ST.5 | PLAN-V3-cards |
| 38 | **OBJ.4** | One constants-coherence clause and its generic lookup lemmas | M2 | GEN · STATEMENT · 2 h · Sonnet | OBJ.2 | after OBJ.2 | PLAN-V3-cards |
| 39 | **OBJ.5** | Object fingerprint KAT | M2 | INFRA · KAT · 0.75 h · Sonnet | OBJ.2 | after OBJ.2 | PLAN-V3-cards |
| 40 | **OBJ.6** | Port the quotient glue of LoweringPlan::new | M2 | GEN · PORT · 2.5 h · strongest | — | READY | PLAN-V3-cards |
| 41 | **OBJ.7** | LoweringPlan.newFromVk, compactBlocksOf, generateAll | M2 | GEN · PORT · 2 h · strongest | OBJ.6 | after OBJ.6 | PLAN-V3-cards |
| 42 | **OBJ.16** | Probe: does the port reproduce the three other in-scope fixtures | M2 | GEN · PROBE · 1 h · Sonnet | OBJ.7 | after OBJ.7 | PLAN-V3-cards |
| 43 | **R.3** | Make `Valid.model` dischargeable (D-P56) | M2 | GEN · PROOF · strongest | F.1 | READY | V2 card below; OBJ.8 offers a second route |
| 44 | **RECON.1** | One `ValidV3`: reconcile the two typechecked texts | M3 | GEN · STATEMENT · 2.5 h · strongest | OBJ.7, ST.1 | after OBJ.7, ST.1 | PLAN-V3-cards; before ST.6 and D-P67 lands |
| 44b | **RECON.1b** | Rebase the generic evidence onto the single `ValidV3` | M3 | GEN · STATEMENT · 2.5 h · strongest | RECON.1 | after RECON.1 | PLAN-V3-cards; D-P71: rebases the generic evidence onto the single `ValidV3` |
| 45 | **RECON.2** | One composition: the four V3 obligations from the staged rows | M3 | SEM · SKELETON · 2.5 h · strongest | SIM.1, ST.1, RECON.1 | after SIM.1, ST.1, RECON.1 | PLAN-V3-cards; before SIM.2 and ST.5 |
| 46 | **ST.2** | Statement-surface decisions | M3 | DECISION · DECISION · 0.5 h · orchestrator + human | ST.1 | DONE — D-P64, D-P66 signed | PLAN-V3-cards |
| 47 | **SIM.0** | Block architecture and proof technology | M3 | DECISION · DECISION · 0.5 h · orchestrator + human | ST.1 | DONE — D-P68 signed | PLAN-V3-cards |
| 48 | **ST.4** | Cut-over B1: codec bundles, calldataOf, EndToEnd, EntryFrame, the headline, the gate | M3 | INFRA · PORT · 2.5 h · Sonnet | ST.3 | after ST.3 | PLAN-V3-cards |
| 49 | **ST.5** | Cut-over B2: the composition in Blocks.lean and the headline assembly | M3 | INFRA · PORT · 2.5 h · Sonnet | ST.4 | after ST.4 | PLAN-V3-cards |
| 50 | **ST.6** | Cut-over C: Render.Valid in its V3 text | M3 | GEN · PORT · 2.5 h · Sonnet | ST.4, RECON.1 | after ST.4, RECON.1 | PLAN-V3-cards |
| 51 | **OBJ.8** | State ValidV3 on the frozen surface and rebuild the fixture render from the generator | M3 | GEN · STATEMENT · 2.5 h · strongest | OBJ.0, ST.3, OBJ.4, OBJ.7 | after ST.3, OBJ.4, OBJ.7 | PLAN-V3-cards |
| 52 | **REF.7** | KeyAgrees: the key pins EnvAgrees lacks | M3 | ALG · STATEMENT · 1.5 h · Sonnet | REF.6 | after REF.6 | PLAN-V3-cards |
| 53 | **ST.15** | Deployment data: delta and the post-processed plan meta | M3 | GEN · PORT · 2 h · Sonnet | ST.6 | after ST.6 | PLAN-V3-cards |
| 54 | **OBJ.9** | Prove the decidable half of ValidV3 at the fixture | M3 | GEN · PROOF · 2 h · Sonnet | OBJ.8 | after OBJ.8 | PLAN-V3-cards |
| 55 | **ST.7** | The V3 clause table at poseidonRender | M3 | GEN · KAT · 2 h · Sonnet | ST.6 | after ST.6 | PLAN-V3-cards |
| 56 | **SIM.1** | Land the Lean staged view (section 1 of the scratch file) | M3 | ALG · PORT · 2 h · Sonnet | SIM.0 | READY | PLAN-V3-cards |
| 57 | **SIM.2** | Land StageInv, BlockSim, BlockProgS and the proved composition | M3 | INFRA · SKELETON · 2.5 h · strongest | SIM.1, RECON.2 | after SIM.1, RECON.2 | PLAN-V3-cards |
| 58 | **SIM.3** | Conjunct 3 without a snapshot: exit scan, TraceReturn exit, two outcomes | M3 | INFRA · PORT · 2 h · Sonnet | SIM.2 | after SIM.2 | PLAN-V3-cards |
| 59 | **SIM.7** | Migrate the proved rows and retire the old composition | M3 | SEM · PORT · 1.5 h · Sonnet | SIM.2 | after SIM.2 | PLAN-V3-cards |
| 60 | **SIM.8** | Restate the VkLoading row over StageInv | M3 | SEM · STATEMENT · 1.5 h · Sonnet | SIM.2 | after SIM.2 | PLAN-V3-cards |
| 61 | **ST.8** | TwoOutcomes: the Step-induction requirements table and the invariant statement | M3 | SEM · SKELETON · 2 h · strongest | ST.1 | after ST.1 | PLAN-V3-cards |
| 62 | **SIM.4** | Probe the exit-discipline meta-lemma | M3 | INFRA · PROBE · 1.5 h · Sonnet | SIM.3 | after SIM.3 | PLAN-V3-cards |
| 63 | **DG.3** | Pin the closure of the frozen statements | M3 | INFRA · DECISION · 1.5 h · strongest | DG.2 | after DG.2 | PLAN-V3-cards |
| 64 | **DG.4** | State `Done` for the generator theorem, with its refutation | M3 | INFRA · STATEMENT · 2 h · Sonnet | DG.1, ST.1, REF.8 | after DG.1, ST.1, REF.8 | PLAN-V3-cards; D-P71: restated for every render |
| 65 | **REF.13** | Probe: snapshotOf against Rust's intermediate values | M4 | ALG · PROBE · 1 h · Sonnet | REF.8 | after REF.8 | PLAN-V3-cards |
| 66 | **REF.14** | Probe: the calldata leg at the real codec | M4 | ALG · PROBE · 1 h · Sonnet | REF.6, REF.11 | after REF.6, REF.11 | PLAN-V3-cards |
| 67 | **DG.5** | The fixture calldata as a pure term | M4 | GEN · KAT · 1.5 h · Sonnet | DG.4 | after DG.4 | PLAN-V3-cards |
| 68 | **T3.11** | Executable exhibit as a KAT | M4 | INFRA · KAT · 1.5 h · Sonnet | T3.1 | after T3.1 | PLAN-V3-cards; D-P71: a test only (feeds W14), never a proof |
| 69 | **ST.14** | Deployment codec: the headline laws at poseidonE | M4 | ALG · PORT · 2 h · Sonnet | ST.4 | after ST.4 | PLAN-V3-cards |
| 70 | **ST.17** | HypothesesInhabitedV3: feasibility probe | M4 | ALG · PROBE · 2.5 h · strongest | ST.14 | after ST.14 | PLAN-V3-cards |
| 71 | **OBJ.10** | Split generateVk into base and reservation loop; data-level base payload | M4 | GEN · PORT · 2.5 h · Sonnet | OBJ.6 | after OBJ.6 | PLAN-V3-cards |
| 72 | **OBJ.12** | The artifact gate: both files byte for byte, nothing from the artifact | M4 | GEN · KAT · 2 h · Sonnet | OBJ.7, OBJ.10, OBJ.11 | after OBJ.7, OBJ.10, OBJ.11 | PLAN-V3-cards |
| 72a | **WID.2** | KAT: the ported partials render the IVC verifier byte for byte | M9 | GEN · KAT · 1 h · Sonnet | — | READY | PLAN-V3-cards (area WID); D-P72 |
| 72b | **WID.1** | Land the widening statements (no frozen edit) | M9 | INFRA · PORT · 2 h · Sonnet | ST.1, SIM.1, SIM.2 | after ST.1, SIM.1, SIM.2 | PLAN-V3-cards (area WID); D-P72 |
| 72c | **WID.3** | Exporter for the decider key (production SRS, no proof) | M9 | INFRA · PORT · 2.5 h · Sonnet | REF.11 | after REF.11 | PLAN-V3-cards (area WID); D-P72 |
| 72d | **WID.4** | Test fixture F2 under one seeded test SRS (D-P72 clauses 7, 8) | M9 | INFRA · PORT · 2.5 h · Sonnet | WID.3 | after WID.3 | PLAN-V3-cards (area WID); D-P72 |
| 72e | **GEN.2** | Clause table of the widened class on both test keys | M9 | INFRA · KAT · 1.5 h · Sonnet | WID.3, WID.1 | after WID.3, WID.1 | PLAN-V3-cards (area WID); D-P72 |
| 72f | **WID.5** | `generateAll` in accumulator and external-evaluator mode; three artifact gates | M9 | GEN · PORT · 2.5 h · strongest | OBJ.7, WID.3 | after OBJ.7, WID.3 | PLAN-V3-cards (area WID); D-P72 |
| 72g | **WID.6** | The evaluator as an object: `evalBodyOf` and its scans | M9 | GEN · STATEMENT · 2.5 h · strongest | WID.5, OBJ.2 | after WID.5, OBJ.2 | PLAN-V3-cards (area WID); D-P72 |
| 72g2 | **WID.7** | `ivcRender` and its validity by computation (test) | M9 | GEN · KAT · 2.5 h · strongest | WID.5, WID.6, WID.4, OBJ.9 | after WID.5, WID.6, WID.4, OBJ.9 | PLAN-V3-cards (area WID); D-P72: a test — the F2 analogue of OBJ.8/OBJ.9 |
| 72h | **WID.8** | Reference gate at F2: the accumulator, `alpha` and the two pairing inputs | M9 | ALG · KAT · 2.5 h · Sonnet | REF.10, WID.4, WID.1, WID.7 | after REF.10, WID.4, WID.1, WID.7 | PLAN-V3-cards (area WID); D-P72 |
| 72i | **WID.9** | Acceptance gate at F2 (test SRS) | M9 | ALG · KAT · 2 h · Sonnet | WID.8, REF.12, WID.5, WID.7 | after WID.8, REF.12, WID.5, WID.7 | PLAN-V3-cards (area WID); D-P72 |
| 73 | **T3.0** | Certificate-cost probe: choose how the kernel checks a symbolic execution | M5 | SEM · PROBE · 2.5 h · strongest | — | OPTIONAL (D-P71): off the path | PLAN-V3-cards; nothing depends on it: loops are not unrolled (GEN.3) |
| 73a | **GEN.0** | Land parametric execution: `vk_all_param` for every constant table and scope | M5 | SEM · PORT · 2 h · Sonnet | T3.1b | after T3.1b | PLAN-V3-cards (area GEN); D-P71: first of the M5 proof cards; may be pulled forward when blocked |
| 73b | **GEN.3** | Land the loop rule for a symbolic bound | M5 | SEM · PORT · 1.5 h · Sonnet | T3.1b | after T3.1b | PLAN-V3-cards (areas GEN, GEN-ROWS); may be pulled forward when blocked |
| 73c | **GEN.4** | The inliner distributes over a concatenation | M5 | GEN · PROOF · 2 h · strongest | — | READY | PLAN-V3-cards (areas GEN, GEN-ROWS); may be pulled forward when blocked |
| 73d | **GEN.5** | Land the generic row statements and their shared definitions | M5 | SEM · PORT · 2 h · Sonnet | RECON.3, RECON.1b | after RECON.3, RECON.1b | PLAN-V3-cards (area GEN-ROWS); every GEN-ROWS child waits for it |
| 74 | **T3.1** | Land the wp engine and the lawful executable Bridge dialect | M5 | SEM · PORT · 2 h · Sonnet | — | READY | PLAN-V3-cards; may be pulled forward when blocked |
| 74a | **T3.1b** | Land the `wp_run` tactic and the existence statements | M5 | SEM · PORT · 1.5 h · Sonnet | T3.1 | after T3.1 | PLAN-V3-cards (area GEN); lands `wp_run` (T3.4 is dropped); may be pulled forward when blocked |
| 75 | **T3.3** | Generated slice literals with pins | M5 | GEN · EMIT · 1.5 h · Sonnet | — | READY | PLAN-V3-cards; may be pulled forward when blocked; D-P71: a test only (feeds W14), never a proof |
| 76 | **T3.2** | Totality: wpSS_exists | M5 | SEM · PROOF · 2.5 h · strongest | T3.1b, GEN.0 | after T3.1b, GEN.0 | PLAN-V3-cards |
| 77 | **T3.4** | TraceReturn at the deployment (calibration A) | M5 | SEM · PROOF · 2 h · Sonnet | T3.1, T3.3 | DROPPED (D-P71) | PLAN-V3-cards; the row is proved for every `R` (`tr_blockSound`, `tr_blockProgress`); SIM.7 migrates it |
| 78 | **T3.5** | Word and memory layer, accepted by the vkLoading residue | M5 | ALG · PROOF · 2.5 h · strongest | T3.1 | after T3.1 | PLAN-V3-cards |
| 79 | **HLP.1** | Helper call summaries | M5 | SEM · SKELETON · 2 h · strongest | GEN.0, T3.5 | after GEN.0, T3.5 | PLAN-V3-cards; D-P71: restated for every render |
| 79a | **HLP.1.a** | The helper block of every render | M5 | GEN · PORT · 0.5 h · Sonnet | GEN.5 | after GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 79b | **HLP.1.b** | batch_invert: the forward pass | M5 | SEM · PROOF · 2.5 h · strongest | GEN.3, HLP.1.a, T3.9.a, GEN.5 | after GEN.3, HLP.1.a, T3.9.a, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 79c | **HLP.1.c** | batch_invert: the backward pass and the summary | M5 | SEM · STATEMENT · 2.5 h · strongest | HLP.1.b, T3.5, GEN.5 | after HLP.1.b, T3.5, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 80 | **T3.6** | vkLoading row at the deployment (calibration B) | M5 | SEM · PROOF · 2.5 h · strongest | T3.4, T3.5 | REPLACED BY GEN.1 (D-P71) | PLAN-V3-cards; do not run |
| 80a | **GEN.1** | The vkLoading row for every render (calibration B; replaces T3.6) | M5 | SEM · PROOF · 2.5 h · strongest | GEN.0, SIM.8, T3.2, T3.5, T3.11, OBJ.4, RECON.3 | after GEN.0, SIM.8, T3.2, T3.5, T3.11, OBJ.4, RECON.3 | PLAN-V3-cards (area GEN); D-P71: calibration B — a missed Accept line goes to the human |
| 81 | **T3.7** | Statement-level driver with cuts, accepted by the lagrange slice | M5 | SEM · PROOF · 2.5 h · strongest | T3.0, T3.1 | DROPPED (D-P71) | PLAN-V3-cards; its deliverable is a proof on the fixture's literal slice |
| 82 | **T3.8** | Field-arithmetic bridge, accepted by x_n = x^(2^k) | M5 | ALG · PROOF · 2 h · strongest | T3.5 | after T3.5 | PLAN-V3-cards |
| 83 | **T3.9** | Lagrange row for every render (calibration C) | M5 | SEM · PROOF · 2.5 h · strongest | GEN.1, GEN.3, HLP.1.c, T3.8, OBJ.4, T3.9.a–h, RECON.3 | after GEN.1, GEN.3, HLP.1.c, T3.8, OBJ.4, T3.9.a–h, RECON.3 | PLAN-V3-cards; D-P71: restated for every render |
| 83a | **T3.9.a** | Lagrange loop 1: k squarings (first use of the loop rule) | M5 | SEM · PROOF · 2 h · strongest | GEN.3, T3.8, GEN.5 | after GEN.3, T3.8, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83b | **T3.9.b** | Lagrange loop 2: the denominators | M5 | SEM · PROOF · 2 h · Sonnet | T3.9.a, T3.5, GEN.5 | after T3.9.a, T3.5, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83c | **T3.9.c** | Lagrange loop 3: inverses to Lagrange values | M5 | SEM · PROOF · 1.5 h · Sonnet | T3.9.b, GEN.5 | after T3.9.b, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83d | **T3.9.d** | Lagrange loop 4: l_blind | M5 | SEM · PROOF · 1 h · Sonnet | T3.9.a, GEN.5 | after T3.9.a, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83e | **T3.9.e** | Lagrange loop 5: the instance polynomial | M5 | SEM · PROOF · 1.5 h · Sonnet | T3.9.a, GEN.5 | after T3.9.a, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83f | **T3.9.g** | The Lagrange word relation is the verifier's Lagrange step | M5 | ALG · PROOF · 2.5 h · strongest | T3.8, GEN.5 | after T3.8, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 83g | **T3.9.h** | Lagrange: the poisoned half | M5 | SEM · PROOF · 1.5 h · Sonnet | HLP.1.c, T3.9.a–e, GEN.5 | after HLP.1.c, T3.9.a–e, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 84 | **ST.16** | BodyTotal: the requirements table | M5 | SEM · PROBE · 2 h · Sonnet | ST.5 | after ST.5 | PLAN-V3-cards |
| 85 | **T3.10** | Quotient numerator: route B only | M5 | SEM · STATEMENT · 2.5 h · strongest | OBJ.2, OBJ.14, OBJ.15 | after OBJ.2, OBJ.14, OBJ.15 | PLAN-V3-cards; D-P71: restated for every render |
| 86 | **SIM.6** | The prefix rows: prefix_sim and prefix_prog | M5 | SEM · PROOF · 2.5 h · strongest | SIM.2, RECON.2, OBJ.4, SIM.6.a–d, RECON.3 | after SIM.2, RECON.2, OBJ.4, SIM.6.a–d, RECON.3 | PLAN-V3-cards; D-P71: restated for every render |
| 86a | **SIM.6.a** | The model's shape flags under validity | M5 | GEN · PROOF · 1 h · strongest | RECON.1, GEN.5 | after RECON.1, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 86b | **SIM.6.b** | The static half of abiHeadOk | M5 | ALG · PROOF · 1 h · strongest | RECON.1, GEN.5 | after RECON.1, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 86c | **SIM.6.c** | The ABI guard | M5 | SEM · PROOF · 2 h · strongest | GEN.0, OBJ.4, SIM.6.b, GEN.5 | after GEN.0, OBJ.4, SIM.6.b, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 86d | **SIM.6.d** | Function definitions execute as a no-op | M5 | SEM · PROOF · 0.5 h · Sonnet | GEN.5 | after GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 87 | **ST.13** | runBody_mono | M5 | SEM · PROOF · 2 h · strongest | ST.5 | after ST.5 | PLAN-V3-cards |
| 87a | **RECON.3** | Move the row families to the widened shape (D-P72 clause 1) | M6/M9 | SEM · STATEMENT · 2.5 h · strongest | RECON.2, WID.1 | after RECON.2, WID.1 | PLAN-V3-cards (area WID); D-P72 clause 1: before any ROW card of M6 |
| 88 | **SIM.5** | Prove quiet_init | M6 | INFRA · PROOF · 2.5 h · strongest | SIM.4 | after SIM.4 | PLAN-V3-cards |
| 89 | **ST.9** | twoOutcomes_of_exitDiscipline: expressions and builtins | M6 | SEM · PROOF · 2.5 h · strongest | — (merged into SIM.4–SIM.5) | DO NOT RUN | PLAN-V3-cards; merged into SIM.4–SIM.5: do not run separately |
| 90 | **ST.10** | twoOutcomes_of_exitDiscipline: statements and the return tail | M6 | SEM · PROOF · 2.5 h · strongest | — (merged into SIM.5) | DO NOT RUN | PLAN-V3-cards; merged into SIM.5: do not run separately |
| 91 | **SIM.9** | leanStage coherence: the staged chain is a chain, with equal fields | M6 | ALG · PROOF · 2.5 h · strongest | SIM.1 | after SIM.1 | PLAN-V3-cards |
| 92 | **SIM.10** | xcript_total: the transcript-only prefix always exists on decodable calldata | M6 | ALG · PROOF · 2.5 h · strongest | SIM.1 | after SIM.1 | PLAN-V3-cards |
| 93 | **SIM.11** | The fault table as a gate and as a theorem statement | M6 | ALG · KAT · 2 h · Sonnet | SIM.1 | after SIM.1 | PLAN-V3-cards |
| 94 | **SIM.12** | PCS row decomposition: the decode-exists lemma | M6 | SEM · STATEMENT · 2 h · strongest | SIM.2, SIM.1 | after SIM.2, SIM.1 | PLAN-V3-cards |
| 95 | **ROW.TP** | TranscriptParser row for every render | M6 | SEM · SKELETON · 2.5 h · strongest | GEN.1, GEN.3, GEN.4, HLP.1, SIM.10, OBJ.4, RECON.3 | after GEN.1, GEN.3, GEN.4, HLP.1, SIM.10, OBJ.4, RECON.3 | PLAN-V3-cards; D-P71: restated for every render |
| 95a | **ROW.TP.1** | A walk loop is constant-free | M6 | GEN · PROOF · 1 h · Sonnet | GEN.4, GEN.5 | after GEN.4, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95b | **ROW.TP.2** | The walk loop, one lemma for six sections | M6 | SEM · PROOF · 2.5 h · strongest | GEN.3, ROW.TP.3, T3.5, GEN.5 | after GEN.3, ROW.TP.3, T3.5, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95c | **ROW.TP.6** | The parser's read schedule is the layout's slot list | M6 | ALG · PROOF · 2 h · strongest | OBJ.7, GEN.5 | after OBJ.7, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95d | **ROW.TP.7** | The parser computes TpPost | M6 | SEM · PROOF · 2.5 h · strongest | ROW.TP.1–6, GEN.1, GEN.5 | after ROW.TP.1–6, GEN.1, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95e | **ROW.TP.8** | TpPost is the staged boundary | M6 | ALG · PROOF · 2 h · strongest | SIM.10, GEN.5 | after SIM.10, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95f | **ROW.TP.9** | The parser: the poisoned half | M6 | SEM · PROOF · 1.5 h · Sonnet | ROW.TP.2, ROW.TP.4, GEN.5 | after ROW.TP.2, ROW.TP.4, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 95h | **ROW.TP.3** | The four parser helper summaries (`common_word`, `common_uncompressed_g1`, `squeeze_to`, `transcript_init`) | M6 | SEM · STATEMENT+PROOF · — · strongest | ROW.TP | ISSUED BY ROW.TP (step 1): no card until ROW.TP merges | — |
| 95i | **ROW.TP.4** | The three scalar loops (instance run, evals spill, q_evals run) | M6 | SEM · STATEMENT+PROOF · — · strongest | ROW.TP, GEN.3 | ISSUED BY ROW.TP (step 1): no card until ROW.TP merges | — |
| 95j | **ROW.TP.5** | The inlined parser refines the fold of `tpEvents` | M6 | SEM · STATEMENT+PROOF · — · strongest | ROW.TP, GEN.4 | ISSUED BY ROW.TP (step 2): no card until ROW.TP merges | — |
| 96 | **ROW.Q** | Quotient row for every render: route B | M6 | SEM · SKELETON · 2.5 h · strongest | T3.10, OBJ.2, OBJ.14, OBJ.15, SIM.2, RECON.3 | after T3.10, OBJ.2, OBJ.14, OBJ.15, SIM.2, RECON.3 | PLAN-V3-cards; D-P71: restated for every render; issues about 30 children (the card's Guidance lists them): only ROW.Q.1 and ROW.Q.6 are written |
| 96a | **ROW.Q.1** | The linearization loop | M6 | SEM · PROOF · 1.5 h · Sonnet | T3.9.a, GEN.5 | after T3.9.a, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 96b | **ROW.Q.6** | qvm_compile_correct_identity | M6 | ALG · PROOF · 2.5 h · strongest | GEN.5 | after GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 97 | **ROW.PCS** | PCS row for every render | M6 | SEM · SKELETON · 2.5 h · strongest | ROW.Q, SIM.12, T3.9, GEN.4, the M1 exit gate, RECON.3 | after ROW.Q, SIM.12, T3.9, GEN.4, the M1 exit gate, RECON.3 | PLAN-V3-cards; D-P71: restated for every render; issues the children for PCS blocks 1, 3–6, the coverage invariant and `scalar_inv`: only ROW.PCS.2 and ROW.PCS.9 are written |
| 97a | **ROW.PCS.2** | PCS block 2: the x1 power table | M6 | SEM · PROOF · 1.5 h · Sonnet | T3.9.b, GEN.5 | after T3.9.b, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 97b | **ROW.PCS.9** | A raw walk with valid frames decodes | M6 | ALG · PROOF · 1 h · Sonnet | SIM.1, GEN.5 | after SIM.1, GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 98 | **ROW.FP** | FinalPairing row for every render | M6 | SEM · PROOF · 2.5 h · strongest | ROW.PCS, PL.1, REF.5, HLP.1, RECON.1, RECON.3 | after ROW.PCS, PL.1, REF.5, HLP.1, RECON.1, RECON.3 | PLAN-V3-cards; D-P71: restated for every render |
| 99 | **TOT.1** | Totality for every render: `TotalV3 R product` | M6 | SEM · PROOF · 2.5 h · strongest | ROW.FP, T3.2, GEN.3 (existence form), SIM.6, RECON.1, RECON.3 | after ROW.FP, T3.2, GEN.3 (existence form), SIM.6, RECON.1, RECON.3 | PLAN-V3-cards; D-P71: restated for every render |
| 99a | **TOT.1.a** | A program without gas() runs the same under every gas oracle | M6 | SEM · PROOF · 2.5 h · strongest | GEN.5 | after GEN.5 | PLAN-V3-cards (area GEN-ROWS) |
| 99m | **WID.11** | The two ALG obligations and the limb lemma | M9 | ALG · PROOF · 2.5 h · strongest | WID.1 | after WID.1 | PLAN-V3-cards (area WID); D-P72 |
| 99n | **WID.12** | Call summaries for the six accumulator helpers | M9 | SEM · PROOF · 2.5 h · strongest | HLP.1, WID.11, OBJ.2, OBJ.13 | after HLP.1, WID.11, OBJ.2, OBJ.13 | PLAN-V3-cards (area WID); D-P72 |
| 99o | **WID.13** | vkLoading row, accumulator arm: establish `AccInv` | M9 | SEM · SKELETON · 2.5 h · strongest | GEN.1, RECON.3, WID.12 | after GEN.1, RECON.3, WID.12 | PLAN-V3-cards (area WID); D-P72 |
| 99p | **WID.14** | Frame clauses: three rows do not write the accumulator slots | M9 | SEM · PROOF · 2 h · strongest | ROW.TP, T3.9, ROW.PCS, RECON.3 | after ROW.TP, T3.9, ROW.PCS, RECON.3 | PLAN-V3-cards (area WID); D-P72 |
| 99q | **WID.15** | finalPairing row, batching arm: `BatchedInv` | M9 | SEM · SKELETON · 2.5 h · strongest | ROW.FP, RECON.3, WID.11 | after ROW.FP, RECON.3, WID.11 | PLAN-V3-cards (area WID); D-P72 |
| 99r | **WID.16** | quotientLin row, external arm | M9 | SEM · SKELETON · 2.5 h · strongest | ROW.Q, RECON.3, WID.6 | after ROW.Q, RECON.3, WID.6 | PLAN-V3-cards (area WID); D-P72 |
| 99s | **WID.17** | The evaluator body: shape, agreement, totality | M9 | SEM · SKELETON · 2.5 h · strongest | ROW.Q, WID.6 | after ROW.Q, WID.6 | PLAN-V3-cards (area WID); D-P72 |
| 99t | **WID.19** | Totality, widened | M9 | SEM · PROOF · 2.5 h · strongest | TOT.1, WID.16, WID.17 | after TOT.1, WID.16, WID.17 | PLAN-V3-cards (area WID); D-P72 |
| 100 | **PL.H** | The headline: `lowering_correct` | M7 | INFRA · PROOF · 1 h · strongest | every ROW card and its children, TOT.1, SIM.5, SIM.6, ST.11–ST.13, RECON.2 | after every ROW card and its children, TOT.1, SIM.5, SIM.6, ST.11–ST.13, RECON.2 | PLAN-V3-cards; D-P71: restated for every render |
| 100a | **WID.H** | The widened headline and the definition of done | M9 | INFRA · PROOF · 1.5 h · strongest | PL.H, RECON.3, WID.13–WID.19, WID.9 | after PL.H, RECON.3, WID.13–WID.19, WID.9 | PLAN-V3-cards (area WID); D-P72 |
| 101 | **DG.9** | The DONE commit | M7 | INFRA · KAT · 1 h · Sonnet | DG.3, DG.4, DG.5, DG.6, DG.7, DG.8, PL.H, WID.H, CERT.H | after DG.3, DG.4, DG.5, DG.6, DG.7, DG.8, PL.H, WID.H, CERT.H | PLAN-V3-cards; D-P71: restated for every render |
| 102 | **PL.E** | End to end and the English statement | M8 | ALG · PROOF · 2.5 h · strongest | PL.H | after PL.H | PLAN-V3-cards; D-P71: restated for every render |
| 103 | **OBJ.13** | Structured emitter for AccumulatorHelpers | M9 | GEN · EMIT · 2 h · Sonnet | OBJ.2 | after OBJ.2 | PLAN-V3-cards; M9: needed by WID.12 (the accumulator helpers as a tree) |
| 104 | **OBJ.14** | Structured emitter for QuotientHelpers | M6 | GEN · EMIT · 0.75 h · Sonnet | OBJ.2 | after OBJ.2 | PLAN-V3-cards; M6: needed by ROW.Q (D-P71: no tree emitter for the numerator helpers) |
| 105 | **OBJ.15** | Structured emitter for the QVM interpreter template | M6 | GEN · EMIT · 2.5 h · Sonnet | OBJ.2 | after OBJ.2 | PLAN-V3-cards; M6: needed by ROW.Q (D-P71: the interpreter template as a tree) |
| 106 | **CERT.0** | Land the certified statement (no frozen edit) | M10 | GEN · PORT · 2 h · Sonnet | OBJ.7, ST.1 | after OBJ.7, ST.1 | PLAN-V3-cards (area CERT); D-P73 |
| 107 | **CERT.1** | Probe the two suspects: `v3_planMeta` and `v3_cdBound` | M10 | GEN · PROBE · 2.5 h · strongest | CERT.0 | after CERT.0 | PLAN-V3-cards (area CERT); D-P73 |
| 108 | **CERT.2** | Route A: the generator prints the tree | M10 | GEN · PORT · 2.5 h · strongest | OBJ.13, OBJ.14, OBJ.15, ROW.Q, OBJ.7, CERT.0 | after OBJ.13, OBJ.14, OBJ.15, ROW.Q, OBJ.7, CERT.0 | PLAN-V3-cards (area CERT); D-P73 |
| 109 | **CERT.3** | `Constants.sol` is printed from the constant table | M10 | GEN · PORT · 2 h · Sonnet | CERT.0 | after CERT.0 | PLAN-V3-cards (area CERT); D-P73 |
| 110 | **CERT.4** | Family (a): what the generator's own validation checks | M10 | GEN · PROOF · 2.5 h · strongest | CERT.0 | after CERT.0 | PLAN-V3-cards (area CERT); D-P73 |
| 111 | **CERT.5** | Family (b): syntactic invariants of the tree emitters | M10 | GEN · SKELETON · 2.5 h · strongest | CERT.0, GEN.4, the tree emitter complete (as CERT.2) | after CERT.0, GEN.4, the tree emitter complete (as CERT.2) | PLAN-V3-cards (area CERT); D-P73 |
| 112 | **CERT.6** | Family (c): builder lemmas | M10 | GEN · PROOF · 2.5 h · strongest | CERT.0, CERT.3 | after CERT.0, CERT.3 | PLAN-V3-cards (area CERT); D-P73 |
| 113 | **CERT.7** | Family (c)+(d): the payload and the key, through the codec laws | M10 | GEN · PROOF · 2.5 h · strongest | CERT.6, REF.5 | after CERT.6, REF.5 | PLAN-V3-cards (area CERT); D-P73 |
| 114 | **CERT.8** | `generate` runs on a real key | M10 | GEN · PORT · 2.5 h · strongest | CERT.0, REF.5g | after CERT.0, REF.5g | PLAN-V3-cards (area CERT); D-P73 |
| 115 | **CERT.H** | `generator_correct`, and the definition of done | M10 | INFRA · PROOF · 1.5 h · strongest | CERT.1–CERT.8, PL.H, WID.H | after CERT.1–CERT.8, PL.H, WID.H | PLAN-V3-cards (area CERT); D-P73 |

### Leads for the cards above (PLAN-V3 §10.1, verified at `4e18c65`; re-check before relying on one)

| card | flag |
|---|---|
| **G1.1–G1.3 batch** | **Do not merge G1.2 without the scope repair** (D-P65, signed: the batch's frozen diff is `Program.lean` and `Statements.lean`): with `q_program_fail` / `q_pow5` in the `.quotientLin` slice, `prog_slices_decomp`'s second conjunct (`Blocks.lean:224`) is false and the frozen `Render.scope` (`Statements.lean:109`, outside D-P52) lacks both functions. G1.3's 895 / 5,489 split is measured as 5,431 / 953 |
| **R.4** | MERGED INTO REF.4–REF.6 at PL.0 (D-P62, signed: constructed pairing, the SRS point as data, no G2 axiom). Do not add D-P55's G2 axiom |
| **R.4b** | A *computable* G1 decoder exists and equals the `Classical.choose` one on the EIP half; prefer it |
| **R.5** | The non-determinism is `OsRng` in `blind_quotient_limbs` (`proofs/src/plonk/prover.rs:126`), baseline code: D-P58's fallback (3) applies |
| **R.8**, **R.9** | Frozen `Valid.circuitMeta` forces `numPointSets = 0`; a faithful plan has 3. Exporting or proving more cannot close clauses 1 and 2 together |
| **T.2b** | A verified `wp` engine proves the literal-slice TraceReturn fact in 13 lines; land it rather than write a tactic. The closed-slice form is still to do |
| **T.3**, **S.5**, **S.6** | The engine's kernel check on the lagrange loop is not bounded yet; do not apply D-P57's hand-proof fallback on that ground before PLAN-V3 card T3.0 has measured it |
| every card | The tip (`4e18c65`) still fails `kat_gate.py`: 1397 annotated checks against a pinned 1393, and two `-- expect TRUE` annotations that can never match `true` (`DeployedProfile.lean:857`, `PoseidonCoherence.lean:502`). The sorry register is back in sync since F.1. Card **DG.0** below fixes it and needs no decision |

### DG.1 — Make the two repack gates honest, and the fixture bundle consistent  **[READY — BLOCKS §6 DONE]**

INFRA · KAT · box 1 h · Sonnet · after DG.0 · **relates to R.5**

- **Goal.** `checks.sh` exits 0 **for the right reason.** Two defects, both found by DG.0:
  1. **`Calldata.lean:916-917` pass vacuously when the dump directory is absent.** A gate that returns
     `true` because its input is missing is not a gate. **Add a presence guard so an absent artifact is
     NOT-COMPUTABLE (or an explicit skip the report names), never a silent `true`.**
  2. **The tracked dump directory is mixed-vintage** (orchestrator-verified: `proof.bin`/`instance.be`
     Nov 17, `calldata.bin` Oct 29, `git status` clean ⇒ committed state). **Resolve to ONE consistent
     vintage.** Because the prover's blinding is non-deterministic, a fresh full regeneration cannot
     reproduce the committed `calldata.bin` — so **the honest options are: revert the dump to the
     Oct 29 set, or track a consistent `proof.bin`+`calldata.bin` pair produced together.** **Name
     which, and say what it costs D.3's `trace.json` pins.**
- **Needs.** DG.0's report; `Calldata.lean:916-917`; the dump dir listing; `check_baseline_pins.py`
  (already reports the dump `proof.bin` has moved); R.5.
- **Does NOT need.** Any proof; the emitter cards; block rows; frozen files.
- **Accept.** `bash scripts/checks.sh` **exits 0**; the two gates either genuinely pass on a consistent
  bundle or are reported as NOT-COMPUTABLE — **not silently true.** Cone unchanged at 9.
- **Stop if.** Making them green requires editing an `expect` value or deleting an artifact to exploit
  the vacuity. **That is the failure mode, not the fix.**

---
### DG.0 — Make the gates green at the tip  **[READY — no decision needed; run before the next PROOF card]**  **[V3: row 1 of the V3 table]**
INFRA · KAT · box 1 h · Sonnet · after —

- **Goal.** `bash scripts/checks.sh` exits 0 at the tip.
- **Needs.** `scripts/kat_gate.py:113` (`EXPECTED_KAT_TOTAL = 1393`; the tree has 1397 since
  `2041977`); `Midfall/Instances/DeployedProfile.lean:857` and
  `Midfall/Instances/PoseidonCoherence.lean:502` (annotations spelled `-- expect TRUE`; the gate
  compares case-sensitively and the values print `true`).
- **Does NOT need.** Any new gate, any proof, PLAN-V3 or any of its decisions.
- **Do.**
  1. Re-measure: `python3 scripts/kat_gate.py` (fails in about a second on the total).
  2. Correct the two annotations to `-- expect true` (keep the prose after it).
  3. Move `EXPECTED_KAT_TOTAL` (and `EXPECTED_KAT_FILES` if it moved) to the measured values, and
     say in the commit which commit added the four gates.
  4. One full `kat_gate.py` run; then `checks.sh`.
- **Deliverable.** The two annotation fixes and the pin; nothing else.
- **Accept.** `bash scripts/checks.sh` exits 0; the KAT report names 1397 gates compared.
- **Stop if.** A gate other than the two annotations fails once the total is corrected: report it
  with its file and line, do not adjust its expectation.

### PL.0 — Cut over to PLAN-V3  **[DONE 2026-11-17 — tag `formal/v2-cutover`; the V3 table above is the result]**
INFRA · DECISION · box 0.5 h · orchestrator, no subagent · after D-P60 is signed in `design.md`

- **Goal.** This queue, `STATUS.md` and `PLAN.md` point at PLAN-V3, with nothing proved deleted and
  no card in flight lost.
- **Card.** Full text: `docs/plans/PLAN-V3-cards.md`, card PL.0. Mapping of every live card
  (CONTINUES / MERGED INTO / SUPERSEDED): PLAN-V3 §10.2. Order of the V3 cards: PLAN-V3 §5, the
  table "Every card, by milestone".
- **READY.** `design.md` D-P60 carries the W2 sign-off line (2026-11-17, after `53bf8c1`).

---

# V2 CARDS (kept for their text; each one is marked by PL.0. Run a V2 card only where the V3 table lists it)

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

### Q0.5 — Repair the non-vacuity gate (R-72) + land the `RETURN_MPTR` pin — ONE `Statements.lean` re-hash  **[READY after F.1 — D-P45 (amended) and D-P48 signed off 2026-11-17]**  **[V3: CONTINUES — row 11; D-P66 strengthens it at ST.4]**

INFRA · PORT · box 1.5 h · strongest · after F.1

- **Goal.** One deliberate re-hash of frozen `Statements.lean` carrying three signed-off changes:
  1. `HypothesesInhabited` gains D-P45's **amended** conjuncts (decode ∧ parse ∧ replay, plus
     `G1CodecLaws`; exact text in `design.md` D-P45). **NOT `LeanAccepts`, NOT a run-existence
     conjunct** — D-P45 records why.
  2. `Render.Valid` gains D-P48's `returnMptr : ∃ m, R.consts.lookup "RETURN_MPTR" = some m` as the
     last clause.
  3. The stale `Valid` docstring (`Statements.lean:179-181`, F.2-G4: "refutes six of the original
     eleven") is rewritten **without a count**: point to `poseidonRender_notValid` and the clause
     table in `Instances/PoseidonValid.lean`, so it cannot go stale again.
- **Needs.** `HypothesesInhabited` at `Statements.lean:317` (line at `4b525ef`); `Valid` at `:182`;
  S.9 (`fece4c7`) as the precedent for adding a `Valid` clause; F.2's `trRetMptr` deployment proof
  (`RETURN_MPTR = some 4096`).
- **Verify first.** R-72's reproducer is **not in the tree**: it lived in `/tmp/q04/probe1.lean`,
  which is gone, and survives only as prose (REVIEW.md:2991-3005: `sel_nondecode`, `gate_weak`,
  `no_accept_at_gate_cd`).
- **Do.**
  1. Re-create the three reproducer theorems **in the tree** (an `Instances/` or `Tests/` file, W5)
     and confirm `gate_weak` type-checks against the CURRENT gate. The falsifier must hold before the
     fix.
  2. Apply changes 1–3 to `Statements.lean` and re-hash `Frozen.sha256` in the same commit. The commit
     message shows the frozen diff.
  3. Add the `returnMptr` discharge to `Instances/PoseidonValid.lean` (a 14th clause row, PROVED).
  4. Repair any anonymous-constructor `Render.Valid` terms as S.9 did.
  5. Update PLAN-V2:355 with one sentence on what the gate now certifies, and its stated limit.
- **Not this card.**
  - `hR : R.Valid` in the headline: REJECTED, D-P54.
  - Discharging the new gate at the deployment: that needs R.4b's G1 decode, and is a later card.
  - D-P46's base pins: they get their own re-hash after R.4 (R.6).
- **Accept.**
  - `gate_weak` type-checks before step 2 and NO LONGER type-checks after it; commands and output go
    in the report. **The repair must have teeth, not just compile.**
  - `#print axioms` of the reproducers is in the report.
  - `Frozen.sha256` all OK after the re-hash, with exactly one line changed.
  - `verify.sh --quick` green.
  - `cone_sorries lowering_equivalence_poseidon` before and after (expected unchanged; report the
    number).
- **Stop if.**
  - Any change would alter a statement other than these three.
  - `G1CodecLaws poseidonE.g1` turns out to be FALSE (not merely unproved) at the deployment's codec:
    the gate would then be undischargeable. Report; do not drop the conjunct.

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
are generic progress only. F.2 and R.2 are DONE. R.1 is DONE (`2041977`, run as "F.1" ahead of
D-P47 sign-off). **All drafted decisions were signed off on 2026-11-17 (D-P45–D-P48, D-P53–D-P59;
`design.md`).** The clause-by-clause route to `poseidon_valid`, each after F.1:
- clause 1 `circuitMeta`: R.9
- clauses 2/3: R.8, an export-first probe for WP-G4
- clause 4 `model`: R.3
- clause 6 `codegen`: G1.4b, then the G1.1–G1.3 batch
- clause 9 `supported`: R.7
- the D-P46 pins: R.4, then R.6
- clause 14 `returnMptr`: Q0.5
- fixture provenance: R.5

### F.2 — The deployment table: every hypothesis of the headline route, decided once  **[MERGED d2f7b61 - 7 PROVED / 4 REFUTED / 2 OPEN; corrected F.1/R.1 clause 1]**
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

**F.2 MEASURED AT `2ec80db` — the table is 7 PROVED / 4 REFUTED / 2 OPEN over 13 clauses** (REFUTED: 2
`layout`, 3 `invariants`, 6 `codegen`, 9 `supported`; SORRY: 4 `model`; **OPEN at the Prop level: 1
`circuitMeta` — F.2-G1**; PROVED: 5, 7, 8, 10, 11, 12, 13). `poseidonRender_notValid` stays PROVED (runs
through clause 2); `cone_sorries lowering_equivalence_poseidon` = **11**, measured, unchanged. Pins:
`trRetMptr poseidonRender` **PROVED** (`RETURN_MPTR = some 4096`, sorry-free — D-P48 is sign-off-ready);
`g1BaseWords` and `fpG2Slots`'s **first** conjunct TRUE under the published-generator identification,
`fpG2Slots`'s **second** conjunct FALSE (VERIFY-FIRST answered: NOT-COMPUTABLE as typed, REFUTED under the
only computable reading — R.4's premise stands, and it is the `sG2Prepared := poseidonSG2` half alone);
`G1CodecLaws poseidonRender.E.g1` **PROVED** sorry-free; the D-P45 accepting-calldata witness is
**NOT-COMPUTABLE** (F.2-G3). New gaps, one line each, each with its reproducer:

| gap | reproducer at `2ec80db` (a file importing `Midfall.Instances.PoseidonValid`, then `lake env lean`) | printed output |
|---|---|---|
| **F.2-G1** `Valid.circuitMeta`'s PROVED is a **Bool** decision: the Prop form is a theorem nowhere in the tree, and neither bridge that would transport it exists | `#check (inferInstance : DecidableEq ConstraintSystemMeta)` · `#check (inferInstance : LawfulBEq ConstraintSystemMeta)` · `theorem t : ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 = .ok poseidonPlanV2.meta_ := by native_decide` · same `:= rfl` | `failed to synthesize instance DecidableEq ConstraintSystemMeta` · `failed to synthesize instance LawfulBEq ConstraintSystemMeta` · `failed to synthesize Decidable (…)` · `Not a definitional equality: … is not definitionally equal to Except.ok poseidonPlanV2.meta_`. **It is dischargeable in 8 lines** with one `native_decide` on `poseidonMetaDerived?.isOk` (sorry-free, no frozen edit, no new instance): `show poseidonMetaDerived? = .ok poseidonMeta; cases h : poseidonMetaDerived?` — ok arm `rw [poseidonMeta, h]`, error arm killed by the `isOk` decision. Land it in `Instances/PoseidonValid.lean` |
| **F.2-G2** `fpG2Slots` is **two gaps, not one**: the `G2_BASE` half already holds at the payload; only `NEG_S_G2` fails, so D-P46's "hold all three until Gap B" is over-cautious for the G1 and G2_BASE pins | `theorem a : vkG2Words poseidonPv vkG2BaseSlot = poseidonEncG2 (g2foldExp 1) := by native_decide` · `theorem b : vkG2Words poseidonPv vkNegSG2BaseSlot ≠ poseidonEncG2 ((g2foldExp 1)⁻¹) := by native_decide` · `#eval (vkG2Words poseidonPv vkNegSG2BaseSlot).toList.drop 16 \|>.take 6` · `#eval (poseidonEncG2 ((g2foldExp 1)⁻¹)).toList.drop 16 \|>.take 6` | both PROVED, no `sorryAx`. Printed: payload `G2_BASE[16..21] = [2,74,162,178,240,143]` **=** `encG2 H2`; payload `NEG_S_G2[16..21] = [5,10,194,124,53,39]` against `encG2(−H2) = [2,74,162,178,240,143]`. As literally typed neither side decides: `native_decide` on `fpG2Slots poseidonRender` → `failed to synthesize Decidable`; on `poseidonRender.E.g1.toEip bls12_381Pairing.g₁` → `failed to compile definition, consider marking it as 'noncomputable' because it depends on 'instGroupBlsGT', which is 'noncomputable'` |
| **F.2-G3** the **D-P45 witness does not exist and cannot be computed**: no term of `HypothesesInhabited poseidonRender _` is in the tree and its decode conjunct is not evaluable at the render's codec | `grep -rn HypothesesInhabited Midfall` (the def plus two docstrings, no term) · `#eval (decodeCalldata (p := blsR) poseidonRender.plan.proofLayout 1 poseidonRender.E.g1 cd).isSome` · same at the proxy codec `g1CodecZ` | `lean.dependsOnNoncomputable: … depends on 'poseidonRender'` / `… depends on 'g1CodecZ', which is 'noncomputable'`. The blocker is the codec, not the layout: `check3_codec_decodes_no_compressed_point` is sorry-free (`∀ b, poseidonE.g1.ofCompressed? b = none`) and `g1zOfEip?` is a `Classical.choose` — a discrete log as literally typed. Blocks D-P45's teeth AND `end_to_end`; same class as Gap B |
| **F.2-G4** **frozen §2's docstring now misstates the measurement**: `Statements.lean:179-181` says "C.4 still refutes six of the original eleven clauses at `poseidonRender`"; at this commit four are refuted and `slots` is a theorem | `#print axioms Midfall.Instances.PoseidonValid.poseidonValid_slots` | no `sorryAx` (clause 8 PROVED at the render, ten `native_decide` uses). Frozen file, so the fix is a decision plus a `Frozen.sha256` re-hash, not an edit |
| **F.2-G5** `PoseidonValid.lean:132` prints a **stale** deciding value for clause 2 ("derived proofLen 1792 against the plan's 4320") while the same file's own defs say 4224/4320 and its header says 4224 | `#eval deciding_layout_derivedProofLen` · `#eval deciding_layout_planProofLen` | `4224` · `4320`. The 1792 is D.3's number at `protocolPlanDefault`, superseded by F.1. Not a soundness problem (`deciding_layout` is a sorry-free Prop-level refutation), but the file claims "every value in it is printed by this file" |

### R.2 — WP-G1 region inventory (`Valid.codegen`)  **[DONE 8c5f237 — the four regions close the gap exactly; EMIT cards G1.1–G1.4]**
GEN · PROBE · box 1 h · Sonnet · after nothing

- **Goal.** The list of regions the `GenAst` emitter does not produce yet, so WP-G1 (PLAN-V2:232) can
  be cut into EMIT cards. C.4 measured 3156 AST tokens against 10433 printed, first difference at
  index 1333.
- **Does NOT need.** Writing any emitter; Yul semantics.
- **Deliverable.** One row per missing region: its name, printed token count (`#eval`) and WP-G1 item;
  one EMIT child card per region in QUEUE.md (EXECUTION-V2 §4 EMIT row).
- **Accept.** The token counts account for the measured gap (10433 − 3156), or the residue is
  explained.

**R.2 RESULT — the WP-G1 region inventory, re-measured at `93fbe23` (branch `t/R.2`).**

Route: the COMPUTABLE proxies `poseidonM` / `poseidonPv` (`Instances/PoseidonValid.lean:90-91`,
pinned to `poseidonRender` by the `rfl` theorems at :93-101 — `poseidonRender` itself is
noncomputable, so nothing that projects from it reaches `#eval`). AST side
`yulTokens (YulSemantics.EVM.print (mainAsmRaw poseidonPv))`; text side `mainAssemblyTokens
poseidonM`. Probe `R2probe.lean` (scratch, `lake env lean`, 8 s, no emitter edit). **No emitter
file was touched; only this file changed.**

**Headline: AST 6761, text 14054, gap 7293, first divergence at token 1333.**

| region of `mainAssemblyText` | AST | text | missing | equal | WP-G1 item (PLAN-V2:232) |
|---|---|---|---|---|---|
| `assemblyHelpers` | 1303 | 1303 | 0 | yes | closed by P-HELPERS |
| `accumulatorHelpers` | 0 | 823 | **823** | **no** | item 1 → **G1.1** |
| `traceAndGasHelpers` | 0 | 0 | 0 | yes | item 1's second include — **vacuous**, finding 1 |
| `vkLoading` | 223 | 223 | 0 | yes | closed |
| `transcriptProofParser` | 923 | 923 | 0 | yes | closed |
| `lagrange` | 501 | 501 | 0 | yes | closed |
| `quotientAndLinearization` | 120 | 6572 | **6452** | **no** | item 2 |
| — `renderQuotientHelpers` | 0 | 68 | 68 | no | item 2a → **G1.2** |
| — `renderQuotientNumeratorBlock` | 0 | 6384 | 6384 | no | item 2b → **G1.3** |
| — the linearization scope | 120 | 120 | 0 | yes | closed (`emitQuotientLin`) |
| `pcs` | 3605 | 3623 | **18** | **no** | not a WP-G1 item — finding 3 → **G1.4** |
| `finalPairing` | 22 | 22 | 0 | yes | closed |
| `traceReturn` | 23 | 23 | 0 | yes | closed |
| shell: `vhMainAssemblyOpen` −6 (30) + `vhAfterTraceAndGas` (10) + closing `}` (1) | 41 | 41 | 0 | yes | closed |
| `includeGlue` × 10 and `verifierDirectSection` (`quotientDirect = none`) | 0 | 0 | 0 | yes | nothing to emit |
| **TOTAL** | **6761** | **14054** | **7293** | | |

**The arithmetic closes, and it closes token-for-token, not just in length.**
823 + 68 + 6384 + 18 = **7293** = 14054 − 6761. Stronger: the measured excision — the text with
`accumulatorHelpers`, `renderQuotientHelpers` and `renderQuotientNumeratorBlock` removed and the
`pcs` region replaced by the emitted one — is **equal to the AST token list** (`excised == ast`
prints `true`, length 6761). So there is no residue and no fifth gap hiding in the middle: the four
rows above are the whole of clause 6.

**Delta from the two earlier figures.** C.4's 3156 / 10433 (gap 7277) and F.2's 6761 / 14054 (gap
7293). F.2 reproduces exactly here. The move is one row: R.1/F.1's `cs.json` re-export gave
`poseidonPlanV2.meta_` a real protocol, so `computationsAst` now returns 8 blocks / 225 statements
(3605 tokens) where it returned none, and the text's pcs region grew from 2 tokens (an empty
`{ }`) to 3623. Under this table C.4's gap decomposes as 823 + 68 + 6384 + 2 = 7277 — same four
rows, only pcs moved (+16 of the +16 gap change; AST +3605, text +3621). The first-divergence index
1333 is unchanged, because it sits before the pcs region.

**Four findings.**

1. **`traceAndGasHelpers` is not a missing region: it renders 0 tokens at this deployment.**
   `renderTraceAndGasHelpers` (`VerifierPartials.lean:2361`) is an `if ctx.trace` and the render
   model has `trace = false` (as has `gasCheckpoints`). `Program.lean:94-97` and PLAN-V2:233
   name "the accumulator / trace helper includes" as one gap; the trace half is vacuous for every
   gas render, so **clause 6 should be restated as three includes, not four**, and no EMIT card is
   issued for it. It becomes real only for a `trace = true` render, which nothing in the cone asks for.
2. **`validate_public_accumulator` is not in the deployed `AccumulatorHelpers` render** — measured:
   5 functions, none of them that one (it appears only at `expectedHasAccumulator := true`, gate 59,
   `GenAst.lean:2848`). So G1.1 does NOT discharge `Partials.lean:1764`
   `closureNamedExceptions = [(.vkLoading, "validate_public_accumulator")]`; that exception belongs
   to an accumulator render and must survive G1.1 green.
3. **The pcs row is neither a missing region nor the circuit gap.** Its 3571 non-brace tokens are
   already **identical** to the text's; the 18-token residue is exactly 9 block-scope brace pairs —
   the region's own wrapper plus the 8 blocks of the `computationsAst` partition — that
   `emitPcsFromPlan`'s `blocks.flatten` (`GenAstDispatch.lean:134`) discards. Consequence for
   WP-G1: PLAN-V2:236's acceptance ("coverage table all-equal except PCS; `codegenAgrees` false only
   because of PCS") is now the WRONG target. With G1.1–G1.4 the measured excision says
   `codegenAgrees poseidonPv poseidonM = true`, i.e. **clause 6 becomes PROVED, not closer**, and
   `Valid.codegen` (`LoweringV2/Statements.lean:200`) stops being a root cause **without** WP-G4 or
   WP-G3. WP-G1 should be re-scoped to these four cards.
4. **Only one of the four cards touches a frozen file.** The `accumulatorHelpers` splice goes in
   `mainAsmRaw` (`Program.lean:99`), and `Program.lean` is sha256-pinned
   (`Midfall/LoweringV2/Frozen.sha256`, checked at `scripts/checks.sh:27`) — so G1.1 needs one
   deliberate re-hash. G1.2–G1.4 land entirely in `GenAstDispatch.lean` (the `quotientLin` arm and
   `emitPcsFromPlan`), which is NOT pinned: the quotient regions belong in `emitPartial`, not in
   `mainAsmRaw`, because `emitSlices` folds `emitPartial` and `emitSlices_eq` (`ProgramLemmas.lean:35`)
   stays a one-`simp` proof either way. The frozen KNOWN-GAP docstring at `Program.lean:92-97` is what
   the set retires — and it names four includes where three are real.

**Premises in the R.2 card that did not survive re-measurement.** (a) "clause 6 — one of the 7 root
causes blocking `poseidon_valid`": F.2's own table at this commit is 4 REFUTED (2, 3, 6, 9) + 1 SORRY
(4) + 1 OPEN (1) over 13 clauses, so clause 6 is one of **four** refutations — but it is the only one
of the four closable inside Lean without a Rust port (2 and 3 need WP-G4, 9 is a v1 `Exec/VerifyingKey`
defect). (b) "the accumulator / trace helper includes": the trace half renders 0 tokens (finding 1).
(c) PLAN-V2:236's "coverage table all-equal except PCS": PCS is 18 brace tokens from equal (finding 3).
(d) The card's 3156 / 10433 is superseded by 6761 / 14054, which is what reproduces here.

### F.1 — Prove the sequencing glue (`slices_seq_sound`, `slices_seq_progress`)  **[READY — RUN NEXT]**  **[V3: MERGED f588ba2 — both lemmas proved, headline cone 11 → 9; SIM.2 reuses the technique]**
> Moved ahead of the G1 cards by the human (2026-11-17): it is the only READY card expected to move the
> headline cone, and it needs no decision. S.3 merged `d0aabba`.
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

---
### G1.4b — Land the pcs block scopes + the 5 gate updates from D-P51  **[READY after F.1 — D-P51 signed off 2026-11-17; needs `t/G1.4` pushed, see Needs]**  **[V3: CONTINUES — M2]**

GEN · EMIT · box 1 h · Sonnet · after G1.4 (stopped), needs D-P51 signed off

- **Goal.** Apply the preserved emitter change AND the five gate/witness updates so the tree is green
  with the corrected scoping.
- **Needs.** **`/tmp/g14-patch/0001-WIP-G1.4-*.patch`** and branch **`t/G1.4` (`3a5b5ce`)** hold the
  verified emitter change — **apply, do not re-derive**. Sites: `GenAstDispatch.lean:280`, `:404`,
  `:505`; `SurfaceFixture.plantPcsPlaceholderLengthVisible_ok:2032`; `PoseidonValid.lean:292`
  (6761 → 6779).
- **Not reachable at `2cad8cc` (human, 2026-11-17).** `t/G1.4` is not on origin and `/tmp/g14-patch` is
  not in the tree. First push `t/G1.4` and copy the patch to `formal/docs/plans/G1-evidence/`
  (EXECUTION-V2 W5: evidence a card relies on is landed, never left in `/tmp`). If neither exists any
  more, STOP: the change must be re-derived, and that is a new card.
- **Do.** 1. Apply the emitter change. 2. Update the five sites **exactly as G1.4 proposed** (`:404`
  already evaluated TRUE). 3. **For each updated gate, state in one line what it was protecting and
  show that protection still holds — stronger or equal, never weaker.** 4. If any gate turns out to
  guard a real property rather than the flattening, **STOP on that one and report**.
- **Accept.** `verify.sh --quick` **green** (the whole point); pcs row prints `equal true`;
  **all 10 GenAstDispatch gates true**, RunEmitted 9/9, DeployedProfile 15/15, D.1 9/9, PoseidonEnv
  18/18; `Frozen.sha256` all OK; **`cone_sorries lowering_equivalence_poseidon` before and after —
  expect 11 → 11, since clause 6 needs G1.1–G1.3 too. Report the number, not a hope.**
- **Stop if.** D-P51 is not signed off · any gate cannot be made stronger-or-equal · the build is still
  red after the five updates (then the analysis is wrong — report, do not hunt).
- **Does NOT need.** G1.1–G1.3; `computationsAst` changes; contracts; frozen files.

---
### ⚠ SEQUENCING COLLISION + RE-SCOPE from G1.2b (probe, `9c1c9a5`, nothing edited)

**Evidence location (human, 2026-11-17).** The G1 reproducers (`/tmp/g11`–`/tmp/g14`, `/tmp/g12-patch`,
`/tmp/g14-patch`) and branch `t/G1.4` are not on origin. Land them under
`formal/docs/plans/G1-evidence/` and push `t/G1.4` before any G1 card relies on them (W5).

**Signed off: D-P52 (2026-11-17).** G1.1–G1.3 run as ONE batch with one `Program.lean` re-hash, after
G1.4b, under D-P52's conditions (`design.md`).

**SITE FOUND: `mainAsmRaw (pv) (m)` — gate 23 AVOIDED, one frozen re-hash (`Program.lean`) unavoidable.
⇒ G1.1 + G1.2 + G1.3 must be BATCHED into that single re-hash.**

- **Flag is a DIRECT `Model` field** (printed: `#eval poseidonM.quotientPow5Helper = true`) — no
  `PartialCtx` hop, no new `PlanView` field, no duplicate fact. Good news.
- **`mainAsmRaw` has FOUR callers, not one** (`Program.lean:116`, `:133`, `:192`;
  `PoseidonValid.lean:292`) — **all already have `m` in scope**, so the change is mechanical but not
  one-line. **My 'one call site' claim was false.**
- **`sliceOf` is a COMPANION, not the site.** Splicing there avoids gate 23 but **cannot close
  `codegenAgrees`** (printed: `sliceOf pv m .quotientLin` = 122 = `emitPartial pv .quotientLin` —
  parallel views, not nested). **AND `sliceOf`'s `.quotientLin` body MUST gain the same region, or
  `prog_slices_decomp` (`Blocks.lean:220`, currently sorry) becomes FALSE, not merely unproved.**
- **⚠ COLLISION — sequence these.** `PoseidonValid.lean:292` pins the AST total. **G1.4b moves it
  6761 → 6779; the G1.1/G1.2/G1.3 batch moves it to 6829.** Two cards edit the same line with
  different values. **Run G1.4b FIRST, then the batch recomputes from 6779** — or the batch will
  silently redden G1.4b's witness.
- **limb7 verdict: include it in G1.2 as one extra conjunct, do not defer** — but the failure is NOT
  silent (at a limb7 render `codegenAgrees` goes FALSE, a red gate). Text side is already covered by
  gate 64 `perturb_quotientHelperFlags_ok`. **Add the AST-side hypothesis**
  `&& m.quotientLimb7Helper = false && m.quotientWideLimb7Helper = false` with a docstring naming the
  un-emitted arm.
- **G1.2 alone does NOT flip clause 6** (printed `codegenAgrees = false` with the splice in, 6829 ≠
  14054). Clause 6 needs all four regions.
- **QUEUE R.2 finding 4 is FALSE for G1.2/G1.3** — it says they land entirely in the unpinned
  `GenAstDispatch.lean` and the regions belong in `emitPartial`. **`emitPartial` cannot read the
  flags; the regions belong in `mainAsmRaw`, a FROZEN file.** That is what makes the re-hash shared.

### G1.1 — EMIT the `AccumulatorHelpers` include (823 tokens)  **[READY after G1.4b — one batch with G1.2/G1.3 under D-P52 (single `Program.lean` re-hash)]**  **[V3: CONTINUES — M2, in the D-P65 batch with G1.2, OBJ.2, ST.3]**
GEN · EMIT · box 2 h · Sonnet · after R.2 (nothing else; parallel with G1.2–G1.4)

- **Goal.** `GenAst` emits the 823-token region `mainAssemblyText` puts between `assemblyHelpers`
  and `traceAndGasHelpers` and `mainAsmRaw` does not, so the `accumulatorHelpers` row reads
  `equal true`.
- **Needs** (measured at `93fbe23` by R.2).
  - the region: `(partsOf poseidonM).accumulatorHelpers` = `renderAccumulatorHelpers
    (partialCtxOfVerifier poseidonM)` — 823 tokens, 165 lines, **exactly 5 complete function
    definitions** and no other tokens: `load_acc_coord_shifted` 202, `is_bls_p_minus_one` 31,
    `check_acc_coord_packing` 151, `load_acc_coord` 165, `load_acc_point` 274 (sum = 823);
  - the splice site: `Program.lean:99`, between `GenAst.emitHelpers pv` and `mainLocals`;
  - the comparator machinery already in the tree: `GenAst.renderFunction` (GenAst.lean:1325),
    `GenAst.sliceIsComplete` (:1302), `yulTokens`, `YulSemantics.EVM.print`; the constructor
    helpers `yfun/ylet/yset/yexpr/yif/yop/yvar/ylit` (GenAst.lean:185-225);
  - the two contract constants the region reads: `BLS_P_HI`, `BLS_P_MINUS_ONE_LO`. They stay as
    `yvar` uses: `mainAsmRaw` is the UN-inlined block (`constTableOf` substitutes at §3).
- **Does NOT need.** `validate_public_accumulator` (finding 2 — not in this render); any block
  contract, `BlockRow`, or Yul semantics; an accumulator render; `Statements.lean`; touching
  `emitHelpers` (see Do 2); `Frozen.sha256` (the orchestrator re-hashes).
- **Do.**
  1. `def GenAst.emitAccumulatorHelpers (pv : PlanView) : Block Op` — the 5 definitions in the
     template's order, each built with the constructor helpers (the pattern of
     `emitTranscriptHelpers`, GenAst.lean:388, and of gates 37/42).
  2. Splice it into `mainAsmRaw` between `emitHelpers` and `mainLocals`. **Do not append to
     `emitHelpers`:** `helpersOf` (`Program.lean:120-121`) reuses that block for the per-block
     contracts, and gate 51 `emitHelpersOrder_matchesTemplate_ok` (GenAst.lean:2582) pins its
     function names to the AssemblyHelpers render — 8 definitions, and adding 5 reddens it.
  3. One token gate per function (`renderFunction … nm` prints to the same tokens as the emitted
     def — the shape of gates 3/4), one whole-region gate, and one perturbation gate that a
     one-literal change of any of the 5 defs reddens (D-P23).
  4. Re-run the R.2 probe: the row goes `equal true` and the gap falls 7293 → 6470.
- **Deliverable.** `GenAst.emitAccumulatorHelpers`; the `mainAsmRaw` splice; 5 + 1 + 1 gates with
  their `#eval` lines; the updated counts in `deciding_codegen_witness`
  (`Instances/PoseidonValid.lean:291`) and in that file's header table.
- **Accept.** `(yulTokens (EVM.print (GenAst.emitAccumulatorHelpers poseidonPv))).drop 1 |>.dropLast
  == yulTokens ((partsOf poseidonM).accumulatorHelpers)` prints `true`; a one-literal mutation of
  any of the 5 defs reddens it; `codegenAgrees poseidonPv poseidonM` is still `false` (G1.2–G1.4
  open); gate 51, gate 59 and `closureNamedExceptions` still green; `verify.sh --quick` green;
  `git status` shows no `.lean` change outside `GenAst`/`GenAstDispatch`/`Program`/`PoseidonValid`.
- **Stop if.** A function slice is not `sliceIsComplete`; a value the region interpolates is not a
  `PlanView`/`Model` field (PREMISE GAP — name the value); > 2.5 h.
- **Reproducer.** `/tmp/g11/p.lean`, then `cd formal && lake env lean /tmp/g11/p.lean` (~8 s):

          import Midfall.Instances.PoseidonValid
          import Midfall.LoweringV2.Program
          open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
          open Midfall.LoweringV2 Midfall.Lowering YulSemantics YulSemantics.EVM
          -- text side, runs today: expect 823
          #eval (yulTokens ((partsOf poseidonM).accumulatorHelpers)).length
          -- function inventory, runs today: expect the 5 names above
          #eval Midfall.Lowering.GenAst.renderFunctionNames ((partsOf poseidonM).accumulatorHelpers)
          -- AST side, runs once this card lands: expect true
          -- #eval ((yulTokens (EVM.print (GenAst.emitAccumulatorHelpers poseidonPv))).drop 1).dropLast
          --         == yulTokens ((partsOf poseidonM).accumulatorHelpers)

### G1.2 — EMIT `QuotientHelpers`: `q_program_fail` and `q_pow5` (68 tokens)  **[READY after G1.4b — batch with G1.1, D-P52]**  **[STOPPED CLEAN 5a8585e - 3 constraints unsatisfiable; splice site unresolved, see G1.2b]**  **[V3: CONTINUES — M2, in the D-P65 batch with G1.1, OBJ.2, ST.3]**
GEN · EMIT · box 0.75 h · Sonnet · after R.2; **a prerequisite of G1.3** (both definitions are
called ONLY from the numerator block — measured: neither `q_program_fail(` nor `q_pow5(` occurs in
any other region of the main block)

- **Goal.** Emit the first of the two `quotient_numerator` includes that `mainAssemblyText` puts in
  front of the linearization scope, so the `renderQuotientHelpers` row reads `equal true`.
- **Needs.**
  - the region: `renderQuotientHelpers (partialCtxOfVerifier poseidonM)` — 68 tokens, 31 lines,
    exactly 2 definitions: `q_program_fail` 23 tokens (4 lines), `q_pow5` 45 tokens (5 lines);
  - the flag that selects the second one: `ctx.quotientPow5Helper = true` at this render
    (`quotientLimb7Helper = false`, `quotientWideLimb7Helper = false`, so those two arms render
    nothing — the emitter must read the flags, not hard-code the pair);
  - the splice: inside the `quotientLin` arm of `GenAst.emitPartial`
    (`GenAstDispatch.lean:193`), PREPENDED to `emitQuotientLin pv`, so `emitSlices` keeps its
    seven-arm shape and `emitSlices_eq` (`ProgramLemmas.lean:35`, proved by one `simp`) still
    discharges;
  - `FR_MODULUS` is the only contract constant the region reads (measured); `mulmod` × 3, `mstore` × 1.
- **Does NOT need.** `renderQuotientNumeratorBlock` (G1.3); the limb7 / wide-limb7 arms (dead at
  this render — emit the flag test, not the bodies); any contract or proof; `GenAstQuotient.lean`.
- **Do.**
  1. `def GenAst.emitQuotientHelpers (pv : PlanView) : Block Op` reading the two flags off the plan
     view (PREMISE GAP if `quotientPow5Helper` is not reachable from `PlanView`/`Model`: name the
     field, do not type the literal).
  2. Prepend it in the `quotientLin` arm; re-run the R.2 probe: the `quotientAndLinearization` row
     goes 120 → 188 and the gap falls 6470 → 6402.
  3. Gates: one per function against `renderFunction`, one whole-region, one perturbation.
- **Deliverable.** `GenAst.emitQuotientHelpers`, the `emitPartial` arm edit, 4 gates, the R.2 table
  row updated in this file.
- **Accept.** the whole-region KAT prints `true`; a one-literal mutation reddens; gates 24/25/26/27/28
  (the existing `emitQuotientLin` gates) still green; `verify.sh --quick` green.
- **Stop if.** The 68 tokens do not decompose as 23 + 45 at this commit; > 1 h.
- **Reproducer.** `/tmp/g12/p.lean` (same imports and `open` line as G1.1's):

          #eval (yulTokens (renderQuotientHelpers (partialCtxOfVerifier poseidonM))).length  -- 68
          #eval Midfall.Lowering.GenAst.renderFunctionNames
                 (renderQuotientHelpers (partialCtxOfVerifier poseidonM))                     -- [q_program_fail, q_pow5]
          #eval (partialCtxOfVerifier poseidonM).quotientPow5Helper                            -- true

### G1.2b — Find the real splice site for the quotient helpers  **[DONE 9c1c9a5 - SITE FOUND: mainAsmRaw(pv,m); gate 23 avoided; batch G1.1+G1.2+G1.3]**

GEN · PROBE · box 0.5 h · Sonnet · after G1.2 (stopped clean)

- **Goal.** Determine where the quotient helper flags can actually be read, given that **G1.2's
  recommended repair (c) rests on a false premise.**
- **THE FALSE PREMISE, caught by the orchestrator at `5a8585e`.** G1.2 states that `mainAsmRaw` and
  `sliceOf` (`Program.lean:98`/`:125`) **both take `(pv, m)`**, so the flag is readable with no new
  duplicate fact. **Measured: `def mainAsmRaw (pv : PlanView) : YulBlock` — it takes `pv` ONLY.** The
  flags are `Halo2Verifier`/`Model` fields (`Models.lean:764-766`), so **`m` is not in scope at
  `mainAsmRaw` at all.** Widening it is a frozen `Program.lean` change with a signature blast radius,
  not the free splice (c) was sold as. **`sliceOf` does take `(pv) (m)` — so half the claim holds.**
- **Do.** For each candidate site — `sliceOf`, `mainAsmRaw`, `emitPartial`, and any call path from
  `DeployedProfile`/`PoseidonV2` that already has a `Model` in hand — print whether `m` (or the flags)
  is in scope, and what a splice there would cost in call sites and frozen re-hashes. **One row per
  site, each with the printed signature that decides it.**
- **Accept.** A table of candidate splice sites with **printed signatures**, and a recommendation that
  states its own blast radius honestly (call sites touched, frozen files re-hashed, gates at risk).
  **If no site has `m` without a signature change, say that plainly — it means repair (a) or a new
  shape, and G1.1/G1.2/G1.3 all wait on it.**
- **Also settle, from G1.2's second finding:** the limb7/wide arms interpolate
  `limb7YulCoeffs`/`wideLimb7YulCoeffs` (6 entries, 203 tokens each) and are **not Bool-selectable in
  any meaningful sense**. **`emit the flag test, not the bodies` would be a silent lie for a limb7
  render.** The honest shape G1.2 proposed: `q_program_fail` unconditional + `q_pow5` on its flag +
  the limb7 family as a **named un-emitted arm with a gate asserting that a true flag makes the region
  unequal.** Decide whether that gate is required here or deferred.
- **Does NOT need.** Implementing any splice; G1.1/G1.3; frozen edits.
- **Reproducer preserved:** `/tmp/g12-patch/G1.2-PROPOSAL.md` + probes `/tmp/g12/p.lean`, `p3.lean`,
  `p5.lean` (~8 s each). **G1.2's emitter is verified working and flag-parametric — the row prints
  `equal true`, and teeth are proven 4/4 (a one-literal mutation reddens both the token row and
  `stmtsBeq`). Only the splice SITE is unresolved.**

---
### G1.2c — Land the splice WITH D-P65's scope repair  **[READY — supersedes the G1.2 frozen half]**

GEN · EMIT · box 1.5 h · strongest · after G1.2a (`0144b8e`) · **carries D-P65**

- **Decision I have made (the card asked):** **re-scope rather than defer.** D-P65 is APPROVED and
  PLAN-V3 states *"Do not merge G1.2 without the scope repair."* Folding the splice into G1.3 would
  leave `emitQuotientHelpersAt` as dead code for a card and would defer an approved repair for no
  benefit. **The splice and the scope repair land together.**
- **Needs.** `/tmp/g12-patch/G1.2-PATCH.md` (ready-to-apply, re-printed lines: `mainAsmRaw` def
  `Program.lean:98`; callers `:116`, `:133`, `:192`, `PoseidonValid.lean:295` — all four have `m`).
  **D-P65's shape: `docs/plans/V3-evidence/design/statements.md` §2(d), candidate B**, including its
  extra `hns : noShadowB R = true` hypothesis and the restated conjunct `[hoist prog] = scopeV3`.
- **Do.** 1. Apply the patch (splice + `sliceOf` companion). 2. Apply D-P65's scope change so
  **`hoist (R.prog)` and `hoist (R.helpers)` agree** — measured: a Program-only splice makes prog
  hoist 10 vs helpers 8 and `prog_slices_decomp`'s **second** conjunct FALSE. 3. Update the
  `PoseidonValid.lean:295` pin **6779 → 6847** (measured; the row renders 70 because 68 is the bare
  region and 70 is brace-wrapped). 4. **Refresh `V3-evidence/ReviewProbes.lean:179` (`sliceOf` lengths
  `[1,44,3,1,225,2,3]` → quotientLin becomes 3) and `:182-184` (8 AST `funDefs` → 10).** ⚠ **That file
  is NOT kat-scanned, so it goes stale SILENTLY** — leaving it is a review artefact that misleads.
- **Frozen diff: `Program.lean` AND `Statements.lean`, two `Frozen.sha256` lines, ONE commit**
  (D-P65 amends D-P52). Show both as a deliberate diff.
- **Accept.** `checks.sh` exits 0; **`prog_slices_decomp` is still a sorry, not a refutation**; gate
  23 green; GenAst 55/55; cone reported at every root (**expect 9 unchanged** — `codegenAgrees` stays
  false at 6847 ≠ 14054 until G1.1/G1.3). **No pin bumped to buy green.**
- **Stop if.** The two frozen lines would become three · `prog_slices_decomp` turns false ·
  `ReviewProbes.lean` cannot be refreshed consistently · >1.5 h.

## ⚠ HANDOVER — the plan changed materially while this session ran

**PL.G has run (D-P71, D-P72, D-P73 signed).** Two things I did not brief against and the next session
**must** read before taking a card:
  1. **The plan is restated for the generator theorem (`lowering_correctW`); fixtures are tests.**
     Rows are marked "restated for every…" — **§6's DONE wording I have been optimising against may no
     longer be the target.** Read PLAN-V3 §2.2 rows 71-73 and the PL.G restatement FIRST.
  2. **D-P72 widens the supported class to the IVC verifier** (accumulator mode with batched pairing
     checks) — *"ensure we cover the IVC proofs with extra pairing check, batched"*. **That is a scope
     expansion beyond `poseidonRender`.** The `mainAsmRaw`/`sliceOf` widening G1.2c performs should be
     checked against it rather than assumed to be the final shape.

**Verified state at handover:** `checks.sh` **exit 0** (1400 gates / 102 files), register 58, **headline
cone 9** (from 11), frozen all OK, `formal/baseline` = `25fafe4` pushed and clean.
### G1.3 — EMIT the quotient-numerator block (6384 tokens)  **[READY after G1.4b — batch with G1.1, D-P52]**  **[V3: MERGED INTO OBJ.2 (and OBJ.15) — do not run; its 895 / 5,489 split is measured 5,431 / 953]**
GEN · EMIT · box 2.5 h, **over-box by measurement — see Do 0** · strongest · after G1.2

- **Goal.** Emit `renderQuotientNumeratorBlock`, the second `quotient_numerator` include: 6384
  tokens, 922 lines, the largest un-emitted region in the tree and 88 % of clause 6.
- **Needs.**
  - the region: `renderQuotientNumeratorBlock (partialCtxOfVerifier poseidonM)` — 6384 tokens, 922
    lines, **0 function definitions** (it is inline statements inside the linearization scope),
    437 `let`, 14 `if`, 10 `for`, 2 `switch`, 91 brace pairs, 182 `mload`, 59 `mstore`,
    158 `mulmod`, 144 `addmod`;
  - **the measured split**, which is what makes this card honest about its box:
    **895 tokens** are the generated inline-computation lines
    (`ctx.quotientInlineComputations`: 1 block, 99 lines) and **5489 tokens** are the QVM
    interpreter template plus the `QuotientProgram`-field interpolations
    (`constMptr`, `programMptr`, `evalNumerMptr`, `len`, `stackMptr`, `guards`, `opUsage`,
    the opcode bytes — `renderQuotientNumeratorBlock` runs `VerifierPartials.lean:1266-1979`);
  - the reuse target PLAN-V2:232 names: `Midfall/Lowering/GenAstQuotient.lean` — AST twins of the
    string formatters already exist there (`evaluateA`, `gateComputationsTaggedA`,
    `permutationComputationsA`, `lookupComputationsA`, `trashcanComputationsA`, :298-589), with
    their own text-vs-AST agreement gates (:627-658). The 895-token part is those four families.
  - the 12 contract constants the region reads: `X_MPTR`, `Y_MPTR`, `INSTANCE_EVAL_MPTR`,
    `GAMMA_MPTR`, `BETA_MPTR`, `THETA_MPTR`, `L_0_MPTR`, `L_LAST_MPTR`, `L_BLIND_MPTR`,
    `TRASH_CHALLENGE_MPTR`, `SELECTOR_ACC_MPTR`, `QUOTIENT_EVAL_MPTR`.
- **Does NOT need.** `renderQuotientHelpers` (G1.2); the linearization scope (already emitted,
  120 = 120); the untaken arms of the template (external quotient, direct, probe, trace, gas
  checkpoints — `ctx.quotientExternal = none`, `ctx.quotientDirect = none`, `quotientProbe =
  false`, `trace = false`); any block contract; WP-G3 (`compact_quotient_computation_blocks`) —
  this card emits what the ported text port renders TODAY, from the model's own fields.
- **Do.**
  0. **Split first.** If the 5489-token interpreter part does not land inside the box, stop and
     report: the two halves (template+program fields / inline computations) are independent EMIT
     cards and this card's reproducer already sizes them. Do not half-emit: a partial region leaves
     the row unequal and buys nothing.
  1. `def GenAst.emitQuotientNumerator (pv : PlanView) : Block Op`, spliced in the `quotientLin`
     arm between `emitQuotientHelpers pv` and `emitQuotientLin pv`.
  2. Every interpolated value comes from `pv` / `partialCtxOfVerifier` — never typed in (D-P30;
     the anti-hard-coding gates 36/41 are the pattern to copy).
  3. Gates: whole-region token KAT, a per-`for`-site count (`VerifierPartials.lean:1262-1264`
     records that the five generated-code for-sites contribute 528 of the 921 rendered lines),
     and a perturbation per interpolation family.
- **Deliverable.** `GenAst.emitQuotientNumerator` (or two defs plus a report saying so), the arm
  splice, the gate set, the R.2 row updated.
- **Accept.** The whole-region KAT — `GenAst.emitPartial poseidonPv .quotientLin` printed (minus its
  outer braces) against `yulTokens ((partsOf poseidonM).quotientAndLinearization)` — prints `true`; a one-literal
  mutation reddens; the gap falls to 18 (pcs only); `verify.sh --quick` green.
- **Stop if.** It needs a plan field that does not exist (PREMISE GAP); the box is blown (Do 0); any
  single `#eval` exceeds 60 s (the region is 55,597 bytes of text — keep the gate on token lists,
  not on pretty-printed string equality).
- **Reproducer.** `/tmp/g13/p.lean`:

          #eval (yulTokens (renderQuotientNumeratorBlock (partialCtxOfVerifier poseidonM))).length -- 6384
          #eval ((partialCtxOfVerifier poseidonM).quotientInlineComputations).flatten.length        -- 99 lines
          #eval (yulTokens (String.intercalate "\n"
                  (partialCtxOfVerifier poseidonM).quotientInlineComputations.flatten)).length     -- 895
          #eval Midfall.Lowering.GenAst.renderFunctionNames
                 (renderQuotientNumeratorBlock (partialCtxOfVerifier poseidonM))                     -- []

### G1.4 — EMIT the pcs block scopes: stop flattening the 8-block partition (18 tokens)  **[SUPERSEDED by G1.4b — do not re-run]**  **[STOP-AND-REPORT 6bde89f - win landed, 4 gates hard-code the flattening; see G1.4b/D-P51]**
GEN · EMIT · box 0.5 h · Sonnet · after R.2 (independent of G1.1–G1.3)

- **Goal.** The `pcs` row's 18-token residue is 9 block-scope brace pairs, not statements: emit the
  partition as `Stmt.block` scopes instead of flattening it, so the row reads `equal true` and
  `codegenAgrees` becomes `true` at the deployment (with G1.1–G1.3).
- **Needs.**
  - the measurement: text pcs 3623 tokens vs emitted 3605; **the 3571 non-brace tokens are already
    identical** (`noBraces` comparison prints `true`); text has 26 `{`/`}` pairs, the AST 17 —
    the missing 9 are the region's own wrapper plus the 8 blocks `computationsAst` returns;
  - the defect: `emitPcsFromPlan` (`GenAstDispatch.lean:131-135`) does `blocks.flatten`, and its
    docstring's justification ("the braces the token gates add are the comparator's, not the
    artifact's") is true of the OUTER comparator and false of the 8 inner scopes — in Yul a `{`
    opens a `let` scope, so dropping them is a scoping change, not a spelling change;
  - `pcsTaggedFromPlan` / `GenAstPcs.Kats.pcsTaggedBlocks` (:152-157), which already recover the
    partition and its roles.
- **Does NOT need.** WP-G4 (the circuit gap is a different thing and this row no longer depends on
  it); any change to `computationsAst`; contracts (the pcs row is S.2's boundary problem, not this).
- **Do.**
  1. `emitPcsFromPlan pv := blocks.map Stmt.block` (flatten one level less), or keep the flat list
     and wrap the region once in `mainAsmRaw` — whichever makes the token KAT close; state which.
  2. Re-check the gates that read the pcs arm, all in `GenAstDispatch.lean`:
     `emitPcsDispatch_beq_ok` (:251), `emitPcsDispatch_tokens_ok` (:276),
     `emitPcsTagging_ok` (:397), `emitPcsFaultArm_ok` (:431), `emitPcsReadsOnlyFourFields_ok` (:376) — several compare against a flattened expectation and
     will need the same one-level change, honestly and in the same commit.
  3. Gate: the whole-region token KAT plus a perturbation that moves one block boundary.
- **Deliverable.** the `emitPcsFromPlan` change, the repaired pcs gate set, and — if G1.1–G1.3 have
  landed — `theorem deciding_codegen : codegenAgrees poseidonPv poseidonM = true` replacing
  `PoseidonValid.lean:276`'s `= false`, with clause 6 flipped REFUTED → PROVED in that file's table.
- **Accept.** the pcs row prints `equal true`; with G1.1–G1.3 in, `codegenAgrees poseidonPv
  poseidonM` prints `true` and `Midfall.Instances.PoseidonValid.poseidonValid_codegen_not` is
  REPLACED by the positive (clause 6 REFUTED → PROVED; `deciding_codegen` at :276 restated to
  `= true`). **Do not promise a cone move:** `poseidonRender_notValid` runs through clause 2, and
  clauses 2/3 (WP-G4) and 9 (a v1 `WellFormed` field) stay refuted, so `poseidon_valid` is still
  open after all four cards — what these four do is delete one of the four refutations and make
  clause 6 the first non-plan clause to close. Report `cone_sorries` before and after anyway.
  `verify.sh --quick` green.
- **Stop if.** The non-brace equality (3571 = 3571) no longer holds at the merge commit — then the
  circuit gap has moved and this card is premature; report instead of forcing braces in.
- **Reproducer.** `/tmp/g14/p.lean`:

          open Midfall Midfall.Generator Midfall.Instances Midfall.Instances.PoseidonValid
            Midfall.LoweringV2 Midfall.Lowering YulSemantics YulSemantics.EVM
          def nb (l : List String) : List String := l.filter (fun t => t != "{" && t != "}")
          def inner (b : Block EVM.Op) : List String := ((yulTokens (EVM.print b)).drop 1).dropLast
          #eval let t := yulTokens ((partsOf poseidonM).pcs)
                let a := inner (GenAst.emitPartial poseidonPv .pcs)
                (t.length, a.length, (nb t).length, nb t == nb a)   -- (3623, 3605, 3571, true)


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

### R.3 — Make `Valid.model` dischargeable (D-P56)  **[READY after F.1 — D-P56 signed off 2026-11-17]**  **[V3: CONTINUES — M2]**
GEN · PROOF · box 1 h · strongest · after F.1

- **Goal.** `Valid` clause 4 (`model`) PROVED at `poseidonRender`, with no `sorryAx`.
- **Needs.** C.4: the clause is true but blocked, because `poseidonModelVal`'s error arm
  (`PoseidonV2.lean:111`) mentions `poseidonModel` (`PoseidonInputs.lean:126`) in its own proof type.
  F.2-G1's pattern (one `native_decide` on `.isOk`, then `cases`).
- **Do.**
  1. `deriving instance Inhabited for Halo2Verifier` in a V2/`Instances/` file. **No v1 edit.**
  2. Restate `poseidonModelVal` as `getD` on `poseidonModel`.
  3. Discharge clause 4 by F.2-G1's pattern.
- **Accept.** Clause 4 PROVED with `#print axioms` free of `sorryAx`; every other `Valid` clause keeps
  its F.2 verdict (report the table); `verify.sh --quick` green.
- **Stop if.** The stand-alone `deriving instance` fails. Only then apply D-P56's fallback (one-line
  `deriving Inhabited` at `Generator/Models.lean:757`, line count unchanged), and report which path ran.

### R.4 — Gap B: name the G2 bases from their bytes (D-P55)  **[READY after F.1 — D-P55 signed off 2026-11-17]**  **[V3: MERGED INTO REF.5, REF.6 (D-P62: no G2 axiom) — do not run]**
ALG · PROOF · box 2.5 h · strongest · after F.1

- **Goal.** At the deployment, `poseidonSG2` and the prepared G2 parameters are the points the payload
  holds, not `g₂`, so D-P46's NEG_S_G2 pin can hold (F.2-G2: the payload's
  `NEG_S_G2[16..21] = [5,10,194,124,53,39]`, not `encG2(−H2)`).
- **Needs.**
  - `PoseidonEnv.lean:236` (`poseidonSG2 := bls12_381Pairing.g₂`, "NOT checked against that hex").
  - `G2Codec.lean:245` (`G2fold = Exp blsR`).
  - `G1PointCount.lean`'s `torsion_eq_zpowers_gen` (`aa53b57`) as the model for the G1 route, and its
    commit message on why the squeeze fails over Fp2.
  - D-P55's exact axiom conditions.
- **Do.**
  1. **First hour, P-POINTCOUNT's lesson:** look for an axiom-free proof of G2 r-torsion cyclicity
     from what this specific curve allows. If found, land it and skip step 2.
  2. Otherwise add D-P55's single axiom in `Midfall/Assumptions/` with the three required KATs and its
     docstring. Update PLAN-V2's axiom lists in the same commit (D-P55 names the lines).
  3. Name the G2 bases from the payload bytes by `Classical.choose`, and re-derive the prepared
     parameters.
- **Accept.**
  - `vkG2Words poseidonPv vkNegSG2BaseSlot = poseidonEncG2 (sG2Prepared)⁻¹` PROVED (and the G2_BASE
    half).
  - `#print axioms` lists only standard + D-P36a + native_decide (+ the D-P55 axiom if step 2 ran).
  - F.2's PROVED `Valid` clauses stay PROVED (report the table).
  - `verify.sh --quick` green.
- **Stop if.**
  - The axiom would need any premise other than a computed validity check of the bytes.
  - A KAT shows the check TRUE off the r-torsion. The axiom would then be false: do NOT land it.

### R.4b — G1: a real `ofCompressed?` and the fixture calldata decoding (D-P55 step 1)  **[READY after F.1]**  **[V3: MERGED INTO REF.4, REF.9, REF.10 — do not run]**
ALG · PROOF · box 2 h · strongest · after F.1

- **Goal.** Two results:
  - `g1CodecZ.ofCompressed?` is the `Classical.choose` decoder (same scheme as `g1zOfEip?`,
    `G1Agreement.lean:1995`) instead of `fun _ => none`.
  - The fixture calldata provably decodes, parses and replays. These are the D-P45 conjuncts, at the
    deployment. **No axiom: existence comes from `torsion_eq_zpowers_gen` plus computed checks.**
- **Needs.**
  - F.2-G3 (the witness is not evaluable at the codec).
  - `check3_codec_decodes_no_compressed_point` (`PoseidonCoherence.lean:432`), which this card retires
    or inverts.
  - The committed fixture `proof.bin`, or R.5's regenerated one if R.5 has merged.
- **Do.** First measure whether `decodeCalldata` reads `ofCompressed?` at all. If it does not, the
  decoder change serves `end_to_end` only; say so and do both.
- **Accept.**
  - `∃ ms instW inst Snap, decodeCalldata … = some (ms, instW) ∧ instOfWords? instW = some inst ∧
    snapshotOf … = .ok Snap` PROVED at the fixture calldata.
  - `G1CodecLaws poseidonE.g1` PROVED.
  - Both with `#print axioms` standard + D-P36a + native_decide.
- **Stop if.** A fixture G1 point fails the computed subgroup check: that is a fixture defect, so
  report it.

### R.5 — Make the fixture export reproducible (D-P58)  **[READY after F.1 — D-P58 signed off 2026-11-17]**  **[V3: MERGED INTO REF.11 (D-P63; source is `OsRng`, prover.rs:126) — do not run]**
GEN · KAT · box 1.5 h · Sonnet · after F.1 · raised by R.1 (`2041977`)

- **Known.**
  - R.1 found that `proof.bin` and `trace.json` differ from run to run, and the committed bundle
    matches neither run.
  - **The exporter already seeds both RNGs** (`proofs/solidity-verifier/tests/conformance_export.rs:330`,
    `:333`), so the source is elsewhere. Do not assume it is the seed.
  - The regenerated `Halo2Verifier.sol` differs from the committed one only in `BUILD_ID`.
- **Do.**
  1. List every consumer of `proof.bin`/`trace.json`/`Halo2Verifier.sol` in the tree (`grep`).
  2. Export twice, diff the outputs, and locate the non-determinism.
  3. Apply D-P58:
     - **(a)** If the fix is in test or exporter code: fix it, regenerate ONCE, replace the files,
       and re-pin D.3 checks 4–5 in the same commit.
     - **(b)** If it is in baseline code (`proofs/src`, `zk_stdlib`): change nothing there. Record
       the committed files' provenance as "unknown; verified by D.3 checks 4–5".
  4. `Halo2Verifier.sol`: refresh it if a gate or KAT reads it, otherwise untrack it.
- **Accept.**
  - Under (a): two consecutive exports byte-identical, with the sha256 of every output in the report.
  - D.3 and `verify.sh --quick` green.
  - The report says which branch ran.
- **Stop if.** A frozen file depends on `proof.bin`/`trace.json`. Or the regenerated bundle describes
  a different circuit or VK from the deployed contract (a scope question).

### R.6 — Land D-P46's three VK base pins (second `Statements.lean` re-hash)  **[READY after R.4 — D-P46 signed off 2026-11-17]**  **[V3: CONTINUES — M1, after REF.6 and Q0.5; subsumed at ST.6]**
INFRA · PORT · box 1.5 h · strongest · after R.4, Q0.5

- **Goal.** `Render.Valid` gains `baseSlots` (three conjuncts, `design.md` D-P46), PROVED at
  `poseidonRender`.
- **Do.**
  1. Add the clause, and the docstring exception D-P46 records (`Statements.lean:170`, "decided by
     computation"). Re-hash `Frozen.sha256` in the same commit.
  2. Discharge the clause at the deployment: F.2-G2's proved halves, plus R.4's NEG_S_G2.
  3. Discharge `fp_finalPairing_contracts`'s `fpG2Slots R` hypothesis from `R.Valid`.
- **Accept.**
  - The clause is PROVED with no `sorryAx`.
  - `fpG2Slots` is no longer a free hypothesis of FinalPairing.
  - `Frozen.sha256` OK, with exactly one line changed.
  - `verify.sh --quick` green.
- **Stop if.** Any conjunct is FALSE at the deployment after R.4.

### R.7 — Fix `WellFormed.permutationCommitmentsMatch` (D-P59, `Valid` clause 9)  **[READY after F.1 — D-P59 signed off 2026-11-17]**  **[V3: CONTINUES — = REF.3, M1]**
GEN · PORT · box 1 h · strongest · after F.1

- **Goal.** `Valid` clause 9 (`supported`) no longer refuted by a mis-ported field.
- **Needs.** `Halo2/Exec/VerifyingKey.lean:99-102,114` and `proofs/src/plonk/permutation.rs:123` (one
  sigma commitment per COLUMN). Consumers: `Halo2/Spec/Degrees.lean:102` (docstring), PoseidonEnv
  gate 13 (`PoseidonEnv.lean:478-500`, which pins the failure), and `PoseidonValid.lean:40,413`
  (`deciding_supported_perm`).
- **Do.**
  1. **First, read the Lean permutation verifier port**, and confirm it indexes
     `vk.permutation.commitments` per column.
  2. Restate the field as `… = vk.cs.permutation.columns.size`, and correct both docstrings in
     place, keeping line counts.
  3. Flip gate 13's second half to assert the corrected clause holds. Expected result: 8 = 8. Gate 13
     already pins `permutation.columns.size == 8`.
  4. Fix gate 4's stale docstring (`PoseidonEnv.lean:354-357`). It predates R.1 and says "no
     permutation columns … divCeil 0 3".
  5. Re-decide clause 9 at the deployment.
- **Accept.**
  - Clause 9 PROVED, or refuted only by a DIFFERENT sub-clause, named in the report with its
    deciding value.
  - Gate 13 green.
  - `SORRY.md` line references are unchanged, or regenerated in the same commit.
  - `verify.sh --quick` green.
- **Stop if.** The port indexes the VK commitments by chunk: that is a port defect larger than this
  field, so report it and do not patch around it.

### R.8 — Export-first probe for `Valid` clauses 2/3 (WP-G4 scope)  **[READY after F.1]**  **[V3: MERGED INTO OBJ.6, OBJ.7, ST.6 — do not run]**
GEN · PROBE · box 1 h · Sonnet · after F.1 · read-only

- **Known (F.2).**
  - Clause 2 `layout` is refuted: proofLen 4224 vs 4320.
  - Clause 3 `invariants` is refuted: PCS memory sizing comes from `LoweringPlan::new`'s
    post-constructor `set_num_point_sets`/`set_num_dummy_evals`.
- **Do.**
  1. Locate the Rust lines that set those numbers.
  2. Decide which case this is: **(i)** the Lean derivation is missing a post-constructor step (so
     port it), or **(ii)** the fixture exports values from before and after those mutations
     inconsistently (so fix the export, as D-P47 did).
- **Deliverable.** A one-page verdict with:
  - the Rust lines;
  - the case, (i) or (ii);
  - the Lean lines to change, with a line estimate;
  - whether any frozen file is touched;
  - a drafted EMIT card.
- **Stop if.** A frozen file must change. Draft the change as a new item at the end of
  `docs/DECISIONS-PENDING.md`, unsigned.

### R.9 — Discharge `Valid.circuitMeta` as a Prop (F.2-G1)  **[READY after F.1 — small]**  **[V3: MERGED INTO OBJ.6, OBJ.7, ST.6 — do not run (the clause it discharges is restated)]**
GEN · PROOF · box 0.5 h · Sonnet · after F.1

- **Goal.** Clause 1 is PROVED as a Prop, not only as a Bool decision. Land F.2-G1's 8-line proof in
  `Instances/PoseidonValid.lean`: `show poseidonMetaDerived? = .ok poseidonMeta; cases h :
  poseidonMetaDerived?`; in the ok arm `rw [poseidonMeta, h]`; the error arm is killed by the
  `native_decide` on `.isOk`.
- **Accept.** `#print axioms` with no `sorryAx`; no new instance; no frozen edit; `verify.sh --quick`
  green.

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

### S.4 — `BlockRow` for `vkLoading`  **[READY after F.1]**  **[MERGED 93c0d4c - PARTIAL: row NOT closed, 15 sorry-free lemmas + 6 pin gaps]**  **[V3: MERGED INTO SIM.8, T3.6 — do not run]**
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

### S.8 — Verify the six `vkLoading` pins at the deployment  **[READY — RUN BEFORE ANY `Valid` CHANGE]**  **[DONE 89e9c0a - all six pins TRUE and PROVED at the deployment; see D-P50/S.9]**  **[V3: DONE]**

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
### S.9 — Land the six pins: `Valid` fields + the proved deployment discharge  **[READY]**  **[MERGED fece4c7 - Valid now 13 clauses; vk_blockRow pin-free; cone unchanged]**  **[V3: DONE]**

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
### S.10 — Fix the stale `Valid` clause-count prose  **[READY — small]**  **[V3: CONTINUES — row 12]**

INFRA · DOCS · box 0.5 h · Sonnet · after S.9

- **Goal.** `Render.Valid` now has **13** clauses (S.9 appended `vkPins`, `vkProgressPins`). Several
  comments still say 11 and actively misdescribe the frozen surface.
- **Needs.** `Instances/PoseidonValid.lean` 'CLAUSE n OF 11' headers; `Instances/PoseidonV2.lean:173`
  'the eleven computation clauses'; any other '11 clauses' mention (`grep -rn 'OF 11\|eleven'
  Midfall/Instances/`).
- **Do.** Update the counts and clause numbering. **Comment text only — no proof changes.** Also fix
  F.2-G5: `PoseidonValid.lean:132`'s docstring says "derived proofLen 1792"; the value the file
  computes is **4224** (`#eval deciding_layout_derivedProofLen`). If Q0.5 has merged, the count is
  **14** (`returnMptr`); after R.6, **15** (`baseSlots`). Use the count at the time you run, or
  better, count-free wording as Q0.5 does for `Statements.lean`.
- **Accept.** `grep` shows no stale '11 clauses'/'OF 11' referring to `Valid` and no '1792' in
  `PoseidonValid.lean`; `verify.sh --quick` green;
  `Frozen.sha256` verifies (these files are NOT frozen, so no re-hash).
- **Note for whoever runs it:** rebuilding `PoseidonValid.lean` re-runs ~20 `native_decide`s — budget
  for it; S.9 left this out of scope for exactly that reason.
- **Does NOT need.** Any proof change; the pins; any block row.

---
### S.5 — `BlockRow` for `transcriptParser`  **[READY after T.3 — D-P57 signed off 2026-11-17; reverts to after F.1 only under D-P57's fallback]**  **[V3: MERGED INTO ROW.TP — do not run]**
SEM · PROOF · box 2.5 h · strongest · after S.3, T.3 (D-P57)
- **Goal.** `BlockRow R product .transcriptParser`. **The big one: 44 stmts, 9 own loops ⇒ fuel + 9
  invariants.** Pre `Clean R .vk`, post `… ∨ Clean R .transcript ∨ …`.
- **Needs.** M0.1's transcriptParser row (16 locals written; 4 static ranges + **11 dynamic write
  sites**; helpers `transcript_init, common_word, fail, common_uncompressed_g1, squeeze_to`, none
  loops); `Yul/Contracts.lean` loop rules.
- **Split at 1 h** into (loops) and (guards) if needed.
- **Accept.** As S.4. **If the 9 invariants do not close, deliver the ones that do and name the rest.**
- **Stop if.** The first loop invariant is not closed at 1 h. PLAN-V2:269 puts automation (WP-T)
  BEFORE block proofs because "hand proofs at that density are infeasible", and TraceReturn took 988
  lines by hand. Report lines per Yul token. (The WP-T decision is taken: D-P57. This stop still
  applies, with the tactic in hand.)

### S.6 — `BlockRow` for `lagrange`  **[READY after T.3 — D-P57: T.3's target IS this row; if T.3 merged it, mark S.6 DONE with T.3's hash and skip]**  **[V3: MERGED INTO T3.7, T3.9 — do not run]**
SEM · PROOF · box 2 h · strongest · after S.3, T.3 (D-P57)
- **Goal.** `BlockRow R product .lagrange`. **The only loop-bearing helper is `batch_invert`.** Pre
  `Clean R .transcript`, post `… ∨ Clean R .lagrange ∨ …`.
- **Needs.** M0.1's lagrange row (3 stmts, 21 locals written, 5 own loops, `success :=
  batch_invert(…)`); `Yul/Contracts.lean` loop inversion; **FP.0's cost finding: the `Inv`-chain
  transfer blows the heartbeat default — do NOT raise heartbeats, fold the clause as FP.0 did.**
- **Accept.** As S.4.

### S.7 — The `quotientLin` contract (GAP G3)  **[BLOCKED: WP-G1 not merged (see R.2) · S.2 may move five `Inv` clauses into this post]**  **[V3: MERGED INTO T3.10, ROW.Q — do not run]**
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

### ~~pcs row~~  **[HELD — blocked by S.2]**  **[V3: MERGED INTO SIM.12, ROW.PCS]**
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

### S.2 — Resolve the `pcs` / `Inv` boundary misalignment  **[READY]**  **[V3: MERGED INTO SIM.12, ROW.PCS — do not run]**

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
### M.1 — Prove `blockContracts_of_valid` generically  **[READY — THE HINGE]**  **[MERGED 126c99e - OUTCOME (B): needs ALL 7 rows; narrowing moves nothing]**  **[V3: SUPERSEDED by SIM.2, PL.H — do not run]**

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
### P.1 — Pairing-check algebra  **[V3: MERGED INTO ROW.FP — do not run]**
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

### T.2b — WP-T tactic: re-prove `traceReturn_spec` in under 100 lines (D-P57)  **[READY after F.1 — D-P57 signed off 2026-11-17]**  **[V3: MERGED INTO T3.1, T3.3, T3.4 — do not run]**
SEM · PROOF · box 2.5 h · strongest · after F.1, T.2

- **Goal.** The PLAN-V2:278-279 accept line. Package T.2's recurring steps S1–S6 (above;
  `Blocks/TraceReturn.lean`) as a tactic, or a small tactic family, and re-prove
  `traceReturn_spec` (`BlockSound` ∧ `BlockProgress` at `.traceReturn`) on the closed slice with it,
  **in under 100 lines**. Also step VkLoading's straight-line prefix as the second client.
- **Needs.** T.2's two traps (slice does not reduce by `simp`; no `classical` before a forward
  `Step`); T.1's interface.
- **Do not** delete the 988-line hand proof. Land the tactic proof alongside it, under a new name, and
  check both against the same statement.
- **Accept.** The tactic proof is sorry-free with the axioms printed. Report:
  - its line count;
  - lines per Yul token, for both TraceReturn and the VkLoading prefix;
  - the hand proof's lines per token, for comparison.
  Under 100 lines ⇒ D-P57's accept line is met, and T.3 is READY.
- **Stop if.** 2.5 h without meeting the line. Then deliver what works and write T.2c (one follow-up,
  ≤ 2.5 h) naming the blocker. If T.2c also misses the line, **D-P57's fallback applies by
  condition:**
  - record it in STATUS;
  - S.5/S.6 revert to `after F.1`;
  - T.3 becomes a hand proof of the lagrange row;
  - re-estimate `docs/ETA.md` from the measured lines per token.

### T.4 — `staticcall` stepping, accepted by `ec_pairing_contract`  **[V3: MERGED INTO ROW.FP — do not run]**
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

### T.5 — Arithmetic and memory, accepted by FinalPairing  **[V3: MERGED INTO ROW.FP — do not run]**
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

### C.5 — Compose FinalPairing ; TraceReturn (calibration point 1)  **[V3: SUPERSEDED by SIM.2, PL.H — do not run]**
SEM · PROOF · box 2 h · strongest · after T.4, T.5, C.2

- **Goal.** C.2's sequencing node for FinalPairing ; TraceReturn, starting from `Clean` at `.pcs`.
- **Needs.** The two block contracts (T.2, T.5) and C.2's sequencing lemma.
- **Does NOT need.** Other blocks, or deployment facts beyond the sorried `poseidon_valid`.
- **Accept.** The cone falls. Then the orchestrator runs **calibration point 1** (EXECUTION-V2 §6;
  PLAN-V2 §9.3).

### C.3 — Staged rejection skeleton  **[V3: SUPERSEDED by SIM.0–SIM.3 (staged contracts replace staged rejection) — do not run]**
SEM · SKELETON · box 2 h · strongest · after C.2

- **Goal.** `Render.Rejects` from per-block rejection lemmas, modulo sorries, with each block's
  invariant and fault class.
- **Needs.** C.2's rejection step and the M0.1 table. The only excluded bad set is the
  `logup.rs:460` panic (`SoundSide`).
- **Does NOT need.** Block soundness or progress proofs.
- **Accept.** The cone lists the per-block lemmas, and the report has a requirements table.

### T.3 — Symbolic branches and loops  **[READY after T.2b (or T.2c) met D-P57's accept line; under D-P57's fallback, hand proof of the lagrange row]**  **[V3: MERGED INTO T3.7, T3.9 — do not run]**
SEM · PROOF · box 2.5 h · strongest · after T.2b (D-P57)

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

## ⚠ HANDOVER 2 (round 43) — G1.2c must NOT be run as written

**I scoped G1.2c before reading the PL.G restatement, and the restatement invalidates its framing.**
The goal is now the generator theorem `lowering_correct` **for every render with `ValidV3`**, widened
to IVC as `lowering_correctW`. **Fixtures are tests.** The binding line is:

> **No PROOF card may state or prove anything at a fixture.**

**G1.2c's acceptance is built on `codegenAgrees poseidonPv poseidonM` and a `PoseidonValid.lean` token
pin — both fixture-level measurements, therefore tests under the restatement.** A card treating them
as the acceptance condition optimises the wrong thing.

**The structural work D-P65 requires is still needed** — the `mainAsmRaw` widening, the `sliceOf`
companion, and the `hoist` scope repair that keeps `prog_slices_decomp` from becoming a refutation —
**but it must be re-framed against `ValidV3`/`lowering_correct`, not against the poseidon fixture.**

**Also noted:** T3.4 dropped; T3.6 replaced by GEN.1; T3.3 and T3.11 are tests. Area WID = milestone
M9; area CERT = M10 (D-P73 certifies the generator itself). **A missed PLAN-V3 §5 M5 threshold goes to
the human — per-fixture rows are not a fallback.**

**Next card comes from the V3 table, not my V2-framed queue: row 2, DG.1 (land the axiom gate), after
DG.0 which is done.** Read PLAN-V3 §2.2 rows 71-73 and §5 M9/M10 before briefing it.
