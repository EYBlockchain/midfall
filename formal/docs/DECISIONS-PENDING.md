# Decisions pending human sign-off — drafts (2026-11-17)

Drafted in a review of `formal/baseline...7bf0497`. **Every drafted item below is now SIGNED OFF**
(2026-11-17) and recorded in `design.md`; the bodies were removed. The headings stay so the
§-references in QUEUE.md and STATUS.md remain valid. How the batch was signed is in **D-P53** (a
one-time human sign-off, not a delegation; W2 stands). New items go at the end, unsigned, in this
format: `Signed off: <name>, <date>, <where: message / commit / PR>`. The orchestrator must not act on
an item without a sign-off line (EXECUTION-V2 W2).

## 1. W2: are there orchestrator decisions on delegated authority? — SIGNED OFF, recorded as D-P53

W2 kept unchanged; no standing grant.

## 2. R-72's second question: add `hR : R.Valid` to `LoweringEquivalence`? — SIGNED OFF, recorded as D-P54

Rejected (vacuity trap: `¬ poseidonRender.Valid` is proved).

## 3. D-P45: repair `HypothesesInhabited` — SIGNED OFF AS AMENDED, recorded in D-P45

Adopted: the witness must decode, parse and replay (`decodeCalldata`, `instOfWords?`, `snapshotOf`)
plus `G1CodecLaws`. **Not** `LeanAccepts`: at a real SRS it is a discrete-log relation in `s` and could
never be discharged at a deployment. QUEUE Q0.5.

## 4. D-P46: VK base-slot pins in `Render.Valid` — SIGNED OFF, recorded in D-P46

All three pins, one `Statements.lean` re-hash, after R.4 (Gap B). QUEUE R.6.

## 5. D-P47: re-export the fixture before porting `LoweringPlan::new` — SIGNED OFF (ratified), recorded in D-P47

Already executed by R.1 (`2041977`). Export-first also governs clauses 2/3 (QUEUE R.8).

## 6. D-P48: `RETURN_MPTR` pin in `Render.Valid` — SIGNED OFF, recorded in D-P48

Lands in Q0.5's re-hash with D-P45.

## 7. D-P49 — SIGNED OFF (2026-11-17), recorded in `design.md`

Kept as a heading so the §8/§9 references in QUEUE.md stay valid.

## 8. Gap B: how s·G₂ is modelled at the deployment (QUEUE R.4) — SIGNED OFF, recorded as D-P55

G1 needs no axiom (`torsion_eq_zpowers_gen`, `aa53b57`); G2 gets one cyclicity axiom in
`Assumptions/` only if R.4's first hour finds no axiom-free route. `ofCompressed?` is QUEUE R.4b.

## 9. `Valid.model`: make it dischargeable (QUEUE R.3) — SIGNED OFF, recorded as D-P56

`getD` restatement + `deriving instance Inhabited` in a V2 file; v1 one-line edit only as fallback.

## 10. WP-T: automation before block proofs? — SIGNED OFF, recorded as D-P57

WP-T first (T.2b, T.3), time-boxed, with a pre-approved fallback to hand proofs.

## 11. Batched `Program.lean` re-hash — SIGNED OFF (2026-11-17), recorded as D-P52 in `design.md`

Kept as a heading so QUEUE.md's §11 references stay valid.

## Also signed off in the same batch (no drafted item)

- **D-P58** — fixture reproducibility (QUEUE R.5).
- **D-P59** — the v1 `WellFormed.permutationCommitmentsMatch` defect behind `Valid` clause 9 (QUEUE R.7).

## Also open (no decision needed yet)

- `Rejects`/`SoundSide` (C.2). Keep it an investigation (C.3). D-P47's refusal to weaken it to
  move the cone was right.
- **Acceptance at the deployment is not certifiable in this model** (D-P45's stated limit). If the
  human wants evidence that `LeanAccepts` is satisfiable at all, the route is a toy render with a
  known `s` — not queued.

## 12. PLAN-V3 — ten decisions, D-P60–D-P69 — SIGNED OFF (2026-11-17), recorded as D-P60–D-P69 in `design.md`

An independent review of `formal/` (`docs/plans/REVIEW-V3.md`, 46 findings) and a revised plan
(`docs/plans/PLAN-V3.md`) were added on 2026-11-17. **All ten were signed off by the human on 2026-11-17, after `53bf8c1`** (see D-P60 for how).
Their conditions still apply, as recorded in each entry. The full text,
recommendation and "if struck" consequence of each row is PLAN-V3 §2.2; how each relates to the
signed D-P45–D-P59 is PLAN-V3 §2.1. Evidence: `bash docs/plans/V3-evidence/check.sh` (about six
minutes, writes nothing into the repository).

| D-P | one line | urgent? |
|---|---|---|
| 60 | Adopt PLAN-V3; hold block rows about the present render until its M4 exit gate; name the target "fixture F1"; rules W12–W15 | — |
| 61 | Two more reference repairs in `Halo2/Exec` (grouping by `CommitSlot`, semantic `BEq Rotation`): today the Lean verifier rejects every proof of the fixture key | yes: without it no headline is worth proving |
| 62 | Curve assumption, amends D-P55 steps 2–3: construct the pairing (no axioms, no G2 axiom); the SRS point is data | before R.4 spends its box |
| 63 | Test SRS with a known trapdoor for F1, amends D-P58's fallback 3 | — |
| 64 | Statement surface V3 (frozen): `calldataOf`, `EntryFrameV3`, codec laws, totality conjunct, `EndToEndV3` | after ST.1 |
| 65 | The block scope, in D-P52's re-hash | **yes: before the G1.1–G1.3 batch merges G1.2** |
| 66 | The gate for F1, amends D-P45: hash pinned to `keccak256`, `LeanAccepts` added back (conditional on 63) | — |
| 67 | `ValidV3` (frozen), seven clauses; subsumes D-P46's and D-P48's pins | after RECON.1 |
| 68 | Staged block contracts and the `wp` engine; thresholds replace D-P57's hand-proof fallback | after RECON.2 |
| 69 | DONE as one Lean term with `#assert_axioms`; closure fingerprint; CI on this branch; exporter schema 2 | — |

Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` — recorded in `design.md` D-P60–D-P69.

## 13. D-P71 — the deliverable is the generator theorem; fixtures are tests — SIGNED OFF (2026-11-17), recorded as D-P71 in `design.md`

Drafted 2026-11-17 at `c22b51a` and **signed off by the human the same day** (instruction: *"Sign
D-P71"*; `design.md` D-P71 quotes it). The text below is the draft as signed. The number D-P70 was
left free for a fixture-F2 draft another session was writing; D-P71 makes a second fixture proof
moot, so no D-P70 is recorded.

**Why it is here.** The human said in session on 2026-11-17: *"I thought we would formally verify
the codegenerator, the lowering itself"* and *"i am not interested in proofs for fixtures"*. The
record shows where the plan left that goal:

| when | record | effect |
|---|---|---|
| 2026-10-23 | original `PLAN.md` §9 (`3d0d778`) | `verifier_sound (g o L) (hL : g.lower o = .ok L) (hsup : Supported g o)`: every supported generator input |
| 2026-10-28 | D-P24 (`c7e71a9`) | "per-deployment translation validation first"; the generic theorem becomes a follow-on |
| 2026-11-16 | D-P44 clause 4 | headline `lowering_equivalence_poseidon`; the every-render theorem is X4, "later"; block rows still generic in `R` |
| 2026-11-17 | D-P68, technology clause | rows proved per fixture on literal slices pinned by `native_decide` |

**What is already generic (checked at `c22b51a`).** The V3 statements quantify over every render:
`ValidV3 R` (`V3-evidence/lean/statements/StatementsV3.lean:613`) contains the generated-by clause
(`Render.GeneratedBy`, `object/ObjectV3Full.lean:615`: `R` is what the Lean generator returns for
its own key, config and flags), and the composition
`lowering_equivalence_of_stages (R) (product) (hR : R.Valid) … (hsim : R.SimContracts product)
(hprog : R.ProgContracts product)` (`soundness/SoundnessV3.lean:1226`) is proved for every `R`.
`tr_blockSound` and `tr_blockProgress` are proved for every `R` (`Blocks/TraceReturn.lean`).
`Blocks/VkLoading.lean` is written for every `R` and stops at three named sorries (`:728`, `:743`,
`:756`). So the route D-P68 changed is the SEM half of the block rows, and only that.

### The decision

1. **Deliverable.** The headline is stated with no fixture in it:

   ```lean
   theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
       (hR : R.ValidV3) : LoweringEquivalenceV3 R product
   ```

   In words: for every program the Lean port of the generator emits, for any circuit in the
   supported class, the four conjuncts of the V3 headline hold. `poseidon_done`,
   `lowering_equivalence_poseidon` and `end_to_end_poseidon` are no longer goals.
2. **Rows.** `R.SimContracts product`, `R.ProgContracts product` and `TotalV3 R product` are proved
   from `hR : R.ValidV3` for every `R`. No block row, totality lemma or headline is stated or
   proved at a fixture. The staged architecture of D-P68 (`StageInv`, `BlockSim`, `BlockProgS`) is
   unchanged; its **technology clause** ("rows are proved per fixture on literal slices pinned by
   `native_decide`") is struck. The `wp` engine is kept as a tool and is run on parametric slices
   (card GEN.0 measures whether it can be).
3. **Validity is checked per circuit, not proved for all inputs.** `ValidV3 R` stays a hypothesis.
   For a given circuit it is discharged by computation, as `StatementsV3.lean:608-612` already
   says of every clause except the codec-bearing ones. A new circuit then costs one evaluation,
   not a new proof. Proving `ValidV3` for every supported input (so that no per-circuit check is
   needed) is **not** part of this decision.
4. **Fixtures are tests.** F1, and any further circuit, are kept for exactly these uses, none of
   which is an equivalence proof: W12 witnesses and falsifiers; the W14 run-it gates; the
   non-vacuity gate (`ValidV3` and the headline's hypotheses hold together at one real circuit,
   whose calldata the Lean verifier accepts); the reference gate against Rust; byte equality of
   the rendered contracts with the Rust artifacts. `native_decide` stays allowed there (D-P44).
5. **Axioms.** `lowering_correct` is closed under `[propext, Classical.choice, Quot.sound]` only.
   A `native_decide` axiom in its cone is a defect: with no fixture in the statement there is no
   fixture fact for one to carry.
6. **Supported class.** `SupportedV3` as typechecked (`StatementsV3.lean:592`): one phase, the
   instance shape of clause `instShape`, no accumulator, embedded quotient evaluator, separate key
   contract, production flags. Widening it is a separate decision per clause. **The IVC verifier
   is outside this class** (it uses the accumulator and the external evaluator, items X1 and X2 of
   PLAN-V3 §5); which other clauses it fails is unmeasured (card GEN.2).

### What it amends

| signed entry | amendment |
|---|---|
| D-P24 | withdrawn: the generic theorem is the deliverable, not a follow-on |
| D-P44 clause 4 | the claimed headline becomes `lowering_correct`; X4 is promoted from "later" to the goal. Clauses 1–3 stand |
| D-P60 | PLAN-V3 stays adopted; M5–M8 are restated by card PL.G (below). "Fixture F1" stays the name of the test circuit |
| D-P68 | technology clause struck (point 2). Architecture, the RECON.2 condition and "stop and re-plan with the human" stand |
| D-P69 | `Done` loses its fixture parameter in `headline` and `valid`; `gate`, `reference`, `artifact`, `vkArtifact` stay as fields about F1 |

D-P61–D-P67 are unaffected: the reference repairs, the curve model, the test SRS, the statement
surface and `ValidV3` are needed on either route.

### What it does to the cards (applied by card PL.G)

| cards | effect |
|---|---|
| M0–M4 (all `DG`, `REF`, `OBJ`, `ST` cards; SIM.1–SIM.5, SIM.7–SIM.12; RECON.1, RECON.2) | unchanged |
| T3.0, T3.1, T3.2, T3.5, T3.7, T3.8, HLP.1 | unchanged in aim; each "accept" slice gains its parametric form after GEN.0 |
| T3.3 (slice literals with pins), T3.11 (executable exhibit) | kept as tests only: they feed W14, never a proof |
| T3.4 (TraceReturn at the deployment) | dropped: the row is proved for every `R`; SIM.7 migrates it |
| T3.6 (vkLoading at the deployment) | replaced by GEN.1 |
| T3.9 (lagrange at the deployment) | restated for every `R`; its loops then have symbolic bounds, so it needs a loop-invariant rule, which is not built (PLAN-V3 §5 M5, "a loop hatch … is not built") |
| T3.10 (quotient numerator route) | route A (execute the emitted numerator) is per fixture and is excluded; route B (the interpreter loop refines the reference VM, proved once) is the only route |
| SIM.6, TOT.1, ROW.TP, ROW.Q, ROW.PCS, ROW.FP | restated for every `R` |
| PL.H, PL.E, DG.4 | restated: `lowering_correct`, the generic end-to-end theorem, the amended `Done` |
| M5 thresholds A–C (PLAN-V3 §5) | replaced by the thresholds of GEN.0 and GEN.1 |

### Conditions (applied, not chosen)

- D-P60's hold stands: no block row is briefed before PLAN-V3's M4 exit gate, and W14 stands.
- **GEN.0 runs first and alone.** It is a probe and proves nothing about the render.
- **If GEN.0 or GEN.1 misses its threshold: stop and re-plan the proof technology with the
  human.** Falling back to per-fixture rows is not pre-approved.
- Card PL.G rewrites PLAN-V3 §0, §5 M5–M8, §6, the affected cards, the goal prompt and the V3
  table. Until it has run, the per-fixture cards it restates are not briefed as written.

### Cost, stated honestly

Unmeasured. One block is closed for every `R`: TraceReturn, 25 tokens, 1,053 lines by `Step`
inversion. At that rate the 14,054 tokens of the F1 main block are out of reach by hand, so the
route is viable only if symbolic execution works with symbolic layout constants (GEN.0) and
symbolic loop bounds (T3.9 restated). Comparing three generated verifiers (Poseidon, RSA, IVC):
the helpers do not differ (0 of 219 code lines), key loading and the transcript parser differ in
7–11 of 42 and 5–11 of 98 lines, and the region from Lagrange to the final pairing differs in
622–845 of 1,094. The quotient and the opening check are the generated code proper. No estimate
is given before GEN.1 reports.

**Cards:** `GEN.0`, `GEN.1`, `GEN.2`, `PL.G` in `docs/plans/PLAN-V3-cards.md`, with rows in the V3
table of `QUEUE.md`.

Signed off: human (repository owner), 2026-11-17, in session at `c22b51a` — recorded in `design.md` D-P71.
