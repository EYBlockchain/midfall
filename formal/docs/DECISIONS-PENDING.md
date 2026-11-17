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

## 14. D-P72 — widen the supported class to the IVC verifier — **SIGNED OFF (2026-11-17), scope and clauses 1–10, recorded as D-P72 in `design.md`**

The human's instruction in the plan session, 2026-11-17: *"ensure we cover the IVC proofs with extra
pairing check, batched"*. That signs the **scope**: the generator theorem covers accumulator mode
with the batched final pairing, and the external quotient evaluator, for every render. The full
text is `design.md` D-P72. The ten clauses below are the plan session's design; the human signed
all ten the same day (*"sign D-P72 clauses 1 to 10"*), so the "if struck" column is history.

| # | clause | recommended | if struck |
|---|---|---|---|
| 1 | One theorem: state `lowering_correctW` now; prove the base class first, in the widened shape | approve | the base class is proved in the V3 shape; M9 restates vkLoading, quotientLin, finalPairing and the last stage |
| 2 | Accumulator kinds: point-and-scalar, no fixed-base tail | approve | no other kind has a circuit, so W12 cannot be met for it |
| 3 | Right-hand side `LeanAcceptsAcc`; two Rust corollaries, no iff, no probability claim | approve | there is no Rust function to state an iff against |
| 4 | `EvaluatorTrust` as a headline hypothesis keyed on the code-hash pin; object = the generated evaluator body | approve | the evaluator slot is a definition and the solc trust is prose only |
| 5 | Conjunct 2 keeps the zero gas oracle; rows proved for any gas | approve | conjunct 2 changes for every render (a frozen-surface change) |
| 6 | `idLaw` as a hypothesis in accumulator mode only | approve | add it to `G1CodecHeadlineLaws` for every render (frozen) |
| 7 | Test fixture F2 regenerated under one seeded test SRS; production render for byte equality only | approve | no acceptance gate for the widened class: non-vacuity is not shown |
| 8 | Add the `s_g2` equality assertion to the Rust e2e test | approve | the one-SRS assumption stays unchecked on the Rust side |
| 9 | Ask for a free-memory guard in the evaluator | approve | `EvalEntry.fmp` stays a trusted bound |
| 10 | Delete `Evaluator.rel_worldLocal` with the v1 track | approve | a sorried, argued-false lemma stays in the tree |

Evidence: `bash docs/plans/V3-evidence/check.sh widening` (four files, about one minute);
`docs/plans/V3-evidence/design/ivc-widening.md` and `ivc-object-reference.md`.

## 15. D-P73 — certify the generator itself: input-only hypotheses — **SIGNED OFF (2026-11-17), with clause 1 as amended; recorded as D-P73 in `design.md`**

Drafted 2026-11-17 at `cf00592`, at the human's request (*"i thought the codegenerator itself would
be certified"*; *"Yes, draft it"*), and completed the same day from a design pass, which amended
clause 1 in two points. The human was shown the amended text and signed it (*"Sign as amended"*).

Evidence: `docs/plans/V3-evidence/lean/object/GeneratorCertified.lean` (elaborates; 33 named open
lemmas; `generator_certified` and `generator_correct` proved from them), `CertMeasure.lean` (the
lemmas' decidable conclusions evaluated at F1), memo `design/generator-certified.md`
(`bash docs/plans/V3-evidence/check.sh object`).

**Why it is here.** D-P71's theorem is `lowering_correct (R) (product) (hR : ValidV3 R)`. `ValidV3 R`
is a hypothesis on the generator's **output**, discharged by computation for one circuit at a time
(D-P71 point 3). That is a generic proof plus a per-circuit check, not a certified generator.
The original plan (`PLAN.md` at `3d0d778`, §9.5) asked for the stronger form: hypotheses on the
generator's **input** only, with the printed text equal to the print of the emitted tree by
construction (`render_eq_print`).

**Two gaps, measured at `cf00592`.**

| gap | today | certified |
|---|---|---|
| G1. Text and tree | The port prints text from templates (`Midfall/Generator`). The proofs are about a tree built by a second emitter (`Midfall/Lowering/GenAst*.lean`). **At F1 they disagree today**: `codegenAgrees = false` (the tree has 6,761 tokens, the text 14,054; first difference at token 1,333, where the text has the accumulator helpers and the tree does not) and `codegenStruct = false` (the text parses to 74 top-level statements, the tree has 290). The tree emitter is incomplete: no tree for the accumulator helpers, the quotient helpers or the quotient numerator block | the tie holds for every input |
| G2. Output conditions | `ValidV3`'s output-side clauses are evaluated at one circuit | each is a theorem: "the generator succeeded on a supported input ⇒ the clause holds". 33 lemmas are stated; at F1 every decidable conclusion is true except the two codegen clauses of G1 |

### The decision

1. **Deliverable.** The headline's hypotheses are on the input only (typechecked):

   ```lean
   theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut)
       (hg : Generates gi o) (hs : SupportedInput gi) : (renderOf gi o).ValidV3
   theorem generator_correct_V3 (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) (product) :
       LoweringEquivalenceV3 (renderOf gi o) product
   ```

   `renderOf gi o` leaves no field of the render free. No per-circuit check remains in the
   theorem. (This strikes D-P71 point 3 and item X11.) After D-P72 the same statement is made
   for `ValidW` and `LoweringEquivalenceW`.
   - **AMENDED (a): the certified function generates the key payload too.**
     `generate gi` is `generateVk`, then the SRS fingerprint, then `generateAll`. With the payload
     taken as an input (as `generateAll` takes it today) the claim is false: flipping the `omega`
     word of the payload leaves the generator accepting, and the constants no longer agree with
     the key (measured). So the certified generator is `generate`, and `GenInput` is the key, the
     SRS, the point codecs, the configuration, the flags and two strings (`features`, `frDelta`)
     that no key determines.
   - **AMENDED (b): `SupportedInput` is not purely decidable.** It is: the scope clauses of the
     supported class (decidable; `layout` is dropped because it follows from generation
     succeeding); the input-only half of `EnvAgrees`; **two codec laws** (the generator's point
     encoders agree with the verifier's `toEip`/`encG2`) — hypotheses on the environment, of the
     same kind as the headline's codec hypothesis, not computations; `deltaLiteral`; and a **new
     size bound** (`numInstances < 2^64`, `k < 64`: Rust computes in `usize`, the port in `Nat`,
     and the header words wrap otherwise).
2. **G1, route A: the tree is the generator's output.** The assembly text the Lean generator
   prints is **defined** as the print of the emitted tree. The template-text port stays in the
   tree as a test oracle. Measured for this route: with solc 0.8.30 under the project's pinned
   options (`--via-ir --optimize --evm-version cancun --no-cbor-metadata`), the port's text and
   the variant with both assembly blocks replaced by the print of the tree compile to **identical
   runtime and creation bytecode** at F1 (with a Homebrew build of solc, not the pinned binary:
   to be repeated with the pinned one). Consequences:
   - the artifact gate against Rust compares **tokens**, or compiled bytecode, inside the assembly
     blocks (comments and layout are not printed); outside them the text is unchanged;
   - **the tree emitter must be complete first**: the accumulator helpers, the quotient helpers
     and the quotient numerator block need tree emitters (OBJ.13, OBJ.14, OBJ.15 and the
     numerator's line families). The block rows need those trees on any route;
   - `Constants.sol` is printed from the constant table (data first), which removes one lemma;
   - not taken: (B) prove the two emitters token-equal for every input — 11 renderer/emitter
     pairs, three trees missing, sized at 25–40 cards, and the kernel cannot reduce the tokenizer
     even on a 15-byte literal, so it needs symbolic string lemmas; (C) define the tree as the
     parse of the text — everything B costs, plus the parser, plus restating the rows.
3. **G2: one lemma per output clause**, proved for every supported input. The 33, by kind:
   (a) what the generator's own validation checks (4: S each); (b) syntactic invariants of the
   tree emitters — constants declared, calls resolved, no world write, exit discipline (4: M
   each), no shadowing and closedness (4: S); (c) builder lemmas (9: S; the payload header: M);
   (c)+(d) with a codec law (5: S to M). A clause that cannot be proved for every input as stated
   is a finding for the human, not a hypothesis to add. **Two are suspects today:** `v3_planMeta`
   (the plan's data is built from the final memory layout, Rust's from an intermediate one) and
   `v3_cdBound` (no generator check bounds the proof length; it may need a circuit-size bound in
   the supported class). Each is the first card of its family: confirm or refute before proving.
4. **What the Lean generator is for.** Certification is about the **Lean** generator. The Rust
   generator is not certified: it is tested against the Lean one. A contract is covered by the
   theorem when it was produced by the Lean generator, or when its text is token-equal (or its
   bytecode equal) to what the Lean generator prints for the same input — a computation, once per
   deployment. **Today the Lean `generate` cannot run on a real key** (there is no computable G2
   decompression), so the second form is the only one available until that is built.
5. **Still trusted** after this decision: the Lean printer `EVM.print` (the text given to solc is
   the print of the tree; a print/parse round-trip theorem would remove it); solc, through
   `EntryFrame`, `EvaluatorTrust`, constant inlining and the Solidity outside the assembly
   blocks; the precompiles; the two codec laws; the Lean kernel and the three standard axioms.
   Removed: the per-circuit evaluation of `ValidV3`, and the Lean token parser.

### What it amends

| signed entry | amendment |
|---|---|
| D-P71 point 3 | struck: validity is proved for every supported input, not checked per circuit |
| D-P67 (`ValidV3`, frozen) | unchanged as a statement; it becomes a lemma's conclusion instead of the headline's hypothesis |
| D-P69 / D-P71 (`GeneratorDone`) | `headline` is `generator_correct`; `artifact` compares tokens or bytecode inside the assembly blocks |
| PLAN-V3 §5 | a new milestone M10 "the generator is certified"; the tree-emitter cards (OBJ.13–OBJ.15, the numerator families) move in front of M5; route A's printing change lands with OBJ.7 |

### Conditions (applied, not chosen)

- The block rows of M5–M6 are proved against the tree emitters, as today. Route A changes which
  text is printed, not what the rows are about, so no row waits for this decision.
- `generator_certified` cannot be proved before the tree emitter is complete: two of its lemmas
  are false at F1 today for that reason alone.
- A confirmed suspect (`v3_planMeta`, `v3_cdBound`), or any clause false for some supported
  input, stops its card and goes to the human.

### Cost

Not estimated as time. In cards: about 33 lemma cards (most S, five M) plus the tree-emitter
completion, which M6 and M9 need anyway. Route B would add 25–40 cards; route A adds the printing
change and the token gate.

Signed off: human (repository owner), 2026-11-17, in the plan session at `cf00592` — recorded in `design.md` D-P73.
