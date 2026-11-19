# PLAN-V3 — prove the Lean verifier equivalent to the Yul emitted by the Lean codegen, on a real object, against a Rust-faithful reference

**STATUS: ADOPTED AND CUT OVER (2026-11-17).** The human signed D-P60–D-P69 (§2.2) after `53bf8c1`; `design.md`
quotes the sign-off (EXECUTION-V2 W2). Each decision's conditions are recorded in its entry and
still apply. The cut-over (card PL.0, §10.2) is done: `QUEUE.md`'s V3 table is the order.

**AMENDED BY D-P71, D-P72 AND D-P73 (signed 2026-11-17, `design.md`); restated by card PL.G.** The
deliverable is the generator theorem `lowering_correct` (§0): every block row is proved for every
render, and no row, totality lemma or headline is proved at a fixture. Fixtures are tests. The
supported class is widened to the IVC verifier (accumulator mode with the batched pairing check,
external evaluator: §5 M9). The generator itself is certified: the final theorem's hypotheses are
on the generator's input only (§5 M10). §0, §2.2, §5 M5–M10, §6, §7, §9 and §10.3 below are the
restated text.
Sections that describe M0–M4 are unchanged: they are needed on either route.

Handover brief for the orchestrator and for the human who signs. Self-contained: read §0–§4 before
touching anything. Paths are relative to `formal/` unless they start with `proofs/`.

> **For the human, before handing over.**
>
> 1. **Read `REVIEW-V3.md` §0–§1** (the verdict and the 46-row table), then §2 of this file: how V3
>    treats the decisions you signed at `5329c3f`, and ten new ones. Five touch the frozen surface
>    and one touches v1 files.
> 2. **Run the evidence once.** `bash docs/plans/V3-evidence/check.sh` typechecks every Lean spec
>    and every measurement this plan cites, against the built tree, in about six minutes, and
>    writes nothing into the repository.
> 3. **Sign or strike each decision in §2**, in `design.md`, with a W2 sign-off line. The
>    orchestrator does not act on an unsigned row.
> 4. **The execution rules are EXECUTION-V2's**, with the four additions of §4 (W12–W15). The cards
>    are in `PLAN-V3-cards.md` (99 cards, QUEUE format, written to be briefed to Sonnet 5.5 without
>    further design: §7); §5 gives their order and the exit gate of each milestone; §10 is the
>    cut-over from the live queue.

---

## 0. Objective, in one sentence

Prove, in Lean 4, **the generator theorem** (D-P71): for **every program the Lean port of the Rust
generator emits, for any circuit in the supported class**, **the body of `verifyProof`**, run in
the yul-semantics EVM dialect from the state Solidity hands it, **returns ABI `true` iff the
Rust-faithful Lean verifier accepts the decoded calldata, and otherwise reverts without touching
the world** — where *the Lean generator is checked against the Rust generator byte for byte* on
test circuits, *the Lean verifier is shown to agree with the Rust verifier on Rust-made proofs*,
the statement is *not vacuous* (at a test circuit the hypothesis holds and an accepted proof runs
to `return(true)`), and the modelled program is *never stuck*.

```lean
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product          -- V3-evidence/lean/statements/GeneratorTheorem.lean
```

**No fixture occurs in the statement, and no block row, totality lemma or headline is proved at a
fixture.** `ValidV3 R` says that `R` is what the generator returns for its own key, configuration
and flags, and that the circuit is in the supported class.

**The generator itself is certified (D-P73).** `ValidV3` is not left as a per-circuit check: it is
proved for every supported input, so the final theorem has hypotheses on the generator's
**input** only (§5 M10):

```lean
theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut)
    (hg : Generates gi o) (hs : SupportedInput gi) : (renderOf gi o).ValidV3
theorem generator_correct (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) (product) :
    LoweringEquivalenceV3 (renderOf gi o) product     -- V3-evidence/lean/object/GeneratorCertified.lean
```

`generate` is the whole Lean generator, key-payload generation included; the assembly text it
prints is defined as the print of the emitted tree. `lowering_correct` is the main lemma of
`generator_correct`; M5–M9 prove it, M10 proves `generator_certified`.

**The supported class.** `SupportedV3` as typechecked (one user phase, the instance shape of clause
`instShape`, separate key contract, production flags), **widened by D-P72 to accumulator mode with
the batched final pairing and to the external quotient evaluator**, which is what the generated
verifier of the IVC decider circuit uses (§5 M9). Until M9 lands, the theorem covers the base
class only.

**Fixtures are tests.** F1 (the `PoseidonExample` circuit, k = 6, test SRS) and F2 (the IVC decider
circuit, k = 20) are kept for exactly these uses, none of which is an equivalence proof: W12
witnesses and falsifiers; the W14 run-it gates; the non-vacuity gate; the reference gate against
Rust; byte equality of the rendered contracts with the Rust artifacts. `native_decide` stays
allowed there (D-P44) and must not occur in the cone of `lowering_correct`.

What changed from PLAN-V2 §0: the four italicised clauses (each was assumed by V2 and was false or
unchecked at `f2fe99b`). What changed with D-P71: the quantifier. Until 2026-11-17 this section
named the fixture render F1 as the object and `poseidon_done` as the goal (D-P24, D-P44 clause 4,
D-P68's technology clause); that text is in git history (`git show cf00592:formal/docs/plans/PLAN-V3.md`).

**Out of scope, stated plainly.** solc (trusted through `EntryFrame`, and for the external
evaluator through `EvaluatorFrame`, D-P72); gas; any on-chain contract (the only one in the
repository, Sepolia `moonlight-wrap`, is from superseded templates — REVIEW-V3 RV-17); the embedded
key; the Rust generator (it is tested against the certified Lean generator, not proved equal to
it); the security statements S1–S7.

## 1. Why V2 is revised (checked, not argued)

`docs/plans/V3-evidence/ReviewProbes.lean` elaborates without error at `f2fe99b` and fails when a
recorded fact is altered. Evidence classes are those of REVIEW-V3: **L** Lean-checked, **X**
executed, **S** source-checked, **R** read-confirmed by two reviewers.

| # | fact | class | finding | what V3 does |
|---|---|---|---|---|
| 1 | The Lean verifier groups multi-open commitments by value; Rust groups by allocation. The fixture key has five equal non-simple fixed commitments opened at `x`, so Lean returns `Error.opening` for every proof | L+S | RV-03 | REF.1: group by allocation slot |
| 2 | `Rotation` equality is structural; on the imported key all eight permutation columns hit a panic site | L | RV-04 | REF.2: equality of the integer |
| 3 | With both repairs shimmed (rotations canonicalised; a scratch copy of `phaseA` with slots assigned by a scratch `slotsFor`) and real key data, the staged Lean pipeline reproduces the Rust verifier's final MSM on the Rust proof: 10 challenges, 72 reads, 1 + 45 terms. The tree's own producers for REF.1 are untested. No Rust proof had ever been run through the Lean verifier | X | RV-14 | REF.8: this becomes a gate on tree functions |
| 4 | At the deployment `LeanAccepts` is identically false: the codec's `ofCompressed?` is the constant `none`. Key data are placeholders (19 identity commitments, `delta := 2`, `sG2 := g₂`) | L+S | RV-05 | REF.4, REF.6: computable real codec, real key data |
| 5 | The five curve axioms leave `g₁`, `g₂` unspecified; a pairing with named generators can be *constructed* on the three standard axioms | S+X | RV-15 | REF.5: construct it, delete the axioms |
| 6 | Frozen `calldataOf` repacks twice and never returns `.ok` | L | RV-06 | ST.4 |
| 7 | Every render satisfying the frozen `Valid` has `numPointSets = 0` (proved); a faithful plan has 3. Clauses 1 and 2 cannot both hold | L | RV-08 | ST.6 / OBJ.8 |
| 8 | Frozen `EnvAgrees` survives any `delta` and any commitments (proved) | L | RV-09 | `PayloadAgrees` |
| 9 | `rejects_of_not_accepts` alone yields rejection for every render; with one accepted calldata it proves `False` (machine-checked) | L | RV-10 | deleted; conjunct 3 from `TwoOutcomes` |
| 10 | `poseidon_valid` is a registered sorry whose negation is proved; `False` follows | L | RV-02 | W13; the sorry leaves the route |
| 11 | The AST has 8 functions, the text 15; 6761 of 14054 tokens; `Valid.codegen` is false at F1 (L) and, by argument, for every in-scope render (R) | L, R | RV-12 | G1 batch, then OBJ.2 |
| 12 | `Render.scope` omits `q_program_fail`, `q_pow5`, which sit inside the quotient slice | L | RV-13 | ST.3, in the same window as the G1 batch |
| 13 | All soundness for calldata Lean rejects before a snapshot exists rests on one monolithic sorry (unchanged by F.1, which proved the sequencing of the accepting side) | R | RV-25 | `StageInv` / `BlockSim`; composition proved |
| 14 | Calldata of 2²⁵⁶ bytes or more falsifies conjunct 1 (proved for the frame) | L | RV-07 | `EntryFrameV3.cdSize` |
| 15 | Nothing shows the modelled program is not stuck on rejected calldata | R | RV-11 | conjunct 4; card TOT.1 |
| 16 | One block of seven is closed, by hand and generically in `R`, in 1,053 lines (both contracts, with the existence half). A verified `wp` engine proves in 13 tactic lines that every run of the *literal* F1 TraceReturn slice ends in `return(abiTrue)` or a revert, for any calls and any gas. Transport to `poseidonRender` and the existence half are T3.4 and are not measured | X | RV-37 | T3.x |
| 17 | `checks.sh` is red at `f2fe99b`; CI never runs on this branch; no gate asserts the headline's axioms | X+S | RV-40–42 | DG.0–DG.7 |

**What V2 got right and V3 keeps.** The three-conjunct shape of the headline; the trusted
`EntryFrame`; no hypothesis over programs; consumer-first skeletons; the cone tool; W1–W11; the
proved TraceReturn rows; R.2's emission inventory and D-P52's batch.

**The order was the main defect.** V2 proved block rows about a program that is half the
generator's output, against a reference that rejects every proof, at a render whose `Valid` is
false. V3 fixes the reference and the object first, makes the model *run*, freezes repaired
statements only once they have witnesses, and only then proves.

## 2. Decisions

### 2.1 Signed while this plan was written (`5329c3f`, 2026-11-17) — how V3 treats each

D-P45–D-P59 were signed after the review's evidence was gathered and before this plan was finished.
V3 **builds on** them. Where the evidence of §3 shows a signed decision can be met more cheaply, or
needs a change, V3 says so and asks for a new signature in §2.2. Three rows of §2.2 *amend* a
signed decision and say so: D-P60 (the order D-P57 set for T.3, S.5, S.6), D-P62 (D-P55 steps
2–3), D-P63 (D-P58's fallback of keeping the committed proof), D-P66 (D-P45). Until those rows are
signed, the signed decisions apply as written.

| signed | what it says | V3 |
|---|---|---|
| D-P45 (amended) | The gate gains decode + parse + `snapshotOf` ok + `G1CodecLaws`; not `LeanAccepts`, "undischargeable at a real SRS" | **Builds on it** (Q0.5 runs as queued). Its reasoning is about a real SRS. On a known-trapdoor test SRS `LeanAccepts` is a 3-second evaluation, so D-P66 asks to add it back *for the fixture*, and to pin the hash (RV-35) |
| D-P46 | Three base-slot pins, after R.4 | **Implemented by `PayloadAgrees`** (D-P67), which adds the commitment, domain and `delta` pins D-P46 lacks (RV-09). R.6 may land first; `PayloadAgrees` then subsumes it |
| D-P47, D-P49–D-P52 | Fixture first; the `BlockSound` gate; the six pins; the PCS gates; the batched `Program.lean` re-hash | **Unchanged.** D-P52's batch needs one addition, D-P65 |
| D-P48 | `RETURN_MPTR` pin | **Unchanged**; subsumed later by the constants clause (D-P67) |
| D-P53 | W2 stands | **Unchanged.** Every row of §2.2 needs its own signature |
| D-P54 | No `hR : R.Valid` in the headline | **Unchanged.** M0 restates the *lemma* that consumes the refuted sorry, not the headline (§5 M0) |
| D-P55 | Gap B: G1 from bytes with no axiom; at most one G2 cyclicity axiom; name `s·G₂` from bytes by `Classical.choose` | **Step 1 implemented, better than asked**: the G1 decoder is *computable* (`g1CodecC`), and provably equal to the `Classical.choose` one on the EIP half. **Step 2's axiom is not needed** (D-P62): R.4's "first hour" has an axiom-free answer in §3 |
| D-P56 | `Valid.model` without a statement change | **Unchanged** (R.3). `Except.getOk` in `object/ObjectV3Full.lean` is a second route |
| D-P57 | WP-T before the loop-heavy rows; accept line "TraceReturn in under 100 lines"; fallback to hand proofs | **Met on the literal slice**: 13 lines (`prooftech/TR.lean`); the closed-slice form D-P57 asks for is T3.4's acceptance. T.2b lands the engine (T3.1, T3.4). D-P68 asks to replace the *fallback* (hand proofs) by measured thresholds, because the engine's open question is loops, not TraceReturn |
| D-P58 | Find the source of fixture non-determinism; fallback if it is in baseline code | **Source found**: `blind_quotient_limbs` draws from `OsRng` (`proofs/src/plonk/prover.rs:126`). That is baseline code, so D-P58's fallback (3) applies. D-P69 extends the export instead of seeding the prover |
| D-P59 | Fix `permutationCommitmentsMatch` | **Unchanged** (R.7 = REF.3) |

### 2.2 Signed (2026-11-17): D-P60–D-P69, D-P71, D-P72, D-P73

Recorded in `design.md` with their conditions. Two points of the sign-off narrow this table: the
optional `EntryFrameV3'` of row 64 is **not** taken, and the "if struck" fallbacks below are **not**
pre-approved (an unmet condition stops its card). "Frozen" means a `Frozen.sha256` re-hash.

| D-P | decision | recommended | touches |
|---|---|---|---|
| **60** | **D-V3: adopt this plan.** Stop SEM block rows about the present render (S.4–S.7, T.3–T.5, C.3, C.5, M.1) until M4's exit gate (W14); the rows already proved are kept. This holds T.3, S.5 and S.6, which D-P57 had sequenced after T.2b: an amendment of D-P57's order. Name the target "fixture F1", never "the deployment". Add rules W12–W15 (§4). The cut-over is §10 | approve | queue, docs |
| **61** | **Two further reference repairs** in v1 `Halo2/Exec` files, beside D-P59's: grouping by `CommitSlot` (REF.1) and semantic `BEq Rotation` (REF.2). They change what the frozen `LeanAccepts` *means*: today it is false for every proof of the fixture key | approve; recorded exception to "do not edit v1 `.lean` files", as D-P59 | v1 files |
| **62** | **Curve assumption (amends D-P55 steps 2–3).** (a) Replace the five D-P36a axioms by the constructed pairing `e(P, k) = k • P` on `(G₁z, G2fold, G₁z)` with `g₁ := g1zGen`, `g₂ := g2foldExp 1`; **no G2 cyclicity axiom**. (b) The SRS point is data: `poseidonRenderAt s`, with the hypothesis `SrsEncodes s` only for an SRS whose trapdoor is unknown, instead of `Classical.choose` over an axiom. (c) The deployment codec is the computable `g1CodecC` | approve. The trusted base shrinks to the standard three plus `native_decide` | `Assumptions/`, `Instances/` |
| **63** | **Test SRS for fixture F1 (amends D-P58's fallback 3).** Regenerate F1 with a seeded `ParamsKZG::unsafe_setup` whose trapdoor is exported, so acceptance, the `−s·G₂` pin and the generator's own SRS check become computations. Consequence: every F1 measurement of §3 and every `native_decide` pin on fixture data is re-taken on the new bundle (REF.11 runs first for that reason) | approve. If struck, F1 keeps the Filecoin SRS and the headline carries `SrsEncodes s` | fixture |
| **64** | **Statement surface V3** (frozen). `calldataOf`; `EntryFrameV3` (adds `cd.size < 2^256`); `G1CodecHeadlineLaws` as a hypothesis of every conjunct; conjunct 4 (totality); `EndToEndV3`. Optional in the same re-hash: zero memory from `TRANSCRIPT_MPTR` instead of from `0x80` (`EntryFrameV3'`, proved to be the weaker assumption) | approve, after ST.1 has landed the compiled text and M2 its witnesses | frozen |
| **65** | **Scope, in D-P52's re-hash.** The block scope becomes `[hoist helpers ++ hoist slices]` and `Render.slices` moves into `Statements.lean`. Without it, `prog_slices_decomp`'s second conjunct is false the moment G1.2 puts `q_program_fail` into a slice (RV-13). D-P52 covers `Program.lean` only | approve; **needed before the G1 batch merges** | frozen |
| **66** | **The gate, for F1 (amends D-P45).** `HypothesesInhabitedV3`: hash pinned to `keccak256`; `LeanAccepts` added back; `G1CodecHeadlineLaws`. Conditional on D-P63 | approve if D-P63 is approved; otherwise keep D-P45's text and pin the hash only | frozen |
| **67** | **`ValidV3`** (frozen). Seven clauses: `generated`, `inputs`, `program`, `noWriters`, `env`, `payload`, `supported`. Subsumes the 13-clause text, `vkPins`, `vkProgressPins`, D-P46's and D-P48's pins. Adds the structural tie `codegenStruct` (AST = parse of the text) | approve, after OBJ.7 shows `generateAll` reproduces the artifact | frozen |
| **68** | **Block architecture and proof technology** (refinable; recorded because it replaces signed shapes and D-P57's fallback). `StageInv`, `BlockSim`, `BlockProgS`; `Render.Rejects` becomes a corollary; `rejects_of_not_accepts`, `prefix_run_clean`, `runBody_iff_slices` are deleted. ~~Rows are proved per fixture on literal slices pinned by `native_decide`~~ (**struck by D-P71, row 71**: rows are proved for every render), with the verified `wp` engine. The certificate strategy is chosen by T3.0's table; the go/no-go thresholds of §5 M5 replace D-P57's hand-proof fallback | approve | `Blocks.lean` |
| **69** | **Definition of done and the fixture bundle.** DONE is the Lean structure `Done` (§6), checked by `#assert_axioms`; the closure fingerprint of the frozen statements joins `Frozen.sha256`; CI runs on `formal/baseline`. Exporter schema 2: `calldata.bin`, the EVM result, a mutation corpus with Rust verdicts, a manifest (extends D-P58) | approve | gates, CI, `proofs/solidity-verifier/tests` |
| **71** | **The deliverable is the generator theorem; fixtures are tests** (signed 2026-11-17; amends D-P24, D-P44 clause 4, D-P60, D-P68's technology clause, D-P69). `lowering_correct (R) (product) (hR : ValidV3 R)` for every render; no row, totality lemma or headline at a fixture; `ValidV3` is checked per circuit by computation; `native_decide` must not occur in the headline's cone | signed | §0, §5 M5–M8, §6, cards |
| **72** | **The supported class is widened to the IVC verifier** (signed 2026-11-17, scope and ten clauses): accumulator mode with the batched final pairing, and the external quotient evaluator, for every render. One theorem `lowering_correctW`; right-hand side `LeanAcceptsAcc` (complete against Rust, sound up to one `alpha`); `EvaluatorTrust` and `idLaw` as hypotheses; test fixture F2 under one seeded test SRS | signed | §5 M9, area WID |
| **73** | **Certify the generator itself: input-only hypotheses** (signed 2026-11-17, with clause 1 as amended; strikes D-P71 point 3). `generator_correct`: generation succeeded on a supported input ⇒ the program is correct. The certified function includes key-payload generation; the assembly text is the print of the emitted tree; 33 lemmas, one per output clause of `ValidV3`. Not provable before the tree emitter is complete | signed | §5 M10, area CERT |

**Must not be done:** deleting `SoundSide` from `Rejects` (RV-10).

**If a row is struck.** 61 struck: the reference stays unfaithful (it rejects every proof of the
fixture key) and no headline is worth proving; stop and re-plan. 62 struck: D-P55 applies as
signed, with its one axiom, and R.4 runs as queued. 63 struck: the gate stays D-P45's, §0's clause "an accepted proof exists and runs to
`return(true)`" is **not shown**, and the F1 headline is conditional on `SrsEncodes s` — whose
satisfiability then needs the G2 fact D-P62 removes, so either keep D-P55's one axiom for the
existence of `s` or report the headline as conditional on a hypothesis not known to be inhabited
(W7). 64 struck: the frozen headline stays false as written (RV-06, RV-07); stop after M2 and
re-plan. 65 struck: the G1 batch must not merge G1.2. 66 struck: as 63 for the gate. 67 struck:
fall back to `PlanMeta` + `PayloadAgrees` added to the 13 clauses (typechecked in
`StatementsV3.lean`) **plus a clause tying `R.qblocks` to the ported generator at `R.E.delta`** —
without it `delta` is unpinned, because `inputs.frDelta` is inert at F1
(`Generator/Artifacts.lean:130-134`). 68 struck: block rows stay generic in `R` and D-P57 applies
as signed.

## 3. Starting point: what is provided

Everything below typechecks against the tree at `f2fe99b`–`5329c3f` (no Lean source differs between
them). It sits under `docs/plans/V3-evidence/`, which no gate scans and `lake build` does not
compile. **These files are specifications and prototypes, not landed code**: each is landed by the
card named in the last column, which re-checks it at the then-current commit.

| file (`V3-evidence/lean/…`) | content | sorries | landed by |
|---|---|---|---|
| `../ReviewProbes.lean` | the review's machine-checked findings, self-checking | 0 | DG.0 |
| `statements/StatementsV3.lean` (990 lines) | the repaired surface in namespace `Midfall.LoweringV3`: `calldataOfV3`, `PlanMeta`, `PayloadAgrees`, `scopeV3`, `noShadowB`, `ExitDiscipline`, `TwoOutcomes`, `EntryFrameV3`, `G1CodecHeadlineLaws`, `BodyTotal`, `LoweringEquivalenceV3`, `RejectsV3`, `CompleteV3`, `TotalV3`, `HypothesesInhabitedV3`, `EndToEndV3`; **`lowering_equivalenceV3_of` proved** | 4 stated obligations | ST.1 |
| `statements/StatementsV3Deploy.lean` | **RETIRED (RECON.1b-iii)** - the fixture clause table now lives in the tree module `Midfall/Instances/StatementsV3Deploy.lean`; this file keeps `poseidon_payloadAgrees_not`, which FALS2 established is OPEN not refuted (its 5 point fields are undecidable: `g1CodecZ` is noncomputable), retained as a bare `Prop` so citations resolve and cannot be expressed against the single text | 0 | ST.1 |
| `statements/StatementsV3Falsifiers.lean` | proofs that the frozen text is broken (double repack, `numPointSets = 0`, padded calldata, `EnvAgrees` free in `delta` and commitments, `rejects_of_not_accepts` ⇒ `False`) | 0 | ST.1 |
| `soundness/SoundnessV3.lean` (1483 lines) | the staged Lean view (`rawDecode`, `pcsReads`, `linearizeFull`, `leanStage`), `StageInv`, `BlockSim`, `BlockProgS`, the exit scan; **all glue proved**, including `lowering_equivalence_of_stages`, `tr_blockSim`, `tr_blockProgS`, `fp_blockSim_of_blockSound`, `two_outcomes_of_exitShape` | 6 leaves | SIM.1–SIM.3 |
| `soundness/RawDecode.lean` | `decodeCalldata_eq_raw`, stand-alone | 0 | SIM.1 |
| `prooftech/WP.lean`, `WPBridge.lean`, `WPTac.lean` | generic demonic `wp` with **`wp_sound` proved**; `Bopen_sound` for any call relation and gas oracle; the `wp_run` driver | 0 | T3.1 |
| `prooftech/P1_Exec.lean` | `execOf` and **`execOf_lawful`**: the lawful executable dialect over the open Bridge dialect | 0 | T3.1 |
| `prooftech/Lits.lean` (generated), `GenLits.lean` | slice literals pinned to `sliceOf` by `native_decide` | 0 | T3.3 |
| `prooftech/TR.lean` | TraceReturn at the fixture, both conjuncts, 13 tactic lines | 0 | T3.4 |
| `prooftech/VK.lean`, `LAGP.lean`, `WPX.lean` | vkLoading (3 of 4 leaves), a lagrange loop prefix, and the stated word-layer lemmas | yes | T3.5–T3.7 |
| `reference/D1_Grouping.lean`, `D2_Rotation.lean` | the two Exec repairs as patched copies, with KATs | 0 | REF.1, REF.2 |
| `reference/RefModel.lean` | `g1zOfPair?`, the computable codec `g1CodecC`, the constructed pairing `pairingC`, `holds_exhibited_noAxiom` | 1 (`compressedEncoderFirst`) | REF.4, REF.5 |
| `reference/RunLib.lean`, `RunABC`, `RunD`–`RunG` | the staged runner on the Rust proof and its falsifiers | 0 | REF.8 |
| `reference/D5_KeyData.lean`, `D6_Render.lean` | real key data, `KeyAgrees`, `poseidonRenderAt`, `SrsEncodes` | 1 (the headline at `s`) | REF.6, REF.7 |
| `object/Parse1.lean` | the total Yul token parser and its round-trip measurements | 0 | OBJ.1 |
| `object/Plan2.lean`, `ObjectV3Full.lean` | the glue port of `LoweringPlan::new`, `generateAll`, `GeneratedBy`, `ValidV3`, `programOk` | 0 | OBJ.6–OBJ.8 |
| `object/Consts2.lean` | `expectedConsts`, `constsCoherent`, and two generic lookup lemmas | 0 | OBJ.4 |
| `object/Cov1.lean`, `Quot1.lean`, `Key1.lean`, `Plan1.lean` | measurements: coverage table, numerator composition, key coherence | 0 | — |
| `tooling/Done.lean`, `T1.lean`, `T7.lean`, `Report.lean` | `#assert_axioms`, `#cone_report`, `#sorry_sweep`, the closure fingerprint, `structure Done`, `not_done_today` | 0 | DG.1–DG.4 |
| `prooftech/TR.lean` (note) | states an all-runs fact on the literal slice with today's eight helpers as scope; it is not yet `BlockSim` at `poseidonRender` | — | T3.4 |

**Known gaps between the provided files** (each closed by the card named, before the statement it
concerns is signed). The six design passes worked independently; their files typecheck one by one
but are not yet one surface.

| gap | closed by |
|---|---|
| Two texts of `ValidV3` and of `PayloadAgrees` (`ObjectV3Full.lean:762`, seven clauses; `StatementsV3.lean:613`, eighteen); `programOk` lacks the exit scan, `cdBound` and the token clause; `PayloadAgrees.delta` pins a field that is inert at F1 | RECON.1 |
| `Render.SimContracts` as written is false for calldata of 2²⁵⁶ bytes or more: `Frame` carries no size bound | RECON.2 |
| `SoundnessV3.lean` concludes the three-conjunct V2 headline under the seven frozen codec laws; `StatementsV3.lean` wants four V3 obligations under `G1CodecHeadlineLaws`; two compositions and two exit scans exist | RECON.2, SIM.3 |
| `tooling/T7.lean`'s `GateAt` and `Done` are stated over the V2 names | DG.4 |
| `prooftech/TR.lean` is an all-runs fact on a literal slice with today's eight helpers as scope, not `BlockSim` at the render | T3.4 |
| The reference runs use a scratch `phaseA` and scratch slots | REF.1, REF.8 |

Also provided: `REVIEW-V3.md`; `V3-evidence/findings-full.md` (every raw finding);
`V3-evidence/design/*.md` (six design memos with the measurements behind this plan);
`PLAN-V3-cards.md` (99 cards).

**Measured at `f2fe99b`, fixture F1** (reproduce with `check.sh`):

| measurement | value | source |
|---|---|---|
| main block: text tokens / AST tokens / agreement | 14054 / 6761 / false | `object/Cov1.lean`; QUEUE R.2 |
| missing regions | accumulator helpers 823, quotient helpers 68, numerator 6384, PCS braces 18 | same |
| numerator: generated lines / interpreter template | 5431 / 953 tokens | `object/Quot1.lean` |
| whole main block through the token parser | 74 statements, prints back to the same 14054 tokens | `object/Parse1.lean` |
| `generateAll` on `cs.json` + payload vs Rust `Halo2Verifier.sol` | equal in 3023 of 3024 lines (`BUILD_ID`), nothing sliced | `object/ObjectV3Full.lean` |
| staged Lean pipeline on the Rust proof, repairs shimmed (a scratch `phaseA` and scratch slots) | all compared values agree with `trace.json`; 9 s | `reference/RunABC.lean` |
| the tree's own `prepare`, as is | panic `circuit.rs:2084`; with rotations fixed, `Error.opening` | `reference/RunG.lean` |
| today's *incomplete* AST (6,816 of 14,054 tokens) under the fuel interpreter, zero proof bytes, pairing mocked true | not stuck; returns `abiTrue` in about 10 s. Evidence about the interpreter, not about acceptance | `prooftech/E3.lean` |
| TraceReturn: generic hand proof of both contracts / `wp` all-runs proof on the literal slice | 1,053 lines / 13 lines, 27 ms tactic, 12 ms kernel (not the same statement: see §1 row 16) | `prooftech/TR.lean` |
| lagrange loop prefix, kernel check at fuel 40 / fuel 400 | 1.85 s / 33 s (fuel 40 is in `check.sh`; fuel 400 and the whole-slice run are design-pass measurements, `design/prooftech.md` §2.3–2.4) | `prooftech/LAGP.lean` |
| static point sets at F1 | `[[0],[0,1],[0,1,-9]]` | `soundness/PointSets.lean` |
| project declarations the frozen statements reach / in hashed files | 3448 / 102 (design-pass measurement; `Report.lean` is not run by `check.sh`) | `tooling/Report.lean` |

## 4. Ground rules

PLAN-V2 §4 (rules 1–12) and EXECUTION-V2 §5 (W1–W11) stand. Four additions, each a V2 failure.

- **W12 Falsifier and witness before a brief [O].** No sorried statement is briefed until the tree
  holds (a) a witness that its hypotheses are jointly satisfiable at F1, and (b) a falsifier: a
  mutated object for which the statement is false or, for a generic statement that is true of
  every object, a weakening (one hypothesis dropped) that is exhibited false. Four sorried leaves in the V2 cone were false as
  stated (RV-10, RV-21–RV-23) and one was refuted (RV-02); none had been attacked before briefing.
  A statement the orchestrator cannot attack in 30 minutes gets a PROBE card first.
- **W13 No refuted hole [O+S].** A registered sorry whose negation is proved in the tree is deleted
  in the same commit as the refutation. Its consumer takes the statement as an explicit hypothesis
  **only if that hypothesis is not itself a closed proposition refuted in the tree**; otherwise the
  consumer is deleted too (a lemma with a refuted closed hypothesis is the vacuity trap D-P54
  rejects). A refutation *by instance* — hypotheses shown to hold while the conclusion fails —
  counts, and `#assert_no_refuted_sorry` (DG.6) must detect both forms. A cone that contains a
  refuted leaf is reported as UNREACHABLE, never as a number.
- **W14 Run it before proving it [O].** No PROOF card about the Yul side is READY until the
  *executable exhibit* for its object exists: the modelled program runs the fixture calldata to the
  intended outcome under the fuel interpreter, and a mutant does not (EXECUTION-V2 §4,
  "outcome-level acceptance", applied to the model itself). V2 proved rows about a program that had
  never been run.
- **W15 Frozen means the meaning, and re-hashes are batched [O+H].** The frozen pin includes the
  closure fingerprint of the frozen statements (DG.3), so an edit to an unhashed definition that
  changes what the headline says reddens the gate. A frozen edit is made only in a card whose brief
  names the decision, shows the one-line hash diff, and carries the witness and falsifier of every
  changed statement. Batch frozen edits per milestone. Five re-hashes in all: the two the queue already holds (Q0.5
  for D-P45, R.6 for D-P46), then the G1 batch together with ST.3 and OBJ.2's signature edits
  (M2), the headline surface (M3) and `ValidV3` (M3).

Two V2 rules need a correction of fact. Rule 9 says keccak is `@[extern]`; it is a pure Lean
definition, so `native_decide` runs compiled code for the same definition. Rule 12's "five D-P36a
curve axioms" disappears if D-P62(a) is signed: the headline's axioms are then the standard three
plus the recorded `native_decide` axioms.

**Lean traps met while preparing this plan** (add to rule 11): never let `simp` see
`List.replicate (2 ^ 256) _`; `Op`, `Inv`, `calldataOf` and `parseTrace` are ambiguous across
namespaces — qualify them; the kernel ignores `@[irreducible]`, so stop markers must be structures;
`Meta.whnf` is about 100 times slower than the kernel reducer on `wp` terms; never `simp` a
continuation-passing `wp` over a whole slice; `leave` and `end` are tokens; `lake env lean -o`
outside `formal/` needs `--root`.

## 5. Milestones and work packages

Eleven milestones, M0–M10. Each has an **exit gate** that is a command with an expected output; a milestone
is not done until its gate is green at the tip. Cards are in `PLAN-V3-cards.md`; this section gives
the context, the Lean specification, the proof strategy and the order. With one subagent the queue
order is M0, then M1 and M2 interleaved (they do not depend on each other), then M3, M4, M5, M6,
M7, M8, with M9's object and fixture cards interleaved from M2 on and its row cards after the
base-class row each one extends. T3.0, T3.1, T3.3, GEN.0, GEN.3, GEN.4 and WID.2 do not depend on
M1–M4 and may be pulled forward whenever the queue is blocked. The *row* cards of M5 (GEN.1
onward) do wait: W14 asks for the program to have run on a test calldata first, which needs
REF.11 (M1) and DG.5 — a test, not a premise of any proof.

```
M0 stop the line ──┬── M1 reference runs ──────────┐
                   ├── M2 object complete, generated ┼── M3 surface V3 frozen ── M4 it runs, and accepts
                   └── (T3.0, T3.1, T3.3) ───────────┘                              │
                                                     M5 proof technology calibrated ┴── M6 block rows ── M7 headline ── M8 end to end
                   M9 widen to the IVC verifier: fixtures and object from M2 on; RECON.3 before M6; rows after M6; WID.H after M7
```

**Every card, by milestone** (the queue order within a milestone is the order listed; decision
cards REF.D, OBJ.0, ST.2, SIM.0 and OBJ.17 are the signatures of §2.2 and run when their evidence is
in the tree):

| milestone | cards, in order |
|---|---|
| M0 | DG.0, DG.1, DG.2, DG.6, PL.1, DG.7, DG.8, ST.1, PL.0, OBJ.17; PL.G (done 2026-11-17: this restatement) |
| M1 | REF.D, REF.11 with OBJ.11 (one Rust run: the F1 bundle), REF.2, REF.1, REF.3 (= live R.7), REF.4, REF.5, REF.5g, REF.6, REF.8, ST.18, REF.9, REF.10, REF.12 |
| M2 | OBJ.0 (D-P65), live G1.4b, OBJ.1, then ONE re-hash: live G1.1 and G1.2, OBJ.2 (which replaces G1.3), ST.3; then ST.11, ST.12, OBJ.4, OBJ.5, OBJ.6, OBJ.7, OBJ.16 |
| M3 | RECON.1, RECON.1b, RECON.2, ST.2, SIM.0, OBJ.0 (D-P67), ST.4, ST.5, ST.6 with OBJ.8, REF.7, ST.15, OBJ.9, ST.7, SIM.1, SIM.2, SIM.3, SIM.7, SIM.8, ST.8, SIM.4, DG.3, DG.4 |
| M4 | REF.13, REF.14, DG.5, T3.11, ST.14, ST.17, OBJ.10, OBJ.12 |
| M5 | T3.1, T3.1b, GEN.0, GEN.3, GEN.4, GEN.5, T3.2, T3.5, HLP.1 (HLP.1.a–c), GEN.1, T3.8, T3.9 (T3.9.a–h), ST.16, T3.10, SIM.6 (SIM.6.a–d), ST.13; optional: T3.0; dropped: T3.7; tests only: T3.3 (and M4's T3.11). T3.4 dropped; T3.6 replaced by GEN.1. ROW/T3.9/SIM.6/HLP.1 children that have no card yet are issued by their parent SKELETON card |
| M6 | RECON.3 (D-P72 clause 1, first), SIM.5 (with ST.9, ST.10), SIM.9, SIM.10, SIM.11, SIM.12, ROW.TP (ROW.TP.1–9), ROW.Q (ROW.Q.1, ROW.Q.6 and the children it issues), ROW.PCS (ROW.PCS.2, ROW.PCS.9), ROW.FP, then TOT.1 (TOT.1.a) |
| M7 | PL.H, DG.9 |
| M8 | PL.E |
| M9 | WID.2, WID.1, WID.3, WID.4, GEN.2, WID.5, WID.6, WID.7, WID.8, WID.9, WID.11, WID.12, WID.13, WID.14, WID.15, WID.16, WID.17, WID.19, WID.H |
| M10 | CERT.0, CERT.1 (suspects, early), CERT.2, CERT.3, CERT.4, CERT.5, CERT.6, CERT.7, CERT.8, CERT.H |
| emitters, no longer optional | OBJ.14, OBJ.15 (the numerator helpers and the interpreter template as trees: needed by ROW.Q, M6); OBJ.13 (the accumulator helpers as a tree: needed by WID.12, M9) |

OBJ.3 is superseded by ST.3 and is not run.

### M0 — Stop the line; make the gates honest (INFRA; about 9 cards)

**Context.** The tip fails its own gates, CI does not run, the register holds a refuted sorry, and
nothing asserts the headline's axioms. Every later exit gate depends on tools that tell the truth.

**Cards.** DG.0 (gates green at the tip: move the KAT pin to the measured total and fix the two
`expect TRUE` annotations; the sorry register is already in sync since F.1); DG.1 (`#assert_axioms`); DG.2 (register keyed by declaration, from the environment);
DG.6 (`#assert_no_refuted_sorry`); DG.7 (CI on `formal/baseline`); DG.8 (STATUS generated from the
report); PL.1 (W13: take the refuted sorry out of the route); ST.1 (land `LoweringV3` as a
*staging* module with its fixture and falsifier files — no frozen edit); PL.0 (the cut-over, §10).

**Lean specification** (`tooling/Done.lean`, typechecked; tested in `tooling/T1.lean`):

```lean
-- fails the build unless the axioms of `thm` are within the named list, plus native_decide
-- axioms generated under the listed owner declarations (checked by statement shape and
-- declaration range, so a hand-written axiom with a generated-looking name is rejected)
#assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound
  [propext, Classical.choice, Quot.sound] native []          -- passes today
#assert_no_refuted_sorry [Midfall]                            -- errors today on poseidon_valid
#cone_report Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon
-- at f2fe99b: 11 sorried leaves = 10 OPEN + 1 REFUTED + 0 VACUOUS  [UNREACHABLE]   (9 after F.1)
-- after PL.1 that theorem is gone; the root is Midfall.LoweringV2.lowering_equivalence_of_blocks
```

**Strategy.** All of M0 is tooling that already runs in scratch. The one design point is W13 applied
to the present tree (PL.1). `poseidon_valid` is deleted, **and so is its consumer**
`lowering_equivalence_poseidon`: restating it with `(hR : poseidonRender.Valid)` would give a lemma
whose hypothesis is refuted in the tree, provable by `absurd` — exactly what D-P54 rejects. Until
M7 the cone root is the generic `lowering_equivalence_of_blocks`, then the four V3 obligations
(M3); the name `lowering_equivalence_poseidon` is not used again until M7. D-P54's sentence "DONE
requires `poseidon_valid` proved" is kept in substance: DONE requires `poseidonRender.ValidV3`
proved (§6). The second refuted sorry, `identityCorrespondence_of_bridge`
(`Lowering/QvmFold.lean:327`, refuted by instance in the same file at `:718`, `:749`), is restated
or deleted in the same card; DG.6's detector is extended to the by-instance form.

**Exit gate.** `bash scripts/verify.sh` exits 0 at the tip, and its report prints
`sorry_sweep: … 0 REFUTED` and `axiom_sweep: ok`. CI shows one green run on `formal/baseline`.

### M1 — The reference runs, and accepts, on the F1 bundle (ALG; 14 cards)

**Context.** The equivalence is only as good as the Lean verifier's fidelity to Rust, and that had
never been tested on a Rust proof (RV-14). With two shims the Lean pipeline already agrees with
Rust on every value the trace records (§3). M1 makes that true of the *tree's* functions, and then
shows acceptance.

**F1 is fixed first.** Under D-P63 and D-P69, REF.11 runs before anything else in this milestone
and, in ONE Rust run, writes the `poseidon-testsrs` bundle: seeded test SRS with its trapdoor,
`vk.json`, `cs.json`, `params.json`, `proof.bin`, `trace.json`, `calldata.bin`, the EVM result,
the mutation corpus, `build.json`, and **both `.sol` dumps** (OBJ.11's export, folded in). A new
SRS changes the commitments, `−s·G₂`, `BUILD_ID` and `Halo2VerifyingKey.sol`, so every later gate
of M1–M4 reads this bundle and only this bundle. The Filecoin bundle is kept as a second instance
of the reference gate (REF.8), where it shows agreement but not acceptance. If D-P63 is struck,
F1 stays the Filecoin bundle, REF.12 is dropped, and the headline carries `SrsEncodes s`.

**Cards, in order.** REF.11 with OBJ.11 (the bundle), REF.2 (rotation), REF.1 (grouping), REF.3
(`WellFormed`), REF.4 (codec), REF.5 + REF.5g (constructed pairing; gates follow the axiom
removal), REF.6 (real key data), REF.8 (the reference gate), ST.18 then REF.9–REF.10 (the
encoder-first codec law), REF.12 (acceptance at the known trapdoor). Needs D-P61, D-P62, D-P63,
D-P69; REF.3 is the live card R.7 (D-P59, signed).

**Lean specification.**

```lean
-- REF.2  Exec/Circuit.lean:130   (reference/D2_Rotation.lean)
inductive Rotation where | cur | next | prev | value (v : Int)
def Rotation.int : Rotation → Int | .cur => 0 | .next => 1 | .prev => -1 | .value v => v
instance : BEq Rotation := ⟨fun a b => a.int == b.int⟩

-- REF.1  Exec/Query.lean:53      (reference/D1_Grouping.lean)
inductive CommitSlot where
  | advice (proof col : Nat) | instance_ (proof col : Nat) | permProduct (proof set : Nat)
  | lookupM (proof lookup : Nat) | lookupHelper (proof lookup j : Nat) | lookupAcc (proof lookup : Nat)
  | trash (proof idx : Nat) | fixed (col : Nat) | sigma (i : Nat) | anon (n : Nat)
  deriving BEq, DecidableEq, Repr
inductive CommitmentReference (F C : Type) where
  | onePiece (slot : CommitSlot) (com : C)
  | linear (points : Array C) (scalars : Array F) (labels : Array CommitmentLabel)
-- kzgCommitBeq, one-piece arm:   | .onePiece s _, .onePiece t _ => s == t

-- REF.3  Exec/VerifyingKey.lean:114
permutationCommitmentsMatch : vk.permutation.commitments.size = vk.cs.permutation.columns.size

-- REF.4  (reference/RefModel.lean) - a COMPUTABLE decoder into the real curve group
def g1zOfPair? (pt : Nat × Nat) : Option G₁z        -- range, on-curve, r-torsion; membership
                                                     -- from G1PointCount.torsion_eq_zpowers_gen
def g1CodecC : G1Codec G₁z                           -- ZCash 48-byte compressed + EIP-2537
theorem g1CodecC_ofEip : g1CodecC.ofEip? = g1CodecZ.ofEip?          -- proved

-- REF.5  (reference/RefModel.lean) - no axiom
instance pairingC : AdmissiblePairing G₁z G2fold G₁z   -- e(P,k) = k • P, g₁ := g1zGen, g₂ := g2foldExp 1
theorem holds_exhibited_noAxiom : ∃ product, Eip2537.Holds g1CodecZ g2CodecFold product
```

**Strategy.**
- *REF.2* is a three-line change; two KAT clauses flip (`Circuit.lean:1892`, `:2083`) and that is
  the falsifier. Twelve declarations use the derived instance directly; all pick up the new one.
- *REF.1.* The label is **not** a usable key: 13 `NoLabel` queries cover 7 allocations, and
  label-keyed grouping also fails on the fixture's 49 queries. Carry an explicit slot. The Rust
  premise to record (P-ALLOC): slot equality is `std::ptr::eq` because each slot names one element
  of one live `Vec`; the committed instance relies on the modelled caller building a fresh local.
  Producers change at `Verifier.lean:757-798`, `Permutation.lean:265-306`, `Logup.lean:196-211`,
  `Trash.lean:135-137`; nine pattern matches gain a binder. KATs: the fixture shape gives six
  entries; the same slot twice at one point still gives `Error.opening`.
- *REF.4.* Decoding into `G₁z` is not a discrete-log problem: `torsion_eq_zpowers_gen`
  (`G1PointCount.lean:238`) supplies the membership proof, so the decoder is computable and runs in
  the VM (one torsion check 128 ms). Decoder-first is by construction (re-encode test); the
  encoder-first law is REF.9–REF.10 (M4).
- *REF.5.* `G2fold` is a discrete-log carrier and `Additive G₁z` a one-dimensional `ZMod r` space,
  so the pairing is a definition. `Holds` then says of the real EVM exactly what it said before:
  G1ADD, G1MSM, MODEXP agree with `Externals.lean`, and PAIRING_CHECK returns 1 iff
  `k₁P₁ + k₂P₂ = 0`. `check_frozen_axioms.py:126-131` and `check_hypothesis_bundles.py:130`
  hard-code the five axioms and change in the same commit.
- *REF.8* runs the tree's `prepare` (staged: `parseTrace`, `readAlgebra`, `linearize`, `phaseA/B/C`,
  `DualMSM.split`, `MSMKZG.eval`) on `proof.bin` in the model `(G₁z, G2fold, G₁z)` and compares with
  `trace.json`: 10 squeezes, the 72-read log, 1 + 45 MSM terms, both pairing inputs.

- *REF.8 must test the tree's producers.* The scratch run assigns slots with a scratch `slotsFor`
  (proof index fixed to 0) and a scratch copy of `phaseA`; the REF.1 producer patch was never
  compiled as patched files. REF.8's acceptance therefore requires the slots produced by the
  tree's `collectQueries` to equal `slotsFor` element by element on the fixture's 49 queries, and
  the read log to be compared byte for byte.
- *REF.12, acceptance.* `check_iff_g1` (proved) makes the final check `s • left = right` in `G₁z`
  once `s` is data; with the exported trapdoor it is a 3-second evaluation.
- *REF.9–REF.10, the encoder-first codec law.* `g1zOfPair?_g1zPair` is proved; what remains is
  that `fpSqrt` recovers `y` from `x` and the sign bit (`p ≡ 3 mod 4`, `ZMod.euler_criterion`) and
  that the three flag bits are free because `x < p < 2^381`. KATs on 50 fixture points hold.

**Exit gate.** In `Instances/`, calling tree functions only: `#eval referenceGate_ok -- expect
true` (about 9 s) on both bundles; `#eval fixture_leanAccepts_ok -- expect true`
(`verifyNative … = .ok ()` on the F1 proof); `#eval mutants_leanRejects_ok -- expect true` (Lean's
verdict class equals Rust's on every mutant). Falsifiers pinned red: `delta := 2` changes exactly
the `-G` scalar; one flipped evaluation byte changes the MSM; one flipped byte of `π` gives
`Error.transcript`. `#print axioms` of `holds_exhibited_noAxiom` and of
`g1CodecC_compressedEncoderFirst` is the standard three.

**Limits of M1.** One circuit, one proof, single-proof slots; the multi-proof slot indices and the
`fewer-point-sets` branch are unexercised.

### M2 — The object is complete and generated (GEN; about 10 cards)

**Context.** The theorem's program must be the generator's whole output, and the render must be the
generator's output for the verifier's own key. Today it is neither (RV-08, RV-09, RV-12). The
orchestrator's G1 batch (D-P52) is in flight and M2 builds on it.

**Cards, in order.** G1.4b; OBJ.1 (parser); then **one re-hash of `Program.lean` and
`Statements.lean` together** (D-P52 extended by D-P65), containing: the live G1.1 and G1.2
(structured emitters, as carded), OBJ.2 (the numerator, and `Program.lean`'s signature edits:
`mainAsmRaw`, `helpersOf`, `sliceOf`, `mainClosed`, `codegenStruct`), and ST.3 (the scope: without
it `prog_slices_decomp`'s second conjunct is false the moment G1.2 lands — RV-13). Then ST.11,
ST.12, OBJ.4 (constants), OBJ.5 (object fingerprint KAT), OBJ.6–OBJ.7 (the glue port and
`generateAll`), OBJ.16 (probe three more fixtures).

**G1.3 is replaced, not run as carded.** The live card sizes the numerator as 895 generated tokens
and 5,489 of template; measured (`object/Quot1.lean`) it is 5,431 generated and 953 of template,
so a structured emitter for it as carded is about six times the work the card assumes. OBJ.2
lands the numerator as the parse of the model's own lines; OBJ.15 (optional) later gives the
953-token interpreter template a structured emitter.

**Lean specification.**

```lean
-- D-P65, Statements.lean:109  (statements/StatementsV3.lean:209-252)
def Render.slices (R) : YulBlock := R.slice .vkLoading ++ … ++ R.slice .traceReturn   -- moves in
def Render.scope (R) (c) (g) : FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) R.helpers ++ hoist (Bridge.Dialect c g) R.slices]
theorem prog_slices_decomp (R) (hns : noShadowB R = true) (vkAddr qAddr) (c) (g) :
    R.prog vkAddr qAddr = R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ R.slices ∧
    [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = R.scope c g

-- OBJ.1 / OBJ.2  (object/Parse1.lean, ObjectV3Full.lean)
def parseTokens : List String → Option YulBlock            -- total, fuel-structural, 120 lines
def codegenStruct (main : YulBlock) (m : Model) : Bool :=  -- AST = parse of the generator text
  (match parsedGuard? m with | some g => SyntaxEq.stmtsBeq (abiGuardBlock m) g | none => false) &&
  (match parsedMain? m  with | some g => SyntaxEq.stmtsBeq main g | none => false)

-- OBJ.4  (object/Consts2.lean)
def expectedConsts (pv : PlanView) (m : Model) : List (String × Nat)    -- the 90-entry table as data
def constsCoherent (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone && constLinesLiteral m && constTableOf m == expectedConsts pv m &&
  ((expectedConsts pv m).map Prod.fst).Nodup &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x

-- OBJ.6 / OBJ.7  (object/Plan2.lean, ObjectV3Full.lean)
def generateAll (feat : Features) (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (cfg : GeneratorConfig)
    (payload : Halo2VerifyingKey) (inputs : ArtifactBuildInputs) (flags : RenderFlags) :
    Except Fault GenOut                                     -- plan, qblocks, model
def Render.GeneratedBy (R) : Prop :=
  ∃ out, R.generated = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧ out.model = R.model
```

**Strategy.**
- *Scope.* Two candidates were compiled against copies of the five block files. `[hoist (R.prog 0
  0)]` breaks `fail_lookup := rfl` (`TraceReturn.lean:405`) for a generic render;
  `[hoist helpers ++ hoist slices]` compiles all five files with **no proof edit**. Take the second.
  `prog_slices_decomp` is proved by pushing `inlineContractConstants` through `++` with
  `inline_append` under `noShadowB` (its side condition, true at F1), then `hoist` over `++`
  (`List.filterMap_append`). `hoist_prog_addr_indep` becomes a corollary.
- *Structural tie.* Token equality cannot see builtin-versus-call (RV-27). The parser resolves it
  with `EVM.mkCall`, and every existing emitter except PCS is *already* `stmtsBeq`-equal to the
  parse of its region. The accumulator and quotient helpers land as structured emitters (G1.1,
  G1.2), diffed against the parse. The numerator lands as a parse of the model's own lines
  (OBJ.2); its six generated line families (5,431 tokens) stay parses permanently: they are the
  output of the ported `compactQuotientComputationBlocks`.
- *What the tie means for a parsed region — stated plainly.* Where the AST region *is*
  `parseLines (render m)` and the text is built from the same `render m`, token and structural
  agreement hold **by construction**: a mutation of the template changes both sides. For those
  regions nothing is checked by `codegen`; what is trusted is the parser–printer round trip
  (measured: print ∘ parse is the identity on all 14,054 tokens) and the parser's builtin-versus-call
  resolution (`EVM.mkCall`). The per-region mutation falsifier therefore applies to structured
  emitters only. The content of a parsed region is checked elsewhere: by `GeneratedBy` (the lines
  are the ported generator's output), by the artifact gate (they equal Rust's), and by the block
  proofs (they compute the Lean quotient).
- *Constants.* The table is read back by string parsing (RV-26). `expectedConsts` states it as data
  from the plan view; one Bool then yields every address pin as a six-line generic lemma (two are
  proved in `Consts2.lean`: `VK_MPTR`, `RETURN_MPTR`). D-P46's table half and D-P48 are subsumed.
- *Generated-by.* Every heavy callee of `LoweringPlan::new` already exists in the tree; about 480
  Rust lines of glue do not. The scratch port reproduces `vk_mptr 0x2900`, `proofLen 4320`, the
  88-byte VM program and its constant *equal to the Rust payload words*, and the whole
  `Halo2Verifier.sol` but for `BUILD_ID`. Port under rules R1–R11; the base key payload stays an
  input (it needs the prover SRS), tied by `PayloadAgrees` (M3). Three typed-in inputs are wrong
  today and are replaced by derived values: `quotientStackWords` (24, derived 25), `sortedSimple`,
  the PCS sizes.

**Exit gate.** `#eval programOk poseidonPv poseidonM -- expect true` (structural and token
agreement, constants, calls resolved, no shadowing, closed including the guard block);
`#eval generated_matches_artifact_but_buildId -- expect true`; a one-literal mutation in each
*structured-emitter* region reddens the first; `delta := 2` reddens the second. `Frozen.sha256`
changed exactly once in this milestone.

### M3 — The statement surface V3 is frozen, with witnesses (STATEMENT; about 14 cards)

**Context.** Statements are frozen only now, when the reference and the object exist to witness
them: after M1 the codec laws hold at `g1CodecC` and the F1 proof is accepted by Lean; after M2
the render is generated. One witness is still missing at the freeze — the calldata-level gate
(`poseidon_inhabited`, M4) — so the freeze is re-checked at M4's exit, and W12 is met for the
headline by the M1 exhibits plus `lawsV3_satisfiable_at_G1z` until then. Two signed re-hashes: the headline surface (D-P64, D-P66) and `ValidV3` (D-P67). The
block-contract architecture (D-P68) lands in the same milestone because the headline's composition is its consumer.

**Cards.** RECON.1 and RECON.2 (one surface, one composition — first), ST.2 (sign-off), ST.4, ST.5, ST.6 / OBJ.8 (the two cut-overs), REF.7 and ST.15 (key
pins and fixture data), OBJ.9 and ST.7 (the clause table at F1), SIM.0–SIM.3 and SIM.7 (the staged
contracts and the proved composition; migrate the proved rows), DG.3 (closure fingerprint), DG.4
(`Done` stated, with `not_done_today`), ST.8 (skeleton of `TwoOutcomes`).

**Lean specification — the headline** (`statements/StatementsV3.lean:818`, verbatim):

```lean
def LoweringEquivalenceV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → obs.isReturn →
        SoundSide R H cd → obs.returnData = abiTrue ∧ LeanAccepts R H cd) ∧
    (LeanAccepts R H cd → CompleteSide R H cd →
        (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀) ∧
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs →
        obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)) ∧
    BodyTotal R product vkAddr st₀

structure EntryFrameV3 … : Prop where            -- EntryFrame, plus:
  cdSize : cd.size < 2 ^ 256
structure G1CodecHeadlineLaws (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedEncoderFirst : ∀ Q, c.ofCompressed? (c.toCompressed Q) = some Q
  compressedWidth : ∀ Q, (c.toCompressed Q).size = g1CompressedWidth
  toEip_one : c.toEip 1 = natToBytesBE 0 128
def GasTotal (g : ExternalGas) : Prop := ∀ st, ∃ w, g.Gas st w
def BodyTotal (R) (product) (vkAddr) (st₀) : Prop :=
  ∀ g, GasTotal g → ∃ obs, RunBody R vkAddr 0 (callsOf product) g st₀ obs
def TwoOutcomes (R) : Prop :=
  ∀ vkAddr c g st₀ obs, RunBody R vkAddr 0 c g st₀ obs →
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)
def HypothesesInhabitedV3 (R) (product) : Prop :=          -- hash PINNED to keccak256
  ∃ W Lyt vkAddr cd st₀, DeploymentV2 R W keccak256 vkAddr ∧ EntryFrameV3 R W Lyt keccak256 cd st₀ ∧
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ G1CodecHeadlineLaws R.E.g1 ∧
    LeanAccepts R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd
def calldataOfV3 (R) (π) (inst) :=
  Lowering.repackThenEncode (p := p) R.cfg.numInstances
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π inst

-- PROVED, no sorry: the headline is four independent obligations
theorem lowering_equivalenceV3_of (R) (product) (h2 : TwoOutcomes R) (hrej : RejectsV3 R product)
    (hcomp : CompleteV3 R product) (htot : TotalV3 R product) : LoweringEquivalenceV3 R product
```

**Lean specification — validity.** Two typechecked texts exist and they differ; **RECON.1 makes
them one before D-P67 is signed.** The target is the seven-clause structure of
`object/ObjectV3Full.lean:762`, shown here with the conjuncts RECON.1 must add marked `+`:

```lean
structure Render.ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  generated : R.GeneratedBy                       -- replaces circuitMeta, layout, invariants, model
  inputs    : R.inputs.numInstances = R.cfg.numInstances ∧ … -- unchanged
  program   : programOk R.pv R.model = true      -- codegenStruct ∧ constsCoherent ∧ callsResolved ∧
                                                  -- noShadow ∧ closed (with the guard block) ∧
                                                  -- 0x80 ≤ TRANSCRIPT_MPTR   (ObjectV3Full.lean:747)
                                                  -- + the frozen token clause  + the exit scan
                                                  -- + cdBound: proofEnd + 32 + 32·n < 2^256
  noWriters : NoWriters (R.prog 0 0)
  env       : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  payload   : PayloadAgrees R                     -- ObjectV3Full.lean:687: digest, header words,
                                                  -- omega, omegaInv, nInv, G1 base, G2 base, −s·G2,
                                                  -- fixed and permutation commitments via E.g1.toEip.
                                                  -- NOT delta: `inputs.frDelta` is inert at F1; delta
                                                  -- reaches the program through `generated`
  supported : SupportedV2 R                       -- its `wf` field means D-P59's repaired WellFormed
```

**Lean specification — the block contracts** (`soundness/SoundnessV3.lean`):

```lean
def StageInv (R) (H) (vkAddr) (cd) (k : Checkpoint) (V) (st) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ BaseInv R k V st ∧
    LeanRaw R cd k ∧ Mirror R cd st k ∧ Agree R H cd k V st
-- Agree k := ∀ ms instW inst, Decoded R cd ms instW inst →
--              ∃ S, leanStage R H inst ms k = .ok S ∧ Inv R.E R.params k R.pv S V st
def BlockSim (R) (q : Partial) (H) (vkAddr) (c) (g) (cd) : Prop :=
  StmtsContractAll (R.scope c g) (R.slice q) (fun V st => StageInv R H vkAddr cd q.pre V st)
    (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSim R q H vkAddr cd V' st' o ∨
      (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
  StmtsContractAll (R.scope c g) (R.slice q) (fun V st => Poisoned R H vkAddr cd V st)
    (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
      (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))
-- exitSim .traceReturn := o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd

-- PROVED in the evidence file from its leaves AND these five hypotheses (the fourteen rows are
-- inside hsim, hprog): no case split on LeanAccepts, no Rejects. It concludes the V2 headline;
-- RECON.2 re-targets it at the four V3 obligations.
theorem lowering_equivalence_of_stages (R) (product) (hR : R.Valid) (hpins : SimPins R)
    (hexit : R.ExitOk) (hsim : R.SimContracts product) (hprog : R.ProgContracts product) :
    LoweringEquivalence R product
```

**Strategy.**
- *Why the staged shape is forced.* Two order mismatches rule out simulating against the existing
  snapshot stages. (1) The contract learns that a G1 word is a group element *last* (G1MSM in the
  PCS block), while `decodeCalldata` checks it *first*; `decodeCalldata_eq_raw` (proved) splits the
  decoder into the raw half the parser mirrors and the `ofEip?` half. (2) The parser writes
  `x1..x4`, `fCom`, `π` before any algebra, while Lean produces them after `linearize`; hence a
  transcript-only Lean prefix (`pcsReads`, `snapshotXcriptRun`). So the invariant has an
  unconditional part (`BaseInv`, `LeanRaw`, `Mirror`: facts about bytes) and a decode-relative part
  (`Agree`). **Rule for every block proof: nothing needed before the PCS exit may live in `Agree`.**
- *Composition.* `seq7` chains the seven rows with `StmtsContractAll.append`; `run_split`/`run_join`
  relate a run of the program to a run of `preBlock ++ slices` existentially in the prefix endpoint,
  so no determinism lemma is needed (RV-21). `soundness_of_sims` reads `LeanFinal` off the
  TraceReturn exit arm. All proved in `SoundnessV3.lean`; its cone has seven leaves
  (`snapshotOf_prepareMsgs`, `noWriters_prog`, `prog_slices_decomp`, `prefix_prog`, `prefix_sim`,
  `quiet_init`, `Run_worldEq_of_noWriters`). One of them, the V2 `prog_slices_decomp`, is false
  under name shadowing (RV-21) and is replaced by ST.11's `prog_slices_decompV3 (hns)`.
- ***The size bound must reach the rows* (found in review of this plan).** `Render.SimContracts`
  quantifies over every `cd` with only `SoundSide`, and `Frame` (`Blocks.lean:56-64`) carries the
  calldata with no size bound. Take `cd ++ 2^256 zero bytes`: `StageInv .start` holds (`Agree` is
  vacuous, the calldata does not decode), vkLoading's `calldatasize` check passes modulo 2^256 and
  the block exits normally with `success = 1`, but `StageInv .vk` needs the length equation in
  `Nat`. So `SimContracts` as written in the evidence file is **false** — RV-07 one layer down.
  Repair (RECON.2): `Frame` gains `cdSize : cd.size < 2 ^ 256` (a §6 refinement of the allowed
  kind: a field added to `Frame`); the prefix rows derive it from `EntryFrameV3.cdSize`; the
  vkLoading row also uses `cdBound`. The padded calldata is that row's W12 falsifier.
- *The evidence files do not yet compose into the V3 headline.* `lowering_equivalenceV3_of` wants
  `TwoOutcomes R` for every state, `RejectsV3` and `CompleteV3` under `G1CodecHeadlineLaws`;
  `SoundnessV3.lean` delivers `two_outcomes_of_exitShape` under an entry frame, `rejects_of_sims`
  under `SimPins`, and `completeness_of_progs` under the seven frozen codec laws, and concludes the
  three-conjunct V2 headline. The statements pass also sketched a second composition from the old
  block rows. **RECON.2 lands exactly one**: `rejectsV3_of_sims`, `completeV3_of_progs` (rows gated
  on `G1CodecHeadlineLaws`; `hasMultiPointSet` moved into `programOk`), conjunct 3 by
  `twoOutcomes_of_scans`, totality by TOT.1; `lowering_equivalence_of_stages` and ST.5's block-row
  composition are not landed.
- *Conjunct 3* needs no Lean-side fact. `exitScan` is a decidable structural scan: no `return`,
  `stop` or `selfdestruct` outside the tail; `break`/`continue` only in loops; `leave` only in
  functions. `tr_exit_any` (proved) says every run of the TraceReturn slice halts with a revert or
  with `return(abiTrue)`. `two_outcomes_of_exitShape` (proved) follows from one meta-lemma,
  `quiet_init`: scanned code ends `normal` and not halted, or with a non-committing halt. That is
  the same `Step` induction `Run_worldEq_of_noWriters` needs — prove one generic per-op lemma and
  instantiate it twice (SIM.4, SIM.5; ST.8–ST.10 are the same work and are merged into them).
- *Two scans, one definition.* The statements and soundness passes each wrote an exit scan
  (`ExitDiscipline`, `ExitOk`). SIM.3 lands exactly one; it is a conjunct of `programOk`.
- *Totality* is stated under the **honest** relation: a permissive run exists trivially by failing
  the first precompile call, so the permissive form says nothing. `runBody_mono` (ST.13) transfers
  an honest run to a permissive one. It is true because all nine `staticcall`s target the four
  precompile addresses and the honest relation answers every request there; what remains is
  closedness, call resolution and loop termination. **It does not come for free from the
  soundness proofs.** `wp_sound` with `Bopen` is an all-runs result. Existence needs `wpSS_exists`
  (T3.2) at the *functional* transformer `Bfun` for the honest dialect, per slice and from every
  `StageInv` state (not only accepted calldata); a gas-obliviousness lemma (the program executes
  no `gas()`, so a run does not depend on the oracle, which lifts the `ofFun 0` rows to every
  total oracle); prefix totality; and composition through `total_append` and `run_join`. That is
  card **TOT.1**. The symbolic execution is shared with the `BlockSim` proof of the same slice,
  which is why TOT.1 runs after the rows.
- *Fault table.* `design/soundness.md` §5 lists 28 fault sites of the Lean pipeline against the Yul
  check that mirrors each. Three have **no** matching check and need a side condition or a pin:
  the logup panic (`SoundSide`), `x^n = 1` (`CompleteSide`), and — new — **`x = 0`**: Rust and Lean
  deduplicate opening points by value and reject, while the contract reverts only if some static
  point set has two points. At F1 the sets are `[[0],[0,1],[0,1,-9]]`, so the decidable pin
  `hasMultiPointSet` closes it; a render whose sets are all singletons would need `x ≠ 0` in
  `SoundSide`. SIM.11 lands the table as a KAT and as the statement `lean_fault_table`, which is
  false until M1 lands and is its acceptance test.
- *Cut-over order* (W15): ST.3 with the G1 batch (M2); then ST.4 + ST.5 (headline, composition);
  then ST.6 / OBJ.8 (`ValidV3`). Land the falsifiers first: one cites `rejects_of_not_accepts`,
  which the cut-over deletes, so it is restated over a verbatim `Prop` copy.

**Exit gate.** `sha256sum -c Frozen.sha256` green with the closure fingerprint line (DG.3 lands
after M1, because D-P61's edits change the closure of `LeanAccepts`); `#cone_sorries` of each of
the four V3 obligations (`rejectsV3_of_sims`, `completeV3_of_progs`, `twoOutcomes_of_scans`, the
totality statement) prints the leaf list RECON.2 names, none of which is the V2
`prog_slices_decomp`; `#assert_no_refuted_sorry` passes; the clause table at F1 (ST.7) prints
every `ValidV3` clause `true`, or names the clause that is not and why; `not_done_today` is
re-proved against `ValidV3` and says why.

### M4 — It runs, and the reference accepts (KAT/ALG; about 10 cards)

**Context.** W14. Before any block proof: the modelled program must run a real accepted calldata to
`return(abiTrue)`, the Lean verifier must accept the same proof, and mutants must fail on both
sides the same way. This is the validation of the Yul model, the program and `EntryFrame` that
PLAN-V2 delegated to a "revm differential (M4)" that never existed. It also discharges the
non-vacuity gate.

**Cards.** REF.13–REF.14 (probes: `snapshotOf` against Rust's intermediate values; the calldata
leg), DG.5 (the fixture calldata as a pure term), T3.11 (the
executable exhibit), ST.14, ST.17 (the gate: route and proof), OBJ.10 and OBJ.12 (the artifact
gate with nothing from the artifact).

**Lean specification.**

```lean
def poseidonParamsAt (s : ZMod blsR) : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s)
def SrsEncodes (s : ZMod blsR) : Prop := g2foldToEip (Multiplicative.ofAdd s)⁻¹ = poseidonNegSG2Bytes
theorem check_iff_g1 … : DualMSM.check g (poseidonParamsAt s) = true ↔ s • left = right   -- proved

-- the four exhibits the report must print PRESENT (each an `#eval … -- expect true` in Instances/)
fixture_leanAccepts_ok      -- verifyNative E Features.solidity (poseidonParamsAt s) vk inst proof = .ok ()
fixture_returns_abiTrue_ok  -- Interp.run (execOf …) fuel (asmOf pv m vk 0) (entry cd) = ok (_, st, .halt),
                            --   st.halted = some (.ret, abiTrue), world unchanged; equals evm.json
mutants_leanRejects_ok      -- every mutation of mutations.json: Lean verdict class = Rust verdict class
mutants_revert_ok           -- the same mutants: the modelled program reverts

theorem g1CodecC_compressedEncoderFirst : ∀ Q : G₁z, g1CodecC.ofCompressed? (g1CodecC.toCompressed Q) = some Q
theorem poseidon_inhabited : HypothesesInhabitedV3 poseidonRender (pairingProductOf …)
```

**Strategy.**
- *The bundle is M1's.* F1, its trapdoor, its calldata and its mutation corpus come from REF.11;
  Lean's acceptance of the proof is REF.12. M4 adds the Yul side and the calldata-level gate.
- *Reproducibility.* The prover's blinding is random (`proofs/src/plonk/prover.rs:126`), so byte
  equality across runs is not available and not needed: the gates compare Lean with the
  `trace.json` and `evm.json` *of the same bundle*, pinned by a manifest. Do not seed the prover
  (that would touch `proofs/src`; D-P58's fallback).
- *The executable exhibit* uses `execOf_lawful`: the open Bridge dialect with the honest precompile
  graph is a lawful executable dialect, so `Interp.run` is adequate there (`honest_adequacy`).
  What exists today is weaker than the exhibit: the *incomplete* AST (6,816 of 14,054 tokens) runs
  to `return(abiTrue)` on zero proof bytes with the pairing mocked true. That shows the interpreter
  works and the present AST is not stuck on that input, nothing more. The exhibit T3.11 must
  deliver is the complete program (M2) on the F1 calldata with the honest precompile model at the
  exported trapdoor, agreeing with `evm.json`.
- *The gate* (`poseidon_inhabited`). `LeanAccepts` at `keccak256` on the fixture calldata follows
  from `fixture_leanAccepts_ok` (by `native_decide` in `Instances/`) through `verifyNative_iff_msgs`
  and the calldata round trip (REF.14 probes the calldata leg first; if the round-trip lemmas are
  not available yet the gate takes the decoded messages directly). ST.17 is a PROBE that picks the
  route before any proof is briefed. `returns_of_inhabited` (proved) then says: headline plus gate
  give an honest run that returns ABI true.
- *Artifact gate.* `generateFromKeyData` reads only `cs.json`, `vk.json`, `params.json`,
  `build.json`; both `.sol` files byte for byte. Missing today: the split of `generateVk` into base
  and reservation loop (OBJ.10), two G2 points in EIP-2537 form, and the two `BUILD_ID` inputs
  (OBJ.11 exports them). Interim gate: everything but the `BUILD_ID` line.

**Exit gate.** `bash scripts/verify.sh --report` prints `exhibits: 4 PRESENT, 0 MISSING of 4`;
`#print axioms poseidon_inhabited` has no `sorryAx`; `artifact_gate_poseidon` is `true` with
`#cone_avoids_decls poseidonRender [poseidonVerifierDump, poseidonVkDump]` passing.

### M5 — Proof technology for every render, calibrated on three blocks (SEM/ALG)

**Context (D-P71).** A row is proved for every render `R` from validity, not at a fixture. A slice
of `R` is `Inline.inlineContractConstants (constTableOf R.model) (GenAst.emitPartial R.pv q)`
(`Program.lean:125`), so a row is a statement about an **emitter** of `Midfall/Lowering/GenAst*.lean`
at every plan view, composed with the inliner at every constant table. Three things that were
numerals on a literal slice are now variables: the layout constants (each use site is a stuck
`match consts.lookup x`, named `vkSite` in `Blocks/VkLoading.lean:94`), the function scope (the
hoisted helpers of `R`), and loop bounds. M5 finds out, on three blocks and with thresholds fixed
in advance, what a proof costs under those three.

**What is already proved for every `R`** (`V3-evidence/lean/soundness/GeneratorRows.lean`,
`check.sh soundness`): the composition (`sim_rows`, `prog_rows`, `rows_correct`'s reduction,
`lowering_correct_of_rows`, `rejectsV3_of_rows`); the helper scope (`helpers_eq`, `fail_is`,
`batch_invert_is`, `helpers_funDefs`: all eight helpers resolve, in every render's scope, to the
body their emitter prints); normal forms of emitted slices on a symbolic table and layout
(`lagInner_length`, `qlinInner_length`, `lag_sq_loop_form`, by the six-line tactic `kernel_rfl`:
the kernel reduces the inliner where the elaborator's `rfl` times out). In the tree:
`tr_blockSound`, `tr_blockProgress` (TraceReturn, 1,053 lines by `Step` inversion) and
`Blocks/VkLoading.lean` up to three named sorries.

**Cards.** T3.0 (certificate-cost probe), T3.1 (land the engine and `execOf`), T3.2 (totality:
`wpSS_exists`), T3.5 (word and memory layer), T3.8 (field-arithmetic bridge), **T3.1b** (land `wp_run`), **GEN.0** (land parametric execution), **GEN.3** (the loop rule),
**GEN.4** (the inliner over a concatenation), **GEN.5** (land the row statements), **HLP.1** with HLP.1.a–c (helper summaries), **GEN.1** (vkLoading for
every render: calibration B), **T3.9** with T3.9.a–h (lagrange: calibration C), **T3.10** (the
quotient contract, route B), **SIM.6** with SIM.6.a–d (the prefix rows), ST.16, ST.13. T3.3 and
T3.11 are tests (W14). T3.4 and T3.7 are dropped (proofs on the fixture's literal slices); T3.6 is
replaced by GEN.1; T3.0 is optional (it measures unrolled loops, which no proof uses any more).
T3.2 also proves the liveness form `wpSS_exists_C`.

**Lean specification** (`prooftech/WP.lean`, `WPBridge.lean`, `WPX.lean`, `VKP.lean`,
`LoopRule.lean`; `soundness/GeneratorRows.lean`):

```lean
theorem wp_sound (hB : BSound D B) (hC : CSound D C) : ∀ n : Nat, …        -- proved, [propext]
theorem Bopen_sound (c : ExternalCalls) (g : ExternalGas) : BSound (Bridge.Dialect c g) (Bopen c g)
theorem wpSS_exists (hB : BLive D B) (hC : ∀ funs fn args st, C funs fn args st = none) …
-- parametric execution (GEN.0): the vkLoading body with its constant sites as free variables
def vkBodyV … ; theorem vkBody_eq_vkBodyV … ; theorem vk_all_param …       -- VKP.lean
-- loops with a symbolic bound (GEN.3)                                      -- LoopRule.lean
-- helper scope, for every render (HLP.1.a; proved)
theorem helpers_eq (R) : R.helpers = …      theorem fail_is (R) …      theorem batch_invert_is (R) …
-- the rows, for every render (GeneratorRows.lean; each is a named open obligation with children)
theorem lag_blockSim (R) (product) (hR : R.Valid) … : BlockSim R .lagrange H vkAddr (permissive (callsOf product)) g cd
theorem rows_correct (R) (product) (hR : R.Valid) :
    R.ExitOk ∧ R.SimContracts product ∧ R.ProgContracts product     -- SimPins comes from the codec laws
```

**Strategy.**
- *The shape of a block proof, unchanged.* Two layers, never mixed. **SEM**: the slice computes a
  word-level function of its input memory, or reverts. **ALG**: that word function agrees with
  the Lean stage, with no Yul in sight. What changes is the SEM half: it is proved about the
  emitter's output for every plan view.
- *Normal form first.* Each emitted group is brought to a normal form with its constant sites as
  variables (`kernel_rfl`, GEN.4 for concatenations), then executed. A proof never unfolds the
  inliner by `simp`.
- *Constants are `Nat` variables with hypotheses.* A site is `Expr.lit (.number v)` with
  `consts.lookup "X" = some v`; the facts a proof needs about `v` (it is the plan view's address;
  it is below `2^256`; two windows are disjoint) come from `ValidV3` clauses, never from a
  numeral. The table of which clause supplies which fact is M6's "premise gaps".
- *Helpers are summarised once.* The scope is a variable, so a helper cannot be executed at a call
  site: each helper gets one call summary with its `CSound` proof (HLP.1), stated as "the scope of
  a valid render defines `f` with this body" (`helpers_eq`).
- *Loops need a rule.* With a symbolic bound a loop cannot be unrolled. GEN.3 lands one invariant
  rule (starting point `Midfall/Yul/Contracts.lean:298`, `ExecLoopAll.countdown_or_halt`) with a
  witness and a falsifier; T3.9.a is its first use on a real loop and fixes the script every later
  loop card copies.
- *Lists need induction over the emitter.* Where the generator maps over a list (user phases,
  lookups, point sets, quotient blocks), the proof is an induction over that list, with one lemma
  per emitted group. The transcript parser's schedule is data (`tpEvents`), and its read
  projection is the layout's slot list (`tp_events_slots`, witnessed and falsified at F1).
- *The `wp` engine runs a parametric slice once its constant sites are variables* (measured by
  the design pass, `prooftech/VKP.lean`, `design/prooftech-generic.md`). On the vkLoading body:
  as emitted, `wp_run` stops at the first stuck `vkSite … consts` (P1); after rewriting with
  `vkBody_eq_vkBodyV` it closes **7 leaves in 86–100 ms, kernel 225–243 ms** (P2), against 4
  leaves, 106 ms and 365 ms for the literal fixture slice. `vk_all_param` is proved for every
  constant table and every scope, with the memory fact (`vk_all_param_mem`), and needed no side
  condition. GEN.0 lands it and re-measures at the tip (point P).
- *The existence half needs a liveness form of a call summary.* `wpSS_exists` assumes no
  summaries; without the `fail` summary three leaves stay stuck at the scope lookup. `CLive` and
  `wpSS_exists_C` are stated (`VKP.lean`); `Cfail_live` is proved; GEN.1 proves `wpSS_exists_C`.
- *The loop rule exists* (`prooftech/LoopRule.lean`, no sorry): `allRuns_for_cons_wp` takes an
  invariant and one-iteration `wp` (`wpIter`), with no variant and no count; witness
  `sumLoop_all` for every `n < 2^256`, falsifiers for a dropped preservation premise and a
  dropped bound. GEN.3 lands it; T3.9.a is its first use on a real loop.
- The cards of M5–M6 state their children as facts about an emitter's output, whatever tactic
  proves them, so a later change of technology changes line counts and not statements.

**Go / no-go thresholds (fixed now).**

| point | card | accept | if missed |
|---|---|---|---|
| P | GEN.0 | at the tip, `vk_all_param` closes its 7 leaves: kernel ≤ 2 s, elaboration ≤ 10 s, no heartbeat raise (design pass: 0.24 s, P2) | the verdict is no longer P2: **stop and ask the human** (D-P71) |
| B | GEN.1 | the vkLoading row closed for every `R`; ≤ 300 new lines; elaboration ≤ 30 s, kernel ≤ 5 s; axioms: the standard three, no native | **stop and re-plan the proof technology with the human**; per-fixture rows are not a fallback |
| L | GEN.3, T3.9.a | the loop rule landed with witness and falsifiers (proved in the design pass); `lag_sq_loop` closed in ≤ 120 lines | the rule is restated with the human; no loop-bearing row is briefed |
| C | T3.9 | the lagrange row closed for every `R`; no `maxRecDepth` or `maxHeartbeats` raise | **stop and re-plan with the human** |
| D | T3.10 | a typechecked contract `QInterpRefines` and a measured prototype of the interpreter refinement on one opcode arm | the numerator is re-planned with the human |

**Exit gate.** The rows for `.traceReturn`, `.vkLoading`, `.lagrange` and the prefix are proved for
every `R` against `StageInv` (`#assert_axioms` each: the standard three, empty native list), with
the ETA rows of points P, B, L, C. No schedule for M6 is written before point C.

### M6 — The remaining block rows, for every render (SEM/ALG; sized at point C)

**Context.** Four rows remain: transcriptParser, quotientLin, pcs, finalPairing, then totality.
Each starts with a restated SKELETON card (`ROW.TP`, `ROW.Q`, `ROW.PCS`, `ROW.FP`, `TOT.1`) whose
children are in area GEN-ROWS of the card file; each child lands one named obligation of
`GeneratorRows.lean`.

| row | what the emitter prints | induct over / loop bound | stated children | hardest point |
|---|---|---|---|---|
| transcriptParser (`GenAst.lean:1073-1178`) | fixed head and tail; one walk loop per section; four loop-free helpers; eleven squeezes | `userPhases`, `L.lookups`; section `byteLen/128`, `numInstances`, `evals.byteLen/32` | `tp_computes`, `tp_agrees`, `tp_poison`, `g1walk_loop_sem` (one lemma for six sections), `tp_events_slots`, `inlineScan_append`; `tp_blockSim` is proved from the first three | the inliner over a symbolic list (GEN.4); the transcript buffer's capacity (gap PG-TPBUF) |
| quotientLin (`GenAst.lean:840-864` today) | the linearization scope (one loop, bound `k`); the interpreter template; six generated-line families | the interpreter loop reads its program from memory; list inductions over `R.qblocks` | `qlin_split_loop`; the contract `QInterpRefines`; builder correctness | **no tree emitter exists for the numerator** (gap PG-Q-OBJECT: OBJ.14, OBJ.15 and the six line families). Route B only. Builder correctness comes into scope: `Qvm.lean:631, :698, :713, :768, :995`, `QvmFold.lean:338, :376, :434`. This is the largest new cost of D-P71 |
| pcs (`GenAstPcs.lean:1128`) | eight blocks at F1 (225 statements) | the point sets; the MSM loops | `pcs_b2_sem`, `decode_exists` | the coverage invariant; the row is false if the PCS emitter faults (the slice is then `[]`): gap PG-PCS-EMIT |
| finalPairing (`GenAst.lean:649`) | fixed text, two arms (`hasAcc`) | none | `ec_pairing_sem`; `fp_poison` is proved | restate `ec_pairing_contract` at `permissive (callsOf product)` (RV-23); the accumulator arm is WID.15 |
| totality | — | — | `gasFree_of_valid`, `runBody_gas_oblivious`, `block_live`, `prefix_live`; `total_correct` is proved from them | "no `gas()` in the program" becomes a clause or a lemma about the emitters (gap PG-GAS) |

**Premise gaps: facts a generic row needs that validity does not state today.** Each is a
typechecked `def PG_*` in `GeneratorRows.lean` §2 and is **never** added as a hypothesis by a
subagent. Each evaluates `true` at F1. Where it comes from:

| gap | the missing fact | supplied by |
|---|---|---|
| PG-SIMPINS | codec laws, `hasMultiPointSet` | the headline's codec hypothesis (`simPins_of_laws`), RECON.2 step 4. `SimPins` is **not** a consequence of validity (`simPins_not_of_valid`); `rows_correct` does not claim it |
| PG-EXIT | `R.ExitOk` (the exit shape of the pre-block and the six slices) | **RECON.1 addition 5**: one exit scan; today `ExitOk` and `ValidV3.exitDiscipline` are two different scans and no lemma links them |
| PG-NOSHADOW | `R.consts.lookup "r" = none` | the single text's `noShadow` clause (RECON.1) |
| PG-CONSTS-LAG, -TP | the table equals the plan view's addresses (6 + 23 names) | `programOk`'s `constsCoherent` (the 7-clause object text; in the single text after RECON.1; OBJ.4, OBJ.8) |
| PG-FRMOD | the table's `FR_MODULUS` is `p` | `constsCoherent` together with `EnvAgrees.modulus` (RECON.1 addition 6) |
| PG-PARSER | the parser's inputs come from the model, `rawSlots` from the plan | `GeneratedBy` (OBJ.7; in the single text after RECON.1) |
| PG-TPBUF | the transcript region holds the longest absorb run and is disjoint from the walk windows | **not stated anywhere today**: RECON.1 addition 2 (a new layout clause, or a lemma from `memory.map.WellFormed`); ROW.TP step 3 checks which |
| PG-NEGLAG | `2 ≤ numNegLagranges` | **RECON.1 addition 4** (RECON.1 step 4 deletes `WellFormedV3`, so the fact must be kept explicitly). If the generator accepts a key without it, the lagrange row is false there: a finding for the human |
| PG-PCS-EMIT | the PCS emitter does not fault and is non-empty | `GeneratedBy` (generation succeeded) |
| PG-G2SLOTS | the G2 slots | `PayloadAgrees` |
| PG-G1ID | the `g1_identity` window lies above `0x80` | **RECON.1 addition 3** (no clause gives it today, and `EntryFrameV3'` was declined) |
| PG-GAS | `gas()` only as the gas argument of a call | **RECON.1 addition 1** ("no `gas()`" would exclude every external-evaluator render) |
| PG-Q-OBJECT | a tree emitter for the numerator | OBJ.14, OBJ.15, and one emitter card per line family (issued by ROW.Q) |

**Two texts of validity exist today**, and the evidence uses both: the 18-clause
`Midfall.LoweringV3.ValidV3` (`statements/StatementsV3.lean:613`; used by `GeneratorTheorem.lean`
and copied by `WideningV3.lean`'s `ValidCore`), the 7-clause `Render.ValidV3`
(`object/ObjectV3Full.lean`; the one with `programOk`, `constsCoherent`, `GeneratedBy`), and the
tree's `R.Valid` (used by `GeneratorRows.lean`). RECON.1 makes them one, with the six additions
above, **before** ST.6's re-hash; **RECON.1b** then rebases the four evidence files onto it. Until
both have run, "supplied by" in the table above names where the fact will come from, not a
projection that exists.

**Supporting ALG cards.** SIM.9 (`leanStage_agree`), SIM.10, SIM.11 (`lean_fault_table`),
`snapshotOf_prepareMsgs` (`Snapshot.lean:380`), `noWriters_prog`, `Run_worldEq_of_noWriters`.

**Exit gate.** `#cone_report` on
`rows_correct (R) (product) (hR : ValidV3 R) : R.ExitOk ∧ R.SimContracts product ∧
R.ProgContracts product`, together with `rows_total : TotalV3 R product` (which also needs
`hasMultiPointSet R = true`, a clause of the single text after RECON.1), prints `0 sorried leaves`, the block-coverage line prints `7 INTEGRATED of 7`,
and `#assert_axioms rows_correct [propext, Classical.choice, Quot.sound] native []` passes.

### M7 — The headline (card PL.H)

```lean
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product
#assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice, Quot.sound] native []
```

**Strategy.** `lowering_equivalenceV3_of` applied to the four obligations for every `R`
(`V3-evidence/lean/statements/GeneratorTheorem.lean`, where the composition is already proved):
`twoOutcomes_correct` (from two `ValidV3` scan clauses), `rejects_correct` and `complete_correct`
(from `rows_correct`), `total_correct` (TOT.1). Nothing is proved here; if a proof is needed, a
leaf was mis-stated — stop and report. A test, not a goal: one `example` instantiating the
theorem at `poseidonRender`. **Exit gate:** §6.

**The SRS.** The Yul program does not depend on the SRS trapdoor, and neither does the theorem:
`ValidV3 R` holds or fails for a render at any SRS, with `PayloadAgrees.negSG2` the one clause a
production SRS cannot compute (it needs `SrsEncodes s`). The test renders use a test SRS whose
trapdoor is public (D-P63), so that the non-vacuity gate is a computation.

### M8 — End to end and the English statement (card PL.E)

`EndToEndV3` for every render, from the headline, `verifyNative_iff_msgs_codec` (proved; copy it
out of `Obligations.lean`), `entryFrame_inhabitedV3`, and the three calldata lemmas
(`Lowering/Calldata.lean:731, :790, :1276`) **for every layout a valid render has**. Then the
English statement of §6 goes into `STATUS.md`. **Exit gate:** `#assert_axioms end_to_end` with an
empty native list.

### M9 — Widen the class to the IVC verifier (D-P72; area WID, 20 cards incl. GEN.2, RECON.3)

**Context.** The generated verifier of the IVC decider circuit is known to fail two clauses of
`SupportedV3`: `noAcc` and `embeddedQuotient` (read off the artifact). Of the others, `advice`,
`instShape`, `singlePhase`, `production`, `separateVk` were read as true; `noRotInst`, `hLimbs`
and `vkPoints` are inferred or checked outside Lean; `wf` and `layout` are not measured. **Card
GEN.2 prints the table from the exported key; until then "two" is a lower bound.**
In accumulator mode the contract decodes a carried KZG accumulator from the public instances
(two G1 points as 7 limbs of 56 bits, a flag and a scalar each), validates it through the G1MSM
precompile, and folds it into the final pairing with a keccak-derived challenge:
`e(kzg_lhs + α·acc_lhs, −[s]₂) · e(kzg_rhs + α·acc_rhs, [1]₂) = 1` — **one pairing check where
Rust makes two**. With the external evaluator, the quotient numerator is computed by a second
contract, pinned by code size and code hash and reached by `staticcall`. D-P72 widens the
generator theorem to both, **for every render**; the IVC circuit is test fixture F2.

**No new block and no new checkpoint.** Accumulator validation is inside VkLoading, the evaluator
call inside QuotientAndLinearization, the batching inside FinalPairing. Three rows gain an arm
(vkLoading, quotientLin, finalPairing), three owe a frame clause (they do not write the two
accumulator slots), and one row is new: the evaluator body, in the closed dialect.

**Lean specification** (`V3-evidence/lean/widening/`, typechecked by `check.sh widening`):

```lean
structure SupportedW (R) : Prop            -- SupportedV3 minus noAcc / embeddedQuotient, plus
                                           --   accKind (point-and-scalar), AccShape (no tail), ExternalPinned
def LeanAcceptsAcc (R) (H) (cd) : Prop     -- the contract's own check: decode the accumulator from the RAW
                                           --   instance words, collapse, batch with the keccak alpha
theorem leanAcceptsAcc_iff_noAcc …         -- without an accumulator it is V3's LeanAccepts   (proved)
theorem leanAcceptsAcc_of_rust …           -- Rust accepts the proof ∧ the accumulator passes its own
                                           --   check ⇒ the reference accepts                  (proved)
theorem rust_or_collision_of_leanAcceptsAcc …  -- the converse, up to AlphaCollision            (proved)
theorem alpha_atMostOne …                  -- at most one alpha makes two failures cancel       (proved)
structure EvaluatorTrust (R) (Q : EvalObject) (W) …   -- an account that passes the verifier's pin answers
                                           --   as the generated evaluator body, and changes no state
def callsW (R) (product) (qAddr) …         -- the honest precompiles plus the evaluator slot
def LoweringEquivalenceW (R) (Q) (product) : Prop      -- the four conjuncts, with qAddr variable
theorem equivalenceW_iff_V3 …              -- at a V3-class render it is the V3 headline        (proved)
theorem lowering_correctW (R) (Q) (product) (hR : ValidW R Q) (hQ : isExternal R → EvalContracts R Q) :
    LoweringEquivalenceW R Q product       -- THE TARGET (WideningStages.lean; hQ is dropped by WID.H)
theorem lowering_correct_of_W …            -- D-P71's theorem is its corollary                  (proved from the target)
-- stages (WideningStages.lean)
def AccInv (R) (cd) (st) : Prop            -- the two slots hold toEip of the collapsed accumulator of the RAW words
def leanStageW …                           -- the last stage asks the batched check, not DualMSM.check
def BatchedInv (R) (H) (cd) (st) : Prop    -- the two pairing slots hold the reference's batched inputs
def EvalContracts (R) (Q) : Prop           -- EvalBodyShape ∧ EvalBodyAgree ∧ EvalBodyTotal
def SimContractsW / ProgContractsW …       -- V3's row families over StageInvW and callsW
```

**What the widened theorem claims about Rust.** In accumulator mode there is no single Rust
function the contract ports: the e2e test verifies the decider proof (`midnight_zk_stdlib::verify`)
and, separately, `final_acc.check` under the IVC SRS. So the theorem's right-hand side is
`LeanAcceptsAcc`, and its relation to Rust is the two corollaries above: **complete, and sound up
to one value of `alpha` per input**. No probability is claimed, and `¬AlphaCollision` is not put
into `SoundSide` (D-P72 clause 3). The English statement at DONE says this in these words.

**Strategy.**
- *Statements first, base class first.* WID.1 lands the statements; RECON.3 moves the row families
  to the widened shape before any ROW card of M6 is briefed, with the proved reduction to the V3
  shape (`leanStageW_noAcc`, `callsW_embedded`), so that every base-class row is proved once.
- *V3's `StageInv` cannot be used at an accumulator render.* It is unsatisfiable after `.start`
  there (`stageInv_false_of_acc`, proved): `Inv`'s `.vk` clause needs a snapshot that carries an
  accumulator, and every staged snapshot has none. `StageInvW` reads the accumulator-carrying
  snapshot and is `StageInv` at V3's corner (`stageInvW_iff_V3`, proved). So RECON.3 restates
  **every** row over `StageInvW`; the rows that use neither `noAcc` nor `embeddedQuotient`
  (transcriptParser, lagrange, pcs, traceReturn) keep one arm, the others (prefix, vkLoading,
  quotientLin, finalPairing, totality) get a second.
- *The target carries the evaluator's contract until the object is tied down.*
  `lowering_correctW (hR : ValidW R Q) (hQ : isExternal R → EvalContracts R Q)`: without `hQ` it is
  false for an arbitrary `Q` (`lowering_correctW_needs_evalContracts`,
  `evalBodyShape_emptyBody_false`: an empty evaluator body). WID.6 ties `Q` to the generated
  body, WID.17 proves the contract, WID.H drops `hQ`.
- *`AccInv` is unconditional.* It is stated on raw instance words with no snapshot, because the
  contract validates the accumulator before any proof point is known to be a group element. It
  belongs with `LeanRaw` and `Mirror`, never in `Agree`.
- *The accumulator helpers have literal loop bounds* at their only call sites (7 limbs, 2
  coordinate words), so they need GEN.0's parametric execution and not the loop rule. The one new
  piece of arithmetic is the contract's `(hi, lo)` reconstruction of a coordinate with a limb
  straddling bit 256 against the port's sum-and-split (WID.11); it is stated nowhere today.
- *The evaluator is the same interpreter.* Its numerator is the object of ROW.Q's route B (the
  interpreter loop refines the reference VM). The widening adds a wrapper, a frame-transport lemma
  (callee memory after `calldatacopy` equals the caller's window) and one opcode arm
  (`0x21 MODARITH7`), **provided ROW.Q is stated over a memory window and a dialect parameter**.
  Today it is not: `QInterpRefines` is fixed to `Bridge.Dialect c g` and T3.10's agreement
  relation is over plan-view addresses. T3.10 and ROW.Q carry a note to state the contract over
  a window and a dialect; this is the one place where M9 constrains M6. The evaluator body also
  needs a **tree emitter** (an extension of OBJ.15 to the external arm), not a parse of its text:
  WID.6 says which.
- *Totality needs more than agreement.* A permissive caller state need not satisfy `StageInv`, so
  the evaluator body must be total on every input (WID.17 child 6).
- *The object side is mostly ported.* Seven template partials already render the IVC verifier byte
  for byte (WID.2). What has never run on a real key: the quotient plan on the decider's limb
  shapes, the evaluator shell, the PCS emitter at five point sets (WID.5).

**Test fixture F2** (D-P72 clause 7). WID.3 exports the decider key under the production SRS
(byte equality, the clause table). WID.4 regenerates the whole flow under ONE seeded test SRS —
the IVC SRS (k = 19) is the `downsize` of the decider's (k = 20), because the contract pairs the
KZG check and the accumulator against one `[s]₂` — and exports the proof, the calldata, the trace
with `alpha` and the two collapsed points, and accumulator mutants. The tracked dump has no
usable proof: its `proof.bin` and `calldata.bin` are untracked leftovers of another render.

**Cards, in order.** WID.2 (now); WID.1; WID.3, WID.4, GEN.2, WID.5, WID.6 (object and fixtures);
WID.8, WID.9 (reference and acceptance at F2); RECON.3 (before M6's rows); WID.11, WID.12 (ALG
and helper summaries); WID.13–WID.17, WID.19 (rows, each after its base-class row); WID.H.

**Exit gate.** `#cone_report` on `lowering_correctW` prints `0 sorried leaves`;
`#assert_axioms lowering_correctW [propext, Classical.choice, Quot.sound]` with an empty native
list passes; the three artifact gates and the acceptance gate at F2 are `true`; every accumulator
mutant of WID.4 is rejected at its intended stage.

### M10 — The generator is certified (D-P73; area CERT, 10 cards)

**Context.** After M7 the theorem reads "for every render with `ValidV3`". `ValidV3 R` is a
condition on the generator's output, and until D-P73 it was to be evaluated once per circuit.
M10 proves it for every supported input, so that the final theorem is about the generator
function: `generate gi = .ok o → SupportedInput gi → …`. Two things have to become true first.

1. **The tree must be the generator's output (route A).** Today the port prints text from
   templates and the proofs talk about a tree built by a second emitter; at F1 the two disagree
   (`codegenAgrees = false`: 6,761 tokens against 14,054, first difference at token 1,333, where
   the text has the accumulator helpers; `codegenStruct = false`). The tree emitter lacks the
   accumulator helpers, the quotient helpers and the quotient numerator block. Once it is
   complete (OBJ.13–OBJ.15 and the numerator families: M6 and M9 need them anyway), the Lean
   generator's assembly text is **defined** as the print of the tree (CERT.2). Measured at F1:
   under the project's pinned solc options the template text and the printed tree compile to
   identical runtime and creation bytecode (with a Homebrew solc 0.8.30; CERT.2 repeats it with
   the pinned binary).
2. **The key payload must be generated inside the certified function.** `generateAll` takes the
   payload as an input; with that, the claim is false (flip the payload's `omega` word: the
   generator still accepts). `generate` runs `generateVk`, the SRS fingerprint and `generateAll`.

**Lean specification** (`V3-evidence/lean/object/GeneratorCertified.lean`; elaborates; 33 named
open lemmas; the two theorems below are proved from them):

```lean
structure GenInput (p) (G₁ G₂ Gₜ)     -- E, encG2, vk, srs, codecs, cfg, flags, features, frDelta
def generate (gi : GenInput p G₁ G₂ Gₜ) : Except Fault CertOut      -- generateVk; srsFingerprint; generateAll
def Generates (gi) (o) : Prop := generate gi = .ok o
def renderOf (gi) (o) : Render p G₁ G₂ Gₜ                            -- no field free
structure SupportedInput (gi) : Prop   -- scope clauses (decidable); the input half of EnvAgrees;
                                       --   two codec laws (hypotheses); deltaLiteral; a size bound
theorem generate_spec …                -- proved
theorem generator_certified (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) : (renderOf gi o).ValidV3
theorem generator_correct_V3 (gi) (o) (hg) (hs) (product) : LoweringEquivalenceV3 (renderOf gi o) product
```

**The 33 lemmas, by kind** (each: "generation succeeded on a supported input ⇒ the clause"):

| kind | lemmas | card |
|---|---|---|
| (a) what the generator's own validation checks | `prog_transcriptFloor`, `supported_layout`, `v3_invariants`, `env_nG2` | CERT.4 |
| (b) syntactic invariants of the tree emitters | `prog_constsDeclared`, `prog_callsResolved`, `prog_noWriters`, `v3_exitDiscipline` (one card each); `prog_noShadow`, `prog_closed`, `v3_closed`, `v3_noShadow` | CERT.5 |
| (c) builder lemmas | `plan_vk_of_generateAll`, `prog_noDirect`, `prog_constNodup`, `env_k`, `env_negLagranges`, `v3_layout`, `v3_model`, `v3_pins_of_valid`; `payload_header`; `prog_constLinesLiteral`, `prog_constTable` (both disappear when `Constants.sol` is printed from the table, CERT.3) | CERT.6 |
| (c)+(d) with a codec law | `env_vkDigest`, `payload_g1Base`, `payload_g2Base`, `payload_negSG2`, `payload_comms`, `v3_payload` | CERT.7 |
| route A | `prog_codegenStruct`, `v3_codegen` (false at F1 today; true by construction after CERT.2) | CERT.2 |
| **suspects** | `v3_planMeta` (the plan's data is built from the final memory layout, Rust's from an intermediate one), `v3_cdBound` (no generator check bounds the proof length) | CERT.1, first |

**Strategy.**
- *Suspects first.* CERT.1 confirms or refutes the two suspects before any proving: a refuted
  lemma is a finding for the human (it may need a clause in the supported class), not a
  hypothesis to add.
- *Kind (a) is unfolding.* `generate_spec` gives the chain of successful steps; the clause is the
  check that a step performed.
- *Kind (b) is induction over the emitters*, once per scan, with one lemma per emitter group. The
  row proofs of M5–M6 already need the emitters' structure; the scans reuse it.
- *Kind (c) is "the table is the data".* The constant table, the plan view and the key payload
  are computed from the key; each lemma unfolds one builder.
- *The token gate.* With route A the artifact gate compares tokens (or compiled bytecode) inside
  the assembly blocks; outside them the text is the port's and stays byte-equal to Rust.

**What stays trusted.** The Lean printer `EVM.print`; solc (through `EntryFrame`,
`EvaluatorTrust`, constant inlining and the Solidity outside the assembly blocks); the
precompiles; the two codec laws; the kernel and the standard axioms. The Rust generator is
tested, not certified. **The Lean `generate` cannot run on a real key today** (no computable G2
decompression: CERT.8), so until then a deployed contract is covered by comparing it with what
the Lean generator prints for the same input.

**Exit gate.** `#assert_axioms generator_correct [propext, Classical.choice, Quot.sound] native []`
passes; `#cone_report generator_correct` prints `0 sorried leaves`; `generate` runs on the F1 key
and on the F2 key and the artifact gates pass in their route-A form.

### Later, each a separate decision

X1 (accumulator mode) and X2 (external evaluator) are no longer "later": D-P72, milestone M9.
X11 (validity for every input) is D-P73, milestone M10.
X4 (the every-render theorem) is the goal: D-P71. Remaining: X3 embedded key; X5 the Solidity
wrapper; X6 delete the retired v1 track (with `Evaluator.rel_worldLocal`, D-P72 clause 10); X7
security; **X8 a total reference verifier** in the contract's order, which would remove `SoundSide`
(RV-20); **X9 the missing-precompile response** in `permissive` (RV-30); **X10** the point-pair
accumulator kind and the fixed-base tail (D-P72 clause 2); **X12** a print/parse round-trip
theorem, which would remove the Lean printer from the trusted base (D-P73 clause 5).

## 6. Definition of done

Two Lean terms, one command.

```lean
-- the generator theorem: no fixture, no native_decide in its cone
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product

-- the proof part of DONE (V3-evidence/lean/statements/GeneratorTheorem.lean)
structure GeneratorDone (Rt : Render p G₁ G₂ Gₜ) (cd : Bytes) : Prop where
  headline   : ∀ (R : Render p G₁ G₂ Gₜ) (product : PairingProduct), ValidV3 R → LoweringEquivalenceV3 R product
  nonvacuous : ValidV3 Rt ∧ ∃ product : PairingProduct, GateAtV3 Rt product cd

-- DONE (card DG.4): the proof part at the test render F1, plus three tests
structure Done (cd : Bytes) : Prop where
  proof      : GeneratorDone poseidonRender cd
  reference  : nativeReplay_ok = true       -- REF.8: the Lean verifier reproduces Rust's MSM on F1 (M1)
  artifact   : ArtifactEq poseidonRender.model poseidonVerifierDump
  vkArtifact : renderHalo2VerifyingKey poseidonRender.plan.vk = poseidonVkDump
theorem generator_done : Done fixtureCd
```

With M9 (D-P72) the headline is `lowering_correctW`, `lowering_correct` is its corollary, and
`Done` gains the same four items at test fixture F2 (card WID.H). With M10 (D-P73) `headline`
becomes `generator_correct` — hypotheses on the generator's input only — `nonvacuous` becomes
"`generate` succeeds on the test key and the gate holds at its render", and `artifact` compares
tokens or bytecode inside the assembly blocks (card CERT.H).

```bash
cd formal
bash scripts/verify.sh          # ram_guard + lake build + checks.sh (incl. kat_gate) + report
# the report must print:
#   cone_report …lowering_correct: 0 sorried leaves
#   cone_report …generator_done:   0 sorried leaves
#   exhibits: 4 PRESENT, 0 MISSING of 4
#   block_coverage …: 7 INTEGRATED of 7
#   axiom_sweep: ok        sorry_sweep: … 0 REFUTED, 0 VACUOUS in the cone
#   closure_fingerprint: matches Frozen.sha256
# and the build contains, as gates:
#   #assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice, Quot.sound] native []
#   #assert_axioms Midfall.Instances.GeneratorDone.generator_done
#     [propext, Classical.choice, Quot.sound] native [<frozen owner list>]
```

The first gate is the point of D-P71: a `native_decide` axiom in the cone of `lowering_correct`
would mean a fixture fact entered a proof. The second gate allows the named fixture
computations of `nonvacuous`, `reference`, `artifact` and `vkArtifact`, and nothing else.
Totality is conjunct 4 of the headline. The names are V3's; after the cut-overs of M3 the same
items carry their landed names.

`not_done_today` is proved today from `¬ ValidV3 poseidonRender` (the payload clause is refuted at
the present render) and is deleted in the commit that proves `generator_done`.

**The English statement `STATUS.md` must carry at DONE** names, itemised:

- **the claim: for every program the Lean port of the generator emits for a circuit in the
  supported class**, and what the class is, clause by clause. Before M10: that it is conditional
  on `ValidV3 R`, checked by computation for each circuit. After M10 (D-P73): that the only
  hypotheses are on the generator's input (`SupportedInput`: the scope clauses, a size bound, and
  two codec laws), and that the Lean printer is trusted;
- that the theorem is about the **Lean** generator's output: the Rust generator is tested against
  it byte for byte on the test circuits, not proved equal;
- the test circuits (F1; F2 after M9), and that no on-chain contract is covered;
- that **the test SRS trapdoor is public** (D-P63): no soundness of the proof system is claimed
  for it;
- the two side conditions and what each excludes, saying that `SoundSide` is a predicate on
  prover-supplied calldata (RV-20);
- **in accumulator mode (M9):** the right-hand side is the contract's own batched check; against
  the Rust verifier the theorem is complete, and sound up to one value of `alpha` per input; the
  IVC and decider SRS are assumed to share one `[s]₂`;
- the trusted base: the yul-semantics EVM dialect and the Bridge; `EntryFrame` (selector routing,
  zero call value, the free-memory prologue, zero memory from `0x80`, calldata shorter than 2²⁵⁶,
  the `memory-safe` footprint, the ABI decoder not reverting on decodable calldata); with the
  external evaluator, `EvaluatorTrust` (an account that passes the code-hash pin behaves as the
  generated evaluator body); the precompile assumption `Eip2537.Holds` in its two real-world
  halves, and that the chain implements EIP-2537 and modexp;
- the Lean Yul token parser and `EVM.mkCall` (they decide what tree a parsed region is);
- the axioms: the standard three for `lowering_correct`; for `generator_done`, each
  `native_decide` axiom by owner declaration;
- port fidelity and how each side is tested: the generator by the artifact gates; the verifier by
  the reference gate and the mutation corpus;
- what is not modelled: gas, including the forwarded-gas constants; solc.

## 7. Briefing: the template, and what makes a card workable by Sonnet 5.5

EXECUTION-V2 §3, unchanged, with one line added to every brief:

```
EVIDENCE (W12): witness <name at commit> · falsifier <name at commit> · exhibit (W14) <name or n/a>
```

Prefix: *"You are executing ticket <ID> of formal/docs/plans/PLAN-V3-cards.md (milestone M<n> of
PLAN-V3.md). PLAN-V2 §4, PLAN-V3 §4 and EXECUTION-V2 §5 (W1–W15) are binding."*

**The cards are written so that the subagent designs nothing.** Each one names: the evidence file
that already contains the statement (and usually the proof) and the lines to port; the target file;
the exact Lean signature of the deliverable; the commands of the acceptance test with their
expected output; the stop conditions; and the traps met when the evidence was written. The
subagent's first two steps are always the same:

1. `bash docs/plans/V3-evidence/check.sh <area>` at the tip. A failure is a false premise: stop
   and report. (The orchestrator runs the same command when it checks the card's NEEDS.)
2. Port the named declarations **verbatim** from the evidence file into the target file, compile,
   and only then adapt names and imports.

**What a subagent must never do** (each is a recorded V2 failure): restate a statement to make a
proof go through; add a hypothesis the card does not list (that is a PREMISE GAP: stop and report
the exact goal); raise `maxHeartbeats` or `maxRecDepth`; evaluate a guard that mentions symbolic
memory; `simp` a continuation-passing `wp`; prove a helper before its consumer compiles.

**Card types.** The cards use EXECUTION-V2 §4's types plus one: **STATEMENT** — a card that lands a
new or changed statement together with its witness and its falsifier (W2, W12); box ≤ 2.5 h; done
when all three are in the tree and the statement's consumer compiles. Decision cards carry
`DECISION` as both layer and type.

**Model routing (W10).** Every card carries `Sonnet` or `strongest`.

| route | cards | why |
|---|---|---|
| Sonnet | every PORT, KAT, EMIT and gate card whose deliverable exists in an evidence file: DG.0–DG.9 (except DG.1–DG.3), REF.2–REF.8, REF.11–REF.14, OBJ.1, OBJ.4, OBJ.5, OBJ.9–OBJ.16, ST.1, ST.3–ST.7, ST.12, ST.14–ST.16, SIM.1, SIM.3, SIM.7, SIM.8, SIM.11, T3.1, T3.3, T3.11, PL.1; WID.1–WID.4, GEN.2, WID.8, WID.9, WID.14; and the row children whose statement is typechecked **and** whose proof pattern has been run once in the tree: HLP.1.a, SIM.6.d, T3.9.b–e, T3.9.h, ROW.TP.1, ROW.TP.9, ROW.Q.1, ROW.PCS.2, ROW.PCS.9 | the statement and usually the proof are provided; the work is landing and checking |
| strongest | SKELETON cards; anything that proves a new theorem about `Step` or `wp`, or new mathematics: SIM.2, SIM.5, SIM.6, SIM.9, SIM.10, SIM.12, T3.0, T3.2, T3.5, T3.7–T3.10, ST.9–ST.11, ST.13, ST.17, REF.1, REF.9, REF.10, OBJ.2, OBJ.6–OBJ.8, DG.1–DG.3, RECON.1–RECON.3, HLP.1, TOT.1, ROW.TP, ROW.Q, ROW.PCS, ROW.FP, PL.H, PL.E; **GEN.0, GEN.1, GEN.3, GEN.4**; the first use of a pattern (T3.9.a for loops, HLP.1.b–c, SIM.6.a–c, T3.9.g, ROW.TP.2, ROW.TP.6–8, ROW.Q.6, TOT.1.a); WID.5, WID.6, WID.11–WID.13, WID.15–WID.17, WID.19, WID.H | a wrong statement or a mis-chosen induction here costs a milestone |

**Why more cards are `strongest` than before D-P71.** On the fixture route most proofs existed in
an evidence file and a card was a port. For every render the statements exist and typecheck
(`GeneratorRows.lean`, `GeneratorTheorem.lean`, `lean/widening/`), and so do the compositions, but
the row proofs do not: each pattern (parametric execution, the loop rule, an induction over an
emitter, a helper summary) is new until its first card has run. That first card is `strongest`;
the cards that copy its script are `Sonnet`. Each `strongest` child carries its Sonnet-only split
in its Guidance line.

If only Sonnet is available, keep the `strongest` cards but split each at its numbered steps into
cards of at most one hour, and give each child the parent's evidence file and stop conditions.

**Proof sketches live in three places**, in increasing detail: the *Strategy* paragraph of each
milestone in §5; the *Guidance* line of each card; and the design memo of the area
(`V3-evidence/design/<area>.md`), which records the options that were tried and failed. A card's
brief copies the first two and links the third.

## 8. Reuse map

- **Keep and build on.** Everything PLAN-V2 §8 lists. In addition: the proved TraceReturn rows
  (lifted by `tr_blockSim`, `tr_blockProgS`); `VkLoading.lean` §1–§4; the transport lemmas of
  `Blocks.lean:579-680`; `G1PointCount.lean`; `holds_staged`; `SyntaxEq.stmtsBeq`; the vendored
  `Interp` and `Adequacy`; R.2's inventory and the G1 cards.
- **Restate.** `ec_pairing_contract`; `vk_progress`, `vk_sound_clean` (over `StageInv`, no decode
  hypothesis needed); `identityCorrespondence_of_bridge`; `Evaluator.rel_worldLocal`.
- **Delete** (in the card that lands the replacement). `poseidon_valid`, `rejects_of_not_accepts`,
  `prefix_run_clean`, `runBody_iff_slices`, `slices_seq_sound`, `slices_seq_progress`,
  `Render.Rejects` as a hypothesis, `vkPins`, `vkProgressPins`, the five D-P36a axioms,
  `poseidonVkCodecRoute`, the 19-identity key, `DeployedProfile.poseidonDerivedParts`' splices.
- **Do not port forward.** Block rows generic in `R` as the route to the headline; pin-by-pin
  growth of `Valid`; the cone count as a progress measure on its own.

## 9. Effort: a prior, then calibration

### 9.1 Facts

| fact | value | source |
|---|---|---|
| cards proposed | 99; the 87 area cards sum to about 160 box-hours as estimated by the design passes. That figure excludes the twelve plan-level cards and every PROOF child of the M6 rows, which is where most of the effort lies | `PLAN-V3-cards.md` |
| of which M0–M4 (no block proof) | about 55 cards | §5 |
| Yul in the F1 main block once the program is complete (the 823 tokens of accumulator helpers are called by no F1 slice and need only the scans) | 14054 tokens; helpers 1303 + 823, parser 923, lagrange 501, quotient 6572, PCS 3623, the rest under 300 | QUEUE R.2 |
| closed blocks | one (25 tokens); 13 lines with the engine | `prooftech/TR.lean` |
| blocks with a measured `wp` execution | vkLoading (75 ms), lagrange (21.5 s, kernel check not completed) | `design/prooftech.md` |
| blocks with no evidence | PCS MSM loops, the quotient VM | same |

Box-hours are estimates by the agents that wrote the cards. They are **not** measurements and the
V2 ledger shows such estimates were wrong by large factors.

### 9.2 Prior (judgment, wide on purpose)

| work | prior, in tickets of ≤ 2.5 h |
|---|---|
| M0 | 8–12 |
| M1 + M2 | 18–30 |
| M3 + M4 | 22–40 |
| M5 to calibration point C | 12–25 |
| M6 onward | unknown until point C; the quotient numerator and the PCS loops dominate |

**No completion date is given before calibration point C.**

**After D-P71 the prior for M5 onward is void.** It was a prior for proofs on literal slices at
one fixture. For every render, one block is closed (TraceReturn: 25 tokens, 1,053 lines by `Step`
inversion); 40 row obligations are stated and typechecked (`GeneratorRows.lean`), 35 cards are
written for them, and ROW.Q lists about 30 further children for the quotient builder. **No
estimate for M5–M9 is recorded before GEN.1 (point B) reports**, and none for M6 before point C.
The largest known costs: the quotient numerator (no tree emitter exists; builder correctness is
now in scope), the transcript parser's list inductions, and the PCS loops.

### 9.3 Calibration points

A, B, C, D of §5 M5, then: end of transcriptParser; end of the quotient row; end of PCS. At each,
the orchestrator records tickets and hours since the previous point, the four report lines, and
re-estimates by analogy, stating the sample size.

### 9.4 Risks

- **Certificate cost on loops** (T3.0, point C). If no strategy checks the lagrange row in bounded
  time, the reflective executor (C3) is built, at a one-off cost the design pass guessed at
  1,500–3,000 lines.
- **The quotient numerator.** No Yul-level statement exists and neither route is demonstrated.
- **PCS.** The MSM loops are not yet emitted; the decode-exists obligation is new mathematics.
- **The glue port was exercised on one circuit**: 10 of 31 opcode arms and no limb shapes occur at
  F1. OBJ.16 probes three more fixtures.
- **The encoder-first codec law** is stated, tested on 50 points, and unproved.
- **Further reference divergences.** None appeared on the fixture once the two repairs were
  shimmed, but no rejecting input, no multi-proof and no other circuit was exercised; the mutation
  corpus (REF.11) is the first test of error-class fidelity.
- **Frozen-surface churn.** Five re-hashes in all (W15). Each needs a signature; a struck decision
  changes the route as listed in §2.
- **A moving tree.** This plan was written while `formal/baseline` advanced eleven commits, from
  `f2fe99b` to `4e18c65` (the last, F.1, proved the two sequencing lemmas and took the headline
  cone from 11 to 9; `Blocks.lean` line numbers in this plan are those of `4e18c65`). Every
  measurement is re-run by the card that relies on it (EXECUTION-V2 §2.3).

## 10. Cut-over: how the orchestrator picks this up

**Nothing in this section needs a new decision except where it says so.** It is written so that the
next orchestrator session can act on it from `STATUS.md` + `QUEUE.md` alone.

### 10.0 How this works with the existing goal prompt (no change to it)

The orchestrator's goal prompt reads `STATUS.md`, `QUEUE.md`, `EXECUTION-V2.md` §0–§7 and
`PLAN-V2.md` §0–§4 at the start of every session, takes the first READY card, and defines DONE as
PLAN-V2 §6. The hand-over therefore lives in those four files, and is conditional on one fact the
orchestrator can check: a signed D-P60 in `design.md`.

| the goal prompt says | what the orchestrator finds there | effect |
|---|---|---|
| read `STATUS.md` | a WAITING ON HUMAN block naming PLAN-V3, D-P60–D-P69 and the two urgent rows | it knows the plan exists and is unsigned |
| read `QUEUE.md`, take the first READY card | a banner of flags on READY cards (leads); card **DG.0** READY; card **PL.0** BLOCKED on D-P60 | before sign-off it fixes its red gate and verifies the flags; after sign-off PL.0 is READY and performs the cut-over |
| read `PLAN-V2.md` §0–§4 | a banner: with D-P60 signed, read PLAN-V3 §0–§4 and §10 instead | the plan it works from switches on the signature, not before |
| DONE means PLAN-V2 §6 | a note in §6: with D-P60 signed, DONE is PLAN-V3 §6 | the definition of done switches with it |
| read `EXECUTION-V2.md` §0–§7 | a note: with D-P60 signed, W12–W15 are added and cards come from `PLAN-V3-cards.md` | the loop and the subagent contract are unchanged |
| "you do not decide" (W2) | every V3 card names the decision it waits for | an unsigned D-P61–D-P69 leaves its cards BLOCKED; nothing is acted on early |

So the human's only action is to sign (or strike) decisions in `design.md`. §10.3 restates the goal
for V3; `v2-bundle/docs/GOAL-PROMPT.md` now holds it in full, with the V2 prompt's loop and rules
adjusted for V3 (updated 2026-11-17, after PL.0). Pasting it removes the reliance on the redirects.

### 10.1 Before D-P60 is signed: flags on live cards (leads, each with its reproducer)

The live queue keeps running under PLAN-V2. These flags are *leads* in the sense of EXECUTION-V2
§2.3: the orchestrator verifies each at the current commit before a brief relies on it. Reproduce
any of them with `bash docs/plans/V3-evidence/check.sh <area>`.

| live card | flag | reproducer |
|---|---|---|
| **G1.1–G1.3 batch** (D-P52) | **Do not merge G1.2 without the scope repair.** With `q_program_fail` / `q_pow5` in the `.quotientLin` slice, `hoist (R.prog) = hoist R.helpers` (`Blocks.lean:224`) is false and `Render.scope` (`Statements.lean:109`, frozen, outside D-P52) lacks both functions. The repair that keeps all five block files compiling unchanged is `[hoist helpers ++ hoist slices]`. Needs D-P65 | `statements` (`port/` experiment in `design/statements.md` §2(d)); `ReviewProbes.lean` §6 |
| **F.1** (sequencing glue) | Merged at `f588ba2` while this plan was written: both lemmas proved, headline cone 11 → 9. Under D-P68 the same chaining is `seq7` / `slices_seq_sim` over `StageInv`; F.1's proofs are the model for it | `soundness` |
| **R.4** (Gap B, D-P55) | Step 1 ("first hour: an axiom-free route") has an answer: construct the pairing, make `s` data. No G2 axiom is needed; `Classical.choose` on G2 bytes is not needed. Landing it as designed needs D-P62 | `reference` (`RefModel.lean`, `D6_Render.lean`) |
| **R.4b** (G1 codec, D-P55 step 1) | A *computable* decoder exists (`g1zOfPair?`, `g1CodecC`), equal to the `Classical.choose` one on the EIP half (`g1CodecC_ofEip`, proved). Prefer it: the fixture decode then evaluates. `G1CodecLaws` at today's `g1CodecZ` is proved only because `ofCompressed?` is `none` | `reference` (`RefModel.lean`, `D4_CodecKats.lean`) |
| **R.5** (D-P58) | The non-determinism is `blind_quotient_limbs` drawing from `OsRng`, `proofs/src/plonk/prover.rs:126` — baseline code. D-P58's fallback (3) applies. The committed `proof.bin` and `trace.json` are one self-consistent run (Lean re-derives the logged reads and challenges) | `reference` (`RunABC.log`) |
| **R.7** (D-P59) | Proceed. The corrected clause is 8 = 8 at the fixture. Its stop condition (does the Lean port index sigma commitments per column?) has supporting evidence: the staged Lean run with the key's eight real sigma commitments reproduces Rust's final MSM | `statements` (`StatementsV3Deploy.log`, `(8, 8, 3)`); `reference` (`RunABC.log`) |
| **R.8** (export-first probe, clauses 2/3) | Answered by measurement: a 180-line port of the missing glue reproduces `vk_mptr`, `proofLen 4320` and the whole verifier text. **But frozen clause 1 forces `numPointSets = 0`**, so a faithful plan fails clause 1 whatever is exported (RV-08). Needs D-P67 | `object` (`Plan2.lean`); `statements` (`("today", true, false, …)`, `("faithful", false, true, …)`) |
| **R.9** (`circuitMeta` as a Prop) | Do not spend it: the clause it discharges is the one RV-08 shows must be restated | `statements` (`frozenValid_numPointSets_zero`) |
| **R.6**, **Q0.5** | Proceed as signed. `PayloadAgrees` (D-P67) and `HypothesesInhabitedV3` (D-P66) later subsume them | — |
| **T.2b** (WP-T, D-P57) | A verified `wp` engine proves the all-runs fact for the literal F1 TraceReturn slice in 13 lines. That meets D-P57's line count on the literal slice; the closed-slice form (`traceReturn_spec` at the render, with the existence half) is still to do and is T3.4. Land the engine (T3.1, T3.3, T3.4) rather than write a new tactic | `prooftech` (`TR.lean`) |
| **T.3**, **S.5**, **S.6** | Hold until T3.0: the engine's kernel check on the lagrange loop is not bounded yet. Do not apply D-P57's hand-proof fallback on that ground | `prooftech` (`LAGP.lean`; `design/prooftech.md` §2.4) |
| **S.4**, **S.7**, **C.3**, **C.5**, **M.1**, pcs row, **S.2** | Hold: these are rows about a render whose `Valid` is false and whose reference rejects every proof. D-P60 makes the hold formal | `ReviewProbes.lean` |
| every card | **The tip is red**: `kat_gate.py` fails at the pinned total (1397 against 1393) and at two `expect TRUE` annotations; the sorry register is back in sync since F.1. Card DG.0 is in `QUEUE.md`, READY, within existing rules, and needs no decision | `python3 scripts/kat_gate.py` |

### 10.2 When D-P60 is signed: PL.0

The orchestrator runs card **PL.0** itself (docs only): let the card in flight return; tag
`formal/v2-cutover`; append the V3 cards to `QUEUE.md` in the order of §5, each READY or BLOCKED on
the decision it names; mark every live card with one of the three verdicts below; point `PLAN.md`
and `STATUS.md` at this file.

| live card | verdict | V3 card |
|---|---|---|
| F.1 | MERGED (`f588ba2`); its technique is reused by SIM.2 | — |
| G1.4b, G1.1, G1.2 | CONTINUE; G1.1 and G1.2 land in the one re-hash with ST.3 and OBJ.2 | — |
| G1.3 | MERGED INTO (its 895 / 5,489 split is measured as 5,431 / 953) | OBJ.2, OBJ.15 |
| R.3 | CONTINUES | (OBJ.8 offers `Except.getOk` as a second route) |
| R.4 | MERGED INTO | REF.5, REF.6 |
| R.4b | MERGED INTO | REF.4, REF.9, REF.10 |
| R.5 | MERGED INTO | REF.11 |
| R.6 | CONTINUES; subsumed at ST.6 | REF.7 |
| R.7 | CONTINUES | = REF.3 |
| R.8, R.9 | MERGED INTO | OBJ.6, OBJ.7, ST.6 |
| Q0.5 | CONTINUES; strengthened at ST.4 if D-P66 is signed | ST.17 |
| S.10 | CONTINUES | — |
| T.2b | MERGED INTO | T3.1, T3.3, T3.4 |
| T.3, S.6 | MERGED INTO | T3.7, T3.9 |
| S.4 | MERGED INTO | SIM.8, T3.6 |
| S.5 | MERGED INTO | ROW.TP |
| S.7 | MERGED INTO | T3.10, ROW.Q |
| pcs row, S.2 | MERGED INTO | SIM.12, ROW.PCS |
| P.1, T.4, T.5 | MERGED INTO | ROW.FP |
| C.3 | SUPERSEDED | SIM.0–SIM.3 (staged contracts replace staged rejection) |
| C.5, M.1 | SUPERSEDED | SIM.2, PL.H |

**What carries over unchanged.** Every proved theorem; the frozen files until their signed
re-hashes; `checks.sh`; the cone tool; W1–W11. **What stops.** Block rows about the present
render; pin-by-pin additions to `Valid` after R.6; any card whose only effect is downstream of a
refuted leaf.

### 10.3 The orchestrator's goal, restated for D-P71 and D-P72 (full text: `v2-bundle/docs/GOAL-PROMPT.md`)

```
GOAL  In the midfall repository (branch formal/baseline; Lean 4.35 project in formal/), prove
        theorem lowering_correct (R) (product) (hR : ValidV3 R) : LoweringEquivalenceV3 R product
      for EVERY render R the Lean port of the generator emits (PLAN-V3 §0), then its widening to
      the IVC verifier, lowering_correctW (PLAN-V3 §5 M9), and theorem generator_done : Done
      fixtureCd (PLAN-V3 §6): the headline, plus non-vacuity, the reference gate and the artifact
      gates at the test circuits. No block row, totality lemma or headline is proved at a fixture.
DONE  means PLAN-V3 §6: verify.sh green; the report prints 0 sorried leaves on lowering_correct
      and on generator_done, 4 exhibits PRESENT, 7 rows INTEGRATED, axiom_sweep ok, closure
      fingerprint matching; #assert_axioms lowering_correct passes with the standard three axioms
      and an EMPTY native list; #assert_axioms generator_done passes with the frozen owner list.
READ AT THE START OF EVERY SESSION (nothing else in full)
      formal/docs/STATUS.md · formal/docs/QUEUE.md · formal/docs/plans/EXECUTION-V2.md §0–§7 ·
      formal/docs/plans/PLAN-V3.md §0–§4 and §10 · the card you are about to brief, in
      formal/docs/plans/PLAN-V3-cards.md.
ROLE  Unchanged: one card, one subagent, re-verify, merge, record. You do not prove, you do not
      edit the frozen surface, you do not decide (W2). Rules W1–W15.
ORDER PLAN-V3 §5: M0, then M1 and M2 interleaved, M3, M4, M5, M6, M7, M8, with M9's cards where
      the V3 table places them. A milestone is done when its exit gate prints the expected output
      at the tip, and not before. GEN.0 runs first among the M5 proof cards; a missed threshold
      of PLAN-V3 §5 M5 goes to the human (per-fixture rows are not a fallback). Then M10:
      generator_correct, with hypotheses on the generator's input only (D-P73).
```

---

*This plan and its evidence were produced by an automated review and six design passes, then restated
for D-P71 and D-P72 from four further design passes (generic rows, proof technology, the IVC widening, its object and reference), and
checked by re-compiling every Lean file from its shipped location (`check.sh`, all files `ok`). Please verify the statements
and measurements against the tree before relying on them.*
