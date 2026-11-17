# Certifying the code generator — statements and distance (HEAD `cf00592`)

Tags: **MEASURED** (a `lake env lean` / `solc` run of this pass, log in `out/`), **READ** (file:line),
**INFERRED** (reasoning, not checked). Paths below are relative to
`formal/` unless absolute; scratch files are in
`lean/object/`.

## 0. Files and typecheck status

| file | what | status (MEASURED) |
|---|---|---|
| `GeneratorCertified.lean` | T1 statements | elaborates, 11 s; 33 `sorry` warnings, each the body of a named theorem; `generate_spec` and `generated_of` proved; `generator_certified`, `generator_certified_V3`, `generator_correct`, `generator_correct_V3` proved from the lemmas; axioms `[propext, sorryAx, Classical.choice, Quot.sound]` (`generate_spec`: no `sorryAx`) |
| `Measure.lean` | T3 codegen state at the fixture | `out/Measure.log` |
| `CertMeasure.lean` | each decidable lemma conclusion at the fixture | `out/CertMeasure.log` |
| `RouteA.lean` + solc | route A bytecode experiment | `out/RouteA.log`, `out/*.sol`, `out/*.solc.txt` |
| `KernelTok.lean` | can the kernel run `yulTokens`? | `out/KernelTok.log` (fails, which is the finding) |

How to rebuild (no `lake build`; one process at a time; from `formal/`):
```
OUT=<cert>/out; BASE_LP="$(lake env printenv LEAN_PATH)"; E=docs/plans/V3-evidence
LEAN_PATH="$BASE_LP:$OUT/object" lake env lean --root=$E/lean/object -o $OUT/object/ObjectV3Full.olean $E/lean/object/ObjectV3Full.lean
for f in StatementsV3 StatementsV3Falsifiers GeneratorTheorem; do
  LEAN_PATH="$BASE_LP:$OUT/statements" lake env lean --root=$E/lean/statements -o $OUT/statements/$f.olean $E/lean/statements/$f.lean; done
LEAN_PATH="$BASE_LP:$OUT/object:$OUT/statements" lake env lean --root=<cert> <cert>/GeneratorCertified.lean
```
The file imports `ObjectV3Full` (object area) and `GeneratorTheorem` (statements area) together;
the combined import has no name clash (MEASURED). In `check.sh` it would need the
`EXTRA_LP=":$OUT/statements"` mechanism the widening area uses.

## 1. T1 — the certified statement

### 1.1 Input, generator, render

```lean
structure GenInput (p) [..] (G₁ G₂ Gₜ) [..] where
  E : VerifierEnv p G₁ G₂ Gₜ        -- the Lean verifier's environment (codec, field, delta)
  encG2 : G₂ → Bytes                 -- the Lean side's G2 encoding
  vk : VerifyingKey (Fr p) G₁
  srs : ParamsKZG G₁ G₂              -- prover SRS: vk.rs reads g_lagrange, g2, s_g2
  codecs : VkPointCodecs G₁ G₂       -- the generator's point encoders
  cfg : GeneratorConfig
  flags : RenderFlags
  features : String                  -- env!("SOLIDITY_VERIFIER_FEATURES") (ART:125), BUILD_ID only
  frDelta : String                   -- fr_delta_literal() (QVM:4131), a curve constant in Rust

def generate (gi) : Except Fault CertOut :=      -- the WHOLE generator
  m0 ← ConstraintSystemMeta.new …; payload ← generateVk … (vkBuildEnvOf field cs) gi.codecs (buildInputsOf gi m0)
  fp ← srsFingerprint …; out ← generateAll … payload (artifactInputsOf gi fp) gi.flags
def Generates gi o : Prop := generate gi = .ok o
def renderOf (gi) (o : CertOut) : Render p G₁ G₂ Gₜ :=
  { E := gi.E, params := ParamsVerifierKZG.ofParams gi.srs.g2 gi.srs.sG2, vk := gi.vk,
    sG2gen := gi.srs.sG2, encG2 := gi.encG2, cfg := gi.cfg,
    inputs := artifactInputsOf gi o.fingerprint, flags := gi.flags,
    plan := o.out.plan, qblocks := o.out.qblocks, model := o.out.model }
```

**No `Render` field is free once `gi` is fixed** (`o` is a function of `gi` through `Generates`).
Three design choices make that true, each READ:
- the payload is **computed** (`generateVk`, `Vk.lean:1093`), not an input. With the payload as an
  input of `generateAll` (ObjectV3Full.lean:585) `PayloadAgrees` is *false for a succeeding run*:
  ObjectV3Full 7.7 flips the omega word and the generator still accepts (MEASURED again in
  `out/object/ObjectV3Full.log`: "omega flipped: generator ok"). This is a class-(e) fact about the
  current `GeneratedBy`, fixed by putting `generate_vk` inside the certified generator.
- `params` and `sG2gen` are `verifier_params` of the same SRS (`Params.lean:30`, params.rs:313-321),
  so `EnvAgrees.sG2` is `rfl` and `EnvAgrees.nG2` is the generator's own check vk.rs:180
  (`g2 == generator`, Vk.lean:806).
- `inputs : ArtifactBuildInputs` is built from `cfg`, `vk`, the computed SRS fingerprint and the two
  strings, so `ValidV3.inputs` is `⟨rfl, rfl, rfl, rfl⟩`.
`vkBuildEnvOf` fills `generate_vk`'s four callbacks with the PlanNew ports; `compact_quotient_program_for`
is QRS:166-180 = plan then `build_quotient_program_items` = the limb-op build at
`DEFAULT_QUOTIENT_LIMB_VM_OPS` (QRS:2102-2111) (READ). The two strings `features`, `frDelta` are
genuine inputs: no key determines them (frDelta is tied to `E.delta` by `SupportedInput.deltaLiteral`).
Not typechecked against a run: `generate` is not evaluable on a real key today (no computable G2
decompression, object.md finding 10; `poseidonRender.E` is noncomputable).

### 1.2 `SupportedInput gi` — every clause input-only

| clause | origin | status |
|---|---|---|
| advice, instShape, noRotInst, singlePhase, hLimbs, vkPoints, production, wf, noAcc, embeddedQuotient, separateVk | `SupportedV2` (Statements.lean:118-134) verbatim, `R.`→`gi.` | already input-only |
| `layout : plan.memory.map.WellFormed ∧ validate.isOk` | SupportedV2:126 | **removed**: mentions the plan; follows from generation (`supported_layout`, class a) |
| wfV3 | `SupportedV3.wf` (StatementsV3.lean:602) | input-only; the reconciliation keeps one of wf / wfV3 |
| modulus, truncWidth, domainN (first half), baryWeight, omegaInvMul, omegaOrder | `EnvAgrees` (Inv.lean:537-567) | input-only (on `E`, `vk`) |
| g1Codec, g2Codec | new | codec law: `g1ToU256s ∘ codecs.g1Repr` (4 words) folds to `E.g1.toEip`; same for G2 / `encG2` |
| deltaLiteral | `LoweringV3.PayloadAgrees.delta` (StatementsV3.lean:427) | input-only (both sides inputs) |
| sizeBound : numInstances < 2^64 ∧ k < 64 | new | Rust `usize`; the port's `BitVec.ofNat 256` wraps (vk.rs:110-111) |

The remaining half of `EnvAgrees` (domainN.2, negLagranges, nG2, sG2, vkDigestWord) mentions the plan
view, so it is output-side: lemmas `env_k`, `env_negLagranges`, `env_nG2`, `rfl`, `env_vkDigest`.

### 1.3 Signatures (MEASURED by `#check`)

```lean
theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut)
    (hg : Generates gi o) (hs : SupportedInput gi) : (renderOf gi o).ValidV3      -- ObjectV3Full:762
theorem generator_certified_V3 … : Midfall.LoweringV3.ValidV3 (renderOf gi o)  -- StatementsV3:613
theorem generator_correct
    (lowering_correct : ∀ R product, R.ValidV3 → LoweringEquivalenceV3 R product)
    (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) (product) :
    LoweringEquivalenceV3 (renderOf gi o) product
theorem generator_correct_V3 (gi) (o) (hg) (hs) (product) :
    LoweringEquivalenceV3 (renderOf gi o) product   -- uses the REAL GeneratorTheorem.lean:67
```
Extra instance: `[DecidableEq G₂]` (Vk.lean:300 needs it for the vk.rs:180 check).

### 1.4 The 33 named sorries

Object text (22): `plan_vk_of_generateAll`; `prog_codegenStruct`, `prog_noDirect`,
`prog_constLinesLiteral`, `prog_constTable`, `prog_constNodup`, `prog_constsDeclared`,
`prog_callsResolved`, `prog_noShadow`, `prog_closed`, `prog_transcriptFloor`; `prog_noWriters`;
`env_k`, `env_negLagranges`, `env_nG2`, `env_vkDigest`; `payload_header`, `payload_g1Base`,
`payload_g2Base`, `payload_negSG2`, `payload_comms`; `supported_layout`.
18-clause text, extra (11): `v3_planMeta`, `v3_layout`, `v3_invariants`, `v3_model`, `v3_codegen`,
`v3_closed`, `v3_exitDiscipline`, `v3_noShadow`, `v3_cdBound`, `v3_payload`, `v3_pins_of_valid`
(the last is a corollary of the object `ValidV3`, not of generation: the three pin clauses are
not new obligations).

**Sanity check at the fixture (MEASURED, `out/CertMeasure.log`)**: with today's `mainAsmRaw`, at the
generator-derived render (payload as input), every decidable conclusion is `true` — P2a-e, P3,
P4, P5, P6, noWriters, exitDiscipline, noShadowB, mainClosed, cdBound, layout, invariants,
supported.layout, env_k (k = 6), env_negLagranges (9 = 9) — **except** `prog_codegenStruct` and
`v3_codegen`, which are false (§3.1). So no lemma is contradicted by the one input we can run,
other than the two the WP-G1 gap already makes false.

## 2. T2 — clause classification

(a) the generator's own validation; (b) syntactic invariant of the tree emitters; (c) builder lemma;
(d) codec/curve law; (e) not provable for all inputs as stated. Sizes: S ≤ 1 card (2.5 h), M 2–4, L more.

| lemma / clause | class | size | where (READ) |
|---|---|---|---|
| generated (`plan_vk_of_generateAll`) | c | S | `newFromVk` stores its payload `LoweringPlan.mk vk …` ObjectV3Full:537-540; `generateAll` :585-601. Rest of the clause PROVED here |
| inputs | by construction | 0 | `artifactInputsOf` |
| P1 `prog_codegenStruct` | **e today** (false at F1), then G1 | L | `mainAsmRaw` Program.lean:98; `emitSlices` GenAstDispatch:200; §3 |
| P2a `prog_noDirect` | c | S | newFromVk `direct := none` (:540) → `generateVerifierFromPlan` (Artifacts.lean) |
| P2b `prog_constLinesLiteral` | b on the text renderer | S-M | `renderConstants` VerifierPartials:1980 (185 lines, 19.9 KB); every interpolation is `hexFilter`/`toString` of a Nat |
| P2c `prog_constTable` | c + d (string read-back) | M | `constTableOf` Program.lean:53 (`splitOn` + `Inline.solConstantLine?`) vs `expectedConsts` ObjectV3Full:175. Vanishes if Constants.sol is printed from `expectedConsts` |
| P2d `prog_constNodup` | c | S | literal names of `expectedConsts`, two optional arms |
| P2e `prog_constsDeclared` | b | M | `freeNames` over every emitter |
| P3 `prog_callsResolved` | b | M | ObjectV3Full:665; helper table `emitHelpers` GenAst:579 |
| P4 `prog_noShadow` | b | S-M | ObjectV3Full:673 |
| P5 `prog_closed` | b | S | from P2e, P2c and an `inlineContractConstants` free-name lemma |
| P6 `prog_transcriptFloor` | a | S | `VerifierMemoryLayout.validate` pins `transcript_mptr` (Layout.lean:1023-1036), run by `validateGeneratorInvariants` (LoweringPlan.lean:534-538) inside `newFromVk` (ObjectV3Full:542) |
| `prog_noWriters` | b | M | `noWritersFuel` Bridge.lean:1105, per emitter; inlining substitutes literals |
| `env_k` | c | S | `pv.k = model.k`; ART:281 `k := inputs.k`; `artifactInputsOf` |
| `env_negLagranges` | c | S | ART builder (mod.rs:509-515); MEASURED 9 = 9 at F1 |
| `env_nG2` | a | S | vk.rs:180 `g2 == generator` (Vk.lean:806), `DecidableEq G₂` |
| `env_vkDigest` | c + d | S | vk.rs:109; slot 0 survives the reservation fold (Vk.lean:1093-1225 rewrites only the two quotient sections); `feToU256 ∘ frToRepr = frWord` |
| `payload_header` (8 fields) | c + d | M | `VkHeaderBuilder` vk.rs:211-222; same fold argument; `invert` = `⁻¹`; `rotationLast` kept by `setNumDummyEvals`/`setNumPointSets`; `sizeBound` |
| `payload_g1Base` | a + d | S | vk.rs:151 `Σ g_lagrange = generator`; slot 11 is `P.g₁` (Vk.lean:802); `g1Codec` |
| `payload_g2Base` | a + d | S | vk.rs:180; `g2Codec` |
| `payload_negSG2` | c + d | S | `s_g2⁻¹` (Vk.lean:804), `sG2gen := srs.sG2`; `g2Codec` |
| `payload_comms` | c + d | S-M | `mapM` Vk.lean:855-858, untouched by the write-back (`listSetMut` on `constants` only); `g1Codec` |
| payload, **if the payload stays an input** | **e** | — | counterexample MEASURED: F1 payload with word 4 (omega) + 1, `generateAll` returns `.ok` (ObjectV3Full 7.7) |
| `supported_layout` | a | S | LoweringPlan.lean:538 → `memory.validate` → `MemoryMap.validate` (Layout.lean:1076, :552); validate ⇒ `wellFormedBool` (Layout.lean:1112 docstring says strictly weaker) |
| other 11 scope clauses | input | 0 | SupportedInput |
| `v3_planMeta` (`PlanMeta`) | **e-suspect** | M | `Data.new` gets the FINAL memory in PlanMeta, the intermediate default-config layout in Rust (StatementsV3.lean:313-318: "NOT settled"); restate as an equation with `newFromVk` |
| `v3_layout` | c | S | ObjectV3Full:521 |
| `v3_invariants` | a | S | ObjectV3Full:542 |
| `v3_model` | c | S | ObjectV3Full:597 |
| `v3_codegen` (frozen token clause) | **e today**; then P1 + `tokens ∘ print ∘ parse = id` | M | Program.lean:190 |
| `v3_closed` | b | S | P5 restricted to the main block |
| `v3_exitDiscipline` | b | M | `exitDisciplineFuel` StatementsV3:520 |
| `v3_noShadow` | b | S | `topBinders` ProgramLemmas:23 |
| `v3_cdBound` | **e-suspect** | S once a bound exists | neither `memory.validate` nor `Halo2Verifier.validateLayout` (Artifacts.lean:357-400) bounds `proofEnd` or `numInstances`; `sizeBound` covers `numInstances` but not the proof length (circuit size). INFERRED counterexample: a key with ≥ 2^251 commitments; not run |
| `v3_payload` | c + d | as above | plus `delta` = `SupportedInput.deltaLiteral` |
| `v3_pins_of_valid` | c (from `ValidV3`) | S | the 6-line script of `ValidV3.vkMptr_const` (ObjectV3Full:783) per name; `disjoint` (a) from the map; `vkLen` needs `runtimeBytes.size = len + 1` |

Rough total, INFERRED: (a)+(c) collapse to two inversion lemmas — "`generateAll` = .ok ⇒ …" (M)
and "`generateVk` = .ok ⇒ header/points/comms" (M) — plus ~8 S; (b) is one scan framework (M) plus
five properties × ~12 emitters (L, mechanical); (d) is two codec facts per concrete curve (S each
as hypotheses, M-L each as theorems for BLS12-381); P1 is G1 (§3).

## 3. T3 — gap G1

### 3.1 Today's state at the fixture (MEASURED, `out/Measure.log`)

At `poseidonRender`'s views (`poseidonPv`/`poseidonM`, `rfl`-equal, PoseidonValid.lean:96-97) and,
identically, at the generator-derived render (`Fixture.gen`):
- `codegenAgrees = false`; guard half `true` (52 tokens); main: AST 6761 tokens, text 14054;
  **first difference at token 1333**: AST `… = 1 } let r := FR_MODULUS let success`, text
  `… = 1 } function load_acc_coord_shifted ( src , bits , …` — the accumulator helpers.
- `codegenStruct (mainAsmRaw pv) m = false`; the text parses (74 top-level statements against
  `mainAsmRaw`'s 290 — the pcs arm is flattened); **first statement difference at index 9**
  (0 = MF-2 guard, 1-8 = the eight helpers, 9 = `let r` vs `function load_acc_coord_shifted`).
- With the ObjectV3Full stand-in `mainV3` (today's emitters, pcs scoped, the three un-emitted
  regions taken as the PARSE of the model's text) both are `true`; `print ∘ parse` round-trips the
  main and guard token streams (`true`, `true`).
Missing trees (READ, object.md §1 table, unchanged): AccumulatorHelpers (823 tokens, 5 functions),
QuotientHelpers (68 tokens, `q_program_fail`, `q_pow5`), QuotientNumeratorBlock (6384 tokens, of
which 5431 are line families from `compactQuotientComputationBlocks`), pcs scopes; the evaluator
contract has no tree.

### 3.2 Cost driver common to B and C (MEASURED, `out/KernelTok.log`)

`decide +kernel` cannot reduce `yulTokens "mstore(0x00, 1)"` (15 bytes) — reduction gets stuck in
`yulTokens` (String `replace`/`splitOn`). With `native_decide` banned from the headline's cone
(D-P71 "Axioms"), any route whose proof compares TEXT needs symbolic lemmas about `String.replace`,
`splitOn`, comment stripping and hex normalisation over concatenations, for ~200 KB of template
text and two string-producing emitters. Not even a concrete template chunk can be closed by
evaluation.

### 3.3 Route A — tree first

Define the Lean generator's assembly text as `print (tree)`: `mainAssemblyText m := print (emitMain …)`,
guard likewise. Then:
- **What replaces `codegenStruct`**: nothing in `ValidV3` (the clause becomes definitional). Optional,
  to take the printer out of the trusted base: ONE generic theorem `parseTokens (yulTokens (print b))
  = some b` for blocks of the emitted fragment (identifier/literal well-formedness) — input-independent,
  M-L, and it too needs the string lemmas of §3.2, but once, not per renderer.
- **Byte equality with Rust becomes token equality** for the two assembly blocks: `yulTokens`
  (YulGolden.lean:119) drops `//` comments line by line, all whitespace, and maps `0x` literals to
  decimal; D-P13 (design.md:297) already says generator identity is structural, not textual.
  Measured at F1: tokens(print(mainV3)) == tokens(text): `true`. This is a per-fixture test
  (`native_decide` allowed there, D-P71).
- **Solidity outside the assembly blocks is unaffected** and stays text: constants (13,873 B),
  constructors (733 B), precompile smoke (14,414 B, its own assembly block, constructor-time),
  pragma/NatSpec/immutables/`verifyProof` wrapper; total contract 175,908 B, main assembly 138,062 B,
  guard 819 B (MEASURED). P2b/P2c are the only clauses that read that text; printing Constants.sol
  from `expectedConsts` (data first) removes P2c. The VK contract and the evaluator contract are
  separate files, unaffected.
- **Bytecode** (MEASURED, solc `0.8.30+commit.73712a01` Homebrew build, sha256 `a037e036…`, NOT the
  pinned binary `738dcdc6…` of ImportSolcIR.lean:20): `orig.sol` (the port's text) and
  `treeprinted.sol` (both assembly blocks replaced by `EVM.print` of the tree; 110,922 vs 175,918
  bytes) give **identical runtime bytecode** (`--bin-runtime --optimize --via-ir --evm-version cancun
  --no-cbor-metadata`, sha256 `8d375741…`, 26,350 hex chars) and **identical creation bytecode**
  (`--bin --optimize-runs 1 …`, sha256 `db6fa57a…`). Without `--no-cbor-metadata` they differ
  (`cae1178b…` vs `9e47dd8f…`), as the metadata hashes the source. The project pins
  `--no-cbor-metadata` (READ: `proofs/solidity-verifier/src/evm.rs:211`, `:291`;
  `docs/reference/REPRODUCIBLE_BUILDS.md:10`; the IR import used `metadata.bytecodeHash=none`,
  ImportSolcIR.lean:22). INFERRED, not proved: inline-assembly comments and layout are not Solidity
  AST nodes, so they cannot move AST ids; for all inputs this remains a solc property, testable per
  deployment by compiling both texts (1 s each here).

### 3.4 Route B — agreement proved once

`∀ inputs, yulTokens (text) = yulTokens (print (tree))`, per renderer/emitter pair (sizes MEASURED by
span; renderers are long string literals, so chars are the better measure):

| text side (VerifierPartials.lean unless noted) | chars | tree side (GenAst*.lean) | chars | alike? |
|---|---|---|---|---|
| `renderAssemblyHelpers` :554 | 19,320 | `emitHelpers` :579 = fail :251, scalarInv :426, transcript helpers :320-388, batchInvert :465, ecPairing :265 | ~9,600 | same statement order; text has trace arm |
| `renderVkLoading` :567 | 9,504 | `emitVkLoadingArms` :926 | 3,158 | embedded-VK arm (loop) absent from emitter |
| `renderTranscriptProofParser` :726 | 25,338 | `emitTranscriptParserAt` :1073 | 6,415 | both loop over `userPhases` |
| `renderLagrange` :604 | 5,524 | `emitLagrangeAt` :681 | 5,210 | close |
| `renderQuotientAndLinearization` :624 (lin scope) | 9,486 | `emitQuotientLinAt` :840 | 1,506 | external/direct/probe/trace arms absent |
| `renderQuotientHelpers` :1183 | 3,903 | — | 0 | no tree |
| `renderQuotientNumeratorBlock` :1266 | 74,207 | — (GenAstQuotient.lean 917 lines covers the per-identity layer only) | 0 | no tree; 5431/6384 tokens are lines from `compactQuotientComputationBlocks` (QuotientBlocks.lean, 2,278 lines, a STRING producer) |
| `renderAccumulatorHelpers` :958 | 23,260 | — | 0 | no tree |
| `renderPcs` :2392 + `model.pcsComputations` (Kzg.lean, 3,116 lines, STRING producer) | 2,079 + | `computationsAst` GenAstPcs:587 (file 1,166 lines) | | two emitters of the same plan, not template vs emitter |
| `renderFinalPairing` :692 | 6,943 | `emitFinalPairing` :617-680 | ~1,800 | close |
| `renderTraceReturn` :2435 | 4,858 | `emitTraceReturnBlock` :786 | 244 | trace arm absent |
| `abiGuardText` / `vhMainAssemblyOpen` (Program.lean:162, Contracts.lean:247,273) | — | `abiGuardBlock`, `mainGuardBlock`, `mainLocals` (Program.lean:62-90) | — | fixed |

Structure: renderers are `++` chains of literal chunks with `if`/`match` on flags and `jinjaFor`
loops; emitters are production-only constructor lists with the same interpolated Nats. Each pair is a
case split on the flags (fixed by `SupportedInput.production` etc.) and an induction on the loops,
BUT every chunk comparison is a string-library lemma (§3.2). INFERRED size: tokenizer algebra L
(≥ 4 cards); 7 existing pairs ~ M each; 3 missing emitters to write and prove (AccumulatorHelpers M+M,
QuotientHelpers S+S, QuotientNumeratorBlock with an AST twin of QuotientBlocks L+L); PCS (two
emitters) L. Total L, order 25–40 cards.

### 3.5 Route C — verified parser

Define the tree as `parseTokens (yulTokens text)` (ObjectV3Full.lean:150, Parse1.lean). The object is
then the text, and the parser is part of the definition. Cost to the block rows: the rows are stated
over `sliceOf pv m q = inline (emitPartial pv q)` (Program.lean:125); they would be restated over
positional slices of the parsed main (object.md slice lengths `[1, 44, 3, 4, 1, 2, 3]`), and EVERY
row proof needs, for all inputs, the shape of `parse (tokens (renderX ctx))` — which is exactly route
B's per-pair theorem composed with the parser, plus parser lemmas (determinism on the emitted
grammar, fuel sufficiency) over symbolic token streams. So C ⊇ B in cost, and moves the parser into
the trusted base.

### 3.6 Recommendation: route A

Because (1) every route needs the missing trees anyway (the rows need them), and after that A needs
no per-renderer proof at all; (2) B and C need symbolic string reasoning over ~200 KB of templates and
two string producers, which kernel evaluation cannot shortcut (MEASURED, §3.2) and `native_decide`
may not (D-P71); (3) what A gives up — source-byte identity of the assembly blocks with Rust — is
already non-normative (D-P13), and at F1 the bytecode is identical under the pinned flags (MEASURED,
§3.3), so the per-deployment link can be the stronger "same bytecode" test instead of a text test.
Corollary: make Constants.sol data-first too, which deletes P2c.

## 4. T4 — what stays trusted with a certified generator

1. **Which generator ships.** The deployed artifacts are produced by the Rust generator
   (`proofs/solidity-verifier`); the theorem certifies the Lean port. Link: a per-deployment check —
   today byte equality of `Halo2Verifier.sol` except BUILD_ID (ObjectV3Full 7.1, MEASURED "differs in
   1 line"), under route A token equality of the assembly blocks or, stronger, equal solc bytecode.
   The comparison runs in compiled Lean (`#eval`), trusted for the test only. Today `generate` cannot
   be run on a real key (no computable G2 decompression), so the payload still comes from Rust and
   must be checked against `generate_vk` symbolically (`PayloadAgrees` per circuit) until it can.
2. **The Lean printer** `YulSemantics.EVM.print` (vendored PrettyPrint), under route A, unless the
   generic print/parse round-trip theorem is proved.
3. **The token normaliser / parser**: under B, `yulTokens` must agree with solc's lexer (its `//` cut
   assumes no string literals, YulGolden.lean:72-75); under C, `parseTokens` is the definition of the
   object and must agree with solc's Yul parser.
4. **solc 0.8.30** with `--via-ir --optimize --evm-version cancun --no-cbor-metadata`: `EntryFrame`
   (Statements.lean:249) is the trusted description of Solidity's entry state; constant substitution
   (`Inline.inlineContractConstants`) is trusted Solidity semantics; the Solidity outside the assembly
   blocks (wrapper, immutables, dispatcher) is covered only through `EntryFrame`.
5. **The VK contract's bytes**: not trusted for soundness beyond keccak — `verifyProof` re-checks
   `extcodesize`/`extcodehash` against `EXPECTED_VK_LENGTH`/`EXPECTED_VK_CODEHASH_WORD` on every call;
   `DeploymentV2` (Statements.lean:233-240) assumes `extCode = runtimeBytes` and `H = keccak256`.
   That solc turns `Halo2VerifyingKey.sol` into exactly `runtimeBytes` is trusted for liveness only.
6. **The evaluator's code hash** (D-P72 widening only): `EvaluatorTrust`, keyed on the code-size and
   code-hash pin, is a hypothesis; the evaluator body has no tree. The base class (embedded VM) does
   not use it.
7. **Hypotheses on the input**: the codec laws `g1Codec`/`g2Codec` (theorems for a concrete curve,
   hypotheses here), the `EnvAgrees` input half, `deltaLiteral`; outside the generator question the
   EVM model, `Eip2537.Holds`, `G1CodecHeadlineLaws` and keccak stay as in the headline.

## 5. What makes certification impossible as stated today

1. **WP-G1**: with today's `mainAsmRaw`, `codegenStruct` and the frozen `codegenAgrees` are false at a
   supported input on which the generator succeeds (MEASURED at F1), so `generator_certified` is false
   until the four regions have trees (`prog_codegenStruct`, `v3_codegen` are false lemmas today).
2. **Payload as an input**: `PayloadAgrees` is not implied by `GeneratedBy` (MEASURED counterexample).
   Repaired here by `generate` = `generate_vk` + `generateAll`; the price is two new inputs (prover SRS,
   point encoders) and two codec laws.
3. **Size**: header words wrap above 2^256 (added `sizeBound`); `cdBound` needs a circuit-size bound
   that no clause has (e-suspect, not added).
4. **`PlanMeta`** (18-clause text only) is not known to hold for all inputs (Data.new memory argument).
5. The certified generator is not yet runnable on a real key (G2 decompression), so it cannot itself
   produce a deployment; the Rust output stays the shipped artifact, linked per deployment.

Please review these results for accuracy and completeness before relying on them.
