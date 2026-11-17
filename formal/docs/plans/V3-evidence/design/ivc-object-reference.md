# The IVC decider verifier ("F2"): object and reference scouting

Repository `midfall`, branch `formal/baseline`. HEAD was `c22b51a` when I started and is `f8f461e` at
the end. `f8f461e` changes only `formal/docs/plans/V3-evidence/lean/tooling/T7.lean`, so no result here is
affected. This memo is read-only scouting. Scratch files are under `f2/` next to this memo:
`f2/lean/object/IvcPartials.lean` (+ `.out`), `F2Lagrange.lean`, `f2/lean/refout/RunABC.log`, and
`f2/tools/regions.py` (region diff).

**Framing (owner scope change, D-P71 PROPOSED).** Proofs are not wanted per fixture. The target is
`lowering_correct (R) (hR : R.ValidV3)` for every render, with fixtures used only as tests. This
memo therefore describes: (i) what the Lean generator and the Lean reference support in
**accumulator mode** and **external-evaluator mode**, which are the two modes the IVC decider
verifier needs; (ii) what an IVC *test bundle* needs; (iii) which `SupportedV3` clauses the IVC key
fails (A5); and (iv) the genericity profile of the new code (A6). The work items are sized as
class-widening work, not as fixture proof cards.

Evidence labels used throughout:
- **MEASURED**: a command printed the value at `c22b51a`.
- **READ**: `file:line`.
- **INFERRED**: my reasoning, not checked.

Paths are relative to the repo root unless they start with `formal/`-relative module names.

---

## 0. Summary

| question | answer |
|---|---|
| Can the Lean generator produce F2's verifier text? | **Seven of the ten template partials already render F2 byte for byte** at an F2-shaped context (MEASURED, §A3.3). The rest is either generated per circuit (PCS, the quotient program, the VK payload) or depends on solc output (the evaluator's runtime length and codehash). All of it needs a decider `cs.json`/`vk.json` export, which does not exist yet. |
| Two programs or three? | **Three contracts** (verifier, evaluator, VK), but only **two programs**. The VK contract is data: an INVALID byte followed by a payload. The evaluator is an **interpreter** (QVM) whose bytecode and constants sit in the VK payload, plus per-circuit native callbacks. |
| Can the Lean reference run the decider proof? | All features are ported in `Halo2/Exec` and none is hard-wired to F1 (0 Poseidon references in Exec, MEASURED). Two things have run on a real proof only at F1 shape, and only with the two shims REF.1/REF.2: multiple lookups and 6 permutation sets (Exec code is generic over both), and rotation `-1`, 5 point sets, 16 instances, k = 20. The accumulator arm exists as a contract-faithful predicate, `ContractRefAcceptsAcc` (`Lowering/Accumulator.lean:1424`). It has never run on real data. |
| Acceptance ("Lean accepts") | **Not decidable** with the Midnight SRS, because the trapdoor is unknown. Everything up to the four G1 inputs and alpha is trapdoor-free. A test-SRS regeneration needs **one shared trapdoor for both the k = 19 IVC SRS and the k = 20 decider SRS**, because the contract batches the accumulator equation against the decider's `NEG_S_G2`. |
| Is the dump consistent? | No (MEASURED/READ, §A4.1). The `.sol` files are tracked and were committed on 2026-10-23 from another machine. The `.bin`/`.txt` files are untracked and come from a local 2026-10-07 run. The VK commitments and header are identical between the two (MEASURED). The quotient program differs, and so does the evaluator. |
| Rust-faithfulness in acc mode | Rust's native decider `verify` **does not check the accumulator** (`zk_stdlib/src/lib.rs:1804-1828`: the `None` argument is the committed instance). The accumulator is checked separately, off-chain, with the IVC SRS (`tests/ivc_keccak_solidity.rs:1021-1024`). The contract checks one alpha-batched pairing instead. These are different predicates (R-10). The reference for acc mode must be the contract-faithful one. |

---

## A. Object: the generator in accumulator and external-evaluator modes

### A1. What the Lean generator ports, per F2 mode

| F2 mode / item | Lean port | status | evidence |
|---|---|---|---|
| `AccumulatorEncoding` (generator type, usize semantics) | `Generator/Api.lean:228` (kind), `:413` (struct) | ported; synthetic KATs | READ |
| `AccumulatorEncoding` (Exec type) and the `toExec` bridge | `Halo2/Exec/Accumulator.lean:170-260`; `Lowering/AccEncoding.lean` | ported. 3 bridge lemmas are `sorry`, see §B6 | READ |
| acc expectations, fixed-base tail, ACC_RHS gas (ART:176-245) | `Generator/Artifacts.lean:270-347` (`accBasePointers`, `accFixedBasesOf`, `accExpectationsOf`, `accRhsMsmGasOf`) | ported; synthetic KATs (`Artifacts.lean:967-990`) | READ |
| AccumulatorHelpers partial: decoders, and `validate_public_accumulator` in both arms | `Generator/VerifierPartials.lean:958` `renderAccumulatorHelpers` | ported. Tree gates cover the decoder half against F1 and the arms only synthetically (`:3181-3263`). **My probe shows the F2 arm (carried scalars, empty tail, "fully collapsed" comment) is byte-exact against the F2 artifact** | MEASURED `IvcPartials.out` |
| alpha-batched FinalPairing arm | `VerifierPartials.lean:692` `renderFinalPairing` | ported. Tree gate is synthetic (`:2681`, which says "No tracked artifact pins the CONTENT of that arm"). **Byte-exact against F2 in my probe** | MEASURED |
| VkLoading acc header cross-checks and the acc-validation call site | `VerifierPartials.lean:567` | byte-exact against F2 in my probe | MEASURED |
| external quotient call site (the extcode pin, `staticcall`, magic, selector-bucket copy) | `VerifierPartials.lean:624-642` (`renderQuotientAndLinearization`, `quotientExternal` arm) | ported. **Byte-exact against F2 in my probe** | MEASURED |
| external frame derivation | `Generator/LoweringPlan.lean:328-349` (`quotientExternalFrameFromBounds`, `quotientExternalFrame`) | ported; untested on a real external render. At F2 inputs (base 0x3680, evals 0x9480, 102 evals, 10 selectors) the formula gives frameLen 0x6ac0 and outputLen 0x180, which matches the artifact | READ + hand computation |
| evaluator contract shell | `Generator/Contracts.lean:490` `renderHalo2QuotientEvaluator`, `EvaluatorCtx` `:392` | ported. Tree gates 16-19 are explicitly "synthetic, none offered as byte evidence" (`Contracts.lean:936-1028`) | READ |
| `generateQuotientEvaluatorFromPlan`, `Halo2QuotientEvaluator.validateLayout` | `Artifacts.lean:428`, `:457` | ported; untested on a real render | READ |
| `RenderQuotient.externalPinned`, `renderQuotientEvaluator` API | `Api.lean:862-873`, `Builder.lean:273-358` | ported. The evaluator text is an **input** `evaluatorStep : Except ApiFault String`. Builder sequences steps and does not compute them | READ |
| evaluator runtime length and codehash pins (`EXPECTED_QUOTIENT_LENGTH` 9656, `EXPECTED_QUOTIENT_CODEHASH_WORD`) | none possible: these are the **solc-compiled runtime** of the evaluator | **must stay an input** (like BUILD_ID). Three different lengths are on record: 9656 in the `.sol`, 9531 in the Oct 7 `contract-sizes.txt`, 10,420 in commit `cd606aa` | READ |
| quotient VM opcode `0x21 MODARITH7` (limb-aware) | `Generator/Quotient/VmRecognizers.lean:1777`, `VmBuilder.lean:2382`, `VmValidator.lean:2140`, `VmTypes.lean:2174` | ported; synthetic KATs only. F1 uses 10 of the 11 opcodes F2 uses, and **never** 0x21 (MEASURED grep). The design memo (`object.md:224`) says "no limb shapes occur" at F1 | MEASURED + READ |
| truncated challenges | `Exec/Arith.lean:265`; template x3 mask | shared with F1, so tested there (`parserProofLayout_derivedFromArtifact_ok`, `VerifierPartials.lean:3142`) | READ |
| fewer point sets | `Generator/Kzg.lean:921-942` (runtime branch), `Vk.lean:1004-1038` | **not used by F2's outer proof**, see below | READ + MEASURED |
| multi-limb quotient (single-H off) | default arm | same as F1: 4 limbs at both (F2 by the proof-length arithmetic, §A3.1) | MEASURED (arith) |
| `numPointSets` | `Encoding.lean:473-474` sets 0 | a lazily filled mirror: `Vk.lean:1037-1038` sets it from `Kzg.numPointSets` (`Kzg.lean:940`) after `Data` is built | READ |
| `LoweringPlan::new` glue, `generateAll` | scratch only (`V3-evidence/lean/object/Plan2.lean`, `ObjectV3Full.lean`); about 480 Rust lines; OBJ.6/OBJ.7 | **absent from the tree**. Exercised on F1 only. `Plan2.lean:17` says "numInstances = 1, no accumulator" | READ |

**Fewer point sets.** `in-circuit-fewer-point-sets` is a feature of `midnight-aggregation`
(`proofs/solidity-verifier/Cargo.toml:82`). It changes the *decider circuit*, that is, the in-circuit
verifier of the leaves. It does not change the outer proof. The outer switch is
`outer-fewer-point-sets` (`Cargo.toml:84`, `src/lib.rs:69`), and the run command does not enable it
(`tests/ivc_keccak_solidity.rs:31`). `proof-evaluation-counts.txt` says `dummy PCS: 0`, and the PCS has
5 ordinary point sets (MEASURED). `Features.solidity` (`Exec/Features.lean:31-35`) is therefore
exactly F2's profile, as it is F1's. `numPointSets := 0` at `Encoding.lean:474` means nothing
specific to F2. The only issue around it is the known `Valid` defect RV-08, which is a statement
issue and not a generator issue.

### A2. Exporting the decider's bundle

**F1 exporter.** `proofs/solidity-verifier/tests/conformance_export.rs::export_poseidon_conformance_bundle`
(`:319`; feature `rust-verifier-trace`; output `formal/fixtures/conformance/poseidon`, `:311`). It
writes `vk.json` (`:594-622`), `params.json` (`:624`), `instances.json` (`:636`), `proof.bin`, and
`trace.json` (`:643`: transcript log, DualMSM terms, solidity_trace). It also writes `cs.json`
(`:732-764`: gates as expression trees, lookups with chunking, trashcans, permutation columns). The
circuit is hard-coded at `:74-101`, and the instance prefix assumes one public column at `:488`.

**What a decider export needs (INFERRED from the two test files).**
1. Factor the decider pipeline (`ivc_keccak_solidity.rs:950-1107`) so that it can feed the exporter's
   traced verify. The exporter wraps the transcript to log reads and squeezes (`:443-551`). For the
   decider this must run under `sha3::Keccak256` with the 16-word public column and the identity
   committed instance. That is the same shape as F1, only with more words.
2. Accumulator section (new, schema 2+): the 16 instance words (already in `instance.le`), the encoding
   `(offset 4, 7, 56, PointAndScalar)`, the Rust `final_acc` as two compressed G1 points, and the IVC
   `ParamsVerifierKZG` (g2 and s_g2), because `final_acc.check` runs against the IVC SRS.
3. `trace.json` for the decider: the KZG DualMSM terms (about 78 pairs on the right, by the final MSM
   size), `left/right_eval`, and additionally `acc_lhs`/`acc_rhs`. The Rust trace already records these
   under ids 29 and 30 when `solidity-verifier-trace` is on (`circuits/src/verifier/accumulator.rs:154-173`).
4. The `.sol` triple and `calldata.bin` from the **same** run, plus the evaluator's compiled runtime
   length and hash (render inputs), BUILD_ID inputs, and a manifest.

**Size of the decider's cs.** All counts below are MEASURED from the artifact, its counts file, and the
test's manifest assertions. F1 counts are MEASURED from `cs.json`/`vk.json`.

| item | F1 | F2 |
|---|---|---|
| k | 6 | 20 |
| advice columns (commitments) | 8 | 15 |
| advice evals | 11 queries | 40 |
| fixed columns | 19 | 27 (17 evaluated + 10 simple selectors) |
| permutation columns / sets | 8 / 3 | 18 / 6 (chunk 3, hence csDegree 5, INFERRED) |
| lookups | 1 (1 helper) | 2 (1 helper each) |
| trashcans | 1 | 1 (partial_round_gate) |
| gates (normal + trash names) | 5 | 11 (`tests/ivc_keccak_solidity.rs:822-861`: arith, 12_minus_34, parallel_add, 6 foreign-field gates, full/partial round) |
| y-batched identities | ~17 | 49 (29 gate + 13 permutation + 6 lookup + 1 trash; commit `33a3b20`) |
| rotations | {0, 1, -9} | {-10, -1, 0, 1} (PCS block 1) |
| point sets | 3 | 5 (cardinalities 3, 3, 2, 2, 1) |
| proof evals | 48 | 102 |
| proof bytes (compressed / padded) | 2640 / 4320 | 5056 / 7776 |
| VK payload words | 4576 B | 17024 B (532 words: 178 quotient constants, 143 program words, 27 + 18 commitments) |

The F1 `cs.json` is 125,612 bytes pretty-printed and 36,706 compact, for about 200 expression nodes
(MEASURED). For F2 I estimate (INFERRED) 3,000–10,000 nodes, because the six foreign-field gates over
7-limb integers dominate (the 7×7 pairwise arm of MODARITH7). That gives a **0.4–2 MB pretty `cs.json`**
and a `vk.json` of about 15 kB. It is fine for `include_str` plus the JSON importer
(`Instances/PoseidonFixture.lean:175`, generic).

### A3. Shape of the F2 object

**A3.1 Three contracts, two programs.**
- `Halo2VerifyingKey.sol`: a constructor writes `INVALID ‖ payload`. The runtime is data, not code.
- `Halo2QuotientEvaluator.sol` (1610 lines): a `fallback()` with one assembly block
  (`:109-1609`). Its body has 1,112 non-comment code lines, 27 `for` loops, 2 `switch` (opcode and
  native index), 15 `case`, 2 functions (`q_program_fail`, `q_pow5`), and **0 staticcall, 0 keccak256,
  0 caller/address/sload/log** (all MEASURED grep).
  - Input: `calldatasize == 0x6ac0`, else `revert(0,0)` (`:114`). The frame is copied by
    `calldatacopy(0x3680, 0, 0x6ac0)` (`:119`), which lands in the same addresses as the verifier's
    memory. It covers the VK payload (0x3680..), challenges at 0x7900, Lagrange values at 0x7c40, and
    evals at 0x9480 up to the frame end 0xa140.
  - Scratch: selector buckets at 0xb140, y powers at 0xb2c0, the accumulator at 0xb280, and the VM
    stack bounded by the guards 0xb8e0/0xbf80 (`:465`, `:476`).
  - Output: 12 words at 0x1000 = magic `…51554556414c0001`, `-nu_y(x)`, and 10 selector buckets
    (`:1601-1608`). The NatSpec at `:106-108` says the return frame "starts at 0x80", which is stale:
    `QUOTIENT_OUTPUT_MPTR = 0x1000`.
- `Halo2Verifier.sol` (2592 lines). The Yul has 14 functions inside `verifyProof`: F1's 15, minus
  `q_program_fail` and `q_pow5`, plus `validate_public_accumulator`. There are 25 staticcall sites.

The evaluator's arithmetic is driven by **data held in the VK payload**: `q_const_mptr := 0x3a60`
and `q_program_mptr := 0x50a0` (`:268-271`). So evaluator correctness is a property of the pair
(interpreter text, VK payload). For the theorem this is one more external program, called by
`staticcall` and pinned by extcodehash, whose code is **not** a function of the verifier's text alone.

**A3.2 Block diff, F2 verifier against F1 (`poseidon-fixture-dump/Halo2Verifier.sol`).** The table is
MEASURED with `f2/tools/regions.py`. Boundaries are at the region marker lines (±3 lines). "Numbers
only" means the code lines are equal after replacing every numeric literal.

| block (template) | F1 lines | F2 lines | code lines F1/F2 | verdict |
|---|---|---|---|---|
| contract header: Constants.sol, PrecompileSmoke.sol, Constructors.sol, notice | 1-573 | 1-597 | 221/232 | parameters, plus **new**: `AUTHORIZED_QUOTIENT`, `EXPECTED_QUOTIENT_LENGTH`/`CODEHASH`, `ACC_RHS_MSM_GAS`, and a two-dependency constructor |
| verifyProof entry and ABI guard | 574-629 | 598-656 | 16/17 | +1 line `let quotientEvaluator := AUTHORIZED_QUOTIENT` |
| AssemblyHelpers.yul | 630-931 | 657-958 | 151/151 | numbers only |
| AccumulatorHelpers.yul (4 decoders) | 932-1099 | 959-1123 | 84/84 | identical code |
| AccumulatorHelpers.yul `validate_public_accumulator` | — | 1124-1265 | 0/54 | **new code** (template arm `expected_has_accumulator`) |
| `let r` / `let success` | 1100-1105 | 1266-1271 | 2/2 | identical |
| VkLoading.yul | 1106-1178 | 1272-1342 | 21/21 | numbers only (acc header words now 1/4/7/56) |
| acc validation call (VkLoading.yul tail) | — | 1343-1365 | 0/6 | **new code** |
| TranscriptProofParser.yul | 1179-1497 | 1366-1700 | 122/134 | parameters, plus one more unrolled copy of the per-lookup helper/acc section (template loop) |
| Lagrange.yul | 1498-1587 | 1701-1792 | 59/59 | numbers only (k 20, 16 instances, 10 negative Lagranges) |
| quotient numerator | 1588-2541 (embedded: helpers + VM + generated families, 659 code lines) | 1793-1832 (external call, 14 code lines) | 659/14 | **replaced**: the external-call arm of QuotientAndLinearization.yul. The numerator moves to the evaluator |
| linearization scalar prep | 2542-2582 | 1833-1873 | 18/18 | numbers only |
| Pcs.yul and generated multi-prepare blocks | 2583-2979 | 1874-2501 | 347/567 | **generated per circuit**: same families, 10 sub-blocks vs 8, 5 point sets vs 3, final MSM 78 vs 47 pairs |
| FinalPairing.yul | 2980-3011 | 2502-2580 | 2/35 | **new code** (alpha-batch arm, 33 lines) |
| TraceReturn.yul | 3012-3024 | 2581-2593 | 6/6 | identical |

**A3.3 Lean partials rendered at an F2-shaped context (MEASURED).** `f2/lean/object/IvcPartials.lean`
is `poseidonCtx` with these fields overridden from the F2 artifact:
- vk 0x3680; acc on, offset 4, 7×56 limbs, carried scalars, tail `[]`, `accMsmScratch` 0xb140;
- external quotient (0x3680, 0x6ac0, 0x180, magic) with a codehash;
- k 20, 16 instances, 10 negative Lagranges, 4 quotients, 10 selectors;
- one phase of 0x780 bytes, the F2 proof layout, 2 lookups, 6 Z, `lookupHPlusAcc` 4.

Output (`IvcPartials.out`):

```
AssemblyHelpers: len 16223, occ F2 1, includeBoundary F2 true
AccumulatorHelpers: len 17544, occ F2 1, includeBoundary F2 true
VkLoading: len 5820, occ F2 1, includeBoundary F2 true
TranscriptProofParser: len 17968, occ F2 1, includeBoundary F2 true
Lagrange: len 4745, occ F2 1, includeBoundary F2 true
QuotientAndLinearization(external): len 4579, occ F2 1, includeBoundary F2 true
FinalPairing: len 4221, occ F2 1, includeBoundary F2 true
```

This is the first byte evidence for the acc arm, the external arm and the batch arm: each is exact
against a Rust artifact. The probe's first run had `numNegLagranges` 9 and was red on Lagrange (0x0320
against 0x0340), so the gate discriminates. Not probed: the contract root and constants
(`Contracts.lean:340`), PCS (needs `Data` from the decider key), the evaluator contract (needs the
quotient plan), and the VK contract (needs the payload).

### A4. Regenerating a consistent dump

**A4.1 What is on disk.**

The `.sol` triple is tracked:
- Last touched by `cd606aa` (2026-10-23, "keep the production (uninstrumented) IVC dump"), after
  `33a3b20` (the regeneration, "602 s" with `rust-verifier-trace`). Both were authored on another
  machine (`julian@Mac.lan`).
- The Nov 16 mtime is a checkout time.
- No generator, template or circuit commit has landed since `cd606aa`, except `9822446`, which is an
  additive `named_bytes` change (MEASURED git log).

The `.bin`/`.txt` files are untracked and dated 2026-10-07. They are from an earlier local run with
older templates: verifier source 122,927 bytes, quotient runtime 9531.

I compared every VK payload word of the current `Halo2VerifyingKey.sol` against the Oct 7
`Halo2VerifyingKey.creation.bin` (MEASURED):

| payload section | words found in the Oct 7 bytecode |
|---|---|
| vk_digest, all 11 header words, G1/G2/NEG_S_G2 bases | all |
| fixed commitment words | 108/108 |
| permutation commitment words | 72/72 |
| quotient constants | 167/178 |
| quotient program words | 0/143 |

So the **decider key is unchanged** and only the quotient program encoding moved. The `proof.bin` +
`instance.le` pair is therefore very likely still a valid proof for the current key (INFERRED; not run).
`calldata.bin` (8420 B = 4 + 3·32 + 7776 + 32 + 512) matches the current proof layout `0x1e60`. The
`.sol`/`.bin` pair is still not one run, and the evaluator codehash in the `.sol` does not match any
local compile.

**A4.2 Recipe** (from `tests/ivc_keccak_solidity.rs:1-45`, `:950-1350`, and `33a3b20`):

```
HALO2_SOLIDITY_RUN_IVC_BENCH=1 SRS_DIR=<repo>/zk_stdlib/examples/assets \
cargo test --release -p halo2_solidity_verifier \
  --features evm,truncated-challenges,in-circuit-fewer-point-sets[,rust-verifier-trace] \
  --test ivc_keccak_solidity -- --nocapture
```

- The `SRS_DIR` default is `CARGO_MANIFEST_DIR/../../zk_stdlib/examples/assets` (`:665-672`).
- **Both files are present**: `midnight-srs-2p19` (100,663,684 B) and `midnight-srs-2p20`
  (201,326,980 B) (MEASURED `ls`).
- Pinned solc 0.8.30 is required (`:970`).
- Run time: 602 s with trace (commit `33a3b20`).
- The test writes everything into one directory from one run (`:1185-1321`), so a single run fixes
  the staleness. A leaf-bundle mode exists (`HALO2_SOLIDITY_WRITE_IVC_LEAF_BUNDLE`, `:901-939`).

**A4.3 Test SRS.** There is no test-SRS source: `SrsSource` is `{Filecoin, Midnight}`
(`zk_stdlib/src/utils/plonk_api.rs:259-262`), and the test hard-codes `SrsSource::Midnight` at `:984`,
`:912`, `:757`. `ParamsKZG::unsafe_setup(k, rng)` exists (`proofs/src/poly/kzg/params.rs:98-143`;
draws `s = Fr::random(rng)`; k ≤ `Fr::S`). `downsize` also exists (`:44`).

A test-SRS variant is a test-file edit in `proofs/solidity-verifier/tests`, the scope D-P69 already
touches:

```
srs20 = unsafe_setup(20, seeded)
srs19 = srs20.clone().downsize(19)
```

The same trapdoor is **required** (§B7). Export `s` and assert `G2·s == s_g2`, as REF.11 does for F1.
The cost of `unsafe_setup(20)` is 2 × 2^20 parallel G1 scalar multiplications (INFERRED: minutes).

### A5. `SupportedV3` / `SupportedV2` clause by clause on the IVC decider key (GEN.2 by reading)

`SupportedV3` is `StatementsV3.lean:592-604`; `SupportedV2` is `LoweringV2/Statements.lean:118-134`.
They are the same except `wf`.

| clause | value on the IVC key | how |
|---|---|---|
| `advice` (numAdviceColumns ≠ 0) | **true** (15 advice commitments) | MEASURED (parser 0x780 / 0x80) |
| `instShape` (2 instance cols, 1 committed) | **true** (test comment `:1112-1114`; 1 committed-instance eval in counts) | READ + MEASURED |
| `noRotInst` (instance queries at rotation 0) | **true, inferred**: the public instance eval is one Lagrange sum at x (`Halo2Verifier.sol:1758-1767`) and the committed instance has one eval | INFERRED; needs `vk.json` |
| `singlePhase` (numChallenges = 0) | **true**: one user phase, 0 "User-phase challenge" lines | MEASURED |
| `hLimbs` (quotient degree = csDegree − 1) | **true, inferred**: 4 quotient limbs (proof-length arithmetic); csDegree 5 from permutation chunk 3 = 18/6 | INFERRED |
| `vkPoints` (fixed + sigma commitments `ptReadable`) | **true**: 27 + 18 points from the VK payload are canonical EIP encodings, on the curve and in the r-torsion (1 fixed commitment is the identity) | MEASURED in Python (not via the Lean codec) |
| `layout` (memory map WF, `validate`) | unmeasured (needs the Lean plan) | — |
| `production` (trace off, gas checkpoints off) | **true** (0 `trace_u256`, 0 `gas_checkpoint`, 0 `log1`) | MEASURED |
| `wf : WellFormedV3` | partial: `permutationCommitmentsMatch` 18 = 18 (sigma evals) **true**; `fixedCommitmentsMatch` 27 = 17 + 10 **true**; `chunkLenPositive` (csDegree ≥ 3) true (inferred 5); `singlePhase` true; `committedInstancesOn` true (`Features.solidity`); `csDegreeMatches`, `domainConsistent` unmeasured | MEASURED/INFERRED |
| `noAcc` | **false**: `HAS_ACCUMULATOR` 1, `ACC_OFFSET` 4, 7×56 limbs | MEASURED |
| `embeddedQuotient` | **false**: `RenderQuotient::ExternalPinned` (`tests/...:1155`), `AUTHORIZED_QUOTIENT` | READ + MEASURED |
| `separateVk` | **true** (`RenderVk::Separate`, `:1154`) | READ |
| other `ValidV3` clause needing care: `cdBound` | 0x1ec4 + 32 + 512 < 2^256, true | arithmetic |

So **exactly the two known clauses fail** (`noAcc`, `embeddedQuotient`). Widening the class means
replacing them with:
1. `accumulator = some enc` with `enc.kind = .pointAndScalar` and an empty tail (the F2 shape), or more
   generally `enc.validFor`; and
2. an external-quotient clause that binds the evaluator code (see A6 and §C).

GEN.2's own acceptance (a Lean `#eval` table, an F1 control, and the committed `ivc/vk.json`) still
needs the export.

### A6. Genericity profile of the new code

The classes are:
- **FIXED**: identical text for every circuit.
- **LAYOUT**: depends on the circuit only through layout constants or flags.
- **GEN**: generated per circuit.

| piece | profile | evidence |
|---|---|---|
| 4 accumulator decoders (`load_acc_*`, `check_acc_coord_packing`, `is_bls_p_minus_one`) | FIXED. Rendered for every profile, even with no accumulator | identical code F1/F2 (MEASURED); template outside the `if` (`VerifierPartials.lean:3173-3180`) |
| `validate_public_accumulator` | LAYOUT: offset (`add(INSTANCE_CPTR, 0x80)`), scratch address, and three template arms (carried scalars yes/no; tail empty/non-empty, with a `for` unrolled **per fixed base**, `AccumulatorHelpers.yul:305-337`). The tail is the only per-circuit list and is empty for a fully collapsed accumulator | MEASURED (probe) + READ. Moonlight (point-pair, older templates) differs in 6/11 lines |
| acc validation call site | FIXED | template text |
| external evaluator call site | LAYOUT: frame base and length, output length, magic, selector count (loop bound) | probe |
| alpha-batched FinalPairing | FIXED apart from four layout offsets (batch pointer, domain tag, G1 sizes) | F2 vs `moonlight-wrap-solidity-dump` FinalPairing: **identical code** (MEASURED) |
| evaluator contract shell (constants, fallback guard, `calldatacopy`, return loop) | LAYOUT (23 memory constants, frame metadata, selector count) | `Contracts.lean:390-421`, gate 17 |
| evaluator numerator body | **an interpreter over a data program**, plus per-circuit straight-line code (detail below) | MEASURED |

**The evaluator numerator body in detail.** It has 1,100 code lines in F2 (MEASURED). Of these, 626
are, after literal normalisation, the same lines as F1's embedded numerator. That is the shared
template `QuotientNumeratorBlock.yul`: the VM dispatch loop `for { } lt(q_pc, q_end)` with
`switch q_op` (`Halo2QuotientEvaluator.sol:448-456`), the opcode arms, and the fold logic. Another 116
lines are the MODARITH7 arm, which is template text gated by an opcode-usage flag. The rest, about
350 lines, are **GEN straight-line Yul**: the native permutation, lookup and identity callbacks (4
native identity cases in F2, 3 in F1), the inline prefix, and the post-VM selector folds.

**Where the per-circuit data lives.** The VM bytecode (143 words) and the Fr constant table (178
words) are in the **VK payload**, pinned by the VK codehash and read at 0x50a0 and 0x3a60. In the Lean
port the families are `PartialCtx.quotient*Computations` (`VerifierPartials.lean:258-299`).

**Comparison with other generated verifiers.** `moonlight-wrap-solidity-dump` is untracked, from
2026-08-13 with older templates, and has the same shape: k 20, 27/18 commitments, 5056-byte proof.
Against F2 it gives:
- Pcs: numbers only (567 code lines each);
- TranscriptProofParser and VkLoading: numbers only;
- FinalPairing, Linearization and TraceReturn: identical.

So the generated PCS families are stable across circuits of one shape. Different shapes (F1) change
only counts and addresses inside the same families.

---

## B. Reference: the Lean verifier on the decider proof

### B5. Protocol features, Exec coverage

There is no `sorry` in any `Halo2/Exec/*.lean` or `Exec/Kzg/*.lean`, and 0 references to Poseidon
(MEASURED grep). The KAT counts per file are 0–22 `#eval`, mostly on toy `Fr 17` data. The only
real-proof run is the scratch F1 run (`V3-evidence/lean/reference/RunABC.lean`, with the shims S1/S2
for REF.2/REF.1).

| feature | Exec | exercised on a real proof? | F2 delta |
|---|---|---|---|
| trash argument | `Trash.lean` (producer `:135-137`) | F1 (1 trashcan) | same shape |
| LogUp with helpers | `Logup.lean` (`:196-211`) | F1: 1 lookup, 1 helper | **2 lookups**. Slot indices `lookupM proof lookup` with lookup > 0 are not tested (REF.1 adds the index) |
| permutation | `Permutation.lean` (`:265-306`) | F1: 3 sets | **6 sets, 18 columns** |
| committed instance + public instances | `Verifier.lean:757-798` | F1: 1 public word | **16 words** (Lagrange `lIRange`, `Domain.lean:251`) |
| truncated challenges | `Arith.lean:265-280`, at kzg/mod.rs:457 | F1 | same |
| multi-open | `Kzg/MultiOpen.lean`, `Kzg/Utils.lean:123-195` | F1: 3 point sets (only with S2) | **5 point sets**, rotation **−1 (`prev`)** and −10. The `prev` arm of REF.2's canonicalisation is not exercised at F1 |
| fewer point sets | runtime branch (`Pcs.lean:79-82`, `Kzg/Utils.lean:199`) | never | **not needed for F2** |
| multi-limb quotient | default | F1 (4 limbs) | same (4) |
| domain k = 20 | `Domain.lean:125-160` (`repeatSquare`, `powVartime` on n = 2^20) | F1 k = 6 | log-cost only; no O(n) loop found (READ) |
| foreign-field gate expressions | generic `Expression` evaluation | F1 has no foreign-field gates | large expressions; Lean-side cost, not a fidelity gap |

Hard-wired to F1: nothing in `Exec`. The F1-specific code is in `Instances/` (`PoseidonFixture.lean:35`,
`:38`, `:175` `include_str` of the poseidon bundle; `PoseidonEnv`). An IVC test needs a sibling of those
files.

### B6. The accumulator on the reference side

**What exists.**
- `Exec/Accumulator.lean` (2738 lines, 0 `sorry`): `AccumulatorEncodingKind {pointAndScalar,
  pointPair}` (`:170-177`), the limb codec (`:328-440`), `decodeAcc` (`:1009-1046`), `alphaOf`
  (`:1068-1074`), `batchedCheck` (`:1090-1101`), `KzgAcc.check/fromDualMsm/accumulate` (`:716-904`),
  and 12 KAT `#eval`s on synthetic points.
- The header (`:27-56`) states the choice: the file **models the contract, not Rust** (R-10). The
  POW2 sponge of `Accumulator::accumulate` is deliberately not ported (`:1131-1133`).
- `Lowering/Accumulator.lean` has `ContractRefAcceptsAcc` (`:1424-1450`, the acc-mode acceptance
  predicate over raw instance words) and these proved lemmas:
  - `contractRefAcceptsAcc_none` (`:1463`);
  - `contractRef_acc_complete` (`:1497`): Rust-verify ok, decoded acc, and `KzgAcc.check` imply the
    contract reference accepts;
  - `batched_complete` (`:1245`) and `batched_atMostOneRoot` (`:1260`);
  - `dualMsm_check_iff_contract` (`:1320`);
  - `decodeAcc_encode` (`:544`, `.pointAndScalar`).

**Every `sorry`** (MEASURED grep):

| file:line | theorem | status |
|---|---|---|
| `Lowering/Accumulator.lean:142` | `decodeAcc_injective` (R-25 projected form) | open obligation. The plan's unprojected form is recorded **FALSE** (`:133`; `Exec/Accumulator.lean:997-1004`; exhibit `accIdentityKats_ok`) |
| `Lowering/Accumulator.lean:955` | `decodeAcc_encode_pointPair` | open. The sketch form without `hfb` is recorded **false** ("third false-as-written statement", `:923-933`) |
| `Lowering/AccEncoding.lean:194` | `toExec_fullyCollapsed` | open bridge lemma |
| `Lowering/AccEncoding.lean:254` | `toExec_validFor` | open. Its hypothesis `hn` is load-bearing, and an example after it refutes the weakened form |
| `Lowering/AccEncoding.lean:306` | `toExec_fixedScalarCount` | open bridge lemma |

**Statements recorded as false or refuted:**
- R-25 (the injectivity statement above).
- R-26 (`decodeAcc_encode` is false for `.pointPair` with the generic encoder; `Lowering/Accumulator.lean:31-35`).
- The third, `hfb`-less point-pair round trip.
- R-10 (acc-mode Rust ≠ contract predicate; `Exec/Accumulator.lean:27-56`).
- Related to the evaluator: `Bridge.rel_worldLocal` (`Yul/Bridge.lean:1006`, `sorry`; "NOT TRUE AS
  STATED", with a separating exhibit), on which `Evaluator.rel_worldLocal`/`honestCalls` depend
  (`Lowering/Partials.lean:39`, `Obligations.lean:154`). Its docstring says "the evaluator DOES read
  keccakOf". **This is not true of the F2 evaluator contract**: it has 0 keccak256, caller(), sload or
  log (MEASURED). A per-program world-locality argument may therefore be available even though the
  generic one is refuted (INFERRED).

**R-52 ("-G" is the identity).** The defect is real, READ at `Exec/Accumulator.lean:556`:
`accMapInsert #[] "-G" ((1 : G₁)⁻¹)`. In multiplicative notation `1⁻¹ = 1`, so the "-G" base is the
identity, where Rust has `-G1::generator()`. The code that cites it is `Lowering/Surface.lean:211`,
`:902`, `Lowering/Accumulator.lean:50`, `:1419`, `Inv.lean:752`. **Label collision**: `docs/REVIEW.md:1769`
"R-52" is a different finding (P-09f recognisers). The "-G" defect has no REVIEW entry under that
number.

**What F2 actually uses.** READ at `Halo2Verifier.sol:1146-1262` and the test's
`AccumulatorEncoding::new(4, 7, 56)` (`tests/ivc_keccak_solidity.rs:1125-1129`); `new` means
`PointAndScalar` (`src/api.rs:82-90`).
- **Kind `pointAndScalar`, empty fixed-base tail.** The layout is LHS point (5 words: x 2, y 2, flag),
  LHS scalar, RHS point (5), RHS scalar, so 12 words at offset 4.
- MEASURED from `instance.le` (Python):
  - words 0-3 are the two leaf states (cnt = 1, identical `val`);
  - both flags are 0;
  - both scalars are 1;
  - both decoded points are on the BLS12-381 curve.
- So F2 is not affected by R-52 (no tail and no `fixedBases` use in `decodeAcc` or `batchedCheck`),
  nor by the point-pair falsities. The relevant proved lemma is `decodeAcc_encode` (`.pointAndScalar`).

**Rust meaning of the instances.**
- The decider circuit verifies two IVC leaf proofs in-circuit (`prepare`), accumulates each with the
  trivial outer accumulator, then accumulates the two (`tests/...:607-631`).
- It fully collapses the result over the IVC VK fixed bases (`fully_collapsed_accumulator`, `:251-260`:
  `Accumulator::new(Msm[lhs]·1, Msm[rhs]·1)`).
- It constrains that `[lhs, 1, rhs, 1]` equals the public accumulator (`:262-290`, `:638`).
- The instance is `[leaf_state_0, leaf_state_1, as_public_input(final_acc)]` (`:541-552`).
- The *meaning* (both leaves valid) needs `final_acc.check(ivc_params, {})`, that is
  `DualMSM(lhs, rhs).check` (`circuits/src/verifier/accumulator.rs:139-149`), with the **IVC** SRS
  (`tests/...:1021-1024`).
- That check is **not** part of the Rust decider `verify` (`zk_stdlib/src/lib.rs:1804-1828`).
- The contract replaces "Rust KZG check ∧ acc check" by one alpha-batched check:
  - "both hold" implies "batched holds" (`batched_complete`);
  - the converse fails for at most one alpha (`batched_atMostOneRoot`).
- So a "returns true **iff** the Lean verifier accepts" headline in acc mode is only stateable against
  the contract-faithful `ContractRefAcceptsAcc`, not against "Rust verify ∧ acc check".
- The R-10 gap between the two is a soundness-style (probabilistic) statement, outside the
  equivalence.

### B7. Pairing and SRS

**Trapdoor-free:**
- decoding all commitments into `G₁z` (computable codec, scratch `RefModel.lean`);
- the transcript, `prepare`, `DualMSM.split`, and `MSMKZG.eval` of both KZG channels;
- `decodeAcc` (two torsion checks), `fullyCollapse`, and `alphaOf` (keccak over EIP encodings);
- the two batched points `kzg_rhs + α·acc_rhs` and `kzg_lhs + α·acc_lhs`.

That is everything up to the two G1 inputs of the single final pairing. A reference gate that
compares these against a Rust trace works with the Midnight SRS. F1's gate does this today (agreement,
not acceptance).

**Trapdoor-dependent:**
- `DualMSM.check` / `batchedCheck` at the constructed pairing, which needs `s` as data (`check_iff_g1`:
  `s • left = right`);
- `KeyAgrees.negSG2` / `SrsEncodes`;
- the generator's own SRS check (`srsTauIsConsistent`, `Generator/Vk.lean:701-704`);
- the separate Rust `final_acc.check` (IVC SRS).

**A test-SRS regeneration changes:**
- the IVC VK and its fixed commitments. These are baked into the decider circuit as fixed values
  (`assign_fixed_vk`, `:589-595`), so the decider cs fixed columns, the decider VK and the decider
  commitments all change;
- the leaf proofs, `final_acc`, the decider proof, `instance.le`, NEG_S_G2/G2 in the payload, the VK
  codehash, and BUILD_ID.

The evaluator text should not change: it depends on the gates and layout, not the SRS (INFERRED).

**Constraint:** IVC and decider SRS must share `s`. Otherwise the contract's batched equation (one
`NEG_S_G2`) rejects honest proofs. Use one `unsafe_setup(20)` and `downsize(19)` (§A4.3).

### B8. Costs

**MEASURED at `c22b51a`** (F1, `RunABC.lean` run C, `f2/lean/refout/RunABC.log`, 29 s for all three
runs). One run C is 8.9 s:

| step | time |
|---|---|
| 27 VK points decoded | 2.8 s (about 104 ms per point) |
| parseTrace (15 reads) | 2.0 s |
| readAlgebra | 0.55 s |
| linearize + phaseA | 0.03 s |
| multiPrepare | 0.6 s |
| final MSM of 1 + 45 terms | 2.9 s (about 63 ms per term) |

**F2 estimate (INFERRED, linear scaling):**

| step | estimate |
|---|---|
| 45 VK points | ~4.7 s |
| 34 proof G1 points (parse) | ~3.5 s |
| 102 evals and 49 identities, foreign-field gates evaluated by Exec over `ZMod` | ~1–3 s (field ops only; no group ops) |
| final MSM of ~80 terms | ~5 s |
| acc decode (2 torsion checks) + 2 scalings + alpha keccak | ~0.5 s |

The total is about **15–20 s** in the VM. k = 20 costs 20 squarings (`repeatSquare`/`powVartime`).
The Lagrange values for 16 instances and 10 blinds are 26 batch-inverted terms. Nothing found is
O(2^k) on the verifier path. The heavy part of the *object* side is different: running the 1,100-line
evaluator plus the verifier under the fuel interpreter. F1's incomplete AST ran in about 10 s
(`PLAN-V3.md:200`). F2 has more VM iterations (143 program words of bytecode), so expect a minute or
more (INFERRED).

---

## C. What statements will need (inputs to the statement author; no statements designed here)

From the object:
1. `GeneratedBy` must cover the **evaluator text** and the **VK payload's quotient program/constants**,
   not only the verifier text.
2. The evaluator runtime length and codehash must be **inputs** (solc output), tied to the evaluator
   program by the trusted solc boundary. A new trusted item, analogous to `EntryFrame`.
3. A call relation for the one non-precompile `staticcall` (`Halo2Verifier.sol:1817`). It needs the
   extcodehash pin (`:1808-1811`), the frame `[0x3680, 0x3680+0x6ac0)`, and the 0x180-byte return.
   The callee reads only calldata and its own memory (MEASURED: no keccak, caller or storage).
4. Scope: `validate_public_accumulator` becomes a hoisted helper, and the acc-validation call and the
   batch block become slices or rows.

From the reference:
1. The acc-mode acceptance predicate `ContractRefAcceptsAcc` (contract-faithful).
2. The bridge sorries `toExec_*` and the `decodeAcc` lemmas, in the `.pointAndScalar` / empty-tail case.
3. The R-10 relation stated as soundness, outside the equivalence.

---

## D. Work items (class widening plus an IVC test bundle)

The sizes: S is at most 1 card, M is 2–4 cards, L is more.

| # | item | size |
|---|---|---|
| W1 | Rust: decider bundle exporter (schema 2+, acc section, IVC params, trace ids 29/30), factored from `ivc_keccak_solidity.rs` | M |
| W2 | Rust: test-SRS variant (shared seeded trapdoor, `downsize(19)`), one consistent dump plus bundle | S–M |
| W3 | GEN.2 as carded on the exported key (Lean `#eval` table and F1 control) | S |
| W4 | Lean: F2 partial-render gates (this memo's probe, landed against the regenerated dump), including the root/constants ctx for acc + external | S |
| W5 | Lean: `generateAll` glue (OBJ.6/OBJ.7) extended to acc config and `RenderQuotient.externalPinned`; evaluator ctx and frame from the plan; the evaluator text as a generated artifact; solc pins as inputs | M |
| W6 | Lean: quotient plan and VM build on the decider cs (MODARITH7 and limb recognisers on real expressions; VK payload words equal to the Rust payload's 178 + 143 words) | M–L (first real use of limb shapes) |
| W7 | Lean: PCS emitter on the decider `Data` (5 sets, rotation −1) against the artifact | S–M |
| W8 | Reference: REF.1/REF.2 producers checked on the decider (2 lookups, `prev`, 5 sets); staged run against the decider `trace.json`, including `acc_lhs`/`acc_rhs` and alpha | M |
| W9 | Reference: run `ContractRefAcceptsAcc` on the test-SRS bundle (accepts), with mutants (flag, scalar ≥ r, off-curve) | S–M |
| W10 | Statements: widen `SupportedV3` (`noAcc` → `.pointAndScalar` with the `validFor` shape; `embeddedQuotient` → external with the evaluator binding), the evaluator call relation (restate `rel_worldLocal` per program, X2/RV-31), and `toExec_*` + `decodeAcc` obligations | L |
| W11 | Docs: renumber the "-G identity" defect (it collides with REVIEW R-52); fix the evaluator NatSpec "0x80" | S |

---

## E. Contradictions with the brief

1. **"Fewer-point-sets multi-open"**: F2's outer proof does not use it. `in-circuit-fewer-point-sets`
   affects only the recursive verifier circuit. Dummy PCS evals are 0 and there are 5 ordinary point
   sets. `Encoding.lean:474`'s `numPointSets := 0` is a placeholder that `Vk.lean:1038` fills.
2. **"Two G1 points as 7×56-bit limbs"**: there are also **two explicit scalar words** (`PointAndScalar`,
   circuit-pinned to 1). The 12 words are 2 × (5 + 1). The tail is empty.
3. **"Dated Nov 16"**: that is checkout mtime. The `.sol` files were committed on 2026-10-23 from
   another machine. The key is unchanged since the local 2026-10-07 `.bin` run (MEASURED); the
   quotient program is not.
4. **Evaluator pin**: `EXPECTED_QUOTIENT_LENGTH` is solc output (9656, 9531 and 10,420 on record), so
   the Lean generator cannot produce it.
5. **R-52**: the code's "-G identity" R-52 is not `REVIEW.md`'s R-52. The defect is real but does not
   bite F2.
6. **Rust-faithful reference in acc mode**: Rust does not verify the accumulator inside the decider
   `verify`. The contract-faithful predicate is the only one an "iff" can be stated against.
7. PLAN-V3 §0 and §5 "Later" put accumulator mode (X1) and the external evaluator (X2) out of scope.
   Widening the class reopens both.

Please review the accuracy and completeness of this memo before relying on it.
