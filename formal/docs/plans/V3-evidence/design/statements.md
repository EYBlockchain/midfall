<!-- Design memo behind PLAN-V3 (M3 — the statement surface). Written by one design pass and kept as delivered, with local paths made repository-relative. Decision numbers inside predate PLAN-V3 §2 (D-P53 onward): follow that table. Where this memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. -->

# PLAN-V3 design memo - area "statements": the repaired statement surface

## 0. Provenance

- The repository, branch `formal/baseline`. HEAD at start `6bde89f`, at end `2cad8cc`. Both differ from the brief's `f2fe99b` by docs only; no Lean source changed, so the built tree is the one measured.
- Scratch directory S = `docs/plans/V3-evidence/lean/statements/`.
- Three deliverables, all typechecking in about 10 s each:
  - `S/StatementsV3.lean` - the V3 surface, namespace `Midfall.LoweringV3`, no `Midfall/Instances` import. Four stated obligations are `sorry`; all definitions are real.
  - `S/StatementsV3Deploy.lean` - the surface evaluated at `Midfall.Instances` data. No `sorry`.
  - `S/StatementsV3Falsifiers.lean` - machine checks that the frozen text is broken. No `sorry` of its own.
- A fourth experiment, `S/port/`, holds copies of five tree files with only `Render.scope` changed.
- Commands (run from `formal/`):
  - `lake env lean --root=S -o S/StatementsV3.olean S/StatementsV3.lean`
  - `lake env sh -c 'LEAN_PATH="$LEAN_PATH:S" lean S/StatementsV3Deploy.lean'` (same for Falsifiers)

V3 names carry a suffix only so the scratch file can sit beside the frozen text. After cut-over they replace the same-named V2 items in place. `Render` is not changed.

## 1. The difference table (k)

Scratch line numbers refer to `StatementsV3.lean`.

| # | Item | Frozen V2 | V3 | Kind |
|---|---|---|---|---|
| 1 | `Render.scope` | Statements.lean:109-110 `[hoist D R.helpers]` | `scopeV3` :219 `[hoist D R.helpers ++ hoist D (slicesV3 R)]` | repaired |
| 2 | `Render.slices` | Blocks.lean:202 (refinable) | `slicesV3` :209, same text, moved into the statement surface | moved |
| 3 | `SupportedV2.wf` | Statements.lean:128 | `SupportedV3.wf : WellFormedV3 ..` :592 | repaired |
| 4 | `WellFormed.permutationCommitmentsMatch` | Exec/VerifyingKey.lean:114-116 `= divCeil columns.size (csDegree - 2)` | `WellFormedV3` :283 `= vk.cs.permutation.columns.size` | repaired |
| 5 | `Valid.circuitMeta` | Statements.lean:186-187 | `PlanMeta R` :320 | repaired |
| 6 | `Valid.layout` | Statements.lean:189-190 | unchanged text | - |
| 7 | `Valid.payload` | absent | `PayloadAgrees R` :373 (13 fields) | added |
| 8 | `Valid.exitDiscipline` | absent | `ExitDiscipline (R.prog 0 0)` :526 | added |
| 9 | `Valid.noShadow` | absent | `noShadowB R = true` :233 | added |
| 10 | `Valid.cdBound` | absent | `proofEnd + 32 + 32 * numInstances < 2 ^ 256` | added |
| 11 | `EntryFrame` | Statements.lean:240-247 | `EntryFrameV3` :658, adds `cdSize : cd.size < 2 ^ 256` | repaired |
| 12 | `LoweringEquivalence` | Statements.lean:298-311 | :818 - `EntryFrameV3`; codec laws for all conjuncts; conjunct 4 | repaired |
| 13 | `HypothesesInhabited` | Statements.lean:317-320 | :923 - `H := keccak256`, codec laws, `LeanAccepts` | repaired |
| 14 | `EntryFrameInhabited` | Statements.lean:327-330 | `entryFrame_inhabitedV3` :677, one more premise `hcd` | repaired |
| 15 | `calldataOf` | Statements.lean:335-340 | `calldataOfV3` :139 | repaired |
| 16 | `EndToEnd` | Statements.lean:347-361 | :946 - V3 items; one `hcodec : G1CodecLawsV3` replaces `hcodec` + `hcomp` | repaired |
| 17 | codec bundles | Assumptions/Codec.lean:75-90 only | `G1CodecHeadlineLaws` :70, `G1CodecLawsV3` :81 | added |
| 18 | `rejects_of_not_accepts` | Blocks.lean:356 (sorried, false) | deleted; `TwoOutcomes` :550, `twoOutcomes_of_exitDiscipline` :565 | replaced |
| 19 | `prog_slices_decomp` | Blocks.lean:220 | `prog_slices_decompV3` :243 | restated |
| 20 | `hoist_prog_addr_indep` | Blocks.lean:145 (sorried) | corollary `hoist_prog_addr_indepV3` :252 | subsumed |
| 21 | `noWriters_prog` | Blocks.lean:340 (sorried) | `scans_prog_addr_indep` :575 | subsumed |
| 22 | `Render.Rejects` | Blocks.lean:134 | `RejectsV3` :853 | restated |
| 23 | `lowering_equivalence_of_blocks` | Blocks.lean:493 | `lowering_equivalenceV3_of` :882, proved | restated |

Unchanged: `Render`, `vkPins`, `vkProgressPins`, `DeploymentV2`, `callsOf`, `RunBody`, `LeanAccepts`, `SoundSide`, `CompleteSide`, all of `Program.lean` and `Shared.lean`.

## 2. The repairs

### (a) calldataOf

Old (Statements.lean:335-340): `repackProof .. >>= fun π' => encodeCalldata .. π' inst`. `Lowering.encodeCalldata` (Calldata.lean:241-250) repacks again.

New:
```lean
def calldataOfV3 (R : Render p G₁ G₂ Gₜ) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  Midfall.Lowering.repackThenEncode (p := p) R.cfg.numInstances
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π inst
```
- Witness: `#eval calldataOfV3_witness_ok` prints `true`. On `katPlan`/`toyCodec`/`katCompressed` the result is `.ok`, equals `Lowering.calldataOf toyCodec katMsgs [5]`, and `decodeCalldata katLayout 1 toyCodec` reads it back.
- Falsifier: `#eval frozenCalldata_isOk` prints `false`. `frozenCalldataOf_eq_core` proves by `rfl` that the evaluated function is the frozen `calldataOf`.
- Cause, measured: the first repack returns 416 bytes, the second demands 176 (`"lengthMismatch expected 176 actual 416"`). At the deployment layout the two lengths are 2640 and 4320.

### (b) circuitMeta and layout

Old clause 1 demands `R.plan.meta_` equal the raw `ConstraintSystemMeta.new` output, whose `numPointSets` is 0 (Encoding.lean:473). Rust post-processes it (vk.rs:504-519) and builds the layout from the result (plan.rs:238-244).

New clause 1 (clause 2 keeps its text):
```lean
def PlanMeta (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ (m0 : ConstraintSystemMeta) (n : Nat),
    ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok m0 ∧
    Data.new (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory = .ok R.plan.data ∧
    numPointSets (m0.setNumDummyEvals 0) R.plan.data = .ok n ∧
    R.plan.meta_ = (m0.setNumDummyEvals 0).setNumPointSets n
```
Measured at the deployment (`poseidonPlanV2` is `Midfall.Instances.PoseidonInputs.poseidonPlanV2`):

| plan | frozen clause 1 | layout clause | V3 clause 1 (decidable face) | derived proofLen | plan proofLen |
|---|---|---|---|---|---|
| today's (`meta_` raw) | true | false | false | 4224 | 4320 |
| faithful (`meta_.setNumPointSets 3`) | false | true | true | 4320 | 4320 |

- The Rust derivation itself, `metaDataForStableStaticLayout Features.solidity` (Vk.lean:1049) with the memory callee instantiated at the ported `VerifierMemoryLayout.new`, on the plan's own payload, returns `(10496, 10496, 3, 48, 0, true, false)`. That is: vkMptr 0x2900 equal to the plan's, numPointSets 3, numEvals 48, 0 dummy evals, meta equal to the faithful plan's and not to today's.
- Generic falsifier, proved: `frozenValid_numPointSets_zero : R.Valid → R.plan.meta_.numPointSets = 0`.
- The `Data` conjunct uses `R.plan.memory`, where Rust uses the intermediate default-config layout. `Data.new` reads ten base pointers (Encoding.lean:626-639) and the two layouts agree on all ten at the deployment. Whether they agree for every render is not settled.
- `planMetaB` covers conjuncts 1, 3 and 4. For conjunct 2, `Data.new` returns `.ok` with field counts 19/8/8 equal to the plan's, and `poseidonPlanV2.data` is by definition that value.

### (c) PayloadAgrees

One structure, 13 fields, slot numbers from `vkHeaderTemplateSlotsDefault` (Models.lean:734). Slot 0 stays `EnvAgrees.vkDigestWord`.

```lean
def payloadWord (PV : PlanView) (i : Nat) : Word256 := (PV.vk.constants.getD i ("", 0)).2
def g1WordsBytes (w : G1Words) : Bytes :=
  wordToBytesBE w.xHi ++ wordToBytesBE w.xLo ++ wordToBytesBE w.yHi ++ wordToBytesBE w.yLo

structure PayloadAgrees (R : Render p G₁ G₂ Gₜ) : Prop where
  numInstances : payloadWord R.pv vkHeaderTemplateSlotsDefault.numInstances =
    BitVec.ofNat 256 R.cfg.numInstances
  k : payloadWord R.pv vkHeaderTemplateSlotsDefault.k = BitVec.ofNat 256 R.vk.domain.k
  nInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.nInv =
    frWord ((((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹)
  omega : payloadWord R.pv vkHeaderTemplateSlotsDefault.omega = frWord R.vk.domain.omega
  omegaInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInv = frWord R.vk.domain.omegaInv
  omegaInvToL : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInvToL =
    frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs)
  accWords : (.. four header words ..) = accWordsOfEncoding R.cfg.accumulator
  g1Base : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip P.g₁
  g2Base : vkG2Words R.pv vkG2BaseSlot = R.encG2 P.g₂
  negSG2 : vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 R.sG2gen⁻¹
  fixedComms : R.pv.vk.fixedComms.map g1WordsBytes = R.vk.fixedCommitments.toList.map R.E.g1.toEip
  permutationComms : R.pv.vk.permutationComms.map g1WordsBytes =
    R.vk.permutation.commitments.toList.map R.E.g1.toEip
  delta : R.E.delta.val = Inline.natOfLiteral R.inputs.frDelta
```
Which Yul read each field justifies (line numbers in the fixture `Halo2Verifier.sol`):
- `numInstances`, `k`, `accWords`: the `eq(mload(*_MPTR), <literal>)` guards of VkLoading (:1145-1150).
- `nInv`: Lagrange (:1534). `omega`: Lagrange (:1513) and the PCS rotation points (:2599). `omegaInv`: PCS (:2600). `omegaInvToL`: both Lagrange loops (:1521, :1535).
- `g1Base`: the final MSM's `-v*G` term (:2955). `g2Base`, `negSG2`: `ec_pairing` (:911, :913).
- `fixedComms`, `permutationComms`: every PCS MSM read of a VK commitment.
- `delta`: `let delta := ..` (:1975).

Decidability:
- Decided by computation: the eight codec-free fields. Measured at the deployment in order numInstances, k, nInv, omega, omegaInv, omegaInvToL, accWords, delta: `[true, true, true, true, true, true, true, false]`. With the field's real constant in place of the placeholder 2, all eight are true.
- The fixture literal equals `modPow 7 (2^32) blsR` and is below r: `(true, true)`.
- Need a codec fact: `fixedComms`, `permutationComms` (`toEip` is noncomputable at `g1CodecZ`).
- Need a codec fact and pinned pairing generators: `g1Base`, `g2Base`, `negSG2` (the pairing axiom leaves g₁, g₂ unspecified).

Other measurements:
- Counts agree: `(19, 19, 8, 8)`.
- The payload's identity fixed commitments are at indices `[8, 10, 11, 12, 14, 16]`, six of them. The review lists five; index 14 is also all-zero in `Halo2VerifyingKey.sol` (:189-192). The Lean key has all nineteen at the identity.
- Falsifiers, proved: `envAgrees_delta_free` and `envAgrees_commitments_free` (the frozen `EnvAgrees` survives any `delta` and any commitments); `payloadAgrees_pins_delta`; `poseidon_payloadAgrees_not`.
- Constraint on WP-G1: the AST emitter for the native permutation block must take its `delta` literal from `R.inputs.frDelta`. In the VM arm the text's literal comes from `R.qblocks`; only `CodegenAgrees` then ties the two.

### (d) Scope and decomposition

Two candidates were tested:
- A, `[hoist D (R.prog 0 0)]` (the brief's suggestion): `fail_lookup .. := rfl` (Blocks/TraceReturn.lean:405) fails for a generic render.
- B, `[hoist D R.helpers ++ hoist D R.slices]`: it holds.

V3 takes B:
```lean
def scopeV3 (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) :
    FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) R.helpers ++ hoist (Bridge.Dialect c g) (slicesV3 R)]

theorem prog_slices_decompV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (vkAddr qAddr : U256) (c : ExternalCalls) (g : ExternalGas) :
    R.prog vkAddr qAddr =
        R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ slicesV3 R ∧
      [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = scopeV3 R c g   -- sorry (obligation)
```
- `hoist_prog_addr_indepV3` is proved from it, so the frozen sorried `hoist_prog_addr_indep` stops being a separate hole.
- `noShadowB` is the side condition of `inline_append`; it evaluates to `true` at the deployment.
- Dependent statements: copies of `Statements.lean` (scope changed to B), `Blocks.lean`, `Blocks/TraceReturn.lean`, `Blocks/VkLoading.lean` and `Blocks/FinalPairing.lean` compile with no proof edit. Sorry-warning counts are 0 / 10 / 0 / 3 / 3. `Blocks/Compose.lean` was not copied.
- The other Blocks.lean changes are rows 18-23 of the table.

### (e) EntryFrame

```lean
structure EntryFrameV3 .. : Prop where
  shape .. ; zeroAbove .. ; fmp .. ; callvalue .. ; selector ..   -- verbatim
  cdSize : cd.size < 2 ^ 256
```
- Choice: `2^256`, the weakest bound that repairs the statement and a fact about every EVM frame. A tighter bound shrinks the covered frames and buys no proof step, because every calldata offset the program computes is a render constant, bounded by the new decidable `Valid.cdBound` (4484 at the deployment).
- Witness: `entryFrame_inhabitedV3` proved, same witness as Blocks.lean:624 with one more premise.
- Falsifiers, proved:
  - `calldatasize_word_wraps`: the word is the same for `l` and `l ++ replicate (2^256) 0`.
  - `byteFrom_pad`, `wordFrom_pad`: every calldata read is blind to the padding.
  - `leanAccepts_pad_false`: Lean accepts at most one of the two.
  - `entryFrame_inhabited_padded`: the frozen frame admits the padded calldata.
  - `entryFrameV3_refuses_padded`: the V3 frame does not.
- Option, a decision: `EntryFrameV3'` (zero from `TRANSCRIPT_MPTR` instead of from `0x80`). `EntryFrameV3.toOption` proves it is the weaker assumption. It needs the pin `g1IdentityAbove`: 4096 ≤ 21760 at the deployment.

### (f) Totality

```lean
def GasTotal (g : ExternalGas) : Prop := ∀ st, ∃ w, g.Gas st w
def BodyTotal (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (vkAddr : U256)
    (st₀ : EvmState) : Prop :=
  ∀ g : ExternalGas, GasTotal g → ∃ obs, RunBody R vkAddr 0 (callsOf product) g st₀ obs
```
- Gas: `gas()` is the one builtin stuck under a partial oracle. The supported renders do not emit it (0 `gas` tokens in the main block), but requiring a total oracle stays true when the scope restrictions are lifted. `ofFun` and `any` are total, `none` is not (proved).
- Calls: a permissive run always exists trivially, by failing the first precompile call, so the permissive form says nothing about paths where the precompiles answer. The useful statement is existence under the honest relation. `callsOf_le_permissive` is proved; `BodyTotal.permissive` follows from the stated obligation `runBody_mono`.
- Why it is true for a well-formed program:
  - All 9 `staticcall`s of the main block target 0x05, 0x0b, 0x0c or 0x0f, and the honest relation answers every request at those addresses.
  - There are no `call`, `delegatecall`, `callcode` or `create` tokens.
  - Out-of-range `returndatacopy` halts rather than sticking.
- What remains is real work: closedness, call resolution and arity, and termination of every loop.

### (g) Codec laws

```lean
structure G1CodecHeadlineLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  toEip_one : c.toEip 1 = natToBytesBE 0 128

structure G1CodecLawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop
    extends G1CodecLaws c where
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q
```
Which law is needed where:
- All four headline laws are needed by every conjunct. `verifyMsgs` re-reads `ofCompressed? (toCompressed Q)`, the cursor advances by the width, memory holds raw bytes while `Inv` compares with `toEip`, and the committed instance is absorbed as 128 zero bytes.
- The four extra laws of the full bundle are needed by `EndToEndV3` only: `compressedRoundtrip` (`verifyNative_iff_msgs_codec`, `repack_spec_of_decodeRust`); `ofEip_toEip`, `eipShape`, `eipWidth` (`calldata_roundtrip`).
- That the four are enough is argued, not proved.

Satisfiability:
- The tree proves all seven frozen laws at `g1CodecZ` (`CurveSurface.g1CodecZ_laws`), whose `ofCompressed?` is `fun _ => none`.
- `g1CodecZ_not_headlineLaws` is proved, hence `poseidon_notInhabitedV3`: the repaired gate is red today.
- `withCompressed_lawsV3` is proved: any codec with the seven laws plus an injective 48-byte compress satisfies all eight.
- `lawsV3_satisfiable_at_G1z` is proved with axioms `[propext, Classical.choice, Quot.sound]`: a codec on `G₁z` with `g1CodecZ`'s EIP half satisfies all eight. Its compressed half is an abstract injection, enough for the headline but not for `EndToEndV3`'s link to Rust bytes. The ZCash functions exist on `G1Affine` (Instances/Bls12_381.lean:76, :120), not on `G₁z`.

### (h) HypothesesInhabitedV3

```lean
def HypothesesInhabitedV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W keccak256 vkAddr ∧ EntryFrameV3 R W Lyt keccak256 cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ G1CodecHeadlineLaws R.E.g1 ∧
      LeanAccepts R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd
```
- `returns_of_inhabited` is proved: gate plus headline give an honest run that returns ABI true.
- `soundSide_of_leanAccepts` is proved, so `SoundSide` is not an extra demand.
- `frozenSides_of_not_decodes` is proved: the frozen gate's two side conditions hold at any calldata that does not decode.

Cost at the deployment. This is the most expensive item on the surface, and the tree has no path for it today. It needs:
1. Real VK commitments and `delta` in the Lean environment.
2. Pinned pairing generators.
3. `sG2`: a known-trapdoor test SRS or a named fixture axiom. `DualMSM.check` is a pairing equation over an opaque pairing.
4. A proof that `verifyMsgs .. = .ok ()` for a concrete calldata. `G₁z` and both codec decoders are noncomputable, so this cannot be evaluated; it needs an executable twin of the verifier over a computable carrier plus a transport argument. The only executed `verifyMsgs` in the tree is on the exponent model (Instances/NativeE2E.lean).
5. One tracked accepted (proof, calldata) pair.

I did not size this beyond a probe.

### (i) TwoOutcomes

```lean
def TwoOutcomes (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs),
    RunBody R vkAddr 0 c g st₀ obs →
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)
```
It mentions no `LeanAccepts`, `SoundSide`, snapshot, entry frame or precompile hypothesis. Three syntactic facts give it:
1. `NoWriters` (already a clause).
2. No `stop`, `selfdestruct` or `return` builtin outside the tail.
3. The program ends with `mstore(p, 1)  return(p, 0x20)`, with no `leave` outside a function and no `break`/`continue` outside a loop.

Facts 2 and 3 are the new decidable `ExitDiscipline` (`exitStep`, `exitScan`, `returnTail?`, in the shape of `Bridge.noWritersStep`).
- Witness and five refusals are proved by `decide`.
- At the deployment AST: `(true, true, false)` = tail found, passes at fuel 20000, exhausted at fuel 200.
- In the generator's text the main block has token counts return 1, stop 0, selfdestruct 0, invalid 0.
- `twoOutcomes_of_exitDiscipline` is the stated obligation, generic in the block. `twoOutcomes_of_scans` and `conj3_of_twoOutcomes` are proved from it.
- Falsifier for the lemma it replaces: `rejects_of_not_accepts_contradiction` derives `False` from the tree's `rejects_of_not_accepts` and one accepted calldata with a returning run. It uses only the missing `R.Valid`: the render with `numInstances + 1` has the same program and rejects everything.

### (j) WellFormed

Corrected clause: `vk.permutation.commitments.size = vk.cs.permutation.columns.size`.
- Rust: keygen.rs:244-250 pushes one commitment per column; permutation.rs:123 reads `(0..argument.columns.len())`.
- The tree's own spec layer already states it this way (Halo2/Spec/Degrees.lean, `CircuitIndex.WellFormed.sigmaCountMatches`).
- At the deployment: `(8, 8, 3)` = commitments, columns, frozen right-hand side.
- No proof outside `Instances/` consumes the field.

### The composition (k)

```lean
theorem lowering_equivalenceV3_of (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h2 : TwoOutcomes R) (hrej : RejectsV3 R product) (hcomp : CompleteV3 R product)
    (htot : TotalV3 R product) : LoweringEquivalenceV3 R product   -- PROVED, no sorryAx
```
- Conjunct 1 is `TwoOutcomes` (a returning run returned `abiTrue`) plus `RejectsV3` (and Lean accepted).
- Conjunct 3 is `TwoOutcomes`.
- So the seven `BlockSound` rows are not spent on conjunct 1's return data. All of "the contract returns, so Lean accepts" is `RejectsV3`, which keeps `SoundSide`.

## 3. V3 clause verdicts at today's `poseidonRender`

| clause | verdict | basis |
|---|---|---|
| circuitMeta (`PlanMeta`) | false; true once `plan.meta_` is post-processed | measured |
| layout | false; true once `plan.meta_` is post-processed | measured |
| payload | refuted (`delta`; placeholder commitments); 7 of 8 scalar pins hold | proved / measured |
| exitDiscipline, noShadow, cdBound | true | measured |
| supported | expected to flip to proved: its one refuted field is the repaired one (8 = 8) | not re-proved here |
| invariants, codegen, model | unchanged (refuted, refuted, sorry) | other areas |

The other seven clauses are unchanged and proved.

## 4. Guidance and pitfalls for the implementer

- Never let `simp` see `List.replicate (2 ^ 256) _`: its simproc unfolds it and the check ran past 300 s before I killed it. Use `rw [List.length_append, List.length_replicate]`.
- Prop structures at different renders are not definitionally equal even when every field is. Transfer field by field (`deployment_bump`, `entryFrame_bump`).
- `Op` is ambiguous between `EVM.Op` and `Lowering.Op` when both namespaces are open.
- `topBinders` lives in the refinable `ProgramLemmas.lean` and `Render.slices` in the refinable `Blocks.lean`. Both must move into the frozen files before `noShadow` and the scope can be stated there.
- `lean -o` on a file outside `formal/` needs `--root=<dir>`.
- `exitDisciplineFuel` needs more than 200 fuel at the deployment, so it is a `native_decide` fact in `Instances/`, like `noWriters`.
- Land the falsifiers before the cut-over: F9 cites `rejects_of_not_accepts`, which the cut-over deletes. At cut-over, restate F2 and F9 over verbatim Prop copies of the old text.

Verification of these results remains with the reader: please review them for accuracy and completeness before relying on them.
