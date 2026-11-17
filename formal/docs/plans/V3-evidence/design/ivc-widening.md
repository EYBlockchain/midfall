# Widening the supported class of `lowering_correct` to the IVC verifier: statement design

> **After review (2026-11-17).** The Lean files were repaired: `lowering_correctW` carries `hQ : isExternal R → EvalContracts R Q` and lives in `WideningStages.lean` (it was false for an arbitrary evaluator object); `StageInvW`/`AgreeW` read an accumulator-carrying snapshot, because V3's `StageInv` is unsatisfiable after `.start` in accumulator mode (`stageInv_false_of_acc`). Line numbers below are the first draft's. Where this memo differs, the Lean files are right.


Status: PROPOSAL. Nothing here is landed, signed or imported by the build.
Lean sources of the built tree: commit `c22b51a`. HEAD moved twice during the session
(`f8f461e`, `cf00592`); both commits touch `docs/` and one evidence file, no file under
`formal/Midfall` (`git diff --stat c22b51a HEAD -- formal/Midfall` is empty), so the oleans the
checks ran against are those of the sources read.

**Scope of this memo, after the owner's change of aim (D-P71).** The deliverable is no longer a
second fixture headline. It is the widening of the supported class so that the one generic
theorem covers renders in accumulator mode with an external, pinned quotient evaluator, which is
the class of the IVC decider verifier. Every statement below is for every render `R`. The IVC
circuit appears only as a test (§7). The files kept their first names.

| file | content | status |
|---|---|---|
| `f2/lean/statements/WideningV3.lean` | scope, reference, evaluator slot, widened headline, validity, target | typechecks; 2 `sorry` (`lowering_correctW`, `model_quotientMode`) |
| `f2/lean/statements/WideningStages.lean` | staged invariants and the widened row families | typechecks; 2 `sorry` (`instWords_of_decoded`, `batchedCheck_iff_contract`) |
| `f2/lean/statements/WideningTests.lean` | tests: five `#eval`, all print `true` | typechecks; 0 `sorry` |
| `f2/lean/statements/AxiomProbe.lean` | `#print axioms` of the v1 accumulator lemmas | typechecks |
| `f2/check.sh` | the compile mechanism of `V3-evidence/check.sh`, copied | `deps` then `f2` |

Reproduce: `bash f2/check.sh deps && bash f2/check.sh f2` (about 60 s in all; refuses to run
unless the build log ends with `EXIT 0`).

Evidence classes used below: **MEASURED** (a command printed it), **READ** (file:line),
**INFERRED** (my reasoning; not checked). Paths starting `sol:` are
`proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol`, `ev:` the
`Halo2QuotientEvaluator.sol` beside it, `test:` is
`proofs/solidity-verifier/tests/ivc_keccak_solidity.rs`.

---

## 1. Conclusions, in order of weight

1. **The widening costs no second theorem.** `LoweringEquivalenceW R Q product` is the V3 text
   with four substitutions, and for a render with no accumulator and an embedded quotient it is
   *equivalent* to `LoweringEquivalenceV3 R product` (`equivalenceW_iff_V3`, proved, standard
   three axioms). `lowering_correct_of_W` (proved from the target and one generator fact) shows
   D-P71's `lowering_correct` is the instance of the widened target at V3's class.
2. **No new block and no new checkpoint.** The three additions sit inside existing template
   partials: accumulator validation in `VkLoading.yul:115-137`, the evaluator call in
   `QuotientAndLinearization.yul:35`, the alpha batching in `FinalPairing.yul` (READ, `grep` in
   `proofs/solidity-verifier/templates`). Three of the seven rows change; one row is new and is
   not a slice of the verifier: the evaluator's fallback body.
3. **The evaluator's numerator is the object V3's quotient row is already about.** The evaluator
   contract is `quotientHelpers ++ quotientNumeratorBlock` between a `calldatacopy` and a
   `return` (READ `Generator/Contracts.lean:492`); the embedded Poseidon verifier contains the
   same interpreter with the same opcode family (READ: ten `case 0x..` arms in
   `poseidon-fixture-dump/Halo2Verifier.sol:1877-1886`; eleven in `ev:430-440`). The widening
   adds a wrapper, a frame transport and one opcode arm (`0x21 modarith7`), not a second
   numerator proof. It does make that proof mandatory in a form that does not depend on where
   the block runs.
4. **The right-hand side in accumulator mode is the contract's own check, `LeanAcceptsAcc`.** It
   is exactly implied by "Rust PLONK accept and the accumulator's own pairing check"
   (`leanAcceptsAcc_of_rust`, proved); the converse holds up to one bad `alpha`
   (`rust_or_collision_of_leanAcceptsAcc` and `alpha_atMostOne`, proved). It is not an iff with
   any Rust function, and `IvcVerifier::verify_final` is not what the e2e test checks.
5. **The evaluator is trusted through one named structure, `EvaluatorTrust`**, keyed on the pin
   the verifier itself tests. The pin is real: the tracked evaluator source compiles under the
   pinned solc to exactly the pinned length and hash (MEASURED, §5.4).
6. **The generator accepts one limb shape only (7 × 56).** The class restriction is therefore
   "no fixed-base tail", plus a recommended restriction to the point-and-scalar kind because
   only it has a circuit and an artifact.
7. **The repository has no proof or calldata for the tracked IVC contracts** (§7.1). A test
   bundle must be regenerated whatever is decided about the SRS.

---

## 2. Scope: what replaces `noAcc` and `embeddedQuotient`

`SupportedV3` (`StatementsV3.lean:592`) has twelve clauses. Ten do not mention the accumulator or
the quotient mode; they become `SupportedCore`, verbatim (`supportedV3_iff_core`, proved).

```lean
structure AccShape (R) (enc : Generator.AccumulatorEncoding) : Prop where
  cfg     : R.cfg.accumulator = some enc
  noTail  : (toExec enc).fixedScalarCount R.cfg.numInstances = some 0
  noFixed : R.model.accFixedBases = []
def ExternalPinned (R) : Prop :=
  R.flags.externalQuotient = true ∧ ∃ len hash, R.flags.expectedQuotient = some (len, hash)
structure SupportedW (R) : Prop where
  core     : SupportedCore R
  acc      : R.cfg.accumulator = none ∨ ∃ enc, AccShape R enc
  accKind  : ∀ enc, R.cfg.accumulator = some enc → enc.kind = .pointAndScalar   -- decision W-2
  quotient : (R.flags.externalQuotient = false ∧ R.flags.expectedQuotient = none) ∨ ExternalPinned R
theorem supportedV3_iff_W :                                                     -- PROVED
  SupportedV3 R ↔ SupportedW R ∧ R.cfg.accumulator = none ∧ (… = false ∧ … = none)
theorem acc_not_supportedV3 : R.cfg.accumulator = some enc → ¬ SupportedV3 R    -- PROVED
```

In words: the class has two independent axes. The accumulator is absent, or present in a shape
that fills the instance array to its end. The quotient is embedded, or external with a pinned
runtime. V3's class is one of the four corners; the IVC decider is the opposite corner.

### 2.1 Which accumulator encodings are covered, and why

| encoding | generator accepts | covered | reason |
|---|---|---|---|
| limb shape other than 7 × 56 | no (READ `proofs/solidity-verifier/src/api.rs:147-148`; port `Exec/Accumulator.lean:234-247`) | n/a | not a restriction of the class: `fixedScalarCount` is `none` there (MEASURED, `noTail_refuses`) |
| point-and-scalar, no tail (12 words) | yes | **yes** | the IVC decider: `offset 4 + 12 = 16` (READ sol:1311, :1314; test:1125-1129) |
| point-pair, no tail (10 words) | yes | admitted by `noTail`, **left out by `accKind`** | `decodeAcc` and `accFinalCheck` already treat it; but no circuit, no tracked artifact and no e2e test exist for it, so rule W12 cannot be met (READ: `point_pair(` occurs only in `src/api.rs` and `src/lowering/tests.rs`). The untracked `moonlight-wrap-solidity-dump` is a point-pair render from superseded templates (READ its `Halo2Verifier.sol:1138`, `let lhs_scalar := 1`) and is not usable |
| point-and-scalar with a fixed-base tail | yes | **no** | needs the fixed-base table as a function of the render; the only table in the tree, `Midfall.Halo2.fixedBases`, is reported to have the identity for `-G` (READ `Lowering/Accumulator.lean:57-59`, a lead, not re-measured); the Yul for the tail is unrolled per base; no artifact |

With `noTail` the fixed-base table is empty (`accTable`, `accBases` are `#[]`), so nothing in the
widened cone reaches `fixedBases`.

### 2.2 Clause table against the IVC artifact

| clause | at the IVC artifact | class |
|---|---|---|
| `instShape` (2 instance columns, 1 committed) | `GeneratorConfig::new(num_instances, 1)` | READ test:1125; column count unmeasured |
| `singlePhase` | `THETA_MPTR = CHALLENGE_MPTR = 0x7900`: no user challenge slot | READ sol:140-144 |
| `production` (no trace, no gas checkpoints) | 0 occurrences of `trace_u256`, `log1(`, `gas_checkpoint` in both contracts | MEASURED (`grep -c`) |
| `separateVk` | `AUTHORIZED_VK`, `extcodecopy(vk, VK_MPTR, 1, …)` | READ sol:89, :1304 |
| `acc` / `AccShape` | `HAS_ACCUMULATOR = 1`, offset 4, 7 limbs, 56 bits, 16 instances; both sides carry a scalar; `acc_msm_len` is one pair | READ sol:1311-1316, :1176, :1218, :1233 |
| `quotient` / `ExternalPinned` | `EXPECTED_QUOTIENT_LENGTH = 9656`, codehash `0x4a17…e575` | READ sol:99-100; MEASURED against solc (§5.4) |
| `advice`, `noRotInst`, `hLimbs`, `vkPoints`, `layout`, `wf` | need the key's `cs` and the ported plan | **unmeasured** (card GEN.2) |
| features | `Features.solidity` is `truncatedChallenges := true, outerFewerPointSets := false, outerSingleHCommitment := false` (READ `Exec/Features.lean:30-34`); the dump masks `x3` to 128 bits (READ sol:1652); the bench string is `evm,truncated-challenges,in-circuit-fewer-point-sets` | consistent, READ; `outerFewerPointSets = false` for this dump is INFERRED from test:1038-1056 |

---

## 3. The reference in accumulator mode

### 3.1 What Rust checks (READ)

- `test:1085-1092`: `midnight_zk_stdlib::verify::<IvcTreeDeciderCircuit, Keccak256>(decider_srs
  .verifier_params(), …)`: the ordinary PLONK verifier on the decider proof, with its own pairing
  check.
- `test:1021-1024`: `decider_instance.final_acc.check(&ivc_srs.verifier_params(),
  &no_fixed_bases)`: the carried accumulator's own pairing check.
- `IvcVerifier::verify_final` (`aggregation/src/ivc/verifier.rs:111-151`) is **not called** by
  the test (MEASURED: `grep -n verify_final tests/ivc_keccak_solidity.rs` is empty). It is a
  third check: it folds the proof's accumulator with the instance's by
  `Accumulator::accumulate`, whose scalar is a Poseidon sponge hash of the two accumulators'
  public inputs, truncated (`circuits/src/verifier/accumulator.rs:223-239`), then does one
  pairing check. It is about a proof of the IVC *step* circuit; the on-chain contract verifies
  the *decider* circuit.

So in accumulator mode the contract is not a port of one Rust function. The contract batches
with `alpha = keccak(tag ‖ vk_digest ‖ kzg_rhs ‖ kzg_lhs ‖ acc_rhs ‖ acc_lhs) mod r`, zero
replaced by one (READ sol:2516-2531); Rust never computes that scalar.

### 3.2 The statements

```lean
def accFinalCheck (R) (H) (instW : Array Word256) (d : DualMSM (Fr p) G₁ G₂ Gₜ) : Bool :=
  match R.cfg.accumulator with
  | none => DualMSM.check d R.params
  | some enc =>
    match decodeAcc (toExec enc) R.E.g1 accTable instW with
    | none => false
    | some a => batchedCheck R.params
        (alphaOf H (vkDigestWordOf R) R.E.g1 d.left.eval d.right.eval
          (a.fullyCollapse accBases).1 (a.fullyCollapse accBases).2) d a accBases
def LeanAcceptsAcc (R) (H) (cd) : Prop :=
  ∃ ms instW inst, decodeCalldata … cd = some (ms, instW) ∧ instOfWords? instW = some inst ∧
    ∃ d, prepareMsgs R.E H Features.solidity R.vk inst ms = .ok d ∧ accFinalCheck R H instW d = true
def RustAcceptsBoth (R) (H) (cd) : Prop :=          -- the two test assertions of §3.1
  ∃ ms instW inst enc a, decode ∧ instOfWords ∧ verifyMsgs … = .ok () ∧
    R.cfg.accumulator = some enc ∧ decodeAcc … instW = some a ∧ KzgAcc.check a R.params accBases = true
def AlphaCollision (R) (H) (cd) : Prop :=           -- accepted although one equation fails
  ∃ … d a, … ∧ (DualMSM.check d R.params = false ∨ KzgAcc.check a R.params accBases = false) ∧
    batchedCheck R.params (alphaOf …) d a accBases = true

theorem leanAcceptsAcc_iff_noAcc    : R.cfg.accumulator = none → (LeanAcceptsAcc R H cd ↔ LeanAccepts R H cd)
theorem leanAcceptsAcc_of_rust      : PrepWf R H → RustAcceptsBoth R H cd → LeanAcceptsAcc R H cd
theorem rust_or_collision_of_leanAcceptsAcc :
    R.cfg.accumulator = some enc → LeanAcceptsAcc R H cd → RustAcceptsBoth R H cd ∨ AlphaCollision R H cd
theorem alpha_atMostOne : (one of the two checks fails) →
    batchedCheck R.params α d a accBases = true → batchedCheck R.params β d a accBases = true → α = β
```

All four theorems are proved; `#print axioms` gives the standard three (MEASURED). The first
rests on `verifyMsgs_ok_iff` (proved here); the second on v1's `batched_complete`; the last is
v1's `batched_atMostOneRoot`.

In words. `LeanAcceptsAcc` reads the accumulator from the **raw** instance words, so a carried
scalar or a packed limb word that is out of range is a rejection, as in the contract.
(a) *Exact direction*: if Rust accepts the proof and the accumulator passes its own check, the
reference accepts, for every hash, hence for every `alpha`. (b) *Converse*: if the reference
accepts, then Rust accepts both, or the keccak output is a root of the batched equation at four
points for which that equation is not identically true; for fixed points there is at most one
such scalar among the `r` possible. That is a soundness-error statement of Schwartz–Zippel kind.
Turning it into a probability needs keccak modelled as a random oracle over the four points and
the digest, which is **not** formalised and should not be claimed.

### 3.3 What the widened headline does and does not say about Rust

It says: the generated contract returns `true` iff `LeanAcceptsAcc` (up to the two V3 side
conditions). By the two corollaries (`returns_of_rustAcceptsBoth`,
`rust_or_collision_of_returns`, both proved from the headline):

- if the Rust PLONK verifier accepts the decider proof and `Accumulator::check` accepts the
  carried accumulator, the contract returns `true`;
- if the contract returns `true`, then both Rust checks pass, or `AlphaCollision` holds.

It does **not** say: that the contract is equivalent to `verify_final` or to any Rust function;
that the accumulator *is* the one the IVC leaves produced (that is the decider circuit's
statement, proved by the PLONK proof, not by the contract); that `AlphaCollision` has negligible
probability; that the two SRS files have the same `[τ]₂`.

**One SRS, two in Rust.** The test checks the accumulator under `ivc_srs.verifier_params()`
(k = 19) and the proof under `decider_srs.verifier_params()` (k = 20). The contract has one
`NEG_S_G2_BASE`. `RustAcceptsBoth` is stated under the one `R.params`. The test does not assert
the two `s_g2` are equal (MEASURED: no `s_g2` in the test file). The two local SRS files end
with the same 384 bytes (MEASURED, sha256 of the tails; that these bytes are `g2 ‖ s_g2` is
INFERRED from the serialisation order).

### 3.4 The v1 statements, re-measured (`AxiomProbe.lean`)

| declaration (`Lowering/`) | line | finding |
|---|---|---|
| `batched_complete`, `batched_atMostOneRoot`, `contractRef_acc_complete`, `dualMsm_check_iff_contract`, `decodeAcc_encode` | `Accumulator.lean:1245, :1260, :1497, :1320, :544` | **proved**, standard three axioms (MEASURED). Their docstrings still say "PROOF OBLIGATION, registered in SORRY.md": stale |
| `decodeAcc_injective`, `decodeAcc_encode_pointPair` | `:134` (sorry `:142`), `:936` (sorry `:955`) | `sorryAx` (MEASURED). Neither is needed by the widened surface |
| `toExec_fullyCollapsed`, `toExec_validFor`, `toExec_fixedScalarCount` | `AccEncoding.lean:191, :251, :303` | `sorryAx` (MEASURED). Avoided: `AccShape.noTail` is stated on the Exec encoding `toExec enc` directly |
| `ContractRefAcceptsAcc` | `Accumulator.lean:1430` | `vkDigest` and `fb` are free parameters, tied to nothing; it uses v1's copy of `instOfWords?`. Superseded by `LeanAcceptsAcc`, which takes both from the render |
| `Inv`, `.pairing` clause | `Inv.lean:818` | `PV.hasAccumulator == true ∨ DualMSM.check …`: in accumulator mode the clause asserts **nothing**. The acc slots are pinned nowhere (`Inv.lean:754`: only `S.acc.isSome`). Repaired by `leanStageW`, `AccInv`, `BatchedInv` (§8) |
| `Evaluator.rel_worldLocal` | `Yul/Bridge.lean:1006` (sorry `:1009`) | `sorryAx`; its own docstring argues it is false. See §5.3 |

---

## 4. The headline, the world, validity

```lean
structure WorldW (R) (Q : EvalObject) (product) (W Lyt H vkAddr qAddr cd st₀ evalRel) : Prop where
  dep   : DeploymentV2 R W H vkAddr                      -- V3
  entry : EntryFrameV3 R W Lyt H cd st₀                  -- V3
  pc    : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product         -- V3
  codec : G1CodecHeadlineLaws R.E.g1                     -- V3
  evaluator : isExternal R → QPinnedEnv R W qAddr ∧ accountKey qAddr ∉ [0x0b,0x0c,0x0f,0x05] ∧
              EvaluatorTrust R Q W Lyt qAddr evalRel     -- vacuous when embedded
  idLaw : R.cfg.accumulator.isSome = true → R.E.g1.ofEip? (R.E.g1.toEip 1) = some 1   -- vacuous without acc
def callsW (R) (product) (qAddr) (evalRel) : ExternalCalls :=
  if isExternal R then honestCalls product qAddr evalRel else callsOf product
def LoweringEquivalenceW (R) (Q) (product) : Prop :=
  ∀ W Lyt H vkAddr qAddr cd st₀ evalRel, WorldW R Q product W Lyt H vkAddr qAddr cd st₀ evalRel →
    (∀ g obs, RunBody R vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g st₀ obs →
        obs.isReturn → SoundSide R H cd → obs.returnData = abiTrue ∧ LeanAcceptsAcc R H cd) ∧
    (LeanAcceptsAcc R H cd → CompleteSide R H cd →
        (∃ obs, RunBody … (callsW …) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody … (callsW …) (ExternalGas.ofFun fun _ => 0) st₀ obs → obs.view = returnView st₀) ∧
    (∀ g obs, RunBody … (permissive (callsW …)) g st₀ obs →
        obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)) ∧
    (∀ g, GasTotal g → ∃ obs, RunBody R vkAddr qAddr (callsW R product qAddr evalRel) g st₀ obs)

theorem lowering_equivalenceW_of : TwoOutcomesW R → RejectsW R Q product → CompleteW R Q product →
    TotalW R Q product → LoweringEquivalenceW R Q product                          -- PROVED
theorem twoOutcomesW_of_scans : NoWriters (R.prog 0 0) → ExitDiscipline (R.prog 0 0) → TwoOutcomesW R
                                                    -- PROVED from V3's two scan obligations
theorem equivalenceW_iff_V3 : R.cfg.accumulator = none → R.model.quotientExternal = none →
    (LoweringEquivalenceW R Q product ↔ LoweringEquivalenceV3 R product)           -- PROVED

structure ValidW (R) (Q) : Prop where
  core : ValidCore R                -- ValidV3 minus `supported`, verbatim (validV3_iff_core, PROVED)
  supported : SupportedW R
  evaluator : isExternal R → EvalPins R Q
theorem lowering_correctW (hR : ValidW R Q) : LoweringEquivalenceW R Q product     -- THE TARGET (sorry)
theorem lowering_correct_of_W (hR : ValidV3 R) : LoweringEquivalenceV3 R product   -- PROVED from the target
```

What is reused unchanged from V3: `RunBody` (it already takes `qAddr`), `SoundSide`,
`CompleteSide`, `EntryFrameV3`, `DeploymentV2`, `G1CodecHeadlineLaws`, `GasTotal`, `returnView`,
`ExitDiscipline`, `NoWriters`, and every clause of `ValidV3` but one.

What changes, and why each change is forced:

- **`qAddr` is a variable.** V3 fixes it to 0. `TwoOutcomesW` and `scans_prog_addr_indep` are
  already stated for every `qAddr`; `prog_qAddr_irrel` (proved) shows the address does not occur
  in an embedded-quotient program.
- **`callsW`.** V3's `callsOf` has no evaluator slot. The slot is switched on by the *model*
  (`R.model.quotientExternal.isSome`), because that is what decides whether the program binds
  `quotientEvaluator` (`Program.lean:107`). The scope clause is about the *flag*; the link is
  the one generator fact `model_quotientMode` (obligation, `Artifacts.lean:534-537`).
- **`idLaw`.** `decodeAcc` turns an identity-flagged point into 128 zero bytes and asks the codec
  for the element (`Exec/Accumulator.lean:1033`); the contract sends the same bytes through
  G1MSM. `G1CodecHeadlineLaws` has only the decoder-first law, so a codec may reject the zero
  encoding, and the reference would then reject every identity-flagged accumulator the contract
  accepts. INFERRED necessity; the falsifier (a codec with `ofEip? := fun _ => none`) is not
  built because no lawful toy codec exists in the tree yet (REF.4 lands `g1CodecC`).
- **Conjunct 2's gas oracle stays the zero oracle**, so that V3's class gives back the V3 text.
  An external render executes `gas()` (sol:1817); with the zero oracle the model forwards a gas
  word of 0 and the slot ignores it (`evalModel_gas_irrel`, proved). `CompleteAnyGasW` is the
  stronger form for every total oracle; it implies `CompleteW` (proved). Decision W-5.

`EvalPins` (three computations): the verifier's two pin constants are the flags' pair with
`0 < len < 2^256`; the evaluator's output window is the verifier's return window
(`QUOTIENT_RETURN_MPTR = QUOTIENT_OUTPUT_MPTR = 0x1000`, READ sol:213, ev:94); the evaluator body
is closed.

---

## 5. The evaluator call

### 5.1 Object, model, trust

```lean
structure EvalObject where body : YulBlock; outMptr : Nat
structure EvalEntry (Q) (W) (Lyt) (qAddr) (st) (req) (stC : EvmState) : Prop where
  shape : ∃ mem₀ aw, stC = { Evaluator.calleeState W Lyt qAddr st req with memory := mem₀, activeWords := aw }
  zeroAbove : ZeroAbove stC.memory
  fmp : (loadWord stC.memory 0x40).toNat ≤ Q.outMptr
def evalModel (Q) (W) (Lyt) (qAddr) : CallRequest → EvmState → CallResponse → Prop :=
  fun req st resp => ∃ stC V' st' o, EvalEntry Q W Lyt qAddr st req stC ∧
    YulSemantics.Run EVM.evm Q.body stC V' st' o ∧
    resp = Evaluator.responseOf st (committedState stC st')
def QPinned (R) (st) (qAddr) : Prop := ∃ len hash, R.flags.expectedQuotient = some (len, hash) ∧
    BitVec.ofNat 256 (st.env.extCodeOf qAddr).length = BitVec.ofNat 256 len ∧
    projectedCodeHash st.env st.env.balanceOf qAddr = hash
structure EvaluatorTrust (R) (Q) (W) (Lyt) (qAddr) (evalRel) : Prop where     -- TRUSTED
  spec  : ∀ req st resp, req.kind = .staticcall → QPinned R st qAddr →
            (evalRel req st resp ↔ evalModel Q W Lyt qAddr req st resp)
  quiet : ∀ req st resp, evalRel req st resp → resp.world = CallWorld.ofState st
```

In words. The **object** is the assembly block of the evaluator's fallback as the Lean generator
emits it, run in the closed dialect. `EvalEntry` is the analogue of `EntryFrame` for the callee:
the frame `Evaluator.calleeState` builds, except that memory is some `mem₀`, zero from `0x80`,
with a free-memory pointer not above the generated layout. `EvaluatorTrust` is the analogue of
the trust in solc for the verifier: *whenever the code at the address passes the pin the
verifier tests, the chain's answers to a STATICCALL there are exactly the runs of the generated
body from an entry frame; and a call there never reports a world change.* The clause bundles
three real-world facts: solc compiles the generated source to the bytes with the pinned hash;
those bytes implement the Yul; no other code has that hash under keccak.

Why keyed on `QPinned`: the verifier's guard (sol:1808-1811) establishes exactly this
proposition in the current state immediately before the call, so the soundness rows need no
deployment fact to use `spec`. The completeness and totality rows need the pin to *pass*, which
is `WorldW.evaluator`'s `QPinnedEnv R W qAddr`.

Witnesses and falsifiers (all proved): `evaluatorTrust_model` (the assumption is satisfiable, by
the model itself); `evalModel_of_rel` (v1's all-zero-memory slot is contained in the model);
`evalModel_quiet`; `callsW_le_permissive` (an honest response is a permissive one; this is what
`quiet` buys and fails without it); `evalRel_answers` (with body totality, the chain answers).

### 5.2 Failure paths: totality and "two outcomes" still hold

| path | where | outcome | covered by |
|---|---|---|---|
| size or hash mismatch | sol:1808-1811 | `fail(ERR_VK_MISMATCH)`, revert | no call is made; conjunct 3 by the exit scan, for **any** call relation |
| call fails | sol:1817 | `fail(ERR_QUOTIENT_PROGRAM_INVALID)` | `permissive` admits a failed response to every request |
| wrong return size, wrong magic | sol:1818-1819 | `fail(…)` | dead on honest paths if `EvalBodyShape` holds; reachable only under an evaluator outside `EvaluatorTrust` |
| `gas()` | sol:1817 | stuck under `ExternalGas.none`; any word under a total oracle | conjunct 4 asks `GasTotal g`; conjuncts 1 and 3 are for-all-runs |

Conjunct 3 needs no evaluator fact: `TwoOutcomesW` is proved from the same two scans for every
call relation. Conjunct 4 needs one: `EvalBodyTotal` (§8.4), because `spec` turns a run of the
body into an answer; without it the honest relation could have no answer at the address.

**Gas.** `ExternalGas` supplies the word `gas()` returns; `externalCall` puts it in
`req.gas` (`EVMExec.lean:889-899`). Neither the precompile relations (`Externals.lean:799`,
`respond` does not read `gas`) nor `evalModel` (`evalModel_gas_irrel`) reads it. So a run's
outcome does not depend on the oracle. V3's totality argument uses "the program executes no
`gas()`" (PLAN-V3 §5 M3); at an external render that premise is false and is replaced by "the
only use of `gas()` is the gas argument of a call whose relation ignores it", a syntactic scan
plus the two facts above.

### 5.3 What replaces the false world-locality lemma

Nothing has to. `ExternalCalls.WorldLocal` is consumed only by v1's `ir_refines` route
(MEASURED: `grep -rn WorldLocal` finds uses in `Lowering/Obligations.lean`,
`Lowering/Partials.lean`, `Lowering/LegacyVacuity.lean`, `Instances/RunShellInhabited.lean`; none
in `LoweringV2/` or `V3-evidence/`). The V2/V3 surface has no solc refinement step, so it needs
three properties of the slot instead, each of which is true and proved here: `quiet`,
gas-insensitivity, and (through `spec`) "an answer is a run of the body".

Recommendation: delete `Evaluator.rel_worldLocal` with the v1 track (X6) rather than repair it.
Its docstring claims the evaluator reads the hash oracle ("the transcript is its whole job",
`Bridge.lean:1004-1005`); the artifact contradicts that: the evaluator body contains no
`keccak256`, `caller`, `address`, `sload`, `staticcall` or `gas` (MEASURED: `grep` on `ev` finds
`keccak256` in one comment only). For such a body a stronger and true locality holds, namely
that the answer depends on `req.input` alone. It is not needed by the headline and is not stated.

### 5.4 The pin is solc's output on the tracked source (MEASURED)

`solc 0.8.30+commit.73712a01 --bin-runtime --optimize --optimize-runs 1 --via-ir --evm-version
cancun --no-cbor-metadata` on the tracked `Halo2QuotientEvaluator.sol` (the flags of
`src/evm.rs:197-213`) gives a runtime of **9656 bytes** with keccak
**`0x4a179319…64cee575`**: the two constants at sol:99-100. Output kept in `f2/solc/`.

The same runtime opens with `61 08c0 60 40 52`: `PUSH2 0x08c0 PUSH1 0x40 MSTORE`. So the callee's
real entry memory has the free-memory pointer `0x8c0`, not zero, and solc owns `[0x80, 0x8c0)`
for stack spills. v1's `Evaluator.calleeState` starts from all-zero memory; `EvalEntry` does not.
**The evaluator's fallback has no guard of the MF-2 kind** (READ ev:109-119; the verifier has
one, sol:641-644), so `EvalEntry.fmp` (`0x8c0 ≤ 0x1000` here) is trusted with no on-chain check.

---

## 6. The evaluator program: what it is

READ from `ev` and from the embedded Poseidon verifier:

- An **interpreter loop** over a byte program stored in the key's payload: `q_pc` runs from
  `q_program_mptr` (`0x50a0`) to `q_end` (`+ 0x11cf`), `switch byte(0, mload(q_pc))`
  (ev:271, :416-456). The loop's guard and its dispatch read memory.
- Eleven opcode arms, rendered from the program's `op_usage` (ev:426-440): seven generic stack
  opcodes; `0x21 modarith7`, a limb-aware opcode with nested loops whose inner bounds are the
  literal 7 and whose outer counts are read from the program (ev:526-690); three native
  callbacks: `0x19` permutation and `0x1f` lookup (loops with circuit-dependent literal bounds,
  ev:692-998) and `0x1b native_identity`, a `switch` over four generated straight-line identity
  bodies (ev:999-1288, 170 `mulmod`/`addmod`).
- A structured post-loop suffix for the trash constraints (ev:1342-).
- Totals: 27 `for`, 4 `switch`, 296 `mulmod`, 252 `addmod`, 2 helper functions, no call, no
  `keccak256` (MEASURED by `grep -c`).

The embedded Poseidon numerator has the same shape with ten of the eleven arms (no `0x21`). So
the evaluator is **an interpreter loop with generated native arms**, not a pure straight-line
program and not a pure interpreter. Consequences for a proof for every `R`:

1. the interpreter loop needs an invariant with a symbolic bound (the program length) and a
   guard that reads memory: D-P71's "route B", unchanged by the widening;
2. the set of arms depends on the render, so each opcode arm is proved once, for every program
   that may contain it; `0x21` occurs in no V3-class test circuit known to me, so its arm is
   covered by no test until an IVC-class circuit is one (W14);
3. the native arms are generated per circuit: their correctness is an induction over what the
   emitter prints for an expression (`Generator/Quotient/Evaluator.lean`), a fourth proof class
   beside the three the coordinator named.

---

## 7. Tests: what the IVC circuit must supply

D-P71 keeps circuits as tests. For the widened class to meet W12 and W14 at its new corner, one
circuit of that corner must give: `ValidW` by computation; `HypothesesInhabitedW` with
`AccNontrivial`; the run-it gate (the modelled program, with the evaluator slot answered by
running the generated evaluator body, returns `abiTrue` on the calldata and reverts on the
mutants); the reference gate; byte equality of three contracts.

### 7.1 Finding: the tracked contracts have no proof

The three `.sol` files are tracked (`git ls-files`); `proof.bin`, `calldata.bin`, `instance.le`,
`contract-sizes.txt` and the `.creation.bin` files beside them are untracked leftovers of a
bench run of 2026-10-07 (MEASURED: `stat`, `git ls-files`). They do not belong to the tracked
contracts: `contract-sizes.txt` records an evaluator runtime of 9531 bytes and a key-contract
hash `0x9b94…b2b7`; the tracked verifier pins 9656 bytes and `0xd2ae…836a` (READ). The calldata
has the right shape (16 instance words at `0x1ee4`, length `0x20e4`; MEASURED) but is a proof
for another key. `formal/BASELINE.md:455-471` already classes these files as "not pins".

So no accepted calldata exists in the repository for the tracked IVC contracts, under any SRS.

### 7.2 Can a production-SRS render serve as the test?

| test | production SRS (Midnight) | test SRS (seeded `unsafe_setup`) |
|---|---|---|
| `ValidW` clause table | yes, except `PayloadAgrees.negSG2` | yes, all clauses |
| byte equality of the three contracts | yes | yes |
| reference gate: Lean reproduces Rust's MSM and the two accumulator points (trace ids 29, 30, `circuits/src/verifier/accumulator.rs:164-169`) | yes | yes |
| `PairingInputsAgree`: the reference's two batched points equal the two G1 slots of the EVM's `0x0f` call (the test already traces precompile calls, test:1414-1420) | yes | yes |
| `HypothesesInhabitedW` (`LeanAcceptsAcc` on a real calldata) | **no**: the batched check is `s • (L + αA_L) = R + αA_R` in the constructed pairing and needs `s` | yes, a computation |
| mutants: Lean verdict = EVM verdict | only for mutants rejected before the pairing | yes, including "valid outer proof, bad inner opening" (test:1355-1440), which fails *at* the pairing |

**Recommendation: regenerate under a test SRS; keep the production render for the artifact gate
only.** The reasons are D-P63's, and one more: the most informative mutant of the e2e test is
rejected at the final pairing, and only a known trapdoor lets Lean give that verdict.

What the regeneration needs (READ `proofs/src/poly/kzg/params.rs:44, :98-135`; test:912, :984,
:1030): the test takes `ParamsKZG` values, so `load_srs(SrsSource::Midnight, …)` is replaced at
three sites. **The two SRS must share one trapdoor**: draw one `unsafe_setup(20, seeded)` and
`downsize(19)` a clone for the IVC circuit. Two independent setups would make the honest proof
fail at the batched pairing, because the contract has one `NEG_S_G2_BASE` (INFERRED from §3.3).
The trapdoor is the first `Fr::random` of the seeded generator and is exported as for F1.

What changes in the artifacts (INFERRED, not measured): `Halo2VerifyingKey.sol` (the
`−s·G₂` slot, every fixed and permutation commitment, the digest) and two constants of
`Halo2Verifier.sol` (`EXPECTED_VK_CODEHASH_WORD`, `BUILD_ID`). `Halo2QuotientEvaluator.sol`
should not change: it contains layout constants and identity code, no key data, so the pinned
pair should stay `(9656, 0x4a17…)`; this is checkable in one solc run.

### 7.3 Tests that are already computations (`WideningTests.lean`, all `true`)

On the sixteen instance words of the local `instance.le` (a Rust-made public input; codec data
only): the ported limb decoder accepts both points, they are non-identity, the rebuilt
coordinates equal those computed independently in Python from the layout read in sol:980-1072,
both are on `y² = x³ + 4`, both carried scalars are 1 (`decoder_accepts`). Falsifiers
(`decoder_refuses`): flag 2 is rejected; flag 1 decodes to 128 zero bytes whatever the
coordinates; an unused high bit is rejected; raw zero words with flag 0 decode to `(1,1)`, which
is off the curve (so the precompile, not the decoder, rejects, as the test comment at
test:946-948 says); the encoded coordinate 0 with flag 0 is rejected by the decoder.
Scope: `noTail_ok`, `noTail_refuses`, `pointPair_noTail`.

---

## 8. Stages (for every `R`)

No new `Partial`, no new `Checkpoint`. `StageInvW` is V3's `StageInv` with three changes.

```lean
def instWordsRaw (R) (cd) : Array Word256 := -- calldataload at proofEnd + 32 + 32·i, no proof decoding
def AccInv (R) (cd) (st) : Prop := ∀ enc, R.cfg.accumulator = some enc →
  ∃ a, decodeAcc (toExec enc) R.E.g1 accTable (instWordsRaw R cd) = some a ∧
    bytesAt st (ptrAddr R.pv.memory.accLhsMptr) 128 = R.E.g1.toEip (a.fullyCollapse accBases).1 ∧
    bytesAt st (ptrAddr R.pv.memory.accRhsMptr) 128 = R.E.g1.toEip (a.fullyCollapse accBases).2
def leanStageW (R) (H) (instW) (inst) (ms) : Checkpoint → Except Fault (Snapshot …)
  | .pairing => do let S ← snapshotOf R.E H R.vk inst ms none
                   if accFinalCheck R H instW S.c.dual then pure S else throw (Fault.error Error.opening)
  | k => leanStage R H inst ms k
def StageInvW (R) (H) (vkAddr qAddr) (cd) (k) V st : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some 1 ∧ BaseInv R k V st ∧ LeanRaw R cd k ∧
  Mirror R cd st k ∧ AgreeW R H cd k V st ∧                      -- AgreeW: Agree over leanStageW
  (accFrom k = true → AccInv R cd st) ∧                          -- from .vk on
  (isExternal R → VEnv.get V "quotientEvaluator" = some qAddr)
```

### 8.1 Accumulator validation (in vkLoading; before the transcript)

Invariant established: `AccInv`. It is **unconditional**: stated on raw instance words, with no
snapshot and no decoding of the proof, because the contract validates the accumulator before any
proof point is known to be a group element. It belongs with `LeanRaw` and `Mirror`, never in
`Agree` (the rule of PLAN-V3 §5 M3). It then holds unchanged up to the final pairing, so the
four rows that do not touch the two slots each owe one frame clause: their write set misses
`[accLhsMptr, +128)` and `[accRhsMptr, +128)`.
Soundness reading: on a normal exit with `success = 1` the accumulator of the raw words decodes;
otherwise the block reverts (`ERR_BAD_POINT_ENCODING`, or `ERR_PRECOMPILE_FAILED` when a G1MSM
failed, which `permissive` allows). Progress premise: `AccDecodes R cd`, which
`LeanAcceptsAcc` supplies (`accDecodes_of_leanAcceptsAcc`, proved from `instWords_of_decoded`).

### 8.2 The widened last stage

`leanStage .pairing` asks `DualMSM.check`, which in accumulator mode need not hold when the
batched check does. `leanStageW` asks `accFinalCheck`. `leanStageW_noAcc` (proved): without an
accumulator it is V3's stage. `LeanFinalAcc` is the closed last stage, and it **is**
`LeanAcceptsAcc`: `leanAcceptsAcc_of_final` and `leanFinalAcc_of_accepts` are proved, both ways,
from the tree's `snapshotOf_prepareMsgs` (a registered obligation, `Snapshot.lean:380`).

### 8.3 The alpha batching (in finalPairing)

Invariant after the batching and before `ec_pairing`: `BatchedInv`. For every decoding, the two
pairing slots hold `toEip` of the reference's two batched inputs
`(kzg_lhs + α·acc_lhs, kzg_rhs + α·acc_rhs)` (`batchedInputs`). It is decode-relative, which is
allowed here: at `.pcs` the calldata decodes. The ALG half is `batchedCheck_iff_contract`
(obligation): the batched check is the contract's pairing equation on those two points; it
follows from `batchedCheck_eq` and `dualMsm_check_iff_contract`, both proved in v1, under the
same two base-point pins as without an accumulator.

### 8.4 The evaluator body (new row; closed dialect)

```lean
def EvalBodyShape (R) (Q) : Prop  -- SEM, content-independent: input of length frameLen ⇒ every run
                                  --   returns outputLen bytes, word 0 = magic; other length ⇒ every run fails
def EvalBodyAgree (R) (Q) : Prop  -- SEM+ALG: for a frame that is the window of a caller state at
                                  --   StageInv .lagrange, under SoundSide, per decoding: word 1 =
                                  --   frWord (linComEval L.linCom), words 2.. = linComBuckets L.linCom
                                  --   where leanStage … .quotient = .ok S, S.lin = some L
def EvalBodyTotal (Q) : Prop      -- from every entry frame a run exists
def EvalContracts (R) (Q) : Prop := isExternal R → EvalBodyShape R Q ∧ EvalBodyAgree R Q ∧ EvalBodyTotal Q
```

`EvalBodyAgree` is V3's quotientLin row transported into the callee's frame. The transport is a
memory fact: the callee's memory after `calldatacopy(QUOTIENT_FRAME_BASE, 0, QUOTIENT_FRAME_LEN)`
equals the caller's window; everything the numerator reads must lie in the window (the frame
runs from `VK_MPTR = 0x3680` for `0x6ac0` bytes, READ sol:1817), and what it uses as scratch lies
outside and is zero in the callee. The generator already checks containment
(`Halo2QuotientEvaluator.validateLayout`, `Generator/Artifacts.lean:428`); the statement should
take that check as its premise.

### 8.5 The quotientLin row at an external render

Pre `StageInvW .lagrange`, post `StageInvW .quotient` (V3's `.quotient` clauses: the expected
evaluation at `quotientEvalMptr`, the buckets at `selectorAccMptr`). The slice is: the pin guard,
`gas()`, the STATICCALL, two checks, one `mstore`, a copy loop over the simple selectors
(sol:1803-1829), then the linearization scope as in V3. The guard gives `QPinned`;
`EvaluatorTrust.spec` turns a successful answer into a run of the body; `EvalBodyShape` and
`EvalBodyAgree` give the returned words.

---

## 9. Generic rows: what the widening adds or changes

Proof classes: **ALG** (Lean only, no Yul); **PAR** (parametric Yul with symbolic layout
constants, straight-line or loops with literal bounds); **LOOP** (needs a loop invariant with a
symbolic bound); **GEN** (induction over what the generator emits). "SEM" below is the Yul half.

| row (for every `R`) | change | SEM class | ALG | notes |
|---|---|---|---|---|
| prefix (`prefix_sim`, `prefix_prog`) | one more wrapper local, `quotientEvaluator` | PAR | none | establishes the last conjunct of `StageInvW .start` |
| **vkLoading** (GEN.1) | + accumulator validation when `expected_has_accumulator` | PAR. Two loops, both with **literal** bounds: 7 limbs (sol:984) and 2 coordinate words (sol:1025); in the helpers the bounds are parameters, bound to literals at the two call sites. Two STATICCALLs to `0x0c` | new: the Yul rebuilds a coordinate as an `(hi, lo)` pair with a straddling limb (sol:993-1007), the port sums and splits (`Exec/Accumulator.lean:362-370`); their equality is **stated nowhere**. Then `Holds.g1Msm1`, `g1Decodes`, `idLaw` | GEN.1's card says "Does NOT need loops, staticcall": true only for V3's class. Six new helper summaries (HLP.1): `load_acc_coord_shifted`, `is_bls_p_minus_one`, `check_acc_coord_packing`, `load_acc_coord`, `load_acc_point`, `validate_public_accumulator` (the 823 tokens PLAN-V3 §3 lists as missing from the AST) |
| transcriptParser, lagrange, pcs | none in the code | as V3 | none | each owes the frame clause for `AccInv` (§8.1) |
| **quotientLin**, external arm | the embedded numerator is replaced by the call block | PAR, plus one **LOOP**: the bucket copy, bound = number of simple selectors (10 at the IVC key) | none new; consumes `EvalContracts` and `EvaluatorTrust` | embedded arm: unchanged |
| **evaluator body** (new; closed dialect) | wrapper: length test, `calldatacopy`, `mstore` of the magic, bucket copy, `return` | wrapper PAR + one LOOP (same copy bound). Numerator: **LOOP** (the interpreter, symbolic bound, memory-driven guard) + **GEN** (native identity arms) + LOOP (permutation and lookup arms, circuit-dependent bounds; `modarith7`, counts read from the program) | the transport lemma (§8.4); `quotientFold_matches_linearization` as in V3 | the numerator is V3's ROW.Q object (route B). The widening requires that row to be stated over a memory window and over a dialect parameter, so that it serves both the verifier's slice and the evaluator's body. The proof engine is stated for `Bridge.Dialect c g`; the evaluator runs in `EVM.evm`. A lemma relating the two for a block with no call and no `gas()` is owed, or the slot is restated over `Bridge.Run ExternalCalls.none ExternalGas.none` |
| **finalPairing** | + the batching block when `expected_has_accumulator` | PAR: straight-line; one `keccak256` over `0x240` bytes, two G1MSM, two G1ADD (sol:2516-2562) | `batchedCheck_iff_contract`; `frOfDigest` against `mod(keccak, r)` with the zero-to-one arm | the poisoned arm is the `if success { … }` guards |
| traceReturn | none | as V3 | none | its exit carries `LeanFinalAcc` |
| `TwoOutcomesW` | `qAddr` quantified | none | none | **proved** from V3's two scan obligations |
| `TotalW` | + `EvalBodyTotal`; the "no `gas()`" premise replaced (§5.2) | LOOP (termination of the interpreter on any frame, including malformed ones) | none | the evaluator must be total on **every** input, not only on frames of valid runs: a permissive caller state need not satisfy `StageInv` |

The row families are stated in `WideningStages.lean`: `BlockSimW`, `SimContractsW`, `BlockProgSW`,
`ProgContractsW`. They are V3's with `StageInvW`, `callsW` and the three extra hypotheses.

---

## 10. Obligations and their W12 plan

| obligation | file | kind | witness | falsifier |
|---|---|---|---|---|
| `lowering_correctW` | Statements | the target | `HypothesesInhabitedW` at an IVC-class circuit (§7) and at F1 | the mutation corpus; a render with a tail (outside the class) |
| `model_quotientMode` | Statements | generator fact | `#eval` at one embedded and one external model | a hand-built model with the flag false and `quotientExternal = some _` fails `Valid.model` |
| `instWords_of_decoded` | Stages | ALG | the F1 calldata KAT | a calldata one word short does not decode |
| `batchedCheck_iff_contract` | Stages | ALG | the constructed pairing at a known `s` | drop `hn`: differs at `lhs = rhs = g₁` (as for `dualMsm_check_iff_contract`) |
| `EvalBodyShape`, `EvalBodyAgree`, `EvalBodyTotal` | Stages (defs) | rows | the run-it gate with the slot answered by the interpreter | an input one byte short reverts; a program byte flipped to an unused opcode reverts |
| the `(hi, lo)` straddle lemma | not stated | ALG | `decoder_accepts` (the port, on Rust data) | a limb moved across the 256-bit boundary |
| inherited: `twoOutcomes_of_exitDiscipline`, `scans_prog_addr_indep`, `snapshotOf_prepareMsgs` | V3, tree | as registered | | |

Not typechecked, because it does not exist yet: anything about the evaluator's AST. `EvalObject`
is a parameter; `ValidW` checks closedness and the pins, not that the body is what the generator
prints.

---

## 11. Decisions for the owner

| id | decision | recommendation |
|---|---|---|
| W-1 | Make `lowering_correctW` the stated target, with D-P71's `lowering_correct` as its proved corollary, or keep the V3 theorem and widen later | **Adopt the widened statement now, prove the V3 corner first.** The statement costs nothing (the reduction is proved) and stops the V3 rows from being stated in a shape that must be redone: `StageInv`, `leanStage .pairing`, `callsOf`, the fixed `qAddr = 0` |
| W-2 | Accumulator kinds | **Point-and-scalar, no tail** (clause `accKind`). Strike `accKind` when a point-pair circuit exists. The tail arm is a later widening: it needs the fixed-base table and R-52 |
| W-3 | The evaluator in the headline | **`EvaluatorTrust` as a hypothesis, keyed on the pin**, with the generated Yul body as object. Alternative: define the slot as the model, with the trust in prose only |
| W-4 | Right-hand side in accumulator mode | **`LeanAcceptsAcc`**, with the two Rust corollaries. The English statement must say: not equivalent to one Rust function; sound up to `AlphaCollision`; one SRS. Do not add `¬AlphaCollision` to `SoundSide`: it would put a cryptographic assumption inside a predicate on calldata |
| W-5 | Conjunct 2's gas oracle | **Keep the zero oracle in the headline** (V3 text recovered exactly); prove the rows for `CompleteAnyGasW`, which totality needs anyway |
| W-6 | `idLaw` | **A hypothesis only in accumulator mode.** Alternative: add it to `G1CodecHeadlineLaws` for every render (a frozen-surface change; `g1CodecC` should satisfy it) |
| W-7 | The test circuit and its SRS | **Regenerate the IVC bundle under one seeded test SRS** (one trapdoor for both sizes), with exporter schema 2 plus: trace ids 29 and 30, the input of the `0x0f` call, the four accumulator mutants and the bad-inner-opening mutant. Keep the production render for byte equality only |
| W-8 | One `[τ]₂` | **Add `assert_eq!(ivc_srs.s_g2(), decider_srs.s_g2())` to the e2e test**, and name the assumption in the English statement |
| W-9 | The evaluator has no free-memory guard | Either accept `EvalEntry.fmp` as trusted (measured `0x8c0 ≤ 0x1000`), or ask the generator's owner for the guard the verifier has. **Recommend the guard**: it turns a trusted bound into a checked one at about 6 gas |
| W-10 | `Evaluator.rel_worldLocal` | **Delete with the v1 track**; no V2/V3 statement needs it |

---

## 12. What the statements need from the object and reference passes

- `evalBodyOf : PlanView → Model → YulBlock` (or the evaluator model), with a token-agreement
  clause against `renderHalo2QuotientEvaluator`, so that `EvalObject.body` becomes a function of
  the render. The evaluator render is exercised by no gate today
  (READ `Generator/Contracts.lean:45-48`).
- The six accumulator helpers and the batching block in the verifier AST.
- A decidable scan for "`gas()` occurs only as the gas argument of a call", and one for "the
  evaluator body contains no call, no `gas()`, no environment read".
- The numerator row stated over a memory window and a dialect parameter (§9).
- In the bundle: the items of W-7.
- The reference: `Snapshot.acc` is passed as `none` everywhere; `LeanAcceptsAcc` does not use it.
  The reference gate should compare `(a.fullyCollapse accBases)` with trace ids 29 and 30.

---

## 13. Where this contradicts the brief

1. *"The Rust side … `verify_final` combines with a Poseidon-sponge `r`."* True of
   `verify_final`, but the e2e test never calls it. The Rust-side facts are a plain PLONK verify
   and a separate `Accumulator::check` (§3.1).
2. *"validate_public_accumulator … folds a carried scalar / fixed-base tail."* At the tracked
   artifact there is no tail: both sides carry a scalar and the RHS MSM is one pair
   (sol:1201-1205, :1233).
3. *The dump as a fixture.* Its proof, calldata and size report are untracked and belong to an
   earlier render (§7.1).
4. *"sorries at :142 and :955"* in `Lowering/Accumulator.lean`: confirmed. The other three
   declarations the brief named (`batched_complete`, `batched_atMostOneRoot`,
   `contractRef_acc_complete`) are proved, whatever their docstrings say (§3.4).
5. *The recorded negative result about `Evaluator.rel`.* The lemma is sorried and argued false,
   but nothing on the V2/V3 route needs it, and its docstring's premise (the evaluator reads the
   hash oracle) is false for the generated evaluator (§5.3).
6. *"7 limbs × 56 bits … accumulator encoding's shape"* as a scope parameter: the generator
   accepts no other limb shape, so it is not a degree of freedom of the class (§2.1).
