# Semantic-equivalence statements in Lean + proof plan (PLAN 9.5 made real)

## Context

PLAN 9.5 (`formal/docs/PLAN.md:402-507`) states, in pseudo-Lean, the theorems that
tie the Lean verifier (`Midfall.Halo2.Exec`, a line-faithful port of the Rust
verifier) to the generated Solidity/Yul contract. Only three of those statements exist
as Lean today (the frozen trio in `Midfall/Statements.lean`), plus one proved lemma in
the untracked `Midfall/Lowering/SemanticEquivalence.lean`. Everything else in 9.5 is
prose. The generator port (M3) is ~75% done; the review boundary keeps adversarial
review off until the semantic-equivalence results are *finished*; ROADMAP names
`finalPairing_spec` as the first point where the proof architecture can be shown
capable of failing.

The user asked for: every 9.5 statement written in real Lean, over the types that exist
now and abstracting over what is still to be ported, copiously documented, plus a
detailed plan for the proofs. Scope confirmed by the user: **full surface** (all files
below, proofs as registered holes except rfl-level lemmas) and **Exec refactor now**
(named phase functions so the L0 snapshot is concrete).

Evidence base: a survey of the tree (8 read-only explorers, 347 verbatim signatures, a
critic that spot-checked 46), three design perspectives, and an adversarial pass that
checked 44 proposed declarations and found 7 false/vacuous/ill-typed ones, all fixed
below. Detailed Lean sketches live in the session scratchpad and are the implementer's
reference (read them before writing each file):

- `P-SE-evidence/survey.md` (signatures, constraints)
- `P-SE-evidence/critic.md` (corrections)
- `P-SE-evidence/design0.md` (partials, Inv, Snapshot, finalPairing), `design1.md` (codecs, accumulator, calldata, QVM), `design2.md` (bridge, headline)
- `P-SE-evidence/attack.md` (verdicts and fixes; every FIX line is binding)

## Findings that change what gets written (report in REVIEW.md, do not silently fix)

1. **`verifyNative_iff_msgs` (frozen) is false for all `E`.** `prepareMsgs`
   re-serialises G1 messages with `E.g1.toCompressed`; `decodeRust` decodes with
   `ofCompressed?`. With `toCompressed := fun _ => Bytes.empty` the re-serialised stream
   is short, `verifyMsgs` faults, `verifyNative` succeeds. Provable form needs
   `E.g1.compressedRoundtrip` only (the attack showed `p ≤ 2^256` is decorative here).
2. **`verifyMsgs_iff_spec` (frozen) cannot hold for all `E`.** `Spec.accepts` takes no
   `E`, while `verifyMsgs` depends on `E.delta`, `E.field.numBits`, `E.g1`,
   `E.fewerPointSetsRuntime`. Needs an `E`-dependent spec (Phase 4).
3. **`contractRef_noAcc` (frozen) is provable now** from
   `Lowering.contractRefAccepts_iff_verifyMsgs`; filling it needs a hash re-pin.
4. **Completeness counterexample at `x ∈ H`** (R-2 first face): `Lagrange.yul:93-99`
   reverts `ProofRejected` when `x^n - 1 = 0` or `x - ω^i = 0`; Lean's `lIRange`
   returns zeros and accepts. Completeness conjuncts need `ChallengesGood.xNotRoot`
   plus `EnvAgrees.omegaOrder/domainN` (so `x^n ≠ 1` really excludes `ω^i`).
5. **Soundness counterexample at `f_j(x) + β = 0` (NEW, confirmed in source).** Both Yul
   logup paths compute the helper identity by prefix/suffix products with no inversion
   (`yul_emit.rs:439-560`, `quotient.rs:1688-1880`; the k=1 arm emits `h*(f+β)-1`), so
   the contract computes a definite value and continues; Lean panics
   (`Logup.lean:279`, faithful to `logup.rs:460`). `verifier_sound` needs an explicit
   `NoLogupPanic` hypothesis. Record as the soundness twin of R-2. Whether the definite
   value is exploitable is an S-level follow-up (the helper eval is KZG-bound).
6. **`decodeAcc_injective` false as planned** (R-25) → stated over `accWords`, needs
   `toEip 1 = 128 zero bytes` as a third hypothesis. **`decodeAcc_encode`** only for
   collapsed `.pointAndScalar`; `.pointPair` round trip is FALSE (`encodeAccInstances`
   always emits carried scalars). **`repack_spec` iff is FALSE** (a byte-valid proof whose
   pipeline panics repacks fine while `decodeRust = none`) → split form.
   **`render_eq_print`** false as text (R-39) → structural only. **QVM trio** unstatable
   as written (D-P20) → per-identity + fold as a new definition.
7. **`Midfall.Halo2.fixedBases` "-G" entry is the group identity**
   (`Accumulator.lean:500-506`; Rust `verifier/mod.rs:119` uses the negated generator).
   New defect; every accumulator statement takes the table as a parameter.
8. **D-P16 reconciliation** (a)-(d) between the two `AccumulatorEncoding` types is stated
   here with the necessary `n < 2^64 - 1` bound (saturating vs unbounded add).
9. **Hash agnosticism couples to extcodehash** (Y-2): `extcodehash a = keccakOf
   (extCodeOf a)`, so `DeploymentW.vkHash` is `H vkRuntime = constant`, a hypothesis on
   `H`. Embedded-VK renders carry no such constraint.
10. **From the adversarial pass:** any-memory soundness needs the `g1_identity` window
    zero (nothing writes it; PCS reads it as the committed-instance commitment);
    `only_two_outcomes` over the shell is false for the `BUILD_ID()` getter selector →
    restrict to the `verifyProof` arm; completeness needs `W.callvalue = 0`, the
    `AUTHORIZED_VK` immutable = `vkAddr`, `memoryguard ≤ 0x1000`, and `toEip 1 =
    zeros` (committed point absorbed as 4 zero words); `ir_refines` needs world-local
    call relations (a relation reading `st.memory 0x40` separates IR from shell);
    `end_to_end_noAcc` needs `inst.size = cfg.numInstances` and `fromRepackError`.
11. **`X_N_MINUS_1_INV_MPTR` has no production consumer** (grep of kzg/mod.rs,
    quotient.rs, QuotientNumeratorBlock.yul, quotient_numerator/*.rs) → `Inv` leaves it
    unconstrained.
12. **`selector_accumulators` is phase-scoped** (`LayoutMemory.lean:268-270`, lifetime
    `.phase .pcsFinalMsm`) but written by the quotient phase and read by PCS block 5 →
    `Checkpoint.liveAt` must be checkpoint-aware for that region.

## Non-negotiable constraints (CI and house rules)

- `Midfall/Statements.lean` is SHA-256 frozen: no edits. New names go in new files; do
  not reuse `Midfall.Statements` namespace.
- Every `sorry` registered in `SORRY.md` via `scripts/gen_sorry.sh`; add `owner()` arms
  in `gen_sorry.sh` for `Midfall/Lowering/*`, `Midfall/Yul/*`, `Midfall/Assumptions/*`.
- **Fix `checks.sh:14`**: `listed` is sorted lexicographically, `found` numerically; use
  `sort -t: -k1,1 -k2,2n` for both. (One-line CI change; flagged as a decision below.)
- `scripts/lean_grep.py` treats `'` as a char-literal delimiter: never spell the s-word
  in comments; avoid primed identifiers in theorem files; write "proof hole".
- D-P17: theorem-bearing files must not import `Midfall.Instances.*`. Transitive trap:
  `Generator/Vk.lean` imports `Instances.ExponentModel`; **no theorem file imports
  `Generator.Vk`** (Vk-dependent facts become `LoweringCorrect` fields). Run
  `#print axioms` on every new theorem.
- Register every new module in `Midfall.lean` (R-50 orphan gate).
- `autoImplicit = false`; report only `lake build` results.
- Phantoms: write `(p := p) (G₂ := G₂) (Gₜ := Gₜ)` on `decodeAcc`, `KzgAcc.new/trivial`,
  `DualMSM.new/init/scale/addMsm`; `(Gₜ := Gₜ)` on `prepareMsgs`/`verifyMsgs`/
  `verifyNative`/`decodeRust`. Use `haveI := P.decEqG₁` where needed; no `[DecidableEq]`
  binders (D-P7).
- `Msg`, `Location`, `Value`, `Ptr`, `Generator.Word`, `EcPoint` have no `DecidableEq`:
  use `=` in statements. Qualify `AccumulatorEncoding` (two namespaces), never `open
  Midfall.Generator.QVM` (`QVM.Fr` shadows `Midfall.Fr`), avoid `Midfall.Generator.Word`
  vs `Midfall.Word256` and `modexpFrameBytes` clashes.
- Vendored tree is a pinned fork: add the ∀-runs layer under `Midfall/Yul/`, do not
  edit `vendor/`.
- Only 25 `.olean`s exist locally; Accumulator, Generator/*, Spec, Security, Statements,
  Yul/Externals have never been built here. `decodeAcc`'s `-s` at
  `Accumulator.lean:987` is unverified: `#check @Midfall.Halo2.decodeAcc` first.
  **Step 0 of implementation is a full `lake build`** to baseline (may need
  `lake exe cache get`).

## Decisions embedded in this plan (approval = sign-off; each has a recommended reading)

| # | decision | reading adopted |
|---|---|---|
| D1 | Statement form for Surface-dependent obligations | `structure LoweringCorrect (S) : Prop` / `PartialSpecs` fields (no holes); plain `theorem … := by sorry` (registered) for statements over existing types |
| D2 | Vacuity guard | `Surface` carries `o₀ : RenderOptions`, `lower_ok : S.lower o₀ = .ok S.L`; every field assumes `S.Supported o₀`; non-vacuity `example`s/KATs next to the structure |
| D3 | D-P18 `Supported.layout` | option 1: `memory.map.WellFormed ∧ (memory.validate).isOk = true` |
| D4 | R-25 `accWords` | normalised tail (window from `enc.offset`, identity-flagged coordinate words zeroed, flags/carried/tail kept) |
| D5 | Bad-set side conditions | explicit hypotheses: `ChallengesGood.xNotRoot` (completeness), `NoLogupPanic` (soundness); not a `ContractRef` widening, not `LeanAccepts ∨ panics` |
| D6 | Exec refactor | R1-faithful split, bodies moved verbatim, old defs become the composition; gate = unchanged KATs + conformance replay |
| D7 | `calldata_canonical` | EXACT in both modes over raw `Word256` (supersedes PLAN 489-490's ≈ fallback) |
| D8 | `repack_spec` | split: wire-level iff over `decodeWire` + one-way `decodeRust → repackProof` |
| D9 | `fixedBases` "-G" defect | report; statements take the table; fix in a separate Exec patch with KAT |
| D10 | `checks.sh` sort | fix the script (both sorts numeric) |
| D11 | Hash-agnosticism scope | `∀ H` with `DeploymentW.vkHash : H vkRuntime = constant`; record restriction in PLAN 10.3 |
| D12 | `worldUnchanged` route | fuel-based `NoWriters` on generated blocks (Supported.production) rather than assuming a STATICCALL entry |
| D13 | P-4a `zeta_order` | out of this package; note it cannot be discharged for `fc17` (ZMod 17 has no order-3 element) |
| D14 | Eip2537.Holds shape | 2-pair `pairing2` (P2) with the `G2Enc` wrapper (P1); `Modexp.Holds` is a THEOREM (`modexpInv_correct`), not an assumption |
| D15 | Accumulator arm reaches the deployment | kind-aware `encodeAccPublicInput` + point-pair round trip; `EnvAgrees` pins the accumulator header words and the fixed-base table to the VK payload; snapshots carry `accOf S instW`; one-way `end_to_end_acc_complete`; still no acc-mode `↔` with Rust (R-10) |

## Architecture

```
Midfall/Yul/Contracts.lean        ∀-runs partial-correctness layer, dialect-generic
Midfall/Yul/Bridge.lean           open-dialect Run/RunCommitted, det, keccak hook, Obs, honest/permissive calls
Midfall/Assumptions/Codec.lean    G1CodecLaws (hypothesis structure) + frOfRepr_frToRepr
Midfall/Assumptions/Eip2537.lean  G2Enc, Eip2537.Holds, modexpInv_correct
Midfall/Lowering/AccEncoding.lean toExec + D-P16 (a)-(d)
Midfall/Lowering/Accumulator.lean accWords, decodeAcc_*, S5, pairing lift, ContractRefAcceptsAcc, contractRef_acc_complete
Midfall/Lowering/VkDigest.lean    feToU256_frToRepr (imports Encoding, never Vk)
Midfall/Lowering/Calldata.lean    encodeContractProof/repackProof/decodeWire/encodeCalldata/calldataOf/decodeCalldata + specs
Midfall/Lowering/Checkpoint.lean  Checkpoint, Partial, liveAt
Exec refactor (Verifier.lean, Kzg/MultiOpen.lean)   readAlgebra/lagrangeTriple/linearize, phaseA/B/C
Midfall/Lowering/Snapshot.lean    Snapshot (+ per-phase prefixes), snapshotOf, snapshotOf_prepareMsgs
Midfall/Lowering/Inv.lean         PlanView, EnvAgrees, ChallengesGood, Inv, Inv_mono
Midfall/Lowering/Surface.lean     Surface record, DeploymentW, initState/RunVerifier/RunShell/RunContractIR, ObsEquiv, LeanAccepts, GenericX, NoLogupPanic, EvaluatorFrame/FrameWellFormed
Midfall/Lowering/Partials.lean    PartialSound/Progress, PartialSpecs, finalPairing_*, traceReturn_spec
Midfall/Lowering/Qvm.lean         QVMFr↔Fr, valuation layer, RecognizersSound, per-identity compile correctness
Midfall/Lowering/QvmFold.lean     globalIdentities, quotientFold, fold ↔ linearization
Midfall/Lowering/Obligations.lean LoweringCorrect + derived/registered theorems
```

Typing rules that every file follows:

- Variable block as `Statements.lean:29-34` (`[P : AdmissiblePairing G₁ G₂ Gₜ]`).
- Instances are raw `Array Word256` wherever the contract rejects `≥ r` (R-26.7);
  `instOfWords?` lifts and rejects; `frWord` only on values already known `< p`.
- `D := Midfall.Yul.Bridge.Dialect calls gas` written explicitly at every `Run`/
  `StmtsContractAll` (Dialect.Op is a structure field, not inferable).
- Soundness quantifies over `permissive calls` and ANY `gas`; completeness and
  determinism use `honestCalls` and `ExternalGas.ofFun`.
- Observations compared at `ObsView` level (outcome, halted, world components); never
  state equality `obs = .return abiTrue`.
- Side conditions through the snapshot API, never a second copy of the transcript
  schedule (R-30/R-32).

## Files and declarations (index)

Status legend: **def** = definition; **thm-hole** = theorem with registered hole;
**rfl** = proved in-line (short); **field** = obligation field of a Prop structure.
Milestone per PLAN 11/14.5. Hypotheses listed are the load-bearing ones; each must
carry a one-line "why" citing its finding in the doc comment. The full Lean statements
for every item in this index are in the section **"Full statements (Lean sketches)"**
after the proof plan; names marked `-- SKETCH` there could not be verified against a
built module and must be `#check`ed first.

### 1. `Midfall/Yul/Contracts.lean` (generic, `{D : Dialect} [DecidableEq D.Value]`) — M4-Lean
- `StmtsContractAll / StmtContractAll / ExprContractAll` **def**: ∀ derivations from `pre` satisfy `post` (vendored `StmtsContract` is existential). Non-vacuity `example`: `¬ StmtsContractAll (D := EVM.evm) [] [] (fun _ _ => True) (fun _ _ _ _ _ => False)` via `Step.seqNil`.
- `Step.stmts_cons_inv` **rfl** (cases on seqCons/seqStop); `Step.stmts_append_inv`, `cond_inv`, `switch_inv`, `call_inv`, `loop_inv` **thm-hole**.
- `StmtsContractAll.cons_split` (halting head: `(o = .normal ∧ mid) ∨ (o ≠ .normal ∧ post)`) **rfl** (given cons_inv); `append`, `block`, `StmtContractAll.cond`, `switch`, `ExprContractAll.callUser`, `ExecLoopAll.countdown_or_halt` (stated in full: `(o = .normal ∧ Inv 0) ∨ (o = .halt ∧ Q)`, inverting loopBodyHalt/loopPostHalt/loopCondHalt), `StmtsContractAll.of_det` **thm-hole**.

### 2. `Midfall/Yul/Bridge.lean` (no `Midfall.Halo2.Exec` import) — M4-Lean
- `Dialect calls gas := EVM.evmWithExternal calls ExternalCreates.none gas` (`@[reducible]`), `Run`, `RunCommitted := ∃ st', Run … ∧ stObs = committedState st0 st'` **def**.
- `YulSemantics.EVM.ExternalCalls.Functional`, `…ExternalGas.Functional` **def** (declared in those namespaces so dot-notation resolves); `ofFun_functional` **rfl**.
- `dialect_deterministic (hc) (hg) : ∀ op, Deterministic op` **thm-hole** (op split: call-family via `externalCall` + hc; `.gas` via hg; create under `.none` = static halt only; rest `stepOp`); `Run.det`, `RunCommitted.det` **rfl** from it; `twoResponses_nondet` gate (two-response `calls`, `staticcall` then `mstore(0,s)`, differing memories) **thm-hole**.
- `hashOfBytes H : List UInt8 → U256`, `withKeccak`, `keccakOf_invariant` (Step induction) **thm-hole**, `RunCommitted_keccakOf`.
- `Obs`, `ObsView`, `Obs.view`, `isReturn`, `returnData`, `isRevertOrHalt` (k.commits = false), `WorldEq`, `worldUnchanged`, `worldUnchanged_of_rollback` **rfl**, `abiTrue := (natToBytesBE 1 32).data.toList` (single definition; KAT: length 32, last byte 1), `returnView`.
- `toYulKind/toYulReq/ofOutcome/failResp`, `hits` on `accountKey`, `honestOf`, `honestCalls product evalAddr evalRel`, `permissive c` (constructor: `world = CallWorld.ofState st ∧ (success → c.Call …)`), `honest_le_permissive` **rfl**, `honestRelations_keys` (`= [0x0b,0x0c,0x0f,0x05]`) **thm-hole**, `honestCalls_functional (hev) (hdisj)` **thm-hole**.
- `WorldLocal c : Prop` (response set depends on `CallWorld.ofState st` only) **def** — attack fix for `ir_refines`.
- `Evaluator.calleeState/responseOf/rel/rel_functional` (`.selfdestruct ↦ success`; `rel` over closed `EVM.evm` on the runtime block) **def/rfl**.
- `Op.isWriter`, `noWritersFuel` (R-37 fuel), `NoWriters`, `Run_worldEq_of_noWriters` **thm-hole** (drop the decorative `hw`).

### 3. `Midfall/Assumptions/Codec.lean` — M5
- `G1CodecLaws c : Prop` **def**: `eipRoundtrip`, `compressedRoundtrip`, `ofEip_toEip`, `eipShape` (16‖48‖16‖48, coords `< pBase`, not (0,0)), `toEip_one`, `compressedWidth`, `eipWidth`. Non-vacuity: toy codec over `Multiplicative (ZMod 17)` as `example`; constant-zero codec violates `eipShape`.
- `frOfRepr_frToRepr (hp : p ≤ 2^256)` **thm-hole**.

### 4. `Midfall/Assumptions/Eip2537.lean` — pulled-forward prerequisite
- `G2Enc G₂ := { toEip : G₂ → Bytes }` **def**.
- `Eip2537.Holds (E) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop` **def**: `g1Valid`, `g2Valid`, `pairing2` (two pairs ↔ additive pairing eq), `g1Add` (0x100 frame), `g1Msm1` (interleaved 0xa0 record, scalar as `frWord`), `g1Decodes`. Header states satisfiability is not demonstrable in-tree (exponent model's `toEip` is not a curve point). Cite `AssemblyHelpers.yul:284-287` layout, `FinalPairing.yul:88` swap.
- `modexpInv_correct (hx : 0 < x) (hr : x < blsR)` **thm-hole**; KAT: inverse of 2 = `(blsR+1)/2`.

### 5. `Midfall/Lowering/AccEncoding.lean` — M5
- `toExecKind`, `toExec`, `toExec_hasCarriedScalars` **rfl**.
- `toExec_coordinateWords (h : numLimbBits ≠ 0)`, `toExec_fixedPayloadWords`, `toExec_fullyCollapsed` (unconditional, `.toOption`), `toExec_validFor (hn : n < usizeMax)` (`.isOk = validFor`), `toExec_fixedScalarCount (hn)` **thm-hole**; `example` at `n = usizeMax`: generator ok ∧ Exec false (the bound is load-bearing).

### 6. `Midfall/Lowering/Accumulator.lean` — M5 (S5 proofs M9)
- `accWords enc inst` **def** (D4).
- `decodeAcc_injective (hrt : eipRoundtrip) (hone : toEip 1 = zeros128) (hnodup : names Nodup)` **thm-hole**.
- `negateByTable`, `decodeAcc_encode (hp : p < 2^256) (hkind = .pointAndScalar) (hshape) (hc : G1CodecLaws) (hsorted) (hnames) (hpre : prefix.size = enc.offset) : decodeAcc … (prefix ++ encodeAccInstances …) = some (negateByTable fb a)`, `decodeAcc_encode_noNeg` **thm-hole**.
- `encodeAccPublicInput` (kind-aware: no scalar words for `.pointPair`, the deployed Moonlight shape) **def**; `decodeAcc_encode_pointPair` (scalars implicitly 1) **thm-hole** (adjustment 1).
- `decideBool_eq_true_iff` **rfl**; `MSMKZG.eval_fromBase` **rfl**; `eval_scale` (no Wf), `eval_addMsm (hm hn : lockstep)` **thm-hole**.
- `batched_complete (hWf) (hd) (ha) (α)`, `batched_atMostOneRoot (hWf) (hbad) (hα hβ) : α = β` **thm-hole**.
- `contractPairingHolds g2 negSG2 lhs rhs`, `dualMsm_check_iff_contract (hn : nG2Prepared = g2⁻¹) (hs : sG2Prepared = negSG2⁻¹)` **thm-hole** (check-level; linearity in G₂ slot, no cyclic lemma). Keep `exists_zmod_smul_generator` (prime order ⇒ cyclic, `hG₁`) as a **thm-hole** for Spec-level use.
- `frOfWord?`, `instOfWords?` **def**; `ContractRefAcceptsAcc E H params vk (cfgAcc : Option Gen.AccumulatorEncoding) (vkDigest : Word256) fb (instW : Array Word256) ms : Bool` **def** (P1 signature: rejects words ≥ p via `instOfWords?`, `alphaOf H vkDigest E.g1 d.left.eval d.right.eval accL accR`, positive-base table); `contractRefAcceptsAcc_none` **rfl**.
- `contractRef_acc_complete (hinst) (hv) (ha : decodeAcc = some a) (hchk over fb table) (hWf)` **thm-hole**.

### 7. `Midfall/Lowering/VkDigest.lean` — M5
- `feToU256_frToRepr : feToU256 (bytesToNats (frToRepr x)) = .ok (frWord x)` **thm-hole** (no bound on p). The `generateBaseVk` corollary is an Obligations field (Vk import forbidden).

### 8. `Midfall/Lowering/Calldata.lean` — M5
- `WireSlot`, `Msg.slot`, `RepackedProofLayoutPlan.slots`, `msgContractBytes`, `encodeContractProof` **def**.
- `repackSlot`, `repackProof plan c π` (exact-length guard first), `decodeWire` (same walk, with the exact-length guard) **def**.
- `fnSigVerifyProof`, `encodeCalldataRaw`, `encodeCalldata numInstances plan c π inst` (instance-length check; `GeneratorError.fromRepackError`), `calldataOf` **def**.
- `cdWord`, `g1WordsOk`, `decodeSlots`, `decodeCalldata L numInstances c cd` **def** — mirrors every contract acceptance line (selector; heads `Halo2Verifier.sol:148`; `VkLoading.yul:101-109`; `TranscriptProofParser.yul:63-68,319,382,416`; `AssemblyHelpers.yul:94-104`), **plus the attack fix `guard (L.proofEnd == L.proofCptr + L.proofLen)`**.
- `repackedLen_mod32` **rfl/omega**; `sum_commitmentReadGroups`, `proofLen_eq_repackedLen (h : fromProtocol … = .ok L)` **thm-hole**.
- `calldata_roundtrip (hL) (hlen) (hend) (hc : G1CodecLaws) (hshape) (hn) (hinst) (hp : p ≤ 2^256)` **thm-hole**.
- `calldata_canonical (hc : eipRoundtrip) (hend)` EXACT **thm-hole**.
- `repack_spec_wire`, `repack_spec_of_decodeRust (hc : compressedRoundtrip) (hsched)` **thm-hole**.
- `points_subgroup_checked_generator (h : validateAbsorbedG1PrecompileCoverage = .ok (.ok ()))` **thm-hole**.

### 9. `Midfall/Lowering/Checkpoint.lean` — M5
- `Checkpoint` (start vk transcript lagrange quotient pcs pairing; `idx`, `LE`, `next`), `Partial` (7 production partials), `Partial.pre` **def**.
- `Checkpoint.liveAt k : MemoryLifetime → Bool`: permanent ⇒ true; `.phase .pcsFinalMsm` ⇒ true at `.quotient`/`.pcs` only (finding 12); else false. Gate against LayoutMemory's region list.

### 10. Exec refactor (`Exec/Verifier.lean`, `Exec/Kzg/MultiOpen.lean`) — M5 prerequisite (D6)
- `Verifier.AlgebraRead` record; `readAlgebra` (`verifier.rs:283-439` body moved); `lagrangeTriple vk x xn` (`mod.rs:509-515`, order `(lLast, lBlind, l0)` documented against `Lagrange.yul:77-79`); `linearize` (`:475-647`). `verifyAlgebraicConstraints` := shape checks; `readAlgebra`; `linearize`; same R-8 collapse.
- `MultiPrepare.PhaseA/B/C` records; `phaseA/B/C`; `multiPrepare := phaseA >>= phaseB >>= phaseC |>.dual`.
- Gate: every existing `#eval` KAT token unchanged; `lake build`; conformance exe replays identically. No theorem needed (definitional composition).

### 11. `Midfall/Lowering/Snapshot.lean` — M5
- `Snapshot p G₁ G₂ Gₜ` **def**: `trace`, `alg : AlgebraRead`, `l0 lLast lBlind`, `instanceEval` (**selected by the unique public-column query with `q.2.int = 0`**, not `getD 0` — attack fix), `expressions`, `linCom`, `queries`, `a b c : PhaseA/B/C`, `acc : Option KzgAcc`.
- Per-phase prefixes `SnapshotVk/Transcript/Lagrange/Quotient/Pcs` (or a `Checkpoint`-indexed family) so partial k is stated over the prefix that exists even when a later phase faults (attack: WEAKER-THAN-PLAN fix).
- `snapshotOf E H vk inst ms acc : Except Fault Snapshot` (`#[#[inst]]`; `Features.solidity`) **def**; `snapshotOf_prepareMsgs` two-part (ok-value equality; `isOk` equality) **thm-hole**.

### 12. `Midfall/Lowering/Inv.lean` — M5
- `PlanView` (`vk : Halo2VerifyingKey`, `vkMptr`, `memory : VerifierMemoryLayout`, `proofLayout`, `numInstances k numNegLagranges`, `hasAccumulator`, `consts : TemplateConstants`) **def**.
- `ptrAddr/wordAt/bytesAt/holdsFr/holdsG1/holdsG1s/holdsFrs`, `LocalsOk V` (`r = p`, `success ∈ {0,1}`) **def**.
- `EnvAgrees E vk PV params sG2gen encG2 fb : Prop`: `modulus : p = frModulusConstant`, `truncWidth : divCeil (divCeil numBits 8) 2 = 16`, `delta : E.delta = blsDeltaLiteral` (new constant from `quotient.rs:1492`), `domainN`, `baryWeight`, `omegaInvMul`, `omegaOrder`, `negLagranges` (over Nat), `nG2 : nG2Prepared = P.g₂⁻¹`, `sG2 : sG2Prepared = sG2gen`, `vkDigestWord : (PV.vk.constants.getD 0 ("",0)).2 = frWord vk.transcriptRepr`, `g1BaseWords/g2BaseWords/negSG2Words`, and (adjustment 2) `accHeader/accNoHeader/accConsistent` (the four accumulator header words cross-checked at `VkLoading.yul:84-87` equal `PV.accEncoding`'s fields) and `accBasesInVk` (every fixed-base table entry is the point its VK slot encodes). `PlanView` gains `accEncoding : Option Generator.AccumulatorEncoding`.
- `ChallengesGood vk S : Prop` := `xNotRoot : S.alg.x ^ vk.domain.n ≠ 1` only (logupNoPanic moves to `verifier_sound`'s hypothesis list; inside PartialSpecs it was decorative).
- `Inv E params k PV S V st : Prop` **def**, clauses per `design0.md` with the attack fixes: `st.halted = none`; `LocalsOk`; `bytesAt st (ptrAddr M.g1IdentityMptr) 128 = natToBytesBE 0 128` at EVERY checkpoint; `.vk` payload image + exact calldata shape + acc points; `.transcript` challenges/commitments/evals/`qEvalCptr`; `.lagrange` xn/lLast/lBlind/l0/instanceEval (X_N_MINUS_1_INV unconstrained); `.quotient` quotientEval = `linCom.eval`, selector buckets, `QUOTIENT_MPTR` words; `.pcs` fEval/v/finalCom/`PAIRING_LHS = d.left.eval`/`PAIRING_RHS = d.right.eval` (at `.pcs` only); `.pairing` success = 1 ∧ (no acc → `DualMSM.check`). `Inv_mono` **thm-hole**.

### 13. `Midfall/Lowering/Surface.lean` — M5
- `Surface p G₁ G₂ Gₜ` **def** (one record; names `DeploymentW`/`SupportedS` to avoid `Types.lean` clashes): `E params vk cfg accFixedBases vkDigest`; `o₀ : RenderOptions`; `L : Lowered`, `lower_ok : lower o₀ = .ok L`; `bindLocals`, `shell`, `shellLayout`, `hoisted : FunEnv …`, `evaluatorRuntime : Option (YulBlock × EVM.Layout)`, `runtimeName`; `repackProof`, `encodeCalldata`, `decodeCalldata`; `lower`, `render`, `print`, `astOfMain`, `irCheck`; `Supported : RenderOptions → Prop`; `blk : Partial → YulBlock`; `memory`, `plan : PlanView`, `qplan qbuild qext`; `snapshotOf` link hypotheses; `g2BaseBytes negSG2Bytes expectedVkCodehash quotientRuntime expectedQuotientCodehash`; `shell_unfolds`; `vkDigest_spec`, `accFixedBases_spec`, `modulusPinned : p = Midfall.Assumptions.r`; `hProofLayout` (fromProtocol at 0x64), `hRepack`, `hDirectSharesLayout`, `hQbuild`.
- `SupportedS (S) (o) : Prop` full fields: `advice`, `instShape ∧ numCommittedInstances = 1`, `noRotInst : ∀ q ∈ instanceQueries, q.2.int = 0`, `acc : ∀ enc, cfg.accumulator = some enc → (enc.validateForNumInstances cfg.numInstances).isOk = true`, `singlePhase`, `hLimbs` via `vk.csDegree`/`WellFormed.domainConsistent`, `vkPoints` over encodings, `layout` (D3), `qvm : Prop` (validator abstract), `production`.
- `DeploymentW W H vkAddr quotientAddr vkRuntime expectedVkCodehash quotientRuntime expectedQuotientCodehash : Prop`: `keccak`, `wf`, `vkCode`, `vkNonEmpty`, `vkHash : H vkRuntime = h`, `qCode/qHash/qNonEmpty`, `disjoint` (accountKeys), `static = false`, **plus attack fixes** `callvalue : W.callvalue = 0`, `vkImm : shellLayout.immutable "AUTHORIZED_VK" = vkAddr` (+ quotient twin), `memguard ≤ 0x1000`, `vkRuntime = 0xfe ‖ hvk.bytes` link. `extcodehash_of_deployment {hsh}` **thm-hole**.
- `initState W Lyt H cd mem₀`, `callState`, `Surface.calls`, `RunVerifier`, `RunContractIR` (via `Object.subObject`), `RunShell`, `ObsEquiv` (view-level) **def**.
- `LeanAccepts S H cd := ∃ ms instW, S.decodeCalldata cd = some (ms, instW) ∧ ContractRefAcceptsAcc … instW ms = true` **def**.
- `accOf S instW := S.cfg.accumulator.bind (decodeAcc (toExec ·) S.E.g1 S.accFixedBases instW)` (adjustment 3: snapshots in accumulator renders carry the decoded accumulator); `GenericX S H ms instW inst := ∀ Snap, snapshotOf … (accOf S instW) = .ok Snap → ChallengesGood vk Snap` (snapshot form, not replay); `NoLogupPanic S H ms inst := prepareMsgs … ≠ .error (Fault.panic "proofs/src/plonk/logup.rs:460")` **def**.
- `EvaluatorFrame`, `tokenBase`, `frameValuation`, `FrameWellFormed` (pins VK window: the frame contains the program) **def**.

### 14. `Midfall/Lowering/Partials.lean` — M5/M7, finalPairing pulled forward
- `Reverted`, `Permissive product calls`, `mainScope`, `PartialSound`, `PartialProgress` **def** (∀-runs over `hoist S.main :: outer`, pre = `Inv … q.pre`, post = `(halt ∧ Reverted) ∨ (normal ∧ Inv next ∧ extra)`).
- `PartialSpecs S E params sG2gen encG2 product : Prop` fields: `vkLoading_sound/_progress`, `transcriptParser_*`, `lagrange_sound` (extra: `x^n ≠ 1` — the contract proves it) `/lagrange_progress (ChallengesGood)`, `quotientLin_sound (NoLogupPanic-derived)` `/_progress`, `pcs_*`, `finalPairing_sound (Holds; extra success = 1)`, `finalPairing_progress (check = true)`, `traceReturn_sound`. Each stated over the per-phase prefix snapshot.
- `finalPairing_sound_noAcc`, `finalPairing_progress_noAcc`, `finalPairing_sound_acc` (alphaOf preimage = 0x1000 batch buffer; `hkec`), `traceReturn_spec` **thm-hole** (statements concrete over `S.blk`; proofs after P-13 + P-BR).

### 15. `Midfall/Lowering/Qvm.lean` — M6
- `qvmFrModulus_eq_r` **rfl/decide**; `qvmToFr` + `_add/_mul/_neg/_injOn` **thm-hole**.
- `Valuation`, `memKey` (wraps `(1+t) % 256`, `addr % 2^32`), `evalExprρ`, `memOfρ`, `NoMiss`, `CacheConsistent`, `leafKeys`, `evalQuotientExpr_memOfρ (hS)` **def/thm-hole**.
- `denoteLin/denoteLimbShape/denoteModarith7`, `shapePtrsU16`, `modarith7WellFormed`, `RecognizersSound r` (pow5, limb, limbSub with `matched ≠ []`, modarith7), `noShapeRecognizers_sound` **rfl**.
- `exprBounded`; `qvm_compile_correct_identity (hr) (hb) (hemit = .ok) (hconsts) (hcompact) (hseg) (ρ) : ∃ v mem', evalQuotientIdentity seg consts (memOfρ ρ (leafKeys e)) = .ok (v, mem') ∧ evalExprρ ρ e = .ok v` **thm-hole** (values only — attack fix).
- `buildItems/buildPlan` **def** (local plan-items driver); `qvm_compile_correct_certifier`, `qvm_compile_correct_program`, `builder_segments_total` (D-P20 item 2 restated over `.readPastEnd/.constSlotOutOfRange`) **thm-hole**.

### 16. `Midfall/Lowering/QvmFold.lean` — M6
- `expandItem/globalIdentities/qvmFrPow/FoldState/foldStep/quotientFold`, `SelectorFoldConsistent`, `IdentityCorrespondence` **def**; `quotientFold_matches_linearization (hcons) (hvals) (hcorr) (hq)` **thm-hole**.

### 17. `Midfall/Lowering/Obligations.lean` — M7/M8 (+ derived theorems)
- `LoweringCorrect S product g2 : Prop` fields (all assume `S.Supported S.o₀`):
  - `verifier_sound` (any `mem₀` with `∀ a ≥ 0x80, mem₀ a = 0` or the g1_identity window zero; `permissive`; any gas; `Holds`; `DeploymentW`; `NoLogupPanic`) → `returnData = abiTrue ∧ LeanAccepts`.
  - `verifier_complete` (`honestCalls`, `ofFun` gas; `GenericX`; `EnvAgrees.omegaOrder/domainN`; `toEip 1 = zeros`) → `∃ run ∧ ∀ run, view = returnView`.
  - `only_two_outcomes` (**hypothesis `cd.extract 0 4 = fnSigVerifyProof`**).
  - `ir_refines (hir) (hloc : WorldLocal c) (gas := ofFun g₀) : ObsEquiv (RunContractIR …) (RunShell …)`.
  - `render_eq_print` structural only: `∀ ast, S.astOfMain o = some ast → stmtsBeq ast L.main = true` (text conjunct dropped).
  - `end_to_end_noAcc (cfg.accumulator = none) (hn : inst.size = cfg.numInstances) (hp : p ≤ 2^256) (compressedRoundtrip) (GenericX ∧ NoLogupPanic)`: `verifyNative … = .ok () ↔ ∃ cd, (S.repackProof π |>.mapError fromRepackError >>= encodeCalldata · inst) = .ok cd ∧ (∃ obs, RunContractIR …) ∧ ∀ obs, … view = returnView`.
  - `partials : PartialSpecs S …`.
  - `qvm_yul_refines` (FrameWellFormed; static; output = `outputBytes magic (quotientFold …)` ∨ revert); `qvm_validated_noBoundsFault`, `qvm_validated_windows` (validator abstract, P-09e); `points_subgroup_checked` (semantic, call trace); `vkDigest_slot0`; `repackProof_faithful`, `encodeCalldata_faithful` (P-12 equalities); `accFixedBases_producer`; `readScheduleAgrees`.
- Theorems: `lowering_equivalence` (3 conjuncts derived via `ir_refines` + `shell_unfolds`) **thm-hole (provable-now)**; `lowering_equivalence_noAcc` **thm-hole (provable-now)**; `end_to_end_acc_complete` (adjustment 4: the one-way accumulator-mode corollary Moonlight needs, from `contractRef_acc_complete` + `verifier_complete` + `ir_refines` + the calldata lemmas) **thm-hole**; `contractRef_noAcc_of_semanticEquivalence` **rfl** (reuses the untracked lemma — commit `SemanticEquivalence.lean` first); `verifyNative_iff_msgs_codec (hc : compressedRoundtrip)` **thm-hole**.
- Non-vacuity gates next to the structure: `example : realSurface.Supported realSurface.o₀` (fixture Surface built from YulGolden ASTs), `#eval (realSurface.astOfMain o₀).isSome -- expect true`, trace-render refutation KAT for `only_two_outcomes`.

### 18. Edits
- `Midfall.lean`: import every new module (Contracts before Bridge; Bridge before Surface).
- `SORRY.md`: regenerate; `scripts/gen_sorry.sh`: owner arms (`Midfall/Yul/*` → "M4-Lean (P-BR)", `Midfall/Assumptions/*` → "named hypothesis / Phase 4a", `Midfall/Lowering/*` → "M5-M8 semantic equivalence (this plan)").
- `scripts/checks.sh:14`: `listed=$(… | sort -t: -k1,1 -k2,2n)`.
- `docs/REVIEW.md`: R-51 logup soundness twin; R-52 `fixedBases` "-G" identity; R-53 frozen trio (findings 1-3); R-54 `repack_spec` iff false + `.pointPair` round trip false; R-55 attack findings (BUILD_ID getter, callvalue, immutable link, g1_identity window, WorldLocal).
- `docs/design.md`: D-P21 (statement architecture D1/D2), record D3/D4/D5/D7/D8/D11 readings as adopted-pending-sign-off.
- `docs/plans/README.md`: standing note on `checks.sh` sort fix and the Vk transitive-import rule.
- Commit `Lowering/SemanticEquivalence.lean` (currently untracked, unbuilt).

## Staging (each stage ends with `lake build` + `bash scripts/checks.sh` green)

0. Baseline: `lake build` whole project; `#check @Midfall.Halo2.decodeAcc`; commit `SemanticEquivalence.lean`; CI script edits (checks.sh sort, gen_sorry arms).
1. `Yul/Contracts.lean`, `Yul/Bridge.lean`, `Assumptions/{Codec,Eip2537}.lean`.
2. `Lowering/{AccEncoding,Accumulator,VkDigest,Calldata}.lean`.
3. Exec refactor + `Lowering/{Checkpoint,Snapshot,Inv}.lean` (KAT tokens unchanged).
4. `Lowering/{Surface,Partials}.lean` with the fixture Surface and non-vacuity gates.
5. `Lowering/{Qvm,QvmFold}.lean`.
6. `Lowering/Obligations.lean`; SORRY.md regen; docs entries; `#print axioms` sweep.

Estimated size: ~3,800 Lean lines + ~200 moved. The scratchpad design files hold the
full sketches; the attack file's FIX lines override them.

## Proof plan (order per PLAN 10 / 14.5; estimates are for chained agent time)

| step | milestone | what | prerequisites | key lemmas | est | risks / evidence |
|---|---|---|---|---|---|---|
| P0 | now | Zero-dependency algebra: `decideBool_eq_true_iff`, `MSMKZG.eval_*`, `dualMsm_check_iff_contract`, D-P16 (a)-(d), `feToU256_frToRepr`, `qvmFrModulus_eq_r` + `qvmToFr_*`, `repackedLen_mod32`, `frOfRepr_frToRepr`, `toExec_*` | stage 2 built | byte lemmas (`natToBytesLowFirst_size`, `bytesToWordLE_natToBytesLE`, `bytesFromNats_bytesToNats`) | 3 d | ZMod 17 counterexamples in the `dualMsm_scale_check` style; `usizeMax` example; `#print axioms` |
| P1 | M4-Lean | Bridge: `dialect_deterministic` (op split), `Run.det`, `RunCommitted.det`, `twoResponses_nondet`, `keccakOf_invariant` (Step induction), `honestRelations_keys`, `honestCalls_functional`, `Run_worldEq_of_noWriters` | stage 1 | — | 3 d | `cases` on Step at the open dialect needs `change` to the match form; BitVec literal arithmetic via `norm_num` |
| P2 | M4-Lean | ∀-runs layer: inversion lemmas, `cons_split`, `append`, `block`, `cond`, `switch`, `callUser`, `countdown_or_halt`, `of_det`; constant-substitution pass `substConsts_run` | stage 1 | — | 4 d | dependent elimination on indexed Step (generalize indices); 7 loop arms |
| P3 | Phase 4a | S5 + lift: `batched_complete`, `batched_atMostOneRoot`, `exists_zmod_smul_generator`, `prepareMsgs_wf` (lockstep channels), `modexpInv_correct` | P0 | `msmSpecific_append`, `smul_left_injective` | 3 d | mathlib names to `#check` (`Int.cast_smul_eq_zsmul`, `smul_eq_zero`); `[1]` shortcut case split |
| P4 | M5 | Exec refactor gate + `snapshotOf_prepareMsgs`; `Inv_mono`; `ptrAddr_new_theta`; Inv satisfiability/perturbation gates | stage 3 | — | 3 d | all KAT tokens unchanged; conformance replay identical |
| P5 | pulled-forward | `finalPairing_sound_noAcc/_progress/_acc`, `traceReturn_spec` for the concrete blocks | **P-BR** (Bridge is this plan), **P-13 first two partials** (`AssemblyHelpers.yul`, `FinalPairing.yul` as `Block EVM.Op`), P1-P3 | `ec_pairing_contract`, `mcopy_frame_bytes`, `staticcall_pairing_inv`, `fail_reverts`, `alpha_preimage_bytes`, `keccak_mod_r_eq_alphaOf`, `g1msm_then_g1add_slot` | 6-10 d | ~10 memory lemmas (copyWithin/loadWord disjointness) not in vendor; MF-4 both failure classes map to revert. Evidence: swapping the call-site args breaks the proof at `pairing2`; constant-true `product` contradicts `hNonDeg` |
| P6 | M5 | Codec/accumulator: `decodeAcc_injective`, `decodeAcc_encode`, `decodeAcc_encode_pointPair` (deployed shape), `contractRef_acc_complete`, `verifyNative_iff_msgs_codec`; calldata: `proofLen_eq_repackedLen`, `calldata_roundtrip`, `calldata_canonical`, `repack_spec_wire`, `repack_spec_of_decodeRust`, `points_subgroup_checked_generator` | P0, P3, **P-12** for `repackProof_faithful`/`encodeCalldata_faithful` | `transcript_log_concat` (largest single item; shared with `verifyNative_iff_msgs_codec`), `decodeSlots_encode`, `loadAccPoint_flag0/1`, `accMapInsert_fold_*` | 10 d | `fromProtocol` tiling induction over 10 cursor steps; `decodeAcc` `-s` elaboration. Evidence: R-20 rule, pins against the poseidon dump (4484 B, 0x10e0, 0x1140) and `keccak256("")`, never self-round-trips |
| P7 | M5 | Early partials: `vkLoading`, `transcriptParser`, `lagrange` (sound + progress) | **P-13** ASTs, **P-4a** domain facts, P2, P4 | `mstore_sequence_image`, `calldata_shape_exact`, `squeeze_to_eq_squeezeChallenge`, `common_uncompressed_g1_eq_common`, `x3_mask_eq_truncate`, `parser_consumes_exactly`, `xn_by_squaring`, `denoms_window`, `batch_invert_contract`, `lIRange_eq_contract`, `instance_eval_eq` | 3-4 w | ~12 parser loops, each via `countdown_or_halt` with the `ProofReadPlan` order; index bijection between Lean's two `lIRange` calls and the fused denominator array |
| P8 | M6 | QVM: `evalQuotientExpr_memOfρ`, shape denotation ↔ byte decoders, `emitExpr_correct` (fuel induction, 4 peepholes under `RecognizersSound`), compaction lemmas, `qvm_compile_correct_identity/_certifier/_program`, `builder_segments_total`, `quotientFold_matches_linearization` | stage 5, **P-09f** (recognizer soundness instances), **P-10** (`SelectorFoldConsistent` discharge) | `foldRangeIdxM_induction`, `identityExpr_bytes_append`, `emitFuel_adequate`, `compactQuotientRuns_segments/_value`, `horner_reverse`, `bucket_horner_with_gaps` | 3 w | 40 builder panic sites; (slot,ptr) operand order; `Selector.index = fixed column index` is an unpinned Rust invariant (potential review item). KATs: ≥2 main and ≥2 selector identities interleaved (R-30 rule) |
| P9 | M6/M7 | `quotientLin_*` (needs **P-09h** emitter + evaluator partials), `pcs_*` (needs an AST-producing PCS emitter or yul% quotes of `Kzg.computations` text — R-42 option A; flagged) | P7, P8, P-13 | `linearization_prep`, `quotientEval_eq_linCom_eval` (R-16/R-19), `buckets_eq_groupedAdd`, truncated-powers lemmas, block-6 slot equations via `Holds.g1Msm1/g1Add` | unestimated (ROADMAP policy) | pcs scratch at 0x1000 is phase-scoped: `Inv .pcs` must not mention it |
| P10 | M7 | Composition: `verifier_sound/complete/only_two_outcomes` via `StmtsContractAll.append` over the seven slices; `snapshot_exists_of_nopanic`; `lowering_equivalence_noAcc`; `end_to_end_noAcc`; `end_to_end_acc_complete` (one direction) | P5-P9, **P-11/P-12** | `main_block_is_concat`, `Inv_start_of_initState` | ≥3 w | R-5/R-12 latent Exec panics must be unreachable under Supported or matched by a revert; R-15 lazy zips pinned by Supported sizes |
| P11 | M8 | `memoryguard` (and `setimmutable` for creation code) in the vendored dialect; `ImportSolcIR` yul% generation; `ShellModel`; `irCheck` (α-equivalence modulo constant substitution and solc renames, fuel-based); `ir_refines` as view-level simulation; `lowering_equivalence` | P10, D-P15 | `irCheck_sound`, `shell_unfolds` | unestimated | only one `hex"…"` literal, 76 user functions; planted rename must fail `irCheck` |
| P12 | M9 | S5 `alpha_batching_sound`, then S2-S4, S1, S7 (uses `lowering_equivalence`) | P3, P11, `security.tex` (D-P14 x1/x4 rows) | — | unestimated | `Pr{…}[…]` VCVio notation; ArkLib sorries excluded from closures |
| P13 | M10/M11 | `direct_correct`; `deployed_equivalence` (needs regenerated Moonlight artifact, R-36) | P10 | — | unestimated | — |

ROADMAP policy: P7-P13 numbers are lower bounds; the first calibration point is P5.

## Verification (for the implementation pass)

1. `cd formal && lake build` green from a clean baseline (stage 0 proves the tree builds
   at all; record time and any `lake exe cache get`).
2. `bash scripts/checks.sh` green: frozen hash unchanged, register in sync (after the sort
   fix), no `native_decide` outside Instances/, no orphans, golden provenance, Instances
   confinement, every `#eval … -- expect` passes.
3. `#check @…` for every declaration the designs cite but that has no local olean
   (`decodeAcc`, `Spec.accepts` binders, `Generator.AccumulatorEncoding` mutual block).
4. `#print axioms` on every new theorem (including the rfl-level ones) ⊆
   `propext, Classical.choice, Quot.sound`; file a note if `orderOf`/mathlib adds more.
5. Non-vacuity gates run by CI: toy codec satisfies `G1CodecLaws`; `usizeMax` D-P16
   example; `twoResponses_nondet`; `isRevertOrHalt` refutes `.stop`; `abiTrue` shape;
   `Inv` satisfiable on a hand-built state and refuted by one swapped word; fixture
   Surface satisfies `Supported o₀`; trace-render block refutes `only_two_outcomes`.
6. Exec refactor gate: every pre-existing `#eval` token in `Verifier.lean`,
   `MultiOpen.lean`, `Native.lean` unchanged; `lake exe midfall-conformance` (if runnable)
   replays identically.
7. Perturbation evidence recorded in each file header (author-run, per PLAN 12 while
   reviews are off): which wrong implementation each statement rejects.

## Reported, not fixed (owners named)

- Frozen trio re-pin (findings 1-3): user sign-off; D-P9-style.
- `Midfall.Halo2.fixedBases` "-G" identity (finding 7): separate Exec patch with KAT.
- `.pointPair` accumulator encoder: now IN scope as `encodeAccPublicInput` (adjustment 1); its Rust source
  (`circuits/src/ecc/foreign/ecc_chip.rs:226-239`) must be read before the definition is written.
- `Spec.accepts` needs `E` (finding 2): Phase 4.
- P-4a `zeta_order` undischargeable for `fc17`: P-4a owner.
- `Selector.index = fixed-column index` at `linearization/verifier.rs:84`: pin as a Rust
  invariant or open a review item.
- Logup definite-value exploitability (finding 5): S-level question for M9; also raise
  `logup.rs:460` upstream as an unnecessary panic.
- `Kzg.computations` emits text: an AST-producing emitter (or yul% quotes) is a
  prerequisite for `pcs_spec` proofs, not for its statement.

## Full statements (Lean sketches)

Conventions for every block: the variable block is the frozen one
(`{p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group …] [PrimeOrderWith … p]
[Module (ZMod p) (Additive …)] [P : AdmissiblePairing G₁ G₂ Gₜ]`) unless a file says
otherwise; `sorry` lines are the registered holes; `-- SKETCH` marks a name or binder
not verified against a built module; doc comments are abbreviated here and are written
in full (with the finding citations) in the implementation.

### A. `Midfall/Yul/Contracts.lean`

```lean
import YulSemantics.BigStep
import YulSemantics.Contract
import YulSemantics.Determinism

namespace YulSemantics
variable {D : Dialect} [DecidableEq D.Value]

/-- Partial correctness over EVERY derivation (the vendored `StmtsContract`, Contract.lean:94,
    is existential and says nothing about all runs under a relational `calls`). -/
def StmtsContractAll (funs : FunEnv D) (stmts : Block D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmts D funs V st stmts V' st' o → post V st V' st' o

def StmtContractAll (funs : FunEnv D) (s : Stmt D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmt D funs V st s V' st' o → post V st V' st' o

def ExprContractAll (funs : FunEnv D) (e : Expr D.Op)
    (pre : VEnv D → D.State → Prop) (post : VEnv D → D.State → EResult D → Prop) : Prop :=
  ∀ V st, pre V st → ∀ r, EvalExpr D funs V st e r → post V st r

def RunContractAll (program : Block D.Op) (pre : D.State → Prop)
    (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ st0 V' st' o, pre st0 → Run D program st0 V' st' o → post st0 V' st' o

/-- Non-vacuity: the layer really quantifies over derivations. -/
example : ¬ StmtsContractAll (D := EVM.evm) [] [] (fun _ _ => True) (fun _ _ _ _ _ => False) :=
  fun h => h [] EVM.EvmState.init trivial [] _ .normal Step.seqNil

theorem Step.stmts_cons_inv {funs : FunEnv D} {V st s ss V' st' o}
    (h : ExecStmts D funs V st (s :: ss) V' st' o) :
    (∃ V₁ st₁, ExecStmt D funs V st s V₁ st₁ .normal ∧ ExecStmts D funs V₁ st₁ ss V' st' o) ∨
    (ExecStmt D funs V st s V' st' o ∧ o ≠ .normal) := by
  cases h with
  | seqCons h₁ h₂ => exact Or.inl ⟨_, _, h₁, h₂⟩
  | seqStop h₁ hne => exact Or.inr ⟨h₁, hne⟩

theorem Step.stmts_append_inv {funs : FunEnv D} {V st ss₁ ss₂ V' st' o}
    (h : ExecStmts D funs V st (ss₁ ++ ss₂) V' st' o) :
    (∃ V₁ st₁, ExecStmts D funs V st ss₁ V₁ st₁ .normal ∧ ExecStmts D funs V₁ st₁ ss₂ V' st' o) ∨
    (ExecStmts D funs V st ss₁ V' st' o ∧ o ≠ .normal) := by sorry

/-- Halting-head cons: the per-partial shape `reverted ∨ Inv next`. -/
theorem StmtsContractAll.cons_split {funs : FunEnv D} {s : Stmt D.Op} {ss : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (head : StmtContractAll funs s pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (tail : ∀ V st, pre V st →
      StmtsContractAll funs ss mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (s :: ss) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases head V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne, _⟩
    · exact tail V st hpre V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne
  · rcases head V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hpost⟩
    · exact absurd heq hne
    · exact hpost

/-- Each partial is a SLICE of the main block, so sequencing is over `++`. -/
theorem StmtsContractAll.append {funs : FunEnv D} {ss₁ ss₂ : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h₁ : StmtsContractAll funs ss₁ pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (h₂ : ∀ V st, pre V st → StmtsContractAll funs ss₂ mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (ss₁ ++ ss₂) pre post := by sorry

theorem StmtsContractAll.block {funs : FunEnv D} {body : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h : StmtsContractAll (hoist D body :: funs) body pre
      (fun V st V' st' o => post V st (restore V V') st' o)) :
    StmtContractAll funs (.block body) pre post := by sorry

theorem StmtContractAll.cond {funs : FunEnv D} {e : Expr D.Op} {body : Block D.Op}
    {pre : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (hcond : ∀ V st cv st₁, pre V st → EvalExpr D funs V st e (.vals [cv] st₁) →
      (cv = D.zero → post V st V st₁ .normal) ∧
      (cv ≠ D.zero → ∀ V' st' o, ExecStmt D funs V st₁ (.block body) V' st' o → post V st V' st' o))
    (hhalt : ∀ V st st₁, pre V st → EvalExpr D funs V st e (.halt st₁) → post V st V st₁ .halt) :
    StmtContractAll funs (.cond e body) pre post := by sorry

-- SKETCH: switch/call shapes follow the Step rules for `.switch` (selectSwitch) and callOk/callHalt
theorem StmtContractAll.switch {funs : FunEnv D} {e : Expr D.Op} {cases : List (Literal × Block D.Op)}
    {dflt : Option (Block D.Op)} {pre post}
    (hsel : ∀ V st cv st₁, pre V st → EvalExpr D funs V st e (.vals [cv] st₁) →
      ∀ V' st' o, ExecStmt D funs V st₁ (.block (selectSwitch D cv cases dflt)) V' st' o → post V st V' st' o)
    (hhalt : ∀ V st st₁, pre V st → EvalExpr D funs V st e (.halt st₁) → post V st V st₁ .halt) :
    StmtContractAll funs (.switch e cases dflt) pre post := by sorry

theorem ExprContractAll.callUser {funs : FunEnv D} {f : Ident} {args : List (Expr D.Op)}
    {decl cenv} (hlook : lookupFun funs f = some (decl, cenv))
    {pre : VEnv D → D.State → Prop} {post : VEnv D → D.State → EResult D → Prop}
    (hargs : ∀ V st, pre V st → ∀ vals st₁, EvalArgs D funs V st args (.vals vals st₁) →
      ∀ V' st' o, ExecStmt D cenv ((decl.params.zip vals) ++ bindZeros D decl.rets) st₁ (.block decl.body) V' st' o →
        (o = .halt → post V st (.halt st')) ∧
        (o ≠ .halt → post V st (.vals (decl.rets.map fun r => (VEnv.get V' r).getD D.zero) st')))
    (hargsHalt : ∀ V st st₁, pre V st → EvalArgs D funs V st args (.halt st₁) → post V st (.halt st₁)) :
    ExprContractAll funs (.call f args) pre post := by sorry

/-- Loops whose body may halt (`fail(...)` inside Lagrange/TranscriptParser loops). -/
theorem ExecLoopAll.countdown_or_halt {funs : FunEnv D} {cond : Expr D.Op} {post body : Block D.Op}
    {Inv : Nat → VEnv D → D.State → Prop} {Q : VEnv D → D.State → Prop}
    (done : ∀ V st, Inv 0 V st → ∀ cv st', EvalExpr D funs V st cond (.vals [cv] st') → cv = D.zero ∧ Inv 0 V st')
    (step : ∀ n V st, Inv (n + 1) V st →
      (∀ cv stc, EvalExpr D funs V st cond (.vals [cv] stc) → cv ≠ D.zero ∧
        ∀ Vb stb ob, ExecStmt D funs V stc (.block body) Vb stb ob →
          ((ob = .normal ∨ ob = .continue) →
             ∀ Vp stp op, ExecStmt D funs Vb stb (.block post) Vp stp op → op = .normal ∧ Inv n Vp stp) ∧
          (ob = .halt → Q Vb stb)) ∧
      (∀ stc, EvalExpr D funs V st cond (.halt stc) → Q V stc)) :
    ∀ n V st, Inv n V st → ∀ V' st' o, ExecLoop D funs V st cond post body V' st' o →
      (o = .normal ∧ Inv 0 V' st') ∨ (o = .halt ∧ Q V' st') := by sorry

/-- The existential contract plus determinism gives the universal one (honest calls). -/
theorem StmtsContractAll.of_det {funs : FunEnv D} {stmts pre post}
    (hdet : ∀ op, D.Deterministic op) (h : StmtsContract funs stmts pre post) :
    StmtsContractAll funs stmts pre post := by sorry
end YulSemantics
```

### B. `Midfall/Yul/Bridge.lean` (no `Midfall.Halo2.Exec` import)

```lean
import YulSemantics
import YulSemantics.Dialect.EVM
import YulSemantics.Contract
import YulSemantics.Observation
import YulSemantics.Object
import YulSemantics.ObjectRun
import Midfall.Common.Bytes
import Midfall.Common.Keccak
import Midfall.Yul.Externals
import Midfall.Yul.Contracts

namespace YulSemantics.EVM
/-- D-P10's determinism condition on `calls`: at most one response per request and pre-state. -/
def ExternalCalls.Functional (c : ExternalCalls) : Prop :=
  ∀ req st r₁ r₂, c.Call req st r₁ → c.Call req st r₂ → r₁ = r₂
def ExternalGas.Functional (g : ExternalGas) : Prop :=
  ∀ st g₁ g₂, g.Gas st g₁ → g.Gas st g₂ → g₁ = g₂
/-- Responses depend on the world only, not on caller memory (attack fix for ir_refines). -/
def ExternalCalls.WorldLocal (c : ExternalCalls) : Prop :=
  ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' → (c.Call req st r ↔ c.Call req st' r)
end YulSemantics.EVM

namespace Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

@[reducible] def Dialect (calls : ExternalCalls) (gas : ExternalGas) : YulSemantics.Dialect :=
  evmWithExternal calls ExternalCreates.none gas

def Run (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (st' : EvmState) (o : Outcome) : Prop :=
  YulSemantics.Run (Dialect calls gas) prog st0 V' st' o

def RunCommitted (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run calls gas prog st0 V' st' o ∧ stObs = committedState st0 st'

theorem ofFun_functional (f : EvmState → U256) : ExternalGas.Functional (ExternalGas.ofFun f) := by
  intro st g₁ g₂ h₁ h₂; simp [ExternalGas.ofFun] at h₁ h₂; rw [h₁, h₂]

theorem dialect_deterministic {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional) (op : Op) : (Dialect c g).Deterministic op := by
  sorry -- op split: call-family via externalCall + hc; .gas via hg; create* static halt only; rest stepOp

theorem Run.det {c g prog st0 V₁ st₁ o₁ V₂ st₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : Run c g prog st0 V₁ st₁ o₁) (h₂ : Run c g prog st0 V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  YulSemantics.Run.det (dialect_deterministic hc hg) h₁ h₂

theorem RunCommitted.det {c g prog st0 V₁ s₁ o₁ V₂ s₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : RunCommitted c g prog st0 V₁ s₁ o₁) (h₂ : RunCommitted c g prog st0 V₂ s₂ o₂) :
    V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  obtain ⟨t₁, r₁, rfl⟩ := h₁; obtain ⟨t₂, r₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := Run.det hc hg r₁ r₂; exact ⟨rfl, rfl, rfl⟩

/-- hc is load-bearing: a two-response relation yields two runs with different memories. -/
theorem twoResponses_nondet :
    let c : ExternalCalls := ⟨fun req st r => req.target = 0x0f ∧ r.world = CallWorld.ofState st ∧
      r.returndata = [] ∧ (r.success = true ∨ r.success = false)⟩
    ∃ V₁ st₁ V₂ st₂, Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₁ st₁ .normal ∧
      Run c (ExternalGas.ofFun fun _ => 0)
        (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₂ st₂ .normal ∧
      st₁.memory 31 ≠ st₂.memory 31 := by sorry

/-- Y-2: the hash is `env.keccakOf`; this is how a Midfall `Hash` is installed. -/
def hashOfBytes (H : Midfall.Bytes → Midfall.H256) : List UInt8 → U256 :=
  fun l => H (ByteArray.mk l.toArray)
def withKeccak (H : Midfall.Bytes → Midfall.H256) (st : EvmState) : EvmState :=
  { st with env := { st.env with keccakOf := hashOfBytes H } }

def Res.state {D : YulSemantics.Dialect} : Res D → D.State
  | .eres (.vals _ st) => st | .eres (.halt st) => st | .sres _ st _ => st

theorem keccakOf_invariant {c g funs V st code res}
    (h : Step (Dialect c g) funs V st code res) : (Res.state res).env.keccakOf = st.env.keccakOf := by
  sorry -- Step induction; CallWorld.install/finishSelfdestruct leave keccakOf alone
theorem RunCommitted_keccakOf {c g prog st0 V' stObs o} (h : RunCommitted c g prog st0 V' stObs o) :
    stObs.env.keccakOf = st0.env.keccakOf := by sorry

structure Obs where
  state : EvmState
  outcome : Outcome

/-- Caller-visible projection: memory, activeWords and the VEnv are NOT observable. -/
structure ObsView where
  outcome : Outcome
  halted : Option (HaltKind × List UInt8)
  storage : U256 → U256
  transient : U256 → U256
  logs : List LogEntry
  selfdestructs : List (U256 × Bool)
  balanceOf : U256 → U256
  extCodeOf : U256 → List UInt8
  nonceOf : U256 → U256
  storageOf : U256 → U256 → U256
  transientOf : U256 → U256 → U256

def Obs.view (o : Obs) : ObsView :=
  { outcome := o.outcome, halted := o.state.halted, storage := o.state.storage,
    transient := o.state.transient, logs := o.state.logs, selfdestructs := o.state.selfdestructs,
    balanceOf := o.state.env.balanceOf, extCodeOf := o.state.env.extCodeOf,
    nonceOf := o.state.env.nonceOf, storageOf := o.state.env.storageOf,
    transientOf := o.state.env.transientOf }

def Obs.isReturn (o : Obs) : Prop := ∃ d, o.state.halted = some (.ret, d)
def Obs.returnData (o : Obs) : List UInt8 :=
  match o.state.halted with | some (_, d) => d | none => []
/-- Non-committing halts only: stop/selfdestruct/running off the end are excluded. -/
def Obs.isRevertOrHalt (o : Obs) : Prop := ∃ k d, o.state.halted = some (k, d) ∧ k.commits = false

def WorldEq (a b : EvmState) : Prop :=
  a.storage = b.storage ∧ a.transient = b.transient ∧ a.logs = b.logs ∧
  a.selfdestructs = b.selfdestructs ∧ a.env.selfBalance = b.env.selfBalance ∧
  a.env.balanceOf = b.env.balanceOf ∧ a.env.extCodeOf = b.env.extCodeOf ∧
  a.env.extCodeHashOf = b.env.extCodeHashOf ∧ a.env.nonceOf = b.env.nonceOf ∧
  a.env.storageOf = b.env.storageOf ∧ a.env.transientOf = b.env.transientOf
def Obs.worldUnchanged (st0 : EvmState) (o : Obs) : Prop := WorldEq st0 o.state

/-- The ONLY definition of abiTrue in the tree (TraceReturn.yul:70-72). -/
def abiTrue : List UInt8 := (Midfall.natToBytesBE 1 32).data.toList
def returnView (w : EvmState) : ObsView :=
  Obs.view ⟨{ w with halted := some (.ret, abiTrue) }, .halt⟩

theorem worldUnchanged_of_rollback {st0 st' : EvmState} {k d} (h : st'.halted = some (k, d))
    (hk : k.commits = false) : Obs.worldUnchanged st0 ⟨committedState st0 st', .halt⟩ := by
  simp [Obs.worldUnchanged, WorldEq, committedState_rollback h hk]

/-- Externals ↔ EVM request/response conversions. -/
def toYulKind : EVM.CallKind → Midfall.Yul.CallKind
  | .call => .call | .callcode => .callcode | .delegatecall => .delegatecall | .staticcall => .staticcall
def toYulReq (req : EVM.CallRequest) : Midfall.Yul.CallRequest :=
  { kind := toYulKind req.kind, gas := req.gas, target := req.target, value := req.value,
    input := ByteArray.mk req.input.toArray }
def ofOutcome (st : EvmState) (o : Midfall.Yul.CallOutcome) : CallResponse :=
  { success := o.success, returndata := o.returndata.data.toList, world := CallWorld.ofState st }
def failResp (st : EvmState) : CallResponse :=
  { success := false, returndata := [], world := CallWorld.ofState st }

/-- Target match on the 160-bit account key (EVMExec.lean:278); Externals.accepts compares full words. -/
def hits (r : Midfall.Yul.ExternalCallRelation) (req : EVM.CallRequest) : Bool :=
  accountKey req.target == accountKey r.address

def honestOf (rels : List Midfall.Yul.ExternalCallRelation) (req : EVM.CallRequest) (st : EvmState) :
    Option CallResponse :=
  (rels.find? (fun r => hits r req)).map fun r =>
    match r.respond (toYulReq req) with
    | some o => ofOutcome st o
    | none => failResp st

/-- Y-1: ONE ExternalCalls, a disjunction split by target. -/
def honestCalls (product : Midfall.Yul.PairingProduct)
    (evalAddr : U256) (evalRel : EVM.CallRequest → EvmState → CallResponse → Prop) : ExternalCalls :=
  ⟨fun req st resp =>
    (honestOf (Midfall.Yul.honestRelations product) req st = some resp) ∨
    (accountKey req.target = accountKey evalAddr ∧ evalRel req st resp)⟩

/-- Soundness relation: any failure allowed (gas unmodelled), a success must be honest, no world change. -/
def permissive (c : ExternalCalls) : ExternalCalls :=
  ⟨fun req st resp => resp.world = CallWorld.ofState st ∧ (resp.success = true → c.Call req st resp)⟩

theorem honest_le_permissive (c : ExternalCalls)
    (hw : ∀ req st r, c.Call req st r → r.world = CallWorld.ofState st) :
    ∀ req st r, c.Call req st r → (permissive c).Call req st r :=
  fun _ _ _ h => ⟨hw _ _ _ h, fun _ => h⟩

theorem honestRelations_keys (product : Midfall.Yul.PairingProduct) :
    (Midfall.Yul.honestRelations product).map (fun r => accountKey r.address) = [0x0b, 0x0c, 0x0f, 0x05] := by
  sorry -- norm_num on four BitVec literals (relationKats_ok is only #eval)

theorem honestCalls_functional (product) (evalAddr) (evalRel)
    (hev : ∀ req st r₁ r₂, evalRel req st r₁ → evalRel req st r₂ → r₁ = r₂)
    (hdisj : accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat)) :
    ExternalCalls.Functional (honestCalls product evalAddr evalRel) := by sorry

theorem honestCalls_worldLocal (product) (evalAddr) (evalRel)
    (hev : ∀ req st st' r, CallWorld.ofState st = CallWorld.ofState st' → (evalRel req st r ↔ evalRel req st' r)) :
    (honestCalls product evalAddr evalRel).WorldLocal := by sorry
theorem permissive_worldLocal (c : ExternalCalls) (hc : c.WorldLocal) : (permissive c).WorldLocal := by sorry

namespace Evaluator
/-- The frame the quotient evaluator's fallback runs in (staticcall, raw frame as calldata). -/
def calleeState (W : ExecEnv) (Lyt : Layout) (addr : U256) (st : EvmState) (req : EVM.CallRequest) : EvmState :=
  { EvmState.init with
    storage := st.env.storageOf addr, transient := st.env.transientOf addr,
    env := { Lyt.env with
      address := addr, caller := st.env.address, callvalue := 0, static := true,
      calldata := req.input, keccakOf := st.env.keccakOf,
      balanceOf := st.env.balanceOf, extCodeOf := st.env.extCodeOf, extCodeHashOf := st.env.extCodeHashOf,
      nonceOf := st.env.nonceOf, storageOf := st.env.storageOf, transientOf := st.env.transientOf } } -- SKETCH: copy the remaining block fields from W

def responseOf (st : EvmState) (stObs : EvmState) : CallResponse :=
  match stObs.halted with
  | some (.ret, d) => { success := true, returndata := d, world := CallWorld.ofState st }
  | some (.stop, _) => { success := true, returndata := [], world := CallWorld.ofState st }
  | some (.selfdestruct, _) => { success := true, returndata := [], world := CallWorld.ofState st }  -- commits (attack fix)
  | some (_, d) => { success := false, returndata := d, world := CallWorld.ofState st }
  | none => { success := true, returndata := [], world := CallWorld.ofState st }

/-- The evaluator slot: run the runtime block in the CLOSED dialect (it calls no precompile). -/
def rel (W : ExecEnv) (Lyt : Layout) (addr : U256) (rt : Block Op) :
    EVM.CallRequest → EvmState → CallResponse → Prop :=
  fun req st resp => ∃ V' st' o,
    YulSemantics.Run EVM.evm rt (calleeState W Lyt addr st req) V' st' o ∧
    resp = responseOf st (committedState (calleeState W Lyt addr st req) st')

theorem rel_functional (W Lyt addr rt) :
    ∀ req st r₁ r₂, rel W Lyt addr rt req st r₁ → rel W Lyt addr rt req st r₂ → r₁ = r₂ := by
  intro req st r₁ r₂ ⟨_, _, _, h₁, rfl⟩ ⟨_, _, _, h₂, rfl⟩
  obtain ⟨_, rfl, _⟩ := EVM.run_det h₁ h₂; rfl
end Evaluator

/-- Syntactic absence of world writers, fuel-bounded (R-37); exhaustion answers false. -/
def Op.isWriter : Op → Bool
  | .sstore | .tstore | .log0 | .log1 | .log2 | .log3 | .log4 | .selfdestruct
  | .create | .create2 | .call | .callcode | .delegatecall => true
  | _ => false
def noWritersFuel : Nat → Block Op → Bool := sorry -- SKETCH: mutual Expr/Stmt walker, `0 => false`
def NoWriters (b : Block Op) : Prop := ∃ n, noWritersFuel n b = true

/-- Only staticcalls and no writers ⇒ the world is untouched (finishCall never installs for staticcall). -/
theorem Run_worldEq_of_noWriters {c g prog st0 V' st' o}
    (hn : NoWriters prog) (h : Run c g prog st0 V' st' o) : WorldEq st0 st' := by sorry
end Midfall.Yul.Bridge
```

### C. `Midfall/Assumptions/Codec.lean`

```lean
import Midfall.Common.Codec
import Midfall.Common.Bytes
import Midfall.Assumptions.Pairing

namespace Midfall.Assumptions
open Midfall

/-- The G1 codec laws the accumulator and calldata statements consume. R-34: no Lean instance
    proves any of them and the BLS codec lives under Instances/ (D-P17), so each is a binder. -/
structure G1CodecLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip                       -- decoder-first, Codec.lean:106
  compressedRoundtrip : c.compressedRoundtrip         -- decoder-first, Codec.lean:113
  /-- encoder-first (deliberately absent from G1Codec, Codec.lean:97-105): the encoders here are OURS -/
  ofEip_toEip : ∀ Q : G₁, c.ofEip? (c.toEip Q) = some Q
  /-- EIP-2537 shape with in-field, non-(0,0) coordinates (AssemblyHelpers.yul:94-104; (0,0) under flag 0 rejected) -/
  eipShape : ∀ Q : G₁, Q ≠ 1 → ∃ x y : Nat, x < pBase ∧ y < pBase ∧ ¬ (x = 0 ∧ y = 0) ∧
    c.toEip Q = natToBytesBE 0 16 ++ natToBytesBE x 48 ++ natToBytesBE 0 16 ++ natToBytesBE y 48
  /-- identity ↔ 128 zero bytes (TranscriptProofParser.yul:36-46, AccumulatorHelpers.yul:137-140) -/
  toEip_one : c.toEip 1 = natToBytesBE 0 128
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  eipWidth : ∀ Q : G₁, (c.toEip Q).size = g1EipWidth

/-- Provable: canonical scalars round-trip through their LE repr. -/
theorem frOfRepr_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≤ 2 ^ 256) (x : Fr p) :
    frOfRepr? (p := p) (frToRepr x) = some x := by sorry

-- Non-vacuity (implementation): a toy codec over `Multiplicative (ZMod 17)` satisfies G1CodecLaws by
-- `decide`; `toEip := fun _ => natToBytesBE 0 128` violates eipShape; `ofEip? := fun _ => none`
-- violates ofEip_toEip.
end Midfall.Assumptions
```

### D. `Midfall/Assumptions/Eip2537.lean`

```lean
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Yul.Externals

namespace Midfall.Assumptions
open Midfall Midfall.Halo2 Midfall.Yul

/-- No G2 codec exists in Common; the generator's g2Repr ∘ g2ToU256s sits behind Vk.lean's
    Instances import, so the hypothesis layer takes an abstract 256-byte encoder. -/
structure G2Enc (G₂ : Type) where
  toEip : G₂ → Bytes

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- What EIP-2537 must deliver for the generated verifier, relative to the codecs. `product` is
    Externals' PairingProduct oracle (the Fp12 hole, Externals.lean:941). The frame is caller-
    ordered: ec_pairing lays out [lhs|G2|rhs|NEG_S_G2] (AssemblyHelpers.yul:284-287) and
    FinalPairing.yul:88 passes (PAIRING_RHS, PAIRING_LHS). Satisfiability is NOT demonstrable
    in-tree (the exponent model's toEip is not a curve point): this is PLAN 1's trusted-base row. -/
structure Eip2537.Holds (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop where
  g1Valid : ∀ Q : G₁, ∃ pt, g1Of? (c.toEip Q) = some pt ∧ g1PointMsmValid pt = true
  g2Valid : ∀ R : G₂, ∃ pt, g2Of? (c₂.toEip R) = some pt ∧ g2PointValid pt = true
  /-- two-pair PAIRING_CHECK ↔ additive pairing equation (the verifier never pairs more than two) -/
  pairing2 : ∀ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
    product (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) + P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) = 0
  /-- G1ADD (0x0b, 0x100-byte frame, R-21) -/
  g1Add : ∀ P₁ P₂ : G₁,
    g1AddOutput (ByteArray.append (c.toEip P₁) (c.toEip P₂)) = some (c.toEip (P₁ * P₂))
  /-- one-pair G1MSM (0x0c, interleaved 0xa0-byte record, R-21); scalar as the canonical word -/
  g1Msm1 : ∀ (Q : G₁) (s : Fr p),
    g1MsmOutput (g1MsmFrame [(c.toEip Q, wordToBytesBE (frWord s))]) = some (c.toEip (gsmul s Q))
  /-- soundness side: a frame the precompile accepts decodes (closes points_subgroup_checked's gap) -/
  g1Decodes : ∀ b : Bytes, (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
    ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-- Modexp.Holds is NOT an assumption: modexpOutput is computed. The inversion frame returns x⁻¹. -/
theorem modexpInv_correct (x : ℕ) (hx : 0 < x) (hr : x < blsR) :
    modexpOutput (modexpInvFrame x) = some (natToBytesBE ((x : ZMod blsR)⁻¹).val 32) := by
  sorry -- SKETCH: modexpInvFrame is the generated (x, r-2, r) frame; modPow + ZMod.pow_card_sub_two_eq_inv
-- KAT: #eval ((modexpOutput (modexpInvFrame 2)).map bytesToNatBE == some ((blsR + 1) / 2)) -- expect true
end Midfall.Assumptions
```

### E. `Midfall/Lowering/AccEncoding.lean`

```lean
import Midfall.Generator.Api
import Midfall.Halo2.Exec.Accumulator

namespace Midfall.Lowering
open Midfall Midfall.Halo2

/-- D-P16 kind map, generator → Exec stand-in. -/
def toExecKind : Midfall.Generator.AccumulatorEncodingKind → Midfall.Halo2.AccumulatorEncodingKind
  | .pointAndScalar => .pointAndScalar
  | .pointPair => .pointPair

/-- D-P16: the faithful generator encoding viewed as the Exec stand-in `decodeAcc` is typed over. -/
def toExec (e : Midfall.Generator.AccumulatorEncoding) : Midfall.Halo2.AccumulatorEncoding :=
  { offset := e.offset, numLimbs := e.numLimbs, numLimbBits := e.numLimbBits, kind := toExecKind e.kind }

theorem toExec_hasCarriedScalars (e : Midfall.Generator.AccumulatorEncoding) :
    (toExec e).hasCarriedScalars = e.hasCarriedScalars := by
  obtain ⟨_, _, _, k⟩ := e; cases k <;> rfl

/-- (d): agree whenever the generator does not hit its api.rs:104 division-by-zero panic. -/
theorem toExec_coordinateWords (e : Midfall.Generator.AccumulatorEncoding) (h : e.numLimbBits ≠ 0) :
    e.coordinateWords = .ok (toExec e).coordinateWords := by sorry
theorem toExec_fixedPayloadWords (e : Midfall.Generator.AccumulatorEncoding) (h : e.numLimbBits ≠ 0) :
    e.fixedPayloadWords = .ok (toExec e).fixedPayloadWords := by sorry

/-- (c), unconditional: the usize::MAX sentinel at api.rs:137 makes the tail bound unfireable. -/
theorem toExec_fullyCollapsed (e : Midfall.Generator.AccumulatorEncoding) :
    e.fullyCollapsedPublicInputWords.toOption = (toExec e).fullyCollapsedPublicInputWords := by sorry

/-- (a). The bound is necessary: the saturating add (api.rs:160) accepts at n = usize::MAX what
    Exec's unbounded ≤ rejects. -/
theorem toExec_validFor (e : Midfall.Generator.AccumulatorEncoding) (n : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    (e.validateForNumInstances n).isOk = (toExec e).validFor n := by sorry

/-- Counterexample gate for the bound (hazard 3 / F-3). -/
example :
    ((Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56).validateForNumInstances
        Midfall.Generator.usizeMax).isOk = true ∧
    (toExec (Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56)).validFor
        Midfall.Generator.usizeMax = false := by decide  -- fallback: rfl per conjunct

/-- (b): under the usize bound the wrapping usizeAdd/usizeSub equal Nat arithmetic. -/
theorem toExec_fixedScalarCount (e : Midfall.Generator.AccumulatorEncoding) (n t : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    e.fixedScalarCount n = .ok t ↔ (toExec e).fixedScalarCount n = some t := by sorry
end Midfall.Lowering
```

### F. `Midfall/Lowering/Accumulator.lean`

```lean
import Midfall.Lowering.AccEncoding
import Midfall.Assumptions.Codec
import Midfall.Halo2.Exec.Accumulator
import Midfall.Halo2.Exec.Native
import Midfall.Lowering.Types
import Midfall.Halo2.Spec.Lemmas

namespace Midfall.Lowering
open Midfall Midfall.Halo2

/-- R-25 projection: the tail window from `enc.offset`, with the coordinate words of an
    identity-flagged point zeroed (AccumulatorHelpers.yul:130-141 never reads them); flag
    words, carried scalars and tail scalars kept verbatim. -/
def accWords (enc : Midfall.Halo2.AccumulatorEncoding) (inst : Array Word256) : Array Word256 :=
  let tail := inst.extract enc.offset inst.size
  let cw := enc.coordinateWords
  let rhsSrc := enc.pointWords + (if enc.hasCarriedScalars then 1 else 0)
  let zeroCoords (a : Array Word256) (src : Nat) : Array Word256 :=
    if a.getD (src + 2 * cw) 0 = 1 then
      (List.range (2 * cw)).foldl (fun acc j => acc.setD (src + j) 0) a   -- SKETCH: setD name
    else a
  zeroCoords (zeroCoords tail 0) rhsSrc

/-- PLAN 9.5 decodeAcc_injective in its R-25 form. -/
theorem decodeAcc_injective {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₂ = some a) :
    accWords enc i₁ = accWords enc i₂ := by sorry
-- hrt: both flag-0 slots rebuild toEip L; hone: otherwise the identity has a flag-1 and a flag-0
-- encoding with different accWords; hnodup: accMapInsert overwrites duplicate names (:466-474).

/-- Contract-convention relabelling (R-26.3): a `negate` base holds the negated scalar. -/
def negateByTable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    (fb : Array (AccFixedBase G₁)) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : KzgAcc (Fr p) G₁ G₂ Gₜ :=
  let neg (n : String) : Bool := fb.any (fun b => b.name == n && b.negate)
  { a with rhs := { a.rhs with fixedBaseScalars :=
      a.rhs.fixedBaseScalars.map (fun (n, s) => (n, if neg n then -s else s)) } }

/-- PLAN 9.5 decodeAcc_encode restricted to the only shape the contract reads (R-26.2): a collapsed
    point-and-scalar accumulator behind `enc.offset` prefix words. The .pointPair round trip is FALSE
    (encodeAccInstances always emits carried scalars). -/
theorem decodeAcc_encode {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : (tail.toList.map Prod.fst).Sorted (· < ·))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (prefix : Array Word256) (hpre : prefix.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (prefix ++ encodeAccInstances (toExec enc) codec a) = some (negateByTable fb a) := by sorry

theorem decodeAcc_encode_noNeg /- same binders -/ (hneg : ∀ b ∈ fb.toList, b.negate = false) :
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (prefix ++ encodeAccInstances (toExec enc) codec a) = some a := by sorry

/-- Adjustment 1: kind-aware public-input encoder. The point-pair layout carries no scalar words
    (Models.lean:863-865: Moonlight wraps do not carry scalars); `encodeAccInstances` always emits them,
    which is why the PLAN round trip is false for .pointPair. Rust source to confirm against:
    circuits/src/ecc/foreign/ecc_chip.rs:226-239 `as_public_input` on fully collapsed points. -/
def encodeAccPublicInput {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : Array Word256 :=
  if enc.hasCarriedScalars then encodeAccInstances enc codec a
  else dropCarriedScalarWords enc (encodeAccInstances enc codec a)   -- SKETCH: drop the two scalar slots (lhs at pointWords, rhs after)

/-- The round trip for the DEPLOYED point-pair shape: carried scalars are implicitly 1. -/
theorem decodeAcc_encode_pointPair /- same binders as decodeAcc_encode -/
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointPair) (hsL : sL = 1) (hsR : sR = 1) :
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (prefix ++ encodeAccPublicInput (toExec enc) codec a) = some (negateByTable fb a) := by sorry

theorem decideBool_eq_true_iff {α : Type} {a b : α} (d : Decidable (a = b)) :
    decideBool d = true ↔ a = b := by cases d <;> simp [decideBool, *]

section Msm
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
theorem MSMKZG.eval_fromBase (Q : G₁) : (MSMKZG.fromBase (p := p) Q).eval = Q := by simp [MSMKZG.eval, MSMKZG.fromBase]
/-- No Wf hypothesis needed: the `[1]` shortcut agrees with msmSpecific case by case. -/
theorem MSMKZG.eval_scale (m : MSMKZG (Fr p) G₁) (c : Fr p) : (m.scale c).eval = gsmul c m.eval := by sorry
/-- Lockstep lengths are required: msmSpecific zips with truncation (Msm.lean:52-56). -/
theorem MSMKZG.eval_addMsm (m n : MSMKZG (Fr p) G₁)
    (hm : m.scalars.size = m.bases.size) (hn : n.scalars.size = n.bases.size) :
    (m.addMsm n).eval = m.eval * n.eval := by sorry
end Msm

section S5
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- S5 completeness half: both equations hold ⇒ the α-batched one holds for every α. -/
theorem batched_complete (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hd : DualMSM.check d params = true) (ha : KzgAcc.check a params tbl = true) (alpha : Fr p) :
    batchedCheck params alpha d a tbl = true := by sorry

/-- S5 soundness half: a bad pair passes the batched check for at most one α. -/
theorem batched_atMostOneRoot (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hbad : DualMSM.check d params = false ∨ KzgAcc.check a params tbl = false)
    (alpha beta : Fr p) (hα : batchedCheck params alpha d a tbl = true)
    (hβ : batchedCheck params beta d a tbl = true) : alpha = beta := by sorry

/-- The contract orientation at CHECK level: e(PAIRING_RHS, G2)·e(PAIRING_LHS, NEG_S_G2) = 1
    (swap at FinalPairing.yul:88; layout AssemblyHelpers.yul:284-287). -/
def contractPairingHolds (g2 negSG2 : G₂) (lhs rhs : G₁) : Prop :=
  P.e (Additive.ofMul rhs) (Additive.ofMul g2) + P.e (Additive.ofMul lhs) (Additive.ofMul negSG2) = 0

/-- Lift of Spec.Lemmas.pairing_reorder to DualMSM.check: only linearity in the G₂ slot is needed. -/
theorem dualMsm_check_iff_contract (d : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (g2 negSG2 : G₂) (hn : params.nG2Prepared = g2⁻¹) (hs : params.sG2Prepared = negSG2⁻¹) :
    DualMSM.check d params = true ↔ contractPairingHolds g2 negSG2 d.left.eval d.right.eval := by sorry
-- hn: R-4 (ofParams g2⁻¹ vs read g2Gen⁻¹; contract G2_BASE = params.g2); hs: NEG_S_G2_BASE = sG2⁻¹.

/-- Spec-level: every G₁ element is a multiple of the SRS base (prime order ⇒ cyclic, hG₁). -/
theorem exists_zmod_smul_generator (Q : G₁) : ∃ s : ZMod p, Q = gsmul s P.g₁ := by sorry

/-- The contract's canonicality gate on instance words (TranscriptProofParser.yul:63-68). -/
def frOfWord? (w : Word256) : Option (Fr p) := if w.toNat < p then some (Nat.cast w.toNat) else none
def instOfWords? (ws : Array Word256) : Option (Array (Fr p)) := (ws.toList.mapM frOfWord?).map List.toArray

/-- PLAN 9.5 ContractRef.accepts with the accumulator arm, over RAW instance words (R-26.7). `fb` is
    the generated positive-base table (artifacts.rs:181-227) because Midfall.Halo2.fixedBases' "-G"
    entry is the identity (defect). alphaOf order: (kzgLhs kzgRhs accLhs accRhs); hashed order is
    tag ‖ vk_digest ‖ RHS ‖ LHS ‖ ACC_RHS ‖ ACC_LHS (FinalPairing.yul:21-26). -/
def ContractRefAcceptsAcc (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (cfgAcc : Option Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256)
    (ms : List (Msg (Fr p) G₁)) : Bool :=
  match instOfWords? (p := p) instW with
  | none => false
  | some inst =>
    match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
    | .error _ => false
    | .ok d =>
      match cfgAcc with
      | none => DualMSM.check d params
      | some enc =>
        match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW with
        | none => false
        | some a =>
          let tbl := fb.map (fun b => (b.name, b.base))
          let (accL, accR) := a.fullyCollapse tbl
          batchedCheck params (alphaOf (p := p) H vkDigest E.g1 d.left.eval d.right.eval accL accR) d a tbl

theorem contractRefAcceptsAcc_none (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params) (vk) (vkDigest) (fb)
    (instW : Array Word256) (ms) :
    ContractRefAcceptsAcc E H params vk none vkDigest fb instW ms = true ↔
      ∃ inst, instOfWords? (p := p) instW = some inst ∧
        Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E H params vk inst ms = true := by
  sorry -- unfold; cases instOfWords?; cases prepareMsgs <;> simp [ContractRefAccepts]

/-- PLAN 9.5 contractRef_acc_complete (R-26.4 direction only: the contract is strictly stronger). -/
theorem contractRef_acc_complete (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (enc : Midfall.Generator.AccumulatorEncoding) (vkDigest : Word256)
    (fb : Array (AccFixedBase G₁)) (instW : Array Word256) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hinst : instOfWords? (p := p) instW = some inst)
    (hv : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms = .ok ())
    (ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW = some a)
    (hchk : KzgAcc.check a params (fb.map fun b => (b.name, b.base)) = true)
    (hWf : ∀ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d →
      d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size) :
    ContractRefAcceptsAcc E H params vk (some enc) vkDigest fb instW ms = true := by
  sorry -- unfold; rw [hinst]; cases prepareMsgs; verifyMsgs ok ⇒ check d; batched_complete
end S5
end Midfall.Lowering
```

### G. `Midfall/Lowering/VkDigest.lean` (imports Encoding, never Generator.Vk)

```lean
import Midfall.Generator.Encoding
import Midfall.Halo2.Exec.Accumulator
import Midfall.Common.Codec

namespace Midfall.Lowering
/-- The deployed VK_DIGEST word (Generator/Vk.lean:763: feToU256 (bytesToNats (frToRepr vk.transcriptRepr)))
    is frWord vk.transcriptRepr. No bound on p: both sides reduce mod 2^256. -/
theorem feToU256_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (x : Midfall.Fr p) :
    Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats (Midfall.frToRepr x)) = .ok (Midfall.Halo2.frWord x) := by
  sorry -- natToBytesLowFirst_size, bytesFromNats_bytesToNats, bytesToWordLE_natToBytesLE
-- Obligations field (needs Generator.Vk, forbidden here):
--   vkDigest_slot0 : ∀ codecs inputs hvk, generateBaseVk codecs inputs = .ok hvk →
--     hvk.constants.head? = some ("vk_digest", frWord inputs.vk.transcriptRepr)
end Midfall.Lowering
```

### H. `Midfall/Lowering/Calldata.lean`

```lean
import Midfall.Generator.Abi
import Midfall.Generator.Quotient.VmTypes
import Midfall.Generator.Encoding
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Accumulator
import Midfall.Assumptions.Codec

namespace Midfall.Lowering
open Midfall Midfall.Halo2
open Midfall.Generator (RepackedProofLayoutPlan ProofCalldataLayout RepackError)

inductive WireSlot | g1 | fr deriving DecidableEq, Repr

def Msg.slot {F G : Type} : Msg F G → WireSlot
  | .g1 _ => .g1
  | .fr _ => .fr

/-- The repack walk order (calldata.rs:109-126) = the transcript read order. -/
def RepackedProofLayoutPlan.slots (plan : RepackedProofLayoutPlan) : List WireSlot :=
  List.replicate plan.prefixG1Count .g1 ++ List.replicate plan.numEvals .fr ++ [.g1] ++
    List.replicate plan.numPointSets .fr ++ [.g1]

/-- Contract-side bytes of one message: EIP-2537 padded point or 32-byte BE scalar. -/
def msgContractBytes {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) : Msg (Fr p) G₁ → Bytes
  | .g1 Q => c.toEip Q
  | .fr s => frToInputBE s

/-- PLAN 9.5 encodeContractProof: the schedule is carried by `ms` itself. -/
def encodeContractProof {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (ms : List (Msg (Fr p) G₁)) : Bytes :=
  ms.foldl (fun acc m => acc ++ msgContractBytes c m) Bytes.empty

/-- Port of VerifierBuildInputs::repack_proof (calldata.rs:43-128), over the codec. -/
def repackSlot {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (π : Bytes) :
    WireSlot → Nat → Except RepackError (Bytes × Nat)
  | .g1, cur =>
    match bytesTake π cur g1CompressedWidth with
    | none => .error (.invalidCompressedG1 cur "")               -- unreachable after the length check
    | some comp =>
      match c.ofCompressed? comp with
      | none => .error (.invalidCompressedG1 cur (hexOf comp))  -- SKETCH: hexOf renderer
      | some Q => .ok (c.toEip Q, cur + g1CompressedWidth)
  | .fr, cur =>
    match bytesTake π cur 32 with
    | none => .error (.nonCanonicalScalar cur "")
    | some le =>
      match frOfRepr? (p := p) le with
      | none => .error (.nonCanonicalScalar cur (hexOf (reverseBytes le)))  -- SKETCH
      | some s => .ok (frToInputBE s, cur + 32)

def repackProof {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) : Except RepackError Bytes := do
  if π.size ≠ plan.compressedLen then
    throw (.lengthMismatch plan.compressedLen π.size plan.prefixG1Count plan.numEvals plan.numPointSets)
  let (out, _) ← plan.slots.foldlM
    (fun (st : Bytes × Nat) sl => do
      let (b, cur') ← repackSlot (p := p) c π sl st.2
      pure (st.1 ++ b, cur'))
    (Bytes.empty, 0)
  pure out

/-- Pure schedule-driven decode of the compressed stream (NOT decodeRust, which also runs the
    pipeline); carries repackProof's exact-length guard (attack fix). -/
def decodeWire {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) : Option (List (Msg (Fr p) G₁)) :=
  if π.size ≠ plan.compressedLen then none
  else (plan.slots.foldlM (fun (st : List (Msg (Fr p) G₁) × Nat) sl =>
    match sl, bytesTake π st.2 (if sl = .g1 then g1CompressedWidth else 32) with
    | .g1, some comp => (c.ofCompressed? comp).map fun Q => (st.1 ++ [.g1 Q], st.2 + g1CompressedWidth)
    | .fr, some le => (frOfRepr? (p := p) le).map fun s => (st.1 ++ [.fr s], st.2 + 32)
    | _, none => none) ([], 0)).map Prod.fst

/-- evm.rs:15 FN_SIG_VERIFY_PROOF. -/
def fnSigVerifyProof : Bytes := Midfall.Generator.bytesFromNats [0x1e, 0x8e, 0x1e, 0x13]

/-- evm.rs:22-38: selector ‖ BE32(0x40) ‖ BE32(0x60+len) ‖ BE32(len) ‖ proof ‖ BE32(n) ‖ instances. -/
def encodeCalldataRaw (proof : Bytes) (instances : List Word256) : Bytes :=
  fnSigVerifyProof ++ natToBytesBE 0x40 32 ++ natToBytesBE (0x40 + 0x20 + proof.size) 32 ++
    natToBytesBE proof.size 32 ++ proof ++ natToBytesBE instances.length 32 ++
    instances.foldl (fun acc w => acc ++ wordToBytesBE w) Bytes.empty

/-- calldata.rs:132-149 with the instance-length check and the RepackError lift (Api.lean:388). -/
def encodeCalldata {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (numInstances : Nat)
    (plan : RepackedProofLayoutPlan) (c : G1Codec G₁) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes := do
  if inst.size ≠ numInstances then
    throw (.planning "calldata"
      ("instance length mismatch: expected " ++ toString numInstances ++ ", got " ++ toString inst.size))
  match repackProof (p := p) plan c π with
  | .error e => throw (Midfall.Generator.GeneratorError.fromRepackError e)
  | .ok proof => pure (encodeCalldataRaw proof (inst.toList.map frWord))

/-- PLAN 9.5 calldataOf: canonical calldata of (ms, raw instance words). -/
def calldataOf {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁)
    (ms : List (Msg (Fr p) G₁)) (inst : List Word256) : Bytes :=
  encodeCalldataRaw (encodeContractProof c ms) inst

/-- calldataload: 32 bytes at i, zero past the end. -/
def cdWord (cd : Bytes) (i : Nat) : Word256 :=
  BitVec.ofNat 256 ((List.range 32).foldl (fun acc j => acc * 256 + ((cd.get? (i + j)).map UInt8.toNat).getD 0) 0)

/-- common_uncompressed_g1's range checks (AssemblyHelpers.yul:94-104). -/
def g1WordsOk (cd : Bytes) (cptr : Nat) : Bool :=
  let xh := (cdWord cd cptr).toNat; let xl := (cdWord cd (cptr + 32)).toNat
  let yh := (cdWord cd (cptr + 64)).toNat; let yl := (cdWord cd (cptr + 96)).toNat
  xh < 2 ^ 128 && yh < 2 ^ 128 &&
    xh * 2 ^ 256 + xl < Midfall.Assumptions.pBase && yh * 2 ^ 256 + yl < Midfall.Assumptions.pBase

def decodeSlots {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (cd : Bytes) :
    List WireSlot → Nat → Option (List (Msg (Fr p) G₁) × Nat)
  | [], cur => some ([], cur)
  | .g1 :: rest, cur => do
    guard (g1WordsOk cd cur)
    let b ← bytesTake cd cur g1EipWidth
    let Q ← c.ofEip? b            -- off-curve/off-subgroup bytes revert later via G1MSM/pairing
    let (ms, cur') ← decodeSlots c cd rest (cur + g1EipWidth)
    pure (.g1 Q :: ms, cur')
  | .fr :: rest, cur => do
    let w := cdWord cd cur
    guard (w.toNat < p)           -- TranscriptProofParser.yul:319, :382
    let (ms, cur') ← decodeSlots c cd rest (cur + 32)
    pure (.fr (Nat.cast w.toNat) :: ms, cur')

/-- PLAN 9.5 decodeCalldata (ours; no Rust decoder exists). Every guard is a template line. -/
def decodeCalldata {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (L : ProofCalldataLayout)
    (numInstances : Nat) (c : G1Codec G₁) (cd : Bytes) :
    Option (List (Msg (Fr p) G₁) × Array Word256) := do
  let plan := RepackedProofLayoutPlan.fromProofLayout L
  let numInstCptr := L.proofEnd
  let instCptr := numInstCptr + 32
  guard (bytesTake cd 0 4 == some fnSigVerifyProof)                                 -- solc dispatcher
  guard (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr)                  -- 0x64
  guard (L.proofEnd == L.proofCptr + L.proofLen)                                     -- attack fix (layout consistency)
  guard ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == numInstCptr - 4)  -- Halo2Verifier.sol:148
  guard ((cdWord cd 0x44).toNat == L.proofLen)                                       -- VkLoading.yul:101
  guard ((cdWord cd numInstCptr).toNat == numInstances)                              -- VkLoading.yul:102
  guard (cd.size == instCptr + 32 * numInstances)                                    -- VkLoading.yul:106-109
  let (ms, cur) ← decodeSlots (p := p) c cd plan.slots L.proofCptr
  guard (cur == numInstCptr)                                                         -- TranscriptProofParser.yul:416
  let inst := (List.range numInstances).map (fun i => cdWord cd (instCptr + 32 * i))
  guard (inst.all (fun w => w.toNat < p))                                            -- TranscriptProofParser.yul:63-68
  pure (ms, inst.toArray)

theorem repackedLen_mod32 (plan : RepackedProofLayoutPlan) : plan.repackedLen % 32 = 0 := by
  unfold RepackedProofLayoutPlan.repackedLen; omega
theorem sum_commitmentReadGroups (L : ProofCalldataLayout) :
    (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count = L.commitmentG1Count := by sorry -- SKETCH field name
/-- Layouts built by fromProtocol at 0x64 tile exactly (hand-built ones need not). -/
theorem proofLen_eq_repackedLen (protocol : Midfall.Generator.ProtocolPlan) (numEvals numPointSets : Nat)
    (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets = .ok L) :
    L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen ∧
    L.proofEnd = L.proofCptr + L.proofLen := by sorry

theorem calldata_roundtrip {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≤ 2 ^ 256) {G₁ : Type} [Group G₁]
    (L : ProofCalldataLayout) (hL : L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr)
    (hlen : L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen)
    (hend : L.proofEnd = L.proofCptr + L.proofLen)
    (c : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws c)
    (ms : List (Msg (Fr p) G₁)) (hshape : ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout L).slots)
    (numInstances : Nat) (inst : List Word256) (hn : inst.length = numInstances)
    (hinst : ∀ w ∈ inst, w.toNat < p) :
    decodeCalldata (p := p) L numInstances c (calldataOf c ms inst) = some (ms, inst.toArray) := by sorry
-- hp: frToInputBE truncates at 2^256 (attack); hc.eipShape/toEip_one: g1WordsOk; hc.ofEip_toEip: recovery.

/-- EXACT in both modes (D7): trailing bytes and non-canonical words fail closed; the R-25
    malleability lives in decodeAcc, not here. -/
theorem calldata_canonical {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (L : ProofCalldataLayout) (numInstances : Nat) (c : G1Codec G₁) (hc : c.eipRoundtrip)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd = calldataOf c ms inst.toList := by sorry

/-- D8: wire-level iff. -/
theorem repack_spec_wire {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π π' : Bytes) :
    repackProof (p := p) plan c π = .ok π' ↔
      ∃ ms, decodeWire (p := p) plan c π = some ms ∧ π' = encodeContractProof c ms := by sorry

/-- D8: the pipeline-level half, in the only true direction (PLAN's iff fails for byte-valid
    proofs whose pipeline panics: x3 ∈ pointSets kzg/mod.rs:479, logup.rs:460). -/
theorem repack_spec_of_decodeRust {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (π : Bytes) (plan : RepackedProofLayoutPlan) (hc : E.g1.compressedRoundtrip)
    (hsched : ∀ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms → ms.map Msg.slot = plan.slots)
    (ms : List (Msg (Fr p) G₁)) (hdec : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    repackProof (p := p) plan E.g1 π = .ok (encodeContractProof E.g1 ms) := by sorry

/-- Generator layer of points_subgroup_checked (semantic layer is an Obligations field). -/
theorem points_subgroup_checked_generator (meta_ : Midfall.Generator.ConstraintSystemMeta)
    (data : Midfall.Generator.Data) (memory : Midfall.Generator.VerifierMemoryLayout) (L : ProofCalldataLayout)
    (h : Midfall.Generator.validateAbsorbedG1PrecompileCoverage meta_ data memory L = .ok (.ok ())) :
    (Midfall.Generator.proofAbsorbedG1s meta_ data memory).length = L.totalG1Count ∧   -- SKETCH names
    ∀ t ∈ Midfall.Generator.proofAbsorbedG1s meta_ data memory,
      ∃ u, Midfall.Generator.precompileValidatedG1s meta_ data memory = .ok u ∧
        ∃ v ∈ u, Midfall.Generator.ecPointBeq t.point v.point = true := by sorry
end Midfall.Lowering
```

### I. `Midfall/Lowering/Checkpoint.lean`

```lean
import Midfall.Generator.Layout

namespace Midfall.Lowering
open Midfall.Generator

/-- The seven boundaries between verifier partials (PLAN 9.5 Inv indices). NOT MemoryPhase
    (Layout.lean:407), which is a 16-way scratch lifetime. -/
inductive Checkpoint
  | start | vk | transcript | lagrange | quotient | pcs | pairing
  deriving DecidableEq, Repr

def Checkpoint.idx : Checkpoint → Nat
  | .start => 0 | .vk => 1 | .transcript => 2 | .lagrange => 3 | .quotient => 4 | .pcs => 5 | .pairing => 6
instance : LE Checkpoint := ⟨fun a b => a.idx ≤ b.idx⟩
def Checkpoint.next : Checkpoint → Checkpoint
  | .start => .vk | .vk => .transcript | .transcript => .lagrange | .lagrange => .quotient
  | .quotient => .pcs | .pcs => .pairing | .pairing => .pairing

/-- The seven production partials in include order (Halo2Verifier.sol:217-229). -/
inductive Partial
  | vkLoading | transcriptParser | lagrange | quotientLin | pcs | finalPairing | traceReturn
  deriving DecidableEq, Repr

def Partial.pre : Partial → Checkpoint
  | .vkLoading => .start | .transcriptParser => .vk | .lagrange => .transcript
  | .quotientLin => .lagrange | .pcs => .quotient | .finalPairing => .pcs | .traceReturn => .pairing

/-- Which region lifetimes carry facts across a checkpoint: permanent regions always; the
    selector_accumulators region (lifetime .phase .pcsFinalMsm, LayoutMemory.lean:268-270) is written
    by the quotient phase and read by PCS block 5, so it is live at .quotient and .pcs (finding 12);
    every other scratch is dead between partials (54 same-byte different-phase pairs). -/
def Checkpoint.liveAt : Checkpoint → MemoryLifetime → Bool
  | _, .permanent => true
  | .quotient, .phase .pcsFinalMsm => true
  | .pcs, .phase .pcsFinalMsm => true
  | _, .phase _ => false
-- Gate: liveAt .pairing (.phase .pcsFixed) = false by rfl; cross-check against LayoutMemory's region list.
end Midfall.Lowering
```

### J. Exec refactor (`Exec/Verifier.lean`, `Exec/Kzg/MultiOpen.lean`) — signatures only; bodies moved verbatim

```lean
-- Exec/Verifier.lean, inside namespace Verifier with its existing binders
/-- verifier.rs:283-439 as one named read phase (R1: body moved, not changed). -/
structure AlgebraRead (Fr G₁ : Type) where
  quotientLimbComs : Array G₁
  x splittingFactor xn : Fr
  lIS : Array Fr
  instanceEvals adviceEvals : Array (Array Fr)
  fixedEvals : Array Fr
  permutationsCommon : Permutation.CommonEvaluated Fr          -- SKETCH names
  permutationsEvaluated : Array (Permutation.Evaluated Fr G₁)
  lookupsEvaluated : Array (Array (Logup.Evaluated Fr G₁))
  trashcansEvaluated : Array (Array (Trash.Evaluated Fr G₁))

def readAlgebra (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (trace : VerifierTrace (Fr p) G₁) (committed : Array (Array G₁))
    (instances : Array (Array (Array (Fr p)))) : TranscriptM (AlgebraRead (Fr p) G₁)

/-- plonk/mod.rs:509-515 lifted out of partiallyEvaluateIdentities: (lLast, lBlind, l0),
    the Rust slot order (Lagrange.yul:77-79). -/
def lagrangeTriple (vk : VerifyingKey (Fr p) G₁) (x xn : Fr p) : Except Fault (Fr p × Fr p × Fr p)

/-- verifier.rs:475-647: tagged expressions, linearization query, multi-open queries. -/
def linearize (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (nbCommitted : Nat) (committed : Array (Array G₁)) (r : AlgebraRead (Fr p) G₁) :
    Except Fault (Array (Option Nat × Fr p) × VerifierQuery (Fr p) G₁ × Array (VerifierQuery (Fr p) G₁))
-- verifyAlgebraicConstraints := shape checks (:260-268); readAlgebra; StateT.lift (linearize …);
--   the R-8 collapse of pcs.multiPrepare — definitionally the old function.

-- Exec/Kzg/MultiOpen.lean
structure PhaseA where x1 x2 : Fr p; qComs : Array (MSMKZG (Fr p) G₁); qEvalSets pointSets : Array (Array (Fr p))  -- SKETCH
structure PhaseB where fCom : G₁; x3 : Fr p; qEvalsOnX3 : List (Fr p); fEval : Fr p
structure PhaseC where x4 : Fr p; finalCom : MSMKZG (Fr p) G₁; v : Fr p; pi : G₁; dual : DualMSM (Fr p) G₁ G₂ Gₜ
def MultiPrepare.phaseA (g1 fc feat fewer queries) : TranscriptM PhaseA   -- :210-223
def MultiPrepare.phaseB (g1 fc feat) (a : PhaseA) : TranscriptM PhaseB      -- :225-232 (x3 truncated here)
def MultiPrepare.phaseC (g1 fc feat) (a : PhaseA) (b : PhaseB) : TranscriptM PhaseC -- :234-252
-- multiPrepare … := do let a ← phaseA …; let b ← phaseB … a; pure (← phaseC … a b).dual
-- Gate: every existing #eval KAT token unchanged; conformance replay identical. No theorem.
```

### K. `Midfall/Lowering/Snapshot.lean`

```lean
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Verifier
import Midfall.Halo2.Exec.Kzg.MultiOpen
import Midfall.Halo2.Exec.Accumulator
import Midfall.Lowering.Checkpoint

namespace Midfall.Lowering
open Midfall.Halo2
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Every L0 intermediate the contract materialises in memory, in production order. -/
structure Snapshot (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type) where
  trace : VerifierTrace (Fr p) G₁              -- theta beta gamma trash y; commitments by region
  alg : Verifier.AlgebraRead (Fr p) G₁         -- quotient limb coms, x, splittingFactor, xn, evals
  l0 lLast lBlind : Fr p
  instanceEval : Fr p                          -- INSTANCE_EVAL = Σ inst_i · l_i(x) over the PUBLIC column
  expressions : Array (Option Nat × Fr p)
  linCom : VerifierQuery (Fr p) G₁             -- QUOTIENT_EVAL := linCom.eval; buckets := selector scalars
  queries : Array (VerifierQuery (Fr p) G₁)
  a : MultiPrepare.PhaseA (p := p) (G₁ := G₁)
  b : MultiPrepare.PhaseB (p := p) (G₁ := G₁)  -- x3 already truncated
  c : MultiPrepare.PhaseC (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)
  acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)

/-- The public-column instance evaluation: the unique instance query on the non-committed column
    at rotation 0 (noRotInst). Attack fix: `getD 0` would pin the committed column's transcript
    read when that query is registered first. -/
def publicInstanceEval (vk : VerifyingKey (Fr p) G₁) (nbCommitted : Nat)
    (alg : Verifier.AlgebraRead (Fr p) G₁) : Option (Fr p) :=
  (vk.cs.instanceQueries.toList.enum.find? (fun (_, q) => decide (nbCommitted ≤ q.1.index) && q.2.int == 0)).bind
    fun (i, _) => (alg.instanceEvals.getD 0 #[])[i]?   -- SKETCH: per-proof × per-query layout

/-- The stage at which the Lean pipeline faults, so per-partial 'fault ⇒ revert' lemmas can be
    stated over prefixes (attack fix: a full-snapshot hypothesis made partial specs vacuous for
    calldata that faults later). -/
def snapshotOf (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)) :
    Except (Checkpoint × Fault) (Snapshot p G₁ G₂ Gₜ) := do
  let bytes := ms.foldl (init := Bytes.empty) (fun a m => ByteArray.append a (msgWire E m))
  let t0 := Transcript.initWithHash H bytes
  let (trace, t1) ← ((parseTrace E.g1 Features.solidity vk #[#[1]] #[#[inst]]).run t0).mapError (.transcript, ·)
  let (alg, t2) ← ((Verifier.readAlgebra E.g1 Features.solidity vk trace #[#[1]] #[#[inst]]).run t1).mapError (.transcript, ·)
  let (lLast, lBlind, l0) ← (Verifier.lagrangeTriple vk alg.x alg.xn).mapError (.lagrange, ·)
  let some instanceEval := publicInstanceEval vk 1 alg | throw (.lagrange, Fault.error Error.invalidInstances)
  let (expressions, linCom, queries) ← (Verifier.linearize E.delta vk trace 1 #[#[1]] alg).mapError (.quotient, ·)
  let (a, t3) ← ((MultiPrepare.phaseA (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field Features.solidity E.fewerPointSetsRuntime queries).run t2).mapError (.pcs, ·)
  let (b, t4) ← ((MultiPrepare.phaseB (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field Features.solidity a).run t3).mapError (.pcs, ·)
  let (c, t5) ← ((MultiPrepare.phaseC E.g1 E.field Features.solidity a b).run t4).mapError (.pcs, ·)
  (t5.assertEmpty).mapError (.transcript, ·)
  pure { trace, alg, l0, lLast, lBlind, instanceEval, expressions, linCom, queries, a, b, c, acc }

/-- Agreement with prepareMsgs; two parts because verifyAlgebraicConstraints collapses every
    multiPrepare Fault.error to Error.opening (R-8). -/
theorem snapshotOf_prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)) :
    (∀ S, snapshotOf E H vk inst ms acc = .ok S →
        prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok S.c.dual) ∧
    ((snapshotOf E H vk inst ms acc).isOk = (prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms).isOk) := by
  sorry
-- Non-vacuity: Features default (truncatedChallenges = false) breaks part 1 on any proof whose x3
-- has nonzero high bits; a misordered lagrangeTriple pins the wrong Lagrange.yul slots.
end Midfall.Lowering
```

### L. `Midfall/Lowering/Inv.lean`

```lean
import Midfall.Lowering.Snapshot
import Midfall.Yul.Bridge
import Midfall.Generator.Layout
import Midfall.Generator.LayoutMemory
import Midfall.Generator.Models
import Midfall.Generator.Abi
import Midfall.Generator.Templates

namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator YulSemantics.EVM

/-- The LoweringPlan fields that exist today (plan.rs:29 is P-11). -/
structure PlanView where
  vk : Halo2VerifyingKey
  vkMptr : Ptr
  memory : VerifierMemoryLayout
  proofLayout : ProofCalldataLayout
  numInstances k numNegLagranges : Nat
  hasAccumulator : Bool
  accEncoding : Option Midfall.Generator.AccumulatorEncoding   -- adjustment 2: = cfg.accumulator; hasAccumulator = accEncoding.isSome
  consts : TemplateConstants
  qplan : QuotientProgramPlan
  qbuild : QuotientProgramBuild
  qext : Option QuotientExternal

def ptrAddr (q : Ptr) : Nat := Value.asUsizeNat (ptrValue q)                 -- Layout.lean:1010
def wordAt (st : EvmState) (a : Nat) : Word256 := loadWord st.memory a       -- EVMExec.lean:320
def bytesAt (st : EvmState) (a n : Nat) : Bytes := ByteArray.mk (readBytes st.memory a n).toArray

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

def holdsFr (st : EvmState) (a : Nat) (x : Fr p) : Prop := wordAt st a = frWord x
def holdsG1 (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (a : Nat) (Q : G₁) : Prop := bytesAt st a 128 = E.g1.toEip Q
def holdsG1s (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (base : Nat) (Qs : Array G₁) : Prop :=
  ∀ i, i < Qs.size → holdsG1 E st (base + 128 * i) (Qs.getD i 1)
def holdsFrs (st : EvmState) (base : Nat) (xs : Array (Fr p)) : Prop :=
  ∀ i, i < xs.size → holdsFr st (base + 32 * i) (xs.getD i 0)

/-- The Yul locals every partial reads (VEnv, not memory): r and success. -/
def LocalsOk {calls gas} (V : VEnv (Midfall.Yul.Bridge.Dialect calls gas)) : Prop :=
  VEnv.get V "r" = some (BitVec.ofNat 256 p) ∧ (VEnv.get V "success" = some 1 ∨ VEnv.get V "success" = some 0)

/-- Literals the contract hard-codes, tied to the abstract environment. -/
structure EnvAgrees (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) (PV : PlanView)
    (params : ParamsVerifierKZG G₁ G₂) (sG2gen : G₂) (encG2 : G₂ → Bytes)
    (fb : Array (AccFixedBase G₁)) : Prop where
  modulus : p = frModulusConstant                                   -- FR_MODULUS in every addmod/mulmod/lt
  truncWidth : divCeil (divCeil E.field.numBits 8) 2 = 16           -- x3 mask 128 bits; truncate keeps 16 bytes
  delta : E.delta = (Nat.cast blsDeltaLiteral : Fr p)               -- SKETCH: new constant from quotient.rs:1492
  domainN : vk.domain.n = 2 ^ vk.domain.k ∧ vk.domain.k = PV.k
  baryWeight : vk.domain.barycentricWeight = ((2 ^ vk.domain.k : ℕ) : Fr p)⁻¹   -- N_INV = invert(2^k)
  omegaInvMul : vk.domain.omegaInv * vk.domain.omega = 1
  omegaOrder : vk.domain.omega ^ vk.domain.n = 1                    -- makes x^n ≠ 1 exclude x = ω^i
  negLagranges : PV.numNegLagranges = (vk.cs.blindingFactors.toOption.getD 0) + 1   -- SKETCH: Nat form
  nG2 : params.nG2Prepared = P.g₂⁻¹                                  -- R-4
  sG2 : params.sG2Prepared = sG2gen
  vkDigestWord : (PV.vk.constants.getD 0 ("", 0)).2 = frWord vk.transcriptRepr
  g1BaseWords : vkG1Words PV 11 = E.g1.toEip P.g₁                   -- SKETCH: header word indices
  g2BaseWords : vkG2Words PV 15 = encG2 P.g₂
  negSG2Words : vkG2Words PV 23 = encG2 sG2gen⁻¹
  /-- Adjustment 2: VkLoading.yul:84-87 cross-checks HAS_ACCUMULATOR, ACC_OFFSET, NUM_ACC_LIMBS and
      NUM_ACC_LIMB_BITS against the generated config; without these clauses vkLoading_spec is
      unprovable in accumulator renders. -/
  accHeader : ∀ enc, PV.accEncoding = some enc →
    (PV.vk.constants.getD hasAccumulatorSlot ("", 0)).2 = 1 ∧                      -- SKETCH: slot indices from vkHeaderTemplateSlotsDefault
    (PV.vk.constants.getD accOffsetSlot ("", 0)).2 = BitVec.ofNat 256 enc.offset ∧
    (PV.vk.constants.getD numAccLimbsSlot ("", 0)).2 = BitVec.ofNat 256 enc.numLimbs ∧
    (PV.vk.constants.getD numAccLimbBitsSlot ("", 0)).2 = BitVec.ofNat 256 enc.numLimbBits
  accNoHeader : PV.accEncoding = none → (PV.vk.constants.getD hasAccumulatorSlot ("", 0)).2 = 0
  accConsistent : PV.hasAccumulator = PV.accEncoding.isSome
  /-- Adjustment 2: the fixed-base tail folds VK points read from memory (AccumulatorHelpers.yul:314-337):
      each table entry's base is the point its VK slot encodes (artifacts.rs:181-227 maps names to VK point
      mptrs), so finalPairing_sound_acc can relate the folded point to `a.fullyCollapse (tblOf PV fb)`. -/
  accBasesInVk : ∀ b ∈ fb.toList, ∃ slot, vkG1Words PV slot = E.g1.toEip b.base   -- SKETCH: slot from the name → mptr map

/-- Completeness side condition (R-2 first face). Soundness's NoLogupPanic is stated in
    Surface.lean operationally; inside a snapshot hypothesis it would be decorative (attack). -/
structure ChallengesGood (vk : VerifyingKey (Fr p) G₁) (S : Snapshot p G₁ G₂ Gₜ) : Prop where
  xNotRoot : S.alg.x ^ vk.domain.n ≠ 1

def tblOf (PV : PlanView) (fb : Array (AccFixedBase G₁)) : Array (String × G₁) := fb.map fun b => (b.name, b.base)

/-- Inv k: memory + locals + state at checkpoint k relative to the snapshot. Clauses accumulate
    (idx-monotone) and mention only regions live at k (Checkpoint.liveAt). -/
def Inv {calls gas} (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (fb : Array (AccFixedBase G₁)) (k : Checkpoint) (PV : PlanView) (S : Snapshot p G₁ G₂ Gₜ)
    (V : VEnv (Midfall.Yul.Bridge.Dialect calls gas)) (st : EvmState) : Prop :=
  let M := PV.memory
  st.halted = none ∧ LocalsOk (p := p) V ∧
  -- permanent, never written: PCS reads it as the committed-instance commitment (attack fix)
  bytesAt st (ptrAddr M.g1IdentityMptr) 128 = natToBytesBE 0 128 ∧
  (Checkpoint.vk ≤ k →
     bytesAt st (ptrAddr M.vkMptr) PV.vk.len = PV.vk.bytes ∧
     st.env.calldata.length = PV.proofLayout.proofEnd + 32 + 32 * PV.numInstances ∧
     (PV.hasAccumulator = true → ∃ a, S.acc = some a ∧
        holdsG1 E st (ptrAddr M.accLhsMptr) (a.fullyCollapse (tblOf PV fb)).1 ∧
        holdsG1 E st (ptrAddr M.accRhsMptr) (a.fullyCollapse (tblOf PV fb)).2)) ∧
  (Checkpoint.transcript ≤ k →
     holdsFr st (ptrAddr M.thetaMptr) S.trace.theta ∧ holdsFr st (ptrAddr M.betaMptr) S.trace.beta ∧
     holdsFr st (ptrAddr M.gammaMptr) S.trace.gamma ∧ holdsFr st (ptrAddr M.trashChallengeMptr) S.trace.trashChallenge ∧
     holdsFr st (ptrAddr M.yMptr) S.trace.y ∧ holdsFr st (ptrAddr M.xMptr) S.alg.x ∧
     holdsFr st (ptrAddr M.x1Mptr) S.a.x1 ∧ holdsFr st (ptrAddr M.x2Mptr) S.a.x2 ∧
     holdsFr st (ptrAddr M.x3Mptr) S.b.x3 ∧ holdsFr st (ptrAddr M.x4Mptr) S.c.x4 ∧
     holdsG1s E st (ptrAddr M.adviceCommsMptrBase) (S.trace.adviceCommitments.getD 0 #[]) ∧   -- SKETCH field names
     holdsG1s E st (ptrAddr M.quotientLimbCommsMptrBase) S.alg.quotientLimbComs ∧
     -- lookupM / permZ / lookupHelper / lookupZ / trashcan regions analogously, in ProofReadPlan order
     holdsG1 E st (ptrAddr M.fComMptr) S.b.fCom ∧ holdsG1 E st (ptrAddr M.piMptr) S.c.pi ∧
     holdsFrs st (ptrAddr M.reversedEvalsMptr) (reversedEvalsOf PV S) ∧                       -- SKETCH: Data.new order bridge
     wordAt st (ptrAddr M.qEvalCptrMptr) = BitVec.ofNat 256 PV.proofLayout.qEvalCptr) ∧       -- SKETCH field
  (Checkpoint.lagrange ≤ k →
     holdsFr st (ptrAddr M.xNMptr) S.alg.xn ∧ holdsFr st (ptrAddr M.lLastMptr) S.lLast ∧
     holdsFr st (ptrAddr M.lBlindMptr) S.lBlind ∧ holdsFr st (ptrAddr M.l0Mptr) S.l0 ∧
     holdsFr st (ptrAddr M.instanceEvalMptr) S.instanceEval) ∧
     -- X_N_MINUS_1_INV_MPTR: no production consumer, no Lean counterpart: unconstrained (finding 11)
  (Checkpoint.quotient ≤ k →
     holdsFr st (ptrAddr M.quotientEvalMptr) S.linCom.eval ∧
     holdsFrs st M.selectorAccMptr (selectorBucketsOf S.linCom) ∧                               -- SKETCH: groupedAdd scalars
     holdsFr st (ptrAddr M.quotientMptr) S.alg.splittingFactor ∧
     holdsFr st (ptrAddr M.quotientMptr + 32) (1 - S.alg.xn)) ∧
  (Checkpoint.pcs ≤ k →
     holdsFr st (ptrAddr M.fEvalMptr) S.b.fEval ∧ holdsFr st (ptrAddr M.vMptr) S.c.v ∧
     holdsG1 E st (ptrAddr M.finalComMptr) S.c.finalCom.eval ∧
     -- at .pcs ONLY: FinalPairing rewrites both slots in place in accumulator mode
     (k = Checkpoint.pcs →
        holdsG1 E st (ptrAddr M.pairingLhsMptr) S.c.dual.left.eval ∧
        holdsG1 E st (ptrAddr M.pairingRhsMptr) S.c.dual.right.eval)) ∧
  (k = Checkpoint.pairing →
     VEnv.get V "success" = some 1 ∧
     (PV.hasAccumulator = false → DualMSM.check S.c.dual params = true))

theorem Inv_mono {calls gas} (E) (params) (fb) {k₁ k₂ : Checkpoint} (h : k₁ ≤ k₂) (hne : k₂ ≠ .pairing ∨ k₁ = k₂)
    (PV) (S) (V : VEnv (Midfall.Yul.Bridge.Dialect calls gas)) (st)
    (hI : Inv E params fb k₂ PV S V st) : Inv E params fb k₁ PV S V st ∨ k₁ = .pcs := by sorry
-- (the pcs-only pairing-slot clause and the pairing-only success clause break plain monotonicity; state
--  the exact monotone fragment in the implementation)
-- Gates: Inv satisfiable on a hand-built state for a 1-instance fixture; refuted when pairingLhs/Rhs
-- words are swapped or `halted` is set; ChallengesGood exhibits a satisfying and a violating x over ZMod 17.
end Midfall.Lowering
```

### M. `Midfall/Lowering/Surface.lean` (never imports `Generator.Vk`)

```lean
import Midfall.Lowering.Inv
import Midfall.Lowering.Accumulator
import Midfall.Lowering.Calldata
import Midfall.Lowering.Types
import Midfall.Generator.Api
import Midfall.Generator.Models

namespace Midfall.Lowering
open Midfall Midfall.Halo2 YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-- Everything PLAN 9.5 names that is not ported yet, as DATA over existing types, plus the pins
    that keep the obligations non-vacuous (D2): the render options o₀ the lowered program came from,
    and lower_ok. A theorem over `S : Surface` becomes a theorem about the deployment when
    `realSurface` is built (P-11/P-12/P-13). -/
structure Surface (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
    [AdmissiblePairing G₁ G₂ Gₜ] where
  -- verifier side (PLAN's g)
  E : VerifierEnv p G₁ G₂ Gₜ
  params : ParamsVerifierKZG G₁ G₂
  vk : VerifyingKey (Fr p) G₁
  cfg : Midfall.Generator.GeneratorConfig
  accFixedBases : Array (AccFixedBase G₁)          -- contract's positive-base table (artifacts.rs:181-245)
  vkDigest : Word256                                -- the VK_DIGEST word hashed into alpha
  sG2gen : G₂                                       -- the G2 point NEG_S_G2_BASE is the inverse of
  encG2 : G₂ → Bytes                                -- abstract G2 encoder (no G2 codec in Common)
  -- lowered program (PLAN's L) and its render pin
  o₀ : Midfall.Generator.RenderOptions
  L : Lowered
  lower : Midfall.Generator.RenderOptions → Except Midfall.Generator.GeneratorError Lowered
  lower_ok : lower o₀ = .ok L
  bindLocals : YulBlock                             -- constant-substituted locals block (fuel pass, R-37)
  shell : YulObject                                 -- dispatcher wrapping headGuard ++ bindLocals ++ main
  shellLayout : EVM.Layout
  hoisted : FunEnv (Dialect ExternalCalls.none ExternalGas.none)  -- SKETCH: scope type; see mainScope below
  evaluatorRuntime : Option (YulBlock × EVM.Layout)
  runtimeName : String → String                     -- ir ↦ "<name>_<id>_deployed"
  -- codecs (P-12 ports; the Lean definitions of Calldata.lean are the spec)
  repackProof : Bytes → Except Midfall.Generator.RepackError Bytes
  encodeCalldata : Bytes → Array (Fr p) → Except Midfall.Generator.GeneratorError Bytes
  plan : PlanView
  -- render surface (P-13) and irCheck (M8)
  render : Midfall.Generator.RenderOptions → Except Midfall.Generator.GeneratorError String
  astOfMain : Midfall.Generator.RenderOptions → Option YulBlock   -- D-P15 yul% re-quote of the rendered main
  irCheck : YulObject → Bool
  -- predicates and the per-partial API
  Supported : Midfall.Generator.RenderOptions → Prop
  blk : Partial → YulBlock
  expectedVkCodehash : Option Word256
  quotientRuntime : Option Bytes
  expectedQuotientCodehash : Option Word256
  -- pins (hypothesis fields; proofs of these are P-11/P-12/P-13 deliverables)
  modulusPinned : p = Midfall.Assumptions.r
  vkDigest_spec : vkDigest = frWord vk.transcriptRepr
  hProofLayout : ∃ protocol numEvals numPointSets,
    ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets = .ok plan.proofLayout
  hRepack : ∀ π, repackProof π =
    Midfall.Lowering.repackProof (p := p) (RepackedProofLayoutPlan.fromProofLayout plan.proofLayout) E.g1 π
  hEncode : ∀ π inst, encodeCalldata π inst =
    Midfall.Lowering.encodeCalldata (p := p) cfg.numInstances (RepackedProofLayoutPlan.fromProofLayout plan.proofLayout) E.g1 π inst
  vkRuntime_spec : L.vkRuntime = ByteArray.mk #[0xfe] ++ plan.vk.bytes        -- EXPECTED_VK_LENGTH = len + 1
  main_concat : L.main = blk .vkLoading ++ blk .transcriptParser ++ blk .lagrange ++ blk .quotientLin ++
    blk .pcs ++ blk .finalPairing ++ blk .traceReturn                            -- SKETCH: helpers prefix
  shell_unfolds : True   -- SKETCH: the shell's verifyProof arm runs headGuard ++ bindLocals ++ main from the dispatcher memory

/-- Full PLAN 9.5 Supported over the plan view, with the corrections. -/
structure SupportedS (S : Surface p G₁ G₂ Gₜ) (o : Midfall.Generator.RenderOptions) : Prop where
  advice : S.vk.cs.numAdviceColumns ≠ 0
  instShape : S.vk.cs.numInstanceColumns = 2 ∧ S.cfg.numCommittedInstances = 1
  noRotInst : ∀ q ∈ S.vk.cs.instanceQueries.toList, q.2.int = 0          -- `.cur` and `.value 0` both denote 0
  acc : ∀ enc, S.cfg.accumulator = some enc →
    (enc.validateForNumInstances S.cfg.numInstances).isOk = true          -- Generator type (D-P16)
  singlePhase : S.vk.cs.numChallenges = 0
  hLimbs : S.vk.domain.getQuotientPolyDegree = S.vk.csDegree - 1          -- via WellFormed.domainConsistent
  vkPoints : ∀ C ∈ S.vk.fixedCommitments.toList ++ S.vk.permutation.commitments.toList,
    ∃ pt, g1Of? (S.E.g1.toEip C) = some pt ∧ g1PointMsmValid pt = true    -- over encodings
  layout : S.plan.memory.map.WellFormed ∧ (S.plan.memory.validate).isOk = true   -- D3
  qvm : True                                                               -- P-09e validator: Prop placeholder until it lands
  production : o.diagnostics.trace = false ∧ o.diagnostics.gasCheckpoints = false
  wf : S.vk.WellFormed Features.solidity

/-- What the world must look like, as hypotheses on an ExecEnv and on H (Y-2). -/
structure DeploymentW (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (vkAddr quotientAddr : U256) : Prop where
  keccak : W.keccakOf = hashOfBytes H
  wf : W.WF                                                                 -- SKETCH: ExecEnv.WF
  callvalue : W.callvalue = 0                                               -- attack: non-payable dispatcher
  static : W.static = false
  vkCode : S.expectedVkCodehash.isSome → W.extCodeOf vkAddr = S.L.vkRuntime.data.toList
  vkNonEmpty : S.L.vkRuntime.size ≠ 0
  vkHash : ∀ h, S.expectedVkCodehash = some h → H S.L.vkRuntime = h
  vkImm : S.expectedVkCodehash.isSome →
    S.shellLayout.immutable (litValue (.string "AUTHORIZED_VK")) = vkAddr           -- attack: loadimmutable link
  qCode : ∀ code, S.quotientRuntime = some code → W.extCodeOf quotientAddr = code.data.toList
  qHash : ∀ code h, S.quotientRuntime = some code → S.expectedQuotientCodehash = some h → H code = h
  qNonEmpty : ∀ code, S.quotientRuntime = some code → code.size ≠ 0
  qImm : S.quotientRuntime.isSome →
    S.shellLayout.immutable (litValue (.string "AUTHORIZED_QUOTIENT")) = quotientAddr
  memguard : True   -- SKETCH: the IR's memoryguard value ≤ 0x1000 (completeness; stated once ImportSolcIR exists)
  disjoint : accountKey vkAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
             accountKey quotientAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
             accountKey vkAddr ≠ accountKey quotientAddr

theorem extcodehash_of_deployment {S W H vkAddr qa} {hsh : U256} (D : DeploymentW S W H vkAddr qa)
    (h : S.expectedVkCodehash = some hsh) : projectedCodeHash W W.balanceOf vkAddr = hsh := by sorry

/-- Entry frames. verifier_sound is for ANY mem₀ above the solc scratch (attack: g1_identity window). -/
def initState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes) (mem₀ : Nat → UInt8) : EvmState :=
  { EvmState.init with memory := mem₀,
    env := { W with calldata := cd.data.toList, code := Lyt.code, dataOffset := Lyt.dataOffset,
             dataSize := Lyt.dataSize, immutable := Lyt.immutable, keccakOf := hashOfBytes H } }  -- SKETCH Layout fields
def callState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes) : EvmState := initState W Lyt H cd (fun _ => 0)
def ZeroAbove (mem₀ : Nat → UInt8) : Prop := ∀ a, 0x80 ≤ a → mem₀ a = 0

def Surface.calls (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : PairingProduct) (quotientAddr : U256) : ExternalCalls :=
  honestCalls product quotientAddr (match S.evaluatorRuntime with
    | some (rt, Lyt) => Evaluator.rel W Lyt quotientAddr rt
    | none => fun _ _ _ => False)

def RunVerifier (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (cd : Bytes) (mem₀ : Nat → UInt8)
    (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g (S.L.headGuard ++ S.bindLocals ++ S.L.main) (initState W S.shellLayout H cd mem₀) V' obs.state obs.outcome

def Surface.irRuntime (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Option YulBlock :=
  (ir.subObject (S.runtimeName ir.name)).map Object.codeBlock          -- SKETCH: Object.name

def RunContractIR (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (ir : YulObject) (irLyt : EVM.Layout)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ rt V', S.irRuntime ir = some rt ∧ RunCommitted c g rt (callState W irLyt H cd) V' obs.state obs.outcome

def RunShell (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g S.shell.codeBlock (callState W S.shellLayout H cd) V' obs.state obs.outcome

/-- Observational equivalence at the view level (memory and VEnv are not observable). -/
def ObsEquiv (R₁ R₂ : Obs → Prop) : Prop :=
  ∀ v : ObsView, (∃ o, R₁ o ∧ o.view = v) ↔ (∃ o, R₂ o ∧ o.view = v)

/-- PLAN 9.5 LeanAccepts over raw calldata and raw instance words. -/
def LeanAccepts (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) ∧
    ContractRefAcceptsAcc S.E H S.params S.vk S.cfg.accumulator S.vkDigest S.accFixedBases instW ms = true

/-- Adjustment 3: the decoded public accumulator of a calldata, so snapshots in accumulator renders
    carry it (`none` would silently state every acc-mode per-partial spec about a no-acc snapshot). -/
def accOf (S : Surface p G₁ G₂ Gₜ) (instW : Array Word256) : Option (KzgAcc (Fr p) G₁ G₂ Gₜ) :=
  S.cfg.accumulator.bind fun enc => decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) S.E.g1 S.accFixedBases instW

/-- Completeness side condition (R-2 first face), via the snapshot (no schedule replay). -/
def GenericX (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) : Prop :=
  ∀ Snap, snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap → ChallengesGood S.vk Snap

/-- Soundness side condition (finding 5), operational: the Lean pipeline does not hit the logup inversion panic. -/
def NoLogupPanic (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms : List (Msg (Fr p) G₁)) (inst : Array (Fr p)) : Prop :=
  prepareMsgs (Gₜ := Gₜ) S.E H Features.solidity S.vk inst ms ≠ .error (Fault.panic "proofs/src/plonk/logup.rs:460")

/-- The evaluator's calldata = memory[vk_mptr, vk_mptr + frame_len) (quotient.rs:760-794). -/
structure EvaluatorFrame where
  base : Nat
  len : Nat
  mem : Nat → UInt8
def EvaluatorFrame.bytes (f : EvaluatorFrame) : List UInt8 := (List.range f.len).map (fun i => f.mem (f.base + i))
def EvaluatorFrame.word (f : EvaluatorFrame) (a : Nat) : Word256 := loadWord f.mem a
def tokenBase (lay : Midfall.Generator.VerifierMemoryLayout) : Nat → Nat := sorry -- SKETCH: 1↦l0,2↦lLast,3↦lBlind,4↦beta,5↦gamma,6↦x,7↦theta,8↦trash,9↦instanceEval
/-- THE FRAME CONTAINS THE PROGRAM: pin the VK window to the lowered payload or the statement is false. -/
def FrameWellFormed (S : Surface p G₁ G₂ Gₜ) (f : EvaluatorFrame) : Prop :=
  f.base = ptrAddr S.plan.vkMptr ∧
  (∀ q, S.plan.qext = some q → f.len = q.frameLen) ∧                       -- SKETCH field
  (∀ i, i < S.plan.vk.len → f.mem (f.base + i) = S.plan.vk.bytes.get! i) ∧
  (∀ a, (f.word a).toNat < Midfall.Generator.qvmFrModulus)                 -- PUSH_MEM is a raw mload; stated on operand reads in the implementation
end Midfall.Lowering
```

### N. `Midfall/Lowering/Partials.lean`

```lean
import Midfall.Lowering.Surface
import Midfall.Yul.Contracts
import Midfall.Assumptions.Eip2537

namespace Midfall.Lowering
open Midfall Midfall.Halo2 YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

def Reverted (st : EvmState) : Prop := ∃ d, st.halted = some (.revert, d)

/-- Soundness relation (Y-1): any success must be the honest one; failure always allowed. -/
def PermissiveFor (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : PairingProduct) (qAddr : U256) (calls : ExternalCalls) : Prop :=
  ∀ req st resp, calls.Call req st resp → resp.success = true → (S.calls W product qAddr).Call req st resp

/-- The scope every partial runs in: the hoisted helpers of the main block (fail, scalar_inv,
    squeeze_to, batch_invert, ec_pairing, validate_public_accumulator). -/
def mainScope (S : Surface p G₁ G₂ Gₜ) (calls gas) (outer : FunEnv (Dialect calls gas)) : FunEnv (Dialect calls gas) :=
  hoist (Dialect calls gas) S.L.main :: outer

/-- Soundness shape of one partial: every run from Inv (pre) reverts or continues into Inv (next). -/
def PartialSound (S : Surface p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (calls gas)
    (extra : VEnv (Dialect calls gas) → EvmState → Prop) : Prop :=
  ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk q)
    (fun V st => Inv S.E S.params S.accFixedBases q.pre S.plan Snap V st)
    (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
      (o = .normal ∧ Inv S.E S.params S.accFixedBases q.pre.next S.plan Snap V' st' ∧ extra V' st'))

/-- Progress shape under the honest functional relation: no revert. -/
def PartialProgress (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : PairingProduct) (qAddr : U256)
    (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (gas : ExternalGas) : Prop :=
  ∀ outer, StmtsContractAll (D := Dialect (S.calls W product qAddr) gas) (mainScope S _ gas outer) (S.blk q)
    (fun V st => Inv S.E S.params S.accFixedBases q.pre S.plan Snap V st)
    (fun _ _ V' st' o => o = .normal ∧ Inv S.E S.params S.accFixedBases q.pre.next S.plan Snap V' st')

/-- 'Fault ⇒ revert' shape: when the Lean pipeline faults at stage k, every run of the partial
    guarding k reverts (attack fix: per-phase prefixes). -/
def PartialRejects (S : Surface p G₁ G₂ Gₜ) (q : Partial) (calls gas) (pre : VEnv (Dialect calls gas) → EvmState → Prop) : Prop :=
  ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk q) pre
    (fun _ _ _ st' o => o = .halt ∧ Reverted st')

/-- The per-partial obligations. Common hypotheses (abbreviated H*): SupportedS S S.o₀; EnvAgrees;
    PermissiveFor for *_sound; decodeCalldata cd = some (ms, instW) ∧ instOfWords? instW = some inst
    with st.env.calldata = cd.data.toList; snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap
    (adjustment 3: the snapshot carries the decoded public accumulator in accumulator renders). -/
structure PartialSpecs (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) : Prop where
  vkLoading_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    PartialSound S .vkLoading Snap calls gas (fun _ _ => True)
  transcriptParser_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    PartialSound S .transcriptParser Snap calls gas (fun _ _ => True)
  /-- a normal exit PROVES xNotRoot: batch_invert rejected zero (the contract is stricter here) -/
  lagrange_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    PartialSound S .lagrange Snap calls gas (fun _ _ => Snap.alg.x ^ S.vk.domain.n ≠ 1)
  quotientLin_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    PartialSound S .quotientLin Snap calls gas (fun _ _ => True)
  pcs_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    PartialSound S .pcs Snap calls gas (fun _ _ => True)
  finalPairing_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
    PartialSound S .finalPairing Snap calls gas (fun V' _ => VEnv.get V' "success" = some 1)
  traceReturn_sound : ∀ H W qAddr calls gas cd ms instW inst Snap, /- H* -/
    ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk .traceReturn)
      (fun V st => Inv S.E S.params S.accFixedBases .pairing S.plan Snap V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue))
  -- fault ⇒ revert twins, keyed by the stage snapshotOf reports
  transcript_rejects : ∀ H W qAddr calls gas cd, /- SupportedS, EnvAgrees, calldata = cd -/
    decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = none →
    PartialRejects S .transcriptParser calls gas (fun V st => ∃ Snap, Inv S.E S.params S.accFixedBases .vk S.plan Snap V st)
  pcs_rejects : ∀ H W qAddr calls gas cd ms instW inst f, /- H* without the snapshot -/
    snapshotOf S.E H S.vk inst ms (accOf S instW) = .error (.pcs, f) →
    PartialRejects S .pcs calls gas (fun V st => ∃ Snap, Inv S.E S.params S.accFixedBases .quotient S.plan Snap V st)
  -- progress twins (honest calls, ofFun gas), each with its side condition
  vkLoading_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/ PartialProgress S W product qAddr .vkLoading Snap (ExternalGas.ofFun fun _ => 0)
  transcriptParser_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/ PartialProgress S W product qAddr .transcriptParser Snap (ExternalGas.ofFun fun _ => 0)
  lagrange_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/ ChallengesGood S.vk Snap →
    PartialProgress S W product qAddr .lagrange Snap (ExternalGas.ofFun fun _ => 0)
  quotientLin_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/ PartialProgress S W product qAddr .quotientLin Snap (ExternalGas.ofFun fun _ => 0)
  pcs_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/ PartialProgress S W product qAddr .pcs Snap (ExternalGas.ofFun fun _ => 0)
  finalPairing_progress : ∀ H W qAddr cd ms instW inst Snap, /- H* -/
    Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product → DualMSM.check Snap.c.dual S.params = true →
    PartialProgress S W product qAddr .finalPairing Snap (ExternalGas.ofFun fun _ => 0)

/-- Pulled-forward finalPairing_spec, no-accumulator arm, stated over the concrete partial block
    (proof after P-13 delivers AssemblyHelpers.yul + FinalPairing.yul as Block EVM.Op). The ec_pairing
    frame is [RHS|G2_BASE|LHS|NEG_S_G2] because FinalPairing.yul:88 passes (RHS, LHS) into a
    [lhs|G2|rhs|NEG_S_G2] layout (AssemblyHelpers.yul:284-287); the decision is DualMSM.check via
    dualMsm_check_iff_contract and Eip2537.Holds.pairing2. Production only (:86, AH:296, AH:307-308). -/
theorem finalPairing_sound_noAcc (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) (W : ExecEnv) (qAddr : U256)
    (H : Hash) (Snap : Snapshot p G₁ G₂ Gₜ) (calls : ExternalCalls) (gas : ExternalGas)
    (hsup : SupportedS S S.o₀) (hperm : PermissiveFor S W product qAddr calls)
    (hH : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen S.encG2 S.accFixedBases) (hacc : S.plan.hasAccumulator = false) :
    ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk .finalPairing)
      (fun V st => Inv S.E S.params S.accFixedBases .pcs S.plan Snap V st)
      (fun _ _ V' st' o =>
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "success" = some 1 ∧
           DualMSM.check Snap.c.dual S.params = true ∧ Inv S.E S.params S.accFixedBases .pairing S.plan Snap V' st')) := by
  sorry

theorem finalPairing_progress_noAcc (S) (product) (W) (qAddr) (H) (Snap) (hsup) (hH) (henv) (hacc)
    (hcheck : DualMSM.check Snap.c.dual S.params = true) :
    ∀ outer, StmtsContractAll (D := Dialect (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0))
      (mainScope S _ _ outer) (S.blk .finalPairing)
      (fun V st => Inv S.E S.params S.accFixedBases .pcs S.plan Snap V st ∧ VEnv.get V "success" = some 1)
      (fun _ _ V' st' o => o = .normal ∧ Inv S.E S.params S.accFixedBases .pairing S.plan Snap V' st') := by
  sorry

/-- Accumulator arm (FinalPairing.yul:14-61 then :88): preimage tag ‖ VK_DIGEST ‖ RHS ‖ LHS ‖ ACC_RHS ‖
    ACC_LHS at the 0x1000 batch buffer, alpha = keccak mod r with 0 ↦ 1 (= alphaOf), slots rewritten in
    place via G1MSM then G1ADD, decision = batchedCheck in DualMSM orientation. -/
theorem finalPairing_sound_acc (S) (product) (W) (qAddr) (H) (Snap) (calls) (gas) (hsup) (hperm) (hH) (henv)
    (henc : S.plan.hasAccumulator = true) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (hS : Snap.acc = some a)
    (hkec : ∀ V st, Inv S.E S.params S.accFixedBases .pcs S.plan Snap V st → st.env.keccakOf = hashOfBytes H) :
    let tbl := tblOf S.plan S.accFixedBases
    ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk .finalPairing)
      (fun V st => Inv S.E S.params S.accFixedBases .pcs S.plan Snap V st)
      (fun _ _ V' st' o =>
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "success" = some 1 ∧
           batchedCheck S.params
             (alphaOf (p := p) H S.vkDigest S.E.g1 Snap.c.dual.left.eval Snap.c.dual.right.eval
               (a.fullyCollapse tbl).1 (a.fullyCollapse tbl).2)
             Snap.c.dual a tbl = true)) := by
  sorry

/-- Production TraceReturn: `if iszero(success) fail(ERR_PROOF_REJECTED); mstore(RETURN_MPTR, 1);
    return(RETURN_MPTR, 0x20)` with RETURN_MPTR = verifierReturnMptr = 0x1000. -/
theorem traceReturn_spec (S : Surface p G₁ G₂ Gₜ) (Snap : Snapshot p G₁ G₂ Gₜ) (calls : ExternalCalls) (gas : ExternalGas)
    (hsup : SupportedS S S.o₀) :
    ∀ outer, StmtsContractAll (D := Dialect calls gas) (mainScope S calls gas outer) (S.blk .traceReturn)
      (fun V st => Inv S.E S.params S.accFixedBases .pairing S.plan Snap V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) := by
  sorry
end Midfall.Lowering
```

### O. `Midfall/Lowering/Qvm.lean`

```lean
import Midfall.Generator.Quotient.VmReference
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmCertify
import Midfall.Assumptions.Pairing

namespace Midfall.Lowering
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientMem QuotientRefMemory fqFromU256 qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus)
-- never `open Midfall.Generator.QVM` (QVM.Fr shadows Midfall.Fr)

theorem qvmFrModulus_eq_r : qvmFrModulus = Midfall.Assumptions.r := by decide  -- fallback rfl

abbrev FrR := Midfall.Fr Midfall.Assumptions.r
def qvmToFr (v : QVMFr) : FrR := (v : FrR)
theorem qvmToFr_add (a b : QVMFr) : qvmToFr (qvmFrAdd a b) = qvmToFr a + qvmToFr b := by sorry
theorem qvmToFr_mul (a b : QVMFr) : qvmToFr (qvmFrMul a b) = qvmToFr a * qvmToFr b := by sorry
theorem qvmToFr_neg (a : QVMFr) (ha : a < qvmFrModulus) : qvmToFr (qvmFrNeg a) = - qvmToFr a := by sorry
theorem qvmToFr_injOn (a b : QVMFr) (ha : a < qvmFrModulus) (hb : b < qvmFrModulus) (h : qvmToFr a = qvmToFr b) : a = b := by sorry

/-- A valuation of verifier memory: domain 0 = literal pointers, domain 1+t = token t; keys wrap like
    the cache key ((1+t) % 256, addr % 2^32), so token 0xff lands in the literal domain (KAT
    tokenDomainU8Wrap_releaseProfile_ok). -/
abbrev Valuation := Nat → Nat → QVMFr
def memKey : QuotientMem → Nat × Nat
  | .literal ptr => (0, ptr % 2 ^ 32)
  | .token t => ((1 + t) % 256, 0)
  | .tokenOffset t o => ((1 + t) % 256, o % 2 ^ 32)

/-- Shadow denotation of an expression under a valuation. -/
def evalExprρ (ρ : Valuation) : QuotientExpr → Except QVMFault QVMFr
  | .const v => fqFromU256 v
  | .mem m => .ok (ρ (memKey m).1 (memKey m).2)
  | .add l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrAdd a b)
  | .mul l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrMul a b)
  | .neg e => do let a ← evalExprρ ρ e; pure (qvmFrNeg a)

/-- A reference memory whose cache is pre-populated from ρ on the keys S: the ported interpreter
    reads ρ (cache hits, VmReference.lean:433-438) — ∀ρ statements without touching VmReference. -/
def memOfρ (ρ : Valuation) (S : List (Nat × Nat)) : QuotientRefMemory :=
  { seed := Midfall.Bytes.empty,
    cache := S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32, ρ (k.1 % 256) (k.2 % 2 ^ 32))) }
def NoMiss (m m' : QuotientRefMemory) : Prop := m'.cache = m.cache
def CacheConsistent (m : QuotientRefMemory) : Prop :=
  ∀ e ∈ m.cache, e.2.2 = Midfall.Generator.deriveReferenceMemory m.seed e.1 e.2.1 ∧ e.1 < 256 ∧ e.2.1 < 2 ^ 32
def leafKeys (e : QuotientExpr) : List (Nat × Nat) := e.memLeaves.map memKey   -- SKETCH: memLeaves

theorem evalQuotientExpr_memOfρ (ρ : Valuation) (e : QuotientExpr) (S : List (Nat × Nat))
    (hS : ∀ k ∈ leafKeys e, k ∈ S) :
    Midfall.Generator.evalQuotientExpr e (memOfρ ρ S) = (evalExprρ ρ e).map (fun v => (v, memOfρ ρ S)) := by sorry

open Midfall.Generator (QuotientLimbShape QuotientModarith7Shape QuotientShapeRecognizers noShapeRecognizers)

def denoteLin (ρ : Valuation) (terms : List (Midfall.Word256 × Nat)) : Except QVMFault QVMFr :=
  terms.foldlM (fun acc t => do let c ← fqFromU256 t.1; pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) 0
/-- Value of a recognised limb shape under ρ, following the byte decoders (VmReference.lean:577-634). -/
def denoteLimbShape (ρ : Valuation) : QuotientLimbShape → Except QVMFault QVMFr
  | .lin7 terms => denoteLin ρ terms
  | .bilin7Row lhs terms => do let inner ← denoteLin ρ terms; pure (qvmFrMul (ρ 0 (lhs % 2 ^ 32)) inner)
  | .bilin7Pairwise a b coeffs =>
    (List.range 7).foldlM (fun acc i => (List.range 7).foldlM (fun acc j => do
        let c ← fqFromU256 (coeffs.getD (i + j) 0)
        pure (qvmFrAdd acc (qvmFrMul (qvmFrMul (ρ 0 ((a + 32 * i) % 2 ^ 32)) (ρ 0 ((b + 32 * j) % 2 ^ 32))) c))) acc) 0
/-- modarith7Form (VmReference.lean:636-700). -/
def denoteModarith7 (ρ : Valuation) (sh : QuotientModarith7Shape) : Except QVMFault QVMFr := by
  sorry -- SKETCH: const + Σ lin + Σ rows + Σ pairwise + Σ c·mem + Σ c·l·r, × mload(cond) when present
def shapePtrsU16 : QuotientLimbShape → Prop := sorry           -- every pointer ≤ 0xffff (emitU16 exactness)
def modarith7WellFormed (sh : QuotientModarith7Shape) : Prop := sorry -- 7 terms/lin & row, 13 coeffs, counts ≤ 255, ptrs ≤ 0xffff

/-- Soundness of the recognizer hooks (P-09f unported): a recognised shape denotes the expression
    under EVERY valuation. Compile correctness is false for arbitrary hooks. -/
structure RecognizersSound (r : QuotientShapeRecognizers) : Prop where
  pow5 : ∀ e b, r.pow5Base e = some b → ∀ ρ,
    evalExprρ ρ e = (evalExprρ ρ b).map (fun v => qvmFrMul v (qvmFrMul (qvmFrMul v v) (qvmFrMul v v)))
  limb : ∀ e sh, r.limbShape e = some sh → sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ, evalExprρ ρ e = denoteLimbShape ρ sh
  limbSub : ∀ e sh res matched, r.limbSubshape e = some (sh, res, matched) →
    matched ≠ [] ∧ sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ,
      evalExprρ ρ e = (do let a ← denoteLimbShape ρ sh; let b ← evalExprρ ρ res; pure (qvmFrAdd a b)) ∧
      denoteLimbShape ρ sh = matched.foldlM (fun acc m => do pure (qvmFrAdd acc (← evalExprρ ρ m))) 0
  modarith7 : ∀ e sh, r.modarith7Shape e = some sh → modarith7WellFormed sh ∧ ∀ ρ, evalExprρ ρ e = denoteModarith7 ρ sh

theorem noShapeRecognizers_sound : RecognizersSound noShapeRecognizers := by
  constructor <;> intros <;> simp_all [noShapeRecognizers]

/-- Operand widths the builder encodes exactly (pushByte pushes raw Nats, emitU32 truncates). -/
def exprBounded : QuotientExpr → Prop
  | .const _ => True
  | .mem (.literal ptr) => ptr < 2 ^ 32
  | .mem (.token t) => t < 256
  | .mem (.tokenOffset t o) => t < 256 ∧ o < 2 ^ 32
  | .add l r | .mul l r => exprBounded l ∧ exprBounded r
  | .neg e => exprBounded e

open Midfall.Generator.QuotientBuilder (QuotientProgramBuilder M identityExpr nativePermutation nativeLookup nativeIdentity finish withLimbVmOps compactQuotientRuns finalizedIdentitySegment)

/-- Per-identity compile correctness, ∀ρ (strictly stronger than the certifier's single Schwartz-Zippel
    sample). VALUES ONLY (attack fix): a sound recognizer may read a pointer outside leafKeys e, so the
    returned memory is existential. -/
theorem qvm_compile_correct_identity (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
    (s₀ s₁ : QuotientProgramBuilder) (e : QuotientExpr) (t : Midfall.Generator.QuotientTarget) (gap : Option Nat)
    (hb : exprBounded e) (hemit : identityExpr r s₀ e t gap = .ok s₁)
    (hconsts : ∀ c ∈ s₁.consts, c.toNat < qvmFrModulus)
    (cseg seg : List Nat)
    (hcompact : compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg)
    (hseg : finalizedIdentitySegment cseg = some seg)
    (ρ : Valuation) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e)) = .ok (v, mem') ∧
      evalExprρ ρ e = .ok v := by sorry

open Midfall.Generator (QuotientProgramItem QuotientProgramPlan QuotientProgramBuild SelectorFoldPlan)

/-- The plan-items driver (quotient.rs:2120 is unported); mirrors QuotientCertifyKats.buildStream with `r`. -/
def buildItems (r : QuotientShapeRecognizers) (sf : SelectorFoldPlan) :
    List QuotientProgramItem → QuotientProgramBuilder → M QuotientProgramBuilder
  | [], s => .ok s
  | .identity id :: rest, s => do buildItems r sf rest (← identityExpr r s id.expr id.target (sf.gapFor id))
  | .nativePermutation :: rest, s => do buildItems r sf rest (← nativePermutation s)
  | .nativeLookup :: rest, s => do buildItems r sf rest (← nativeLookup s)
  | .nativeIdentity i :: rest, s => do buildItems r sf rest (← nativeIdentity s i)
def buildPlan (r : QuotientShapeRecognizers) (plan : QuotientProgramPlan) (s₀ : QuotientProgramBuilder) : M QuotientProgramBuild :=
  buildItems r plan.selectorFold plan.items s₀ >>= finish

/-- Form (a): the certifier walk succeeds on every consistent memory and consumes the whole stream. -/
theorem qvm_compile_correct_certifier (r) (hr : RecognizersSound r) (plan : QuotientProgramPlan) (limbOps : Bool)
    (build : QuotientProgramBuild) (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < qvmFrModulus)
    (mem : QuotientRefMemory) (hcc : CacheConsistent mem) :
    ∃ mem', Midfall.Generator.QuotientCertify.certifyItemWalk plan build (Midfall.Generator.qvmBytesToNats build.bytes) mem =
      .ok ((Midfall.Generator.qvmBytesToNats build.bytes).length, mem') := by sorry
theorem qvm_compile_correct_program (r) (hr) (plan) (limbOps) (build) (hbuild) (hbounded) (hconsts)
    (vk : Midfall.Generator.Halo2VerifyingKey) :
    Midfall.Generator.QuotientCertify.certifyQuotientProgram plan build vk = .ok () := by sorry

/-- D-P20 item 2 restated over the two real fault classes (no `.oob` exists): builder-produced
    segments never fault at all on any memory when constants are canonical. -/
theorem builder_segments_total (r) (hr : RecognizersSound r) (plan) (limbOps) (build) (hbuild) (hbounded) (hconsts)
    (cursor exprEnd foldOp : Nat) (hstart : cursor ∈ itemStarts plan build)   -- SKETCH: from quotientOpLen
    (hseg : Midfall.Generator.QuotientCertify.identitySegment (Midfall.Generator.qvmBytesToNats build.bytes) cursor = .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity
      (((Midfall.Generator.qvmBytesToNats build.bytes).drop cursor).take (exprEnd - cursor)) build.consts mem = .ok (v, mem') := by sorry
end Midfall.Lowering
```

### P. `Midfall/Lowering/QvmFold.lean`

```lean
import Midfall.Lowering.Qvm
import Midfall.Halo2.Exec.Linearization
import Midfall.Halo2.Exec.VerifyingKey

namespace Midfall.Lowering
open Midfall.Generator (QuotientIdentity QuotientProgramItem QuotientProgramPlan SelectorFoldPlan QVMFr qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus)

/-- The global y-order: inline prefix, items with native markers expanded, structured tail
    (QuotientNumeratorBlock.yul:198, :1205-1279, :1368). -/
def expandItem (plan : QuotientProgramPlan) : QuotientProgramItem → List QuotientIdentity
  | .identity id => [id]
  | .nativePermutation => plan.nativePermutationIdentities   -- SKETCH field names
  | .nativeLookup => plan.nativeLookupIdentities
  | .nativeIdentity i => (plan.nativeIdentities[i]?).toList
def globalIdentities (plan : QuotientProgramPlan) : List QuotientIdentity :=
  plan.inlineIdentities ++ plan.items.flatMap (expandItem plan) ++ plan.structuredTailIdentities

def qvmFrPow (y : QVMFr) : Nat → QVMFr
  | 0 => 1 % qvmFrModulus
  | n + 1 => qvmFrMul (qvmFrPow y n) y

structure FoldState where
  qn : QVMFr
  buckets : List QVMFr   -- indexed by position in plan.sortedSimple

/-- FOLD_MAIN (yul:1284-1299): qn := qn·y + v. FOLD_SELECTOR (yul:1303-1341): qn := qn·y and
    bucket[s] := bucket[s]·y^gap (if gap ≠ 0) + v. -/
def foldStep (y : QVMFr) (sf : SelectorFoldPlan) (st : FoldState) (id : QuotientIdentity) (v : QVMFr) : FoldState :=
  match id.target with
  | .main => { st with qn := qvmFrAdd (qvmFrMul st.qn y) v }
  | .selector s =>
    let gap := (sf.gapFor id).getD 0
    { qn := qvmFrMul st.qn y,
      buckets := st.buckets.modify (fun b => qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow y gap)) v) s }

/-- The whole-stream fold (NEW definition, D-P20 addendum): (QUOTIENT_EVAL = -qn, buckets after tails). -/
def quotientFold (plan : QuotientProgramPlan) (y : QVMFr) (vals : List QVMFr) : QVMFr × List QVMFr :=
  let init : FoldState := { qn := 0, buckets := List.replicate plan.sortedSimple.length 0 }
  let st := (List.zip (globalIdentities plan) vals).foldl (fun st iv => foldStep y plan.selectorFold st iv.1 iv.2) init
  (qvmFrNeg st.qn, List.zipWith (fun b t => qvmFrMul b (qvmFrPow y t)) st.buckets plan.selectorFold.tailExponents)

/-- What quotient_program_plan / selector_fold_plan (P-10) guarantee about gaps and tails. -/
def SelectorFoldConsistent (plan : QuotientProgramPlan) : Prop :=
  let ids := globalIdentities plan
  plan.sortedSimple.Sorted (· < ·) ∧
  (∀ i (h : i < ids.length), ids[i].meta_.globalIndex = i) ∧
  (∀ i (h : i < ids.length) s, ids[i].target = .selector s → s < plan.sortedSimple.length ∧
     ∀ j (hj : j < i), ids[j].target = .selector s →
       (∀ k, j < k → k < i → ∀ hk, (ids[k]'hk).target ≠ .selector s) →
       plan.selectorFold.gapFor ids[i] = some (i - j)) ∧
  plan.selectorFold.tailExponents.length = plan.sortedSimple.length ∧
  (∀ s (hs : s < plan.sortedSimple.length), (∃ i (h : i < ids.length), ids[i].target = .selector s) ∧
     ∀ i (h : i < ids.length), ids[i].target = .selector s →
       (∀ k, i < k → ∀ hk, (ids[k]'hk).target ≠ .selector s) →
       plan.selectorFold.tailExponents[s] = ids.length - 1 - i)

/-- Bridge to the Lean verifier's tagged expression array: same length, same values, bucket s ↔
    fixed column plan.sortedSimple[s] (quotient_expr_from_expression is unported). -/
def IdentityCorrespondence (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) : Prop :=
  let ids := globalIdentities plan
  exprs.size = ids.length ∧ vals.length = ids.length ∧
  ∀ i (h : i < ids.length), (exprs[i]'(by omega)).2 = qvmToFr (vals[i]'(by omega)) ∧
    (match ids[i].target with
     | .main => (exprs[i]'(by omega)).1 = none
     | .selector s => (exprs[i]'(by omega)).1 = plan.sortedSimple[s]?)

/-- The fold equals computeLinearizationCommitment's reverse y-fold (Linearization.lean:68-110,
    R-16/R-19): identity i gets y^(m-1-i); None bucket subtracts into the eval; Some buckets appear in
    ascending column order = ascending s. -/
theorem quotientFold_matches_linearization {G₁ : Type} (plan : QuotientProgramPlan)
    (hcons : SelectorFoldConsistent plan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) (hvals : ∀ v ∈ vals, v < qvmFrModulus)
    (hcorr : IdentityCorrespondence plan exprs vals)
    (vk : Midfall.Halo2.VerifyingKey FrR G₁) (x y xn sf : FrR) (limbs : Array G₁) (q : Midfall.Halo2.VerifierQuery FrR G₁)
    (hq : Midfall.Halo2.computeLinearizationCommitment exprs vk x y xn sf limbs = .ok q) :
    let r := quotientFold plan y.val vals
    q.eval = qvmToFr r.1 ∧
    ∃ pts labs, q.commitment = .linear pts ((limbScalars limbs.size xn sf) ++ r.2.map qvmToFr).toArray labs := by
  sorry -- SKETCH: limbScalars n xn sf = the n scalars (1 - xn)·sf^i (Linearization.lean:84-90)
-- KAT rule (R-30): ≥ 2 main and ≥ 2 selector identities, interleaved; an off-by-one gap flips a bucket by y.
end Midfall.Lowering
```

### Q. `Midfall/Lowering/Obligations.lean` — the headline

```lean
import Midfall.Lowering.Surface
import Midfall.Lowering.Partials
import Midfall.Lowering.QvmFold
import Midfall.Lowering.SemanticEquivalence
import Midfall.Assumptions.Eip2537
import Midfall.Assumptions.Codec

namespace Midfall.Lowering
open Midfall Midfall.Halo2 YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Both bad-set side conditions for a calldata (finding 4 completeness, finding 5 soundness). -/
def SideConditions (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → GenericX S H ms instW inst ∧ NoLogupPanic S H ms inst
def SoundSide (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → NoLogupPanic S H ms inst
def CompleteSide (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∀ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst → GenericX S H ms instW inst

/-- The headline obligations over a Surface. Every field assumes `SupportedS S S.o₀` (D2: the options the
    lowered program came from, so a trace-render L cannot pass with a production o) and quantifies over
    all H (PLAN 10.3), with DeploymentW pinning H on the two code strings (Y-2). Deployment target:
    H := keccak256. Future deliverable: `theorem lowering_correct : LoweringCorrect realSurface product`. -/
structure LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) : Prop where
  /-- ANY run of the assembly, from ANY memory zero above the solc scratch (attack: the g1_identity
      window must be zero), under adversarial precompiles and ANY gas oracle, that returns, returns
      abiTrue and Lean accepts. Side condition: NoLogupPanic (finding 5). -/
  verifier_sound : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (mem₀ : Nat → UInt8)
      (gas : ExternalGas) (obs : Obs),
    SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
    Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
    ZeroAbove mem₀ →
    RunVerifier S W H cd mem₀ (permissive (S.calls W product qAddr)) gas obs → obs.isReturn →
    SoundSide S H cd →
    obs.returnData = abiTrue ∧ LeanAccepts S H cd
  /-- Lean accepts ⇒ an honest shell run exists and every honest run returns abiTrue (view-level).
      Side condition: GenericX (finding 4); needs EnvAgrees.omegaOrder/domainN and toEip 1 = zeros. -/
  verifier_complete : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes),
    SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
    Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
    EnvAgrees S.E S.vk S.plan S.params S.sG2gen S.encG2 S.accFixedBases → Midfall.Assumptions.G1CodecLaws S.E.g1 →
    LeanAccepts S H cd → CompleteSide S H cd →
    (∃ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
    (∀ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
       obs.view = returnView (callState W S.shellLayout H cd))
  /-- Only two outcomes, read-only — on the verifyProof arm (attack: the BUILD_ID()/AUTHORIZED_*
      getters return other data). -/
  only_two_outcomes : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (gas : ExternalGas) (obs : Obs),
    SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr →
    bytesTake cd 0 4 = some fnSigVerifyProof →
    RunShell S W H cd (permissive (S.calls W product qAddr)) gas obs →
    obs.view = returnView (callState W S.shellLayout H cd) ∨
    (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W S.shellLayout H cd))
  /-- M8: the imported via-ir object refines the shell model, for world-local calls and a fixed gas
      oracle (attack: a relation reading caller memory separates IR from shell). -/
  ir_refines : ∀ (ir : YulObject) (irLyt : EVM.Layout), S.irCheck ir = true →
    ∀ (W : ExecEnv) (H : Hash) (cd : Bytes) (c : ExternalCalls) (g₀ : U256), c.WorldLocal →
    ObsEquiv (RunContractIR S W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
             (RunShell S W H cd c (ExternalGas.ofFun fun _ => g₀))
  /-- D-P13 structural render_eq_print (R-39: the text equation is false and is dropped). -/
  render_eq_print : ∀ o L, S.lower o = .ok L →
    ∀ ast, S.astOfMain o = some ast → YulSemantics.SyntaxEq.stmtsBeq ast L.main = true
  /-- end_to_end_noAcc with the RHS carrying an existence conjunct (PLAN's `∀ obs` alone is vacuous
      when no run exists), the RepackError lift (attack: the two error types never met), the
      instance-length check and the modulus bound. -/
  end_to_end_noAcc : S.cfg.accumulator = none → ∀ (W : ExecEnv) (vkAddr qAddr : U256) (ir : YulObject) (irLyt : EVM.Layout)
      (inst : Array (Fr p)) (π : Bytes),
    SupportedS S S.o₀ → DeploymentW S W keccak256 vkAddr qAddr →
    Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product → Midfall.Assumptions.G1CodecLaws S.E.g1 →
    EnvAgrees S.E S.vk S.plan S.params S.sG2gen S.encG2 S.accFixedBases →
    S.irCheck ir = true → inst.size = S.cfg.numInstances → p ≤ 2 ^ 256 →
    (∀ ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
       GenericX S keccak256 ms (inst.map frWord) inst ∧ NoLogupPanic S keccak256 ms inst) →
    (verifyNative (Gₜ := Gₜ) S.E Features.solidity S.params S.vk inst π = .ok () ↔
      ∃ cd, ((S.repackProof π).mapError Midfall.Generator.GeneratorError.fromRepackError >>=
               fun π' => S.encodeCalldata π' inst) = .ok cd ∧
        (∃ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
        ∀ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
          obs.view = returnView (callState W irLyt keccak256 cd))
  /-- The per-partial contracts (Partials.lean), including the pulled-forward finalPairing_spec. -/
  partials : PartialSpecs S product
  /-- M6: the evaluator contract computes the whole-stream fold of the per-identity values, or reverts;
      the frame must pin the VK window because the frame contains the program. -/
  qvm_yul_refines : ∀ (f : EvaluatorFrame) (rt : YulBlock) (Lyt : EVM.Layout) (W : ExecEnv),
    S.evaluatorRuntime = some (rt, Lyt) → FrameWellFormed S f →
    ∀ (st₀ : EvmState), st₀.env.calldata = f.bytes → st₀.env.static = true →
    ∀ V' st' o, YulSemantics.Run EVM.evm rt st₀ V' st' o →
      (∃ vals, perIdentityValues S (frameValuation S.plan.memory f) = some vals ∧      -- SKETCH: evalExprρ over globalIdentities
         ∃ q, S.plan.qext = some q ∧
         st'.halted = some (.ret, outputBytes q.magic (quotientFold S.plan.qplan (yOf S f) vals)))  -- SKETCH: outputBytes/yOf
      ∨ (∃ d, st'.halted = some (.revert, d))
  /-- D-P20 item 2, validator form (P-09e): no bounds fault class is reachable from a validated program,
      and every operand key lies in the read windows (plan.rs:570-618). -/
  qvm_validated_noBoundsFault : ∀ (validate : List Nat → List Word256 → OperandModel → Except String Unit)  -- SKETCH types
      bytes consts model, validate bytes consts model = .ok () →
    ∀ seg, seg ∈ segmentsOf bytes → ∀ mem f, Midfall.Generator.evalQuotientIdentity seg consts mem = .error f →
      (match f with | .readPastEnd _ => False | .constSlotOutOfRange _ _ => False | _ => True)
  /-- Semantic points_subgroup_checked: every decoded G1 of an accepting run reached G1MSM/PAIRING
      (0x0b G1ADD does NOT subgroup-check, PLAN.md:567). -/
  points_subgroup_checked : ∀ (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (mem₀ : Nat → UInt8) (gas) (obs : Obs) ms instW,
    SupportedS S S.o₀ → DeploymentW S W H vkAddr qAddr → ZeroAbove mem₀ →
    RunVerifier S W H cd mem₀ (permissive (S.calls W product qAddr)) gas obs → obs.isReturn →
    decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) →
    ∀ Q, Msg.g1 Q ∈ ms → ∃ req resp, (permissive (S.calls W product qAddr)).Call req obs.state resp ∧
      accountKey req.target ∈ ([0x0c, 0x0f] : List Nat) ∧ IsAlignedSubslice (S.E.g1.toEip Q) req.input  -- SKETCH: call-trace witness
  /-- Vk-dependent facts, kept here because Generator.Vk imports Instances.ExponentModel (D-P17). -/
  vkDigest_slot0 : (S.plan.vk.constants.getD 0 ("", 0)).2 = S.vkDigest
  /-- P-12 port equalities (the Calldata.lean definitions are the spec). -/
  repackProof_faithful : ∀ π, S.repackProof π =
    Midfall.Lowering.repackProof (p := p) (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π
  encodeCalldata_faithful : ∀ π inst, S.encodeCalldata π inst =
    Midfall.Lowering.encodeCalldata (p := p) S.cfg.numInstances (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout) S.E.g1 π inst
  /-- artifacts.rs:181-227: the table is sorted by name, "-G" ↦ (P.g₁, negate := true). -/
  accFixedBases_producer : (S.accFixedBases.toList.map AccFixedBase.name).Sorted (· < ·) ∧
    ∀ b ∈ S.accFixedBases.toList, b.name = "-G" → b.base = P.g₁ ∧ b.negate = true
  /-- The Exec read schedule has the layout's slot shape (Protocol ↔ Exec bridge). -/
  readScheduleAgrees : ∀ inst π ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
    ms.map Msg.slot = (Midfall.Generator.RepackedProofLayoutPlan.fromProofLayout S.plan.proofLayout).slots

-- Non-vacuity gates next to the structure (implementation):
--   example : SupportedS fixtureSurface fixtureSurface.o₀ := ⟨…⟩        (fixture built from YulGolden ASTs)
--   #eval (fixtureSurface.astOfMain fixtureSurface.o₀).isSome -- expect true
--   a trace-render block refutes only_two_outcomes (log1 changes logs); swapped ec_pairing args refute verifier_complete.

/-- PLAN 9.5's headline, derived from the fields: soundness via ir_refines (isReturn/returnData are
    view-level) and shell_unfolds, completeness via ir_refines on both conjuncts, the two-outcome
    conjunct via ir_refines. Hypotheses are the union of the fields'. -/
theorem lowering_equivalence (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (hc : LoweringCorrect S product) (hsup : SupportedS S S.o₀)
    (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (hdep : DeploymentW S W H vkAddr qAddr)
    (hpc : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen S.encG2 S.accFixedBases) (hcodec : Midfall.Assumptions.G1CodecLaws S.E.g1)
    (ir : YulObject) (irLyt : EVM.Layout) (hir : S.irCheck ir = true)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hside : SideConditions S H cd) (g₀ : U256) :
    -- soundness: any run that returns, returns true, and Lean accepts
    (∀ obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) (ExternalGas.ofFun fun _ => g₀) obs →
        obs.isReturn → obs.returnData = abiTrue ∧ LeanAccepts S H cd) ∧
    -- completeness: Lean accepts ⇒ honest runs exist and all return true
    (LeanAccepts S H cd →
        (∃ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
        ∀ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
          obs.view = returnView (callState W irLyt H cd)) ∧
    -- only two outcomes, read-only
    (∀ obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) (ExternalGas.ofFun fun _ => g₀) obs →
        obs.view = returnView (callState W irLyt H cd) ∨
        (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W irLyt H cd))) := by
  sorry -- provable now: transport each field through hc.ir_refines (permissive/honest are WorldLocal)

/-- Exact equivalence to the message-level verifier without an accumulator (R-10 makes `h` necessary). -/
theorem lowering_equivalence_noAcc (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : S.cfg.accumulator = none) :
    LeanAccepts S H cd ↔
      ∃ ms instW inst, decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances S.E.g1 cd = some (ms, instW) ∧
        instOfWords? (p := p) instW = some inst ∧
        verifyMsgs (Gₜ := Gₜ) S.E H Features.solidity S.params S.vk inst ms = .ok () := by
  sorry -- unfold; rw [h]; cases prepareMsgs …; simp [verifyMsgs, bind, Except.bind]  (mirrors SemanticEquivalence.lean)

/-- Adjustment 4: the accumulator-mode corollary Moonlight needs, one direction only (R-10, R-26.4): an
    honest compressed proof that verifyNative accepts, with a public accumulator that decodes and passes its
    own check, yields calldata on which every honest IR run returns abiTrue. Derived from
    contractRef_acc_complete + verifier_complete + ir_refines + the calldata lemmas. There is deliberately
    no acc-mode `↔`: the contract batches with keccak-alpha, Rust with the sponge r. -/
theorem end_to_end_acc_complete (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (hc : LoweringCorrect S product) (enc : Midfall.Generator.AccumulatorEncoding)
    (henc : S.cfg.accumulator = some enc)
    (W : ExecEnv) (vkAddr qAddr : U256) (ir : YulObject) (irLyt : EVM.Layout)
    (inst : Array (Fr p)) (π : Bytes) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀) (hdep : DeploymentW S W keccak256 vkAddr qAddr)
    (hpc : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product) (hcodec : Midfall.Assumptions.G1CodecLaws S.E.g1)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen S.encG2 S.accFixedBases)
    (hir : S.irCheck ir = true) (hn : inst.size = S.cfg.numInstances) (hp : p ≤ 2 ^ 256)
    (hv : verifyNative (Gₜ := Gₜ) S.E Features.solidity S.params S.vk inst π = .ok ())
    (hdec : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) S.E.g1 S.accFixedBases (inst.map frWord) = some a)
    (hchk : KzgAcc.check a S.params (tblOf S.plan S.accFixedBases) = true)
    (hWf : ∀ ms d, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
      prepareMsgs (Gₜ := Gₜ) S.E keccak256 Features.solidity S.vk inst ms = .ok d →
      d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hside : ∀ ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms →
      GenericX S keccak256 ms (inst.map frWord) inst) :
    ∃ cd, ((S.repackProof π).mapError Midfall.Generator.GeneratorError.fromRepackError >>=
             fun π' => S.encodeCalldata π' inst) = .ok cd ∧
      (∃ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
      ∀ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
        obs.view = returnView (callState W irLyt keccak256 cd) := by
  sorry -- verifyNative_iff_msgs_codec; contractRef_acc_complete; calldata_roundtrip; hc.verifier_complete; hc.ir_refines

/-- Finding 3: the frozen Statements.contractRef_noAcc, under a new name (filling it needs a re-pin). -/
theorem contractRef_noAcc_of_semanticEquivalence (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) :
    (Midfall.Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms = true) ↔
      verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () :=
  contractRefAccepts_iff_verifyMsgs E keccak256 params vk inst ms

/-- Finding 1: the frozen verifyNative_iff_msgs is false for a degenerate codec; this is the provable
    form. Only compressedRoundtrip is needed (the attack showed p ≤ 2^256 is decorative here). -/
theorem verifyNative_iff_msgs_codec (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) (hc : E.g1.compressedRoundtrip) :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
      ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
        verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by
  sorry -- key lemma: transcript_log_concat — the log's reprs concatenate to the consumed prefix
end Midfall.Lowering
```

### R. Side-by-side with PLAN 9.5 (what changed and why)

| PLAN 9.5 item | here | change |
|---|---|---|
| `Lowered` (plan/shell/consts) | `Surface` fields `plan : PlanView`, `shell`, `plan.consts` | unported pieces become data; `Types.lean` placeholder untouched |
| `SolidityGenerator.lower`, `render_eq_print` | `Surface.lower/render/astOfMain`, structural field | R-39: text equality dropped |
| `Supported` | `SupportedS` | `noRotInst` as `q.2.int = 0`; `acc` on the Generator type; `layout` D-P18 opt 1; `hLimbs` via `csDegree`; `vkPoints` over encodings |
| `Deployment` | `DeploymentW` | Y-2: codehash is `H code = const`; + callvalue, immutables, memoryguard, disjointness |
| `calls`, `RunVerifier`, `RunContractIR`, `RunShell` | Bridge + Surface defs | over `Bridge.Run` at `evmWithExternal` (Y-3); keccak via `env.keccakOf` |
| `ContractRef.accepts`, `LeanAccepts` | `ContractRefAcceptsAcc`, `LeanAccepts` | raw `Word256` instances (R-26.7); 4-arg `decodeAcc`, 7-arg `alphaOf`, table parameter (defect) |
| `lowering_equivalence` | derived theorem | + selector hypothesis, side conditions, view-level outcomes, WorldLocal calls |
| `lowering_equivalence_noAcc`, `end_to_end_noAcc` | as stated | + `∃ obs`, `fromRepackError`, `inst.size = numInstances`, `p ≤ 2^256`, codec law |
| `contractRef_acc_complete` | as stated | one direction (R-26.4), `hWf`, contract table |
| `ir_refines`, `ObsEquiv` | fields/defs | view-level; WorldLocal; fixed gas |
| `verifier_sound/complete` | fields | any-memory ⇒ `ZeroAbove`; `NoLogupPanic`/`GenericX` |
| `repack_spec` | `repack_spec_wire` + `repack_spec_of_decodeRust` | PLAN iff false |
| `calldata_roundtrip/canonical` | as stated | canonical EXACT in both modes; layout-consistency hypotheses |
| `decodeAcc_encode/injective` | as stated | collapsed `.pointAndScalar` + `negateByTable`; `accWords` + `toEip 1` law |
| `QVM.run`, `qvm_compile_correct` | per-identity + certifier forms | D-P20; values only; `RecognizersSound` |
| `qvm_validated_noOOB` | `builder_segments_total` + validator field | no `.oob`; two real fault classes |
| `qvm_yul_refines` | field over `FrameWellFormed` | frame pins the program |
| `direct_correct` | not stated (M10) | `o.quotientLowering = .direct`, after the direct/ port |
| `Inv k`, `*_spec` | `Inv` + `PartialSpecs` (sound/progress/rejects) | ∀-runs `StmtsContractAll`, VEnv-aware, lifetime-scoped, pairing-slot clause at `.pcs` |
| `finalPairing_spec`, `traceReturn_spec` | concrete theorems over `S.blk` | frame order from the FinalPairing.yul:88 swap |
| `points_subgroup_checked` | generator theorem + semantic field | two layers |
| `deployed_equivalence` | not stated (M11) | blocked on artifact regeneration (R-36) |
