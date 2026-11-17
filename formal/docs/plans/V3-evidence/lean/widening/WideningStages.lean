/-
  WideningStages - the STAGED INVARIANTS and BLOCK ROWS the widening adds or changes, for EVERY render.

  SPECIFICATION, NOT LANDED CODE. Built on `SoundnessV3.lean` (`StageInv`, `BlockSim`,
  `BlockProgS`, `leanStage`) and `WideningV3.lean`. No new `Partial` and no new `Checkpoint`:
  the three additions sit INSIDE existing partials of the Rust templates,

      accumulator validation   VkLoading.yul:115-137      (helpers: AccumulatorHelpers.yul)
      the evaluator call       QuotientAndLinearization.yul:35
      the alpha batching       FinalPairing.yul:14-60

  so the seven rows keep their names and three of them change. One row is NEW and is not a slice
  of the verifier: the evaluator's fallback body, run in the closed dialect.

  Sections
    §1  the raw instance words and the accumulator invariant        instWordsRaw, AccInv
    §2  the widened Lean stage and the widened staged invariant     leanStageW, accOfRaw, StageInvW
        PROVED: V3's `StageInv` is unsatisfiable after `.start` in accumulator mode
        (`stageInv_false_of_acc`); at V3's corner `StageInvW` IS `StageInv` (`stageInvW_iff_V3`)
    §3  the last stage is `LeanAcceptsAcc` (PROVED both ways)       LeanFinalAcc
    §4  the evaluator body: three contracts                         EvalBodyShape/Agree/Total
    §5  the batching invariant inside finalPairing                  BatchedInv
    §6  the widened row families                                    BlockSimW, BlockProgSW
    §7  THE TARGET `lowering_correctW` (with the evaluator's contract as a hypothesis), what the
        statement without it would imply (`lowering_correctW_needs_evalContracts`, PROVED), and
        `lowering_correct_of_W` (D-P71's deliverable follows; PROVED)

  ## WHICH CLAUSES OF VALIDITY EACH BASE ROW USES (review finding D4)

  Every base row (`soundness/GeneratorRows.lean`) takes `hR : R.Valid` WHOLE, and
  `Valid.supported : SupportedV2` contains `noAcc` and `embeddedQuotient`. This table says what
  each row's statement and its stated children actually read. Sources: the statements and
  docstrings of `GeneratorRows.lean` / `SoundnessV3.lean`, `Midfall/LoweringV2/Blocks/*.lean`,
  and the emitters (`Midfall/Lowering/GenAst.lean`, `GenAstDispatch.lean`,
  `Midfall/LoweringV2/Program.lean`). "TEXT" = the emitter of the slice branches on the flag.
  [PG …] = a premise gap of `GeneratorRows.lean` §2 (not a clause of `Valid` today).

  row              | noAcc | embeddedQuotient | other validity read                     | widened
  -----------------+-------+------------------+-----------------------------------------+---------
  prefix (SIM.6)   | no ¹  | YES              | layout, transcriptMptr, separateVk      | 2nd arm
  vkLoading        | YES   | no               | vkPins, vkProgressPins                  | 2nd arm
  transcriptParser | no    | no               | model, layout, circuitMeta, slots, wf   | one arm
  lagrange         | no    | no               | slots (EnvAgrees), wf                   | one arm
  quotientLin      | no    | YES              | slots, codegen                          | 2nd arm
  pcs              | no    | no               | circuitMeta, invariants, slots          | one arm
  finalPairing     | YES   | no               | slots (+ payload: PG-G2SLOTS)           | 2nd arm
  traceReturn      | no    | no               | sim: NONE; progress: returnMptr only    | one arm
  totality (TOT.1) | via vk/fp | YES          | production; the blocks' own             | 2nd arm

  Row by row:
  * prefix. `model_flags_of_valid` reads `separateVk` and `embeddedQuotient` so that
    `wrapperLocals` (Program.lean:105) is the single `let vk`. At an external render it also
    prints `let quotientEvaluator := qAddr` (:107), and the exit must establish the last conjunct
    of `StageInvW`. Also read: `layout` (`layout_static_of_valid`), `transcriptMptr` (the memory
    guard is passable), [PG noShadow, FR_MODULUS, g1Identity; RECON.2's `cdSize`].
    ¹ `helpers_eq` (eight definitions, for EVERY `R`) holds today only because the accumulator
    helpers are not emitted (WP-G1, Program.lean:96). When they are, `helpers_eq`/`HelperIs` gain
    an arm; `funDefs_noop` is generic, so the prefix proof itself does not.
  * vkLoading. TEXT: `emitVkLoadingArms pv.hasAccumulator …` (GenAst.lean:984). `noAcc` enters
    through `pv_hasAcc_false` (Blocks/VkLoading.lean:178) in `vk_slice` (:194) and in the `.vk`
    clause of `Inv` (:708). Second arm: accumulator validation (VkLoading.yul:115-137), which
    establishes `AccInv`. Also read: `vkPins` (sim and progress), `vkProgressPins` (progress).
  * transcriptParser. No flag: `emitTranscriptParserAt numInstances userPhases numLookups
    numPermutationZs lookupHPlusAcc numTrashcans truncatedChallenges proofLayout`
    (GenAst.lean:1182). Read: `model`/`layout`/`circuitMeta`/`inputs` (`tp_events_slots`,
    PG-PARSER), `slots`, `supported.wf` and the shape clauses (`xcript_total`), [PG consts-TP,
    FR_MODULUS, noShadow]; `SimPins.eipRt`, `.toEipOne` from the headline.
  * lagrange. No flag: `emitLagrangeAt k numInstances numNegLagranges` (GenAst.lean:766). Read:
    `slots` (`lag_agrees`: `n = 2^k`, `ω`, `numNegLagranges`), `supported.wf`, [PG consts-LAG,
    FR_MODULUS, negLagranges, noShadow].
  * quotientLin. `embeddedQuotient` decides WHICH TEXT the slice is: the embedded numerator, or
    the pin guard and `staticcall(gas(), quotientEvaluator, …)` (QuotientAndLinearization.yul:21-38).
    Today `qlin_slice` is the linearization scope for every `R` and neither arm is emitted
    (PG-Q-OBJECT; `CodegenAgrees` is false). Second arm: `EvalContracts` + `EvaluatorTrust`.
  * pcs. No flag: `emitPcsFromPlan pv` reads `meta_`, `dat`, `memory`, `truncatedChallenges`
    (GenAstDispatch.lean:131). Read: `circuitMeta`/`invariants` (PG-PCS-EMIT), `slots`, [PG consts
    PCS names, noShadow]; `SimPins.multiPoint`.
  * finalPairing. TEXT: `emitFinalPairingArms pv.hasAccumulator …` (GenAst.lean:658). `noAcc`
    enters there (Blocks/FinalPairing.lean:24) and in `fp_blockSim_of_blockSound`, which turns
    `Inv.pairing_dualMsm_or` into `DualMSM.check` with `pv_hasAcc_false` (SoundnessV3.lean:1338).
    Second arm: the alpha batching (`BatchedInv`, `batchedCheck_iff_contract`, `leanStageW`).
  * traceReturn. Constant text (`emitTraceReturn _pv`, GenAst.lean:793). `tr_blockSim` takes NO
    validity; `tr_blockProgS` takes `trRetMptr R`, i.e. `Valid.returnMptr` (Statements.lean:226).
  * totality. `gasFree_of_valid` reads `production` and `embeddedQuotient`: an external render
    executes `gas()` once, so `GasFree` is false there and `runBody_gas_oblivious` does not apply.
    Second arm: "`gas()` occurs only as the gas argument of the evaluator call",
    `evalModel_gas_irrel`, `EvalBodyTotal`. `block_live`/`prefix_live` inherit their blocks' arms.

  TWO FACTS THE TABLE DEPENDS ON
  (i) THE BOUNDARY, not validity, is what keeps the "one arm" rows out of accumulator mode. Every
      base row whose boundary is `.vk` or later reads `hasAccumulator = false` through its
      invariant: the `.vk` clause of `Inv` (Inv.lean:754) demands `S.acc.isSome`, and `StageInv`
      feeds it `witnessSnapshot` / `snapshotOf … none`. PROVED in §2: `stageInv_false_of_acc`. So a
      "one arm" row is not reusable VERBATIM over `StageInv`: it is restated over `StageInvW`
      (the shape `BlockSimW`/`BlockProgSW` already have) with the same children and two frame
      obligations - the two accumulator slots of `AccInv` are not written, and the local
      `quotientEvaluator` is not assigned. Its validity hypothesis can then be
      `ValidCore R ∧ SupportedW R`.
  (ii) THE VALIDITY VOCABULARIES. `ValidCore` / `validV3_iff_core` (WideningV3.lean §G) ARE stated
      over the 18-clause `Midfall.LoweringV3.ValidV3` of `statements/StatementsV3.lean:613` (17
      fields; `ValidCore` is the 16 other than `supported`). The base rows are stated over the
      tree's `LoweringV2.Render.Valid` (14 fields). `Valid.returnMptr`, which the traceReturn
      progress row reads, is a field of NEITHER `ValidV3` nor `ValidCore`: RECON.1 must supply it
      (for example as a `constsCoherent` name) before that row can take `ValidCore`.
-/
import WideningV3
import SoundnessV3

namespace Midfall.LoweringW

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV2.V3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §1. The accumulator stage -/

/-- The instance words as the CONTRACT reads them: `calldataload` at the instance cursor, with no
    decoding of the proof. Defined on raw calldata because the contract validates the accumulator
    BEFORE the transcript (VkLoading.yul:130), i.e. before any proof point is known to be a group
    element; so the accumulator fact is of the `LeanRaw`/`Mirror` class, never of the `Agree`
    class (PLAN-V3 §5 M3: "nothing needed before the PCS exit may live in `Agree`"). -/
def instWordsRaw (R : Render p G₁ G₂ Gₜ) (cd : Bytes) : Array Word256 :=
  (Array.range R.cfg.numInstances).map fun i =>
    BitVec.ofNat 256 (bytesToNatBE (cdSlice cd (R.plan.proofLayout.proofEnd + 32 + 32 * i) 32))

/-- OBLIGATION (ALG, Lean only): on a calldata that decodes, the decoder's instance words are the
    raw ones. About `decodeCalldata` alone (`Calldata.lean:341`). -/
theorem instWords_of_decoded (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
    (instW : Array Word256) (inst : Array (Fr p)) (h : Decoded R cd ms instW inst) :
    instW = instWordsRaw R cd := by
  sorry

/-- The accumulator of the calldata decodes (the progress-side premise of the vkLoading row). -/
def AccDecodes (R : Render p G₁ G₂ Gₜ) (cd : Bytes) : Prop :=
  ∀ enc, R.cfg.accumulator = some enc →
    ∃ a : KzgAcc (Fr p) G₁ G₂ Gₜ,
      decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1 accTable
        (instWordsRaw R cd) = some a

/-- **THE INVARIANT ACCUMULATOR VALIDATION ESTABLISHES**, and that holds unchanged up to the final
    pairing: the accumulator of the raw instance words decodes, and the two slots hold the EIP
    encodings of the two SCALED points (the outputs of the two G1MSM calls). Unconditional: no
    snapshot, no decoding of the proof. Vacuous without an accumulator. -/
def AccInv (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) : Prop :=
  ∀ enc, R.cfg.accumulator = some enc →
    ∃ a : KzgAcc (Fr p) G₁ G₂ Gₜ,
      decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1 accTable
        (instWordsRaw R cd) = some a ∧
      bytesAt st (ptrAddr R.pv.memory.accLhsMptr) 128 =
        R.E.g1.toEip (a.fullyCollapse accBases).1 ∧
      bytesAt st (ptrAddr R.pv.memory.accRhsMptr) 128 =
        R.E.g1.toEip (a.fullyCollapse accBases).2

/-- From which boundary the accumulator invariant is carried: every one after vkLoading. -/
def accFrom : Checkpoint → Bool
  | .start => false
  | _ => true

/-! ## §2. The widened Lean stage and staged invariant -/

/-- `leanStage` (`SoundnessV3.lean:336`) with the LAST stage widened: the final check is the
    contract's (`accFinalCheck`), not the plain pairing check. In accumulator mode the plain check
    need not hold when the batched one does (`AlphaCollision`), so `leanStage .pairing` is the
    wrong stage there. -/
def leanStageW (R : Render p G₁ G₂ Gₜ) (H : Hash) (instW : Array Word256) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Checkpoint → Except Fault (Snapshot p G₁ G₂ Gₜ)
  | .pairing => do
      let S ← snapshotOf R.E H R.vk inst ms none
      if accFinalCheck R H instW S.c.dual then pure S else throw (Fault.error Error.opening)
  | k => leanStage R H inst ms k

/-- Without an accumulator the widened stage is V3's stage. PROVED. -/
theorem leanStageW_noAcc (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none) (H : Hash)
    (instW : Array Word256) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (k : Checkpoint) :
    leanStageW R H instW inst ms k = leanStage R H inst ms k := by
  cases k <;> simp [leanStageW, leanStage, accFinalCheck, hacc]

/-! ### The snapshot the staged invariant reads must CARRY the accumulator

  `Inv` reads the snapshot's accumulator in exactly one place: its `.vk` clause
  `PV.hasAccumulator == false || S.acc.isSome` (Inv.lean:754). Every snapshot V3's `StageInv`
  feeds it has `acc = none` (`witnessSnapshot`, `padSnap`, `snapshotOf … none`), which is right
  for V3's class and makes the invariant UNSATISFIABLE after `.start` in accumulator mode. The
  four lemmas below are that finding, PROVED; `accOfRaw`/`withAcc` are the repair. -/

/-- The plan view's accumulator flag is the configuration's. PROVED. -/
theorem pv_hasAcc_eq (R : Render p G₁ G₂ Gₜ) :
    R.pv.hasAccumulator = R.cfg.accumulator.isSome := by
  show (planViewOf R.plan R.model R.cfg.accumulator).hasAccumulator = _
  rw [planViewOf, planViewWithAccumulator]

/-- In accumulator mode `Inv` at `.vk` or later fails on a snapshot without an accumulator.
    PROVED. -/
theorem inv_needs_acc (R : Render p G₁ G₂ Gₜ) (hacc : R.pv.hasAccumulator = true)
    (k : Checkpoint) (hk : Checkpoint.vk ≤ k) (S : Snapshot p G₁ G₂ Gₜ) (hS : S.acc = none)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    ¬ Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st := by
  intro h
  simp [Midfall.Lowering.Inv, Midfall.Lowering.InvAt, hk, hacc, hS] at h

/-- `snapshotOf … none` has no accumulator. PROVED. -/
theorem snapshotOf_none_acc (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁))
    (S : Snapshot p G₁ G₂ Gₜ) (h : snapshotOf E H vk inst ms none = .ok S) : S.acc = none := by
  unfold snapshotOf at h
  cases h1 : snapshotPcsRun E H vk inst ms with
  | error e => rw [h1] at h; cases h
  | ok r =>
      obtain ⟨s5, t5⟩ := r
      rw [h1] at h
      cases h2 : t5.assertEmpty with
      | error e => simp [bind, Except.bind, h2] at h
      | ok u =>
          simp [bind, Except.bind, h2, pure, Except.pure] at h
          rw [← h]

/-- **FINDING (PROVED): V3's STAGED INVARIANT IS UNSATISFIABLE AFTER `.start` IN ACCUMULATOR
    MODE.** So no base row (`BlockSim`, `BlockProgS`: `SoundnessV3.lean:559`, `:1065`) says anything
    true and useful about an accumulator render: a row whose pre-boundary is `.vk` or later is
    vacuous there, and the vkLoading rows (exit `StageInv .vk`) say that every run from a staged
    `.start` boundary reverts or ends poisoned, so they fail wherever vkLoading has a clean exit.
    This, not a clause of validity, is why the "one arm" rows of the table at the top of this
    file must be RESTATED over `StageInvW`. -/
theorem stageInv_false_of_acc (R : Render p G₁ G₂ Gₜ)
    (enc : Midfall.Generator.AccumulatorEncoding) (henc : R.cfg.accumulator = some enc)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint) (hk : k ≠ .start)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    ¬ StageInv R H vkAddr cd k V st := by
  have hacc : R.pv.hasAccumulator = true := by rw [pv_hasAcc_eq, henc]; rfl
  rintro ⟨_, _, hbase, hraw, _, hagree⟩
  have hw : (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)).acc = none := rfl
  cases k with
  | start => exact hk rfl
  | vk => exact inv_needs_acc R hacc .vk (by decide) _ hw V st hbase
  | transcript => exact inv_needs_acc R hacc .vk (by decide) _ hw V st hbase
  | lagrange => exact inv_needs_acc R hacc .vk (by decide) _ hw V st hbase
  | quotient => exact inv_needs_acc R hacc .vk (by decide) _ hw V st hbase
  | pcs =>
      obtain ⟨ms, instW, inst, hdec⟩ := hraw
      obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
      exact inv_needs_acc R hacc .pcs (by decide) S
        (snapshotOf_none_acc R.E H R.vk inst ms S hS) V st hinv
  | pairing =>
      obtain ⟨ms, instW, inst, hdec⟩ := hraw
      obtain ⟨S, hS, hinv⟩ := hagree ms instW inst hdec
      exact inv_needs_acc R hacc .pairing (by decide) S
        (snapshotOf_none_acc R.E H R.vk inst ms S (leanStage_pairing_ok hS).1) V st hinv

/-- **THE ACCUMULATOR THE STAGED SNAPSHOT CARRIES**: the decoding of the RAW instance words
    (`instWordsRaw`, calldata only - the accumulator is validated before the transcript).
    `none` without an accumulator, and `none` when the words do not decode. -/
def accOfRaw (R : Render p G₁ G₂ Gₜ) (cd : Bytes) : Option (KzgAcc (Fr p) G₁ G₂ Gₜ) :=
  match R.cfg.accumulator with
  | none => none
  | some enc =>
      decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1 accTable
        (instWordsRaw R cd)

/-- A staged snapshot with its accumulator hole filled from the raw instance words. -/
def withAcc (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (S : Snapshot p G₁ G₂ Gₜ) :
    Snapshot p G₁ G₂ Gₜ :=
  { S with acc := accOfRaw R cd }

/-- WITNESS (V3's corner): without an accumulator, filling the hole changes nothing `Inv` reads.
    PROVED. -/
theorem inv_withAcc_of_noAcc (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (cd : Bytes) (k : Checkpoint) (S : Snapshot p G₁ G₂ Gₜ)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv (withAcc R cd S) V st ↔
      Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st := by
  have h : R.pv.hasAccumulator = false := by rw [pv_hasAcc_eq, hacc]; rfl
  simp [Midfall.Lowering.Inv, Midfall.Lowering.InvAt, withAcc, h]

/-- WHAT THE REPAIRED CLAUSE SAYS in accumulator mode: from `.vk` on, the accumulator of the raw
    instance words decodes (the first conjunct of `AccInv`; nothing new). PROVED. -/
theorem inv_withAcc_decodes (R : Render p G₁ G₂ Gₜ)
    (enc : Midfall.Generator.AccumulatorEncoding) (henc : R.cfg.accumulator = some enc)
    (cd : Bytes) (k : Checkpoint) (hk : Checkpoint.vk ≤ k) (S : Snapshot p G₁ G₂ Gₜ)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (h : Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv (withAcc R cd S) V st) :
    ∃ a, decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1 accTable
        (instWordsRaw R cd) = some a := by
  have hpv : R.pv.hasAccumulator = true := by rw [pv_hasAcc_eq, henc]; rfl
  cases ha : accOfRaw R cd with
  | none => exact absurd h (inv_needs_acc R hpv k hk (withAcc R cd S) ha V st)
  | some a =>
      unfold accOfRaw at ha
      rw [henc] at ha
      exact ⟨a, ha⟩

/-- `BaseInv` (`SoundnessV3.lean:473`) on the accumulator-carrying witness snapshot. -/
def BaseInvW (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (k : Checkpoint) {c : ExternalCalls}
    {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  match k with
  | .pcs | .pairing => True
  | _ => Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params (baseCk k) R.pv
      (withAcc R cd (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))) V st

/-- `Agree` over the widened stage, on the accumulator-carrying snapshot. -/
def AgreeW (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∃ S, leanStageW R H instW inst ms k = .ok S ∧
      Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv (withAcc R cd S) V st

/-- **THE WIDENED STAGED INVARIANT.** V3's five parts (with `BaseInvW` for `BaseInv` and `AgreeW`
    for `Agree`: the snapshot `Inv` reads carries the accumulator of the raw instance words),
    plus: the accumulator invariant from `.vk` on, and - for a render that calls an evaluator -
    the wrapper local `quotientEvaluator` bound to the deployment's address (the `Frame` of V3
    binds `vk` only). -/
def StageInvW (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (k : Checkpoint) {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g))
    (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ BaseInvW R cd k V st ∧
    LeanRaw R cd k ∧ Mirror R cd st k ∧ AgreeW R H cd k V st ∧
    (accFrom k = true → AccInv R cd st) ∧
    (isExternal R → VEnv.get V "quotientEvaluator" = some qAddr)

/-- **AT V3's CORNER THE WIDENED INVARIANT IS V3's. PROVED.** No accumulator and no evaluator:
    `StageInvW` and `StageInv` are equivalent, at every checkpoint and every evaluator address. So
    a base row proved over `StageInv` IS the widened row there, and nothing in V3's class is lost
    by stating the rows over `StageInvW`. -/
theorem stageInvW_iff_V3 (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (hext : ¬ isExternal R) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    StageInvW R H vkAddr qAddr cd k V st ↔ StageInv R H vkAddr cd k V st := by
  have hbase : BaseInvW R cd k V st ↔ BaseInv R k V st := by
    cases k <;> first
      | exact Iff.rfl
      | exact inv_withAcc_of_noAcc R hacc cd _ _ V st
  have hagree : AgreeW R H cd k V st ↔ Agree R H cd k V st := by
    unfold AgreeW Agree
    constructor
    · intro h ms instW inst hdec
      obtain ⟨S, hS, hinv⟩ := h ms instW inst hdec
      rw [leanStageW_noAcc R hacc] at hS
      exact ⟨S, hS, (inv_withAcc_of_noAcc R hacc cd k S V st).mp hinv⟩
    · intro h ms instW inst hdec
      obtain ⟨S, hS, hinv⟩ := h ms instW inst hdec
      exact ⟨S, by rw [leanStageW_noAcc R hacc]; exact hS,
        (inv_withAcc_of_noAcc R hacc cd k S V st).mpr hinv⟩
  constructor
  · rintro ⟨hf, hs, hb, hr, hm, ha, _, _⟩
    exact ⟨hf, hs, hbase.mp hb, hr, hm, hagree.mp ha⟩
  · rintro ⟨hf, hs, hb, hr, hm, ha⟩
    exact ⟨hf, hs, hbase.mpr hb, hr, hm, hagree.mpr ha,
      fun _ enc henc => (by rw [hacc] at henc; cases henc), fun he => absurd he hext⟩

/-- A poisoned boundary of a render that calls an evaluator still knows the address. -/
def PoisonedW (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Poisoned R H vkAddr cd V st ∧ (isExternal R → VEnv.get V "quotientEvaluator" = some qAddr)

/-! ## §3. The last stage is `LeanAcceptsAcc` -/

/-- The last stage, closed. -/
def LeanFinalAcc (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW inst, Decoded R cd ms instW inst ∧
    ∃ S, leanStageW R H instW inst ms .pairing = .ok S

theorem leanStageW_pairing_ok {R : Render p G₁ G₂ Gₜ} {H : Hash} {instW : Array Word256}
    {inst : Array (Fr p)} {ms : List (Msg (Fr p) G₁)} {S : Snapshot p G₁ G₂ Gₜ}
    (h : leanStageW R H instW inst ms .pairing = .ok S) :
    snapshotOf R.E H R.vk inst ms none = .ok S ∧ accFinalCheck R H instW S.c.dual = true := by
  unfold leanStageW at h
  cases hs : snapshotOf R.E H R.vk inst ms none with
  | error e => rw [hs] at h; cases h
  | ok S0 =>
      rw [hs] at h
      by_cases hc : accFinalCheck R H instW S0.c.dual = true
      · simp only [bind, Except.bind, hc, ite_true, pure, Except.pure] at h
        cases h
        exact ⟨rfl, hc⟩
      · simp only [bind, Except.bind, hc] at h
        cases h

/-- **LINK, soundness direction** (the widened `leanAccepts_of_final`). PROVED from the tree's
    `snapshotOf_prepareMsgs` (itself a registered obligation). -/
theorem leanAcceptsAcc_of_final {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes}
    (h : LeanFinalAcc R H cd) : LeanAcceptsAcc R H cd := by
  obtain ⟨ms, instW, inst, ⟨hdec, hinst⟩, S, hS⟩ := h
  obtain ⟨hsnap, hchk⟩ := leanStageW_pairing_ok hS
  exact ⟨ms, instW, inst, hdec, hinst, S.c.dual,
    (snapshotOf_prepareMsgs (Gₜ := Gₜ) R.E H R.vk inst ms none).1 S hsnap, hchk⟩

/-- **LINK, completeness direction.** PROVED likewise. -/
theorem leanFinalAcc_of_accepts {R : Render p G₁ G₂ Gₜ} {H : Hash} {cd : Bytes}
    (h : LeanAcceptsAcc R H cd) : LeanFinalAcc R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, d, hd, hchk⟩ := h
  have hboth := snapshotOf_prepareMsgs (Gₜ := Gₜ) R.E H R.vk inst ms none
  have hok : (snapshotOf R.E H R.vk inst ms none).isOk = true := by
    rw [hboth.2, hd]; rfl
  cases hs : snapshotOf R.E H R.vk inst ms none with
  | error e => rw [hs] at hok; cases hok
  | ok S =>
      have hg : d = S.c.dual := by
        have h1 := hboth.1 S hs
        rw [hd] at h1
        exact Except.ok.inj h1
      refine ⟨ms, instW, inst, ⟨hdec, hinst⟩, S, ?_⟩
      unfold leanStageW
      rw [hs]
      have hc : accFinalCheck R H instW S.c.dual = true := by rw [← hg]; exact hchk
      simp only [bind, Except.bind, hc, ite_true, pure, Except.pure]

/-! ## §4. The evaluator body (a NEW row; closed dialect; not a slice of the verifier) -/

/-- Word `i` of a return buffer. -/
def retWord (ret : List UInt8) (i : Nat) : Word256 :=
  BitVec.ofNat 256 (bytesToNatBE (ByteArray.mk ((ret.drop (32 * i)).take 32).toArray))

/-- The frame the verifier sends: the window `[frameBase, frameBase + frameLen)` of ITS memory
    (`staticcall(gas(), quotientEvaluator, frame_base, frame_len, q_out, output_len)`). -/
def frameOf (qe : QuotientExternal) (st : EvmState) : List UInt8 :=
  readBytes st.memory qe.frameBase qe.frameLen

/-- **EVALUATOR ROW 1 - SHAPE (SEM; independent of the frame's CONTENT).** On an input of exactly
    `frameLen` bytes every run of the body returns: `outputLen` bytes whose first word is the
    magic. On an input of any other length every run fails. So, for a valid render, the three
    checks the verifier makes after the call (call failed, wrong return size, wrong magic) are
    dead on the honest path, and reachable only through `permissive`.

    Why it should be true: the body's only reverts are `revert(0,0)` on the length test and
    `q_program_fail()` on a malformed program; it makes no call and inverts nothing. The second
    is where the render enters: the program bytes are in the frame, so "well-formed program" must
    be a fact about the frame (the `.vk` clause of the staged invariant pins the payload image),
    hence the staged premise. It is `StageInvW`, NOT V3's `StageInv`: in accumulator mode
    `StageInv … .lagrange` is unsatisfiable (`stageInv_false_of_acc`), which would make this
    conjunct and `EvalBodyAgree` vacuous exactly at the IVC corner (accumulator, external), and
    `EvalContracts` would then hold of an evaluator that returns nothing. At V3's corner the two
    premises are the same (`stageInvW_iff_V3`). -/
def EvalBodyShape (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) : Prop :=
  ∀ (qe : QuotientExternal), R.model.quotientExternal = some qe →
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (req : YulSemantics.EVM.CallRequest) (stC : EvmState) (V' : VEnv EVM.evm) (st' : EvmState)
    (o : Outcome),
    EvalEntry Q W Lyt qAddr st req stC → YulSemantics.Run EVM.evm Q.body stC V' st' o →
    (req.input.length ≠ qe.frameLen →
      (Evaluator.responseOf st (committedState stC st')).success = false) ∧
    (StageInvW R H vkAddr qAddr cd .lagrange V st → req.input = frameOf qe st →
      (Evaluator.responseOf st (committedState stC st')).success = true ∧
      (Evaluator.responseOf st (committedState stC st')).returndata.length = qe.outputLen ∧
      retWord (Evaluator.responseOf st (committedState stC st')).returndata 0 =
        BitVec.ofNat 256 qe.magic)

/-- **EVALUATOR ROW 2 - AGREEMENT (SEM + ALG).** When the frame is the window of a caller state at
    the `.lagrange` boundary (`StageInvW`, for the reason given at row 1), the returned words are
    the Lean quotient stage's: word 1 is the
    linearization's expected evaluation and words 2.. are the selector buckets. Decode-relative
    (it is `Agree`-class) and under `SoundSide` (the Lean stage is `linearize`, which panics at
    logup.rs:460 where the contract does not).

    THIS IS V3's quotientLin ROW, TRANSPORTED INTO THE CALLEE FRAME: the evaluator contract is
    the same two template partials (`QuotientHelpers`, `QuotientNumeratorBlock`) between a
    `calldatacopy` and a `return` (`Contracts.lean:492`). -/
def EvalBodyAgree (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) : Prop :=
  ∀ (qe : QuotientExternal), R.model.quotientExternal = some qe →
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (req : YulSemantics.EVM.CallRequest) (stC : EvmState) (V' : VEnv EVM.evm) (st' : EvmState)
    (o : Outcome),
    StageInvW R H vkAddr qAddr cd .lagrange V st → SoundSide R H cd → req.input = frameOf qe st →
    EvalEntry Q W Lyt qAddr st req stC → YulSemantics.Run EVM.evm Q.body stC V' st' o →
    ∀ ms instW inst, Decoded R cd ms instW inst →
      ∃ S L, leanStage R H inst ms .quotient = .ok S ∧ S.lin = some L ∧
        retWord (Evaluator.responseOf st (committedState stC st')).returndata 1 =
          frWord (linComEval L.linCom) ∧
        ∀ i, i < (linComBuckets L.linCom).size →
          retWord (Evaluator.responseOf st (committedState stC st')).returndata (2 + i) =
            frWord ((linComBuckets L.linCom).getD i 0)

/-- **EVALUATOR ROW 3 - TOTALITY.** From every entry frame the body has a run. Needed by conjunct
    4 and by the existence half of conjunct 2: `EvaluatorTrust.spec` turns a run of the body into
    an answer of the chain, so without this the honest relation may have no answer at the
    evaluator address and the verifier would be stuck there. -/
def EvalBodyTotal (Q : EvalObject) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (qAddr : U256) (st : EvmState)
    (req : YulSemantics.EVM.CallRequest) (stC : EvmState),
    EvalEntry Q W Lyt qAddr st req stC →
    ∃ (V' : VEnv EVM.evm) (st' : EvmState) (o : Outcome),
      YulSemantics.Run EVM.evm Q.body stC V' st' o

/-- The three evaluator rows of a render. Vacuous for a render with an embedded quotient. -/
def EvalContracts (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) : Prop :=
  isExternal R → EvalBodyShape R Q ∧ EvalBodyAgree R Q ∧ EvalBodyTotal Q

/-- CONSEQUENCE of row 3, PROVED: under the trust assumption, at a pinned state, the chain answers
    every STATICCALL at the evaluator address. -/
theorem evalRel_answers (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (W : ExecEnv) (Lyt : EVM.Layout)
    (qAddr : U256) (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop)
    (ht : EvaluatorTrust R Q W Lyt qAddr evalRel) (htot : EvalBodyTotal Q)
    (req : YulSemantics.EVM.CallRequest) (st : EvmState)
    (hk : req.kind = YulSemantics.EVM.CallKind.staticcall) (hp : QPinned R st qAddr) :
    ∃ resp, evalRel req st resp := by
  have hentry : EvalEntry Q W Lyt qAddr st req (Evaluator.calleeState W Lyt qAddr st req) := by
    refine ⟨⟨_, _, rfl⟩, fun a _ => rfl, ?_⟩
    have h0 : (loadWord (Evaluator.calleeState W Lyt qAddr st req).memory 0x40).toNat = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; exact Nat.zero_le _
  obtain ⟨V', st', o, hrun⟩ := htot W Lyt qAddr st req _ hentry
  exact ⟨_, (ht.spec req st _ hk hp).mpr ⟨_, V', st', o, hentry, hrun, rfl⟩⟩

/-! ## §5. The batching invariant inside finalPairing -/

/-- **AFTER THE ALPHA BATCHING, BEFORE `ec_pairing`** (FinalPairing.yul:14-60): the two pairing
    slots hold the reference's two batched inputs. Decode-relative: at `.pcs` the calldata
    decodes (`LeanRaw .pcs`), so `Agree` is live. Vacuous without an accumulator, where the slots
    are left as the PCS block wrote them. -/
def BatchedInv (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∀ S, snapshotOf R.E H R.vk inst ms none = .ok S →
      ∀ enc (a : KzgAcc (Fr p) G₁ G₂ Gₜ), R.cfg.accumulator = some enc →
        decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1 accTable
          instW = some a →
        bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128 =
          R.E.g1.toEip (batchedInputs R H S.c.dual a).1 ∧
        bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128 =
          R.E.g1.toEip (batchedInputs R H S.c.dual a).2

/-- OBLIGATION (ALG, no Yul): the batched check is the contract's pairing equation on the two
    batched inputs. `batchedCheck_eq` (`Accumulator.lean:1194`, proved) plus the orientation lift
    `dualMsm_check_iff_contract` (`:1320`, proved); the same two pins `hn`, `hs` as without an
    accumulator. This is the ALG half of the widened finalPairing row. -/
theorem batchedCheck_iff_contract (R : Render p G₁ G₂ Gₜ) (H : Hash)
    (d : DualMSM (Fr p) G₁ G₂ Gₜ) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (g2 negSG2 : G₂)
    (hn : R.params.nG2Prepared = g2⁻¹) (hs : R.params.sG2Prepared = negSG2⁻¹)
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size) :
    batchedCheck R.params
        (alphaOf (p := p) H (vkDigestWordOf R) R.E.g1 d.left.eval d.right.eval
          (a.fullyCollapse accBases).1 (a.fullyCollapse accBases).2) d a accBases = true ↔
      Midfall.Lowering.contractPairingHolds (p := p) (Gₜ := Gₜ) g2 negSG2
        (batchedInputs R H d a).1 (batchedInputs R H d a).2 := by
  sorry

/-! ## §6. The widened row families -/

/-- How block `q` finishes when nothing failed, widened. -/
def exitSimW (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinalAcc R H cd
  | _ => o = .normal ∧ StageInvW R H vkAddr qAddr cd q.pre.next V' st'

/-- **THE PER-BLOCK SIMULATION CONTRACT, widened.** `BlockSim` (`SoundnessV3.lean:559`) over
    `StageInvW` / `PoisonedW` / `exitSimW`. Same slices, same scope. -/
def BlockSimW (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => StageInvW R H vkAddr qAddr cd q.pre V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSimW R q H vkAddr qAddr cd V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ PoisonedW R H vkAddr qAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => PoisonedW R H vkAddr qAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ PoisonedW R H vkAddr qAddr cd V' st'))

/-- The seven simulation rows of a render, widened (`Render.SimContracts`). The evaluator rows are
    a HYPOTHESIS of the quotientLin row, not part of it: that row is about the verifier's slice
    and consumes `EvaluatorTrust.spec` to turn the chain's answer into a run of the body. -/
def SimContractsW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ValidW R Q → SimPins R → Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → EvalContracts R Q →
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    (isExternal R → EvaluatorTrust R Q W Lyt qAddr evalRel) →
    (R.cfg.accumulator.isSome = true → R.E.g1.ofEip? (R.E.g1.toEip 1) = some 1) →
    SoundSide R H cd →
    ∀ (q : Partial) (g : ExternalGas),
      BlockSimW R q H vkAddr qAddr (permissive (callsW R product qAddr evalRel)) g cd

/-- The clean exit of block `q`, widened (`exitProg`). -/
def exitProgW (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue)
  | _ => o = .normal ∧ StageInvW R H vkAddr qAddr cd q.pre.next V' st'

/-- **THE TOTAL PROGRESS CONTRACT, widened** (`BlockProgS`): honest relation, zero gas oracle. -/
def BlockProgSW (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (product : PairingProduct)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) (cd : Bytes) :
    Prop :=
  StmtsTotal (D := Bridge.Dialect (callsW R product qAddr evalRel) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => StageInvW R H vkAddr qAddr cd q.pre V st)
    (fun _ _ V' st' o => exitProgW R q H vkAddr qAddr cd V' st' o)

/-- The seven progress rows of a render, widened (`Render.ProgContracts`). The premise is
    `LeanAcceptsAcc`; the vkLoading row reads from it that the accumulator decodes, and the
    quotientLin row needs the pinned evaluator code in the world (`QPinnedEnv`), which the
    soundness rows do not (there the contract's own guard supplies it). -/
def ProgContractsW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct) : Prop :=
  ValidW R Q → SimPins R → Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → EvalContracts R Q →
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop),
    LoweringV3.G1CodecHeadlineLaws R.E.g1 →
    (isExternal R → QPinnedEnv R W qAddr ∧ EvaluatorTrust R Q W Lyt qAddr evalRel) →
    (R.cfg.accumulator.isSome = true → R.E.g1.ofEip? (R.E.g1.toEip 1) = some 1) →
    LeanAcceptsAcc R H cd → CompleteSide R H cd →
    ∀ q : Partial, BlockProgSW R q H vkAddr qAddr product evalRel cd

/-- WITNESS that the progress premise carries what the vkLoading row needs. PROVED from
    `instWords_of_decoded`: an accepted calldata has a decodable accumulator. -/
theorem accDecodes_of_leanAcceptsAcc (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : LeanAcceptsAcc R H cd) : AccDecodes R cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, d, _, hchk⟩ := h
  intro enc henc
  have hw := instWords_of_decoded R cd ms instW inst ⟨hdec, hinst⟩
  unfold accFinalCheck at hchk
  simp only [henc] at hchk
  rw [← hw]
  cases ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (Midfall.Lowering.toExec enc) R.E.g1
      accTable instW with
  | none => simp [ha] at hchk
  | some a => exact ⟨a, rfl⟩

/-! ## §7. The target

  FIRST STATED (in `WideningV3.lean`) as
  `lowering_correctW (R) (Q) (product) (hR : ValidW R Q) : LoweringEquivalenceW R Q product`.
  THAT STATEMENT IS FALSE at an external render. `ValidW` constrains the evaluator object only
  through `EvalPins` (the pin constants, the output pointer, closedness of the body), so the same
  render is `ValidW` with the EMPTY body (`ValidW.emptyBody`, PROVED). Every answer of the empty
  body is a successful call with no return data (`evalModel_emptyBody`, PROVED); under
  `EvaluatorTrust.spec` those are all the chain's answers; the verifier's check
  `returndatasize() = outputLen` (QuotientAndLinearization.yul:37) fails; every run reverts; and
  conjunct 2 of `LoweringEquivalenceW` fails at any accepted calldata.

  THE TARGET THEREFORE CARRIES THE EVALUATOR'S CONTRACT, `hQ : isExternal R → EvalContracts R Q`
  (§4), the hypothesis the row families `SimContractsW` / `ProgContractsW` (§6) already take. It
  is dropped again in three cards:
    * WID.6  defines `evalObjectOf R : EvalObject` (the fallback body the Lean generator emits
             for `R`) and adds the clause `Q = evalObjectOf R` to `ValidW`;
    * WID.17 proves `EvalContracts R (evalObjectOf R)`;
    * WID.H  then drops `hQ`: `lowering_correctW (R) (product) (hR : ValidW R (evalObjectOf R))`. -/

/-- **THE TARGET.** The widened generic theorem: for every render the Lean generator emits in the
    widened class, PAIRED WITH AN EVALUATOR OBJECT THAT MEETS ITS THREE CONTRACTS, the four
    conjuncts hold. THE obligation; its decomposition is `lowering_equivalenceW_of` and the rows
    of §6. `hQ` is vacuous at a render that calls no evaluator (its guard is written out although
    `EvalContracts R Q` already reads `isExternal R → …`, so that the vacuity is visible in the
    statement), and is removed by cards WID.6 / WID.17 / WID.H (see above). -/
theorem lowering_correctW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (hR : ValidW R Q) (hQ : isExternal R → EvalContracts R Q) :
    LoweringEquivalenceW R Q product := by
  sorry

/-- **WHY `hQ` IS THERE (PROVED, no `sorry`).** If the target held WITHOUT the evaluator's
    contract, for every render and every evaluator object, then at every `ValidW` render the
    headline would hold with the evaluator's body replaced by the EMPTY block - an evaluator that
    answers every call with no return data (`evalModel_emptyBody`), which the verifier rejects.
    The conclusion is false at any external render with an accepted calldata; exhibiting one needs
    a real circuit (a test under rule W12), which is why this is the implication and not a `¬`. -/
theorem lowering_correctW_needs_evalContracts (product : PairingProduct)
    (hold : ∀ (R' : Render p G₁ G₂ Gₜ) (Q' : EvalObject),
      ValidW R' Q' → LoweringEquivalenceW R' Q' product)
    (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (hR : ValidW R Q) :
    LoweringEquivalenceW R ⟨[], Q.outMptr⟩ product :=
  hold R ⟨[], Q.outMptr⟩ hR.emptyBody

/-- The empty body does NOT meet the evaluator's contract: its shape row fails on every request
    of the wrong length (the body answers `success`, the row demands a failure). So `hQ` excludes
    the counterexample above. PROVED, given one entry frame and one request whose input is not
    `frameLen` bytes long. -/
theorem evalBodyShape_emptyBody_false (R : Render p G₁ G₂ Gₜ) (outMptr : Nat)
    (qe : QuotientExternal) (hqe : R.model.quotientExternal = some qe)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    (st : EvmState) (req : YulSemantics.EVM.CallRequest) (stC : EvmState)
    (hentry : EvalEntry ⟨[], outMptr⟩ W Lyt qAddr st req stC)
    (hlen : req.input.length ≠ qe.frameLen) : ¬ EvalBodyShape R ⟨[], outMptr⟩ := by
  intro h
  have hrun : YulSemantics.Run EVM.evm ([] : YulBlock) stC [] stC .normal := by
    unfold YulSemantics.Run
    exact Step.block (D := EVM.evm) (V := []) (Vb := []) Step.seqNil
  have hmodel : evalModel ⟨[], outMptr⟩ W Lyt qAddr req st
      (Evaluator.responseOf st (committedState stC stC)) :=
    ⟨stC, [], stC, .normal, hentry, hrun, rfl⟩
  have hfalse := (h qe hqe W Lyt H vkAddr qAddr cd
    (c := ExternalCalls.none) (g := ExternalGas.none) [] st req stC [] stC .normal hentry hrun).1
    hlen
  rw [(evalModel_emptyBody outMptr W Lyt qAddr req st _ hmodel).1] at hfalse
  cases hfalse

/-- **THE WIDENING SUBSUMES D-P71'S DELIVERABLE.** `lowering_correct` for `ValidV3` renders is the
    instance of `lowering_correctW` at V3's class. PROVED from `lowering_correctW`,
    `equivalenceW_iff_V3` and `model_quotientMode`: proving the widened theorem is not a second
    theorem beside the V3 one, it replaces it. A V3-valid render calls no evaluator, so the
    evaluator's contract is vacuous there and no hypothesis is added to D-P71's statement. -/
theorem lowering_correct_of_W (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : LoweringV3.ValidV3 R) : LoweringV3.LoweringEquivalenceV3 R product := by
  have Q : EvalObject := ⟨[], 0⟩
  have hq : R.model.quotientExternal = none := quotientExternal_none_of_V3 hR
  have hext : ¬ isExternal R := by simp [isExternal, hq]
  exact (equivalenceW_iff_V3 R Q product hR.supported.noAcc hq).mp
    (lowering_correctW R Q product (ValidW.ofV3 Q hR) (fun he => absurd he hext))

#print axioms pv_hasAcc_eq
#print axioms stageInv_false_of_acc
#print axioms inv_withAcc_of_noAcc
#print axioms inv_withAcc_decodes
#print axioms stageInvW_iff_V3
#print axioms lowering_correctW_needs_evalContracts
#print axioms evalBodyShape_emptyBody_false
#print axioms lowering_correct_of_W           -- sorryAx: lowering_correctW, model_quotientMode
#print axioms leanStageW_noAcc
#print axioms leanAcceptsAcc_of_final          -- sorryAx: the tree's snapshotOf_prepareMsgs
#print axioms leanFinalAcc_of_accepts          -- sorryAx: the tree's snapshotOf_prepareMsgs
#print axioms evalRel_answers
#print axioms accDecodes_of_leanAcceptsAcc     -- sorryAx: instWords_of_decoded

end Midfall.LoweringW
