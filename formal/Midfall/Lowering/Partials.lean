-- |
-- Midfall.Lowering.Partials
--
-- P-SE stage 4, file 2 of 2 (docs/plans/P-SE-stage4.md file row 2; design0.md
-- sections "Midfall.Lowering.PartialSpecs", "finalPairing_spec" and
-- "Midfall.Lowering.abiTrue / traceReturn_spec"; P-SE-semantic-equivalence.md
-- section N).
--
-- WHAT THIS FILE IS FOR. Stage 3 reported the headline blocker in one sentence: all
-- seven per-partial theorems had their Inv hypotheses and none of them could be
-- written, because there was no blk. P-13 ported the verifier templates as TEXT
-- renders - VerifierPartials.lean:2175 and its neighbours really do return String -
-- so no Lean function hands back the Block Op of a partial. This file is where that
-- function exists: Surface.blk (Surface.lean) is the abstract partial API, and
-- PartialSound, PartialProgress, PartialRejects and PartialSpecs below are the shapes
-- a per-partial theorem takes. The conversion is the point of the stage: seven
-- unwriteable theorems become seven statable ones, each with a registered hole where
-- the proof needs the AST that P-13 owes.
--
-- WHY THE SHAPE IS forall-runs AND NOT the vendored contract layer. The existential
-- StmtsContract (vendor Contract.lean:94) says SOME run of the block satisfies the
-- post. Under a RELATIONAL external-call relation - which is what soundness must
-- quantify over, since an open-world call admits many responses - that is the wrong
-- quantifier: the contract returns only if EVERY run does. Midfall/Yul/Contracts.lean
-- supplies StmtsContractAll and the composition lemmas the vendor lacks, including
-- the halting-head cons the fail(..) arms need, and this file consumes them.
--
-- THE ARITY LESSON FROM STAGE 3, APPLIED THROUGHOUT. Bridge.Dialect is @[reducible]
-- so that DecidableEq D.Value resolves, and the price is that calls and gas are
-- erased from VEnv (Bridge.Dialect calls gas): Inv implicit calls gas cannot be
-- recovered from the VEnv its own argument carries. So every definition here binds
-- calls and gas at the theorem level and passes them to Inv with named arguments.
-- Nothing in this file lets Lean guess them.
--
-- ATTACK FIX 36, USED RATHER THAN RESTATED. The soundness theorems quantify over an
-- arbitrary calls and take its world-locality as a hypothesis; the two lemmas stage 1
-- proved (honestCalls_worldLocal, permissive_worldLocal) are what discharge it, and
-- neither is reproved or restated here. The progress theorems run under the honest
-- fold, whose world-locality needs Evaluator.rel_worldLocal - a registered hole in
-- Bridge.lean - so it is a hypothesis here and named as such.
--
-- WHAT IS NOT HERE, and why. ir_refines and the shell-versus-IR equivalence are not
-- stated: their only run hypothesis is RunContractIR, which is uninhabited until the
-- vendored dialect grows memoryguard (D-P15; see the Surface.lean header), so a
-- theorem about it would be true because nothing satisfies it. The phase-prefix
-- refinement attack.md demands for PartialSpecs (its WEAKER-THAN-PLAN entry: state
-- partial k over a Snapshot_k built from the phase prefixes, so a late Lean fault does
-- not erase the hypothesis an earlier partial needs) is only HALF available here.
-- Stage 3 built the prefix runners - snapshotOfLagrange, snapshotOfQueries,
-- snapshotOfPcs - and Checkpoint.prefixNeeds records which boundary reads which, but
-- Inv is typed over a full Snapshot (Inv.lean, Inv and InvAt both take
-- Snapshot p G₁ G₂ Gₜ), and Inv.lean is stage 3 file, not this package to edit. So
-- every field below is stated against the whole snapshot, which is exactly the form
-- the attack calls weaker than plan. The remedy is one arity change in Inv.lean plus a
-- Snapshot_k projection per prefix record; it is reported as the outstanding
-- structural gap in the per-partial layer, not papered over here.
--
-- ONE MORE THING blk CANNOT DO. design0 second PartialSpecs shape - "if the Lean
-- prefix for phase k faults then every run of blk k from Inv (k-1) reverts" - is
-- stated here as PartialRejects, but keyed on an untyped Fault rather than on a
-- phase: Fault has two constructors, error of Error and panic of a site string
-- (Error.lean:56-58), and neither carries a phase, so the plan sketch form
-- snapshotOf = .error (.pcs, f) does not typecheck. Reported as a sketch name that
-- does not resolve.

import Midfall.Lowering.Surface
import Midfall.Yul.Contracts
import Midfall.Assumptions.Eip2537

namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]
  {calls : ExternalCalls} {gas : ExternalGas}

/-! ### The shapes -/

/-- A revert as the EVM state records it (EVMExec.lean:844-846): the halt kind is
    revert and the returned bytes are whatever the failing arm passed. Every
    fail(ERR_*) in a partial ends here, and the soundness post is a disjunction whose
    left arm is this - the right arm being the next checkpoint.

    Bool-valued with the Prop as the wrapper, the way stage 3 made Inv decidable: the
    gate below has to CHECK that a return record is not a revert, and a bare exists
    over a halt payload cannot be evaluated. -/
def revertedOf (h : Option (HaltKind × List UInt8)) : Bool :=
  match h with
  | some (.revert, _) => true
  | _ => false

/-- Reverted st: the frame halted by reverting. -/
def Reverted (st : EvmState) : Prop := revertedOf st.halted = true

/-- The soundness relation, in the form this package needs: any SUCCESS a run sees must
    be an answer the honest fold could have given, and a failure is always allowed
    because gas is unmodelled (a precompile may be missing, or out of gas, on a
    different deployment).

    Stated as a relation between two ExternalCalls rather than as an equality of
    response sets, because the fold under test is a parameter: a proof gets to assume
    the weakest relation that still pins the successful answers. design0 Permissive
    referred to Bridge.honestResponds, which does not exist in the tree; this is the
    same condition over the honest fold that does. -/
def PermissiveFor (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : PairingProduct)
    (qAddr : U256) (calls : ExternalCalls) : Prop :=
  ∀ req st resp, calls.Call req st resp → resp.success = true →
    (S.calls W product qAddr).Call req st resp

/-- The function scope a partial runs in: the hoisted definitions of the main block,
    then whatever the caller adds. AssemblyHelpers lives at the top of the assembly
    (fail, scalar_inv, squeeze_to, batch_invert, ec_pairing,
    validate_public_accumulator), and BigStep callOk runs a user function with only
    params ++ rets bound, so a helper has to be resolvable from the scope rather than
    from the partial. That is why the scope is hoist of the MAIN block and not of the
    slice: design0 says exactly this, and a scope built from the slice cannot find
    fail. -/
def mainScope (S : Surface p G₁ G₂ Gₜ) (calls : ExternalCalls) (gas : ExternalGas)
    (outer : FunEnv (Bridge.Dialect calls gas)) : FunEnv (Bridge.Dialect calls gas) :=
  hoist (Bridge.Dialect calls gas) S.L.main :: outer

/-- The one fact about the frame that every per-partial pre needs and Inv does not
    carry: the bytes the contract is reading are the bytes the decoder was given.
    Passed in as the addl slot of PartialSound rather than folded into Inv, because
    Inv is a memory-and-locals invariant over a snapshot and this is a fact about the
    run, not about the state the snapshot describes. -/
def calldataPre (_S : Surface p G₁ G₂ Gₜ) (cd : Bytes)
    (_V : VEnv (Bridge.Dialect calls gas)) (st : EvmState) : Prop :=
  st.env.calldata = cd.data.toList

/-- Soundness shape of one partial: every run from the invariant at q.pre either
    reverts, or finishes normally in the invariant at q.pre.next and establishes the
    partial-specific extra.

    addl is the extra pre-condition (the calldata link above) and extra the extra
    post-condition. Both are parameters rather than fixed because the two that matter
    are not uniform: lagrange_spec post-proves x^n not equal to 1 (the contract is
    STRICTER than Lean there, since batch_invert rejects zero and lIRange does not),
    and finalPairing_spec post-requires the success local to be 1.

    Note the quantifier: forall outer, so the contract holds in every caller scope,
    which is what lets the composition append the seven slices without pinning the
    scope each one was proved under. -/
def PartialSound (S : Surface p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ)
    (calls : ExternalCalls) (gas : ExternalGas)
    (addl : VEnv (Bridge.Dialect calls gas) → EvmState → Prop)
    (extra : VEnv (Bridge.Dialect calls gas) → EvmState → Prop) : Prop :=
  ∀ outer,
    StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)
      (S.blk q S.plan)
      (fun V st => Inv (calls := calls) (gas := gas) S.E S.params q.pre S.plan Snap V st ∧
        addl V st)
      (fun _ _ V' st' o =>
        (o = .halt ∧ Reverted st') ∨
          (o = .normal ∧
            Inv (calls := calls) (gas := gas) S.E S.params q.pre.next S.plan Snap V' st' ∧
            extra V' st'))

/-- Progress shape: under the honest functional relation, no revert, and the next
    checkpoint. The gas oracle stays a parameter: determinism needs ofFun (Bridge
    ExternalGas.any has no Functional proof, so Run.det would be unavailable), and the
    plan pins it to ofFun (fun _ => 0) at every call site.

    This is the twin that gives PartialSound its content. A block that reverts
    unconditionally satisfies PartialSound for every checkpoint - the left disjunct is
    always available - so soundness alone proves nothing about the deployment. always
    Reverts satisfies soundness is the lemma that says so, and it is proved rather
    than claimed. -/
def PartialProgress (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : PairingProduct)
    (qAddr : U256) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (gas : ExternalGas)
    (addl : VEnv (Bridge.Dialect (S.calls W product qAddr) gas) →
      EvmState → Prop) : Prop :=
  ∀ outer,
    StmtsContractAll (D := Bridge.Dialect (S.calls W product qAddr) gas)
      (mainScope S _ gas outer) (S.blk q S.plan)
      (fun V st =>
        Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params q.pre S.plan Snap V st ∧
          addl V st)
      (fun _ _ V' st' o =>
        o = .normal ∧
          Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params q.pre.next S.plan
            Snap V' st')

/-- The fault implies revert shape: when the Lean pipeline has already failed by the
    point this partial runs, every run of the partial reverts. design0 asks for this
    as the second form per partial, and it is the one that survives a missing snapshot:
    the pre is existential over snapshots precisely because a faulting run has no
    full snapshot to name.

    WHAT THE PLAN WROTE AND WHAT EXISTS. The plan sketch keys the hypothesis on a
    stage-tagged fault, snapshotOf = .error (.pcs, f). Fault has two constructors and
    neither carries a stage (Error.lean:56-58: error of Error, or panic of a site
    string), so the stage is not recoverable from the fault value and the sketch form
    does not typecheck. The version below takes an arbitrary fault and says which
    partial it is about by which partial the field names. -/
def PartialRejects (S : Surface p G₁ G₂ Gₜ) (q : Partial) (k : Checkpoint)
    (calls : ExternalCalls) (gas : ExternalGas) (pre : EvmState → Prop) : Prop :=
  ∀ outer,
    StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)
      (S.blk q S.plan)
      (fun V st =>
        (∃ Snap, Inv (calls := calls) (gas := gas) S.E S.params k S.plan Snap V st) ∧
          pre st)
      (fun _ _ _ st' o => o = .halt ∧ Reverted st')

/-- The per-partial obligations as a Prop structure, so the file that consumes them
    (Obligations.lean, stage 5) has one name to assume. Every field carries the common
    hypotheses explicitly rather than through a section variable, because the point of
    the structure is to be a checklist: a field that silently drops EnvAgrees is a
    theorem that cannot be proved later.

    The hypotheses, once, in words: hsup is the render (SupportedS over the Surface
    own data, so it cannot be chosen to make a field vacuous); henv ties the abstract
    environment to the literals the contract hard-codes; hperm is the soundness
    relation constraint; hcd and hinst are the calldata decode; hsnap is the snapshot
    of the run, which is what Inv relates memory to. logupNoPanic is deliberately
    absent from every field: under hsnap it is already implied, and attack.md marks a
    field implied by its own hypotheses decorative. -/
structure PartialSpecs (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) : Prop where
  /-- VkLoading.yul: the payload image lands at vkMptr and the calldata envelope is
      the one the layout says. -/
  vkLoading_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .vkLoading Snap calls gas (calldataPre S cd) (fun _ _ => True)
  transcriptParser_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .transcriptParser Snap calls gas (calldataPre S cd) (fun _ _ => True)
  /-- A normal exit PROVES x^n is not 1: the contract batch-inverts x^n - 1 and every
      x - omega^i in the rotation window and reverts on a zero (Lagrange.yul:93-99),
      where Lean lIRange yields zeros silently. -/
  lagrange_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .lagrange Snap calls gas (calldataPre S cd)
        (fun _ _ => Snap.alg.x ^ S.vk.domain.n ≠ 1)
  quotientLin_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .quotientLin Snap calls gas (calldataPre S cd) (fun _ _ => True)
  pcs_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .pcs Snap calls gas (calldataPre S cd) (fun _ _ => True)
  /-- The pairing decision: a normal exit has success = 1 in the locals, which is what
      TraceReturn keys on, and the post is the .pairing checkpoint of Inv. -/
  finalPairing_sound : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      PermissiveFor S W product qAddr calls →
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialSound S .finalPairing Snap calls gas (calldataPre S cd) (fun _ _ => True)
      -- R-58 F9: this post used to carry an extra conjunct, the claim that the
      -- success local is 1 after the block returns. It is implied by the post
      -- invariant itself: finalPairing's post checkpoint is .pairing, and Inv
      -- .pairing IS the clause (VEnv.get V "success" == some 1) plus the rest, so
      -- the conjunct could never fail independently of the invariant it sits next to
      -- - the decorative class. The fact is still asserted, once, where it belongs.
      -- the progress twin keeps its success = 1 entry condition on the PRE, where
      -- nothing implies it and where it is what makes the no-revert claim need the
      -- pairing check as a hypothesis.
  /-- traceReturn establishes no invariant, so its post is the halt record: return
      (RETURN_MPTR, 0x20) with the word 1 in it (TraceReturn.yul:70-72). -/
  traceReturn_sound : ∀ (H : Hash) (calls : ExternalCalls)
      (gas : ExternalGas) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
      (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      ∀ outer,
        StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)
          (S.blk .traceReturn S.plan)
          (fun V st =>
            Inv (calls := calls) (gas := gas) S.E S.params .pairing S.plan Snap V st ∧
              calldataPre S cd V st)
          (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue))
  -- progress twins, each with the side condition that makes it true
  vkLoading_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .vkLoading Snap gas (calldataPre S cd)
  transcriptParser_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .transcriptParser Snap gas (calldataPre S cd)
  /-- Needs ChallengesGood: at x = omega^i the contract reverts and Lean accepts, so
      without the side condition the no-revert claim is false (attack GenericX entry,
      and the reason EnvAgrees.omegaOrder exists). -/
  lagrange_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      ChallengesGood S.vk Snap →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .lagrange Snap gas (calldataPre S cd)
  quotientLin_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .quotientLin Snap gas (calldataPre S cd)
  pcs_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .pcs Snap gas (calldataPre S cd)
  /-- The pairing check has to pass for the honest fold to return: the contract
      reverts PROOF_REJECTED when the precompile answers 0, so DualMSM.check is a
      hypothesis of the no-revert claim and not a consequence of it. -/
  finalPairing_progress : ∀ (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
      (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
      (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
      SupportedS S S.o₀ → EnvAgrees S.E S.vk S.plan S.params S.sG2gen →
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
      DualMSM.check Snap.c.dual S.params = true →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .finalPairing Snap gas (calldataPre S cd)

/-! ### The seven per-partial theorems -/

/-! Each of the seven is stated with its full hypothesis bundle spelled out rather
    than hidden in a structure: the point of stating them is to see what each one
    needs, and a bundle alias would hide exactly that. -/

/-- VkLoading: the payload copy and the calldata envelope. PROOF HOLE: needs the
    VkLoading.yul AST as a Block Op (P-13), the memory-copy lemmas for mcopy over
    the payload window, and the extcodehash / extcodesize facts, which are
    DeploymentW conclusions (extcodehash_of_deployment) rather than assumptions. -/
theorem vkLoading_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .vkLoading Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- TranscriptProofParser: the challenge slots, the commitment regions and the read
    cursor. PROOF HOLE: needs the parser AST (P-13) and the transcript-squeeze
    agreement between the Yul keccak path and the Lean transcript, which is the
    readScheduleAgrees bridge the Encoding area owes. Note this is the one partial
    whose Inv post reaches past the parser: x1..x4 are squeezed inside the PCS phases
    (Snapshot.lean prefixNeeds), so the snapshot has to be the full one. -/
theorem transcriptParser_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .transcriptParser Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- Lagrange: x_n, the three Lagrange slots and the instance evaluation. The extra
    post-condition is the strictness direction: a normal exit proves x^n is not 1,
    because batch_invert rejected the zero that Lean lIRange would have returned.
    PROOF HOLE: needs the Lagrange.yul AST (P-13) and the batch-inversion contract
    from AssemblyHelpers (AssemblyHelpers.yul:226-229), plus EnvAgrees.domainN and
    baryWeight to make the k squarings and the N_INV factor agree. -/
theorem lagrange_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .lagrange Snap calls gas (calldataPre S cd)
      (fun _ _ => Snap.alg.x ^ S.vk.domain.n ≠ 1) := by
  sorry

/-- The progress twin, with the side condition that makes it true. Without
    ChallengesGood the claim is FALSE: at x = omega^i outside the rotation window the
    contract reverts ProofRejected and Lean accepts, so a no-revert statement needs
    the bad set excluded. EnvAgrees.omegaOrder is what turns x^n not equal to 1 into
    that exclusion (attack GenericX FIX). PROOF HOLE as for lagrange_spec. -/
theorem lagrange_progress_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hgood : ChallengesGood S.vk Snap)
    (hwl : (S.calls W product qAddr).WorldLocal)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialProgress S W product qAddr .lagrange Snap gas (calldataPre S cd) := by
  sorry

/-- QuotientAndLinearization: the two splitting-factor words, the linearization eval
    and the selector buckets. PROOF HOLE, and one of the two deepest ones: the Inv
    clauses for the eval and the buckets read Snapshot.lin, which snapshotOf always
    leaves none (D6 limit 1 - linearize returns only the query array), so the post
    cannot be established for a render that writes those slots until either linearize
    widens or the buckets become nameable another way. Hazard 4 decision: the
    positional pin (queries.back? at Verifier.lean:802) was NOT taken, so this hole
    stays where the widening belongs. -/
theorem quotientLin_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .quotientLin Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- Pcs.yul: f_eval, v, final_com and the two pairing inputs. PROOF HOLE: needs the
    Pcs.yul AST, which P-13 ported as TEXT only (Kzg.lean:1320 is the render), plus
    the committed-instance identity fact the attack names as finding 1 - the
    g1_identity window clause in Inv is what carries it, and it is only enough
    because that clause exists. -/
theorem pcs_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .pcs Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- FinalPairing, no-accumulator arm: the ec_pairing frame
    [RHS | G2_BASE | LHS | NEG_S_G2] (AssemblyHelpers.yul:284-287) built by
    ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR) (FinalPairing.yul:88)
    decides exactly DualMSM.check. The swap is at the call site, not in the helper,
    and the stale comment in Spec/Lemmas.lean:19-20 is about the layout rather than
    about the resulting pairs (attack dualMsm_check_reorder entry).

    Production only, and that is a hypothesis and not an assumption: a trace render
    returns iszero(iszero(ret)) and never reverts (FinalPairing.yul:81-87), which
    refutes both the revert arm and the success = 1 post. SupportedS.production is
    what excludes it. PROOF HOLE: needs the FinalPairing.yul and AssemblyHelpers.yul
    ASTs (P-13), the staticcall failure mapping (MF-4: both failure classes become
    PRECOMPILE_FAILED, absorbed by the revert arm), and Eip2537.Holds.pairing2 to
    turn the precompile answer into the pairing equation. -/
theorem finalPairing_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hh : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (hacc : S.plan.hasAccumulator = false)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .finalPairing Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
    -- R-58 F9: the success = 1 post conjunct is dropped here too, for the reason at
    -- PartialSpecs.finalPairing_sound: Inv .pairing already asserts it.
  sorry

/-- The progress twin: with the pairing check passing and the honest fold answering,
    the block returns normally into the .pairing checkpoint. The success = 1 entry
    condition is on the pre rather than derived, because Inv .pairing is the only
    place the local is claimed and this starts at .pcs (Inv.lean LocalsOk note).
    PROOF HOLE as for finalPairing_spec, plus Eip2537.Holds.pairing2 in the direction
    that turns a true check into a true precompile answer. -/
theorem finalPairing_progress_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hh : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (hcheck : DualMSM.check Snap.c.dual S.params = true)
    (hacc : S.plan.hasAccumulator = false)
    (hwl : (S.calls W product qAddr).WorldLocal)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialProgress S W product qAddr .finalPairing Snap gas (calldataPre S cd) := by
  sorry

/-- The accumulator arm (FinalPairing.yul:14-61 then :88). The batch preimage is
    tag, VK_DIGEST, RHS, LHS, ACC_RHS, ACC_LHS - 0x240 bytes at 0x1000 - and alpha is
    keccak mod r with 0 mapped to 1, which is exactly alphaOf
    (Exec/Accumulator.lean:1014-1021); the two slots are rewritten in place through
    G1MSM then G1ADD, so the decision is batchedCheck in the DualMSM orientation. The
    argument order is the R-11 trap: alphaOf takes (kzgLhs kzgRhs accLhs accRhs)
    while the hashed order puts RHS before LHS.

    hkec is necessary and not hygiene: alphaOf is hash-parametric while the EVM hashes
    through env.keccakOf (finding Y-2), so without it the alpha the contract computes
    is not the alpha the statement names. Snap.acc is the D6 limit 3 hole: no Exec
    phase produces a KzgAcc, so the snapshot carries none unless the caller decoded
    one - which is what accOf is for, and why hS is a hypothesis rather than a
    computation. PROOF HOLE: needs the accumulator partial ASTs and Eip2537.Holds
    g1Msm1 and g1Add for the slot rewrite. -/
theorem finalPairing_acc_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hh : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
    (henc : S.plan.hasAccumulator = true)
    (hS : Snap.acc = some a)
    (hkec : ∀ V st,
      Inv (calls := calls) (gas := gas) S.E S.params .pcs S.plan Snap V st →
        st.env.keccakOf = hashOfBytes H)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    ∀ outer,
      StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)
        (S.blk .finalPairing S.plan)
        (fun V st =>
          Inv (calls := calls) (gas := gas) S.E S.params .pcs S.plan Snap V st ∧
            calldataPre S cd V st)
        (fun _ _ V' st' o =>
          (o = .halt ∧ Reverted st') ∨
            (o = .normal ∧ VEnv.get V' "success" = some 1 ∧
              batchedCheck S.params
                (alphaOf (p := p) H S.vkDigest S.E.g1 Snap.c.dual.left.eval
                  Snap.c.dual.right.eval (a.fullyCollapse (tblOf S.accFixedBases)).1
                  (a.fullyCollapse (tblOf S.accFixedBases)).2)
                Snap.c.dual a (tblOf S.accFixedBases) = true)) := by
  sorry

/-- TraceReturn: the only partial whose post is a halt record rather than the next
    checkpoint, because there is no checkpoint after the pairing decision (Checkpoint
    next saturates). The exact shape matters: halted = some (.ret, abiTrue) is
    refuted by a block that returns 0x40 bytes, by one that returns the success word
    itself (a trace render), and by one that falls off the end without halting.
    PROOF HOLE: needs the TraceReturn.yul AST (P-13) and the return builtin record
    (EVMExec.lean:840-843 stores readBytes memory p s). -/
theorem traceReturn_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    ∀ outer,
      StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer)
        (S.blk .traceReturn S.plan)
        (fun V st =>
          Inv (calls := calls) (gas := gas) S.E S.params .pairing S.plan Snap V st ∧
            calldataPre S cd V st)
        (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) := by
  sorry

/-! ### Why both twins are needed -/

/-- The smallest block whose every run reverts: revert(0, 0) as the whole slice. -/
def alwaysReverts : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 0)])]

/-- SOUNDNESS ALONE IS SATISFIED BY A BLOCK THAT ALWAYS REVERTS. Stated and proved
    nowhere near trivially, but stated here because it is the vacuity class the whole
    programme keeps hitting (attack.md F1, four instances): the left disjunct of the
    PartialSound post is available to any block whose first statement reverts,
    whatever the invariant says. So the seven sound theorems, even all proved, would
    not establish that the deployment accepts an honest proof. That is what the
    progress twins are for, and why PartialSpecs carries both.

    PROOF HOLE, registered: the inversion is two cases on Step (seqCons versus
    seqStop, then exprStmt), and the remaining branch needs that no EVM builtin
    returns the empty value list for revert, i.e. an inversion through
    D.Builtin at the open dialect. Mechanical, not short, and nothing downstream
    depends on it - it is evidence about the definitions, not a step in a proof. -/
theorem partialSound_of_alwaysReverts (S : Surface p G₁ G₂ Gₜ) (q : Partial)
    (Snap : Snapshot p G₁ G₂ Gₜ) (calls : ExternalCalls) (gas : ExternalGas)
    (addl : VEnv (Bridge.Dialect calls gas) → EvmState → Prop)
    (extra : VEnv (Bridge.Dialect calls gas) → EvmState → Prop)
    (hblk : S.blk q S.plan = alwaysReverts) :
    PartialSound S q Snap calls gas addl extra := by
  sorry

/-- The same block refutes the progress twin whenever the pre is satisfiable, which is
    the other half of the point: the two shapes are not redundant with each other.
    PROOF HOLE, registered, same inversion as above plus that .halt is not .normal. -/
theorem partialProgress_not_of_alwaysReverts (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv)
    (product : PairingProduct) (qAddr : U256) (q : Partial)
    (Snap : Snapshot p G₁ G₂ Gₜ) (gas : ExternalGas)
    (addl : VEnv (Bridge.Dialect (S.calls W product qAddr) gas) → EvmState → Prop)
    (hblk : S.blk q S.plan = alwaysReverts)
    (hpre : ∃ (V : VEnv (Bridge.Dialect (S.calls W product qAddr) gas)) (st : EvmState),
      Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params q.pre S.plan Snap V st ∧
        addl V st) :
    ¬ PartialProgress S W product qAddr q Snap gas addl := by
  sorry

/-! ### Known-answer checks -/

/-- Reverted reads the halt record the way the EVM writes it: a revert with bytes and
    a revert without both count, a return does not, and no halt at all does not. If
    Reverted accepted .ret the soundness post would let a returning partial discharge
    the left disjunct, which is the exact collapse the only-two-outcomes conjunct
    exists to prevent. -/
def revertedKats_ok : Bool :=
  revertedOf (some (.revert, [1, 2])) &&
    revertedOf (some (.revert, [])) &&
    ! revertedOf (some (.ret, abiTrue)) &&
    ! revertedOf (some (.stop, [])) &&
    ! revertedOf (some (.selfdestruct, [])) &&
    ! revertedOf none &&
    -- and abiTrue is the 32-byte BE word 1 the return records
    abiTrue.length == 32

#eval revertedKats_ok                     -- expect true

/-- The seven partials and their boundaries, as the obligations use them: pre is the
    boundary the invariant is taken at, post its successor, and the seven pre
    boundaries are the seven checkpoints in order. Refuted by an off-by-one, which
    would state every partial against its neighbour invariant and still typecheck. -/
def partialSpecsChainKats_ok : Bool :=
  partials.length == 7 &&
    (partials.zipIdx.all fun (q, i) => q.pre.idx == i && q.post.idx == min (i + 1) 6) &&
    Partial.pre .traceReturn == .pairing && Partial.post .traceReturn == .pairing &&
    Partial.pre .vkLoading == .start && Partial.post .finalPairing == .pairing

#eval partialSpecsChainKats_ok            -- expect true

/-- The mechanism mainScope is built from: hoist of a block puts that block function
    definitions in scope for a call, and a scope without it cannot resolve the name.
    This is the assembly-helpers claim (fail and scalar_inv live at the top of the
    main assembly block, so a partial slice cannot see them on its own), checked on
    the smallest possible pair of scopes. mainScope itself cannot be exercised here
    without a Surface, which needs a pairing model (hazard 3), so the gate is on the
    mechanism and the claim about mainScope is that it is literally this expression. -/
def hoistScopeKats_ok : Bool :=
  let c : ExternalCalls := ⟨fun _ _ _ => False⟩
  let g : ExternalGas := ExternalGas.ofFun fun _ => 0
  let d := Bridge.Dialect c g
  let fd : FunEnv (Bridge.Dialect c g) := []
  let helpers : YulBlock := [Stmt.funDef "fail" ["code"] [] []]
  -- the hoisted scope resolves fail
  (lookupFun (hoist d helpers :: fd) "fail").isSome &&
    -- the bare scope does not
    (lookupFun fd "fail").isNone &&
    -- and a name nobody defines is absent from both
    (lookupFun (hoist d helpers :: fd) "ec_pairing").isNone &&
    -- so the hoist is a function of the block: an empty block adds nothing
    (lookupFun (hoist d [] :: fd) "fail").isNone

#eval hoistScopeKats_ok                   -- expect true

/-- The always-revert block really is a block of one statement whose only effect is a
    revert, i.e. the hypothesis of the two lemmas above is about something that exists
    and is not an empty type. Cheap, and it is the only executable thing that can be
    said about blk without a Surface. -/
def alwaysRevertsKats_ok : Bool :=
  alwaysReverts.length == 1 &&
    alwaysReverts.head?.isSome &&
    -- the one statement is an exprStmt whose expression is the revert builtin with two
    -- literal arguments. Matched rather than compared with = because Stmt carries no
    -- DecidableEq at this dialect, and a BEq-free equality would be a hole, not a gate.
    (match alwaysReverts with
     | [Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 0)])] => true
     | _ => false) &&
    -- and it is NOT the user-call spelling, which is what the yul% DSL produces for a
    -- name the dialect parser does not resolve: the difference is the whole D-P15 class
    (match alwaysReverts with
     | [Stmt.exprStmt (Expr.call _ _)] => false
     | _ => true)

#eval alwaysRevertsKats_ok                -- expect true

end Midfall.Lowering
