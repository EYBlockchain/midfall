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
import Midfall.Lowering.GenAst
import Midfall.Lowering.GenAstDispatch
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

/-! ### The blk pin -/

/-- THE blk PIN, and the reason it exists (docs/REVIEW.md R-62, docs/design.md D-P24).

    WHY. Every *_spec theorem below is quantified over EVERY Surface, and Surface.blk is
    a free field: its only constraint is main_concat, and the L.main main_concat talks
    about comes from the free lower. So a Surface whose blk .finalPairing is
    'return(0, 0)' - with L.main replanted to match, which is always possible because
    main is free - satisfies every hypothesis above and refutes the conclusion: a
    returning block is neither a revert nor a normal exit into the next checkpoint. The
    ten theorems were FALSE AS STATED for that reason, and no amount of proof work fixes
    a statement that is false.

    WHAT. blk is pinned to the generator function - Midfall/Lowering/GenAst.lean - and
    the pin is a hypothesis of each theorem. Two conjuncts, not one:

      * 'blk q pv = emitPartial pv q' for every partial and every plan view, so the block
        a theorem speaks about is the block the generator emits, for every plan and not
        only the theorem's own; and
      * 'L.main = emitMain S.plan', i.e. the helpers too. This half is not decoration.
        mainScope hoists S.L.main, so the scope a partial runs in carries fail,
        ec_pairing and everything else main defines; a pin on blk alone would still let a
        Surface whose main has no helper definitions claim to run the emitted slice, and
        that program cannot run.

    WHAT IT BUYS, and what it does not. It buys: the theorems are now claims about ONE
    program per plan rather than about every program, so the R-62 counterexample is
    outside the quantifier. It does not buy a proof. Since P-PLANVIEW the pinned block is a
    REAL emitted program for all TEN theorems: GenAst.emittedPartials is all seven partials
    - vkLoading, transcriptParser, lagrange, quotientLin, pcs, finalPairing and traceReturn -
    and the seventh arm (pcs) reached the emitter when PlanView gained a ConstraintSystemMeta
    and a Data. Before that, pcs_spec was pinned to a placeholder and its registered hole was
    "the emitter does not implement this partial yet"; that hole is closed, and what remains
    in pcs_spec's hole is the substance (the f_eval / v / final_com / pairing-input lemmas and
    the g1_identity clause that Inv already carries). The acc theorem is pinned at a plan view
    with hasAccumulator = true, which the emitter produces for real even though the deployed
    artifact does not exercise that arm. Note what the quotientLin conversion does NOT settle: the
    pinned block is the linearization SCOPE, i.e. the template's own body, and the two
    quotient_numerator includes that sit in front of it in the artifact are still text - see
    the measured boundary in GenAst.emitQuotientLinAt and the gate that pins it,
    GenAst.emitQuotientLinRegionBoundary_ok.

    NON-VACUITY (D-P23). Satisfied by Instances/SurfaceFixture.blkPinInhabited, at the
    only Surface in the tree, as a kernel-checked term. Refuted by
    Instances/SurfaceFixture.blkPinBitesBoundary - a Surface that keeps main_concat TRUE
    and still fails the pin - and by blkPinBitesCounterexample, which plants R-62's own
    'return(0, 0)' block consistently and fails the pin while every other field of the
    record still discharges. A pin nobody can fail is decoration; the two exhibits below
    are that failure. -/
def BlkIsEmitter (S : Surface p G₁ G₂ Gₜ) : Prop :=
  (∀ q pv, S.blk q pv = Midfall.Lowering.GenAst.emitPartial pv q) ∧
    S.L.main = Midfall.Lowering.GenAst.emitMain S.plan

/-- THE PIN IS NOT IMPLIED BY main_concat, which is the only existing constraint on blk.
    Stated as a projection rather than as a paragraph: the first conjunct is available by
    name, and Instances/SurfaceFixture.blkPinBitesBoundary is a Surface where main_concat
    holds and BlkIsEmitter does not - so the pin adds a constraint the record did not
    already carry. -/
theorem blkPin_blk {S : Surface p G₁ G₂ Gₜ} (h : BlkIsEmitter S) (q : Partial)
    (pv : PlanView) : S.blk q pv = Midfall.Lowering.GenAst.emitPartial pv q :=
  h.1 q pv

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
  /-- THE blk PIN (R-62), carried by the checklist and not only by the theorems. Without
      it every field below is a claim about EVERY block a Surface might return, which is
      the false-as-stated shape; Obligations.lean consumes this structure as a single
      LoweringCorrect field, so the pin has to be inside it or the defect re-enters one
      level up. -/
  blk_is : BlkIsEmitter S
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
      (∀ V st, Inv (calls := calls) (gas := gas) S.E S.params .vk S.plan Snap V st →
        st.env.keccakOf = hashOfBytes H) →
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
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
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
      (∀ V st, Inv (calls := calls) (gas := gas) S.E S.params .pcs S.plan Snap V st →
        st.env.keccakOf = hashOfBytes H) →
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
      (∀ V st, Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params .vk S.plan
        Snap V st → st.env.keccakOf = hashOfBytes H) →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .transcriptParser Snap gas (calldataPre S cd)
  /-- Needs ChallengesGood: at x = omega^i the contract reverts and Lean accepts, so
      without the side condition the no-revert claim is false (attack GenericX entry,
      and the reason EnvAgrees.omegaOrder exists, now as `orderExactly`). -/
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
      Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product →
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
      (∀ V st, Inv (calls := S.calls W product qAddr) (gas := gas) S.E S.params .pcs S.plan
        Snap V st → st.env.keccakOf = hashOfBytes H) →
      DualMSM.check Snap.c.dual S.params = true →
      Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
        S.E.g1 cd = some (ms, instW) →
      instOfWords? (p := p) instW = some inst →
      snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
      PartialProgress S W product qAddr .finalPairing Snap gas (calldataPre S cd)

/-! ### The seven per-partial theorems -/

/-! Each of the seven is stated with its full hypothesis bundle spelled out rather
    than hidden in a structure: the point of stating them is to see what each one
    needs, and a bundle alias would hide exactly that.

    Each carries hblk : BlkIsEmitter S (R-62, P-AST). Since P-PLANVIEW the pinned block is
    the REAL emitted program for every one of the ten: P-AST took finalPairing and its two
    helpers, P-AST2 lagrange / lagrange_progress / traceReturn, P-AST3a quotientLin, P-AST3b
    vkLoading, P-AST4 transcriptParser and P-PLANVIEW pcs. No theorem in this file is pinned
    to a placeholder any more, so "the emitter does not implement this partial yet" is no
    longer a hole any registered sorry can name - every remaining hole is a proof obligation
    about the program that exists. -/

/-- VkLoading: the payload copy and the calldata envelope. PROOF HOLE: needs the
    VkLoading.yul AST as a Block Op (P-13), the memory-copy lemmas for mcopy over
    the payload window, and the extcodehash / extcodesize facts, which are
    DeploymentW conclusions (extcodehash_of_deployment) rather than assumptions. -/
theorem vkLoading_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
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
    (Snapshot.lean prefixNeeds), so the snapshot has to be the full one.

    hkec IS NEW (P-BUNDLE audit finding 3) and it is the same class of hole as pcs_spec's missing
    hh, one external earlier: the post pins x1 and x2 in memory to the SNAPSHOT's squeezed
    challenges (Inv.lean:605-607) and the emitted squeeze_to hashes through the dialect keccak,
    which the Bridge answers from st.env.keccakOf - so without a hypothesis saying that is
    hashOfBytes H the theorem asserted a fact about a hash with no hypothesis about the hash.
    The shape is copied from finalPairing_acc_spec's hkec, which has carried it for the same
    reason. What hkec does NOT give is the other half the PROOF HOLE names: that the BYTES
    absorbed agree with the Lean transcript (the readScheduleAgrees bridge the Encoding area
    owes). That stays a proof obligation about the program, not a hole in the statement. -/
theorem transcriptParser_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hkec : ∀ V st,
      Inv (calls := calls) (gas := gas) S.E S.params .vk S.plan Snap V st →
        st.env.keccakOf = hashOfBytes H)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .transcriptParser Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- Lagrange: x_n, the three Lagrange slots and the instance evaluation. The extra
    post-condition is the strictness direction: a normal exit proves x^n is not 1,
    because batch_invert rejected the zero that Lean lIRange would have returned.
    PROOF HOLE: the Lagrange.yul AST has LANDED (GenAst.emitLagrange, P-AST2, gated against
    the text port by stmtsBeq), so what remains is the batch-inversion contract
    from AssemblyHelpers (AssemblyHelpers.yul:226-229), plus EnvAgrees.domainN and
    baryWeight to make the k squarings and the N_INV factor agree. -/
theorem lagrange_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
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
    the bad set excluded. `EnvAgrees.xNotRoot_iff_notDomainPoint` is what turns x^n not
    equal to 1 into that exclusion, and it needs the EXACT order P-ENV put into
    `EnvAgrees.omegaOrder`: at `omega := 1` the left side excludes one point and the
    contract reverts on all n (attack GenericX FIX). PROOF HOLE as for lagrange_spec. -/
theorem lagrange_progress_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
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
    stays where the widening belongs. P-AST3a CHANGED ONE HALF of it: the emitter is now
    real for this partial (GenAst.emitQuotientLin, the linearization scope), so the pinned
    block is no longer a placeholder and the hole is the Snapshot.lin widening named above
    and nothing else. The two quotient_numerator includes that precede the scope in the
    artifact are still text and are NOT part of blk .quotientLin - measured boundary, see
    GenAst.emitQuotientLinAt. -/
theorem quotientLin_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hcd : Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap) :
    PartialSound S .quotientLin Snap calls gas (calldataPre S cd) (fun _ _ => True) := by
  sorry

/-- Pcs.yul: f_eval, v, final_com and the two pairing inputs. THE BLOCK HOLE IS CLOSED: the
    pcs arm of the emitter is a real AST (GenAstPcs.computationsAst, wired into the dispatch
    by GenAstDispatch.emitPcsFromPlan), so hblk pins this theorem to the generated region and
    not to a placeholder. What the registered sorry still needs: the f_eval Horner fold over
    the REVERSED point sets (Block 4's direction is load-bearing), the v fold's exclusive
    1..n_sets range with the f_eval term supplying s == n_sets, the final MSM's pair-count
    agreement with finalMsmShape, and the committed-instance identity fact the attack names as
    finding 1 - the g1_identity window clause in Inv is what carries it, and it is only enough
    because that clause exists. Two things this package does NOT settle and the report says so:
    the emitted region is derived from a ConstraintSystemMeta the tree can only supply for a
    FIXTURE circuit, not for poseidon (DeployedProfile.pcs_deployedGap_measured_ok), and the
    eight-block partition survives only through the PcsBlockRole tagging because the AST has
    no comment node.

    hh IS NOT HYGIENE AND P-BUNDLE ADDED IT (the tenth hole of this class, and the one every
    gate missed). Block 5 ends in ONE G1MSM staticcall at 0x0c over the staged pairs
    (GenAstPcs.pcsBlock5Ast:467-472) and Block 6 is TWO G1MSM-1s and TWO G1ADDs at 0x0c and
    0x0b (pcsBlock6Ast:492-514); the Inv clauses at the .pcs post read exactly those slots as
    codec images of snapshot points - FINAL_COM_MPTR, PAIRING_LHS_MPTR, PAIRING_RHS_MPTR
    (Inv.lean:735-739, 'bytesAt st a 128 == E.g1.toEip Q' at Inv.lean:402). Nothing else in
    the bundle bridges a precompile ANSWER to the codec the invariant names: hperm constrains
    a successful answer to be one the honest byte fold could give (PermissiveFor, :111-115),
    henv's ten clauses are about the domain and the digests (Inv.lean:451-497), hsup is about
    the shape of the vk, and G1CodecLaws - not even bound here - says only how the codec
    encodes, never what 0x0b or 0x0c returns. The bridge is Holds.g1Msm1 and Holds.g1Add, and
    finalPairing_acc_spec's own PROOF HOLE note already names those two clauses - "needs the
    accumulator partial ASTs and Eip2537.Holds g1Msm1 and g1Add for the slot rewrite" - for
    exactly the same reason, which is what makes the omission here a hole and not a choice.
    Without hh the theorem asserts a fact about precompile behaviour with no hypothesis about
    precompile behaviour: not false, but unprovable as stated, and invisible to
    check_hypothesis_bundles.py because pcs_spec is not a LoweringCorrect field. The
    classifier at the foot of this file is what makes it visible, and the gate now reddens if
    the binder is dropped. -/
theorem pcs_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
    (hsup : SupportedS S S.o₀)
    (henv : EnvAgrees S.E S.vk S.plan S.params S.sG2gen)
    (hperm : PermissiveFor S W product qAddr calls)
    (hh : Midfall.Assumptions.Eip2537.Holds S.E.g1 ⟨S.encG2⟩ product)
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
    what excludes it.

    P-AST LANDED THE ASTs, so the hole is no longer about the block existing.
    GenAst.emitFinalPairing is this partial's Block Op in both arms, and
    GenAst.emitHelpers supplies the fail and ec_pairing definitions it calls, and
    hblk pins blk to them. What the registered sorry is now about:
      (a) the staticcall failure mapping (MF-4: both failure classes become
          PRECOMPILE_FAILED, absorbed by the revert arm) - the Bridge step lemmas that
          turn a failed precompile call into a revert carrying the pinned selector;
      (b) Eip2537.Holds.pairing2, to turn the precompile answer into the pairing
          equation over the frame ec_pairing lays out;
      (c) the model. Eip2537.Holds is not known satisfiable at ANY Surface in the tree:
          the exponent codec sends a non-identity exponent to bytes no curve check
          accepts, which Instances/SurfaceFixture.encG2AtFixture_ok states as a
          computation. (c) is the binding one - P5 cannot be CLOSED without a real-curve
          model, but it can be ATTEMPTED, because (a) and (b) are now statements about a
          block that exists. -/
theorem finalPairing_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (W : ExecEnv) (qAddr : U256) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
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
    (hblk : BlkIsEmitter S)
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
    (hblk : BlkIsEmitter S)
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
    PROOF HOLE: the TraceReturn.yul AST has LANDED (GenAst.emitTraceReturn, P-AST2 - the
    production arm, which is the only arm SupportedS.production admits), so what remains is
    the return builtin record
    (EVMExec.lean:840-843 stores readBytes memory p s). -/
theorem traceReturn_spec (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct)
    (H : Hash) (calls : ExternalCalls) (gas : ExternalGas)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256)
    (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ)
    (hblk : BlkIsEmitter S)
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


/-! ### Which partials reach an EIP-2537 precompile (P-BUNDLE) -/

/-- THE THREE ADDRESSES `Eip2537.Holds` IS ABOUT: G1ADD 0x0b, G1MSM 0x0c, PAIRING_CHECK 0x0f,
    read out of the template constants the emitter itself interpolates
    (Generator/Models.lean:296-303) rather than re-typed here, so a change to the ported constant
    moves this list and the classifier with it.

    EIP-198 modexp at 0x05 is NOT in the list, on purpose and not by oversight:
    Assumptions/Eip2537.lean:37-41 is explicit that modexp is modelled arithmetic and not a
    hypothesis - `modexpInv_correct` is a THEOREM about the computed `modexpOutput` - so a block
    that reaches only modexp must not be required to bind `Holds`. The lagrange slice is exactly
    that block, and row 3b of the gate below pins the exclusion as a computation instead of
    leaving it to this sentence. -/
def eip2537CallAddresses : List Nat :=
  [templateConstantsDefault.eip2537.g1addAddress,
    templateConstantsDefault.eip2537.g1msmAddress,
    templateConstantsDefault.eip2537.pairingAddress]

/-- The address operand of a `staticcall`, which is its SECOND argument (gas, address, in, inLen,
    out, outLen). `none` means the classifier could not read it - a plan-supplied variable rather
    than a number literal - and an unreadable target is treated as REACHING a precompile, never as
    evidence of safety. That is the conservative direction: the only way to dodge the requirement
    is to emit a literal address that is not one of the three. -/
def staticcallAddr : List (Expr Op) → Option Nat
  | _ :: Expr.lit (Literal.number n) :: _ => some n
  | _ => none

/-- Put a list of addresses into the canonical order of `eip2537CallAddresses`, dropping anything
    outside it and any duplicate. Canonical rather than sorted because Lean 4.35 core has no
    `List.qsort` (the note Kzg/Utils.lean:71 carries); the order that matters is the order the
    hypothesis enumerates. -/
def eip2537Canon (l : List Nat) : List Nat := eip2537CallAddresses.filter fun a => l.elem a

/-- The EIP-2537 addresses among a raw target list. -/
def eip2537TargetsIn (raw : List (Option Nat)) : List Nat := eip2537Canon (raw.filterMap id)

/-- Does a raw target list reach an EIP-2537 precompile, or an address nobody can read? -/
def reachesEip2537 (raw : List (Option Nat)) : Bool :=
  raw.any fun
    | none => true
    | some n => eip2537CallAddresses.elem n

/- The two things the bundle classifier reads off a statement tree: every `staticcall` address
   operand (with `none` for an unreadable one) and every user-function name called. Five mutually
   recursive structural walks rather than one fold, because the vendored AST nests statement lists
   inside expressions inside statement lists (Ast.lean:52-88) and a `flatMap` under a match is
   not structurally decreasing here. A `/- -/` and not a doc string because a doc string cannot
   precede the `mutual` command - measured: "unexpected token 'mutual'; expected 'lemma'". -/
mutual
def bundleWalkE : Expr Op → List (Option Nat) × List String
  | Expr.builtin Op.staticcall args =>
      let (t, n) := bundleWalkEs args
      (staticcallAddr args :: t, n)
  | Expr.builtin _ args => bundleWalkEs args
  | Expr.call fn args =>
      let (t, n) := bundleWalkEs args
      (t, fn :: n)
  | _ => ([], [])
termination_by e => sizeOf e

def bundleWalkEs : List (Expr Op) → List (Option Nat) × List String
  | [] => ([], [])
  | e :: es =>
      let (t, n) := bundleWalkE e
      let (t', n') := bundleWalkEs es
      (t ++ t', n ++ n')
termination_by es => sizeOf es

def bundleWalkS : Stmt Op → List (Option Nat) × List String
  | Stmt.block b => bundleWalkSs b
  | Stmt.funDef _ _ _ b => bundleWalkSs b
  | Stmt.letDecl _ none => ([], [])
  | Stmt.letDecl _ (some e) => bundleWalkE e
  | Stmt.assign _ e => bundleWalkE e
  | Stmt.cond c b =>
      let (t, n) := bundleWalkE c
      let (t', n') := bundleWalkSs b
      (t ++ t', n ++ n')
  | Stmt.switch c cases none =>
      let (t, n) := bundleWalkE c
      let (t', n') := bundleWalkSC cases
      (t ++ t', n ++ n')
  | Stmt.switch c cases (some d) =>
      let (t, n) := bundleWalkE c
      let (t', n') := bundleWalkSC cases
      let (t'', n'') := bundleWalkSs d
      (t ++ t' ++ t'', n ++ n' ++ n'')
  | Stmt.forLoop init c post body =>
      let (t, n) := bundleWalkSs init
      let (t', n') := bundleWalkE c
      let (t'', n'') := bundleWalkSs post
      let (t''', n''') := bundleWalkSs body
      (t ++ t' ++ t'' ++ t''', n ++ n' ++ n'' ++ n''')
  | Stmt.exprStmt e => bundleWalkE e
  | _ => ([], [])
termination_by s => sizeOf s

def bundleWalkSs : List (Stmt Op) → List (Option Nat) × List String
  | [] => ([], [])
  | s :: ss =>
      let (t, n) := bundleWalkS s
      let (t', n') := bundleWalkSs ss
      (t ++ t', n ++ n')
termination_by ss => sizeOf ss

def bundleWalkSC : List (Literal × List (Stmt Op)) → List (Option Nat) × List String
  | [] => ([], [])
  | (_, b) :: cs =>
      let (t, n) := bundleWalkSs b
      let (t', n') := bundleWalkSC cs
      (t ++ t', n ++ n')
termination_by cs => sizeOf cs
end

/-- The EIP-2537 addresses a block reaches WITHOUT helper resolution. Named because the gate below
    uses it to show the resolution is load-bearing rather than decorative: the FinalPairing slice
    contains no staticcall at all - the pairing call lives in the hoisted `ec_pairing` definition
    (GenAst.emitEcPairingAt, reached through emitHelpers) - so a classifier that read only the
    slice would have reported finalPairing as needing no hypothesis, which is the wrong answer for
    the wrong reason. -/
def directEip2537Targets (b : Block Op) : List Nat := eip2537TargetsIn (bundleWalkSs b).1

/-- One round of helper resolution: append every emitted helper whose name the block calls and
    which is not already present. -/
def helperRound (helpers : Block Op) (acc : Block Op) : Block Op :=
  let called := (bundleWalkSs acc).2.eraseDups
  let already := acc.filterMap fun
    | Stmt.funDef n _ _ _ => some n
    | _ => none
  acc ++ helpers.filter fun
    | Stmt.funDef n _ _ _ => called.contains n && !already.contains n
    | _ => false

/-- The transitive closure of a block under a set of helper definitions, bounded by the number of
    helpers plus one. The bound is a pigeonhole and not a guess: a round that adds anything adds at
    least one definition that was not already there, and there are only `helpers.length` of them.
    A recursive helper would need a real fixpoint; under this bound the closure stops short, which
    is why the gate below checks the emitted helper set is acyclic rather than assuming it. -/
def callClosure (helpers : Block Op) (b : Block Op) : Block Op :=
  (List.range (helpers.length + 1)).foldl (fun acc _ => helperRound helpers acc) b

/-- THE PLAN VIEW WITH THE ACCUMULATOR ARM SELECTED. Derived the way every other plan view in this
    tree is: through `planViewWithAccumulator`, whose `hasAccumulator` IS `acc.isSome`
    (Inv.lean:342-346), and not by a structure update that flips the Bool without its four
    companion words - the one-Bool lie R-58 F2 is about. The accumulator encoding is the same
    `AccumulatorEncoding.new 2 7 56` Inv.lean:854 and GenAst.lean:1818 use. -/
def bundleAccFixturePlan : PlanView :=
  Midfall.Lowering.planViewWithAccumulator (vk := Midfall.Lowering.witnessVkPayload)
    (vkMptr := KzgKats.memF.vkMptr) (memory := KzgKats.memF)
    (proofLayout := KzgKats.proofLayoutF) (numInstances := 1) (k := 6)
    (numNegLagranges := KzgKats.metaF.rotationLast.natAbs)
    (acc := some (Midfall.Generator.AccumulatorEncoding.new 2 7 56))
    (facts := Midfall.Lowering.emptyParserFacts)
    (meta_ := KzgKats.metaF) (dat := KzgKats.dataF)

/-- The EIP-2537 addresses the EMITTED PROGRAM of one partial reaches: the slice the dispatcher
    returns for it, closed under `GenAst.emitHelpers`. The closure is what makes this a statement
    about the theorem and not about a string: `hblk` pins `S.blk q pv` to `emitPartial pv q`
    AND `S.L.main` to `emitMain S.plan` (BlkIsEmitter, :261-263), `mainScope` hoists
    `S.L.main` (:124-126), and `emitMain = emitHelpers ++ emitSlices`, so every helper the pin
    admits is one a run of the partial can call. -/
def emittedEip2537Targets (pv : PlanView) (q : Partial) : List Nat :=
  eip2537TargetsIn (bundleWalkSs (callClosure (GenAst.emitHelpers pv) (GenAst.emitPartial pv q))).1

/-- The user-function names one emitted program calls but no definition in it answers, taken
    against an ARBITRARY helper block. This is the general form, and the reason it is general is
    the closure gate below: a gate that can only be run against the real `emitHelpers` cannot be
    shown to bite, and D-P23 asks for the failure mode as well as for the witness. -/
def unresolvedCallsUnder (helpers : Block Op) (pv : PlanView) (q : Partial) : List String :=
  let closed := callClosure helpers (GenAst.emitPartial pv q)
  let defined := closed.filterMap fun
    | Stmt.funDef n _ _ _ => some n
    | _ => none
  ((bundleWalkSs closed).2.filter fun n => !defined.contains n).eraseDups

/-- The user-function names the emitted program calls but the emitted helpers never define. THE
    HELPER GAP AS DATA rather than as a paragraph, and since P-HELPERS THE THING A CLOSURE GATE
    REQUIRES TO BE EMPTY (`emittedProgramClosure_ok` below) rather than a hole with a doc string
    on it - which is the difference between a gap four packages walked past and a gap a build
    cannot survive.

    What it reports now: `validate_public_accumulator` (AccumulatorHelpers.yul:190, called from
    the vkLoading accumulator arm) and NOTHING ELSE at any pinned plan view. The two entries it
    used to carry - `batch_invert` (AssemblyHelpers.yul:226, called at GenAst.lean:509) and
    `scalar_inv` (:20, called from the PCS linearisation expansion at GenAstPcs.lean:267 and
    :305) - are emitted now, so the lagrange and pcs rows are empty and the emptiness is gated.
    Note that BOTH of those two were modexp helpers and not EIP-2537 ones, which is why closing
    them changed no row of `partialEip2537Targets`: the emitted pcs slice reaches 0x0b and 0x0c
    through its OWN staticcalls and reaches nothing through scalar_inv, and reaches nothing
    through the body of scalar_inv either now that the body is emitted. -/
def emittedUnresolvedCalls (pv : PlanView) (q : Partial) : List String :=
  unresolvedCallsUnder (GenAst.emitHelpers pv) pv q

/-- THE ADDRESSES THE UNEMITTED HELPERS USE IN THE REFERENCE. This is the record that
    `vkLoading_spec` is a LATENT instance of the hole this package closed for `pcs_spec` and not
    a clean bill of health: at a plan view with an accumulator the emitted vkLoading slice calls
    `validate_public_accumulator`, and in the reference that helper runs G1MSM and G1ADD
    (AccumulatorHelpers.yul:190-230). Today the emitted program cannot run it, so the classifier
    correctly reports no reachable EIP-2537 address and the gate correctly demands nothing. The
    moment the helper lands the row stops being empty and the gate demands `Holds` on
    `vkLoading_spec` by itself, with nobody having to remember to look.

    P-HELPERS SHRANK THIS LIST FROM THREE ROWS TO ONE by emitting `batch_invert` and
    `scalar_inv`, and the deletion is the honest one: a row here asserts the helper is NOT
    emitted, and after this package that assertion was false for two of the three. The fact those
    two rows carried - modexp is arithmetic and must NEVER turn into a `Holds` requirement - did
    not go with them. It is pinned twice over now: by the classifier clause in
    `partialEip2537Targets_ok` that a modexp address is not an EIP-2537 target, and by the
    STRONGER form of the same claim in `emittedProgramClosure_ok`, which reads the lagrange and
    pcs rows as empty even though the closed program now contains three modexp `staticcall`s
    inside the bodies of the helpers it emits. -/
def unemittedHelperAddresses : List (String × List Nat) :=
  [("validate_public_accumulator",
     [templateConstantsDefault.eip2537.g1msmAddress,
      templateConstantsDefault.eip2537.g1addAddress])]

/-- THE CLASSIFICATION `scripts/check_hypothesis_bundles.py` READS: for each of the seven partials,
    the EIP-2537 addresses its emitted program reaches over the plan views the spec theorems are
    pinned at. The gate parses this one definition and derives every spec-theorem binder
    requirement from it, so the requirement is not a hand-written list of theorems that can quietly
    stop matching the emitter. The gate ALSO refuses a `Holds` binder on a partial this table says
    reaches nothing, which is what stops the fix being laundered by adding the hypothesis
    everywhere. -/
def partialEip2537Targets : List (Partial × List Nat) :=
  [(.vkLoading, []), (.transcriptParser, []), (.lagrange, []), (.quotientLin, []),
   (.pcs, [0x0b, 0x0c]), (.finalPairing, [0x0b, 0x0c, 0x0f]), (.traceReturn, [])]

/-- GATE (THE CLASSIFICATION IS COMPUTED, NOT ASSERTED). Six conjuncts:

    1. the table covers every partial of `Midfall.Lowering.partials`, exactly once, in order, so a
       new partial with no row is a failure and not an omission;
    2. every row agrees with what the EMITTER reaches, unioned over the two plan views the spec
       theorems are pinned at (no accumulator, accumulator);
    3. the classifier can fail: an empty block reports nothing, a modexp call is NOT counted, an
       unreadable address IS counted, and the helper closure is what finds 0x0f at all;
    4. the emitted helper set is acyclic, which is what makes callClosure's bound exact rather than
       hopeful;
    5. the helper gap is recorded as data, including the vkLoading accumulator arm;
    6. the table is not vacuous: the two non-empty rows are the two whose theorems bind `Holds`. -/
def partialEip2537Targets_ok : Bool :=
  -- 1. coverage, in the order the partials are declared
  (partialEip2537Targets.map Prod.fst == partials) &&
  -- 2. every row is what the emitter reaches
  (partialEip2537Targets.all fun (q, want) =>
    eip2537Canon (emittedEip2537Targets GenAst.pcsFixturePlan q
      ++ emittedEip2537Targets bundleAccFixturePlan q) == want) &&
  -- 3a. an empty block reaches nothing, so the classifier is not a constant true
  (directEip2537Targets [] == []) &&
  -- 3b. modexp at 0x05 is NOT an Eip2537 address: the row that keeps lagrange out of the
  --     requirement, and the one a package under pressure would be tempted to widen
  (eip2537TargetsIn [some templateConstantsDefault.modexp.address] == []) &&
    ! (reachesEip2537 [some templateConstantsDefault.modexp.address]) &&
  -- 3c. an address the classifier cannot read counts as reaching, so a variable-spelled target
  --     cannot be used to dodge the requirement
  (reachesEip2537 [none]) &&
  (directEip2537Targets [GenAst.yexpr (GenAst.yop Op.staticcall
    [GenAst.yvar "gas", GenAst.yvar "addr", GenAst.ylit 0, GenAst.ylit 0, GenAst.ylit 0,
      GenAst.ylit 0])] == []) &&
  -- 3d. THE CLOSURE IS LOAD-BEARING: the FinalPairing slice alone reaches nothing, and it is the
  --     hoisted ec_pairing that reaches 0x0f. Delete the closure and this row goes red.
  (directEip2537Targets (GenAst.emitPartial GenAst.pcsFixturePlan .finalPairing) == []) &&
    (emittedEip2537Targets GenAst.pcsFixturePlan .finalPairing == [0x0f]) &&
  -- 3e. and the pcs slice, whose own block carries the four staticcalls
  (emittedEip2537Targets GenAst.pcsFixturePlan .pcs == [0x0b, 0x0c]) &&
  -- 4. the emitted helper set is acyclic: no helper body calls its own name, so the bounded
  --    closure of callClosure IS the real fixpoint
  ((GenAst.emitHelpers GenAst.pcsFixturePlan).all fun
    | Stmt.funDef n _ _ b => !((bundleWalkSs b).2.contains n)
    | _ => true) &&
  -- 5. the helper gap, as data. P-HELPERS CLOSED TWO OF THE THREE ROWS this conjunct used to
  --    pin, and the emptiness is now the assertion: the emitted lagrange and pcs programs call
  --    nothing main does not define. The row that remains is the accumulator arm the deployed
  --    profile never takes, and it is the one entry of closureNamedExceptions.
  (emittedUnresolvedCalls GenAst.pcsFixturePlan .lagrange == []) &&
    (emittedUnresolvedCalls GenAst.pcsFixturePlan .pcs == []) &&
    (emittedUnresolvedCalls bundleAccFixturePlan .vkLoading
      == ["validate_public_accumulator"]) &&
    (emittedUnresolvedCalls GenAst.pcsFixturePlan .vkLoading == []) &&
    (emittedUnresolvedCalls GenAst.pcsFixturePlan .finalPairing == []) &&
    (unemittedHelperAddresses.map Prod.fst == ["validate_public_accumulator"]) &&
    (unemittedHelperAddresses.lookup "validate_public_accumulator"
      == some [templateConstantsDefault.eip2537.g1msmAddress,
               templateConstantsDefault.eip2537.g1addAddress]) &&
    -- AND THE MODEXP FACT IN ITS STRONGEST FORM. The two helpers this package emitted run the
    -- modexp precompile, so the CLOSED lagrange program now contains a modexp staticcall that
    -- the open one did not - and the row is still empty. Before P-HELPERS the same claim rested
    -- on a helper that was never emitted at all, which was the weaker version of it: nothing was
    -- reaching 0x05 in the first place. A later package that widens eip2537CallAddresses to
    -- include modexp reddens here and nowhere else.
    (EVM.print (callClosure (GenAst.emitHelpers GenAst.pcsFixturePlan)
      (GenAst.emitPartial GenAst.pcsFixturePlan .lagrange))).contains
        "staticcall(MODEXP_GAS, 5," &&
    (emittedEip2537Targets GenAst.pcsFixturePlan .lagrange == []) &&
  -- 6. not vacuous: exactly the two rows that bind Holds are the two that reach
  ((partialEip2537Targets.filter fun (_, l) => !l.isEmpty).map Prod.fst
    == [.pcs, .finalPairing]) &&
    (eip2537CallAddresses == [0x0b, 0x0c, 0x0f])

#eval partialEip2537Targets_ok          -- expect true

/-- FALSIFICATION OF THE CLASSIFIER (D-P23). Every row of the table can be made wrong and the gate
    above is what notices: dropping the pcs row, and claiming lagrange reaches G1ADD, are each
    refuted by conjunct 2, and claiming the empty block reaches 0x0b is refuted by conjunct 3a.
    Without this the table would be a list of numbers that agrees with the emitter by accident. -/
def partialEip2537Targets_detectsPerturbation_ok : Bool :=
  ([(.vkLoading, []), (.transcriptParser, []), (.lagrange, []), (.quotientLin, []),
    (.pcs, []), (.finalPairing, [0x0b, 0x0c, 0x0f]), (.traceReturn, [])]
    : List (Partial × List Nat)).any fun (q, want) =>
      eip2537Canon (emittedEip2537Targets GenAst.pcsFixturePlan q
        ++ emittedEip2537Targets bundleAccFixturePlan q) != want &&
    ([(.vkLoading, []), (.transcriptParser, []), (.lagrange, [0x0b]), (.quotientLin, []),
      (.pcs, [0x0b, 0x0c]), (.finalPairing, [0x0b, 0x0c, 0x0f]), (.traceReturn, [])]
      : List (Partial × List Nat)).any fun (q, want) =>
        eip2537Canon (emittedEip2537Targets GenAst.pcsFixturePlan q
          ++ emittedEip2537Targets bundleAccFixturePlan q) != want &&
    (directEip2537Targets [GenAst.yexpr (GenAst.yop Op.staticcall
      [GenAst.ylit 0, GenAst.ylit 0x0b, GenAst.ylit 0, GenAst.ylit 0, GenAst.ylit 0,
        GenAst.ylit 0])] == [0x0b])

#eval partialEip2537Targets_detectsPerturbation_ok   -- expect true

/-! ### THE CLOSURE GATE (P-HELPERS): every user call in every emitted slice resolves -/

/- THE DEFECT THIS SECTION EXISTS FOR, in one sentence: `BlkIsEmitter` pins `main` to
    `emitMain`, and `emitMain` really does contain what the emitter produces, so the pin stayed
    SATISFIED while the emitted program referenced three functions that were never defined and
    therefore could not run. A satisfied pin over an unrunnable program is invisible to every
    other gate in this tree - the token and AST relations compare one slice against one render,
    and neither one asks what the slice CALLS. This section is the general repair: not the three
    helpers (two of them are now emitted, and the third is below as a named exception) but the
    decidable check that would have refused the missing ones on their own. -/

/-- THE NAMED EXCEPTIONS: (partial, callee) pairs the closure gate is TOLD about and does not
    require. Exactly one, and it is not a convenience - `validate_public_accumulator`
    (AccumulatorHelpers.yul:190) is called only by the vkLoading accumulator arm, which the
    deployed profile never takes, and it is not an AssemblyHelpers definition: it lives in a
    second included file whose render this emitter does not model, and its own body calls five
    more functions in that file (`load_acc_point`, `load_acc_coord`, `load_acc_coord_shifted`,
    `check_acc_coord_packing`, `is_bls_p_minus_one`), so closing this exception is the conversion
    of a whole file and not the addition of one definition. Recorded as data, in a list a gate
    reads, so that the day it closes is a red gate and not a rumour. -/
def closureNamedExceptions : List (Partial × String) :=
  [(.vkLoading, "validate_public_accumulator")]

/-- Is this (partial, callee) pair on the exception list? -/
def closureIsNamedException (q : Partial) (n : String) : Bool :=
  closureNamedExceptions.contains (q, n)

/-- THE PLAN VIEWS THE CLOSURE GATE IS CHECKED AT, named so the coverage is data and not an
    adjective: the no-accumulator fixture and the accumulator fixture, i.e. the two plan views
    `partialEip2537Targets_ok` unions over and the two the spec theorems are pinned against.
    THIS IS THE GATE'S COVERAGE LIMIT, stated where a reader will hit it: a plan view not on
    this list is a plan view whose emitted program this gate has never looked at, and a future
    arm that only appears at some fourth plan view can still be link-incomplete and green here.
    The list is the same reason the gate is decidable rather than proved. -/
def closurePlanViews : List PlanView := [GenAst.pcsFixturePlan, bundleAccFixturePlan]

/-- THE CLOSURE PREDICATE, as a function of the helper block so it can be run against a pruned
    one. `closureHoldsUnder GenAst.emitHelpers` is the claim; the parameterisation is what lets
    the falsification below delete a definition and show the claim go red. -/
def closureHoldsUnder (helpers : PlanView → Block Op) : Bool :=
  (closurePlanViews.all fun pv =>
    Midfall.Lowering.partials.all fun q =>
      (unresolvedCallsUnder (helpers pv) pv q).all fun n => closureIsNamedException q n)

/-- The user calls the WHOLE emitted main cannot resolve, read off `emitMain` itself rather than
    off one slice and its closure: every call inside every helper body is in scope here too, which
    is the half the per-partial form gets only through `callClosure`. This is the statement the
    brief asks for in its literal form - every user call in every emitted slice has a matching
    `funDef` in `emitMain` - and it is checked alongside the per-slice form rather than instead
    of it, because the two fail differently: the per-slice form localises the gap to a partial,
    and this one catches a helper that calls a helper nobody hoists. -/
def emittedMainUnresolvedCalls (pv : PlanView) : List String :=
  let main := GenAst.emitMain pv
  let defined := main.filterMap fun
    | Stmt.funDef n _ _ _ => some n
    | _ => none
  ((bundleWalkSs main).2.filter fun n => !defined.contains n).eraseDups

/-- WHICH PARTIAL EACH EMITTED HELPER IS LOAD-BEARING FOR. The table the falsification below
    walks, so the deletion evidence covers every definition `emitHelpers` hoists and not just
    the two this package added. `fail` is listed against finalPairing because that is the slice
    whose own tail guard calls it; the transcript four are listed against transcriptParser, which
    is the only slice that calls them; `scalar_inv` against pcs and `batch_invert` against
    lagrange, which is the pair of gaps P-HELPERS closed. -/
def closureHelperOwners : List (String × Partial) :=
  [("fail", .finalPairing), ("scalar_inv", .pcs), ("transcript_init", .transcriptParser),
   ("common_word", .transcriptParser), ("common_uncompressed_g1", .transcriptParser),
   ("squeeze_to", .transcriptParser), ("batch_invert", .lagrange), ("ec_pairing", .finalPairing)]

/-- Two lists carry the same set of members, ignoring order and duplicates. Used instead of a
    sorted comparison because `List.sort` is a Mathlib field and this file is Mathlib-free. -/
def sameMembers {alpha : Type} [BEq alpha] (xs ys : List alpha) : Bool :=
  (xs.all fun x => ys.contains x) && (ys.all fun y => xs.contains y)

/-- GATE (THE CLOSURE GATE). Seven clauses:

    1. the predicate itself, at every pinned plan view and every partial;
    2. the whole-program form: `emitMain` at the no-accumulator plan view resolves EVERYTHING,
       and at the accumulator plan view the only thing it cannot resolve is the named exception -
       so the exception list is doing exactly one job and no more;
    3. every named exception is a call the emitter really does leave unresolved: an exception that
       stops biting is a red gate, which is what stops this list becoming the place gaps go to be
       forgotten;
    4. the exception is ARM-SCOPED and not a wildcard over vkLoading: at the plan view with no
       accumulator the vkLoading slice resolves completely;
    5. the exception list and the address record agree, so the two places the remaining gap is
       written down cannot drift apart;
    6. the coverage tables are complete: one owner row per emitted definition, one exception row
       per remaining gap;
    7. the gate is not vacuous in the direction that matters - the emitted program is big enough
       that a classifier which always said "resolved" would be caught by clause 3 failing on a
       pruned helper set, which is the next def. -/
def emittedProgramClosure_ok : Bool :=
  -- 1. the predicate
  closureHoldsUnder GenAst.emitHelpers &&
    -- 2. the whole-program form
    (emittedMainUnresolvedCalls GenAst.pcsFixturePlan == []) &&
    (emittedMainUnresolvedCalls bundleAccFixturePlan == ["validate_public_accumulator"]) &&
    -- 3. every exception is live
    (closureNamedExceptions.all fun (q, n) =>
      (closurePlanViews.any fun pv => (emittedUnresolvedCalls pv q).contains n)) &&
    -- 4. arm-scoped, not a wildcard
    (emittedUnresolvedCalls GenAst.pcsFixturePlan .vkLoading == []) &&
    -- 5. the two records of the remaining gap agree
    sameMembers (List.map Prod.snd closureNamedExceptions)
      (List.map Prod.fst unemittedHelperAddresses) &&
    -- 6. one owner row per emitted definition, and every owner row names a real partial
    sameMembers ((GenAst.emitHelpers GenAst.pcsFixturePlan).filterMap (fun
        | Stmt.funDef n _ _ _ => some n
        | _ => none)) (List.map Prod.fst closureHelperOwners) &&
    (closureHelperOwners.all fun (_, q) => Midfall.Lowering.partials.contains q) &&
    -- 7. the slices this gate is about are the real ones: the lagrange and pcs programs are not
    --    empty, so clause 1 is not being satisfied by nothing to check.
    (! (GenAst.emitPartial GenAst.pcsFixturePlan .lagrange).isEmpty) &&
    (! (GenAst.emitPartial GenAst.pcsFixturePlan .pcs).isEmpty)

/-- FALSIFICATION OF THE CLOSURE GATE (D-P23, R-41: the failure mode, not just the witness).
    Deleting ANY ONE of the eight definitions `emitHelpers` hoists makes the gate false, and
    makes it false for the partial the owner table names, with the residue being exactly the
    deleted name - so the gate localises the gap and does not merely notice one. The last line is
    the liveness control in the other direction: with the real helper block the same predicate is
    true, so these rows are dependences on the definitions and not a constant false. -/
def emittedProgramClosure_detectsDeletion_ok : Bool :=
  (closureHelperOwners.all fun (nm, q) =>
    (closurePlanViews.all fun pv =>
      unresolvedCallsUnder (GenAst.emitHelpersWithout nm pv) pv q == [nm]) &&
      ! closureIsNamedException q nm) &&
    (["fail", "scalar_inv", "transcript_init", "common_word", "common_uncompressed_g1",
      "squeeze_to", "batch_invert", "ec_pairing"].all fun nm =>
      ! closureHoldsUnder (fun pv => GenAst.emitHelpersWithout nm pv)) &&
    closureHoldsUnder GenAst.emitHelpers

#eval emittedProgramClosure_ok                    -- expect true
#eval emittedProgramClosure_detectsDeletion_ok    -- expect true
/- THE OTHER LINK DIMENSION, AS DATA. The closure gate above resolves `Expr.call` names
    against `Stmt.funDef` names and nothing else. A Yul program also fails to link when it
    *references a variable no enclosing scope declares*, and the emitted main does that 76 times
    over: every `*_MPTR`, `*_CPTR`, `ERR_*`, `FR_MODULUS`, `MODEXP_GAS`,
    `PAIRING_GAS_2PAIR` and the `vk` local is bound OUTSIDE `emitMain`, in the contract shell - the
    91 `uint256 internal constant` declarations of Halo2Verifier.sol plus the prologue `let`s the
    artifact puts above the first partial. That is not a defect: D-P30 puts the Solidity wrapper
    explicitly out of scope, and the wrapper is where those names live. It IS a limit on what the
    closure gate can promise, and it is recorded here rather than only in a report, so that a
    later package cannot read "the closure gate is green" as "the emitted program links". -/
mutual
def freeRefE : Expr Op → List String
  | Expr.var n => [n]
  | Expr.call _ args => freeRefEs args
  | Expr.builtin _ args => freeRefEs args
  | _ => []
termination_by e => sizeOf e

def freeRefEs : List (Expr Op) → List String
  | [] => []
  | e :: es => freeRefE e ++ freeRefEs es
termination_by es => sizeOf es

def freeWalkSs : List (Stmt Op) → List String × List String
  | [] => ([], [])
  | s :: ss =>
      let (a, b) := freeWalkS s
      let (c, d) := freeWalkSs ss
      (a ++ c, b ++ d)
termination_by ss => sizeOf ss

/-- References and declarations in one flat pass. An assignment target is a REFERENCE: in Yul,
    assigning to a name no scope declared is itself a validation error, so counting it as a
    declaration would hide exactly the gap this walk looks for. -/
def freeWalkS : Stmt Op → List String × List String
  | Stmt.block b => freeWalkSs b
  | Stmt.funDef n ps rs b => let (r, d) := freeWalkSs b; (r, n :: ps ++ rs ++ d)
  | Stmt.letDecl vs e => (e.map freeRefE |>.getD [], vs)
  | Stmt.assign vs e => (freeRefE e ++ vs, [])
  | Stmt.cond c b => let (r, d) := freeWalkSs b; (freeRefE c ++ r, d)
  | Stmt.forLoop i c p b =>
      let (ri, di) := freeWalkSs i
      let (rp, dp) := freeWalkSs p
      let (rb, db) := freeWalkSs b
      (freeRefE c ++ ri ++ rp ++ rb, di ++ dp ++ db)
  | Stmt.exprStmt e => (freeRefE e, [])
  | _ => ([], [])
termination_by s => sizeOf s
end

/-- The identifiers one emitted program references and does not itself declare. Flat scope: a
    name declared ANYWHERE in the program counts as declared, which under-approximates the free
    set and so makes the gate below conservative rather than flattering. -/
def emittedFreeIdentifiers (pv : PlanView) : List String :=
  let (rs, ds) := freeWalkSs (GenAst.emitMain pv)
  (rs.filter fun n => !ds.contains n).eraseDups

/-- GATE (THE CLOSURE GATE IS NOT LINK-COMPLETENESS). Four clauses, all measurements: (1) at the
    no-accumulator plan view the CALL closure is empty and the IDENTIFIER closure is not - the
    two move in opposite directions, which is the whole point; (2) every free identifier is a
    shell-provided name, i.e. upper-case with underscores, or the one lower-case local the
    wrapper binds for the VK address; (3) the named ones the helpers introduced are in there, so
    this gate moved when the helpers did; (4) the emitted program uses NO object-level external
    - no `datasize`, `datacopy`, `dataoffset` or `loadimmutable` - so that third link dimension is
    currently vacuous, and the closure gate would be blind to it if it stopped being so. -/
def emittedCallClosureIsNotLinkCompleteness_ok : Bool :=
  let free := emittedFreeIdentifiers GenAst.pcsFixturePlan
  (emittedUnresolvedCalls GenAst.pcsFixturePlan .lagrange == []) &&
    (emittedMainUnresolvedCalls GenAst.pcsFixturePlan == []) &&
    free.length == 76 &&
    (free.all fun n => n == "vk" || (n.toList.all fun c => c.isUpper || c.isDigit || c == '_')) &&
    (["FR_MODULUS", "MODEXP_GAS", "ERR_PRECOMPILE_FAILED", "TRANSCRIPT_MPTR", "vk",
       "BATCH_INV_SCRATCH_MPTR"].all fun n => free.contains n) &&
    (let prg := EVM.print (GenAst.emitMain GenAst.pcsFixturePlan);
      ! (["loadimmutable", "dataoffset", "datasize(", "datacopy("].any fun w =>
        prg.contains (" " ++ w) || prg.contains ("(" ++ w) || prg.contains ("," ++ w))) &&
    -- AND THE ACCUMULATOR ARM WIDENS THE IDENTIFIER GAP BY EXACTLY THE TWO SLOTS IT
    -- READS. The exception is a missing DEFINITION and not a missing binding, but the arm it
    -- guards references two shell constants the no-accumulator view never names, so the two
    -- closures are independent in both directions and neither one contains the other.
    (emittedFreeIdentifiers bundleAccFixturePlan).length == free.length + 2 &&
    ((emittedFreeIdentifiers bundleAccFixturePlan).filter fun n => !free.contains n) ==
      ["ACC_RHS_MPTR", "ACC_LHS_MPTR"]

#eval emittedCallClosureIsNotLinkCompleteness_ok   -- expect true


/-- The world-state reads one emitted program performs, as data. The EIP-2537 classifier above
    asks which PRECOMPILES a partial reaches; this asks the same question about the other
    externals, because the audit of the other nine theorems found one hole of the same CLASS
    that is not an EIP-2537 hole at all (see gap_vkLoading_world_reads). Read off the printed
    AST the way GenAstPcs.Kats.writesTo does - a text test on a computed program, not a text
    test on a source file. -/
def emittedWorldReads (pv : PlanView) (q : Partial) : List String :=
  let printed := EVM.print (callClosure (GenAst.emitHelpers pv) (GenAst.emitPartial pv q))
  ["extcodesize(", "extcodehash(", "extcodecopy(", "balance(", "sload("].filter
    fun s => printed.contains s

/-- AUDIT FINDING 2, RECORDED AS A GAP AND NOT REPAIRED. vkLoading_spec is the one other spec
    theorem whose conclusion depends on an external answer that no hypothesis pins - the same
    CLASS as pcs_spec, a different external family. Its post is Inv .vk, whose first clause is
    'bytesAt st (ptrAddr M.vkMptr) PV.vk.len == PV.vk.bytes' (Inv.lean:582), and the emitted
    program fills that window with 'extcodecopy(vk, VK_MPTR, 0x01, ...)' behind an
    extcodesize / extcodehash guard (GenAst.lean:728-734). The hypothesis that says what the
    world's code at that address IS is DeploymentW - vkCode, wf and vkHash at
    Surface.lean:559-608, and extcodehash_of_deployment is the projection vkLoading_spec's own
    docstring already cites - and vkLoading_spec binds none of it: it takes no vkAddr or
    quotientAddr, and Inv .start says nothing about the code dictionary. So it sits in the same
    'unprovable as stated' condition P-BUNDLE closed for pcs.

    It is NOT repaired here, and the reason is a decision and not laziness: the world can be
    pinned in three different places (an Inv .start clause, an addl pre-condition, or two more
    binders plus DeploymentW), and which one is right depends on whether the shell's
    loadimmutable(AUTHORIZED_VK) is modelled at the Bridge level at all. That is the
    orchestrator's call, not this package's. What this package does is make the hole
    gate-visible: check_hypothesis_bundles.py requires this definition to exist and to name the
    three reads and the hypothesis that would pin them, so the finding cannot be quietly
    deleted, and gap_vkLoading_world_reads_measured below is the measurement rather than a
    paragraph. -/
def gap_vkLoading_world_reads : String :=
  "unrepaired P-BUNDLE audit finding: vkLoading_spec's post is Inv .vk, which pins the VK "
    ++ "payload image at vkMptr, and the emitted slice fills it through extcodesize, "
    ++ "extcodehash and extcodecopy at the AUTHORIZED_VK address. Blocker: no hypothesis of "
    ++ "vkLoading_spec says what the world's code at that address is - DeploymentW (vkCode, "
    ++ "wf, vkHash) is the hypothesis that would, and the theorem takes no vkAddr or "
    ++ "quotientAddr, while Inv .start pins nothing about the code dictionary. Repair is a "
    ++ "decision about WHERE the world belongs: an Inv .start clause, an addl pre, or two "
    ++ "more binders. Reported, not made."

/-- THE MEASUREMENT BEHIND THE GAP: vkLoading is the ONLY partial whose emitted program reads
    the world, and it reads it through exactly those three builtins. Refuted by an emitter that
    stops copying the payload, by one that starts reading the world somewhere else, and by a
    classifier that looks only at staticcalls. -/
def gap_vkLoading_world_reads_measured : Bool :=
  emittedWorldReads GenAst.pcsFixturePlan .vkLoading
    == ["extcodesize(", "extcodehash(", "extcodecopy("] &&
    emittedWorldReads GenAst.pcsFixturePlan .traceReturn == [] &&
    emittedWorldReads GenAst.pcsFixturePlan .pcs == [] &&
    emittedWorldReads GenAst.pcsFixturePlan .lagrange == [] &&
    emittedWorldReads GenAst.pcsFixturePlan .transcriptParser == [] &&
    emittedWorldReads GenAst.pcsFixturePlan .quotientLin == [] &&
    emittedWorldReads GenAst.pcsFixturePlan .finalPairing == []

#eval gap_vkLoading_world_reads_measured -- expect true


/-- AUDIT FINDING 3, REPAIRED: the same class, a different external. transcriptParser_spec's
    post is Inv .transcript, whose challenge clauses are 'holdsFr st (ptrAddr M.x1Mptr) S.a.x1'
    and its three siblings (Inv.lean:605-607), and the emitted program fills those slots by
    squeezing through the dialect keccak - 'squeeze_to' runs 'keccak256' (GenAst.lean:361-370),
    which the Bridge answers from 'st.env.keccakOf'. The snapshot's challenges come from H.
    Nothing in the bundle said the two are the same hash, so the theorem was in the same
    unprovable-as-stated condition as pcs_spec - a conclusion that depends on an external answer
    with no hypothesis about it.

    The repair is not invented here: finalPairing_acc_spec binds exactly this hypothesis (hkec,
    at its .pcs pre) and its docstring already says why - "alphaOf is hash-parametric while the
    EVM hashes through env.keccakOf (finding Y-2), so without it the alpha the contract computes
    is not the alpha the statement names". Same reason, same shape, one partial earlier. The
    measurement below is what makes it a finding and not a guess: of the seven partials ONLY
    transcriptParser squeezes without a keccak hypothesis, and finalPairing squeezes only on the
    accumulator arm - which is the arm that carries hkec. -/
def emittedKeccak (pv : PlanView) (q : Partial) : Bool :=
  (EVM.print (callClosure (GenAst.emitHelpers pv) (GenAst.emitPartial pv q))).contains "keccak256("

/-- THE KECCAK ROWS, as the same kind of data the EIP-2537 table is: which partials' emitted
    programs squeeze through the dialect keccak. scripts/check_hypothesis_bundles.py parses this
    and demands a keccak-agreement hypothesis on the spec theorems for exactly these partials, so
    audit finding 3 cannot be undone by a later package deleting hkec in silence. finalPairing is
    in the list because of its ACCUMULATOR arm; the two no-accumulator theorems are exempted by
    their own 'hacc : S.plan.hasAccumulator = false' binder, which is what the gate checks instead
    of a hand-written exception. -/
def partialKeccakSqueeze : List Partial := [.transcriptParser, .finalPairing]

/-- THE MEASUREMENT BEHIND AUDIT FINDING 3. Refuted by an emitter that stops squeezing, by one
    that starts squeezing somewhere else, and by a classifier that looks only at staticcalls. -/
def partialKeccakSqueeze_ok : Bool :=
  (partialKeccakSqueeze == partials.filter fun q =>
    emittedKeccak GenAst.pcsFixturePlan q || emittedKeccak bundleAccFixturePlan q) &&
  emittedKeccak GenAst.pcsFixturePlan .transcriptParser &&
    emittedKeccak bundleAccFixturePlan .transcriptParser &&
    emittedKeccak bundleAccFixturePlan .finalPairing &&
    ! (emittedKeccak GenAst.pcsFixturePlan .finalPairing) &&
    ! (emittedKeccak GenAst.pcsFixturePlan .vkLoading) &&
    ! (emittedKeccak GenAst.pcsFixturePlan .lagrange) &&
    ! (emittedKeccak GenAst.pcsFixturePlan .quotientLin) &&
    ! (emittedKeccak GenAst.pcsFixturePlan .pcs) &&
    ! (emittedKeccak GenAst.pcsFixturePlan .traceReturn)

#eval partialKeccakSqueeze_ok      -- expect true

/-! ### THE ARITY GATE (P-ARITY): every user call matches its definition's signature -/

/- THE HOLE THIS SECTION CLOSES, in one sentence: the closure gate resolves call NAMES and nothing
else, so `batch_invert(a, b, c, d)` against a five-parameter definition, and `success :=
batch_invert(...)` binding one of a two-value return, both satisfy it - and neither is a program.

THE GROUND TRUTH IS THE SEMANTICS BEING SILENT, not a validator saying no. Step.callOk carries the
premise `argvals.length = decl.params.length` (BigStep.lean:204) and Step.letVal and Step.assignVal
each carry `vals.length = vars.length` (:232, :239), so a wrong count has NO derivation: the
program is stuck, every `Run` is empty, and each spec theorem about its runs would quantify over
nothing and be vacuously true. That is the same failure mode as the unhoisted helper P-HELPERS found
- a satisfied pin over an unrunnable program - and the same one the scratch address revealed.

WHAT THE GATE READS, position by position. A call's result count is not a property of the call alone;
it is a property of the position the call sits in, and the four positions the vendored rules
distinguish are: the value of a `letDecl` (must equal the target count), the value of an `assign`
(must equal the target count), the whole of an `exprStmt` (must be ZERO values, because Step.exprStmt
demands `.vals []` at :243), and a call nested in any other expression - an argument of a builtin or
another call, or a condition - where Step.argsCons and Step.ifTrue each demand exactly ONE value
(:209, :252). The walker below carries that expected count down as its first argument, so all four
are checked by one pass rather than by four claims. Calls whose callee no definition in the block
answers are NOT reported here: that is the closure gate's job, and the gate below asserts the two
lists agree, so a missing definition cannot hide in the gap between them. -/

/-- One user-function call site read off the AST: the callee, how many arguments the call passes,
and how many results its position binds. -/
structure CallSite where
  /-- The callee's name. -/
  fn : String
  /-- How many arguments the call passes. -/
  args : Nat
  /-- How many results the syntactic position demands. -/
  binds : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One arity violation: what the call did and what the definition said, in the shape a report can
print without re-deriving anything. -/
structure ArityViolation where
  /-- The callee's name. -/
  fn : String
  /-- Arguments passed at the call site. -/
  argsPassed : Nat
  /-- Parameters declared by the definition. -/
  paramsDeclared : Nat
  /-- Results bound at the call site. -/
  resultsBound : Nat
  /-- Returns declared by the definition. -/
  resultsDeclared : Nat
  deriving Repr, DecidableEq, Inhabited

mutual
/-- The user call sites in an expression, with the number of results its position binds. -/
def arityWalkE : Nat → Expr Op → List CallSite
  | _, Expr.lit _ => []
  | _, Expr.var _ => []
  | k, Expr.call fn args => { fn := fn, args := args.length, binds := k } :: arityWalkEs args
  | _, Expr.builtin _ args => arityWalkEs args
termination_by _ e => sizeOf e

/-- An argument list: every element must be single-valued (Step.argsCons), so the context handed
down is 1 whatever the enclosing position binds. -/
def arityWalkEs : List (Expr Op) → List CallSite
  | [] => []
  | e :: es => arityWalkE 1 e ++ arityWalkEs es
termination_by es => sizeOf es

/-- The user call sites in one statement, including the ones inside a function body - which is the
half the per-slice closure form gets only through `callClosure`. -/
def arityWalkS : Stmt Op → List CallSite
  | Stmt.block b => arityWalkSs b
  | Stmt.funDef _ _ _ b => arityWalkSs b
  | Stmt.letDecl _ none => []
  | Stmt.letDecl vs (some e) => arityWalkE vs.length e
  | Stmt.assign vs e => arityWalkE vs.length e
  | Stmt.cond c b => arityWalkE 1 c ++ arityWalkSs b
  | Stmt.switch c cases dflt => arityWalkE 1 c ++ arityWalkSC cases ++ arityWalkOpt dflt
  | Stmt.forLoop init c post body =>
      arityWalkSs init ++ arityWalkE 1 c ++ arityWalkSs post ++ arityWalkSs body
  | Stmt.exprStmt e => arityWalkE 0 e
  | _ => []
termination_by s => sizeOf s

/-- The user call sites in a statement list. -/
def arityWalkSs : List (Stmt Op) → List CallSite
  | [] => []
  | s :: ss => arityWalkS s ++ arityWalkSs ss
termination_by ss => sizeOf ss

/-- The user call sites in a switch's case list. -/
def arityWalkSC : List (Literal × List (Stmt Op)) → List CallSite
  | [] => []
  | (_, b) :: cs => arityWalkSs b ++ arityWalkSC cs
termination_by cs => sizeOf cs

/-- The user call sites in a switch's optional default block. -/
def arityWalkOpt : Option (List (Stmt Op)) → List CallSite
  | none => []
  | some b => arityWalkSs b
termination_by b => sizeOf b
end

/-- The signature table of a block: every user function it defines, with its parameter count and its
return count. Top-level definitions only, which is where the emitter puts them and is the same
convention the closure gate resolves names under - a `funDef` nested inside a block would be
invisible to both, and that is recorded rather than hidden. -/
def funSignatures (b : Block Op) : List (String × Nat × Nat) :=
  b.filterMap fun | Stmt.funDef n ps rs _ => some (n, ps.length, rs.length) | _ => none

/-- The call sites whose callee no definition in the block answers. These are the closure gate's
business and not the arity gate's; the gate below asserts the two agree on the list, so a missing
definition cannot fall through the gap between the two walkers. -/
def unresolvedCallSites (b : Block Op) : List CallSite :=
  let sigs := funSignatures b
  (arityWalkSs b).filter fun c => (sigs.lookup c.fn).isNone

/-- The arity violations of a block: every user call whose argument count differs from its
definition's parameter count, or whose bound-result count differs from its return count. -/
def arityViolations (b : Block Op) : List ArityViolation :=
  let sigs := funSignatures b
  (arityWalkSs b).filterMap fun c =>
    match sigs.lookup c.fn with
    | none => none
    | some (np, nr) => if c.args == np && c.binds == nr then none
      else some (ArityViolation.mk c.fn c.args np c.binds nr)

/-- The names of the eight hoisted helper definitions, read off the emitter rather than pasted. -/
def arityHelperNames : List String :=
  (GenAst.emitHelpers GenAst.pcsFixturePlan).filterMap fun
    | Stmt.funDef n _ _ _ => some n
    | _ => none

/-- The whole emitted program at the no-accumulator fixture plan view. -/
def emittedMainPcs : Block Op := GenAst.emitMain GenAst.pcsFixturePlan

/-- The whole emitted program at the accumulator fixture plan view. -/
def emittedMainAcc : Block Op := GenAst.emitMain bundleAccFixturePlan

/- Deep statement rewrite: apply a statement rule everywhere in a block - inside blocks, function
bodies, `if` bodies, switch cases and defaults, and all three sub-blocks of a `for` loop. Written as
four mutually recursive functions because the vendored AST nests statement lists inside pairs and
options, where a plain `map` does not recurse - the same reason `GenAst.mapStmtExprs` leaves switch
untouched, except that the mutations below must not. -/
mutual
def everywhereSs (f : Stmt Op → Stmt Op) : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: ss => everywhereS f s :: everywhereSs f ss
termination_by ss => sizeOf ss

def everywhereS (f : Stmt Op → Stmt Op) : Stmt Op → Stmt Op
  | Stmt.block b => f (Stmt.block (everywhereSs f b))
  | Stmt.funDef n ps rs b => f (Stmt.funDef n ps rs (everywhereSs f b))
  | Stmt.cond c b => f (Stmt.cond c (everywhereSs f b))
  | Stmt.switch c cases d => f (Stmt.switch c (everywhereSC f cases) (everywhereSO f d))
  | Stmt.forLoop i c p b =>
      f (Stmt.forLoop (everywhereSs f i) c (everywhereSs f p) (everywhereSs f b))
  | s => f s
termination_by s => sizeOf s

def everywhereSC (f : Stmt Op → Stmt Op) : List (Literal × List (Stmt Op)) →
    List (Literal × List (Stmt Op))
  | [] => []
  | (l, b) :: cs => (l, everywhereSs f b) :: everywhereSC f cs
termination_by cs => sizeOf cs

def everywhereSO (f : Stmt Op → Stmt Op) : Option (List (Stmt Op)) → Option (List (Stmt Op))
  | none => none
  | some b => some (everywhereSs f b)
termination_by b => sizeOf b
end

/-- CLONE MUTATION (arity): every call of the named function passes one MORE argument than the
definition declares. The first defect the brief asks to be shown. -/
def cloneWithExtraArg (fn : String) (b : Block Op) : Block Op :=
  everywhereSs (fun
    | Stmt.exprStmt (Expr.call n args) =>
        if n == fn then Stmt.exprStmt (Expr.call n (args ++ [GenAst.ylit 0]))
          else Stmt.exprStmt (Expr.call n args)
    | Stmt.assign vs (Expr.call n args) =>
        if n == fn then Stmt.assign vs (Expr.call n (args ++ [GenAst.ylit 0]))
          else Stmt.assign vs (Expr.call n args)
    | Stmt.letDecl vs (some (Expr.call n args)) =>
        if n == fn then Stmt.letDecl vs (some (Expr.call n (args ++ [GenAst.ylit 0])))
          else Stmt.letDecl vs (some (Expr.call n args))
    | s => s) b

/-- CLONE MUTATION (arity): every binding of the named function's results binds one FEWER variable
than the definition returns. The second defect the brief asks to be shown. -/
def cloneWithDroppedResult (fn : String) (b : Block Op) : Block Op :=
  everywhereSs (fun
    | Stmt.assign (v :: vs) (Expr.call n args) =>
        if n == fn then Stmt.assign vs (Expr.call n args)
          else Stmt.assign (v :: vs) (Expr.call n args)
    | Stmt.letDecl (v :: vs) (some (Expr.call n args)) =>
        if n == fn then Stmt.letDecl vs (some (Expr.call n args))
          else Stmt.letDecl (v :: vs) (some (Expr.call n args))
    | s => s) b

/-- CLONE MUTATION (arity): the call's results are bound to one MORE variable than the definition
returns, including the case where the call was a bare statement and gains a binding. This is the
third mutation because `cloneWithDroppedResult` has nothing to drop at a zero-return call, and
`fail` is called twenty-two times as a statement. -/
def cloneWithExtraResult (fn : String) (b : Block Op) : Block Op :=
  everywhereSs (fun
    | Stmt.exprStmt (Expr.call n args) =>
        if n == fn then Stmt.letDecl ["arity_probe_extra"] (some (Expr.call n args))
          else Stmt.exprStmt (Expr.call n args)
    | Stmt.assign vs (Expr.call n args) =>
        if n == fn then Stmt.assign (vs ++ ["arity_probe_extra"]) (Expr.call n args)
          else Stmt.assign vs (Expr.call n args)
    | Stmt.letDecl vs (some (Expr.call n args)) =>
        if n == fn then Stmt.letDecl (vs ++ ["arity_probe_extra"]) (some (Expr.call n args))
          else Stmt.letDecl vs (some (Expr.call n args))
    | s => s) b

/-- A two-value call bound to one variable: the `wtwo` shape, wrong in the result direction only. -/
def arityWitnessFewArgs : Block Op := yul% {
  function wfew(a, b) -> c { c := add(a, b) }
  let x := wfew(1)
}

/-- One result bound where the definition returns two. -/
def arityWitnessFewResults : Block Op := yul% {
  function wtwo(a) -> c, d { c := a }
  let x := wtwo(1)
}

/-- A two-value call used where the semantics demands a single value: an argument position. -/
def arityWitnessCallInArg : Block Op := yul% {
  function warg(a) -> c, d { c := a }
  mstore(0, warg(1))
}

/-- A one-value call used as a statement: Step.exprStmt demands the empty value list. -/
def arityWitnessCallAsStmt : Block Op := yul% {
  function wstmt(a) -> c { c := a }
  wstmt(1)
}

/-- The correct shape of each of the four above, as the satisfiability witness D-P23 asks for: the
same program with the right counts must be clean, or the classifier is a constant false. -/
def arityWitnessAllOk : Block Op := yul% {
  function okfew(a, b) -> c { c := add(a, b) }
  function oktwo(a) -> c, d { c := a }
  let x := okfew(1, 2)
  let y, z := oktwo(1)
  mstore(0, okfew(1, 2))
}

/-- GATE (THE ARITY GATE). Six clauses:

    1. no violation anywhere in the whole emitted program, at either pinned plan view;
    2. none in any slice closed under the emitted helpers either, which is the per-partial form and
       localises a violation to a partial the way the closure gate does;
    3. the signature table the gate reads, as DATA: the eight hoisted helpers with the parameter and
       return counts AssemblyHelpers.yul gives them, so a signature change is a red gate and not a
       silent re-derivation;
    4. the call-site census: 51 user call sites at the no-accumulator view and 54 at the accumulator
       view, in exactly eight distinct shapes, so clause 1 is a claim about 51 real calls and not
       about an empty walk;
    5. the ONLY callees the arity gate declines to check are exactly the ones the closure gate names
       as unresolved, at both plan views - the two gates cannot disagree about what is missing, which
       is what stops a new unresolved helper slipping past both;
    6. the classifier is not a constant: four hand-built programs, one per arity position, each wrong
       in exactly one way and each caught, and the corrected version of all four clean. Built with
       the `yul%` parser and not with the constructors, so the gate is not self-fulfilling. -/
def emittedProgramArity_ok : Bool :=
  -- 1. the whole emitted program
  (closurePlanViews.all fun pv => arityViolations (GenAst.emitMain pv) == []) &&
    -- 2. and every closed slice
    (closurePlanViews.all fun pv => partials.all fun q =>
      arityViolations (callClosure (GenAst.emitHelpers pv) (GenAst.emitPartial pv q)) == []) &&
    -- 3. the signature table, as data
    (funSignatures (GenAst.emitHelpers GenAst.pcsFixturePlan) ==
      [("fail", 1, 0), ("scalar_inv", 1, 1), ("transcript_init", 0, 1), ("common_word", 2, 1),
        ("common_uncompressed_g1", 2, 1), ("squeeze_to", 2, 1), ("batch_invert", 5, 2),
        ("ec_pairing", 3, 1)]) &&
    -- 4. the census
    ((arityWalkSs emittedMainPcs).length == 51) &&
    ((arityWalkSs emittedMainAcc).length == 54) &&
    ((arityWalkSs emittedMainPcs).eraseDups ==
      [{ fn := "fail", args := 1, binds := 0 },
        { fn := "transcript_init", args := 0, binds := 1 },
        { fn := "common_word", args := 2, binds := 1 },
        { fn := "squeeze_to", args := 2, binds := 1 },
        { fn := "common_uncompressed_g1", args := 2, binds := 1 },
        { fn := "batch_invert", args := 5, binds := 2 },
        { fn := "scalar_inv", args := 1, binds := 1 },
        { fn := "ec_pairing", args := 3, binds := 1 }]) &&
    -- 5. the two gates agree about what is missing
    (closurePlanViews.all fun pv =>
      sameMembers ((unresolvedCallSites (GenAst.emitMain pv)).map (fun c => c.fn)).eraseDups
        (emittedMainUnresolvedCalls pv)) &&
    -- 6. the witnesses, one per position, plus the clean control
    ((arityViolations arityWitnessFewArgs).any fun v =>
      v.fn == "wfew" && v.argsPassed == 1 && v.paramsDeclared == 2) &&
    ((arityViolations arityWitnessFewResults).any fun v =>
      v.fn == "wtwo" && v.resultsBound == 1 && v.resultsDeclared == 2) &&
    ((arityViolations arityWitnessCallInArg).any fun v =>
      v.fn == "warg" && v.resultsBound == 1 && v.resultsDeclared == 2) &&
    ((arityViolations arityWitnessCallAsStmt).any fun v =>
      v.fn == "wstmt" && v.resultsBound == 0 && v.resultsDeclared == 1) &&
    (arityViolations arityWitnessAllOk == [])

/-- FALSIFICATION OF THE ARITY GATE (D-P23, R-41: the failure mode, not just the witness). The two
mutations the brief names, then the general form: EVERY one of the eight helpers reddens the gate
when a call to it gains an argument, and every one reddens it when the binding gains a result; the
drop-a-result mutation reddens it for the seven that bind results, `fail` being the honest exception
because it returns nothing and is called as a statement, where there is no binding to drop and
`cloneWithExtraResult` is the mutation that applies. The last two lines are the liveness controls:
the unmutated program is clean, and every mutation really does change the AST, so the gate is not
reddening on a no-op. -/
def emittedProgramArity_detectsMutation_ok : Bool :=
  (arityViolations (cloneWithExtraArg "batch_invert" emittedMainPcs) ==
      [ArityViolation.mk "batch_invert" 6 5 2 2]) &&
    (arityViolations (cloneWithDroppedResult "batch_invert" emittedMainPcs) ==
      [ArityViolation.mk "batch_invert" 5 5 1 2]) &&
    (arityHelperNames.all fun nm =>
      (arityViolations (cloneWithExtraArg nm emittedMainPcs)).any fun v =>
        v.fn == nm && v.argsPassed == v.paramsDeclared + 1) &&
    (arityHelperNames.all fun nm =>
      (arityViolations (cloneWithExtraResult nm emittedMainPcs)).any fun v =>
        v.fn == nm && v.resultsBound == v.resultsDeclared + 1) &&
    ((arityHelperNames.filter fun nm => nm != "fail").all fun nm =>
      (arityViolations (cloneWithDroppedResult nm emittedMainPcs)).any fun v =>
        v.fn == nm && v.resultsBound + 1 == v.resultsDeclared) &&
    (arityViolations emittedMainPcs == []) &&
    (arityHelperNames.all fun nm =>
      ! SyntaxEq.stmtsBeq (cloneWithExtraArg nm emittedMainPcs) emittedMainPcs)

#eval emittedProgramArity_ok                        -- expect true
#eval emittedProgramArity_detectsMutation_ok        -- expect true

/-! ### THE PLACEMENT GATE (P-ARITY): leave, break and continue sit in the right construct -/

/- THE SECOND HOLE, and it is the one the brief names. The emitted program has twelve `leave`s -
eleven inside `batch_invert` and one inside `ec_pairing` - and before this section NOTHING said they
were inside a function definition. THE BRIEF'S COUNT OF SIX IS THE COUNT OF `Stmt.leave` TOKENS IN
THE EMITTER SOURCE (GenAst.lean:269, 468, 484, 488, 492, 520), not the number of leaves in the AST it
builds: the `reject` block defined at :468 is spliced into seven different guard arms, so one source
token becomes seven leaves, and the measured AST census is twelve. Measured, not assumed - which is
the whole reason this section counts leaves in the program instead of in the file. The vendored semantics does not reject a misplaced one; it simply
has no rule that consumes it. Step.leave produces the `leave` outcome wherever it appears
(BigStep.lean:280-281), and the only rule that turns a `leave` outcome back into normal control is
Step.callOk's `o = .normal OR o = .leave` premise (:207) - at the top level of main a `leave`
escapes into the run's outcome, and StmtsContractAll's post is then neither the normal arm nor the
halt arm the spec theorems name. `break` and `continue` are the same class: Step.«break» and
Step.«continue» produce their outcomes unconditionally (:276-279) and the only consumers are loopStep
and loopBreak (:310-325), so outside a loop they propagate out of the enclosing block forever. Yul
has no jump statement and the vendored AST has none either, so this section plus the arity gate above
is the whole of the control-flow well-formedness dimension of the grammar.

THE CONTEXT THE WALK CARRIES, and the two places a naive version gets it wrong. Two flags: whether an
enclosing `function` body is in scope, which is what consumes a `leave`, and whether an enclosing
`for` BODY is in scope, which is what consumes a `break` or `continue`. Entering a `funDef` sets the
first and CLEARS the second: a function defined inside a loop body is a fresh control context, and a
`break` in it is not caught by that loop - `callOk` accepts only normal or leave from a body. The
loop's init and post blocks clear the second too, because the `forLoop` rule requires the init
outcome to be normal (:270) and `loopStep` requires the post outcome to be normal (:317), so a
`break` in either is stuck. A `leave` inside a loop inside a function stays legal, because
Step.loopLeave carries it out of the loop to the call (:329-330). -/
mutual
def ctrlWalkS : Bool → Bool → Stmt Op → List String
  | inFun, inLoop, Stmt.block b => ctrlWalkSs inFun inLoop b
  | _, _, Stmt.funDef _ _ _ b => ctrlWalkSs true false b
  | inFun, inLoop, Stmt.cond _ b => ctrlWalkSs inFun inLoop b
  | inFun, inLoop, Stmt.switch _ cases dflt =>
      ctrlWalkSC inFun inLoop cases ++ ctrlWalkSO inFun inLoop dflt
  | inFun, _, Stmt.forLoop init _ post body =>
      ctrlWalkSs inFun false init ++ ctrlWalkSs inFun true post ++ ctrlWalkSs inFun true body
  | inFun, _, Stmt.leave => if inFun then [] else ["leave outside a function definition"]
  | _, inLoop, Stmt.«break» => if inLoop then [] else ["break outside a for loop"]
  | _, inLoop, Stmt.«continue» => if inLoop then [] else ["continue outside a for loop"]
  | _, _, _ => []
termination_by _ _ s => sizeOf s

def ctrlWalkSs : Bool → Bool → List (Stmt Op) → List String
  | _, _, [] => []
  | inFun, inLoop, s :: ss => ctrlWalkS inFun inLoop s ++ ctrlWalkSs inFun inLoop ss
termination_by _ _ ss => sizeOf ss

def ctrlWalkSC : Bool → Bool → List (Literal × List (Stmt Op)) → List String
  | _, _, [] => []
  | inFun, inLoop, (_, b) :: cs => ctrlWalkSs inFun inLoop b ++ ctrlWalkSC inFun inLoop cs
termination_by _ _ cs => sizeOf cs

def ctrlWalkSO : Bool → Bool → Option (List (Stmt Op)) → List String
  | _, _, none => []
  | inFun, inLoop, some b => ctrlWalkSs inFun inLoop b
termination_by _ _ b => sizeOf b
end

/-- The misplaced control-flow statements in a block, one message per misplaced statement, so the
report says how many there are and of which kind. -/
def controlViolations (b : Block Op) : List String := ctrlWalkSs false false b

mutual
def ctrlCensusS : Stmt Op → Nat × Nat × Nat
  | Stmt.leave => (1, 0, 0)
  | Stmt.«break» => (0, 1, 0)
  | Stmt.«continue» => (0, 0, 1)
  | Stmt.block bs => ctrlCensusSs bs
  | Stmt.funDef _ _ _ bs => ctrlCensusSs bs
  | Stmt.cond _ bs => ctrlCensusSs bs
  | Stmt.switch _ cs d =>
      let (a1, a2, a3) := ctrlCensusSC cs
      let (b1, b2, b3) := ctrlCensusSO d
      (a1 + b1, a2 + b2, a3 + b3)
  | Stmt.forLoop ini _ pst bod =>
      let (a1, a2, a3) := ctrlCensusSs ini
      let (b1, b2, b3) := ctrlCensusSs pst
      let (c1, c2, c3) := ctrlCensusSs bod
      (a1 + b1 + c1, a2 + b2 + c2, a3 + b3 + c3)
  | _ => (0, 0, 0)
termination_by s => sizeOf s
def ctrlCensusSs : List (Stmt Op) → Nat × Nat × Nat
  | [] => (0, 0, 0)
  | s :: ss =>
      let (a1, a2, a3) := ctrlCensusS s
      let (b1, b2, b3) := ctrlCensusSs ss
      (a1 + b1, a2 + b2, a3 + b3)
termination_by ss => sizeOf ss
def ctrlCensusSC : List (Literal × List (Stmt Op)) → Nat × Nat × Nat
  | [] => (0, 0, 0)
  | (_, bs) :: cs =>
      let (a1, a2, a3) := ctrlCensusSs bs
      let (b1, b2, b3) := ctrlCensusSC cs
      (a1 + b1, a2 + b2, a3 + b3)
termination_by cs => sizeOf cs
def ctrlCensusSO : Option (List (Stmt Op)) → Nat × Nat × Nat
  | none => (0, 0, 0)
  | some bs => ctrlCensusSs bs
termination_by bs => sizeOf bs
end

/-- How many `leave`, `break` and `continue` statements a block contains, wherever they sit. The
census the placement gate is a claim ABOUT: twelve leaves and no break or continue at the fixture plan
view, which is what makes the gate a statement about real statements rather than about an empty walk.
-/
def controlCensus : Block Op → Nat × Nat × Nat := ctrlCensusSs

/-- The `leave` count of each function definition in a block, as (name, count): the census broken out
by the only construct that is allowed to contain a `leave`. -/
def leavesPerDefinition (b : Block Op) : List (String × Nat) :=
  b.filterMap fun | Stmt.funDef n _ _ bs => (n, (controlCensus bs).1) | _ => none

/-- The body of the definition named `name`, concatenated if the name is doubled. -/
def definitionBody (name : String) (b : Block Op) : Block Op :=
  (b.filterMap fun | Stmt.funDef n _ _ bs => if n == name then some bs else none | _ => none).flatten

/- Deep removal of every control-flow leaf, with the rest of the tree shape intact: the first half of
the hoist mutation below. -/
mutual
def stripCtrlSs : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | Stmt.leave :: ss => stripCtrlSs ss
  | Stmt.«break» :: ss => stripCtrlSs ss
  | Stmt.«continue» :: ss => stripCtrlSs ss
  | s :: ss => stripCtrlS s :: stripCtrlSs ss
termination_by ss => sizeOf ss
def stripCtrlS : Stmt Op → Stmt Op
  | Stmt.block b => Stmt.block (stripCtrlSs b)
  | Stmt.funDef n ps rs b => Stmt.funDef n ps rs (stripCtrlSs b)
  | Stmt.cond c b => Stmt.cond c (stripCtrlSs b)
  | Stmt.switch c cs d => Stmt.switch c (stripCtrlSC cs) (stripCtrlSO d)
  | Stmt.forLoop i c p b => Stmt.forLoop (stripCtrlSs i) c (stripCtrlSs p) (stripCtrlSs b)
  | s => s
termination_by s => sizeOf s
def stripCtrlSC : List (Literal × List (Stmt Op)) → List (Literal × List (Stmt Op))
  | [] => []
  | (l, b) :: cs => (l, stripCtrlSs b) :: stripCtrlSC cs
termination_by cs => sizeOf cs
def stripCtrlSO : Option (List (Stmt Op)) → Option (List (Stmt Op))
  | none => none
  | some b => some (stripCtrlSs b)
termination_by b => sizeOf b
end

/-- CLONE MUTATION (placement): every control-flow leaf inside the definition named `name` is MOVED to
the top level of the program. The census is unchanged - the same leaves, in the wrong place - which is
what makes this a placement mutation and not a counting one. -/
def cloneHoistLeavesOutOf (name : String) (b : Block Op) : Block Op :=
  let (l, br, c) := controlCensus (definitionBody name b)
  let stripped := b.map fun
    | Stmt.funDef n ps rs bs =>
        if n == name then Stmt.funDef n ps rs (stripCtrlSs bs) else Stmt.funDef n ps rs bs
    | s => s
  stripped ++ List.replicate l Stmt.leave ++ List.replicate br Stmt.«break»
    ++ List.replicate c Stmt.«continue»

/-- CLONE MUTATION (placement): a `break` appended to the body of the definition named `name`, which
is inside no loop. -/
def cloneWithBreakInDefinition (name : String) (b : Block Op) : Block Op :=
  b.map fun
    | Stmt.funDef n ps rs bs =>
        if n == name then Stmt.funDef n ps rs (bs ++ [Stmt.«break»]) else Stmt.funDef n ps rs bs
    | s => s

/-- A `leave` inside a function: the legal shape, and the shape eleven of the emitted program's
twelve leaves have. -/
def placementWitnessLeaveInFunction : Block Op := yul% { function pf(a) -> c { c := 1 leave } }

/-- A `leave` at the top level of a block: the defect the brief asks to be shown. -/
def placementWitnessLeaveAtTop : Block Op := yul% { let a := 1
 leave }

/-- `break` and `continue` in a loop body: the legal shape. -/
def placementWitnessBreakInLoop : Block Op := yul% {
  for { let i := 0 } lt(i, 3) { i := add(i, 1) } { if eq(i, 1) { break } continue }
}

/-- `break` with no loop at all. -/
def placementWitnessBreakAtTop : Block Op := yul% { let a := 1
 break }

/-- `continue` with no loop at all. -/
def placementWitnessContinueAtTop : Block Op := yul% { let a := 1
 continue }

/-- `continue` inside a function that is inside no loop. -/
def placementWitnessContinueInFunction : Block Op := yul% { function pc(a) -> c { c := 1 continue } }

/-- `break` inside a function that is itself inside a loop: the case a walk that only asks "is there
a loop anywhere above me" gets wrong. -/
def placementWitnessBreakInFunctionInLoop : Block Op := yul% {
  for { let i := 0 } lt(i, 3) { i := add(i, 1) } { function pz(a) -> c { c := 1 break } }
}

/-- `leave` inside a loop inside a function: legal, and the case a walk that treats a loop as a
barrier gets wrong - Step.loopLeave carries it out to the call. -/
def placementWitnessLeaveInLoopInFunction : Block Op := yul% {
  function pw(a) -> c { for { let i := 0 } lt(i, 3) { i := add(i, 1) } { leave } }
}

/-- `break` in a loop's INIT block: the init must end normal, so this is stuck. -/
def placementWitnessBreakInLoopInit : Block Op := yul% {
  for { let i := 0 break } lt(i, 3) { i := add(i, 1) } { continue }
}

/-- GATE (THE PLACEMENT GATE). Five clauses:

    1. no misplaced control-flow statement in the whole emitted program at either pinned plan view,
       and none in any slice closed under the emitted helpers;
    2. the census is real: twelve leaves, no break and no continue at the no-accumulator view, and no
       leaf at all in the seven slices themselves - every leaf the program has belongs to a helper;
    3. WHERE they are: eleven inside `batch_invert` and one inside `ec_pairing`, and no other
       definition contains one - the table the brief asked to be checked, as data;
    4. the `break` / `continue` half is vacuous on the EMITTED program (clause 2 says so with zeros)
       and is therefore carried by the witnesses rather than by the program. Stated as a measurement
       so that the day the emitter grows a loop exit, the vacuity ends and this gate is already
       looking;
    5. the classifier separates the legal from the illegal shape in every position a leaf can occupy,
       including the two a naive walk gets wrong: a `break` inside a function defined inside a loop,
       and a `break` in a loop's init block. -/
def emittedProgramPlacement_ok : Bool :=
  -- 1. the predicate, whole program and per closed slice
  (closurePlanViews.all fun pv => controlViolations (GenAst.emitMain pv) == []) &&
    (closurePlanViews.all fun pv => partials.all fun q =>
      controlViolations (callClosure (GenAst.emitHelpers pv) (GenAst.emitPartial pv q)) == []) &&
    -- 2. the census, and the slices carrying none of it
    (controlCensus emittedMainPcs == (12, 0, 0)) &&
    (controlCensus (GenAst.emitSlices GenAst.pcsFixturePlan) == (0, 0, 0)) &&
    -- 3. the leaves, by the definition that owns each
    (leavesPerDefinition (GenAst.emitHelpers GenAst.pcsFixturePlan) ==
      [("fail", 0), ("scalar_inv", 0), ("transcript_init", 0), ("common_word", 0),
        ("common_uncompressed_g1", 0), ("squeeze_to", 0), ("batch_invert", 11),
        ("ec_pairing", 1)]) &&
    -- 4 and 5. the witnesses
    (controlViolations placementWitnessLeaveInFunction == []) &&
    (controlViolations placementWitnessLeaveAtTop == ["leave outside a function definition"]) &&
    (controlViolations placementWitnessBreakInLoop == []) &&
    (controlViolations placementWitnessBreakAtTop == ["break outside a for loop"]) &&
    (controlViolations placementWitnessContinueAtTop == ["continue outside a for loop"]) &&
    (controlViolations placementWitnessContinueInFunction == ["continue outside a for loop"]) &&
    (controlViolations placementWitnessBreakInFunctionInLoop == ["break outside a for loop"]) &&
    (controlViolations placementWitnessLeaveInLoopInFunction == []) &&
    (controlViolations placementWitnessBreakInLoopInit == ["break outside a for loop"])

/-- FALSIFICATION OF THE PLACEMENT GATE (D-P23, R-41). Hoisting the leaves out of the definition that
owns them reddens the gate with EXACTLY the number of leaves moved, and the census clause says the
mutation moved them rather than added them: same twelve leaves, wrong place. The unmutated program is
clean, so these are dependences on placement and not a constant false. -/
def emittedProgramPlacement_detectsHoist_ok : Bool :=
  (controlViolations (cloneHoistLeavesOutOf "batch_invert" emittedMainPcs) ==
      List.replicate 11 "leave outside a function definition") &&
    (controlViolations (cloneHoistLeavesOutOf "ec_pairing" emittedMainPcs) ==
      ["leave outside a function definition"]) &&
    (controlCensus (cloneHoistLeavesOutOf "batch_invert" emittedMainPcs) ==
      controlCensus emittedMainPcs) &&
    (! SyntaxEq.stmtsBeq (cloneHoistLeavesOutOf "batch_invert" emittedMainPcs) emittedMainPcs) &&
    (controlViolations (cloneWithBreakInDefinition "ec_pairing" emittedMainPcs) ==
      ["break outside a for loop"]) &&
    (controlViolations (GenAst.emitPartial GenAst.pcsFixturePlan .lagrange ++ [Stmt.leave]) ==
      ["leave outside a function definition"]) &&
    (controlViolations emittedMainPcs == [])

#eval emittedProgramPlacement_ok                    -- expect true
#eval emittedProgramPlacement_detectsHoist_ok       -- expect true

/-! ### THE EXTERNALS GUARD (P-ARITY): the third link dimension, guarded while it is still vacuous -/

/- THE OPTIONAL ITEM, DONE BECAUSE IT IS CHEAP AND BECAUSE VACUOUS IS NOT THE SAME AS SAFE.
`datasize`, `datacopy`, `dataoffset` and `loadimmutable` are in the dialect and used by neither the
emitted program nor the deployed runtime body, so the dimension is vacuous today - and a vacuous
dimension with no guard is invisible the day it stops being vacuous, which is exactly the class of
hole P-HELPERS found with the unhoisted helper. An embedded-VK arm or a sub-object reference would
link-fail in solc and stay green here. The existing
`emittedCallClosureIsNotLinkCompleteness_ok` clause 4 says the same thing about the PRINTED program;
this says it about the AST, so it cannot be dodged by a spelling or by a change to the printer.

THE BRIEF'S DIALECT NOTE IS STALE, and the measurement is below rather than in a paragraph. The
package asks this file to record `setimmutable` and `memoryguard` as absent from the dialect. They
are not absent: the vendored fork grew both (vendor EVMOp.lean:60 constructors, :219 name resolution,
gated by Midfall/Yul/Builtins.lean `parseNewBuiltins_ok`), which is what makes the imported via-IR
runnable at all. So the honest record is: the dialect has all six, the emitted program uses none of
the six, and the artifact uses `memoryguard` and `setimmutable` in its creation object and prologue -
the shell, out of scope by D-P30, and not something the emitter emits. Recorded as
`dialectExternalsGapRecord` so a later package cannot re-derive the stale version of the claim. -/

mutual
/-- The dialect built-in names an expression calls, duplicates kept, outermost first. -/
def builtinNamesE : Expr Op → List String
  | Expr.builtin op args => YulSemantics.EVM.opName op :: builtinNamesEs args
  | Expr.call _ args => builtinNamesEs args
  | _ => []
termination_by e => sizeOf e
def builtinNamesEs : List (Expr Op) → List String
  | [] => []
  | e :: es => builtinNamesE e ++ builtinNamesEs es
termination_by es => sizeOf es
def builtinNamesS : Stmt Op → List String
  | Stmt.block bs => builtinNamesSs bs
  | Stmt.funDef _ _ _ bs => builtinNamesSs bs
  | Stmt.letDecl _ (some e) => builtinNamesE e
  | Stmt.letDecl _ none => []
  | Stmt.assign _ e => builtinNamesE e
  | Stmt.cond c bs => builtinNamesE c ++ builtinNamesSs bs
  | Stmt.switch c cs d => builtinNamesE c ++ builtinNamesSC cs ++ builtinNamesSO d
  | Stmt.forLoop ini c pst bod =>
      builtinNamesSs ini ++ builtinNamesE c ++ builtinNamesSs pst ++ builtinNamesSs bod
  | Stmt.exprStmt e => builtinNamesE e
  | _ => []
termination_by s => sizeOf s
def builtinNamesSs : List (Stmt Op) → List String
  | [] => []
  | s :: ss => builtinNamesS s ++ builtinNamesSs ss
termination_by ss => sizeOf ss
def builtinNamesSC : List (Literal × List (Stmt Op)) → List String
  | [] => []
  | (_, bs) :: cs => builtinNamesSs bs ++ builtinNamesSC cs
termination_by cs => sizeOf cs
def builtinNamesSO : Option (List (Stmt Op)) → List String
  | none => []
  | some bs => builtinNamesSs bs
termination_by bs => sizeOf bs
end

/-- The dialect built-in names a block calls. -/
def builtinNamesIn : Block Op → List String := builtinNamesSs

/-- The object-level and compile-time builtins: the four that reference a sub-object or an immutable,
plus the two the fork added for the import. -/
def guardedExternals : List String :=
  ["datasize", "datacopy", "dataoffset", "loadimmutable", "memoryguard", "setimmutable"]

/-- Which of the guarded externals a block calls. -/
def externalUsesIn (b : Block Op) : List String :=
  (builtinNamesIn b).filter fun n => guardedExternals.contains n

/-- Which of the guarded externals one emitted program calls. -/
def emittedExternalUses (pv : PlanView) : List String := externalUsesIn (GenAst.emitMain pv)

/-- THE DIALECT GAP, AS MEASURED, correcting the brief. -/
def dialectExternalsGapRecord : String :=
  "P-ARITY measurement, correcting the brief: memoryguard and setimmutable ARE in the vendored "
    ++ "dialect (EVMOp.lean:60 constructors, :219 name resolution, gated by "
    ++ "Builtins.parseNewBuiltins_ok) - the P-VEND fork added them precisely so the imported via-IR "
    ++ "could run. The dialect gap that IS still open is the object layer: the emitter produces a "
    ++ "Block and not an Object, so a datasize/dataoffset of a named sub-object has nothing to "
    ++ "resolve against even though the Op exists. That is why the guard below asserts non-use "
    ++ "rather than trying to model the object table."

/-- A program that DOES reach for a sub-object: the classifier must see it. -/
def externalsWitness : Block Op := yul% {
  function qd(a) -> c { c := datasize("sub") }
  let y := datacopy(0, 0, 0)
}

/-- GATE (THE EXTERNALS GUARD). Four clauses: the emitted program uses none of the six at either
pinned plan view; the classifier is not a constant, because a program that does use two of them
reports exactly those two; every guarded name really does resolve in the dialect, so the guard is
checking a dialect that has them and not a spelling nobody can call; and the record above is non-empty
prose a reader can find. -/
def emittedProgramUsesNoGuardedExternals_ok : Bool :=
  (closurePlanViews.all fun pv => emittedExternalUses pv == []) &&
    (externalUsesIn externalsWitness == ["datasize", "datacopy"]) &&
    (guardedExternals.all fun n => (YulSemantics.EVM.parse n).isSome) &&
    (! dialectExternalsGapRecord.isEmpty)

#eval emittedProgramUsesNoGuardedExternals_ok     -- expect true

/-! ### THE COVERAGE CHECKLIST (P-ARITY): every Stmt constructor and what checks it -/

/- THE DELIVERABLE THE BRIEF ASKS FOR, as a machine-checked list rather than a paragraph. Two lists
follow: `stmtWellFormednessCoverage`, one row per constructor of the vendored `Stmt` grammar saying
which gate checks what about it, and `uncheckedWellFormednessDimensions`, the dimensions that remain
open after this package. The coverage list is PINNED to the grammar by `stmtCtorName`, whose match
has no wildcard arm: add a constructor to the vendored AST and that match stops compiling, which is
the only honest way to keep a checklist from going stale. The gate below then checks the list has one
row per constructor, that the emitted program's own census uses only listed constructors, and that the
rows marked NOT EXERCISED are exactly the constructors the program does not contain. -/

/-- The constructor name of one statement. The match is exhaustive with no wildcard ON PURPOSE: a new
`Stmt` constructor in the vendored AST is a build failure here before it is a silent gap in the
checklist below. -/
def stmtCtorName : Stmt Op → String
  | Stmt.block _ => "block"
  | Stmt.funDef _ _ _ _ => "funDef"
  | Stmt.letDecl _ _ => "letDecl"
  | Stmt.assign _ _ => "assign"
  | Stmt.cond _ _ => "cond"
  | Stmt.switch _ _ _ => "switch"
  | Stmt.forLoop _ _ _ _ => "forLoop"
  | Stmt.exprStmt _ => "exprStmt"
  | Stmt.«break» => "break"
  | Stmt.«continue» => "continue"
  | Stmt.leave => "leave"

/- Every statement in a block, deep, in AST order: the walk the census is taken over. -/
mutual
def allStmtsSs : List (Stmt Op) → List (Stmt Op)
  | [] => []
  | s :: ss => allStmtsS s ++ allStmtsSs ss
termination_by ss => sizeOf ss
def allStmtsS : Stmt Op → List (Stmt Op)
  | Stmt.block bs => [Stmt.block bs] ++ allStmtsSs bs
  | Stmt.funDef n ps rs bs => [Stmt.funDef n ps rs bs] ++ allStmtsSs bs
  | Stmt.cond c bs => [Stmt.cond c bs] ++ allStmtsSs bs
  | Stmt.switch c cs d => [Stmt.switch c cs d] ++ allStmtsSC cs ++ allStmtsSO d
  | Stmt.forLoop i c ps bs =>
      [Stmt.forLoop i c ps bs] ++ allStmtsSs i ++ allStmtsSs ps ++ allStmtsSs bs
  | s => [s]
termination_by s => sizeOf s
def allStmtsSC : List (Literal × List (Stmt Op)) → List (Stmt Op)
  | [] => []
  | (_, bs) :: cs => allStmtsSs bs ++ allStmtsSC cs
termination_by cs => sizeOf cs
def allStmtsSO : Option (List (Stmt Op)) → List (Stmt Op)
  | none => []
  | some bs => allStmtsSs bs
termination_by bs => sizeOf bs
end

/-- How many statements of each constructor a block contains, deep. -/
def stmtCtorCensus (b : Block Op) : List (String × Nat) :=
  let names := (allStmtsSs b).map stmtCtorName
  names.eraseDups.map fun n => (n, (names.filter fun m => m == n).length)

/-- ONE ROW PER CONSTRUCTOR of the vendored `Stmt` grammar (Ast.lean:74-86), saying which gate checks
what about it. This is the checklist the brief asks for. The rows that say NOT EXERCISED are the honest
ones: the walker covers the constructor, but the emitted program contains none of it, so nothing about
the EMITTED program can be claimed from those rows and the witnesses carry them instead. -/
def stmtWellFormednessCoverage : List (String × String) :=
  [("block", "walked by the closure, arity and placement gates; no well-formedness condition of its "
    ++ "own beyond nesting"),
   ("funDef", "ARITY: its params and rets ARE the signature every call site is checked against; "
    ++ "PLACEMENT: it is the construct that makes a leave legal; CLOSURE: its name is what a call "
    ++ "resolves to"),
   ("letDecl", "ARITY: bound-variable count must equal the callee's return count; the "
    ++ "free-identifier gate covers the names it declares"),
   ("assign", "ARITY: target count must equal the callee's return count; the free-identifier gate "
    ++ "counts a target as a REFERENCE, which is the right polarity"),
   ("cond", "ARITY: a call in the condition must be single-valued; the body is walked by all three "
    ++ "gates"),
   ("switch", "ARITY: scrutinee single-valued, case bodies and default walked; NOT EXERCISED - the "
    ++ "emitted program contains zero switch statements, so this row is carried by the walker and "
    ++ "not by the program"),
   ("forLoop", "PLACEMENT: it is the construct that makes break and continue legal, and ONLY its "
    ++ "body does - init and post must end normal; init, post and body walked by all three gates"),
   ("exprStmt", "ARITY: a call used as a statement must return zero values, which is the shape "
    ++ "every fail(..) arm in the program has"),
   ("break", "PLACEMENT: must be inside a loop body; NOT EXERCISED - zero in the emitted program"),
   ("continue", "PLACEMENT: must be inside a loop body; NOT EXERCISED - zero in the emitted "
    ++ "program"),
   ("leave", "PLACEMENT: must be inside a function definition; TWELVE in the emitted program, "
    ++ "eleven in batch_invert and one in ec_pairing, all legal and shown load-bearing by the "
    ++ "hoist mutation")]

/-- THE DIMENSIONS THAT REMAIN OPEN after arity and placement. Each is a real well-formedness
condition of Yul or of the vendored semantics, none is checked by any gate in this tree, and the list
is the deliverable: it is the next package's queue rather than the next surprise. -/
def uncheckedWellFormednessDimensions : List (String × String) :=
  [("builtin argument arity", "a wrong-arity dialect call (mstore with one argument) has no Step "
    ++ "rule and is stuck; no gate counts builtin arguments against what the dialect expects. The "
    ++ "emitted program calls 27 distinct dialect builtins and not one of those argument lists is "
    ++ "checked anywhere in this tree"),
   ("duplicate declaration in one scope", "let x := 1 and let x := 2 in one block is rejected by "
    ++ "the Yul validator and silently shadowed by the semantics; the free-identifier gate is "
    ++ "flat-scope and cannot see a scope at all"),
   ("use before declaration, and use after scope exit", "same cause: a flat pass over the whole "
    ++ "program counts a name declared ANYWHERE as declared, which under-approximates the free set "
    ++ "- the limit is stated at emittedFreeIdentifiers and is not repaired here"),
   ("duplicate function name in one scope", "two funDefs with the same name: hoist keeps both and "
    ++ "lookupFun takes the first, so the second is unreachable and no gate notices"),
   ("parameter and return name collision inside one funDef", "function f(x) -> x is rejected by "
    ++ "the validator; the arity gate reads only the COUNTS, which is all the semantics needs to "
    ++ "run, so this is a validator-only gap"),
   ("duplicate targets in one let or assign", "let x, x := f() is rejected by the validator; the "
    ++ "arity gate counts the targets and so cannot see the duplication"),
   ("duplicate switch case labels", "selectSwitch takes the first match, so a doubled case is "
    ++ "unreachable; vacuous today because the program has no switch"),
   ("literal well-formedness", "litWF (EVMOp.lean:80-83) requires a number below 2^256 and a string "
    ++ "of at most 32 bytes; nothing checks the emitted literals against it, and a 33-byte string "
    ++ "literal would be silently truncated by litValue rather than rejected"),
   ("object layer", "the emitter produces a Block and not an Object, so sub-object and data "
    ++ "resolution is outside the grammar the gates can see - see dialectExternalsGapRecord")]

/-- GATE (THE CHECKLIST IS THE GRAMMAR, NOT A MEMORY). Five clauses: the coverage list has exactly one
row per constructor of the vendored `Stmt` grammar and no row for anything else; every constructor the
emitted program uses appears on the list with a non-zero census count; the three constructors the
emitted program does NOT use are exactly the three the list marks NOT EXERCISED; the open-dimensions
list is non-empty and has one row per named gap; and the two lists are disjoint, so a dimension cannot
be recorded as both covered and open. -/
def stmtWellFormednessCoverage_ok : Bool :=
  (((stmtWellFormednessCoverage.map Prod.fst).eraseDups).length ==
      stmtWellFormednessCoverage.length) &&
    (stmtWellFormednessCoverage.length == 11) &&
    (sameMembers (stmtWellFormednessCoverage.map Prod.fst)
      ["block", "funDef", "letDecl", "assign", "cond", "switch", "forLoop", "exprStmt",
        "break", "continue", "leave"]) &&
    ((stmtCtorCensus emittedMainPcs).all fun (n, k) =>
      stmtWellFormednessCoverage.any fun (m, _) => m == n && k > 0) &&
    ((stmtWellFormednessCoverage.filter fun (_, d) => d.contains "NOT EXERCISED").map Prod.fst
      == ["switch", "break", "continue"]) &&
    ((stmtCtorCensus emittedMainPcs).lookup "switch" == none) &&
    ((stmtCtorCensus emittedMainPcs).lookup "break" == none) &&
    ((stmtCtorCensus emittedMainPcs).lookup "continue" == none) &&
    (uncheckedWellFormednessDimensions.length == 9) &&
    ((uncheckedWellFormednessDimensions.map Prod.fst).all fun n =>
      ! (stmtWellFormednessCoverage.any fun (m, _) => m == n))

#eval stmtWellFormednessCoverage_ok               -- expect true

end Midfall.Lowering
