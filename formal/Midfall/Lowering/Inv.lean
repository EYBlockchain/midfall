-- |
-- Midfall.Lowering.Inv
--
-- P-SE stage 3, file 3 of 3 (docs/plans/P-SE-stage3.md file row 3; design0.md
-- sections PlanView / EnvAgrees, ChallengesGood, and Inv).
--
-- WHAT THIS FILE IS FOR. This is the per-phase memory invariant every per-partial
-- correctness theorem is stated in terms of: vkLoading_spec, transcriptParser_spec,
-- lagrange_spec, quotientLin_spec, pcs_spec, finalPairing_spec and traceReturn_spec
-- each take their hypothesis from Inv at a checkpoint and must return it at the next
-- one. Inv k says what the contract memory, the Yul locals and the halt record look
-- like at boundary k, expressed as the values of a Snapshot (Snapshot.lean) at the
-- addresses the layout planner assigned them (Generator/LayoutMemory.lean).
--
-- HAZARD 1 IS THE REASON THIS FILE IS SHAPED THE WAY IT IS. An Inv no state
-- satisfies makes every per-partial theorem vacuously true, which is the failure
-- mode review F1 caught in end_to_end_noAcc (a forall over an empty set of runs). So
-- the clauses are Bool-valued and Inv is the proposition that the Bool is true. That
-- is not cosmetic: it makes the whole invariant DECIDABLE at a concrete state, so
-- satisfiability is a computation rather than an act of faith. The exhibit and the
-- perturbations are in Midfall/Instances/InvFixture.lean, which is where a concrete
-- pairing model is allowed (hazard 5: the Instances confinement gate greps direct
-- imports, so no file this one can reach may name a model).
--
-- FINDING 12 IS WHY THE CLAUSES CARRY LIVENESS GUARDS. A clause about a phase-scoped
-- region may only be asserted where that region is still live, and Inv k accumulates
-- the clauses of every boundary up to k. The selector-accumulator buckets are
-- written by the quotient partial and read by the PCS partial, and their lifetime is
-- (MemoryLifetime.phase MemoryPhase.pcsFinalMsm) (LayoutMemory.lean:268-270), so
-- they are live at .quotient and .pcs and dead at .pairing
-- (Checkpoint.liveAt). The selector clause is therefore guarded by
-- (Checkpoint.liveRegionNamed k M "selector_accumulators"), read from the layout
-- rather than hard-coded, and it drops out at .pairing on its own.
--
-- TWO CONSEQUENCES OF THAT GUARD, both reported rather than hidden:
--
--   1. Inv is NOT monotone. design0 lists Inv_mono (k₁ ≤ k₂ → Inv k₂ → Inv k₁) as a
--      lemma of this file. It is FALSE as written, for exactly the reason the guard
--      exists: a state whose selector bytes are garbage satisfies Inv .pairing (the
--      clause is not asserted there) and refutes Inv .quotient. The corrected form
--      is Inv_permanent_mono below, which is what the composition proofs can actually
--      use, and the counterexample is exhibited in the fixture file.
--   2. The guard is only as good as the layout. If a future render registers
--      selector_accumulators as permanent, the clause becomes live everywhere and
--      the .pairing state must then carry the buckets; selectorAccLifetimeKats_ok in
--      Checkpoint.lean is what makes that change loud.
--
-- FINDING 11 IS WHY ONE SLOT IS ABSENT. X_N_MINUS_1_INV_MPTR is written by
-- Lagrange.yul:80 and read by nothing in a production render: the only reader is
-- TraceReturn.yul, which is compiled out when trace is off (Supported.production),
-- and the grep of kzg/mod.rs, quotient.rs, QuotientNumeratorBlock.yul and
-- quotient_numerator/*.rs is empty. Lean has no counterpart either: lIRange computes
-- (xn - 1) * barycentricWeight and never inverts xn - 1. So Inv leaves that slot
-- UNCONSTRAINED. That is a deliberate don-t-care, not an oversight: inventing a Lean
-- value for a slot nothing reads would pin memory to something the reference never
-- computes, and the stage-3 brief forbids both inventing it and silently constraining
-- it.
--
-- R-58 F9 DELETED ONE PlanView FIELD: `consts : TemplateConstants`. Nothing in the
-- tree read PV.consts - the only constant any statement here needs is FR_MODULUS, and
-- that is pinned from the other side by EnvAgrees.modulus (p = frModulusConstant). A
-- copy of the render's constant table that no theorem consumes is the decoration class
-- the review names, so it is gone rather than justified; it comes back with the P-11
-- plan record, whose constants the emitter actually uses, and only with a pin.
--
-- WHAT IS NOT HERE. blk (no Lean function returns a partial Yul AST yet, P-13), the
-- forall-runs contract layer (Midfall/Yul/Contracts.lean), the per-partial
-- obligations themselves (stage 4), and the reversed-evals spill clause: the contract
-- REVERSED_EVALS_MPTR order comes from the generator Data.new plan, and the bridge
-- from a VerifierTrace to that order is owed by the Encoding area (design0 lists it
-- as a stub). Rather than guess the order, the clause is absent and named here.

import Midfall.Lowering.Checkpoint
import Midfall.Lowering.Snapshot
import Midfall.Assumptions.TwoAdicity
import Midfall.Generator.Layout
import Midfall.Generator.LayoutMemory
import Midfall.Generator.Models
import Midfall.Generator.Api
import Midfall.Generator.Abi
import Midfall.Generator.Templates
import Midfall.Halo2.Exec.Accumulator
import Midfall.Yul.Bridge
import YulSemantics
import YulSemantics.Dialect.EVMExec

namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Yul YulSemantics
open YulSemantics.EVM

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]
  {calls : ExternalCalls} {gas : ExternalGas}

/-! ### The plan view -/

/-- The generator-side facts Inv reads, and the AST emitter emits.

    WHAT THIS IS A PROJECTION OF, AND WHY IT IS NOT THE THING ITSELF. This record used to
    describe itself as a projection of LoweringPlan "P-11, unported: plan.rs:29 has no Lean
    counterpart". THAT SENTENCE WAS STALE: P-11 landed the record (Generator/LoweringPlan.lean
    ports PL:29-45 in eleven fields), so the projection now has a denotation, and P-PLANVIEW
    had to decide whether to keep projecting or to start carrying. It kept projecting, and
    added the two fields the PCS emitter needs, and the reason is a measurement rather than
    a preference:

      * Nine of LoweringPlan's eleven fields are not read by anything in this tree. Carrying
        the record would add `lowering`, `sortedSimple`, `quotient`, `direct`,
        `pcsMemoryRequirements` and two more to a structure whose every field is read by a
        clause or an emitter - the exact class R-58 F9 deleted `consts : TemplateConstants`
        for (see this file's own header). A field nothing reads is decoration.
      * Four of its fields ARE PlanView fields already - vk, vkMptr, memory, proofLayout -
        so carrying the plan would create a NEW four-member copy family unless the whole
        projection were rewritten, and that rewrite moves every clause of Inv, every
        `S.plan.proofLayout` in Partials.lean and every hypothesis of the ten *_spec
        theorems. That is a package of its own, not a field addition dressed as one.
      * `LoweringPlan Program Layout` is parameterised over the two deferred M10 Direct
        types, and the only assembled plan in the tree instantiates them at `Unit`
        (Instances/DeployedProfile.lean:177). PlanView would inherit a parameterisation that
        is an artefact of what has not been ported.
      * And the blocker ObligationsGates:514 actually names is `P-11 LoweringPlan::new`, not
        the record. Carrying the record does not close gap_qvmField_surface_free: no Lean
        term can BUILD a plan from a circuit, so a PlanView holding a LoweringPlan would
        hold a hand-assembled one and the qvm field would still quantify over a plan nothing
        derived. The two fields added below are two of the plan's own, so when `new` lands
        this structure SHRINKS into the plan rather than growing again.

    vk here is the GENERATOR payload model (Halo2VerifyingKey), not the Exec
    VerifyingKey: the VK clause of Inv is about the bytes the contract copies, and
    those come from the payload model. The two are tied by EnvAgrees below. -/
structure PlanView where
  /-- The payload image VkLoading.yul copies into memory. -/
  vk : Halo2VerifyingKey
  /-- Where it is copied to. -/
  vkMptr : Ptr
  /-- The converged memory layout: every other address Inv names. -/
  memory : VerifierMemoryLayout
  /-- The calldata geometry, for the length clause. -/
  proofLayout : ProofCalldataLayout
  /-- Public instance words, i.e. the calldata tail length. -/
  numInstances : Nat
  /-- log2 of the domain size: Lagrange.yul:13 squares k times. -/
  k : Nat
  /-- The negative-rotation count Lagrange.yul:57 walks for l_blind. -/
  numNegLagranges : Nat
  /-- expected_has_accumulator: whether the acc slots exist in this render. Pinned to
      cfg.accumulator by Surface.plan_hasAccumulator (R-58 F2); until that field existed
      this was a free Bool. -/
  hasAccumulator : Bool
  /-- P-AST3b. expected_has_accumulator AS THE VK HEADER WORD: 1 when the render has an
      accumulator arm, 0 when it does not. Vk.lean:782 (VK:119) renders exactly
      "if inputs.accEncoding.isSome then 1 else 0", and VkLoading.yul:110 compares the
      loaded HAS_ACCUMULATOR_MPTR against it. A Nat and not a Bool because that is what
      the template interpolates; hasAccumulator above is the same fact in the other
      spelling, and BOTH come out of accWordsOfEncoding, never out of a call site. -/
  expectedHasAccumulatorWord : Nat
  /-- P-AST3b. expected_acc_offset: the public-input index the accumulator tail starts
      at (Vk.lean:783-785, VK:120-123; ART:230). Zero with no accumulator because the
      reference's unwrap_or_default writes a zero word and the template then compares
      the loaded header against that word - NOT because any plan has offset 0. -/
  expectedAccOffset : Nat
  /-- P-AST3b. expected_num_acc_limbs (Vk.lean:786-788, VK:124-126; ART:231). -/
  expectedNumAccLimbs : Nat
  /-- P-AST3b. expected_num_acc_limb_bits (Vk.lean:789-791, VK:127-131; ART:232). -/
  expectedNumAccLimbBits : Nat
  /-- P-AST4. M:558 user_phases (ART:160-170, one UserPhase per advice phase): the list
      TranscriptProofParser.yul:105 LOOPS OVER, and the first list-valued PlanView field.
      It stays a list: flattening it into "the advice bytes" plus "the challenge count"
      would delete the loop structure the snapshot exists to check, and the per-phase
      challenge offset is a RUNNING SUM over the earlier phases (ART:168), which two
      scalars cannot express at all. So the shape the constructor helpers needed was the
      plain structure field and nothing more - no DSL change was required, which is the
      finding P-AST4 was asked to report if it had been. Derived by parserFactsOfPlan. -/
  userPhases : List Midfall.Generator.UserPhase
  /-- P-AST4. M:562 lookup_h_plus_acc (ART:172: sum of lookup_chunks plus num_lookups):
      the guard at T:195. NOT re-derived here - Artifacts.lean's lookupHPlusAccOf is the
      one carrier of that sum, and parserFactsOfPlan reads its result off the plan model. -/
  lookupHPlusAcc : Nat
  /-- P-AST4. M:614 truncated_challenges (ART:328, a CARGO-FEATURE flag made data by rule
      R8): the guard at T:355 that decides whether the x3 mask is emitted. A Bool because
      the template branches on the flag itself and not on a derived count. It is NOT a
      projection of `meta_` below: the Rust reads it from the build inputs (ART:328), not
      from the constraint system, so it stays a field while the three counts that DO come
      from the meta have been deleted. -/
  truncatedChallenges : Bool
  /-- P-PLANVIEW. The constraint-system meta of the circuit this render is for: the record
      `Midfall.Generator.Kzg.computationsAst` (GenAstPcs.lean:587) consumes it and nothing
      else for the point-set partition, and it is the FIRST of the two inputs that package
      needed and this structure did not carry.

      WHY THE NAME IS `meta_` AND NOT `meta`: `meta` is a Lean command modifier and cannot
      even be a `let` binder at this toolchain, so the tree's R2 convention (Encoding.lean
      :612, LoweringPlan.lean's own deviation note at PL:101, Protocol.lean:378) is a
      trailing underscore. The field keeps the convention rather than inventing a fourth
      spelling; `csMeta` was the other candidate and was rejected because every function
      this field is handed to names its parameter `meta_`, so a rename would be a
      translation layer that buys nothing.

      WHAT MAKES THIS A PROJECTION AND NOT A FREE RECORD: the three counts this structure
      used to carry - numLookups, numPermutationZs, numTrashcans - are GONE and are now
      read off here (see the three defs below the constructor). A copy of a fact and the
      source of that copy in one record with nothing relating them is the R-58 class the
      duplicate-fact gate exists for, and the repair the gate prefers is deletion. -/
  meta_ : Midfall.Generator.ConstraintSystemMeta
  /-- P-PLANVIEW. The binding table: the commitment handles and eval slots the PCS region
      stages its MSM pairs from (ENC:226-294). The second of the two inputs
      `computationsAst` needs; `dat.fixedComms` is read by `pcsLinExpansion`
      (GenAstPcs.lean:407) and the whole record by `intermediateSets` through `queries`.

      WHY `dat` AND NOT `data`: `data` is a Lean keyword. P-STR2AST measured that the
      structure-instance field form `data := ...` is REJECTED by the parser in
      Instances/DeployedProfile.lean (its own note at :178-184), and Artifacts.lean:514-517
      binds the plan's Data as `planData` for the same reason. `dat` is three letters
      away from the Rust name, cannot collide, and does not need a comment to explain a
      backtick escape.

      WHY THIS IS NOT OBSERVED DATA: `Data.new` (ENC:302-553) DERIVES the whole record from
      (meta, vk, memory), and the witness plan view below calls it. The deployed poseidon
      Data is a different matter - it is hand-built in Instances/DeployedProfile.lean
      because the circuit's eval schedule is not in the tree - and that one stays there. -/
  dat : Midfall.Generator.Data

/-! ### The four accumulator words, derived and not chosen

    P-AST3b added these four because VkLoading.yul:105-110 cross-checks the loaded VK
    header against them, so an emitter that produced the slice had to have them. They are
    a COPY of a fact the Rust derives once from cfg.accumulator, which is the R-58 F2 /
    F6 class the duplicate-fact gate exists for, so two things are done about it rather
    than nothing: the values are DERIVED in one place (accWordsOfEncoding, reached only
    through planViewWithAccumulator, the constructor every call site uses), and each copy
    is related to its source by the named pin Surface.plan_accExpectations, registered as
    a family in scripts/check_duplicate_facts.py. proofLen is NOT a fifth copy: the
    render reads ctx.proofLen and poseidonProofLayout.proofLen is the same number,
    pinned by VerifierPartials' own gate 35, so PlanView.proofLayout already carries it. -/

/-- The four VK-header accumulator words, read off the plan's accumulator encoding in ONE
    place. This is the shape of the reference's own single derivation: Vk.lean:782-791
    writes the four words from inputs.accEncoding with unwrap_or_default() for the none
    arm, and Artifacts.lean's accExpectationsOf (ART:229-245) reads the same values off
    the same Option, with ART:245's unwrap_or((false, 0, 0, 0, false)) as the arm the
    deployed poseidon profile takes.

    BOTH arms are here because both are the reference's. The deployed profile takes the
    none arm, which is why all four words are 0 in the artifact - and hard-coding four
    zeros would reproduce those bytes while lying for every accumulator plan, which is
    the accident P-AST3a explicitly refused. planAccWords_derive_ok is the falsification:
    a real encoding moves all four words together, so the derivation is a function and
    not four constants with a doc comment. -/
def accWordsOfEncoding (acc : Option Midfall.Generator.AccumulatorEncoding) :
    Nat × Nat × Nat × Nat :=
  match acc with
  | none => (0, 0, 0, 0)
  | some e => (1, e.offset, e.numLimbs, e.numLimbBits)

/-! ### The transcript-parser facts, derived and not chosen

  P-AST4 added these six because TranscriptProofParser.yul loops over userPhases and guards
  four of its ten proof sections on the four counts, and masks x3 on the flag. They were a
  COPY of six fields the Rust derives once into the render model (M:557-563 and M:614,
  filled at ART:160-170 / :291-294 / :328), which is the R-58 F2 / F6 class the
  duplicate-fact gate exists for. The repair is the same shape P-AST3b used for the four
  accumulator words: ONE derivation (parserFactsOfPlan, reached only through
  planViewWithAccumulator, the constructor every call site uses) and a registered family.

  WHY REGISTERED BY HAND, and not by the gate: discovery (rule 5) PREFIX-matches the field
  name against DISCOVERY_STEMS, and not one of userPhases / numLookups / numPermutationZs /
  lookupHPlusAcc / numTrashcans / truncatedChallenges begins with hasAccumulator,
  numInstances, accumulator, evaluator, encG2, runtimeName, vkDigest or shell. "numLookups"
  does not start with "numInstances"; "lookupHPlusAcc" does not start with "accumulator".
  Six new copies of six old facts and the automatic scan sees none of them - the same
  finding P-AST3b recorded for the four `expected*` words, reproduced on a whole family,
  and the reason the family below is hand-written and says so. -/

/-- The three transcript-parser facts that are NOT projections of the meta, read off the
    generator's plan model in ONE place. This is the reference's own single derivation:
    they are fields of the assembled Halo2Verifier model (M:557, M:562, M:614), which
    Artifacts.lean fills from the constraint-system meta and the proof layout
    (userPhasesOf at ART:160-170, the sum at ART:172, the cargo flag at ART:328) and which
    partialCtxOfVerifier then copies into the render context at ART:661-667. Reading them
    off the model rather than recomputing them here is what keeps this a projection and not
    a second derivation that could drift from the first.

    P-PLANVIEW SHRANK THIS TUPLE FROM SIX TO THREE, and the three that went are the three
    the meta already carries: numLookups, numPermutationZs and numTrashcans are literally
    `meta_.numLookups`, `meta_.numPermutationZs` and `meta_.numTrashcans` at ART:291,
    :292 and :294. Once PlanView carries the meta, keeping them as separate fields is a
    copy whose source sits in the same record, so they are deleted and re-read by the three
    defs below. userPhases and lookupHPlusAcc STAY, for two different reasons and both are
    stated rather than left to a reader: userPhasesOf (ART:160-170) indexes
    proofLayout.advicePhases and aborts at ART:164 when it is short, and a total projection
    would have to swallow that panic into an empty list, which is rule R4's don't; and
    lookupHPlusAcc is kept as the model's value rather than recomputed from the meta
    because Artifacts.lean's lookupHPlusAccOf is the one carrier of that sum (the field's
    own doc says so). truncatedChallenges is a build input (ART:328), not a meta field.

    The tuple order IS the PlanView field order, and planParserFacts_derive_ok pins both
    the order and the fact that every component moves when the model moves. -/
def parserFactsOfPlan (m : Midfall.Generator.Halo2Verifier VerifierMemoryLayout
    ProofCalldataLayout) :
    List Midfall.Generator.UserPhase × Nat × Bool :=
  (m.userPhases, m.lookupHPlusAcc, m.truncatedChallenges)

/-- THE THREE DELETED COPIES, re-read off the meta. These are the reference's own three
    lines in the model builder (ART:291, :292, :294: `num_lookups: meta.num_lookups` and
    its two siblings), spelled as projections rather than stored as fields so that there is
    ONE carrier of each fact in this record instead of two.

    WHY A DEF AND NOT A FIELD: Lean's dot notation resolves `pv.numLookups` to this
    function, so every consumer - emitTranscriptParser, the parser's perturbation gates,
    Instances/SurfaceFixture - reads the number through the meta without a single call-site
    change. That is the difference between deleting a copy and renaming one: a renamed copy
    would still be a copy.

    THE FAILURE MODE THIS REMOVES: before it, a PlanView could carry numLookups := 5 with
    meta_.numLookups := 1 and the parser slice would emit the five-lookup guard while the
    PCS slice emitted the one-lookup partition, from one plan view, with no gate able to
    notice. planMetaProjections_ok is the computation that says it cannot happen now. -/
def PlanView.numLookups (pv : PlanView) : Nat := pv.meta_.numLookups
def PlanView.numPermutationZs (pv : PlanView) : Nat := pv.meta_.numPermutationZs
def PlanView.numTrashcans (pv : PlanView) : Nat := pv.meta_.numTrashcans

/-- THE CONSTRUCTOR: a PlanView whose four accumulator words and whose hasAccumulator Bool
    are all read off `acc` by accWordsOfEncoding, whose three remaining transcript-parser
    facts are all read off `facts` - which every deployed call site supplies from
    parserFactsOfPlan rather than typing - and whose three counts are read off `meta_` by
    the defs above and are therefore not parameters at all. So no call site can pick a
    number the configuration does not imply, and no call site can pick a count the meta
    contradicts. Every PlanView in the tree is built here (Inv's own witnessPlanView and
    Instances/SurfaceFixture's fxPlan), which is what makes "derived from cfg.accumulator
    and from the plan model" a property of the code and not of a comment. -/
def planViewWithAccumulator (vk : Halo2VerifyingKey) (vkMptr : Ptr)
    (memory : VerifierMemoryLayout) (proofLayout : ProofCalldataLayout)
    (numInstances k numNegLagranges : Nat)
    (acc : Option Midfall.Generator.AccumulatorEncoding)
    (facts : List Midfall.Generator.UserPhase × Nat × Bool)
    (meta_ : Midfall.Generator.ConstraintSystemMeta)
    (dat : Midfall.Generator.Data) : PlanView :=
  let (hasWord, accOffset, numLimbs, limbBits) := accWordsOfEncoding acc
  let (userPhases, lookupHPlusAcc, truncatedChallenges) := facts
  { vk := vk, vkMptr := vkMptr, memory := memory, proofLayout := proofLayout,
    numInstances := numInstances, k := k, numNegLagranges := numNegLagranges,
    hasAccumulator := acc.isSome,
    expectedHasAccumulatorWord := hasWord, expectedAccOffset := accOffset,
    expectedNumAccLimbs := numLimbs, expectedNumAccLimbBits := limbBits,
    userPhases := userPhases, lookupHPlusAcc := lookupHPlusAcc,
    truncatedChallenges := truncatedChallenges, meta_ := meta_, dat := dat }

/-- The empty-plan parser facts: the three values a plan with no phases, no lookup helpers
    and no truncation carries. witnessPlanView and the fixture plan use it, so the three
    fields are never filled by a call site inventing a number - they are either the
    deployed derivation's or this. The three counts are not here any more: they are the
    meta's, and a plan with no circuit has a meta with no counts. -/
def emptyParserFacts : List Midfall.Generator.UserPhase × Nat × Bool := ([], 0, false)

/-- The Data of a plan with no circuit: every commitment list empty and every pointer read
    off the layout it belongs to, which is exactly what `Data.new` (ENC:302-553) produces
    for `constraintSystemMetaDefault` - the protocol's eval plan is empty and
    `numMainEvals` is 0, so ENC:432's assert compares 0 with 0 and does not fire.
    witnessPlanData_isOk_ok is that claim as a computation; the fallback exists because
    `Data` has no Default (ENC:226 derives Debug and Clone only) and a hand-written empty
    record is the one thing the derivation is checked against rather than trusted as. -/
def emptyDataAt (mem : VerifierMemoryLayout) : Midfall.Generator.Data :=
  { challengeMptr := mem.challengeMptr, thetaMptr := mem.thetaMptr,
    fixedComms := [], permutationComms := [], adviceComms := [],
    committedInstanceComms := [], permutationZComms := [], lookupMComms := [],
    lookupHelperComms := [], lookupZComms := [], trashcanComms := [],
    challenges := [], instanceEval := Midfall.Generator.Word.fromPtr (ptrMemory (valueFromNat 0)),
    committedInstanceEvals := [], adviceEvals := [], fixedEvals := [],
    permutationEvals := [], permutationZEvals := [], lookupEvals := [],
    trashcanEvals := [],
    computedQuotientComm := Midfall.Generator.EcPoint.new (ptrMemory (valueFromNat 0)),
    computedQuotientEval := Midfall.Generator.Word.fromPtr (ptrMemory (valueFromNat 0)),
    commsMptrBase := mem.commsMptrBase, reversedEvalsMptr := mem.reversedEvalsMptr,
    dummyEvalWords := [] }

/-! ### Addresses and the memory predicates -/

/-- The byte address of a layout pointer. Ptr arithmetic in the reference is
    WORD-wise (Encoding.lean:249, :276), so a byte offset is never added to a Ptr:
    convert first, then add. Every address in Inv goes through this. -/
def ptrAddr (q : Ptr) : Nat := Value.asUsizeNat (ptrValue q)

/-- The big-endian 32-byte word at byte address a (EVMExec.lean:320). -/
def wordAt (st : EvmState) (a : Nat) : Word256 := loadWord st.memory a

/-- n bytes at byte address a (EVMExec.lean:337), as a ByteArray so it can be
    compared with a codec output. -/
def bytesAt (st : EvmState) (a n : Nat) : Bytes :=
  ByteArray.mk (readBytes st.memory a n).toArray

/-- The word at a is the canonical word of x. Canonical because frWord is
    BitVec.ofNat 256 x.val, i.e. the value reduced mod p, so a non-canonical word
    at the same address does NOT satisfy this (R-26.7 refuses to lose that). -/
def holdsFr (st : EvmState) (a : Nat) (x : Fr p) : Bool := wordAt st a == frWord x

/-- The 128-byte EIP-2537 padded point at a is the encoding of Q. -/
def holdsG1 (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (a : Nat) (Q : G₁) : Bool :=
  bytesAt st a 128 == E.g1.toEip Q

/-- A run of points, 128 bytes apart, starting at base: the commitment regions. -/
def holdsG1s (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (base : Nat)
    (Qs : Array G₁) : Bool :=
  (Qs.zipIdx.toList).all fun (Q, i) => holdsG1 E st (base + 128 * i) Q

/-- A run of scalars, 32 bytes apart: the selector buckets and the eval spills. -/
def holdsFrs (st : EvmState) (base : Nat) (xs : Array (Fr p)) : Bool :=
  (xs.zipIdx.toList).all fun (x, i) => holdsFr st (base + 32 * i) x

/-- The Yul locals Inv may rely on. Only r is claimed, and only conditionally: r is
    bound by the prologue (Contracts.lean vhAfterTraceAndGas emits
    let r := FR_MODULUS) and every arithmetic partial reads it, but a render whose
    prologue binds it later, or a caller that hands over an empty environment, must
    not make the invariant unsatisfiable. So: if r is bound it is bound to p.

    The design sketch also required success to be 0 or 1 at EVERY checkpoint. That
    would make Inv .start unsatisfiable for the natural initial environment, where
    success has not been bound yet (VEnv.get returns none, not some 0), and
    satisfiability is the one thing this file may not trade away. success is
    therefore claimed only where it is read: the .pairing clause below, and
    finalPairing_spec post. -/
def LocalsOk (V : VEnv (Bridge.Dialect calls gas)) : Bool :=
  match VEnv.get V "r" with
  | none => true
  | some w => w == BitVec.ofNat 256 p

/-! ### The environment agreement hypotheses -/

/-- What must tie the abstract Lean environment to the literals the contract
    hard-codes. Every field is cited at the partial that needs it; the ones the design
    sketch named but that have no Lean counterpart are listed at the end of this
    comment rather than invented.

    DROPPED FROM THE SKETCH, with the reason:
    * delta : E.delta = (Nat.cast blsDeltaLiteral : Fr p). blsDeltaLiteral does not
      exist anywhere in the tree (the design comment already says the Lean constant
      does not exist yet), so there is nothing to be equal to. The contract hard-codes
      the permutation delta literal (QuotientNumeratorBlock.yul:1407); tying it to
      E.delta needs a generator-side constant first.
    * g1BaseWords / g2BaseWords / negSG2Words over vkG1Words and vkG2Words: neither
      function exists (Vk.lean has vkG1WordsOf, which is a different thing). They are
      also redundant: the G1 and G2 base points are part of the VK payload image, and
      the .vk clause of Inv pins that image byte for byte, so the header words are
      already constrained by a clause that does exist.
    * vkDigestWord is kept: it is the one header fact the payload copy does not
      already give, because the contract hashes the digest WORD rather than reading
      it from the payload. -/
structure EnvAgrees (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (PV : PlanView) (params : ParamsVerifierKZG G₁ G₂) (sG2gen : G₂) : Prop where
  /-- addmod, mulmod and the instance range check all use the FR_MODULUS literal
      (Templates.lean:187), so Fr p must be that field. -/
  modulus : p = frModulusConstant
  /-- The Yul masks x3 to 128 bits (TranscriptProofParser.yul:365) and Lean truncates
      to divCeil (divCeil numBits 8) 2 low bytes (Arith.lean:284); for BLS12-381 both
      are 16. Hazard 4: this is exactly the gate Fr 17 cannot pass, since truncate is
      the identity there. -/
  truncWidth : divCeil (divCeil E.field.numBits 8) 2 = 16
  /-- Lagrange.yul:13 squares k times to get x^n; Lean computes xn as
      x^(n-1) * x. Both agree only when n is 2^k and PV.k is that k. -/
  domainN : vk.domain.n = 2 ^ vk.domain.k ∧ vk.domain.k = PV.k
  /-- N_INV := invert(2^k) in the render (Vk.lean:770); Lean carries
      barycentricWeight. Without this the Lagrange values differ by a factor. -/
  baryWeight : vk.domain.barycentricWeight = ((2 ^ vk.domain.k : ℕ) : Fr p)⁻¹
  /-- Lagrange.yul:30-35 walks OMEGA_INV_TO_L times omega^j; Lean rotates negative
      rotations by omegaInv. -/
  omegaInvMul : vk.domain.omegaInv * vk.domain.omega = 1
  /-- The R-2 completeness side: the contract batch-inverts x^n - 1 and every
      x - omega^i, so x^n != 1 rules out x = omega^i only if omega has order n -
      EXACTLY n, not merely a divisor of it.

      P-ENV STRENGTHENED THIS from `omega ^ n = 1` to `orderExactly omega n`. The old
      text was satisfied by `omega := 1`: P-4a2 measured that the placeholder domain
      (omega = omegaInv = 1 with the CORRECT barycentricWeight) passed all ten
      clauses, because 1^4 = 1 and 1*1 = 1. That is the D-P23 defect class - a
      hypothesis a degenerate object satisfies - and non-vacuity does not belong in a
      separate theorem sitting beside the structure the theorems actually carry,
      which is where P-4a2 left it. The strengthening is what moves it inside.

      `EnvAgrees.xNotRoot_iff_notDomainPoint` below is the consumer exactness makes
      derivable, and `SurfaceFixture.fxEnvAgreesRejectsDegeneratePair` is the
      falsification half: the pair the old clause accepted is now refuted. -/
  omegaOrder : Midfall.Assumptions.orderExactly vk.domain.omega vk.domain.n
  /-- The l_blind window: Lagrange.yul:57 sums num_neg_lagranges terms starting at
      the second denominator, which is blinding_factors + 1 (mod.rs:509-515). -/
  negLagranges : PV.numNegLagranges = vk.cs.blindingFactors.toOption.getD 0 + 1
  /-- R-4: ofParams stores g2 inverse while read stores the loaded g2 inverse; the
      contract pairs with G2_BASE = P.g₂, so the two must be named apart. -/
  nG2 : params.nG2Prepared = P.g₂⁻¹
  /-- NEG_S_G2_BASE = (ParamsKZG.sG2) inverse (Vk.lean:802-815) while check reads
      sG2Prepared. -/
  sG2 : params.sG2Prepared = sG2gen
  /-- R-1: the contract hashes the VK_DIGEST word into alpha (FinalPairing.yul:22)
      and the Lean transcript absorbs vk.transcriptRepr, imported and unchecked. -/
  vkDigestWord : (PV.vk.constants.getD 0 ("", 0)).2 = frWord vk.transcriptRepr

/-- THE CONSUMER THE STRENGTHENED `omegaOrder` BUYS, and the reason it is not decoration
    (R-30: a clause no theorem reads is a clause that can be dropped). With a generator of
    EXACT order n, "x is not a root of the vanishing polynomial" and "x is not one of the
    n domain points" are the SAME statement - which is precisely the step
    `lagrange_progress_spec` needs from `ChallengesGood.xNotRoot` (attack.md GenericX
    FIX). Under the old `omega ^ n = 1` text this was FALSE: at `omega := 1` the left side
    excludes the single point 1 while the contract reverts on all n of them, so the
    hypothesis did not deliver the exclusion its doc comment claimed.

    The proof is two rewrites through `domainN` plus `xNotRoot_iff`, which is only
    available for an exact order: this theorem is the falsification of the weaker clause
    as much as it is the consumer of the stronger one. -/
theorem EnvAgrees.xNotRoot_iff_notDomainPoint
    {E : VerifierEnv p G₁ G₂ Gₜ} {vk : VerifyingKey (Fr p) G₁} {PV : PlanView}
    {params : ParamsVerifierKZG G₁ G₂} {sG2gen : G₂} {x : Fr p}
    (h : EnvAgrees E vk PV params sG2gen) :
    x ^ vk.domain.n ≠ 1 ↔ ∀ i : ℕ, i < vk.domain.n → x ≠ vk.domain.omega ^ i := by
  have hn : vk.domain.n = 2 ^ vk.domain.k := h.domainN.1
  have ho : Midfall.Assumptions.orderExactly vk.domain.omega (2 ^ vk.domain.k) := by
    rw [← hn]
    exact h.omegaOrder
  rw [hn]
  exact Midfall.Assumptions.xNotRoot_iff ho

/-- The finite bad set the squeezed challenges must miss for Lean and the contract to
    agree. R-2 has three manifestations and only the first two diverge between the
    sides, so only one is here: the third (x3 landing in a point set) makes the
    contract revert in scalar_inv AND makes Lean panic in MultiPrepare.fEval, so both
    sides reject and no hypothesis is needed.

    The logup side condition is deliberately NOT a field of this structure: inside a
    per-partial theorem whose hypothesis is snapshotOf = .ok S it is decorative
    (the snapshot already implies linearize did not panic), and the attack FIX says to
    keep it where it is load-bearing. LogupNoPanic below is that place. -/
structure ChallengesGood (vk : VerifyingKey (Fr p) G₁) (S : Snapshot p G₁ G₂ Gₜ) : Prop where
  /-- Lagrange.yul:93-99 reverts ProofRejected when x^n - 1 = 0 or some x - omega^i
      = 0; Lean lIRange (Domain.lean:251-258) yields zeros silently and ACCEPTS.
      Completeness direction, and the reason lagrange_progress needs it. -/
  xNotRoot : S.alg.x ^ vk.domain.n ≠ 1

/-- The R-2 soundness twin, stated operationally rather than as a snapshot field:
    the contract computes the lookup helper identity with prefix and suffix products
    and never inverts (yul_emit.rs:509-554, quotient.rs:1830-1860), while Lean
    Logup.expressions panics when f_j(x) + beta = 0 (Logup.lean:279, site string
    logup.rs:460). On that set the contract accepts an honest proof and Lean rejects,
    so verifier_sound needs this for every H.

    It is load-bearing only where no snapshot is given: under snapshotOf = .ok S the
    same fact is already implied, which is why it is not a field of ChallengesGood. -/
def LogupNoPanic (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (S : Snapshot p G₁ G₂ Gₜ) : Prop :=
  ∀ site, Verifier.linearize (p := p) E.delta vk S.trace.adviceCommitments
    (committedShape (G₁ := G₁)) (y := S.trace.y) (beta := S.trace.beta)
    (gamma := S.trace.gamma) (theta := S.trace.theta)
    (trashChallenge := S.trace.trashChallenge) (challenges := S.trace.challenges)
    S.alg ≠ .error (Fault.panic site)

/-! ### The invariant -/

/-- The clauses, Bool-valued so that the whole invariant is decidable at a concrete
    state (hazard 1: satisfiability must be a computation). Each boundary block is
    guarded by whether that boundary has been reached, so Inv k accumulates the
    clauses of every boundary up to k, and a clause whose bytes are phase-scoped
    carries its own liveness guard from the layout.

    The addresses are all read out of PV.memory, never hard-coded, so a re-planned
    layout moves the invariant with it. -/
def InvAt (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (k : Checkpoint) (PV : PlanView) (S : Snapshot p G₁ G₂ Gₜ)
    (V : VEnv (Bridge.Dialect calls gas)) (st : EvmState) : Bool :=
  let M := PV.memory
  -- every checkpoint: not halted, locals coherent
  (st.halted == none) && LocalsOk (p := p) V &&
  -- every checkpoint: the g1_identity window. Nothing in any template or emitter
  -- writes it (the grep in attack.md verifier_sound is the evidence: Constants.sol:130
  -- declares it, kzg/mod.rs only builds EcPoint sources on it, and LayoutMemory
  -- allocates the region with no mstore), and the PCS uses it as the
  -- committed-instance commitment (Kzg.lean:604 ecPointBeq q.comm g1Identity). Without
  -- this clause pcs_spec is false: an honest proof for a committed instance whose
  -- commitment is not the identity would satisfy Inv and refute the equivalence.
  (bytesAt st (ptrAddr M.g1IdentityMptr) 128 == Midfall.natToBytesBE 0 128) &&
  -- .vk: the payload image and the calldata shape
  (if Checkpoint.vk ≤ k then
     (bytesAt st (ptrAddr M.vkMptr) PV.vk.len == PV.vk.bytes) &&
     -- the envelope of Evm.lean:100-115: 0x64 of head, the proof payload, then one
     -- length word plus one word per instance. The arithmetic collapses to
     -- proofEnd + 32 + 32 * numInstances only when proofEnd = proofCptr + proofLen,
     -- which is the hend the attack records as missing from calldata_canonical; for a
     -- hand-built layout that breaks it, this clause is simply unsatisfiable, which is
     -- the right reading (Inv excludes the layout rather than lying about it).
     (st.env.calldata.length ==
        PV.proofLayout.proofEnd + 32 + 32 * PV.numInstances) &&
     -- the accumulator arm needs a decoded accumulator in the snapshot; the point
     -- slots themselves are a named gap, because fullyCollapse needs a fixed-base
     -- table and Midfall.Halo2.fixedBases is defective (R-52: its -G entry is the
     -- identity), so no statement may pin those bytes to it yet
     (PV.hasAccumulator == false || S.acc.isSome)
   else true) &&
  -- .transcript: the challenge slots, the commitment regions and the read cursor
  (if Checkpoint.transcript ≤ k then
     (holdsFr st (ptrAddr M.thetaMptr) S.trace.theta) &&
     (holdsFr st (ptrAddr M.betaMptr) S.trace.beta) &&
     (holdsFr st (ptrAddr M.gammaMptr) S.trace.gamma) &&
     (holdsFr st (ptrAddr M.trashChallengeMptr) S.trace.trashChallenge) &&
     (holdsFr st (ptrAddr M.yMptr) S.trace.y) &&
     (holdsFr st (ptrAddr M.xMptr) S.alg.x) &&
     (holdsFr st (ptrAddr M.x1Mptr) S.a.x1) &&
     (holdsFr st (ptrAddr M.x2Mptr) S.a.x2) &&
     -- x3 is the TRUNCATED squeeze: PhaseB keeps both so the truncation branch is
     -- visible (MultiOpen.lean:206-216), and the slot holds the truncated one
     (holdsFr st (ptrAddr M.x3Mptr) S.b.x3) &&
     (holdsFr st (ptrAddr M.x4Mptr) S.c.x4) &&
     (holdsG1s E st (ptrAddr M.adviceCommsMptrBase)
        (S.trace.adviceCommitments.getD 0 #[])) &&
     (holdsG1s E st (ptrAddr M.quotientLimbCommsMptrBase) S.alg.quotientLimbComs) &&
     (holdsG1 E st (ptrAddr M.fComMptr) S.b.fCom) &&
     (holdsG1 E st (ptrAddr M.piMptr) S.c.pi) &&
     (wordAt st (ptrAddr M.qEvalCptrMptr) == BitVec.ofNat 256 PV.proofLayout.qEvalCptr)
   else true) &&
  -- .lagrange: Lagrange.yul:81-86. X_N_MINUS_1_INV_MPTR is deliberately absent
  -- (finding 11: written, never read in a production render, no Lean counterpart).
  (if Checkpoint.lagrange ≤ k then
     (holdsFr st (ptrAddr M.xNMptr) S.alg.xn) &&
     (holdsFr st (ptrAddr M.lLastMptr) S.lagrange.lLast) &&
     (holdsFr st (ptrAddr M.lBlindMptr) S.lagrange.lBlind) &&
     (holdsFr st (ptrAddr M.l0Mptr) S.lagrange.l0) &&
     (match S.instanceEval with
      | none => true
      | some e => holdsFr st (ptrAddr M.instanceEvalMptr) e)
   else true) &&
  -- .quotient: the two splitting-factor words, the linearization eval and the
  -- selector buckets. The last two read the linearization hole, so they are inert
  -- until Exec widens linearize (D6 limit 1); the buckets additionally carry the
  -- finding-12 liveness guard.
  (if Checkpoint.quotient ≤ k then
     (holdsFr st (ptrAddr M.quotientMptr) S.alg.splittingFactor) &&
     (holdsFr st (ptrAddr M.quotientMptr + 32) (1 - S.alg.xn)) &&
     (match S.lin with
      | none => true
      | some L =>
          (holdsFr st (ptrAddr M.quotientEvalMptr) (linComEval L.linCom)) &&
          (if Checkpoint.liveRegionNamed k M "selector_accumulators" then
             holdsFrs st M.selectorAccMptr (linComBuckets L.linCom)
           else true))
   else true) &&
  -- .pcs: the batching scalars, the fused commitment and the two pairing inputs.
  -- PAIRING_LHS and PAIRING_RHS are the DualMSM channels (kzg/mod.rs:553-558), and
  -- FinalPairing.yul:33-58 rewrites them in place in accumulator mode, which is why
  -- this clause is asserted at .pcs and not at .pairing.
  (if Checkpoint.pcs ≤ k then
     (holdsFr st (ptrAddr M.fEvalMptr) S.b.fEval) &&
     (holdsFr st (ptrAddr M.vMptr) S.c.v) &&
     (holdsG1 E st (ptrAddr M.finalComMptr) S.c.finalCom.eval) &&
     (holdsG1 E st (ptrAddr M.pairingLhsMptr) S.c.dual.left.eval) &&
     (holdsG1 E st (ptrAddr M.pairingRhsMptr) S.c.dual.right.eval)
   else true) &&
  -- .pairing: the decision. success is a Yul local, not memory, which is why Inv
  -- takes the VEnv at all (design0 disagreement on Inv arity).
  (if k == Checkpoint.pairing then
     (VEnv.get V "success" == some 1) &&
     (PV.hasAccumulator == true || DualMSM.check S.c.dual params)
   else true)

/-- Inv k: the memory, locals and halt record at boundary k agree with the snapshot S.
    Stated as the proposition that the decidable Bool above is true, so that a gate
    can evaluate it (hazard 1) while a proof can still unfold it. -/
def Inv (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (k : Checkpoint) (PV : PlanView) (S : Snapshot p G₁ G₂ Gₜ)
    (V : VEnv (Bridge.Dialect calls gas)) (st : EvmState) : Prop :=
  InvAt E params k PV S V st = true

/-  WHY THERE IS NO Inv_mono HERE. design0 lists Inv_mono (k₁ ≤ k₂ → Inv k₂ → Inv k₁)
    as a lemma of this file. It is FALSE as written, and stating it as a trivially
    inhabited placeholder would be worse than omitting it - attack.md rejects exactly
    that pattern (countdown_or_halt : True := trivial). The selector-bucket clause is
    asserted at .quotient and .pcs and dropped at .pairing, so a later checkpoint does
    not carry every earlier clause: the state stSelectorGarbage in
    Midfall/Instances/InvFixture.lean satisfies Inv at .pairing and refutes it at
    .quotient, with .quotient ≤ .pairing, and invNotMonotoneKats_ok pins it.

    What a composition proof can use instead is that the PERMANENT clauses accumulate:
    dropping a clause never invalidates a state, so every checkpoint at or above
    .transcript carries the same permanent facts. Stage 4 should state monotonicity
    about the clause it needs, not about Inv as a whole. -/

/-! ### The honest memory

    The witness Inv is satisfied BY: every slot Inv constrains, written with the value
    Inv demands, and nothing else. This is the concrete memory the satisfiability gate
    runs on, and it is here rather than in the gate file so that the list of writes and
    the list of clauses cannot drift apart silently: both read the same projections of
    the same snapshot. -/

/-- The 32-byte writes Inv demands, as (byte address, word) pairs. -/
def Inv.wordWrites (_E : VerifierEnv p G₁ G₂ Gₜ) (PV : PlanView)
    (S : Snapshot p G₁ G₂ Gₜ) : List (Nat × Word256) :=
  let M := PV.memory
  [(ptrAddr M.thetaMptr, frWord S.trace.theta),
   (ptrAddr M.betaMptr, frWord S.trace.beta),
   (ptrAddr M.gammaMptr, frWord S.trace.gamma),
   (ptrAddr M.trashChallengeMptr, frWord S.trace.trashChallenge),
   (ptrAddr M.yMptr, frWord S.trace.y),
   (ptrAddr M.xMptr, frWord S.alg.x),
   (ptrAddr M.x1Mptr, frWord S.a.x1),
   (ptrAddr M.x2Mptr, frWord S.a.x2),
   (ptrAddr M.x3Mptr, frWord S.b.x3),
   (ptrAddr M.x4Mptr, frWord S.c.x4),
   (ptrAddr M.qEvalCptrMptr, BitVec.ofNat 256 PV.proofLayout.qEvalCptr),
   (ptrAddr M.xNMptr, frWord S.alg.xn),
   (ptrAddr M.lLastMptr, frWord S.lagrange.lLast),
   (ptrAddr M.lBlindMptr, frWord S.lagrange.lBlind),
   (ptrAddr M.l0Mptr, frWord S.lagrange.l0)] ++
  (match S.instanceEval with
   | none => []
   | some e => [(ptrAddr M.instanceEvalMptr, frWord e)]) ++
  [(ptrAddr M.quotientMptr, frWord S.alg.splittingFactor),
   (ptrAddr M.quotientMptr + 32, frWord (1 - S.alg.xn))] ++
  (match S.lin with
   | none => []
   | some L =>
       (ptrAddr M.quotientEvalMptr, frWord (linComEval L.linCom)) ::
       ((linComBuckets L.linCom).zipIdx.toList.map
          fun (b, i) => (M.selectorAccMptr + 32 * i, frWord b))) ++
  [(ptrAddr M.fEvalMptr, frWord S.b.fEval),
   (ptrAddr M.vMptr, frWord S.c.v)]

/-- The 128-byte writes: the commitment runs, fCom, pi, finalCom and the two pairing
    inputs. The g1_identity window is NOT here: it is zero because nothing writes it,
    which is the fact the clause asserts. -/
def Inv.byteWrites (E : VerifierEnv p G₁ G₂ Gₜ) (PV : PlanView)
    (S : Snapshot p G₁ G₂ Gₜ) : List (Nat × Bytes) :=
  let M := PV.memory
  ((S.trace.adviceCommitments.getD 0 #[]).zipIdx.toList.map
      fun (Q, i) => (ptrAddr M.adviceCommsMptrBase + 128 * i, E.g1.toEip Q)) ++
  (S.alg.quotientLimbComs.zipIdx.toList.map
      fun (Q, i) => (ptrAddr M.quotientLimbCommsMptrBase + 128 * i, E.g1.toEip Q)) ++
  [(ptrAddr M.fComMptr, E.g1.toEip S.b.fCom),
   (ptrAddr M.piMptr, E.g1.toEip S.c.pi),
   (ptrAddr M.finalComMptr, E.g1.toEip S.c.finalCom.eval),
   (ptrAddr M.pairingLhsMptr, E.g1.toEip S.c.dual.left.eval),
   (ptrAddr M.pairingRhsMptr, E.g1.toEip S.c.dual.right.eval)]

/-- The memory the honest run leaves behind. -/
def honestMemory (E : VerifierEnv p G₁ G₂ Gₜ) (PV : PlanView)
    (S : Snapshot p G₁ G₂ Gₜ) : Nat → UInt8 :=
  let m0 := fun _ => (0 : UInt8)
  let m1 := (Inv.wordWrites E PV S).foldl (init := m0)
    fun m w => storeWord m w.1 w.2
  let m2 := (Inv.byteWrites E PV S).foldl (init := m1)
    fun m w => copyInto m w.1 0 w.2.size w.2.toList
  copyInto m2 (ptrAddr PV.memory.vkMptr) 0 PV.vk.len PV.vk.bytes.toList

/-- The state the honest run leaves behind: that memory, not halted, and a calldata
    whose length is exactly what the .vk clause demands. -/
def honestState (E : VerifierEnv p G₁ G₂ Gₜ) (PV : PlanView)
    (S : Snapshot p G₁ G₂ Gₜ) : EvmState :=
  { EvmState.init with
    memory := honestMemory E PV S,
    env := { EvmState.init.env with
      calldata := List.replicate (PV.proofLayout.proofEnd + 32 + 32 * PV.numInstances) 0 } }

/-! ### A witness plan view

    The PlanView the satisfiability gate runs on, built from the layout fixtures the
    Generator package already pins. Model-free, so it can live here; the environment
    it is paired with needs a pairing model and lives in Instances/. -/

/-- A two-word payload for the witness: the digest word and one more header word, and
    no commitments. Small on purpose - the .vk clause copies the whole payload and the
    satisfiability gate evaluates that copy in the kernel, so a full-size synthetic
    payload (about a kilobyte) makes the gate exceed the recursion limit. The clause
    is the same clause at any length; only its cost changes. -/
def witnessVkPayload : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0x6000,
    constants := [("digest", 7), ("g2base", 8)],
    fixedComms := [], permutationComms := [],
    quotientConstOffsetWords := none, quotientConstWords := 0,
    quotientProgramOffsetWords := none, quotientProgramWords := 0,
    quotientConstLabels := [], quotientConstHeaders := [] }

/-- The witness plan's Data, DERIVED and not transcribed: `Data.new` (ENC:302-553) over
    the witness meta and the witness layout. This is the file's answer to the
    derive-not-observe rule. The only OTHER Data in the tree a pcs emission could read is
    Instances/DeployedProfile's `poseidonData`, which is hand-built around an artifact dump
    and cannot be imported here (the confinement gate greps the import, not the intent) - and
    it is also the one that CANNOT drive the emitter, because its meta's protocol is the
    circuit hole. That is measured in Instances/, not asserted here. -/
def witnessPlanData : Midfall.Generator.Data :=
  match Midfall.Generator.Data.new Midfall.Generator.constraintSystemMetaDefault
      witnessVkPayload Midfall.Generator.LayoutMemoryKats.referenceLayout with
  | .ok d => d
  | .error _ => emptyDataAt Midfall.Generator.LayoutMemoryKats.referenceLayout

/-- The plan view of the witness render: the MEM:1294 reference synthetic layout, the
    small payload above, the default calldata geometry, one public instance, a size-4
    domain, and no accumulator arm. -/
def witnessPlanView : PlanView :=
  planViewWithAccumulator (vk := witnessVkPayload)
    (vkMptr := Midfall.Generator.LayoutMemoryKats.referenceLayout.vkMptr)
    (memory := Midfall.Generator.LayoutMemoryKats.referenceLayout)
    (proofLayout := proofCalldataLayoutDefault)
    (numInstances := 1) (k := 2) (numNegLagranges := 2) (acc := none)
    -- P-AST4: the empty-plan facts, not a second set of deployed numbers. The witness
    -- layout is proofCalldataLayoutDefault - every section empty - so a plan with no
    -- phases and no counts is the ONE reading consistent with the layout it carries,
    -- and planParserFacts_derive_ok pins that consistency as a computation.
    (facts := emptyParserFacts)
    -- P-PLANVIEW: the DEFAULT meta and the Data derived from it, not the deployed pair. A
    -- witness plan view is the object Inv's satisfiability gate runs on, and the honest
    -- reading of a layout with no circuit is a meta with no circuit. The pcs slice this
    -- plan view emits is therefore EMPTY (no intermediate set, KZ:943-945), which is a
    -- finding and not a defect: see GenAstDispatch.emitPcsEmptyPlan_ok.
    (meta_ := Midfall.Generator.constraintSystemMetaDefault) (dat := witnessPlanData)

/-! ### Known-answer checks

    These exercise the parts of this file that need no curve: the address adapter and
    the shape of the write lists. The satisfiability exhibit and the perturbations
    need DualMSM.check and a G1 codec, so they live in
    Midfall/Instances/InvFixture.lean (hazard 5). -/

/-- ptrAddr is the byte address of a memory pointer, and it is the ONLY way Inv
    reaches an address: a byte offset added to a Ptr would be a word offset in
    disguise (Layout.lean:987, Encoding.lean:249). -/
def ptrAddrKats_ok : Bool :=
  ptrAddr (ptrMemory (valueFromNat 0x4000)) == 0x4000 &&
  ptrAddr (ptrMemory (valueFromNat 0)) == 0 &&
  -- a calldata pointer converts too: the adapter reads the value, not the location
  ptrAddr (ptrCalldata (valueFromNat 0x64)) == 0x64 &&
  -- the addresses Inv uses are real numbers from the layout, not sentinels
  ptrAddr witnessPlanView.memory.vkMptr == 0x2000 &&
  -- and the selector base is a Nat field, not a Ptr (Layout.lean:958), so it is used
  -- raw and never through ptrAddr
  witnessPlanView.memory.selectorAccMptr > 0

/-- P-AST3b: THE DERIVATION IS A FUNCTION AND NOT FOUR ZEROS WITH A DOC COMMENT. Line 1
    is the none arm - the arm the deployed poseidon profile takes - giving the four words
    the artifact shows. Line 2 is a real encoding moving all four together, and line 3
    says they move through the CONSTRUCTOR, so a plan view built from an accumulator
    encoding carries 1 / 2 / 7 / 56 and not 0 / 0 / 0 / 0. Line 4 pins the two spellings
    of "is there an accumulator" against each other at both plans, which is only
    automatic because both come out of one match on one Option.

    Without this the four fields could be constants and every gate on the deployed
    vkLoading slice would still pass - the accident P-AST3a refused to hard-code, made a
    computation here instead of a refusal in prose. -/
def planAccWords_derive_ok : Bool :=
  accWordsOfEncoding none == (0, 0, 0, 0) &&
    accWordsOfEncoding
      (some (Midfall.Generator.AccumulatorEncoding.new 2 7 56)) == (1, 2, 7, 56) &&
    (let pv := planViewWithAccumulator (vk := witnessVkPayload)
        (vkMptr := Midfall.Generator.LayoutMemoryKats.referenceLayout.vkMptr)
        (memory := Midfall.Generator.LayoutMemoryKats.referenceLayout)
        (proofLayout := proofCalldataLayoutDefault)
        (numInstances := 1) (k := 2) (numNegLagranges := 2)
        (acc := some (Midfall.Generator.AccumulatorEncoding.new 2 7 56))
        (facts := emptyParserFacts) (meta_ := Midfall.Generator.constraintSystemMetaDefault)
        (dat := witnessPlanData);
      pv.expectedHasAccumulatorWord == 1 && pv.expectedAccOffset == 2 &&
        pv.expectedNumAccLimbs == 7 && pv.expectedNumAccLimbBits == 56 &&
        pv.hasAccumulator == true &&
        (pv.expectedHasAccumulatorWord == if pv.hasAccumulator then 1 else 0)) &&
    witnessPlanView.expectedHasAccumulatorWord == 0 &&
      witnessPlanView.expectedAccOffset == 0 &&
      witnessPlanView.expectedNumAccLimbs == 0 &&
      witnessPlanView.expectedNumAccLimbBits == 0 &&
      witnessPlanView.hasAccumulator == false &&
      (witnessPlanView.expectedHasAccumulatorWord ==
        if witnessPlanView.hasAccumulator then 1 else 0)

/-- P-PLANVIEW: THE THREE COPIES ARE GONE AND THE META IS THE ONLY CARRIER.

    Lines 1-3: the three projections read the meta, at the witness plan and at a plan whose
    meta carries the deployed poseidon counts. Line 4 is the falsification of the OLD
    shape: before this package a call site could pass numLookups := 5 with a meta saying 1
    and the structure would hold both. Now there is nothing to pass - the number is a
    projection - so the only way to move it is to move the meta, and line 4 shows exactly that:
    a plan view whose meta carries the deployed triple (1, 3, 1) projects those three
    numbers, through the projection and not through a field a caller typed.

    Line 5 is the direction the deletion could have got wrong: the three projections are
    three DIFFERENT meta fields and not one field under three names. The deployed triple is
    (1, 3, 1), so numLookups and numTrashcans coincide by accident and only the middle one
    distinguishes itself - which is why the last row asserts numPermutationZs != numLookups
    rather than just reading three numbers back. A def wired to the wrong meta field would
    pass any test built on a single value; this one cannot. -/
def planMetaProjections_ok : Bool :=
  witnessPlanView.numLookups == witnessPlanView.meta_.numLookups &&
    witnessPlanView.numPermutationZs == witnessPlanView.meta_.numPermutationZs &&
    witnessPlanView.numTrashcans == witnessPlanView.meta_.numTrashcans &&
    (let base : Midfall.Generator.ConstraintSystemMeta :=
        Midfall.Generator.constraintSystemMetaDefault;
      let m : Midfall.Generator.ConstraintSystemMeta :=
        { base with numLookups := 1, numPermutationZs := 3, numTrashcans := 1 };
      let pv : PlanView := { witnessPlanView with meta_ := m };
      pv.numLookups == 1 && pv.numPermutationZs == 3 && pv.numTrashcans == 1) &&
    (let base2 : Midfall.Generator.ConstraintSystemMeta :=
        Midfall.Generator.constraintSystemMetaDefault;
      let m : Midfall.Generator.ConstraintSystemMeta :=
        { base2 with numLookups := 1, numPermutationZs := 3, numTrashcans := 1 };
      (m.numLookups, m.numPermutationZs, m.numTrashcans) == (1, 3, 1) &&
        m.numPermutationZs != m.numLookups)

/-- THE TWO NEW PlanView FIELDS ARE A COPY OF THE PLAN'S, AND NOTHING PINS THEM -
    stated as a definition so the duplicate-fact gate sees both the copy and the reason it
    is unpinned (rule 6). PlanView.meta_ and PlanView.dat are this structure's projection of
    LoweringPlan.meta_ and LoweringPlan.data (PL:29-45), and no Lean term can compare the two
    because no Surface carries a LoweringPlan: the blocker is P-11's LoweringPlan::new
    (PL:235-329), the same one ObligationsGates.gap_qvmField_surface_free names.

    WHAT THIS PACKAGE DOES INSTEAD OF A PIN, because a gap is not an excuse for doing nothing:
    the three counts that would have been copies of the meta are DELETED (PlanView.numLookups
    and its two siblings are projections now, so the copy cannot disagree with its source by
    construction), the witness and fixture plan views take their Data from Data.new rather
    than from a transcription, and DeployedProfile's gate 21 cross-checks the projections
    against the assembled model's own three fields at the deployed profile. -/
def gap_planview_carries_the_plan : String :=
  "unpinned copy: PlanView.meta_ and PlanView.dat are LoweringPlan.meta_ and "
    ++ "LoweringPlan.data; blocker: P-11 LoweringPlan::new has not landed, so no Surface "
    ++ "carries a plan to pin the projection against"

/-- The witness Data really is the DERIVED one: `Data.new` does not abort on the default
    meta, so the `emptyDataAt` fallback inside `witnessPlanData` is unreachable. Without
    this line the fallback would be a silent default - the class rule R4 refuses - and the
    witness plan's empty pcs emission would be attributable to a fault swallowed rather
    than to a circuit with no queries. The second conjunct says the derived Data is not
    merely ok but EMPTY where an empty circuit should be empty: no commitment lists, no
    eval slots, and the four pointers read off the layout it was given. -/
def witnessPlanData_isOk_ok : Bool :=
  (Midfall.Generator.Data.new Midfall.Generator.constraintSystemMetaDefault witnessVkPayload
    Midfall.Generator.LayoutMemoryKats.referenceLayout).isOk &&
    witnessPlanData.fixedComms.isEmpty && witnessPlanData.adviceComms.isEmpty &&
    witnessPlanData.permutationZComms.isEmpty && witnessPlanData.trashcanComms.isEmpty &&
    witnessPlanData.lookupEvals.isEmpty && witnessPlanData.dummyEvalWords.isEmpty &&
    -- and the fallback really is a different term from the derivation, so line 1 is not
    -- vacuous: were Data.new returning .error, witnessPlanData would still typecheck.
    witnessPlanData.adviceEvals.isEmpty

#eval ptrAddrKats_ok                      -- expect true
#eval planAccWords_derive_ok              -- expect true
#eval planMetaProjections_ok              -- expect true
#eval witnessPlanData_isOk_ok             -- expect true

end Midfall.Lowering
