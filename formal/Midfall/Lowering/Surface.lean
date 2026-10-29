-- |
-- Midfall.Lowering.Surface
--
-- P-SE stage 4, file 1 of 2 (docs/plans/P-SE-stage4.md file row 1; design2.md
-- section "Midfall.Lowering.Surface.Surface"; design0.md section
-- "Midfall.Lowering.DeploymentW"; P-SE-semantic-equivalence.md section M).
--
-- WHAT THIS FILE IS FOR. Stage 3 built the per-checkpoint invariant (Inv.lean) and
-- the values it relates memory to (Snapshot.lean), and reported that none of the
-- seven per-partial theorems could be written, because there was no name for the
-- block a partial runs, no name for the render those theorems quantify over, and no
-- name for the deployment they assume. This file supplies those three things under
-- the names the frozen Lowering/Types.lean could not carry: Types.lean keeps
-- Supported and Deployment as placeholders so Statements.lean keeps elaborating, and
-- P-SE may not edit it, so the real ones are SupportedS and DeploymentW - the naming
-- choice design2 hazard 8 records.
--
-- FOUR DELIBERATE DEVIATIONS FROM THE DESIGN SKETCHES: the first three were forced
-- by attack.md rather than chosen for convenience, and the fourth is the R-58 repair.
--
--   1. THERE IS NO Supported FIELD ON THE RECORD. design2 carried
--      "Supported : RenderOptions -> Prop" as data, and attack.md marks the whole
--      LoweringCorrect structure VACUOUS for exactly that reason: a record whose
--      Supported is a free field admits { Supported := fun _ => False }, and then
--      every theorem above it is true because its hypothesis is unsatisfiable. Here
--      SupportedS is a STRUCTURE OVER REAL SURFACE DATA - vk, cfg, plan, E, the
--      render options - so the only way to make it unsatisfiable is to make the
--      verifier itself unsatisfiable, which is the point. The one abstract slot that
--      survives was qvmValidated, named as the field the QVM area owns; R-58 F4
--      deletes it (see deviation 4).
--
--   2. THERE ARE NO CODEC FIELDS. design2 carried repackProof, encodeCalldata and
--      decodeCalldata as Surface data because P-12 had not landed. It has:
--      Lowering/Calldata.lean:186, :241 and :328 define all three concretely over
--      (proofLayout, numInstances, E.g1). A free copy of a function that exists is a
--      field the Surface can lie about, and the pins that would tie it down (hRepack,
--      hEncode, hProofLayout in the sketch) are P-12 deliverables that no statement
--      in this package consumes. So LeanAccepts calls the real decoder, and the three
--      fields plus their three pins are absent. Reported, not hidden.
--
--   3. hoisted, render, print, EvaluatorFrame, FrameWellFormed and tokenBase are
--      ABSENT, and shell_unfolds - absent when stage 4 landed - NOW EXISTS as a real
--      equation (R-58 F3, deviation 4 below). hoisted duplicates what mainScope
--      derives from S.L.main (design0: hoisted funs = hoist S.main :: outer), so
--      one of the two is
--      decoration. render and print exist only for render_eq_print, whose text
--      conjunct attack.md proves FALSE under a pretty-printer and TAUTOLOGICAL under
--      print defined as whatever render emits; the surviving conjunct needs stmtsBeq,
--      which is cited in Generator/Templates.lean prose as the authoritative AST
--      equality (D-P13) but has NO declaration anywhere in the tree - grep for
--      "def stmtsBeq" is empty, so the conjunct cannot be written yet - and R-58 F8
--      shows the surviving conjunct was itself a vacuity, so render_eq_print is now the
--      astOfMain/lower link instead (Obligations.lean). EvaluatorFrame and
--      FrameWellFormed need a quotient frame length on PlanView (sketch name qext),
--      which stage 3 did not define because nothing in
--      Exec exposes one; the QVM area has tokenBases (LoweringPlan.lean:1216) over
--      QuotientMem, which is a different object from the sketch's
--      tokenBase : VerifierMemoryLayout -> Nat -> Nat. Each is reported in the stage-4
--      findings as a sketch name that does not resolve.
--
--   4. R-58 (docs/REVIEW.md) found that the record still carried COPIES of facts the
--      Rust derives once with nothing relating them, which is the vacuity class in the
--      generalisation at the end of that entry. Five pin fields are added below, each
--      named plan_*, evaluator_agrees, encG2_eip or shell_unfolds so a gate can find
--      them: shell_unfolds (F3, the pin that makes RunShell and RunVerifier be about
--      ONE program - without it the lowering_equivalence sketch hint was false as
--      written), plan_hasAccumulator (F2, hasAccumulator was a free Bool, so 11 of the
--      13 PartialSpecs fields discharged on a one-Bool lie), plan_numInstances and
--      evaluator_agrees (F6, the same class twice more), and encG2_eip (G2, which pins
--      the abstract G2 encoder to the EIP-2537 validator instead of letting it be any
--      function at all). qvmValidated is DELETED (F4): a Prop field no Surface
--      construction can fail is decoration, and the QVM obligation that can fail is
--      LoweringCorrect.qvm_validated_noBoundsFault, which quantifies over a real
--      LoweringPlan and its real validator. scripts/check_duplicate_facts.py is the
--      gate against the class: it asserts each copied fact is either single or has a
--      named pin mentioning both sides.
--
--   5. R-60 (docs/REVIEW.md, the second statement pass) changed four more things in
--      this record, and the header says so because each one is a field a reader would
--      otherwise take on trust:
--        * irCheck is GONE AS A FIELD and is now a PROJECTION of runtimeName
--          (Surface.irCheck). The free field let the fixture's check hard-code its own
--          naming convention, so the gate on the headline hypothesis disagreed with the
--          run relation - S1, the blocking defect of that pass. Deleting the copy is
--          stronger than pinning it: there is now one naming function on the record.
--        * evaluator_agrees was strengthened from the isSome agreement to the runtime
--          BLOCK equation (S3), because Object.codeBlock has been in the vendored API
--          all along and the comment claiming otherwise was false.
--        * encG2_eip is renamed encG2_shape (S4). The statement is unchanged; the name
--          was overclaiming, since a constant encoder satisfies it and the fixture uses
--          one. What it does NOT claim - Function.Injective encG2 - is a named gap the
--          fixture cannot meet, recorded at the field and in ObligationsGates.
--        * memoryguardOk now FAILS on a runtime that installs no free-memory pointer
--          (S7). The old def answered true for the empty prologue, which made
--          DeploymentW.memguard satisfiable by shipping nothing; transcriptMptr and
--          headGuardThreshold are the single threshold the byte bound and the AST guard
--          are both compared against, and gap_shell_code_vs_layout_code records the
--          copy that still cannot be pinned (no Yul-to-bytecode compiler in the tree).
--
-- THE BLOCKER, DECIDED RATHER THAN WORKED AROUND: memguard. attack FIX 32 requires
-- DeploymentW to bound the free-memory pointer, and D-P15 recorded that memoryguard
-- and setimmutable were absent from the vendored dialect - measured at the time, and
-- since closed by P-VEND (9fe74f9), which added the ops and the memoryguard Step rule;
-- the historical re-measurement is kept because it is what the stage-4 decision turned
-- on. At the time it was:
-- zero occurrences of either word in
-- vendor/yul-semantics/YulSemantics/Dialect/EVMOp.lean, whose parse (EVMOp.lean:173)
-- maps names to the closed Op enum and falls through to none, so a memoryguard call
-- elaborates to a USER CALL (mkCall, EVMOp.lean:216) with no Step derivation. The
-- route taken is the named gap, and the gap is NARROWER than the sketch assumed: the
-- bound itself is nameable today, because Generator/Evm.lean:129 reads the
-- free-memory-pointer initialiser out of the deployed runtime BYTES (PUSH1 v or
-- PUSH2 v_hi v_lo, optional DUP1, then PUSH1 0x40 MSTORE), which is exactly what solc
-- compiles the prologue store into. So memguard below is a real decidable Prop over
-- the shell runtime, not True: it is satisfiable (the fixture exhibits it) and
-- refutable (a 0x2000 prologue refutes it, and memoryguardKats_ok pins that). What
-- the vendor edit still blocks is the AST-level form, i.e. importing the via-ir object
-- so that RunContractIR and ir_refines can run it at all. That is M8 work, it is
-- recorded at the field, and nothing in this package is unsatisfiable because of it.
--
-- WHAT IS NOT HERE. blk and the per-partial obligations (Partials.lean), the
-- invariant (Inv.lean), and the fixture Surface with its non-vacuity exhibits
-- (Instances/SurfaceFixture.lean). The fixture cannot live here: the record needs an
-- AdmissiblePairing, the only model in the tree is in Instances/, and the confinement
-- gate keeps that import out of any file that states theorems (hazard 3).

import Midfall.Lowering.Inv
import Midfall.Lowering.Types
import Midfall.Lowering.Calldata
import Midfall.Lowering.Accumulator
import Midfall.Yul.Bridge
import Midfall.Yul.Contracts
import Midfall.Assumptions.Eip2537
import Midfall.Generator.Api
import Midfall.Generator.Models
import Midfall.Generator.Evm
import YulSemantics.Object
import YulSemantics.ObjectRun
import YulSemantics.Contract

namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ### The surface -/

/-- An EIP-2537 G2 encoding: 256 bytes that decode to a point PAIRING_CHECK accepts.
    Decidable, and it is the only thing the abstract encoder can be pinned to without a
    G2 codec in Common (there is none: the generator goes through VkPointCodecs, which
    sits behind Instances/ExponentModel - D-P17). The all-zero 256-byte word is the
    EIP-2537 infinity encoding and passes; the empty byte string - what the fixture
    used before R-58 G2 - does not, and encG2Kats_ok pins both halves. -/
def encG2IsEip (b : Bytes) : Bool :=
  b.size = Midfall.Yul.g2Bytes &&
    match g2Of? b with
    | some pt => g2PointValid pt
    | none => false

/-- Everything PLAN 9.5 names that the port does not produce yet, as DATA over the
    types that do exist, plus the two pins that keep the obligations above it from
    being vacuous (P-SE decision D2): o0, the render options the lowered program came
    from, and lower_ok, which says so.

    A theorem stated over S : Surface becomes a theorem about the deployment the day a
    realSurface is built from the P-11 plan, the P-12 codecs and the P-13 ASTs. Until
    then the fields are functions and records the statements consume, not propositions
    a proof could pick to make itself true - which is the difference between this
    record and the one attack.md marks VACUOUS.

    blk is the field stage 3 reported as missing, and the field R-62 found the ten
    *_spec theorems were FALSE ABOUT. It used to be a free function whose only constraint
    was main_concat, and since L.main comes from the free lower, a Surface could plant any
    block at all - 'return(0, 0)' for finalPairing - satisfy every hypothesis and refute the
    conclusion.

    P-AST (docs/plans/P-AST.md) closed that from the generator side: Midfall/Lowering/
    GenAst.lean now returns a real Yul AST for FinalPairing and for the two AssemblyHelpers
    definitions it calls, checked against the text port under the token comparator, and
    Lowering/Partials.lean's BlkIsEmitter pins blk to it as a hypothesis of each spec
    theorem. P-AST2 added Lagrange and TraceReturn, so four of the seven partials are still
    placeholders in that emitter, and the pin is
    what makes those nine theorems well-posed rather than about-every-program; the text
    renders (VerifierPartials.lean really does return String) stay what D-P25 calls them: a
    Lean-side reference, not the deliverable. -/
structure Surface (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ] where
  -- the verifier side: PLAN 9.5 g
  E : VerifierEnv p G₁ G₂ Gₜ
  params : ParamsVerifierKZG G₁ G₂
  vk : VerifyingKey (Fr p) G₁
  cfg : GeneratorConfig
  /-- The contract positive-base table (artifacts.rs:181-245), NOT Exec fixedBases,
      whose -G entry is the identity (R-52, a live Exec-row defect). Every statement
      that needs a table takes it from here. -/
  accFixedBases : Array (AccFixedBase G₁)
  /-- The VK_DIGEST word the contract hashes into alpha (Vk.lean:763). A field rather
      than a projection because computing it needs Generator.Vk, which pulls in
      Instances/ExponentModel (D-P17); vkDigest_spec below is the link. -/
  vkDigest : Word256
  /-- The G2 point NEG_S_G2_BASE is the inverse of, and the abstract G2 encoder.
      Common has no G2 codec, and the generator embeds g2ToU256s after the VK codecs
      (Vk.lean:331). Eip2537.Holds is stated over exactly this pair. -/
  sG2gen : G₂
  encG2 : G₂ → Bytes
  -- the lowered program: PLAN 9.5 L, and the render it came from
  o₀ : RenderOptions
  L : Lowered
  /-- The render function. Abstract because the AST emitter (GenAst.lean) covers three
      partials of seven, so no Lean function yet produces a whole Lowered from RenderOptions;
      lower_ok is what makes o₀ the options this L came from. -/
  lower : RenderOptions → Except Midfall.Generator.GeneratorError Lowered
  lower_ok : lower o₀ = .ok L
  /-- The constant-substituted locals block (R-37: produced with fuel, because the
      substitution rewrites free Solidity constants into literals, and an unbounded
      walk over a generated block is not something to trust). -/
  bindLocals : YulBlock
  /-- The shell model. Before R-58 F3 the doc said "the solc dispatcher wrapping
      headGuard ++ bindLocals ++ main", and nothing in the tree made that true: the
      shell was a free YulObject and shell.codeBlock occurred at exactly one site, so
      RunShell, RunVerifier and RunContractIR were about three unrelated programs.
      shell_unfolds below now states the wrapping as an equality, which is what every
      Surface in the tree actually is - a MODEL of the entry path, not the dispatcher.
      A real solc dispatcher does not satisfy the equality (it decodes ABI heads and
      tests the selector first), so when M8 imports the via-ir object this pin must be
      restated as design2 had it: the verifyProof ARM of shell runs headGuard ++
      bindLocals ++ main from the dispatcher memory. Recorded, not hidden. -/
  shell : YulObject
  /-- The shell runtime layout: code, the data maps, and the immutable map that
      loadimmutable reads (EVMExec.lean:793 routes it through env.immutable, which is
      why DeploymentW can pin AUTHORIZED_VK at all). -/
  shellLayout : EVM.Layout
  /-- The standalone quotient evaluator, when the render externalises it: its runtime
      block and layout, used by Surface.calls to answer the staticcall that
      QuotientAndLinearization.yul:35 makes. -/
  evaluatorRuntime : Option (YulBlock × EVM.Layout)
  /-- solc names a runtime sub-object "name_id_deployed"; which one is a deployment
      fact rather than a property of the AST, so the naming function is a field.

      R-60 S1: this is the ONLY place the runtime's name is carried. `Surface.irRuntime`
      and `Surface.irCheck` are both projections of it, so the check cannot drift away
      from the run relation the way a second copy did before the repair. -/
  runtimeName : String → String
  -- the per-partial API
  /-- The AST of the rendered main block, for the D-P15 re-quote gate: the plan sketch
      had render and print too, and attack.md proves the text conjunct they existed for
      is FALSE under a pretty-printer and TAUTOLOGICAL under print defined as whatever
      render emits, so only the AST accessor survives. A Surface whose astOfMain returns
      none for every option is refuted by the fixture gate, not by a doc comment. -/
  astOfMain : RenderOptions → Option YulBlock
  /-- THE FIELD STAGE 3 COULD NOT NAME. The Yul block of one partial under one plan
      view. It takes the PlanView because the partials are generated FROM the plan:
      the same partial at two different layouts is two different blocks, and a blk
      that ignored PV would let one theorem speak about a block no render emits. -/
  blk : Partial → PlanView → YulBlock
  plan : PlanView
  -- the codehash and runtime images the deployment pins
  /-- none is the embedded-VK render (VkLoading.yul:22-53), which reads no code at
      all; every code field below is conditional for exactly that reason. -/
  expectedVkCodehash : Option Word256
  quotientRuntime : Option Bytes
  expectedQuotientCodehash : Option Word256
  -- pins: hypotheses about the data above, not new data
  /-- The link that makes vkDigest the contract word rather than a free literal.
      Discharged by feToU256_frToRepr (Lowering/VkDigest.lean:69) once the digest is
      read out of the VK payload; until then it is a pin, and a wrong constant fails
      it. -/
  vkDigest_spec : vkDigest = frWord vk.transcriptRepr
  /-- EXPECTED_VK_LENGTH is the payload length plus the 0xfe deployment prefix
      (VkLoading.yul:64-74 compares extcodesize to len + 1 and copies from byte 1),
      so the runtime image and the payload image are two different byte strings and
      the link between them has to be stated. -/
  vkRuntime_spec : L.vkRuntime =
    ByteArray.append (ByteArray.mk #[0xfe]) plan.vk.bytes
  /-- The seven partials tile the TAIL of the main block, in include order
      (Halo2Verifier.sol:217-229). This is what stops blk from being a free function:
      whatever it returns, that concatenation has to be the end of the program the
      render produced.

      FINDING 5, THE PLAN STATES THIS AS AN EQUALITY AND THE EQUALITY IS FALSE. The
      sketch writes L.main = blk .vkLoading ++ ... ++ blk .traceReturn with no prefix.
      But design0 own hazard for Partials.lean says the AssemblyHelpers definitions -
      fail, scalar_inv, squeeze_to, batch_invert, ec_pairing,
      validate_public_accumulator - "live at the top of the main assembly block", which
      is why mainScope hoists S.L.main rather than the slice. If the helper definitions
      are inside main, main is not the concatenation of the seven slices; it has a
      prefix. And the exact prefix is not knowable yet: each included file interleaves
      its own function definitions with its own statements, and P-13 has not landed the
      AST emitter, so nobody can say whether the prefix is one helper block or seven
      fragments. So the pin is stated existentially: the seven slices tile the tail, and
      the helper prefix is a named gap that P-13 will turn into a computation. Weaker than the
      sketch, and true; the sketch version would have been a pin no real render
      satisfies, which is the unsatisfiable-hypothesis failure mode in the other
      direction. -/
  main_concat : ∃ (helpers : YulBlock), L.main =
    helpers ++ blk .vkLoading plan ++ blk .transcriptParser plan ++ blk .lagrange plan ++
      blk .quotientLin plan ++ blk .pcs plan ++ blk .finalPairing plan ++
      blk .traceReturn plan

  /-- R-58 F3, THE PIN THAT MAKES THE THREE RUN RELATIONS BE ABOUT ONE PROGRAM.
      RunVerifier runs L.headGuard ++ bindLocals ++ L.main, RunShell runs
      shell.codeBlock, and before this field nothing related them: shell.codeBlock
      occurs at exactly one site in the tree, so a Surface could hand RunShell any
      program at all and every field of LoweringCorrect that mentions a shell run was
      about a program no render emits - which is why the lowering_equivalence sketch
      hint ("transport each field through hc.ir_refines") was FALSE as written.
      With this equation the two runs differ only in the entry memory: callState is
      initState at (fun _ => 0), so a shell run is a verifier run at zeroed memory.
      Stated as an equality rather than as the sketch's True, which attack.md rejects
      as a pattern (countdown_or_halt : True := trivial). It can fail: the fixture
      exhibits it and SurfaceFixture.shellPinsKats_ok shows that a shell whose code
      block is only the main block refutes it. See the shell field for why the equality is the right
      form for a MODEL and what M8 has to restate it to. -/
  shell_unfolds : shell.codeBlock = L.headGuard ++ bindLocals ++ L.main

  /-- R-58 F2, the free Bool. PlanView.hasAccumulator is a copy of a fact the Rust
      derives once: expected_has_accumulator IS accEncoding.isSome (Vk.lean:782 renders
      the header word as "if inputs.accEncoding.isSome then 1 else 0"). Nothing in the
      tree compared the copy to the source, so Inv .vk's (PV.hasAccumulator == false ||
      S.acc.isSome) and Inv .pairing's (PV.hasAccumulator == true || DualMSM.check ...)
      could both be steered by a one-Bool lie, and every PartialSpecs field that takes
      hacc : S.plan.hasAccumulator = false discharged on it - the copy, not the
      configuration, decided whether the no-accumulator arm was available. -/
  plan_hasAccumulator : plan.hasAccumulator = cfg.accumulator.isSome

  /-- R-58 F6, first half. PlanView.numInstances is Inv's copy of the calldata tail
      length (the .vk clause of Inv uses it for the calldata envelope) and cfg.numInstances is the
      generator's; decodeCalldata is called with the cfg one and Inv with the plan one,
      so an unequal pair describes a verifier whose decoder and memory invariant
      disagree about how many instance words the calldata carries. -/
  plan_numInstances : plan.numInstances = cfg.numInstances

  /-- P-AST3b, THE FOUR ACCUMULATOR WORDS PINNED TO THEIR SOURCE. PlanView now carries
      expectedHasAccumulatorWord, expectedAccOffset, expectedNumAccLimbs and
      expectedNumAccLimbBits because VkLoading.yul:105-110 cross-checks the loaded VK
      header against them, and the Rust derives those four ONCE from the accumulator
      encoding (Vk.lean:782-791, and Artifacts.lean's accExpectationsOf at ART:229-245).
      Four copies of one fact is the R-58 F2 / F6 class, so the pin is stated as one
      equation over the tuple: the four fields ARE accWordsOfEncoding cfg.accumulator -
      the same function planViewWithAccumulator applied, now read back off the
      configuration the render was built from. A plan claiming offset 7 while cfg says
      none refutes it, and SurfaceFixture.planAccExpectationsKats_ok exhibits both the
      agreement and the refutation. Registered as the accExpectations family in
      scripts/check_duplicate_facts.py and fingerprinted in
      scripts/check_statement_fingerprints.py. -/
  plan_accExpectations :
    (plan.expectedHasAccumulatorWord, plan.expectedAccOffset,
     plan.expectedNumAccLimbs, plan.expectedNumAccLimbBits) =
      accWordsOfEncoding cfg.accumulator

  /-- R-58 F6, second half: the dead/live evaluator pair. Lowered.evaluator is the
      render's Option YulObject and Surface.evaluatorRuntime is the deployment's
      Option (YulBlock x EVM.Layout) that Surface.calls actually answers with; nothing
      read L.evaluator at all, so a render that externalised no evaluator could still
      deploy one (and the reverse).

      R-60 S3: THIS IS NOW THE CONTENT EQUATION, NOT THE isSome HALF. The previous form
      (`L.evaluator.isSome = evaluatorRuntime.isSome`) was defeated because the types
      differ only in the LAYOUT, and `Object.codeBlock` has been in the vendored API
      all along - `Surface.irRuntime` two paragraphs below already uses it, so the
      comment claiming the block half was "not nameable today" was false. The layout is
      still not derivable from the object (that is the P-13 AST emitter), so what is
      pinned is the RUNTIME BLOCK: the block the render's evaluator object carries is
      the block the deployment answers staticcalls with. A render that externalised one
      evaluator and deployed another now fails here instead of agreeing on isSome. -/
  evaluator_agrees : L.evaluator.map YulSemantics.Object.codeBlock =
    evaluatorRuntime.map Prod.fst

  /-- R-58 G2, RENAMED encG2_eip -> encG2_shape BY R-60 S4, and the rename is the
      honest part of the repair: the statement is UNCHANGED, the name was overclaiming.
      encG2 is an abstract G2 -> Bytes function, and Eip2537.Holds is stated over it
      (its g2Valid clause is exactly this claim, one forall higher), so an unconstrained
      encoder makes every Holds hypothesis unsatisfiable and every field that carries
      one vacuous. The fixture had encG2 := fun _ => Bytes.empty, which fails
      encG2IsEip, so NO Holds was satisfiable at the only Surface in the tree. This pin
      forces the encoder's OUTPUT to be EIP-2537-shaped and precompile-valid for every
      point, which is what the old fixture could not do.

      WHAT IT DOES NOT CLAIM, stated because the review found a constant function
      satisfies it and the fixture USES one (`fun _ => bytesZero g2Bytes`, the EIP
      infinity encoding): it does not say encG2 is a codec. The strengthening it does
      not make is `Function.Injective encG2` - distinct points, distinct encodings -
      and the fixture CANNOT meet it, so it is not added here: adding a pin the only
      Surface in the tree fails would either force a fake encoder or break the exhibit,
      and pretending the pin is satisfied is how R-58 G2 got oversold. It is recorded as
      a NAMED GAP with that blocker instead. A second gap behind it: even an injective
      encoder is not the contract's encoder until encG2 P.g₂ is pinned to the 256 bytes
      the render embeds at the G2_BASE slot, which needs the header slot layout from the
      P-11 plan that PlanView does not carry (D-P17). SurfaceFixture.encG2AtFixture_ok
      exhibits the constant that satisfies this pin, so the limitation is a computation
      in the tree and not a paragraph. -/
  encG2_shape : ∀ R : G₂, encG2IsEip (encG2 R) = true

/-! ### Supported -/

/-- The codec-side readability of one embedded G1 point, factored out so the forall in
    vkPoints stays readable: the EIP-2537 bytes parse, and what they parse to is a
    point the MSM precompile accepts rather than a non-canonical word. Both halves are
    computable (Externals.lean:476, :512), so a gate can point at the one that fails. -/
def ptReadable (b : Bytes) : Prop :=
  ∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true


/-- PLAN 9.5 Supported, the real one, over Surface DATA rather than over free fields
    (deviation 1 in the header). D-P18, adopted as D3, fixes the layout field as
    WellFormed AND validate = .ok (), and both halves are decidable:
    LayoutMemory.lean:869 decides them for the poseidon layout.

    What is NOT here, with the reason:
    * PLAN qvm is ABSENT (R-58 F4). It was S.qvmValidated, a Prop field the fixture
      discharged with True, i.e. a field no Surface could fail. The QVM obligation that
      can fail is LoweringCorrect.qvm_validated_noBoundsFault, which quantifies over a
      real LoweringPlan and the real LoweringPlan.supportedQvm validator.
    * The column-count arithmetic is stated through vk.cs and cfg rather than through
      the plan, because PlanView carries only the counts Inv reads.
    * instShape carries numCommittedInstances = 1 as well as two instance columns: the
      attack end_to_end_noAcc entry shows Lean accepts ANY instance length, so the
      shape the render assumes has to be an assumption rather than a coincidence. -/
structure SupportedS (S : Surface p G₁ G₂ Gₜ) (o : RenderOptions) : Prop where
  /-- rust: try_new rejects a circuit with no advice columns (API:597-599). -/
  advice : S.vk.cs.numAdviceColumns ≠ 0
  /-- Exactly two instance columns, one of them committed (API:601-608). -/
  instShape : S.vk.cs.numInstanceColumns = 2 ∧ S.cfg.numCommittedInstances = 1
  /-- The no-rotation instance shape the parser assumes: every instance query is at
      rotation 0, which is what makes INSTANCE_EVAL a single word. cur and value 0
      both denote 0, so the test is on the int. -/
  noRotInst : ∀ q ∈ S.vk.cs.instanceQueries.toList, q.2.int = 0
  /-- D-P16: the accumulator encoding is the GENERATOR one, and the validator that
      runs over it is validateForNumInstances. Vacuous when the render has no
      accumulator, which is the primary case. -/
  acc : ∀ enc, S.cfg.accumulator = some enc →
    (enc.validateForNumInstances S.cfg.numInstances).isOk = true
  /-- Multi-phase circuits are out of scope (plan Section 13). -/
  singlePhase : S.vk.cs.numChallenges = 0
  /-- Assessment F7: the quotient limb count is degree - 1, which is what the limb
      loop in the parser and the splitting-factor arithmetic both assume. -/
  hLimbs : S.vk.domain.getQuotientPolyDegree = S.vk.csDegree - 1
  /-- Every G1 point the render embeds must round-trip through the codec and be a
      point the MSM precompile accepts. Stated over ENCODINGS, because the contract
      sees bytes: an off-curve word in the payload is a deployment bug the contract
      finds later or not at all, and the codec is the only thing that ties the payload
      to a group element. -/
  vkPoints : ∀ C ∈ S.vk.fixedCommitments.toList ++ S.vk.permutation.commitments.toList,
    ptReadable (S.E.g1.toEip C)
  /-- D-P18, both halves, not the half LoweringPlan.lean:748 can state. -/
  layout : S.plan.memory.map.WellFormed ∧ S.plan.memory.validate.isOk = true
  /-- Production renders only: a trace render emits log1 (TraceAndGasHelpers.yul:20-22)
      and returns iszero(iszero(success)) instead of reverting, which refutes
      traceReturn_spec and only_two_outcomes. -/
  production : o.diagnostics.trace = false ∧ o.diagnostics.gasCheckpoints = false
  /-- The key itself: the seven clauses of VerifyingKey.WellFormed
      (VerifyingKey.lean:109-116), including domainConsistent, which is what makes the
      contract k squarings compute x^n at all (attack GenericX entry). -/
  wf : S.vk.WellFormed Features.solidity



/-! ### The memoryguard bound -/

/-- The free-memory pointer the deployed runtime installs at 0x40, read out of the
    runtime BYTES. This is the nameable half of attack FIX 32 memoryguard clause.

    WHY BYTES AND NOT THE AST. memoryguard is not an operation in the vendored
    dialect: EVMOp.lean:173 parse returns none for it, so a memoryguard call
    elaborates to a call to a USER FUNCTION named memoryguard (mkCall,
    EVMOp.lean:216) and no Step rule derives anything from it. That is D-P15, and it
    is a vendor edit this package may not make. The bound, however, does not need the
    AST: solc lowers the prologue to PUSH1/PUSH2 then PUSH1 0x40 MSTORE, and
    Generator/Evm.lean:129 reads that initialiser back out of the bytecode, so the
    value the pointer is set to is a fact about the deployment rather than about the
    dialect.

    none - no recognised initialiser - is a FAILURE as of R-60 S7. The old def
    answered true and the comment called it "the conservative direction"; the review
    pointed out what that made the field: a deployment that ships NO prologue at all
    satisfied it, since `memoryguardValue [] = none`, so `DeploymentW.memguard` was
    satisfiable by an artifact that is not a solc deployment. A bound no artifact can
    fail is decoration, and the honest reading of "no recognised initialiser" is "this
    runtime does not install the free-memory pointer the head guard then reads", which
    is exactly what the clause exists to rule out. -/
def memoryguardValue (code : List UInt8) : Option Nat :=
  runtimeFreeMemoryPointerInit (ByteArray.mk code.toArray)

/-- THE THRESHOLD, in one place: TRANSCRIPT_MPTR = 0x1000, the first address the
    verifier writes and the value the assembly head guard compares `mload 0x40`
    against before reverting. R-60 S7: the bound and the guard must be stated against
    the same literal or the byte-level clause and the AST-level guard are two copies
    of a threshold with nothing relating them - `memguardThresholdKats_ok` is the pin. -/
def transcriptMptr : Nat := 0x1000

/-- The bound itself: the shell runtime must install a free-memory pointer, and the
    pointer it installs must not exceed `transcriptMptr`, the first address the
    verifier uses. Above it the head guard reverts an honest proof, which is the
    completeness counterexample attack.md records against verifier_complete. Below it
    by enough is also a fact worth having: a runtime that installs no pointer at all
    answers `none` and now FAILS the bound (R-60 S7). -/
def memoryguardOk (code : List UInt8) : Bool :=
  match memoryguardValue code with
  | none => false
  | some v => v ≤ transcriptMptr

/-- The threshold the AST head guard tests, read back out of the guard block: the
    guard is `if gt (mload 0x40) THRESHOLD then revert`, so the number the running
    program compares the free-memory pointer against is a fact about the block, not
    about a comment. R-60 S7 asked for `memguard` to be pinned to the threshold the
    head guard tests instead of being satisfiable by shipping nothing; this is the
    reader that makes that comparison possible, and `memguardThresholdKats_ok` in the
    fixture is the comparison. -/
def headGuardThreshold : YulBlock -> Option Nat
  | Stmt.cond (Expr.builtin Op.gt [Expr.builtin Op.mload [Expr.lit (.number 0x40)],
      Expr.lit (.number v)]) _ :: _ => some v
  | _ :: rest => headGuardThreshold rest
  | [] => none

/-- R-60 S7 NAMED GAP, declared in code so a gate can point at it rather than at a
    paragraph. `shell.codeBlock` (the Yul AST `RunShell` runs) and
    `shellLayout.code` (the bytecode the deployment installs) are two copies of "the
    shell program" in two representations, and nothing in the tree relates them: there
    is no Yul-to-bytecode compiler here, because P-13 ported the templates as TEXT
    renders and no Lean function emits bytecode from a `Block Op`. `shell_unfolds`
    pins the AST side to the assembly and `DeploymentW.memguard` pins the byte side to
    the free-memory bound; the missing link is the compiler, not a field someone forgot
    to write. The decidable fragment that IS nameable today is the threshold agreement
    below - the guard in the AST and the store in the bytes are compared against the
    same literal - which is what makes this a gap with a partial pin rather than a
    blank. -/
def gap_shell_code_vs_layout_code : String :=
  "unpinned copy: shell.codeBlock vs shellLayout.code; blocker: there is no "
    ++ "Yul-to-bytecode compiler in the tree (P-13 AST emitter)"

/-! ### The deployment -/

/-- What the world must look like for the contract and the Lean verifier to agree, as
    hypotheses on an ExecEnv and on the hash H the frame runs with (design2
    DeploymentW, plus the three fields attack FIX 32 requires).

    The codehash pin is a fact about H and not about W: extcodehash in the dialect is
    projectedCodeHash env balanceOf a = keccakOf (extCodeOf a) for a non-empty
    account (EVMExec.lean:295-298, :822), so vkHash says the generation-time constant
    equals H applied to the runtime bytes. Stated as H vkRuntime = h rather than
    keccak256 vkRuntime = h so that a forall-H theorem is not refuted by an H nobody
    deployed with (finding Y-2).

    vkNonEmpty is necessary and not hygiene: projectedCodeHash returns 0 for an
    EIP-161-empty account whatever H says, so an empty VK runtime would satisfy
    vkHash vacuously at hash 0.

    disjoint is what honestCalls_functional needs: the four precompile addresses are
    the ones the honest fold dispatches on, and a VK or evaluator deployed at 0x0f
    would be answered by the pairing relation instead of by the world. -/
structure DeploymentW (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash)
    (vkAddr quotientAddr : U256) : Prop where
  /-- The frame hashes through H (finding Y-2: the hash is a state field, so this is
      where it stops being one). -/
  keccak : W.keccakOf = hashOfBytes H
  /-- The world is well formed: every extcodehash agrees with the projection, and the
      self balance with the balance map (EVMExec.lean:309). Without it the codehash
      fields below say nothing about what extcodehash actually returns. -/
  wf : W.WF
  /-- attack FIX 32, first counterexample: verifyProof is external view, so the solc
      dispatcher reverts a call carrying value. Without this the completeness
      theorem forall over runs includes a reverting one. -/
  callvalue : W.callvalue = 0
  /-- The production function is view, not pure: writes are excluded by NoWriters and
      by the head guard, not by the static bit, so a static frame models only a
      STATICCALL entry. -/
  static : W.static = false
  /-- attack FIX 32, second counterexample: VkLoading.yul:67-70 hashes
      extcodehash(vk) where vk is a loadimmutable read of AUTHORIZED_VK, i.e.
      shellLayout.immutable, so the immutable map has to name the address the world
      was pinned at. Conditional, because an embedded render reads no code at all. -/
  vkImm : S.expectedVkCodehash.isSome →
    S.shellLayout.immutable (litValue (.string "AUTHORIZED_VK")) = vkAddr
  vkCode : S.expectedVkCodehash.isSome →
    W.extCodeOf vkAddr = S.L.vkRuntime.data.toList
  vkNonEmpty : S.L.vkRuntime.size ≠ 0
  vkHash : ∀ h, S.expectedVkCodehash = some h → H S.L.vkRuntime = h
  /-- The quotient twin of vkImm, and the reason the two addresses are separate
      parameters: a separate-quotient render reads AUTHORIZED_QUOTIENT and staticcalls
      whatever it names (QuotientAndLinearization.yul:35). -/
  qImm : S.quotientRuntime.isSome →
    S.shellLayout.immutable (litValue (.string "AUTHORIZED_QUOTIENT")) = quotientAddr
  qCode : ∀ code, S.quotientRuntime = some code →
    W.extCodeOf quotientAddr = code.data.toList
  qHash : ∀ code h, S.quotientRuntime = some code →
    S.expectedQuotientCodehash = some h → H code = h
  qNonEmpty : ∀ code, S.quotientRuntime = some code → code.size ≠ 0
  /-- attack FIX 32, third field: the memoryguard bound. A named gap with a decidable
      statement rather than True - see memoryguardValue for what the vendored dialect
      cannot express and why that no longer blocks this field. -/
  memguard : memoryguardOk S.shellLayout.code
  disjoint : accountKey vkAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
    accountKey quotientAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
    accountKey vkAddr ≠ accountKey quotientAddr

/-- The one consequence of DeploymentW that every codehash argument in the partials
    reduces to: under the deployment, the projected code hash at the VK address IS the
    pinned constant. PROOF HOLE, registered in SORRY.md: unfold projectedCodeHash, take
    the non-empty branch, rewrite D.vkCode, D.keccak and D.vkHash, and the ByteArray
    round trip ByteArray.mk (l.toArray) = l. Note the hsh binder the sketch omitted -
    attack.md marks that version ILL-TYPED because autoImplicit is off. -/
theorem extcodehash_of_deployment {S : Surface p G₁ G₂ Gₜ} {W : ExecEnv} {H : Hash}
    {vkAddr quotientAddr : U256} {hsh : U256} (D : DeploymentW S W H vkAddr quotientAddr)
    (h : S.expectedVkCodehash = some hsh) :
    projectedCodeHash W W.balanceOf vkAddr = hsh := by
  sorry

/-! ### Entry frames and runs -/

/-- The assembly entry frame: arbitrary initial memory mem0 (verifier_sound is stated
    for ANY mem0, which is why the g1_identity window is an Inv clause rather than an
    assumption about zeroed memory), the calldata, the world W, the hash H, and the
    shell layout for the data and immutable maps. Every other field comes from W, so
    callvalue and static are deployment facts rather than frame facts, which is what
    makes DeploymentW the right home for them. -/
def initState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes)
    (mem₀ : Nat → UInt8) : EvmState :=
  { EvmState.init with
    memory := mem₀
    env := { W with
      calldata := cd.data.toList
      code := Lyt.code
      dataOffset := Lyt.dataOffset
      dataSize := Lyt.dataSize
      immutable := Lyt.immutable
      keccakOf := hashOfBytes H } }

/-- A fresh external call frame: zero memory. EVM-faithful for a call into a cold
    account; the solc prologue store at 0x40 is in the runtime and is what the
    memoryguard bound is about. -/
def callState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes) : EvmState :=
  initState W Lyt H cd (fun _ => 0)

/-- Memory that is zero from 0x80 up: the attack FIX 1 hypothesis. The solc dispatcher
    writes only mem[0x00..0x80), so everything above is whatever the caller left, and
    the counterexample in attack.md is a caller that left a non-identity
    committed-instance commitment in the g1_identity window.

    R-58 F9 deleted the Bool-valued sampler that used to sit here
    (memoryZeroAbove, four addresses plus a KAT). Nothing consumed it: every theorem
    takes the Prop below, so the sample was decoration and its gate was a gate about
    the sample, not about the hypothesis. ZeroAbove stays a Prop because it IS the
    hypothesis, and a decidable stand-in for a forall over all memory would be a
    different and weaker claim, not a check of this one. -/
def ZeroAbove (mem₀ : Nat → UInt8) : Prop := ∀ a, 0x80 ≤ a → mem₀ a = 0

/-- The call relation of a deployment: the honest precompiles, plus the quotient
    evaluator slot answered by running the evaluator runtime when the render
    externalises it. product is the pairing oracle (Externals.lean:941 makes the
    pairing check an oracle rather than a computation), and the address is a
    deployment fact, which is why it is a parameter. -/
def Surface.calls (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv)
    (product : PairingProduct) (quotientAddr : U256) : ExternalCalls :=
  honestCalls product quotientAddr (match S.evaluatorRuntime with
    | some (rt, Lyt) => Evaluator.rel W Lyt quotientAddr rt
    | none => fun _ _ _ => False)

/-- The runtime block of a solc object. There is no .runtime field on Object
    (Object.lean gives name, code, children and data), so the runtime is the sub-object
    solc names "name_id_deployed". -/
def Surface.irRuntime (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Option YulBlock :=
  (ir.subObject (S.runtimeName ir.name)).map YulSemantics.Object.codeBlock

/-- The names a block declares at its top level. -/
def declaredTops : YulBlock → List Ident :=
  fun b => b.foldl (init := []) fun ns s =>
    match s with
    | Stmt.funDef n _ _ _ => n :: ns
    | _ => ns

/-- A top-level statement that calls a user function the block does not declare. This
    is the decidable fragment of the import check: it sees a call in statement position
    and a call that initialises a let, which between them cover the two shapes a solc
    prologue and a planted rename produce. -/
def unresolvedTop (b : YulBlock) : Bool :=
  let declared := declaredTops b
  b.any fun s => match s with
    | Stmt.exprStmt (Expr.call f _) => ! declared.contains f
    | Stmt.letDecl _ (some (Expr.call f _)) => ! declared.contains f
    | _ => false

/-- THE IMPORT SANITY CHECK ON A SOLC OBJECT (M8), R-60 S1.

    IT IS A PROJECTION, NOT A FIELD. This used to be a free Surface field
    `irCheck : YulObject → Bool`, and the fixture filled it with a function that
    hard-coded its OWN naming convention (`n ++ "_1_deployed"`) instead of reading
    `S.runtimeName`. The imported runtime sub-object is `Halo2Verifier_292_deployed`,
    so the lookup asked for `Halo2Verifier_292_1_deployed`, missed, and `irCheck`
    returned FALSE on the real artifact - while `RunContractIR), which reads
    `S.runtimeName`, had a committed run of exactly that object. Two fields carried
    the same fact and only one of them was read by the check that gated the theorem:
    the R-58 copy class again, in the place where it does the most damage, because
    every headline field takes `S.irCheck ir = true` as a hypothesis and none of them
    was satisfiable at the artifact the package exists to talk about.

    The repair deletes the copy rather than pinning it: there is now exactly ONE
    naming function on the record, `runtimeName`, and the check reads it through
    `Surface.irRuntime`. A Surface can no longer disagree with itself about which
    sub-object is the runtime, because it cannot name a runtime twice.

    WHAT IT CHECKS stays the decidable fragment: the deployed sub-object exists and has
    no unresolved top-level call. attack.md FIX (Evaluator.rel entry) requires the
    importer to rewrite memoryguard(x) to x, and a memoryguard call in a yul% quote
    elaborates to a call to a user function named memoryguard (mkCall, EVMOp.lean:216)
    that nothing declares - so the D-P15 vendor gap is what this gate detects rather
    than something it hides. A planted rename fails it too (P11 non-vacuity). A full
    alpha-equivalence check modulo constant substitution is M8 work and is recorded as
    a gap at `LoweringCorrect.ir_refines`. -/
def Surface.irCheck (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Bool :=
  match S.irRuntime ir with
  | some rt => ! unresolvedTop rt
  | none => false

/-- PLAN 9.5 RunVerifier: headGuard ++ bindLocals ++ main, from an arbitrary memory,
    observed at the frame boundary. -/
def RunVerifier (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (cd : Bytes)
    (mem₀ : Nat → UInt8) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g (S.L.headGuard ++ S.bindLocals ++ S.L.main)
    (initState W S.shellLayout H cd mem₀) V' obs.state obs.outcome

/-- PLAN 9.5 RunContractIR over the imported via-ir object runtime block. Stated here
    so the shape exists; it is UNINHABITED until D-P15 lands, because the IR prologue
    calls memoryguard and no Step rule derives anything from a user call (header: THE
    BLOCKER). Any theorem whose only hypothesis is a RunContractIR is therefore
    vacuously true today, and ir_refines is exactly such a theorem - which is why that
    one is not stated in this package. -/
def RunContractIR (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (ir : YulObject)
    (irLyt : EVM.Layout) (cd : Bytes) (c : ExternalCalls) (g : ExternalGas)
    (obs : Obs) : Prop :=
  ∃ rt V', S.irRuntime ir = some rt ∧
    RunCommitted c g rt (callState W irLyt H cd) V' obs.state obs.outcome

/-- PLAN 9.5 RunShell: the hand-written dispatcher model wrapping the assembly. -/
def RunShell (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (H : Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g S.shell.codeBlock (callState W S.shellLayout H cd)
    V' obs.state obs.outcome

/-- Observational equivalence at the view level. Memory, activeWords and the VEnv are
    deliberately not observable: that is what makes an IR whose layout differs from
    the shell model comparable to it at all (attack FIX 36, and the reason the call
    relations have to be world-local for the comparison to mean anything). -/
def ObsEquiv (R₁ R₂ : Obs → Prop) : Prop :=
  ∀ v : ObsView, (∃ o, R₁ o ∧ o.view = v) ↔ (∃ o, R₂ o ∧ o.view = v)

/-! ### Acceptance -/

/-- PLAN 9.5 LeanAccepts, over raw calldata and raw instance words. The instance words
    stay raw because the rejection of a word at or above r is the contract own gate
    (TranscriptProofParser.yul:63-68) and reducing mod p would lose it (R-26.7);
    instOfWords? re-enters it inside ContractRefAcceptsAcc.

    The decoder is the real one from Lowering/Calldata.lean:328, applied to the
    Surface own layout, instance count and codec - not a free Surface field. -/
def LeanAccepts (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW,
    Midfall.Lowering.decodeCalldata (p := p) S.plan.proofLayout S.cfg.numInstances
      S.E.g1 cd = some (ms, instW) ∧
      ContractRefAcceptsAcc S.E H S.params S.vk S.cfg.accumulator S.vkDigest
        S.accFixedBases instW ms = true

/-- Adjustment 3 from the plan: the decoded public accumulator of a calldata, so a
    snapshot in an accumulator render carries it. Stating a per-partial spec with
    acc := none in an accumulator render would describe a no-accumulator snapshot and
    prove nothing about the slots the render writes. -/
def accOf (S : Surface p G₁ G₂ Gₜ) (instW : Array Word256) :
    Option (KzgAcc (Fr p) G₁ G₂ Gₜ) :=
  S.cfg.accumulator.bind fun enc =>
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) S.E.g1 S.accFixedBases instW

/-- The fixed-base table in the shape decodeAcc, fullyCollapse and batchedCheck take
    it: name and base, no negate flag. The flag is folded in by negateByTable at decode
    time, which is why the table has to be the generated positive-base one and not Exec
    fixedBases (R-52). -/
def tblOf (fb : Array (AccFixedBase G₁)) : Array (String × G₁) :=
  fb.map fun b => (b.name, b.base)

/-! ### Side conditions -/

/-- Completeness side condition, R-2 first face, stated through the snapshot rather
    than by replaying the Fiat-Shamir schedule. design2 xOf replay was rejected:
    attack.md marks it ILL-TYPED and a second copy of the schedule, the R-30/R-32
    drift hazard D6 exists to avoid. So the challenge is whatever the run squeezed.

    The shape is forall Snap, snapshotOf ... = .ok Snap implies ChallengesGood vk Snap:
    a run whose snapshot does not exist contributes nothing, which is honest - the
    contract cannot return on calldata the Lean pipeline faults on, and the direction
    that needs this is the one where a snapshot does exist. -/
def GenericX (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms : List (Msg (Fr p) G₁))
    (instW : Array Word256) (inst : Array (Fr p)) : Prop :=
  ∀ Snap, snapshotOf S.E H S.vk inst ms (accOf S instW) = .ok Snap →
    ChallengesGood S.vk Snap

/-- Soundness side condition, finding 5 / item C, stated operationally: the contract
    computes the lookup helper identity with prefix and suffix products and never
    inverts (yul_emit.rs:509-554, quotient.rs:1830-1860), while Lean aborts when
    f_j(x) + beta = 0 (Logup.lean:279, site string logup.rs:460). On that set the
    contract accepts an honest proof and Lean rejects, so verifier_sound needs this
    for every H.

    Not a field of ChallengesGood, per the attack FIX: inside a per-partial theorem
    whose hypothesis is snapshotOf = .ok Snap it is already implied, and a decorative
    field is what that FIX exists to prevent. It is load-bearing only where no snapshot
    is given, which is where it is stated. -/
def NoLogupPanic (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms : List (Msg (Fr p) G₁))
    (inst : Array (Fr p)) : Prop :=
  prepareMsgs (Gₜ := Gₜ) S.E H Features.solidity S.vk inst ms ≠
    .error (Fault.panic "proofs/src/plonk/logup.rs:460")

/-! ### Known-answer checks

    Model-free, per the Instances confinement gate: everything here needs only the
    generator and the dialect, so it can live in a file that states theorems. The
    exhibits that need a pairing - a Surface, a DeploymentW, a SupportedS - are in
    Midfall/Instances/SurfaceFixture.lean. -/

/-- Bytes as the runtime code list the deployment carries: the generator builds
    ByteArrays from Nat lists and the dialect layouts hold List UInt8, so every
    memoryguard case below converts through the same pair of projections. -/
def bytesNats (ns : List Nat) : List UInt8 :=
  (Midfall.Generator.bytesFromNats ns).data.toList

/-- THE MEMORYGUARD BOUND BITES. The cases are the reason the field is a Prop and not
    True: a prologue that raises the pointer to 0x100 satisfies the bound, one that
    raises it to 0x2000 does not, and a runtime with no recognised initialiser
    satisfies it in the conservative direction the def comment argues for. Refuted by
    a memoryguardOk that ignores the value (the third line would go green) or that
    treats none as a failure (the fourth would go red). -/
def memoryguardKats_ok : Bool :=
  -- PUSH1 0x80 PUSH1 0x40 MSTORE: the ordinary solc prologue
  memoryguardOk (bytesNats [0x60, 0x80, 0x60, 0x40, 0x52]) &&
    -- PUSH2 0x0100: still under the transcript pointer
    memoryguardOk (bytesNats [0x61, 0x01, 0x00, 0x60, 0x40, 0x52]) &&
    -- PUSH2 0x2000: above TRANSCRIPT_MPTR, so the head guard reverts an honest proof
    ! memoryguardOk (bytesNats [0x61, 0x20, 0x00, 0x60, 0x40, 0x52]) &&
    -- R-60 S7: no prologue at all is now a FAILURE, not the conservative direction.
    -- This is the line that used to read `memoryguardOk []`, i.e. the field was
    -- satisfiable by shipping nothing.
    memoryguardValue [] = none && ! memoryguardOk [] &&
    -- the boundary itself: exactly 0x1000 is allowed, 0x1001 is not. PUSH2 only:
    -- the reader recognises PUSH1 and PUSH2 (Evm.lean:132-138) and a PUSH3 prologue
    -- would answer none, which now fails the bound for the right reason.
    memoryguardOk (bytesNats [0x61, 0x10, 0x00, 0x60, 0x40, 0x52]) &&
    ! memoryguardOk (bytesNats [0x61, 0x10, 0x01, 0x60, 0x40, 0x52]) &&
    -- and a PUSH3 store is NOT recognised, which is the none case again
    memoryguardValue (bytesNats [0x62, 0x00, 0x10, 0x00, 0x60, 0x40, 0x52]) = none

#eval memoryguardKats_ok                  -- expect true

/-- THE THRESHOLD IS ONE NUMBER, not two. `memoryguardOk` bounds the pointer the
    deployed BYTES install; the head guard in the AST reverts when `mload 0x40` is
    above the transcript pointer. R-60 S7: those are two copies of a threshold in two
    representations, and if they drift the byte-level clause stops meaning anything
    about the guard that actually runs. The fixture's head guard literal and the bound
    are compared here, so a drift is a red gate rather than a silent one. Refuted by
    changing either number. -/
def memguardThresholdKats_ok : Bool :=
  transcriptMptr == 0x1000 &&
    -- the bound bites exactly at the threshold: at it, allowed; one above, not
    (memoryguardOk (bytesNats [0x61, 0x10, 0x00, 0x60, 0x40, 0x52]) &&
      ! memoryguardOk (bytesNats [0x61, 0x10, 0x01, 0x60, 0x40, 0x52])) &&
    -- the reader is a reader and not a constant: a guard that tests a different
    -- number reports that number, and a block with no such guard reports none
    (headGuardThreshold [Stmt.cond (Expr.builtin Op.gt
        [Expr.builtin Op.mload [Expr.lit (.number 0x40)], Expr.lit (.number 0x999)])
        [Stmt.exprStmt (Expr.builtin Op.revert [Expr.lit (.number 0), Expr.lit (.number 0)])]]
      == some 0x999) &&
    headGuardThreshold ([] : YulBlock) = none

#eval memguardThresholdKats_ok            -- expect true

/-- initState installs exactly the fields the comment claims and nothing else: the
    calldata, code, data maps, immutable map and keccak oracle come from the layout
    and H, while callvalue, static and the world projections come from W untouched.
    The last two lines are the ones that matter for DeploymentW: if initState took
    callvalue from the layout instead of the world, the callvalue field would be a
    hypothesis about a field no run reads. -/
def initStateKats_ok : Bool :=
  let W : ExecEnv := { callvalue := 7, static := true }
  let Lyt : EVM.Layout :=
    { code := [1, 2, 3]
      dataOffset := fun _ => 9
      dataSize := fun _ => 8
      immutable := fun _ => 6 }
  let st := initState W Lyt keccak256 (ByteArray.mk #[4, 5]) (fun _ => 1)
  st.env.callvalue == 7 && st.env.static && st.env.code == [1, 2, 3] &&
    st.env.calldata == [4, 5] && st.env.dataOffset 0 == 9 && st.env.dataSize 0 == 8 &&
    st.env.immutable 0 == 6 && st.memory 0 == 1 &&
    st.env.keccakOf [1] == keccak256 (ByteArray.mk #[1]) &&
    -- and a call frame zeroes memory instead of inheriting it
    (callState W Lyt keccak256 (ByteArray.mk #[4, 5])).memory 0 == 0 &&
    (callState W Lyt keccak256 (ByteArray.mk #[4, 5])).env.callvalue == 7

#eval initStateKats_ok                    -- expect true

/-- encG2IsEip is a decision about the encoder, not a formality: the EIP-2537 infinity
    encoding (256 zero bytes) passes, the empty byte string fails on the width alone,
    and a 256-byte string that is not a valid encoding fails on the second clause.
    The second line is the R-58 G2 perturbation: the value the fixture used before
    this pin existed refutes it, so the pin is not satisfied by whatever the encoder
    happens to return. -/
def encG2Kats_ok : Bool :=
  encG2IsEip (bytesZero Midfall.Yul.g2Bytes) &&
    ! encG2IsEip Midfall.Bytes.empty &&
    ! encG2IsEip (bytesZero (Midfall.Yul.g2Bytes - 32)) &&
    -- right width, garbage coordinates: the decode/validity half, not the width half
    ! encG2IsEip (bytesAppend (bytesZero 64) (bytesReplicate 192 (UInt8.ofNat 0xff))) &&
    Midfall.Yul.g2Bytes == 0x100

#eval encG2Kats_ok                        -- expect true

/-- The immutable key the deployment pins is the string-literal encoding of the
    Solidity name, not the name itself: loadimmutable reads env.immutable at
    litValue (.string name) (EVMExec.lean:793), so a DeploymentW that indexed the map
    by a raw word would pin an address no read consults. The two literals are distinct,
    which is what makes the pin about the right key. -/
def immutableKeyKats_ok : Bool :=
  let empty : EVM.Layout :=
    { code := []
      dataOffset := fun _ => 0
      dataSize := fun _ => 0 }
  litValue (.string "AUTHORIZED_VK") != litValue (.string "AUTHORIZED_QUOTIENT") &&
    litValue (.string "AUTHORIZED_VK") != 0 &&
    -- and the map is total, so a missing key answers 0 rather than failing: which is
    -- why vkImm is conditional on the render reading immutables at all
    empty.immutable (litValue (.string "AUTHORIZED_VK")) == 0

#eval immutableKeyKats_ok                 -- expect true

/-- The table projection drops the negate flag and keeps the name order, which is what
    decodeAcc and fullyCollapse index by. A tblOf that sorted or deduped would silently
    change which base a name resolves to, and the acc arm of finalPairing_spec would be
    about a different table than the contract carries. -/
def tblOfKats_ok : Bool :=
  let fb : Array (AccFixedBase Nat) :=
    #[{ name := "b0", base := 1, negate := true },
      { name := "b1", base := 2, negate := false }]
  tblOf (G₁ := Nat) fb = #[("b0", 1), ("b1", 2)] &&
    -- the flag is gone, so a negated base has to be folded in elsewhere
    (tblOf (G₁ := Nat) fb).map (fun e => e.1) = #["b0", "b1"]

#eval tblOfKats_ok                        -- expect true

end Midfall.Lowering
