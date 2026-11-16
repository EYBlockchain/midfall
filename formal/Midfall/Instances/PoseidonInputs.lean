/-
  Midfall.Instances.PoseidonInputs

  D.1 (GEN - PORT): the generator-side inputs of `poseidonRender` as PURE terms - no `IO`, no
  `readDump`, no CWD dependency. Both halves of the card landed: the VK and the plan (the split
  point), then the render context, the quotient blocks and the model.

  WHY THIS FILE EXISTS. Every generator-side input of the render currently reaches the cone
  through `Midfall.Instances.DeployedProfile`, and the five that matter - verifying key, memory,
  lowering plan, quotient blocks, render model - are produced inside an `IO` block
  (`poseidonDerived` :207, `poseidonDerivedCtx` :219). A `Render` record (WP-I2,
  `LoweringV2/Statements.lean` :71-88) is a structure of DATA, so nothing can put an
  `IO (Option ...)` in its `plan`, `vk`, `qblocks` or `model` field. Until the roots of those
  fields are terms, no card can move a cone: the V2 roots are bare sorries over a render that
  does not exist yet. This file makes them terms. ONE exception, stated at `poseidonModel`: the
  model is an `Except`, not a bare value, because the record has no inhabitant to totalise on -
  see the premise gap recorded there.

  HOW: `include_str`. The card's VERIFY-FIRST (a) was measured by the orchestrator and
  re-measured here: `include_str` ELABORATES and resolves its path relative to the CONTAINING
  FILE, not the process CWD, so a fixture reached from `Midfall/Instances/` needs no script and
  no working directory. The path below is `../../../proofs/...` and it resolves at build time to
  the same tracked artifacts the IO readers open at elaboration time. That is the whole point:
  ONE fixture set, two access channels, and the gates below are what say the channels agree.

  WHAT IS NOT HERE. Nothing is re-parsed and nothing is re-transcribed. The VK comes out of
  `vkModelFromArtifact` (Contracts.lean:857), the exact function `poseidonDerived` :211 applies
  to the bytes it reads; the plan comes out of `poseidonPlan` :177 applied to
  `poseidonDerivedMemory` :192 and `quotientDeployedProgram` (VerifierPartials.lean:1068), the
  exact terms :213-214 uses. So this file adds no model and no numbers - it moves two terms from
  the IO monad into the pure fragment and gates say that the move changed nothing.

  (b) ANSWERED, because it decides the path. `poseidonDerived` reads TWO files, both through
  `EvmKats.readFirst`, which tries CWD-relative candidates in order:
    readVkDump -> vkDumpCandidates =
      ../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2VerifyingKey.sol
      (then the repo-root form)
    readDump   -> generatedVerifierCandidates =
      ../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol
  Both are TRACKED in git (`git ls-files` lists them; this `target/` is not ignored), so
  `include_str` on them is stable. TRUE.

  (c) ANSWERED: `poseidonPlan` :177 returns `LoweringPlan Unit Unit`, which is exactly the type
  of `Render.plan` (Statements.lean:84). TRUE - no coercion, no port needed.

  A NOTE ON EQUALITY. `Halo2VerifyingKey` and `LoweringPlan` carry no `BEq` (Models.lean:385 and
  LoweringPlan.lean:213 derive nothing; the plan's own docstring records that the Rust derives
  Debug only and that "the gates compare fields, never whole plans"). Rather than add a
  `deriving` to someone else's record, the gates compare the VK through `renderHalo2VerifyingKey`
  - the whole 26,018-byte file it produces, gate 12's own channel - plus every field of the
  record structurally, and compare the plan field by field through the total `Ptr` adapter. That
  is equality of the data, not a hash of it.
-/
import Midfall.Instances.DeployedProfile

namespace Midfall.Instances.PoseidonInputs
open Midfall Midfall.Generator Midfall.Generator.ContractKats
open Midfall.Generator.VerifierPartialKats Midfall.Generator.QuotientFold

/-- THE FIXTURE, baked in at build time: the tracked separate-VK artifact, 26,018 bytes / 271
    lines. Relative to THIS file, so it does not care where `lake` was started. -/
def poseidonVkDump : String :=
  include_str "../../../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2VerifyingKey.sol"

/-- The payload a parse failure leaves behind. It is NOT a second guess at the fixture - every
    field is empty - and it exists only so `poseidonVkGen` is a total term instead of an
    `Option`. A drifted artifact therefore does not silently render a default: gate D.1-1 fails,
    because the empty payload does not render to the file it came from. -/
def poseidonVkUnparsed : Halo2VerifyingKey :=
  { constructorPayloadMptr := 0, constants := [], fixedComms := [], permutationComms := [],
    quotientConstOffsetWords := none, quotientConstWords := 0,
    quotientProgramOffsetWords := none, quotientProgramWords := 0,
    quotientConstLabels := [], quotientConstHeaders := [] }

/-- The parse, before the totalisation: `some` exactly when the fixture still reads. -/
def poseidonVkGen? : Option Halo2VerifyingKey := vkModelFromArtifact poseidonVkDump

/-- GENERATOR-SIDE INPUT 1 OF `poseidonRender`: the verifying key, as a pure term. Same
    function, same bytes, same result as `poseidonDerived`'s `vkModelFromArtifact dvk` at :211 -
    gated by `poseidonVkGen_matchesIo_ok`. -/
def poseidonVkGen : Halo2VerifyingKey := (poseidonVkGen?).getD poseidonVkUnparsed

/-- GENERATOR-SIDE INPUT 2 OF `poseidonRender`: the lowering plan, as a pure term. Built by the
    same three terms :213-214 builds the IO one from, so the only thing that changed on the way
    here is that the VK arrived by `include_str` instead of by `IO.readFile`. `Render.plan` wants
    `LoweringPlan Unit Unit` (Statements.lean:84) and that is what `poseidonPlan` returns -
    VERIFY-FIRST (c), true. -/
def poseidonPlanV2 : LoweringPlan Unit Unit :=
  poseidonPlan poseidonVkGen (poseidonDerivedMemory poseidonVkGen) quotientDeployedProgram

/-! ## Second half: the render context, the quotient blocks, the model -/

/-- THE SECOND FIXTURE, baked in the same way: the tracked deployed verifier artifact,
    175,908 characters / 3,024 lines. This is the file `readDump` opens at :210 - the same
    bytes, reached purely. -/
def poseidonVerifierDump : String :=
  include_str "../../../proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol"

/-- GENERATOR-SIDE INPUT 3 OF `poseidonRender`: the render context, as a pure term - the same
    `quotientDeployedCtx` :1162 :212 applies to the bytes it reads, now applied to the baked
    fixture. The transcribed `Midfall.Generator.poseidonCtx` is the fallback; gate D.1-7
    requires all five generated-code regions NON-EMPTY, which is what stops that fallback from
    being silently load-bearing (the transcribed ctx carries zero lines in all five), and gate
    D.1-8 renders the whole contract from this context. -/
def poseidonCtx : PartialCtx :=
  (quotientDeployedCtx poseidonVerifierDump).getD Midfall.Generator.poseidonCtx

/-- GENERATOR-SIDE INPUT 4 OF `poseidonRender`: what the unported QRS:2000 emitter would
    return, as a pure term - the same `poseidonBlocks` :197 the derivation applies at :215,
    now applied to the pure context instead of to one read inside an `IO` block. -/
def poseidonQBlocks : QuotientComputationBlocks := poseidonBlocks poseidonCtx

/-- GENERATOR-SIDE INPUT 5 OF `poseidonRender`: the render model, as a pure term.

    PREMISE GAP, stated rather than worked around. The card asks for "the `.ok` value of"
    this call. That projection needs an inhabitant of `Halo2Verifier VerifierMemoryLayout
    ProofCalldataLayout` to totalise the `.error` arm, and there is none: the record
    (Models.lean:757) derives nothing, so `inferInstance : Inhabited Model` fails to
    synthesize (measured), and `Halo2Verifier` has 71 fields, so the alternative - a literal
    fallback - is a transcription of the very artifact this file is supposed to derive from.
    Adding `deriving Inhabited` to Models.lean would fix it in one line and is a v1 edit this
    card forbids. So the term is delivered as the `Except` it is: still pure, still no `IO`,
    and gate D.1-5 is the card's "KAT that it returns `.ok`". WP-I2 needs one of the two
    openings named here to get a bare `Model`; `Render.model` is `Model`
    (Statements.lean:86, Program.lean:37). -/
def poseidonModel : Except Midfall.Halo2.Fault
    (Halo2Verifier VerifierMemoryLayout ProofCalldataLayout) :=
  generateVerifierFromPlan (fun _ _ => poseidonQBlocks) poseidonInputs poseidonFlags poseidonPlanV2

end Midfall.Instances.PoseidonInputs

namespace Midfall.Instances.PoseidonInputsKats
open Midfall Midfall.Generator Midfall.Generator.ContractKats
open Midfall.Generator.VerifierPartialKats Midfall.Generator.QuotientFold
open Midfall.Instances
open Midfall.Instances.PoseidonInputs

/-- A `Ptr` read as a byte address: `Value` carries no BEq (DeployedProfile's own note, and the
    plan README's finding F5), so every pointer comparison in these gates goes through this total
    adapter. -/
def pv (p : Ptr) : Nat := Value.asUsizeNat p.value

/-- One G1 commitment as the four words it is, so the two lists can be compared STRUCTURALLY
    without asking `G1Words` for a BEq it does not have. -/
def g1 (w : G1Words) := (w.xHi, w.xLo, w.yHi, w.yLo)

/-- GATE D.1-1 (PURE, no IO at all). The term round-trips: rendering the pure VK reproduces the
    fixture byte for byte, at the fixture's own size, and the payload length the plan reads is
    the artifact's. This is the gate that reddens if `poseidonVkUnparsed` is ever what the parse
    returns, and it needs no file read to say so - the string is already in the module. The 35 / 19 /
    8 are the constant-table and commitment counts the fixture's own label scan yields, restated
    here so a parse that returns a SHORTER payload cannot pass by rendering nothing different. -/
def poseidonVkGen_roundTrips_ok : Bool :=
  renderHalo2VerifyingKey poseidonVkGen == poseidonVkDump
    && poseidonVkDump.length == 26018
    && (poseidonVkDump.splitOn "\n").length == 271
    && ! poseidonVkDump.endsWith "\n"
    && poseidonVkGen.len == 4576
    && poseidonVkGen.constants.length == 35
    && poseidonVkGen.fixedComms.length == 19
    && poseidonVkGen.permutationComms.length == 8

/-- GATE D.1-2 (the KAT the card asks for, VK half). The pure term EQUALS the IO-derived
    counterpart: `readVkDump` then `vkModelFromArtifact` is the exact chain `poseidonDerived`
    :209-211 runs, and every field of the two models agrees - the whole render, the payload
    base, the constant table by value, both commitment lists by value, the length. -/
def poseidonVkGen_matchesIo_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | none => false
    | some vk =>
        dvk.length == 26018
          && renderHalo2VerifyingKey vk == renderHalo2VerifyingKey poseidonVkGen
          && vk.constructorPayloadMptr == poseidonVkGen.constructorPayloadMptr
          && vk.constants == poseidonVkGen.constants
          && vk.fixedComms.map g1 == poseidonVkGen.fixedComms.map g1
          && vk.permutationComms.map g1 == poseidonVkGen.permutationComms.map g1
          && vk.len == poseidonVkGen.len
          && vk.quotientConstOffsetWords == poseidonVkGen.quotientConstOffsetWords
          && vk.quotientProgramOffsetWords == poseidonVkGen.quotientProgramOffsetWords)

/-- GATE D.1-3 (the KAT the card asks for, plan half). The pure plan EQUALS the plan
    `poseidonDerived` builds at :214, field by field: the VK it carries, vk_mptr, the sorted
    selector buckets, the proof layout's end and length, the four Data pointers that came off
    the DERIVED layout, the derived memory's own vk_mptr, the quotient plan's anchors and flags,
    and the meta counts the model reads. -/
def poseidonPlanV2_matchesIo_ok : IO Bool :=
  readVkDump >>= fun dvk =>
  pure (match vkModelFromArtifact dvk with
    | none => false
    | some vk =>
        let L := poseidonPlan vk (poseidonDerivedMemory vk) quotientDeployedProgram
        let P := poseidonPlanV2
        renderHalo2VerifyingKey L.vk == renderHalo2VerifyingKey P.vk
          && pv L.vkMptr == pv P.vkMptr
          && L.sortedSimple == P.sortedSimple
          && L.proofLayout.proofEnd == P.proofLayout.proofEnd
          && L.proofLayout.proofLen == P.proofLayout.proofLen
          && pv L.memory.vkMptr == pv P.memory.vkMptr
          && pv L.data.challengeMptr == pv P.data.challengeMptr
          && pv L.data.thetaMptr == pv P.data.thetaMptr
          && pv L.data.commsMptrBase == pv P.data.commsMptrBase
          && pv L.data.reversedEvalsMptr == pv P.data.reversedEvalsMptr
          && L.meta_.numEvals == P.meta_.numEvals
          && L.meta_.numQuotients == P.meta_.numQuotients
          && L.meta_.numPermutationZs == P.meta_.numPermutationZs
          && L.meta_.numUserAdvices == P.meta_.numUserAdvices
          && (match L.quotient, P.quotient with
              | some q, some r =>
                  q.program.evalNumerMptr == r.program.evalNumerMptr
                    && q.program.stackMptr == r.program.stackMptr
                    && q.program.programMptr == r.program.programMptr
                    && q.plan.sortedSimple == r.plan.sortedSimple
                    && q.plan.hasNativePermutation == r.plan.hasNativePermutation
                    && q.plan.hasNativeLookup == r.plan.hasNativeLookup
              | _, _ => false))

/-- GATE D.1-4 (the pure plan is the plan the DERIVATION uses). Not a second copy of D.1-3: this
    one goes through `poseidonDerived` itself and compares the pure plan against what the model
    that derivation produced says about its own inputs - `vkLen`, the expected VK codehash,
    `proofLen`, and the memory the model carries. If the pure plan were a different plan, the
    model built from it would disagree with the derived one here. -/
def poseidonPlanV2_isTheDerivedPlan_ok : IO Bool :=
  poseidonDerived >>= fun vm =>
  pure (match vm with
    | none => false
    | some v =>
        v.vkLen == poseidonPlanV2.vk.len
          && v.expectedVkCodehash == some (expectedVkCodehashOf poseidonPlanV2.vk)
          && v.proofLen == poseidonPlanV2.proofLayout.proofLen
          && pv v.memory.vkMptr == pv poseidonPlanV2.memory.vkMptr
          && pv v.memory.vkMptr == 0x2900)

/-- GATE D.1-5 (the card's second-half KAT). The pure generator call returns `.ok`. Pure, so
    it says something an `IO` gate could not: the derivation does not depend on a file read
    succeeding at gate time. -/
def poseidonModel_isOk_ok : Bool := poseidonModel.isOk

/-- GATE D.1-6 (the model validates, purely). ART:337-339's `validate_layout().unwrap_or_else`
    run on the PURE model - gate 5's check with the `IO` taken out. -/
def poseidonModel_validates_ok : Bool :=
  match poseidonModel with
  | .ok v => (Halo2Verifier.validateLayout v).isOk
  | .error _ => false

/-- GATE D.1-7 (the pure ctx and the pure blocks EQUAL their IO-derived counterparts).
    `quotientDeployedCtx sol` is the term :212 feeds to `poseidonBlocks`; the five generated
    code regions are compared BY VALUE, and each is required non-empty. The non-emptiness is
    what stops the fallback above from being silently load-bearing: the transcribed
    `Midfall.Generator.poseidonCtx` carries ZERO lines in all five regions (measured - it is
    P-13b's ctx, and filling these five is exactly what `quotientDeployedCtx` adds), so had the
    slice failed and the fallback been taken, every one of these five lengths would read 0. -/
def poseidonCtx_matchesIo_ok : IO Bool :=
  readDump >>= fun sol =>
  pure (match quotientDeployedCtx sol with
    | none => false
    | some q =>
        let c := PoseidonInputs.poseidonCtx
        let b := PoseidonInputs.poseidonQBlocks
        let qb := poseidonBlocks q
        c.quotientInlineComputations == q.quotientInlineComputations
          && c.quotientNativePermutationComputation == q.quotientNativePermutationComputation
          && c.quotientNativeLookupComputation == q.quotientNativeLookupComputation
          && c.quotientNativeIdentityComputations == q.quotientNativeIdentityComputations
          && c.quotientPostVmComputations == q.quotientPostVmComputations
          && c.quotientInlineComputations.length > 0
          && c.quotientNativePermutationComputation.length > 0
          && c.quotientNativeLookupComputation.length > 0
          && c.quotientNativeIdentityComputations.length > 0
          && c.quotientPostVmComputations.length > 0
          && b.inlineComputations == qb.inlineComputations
          && b.evalNumerComputations == qb.evalNumerComputations
          && b.postVmComputations == qb.postVmComputations
          && b.nativePermutationComputation == qb.nativePermutationComputation
          && b.nativeLookupComputation == qb.nativeLookupComputation
          && b.nativeIdentityComputations == qb.nativeIdentityComputations)

/-- GATE D.1-8 (THE HEADLINE, AND PURE). The five terms above - VK, plan, ctx, blocks, model -
    render the deployed verifier contract EXACTLY: 175,908 characters, 3,024 lines, no trailing
    newline, no `IO` anywhere in the chain. This is DeployedProfile's gate 7 with the two file
    reads replaced by `include_str` and the VK replaced by a term, which is what makes it the
    thing WP-I2 can put in a `Render`. -/
def poseidonRender_bytesExact_ok : Bool :=
  match PoseidonInputs.poseidonModel with
  | .error _ => false
  | .ok v =>
      let c : PartialCtx := { partialCtxOfVerifier v with
        buildId := Midfall.Generator.poseidonCtx.buildId }
      let rc : RootCtx := { base := c, abiSelectorBytes := 4, abiProofHeadOffset := 0x40, abiInstancesHeadCptr := 0x24 }
      let r := renderHalo2Verifier rc (poseidonDerivedParts PoseidonInputs.poseidonVerifierDump c)
      r == PoseidonInputs.poseidonVerifierDump && r.length == 175908
        && (r.splitOn "\n").length == 3024 && ! r.endsWith "\n"

/-- GATE D.1-9 (the pure model EQUALS the model `poseidonDerived` produced, on the fields the
    plan and the blocks control). Cross-checks D.1-8 through the IO path rather than the baked
    fixture, so a stale `include_str` and a live read cannot both be quietly wrong. -/
def poseidonModel_matchesIo_ok : IO Bool :=
  poseidonDerived >>= fun vm =>
  pure (match vm, PoseidonInputs.poseidonModel with
    | some v, .ok w =>
        v.buildId == w.buildId && v.vkLen == w.vkLen && v.proofLen == w.proofLen
          && v.numEvals == w.numEvals && v.numQuotients == w.numQuotients
          && v.numPermutationZs == w.numPermutationZs
          && v.expectedVkCodehash == w.expectedVkCodehash
          && pv v.memory.vkMptr == pv w.memory.vkMptr
          && pv v.memory.challengeMptr == pv w.memory.challengeMptr
          && v.memory.quotientTmpMptr == w.memory.quotientTmpMptr
          && v.userPhases.length == w.userPhases.length
    | _, _ => false)

end Midfall.Instances.PoseidonInputsKats

#eval Midfall.Instances.PoseidonInputsKats.poseidonVkGen_roundTrips_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonVkGen_matchesIo_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonPlanV2_matchesIo_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonPlanV2_isTheDerivedPlan_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonModel_isOk_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonModel_validates_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonCtx_matchesIo_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonRender_bytesExact_ok -- expect true
#eval Midfall.Instances.PoseidonInputsKats.poseidonModel_matchesIo_ok -- expect true
