-- |
-- Midfall.LoweringV2.Generated
--
-- OBJ.7 (PLAN-V3, V3 row 41): THE GENERATOR, END TO END, IN LEAN.
--
-- `generateAll` is the card's object: constraint system + configuration + payload in, the
-- finalized plan, the compact quotient blocks and the render model out. Everything it runs was
-- already in the tree - OBJ.6's quotient glue, P-11's record and validators, P-13f's
-- `generateVerifierFromPlan`, P-09h's `compactQuotientComputationBlocks` - and this file adds
-- no computation of its own. It is the SEAM: the one place that says which of those pieces the
-- generator actually calls, in the order the reference calls them, and what it refuses to
-- return.
--
-- WHY A NEW FILE UNDER LoweringV2/ AND NOT AN ADDITION TO Generator/. The card names this
-- path, and the reason is visible in the type of `GenOut.model`: a `Model` is
-- `Midfall.LoweringV2.Model` (Program.lean:37), the render model the V2 program surface is
-- built from, so the record the generator returns belongs to the surface it feeds and not to
-- the codegen row that produces it. `Generator/` must not import `LoweringV2/` - the
-- dependency runs the other way (Program.lean:28 imports Generator.Artifacts) - so the seam
-- has to sit on this side of it. The three files of `LoweringV2/Frozen.sha256`
-- (Program.lean, Shared.lean, Statements.lean) are NOT touched by this card: `GenOut` and
-- `generateAll` are new definitions in a new file, and OBJ.8 is the card that moves the
-- statement surface.
--
-- NO THEOREM LIVES HERE, AND THAT IS A CONSTRAINT AND NOT AN OMISSION. D-P17 confines
-- `native_decide` to `Midfall/Instances/`, and checks.sh reddens any file that imports
-- `Midfall/Instances/` while stating a theorem. This file imports `Generator.PlanNew`, which
-- imports `Generator.Vk`, which imports `Instances.ExponentModel` - the tree's only runnable
-- `AdmissiblePairing` - so a proof stated here would silently acquire a dependence on the
-- exponent model. D-P71 is the harder version of the same rule: nothing in the cone of
-- `lowering_correct` may rest on a native axiom. So every item here is a `def`, computable,
-- with no tactic anywhere, and the gates are in `Instances/GeneratedKats.lean`.
--
-- THE FAULT-STRING CONVENTION IS OBJ.6'S, INHERITED AND STATED (the handoff asks for a
-- decision, so this is it). Every abort this card adds carries
-- `path:line (message)` - the `siteQ` form (QuotientBlocks.lean:144-148) - and NOT P-11's
-- bare `path:line`. Where the Rust's panic formats an Err payload into the message, the
-- payload travels too, because `Fault.panic` carries a String and losing the reason is a
-- choice the port does not have to make. The four sites are plan.rs:310, plan.rs:326,
-- vk.rs:457 and artifacts.rs:339; the helpers are `sitePlan` / `siteVk` / `siteArt` in
-- PlanNew.lean, and `GeneratedKats` gate 12 reads the three Rust files at #eval time and pins
-- every one of them, so a re-cite cannot drift silently. Two consequences for the card's own
-- acceptance text, recorded rather than absorbed: the fired strings are longer than the
-- card's predictions, and the "payload without reservation fields" abort is quotient.rs:202
-- and not :204 (OBJ.6's handoff note, re-measured here at gate 11).
--
-- WHAT `generateAll` REFUSES, AND WHY EACH REFUSAL IS IN THE RIGHT ORDER. The three aborts of
-- `newFromVk` fire before any Yul is emitted; the fourth, ART:339, fires after the model is
-- built, because the Rust builds the record and validates it in the same body
-- (`verifier.validate_layout().unwrap_or_else(|err| panic!(...))`, ART:337-339). P-13f
-- deliberately split those two steps when it ported `generate_verifier_from_plan`
-- (Artifacts.lean:495-500: "the port keeps the two steps separate so a gate can inspect a
-- model whose validator disagrees with it"), so the validation belongs HERE, in the seam, and
-- not folded back into a file another package owns.

import Midfall.Generator.Api
import Midfall.Generator.PlanNew
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.VerifyingKey
import Midfall.LoweringV2.Program

set_option autoImplicit false

namespace Midfall.LoweringV2

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Generator.PlanNew
open Midfall.Generator.QuotientFold

/-- **What the generator produces for one render.** Three fields, and they are exactly the
    three fields of the frozen `Render` record a generator run determines
    (Statements.lean:84-86: `plan`, `qblocks`, `model`), in that order, at those types. That
    is deliberate and it is the whole point of the shape: OBJ.8's generated-by clause has to
    say "this render's plan IS the generator's plan", and it can only say that if the two
    sides are the same type. Nothing here edits the frozen record - the projection is on this
    side of the seam.

    `plan` is `LoweringPlan Unit Unit` because the Direct row (M10) is not ported: the two
    deferred type parameters of PL:29-45 are uninhabited, and every VM plan in the tree -
    `poseidonPlanV2` (PoseidonInputs.lean:88) included - is a `LoweringPlan Unit Unit`. -/
structure GenOut where
  /-- The finalized plan `newFromVk` returned (rust: PL:291-308). -/
  plan : LoweringPlan Unit Unit
  /-- The compact quotient blocks for the render's trace flag (rust: PL:391-406). -/
  qblocks : QuotientComputationBlocks
  /-- The render model (rust: ART:68-335, validated at ART:337-339). -/
  model : Model

/-- **THE GENERATOR.** rust: PL:235-329 + ART:68-341 in one call. Features, the field's DELTA,
    the verifier's own `VerifyingKey` (whose `cs` is the constraint system the identity stream
    comes from), the `GeneratorConfig`, the VK PAYLOAD the plan is built against, the artifact
    build inputs and the render flags in; `GenOut` out, or a panic at the reference's own site.

    THE SEVEN ARGUMENTS ARE THE SEVEN THINGS THE RUST READS, each from where the Rust reads it:
    * `feat` - the features the meta and the payload layout are built under (VK:505-509 is the
      one runtime branch the port carries for it).
    * `delta` - not a Rust argument at all: the reference resolves `PrimeField::DELTA` from the
      field and Lean has no dictionary to resolve it from, so the caller supplies it and
      `frFieldCtx` (PlanNew.lean:152) is the record it fills. OBJ.6's gate 1 pins the value
      against `curves/src/bls12_381/fq.rs:492`. It is load-bearing and not decoration: the
      quotient blocks print it, so a wrong delta is a different contract - GeneratedKats
      gate 9 falsifies exactly that.
    * `vk` - `inputs.vk`, reached for `self.vk.cs()` (QRS:166, :426) and for nothing else here.
    * `cfg` - `num_instances`, `num_committed_instances` and `accumulator` (API:375-380), and
      BAPI:64 is the reference's own `ConstraintSystemMeta::new(vk.cs(),
      config.num_committed_instances)`.
    * `payload` - the output of `inputs.generate_vk()` (PL:237). It is an INPUT here because
      generate_vk is not ported on this card (the card forbids it; OBJ.10 owns the split), and
      that substitution is exactly what `vkCarriesBuild` (PlanNew.lean) has to police: a
      payload whose quotient sections are not the lowered program is refused at vk.rs:457.
    * `inputs`, `flags` - ART:68's other two arguments, unchanged.

    THE META IS THE RAW ONE, ON PURPOSE. `ConstraintSystemMeta.new` (ENC:454-466) yields
    `num_point_sets = 0`; the plan's meta is what `metaDataForStableStaticLayout` converges to
    after `set_num_dummy_evals` and `set_num_point_sets` (VK:510-517). REVIEW-V3 A-1's finding
    was that frozen clause 1 equates the plan's meta with the raw `new` and is therefore false
    of every faithful plan; this seam reproduces the reference's order - raw in, converged out -
    and GeneratedKats gate 3 prints both, so the disagreement is on the record and not buried.

    THE EMITTER CLOSURE IS `(fun _ _ => blocks)` AND NOT A SECOND CALL. The Rust reaches
    `compact_quotient_blocks` exactly once, through the injected emitter, at `flags.trace`
    (ART:146 -> PL:368-370 -> PL:391-406). Computing the blocks at `flags.trace` and handing
    back a constant closure is therefore the same value on the path the generator takes - and
    it is the shape frozen clause 4 already states
    (`generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = .ok R.model`,
    Statements.lean:218), which is what lets OBJ.8 tie `out.qblocks` to `R.qblocks` without
    restating a call. -/
def generateAll {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (feat : Features) (delta : Fr p) (vk : VerifyingKey (Fr p) G₁)
    (cfg : GeneratorConfig) (payload : Halo2VerifyingKey) (inputs : ArtifactBuildInputs)
    (flags : RenderFlags) : Except Fault GenOut := do
  let field := frFieldCtx delta
  -- BAPI:64: the raw meta the receiver is built with.
  let rawMeta <- ConstraintSystemMeta.new feat vk.cs cfg.numCommittedInstances
  -- PL:235-329.
  let plan <- newFromVk feat field vk.cs rawMeta cfg.numInstances cfg.accumulator payload
  -- PL:391-406, at the render's trace flag.
  let blocks <- compactBlocksOf field vk.cs plan flags.trace
  -- ART:68-335.
  let model <- generateVerifierFromPlan (fun _ _ => blocks) inputs flags plan
  -- ART:337-339: the model is returned only if it validates.
  match Halo2Verifier.validateLayout model with
  | .ok () => pure { plan := plan, qblocks := blocks, model := model }
  | .error err =>
      throw (Fault.panic (siteArt 339 ("invalid generated verifier layout: " ++ err)))

end Midfall.LoweringV2
