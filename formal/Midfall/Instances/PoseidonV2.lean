/-
  Midfall.Instances.PoseidonV2

  C.1 (SEM / SKELETON): THE HEADLINE, STATED AT A DEPLOYMENT. This file forms the first
  `Midfall.LoweringV2.Render` in the tree - `poseidonRender` - out of D.1's five generator-side
  terms (`Instances/PoseidonInputs.lean`) and D.2's five verifier-side terms
  (`Instances/PoseidonEnv.lean`), states `lowering_equivalence_poseidon` for EVERY pairing
  product, and proves it from exactly three named sorried lemmas. Until this file there was no
  cone root: the two existing roots are the generic composition theorem and the generic end-to-end
  corollary, and neither is a deployment, so `#cone_sorries` measured nothing that a card could
  move.

  WHAT THIS FILE IS NOT. It proves nothing about the program. The three lemmas are `sorry`, they
  are registered in SORRY.md, and each says what would discharge it. What is delivered is that the
  obligations are now stated AT A RENDER - typed, kernel-checked, with a dependency cone.

  ## THE ONE JUDGEMENT CALL: `Render.model`

  `Render.model` is a bare `Model` (`Statements.lean:86`, `Program.lean:37`). D.1 delivers
  `poseidonModel : Except Fault Model`, and its own docstring records why it stops there: there
  is no `Inhabited Model` to totalise the `.error` arm, and `Halo2Verifier` has 71 fields, so a
  literal fallback would be a transcription of the artifact this render is supposed to be DERIVED
  from. The card names that as a stop-and-report, and it IS reported - as gap (b) below.

  It is not a licence to fabricate, and nothing here fabricates. `poseidonModel_isOk` is proved by
  `native_decide` - by RUNNING the ported generator - and `poseidonModelVal` sends the `.error`
  arm to `False.elim` of that proof. The error arm is not defaulted, it is shown unreachable, and
  the only two inhabitants of the match are the real `.ok` payload and `False`.

  `native_decide` is the sanctioned computation channel in `Midfall/Instances/` (D-P17
  confinement; `Statements.lean:136-138` says the `Valid` clauses are to be discharged "by
  `decide`, `rfl` or, in `Instances/`, `native_decide`"). Its cost is a fourth axiom in the
  headline's `#print axioms` - the generated `PoseidonV2.poseidonModel_isOk.native_decide`
  constant - which is compiler-trusted, not kernel-trusted. That is a real weakening of the
  evidence and it is stated here rather than left in the axiom list for a reader to find. It is
  the same base the fixture exhibits already stand on (`Instances/FrameWalkWitness.lean:305-350`,
  `Instances/SurfaceFixture.lean:594`).

  ## PREMISE GAPS, stated rather than worked around

  (a) `Render.cfg` has NO source in D.1 or D.2. Neither file supplies a `GeneratorConfig`. It is
      formed here as `GeneratorConfig.new 1 1`, and `poseidonConfig_forced` pins that the values
      are DETERMINED rather than chosen: `Valid.inputs` demands `inputs.numInstances =
      cfg.numInstances` and `poseidonInputs.numInstances` is 1 (`DeployedProfile.lean:123`);
      `SupportedV2.instShape` demands `cfg.numCommittedInstances = 1`; `SupportedV2.noAcc`
      demands `cfg.accumulator = none`; and `GeneratorConfig.new` (`Api.lean:827`) is the only
      constructor that sets the last two. Any other triple fails one of the three.
  (b) `Render.model` exists only as a projection of an `Except` whose error arm is proved
      unreachable. See the judgement call.
  (c) MEASURED HERE, NOT IN THE CARD: the kernel will NOT reduce `poseidonModel`. `by decide` and
      `rfl` on `poseidonModel.isOk = true` both fail ("reduction got stuck at `match
      poseidonModel with`"), so `generateVerifierFromPlan` is VM-reducible and not
      kernel-reducible. The consequence is that `Valid.model` - an equality of two `Except`s over
      a 71-field record with no `BEq` and no `DecidableEq` - is NOT machine-dischargeable at this
      render by any of the three channels `Statements.lean:136-138` names, even with the bare
      `Model` in hand. It is true (the render's model is a projection of exactly that call) and it
      is not provable by computation here. That is a finding about `Valid`, not about this card.
  (d) `poseidon_valid` is REFUTED-AT-TYPED-IN-META, not open. D.3
      (`Instances/PoseidonCoherence.lean`) proves `Valid.layout` and `Valid.circuitMeta`
      unsatisfiable at `poseidonPlanV2.meta_`, root cause `check2_typedInProtocolIsDefault`
      (`planM.protocol = protocolPlanDefault`, by `rfl`). The headline is still statable because
      `LoweringEquivalence R product` takes no `R.Valid` hypothesis (`Statements` §5); `Valid`
      enters only through `blockContracts_of_valid`, and that is where the sorry sits.

  ## THE IMPORT CONE, and the one edit outside this file

  `#imports_avoid` in `ConeReport.lean` is a FILE-level check: it fails if ConeReport transitively
  imports any of the AVOID 14. `Midfall.Instances.PoseidonEnv` transitively imports TEN of them,
  and every one arrives through a single edge - `PoseidonEnv -> CurveSurface ->
  {Lowering.Partials, Instances.ImportedIR, Yul.ImportSolcIR, Instances.ObligationsGates}`.
  Measured: with that one edge removed, PoseidonEnv's closure contains ZERO AVOID modules. The edge
  exists for exactly one theorem, `poseidonEncG2_isCurveSurfaceEncG2`, which pins `poseidonEncG2`
  against `curveSurface.encG2` and which nothing else references. It has been MOVED (not deleted)
  into `Instances/CurveSurface.lean`, where the term it talks about lives, so the pin survives and
  the V2 cone stays cut off from retired v1. Without that move this card cannot land: importing the
  render into ConeReport would redden the very guard whose job is to stop a retired module
  re-entering through an instance file.

  ## WHAT THE CONE SAYS

  `#cone_sorries lowering_equivalence_poseidon` is the first real number for the headline root and
  ConeReport prints it, with `#cone_avoids` beside it.
-/
import Midfall.Instances.PoseidonEnv
import Midfall.Instances.PoseidonInputs
import Midfall.LoweringV2.Blocks

namespace Midfall.Instances.PoseidonV2

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions Midfall.Yul
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs
open Midfall.LoweringV2

/-! ## 1. The model: an `Except` with a proved-unreachable error arm -/

/-- **THE GENERATOR CALL SUCCEEDS.** `poseidonModel.isOk` by `native_decide`, i.e. by running
    `generateVerifierFromPlan` on the pure D.1 inputs. D.1 states the same fact as a `Bool` the
    VM prints (`poseidonModel_isOk_ok`); here it is a theorem the kernel accepts, which is what
    makes the projection below honest: the error arm is not papered over with a default, it is
    proved impossible. NOT provable by `decide` or `rfl` - gap (c) of the header. -/
theorem poseidonModel_isOk : poseidonModel.isOk = true := by native_decide

/-- The error arm, closed: `.error` would make `isOk` false, and it is true. -/
theorem poseidonModel_notError (e : Fault) (h : poseidonModel = .error e) : False := by
  have h2 : poseidonModel.isOk = false := by rw [h]; rfl
  rw [poseidonModel_isOk] at h2
  exact absurd h2 (by decide)

/-- **THE BARE `Model` THAT `Render.model` ASKS FOR.** The projection of D.1's `Except` along
    the proof above. Nothing is invented: the only other arm of the match is `False]. -/
def poseidonModelVal : Model :=
  match h : poseidonModel with
  | .ok v => v
  | .error e => False.elim (poseidonModel_notError e h)

/-! ## 2. The one field with no upstream term -/

/-- `Render.cfg` at the deployment. NO D.1 OR D.2 TERM SUPPLIES THIS - gap (a) of the header. The
    values are forced, not chosen, and `poseidonConfig_forced` is the pin that says so. -/
def poseidonConfig : GeneratorConfig := GeneratorConfig.new 1 1

/-- **WHY `cfg` IS NOT A FREE FIELD.** The three clauses of `Valid`/`SupportedV2` that read it
    hold by `rfl` at exactly these numbers: `Valid.inputs` wants
    `inputs.numInstances = cfg.numInstances`, `SupportedV2.instShape` wants
    `cfg.numCommittedInstances = 1`, `SupportedV2.noAcc` wants `cfg.accumulator = none`. Refuted
    by any of the literals changing, on either side. -/
theorem poseidonConfig_forced :
    poseidonInputs.numInstances = poseidonConfig.numInstances ∧
      poseidonConfig.numCommittedInstances = 1 ∧ poseidonConfig.accumulator = none :=
  ⟨rfl, rfl, rfl⟩

/-! ## 3. THE RENDER -/

/-- **THE DEPLOYMENT.** `Render blsR G₁z G2fold blsGT` - D.2's carrier triple over D.1's generator
    terms. Every field is a citation of an existing term except `cfg` and `model`, and both are
    explained at their site and in the header.

    Field by field, which is the card's own acceptance question ("whether `poseidonRender` formed
    and from which terms"):

      `E`        `poseidonE`          D.2 term 1          `PoseidonEnv.lean:379`
      `params`   `poseidonParams`     D.2 term 2          `PoseidonEnv.lean:391`
      `vk`       `poseidonVkExec`     D.2 term 3          `PoseidonEnv.lean:367`
      `sG2gen`   `poseidonSG2`        D.2 term 4          `PoseidonEnv.lean:386`
      `encG2`    `poseidonEncG2`      D.2 term 5          `PoseidonEnv.lean:399`
      `cfg`      `poseidonConfig`     NO SOURCE - gap (a)  this file, §2
      `inputs`   `poseidonInputs`     D.1 via DeployedProfile  `DeployedProfile.lean:122`
      `flags`    `poseidonFlags`      D.1 via DeployedProfile  `DeployedProfile.lean:132`
      `plan`     `poseidonPlanV2`     D.1 term 2          `PoseidonInputs.lean:88`
      `qblocks`  `poseidonQBlocks`    D.1 term 4          `PoseidonInputs.lean:111`
      `model`    `poseidonModelVal`   D.1 term 5, projected  this file, §1 -/
noncomputable def poseidonRender : Render blsR G₁z G2fold blsGT where
  E := poseidonE
  params := poseidonParams
  vk := poseidonVkExec
  sG2gen := poseidonSG2
  encG2 := poseidonEncG2
  cfg := poseidonConfig
  inputs := poseidonInputs
  flags := poseidonFlags
  plan := poseidonPlanV2
  qblocks := poseidonQBlocks
  model := poseidonModelVal

/-- The three projections every downstream card reads, pinned by `rfl` so a later edit to the
    record cannot quietly re-point them. -/
theorem poseidonRender_plan_isD1 : poseidonRender.plan = poseidonPlanV2 := rfl
theorem poseidonRender_vk_isD2 : poseidonRender.vk = poseidonVkExec := rfl
theorem poseidonRender_E_isD2 : poseidonRender.E = poseidonE := rfl

/-! ## 4. THE THREE LEMMAS -/

/-- **LEMMA 1 OF 3 - STATUS: REFUTED-AT-TYPED-IN-META.** `poseidonRender.Valid`, the eleven
    computation clauses of `Statements` §2.

    NOT merely open. D.3 proves two of the eleven UNSATISFIABLE at the plan this render carries:
    `check2_circuitMeta_holds` is false and `check1_validLayout_holds` is false, and the root
    cause is `check2_typedInProtocolIsDefault` - `poseidonPlanV2.meta_.protocol =
    protocolPlanDefault`, by `rfl`. The typed-in `poseidonMeta` (`DeployedProfile.lean:81`)
    carries no `ProtocolPlan` because the halo2 `ConstraintSystem` of the circuit is not in the
    tree, and `ProofCalldataLayout.fromProtocol` refuses a default protocol. No amount of
    computation discharges this lemma at this plan. A third clause, `model`, is true but not
    machine-dischargeable either (gap (c)).

    WHAT WOULD DISCHARGE IT: porting `ProtocolPlan::from_constraint_system` - the circuit gap, and
    D.3's plan-level blocker - so that `poseidonPlanV2.meta_` is the ported meta rather than a
    transcription of counts. Then `circuitMeta` and `layout` become computations like the other
    clauses. The headline below does NOT depend on this lemma being dischargeable; it depends on it
    being STATED, because `Valid` enters only through `blockContracts_of_valid`. -/
theorem poseidon_valid : poseidonRender.Valid := by
  sorry

/-- **LEMMA 2 OF 3 - STATUS: OPEN.** The quotient block: the one `Partial` that
    `blockContracts_of_valid` cannot cover generically, because its code is a function of
    `poseidonRender.qblocks` as well as of the plan view (GAP G3 - the unported QRS:2000
    `compact_quotient_computation_blocks`; `qblocks` here is CHECKED data sliced out of the
    artifact, `PoseidonInputs.lean:111`).

    Stated as the missing half of `BlockContractsAt`: the generic theorem gives every partial
    except `.quotientLin`, this gives `.quotientLin`, and `poseidon_block_contracts` glues them
    with no third sorry.

    WHAT WOULD DISCHARGE IT: WP-M0's staged contract for `Partial.quotientLin` at this render -
    `BlockSound` and total `BlockProgress` for `poseidonRender.slice .quotientLin` in
    `poseidonRender.scope`, over the quotient VM the D.1 blocks actually emit. That is a block
    proof, which this card does not open. -/
theorem poseidon_quotient_block (product : PairingProduct) :
    poseidonRender.BlockContractsAt product (fun q => q = Partial.quotientLin) := by
  sorry

/-- **LEMMA 3 OF 3 - STATUS: OPEN.** Program-level rejection at this render (`Blocks.lean:134`):
    where the Lean verifier does not accept, outside the logup-panic bad set, every run of the
    generated program reverts or halts. This is the half of soundness the block contracts do not
    cover, because they assume a snapshot exists.

    WHAT WOULD DISCHARGE IT: WP-M0's STAGED per-block rejection contracts - the Lean state reached
    so far, from `snapshotOfTrace` to `snapshotOfPcs`, with the stage fault each block is
    responsible for - composed at `poseidonRender.prog`. Stated at program level because that is
    the shape `lowering_equivalence_of_blocks` consumes. -/
theorem poseidon_rejects (product : PairingProduct) : poseidonRender.Rejects product := by
  sorry

/-! ## 5. THE HEADLINE -/

/-- The two halves of `BlockContractsAt` glued: the generic six from `blockContracts_of_valid`,
    which covers every partial but `.quotientLin`, and the quotient one from lemma 2. NO SORRY
    HERE - it is a re-indexing of the two hypotheses, and it is the only place the split is paid
    for. -/
theorem poseidon_block_contracts (product : PairingProduct) (hR : poseidonRender.Valid) :
    poseidonRender.BlockContractsAt product (fun _ => True) := by
  refine fun hpc H vkAddr cd ms instW inst Snap h1 h2 h3 q _ => ?_
  by_cases hq : q = Partial.quotientLin
  · exact poseidon_quotient_block product hpc H vkAddr cd ms instW inst Snap h1 h2 h3 q hq
  · exact blockContracts_of_valid poseidonRender product hR hpc H vkAddr cd ms instW inst Snap
      h1 h2 h3 q hq

/-- **THE HEADLINE, AT THE DEPLOYMENT, FOR EVERY PAIRING PRODUCT.**
    `LoweringEquivalence poseidonRender product` - the three-part statement of `Statements` §5
    (soundness under poisoned precompiles and any gas oracle, total completeness under the honest
    ones, two outcomes) quantified over every world, layout, hash, VK address, calldata and entry
    frame. No hypothesis on the product, and no `R.Valid` hypothesis in the statement.

    Proved from exactly three sorried lemmas - `poseidon_valid` (REFUTED-AT-TYPED-IN-META),
    `poseidon_quotient_block` (open), `poseidon_rejects` (open) - through the generic composition
    theorem `lowering_equivalence_of_blocks`. ST.4's headline asks every conjunct for
    `G1CodecHeadlineLaws`, and the progress half of `BlockContractsAt` is now gated on the SAME
    bundle (ST.5 step 3, pulled forward: the seven frozen laws are not derivable from four, and
    the only in-tree witness at a real codec, `CurveSurface.g1CodecZ_laws`, sits behind the
    `imports_avoid` wall of `Tools/ConeReport.lean`, so citing it here would have polluted the
    cone). The fourth conjunct, totality, is the composition's own registered sorry
    `bodyTotal_of_valid`. `#cone_sorries` on it is the progress measure of EXECUTION-V2 §6,
    printed by ConeReport. -/
theorem lowering_equivalence_poseidon (product : PairingProduct) :
    LoweringEquivalence poseidonRender product :=
  lowering_equivalence_of_blocks poseidonRender product poseidon_valid
    (poseidon_block_contracts product poseidon_valid) (poseidon_rejects product)

/-- The headline states a deployment, not a non-vacuity: `HypothesesInhabited` (`Statements` §8)
    is a separate obligation this card does not claim, and `poseidon_valid` is refuted at the
    typed-in meta. Recorded so nobody mistakes a stated headline for an inhabited one. -/
theorem lowering_equivalence_poseidon_is_the_root (product : PairingProduct) :
    LoweringEquivalence poseidonRender product := lowering_equivalence_poseidon product

end Midfall.Instances.PoseidonV2
