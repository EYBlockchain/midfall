/-
  GeneratorTheorem.lean — D-P71: the deliverable is the generator theorem.

  EVIDENCE, not landed code (see ../../README.md). Card PL.H lands this file's statements in the
  tree; cards DG.4 / DG.9 land `GeneratorDone`.

  RECON.1b REBASE. Every theorem here is stated over the ONE `Midfall.LoweringV3.ValidV3` — the
  seven-clause text RECON.1 landed at `Midfall/LoweringV3/Statements.lean:1116` — and this file now
  imports that landed module, NOT the eighteen-clause draft still kept in `StatementsV3.lean` beside
  it (the D-P67 fallback, which RECON.1's Guidance keeps in the evidence directory). One file, one
  `ValidV3`: nothing here names a second text, and no clause is read that the single text does not
  have. Where the old text had a clause the new one folds into `programOk`, the projection named by
  RECON.1 is used (`exitDiscipline_of_valid`, `noWriters` is a clause).

  WHAT IS HERE
    §1  The four obligations of the V3 headline, each stated FOR EVERY RENDER from `ValidV3 R`.
        `twoOutcomes_correct` is proved from two `ValidV3` clauses. The other three are the open
        work of milestones M5-M6 and carry a named `sorry` each.
    §2  `lowering_correct`: the headline of D-P71. PROVED from §1 (no `sorry` of its own).
    §3  `GateAtV3` and `GeneratorDone`: the definition of done with no fixture in the headline.
    §4  W12 evidence. Witness: the generic headline instantiates at the test render. Falsifier:
        the headline with `hR : ValidV3 R` dropped is refuted (`lowering_correct_needs_valid`,
        no `sorry`).

  WHAT IS NOT HERE. The staged rows (`SimContracts`, `ProgContracts`) are in
  `../soundness/GeneratorRows.lean`: `statements/` and `soundness/` are separate roots of
  `check.sh`, and cards RECON.1 / RECON.2 own their reconciliation.
-/
import Midfall.LoweringV3.Statements
import Midfall.Instances.StatementsV3Falsifiers

set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
variable [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §1. The four obligations, for every render -/

/-- Obligation 1 (syntactic). PROVED from the two scan clauses of the single `ValidV3`: `noWriters`
    is a clause, and the exit scan is the projection `exitDiscipline_of_valid` of the `program`
    clause (RECON.1 addition 5 — ONE scan in the text, not two). Its own cone still holds the two
    sorries of `twoOutcomes_of_scans` (`Midfall/LoweringV3/Statements.lean`; cards ST.11, ST.12). -/
theorem twoOutcomes_correct (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) : TwoOutcomes R :=
  twoOutcomes_of_scans R hR.noWriters (exitDiscipline_of_valid hR)

/-- Obligation 2 (soundness). OPEN: this is `rejectsV3_of_sims` applied to the staged rows of
    `GeneratorRows.lean` (`rows_correct`); cards RECON.2, SIM.5, and every ROW card. -/
theorem rejects_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    RejectsV3 R product := by
  sorry -- OPEN (M5-M6): the staged simulation rows, for every R

/-- Obligation 3 (completeness). OPEN: `completeV3_of_progs` applied to the progress rows. -/
theorem complete_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    CompleteV3 R product := by
  sorry -- OPEN (M5-M6): the staged progress rows, for every R

/-- Obligation 4 (totality). OPEN: card TOT.1, restated for every render. -/
theorem total_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    TotalV3 R product := by
  sorry -- OPEN (M6): TOT.1 for every R

/-! ## §2. The headline of D-P71 -/

/-- **THE GENERATOR THEOREM.** For every render the Lean port of the generator emits for a circuit
    in the supported class (`hR : ValidV3 R` contains the generated-by, payload and scope
    clauses), and for every pairing answer `product`, the four conjuncts of the V3 headline hold.
    No fixture occurs in the statement. PROVED from the four obligations of §1. -/
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    LoweringEquivalenceV3 R product :=
  lowering_equivalenceV3_of R product (twoOutcomes_correct R hR) (rejects_correct R product hR)
    (complete_correct R product hR) (total_correct R product hR)

/-! ## §3. The definition of done, with no fixture in the headline -/

/-- The non-vacuity gate at a GIVEN calldata: `HypothesesInhabitedV3`
    (`Midfall/LoweringV3/Statements.lean:1483`)
    with `cd` supplied by the caller, so that the gate speaks about the test bundle's calldata and
    not about some calldata. -/
def GateAtV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (cd : Bytes) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256) (st₀ : EvmState),
    DeploymentV2 R W keccak256 vkAddr ∧ EntryFrameV3 R W Lyt keccak256 cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ G1CodecHeadlineLaws R.E.g1 ∧
      LeanAccepts R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd

/-- Nothing is lost by pinning the calldata. PROVED. -/
theorem hypothesesInhabitedV3_of_gateAtV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (cd : Bytes) (h : GateAtV3 R product cd) : HypothesesInhabitedV3 R product := by
  obtain ⟨W, Lyt, vkAddr, st₀, h⟩ := h
  exact ⟨W, Lyt, vkAddr, cd, st₀, h⟩

/-- **DONE, the proof part** (D-P71; replaces the first three fields of PLAN-V3 §6's `Done`).
    `Rt` is a TEST render and `cd` its test calldata: they occur only in `nonvacuous`. The
    remaining fields of `Done` (`reference`, `artifact`, `vkArtifact`) are computations about the
    test bundle and are added in `tooling/` by card DG.4, unchanged. -/
structure GeneratorDone (Rt : Render p G₁ G₂ Gₜ) (cd : Bytes) : Prop where
  /-- The generator theorem: every render, every pairing answer. -/
  headline : ∀ (R : Render p G₁ G₂ Gₜ) (product : PairingProduct),
    ValidV3 R → LoweringEquivalenceV3 R product
  /-- The theorem is not vacuous: its hypothesis and the headline's hypotheses hold together at
      one real circuit, whose calldata the Lean verifier accepts. -/
  nonvacuous : ValidV3 Rt ∧ ∃ product : PairingProduct, GateAtV3 Rt product cd

/-- What `GeneratorDone` buys at the test render, PROVED: an honest run exists and returns the
    ABI word `true`. (`returns_of_inhabited` through the two fields.) -/
theorem GeneratorDone.returns {Rt : Render p G₁ G₂ Gₜ} {cd : Bytes} (h : GeneratorDone Rt cd) :
    ∃ (product : PairingProduct) (vkAddr : U256) (st₀ : EvmState) (obs : Obs),
      RunBody Rt vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs ∧
        obs.view = returnView st₀ := by
  obtain ⟨hR, product, hg⟩ := h.nonvacuous
  exact ⟨product, returns_of_inhabited Rt product (h.headline Rt product hR)
    (hypothesesInhabitedV3_of_gateAtV3 Rt product cd hg)⟩

/-! ## §4. W12: the witness and the falsifier of the generic headline -/

section Witness
open Midfall.Instances.PoseidonV2

/-- WITNESS (shape). The generic headline instantiates at the test render; nothing else is
    needed there. The hypothesis `ValidV3 poseidonRender` is refuted today
    (`Midfall/Instances/PoseidonValid.lean: poseidonRender_notValid`, sorry-free through `supported`;
    `generated` refutes it independently, `Midfall/Instances/StatementsV3Deploy.lean`) and becomes
    provable at the exit of milestone M4; until then this `example` shows the instantiation
    typechecks. `Valid poseidonRender` is NOT inhabited and this card did not weaken a clause. -/
example (product : PairingProduct) (hR : ValidV3 poseidonRender) :
    LoweringEquivalenceV3 poseidonRender product :=
  lowering_correct poseidonRender product hR

end Witness

section Falsifier
open Midfall.LoweringV3.Falsifiers

/-- The V3 entry frame transfers to the bumped render field by field. -/
theorem entryFrameV3_bump {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrameV3 R W Lyt H cd st) :
    EntryFrameV3 (bumpInst R) W Lyt H cd st :=
  ⟨h.shape, h.zeroAbove, h.fmp, h.callvalue, h.selector, h.cdSize⟩

/-- **FALSIFIER.** The headline with `hR : ValidV3 R` dropped is false. Take any render `R` with
    ONE accepted calldata and a returning permissive run (what conjunct 2 of the headline promises
    at every render the gate holds for). `bumpInst R` configures one more public instance: its
    program, constants and runs are `R`'s by `rfl`, and its Lean verifier rejects everything `R`
    accepts (`leanAccepts_bump_false`). So conjunct 1 at `bumpInst R` is false: the same run
    returns, and Lean does not accept. `bumpInst R` is not `ValidV3` (its `inputs` clause fails),
    which is exactly what `hR` excludes. PROVED, no `sorry`. -/
theorem lowering_correct_needs_valid (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrameV3 R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hacc : LeanAccepts R H cd) (hss : SoundSide (bumpInst R) H cd)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs)
    (hret : obs.isReturn) :
    ¬ ∀ R' : Render p G₁ G₂ Gₜ, LoweringEquivalenceV3 R' product := by
  intro hall
  obtain ⟨h1, _, _, _⟩ := hall (bumpInst R) W Lyt H vkAddr cd st₀ (deployment_bump hdep)
    (entryFrameV3_bump hentry) hpc hcodec
  exact leanAccepts_bump_false R H cd hacc (h1 g obs hobs hret hss).2

end Falsifier

/-! ## Axiom audit -/

#print axioms lowering_correct               -- sorryAx: the three open obligations and the two scans
#print axioms hypothesesInhabitedV3_of_gateAtV3  -- no sorryAx
#print axioms GeneratorDone.returns          -- no sorryAx
#print axioms lowering_correct_needs_valid   -- no sorryAx

end Midfall.LoweringV3
