/-
  Midfall.LoweringV2.Blocks.Compose

  THE COMPOSITION M.1 CAN ACTUALLY DO, AND WHERE IT HAS TO LIVE.

  WHY THIS FILE EXISTS. The hinge `blockContracts_of_valid` (Blocks.lean:152) is the only route from a
  per-block contract to C.1's headline, but it sits in `Blocks.lean` and BOTH proved per-block
  contracts live in files that import it: `Blocks/TraceReturn.lean:68` and `Blocks/FinalPairing.lean:117`
  each say `import Midfall.LoweringV2.Blocks`. So Blocks.lean cannot cite a single per-block contract
  without a module cycle, and the composition has to be written downstream of all three. That is this
  file. It is the landing site: every future per-block row (T.3, T.4, T.5 and the four cards that do
  not exist yet) is a `BlockRow` added here, and `blockContracts_of_valid_of_rows` (Blocks.lean)
  turns six of them into the hinge with no further work.

  WHAT IS PROVED HERE, AND WHAT IT COSTS. Two of the six rows:
  * `tr_blockRow` — TraceReturn, sorry-free, and since OBJ.4 IT COSTS NOTHING. It used to carry
    `trRetMptr R` (the RETURN_MPTR pin) as a free premise, and M.1's brief correctly counted that as
    a second premise gap. That gap is closed: `RETURN_MPTR` is an UNCONDITIONAL entry of
    `expectedConsts`, so `Consts.lean` derives the pin from `Render.Valid` alone
    (`trRetMptr_of_valid`) and the row now takes no render premise at all. It is the first of the six
    rows to need none.
  * `fp_blockRow` — FinalPairing, sorry-free over its own three groups, at the cost of `fpG2Slots R`
    the unresolved human decision; carried as an explicit hypothesis, never assumed.

  WHY THIS DOES NOT MOVE THE HEADLINE CONE, stated plainly because it is the card's main
  finding. `slices_seq_sound` and `slices_seq_progress` (Blocks.lean:307, :325) take
  `h7 : ∀ q : Partial, BlockSound R q ...` and `∀ q : Partial, BlockProgress R q ...`, and `Render.slices`
  concatenates all seven slices, so two rows out of seven discharge nothing: `blockContractsAt_twoRows`
  has no consumer. `cone_sorries lowering_equivalence_poseidon` stays 11 with this file in the tree,
  and stays 11 until ALL SIX non-quotient rows exist — at which point it drops to 10 (the hinge's
  own sorry disappears) and no further, because the other ten are C.1's three deployment
  sorries, C.2's five composition obligations and the registered Bridge transport.

  NO `sorry` IN THIS FILE.
-/
import Midfall.LoweringV2.Consts
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Blocks.FinalPairing
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.LoweringV2.Blocks.VkLoading

namespace Midfall.LoweringV2.Blocks

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-- **ROW `traceReturn` — THE ONE FULLY PROVED BLOCK, IN M.1'S OWN WRAPPER.** T.1's `tr_blockSound`
    and T.2's `tr_blockProgress` are already stated at exactly the dialect §6 asks for (the
    permissive dialect for soundness, the honest calls with zero gas for progress), so the row is a
    re-wrap: no transport, no new semantics, no `sorry`. Since OBJ.4 it carries no render premise
    either: `trRetMptr R` is projected from `hR` by `Consts.trRetMptr_of_valid` (header). -/
theorem tr_blockRow (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    BlockRow R product .traceReturn := by
  intro hR _hpc H vkAddr cd ms instW inst Snap _hdec _hinst _hsnap
  -- THE REWIRE (OBJ.4): `RETURN_MPTR` is an UNCONDITIONAL entry of `expectedConsts`, so `trRetMptr`
  -- is now a THEOREM of `Render.Valid` (`Consts.lean` §5, `trRetMptr_of_valid`) and this row takes no
  -- render premise at all. It is the first of the six rows to need none.
  refine ⟨fun g => ?_, fun _hcodec _hcg _hdual => ?_⟩
  · exact TraceReturn.tr_blockSound R product Snap H vkAddr g cd
  · exact TraceReturn.tr_blockProgress R product (trRetMptr_of_valid hR) Snap H vkAddr cd

/-- **ROW `finalPairing`, IN M.1'S OWN WRAPPER.** FP.0 already states its contract as
    `BlockContractsAt product (· = .finalPairing)`, so the row is one instantiation at
    `q := .finalPairing`. It carries `fpG2Slots R` as an explicit hypothesis: that is FP.0's
    premise gap and an UNRESOLVED human decision, and nothing here discharges it. Its cone is FP.0's
    three groups (`fp_pairing_algebra`, `ec_pairing_contract`, `fp_stmt_steps`), not a new hole. -/
theorem fp_blockRow (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hslots : FinalPairing.fpG2Slots R) : BlockRow R product .finalPairing :=
  fun hR hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap =>
    FinalPairing.fp_finalPairing_contracts R product hR hslots hpc H vkAddr cd ms instW inst Snap
      hdec hinst hsnap Partial.finalPairing rfl

/-- **ROW vkLoading, IN M.1'S OWN WRAPPER (S.4, REWIRED BY D-P50/S.9, REWIRED AGAIN BY ST.6).
    The third of the six, and unlike the two below it is NOT sorry-free: `VkLoading.vk_blockRow`
    carries the three named gaps of Blocks/VkLoading.lean section 6 (the clean walk, the poisoned
    walk, the exhibited run). Under D-P50 it carried no render hypothesis at all, because `vkPins`
    and `vkProgressPins` were clauses 12-13 of `Valid`; ST.6 (D-P67) cut `Valid` over to the seven
    V3 clauses, in which the two bundles are not clauses but obligations of the `program` clause -
    and OBJ.4 has now ported FOUR of the six bundle fields: `vkMptr`, `payloadLen`, `vkLen` and
    `vkHash` are lookups in `expectedConsts` and `Consts.lean` derives all four from `hR`
    (`vkPins_of_valid`, `vkProgressPins_of_valid`). What it CANNOT derive, because neither mentions a
    constant name, is `numInst` (`R.model.numInstances = R.cfg.numInstances` — a generator-spec fact
    whose source is the `generated` clause) and `disjoint` (a layout inequality whose source is
    `supported.layout`). Those two, plus the `expectedVkCodehash` arm the three guarded lookups need,
    are what this row still asks for — three named residuals instead of two opaque bundles.
    `fp_blockRow` still carries `fpG2Slots`; `tr_blockRow` now carries nothing. S.8's deployment proofs
    (`Instances/PoseidonPins.lean`) are what discharge them at `poseidonRender`. It lands here
    anyway because it fixes the SHAPE the four missing rows must have, and because the interface it
    needed (that file's sections 1-4: the slice form with the shadow-list refinement T.1 did not
    need, the site inversion, the fail helper at an ARBITRARY selector site, the recurring assign
    inversion, the VEnv set/get fact) is sorry-free and is what S.5, S.6 and S.7 can reuse
    verbatim. -/
theorem vk_blockRow (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hcode : vkCodehashArm R.model)
    (hnum : R.pv.numInstances = R.cfg.numInstances)
    (hdisj : ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
      ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr) :
    BlockRow R product Partial.vkLoading :=
  VkLoading.vk_blockRow R product hcode hnum hdisj

/-- **TWO OF THE SIX ROWS COMPOSE.** The demonstration that `BlockRow` is the right shape: both
    proved contracts fit §6's wrapper with no refinement of `Frame`/`Clean`/`Poisoned` and no
    new field — and since OBJ.4 the only thing they need that `Valid` does not give is `fpG2Slots`. Read
    this as the acceptance test for the four missing rows: each must produce a `BlockRow` and
    nothing more. -/
theorem blockContractsAt_twoRows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hslots : FinalPairing.fpG2Slots R) :
    R.BlockContractsAt product (fun q => q = Partial.finalPairing ∨ q = Partial.traceReturn) :=
  blockContractsAt_of_rows R product hR (fun q => q = .finalPairing ∨ q = .traceReturn)
    fun q hq => by
      rcases hq with rfl | rfl
      · exact fp_blockRow R product hslots
      · exact tr_blockRow R product

#print axioms Midfall.LoweringV2.Blocks.vk_blockRow
#print axioms Midfall.LoweringV2.Blocks.tr_blockRow
#print axioms Midfall.LoweringV2.Blocks.blockContractsAt_twoRows

end Midfall.LoweringV2.Blocks
