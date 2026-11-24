/-
  Midfall.LoweringV3.BlockLive

  FINAL ASSEMBLY - **THE SEVEN-BLOCK CASE TABLE AND THE TWO OBLIGATIONS THAT SPEND IT.**

  WHY THIS MODULE EXISTS. `block_live` and `totalV3_correct` cannot be closed in `Totality`: the
  closed case proofs live ABOVE it (`FpFit.block_live_finalPairing`, and the per-block contracts of
  `PcsBlock4`/`LagrangeBlock`), while `Totality` is below every one of them. So the two declarations
  move here, above the case modules and below `Composition` (which imports this module for
  `totalV3_correct`). The statements are the ones `Totality` carried, VERBATIM; nothing is weakened,
  no hypothesis is added.

  THE CASE TABLE. `block_live` is a seven-way dispatch, one named theorem per block:

    | block            | case theorem                        | state   |
    |------------------|-------------------------------------|---------|
    | vkLoading        | `block_live_case_vkLoading`         | CLOSED  |
    | transcriptParser | `block_live_case_transcriptParser`  | OPEN    |
    | lagrange         | `block_live_case_lagrange`          | OPEN    |
    | quotientLin      | `block_live_case_quotientLin`       | OPEN    |
    | pcs              | `block_live_case_pcs`               | OPEN    |
    | finalPairing     | `block_live_case_finalPairing`      | CLOSED  |
    | traceReturn      | `block_live_case_traceReturn`       | CLOSED  |

  The three closed rows WIRE the existing theorems (`Totality.block_live_vkLoading`,
  `FpFit.block_live_finalPairing`, `Totality.block_live_traceReturn`). The four open rows are the
  ONLY inputs left in this module; `block_live` itself is PROVED from the table, so its own cone is
  the four case rows and nothing else. Each open row names its reduction theorem in `Totality` and
  the row statement its owner must strengthen.

  THE STATEMENT MISMATCH THE OPEN ROWS RECORD (measured, not assumed). The generic packers
  (`Totality.block_live_of_blockProgS`, `block_live_pcs`, `block_live_transcriptParser_of_prog`,
  `block_live_quotientLin_of_prog`) close a case from a `BlockProgS` over `StageInv` with NO
  acceptance premise. The landed row statements in `Rows` (`lag_blockProgS`, `pcs_blockProgS`,
  `tp_blockProgS`) and `QuotientRows` (`q_blockProgS`) additionally take
  `hacc : LeanAccepts R H cd` and `hcomp : CompleteSide R H cd`. Those two facts are NOT available
  to `block_live` (it is unconditional in the calldata), so the rows cannot be wired as stated.
  The open rows are therefore stated at `BlockLive` itself; the residual is the unconditional
  progress row, which is what the owner lanes must land. Adding `hacc`/`hcomp` to `block_live`
  would weaken its statement and is forbidden (D-P71).

  D-P71: every statement here is generic in the render and carries no fixture. The only holes are
  the four named case rows above.
-/
import Midfall.LoweringV3.Totality
import Midfall.LoweringV3.FpFit
import Midfall.LoweringV3.LagrangeBlock
import Midfall.LoweringV3.PcsBlock4
import Midfall.Tools.ConeSorries
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. The closed rows of the case table (wired to the existing proofs) -/

/-- **CASE `.vkLoading` - CLOSED.** Wires `Totality.block_live_vkLoading` (the existence half is
    `vk_run_exists`, the classification is `vk_clean_walkV3`). -/
theorem block_live_case_vkLoading (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .vkLoading H vkAddr product cd :=
  block_live_vkLoading R product hR H vkAddr cd

/-- **CASE `.finalPairing` - CLOSED.** Wires `FpFit.block_live_finalPairing` (the body run is
    `Totality.fpBodyRun`, the fit bundle is `fpBodyEnvFits_of_valid`, the two pointer fits are
    `pairingLhsMptr_toNat_of_valid`/`pairingRhsMptr_toNat_of_valid`). -/
theorem block_live_case_finalPairing (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .finalPairing H vkAddr product cd :=
  block_live_finalPairing R product hR hpc H vkAddr cd

/-- **CASE `.traceReturn` - CLOSED.** Wires `Totality.block_live_traceReturn` (TraceReturn halts on
    every run, so the `LiveTo` post is its non-normal disjunct; `tr_progress_ex` / `tr_poison_exists`
    supply the exhibited run). -/
theorem block_live_case_traceReturn (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .traceReturn H vkAddr product cd :=
  block_live_traceReturn R product hR H vkAddr cd

/-! ## 2. The four open rows of the case table (the only remaining inputs) -/

/-- **CASE `.transcriptParser` - OPEN (owner ROW.TP, WP A6).** Reduction available:
    `Totality.block_live_transcriptParser_of_prog` closes it from
    `BlockProgS R .transcriptParser H vkAddr product cd` over `StageInv`, with no acceptance
    premise. The landed `Rows.tp_blockProgS` / `TranscriptRows.tp_blockProgS` additionally take
    `LeanAccepts`/`CompleteSide`, which `block_live` does not have, so the row cannot be wired as
    stated (header). Residual: the unconditional progress row for this block. -/
theorem block_live_case_transcriptParser (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .transcriptParser H vkAddr product cd := by
  sorry

/-- **CASE `.lagrange` - OPEN (owner T3.9, WP A4).** Reduction available:
    `Totality.block_live_of_blockProgS` closes it from `BlockProgS R .lagrange ...` over
    `StageInv`, with no acceptance premise. The landed `Rows.lag_blockProgS` takes
    `LeanAccepts`/`CompleteSide`, which `block_live` does not have (header). Residual: the
    unconditional progress row for this block. -/
theorem block_live_case_lagrange (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .lagrange H vkAddr product cd := by
  sorry

/-- **CASE `.quotientLin` - OPEN (owner ROW.Q, QVM lane).** Reduction available:
    `Totality.block_live_quotientLin_of_prog` closes it from
    `BlockProgS R .quotientLin ...` over `StageInv`, with no acceptance premise. The landed
    `QuotientRows.q_blockProgS` / `Rows` row takes `LeanAccepts`/`CompleteSide`, which `block_live`
    does not have (header). Residual: the unconditional progress row for this block. -/
theorem block_live_case_quotientLin (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .quotientLin H vkAddr product cd := by
  sorry

/-- **CASE `.pcs` - OPEN (owner ROW.PCS, WP A9/A10).** Reduction available:
    `Totality.block_live_pcs` closes it from `BlockProgS R .pcs ...` over `StageInv`, with no
    acceptance premise. The landed `Rows.pcs_blockProgS` takes `LeanAccepts`/`CompleteSide`, which
    `block_live` does not have (header). Residual: the unconditional progress row for this block. -/
theorem block_live_case_pcs (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockLive R .pcs H vkAddr product cd := by
  sorry

/-! ## 3. The seven-block dispatch and the totality theorem -/

/-- **LEAF (TOT.1): PER-BLOCK EXISTENCE, FOR EVERY RENDER.** The statement is `Totality`'s,
    VERBATIM; the proof is the seven-row case table above (`cases q` and nothing more). Its cone is
    the three closed case proofs plus the four open rows; no hypothesis was added.
    Owner: TOT.1 (WP A12). WITNESS: `gap_lowering_correct_witness_unexhibited`.
    FALSIFIER: `mid_start_not_vacuous` (Stages.lean:672, PROVED). -/
theorem block_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (_hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (q : Partial) : BlockLive R q H vkAddr product cd := by
  cases q with
  | vkLoading => exact block_live_case_vkLoading R product hR H vkAddr cd
  | transcriptParser => exact block_live_case_transcriptParser R product hR H vkAddr cd
  | lagrange => exact block_live_case_lagrange R product hR H vkAddr cd
  | quotientLin => exact block_live_case_quotientLin R product hR H vkAddr cd
  | pcs => exact block_live_case_pcs R product hR H vkAddr cd
  | finalPairing => exact block_live_case_finalPairing R product hR hpc H vkAddr cd
  | traceReturn => exact block_live_case_traceReturn R product hR H vkAddr cd

#assert_axioms Midfall.LoweringV3.block_live_case_vkLoading
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.block_live_case_finalPairing
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.block_live_case_traceReturn
  [propext, Classical.choice, Quot.sound] native []

/-- **OBLIGATION 4, PROVED from the four named leaves** (`gasFree_of_valid`,
    `runBody_gas_oblivious`, `block_live`, `prefix_live`). This replaces `totalV3_of_stages`,
    which the unfolding of `BodyTotal` shows cannot be derived from `ProgRowsV3` at all (header).
    The `GasTotal` hypothesis is carried by the statement and not used by the glue: the gas oracle is
    arbitrary precisely because a gas-free program cannot tell one from another. -/
theorem totalV3_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R) :
    TotalV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec g _hg
  have hlive := live_append
    (prefix_live R product hR W Lyt H vkAddr cd st₀ hdep hentry)
    (slices_live R product H vkAddr cd
      (fun q => block_live R product hR hcodec hpc H vkAddr cd q))
  obtain ⟨V', st', o, hrun, _⟩ := hlive [] st₀ ⟨rfl, rfl⟩
  exact ⟨_, runBody_gas_oblivious R vkAddr (gasFree_of_valid R hR vkAddr) _ _ g st₀ _
    (run_joinV3 R (noShadowB_of_valid hR) vkAddr _ _ st₀ V' st' o hrun)⟩

/-! ## 4. Gate lines -/

#cone_sorries Midfall.LoweringV3.block_live
#cone_sorries Midfall.LoweringV3.block_live_case_transcriptParser
#cone_sorries Midfall.LoweringV3.block_live_case_lagrange
#cone_sorries Midfall.LoweringV3.block_live_case_quotientLin
#cone_sorries Midfall.LoweringV3.block_live_case_pcs
#cone_sorries Midfall.LoweringV3.totalV3_correct

#print axioms Midfall.LoweringV3.block_live
#print axioms Midfall.LoweringV3.totalV3_correct
#print axioms Midfall.LoweringV3.block_live_case_vkLoading
#print axioms Midfall.LoweringV3.block_live_case_finalPairing
#print axioms Midfall.LoweringV3.block_live_case_traceReturn

end Midfall.LoweringV3
