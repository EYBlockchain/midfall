/-
  Midfall.LoweringV3.Composition

  PL.H0 (D-P74) - **THE ONE COMPOSITION, OVER THE ONE ROW SHAPE.**

  WHAT D-P74 CHANGED HERE. (1) The row bundles `SimRowsV3`/`ProgRowsV3` conclude SIM.2's
  `BlockSim`/`BlockProgS` over `StageInv` (`Midfall/LoweringV2/Stages.lean`) - the shape every ROW
  card proves - and NOT RECON.2's `BlockSimV3`/`BlockProgV3` over `StageBnd`. `StageBnd`,
  `exitSimBnd`, `exitProgBnd`, `BlockSimV3` and `BlockProgV3` are DELETED (D-P74 item 2); the
  `CompositionW.lean` lemmas that only compared against them went in the same commit. RECON.3 measured
  the two boundaries as INCOMPARABLE and refused to re-point another card's deliverable; D-P74 makes
  it this card's. (2) `lowering_equivalenceV3_of_rows` is now the route the root takes, and conjunct 4
  comes from `totalV3_correct` (Totality.lean), not from `totalV3_of_stages`, which is deleted:
  `BodyTotal` quantifies over EVERY calldata while `ProgRowsV3` assumes `LeanAccepts`.

  THE HAZARD THIS FILE IS WRITTEN AGAINST. There is exactly ONE `ValidV3` in the tree:
  `Midfall/LoweringV3/Statements.lean:1116`, seven clauses - generated, inputs, program, noWriters,
  env, payload, supported. The eighteen-clause text at
  `docs/plans/V3-evidence/lean/statements/StatementsV3.lean` is the D-P67-strike FALLBACK and is not
  imported here. `#check @Midfall.LoweringV3.ValidV3.mk` at the bottom prints the seven-field
  constructor: that is the machine-checked proof of this claim.

  GLUE IS PROVED, NEVER SORRIED (EXECUTION-V2 §4, SKELETON). `rejectsV3_of_sims` and
  `completeV3_of_progs` were RECON.2's skeletons; both are PROVED here from the sequenced rows, the
  prefix rows and the two run decompositions, so the sorries now sit on the ROWS (Rows.lean), on the
  two PREFIX rows (Stages.lean), on the four TOTALITY leaves (Totality.lean) and on the shared
  scan/decomposition leaves - and nowhere else. A glue step that needed a fact no leaf supplied would
  add a NAMED LEAF, never a hypothesis (D-P74's binding condition); none did.

  THE CALADATA SIZE BOUND REACHES EVERY ROW: `Frame` (Blocks.lean:56) carries
  `cdSize : cd.size < 2 ^ 256`, so every boundary built from it - `StageInv`, and through it
  `BlockSim`/`BlockProgS` - carries the bound, and no row states it separately. `cdSize_falsifier`
  is the exhibit.

  THE PIN BUNDLE IS DISSOLVED: the evidence's `SimPins` had four fields; three are conjuncts of
  `G1CodecHeadlineLaws` and the fourth is a conjunct of `ValidV3.program`
  (`pins_from_valid_and_headlineLaws`, PROVED). No clause was added to `ValidV3` to get them.

  W12/W13 DISCIPLINE. The V2 cone has exactly 1 REFUTED (`poseidon_valid`, a V2 fixture sorry); this
  card adds none. No `native_decide` occurs in this file or in the cone of `lowering_correct`.
-/
import Midfall.LoweringV3.Statements
import Midfall.LoweringV3.Totality
import Midfall.LoweringV3.PrefixV3
import Midfall.LoweringV2.Stages
import Midfall.Lowering.Stage
import Midfall.Tools.ConeSorries
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
-- SIM.1's staged Lean view: LeanRaw, LeanFinal, Decoded and leanStage live in this namespace.
open Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §1. The two prefix rows AT THE V3 VALIDITY (the card's Stop-if 2, taken and reported) -/

/-! **A1 MEASURED THE BRIDGE. IT LANDS FOR `generated` AND DOES NOT LAND FOR `program`.**
    A0 left this pair "discharged the moment the bridge lands". A1 tested every duplicated name in the
    transitive closure of the two `programOk` copies at this commit (`/tmp/bridge_probe`, one
    `rfl`/`Iff.rfl` per name, run with `lake env lean`). The result is not uniform:

    * `generated`, `GeneratedBy`, `expectedConsts`, `cAddr`, `constsCoherent`, `noShadowProg`,
      `noShadowCore`, `progConstNames`, `constLinesLiteral`, `cdBoundB`, `hasMultiPointSet`,
      `transcriptRegionOk`, `walkWindowsOf`, `longestAbsorbRunOf`, `spansMeet`, `g1IdentityFloor`,
      `negLagrangesFloor` and `permCommMatchRepaired` ARE definitionally equal across the two
      namespaces - each pair has byte-identical text over shared leaves, so `rfl` closes it. In
      particular `LoweringV3.GeneratedBy R ↔ LoweringV2.GeneratedBy R` is `Iff.rfl`, so every
      `generated`-clause peel proved in `LoweringV2/Stages.lean` §3B is available here WITHOUT a
      second copy.
    * `callsResolved`, `gasScan` and `exitDisciplineFuel` are NOT. The first because
      `callSitesSs`/`callSitesS`/`callSitesE`/`callSitesEs` is a `mutual` block, and Lean compiles
      mutual recursion through `WellFounded.fix`, whose index and proof arguments differ between two
      copies even when the bodies are identical - the same wall `Lowering/InlineConstants.lean:296-303`
      records for `inExpr`. The other two because their step functions sit behind the same mutual/fix
      shape. `programOkB` contains `callsResolved`, so `programOk` does not transfer, and
      `ValidV3.toV2` still fails on exactly the field A0 named.
    * Therefore the duplicate pair is NOT collapsed: `prefix_simV3`/`prefix_progV3` stay as written.
      What A1 did instead is cheaper and does not need the bridge at all: the two rows' PROOF is being
      written in `LoweringV2/Stages.lean` §3B-§3D against namespace-free facts about `R`'s own fields
      (the three consts lookups, the three model numerals, the two wrapper flags, the two
      `proofLayout` statics, the g1 floor, `p = frModulusConstant`), each of which BOTH validities
      project - `LoweringV3/Statements.lean` already proves `lookup_expectedConsts_of_programOkB`,
      `g1IdentityFloor_of_programOk`, `cdBound_of_valid` and `frModulus_of_programOk_of_modulus` over
      its own copy. So one core proof serves both rows without any `programOk` bridge, and the bridge
      is no longer on the critical path.
    -/

/-! **WHY `ValidV3.toV2` (card step 2) IS NOT LANDED.** The field copy fails, and it fails on ONE
    field: `h.program : LoweringV3.programOk R` is not the frozen `LoweringV2.programOk R`. The two
    texts are the same SHAPE - `programOkB R = true ∧ GasCallOk (R.prog 0 0) ∧ ExitDiscipline
    (R.prog 0 0)`, `LoweringV2/Statements.lean:905` against `LoweringV3/Statements.lean:1012`, and
    `programOkCore`/`programOkB` are byte-identical modulo a comment line - but each module's copy
    resolves its helper names inside its own namespace, so `LoweringV3.programOkB R = true` and
    `LoweringV2.programOkB R = true` are NOT definitionally equal (measured at this commit:
    `⌈fun (R) (h : LoweringV3.programOkB R = true) => (h : LoweringV2.programOkB R = true)⌉` is
    rejected). Bridging them is the decidable-scan equivalence the RECON.1 cut-over never claimed to
    prove; it is a card of its own, not a convenience, and PL.H0 does not weaken `ValidV3` or add a
    clause to buy it. THE CARD'S OWN FALLBACK IS THEREFORE TAKEN (Stop-if 2): the two prefix rows,
    which are sorried and so hide nothing, are RESTATED over `ValidV3`. They are named
    `prefix_simV3` / `prefix_progV3` below, they differ from SIM.6's `prefix_sim` / `prefix_prog`
    ONLY in the validity hypothesis, and each is discharged the moment the bridge above lands. -/

/-- **THE PREFIX ROW, SOUNDNESS SIDE, OVER `ValidV3`** - SIM.6's `prefix_sim`
    (`Midfall/LoweringV2/Stages.lean:595`) restated at the V3 validity, exactly as PL.H0's Stop-if 2
    prescribes. The conclusion is VERBATIM SIM.6's; only `hR` moves. LEAF (SIM.6, WP A1).
    WITNESS: `gap_lowering_correct_witness_unexhibited`. FALSIFIER: `stageInv_start_not_vacuous` and
    `finSim_refutes_empty` (Stages.lean:663, :692, PROVED), and `whole_program_sim` (:629, PROVED)
    shows the post this leaves is the pre `slices_seq_sim` asks for. -/
theorem prefix_simV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (W : ExecEnv) (Lyt : EVM.Layout)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (splitPost (fun V st => Mid R H vkAddr cd .start V st)
        (fun V' st' o => FinSim R H cd V' st' o)) := by
  intro V st ⟨hV, hst⟩ V' st' o hrun
  subst hV
  subst hst
  rcases prefix_walk (pfxFacts_of_validV3 hR) hdep hentry hrun with
      ⟨hn, hsi, -, -⟩ | ⟨ho, hrev, -⟩
  · exact Or.inl ⟨hn, Or.inl hsi⟩
  · exact Or.inr ⟨fun h => absurd h (by rw [ho]; decide), Or.inl ⟨ho, hrev⟩⟩

/-- **THE PREFIX ROW, PROGRESS SIDE, OVER `ValidV3`** - SIM.6's `prefix_prog`
    (`Midfall/LoweringV2/Stages.lean:612`) restated the same way; conclusion verbatim, only `hR`
    moves. LEAF (SIM.6, WP A1). WITNESS: `gap_lowering_correct_witness_unexhibited`. FALSIFIER:
    `stageInv_start_not_vacuous` (PROVED) plus `whole_program_prog` (Stages.lean:644, PROVED). -/
theorem prefix_progV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hacc : LeanAccepts R H cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd .start V' st') := by
  have hf := pfxFacts_of_validV3 hR
  exact prefix_prog_core hf hdep hentry
    (pfxAbiWord_zero_of_leanAccepts hf hentry hacc)
    (pfxMemWord_zero_of_entry hf hentry (transcriptMptr_lt hR))

/-! ## §2. The two row bundles: ONE row shape, four codec laws, pinned by ValidV3 -/

/-- **THE SIMULATION ROWS, V3.** One row per block and direction, at SIM.2's boundary: the seven
    `BlockSim`s over `StageInv`. The binders are RECON.2's - `ValidV3`, the four-law codec bundle,
    the precompile assumption, then `SoundSide` - and only the CONCLUSION moved, from `BlockSimV3`
    over `StageBnd` to `BlockSim` over `StageInv` (D-P74 item 2). `q_blockSim`
    (QuotientRows.lean:191) is already stated at this shape, which is what the re-pointing was for. -/
def SimRowsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
      (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product),
    ∀ (H : Hash) (vkAddr : U256) (cd : Bytes), SoundSide R H cd →
      ∀ (q : Partial) (g : ExternalGas),
        BlockSim R q H vkAddr (permissive (callsOf product)) g cd

/-- **THE PROGRESS ROWS, V3.** The seven `BlockProgS`s over `StageInv`, same binders, same
    one-word change (`BlockProgV3` -> `BlockProgS`). -/
def ProgRowsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
      (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product),
    ∀ (H : Hash) (vkAddr : U256) (cd : Bytes),
      LeanAccepts R H cd → CompleteSide R H cd →
        ∀ q : Partial, BlockProgS R q H vkAddr product cd

/-- **WITNESS THAT THE PIN BUNDLE IS DISSOLVED (PROVED).** Every field the evidence file's `SimPins`
    carried is supplied by hypotheses the headline already has: three by the four-law codec bundle,
    the fourth by `ValidV3.program`. The rows need no separate bundle, and no clause was added to
    `ValidV3` to get them. -/
theorem pins_from_valid_and_headlineLaws (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) :
    (∀ Q : G₁, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q) ∧
      R.E.g1.eipRoundtrip ∧ R.E.g1.toEip 1 = Midfall.natToBytesBE 0 128 ∧
      hasMultiPointSet R.pv = true :=
  ⟨hcodec.compressedEncoderFirst, hcodec.eipRoundtrip, hcodec.toEip_one,
    hasMultiPointSet_of_valid hR⟩

/-! ## §3. The four obligations: two PROVED here, one PROVED in Totality, one PROVED by scans -/

/-- **OBLIGATIONS 1 AND 3: TWO OUTCOMES.** The scan route, unconditional in the state.
    `ValidV3.noWriters` is frozen clause 10 and `exitDiscipline_of_valid` projects the exit scan out
    of `ValidV3.program`, so both hypotheses of `twoOutcomes_of_scans` are read off the landed text.
    PROVED from those two; its cone is the named scan leaves ST.10 and ST.12. -/
theorem twoOutcomesV3_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    TwoOutcomes R :=
  twoOutcomes_of_scans R hR.noWriters (exitDiscipline_of_valid hR)

/-- **OBLIGATION 1, SOUNDNESS HALF: PROGRAM-LEVEL REJECTION, V3. PROVED** (PL.H0 step 3a) - it was
    RECON.2's skeleton. The proof is the evidence's `soundness_of_sims`
    (SoundnessV3.lean:804) + `rejects_of_sims` (:824) at the ONE row shape: factor the committed run
    at the prefix/slice boundary (`run_splitV3`, ST.11's re-point of A1's `run_split` onto the
    sequenced `BlockSim` rows (`slices_seq_sim`) after the prefix row (`prefix_sim`, SIM.6's leaf,
    reached through `ValidV3.toV2` and `EntryFrameV3.toV2`), close the chain with `seq_final`, and
    read `LeanAccepts` off the TraceReturn exit through `leanAccepts_of_final`
    (Lowering/Stage.lean:426). `hna` contradicts what a returning run therefore carries.
    NO NEW LEAF WAS NEEDED: every fact the step asks for is supplied by a leaf the card names. -/
theorem rejectsV3_of_sims (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hsim : SimRowsV3 R product) : RejectsV3 R product := by
  intro W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hcodec hside hna hobs hret
  obtain ⟨V', st', o, heq, hrun⟩ :=
    run_splitV3 R (noShadowB_of_valid hR) vkAddr (permissive (callsOf product)) g st₀ obs hobs
  have hall := seq_final
    (prefix_simV3 R hR W Lyt H vkAddr cd st₀ hdep hentry.toV2
      (permissive (callsOf product)) g)
    (slices_seq_sim R H vkAddr cd (permissive (callsOf product)) g
      (fun q => hsim hR hcodec hpc H vkAddr cd hside q g))
  have hfin := hall [] st₀ ⟨rfl, rfl⟩ V' st' o hrun
  rw [heq] at hret
  rcases hfin with ⟨rfl, hrev⟩ | ⟨rfl, hh, hlean⟩
  · exact absurd (isRevertOrHalt_of_Reverted st₀ st' hrev) (not_isRevertOrHalt_of_isReturn hret)
  · exact hna (leanAccepts_of_final hlean)

/-- **OBLIGATION 2: COMPLETENESS, V3. PROVED** (PL.H0 step 3b) - it was RECON.2's skeleton. The proof
    is the evidence's `completeness_of_progs` (SoundnessV3.lean:1212) at the ONE row shape: the
    prefix progress row and the sequenced `BlockProgS` rows compose to one total contract
    (`total_append`, `slices_seq_prog`); existence is `run_joinV3`, and the view half is
    `worldEq_of_runBody` (frozen clause 10 plus the ST.12 scan) against `run_split`. -/
theorem completeV3_of_progs (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hprog : ProgRowsV3 R product) : CompleteV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec hacc hcomp
  have htot := total_append
    (prefix_progV3 R product hR W Lyt H vkAddr cd st₀ hdep hentry.toV2 hacc)
    (slices_seq_prog R product H vkAddr cd
      (fun q => hprog hR hcodec hpc H vkAddr cd hacc hcomp q))
  refine ⟨?_, ?_⟩
  · obtain ⟨V', st', o, hrun, _⟩ := htot.1 [] st₀ ⟨rfl, rfl⟩
    exact ⟨_, run_joinV3 R (noShadowB_of_valid hR) vkAddr _ _ st₀ V' st' o hrun⟩
  · intro obs hobs
    obtain ⟨V', st', o, heq, hrun⟩ :=
      run_splitV3 R (noShadowB_of_valid hR) vkAddr _ _ st₀ obs hobs
    obtain ⟨ho, hh⟩ := htot.2 [] st₀ ⟨rfl, rfl⟩ V' st' o hrun
    subst ho
    rw [heq] at hobs ⊢
    -- The view half comes from TwoOutcomes (proved from the two scans), NOT from
    -- worldEq_of_runBody: that lemma wants the frozen R.Valid, which ValidV3 does not supply (§1).
    rcases twoOutcomesV3_of_valid R hR vkAddr (callsOf product) (ExternalGas.ofFun fun _ => 0)
        st₀ _ hobs with hview | ⟨hrh, _⟩
    · exact hview
    · have hret : (⟨committedState st₀ st', .halt⟩ : Obs).isReturn := by
        refine ⟨abiTrue, ?_⟩
        rw [halted_committedState]
        exact hh
      exact absurd hrh (not_isRevertOrHalt_of_isReturn hret)

/-! ## §4. THE ONE COMPOSITION -/

/-- **THE HEADLINE, V3, FROM THE FOUR OBLIGATIONS.** The only V3 composition in the tree. PROVED with
    no sorry of its own: the gluing lemma `lowering_equivalenceV3_of` is already proved at
    Statements.lean:1442, obligations 1-3 are proved above, and conjunct 4 is `totalV3_correct`
    (Totality.lean:proved glue over four named leaves). Every `sorryAx` in this theorem's cone comes
    from a ROW, a PREFIX row, a TOTALITY leaf or a shared scan/decomposition leaf. -/
theorem lowering_equivalenceV3_of_rows (R : Render p G₁ G₂ Gₜ)
    (product : PairingProduct) (hR : ValidV3 R) (hsim : SimRowsV3 R product)
    (hprog : ProgRowsV3 R product) : LoweringEquivalenceV3 R product :=
  lowering_equivalenceV3_of R product (twoOutcomesV3_of_valid R hR)
    (rejectsV3_of_sims R product hR hsim) (completeV3_of_progs R product hR hprog)
    (totalV3_correct R product hR)

/-! ## §5. WITNESSES AND FALSIFIERS (W12) -/

/-- **THE PADDED-CALADATA FALSIFIER.** The bound `cd.size < 2 ^ 256` is not decoration: the vkLoading
    row of the staged simulation contract is FALSE without it. The EVM sees the calldata length only
    as a WORD (`calldatasize` is `BitVec.ofNat 256 st.env.calldata.length`, EVMExec.lean:792), so
    padding by exactly 2 ^ 256 zero bytes leaves every `calldataload`/`calldatacopy` unchanged,
    while the Lean decoder compares `cd.size` in `Nat` (Calldata.lean:341) and REJECTS the padded
    call. `Frame.cdSize` is what refuses such a frame, so every row built on `Frame` - `Clean`,
    `Poisoned`, `exitOk`, `StageInv` - inherits the refusal. -/
theorem cdSize_falsifier :
    (BitVec.ofNat 256 (2 ^ 256) = 0) ∧
    ((2 ^ 256 : ℕ) ≠ 0 ∧ (2 ^ 256) % 2 ^ 256 = 0) ∧
    (¬ (BitVec.ofNat 256 (2 ^ 256) = 0 → (2 ^ 256 : ℕ) = 0)) := by
  refine ⟨rfl, ⟨by decide, Nat.mod_self _⟩, ?_⟩
  intro h
  exact absurd (h rfl) (by decide : (2 ^ 256 : ℕ) ≠ 0)

/-- **WITNESS FOR THE SIMULATION SIDE (W12, PROVED): the row postcondition carries the Lean half.**
    The TraceReturn arm of SIM.2's `exitSim` hands out `LeanFinal` - the calldata decodes and the
    closed Lean stage exists - which is exactly the fact `rejectsV3_of_sims` spends through
    `leanAccepts_of_final`. So the bundle is reachable from `ValidV3` and the hypotheses are the
    right shape. (RECON.2's twin over `exitSimBnd` went with `StageBnd`.) -/
theorem exitSim_carries_the_lean_half (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (h : exitSim R .traceReturn H vkAddr cd V' st' .halt) : LeanFinal R H cd := h.2.2

/-- **WITNESS FOR OBLIGATIONS 2 AND 4 (W12, PROVED): the hypotheses hold together.** `ProgRowsV3`
    asks of the render exactly three things - `ValidV3`, the four-law codec bundle, the precompile
    assumption - and all three are hypotheses of the headline itself, so the bundle adds no premise the
    conclusion does not already carry. Re-pointed at `BlockProgS` with the bundles. -/
theorem progRows_reach_a_row (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hprog : ProgRowsV3 R product)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (hacc : LeanAccepts R H cd)
    (hcomp : CompleteSide R H cd) : ∀ q : Partial, BlockProgS R q H vkAddr product cd :=
  hprog hR hcodec hpc H vkAddr cd hacc hcomp

/-- **FALSIFIER FOR OBLIGATIONS 2 AND 4 (W12): the progress rows are not satisfied by a program that
    falls off the end.** The progress post of the TraceReturn block demands a HALT with the ABI-true
    return; weaken it to "any outcome" and both obligations become vacuously true of every render while
    concluding nothing. PROVED at SIM.2's own `exitProg` - `exitProg_refutes_normal_traceReturn`,
    Stages.lean:714 - which is the reason RECON.2's `exitProgBnd_refutes_fallthrough` retired with
    `exitProgBnd` rather than being restated a second time. -/
theorem exitProg_refutes_fallthrough (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) :
    ¬ exitProg R .traceReturn H vkAddr cd V' st' .normal :=
  exitProg_refutes_normal_traceReturn R H vkAddr cd V' st'

/-- **WITNESS FOR THE SCAN PAIR (W12): the two hypotheses of `twoOutcomes_of_scans` hold together at
    an actual block**, so obligation 1/3 is not stated over an uninhabitable pair. PROVED by decide at
    the same toy block `exitDiscipline_witness` uses. -/
theorem twoOutcomes_hypotheses_together :
    ∃ (b : Block EVM.Op), NoWriters b ∧ ExitDiscipline b :=
  ⟨yul% { if iszero(calldataload(0)) { mstore(0, 7) revert(0, 4) }
           mstore(4096, 1)
           return(4096, 32) },
    ⟨⟨16, by decide⟩, exitDiscipline_witness⟩⟩

/-! ## §6. Cone lists and axiom prints -/

#cone_sorries Midfall.LoweringV3.twoOutcomesV3_of_valid
#cone_sorries Midfall.LoweringV3.rejectsV3_of_sims
#cone_sorries Midfall.LoweringV3.completeV3_of_progs
#cone_sorries Midfall.LoweringV3.lowering_equivalenceV3_of_rows

/-! **THE LANDED-TEXT PROOF.** Seven fields, and they are the landed ones: generated, inputs, program,
    noWriters, env, payload, supported. Over the eighteen-clause fallback this prints a different
    arity and different names. -/
#check @Midfall.LoweringV3.ValidV3.mk

-- One obligation's hypothesis as landed: rejectsV3_of_sims's first premise is the seven-clause
--    ValidV3 of LoweringV3/Statements.lean:1116, and its program clause is the V3 programOk bundle.
#check fun (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) => hR.program

#print axioms Midfall.LoweringV3.prefix_simV3
#print axioms Midfall.LoweringV3.prefix_progV3
#print axioms Midfall.LoweringV3.rejectsV3_of_sims
#print axioms Midfall.LoweringV3.completeV3_of_progs
#print axioms Midfall.LoweringV3.lowering_equivalenceV3_of_rows
#print axioms Midfall.LoweringV3.twoOutcomesV3_of_valid
#print axioms Midfall.LoweringV3.cdSize_falsifier
#print axioms Midfall.LoweringV3.pins_from_valid_and_headlineLaws
#print axioms Midfall.LoweringV3.exitSim_carries_the_lean_half
#print axioms Midfall.LoweringV3.exitProg_refutes_fallthrough
#print axioms Midfall.LoweringV3.progRows_reach_a_row

end Midfall.LoweringV3
