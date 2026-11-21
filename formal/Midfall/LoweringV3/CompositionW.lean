/-
  Midfall.LoweringV3.CompositionW

  RECON.3 - MOVE THE ROW FAMILIES TO THE WIDENED SHAPE (D-P72 clause 1): SimContracts, ProgContracts and
  the composition stated ONCE, in the widened shape, before any M6 ROW card is briefed, so the
  base-class rows need no restatement when the two new arms are proved.

  ==============================================================================
  THE CENTRAL HAZARD, AND WHICH READING THIS FILE IS.
  ==============================================================================

  "Stated once, in the widened shape" is ambiguous between

    (A) MODIFY RECON.2's Midfall/LoweringV3/Composition.lean so its five obligations are stated in the
        widened shape (one statement total, the base rows become instances of it); and
    (B) ADD the widened shape beside the base one, and prove the reduction that relates them.

  THIS FILE IS (B). Five facts in the card text decide it; none is convenience.

  1. THE CARD'S OWN Needs LIST NAMES THE WIDENED FAMILIES AS ALREADY THERE: StageInvW, BlockSimW,
     SimContractsW, BlockProgSW, ProgContractsW (WideningStages.lean), and lowering_equivalenceW_of and
     equivalenceW_iff_V3 (WideningV3.lean, landed as Widening.lean). WID.1 landed them and is MERGED.
     Under (A) there is nothing to "replay RECON.2's composition with StageInvW" against: the widened
     shape would have to be invented here, which is what Needs forbids.
  2. DO STEP 1 NAMES A NEW DECLARATION: lowering_equivalence_of_stagesW, with the W suffix. It is not
     one of RECON.2's five names and is not in Composition.lean. (A) would have to introduce this name
     anyway, so (A) buys nothing where it costs everything.
  3. DO STEP 2 IS A REDUCTION BETWEEN TWO FAMILIES (BlockSimW R q ... <-> BlockSim R q ...). A reduction
     presupposes two statements. Under (A) there is one family and step 2 is vacuous - yet the card's
     Accept asks for #assert_axioms on "the composition AND THE REDUCTION", and its Witness is "THE
     REDUCTION instantiated at poseidonRender". The card requires two families to exist.
  4. THE CARD'S FALSIFIER IS THAT THE BASE FAMILIES MUST STAY: acc_not_supportedV3 (tree name
     acc_not_supportedV2, Widening.lean:141) "shows the V3 families do not cover an accumulator
     render". Under (A) the V3 families are deleted or repurposed, and RECON.2's five names - which the
     M3 exit gate reads through #cone_sorries and which scripts/gen_sorry.sh keys its owners by - would
     move. The brief forbids a frozen edit and requires the cone to stay at ten leaves.
  5. THE CRITIC'S FINDING IS THE REASON THE WIDENED SHAPE CANNOT BE THE ONLY SHAPE. "The reduction of
     step 2 transports a row only at a render with no accumulator and an embedded evaluator." Those two
     conditions are HYPOTHESES, not definitional identities: R.cfg.accumulator = none and
     R.model.quotientExternal = none. So the base families are instances of the widened ones only AT
     THE CORNER, and the corner is where the base families are the only ones the V3 headline can read.

  WHY A REVIEWER ACCEPTS TWO STATEMENTS THAT ARE NOT DUPLICATES. The two families differ in five places
  and every difference is load-bearing:

      base (SimRowsV3 / ProgRowsV3, Composition.lean:140, :150)     widened (SimContractsW /
                                                                     ProgContractsW,
                                                                     WideningStages.lean:586, :620)
      boundary  StageInv (six fields, after D-P74)                  StageInvW (eight: + BaseInvW,
      per-block BlockSim / BlockProgS                               Mirror, AccInv, quotientEvaluator)
      calls     callsOf product                                     BlockSimW / BlockProgSW
      validity  ValidV3 R (scope clause SupportedV2: has noAcc)     callsW R product qAddr evalRel
      acceptance LeanAccepts R H cd                                ValidW R Q (scope SupportedW: NO
      extra       -                                                 noAcc) + EvalContracts R Q
                                                                    + idLaw, + qAddr, + evalRel

  * The widened one is NOT the base one restated. At an accumulator render SupportedV2 R is FALSE
    (acc_not_supportedV2, PROVED), so ValidV3 R is uninhabited there
    (v3_class_excludes_an_accumulator_render, PROVED below) and the base family quantifies over an
    EMPTY class. Independently stageInv_false_of_acc (PROVED, WideningStages.lean:239) shows the base
    per-block boundary is UNSATISFIABLE after .start there, so a base row says nothing at an
    accumulator render even where its class is not empty - stageInv_unreachable_at_acc below makes that
    precise for six of the seven blocks. A statement over an empty class is not a second statement of
    the same fact; it is no statement of it.
  * The base one is NOT derivable from the widened one in general - only at the corner, and section 1
    proves the corner hypotheses are exactly accumulator = none and quotientExternal = none. That is the
    critic's finding, and this is the card that had to prove it rather than assume it.
  * NOTHING IS PROVED TWICE, which is what "stated once" actually buys. Each M6 row is written ONCE,
    against BlockSimW / BlockProgSW (D-P72 clause 1: "the rows of the base class are proved first, IN
    THE WIDENED SHAPE, so that nothing is restated when the two new arms are added"). Section 1 proves
    that at the corner a widened row IS SIM.2's row, and section 2 lands the corner consequence. WHAT
    SECTION 2 ALSO REPORTS IS THIS CARD'S MOST IMPORTANT OUTPUT: a widened row does NOT reach RECON.2's
    SimRowsV3 / ProgRowsV3. Those concluded BlockSimV3 / BlockProgV3 at RECON.2's own FOUR-FIELD
    StageBnd. As a PREDICATE StageBnd is WEAKER than StageInvW (it drops BaseInvW and Mirror), but a
    contract "every run from pre ends in post" moves one way in the pre and the other in the post, so a
    WEAKER predicate makes a STRONGER contract: BlockSimV3 quantified over more starting states than
    BlockSimW and asked less of each. The two were therefore INCOMPARABLE - neither implies the other,
    and no transport lemma existed to be landed. So "stated once" costs one more thing than the card
    knew: RECON.2's two bundles have to be read at SIM.2's StageInv boundary - which §1 proves IS
    the widened boundary at the corner - for a widened proof to discharge the V3 headline. **D-P74
    item 2 made exactly this re-pointing PL.H0's deliverable, and it is landed.** That is a
    decision about another card's deliverable, and this card reports it rather than making it
    unilaterally. One PROOF per row; two STATEMENTS because there are two headlines, and the gap between
    the widened headline and the V3 one is §2's finding, not §1's.
  * PRECEDENT IN THE MERGED TREE: WID.1 landed ValidW beside ValidV3, SupportedW beside SupportedV2,
    TwoOutcomesW beside TwoOutcomes, RejectsW / CompleteW / TotalW beside RejectsV3 / CompleteV3 /
    TotalV3 on exactly these grounds, and this card's own acceptance REQUIRES ValidV3 and ValidW to
    stay two separate declarations, neither merged. Base-plus-widened-sibling is the tree's convention;
    (A) would break it in one file while every other file kept it.

  WHAT "NO SECOND COMPOSITION" THEN MEANS. RECON.2's Goal is "no second composition in the tree", and
  ST.5 and SIM.2 were both stopped by it. Read literally that constraint is already spent: WID.1 merged
  lowering_equivalenceW_of (Widening.lean:620), a second gluing lemma, and RECON.3's Needs list tells
  this card to USE it. So the constraint cannot mean "one gluing lemma in the tree". It means ONE
  COMPOSITION PER HEADLINE: no parallel route to LoweringEquivalenceV3, which is what ST.5 and SIM.2
  were about to build from the old V2 block rows (completeV3_of_blocks, lowering_equivalence_of_stages).
  This card adds no second route to the V3 headline: lowering_equivalenceV3_of_rows remains the only
  one, and nothing here concludes LoweringEquivalenceV3 from a W row bundle directly - the only V3-side
  conclusion, lowering_equivalenceW_of_V3, is WID.1's equivalence restricted at the corner, not a
  second composition. Exactly one route to each headline from its own row family. AT DECLARATION LEVEL
  the check RECON.2 asked for still passes: grep -rE '^(theorem|def|structure|abbrev)
  lowering_equivalence_of_stages([ (]|$)' over Midfall/ is 0, and the same for completeV3_of_blocks.
  (A plain grep -c for those strings is NOT 0 and never was: both names are discussed in the header
  comments of Stages.lean and Composition.lean. This card's own deliverable name,
  lowering_equivalence_of_stagesW, is a prefix match too - the card chose it, not this file.)

  WHAT THIS CARD DOES NOT LAND. The rows (M6). GeneratorRows.lean IS NOT IN THE TREE - it is
  evidence-only (docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean), so card step 3's
  "re-point the generic row statements of GeneratorRows.lean" has no tree file to re-point; section 5
  says what was landed instead, and this is reported as a false premise. The StatementsV3 fallback
  retirement (a separate decision). Any frozen edit: none was needed - ValidW already carries no noAcc
  clause, so the widened shape asks for no new clause of anything.

  W12/W13 DISCIPLINE. Three obligations are registered as skeletons, each with its NAMED LEAVES in its
  docstring, exactly as RECON.2 did for its three. None is refuted and none is in the headline cone:
  the cone is rooted at Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon and nothing there
  reads a W declaration, so the cone stays at ten leaves. No native_decide occurs in this file.
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.WideningStages
import Midfall.LoweringV2.Stages
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done
set_option autoImplicit false

namespace Midfall.LoweringW

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §0. The corner

  Every reduction below is stated under the SAME two hypotheses, and they are the only two the critic's
  finding names: no accumulator, and an embedded quotient. stageInvW_iff_V3 (WideningStages.lean:338)
  and equivalenceW_iff_V3 (Widening.lean:653) already need exactly these, so this is not a hypothesis
  invented here to make a lemma go through - it is the corner D-P72 clause 1 names. -/

/-- An embedded quotient means no evaluator is called. The same one-line proof equivalenceW_iff_V3 and
    ValidW.ofV3 use, named so that §1 states its hypotheses once. -/
theorem not_isExternal_of_embedded (R : Render p G₁ G₂ Gₜ) (hq : R.model.quotientExternal = none) :
    ¬ isExternal R := by
  simp [isExternal, hq]

/-- **EVERY RENDER THE V3 HEADLINE CAN SPEAK OF STANDS AT THE CORNER.** hR.supported.noAcc and
    quotientExternal_none_of_V3 (Widening.lean:870). PROVED; §2 applies it, so the corner is not a
    hypothesis this card invents but a consequence of the class RECON.2's composition already reads. -/
theorem corner_of_validV3 (R : Render p G₁ G₂ Gₜ) (hR : LoweringV3.ValidV3 R) :
    R.cfg.accumulator = none ∧ R.model.quotientExternal = none :=
  ⟨hR.supported.noAcc, quotientExternal_none_of_V3 hR⟩

/-! ## §1. THE REDUCTION (card step 2)

  The card asks for BlockSimW R q ... <-> BlockSim R q ... at the corner, "from leanStageW_noAcc and
  callsW_embedded". Both are needed and neither is enough alone: leanStageW_noAcc moves the LEAN half
  (the last stage), callsW_embedded moves the CALL half (the dialect), and the boundary half is
  stageInvW_iff_V3, already proved. Five pieces, then the block-level <->, then the half that fails. -/

/-- **PIECE 1, the Lean half.** With no accumulator the widened last stage exists exactly when V3's
    does: the two definitions differ only by accFinalCheck at .pairing, and accFinalCheck reads
    R.cfg.accumulator. From leanStageW_noAcc (WideningStages.lean:188). -/
theorem leanFinalAcc_iff (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none) (H : Hash)
    (cd : Bytes) : LeanFinalAcc R H cd ↔ LeanFinal R H cd := by
  constructor
  · rintro ⟨ms, instW, inst, hdec, S, hS⟩
    exact ⟨ms, instW, inst, hdec, S,
      by rwa [leanStageW_noAcc R hacc H instW inst ms Checkpoint.pairing] at hS⟩
  · rintro ⟨ms, instW, inst, hdec, S, hS⟩
    exact ⟨ms, instW, inst, hdec, S,
      by rwa [← leanStageW_noAcc R hacc H instW inst ms Checkpoint.pairing] at hS⟩

/-- **PIECE 2, the poisoned half.** PoisonedW is Poisoned plus the evaluator-address conjunct, so at an
    embedded render the two are the same proposition. -/
theorem poisonedW_iff (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr qAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hext : ¬ isExternal R) :
    PoisonedW R H vkAddr qAddr cd V st ↔ Poisoned R H vkAddr cd V st :=
  ⟨fun h => h.1, fun hp => ⟨hp, fun he => absurd he hext⟩⟩

-- PIECE 3, the boundary half, is stageInvW_iff_V3 ALONE (WideningStages.lean, PROVED). RECON.2's
-- StageBnd and the projection stageInvW_to_StageBnd that reached it were DELETED by PL.H0 under
-- D-P74 item 2: the V3 bundles now read SIM.2's StageInv directly, so the drop-to-four-fields step
-- has no consumer left. Nothing else in this file used it.

/-- **PIECE 4, the simulation exit.** At the corner the widened clean exit of block q is SIM.2's, both
    ways: the traceReturn arms differ only by LeanFinalAcc vs LeanFinal (piece 1) and the other arms
    only by StageInvW vs StageInv (piece 3). -/
theorem exitSimW_iff_exitSim (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (hq : R.model.quotientExternal = none) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g))
    (st' : EvmState) (o : Outcome) :
    exitSimW R q H vkAddr qAddr cd V' st' o ↔ exitSim R q H vkAddr cd V' st' o := by
  have hext := not_isExternal_of_embedded R hq
  cases q <;> first
    | exact ⟨fun h => ⟨h.1, h.2.1, (leanFinalAcc_iff R hacc H cd).mp h.2.2⟩,
                 fun h => ⟨h.1, h.2.1, (leanFinalAcc_iff R hacc H cd).mpr h.2.2⟩⟩
    | exact ⟨fun h => ⟨h.1, (stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd _ V' st').mp h.2⟩,
                 fun h => ⟨h.1, (stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd _ V' st').mpr h.2⟩⟩

/-- **PIECE 5, the progress exit.** Same, without the Lean half: both traceReturn arms are the bare
    halt-with-ABI-true, so only the boundary moves. -/
theorem exitProgW_iff_exitProg (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (hq : R.model.quotientExternal = none) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g))
    (st' : EvmState) (o : Outcome) :
    exitProgW R q H vkAddr qAddr cd V' st' o ↔ exitProg R q H vkAddr cd V' st' o := by
  have hext := not_isExternal_of_embedded R hq
  cases q <;> first
    | exact Iff.rfl
    | exact ⟨fun h => ⟨h.1, (stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd _ V' st').mp h.2⟩,
                 fun h => ⟨h.1, (stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd _ V' st').mpr h.2⟩⟩

/-- **THE REDUCTION, SIMULATION SIDE - THE CARD'S STEP 2, VERBATIM.** At a render with no accumulator
    and an embedded evaluator the widened per-block simulation contract IS SIM.2's. Same slice, same
    scope, same call relation (a parameter at this level, so callsW_embedded is not needed until the
    bundle transport in §2), and the three boundary pieces above. PROVED both ways.

    WHY THE MONOTONICITY WORKS HERE AND NOWHERE ELSE: StmtsContractAll pre post is
    "every run from pre ends in post". A STRONGER pre and a STRONGER post can be traded for a weaker
    pair only when the two are EQUIVALENT, which at the corner they are (pieces 3-5). §2 records what
    happens when they are merely one-way. -/
theorem blockSimW_iff_blockSim (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (hq : R.model.quotientExternal = none) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) :
    BlockSimW R q H vkAddr qAddr c g cd ↔ BlockSim R q H vkAddr c g cd := by
  have hext := not_isExternal_of_embedded R hq
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · intro V st hS V' st' o hrun
      have hh := h₁ V st
        ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mpr hS) V' st' o hrun
      cases hh with
      | inl e => exact Or.inl e
      | inr e => cases e with
        | inl h =>
            exact Or.inr (Or.inl
              ((exitSimW_iff_exitSim R hacc hq q H vkAddr qAddr cd V' st' o).mp h))
        | inr h =>
            exact Or.inr (Or.inr ⟨h.1, h.2.1,
              (poisonedW_iff R H vkAddr qAddr cd V' st' hext).mp h.2.2⟩)
    · intro V st hS V' st' o hrun
      have hh := h₂ V st ((poisonedW_iff R H vkAddr qAddr cd V st hext).mpr hS) V' st' o hrun
      cases hh with
      | inl e => exact Or.inl e
      | inr h =>
          exact Or.inr ⟨h.1, h.2.1,
            (poisonedW_iff R H vkAddr qAddr cd V' st' hext).mp h.2.2⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · intro V st hW V' st' o hrun
      have hh := h₁ V st
        ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mp hW) V' st' o hrun
      cases hh with
      | inl e => exact Or.inl e
      | inr e => cases e with
        | inl h =>
            exact Or.inr (Or.inl
              ((exitSimW_iff_exitSim R hacc hq q H vkAddr qAddr cd V' st' o).mpr h))
        | inr h =>
            exact Or.inr (Or.inr ⟨h.1, h.2.1,
              (poisonedW_iff R H vkAddr qAddr cd V' st' hext).mpr h.2.2⟩)
    · intro V st hW V' st' o hrun
      have hh := h₂ V st ((poisonedW_iff R H vkAddr qAddr cd V st hext).mp hW) V' st' o hrun
      cases hh with
      | inl e => exact Or.inl e
      | inr h =>
          exact Or.inr ⟨h.1, h.2.1,
            (poisonedW_iff R H vkAddr qAddr cd V' st' hext).mpr h.2.2⟩

/-- **THE REDUCTION, PROGRESS SIDE.** Same, with the dialect moved by callsW_embedded: BlockProgSW runs
    in Bridge.Dialect (callsW R product qAddr evalRel) and BlockProgS in
    Bridge.Dialect (callsOf product), and at the corner those are the same dialect. PROVED both ways. -/
theorem blockProgSW_iff_blockProgS (R : Render p G₁ G₂ Gₜ) (hacc : R.cfg.accumulator = none)
    (hq : R.model.quotientExternal = none) (q : Partial) (H : Hash) (vkAddr qAddr : U256)
    (product : PairingProduct)
    (evalRel : YulSemantics.EVM.CallRequest → EvmState → CallResponse → Prop) (cd : Bytes) :
    BlockProgSW R q H vkAddr qAddr product evalRel cd ↔ BlockProgS R q H vkAddr product cd := by
  have hext := not_isExternal_of_embedded R hq
  have hc : callsW R product qAddr evalRel = callsOf product :=
    callsW_embedded R hq product qAddr evalRel
  unfold BlockProgSW BlockProgS BlockProgAt
  rw [hc]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · intro V st hS
      obtain ⟨fe, fs, o, hrun, hpost⟩ :=
        h₁ V st ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mpr hS)
      exact ⟨fe, fs, o, hrun,
        (exitProgW_iff_exitProg R hacc hq q H vkAddr qAddr cd fe fs o).mp hpost⟩
    · intro V st hS V' st' o hrun
      exact (exitProgW_iff_exitProg R hacc hq q H vkAddr qAddr cd V' st' o).mp
        (h₂ V st ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mpr hS) V' st' o hrun)
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · intro V st hW
      obtain ⟨fe, fs, o, hrun, hpost⟩ :=
        h₁ V st ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mp hW)
      exact ⟨fe, fs, o, hrun,
        (exitProgW_iff_exitProg R hacc hq q H vkAddr qAddr cd fe fs o).mpr hpost⟩
    · intro V st hW V' st' o hrun
      exact (exitProgW_iff_exitProg R hacc hq q H vkAddr qAddr cd V' st' o).mpr
        (h₂ V st ((stageInvW_iff_V3 R hacc hext H vkAddr qAddr cd q.pre V st).mp hW) V' st' o hrun)

/-! **THE HALF THAT FAILED, AND THE CLAUSES THAT MADE IT FAIL (RECON.3's stop condition: "Stop if.
    The reduction is false for a clause of StageInvW: report the clause").** REPORTED, NOT PAPERED
    OVER, AND NOW RESOLVED BY D-P74. StageInvW carries EIGHT conjuncts; RECON.2's now-deleted StageBnd
    carried FOUR. The four it lacked were BaseInvW and Mirror (plus, off the corner, the accumulator
    invariant and the evaluator-address clause). A contract "every run from pre ends in post" moves one
    way in the pre and the other in the post, so the two boundaries were INCOMPARABLE and no transport
    lemma existed to be landed. **D-P74 item 2 took the decision RECON.3 correctly refused to take: the
    V3 bundles are read at SIM.2's StageInv boundary**, so the incomparability is gone - which is what
    lets a widened row discharge the V3 headline through blockSimW_iff_blockSim below. -/

/-- **FALSIFIER OF "THE BASE ROWS ALREADY SAY SOMETHING AT AN ACCUMULATOR RENDER".** For six of the
    seven blocks the base per-block contract's PRE-BOUNDARY is unsatisfiable in accumulator mode, by
    stageInv_false_of_acc: only vkLoading starts at .start. So a base row for those six is a vacuous
    statement about an accumulator render, and the widened family is the only one that can carry the
    second arm. PROVED. (vkLoading is the seventh, and its widened arm is WID.13.) -/
theorem stageInv_unreachable_at_acc (R : Render p G₁ G₂ Gₜ)
    (enc : Midfall.Generator.AccumulatorEncoding) (henc : R.cfg.accumulator = some enc)
    (q : Partial) (hq : q ≠ Partial.vkLoading) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    ¬ StageInv R H vkAddr cd q.pre V st := by
  have hk : q.pre ≠ Checkpoint.start := by
    cases q <;> first
      | exact absurd rfl hq
      | decide
  exact stageInv_false_of_acc R enc henc H vkAddr cd q.pre hk V st

/-! ## §2. THE CORNER CONSEQUENCE, AND THE FINDING ABOUT RECON.2's BOUNDARY

  WHAT THE CARD ASKED FOR AND WHAT IS PROVABLE. The card's step 2 asks for the reduction at
  BlockSimW <-> BlockSim, and §1 proves it. The natural next sentence - "so a widened row discharges
  RECON.2's SimRowsV3" - was FALSE as RECON.2 had it, and this card found that by trying to prove it.
  RECON.2's SimRowsV3 / ProgRowsV3 concluded BlockSimV3 / BlockProgV3, StmtsContractAll at RECON.2's
  OWN boundary StageBnd, a FOUR-field predicate. A contract "every run from pre ends in post" is
  transportable across a boundary change only when the pre gets STRONGER while the post gets WEAKER,
  or both move together as an EQUIVALENCE. StageBnd -> StageInvW went the wrong way for the pre:
  StageBnd was weaker, so a row stated at StageBnd had to handle more starting states than one stated
  at StageInvW, and the widened row simply did not cover them. SIM.2 saw this coming and wrote the
  only thing that is true about the two boundaries: stageInv_drops_to_bnd_form (Stages.lean) is a
  PROJECTION, StageInv being "a REFINEMENT of the boundary the headline reads, not a rival to it". A
  projection is not an equivalence, so BlockSimV3 and BlockSimW were INCOMPARABLE, and no transport
  lemma between them existed to be landed. **PL.H0 (D-P74 item 2) resolved this by deleting the
  StageBnd family and re-pointing both bundles at BlockSim / BlockProgS over StageInv**, which is the
  boundary §1 proves StageInvW coincides with at the corner.

  WHAT THAT MEANS FOR THE PLAN, IN ONE SENTENCE: the M6 rows, to be proved once in the widened shape
  (D-P72 clause 1), must be read at SIM.2's StageInv boundary - which §1 shows is exactly StageInvW at
  the corner - and RECON.2's two row bundles named StageBnd instead. Either RECON.2's SimRowsV3 /
  ProgRowsV3 are re-pointed at BlockSim / BlockProgS (a two-word edit to another card's deliverable,
  which this card's brief says is a decision and not a convenience), or the rows are proved twice at
  two boundaries, which is what D-P72 clause 1 exists to prevent. THIS CARD DID NOT MAKE THAT DECISION:
  it landed the reduction that is true, stated the corner consequence that is provable, and reported
  the gap. **D-P74 (signed 2026-11-19) made the decision, and PL.H0 landed the re-pointing.** -/

/-- **THE CORNER CONSEQUENCE OF THE WIDENED SIMULATION ROWS.** Every hypothesis SimContractsW asks
    beyond what is needed here is supplied at the corner and is VACUOUS there: ValidW R Q from ValidV3 R
    (ValidW.ofV3), EvalContracts R Q and the evaluator trust from not_isExternal_of_embedded, idLaw
    from R.cfg.accumulator = none, and qAddr := 0 / evalRel := fun _ _ _ => False because the widened
    contract stops reading them once callsW_embedded has fired. The conclusion is SIM.2's row - the one
    §1's reduction reaches - NOT RECON.2's deleted BlockSimV3, for the reason in the section header.
    PROVED, and it is the transport D-P74 item 1 routes M9 through. -/
theorem blockSim_of_simContractsW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hR : LoweringV3.ValidV3 R)
    (hcodec : LoweringV3.G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hsim : SimContractsW R Q product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (hside : SoundSide R H cd)
    (q : Partial) (g : ExternalGas) :
    BlockSim R q H vkAddr (permissive (callsOf product)) g cd := by
  obtain ⟨hacc, hq⟩ := corner_of_validV3 R hR
  have hext := not_isExternal_of_embedded R hq
  have h := hsim (ValidW.ofV3 Q hR) hcodec hpc (fun he => absurd he hext)
    {} { code := [], dataOffset := fun _ => 0, dataSize := fun _ => 0 } H vkAddr 0 cd
    (fun _ _ _ => False) (fun he => absurd he hext) (fun ha => by simp [hacc] at ha) hside q g
  have hc : callsW R product (0 : U256) (fun _ _ _ => False) = callsOf product :=
    callsW_embedded R hq product 0 _
  rw [hc] at h
  exact (blockSimW_iff_blockSim R hacc hq q H vkAddr 0 (permissive (callsOf product)) g cd).mp h

/-- **THE CORNER CONSEQUENCE OF THE WIDENED PROGRESS ROWS.** Same, with LeanAccepts read back from
    LeanAcceptsAcc by leanAcceptsAcc_iff_noAcc (Widening.lean:204). PROVED. -/
theorem blockProgS_of_progContractsW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hR : LoweringV3.ValidV3 R)
    (hcodec : LoweringV3.G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hprog : ProgContractsW R Q product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (hacc : LeanAccepts R H cd)
    (hcomp : CompleteSide R H cd) (q : Partial) :
    BlockProgS R q H vkAddr product cd := by
  obtain ⟨ha, hq⟩ := corner_of_validV3 R hR
  have hext := not_isExternal_of_embedded R hq
  have h := hprog (ValidW.ofV3 Q hR) hpc (fun he => absurd he hext)
    {} { code := [], dataOffset := fun _ => 0, dataSize := fun _ => 0 } H vkAddr 0 cd
    (fun _ _ _ => False) hcodec (fun he => absurd he hext)
    (fun ha2 => by simp [ha] at ha2)
    ((leanAcceptsAcc_iff_noAcc R ha H cd).mpr hacc) hcomp q
  exact (blockProgSW_iff_blockProgS R ha hq q H vkAddr 0 product (fun _ _ _ => False) cd).mp h

/-! ## §3. THE COMPOSITION, WIDENED (card step 1)

  lowering_equivalence_of_stagesW: the widened headline from SimContractsW, ProgContractsW,
  EvalContracts (a hypothesis of both bundles), TotalW and the scans - proved by replaying RECON.2's
  composition with StageInvW in place of StageInv. The gluing step is NOT restated: it is
  lowering_equivalenceW_of (Widening.lean:620), which WID.1 landed and this card's Needs list told it
  to use.

  The shape mirrors RECON.2 exactly: one PROVED scan route, three SKELETON obligations whose named
  leaves are the rows, and one PROVED glue. Totality is a separate leaf rather than a projection of
  conjunct 2 for RECON.2's own reason (Composition.lean:207-213). Conjunct 2 is stated in the STRONGER
  form CompleteAnyGasW and the headline's zero-oracle conjunct is then PROVED from it by
  CompleteAnyGasW.toComplete - D-P72 clause 5 as this card's critic restates it ("progress rows are
  stated for every functional gas oracle; the headline's zero-oracle conjunct follows by
  CompleteAnyGasW.toComplete"), and one fewer sorry than RECON.2's shape would have had. -/

/-- **OBLIGATIONS 1 AND 3, WIDENED: TWO OUTCOMES.** PROVED, and it adds no leaf of its own beyond the
    two scan obligations ST.10 and ST.12 that twoOutcomesV3_of_valid already rests on. The exit scan is
    read off ValidCore.program - the same projection exitDiscipline_of_valid performs on ValidV3, at
    the ValidCore face of it (programOk's third conjunct), so no clause is added and no fact restated.
    Conjunct 3 reads no evaluator and no accumulator fact, whatever the evaluator answers: that is why
    TwoOutcomesW needs no Q. -/
theorem twoOutcomesW_of_valid (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (hR : ValidW R Q) :
    TwoOutcomesW R :=
  twoOutcomesW_of_scans R hR.core.noWriters hR.core.program.2.2.1

/-- **OBLIGATION 1, SOUNDNESS HALF, WIDENED: PROGRAM-LEVEL REJECTION.** SKELETON. NAMED LEAVES: the
    seven widened simulation rows of SimContractsW sequenced (SIM.2's proofs, re-pointed at BlockSimW),
    the widened prefix row (SIM.6), the accumulator arms of the vkLoading and finalPairing rows (WID.13,
    WID.15), the external arm of the quotientLin row (WID.16), and the frame clauses the one-arm rows
    owe StageInvW - the two accumulator slots are not written and quotientEvaluator is not assigned
    (WID.14). The proof is RECON.2's rejectsV3_of_sims shape (Composition.lean) with StageInvW for
    StageInv and LeanAcceptsAcc for LeanAccepts: the traceReturn arm of exitSimW hands out LeanFinalAcc
    and leanAcceptsAcc_of_final (WideningStages.lean:394) is the link rejection reads. No block proof is
    in scope (D-P72 clause 1 is a STATEMENT obligation), so the hole is registered here, not filled. -/
theorem rejectsW_of_sims (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (hR : ValidW R Q) (hsim : SimContractsW R Q product) : RejectsW R Q product := by
  intro W Lyt H vkAddr qAddr cd st₀ evalRel g obs hw hside hna hobs hret
  sorry

/-- **OBLIGATION 2, WIDENED, IN THE STRONG GAS FORM (D-P72 clause 5).** SKELETON. NAMED LEAVES: the
    seven widened progress rows of ProgContractsW sequenced (SIM.2), the widened prefix progress row
    (SIM.6), runBody_mono (ST.13) to move from the zero gas oracle BlockProgSW fixes to the arbitrary
    total oracle this states, evalModel_gas_irrel (Widening.lean:439) for the gas() an external render
    executes once, and WID.19 for the accumulator and external arms. -/
theorem completeAnyGasW_of_progs (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hR : ValidW R Q) (hprog : ProgContractsW R Q product) :
    CompleteAnyGasW R Q product := by
  intro W Lyt H vkAddr qAddr cd st₀ evalRel hw hacc hcomp g hgt
  sorry

/-- **OBLIGATION 2, WIDENED, AT THE HEADLINE'S ZERO ORACLE.** PROVED from the strong form by
    CompleteAnyGasW.toComplete (Widening.lean:613): no new leaf, and this is the conjunct
    lowering_equivalenceW_of reads. -/
theorem completeW_of_progs (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (hR : ValidW R Q) (hprog : ProgContractsW R Q product) : CompleteW R Q product :=
  (completeAnyGasW_of_progs R Q product hR hprog).toComplete

/-- **OBLIGATION 4, WIDENED: TOTALITY.** SKELETON, and a separate leaf rather than a projection of
    conjunct 2 for RECON.2's reason (Composition.lean:207-213): totality carries no acceptance
    hypothesis, so it cannot be read off CompleteAnyGasW. NAMED LEAVES: the widened progress rows
    sequenced, the widened prefix progress row, and EvalBodyTotal (the third evaluator row,
    WideningStages.lean:492) - without it the honest relation may have no answer at the evaluator
    address and the run is stuck there; evalRel_answers (WideningStages.lean:505) is the link. -/
theorem totalW_of_stages (R : Render p G₁ G₂ Gₜ) (Q : EvalObject) (product : PairingProduct)
    (hR : ValidW R Q) (hprog : ProgContractsW R Q product) : TotalW R Q product := by
  intro W Lyt H vkAddr qAddr cd st₀ evalRel hw g hgt
  sorry

/-- **THE WIDENED COMPOSITION - THE CARD'S STEP 1.** The only route in the tree from the widened row
    families to the widened headline, exactly as lowering_equivalenceV3_of_rows is the only route from
    RECON.2's row families to the V3 headline. PROVED glue: the gluing step is WID.1's
    lowering_equivalenceW_of, so every sorryAx in this theorem's cone comes from the three obligations
    above and from nowhere else, and from no V2 block row. -/
theorem lowering_equivalence_of_stagesW (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hR : ValidW R Q) (hsim : SimContractsW R Q product)
    (hprog : ProgContractsW R Q product) : LoweringEquivalenceW R Q product :=
  lowering_equivalenceW_of R Q product (twoOutcomesW_of_valid R Q hR)
    (rejectsW_of_sims R Q product hR hsim) (completeW_of_progs R Q product hR hprog)
    (totalW_of_stages R Q product hR hprog)

/-- **THE WIDENED HEADLINE RESTRICTS TO THE V3 ONE, WITH NO SECOND COMPOSITION.** The sentence the
    whole card exists for, stated at the level that is TRUE. Take a V3-valid render and suppose the M6
    rows have been proved ONCE, in the widened shape. Then §1's reduction turns them into SIM.2's rows
    at StageInv - here, at the corner, sequenced by SIM.2's own slices_seq_sim - and RECON.2's
    composition consumes them once its two bundles are read at that boundary (§2's finding). PROVED
    glue; the point is that the route to LoweringEquivalenceV3 is still RECON.2's and this card adds no
    second one: it never concludes LoweringEquivalenceV3 from a W bundle directly. -/
theorem lowering_equivalenceW_of_V3 (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (product : PairingProduct) (hR : LoweringV3.ValidV3 R)
    (hW : LoweringEquivalenceW R Q product) : LoweringV3.LoweringEquivalenceV3 R product :=
  (equivalenceW_iff_V3 R Q product hR.supported.noAcc (quotientExternal_none_of_V3 hR)).mp hW

/-! ## §4. WITNESSES AND FALSIFIERS (rule W12) -/

/-- **THE CARD'S FALSIFIER, STEP FOR STEP.** The card names acc_not_supportedV3 (WideningV3.lean:123;
    tree name acc_not_supportedV2, Widening.lean:141) as showing "the V3 families do not cover an
    accumulator render". Stated as the consequence the duplicate-count question turns on: at an
    accumulator render the base families quantify over an EMPTY class, because ValidV3.supported is a
    SupportedV2 and SupportedV2 has a noAcc clause. So the widened families are not a paraphrase of the
    base ones - there is no ValidV3 to paraphrase from. PROVED. -/
theorem v3_class_excludes_an_accumulator_render (R : Render p G₁ G₂ Gₜ)
    (enc : Midfall.Generator.AccumulatorEncoding) (h : R.cfg.accumulator = some enc) :
    ¬ LoweringV3.ValidV3 R :=
  fun hR => acc_not_supportedV2 R enc h hR.supported

/-- **WITNESS THAT THE CORNER IS REACHED, WITH THE VALIDITY THE WIDENED BUNDLE NEEDS (W12).** Every
    render the V3 headline can speak of satisfies both corner hypotheses AND is ValidW with any
    evaluator object - ValidW.ofV3 is PROVED at Widening.lean:860 - so §1's reduction is not a lemma
    about a corner nobody stands on: it fires at every render RECON.2's composition reads, and the
    widened bundle adds no premise the V3 side did not already carry. PROVED. -/
theorem corner_is_reachable (R : Render p G₁ G₂ Gₜ) (Q : EvalObject)
    (hR : LoweringV3.ValidV3 R) : ValidW R Q ∧ R.cfg.accumulator = none ∧
      R.model.quotientExternal = none :=
  ⟨ValidW.ofV3 Q hR, hR.supported.noAcc, quotientExternal_none_of_V3 hR⟩

/-! ## §5. Card step 3: the re-pointing, and what the tree actually has

  THE CARD'S STEP 3 CANNOT BE DONE AS WRITTEN, AND THIS IS REPORTED RATHER THAN WORKED AROUND:
  GeneratorRows.lean IS NOT IN THE TREE. find . -name 'GeneratorRows*' returns
  docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean and its …Witness.lean sibling, and nothing
  under Midfall/: grep -rn 'HelperIs' Midfall/ is empty. The generic row statements have never been
  ported - that is RECON.1b's rebase and GEN.5's landing (QUEUE.md row 73d, "after RECON.3, RECON.1b"),
  and this card's ticket explicitly puts "the GeneratorRows repair" out of scope. There is no file to
  re-point.

  WHAT THE STEP ACTUALLY NEEDS, AND IS LANDED. The re-pointing is one line per row once it happens: a
  row's statement names a per-block contract, and the re-point is BlockSim -> BlockSimW and
  BlockProgS -> BlockProgSW. §1 proves those two pairs equivalent at the corner, so GEN.5 can state
  every row against the W family and discharge BOTH headlines with ONE proof - subject to §2's
  finding, which says RECON.2's two bundles must be read at SIM.2's boundary for that to reach the V3
  headline. That is the whole content step 3 could deliver before the rows exist; the rows are M6.

  The critic's table (top of WideningStages.lean, "WHICH CLAUSES OF VALIDITY EACH BASE ROW USES") is the
  row-by-row map of which rows need a second arm and which carry over: prefix, vkLoading, quotientLin,
  finalPairing and totality keep a base arm and get their second arm in WID.13, WID.15, WID.16, WID.19
  and a prefix child; transcriptParser, lagrange, pcs and traceReturn are one-arm and are restated over
  StageInvW with the two frame obligations WID.14 proves. All eight are now statable: BlockSimW /
  BlockProgSW is the boundary, ValidCore R ∧ SupportedW R is the validity the table's note (i) says is
  enough, and EvalContracts R Q is the evaluator's. -/

/-! ## §6. The card's Accept: #assert_axioms on the reduction and on the composition

  THE REDUCTION FIRST, exactly as the card asks: standard three, empty native list. Every lemma in §1
  that carries no render content beyond the corner passes this, and it is the machine-checked proof that
  the headline cone gains no native axiom from this card - the native count of
  lowering_equivalence_poseidon is untouched because nothing in that cone reads a W declaration. -/

#assert_axioms Midfall.LoweringW.leanFinalAcc_iff [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.poisonedW_iff [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.exitSimW_iff_exitSim [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.exitProgW_iff_exitProg [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.blockSimW_iff_blockSim [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.blockProgSW_iff_blockProgS [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.stageInv_unreachable_at_acc [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.v3_class_excludes_an_accumulator_render [propext, Classical.choice, Quot.sound] native []

/-  THE COMPOSITION, asserted. The card asks for "standard three, empty native list" on the composition
    too, and that is impossible for a SKELETON: three of its four obligations are registered holes, so
    sorryAx is in its cone by construction and not by accident - exactly as RECON.2's
    lowering_equivalenceV3_of_rows carries sorryAx for the same reason. What the card's clause is
    protecting is the NATIVE list, and that IS empty: no native axiom, and no new named axiom beyond
    the sorryAx of the leaves §3 names. -/
#assert_axioms Midfall.LoweringW.lowering_equivalence_of_stagesW [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.rejectsW_of_sims [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.completeAnyGasW_of_progs [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.totalW_of_stages [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.twoOutcomesW_of_valid [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.completeW_of_progs [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.blockSim_of_simContractsW [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.blockProgS_of_progContractsW [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.corner_of_validV3 [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.corner_is_reachable [propext, sorryAx, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringW.lowering_equivalenceW_of_V3 [propext, sorryAx, Classical.choice, Quot.sound] native []

/-! ## §7. Cone lists and axiom prints -/

#cone_sorries Midfall.LoweringW.twoOutcomesW_of_valid
#cone_sorries Midfall.LoweringW.rejectsW_of_sims
#cone_sorries Midfall.LoweringW.completeAnyGasW_of_progs
#cone_sorries Midfall.LoweringW.completeW_of_progs
#cone_sorries Midfall.LoweringW.totalW_of_stages
#cone_sorries Midfall.LoweringW.lowering_equivalence_of_stagesW

-- The reduction and the transport: PROVED, so their cones name only the leaves they route through.
#print axioms Midfall.LoweringW.leanFinalAcc_iff
#print axioms Midfall.LoweringW.poisonedW_iff
#print axioms Midfall.LoweringW.blockSimW_iff_blockSim
#print axioms Midfall.LoweringW.blockProgSW_iff_blockProgS
#print axioms Midfall.LoweringW.blockSim_of_simContractsW
#print axioms Midfall.LoweringW.blockProgS_of_progContractsW
#print axioms Midfall.LoweringW.exitSimW_iff_exitSim
#print axioms Midfall.LoweringW.exitProgW_iff_exitProg
#print axioms Midfall.LoweringW.stageInv_unreachable_at_acc
#print axioms Midfall.LoweringW.twoOutcomesW_of_valid
#print axioms Midfall.LoweringW.completeW_of_progs
#print axioms Midfall.LoweringW.lowering_equivalence_of_stagesW
#print axioms Midfall.LoweringW.v3_class_excludes_an_accumulator_render
#print axioms Midfall.LoweringW.corner_is_reachable
#print axioms Midfall.LoweringW.lowering_equivalenceW_of_V3
#print axioms Midfall.LoweringW.corner_of_validV3

-- The three registered holes, named for the register.
#print axioms Midfall.LoweringW.rejectsW_of_sims
#print axioms Midfall.LoweringW.completeAnyGasW_of_progs
#print axioms Midfall.LoweringW.totalW_of_stages

end Midfall.LoweringW
