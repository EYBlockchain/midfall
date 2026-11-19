/-
  Midfall.LoweringV3.Composition

  RECON.2 - THE ONE COMPOSITION: the four V3 obligations from the staged rows.

  THE HAZARD THIS FILE IS WRITTEN AGAINST. There is exactly ONE ValidV3 in the tree:
  Midfall/LoweringV3/Statements.lean:1116, seven clauses - generated, inputs, program, noWriters,
  env, payload, supported (RECON.1). The eighteen-clause text at
  docs/plans/V3-evidence/lean/statements/StatementsV3.lean is the D-P67-strike FALLBACK and is NOT
  imported here, and is not read by anything in this file. The line "#check @Midfall.LoweringV3.ValidV3.mk"
  at the bottom prints the seven-field constructor: that is the machine-checked proof of this claim,
  because over the fallback it prints eighteen fields with different names.

  WHAT "ONE COMPOSITION" MEANS. The V3 headline LoweringEquivalenceV3 (Statements.lean:1378) is four
  obligations - TwoOutcomes (:553), RejectsV3 (:1413), CompleteV3 (:1422), TotalV3 (:1432) - and
  lowering_equivalenceV3_of (:1442) already glues the four to the headline with no sorry. This file
  supplies the FOUR WAYS IN, each stated ONCE, each taking ValidV3:

    1. twoOutcomesV3_of_valid  - PROVED, via twoOutcomes_of_scans (step 5: the scan route,
       unconditional in the state; the entry-frame-guarded two_outcomes_of_exitShape route of the
       evidence file is NOT ported, and tr_exit_any / quiet_init stay evidence-only leaves of it).
    2. rejectsV3_of_sims       - SKELETON (step 4).
    3. completeV3_of_progs     - SKELETON (step 4).
    4. totalV3_of_stages       - SKELETON (conjunct 4, D-P64 (f)).

  lowering_equivalenceV3_of_rows then glues them, and it is the only V3 composition in the tree: the
  old staged one, lowering_equivalence_of_stages, is deleted from the evidence file by this card
  (step 6), and the V2 block-row composition lowering_equivalence_of_blocks is not restated here (the
  card: "the old rows are not composed again").

  THE CALLDATA SIZE BOUND REACHES EVERY ROW (step 2). Frame (Midfall/LoweringV2/Blocks.lean:56) now
  carries cdSize : cd.size < 2 ^ 256, so every boundary predicate built from Frame - Clean, Poisoned,
  exitOk, and the staged boundary StageBnd below - carries the bound, and no row states it separately.
  That is section 6 property (iv): these facts enter through Frame, never as a free hypothesis.
  cdSize_falsifier is the exhibit (step 1, W12).

  THE PIN BUNDLE IS DISSOLVED (step 4). The evidence file's SimPins had four fields. Three are
  conjuncts of G1CodecHeadlineLaws (compressedEncoderFirst, eipRoundtrip, toEip_one) and the fourth,
  hasMultiPointSet R = true, is a conjunct of programOk and so a projection of ValidV3.program.
  pins_from_valid_and_headlineLaws is that fact, PROVED. No clause was added to ValidV3 to get it.

  THE ROWS ARE RE-GATED ON FOUR LAWS, NOT SEVEN (step 3). SimRowsV3 and ProgRowsV3 take
  G1CodecHeadlineLaws R.E.g1 (four), never G1CodecLaws (seven). No V3 row needs a fifth law, so
  D-P64's bundle does not grow; the seven-law demand survives only in the frozen V2 BlockProgress,
  which this card does not touch.

  W12/W13 DISCIPLINE. Each sorried obligation carries a WITNESS (its hypotheses are the right ones and
  are jointly available - proved) and a FALSIFIER (a degenerate weakening exhibited false - proved).
  None is refuted: the cone prints 1 REFUTED at baseline (poseidon_valid, a V2 fixture sorry) and this
  card adds none. No native_decide occurs in this file, and the headline root
  lowering_equivalence_poseidon does not import it.
-/
import Midfall.LoweringV3.Statements
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

/-! ## §1. The staged boundary, over the SINGLE ValidV3 -/

/-- **THE STAGED BOUNDARY.** The V3 form of the evidence file's StageInv (SoundnessV3.lean:556; the
    card cites :539 - see the drift report), written with the vocabulary the built tree actually has:
    Frame (which now carries cdSize), LeanRaw, Decoded and leanStage from Midfall/Lowering/Stage.lean
    (SIM.1), and Inv. The evidence file splits Inv into BaseInv plus a snapshot half and adds a Mirror
    clause; those two names do not exist in the tree - they are SIM.2's - so the snapshot half is
    written here in full. This is a BOUNDARY PREDICATE, not a composition: SIM.2 lands BlockSim over
    it and proves the rows, and RECON.2 is the card that fixes the shape the headline reads. -/
def StageBnd (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (k : Checkpoint) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ LeanRaw R cd k ∧
    ∀ ms instW inst, Decoded R cd ms instW inst →
      ∃ S, leanStage R H inst ms k = .ok S ∧
        Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st

/-- How block q finishes a soundness run: revert, or the staged boundary at q.pre.next, except
    TraceReturn, which returns ABI true and hands out the closed Lean stage. -/
def exitSimBnd (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd
  | _ => o = .normal ∧ StageBnd R H vkAddr cd q.pre.next V' st'

/-- How block q finishes a progress run: the same, without the Lean fact (under LeanAccepts it is a
    hypothesis, read off at the return). -/
def exitProgBnd (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue)
  | _ => o = .normal ∧ StageBnd R H vkAddr cd q.pre.next V' st'

/-- **THE STAGED SIMULATION CONTRACT OF ONE BLOCK, V3**: every run of the CLOSED slice R.slice q in
    scope, from the staged boundary, reverts / exits at the next boundary / stays poisoned; from a
    poisoned boundary it reverts or stays poisoned, never laundered. -/
def BlockSimV3 (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (StageBnd R H vkAddr cd q.pre)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSimBnd R q H vkAddr cd V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))

/-- **THE STAGED PROGRESS CONTRACT OF ONE BLOCK, V3**, over the SAME boundary: total, under the honest
    precompiles and the zero gas oracle. -/
def BlockProgV3 (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.slice q)
      (StageBnd R H vkAddr cd q.pre)
      (fun _ _ V' st' o => exitProgBnd R q H vkAddr cd V' st' o)

/-! ## §2. The two row bundles: re-gated on FOUR codec laws (step 3), pinned by ValidV3 (step 4) -/

/-- **THE STAGED SIMULATION ROWS, V3.** The evidence file's Render.SimContracts (SoundnessV3.lean:621;
    the card cites :604) restated against the SINGLE ValidV3 and re-gated on the four-law bundle.
    Three changes, one per card step:
    * the validity hypothesis becomes ValidV3 R (step 4: the landed seven-clause text);
    * the SimPins hypothesis disappears: its three codec fields are conjuncts of
      G1CodecHeadlineLaws, which the headline already assumes, and its fourth is ValidV3.program
      (step 4, and pins_from_valid_and_headlineLaws);
    * the seven-law G1CodecLaws is not asked for anywhere (step 3). -/
def SimRowsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
      (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product),
    ∀ (H : Hash) (vkAddr : U256) (cd : Bytes), SoundSide R H cd →
      ∀ (q : Partial) (g : ExternalGas),
        BlockSimV3 R q H vkAddr (permissive (callsOf product)) g cd

/-- **THE STAGED PROGRESS ROWS, V3.** The evidence file's Render.ProgContracts (SoundnessV3.lean:1088;
    the card cites :1065) restated the same way. RECON.1b-i had already put G1CodecHeadlineLaws there;
    what this card changes is the validity hypothesis. -/
def ProgRowsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (hR : ValidV3 R) (hcodec : G1CodecHeadlineLaws R.E.g1)
      (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product),
    ∀ (H : Hash) (vkAddr : U256) (cd : Bytes),
      LeanAccepts R H cd → CompleteSide R H cd →
        ∀ q : Partial, BlockProgV3 R q H vkAddr product cd

/-- **WITNESS THAT THE PIN BUNDLE IS DISSOLVED (step 4, PROVED).** Every field the evidence file's
    SimPins carried is supplied by hypotheses the headline already has: three by the four-law codec
    bundle, the fourth by ValidV3.program. The rows need no separate bundle, and no clause was added
    to ValidV3 to get them. -/
theorem pins_from_valid_and_headlineLaws (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1) :
    (∀ Q : G₁, R.E.g1.ofCompressed? (R.E.g1.toCompressed Q) = some Q) ∧
      R.E.g1.eipRoundtrip ∧ R.E.g1.toEip 1 = Midfall.natToBytesBE 0 128 ∧
      hasMultiPointSet R.pv = true :=
  ⟨hcodec.compressedEncoderFirst, hcodec.eipRoundtrip, hcodec.toEip_one,
    hasMultiPointSet_of_valid hR⟩

/-! ## §3. The four obligations, each stated ONCE against ValidV3 -/

/-- **OBLIGATIONS 1 AND 3: TWO OUTCOMES.** Card step 5: the scan route, unconditional in the state.
    ValidV3.noWriters is frozen clause 10 and exitDiscipline_of_valid projects the exit scan out of
    ValidV3.program, so both hypotheses of twoOutcomes_of_scans are read off the landed text - no
    clause was added. PROVED from those two; its cone is exactly the two named leaves ST.10 and ST.12.
    The entry-frame-guarded evidence route (two_outcomes_of_exitShape, SoundnessV3.lean:1038; the card
    cites :1023) is NOT ported: it needs Render.ExitOk, which the single text does not carry, and its
    leaves tr_exit_any and quiet_init stay in the evidence file. -/
theorem twoOutcomesV3_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    TwoOutcomes R :=
  twoOutcomes_of_scans R hR.noWriters (exitDiscipline_of_valid hR)

/-- **OBLIGATION 1, SOUNDNESS HALF: PROGRAM-LEVEL REJECTION, V3.** Card step 4's restatement.
    SoundSide stays a hypothesis of the bundle (it excludes the logup-panic set, where the contract
    accepts and Lean panics - the set on which the frozen rejects_of_not_accepts was FALSE), and the
    conclusion is "not obs.isReturn", which with TwoOutcomes is the same as obs.isRevertOrHalt.

    SKELETON. The proof is the evidence file's rejects_of_sims (SoundnessV3.lean:822): four lines once
    the whole-program contract is available - factor the run at the prefix/slice boundary, spend the
    sequenced rows, read LeanAccepts off the TraceReturn exit through LeanFinal. NAMED LEAVES: the
    per-partial rows of SimRowsV3 sequenced (SIM.2) and the prefix row (SIM.6). The card's "Does NOT
    need" puts any block proof out of scope, so the hole is registered here and not filled. -/
theorem rejectsV3_of_sims (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hsim : SimRowsV3 R product) : RejectsV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec hside hna g obs hobs hret
  sorry

/-- **OBLIGATION 2: COMPLETENESS, V3.** Card step 4's restatement, re-gated on the four laws (step 3)
    and reading ValidV3 instead of the frozen Valid. SKELETON: the proof is the evidence file's
    completeness_of_progs (SoundnessV3.lean:1210; the card cites :1197) with the codec premise at the
    four laws, which is all the rows of ProgRowsV3 ask for. NAMED LEAVES: the seven progress rows
    (SIM.2) and the prefix progress row (SIM.6). -/
theorem completeV3_of_progs (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hprog : ProgRowsV3 R product) : CompleteV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec hacc hcomp
  sorry

/-- **OBLIGATION 4: TOTALITY, V3.** Under the honest precompiles and ANY total gas oracle a run
    exists, from every entry frame. D-P64 (f) generalises the frozen V2 BodyTotal over the frame; the
    V3 statement is Statements.lean:1432. SKELETON: the same row bundle as obligation 2 plus
    runBody_mono (ST.13) to move from the zero gas oracle the rows fix to the arbitrary total oracle
    this obligation quantifies over - which is why this is a separate leaf and not a projection of
    completeV3_of_progs. NAMED LEAVES: the progress rows (SIM.2), the prefix progress row (SIM.6),
    runBody_mono (ST.13). -/
theorem totalV3_of_stages (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hprog : ProgRowsV3 R product) : TotalV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec
  sorry

/-! ## §4. THE ONE COMPOSITION -/

/-- **THE HEADLINE, V3, FROM THE FOUR OBLIGATIONS.** The only V3 composition in the tree. PROVED with
    no sorry of its own: the gluing lemma lowering_equivalenceV3_of is already proved at
    Statements.lean:1442, so every sorryAx in this theorem's cone comes from the four obligations
    above and from nowhere else. -/
theorem lowering_equivalenceV3_of_rows (R : Render p G₁ G₂ Gₜ)
    (product : PairingProduct) (hR : ValidV3 R) (hsim : SimRowsV3 R product)
    (hprog : ProgRowsV3 R product) : LoweringEquivalenceV3 R product :=
  lowering_equivalenceV3_of R product (twoOutcomesV3_of_valid R hR)
    (rejectsV3_of_sims R product hR hsim) (completeV3_of_progs R product hR hprog)
    (totalV3_of_stages R product hR hprog)

/-! ## §5. WITNESSES AND FALSIFIERS (W12) -/

/-- **THE PADDED-CALLDATA FALSIFIER (card step 1).** The bound cd.size < 2 ^ 256 is not decoration:
    the vkLoading row of the staged simulation contract is FALSE without it. The mechanism, exhibited
    decidable and with no giant value built:

    * the EVM sees the calldata length only as a WORD - calldatasize is
      BitVec.ofNat 256 st.env.calldata.length (EVMExec.lean:792) - so padding by exactly 2 ^ 256 zero
      bytes leaves calldatasize, and hence every calldataload and calldatacopy the program performs,
      unchanged: conjunct (1);
    * the Lean decoder compares cd.size in Nat (Calldata.lean:341), so the same padding trips its
      length guard and it REJECTS the padded call although the frame cannot tell the two calls apart:
      conjunct (2) says the two views disagree at exactly this length;
    * conjunct (3) is the negation about the statement shape the card asks for: the inference "the
      frame's word view of the length determines the decoder's Nat view" is FALSE, because a length
      that is 0 to the frame and 2 ^ 256 to the decoder exists.

    Frame.cdSize is what refuses to admit such a frame, so every row built on Frame - Clean, Poisoned,
    exitOk, StageBnd - inherits the refusal. That is the Goal's "the calldata size bound reaches every
    row", and it is why no row had to state the bound itself. -/
theorem cdSize_falsifier :
    (BitVec.ofNat 256 (2 ^ 256) = 0) ∧
    ((2 ^ 256 : ℕ) ≠ 0 ∧ (2 ^ 256) % 2 ^ 256 = 0) ∧
    (¬ (BitVec.ofNat 256 (2 ^ 256) = 0 → (2 ^ 256 : ℕ) = 0)) := by
  refine ⟨rfl, ⟨by decide, Nat.mod_self _⟩, ?_⟩
  intro h
  exact absurd (h rfl) (by decide : (2 ^ 256 : ℕ) ≠ 0)

/-- **WITNESS FOR OBLIGATION 1 (W12): the row postcondition carries the Lean half, so the hypotheses
    are the right shape and are reachable.** The TraceReturn arm of exitSimBnd hands out LeanFinal -
    the calldata decodes and the closed Lean stage exists - which is the fact the rejection conclusion
    needs: rejectsV3_of_sims is proved by contradicting hna with it, via the tree lemma
    leanAccepts_of_final that the evidence file uses at SoundnessV3.lean:819. PROVED, and it is the
    projection the composition will actually use, which is what "the hypotheses hold together" means
    here: nothing in the bundle is unreachable from ValidV3. -/
theorem exitSimBnd_carries_the_lean_half (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (h : exitSimBnd R .traceReturn H vkAddr cd V' st' .halt) : LeanFinal R H cd := h.2.2

/-- **FALSIFIER FOR OBLIGATION 1 (W12): the simulation rows are not satisfied by a fall-through.** If
    the TraceReturn arm of exitSimBnd were weakened to allow a NORMAL exit - the v1 defect, a contract
    a stuck or empty program satisfies - then the bundle would be trivially satisfiable while the
    rejection conclusion stays open. Exhibited false: the traceReturn post refuses .normal outright. -/
theorem exitSimBnd_refutes_normal_traceReturn (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) :
    ¬ exitSimBnd R .traceReturn H vkAddr cd V' st' .normal := by
  intro h
  exact absurd h.1 (by decide)

/-- **WITNESS FOR OBLIGATIONS 2 AND 4 (W12): the hypotheses hold together.** ProgRowsV3 asks of the
    render exactly three things - ValidV3, the four-law codec bundle, the precompile assumption - and
    all three are hypotheses of the headline itself (Statements.lean:1379-1381), so the bundle adds no
    premise the conclusion does not already carry and the two cannot be jointly contradictory while the
    headline is satisfiable. PROVED as the projection the composition uses. -/
theorem progRows_reach_a_row (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hprog : ProgRowsV3 R product)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (hacc : LeanAccepts R H cd)
    (hcomp : CompleteSide R H cd) : ∀ q : Partial, BlockProgV3 R q H vkAddr product cd :=
  hprog hR hcodec hpc H vkAddr cd hacc hcomp

/-- **FALSIFIER FOR OBLIGATIONS 2 AND 4 (W12): the progress rows are not satisfied by a program that
    falls off the end.** The progress post of the TraceReturn block demands a HALT with the ABI-true
    return; weaken it to "any outcome" and both obligations become vacuously true of every render while
    concluding nothing. Exhibited false at the statement shape, decidable. -/
theorem exitProgBnd_refutes_fallthrough (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) :
    ¬ exitProgBnd R .traceReturn H vkAddr cd V' st' .normal := by
  intro h
  exact absurd h.1 (by decide)

/-- **WITNESS FOR THE SCAN PAIR (W12): the two hypotheses of twoOutcomes_of_scans hold together at an
    actual block**, so obligation 1/3 is not stated over an uninhabitable pair. PROVED by decide at
    the same toy block exitDiscipline_witness uses. -/
theorem twoOutcomes_hypotheses_together :
    ∃ (b : Block EVM.Op), NoWriters b ∧ ExitDiscipline b :=
  ⟨yul% { if iszero(calldataload(0)) { mstore(0, 7) revert(0, 4) }
           mstore(4096, 1)
           return(4096, 32) },
    ⟨⟨16, by decide⟩, exitDiscipline_witness⟩⟩

/-! ## §6. What M3's exit gate consumes: the leaf lists, and the landed-text check -/

#cone_sorries Midfall.LoweringV3.twoOutcomesV3_of_valid
#cone_sorries Midfall.LoweringV3.rejectsV3_of_sims
#cone_sorries Midfall.LoweringV3.completeV3_of_progs
#cone_sorries Midfall.LoweringV3.totalV3_of_stages
#cone_sorries Midfall.LoweringV3.lowering_equivalenceV3_of_rows

/-! **THE LANDED-TEXT PROOF.** Seven fields, and they are the landed ones: generated, inputs, program,
    noWriters, env, payload, supported. Over the eighteen-clause fallback this prints a different
    arity and different names. -/
#check @Midfall.LoweringV3.ValidV3.mk

/-! One obligation's hypothesis as landed: rejectsV3_of_sims's first premise is the seven-clause
    ValidV3 of LoweringV3/Statements.lean:1116, and its program clause is the V3 programOk bundle. -/
#check fun (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) => hR.program

-- The three boundary definitions are DEFINITIONS, not holes: none of them uses sorryAx, which is why
-- the cone lists above name only the five obligations and nothing of RECON.2's own scaffolding.
#print axioms Midfall.LoweringV3.StageBnd
#print axioms Midfall.LoweringV3.exitSimBnd
#print axioms Midfall.LoweringV3.BlockSimV3

#print axioms Midfall.LoweringV3.twoOutcomesV3_of_valid
#print axioms Midfall.LoweringV3.rejectsV3_of_sims
#print axioms Midfall.LoweringV3.completeV3_of_progs
#print axioms Midfall.LoweringV3.totalV3_of_stages
#print axioms Midfall.LoweringV3.lowering_equivalenceV3_of_rows
#print axioms Midfall.LoweringV3.cdSize_falsifier
#print axioms Midfall.LoweringV3.pins_from_valid_and_headlineLaws

end Midfall.LoweringV3
