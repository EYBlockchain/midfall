/-
  Midfall.LoweringV2.Stages

  SIM.2 - THE STAGED BOUNDARY AND THE STAGED CONTRACTS, AND NOW THE ONLY ROW SHAPE IN THE TREE
  (D-P74 item 2). This is the vocabulary the V3 obligations quantify over: Composition.lean's
  rejectsV3_of_sims and completeV3_of_progs - PROVED glue since PL.H0 - name "the rows sequenced
  (SIM.2)" and "the prefix row (SIM.6)" as their leaves; conjunct 4 goes through Totality.lean. This file lands the boundary refinement (StageInv, with the BaseInv / Mirror /
  Agree clauses RECON.2 had to write out inline), the two per-block contracts (BlockSim, BlockProgS), the
  sequencing that turns seven rows into ONE whole-program contract, the run decomposition that puts a
  RunBody and a slice run in the same breath, and the two prefix leaves as REGISTERED holes.

  IT LANDS NO COMPOSITION. RECON.2's Goal is "no second composition in the tree", and its change note on
  this card says the composition concludes rejectsV3_of_sims and completeV3_of_progs, not
  lowering_equivalence_of_stages. So the evidence file's soundness_of_sims, rejects_of_sims,
  completeness_of_progs and lowering_equivalence_of_stages are NOT ported: over R.Valid + SimPins they
  would be a parallel headline, and over ValidV3 they would be a second one. What is ported is everything
  those four consume, so the discharge is a few lines of application in a V3-side card and nowhere else.

  NO IMPORT OF LoweringV3, AND THAT IS FORCED. LoweringV3/Statements.lean:32 imports
  LoweringV2/Blocks (ST.5's finding), so a V2 file may not be on the receiving end of a future V3 edge:
  the card that fills rejectsV3_of_sims lives IN Composition.lean, and if Stages.lean imported
  Composition.lean that hole could never be filled in place - the same cycle ST.5 declined to rewire.
  The boundary-generic definitions below (exitSimAt / exitProgAt / BlockSimAt / BlockProgAt / MidAt and
  the _of lemmas) are what buys the reuse instead. **D-P74 item 2 made this file's shape the ONLY row
  shape**: PL.H0 re-pointed Midfall.LoweringV3.SimRowsV3 / ProgRowsV3 at BlockSim / BlockProgS and
  DELETED RECON.2's StageBnd, BlockSimV3 and BlockProgV3, so the V3 composition consumes these
  contracts directly and there is nothing left to bridge. The bridges were checked at the time against
  a scratch file importing both this module and Midfall.LoweringV3.Composition, each closed by the
  hypothesis alone; the four-field projection stageInv_drops_to_bnd_form below is the half of that
  this file can still state. The scratch is deliberately NOT landed: landing it would be the
  V3 import this file must not have.

  WHAT THE CARD ASKED FOR AND IS NOT HERE, WITH THE REASON (card steps 1 and 4 predate RECON.2, which
  dissolved them):
    * SimPins - RECON.2 dissolved it into G1CodecHeadlineLaws + ValidV3.program and PROVED the
      projection (Composition.lean:161, pins_from_valid_and_headlineLaws). A second pin bundle is a
      second hypothesis bundle for the same rows.
    * hasMultiPointSet - already in the tree TWICE (LoweringV2/Statements.lean:855,
      LoweringV3/Statements.lean:962), both taking a PlanView. Not restated here a third time.
    * Render.SimContracts / Render.ProgContracts - these are SimRowsV3 / ProgRowsV3 (Composition.lean
      :140, :150) with the validity hypothesis put back to the frozen R.Valid and SimPins re-added.
      RECON.2 restated them against ValidV3 on purpose; the rows the composition reads are its.
    * stmts_append_run, ex_append - Blocks.lean already carries the proved ExecStmts.append (:314) and
      StmtsContract.append (:333), which are these two. total_append below is built from them.
    * Render.ExitOk, two_outcomes_of_exitShape, quiet_init, tr_exit_any - SIM.3's, and RECON.2 took the
      scan route instead (Composition.lean:171-180), so conjunct 3 needs none of them.
    * XNonzero - the card does not list it and no obligation here reads it.

  CITATION DRIFT. The card cites SoundnessV3.lean by its pre-RECON.1b-i line numbers; that file was
  edited after the card was written (the hhoist.symm scope fix, the BodyTotal fourth conjunct, the
  G1CodecLaws -> G1CodecHeadlineLaws premise move). The mapping actually ported from, measured with
  grep -n on the current 1501-line file, is in the section headers below: section 1 drifted +17
  uniformly (SIM.1's report), sections 2-5 drifted non-uniformly, and the card's "460-830" is now
  471-835 while its "1050-1350" is now 1066-1393.

  W12/W13. Two holes are registered: prefix_sim and prefix_prog. Each carries a PROVED witness that its
  conclusion is the one the chain consumes (whole_program_sim, whole_program_prog) and a PROVED falsifier
  that the boundary it hands over is not True (stageInv_start_not_vacuous, mid_start_not_vacuous,
  finSim_refutes_empty, exitSim_refutes_normal_traceReturn, exitProg_refutes_normal_traceReturn). Nothing
  here is refuted: the cone still prints exactly 1 REFUTED (poseidon_valid), and no hypothesis was added
  to ValidV3 or to Render.Valid to make a contract close. No native_decide in this file (D-P17).
-/
import Midfall.LoweringV2.Blocks
import Midfall.Lowering.Stage
import Midfall.Yul.Contracts
import Midfall.Tools.ConeSorries

set_option autoImplicit false

namespace Midfall.LoweringV2

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
-- SIM.1's staged Lean view: LeanRaw, LeanFinal, Decoded and leanStage live in this namespace.
open Midfall.Lowering.Stage

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. The staged boundary (evidence SoundnessV3.lean section 2, now :471-627; the card cites 460-620)

  `StageInv k` takes NO snapshot argument. It is six things: `Frame` (which since RECON.2 carries the
  calldata size bound), `success = 1`, `BaseInv k` (the snapshot-free clauses of `Inv`),
  `LeanRaw k` (what the contract has established about the calldata bytes so far), `Mirror k`
  (memory regions that are verbatim copies of calldata sections - the D-5 clauses, which need no Lean
  value at all), and `Agree k` (for EVERY decoding, the Lean prefix at k exists and `Inv` holds for
  it). RECON.2's deleted `StageBnd` was this family with `BaseInv` and `Mirror` dropped: it wrote
  the `Agree` clause inline because the name did not exist yet. D-P74 item 2 retires it: the V3
  bundles read `StageInv` itself. -/

/-- The checkpoint whose `Inv` clauses mention no snapshot field. -/
def baseCk : Checkpoint → Checkpoint
  | .start => .start
  | _ => .vk

/-- The snapshot-free clauses of `Inv`, at any boundary: `InvAt .start` / `InvAt .vk` read the
    snapshot only through `S.acc.isSome`, which `witnessSnapshot` makes false, so the carrier is
    inert here. -/
def BaseInv (R : Render p G₁ G₂ Gₜ) (k : Checkpoint) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  match k with
  | .pcs | .pairing => True      -- the calldata decodes from here on, so `Agree` carries `Inv`
  | _ => Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params (baseCk k) R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) V st

/-- `n` bytes of calldata at offset `a` (no zero padding: a short slice is shorter). -/
def cdSlice (cd : Bytes) (a n : Nat) : Bytes :=
  ByteArray.mk ((cd.data.toList.drop a).take n).toArray

/-- A memory window is the verbatim copy of one calldata section (what `calldatacopy` /
    `mstore(eval_buf, calldataload(..))` leave behind in the parser). -/
def mirrorsSection (st : EvmState) (maddr : Nat) (cd : Bytes) (s : ProofSection) : Prop :=
  bytesAt st maddr s.byteLen = cdSlice cd s.start s.byteLen

/-- Lookup helpers and lookup accumulators interleave in calldata and are split in memory
    (TranscriptProofParser.yul:202-229): the helper walk advances by the helper section, the z walk by
    one G1 per lookup. -/
def lookupMirror (st : EvmState) (cd : Bytes) (hBase zBase : Nat) :
    List ProofLookupCommitmentsLayout → Nat → Nat → Prop
  | [], _, _ => True
  | l :: rest, hOff, i =>
      mirrorsSection st (hBase + hOff) cd l.helpers ∧
        mirrorsSection st (zBase + 128 * i) cd l.accumulator ∧
        lookupMirror st cd hBase zBase rest (hOff + l.helpers.byteLen) (i + 1)

/-- **THE CLAUSES DIGEST D-5 SAYS ARE MISSING FOR THE QUOTIENT-TO-PCS BOUNDARY**, stated against
    CALLDATA rather than against a snapshot: the five commitment regions `Inv` never pinned
    (lookup-m, perm-z, lookup-helper, lookup-z, trashcan), the REVERSED_EVALS window, plus the four
    regions `Inv .transcript` pins through the snapshot today. No `EvalRead → Fr` bridge is needed
    in the invariant: the window IS the evals section word for word, and relating that section to
    Lean's six arrays is an ALG lemma about `decodeCalldata` and `readAlgebra`. -/
structure MirrorAt (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) : Prop where
  advice : bytesAt st (ptrAddr R.pv.memory.adviceCommsMptrBase)
      (R.pv.proofLayout.advicePhases.foldl (fun a s => a + s.byteLen) 0) =
    cdSlice cd R.pv.proofLayout.proofCptr
      (R.pv.proofLayout.advicePhases.foldl (fun a s => a + s.byteLen) 0)
  lookupM : mirrorsSection st (ptrAddr R.pv.memory.lookupMCommsMptrBase) cd
      R.pv.proofLayout.lookupMultiplicities
  permZ : mirrorsSection st (ptrAddr R.pv.memory.permZCommsMptrBase) cd
      R.pv.proofLayout.permutationProducts
  lookups : lookupMirror st cd (ptrAddr R.pv.memory.lookupHelperCommsMptrBase)
      (ptrAddr R.pv.memory.lookupZCommsMptrBase) R.pv.proofLayout.lookups 0 0
  trash : mirrorsSection st (ptrAddr R.pv.memory.trashcanCommsMptrBase) cd R.pv.proofLayout.trash
  quotientLimbs : mirrorsSection st (ptrAddr R.pv.memory.quotientLimbCommsMptrBase) cd
      R.pv.proofLayout.quotientLimbs
  evals : mirrorsSection st (ptrAddr R.pv.memory.reversedEvalsMptr) cd R.pv.proofLayout.evals
  fCom : mirrorsSection st (ptrAddr R.pv.memory.fComMptr) cd R.pv.proofLayout.fCom
  pi : mirrorsSection st (ptrAddr R.pv.memory.piMptr) cd R.pv.proofLayout.pi
  qEvalCptr : wordAt st (ptrAddr R.pv.memory.qEvalCptrMptr) =
    BitVec.ofNat 256 R.pv.proofLayout.qEvalCptr

/-- The mirror is asserted between the parser and the PCS block, which is where it is read; elsewhere it
    costs nothing. -/
def Mirror (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) : Checkpoint → Prop
  | .transcript | .lagrange | .quotient => MirrorAt R cd st
  | _ => True

/-- The decode-relative half: for every decoding, the Lean prefix exists and `Inv` holds for it. This
    is the clause RECON.2 wrote inline as the last conjunct of its (now deleted) `StageBnd`; it
    is the same proposition, named. -/
def Agree (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∃ S, leanStage R H inst ms k = .ok S ∧
      Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params k R.pv S V st

/-- **THE STAGED INVARIANT.** One family, used by soundness AND completeness. -/
def StageInv (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ BaseInv R k V st ∧
    LeanRaw R cd k ∧ Mirror R cd st k ∧ Agree R H cd k V st

/-- **THE BOUNDARY SHAPE, GENERIC IN THE BOUNDARY PREDICATE.** Everything in sections 2 and 3 is proved
    over this, so ONE copy of the sequencing serves every boundary: `StageInv` here, and RECON.2's
    the V3 side's boundary, with nothing restated. The `traceReturn` arm is boundary-free: it is
    where the closed Lean stage leaves the program, which is the fact rejection reads. -/
def exitSimAt (R : Render p G₁ G₂ Gₜ) (H : Hash) (_vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop)
    (q : Partial) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd
  | _ => o = .normal ∧ B q.pre.next V' st'

/-- The progress arm: the same, without the Lean fact (under `LeanAccepts` it is a hypothesis, read off
    at the return). -/
def exitProgAt (_R : Render p G₁ G₂ Gₜ) (_H : Hash) (_vkAddr : U256) (_cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop)
    (q : Partial) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue)
  | _ => o = .normal ∧ B q.pre.next V' st'

/-- **THE PER-BLOCK SIMULATION CONTRACT, GENERIC IN THE BOUNDARY.** No snapshot is presupposed. From a
    staged boundary every run of the CLOSED slice, in `R.scope`, reverts; or exits at the next
    boundary; or exits poisoned. From a poisoned boundary a run reverts or stays poisoned, never
    laundered. The four §6 properties of Blocks.lean are kept: (i) closed slices in `R.scope`,
    (iii) the poisoned arm, (iv) facts enter through `Frame`; (ii) totality is `BlockProgAt`. -/
def BlockSimAt (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes)
    (B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q) (B q.pre)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSimAt R H vkAddr cd B q V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))

/-- How block `q` finishes a soundness run at the staged invariant. -/
def exitSim (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  exitSimAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st) q V' st' o

/-- **THE PER-BLOCK SIMULATION CONTRACT** over `StageInv`: the `BlockSimAt` instance at the staged
    invariant. -/
def BlockSim (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  BlockSimAt R q H vkAddr c g cd (fun k V st => StageInv R H vkAddr cd k V st)

/-- How block `q` finishes a progress run at the staged invariant. -/
def exitProg (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  exitProgAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st) q V' st' o

/-- The progress contract shape, generic in the boundary. -/
def BlockProgAt (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes)
    (B : Checkpoint → VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        → EvmState → Prop) : Prop :=
  StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.slice q) (B q.pre)
      (fun _ _ V' st' o => exitProgAt R H vkAddr cd B q V' st' o)

/-- **THE TOTAL PROGRESS CONTRACT**, over `StageInv`: total, under the honest precompiles and the zero
    gas oracle. -/
def BlockProgS (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  BlockProgAt R q H vkAddr product cd (fun k V st => StageInv R H vkAddr cd k V st)

/-! ## 2. Sequencing plumbing (evidence section 3, now :631-751; the card cites 629-751)

  Dialect-generic, all PROVED, no render content: these are the composition facts the vendored layer
  lacks. `StmtsContractAll.append` (Contracts.lean:156) and `StmtsContract.append` /
  `ExecStmts.append` (Blocks.lean:333, :314) already exist and are used rather than duplicated. -/

section Seq

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- A postcondition that says "continue at `mid`, or stop with `fin` already established". -/
def splitPost (mid : VEnv D → D.State → Prop) (fin : VEnv D → D.State → Outcome → Prop) :
    VEnv D → D.State → VEnv D → D.State → Outcome → Prop :=
  fun _ _ V' st' o => (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ fin V' st' o)

/-- Two split contracts compose to a split contract. -/
theorem seq_split {funs : FunEnv D} {a b : Block D.Op}
    {pre mid mid' : VEnv D → D.State → Prop} {fin : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsContractAll funs a pre (splitPost mid fin))
    (hb : StmtsContractAll funs b mid (splitPost mid' fin)) :
    StmtsContractAll funs (a ++ b) pre (splitPost mid' fin) := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases ha V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact hb V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne'
  · rcases ha V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hfin⟩
    · exact absurd heq hne
    · exact Or.inr ⟨hne, hfin⟩

/-- A split contract followed by a closing contract. -/
theorem seq_final {funs : FunEnv D} {a b : Block D.Op}
    {pre mid : VEnv D → D.State → Prop} {fin : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsContractAll funs a pre (splitPost mid fin))
    (hb : StmtsContractAll funs b mid (fun _ _ V' st' o => fin V' st' o)) :
    StmtsContractAll funs (a ++ b) pre (fun _ _ V' st' o => fin V' st' o) := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases ha V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne', _⟩
    · exact hb V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne'
  · rcases ha V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hfin⟩
    · exact absurd heq hne
    · exact hfin

/-- Seven blocks: six split contracts along a chain of mids, then a closing one. -/
theorem seq7 {funs : FunEnv D} {s1 s2 s3 s4 s5 s6 s7 : Block D.Op}
    {m0 m1 m2 m3 m4 m5 m6 : VEnv D → D.State → Prop}
    {fin : VEnv D → D.State → Outcome → Prop}
    (h1 : StmtsContractAll funs s1 m0 (splitPost m1 fin))
    (h2 : StmtsContractAll funs s2 m1 (splitPost m2 fin))
    (h3 : StmtsContractAll funs s3 m2 (splitPost m3 fin))
    (h4 : StmtsContractAll funs s4 m3 (splitPost m4 fin))
    (h5 : StmtsContractAll funs s5 m4 (splitPost m5 fin))
    (h6 : StmtsContractAll funs s6 m5 (splitPost m6 fin))
    (h7 : StmtsContractAll funs s7 m6 (fun _ _ V' st' o => fin V' st' o)) :
    StmtsContractAll funs (s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7) m0
      (fun _ _ V' st' o => fin V' st' o) :=
  seq_final (seq_split (seq_split (seq_split (seq_split (seq_split h1 h2) h3) h4) h5) h6) h7

/-- Total contracts compose, both halves. The existential half is `StmtsContract.append`
    (Blocks.lean:333) with a post that ignores the initial frame; the forall-runs half is the inversion
    of `Step.stmts_append_inv`, which `StmtsContractAll.append` cannot express because its head post
    is disjunctive and `StmtsTotal`'s is not. -/
theorem total_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → Outcome → Prop}
    (ha : StmtsTotal funs a pre (fun _ _ V' st' o => o = .normal ∧ mid V' st'))
    (hb : StmtsTotal funs b mid (fun _ _ V' st' o => post V' st' o)) :
    StmtsTotal funs (a ++ b) pre (fun _ _ V' st' o => post V' st' o) := by
  refine ⟨StmtsContract.append ha.1 (fun _ _ _ => hb.1), ?_⟩
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := D) hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · exact hb.2 V₁ st₁ (ha.2 V st hpre V₁ st₁ .normal h₁).2 V' st' o h₂
  · exact absurd (ha.2 V st hpre V' st' o h₁).1 hne

end Seq

/-- The boundary predicate the chain runs on: staged-clean or poisoned, generic in the boundary. -/
def MidAt (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop)
    (k : Checkpoint) (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  B k V st ∨ Poisoned R H vkAddr cd V st

/-- The chain's boundary at the staged invariant. -/
def Mid (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  MidAt R H vkAddr cd (fun k V st => StageInv R H vkAddr cd k V st) k V st

/-- What the whole slice list may end in: a revert, or ABI `true` together with the closed Lean stage.
    **THE LEAN FACT LEAVES THE PROGRAM HERE**, which is what the old `slices_seq_sound` dropped. It is
    boundary-free, so the same `FinSim` closes the chain at every boundary this shape is spent at. -/
def FinSim (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (_V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop :=
  (o = .halt ∧ Reverted st') ∨ (o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd)

/-- One non-terminal simulation row, in the split form the chain consumes - GENERIC IN THE BOUNDARY. -/
theorem blockSim_split_of {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes}
    {B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop}
    (hq : q ≠ .traceReturn) (h : BlockSimAt R q H vkAddr c g cd B) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => MidAt R H vkAddr cd B q.pre V st)
      (splitPost (fun V st => MidAt R H vkAddr cd B q.pre.next V st)
        (fun V' st' o => FinSim R H cd V' st' o)) := by
  intro V st hpre V' st' o hrun
  have hhalt : (Outcome.halt : Outcome) ≠ Outcome.normal := by decide
  rcases hpre with hclean | hpois
  · rcases h.1 V st hclean V' st' o hrun with ⟨ho, hrev⟩ | hexit | ⟨_, ho, hp⟩
    · exact Or.inr ⟨ho ▸ hhalt, Or.inl ⟨ho, hrev⟩⟩
    · have hexit' : o = .normal ∧ B q.pre.next V' st' := by
        cases q <;> first | exact absurd rfl hq | exact hexit
      exact Or.inl ⟨hexit'.1, Or.inl hexit'.2⟩
    · exact Or.inl ⟨ho, Or.inr hp⟩
  · rcases h.2 V st hpois V' st' o hrun with ⟨ho, hrev⟩ | ⟨_, ho, hp⟩
    · exact Or.inr ⟨ho ▸ hhalt, Or.inl ⟨ho, hrev⟩⟩
    · exact Or.inl ⟨ho, Or.inr hp⟩

/-- The terminal simulation row, in closing form - GENERIC IN THE BOUNDARY: the `traceReturn` arm of
    `exitSimAt` is exactly the second arm of `FinSim`, Lean fact included. -/
theorem blockSim_final_of {R : Render p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes}
    {B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop}
    (h : BlockSimAt R .traceReturn H vkAddr c g cd B) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .traceReturn)
      (fun V st => MidAt R H vkAddr cd B .pairing V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) := by
  intro V st hpre V' st' o hrun
  rcases hpre with hclean | hpois
  · rcases h.1 V st hclean V' st' o hrun with hrev | hexit | ⟨hne, _⟩
    · exact Or.inl hrev
    · exact Or.inr hexit
    · exact absurd rfl hne
  · rcases h.2 V st hpois V' st' o hrun with hrev | ⟨hne, _⟩
    · exact Or.inl hrev
    · exact absurd rfl hne

/-- **SEQUENCING, SIMULATION, GENERIC IN THE BOUNDARY.** Seven rows compose to ONE contract for
    `R.slices`: from a boundary at `.start`, every run reverts or returns ABI `true` WITH
    `LeanFinal`. This is the lemma `rejectsV3_of_sims` consumes: instantiated at `StageInv` it turns
    the seven `BlockSim` rows of `SimRowsV3` into a whole-program contract,
    and the `LeanFinal` in `FinSim` is what `leanAccepts_of_final` (Stage.lean:426) turns back into
    `LeanAccepts`. -/
theorem slices_seq_sim_at (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas)
    {B : Checkpoint → VEnv (Bridge.Dialect c g) → EvmState → Prop}
    (h7 : ∀ q : Partial, BlockSimAt R q H vkAddr c g cd B) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices
      (fun V st => MidAt R H vkAddr cd B .start V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) :=
  seq7 (blockSim_split_of (q := .vkLoading) (by decide) (h7 .vkLoading))
    (blockSim_split_of (q := .transcriptParser) (by decide) (h7 .transcriptParser))
    (blockSim_split_of (q := .lagrange) (by decide) (h7 .lagrange))
    (blockSim_split_of (q := .quotientLin) (by decide) (h7 .quotientLin))
    (blockSim_split_of (q := .pcs) (by decide) (h7 .pcs))
    (blockSim_split_of (q := .finalPairing) (by decide) (h7 .finalPairing))
    (blockSim_final_of (h7 .traceReturn))

/-- One non-terminal `BlockSim`, in the split form the chain consumes (card step 2). -/
theorem blockSim_split {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes} (hq : q ≠ .traceReturn)
    (h : BlockSim R q H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Mid R H vkAddr cd q.pre V st)
      (splitPost (fun V st => Mid R H vkAddr cd q.pre.next V st)
        (fun V' st' o => FinSim R H cd V' st' o)) :=
  blockSim_split_of hq h

/-- The terminal `BlockSim`, in closing form (card step 2). -/
theorem blockSim_final {R : Render p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256}
    {c : ExternalCalls} {g : ExternalGas} {cd : Bytes}
    (h : BlockSim R .traceReturn H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice .traceReturn)
      (fun V st => Mid R H vkAddr cd .pairing V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) :=
  blockSim_final_of h

/-- **SEQUENCING (replaces `slices_seq_sound`), PROVED.** Seven `BlockSim`s compose to one contract
    for `R.slices`: from a staged boundary at `.start`, every run reverts or returns ABI `true`
    WITH `LeanFinal`. Six applications of `seq_split` and one of `seq_final`. -/
theorem slices_seq_sim (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (h7 : ∀ q : Partial, BlockSim R q H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices
      (fun V st => Mid R H vkAddr cd .start V st)
      (fun _ _ V' st' o => FinSim R H cd V' st' o) :=
  slices_seq_sim_at R H vkAddr cd c g h7

/-- One non-terminal progress row in chain form - GENERIC IN THE BOUNDARY. -/
theorem blockProg_step_of {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {product : PairingProduct} {cd : Bytes}
    {B : Checkpoint → VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        → EvmState → Prop}
    (hq : q ≠ .traceReturn) (h : BlockProgAt R q H vkAddr product cd B) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.slice q)
      (fun V st => B q.pre V st)
      (fun _ _ V' st' o => o = .normal ∧ B q.pre.next V' st') := by
  have hconv : ∀ (V' : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)))
      (st' : EvmState) (o : Outcome), exitProgAt R H vkAddr cd B q V' st' o →
      o = .normal ∧ B q.pre.next V' st' := by
    intro V' st' o hexit
    cases q <;> first | exact absurd rfl hq | exact hexit
  refine ⟨?_, ?_⟩
  · intro V st hpre
    obtain ⟨V', st', o, hrun, hexit⟩ := h.1 V st hpre
    exact ⟨V', st', o, hrun, hconv V' st' o hexit⟩
  · intro V st hpre V' st' o hrun
    exact hconv V' st' o (h.2 V st hpre V' st' o hrun)

/-- One non-terminal `BlockProgS` in chain form (card step 4). -/
theorem blockProg_step {R : Render p G₁ G₂ Gₜ} {q : Partial} {H : Hash} {vkAddr : U256}
    {product : PairingProduct} {cd : Bytes} (hq : q ≠ .traceReturn)
    (h : BlockProgS R q H vkAddr product cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.slice q)
      (fun V st => StageInv R H vkAddr cd q.pre V st)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st') :=
  blockProg_step_of hq h

/-- **SEQUENCING, PROGRESS (replaces `slices_seq_progress`), PROVED - BOTH HALVES, GENERIC IN THE
    BOUNDARY.** This is the lemma `completeV3_of_progs` consumes: instantiated at `StageInv` it turns
    the seven `BlockProgS` rows of `ProgRowsV3` into one total contract over `R.slices`, existence
    included. Conjunct 4 does NOT come this way: `BodyTotal` quantifies over every calldata while
    `ProgRowsV3` assumes `LeanAccepts`, so PL.H0 routes it through `totalV3_correct`
    (LoweringV3/Totality.lean) and deletes `totalV3_of_stages`. -/
theorem slices_seq_prog_at (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    {B : Checkpoint → VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        → EvmState → Prop}
    (h7 : ∀ q : Partial, BlockProgAt R q H vkAddr product cd B) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => B .start V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) :=
  total_append
    (total_append
      (total_append
        (total_append
          (total_append
            (total_append (blockProg_step_of (q := .vkLoading) (by decide) (h7 .vkLoading))
              (blockProg_step_of (q := .transcriptParser) (by decide) (h7 .transcriptParser)))
            (blockProg_step_of (q := .lagrange) (by decide) (h7 .lagrange)))
          (blockProg_step_of (q := .quotientLin) (by decide) (h7 .quotientLin)))
        (blockProg_step_of (q := .pcs) (by decide) (h7 .pcs)))
      (blockProg_step_of (q := .finalPairing) (by decide) (h7 .finalPairing)))
    (h7 .traceReturn)

/-- The `StageInv` instance of the progress chain (card step 4). -/
theorem slices_seq_prog (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (h7 : ∀ q : Partial, BlockProgS R q H vkAddr product cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => StageInv R H vkAddr cd .start V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) :=
  slices_seq_prog_at R product H vkAddr cd h7

/-! ## 3. The prefix, and the two run decompositions (evidence :753-835 and :1197-1234; the card cites
  736-830 and 1184-1221)

  Everything the closed program runs before the first slice, and the two directions that let a row be
  spent on a `RunBody` hypothesis. Both decompositions are PROVED from `prog_slices_decomp`
  (Blocks.lean:234, a REGISTERED sorry of ST.11): no new hole is opened by them, and their cones print
  that one name and nothing else. -/

/-- Everything the closed program runs before the first slice (`funDef` statements included: each is a
    no-op step). -/
def Render.preBlock (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) : YulBlock :=
  R.preSlice vkAddr 0 ++ R.helpers ++ R.mainLocalsInlined

/-- **RUN DECOMPOSITION, PROVED from `prog_slices_decomp`** (the existential form digest C-3 asks
    for: no prefix endpoint is fixed, so no determinism is needed). A committed run of the program IS a
    run of `preBlock ++ slices` in the block scope. -/
theorem run_split (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (hobs : RunBody R vkAddr 0 c g st₀ obs) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome),
      obs = ⟨committedState st₀ st', o⟩ ∧
        ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
          (R.preBlock vkAddr ++ R.slices) V' st' o := by
  obtain ⟨V', st', hrun, heq⟩ := hobs
  obtain ⟨hprog, hhoist⟩ := prog_slices_decomp R vkAddr 0 c g
  have hrun' : ExecStmt (Bridge.Dialect c g) [] [] st₀ (.block (R.prog vkAddr 0)) V' st'
      obs.outcome := hrun
  cases hrun' with
  | block hstmts =>
      rename_i Vb
      refine ⟨Vb, st', obs.outcome, ?_, ?_⟩
      · cases obs
        simp only at heq ⊢
        rw [heq]
      · have hscope : R.scope c g = [hoist (Bridge.Dialect c g) (R.prog vkAddr 0)] := hhoist.symm
        rw [hscope]
        have hbody : R.preBlock vkAddr ++ R.slices = R.prog vkAddr 0 := by
          rw [hprog]; rfl
        rw [hbody]
        exact hstmts

/-- The converse of `run_split` (PROVED from `prog_slices_decomp`): a run of `preBlock ++ slices`
    in the block scope is a committed run of the program. -/
theorem run_join (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
      (R.preBlock vkAddr ++ R.slices) V' st' o) :
    RunBody R vkAddr 0 c g st₀ ⟨committedState st₀ st', o⟩ := by
  obtain ⟨hprog, hhoist⟩ := prog_slices_decomp R vkAddr 0 c g
  have hscope : R.scope c g = [hoist (Bridge.Dialect c g) (R.prog vkAddr 0)] := hhoist.symm
  have hbody : R.preBlock vkAddr ++ R.slices = R.prog vkAddr 0 := by
    rw [hprog]; rfl
  rw [hscope, hbody] at hrun
  exact ⟨restore [] V', st', Step.block hrun, rfl⟩

/-- **SIM.6.d's DELIVERABLE, LANDED HERE (dialect-generic, no premise gap).** A block whose every
    statement is a function definition is a NO-OP step sequence: the environment, the state and the
    outcome are the ones it started with. This is the fact the prefix walk needs for R.helpers
    (Render.preBlock puts the helper definitions between the two guards and the main locals), and it
    is SIM.6's own 0.5 h child card: SIM.6.a-d are prerequisites of SIM.6 and had not landed in this
    tree, so the piece of them that needs nothing beyond the vendored Step rules is proved here
    rather than left as a hole inside a hole. Only Step.funDef (BigStep.lean:223) and
    Step.stmts_cons_inv are used - no EVM, no render, no computation. -/
theorem funDefs_noop {D : YulSemantics.Dialect} [DecidableEq D.Value]
    (funs : FunEnv D) (b : Block D.Op)
    (hb : forall s, s ∈ b -> ∃ (n : String) (ps rs : List String) (body : Block D.Op),
      s = Stmt.funDef n ps rs body)
    {V V' : VEnv D} {st st' : D.State} {o : Outcome}
    (h : ExecStmts D funs V st b V' st' o) : V' = V ∧ st' = st ∧ o = .normal := by
  induction b with
  | nil => cases h with | seqNil => exact ⟨rfl, rfl, rfl⟩
  | cons s rest ih =>
      have hrest : ∀ x ∈ rest, ∃ (n : String) (ps rs : List String) (body : Block D.Op),
          x = Stmt.funDef n ps rs body := fun x hx => hb x (List.Mem.tail s hx)
      rcases Step.stmts_cons_inv (D := D) h with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
      · obtain ⟨n, ps, rs, body, rfl⟩ := hb s (List.Mem.head rest)
        cases h₁ with | funDef =>
        obtain ⟨hV, hst, ho⟩ := ih hrest h₂
        exact ⟨hV, hst, ho⟩
      · obtain ⟨n, ps, rs, body, rfl⟩ := hb s (List.Mem.head rest)
        cases h₁ with | funDef => exact absurd rfl hne

/-- **LEAF (SEM, SIM.6): THE PREFIX ROW, SOUNDNESS SIDE.** From an entry frame every run of the prefix
    reverts (ABI guard, memory guard) or ends at a staged boundary at `.start`. No `LeanAccepts` and
    no snapshot in the statement: `StageInv .start` is `Frame`, `success = 1` and the three
    `Inv .start` clauses.

    REGISTERED HOLE. WITNESS: `whole_program_sim` below is PROVED - the postcondition this leaves is
    exactly the hypothesis `slices_seq_sim` asks for, so the two leaves fit and the hole is one row,
    not a shape error. FALSIFIER: `stageInv_start_not_vacuous` below - the boundary it hands over is
    not `True`, so the row cannot be satisfied by just any prefix; and `finSim_refutes_empty` - the
    empty program does not satisfy the post. -/
theorem prefix_sim (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (W : ExecEnv) (Lyt : EVM.Layout)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (splitPost (fun V st => Mid R H vkAddr cd .start V st)
        (fun V' st' o => FinSim R H cd V' st' o)) := by
  sorry

/-- **LEAF (SEM, SIM.6): THE PREFIX ROW, PROGRESS SIDE.** Under the honest calls and a decodable
    calldata the prefix run EXISTS and every prefix run ends at the staged boundary `.start`.

    REGISTERED HOLE. WITNESS: `whole_program_prog` below is PROVED. FALSIFIER: the same pair -
    `stageInv_start_not_vacuous` refuses a vacuous boundary, and the existence half is not free: the
    zero gas oracle and the honest call relation are fixed here. PL.H0 routes conjunct 4 through
    `totalV3_correct` (LoweringV3/Totality.lean), which needs `prefix_live` and not this row. -/
theorem prefix_prog (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hacc : LeanAccepts R H cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd .start V' st') := by
  sorry

/-! ## 4. WITNESSES AND FALSIFIERS (W12) for the two registered holes -/

/-- **WITNESS FOR `prefix_sim` (W12): the two leaves FIT.** The split post `prefix_sim` leaves is
    literally the pre `slices_seq_sim` asks for, and the pair closes to one contract over the whole
    program. PROVED with no render content - which is the point: it shows the hole is a row to prove, not
    a statement that cannot be used. The evidence file's `soundness_of_sims` is this plus
    `leanAccepts_of_final`. -/
theorem whole_program_sim (R : Render p G₁ G₂ Gₜ) (st₀ : EvmState) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas)
    (hp : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr)
        (fun V st => V = [] ∧ st = st₀)
        (splitPost (fun V st => Mid R H vkAddr cd .start V st)
          (fun V' st' o => FinSim R H cd V' st' o)))
    (hs : StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices
        (fun V st => Mid R H vkAddr cd .start V st)
        (fun _ _ V' st' o => FinSim R H cd V' st' o)) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.preBlock vkAddr ++ R.slices)
        (fun V st => V = [] ∧ st = st₀) (fun _ _ V' st' o => FinSim R H cd V' st' o) :=
  seq_final hp hs

/-- **WITNESS FOR `prefix_prog` (W12): the progress leaves FIT**, existence half included - which is
    what `CompleteV3` needs; `TotalV3` is a separate tree (LoweringV3/Totality.lean, PL.H0). -/
theorem whole_program_prog (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (st₀ : EvmState)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hp : StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope _ _) (R.preBlock vkAddr) (fun V st => V = [] ∧ st = st₀)
        (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd .start V' st'))
    (hs : StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope _ _) R.slices (fun V st => StageInv R H vkAddr cd .start V st)
        (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue))) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope _ _) (R.preBlock vkAddr ++ R.slices) (fun V st => V = [] ∧ st = st₀)
        (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) :=
  total_append hp hs

/-- **FALSIFIER FOR BOTH PREFIX ROWS (W12): the boundary they hand over is not `True`.** Weaken
    `splitPost (Mid R H vkAddr cd .start) ...` to `splitPost (fun _ _ => True) ...` and each prefix
    row becomes trivially satisfiable while carrying no fact about the frame, the success bit, or the
    Lean stage - i.e. it stops being a row about THIS program. Exhibited: the empty environment fails the
    `success = 1` conjunct of `StageInv` at `.start` for EVERY state, so the boundary is a real
    claim. PROVED, decidable, no giant value built. -/
theorem stageInv_start_not_vacuous (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (st : EvmState) :
    ¬ StageInv R H vkAddr cd .start ([] : VEnv (Bridge.Dialect c g)) st := by
  intro h
  exact absurd h.2.1 (by decide : ¬ ((none : Option U256) = some (1 : U256)))

/-- The same for the disjunction the chain actually carries: `Mid .start` is not `True` at the empty
    environment either arm - the clean arm wants `success = 1` and the poisoned arm wants `success = 0`,
    and an empty environment has neither. So the prefix row's postcondition is not the trivial one. -/
theorem mid_start_not_vacuous (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) (st : EvmState) :
    ¬ Mid R H vkAddr cd .start ([] : VEnv (Bridge.Dialect c g)) st := by
  intro hm
  rcases hm with hsi | hpo
  · exact absurd hsi.2.1 (by decide : ¬ ((none : Option U256) = some (1 : U256)))
  · exact absurd hpo.2 (by decide : ¬ ((none : Option U256) = some (0 : U256)))

/-- **WITNESS THAT THE MIRROR CONJUNCT DOES NOT BLOCK THE ENTRY BOUNDARY.** `Mirror` is asserted only
    between the parser and the PCS block, so at `.start` it costs nothing: PROVED for every state.
    Without this the six-clause `StageInv` could be unsatisfiable at the boundary the prefix row has to
    reach, and `prefix_sim` would be a hole that cannot be filled. -/
theorem mirror_start (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (st : EvmState) :
    Mirror R cd st .start := trivial

/-- **FALSIFIER FOR THE SEQUENCED CONTRACT (W12, card step 6): it is not satisfied by a program that
    falls off the end.** `FinSim` demands a HALT - either a revert or the ABI-true return with the
    closed Lean stage. Weaken it to "any outcome" and `slices_seq_sim` is true of the EMPTY program
    while concluding nothing, which is the v1 defect this guards. Exhibited false at the statement shape,
    decidable, with no render content. -/
theorem finSim_refutes_empty (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (c : ExternalCalls) (g : ExternalGas) (funs : FunEnv (Bridge.Dialect c g)) :
    ¬ StmtsContractAll (D := Bridge.Dialect c g) funs []
        (fun _ _ => True) (fun _ _ V' st' o => FinSim R H cd V' st' o) := by
  intro h
  have hfin := h [] EVM.EvmState.init trivial [] _ .normal Step.seqNil
  rcases hfin with ⟨ho, _⟩ | ⟨ho, _⟩ <;> cases ho

/-- **FALSIFIER FOR `BlockSim` (W12): the `traceReturn` arm refuses a normal exit.** If the terminal
    row were allowed to hand off "normally" instead of returning ABI `true` with `LeanFinal`, the
    bundle would be trivially satisfiable while the rejection conclusion stays open - the same v1 defect
    at the per-block level rather than at the chain. PROVED, decidable. -/
theorem exitSim_refutes_normal_traceReturn (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) :
    ¬ exitSim R .traceReturn H vkAddr cd V' st' .normal := by
  intro h
  exact absurd h.1 (by decide)

/-- **FALSIFIER FOR `BlockProgS` (W12):** the progress post of the terminal block demands the HALT
    with the ABI-true return; weaken it to "any outcome" and `completeV3_of_progs` becomes vacuously
    true of every render while concluding nothing. -/
theorem exitProg_refutes_normal_traceReturn (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) :
    ¬ exitProg R .traceReturn H vkAddr cd V' st' .normal := by
  intro h
  exact absurd h.1 (by decide)

/-- **WITNESS FOR `BlockSim` / `BlockProgS` (W12): what the boundary asks for at the entry
    checkpoint, split out by name.** `StageInv .start` is a conjunction of five live facts plus the
    decode-relative `Agree`; this projection is the shape SIM.6 has to establish, and it is PROVED, so
    the registered hole is the run of the prefix and not a misunderstanding of the boundary. -/
theorem stageInv_start_conjuncts (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (h : StageInv R H vkAddr cd .start V st) :
    Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧
      BaseInv R .start V st ∧ LeanRaw R cd .start ∧ Mirror R cd st .start :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- **THE FOUR-FIELD PROJECTION, KEPT AS A FACT ABOUT `StageInv` ITSELF.** Drop `BaseInv` and
    `Mirror` from `StageInv` and what is left is `Frame`, the success bit, `LeanRaw` and the
    decode-relative `Agree` clause - i.e. the cheaper boundary RECON.2 used to write as `StageBnd`,
    deleted by D-P74 item 2. The projection is kept because it says how little of `StageInv` a caller
    has to use, and RECON.3's corner reduction reads it. The type names only V2 constants on purpose:
    this file may not import `LoweringV3` (header). -/
theorem stageInv_drops_to_bnd_form (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (k : Checkpoint) {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g))
    (st : EvmState) (h : StageInv R H vkAddr cd k V st) :
    Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ LeanRaw R cd k ∧
      Agree R H cd k V st :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

/-! ## 5. Cone lists and axiom prints -/

-- The two registered holes. Every other declaration in this file is PROVED, and the sequencing lemmas
-- carry no render content, so their cones are empty or the one existing ST.11 leaf.
#cone_sorries Midfall.LoweringV2.prefix_sim
#cone_sorries Midfall.LoweringV2.prefix_prog
#cone_sorries Midfall.LoweringV2.slices_seq_sim
#cone_sorries Midfall.LoweringV2.slices_seq_prog
#cone_sorries Midfall.LoweringV2.finSim_refutes_empty
#cone_sorries Midfall.LoweringV2.run_split

#print axioms Midfall.LoweringV2.funDefs_noop
#cone_sorries Midfall.LoweringV2.funDefs_noop

#print axioms Midfall.LoweringV2.StageInv
#print axioms Midfall.LoweringV2.BlockSim
#print axioms Midfall.LoweringV2.BlockProgS
#print axioms Midfall.LoweringV2.slices_seq_sim
#print axioms Midfall.LoweringV2.slices_seq_prog
#print axioms Midfall.LoweringV2.run_split
#print axioms Midfall.LoweringV2.run_join
#print axioms Midfall.LoweringV2.total_append
#print axioms Midfall.LoweringV2.finSim_refutes_empty
#print axioms Midfall.LoweringV2.whole_program_sim
#print axioms Midfall.LoweringV2.whole_program_prog
#print axioms Midfall.LoweringV2.stageInv_drops_to_bnd_form
#print axioms Midfall.LoweringV2.stageInv_start_not_vacuous
#print axioms Midfall.LoweringV2.exitSim_refutes_normal_traceReturn
#print axioms Midfall.LoweringV2.exitProg_refutes_normal_traceReturn

end Midfall.LoweringV2
