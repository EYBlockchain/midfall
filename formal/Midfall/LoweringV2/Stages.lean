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


/-! ## 3B. WHAT THE VALIDITY CLAUSES PIN ABOUT THE PREFIX (SIM.6.a, SIM.6.b, SIM.6.c's numerals)

  SIM.6's three remaining children were carded against a `GeneratorRows.lean` that is not in this
  tree (`grep -rn 'model_flags_of_valid|layout_static_of_valid|abi_guard_sem' Midfall/` returns only
  a docstring mention in `LoweringV3/WideningStages.lean`), so the pieces the prefix walk needs are
  proved here rather than left as holes inside a hole - the same call SIM.6.d's `funDefs_noop`
  records above. NOTHING IS ADDED: every fact below is a projection of a clause `Render.Valid`
  already carries, and the same seven clauses are `ValidV3`'s, so the V3 restatements of the two
  prefix rows read them through the same door.

  THE SOURCE IS `generated`, NOT `supported.layout`. `layout_windows_not_tied_to_the_map`
  (`LoweringV3/MemoryPairs.lean` §6) exhibits a layout whose map is well-formed and whose windows
  overlap, so no `WellFormed` machinery delivers a window fact; the CONSTRUCTION does. `MemoryPairs`
  §8-§9 peel `generateAll` for the three vkLoading premises; the peel is copied here over the V2
  `GeneratedBy` because this module may not import `LoweringV3` (header) - same binds, same shape,
  different fields. -/

/-- **THE MODEL CLAUSE OUT OF `generated`.** The peel `MemoryPairs.gvfp_of_generated` does on the V3
    side, on the frozen V2 `GeneratedBy`: seven binds and the record injection. -/
theorem pfx_gvfp {R : Render p G₁ G₂ Gₜ} (h : GeneratedBy R) :
    generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = .ok R.model := by
  obtain ⟨out, hg, hplan, hq, hm⟩ := h
  simp only [generated] at hg
  simp only [generateAll, Bind.bind] at hg
  obtain ⟨rawMeta, _, h1⟩ := except_bind_ok _ _ hg
  obtain ⟨plan, _, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨blocks, _, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨model, hgen, h4⟩ := except_bind_ok _ _ h3
  cases h5 : (Halo2Verifier.validateLayout model) with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
      simp only [h5] at h4
      have hA : { plan := plan, qblocks := blocks, model := model } = out :=
        Except.ok.inj (show Except.ok { plan := plan, qblocks := blocks, model := model } =
          Except.ok out from h4)
      have hp : plan = R.plan := (congrArg GenOut.plan hA).trans hplan
      have hb : blocks = R.qblocks := (congrArg GenOut.qblocks hA).trans hq
      have hm' : model = R.model := (congrArg GenOut.model hA).trans hm
      rw [hp, hb, hm'] at hgen
      exact hgen

/-- **SIM.6.a AND THE THREE ABI NUMERALS OF SIM.6.c, ONE PEEL.** The four `Model` fields the prefix
    statement reads: the two wrapper-locals flags and the three numerals the ABI guard compares
    against. Each is a field of the record literal `generateVerifierFromPlan` returns
    (Artifacts.lean:576, :580-582), so each is one `congrArg` on the injection - the card's "Stop if:
    the three model numerals are not derivable from the model clause" does NOT fire, and no premise
    gap is needed. `abiSelectorBytes` is `Generator.abiSelectorBytes = 0x04`,
    `abiProofHeadOffset` is `abiVerifyProofProofHeadOffset = 2 * wordBytes = 0x40` and
    `abiInstancesHeadCptr` is their sum `0x24`, all by computation. -/
theorem pfx_model_prefix_facts {R : Render p G₁ G₂ Gₜ} (h : GeneratedBy R) :
    R.model.abiSelectorBytes = 4 ∧ R.model.abiProofHeadOffset = 0x40 ∧
      R.model.abiInstancesHeadCptr = 0x24 ∧
      (R.model.embeddedVk = (if R.flags.separate then none else some R.plan.vk)) ∧
      (R.flags.externalQuotient = false → R.model.quotientExternal = none) := by
  have hg := pfx_gvfp h
  simp only [generateVerifierFromPlan, Bind.bind, Except.bind] at hg
  split at hg
  · cases hg
  · cases hg
  · obtain ⟨_vd, _, h1⟩ := except_bind_ok _ _ hg
    obtain ⟨rendering, hrender, h2⟩ := except_bind_ok _ _ h1
    obtain ⟨_pcs, _, h3⟩ := except_bind_ok _ _ h2
    obtain ⟨_up, _, h4⟩ := except_bind_ok _ _ h3
    obtain ⟨_afb, _, h5⟩ := except_bind_ok _ _ h4
    obtain ⟨_cg, _, h6⟩ := except_bind_ok _ _ h5
    obtain ⟨_ar, _, h7⟩ := except_bind_ok _ _ h6
    have hrec := Except.ok.inj h7
    have hA1 : R.model.abiSelectorBytes = Midfall.Generator.abiSelectorBytes := by rw [← hrec]
    have hA2 : R.model.abiProofHeadOffset =
        Midfall.Generator.abiVerifyProofProofHeadOffset := by rw [← hrec]
    have hA3 : R.model.abiInstancesHeadCptr =
        Midfall.Generator.abiSelectorBytes + Midfall.Generator.wordBytes := by rw [← hrec]
    have hEvk : R.model.embeddedVk =
        (if R.flags.separate = true then none else some R.plan.vk) := by rw [← hrec]
    refine ⟨hA1.trans rfl, hA2.trans rfl, hA3.trans rfl, hEvk, ?_⟩
    intro hext
    have hqe : R.model.quotientExternal = (rendering.intoTemplateParts).1 :=
      (congrArg (fun x => x.quotientExternal) hrec).symm
    rw [hqe]
    rw [hext] at hrender
    simp only [LoweringPlan.quotientRendering, Bind.bind, Except.bind] at hrender
    rw [if_neg Bool.false_ne_true] at hrender
    have hcase : R.plan.direct = none ∨ ∃ d, R.plan.direct = some d := by
      cases R.plan.direct with
      | none => exact Or.inl rfl
      | some d => exact Or.inr ⟨d, rfl⟩
    rcases hcase with hn | ⟨d, hd⟩
    · rw [hn] at hrender
      have hcase2 : (∃ v, R.plan.vmQuotient = .ok v) ∨ (∃ e, R.plan.vmQuotient = .error e) := by
        cases R.plan.vmQuotient with
        | ok v => exact Or.inl ⟨v, rfl⟩
        | error e => exact Or.inr ⟨e, rfl⟩
      rcases hcase2 with ⟨v, hv⟩ | ⟨e, he⟩
      · rw [hv] at hrender
        have hri := Except.ok.inj hrender
        rw [← hri]
        rfl
      · rw [he] at hrender
        cases hrender
    · rw [hd] at hrender
      have hri := Except.ok.inj hrender
      rw [← hri]
      rfl

/-- The plan equation out of `generated` (`MemoryPairs.plan_of_generated`, on the V2 clause). -/
theorem pfx_plan_of_generated {R : Render p G₁ G₂ Gₜ} (h : GeneratedBy R) :
    ∃ (rawMeta : ConstraintSystemMeta) (plan : LoweringPlan Unit Unit),
      ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances =
        Except.ok rawMeta ∧
      Midfall.Generator.PlanNew.newFromVk Features.solidity
        (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs
        rawMeta R.cfg.numInstances R.cfg.accumulator R.plan.vk = Except.ok plan ∧
      R.plan = plan := by
  obtain ⟨out, hg, hplan, hq, hm⟩ := h
  simp only [generated] at hg
  simp only [generateAll, Bind.bind] at hg
  obtain ⟨rawMeta, hraw, h1⟩ := except_bind_ok _ _ hg
  obtain ⟨plan, hpl, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨_blocks, _, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨_model, _, h4⟩ := except_bind_ok _ _ h3
  cases h5 : (Halo2Verifier.validateLayout _model) with
  | error e => simp only [h5] at h4; cases h4
  | ok u =>
      simp only [h5] at h4
      have hA : { plan := plan, qblocks := _blocks, model := _model } = out :=
        Except.ok.inj (show Except.ok { plan := plan, qblocks := _blocks, model := _model } =
          Except.ok out from h4)
      have hp : plan = R.plan := (congrArg GenOut.plan hA).trans hplan
      exact ⟨rawMeta, plan, hraw, hpl, hp.symm⟩

/-- `newFromVk`'s SECOND bind: the proof layout is `fromProtocol`'s output at the ABI pointer, for
    the meta the first bind produced. The twelve-bind peel `MemoryPairs.newFromVk_memory` does for
    `plan.memory`, done for `plan.proofLayout`; the split tail is the same
    `validateGeneratorInvariants` / `vkCarriesBuild` pair. -/
theorem pfx_newFromVk_proofLayout {F : Type} [BEq F] (feat : Features)
    (field : Midfall.Generator.QuotientEvaluator.FieldCtx F) (cs : ConstraintSystem F)
    (rawMeta : ConstraintSystemMeta) (numInstances : Nat)
    (accEncoding : Option Midfall.Generator.AccumulatorEncoding) (payload : Halo2VerifyingKey)
    (plan : LoweringPlan Unit Unit)
    (h : Midfall.Generator.PlanNew.newFromVk feat field cs rawMeta numInstances accEncoding
        payload = .ok plan) :
    ∃ (meta_ : ConstraintSystemMeta) (L : ProofCalldataLayout),
      ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr meta_.numEvals
        meta_.numPointSets = .ok L ∧ plan.proofLayout = L := by
  simp only [Midfall.Generator.PlanNew.newFromVk, Bind.bind, Except.bind] at h
  obtain ⟨q, _, h1⟩ := except_bind_ok _ _ h
  obtain ⟨proofLayout, hpl, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨_qplan, _, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨_build, _, h4⟩ := except_bind_ok _ _ h3
  obtain ⟨_nw, _, h5⟩ := except_bind_ok _ _ h4
  obtain ⟨_pcs, _, h6⟩ := except_bind_ok _ _ h5
  obtain ⟨_acc, _, h7⟩ := except_bind_ok _ _ h6
  obtain ⟨_memory, _, h8⟩ := except_bind_ok _ _ h7
  obtain ⟨_op, _, h9⟩ := except_bind_ok _ _ h8
  obtain ⟨_trip, _, h10⟩ := except_bind_ok _ _ h9
  split at h10 <;> (try (split at h10)) <;> (try (split at h10)) <;> (try (split at h10)) <;>
    (try (split at h10)) <;> (try (split at h10))
  all_goals (try (cases h10))
  all_goals (exact ⟨q.2.1, proofLayout, hpl, rfl⟩)

/-- `fromProtocol`'s first field is the pointer it was handed: Abi.lean:340 binds
    `proofCptr := abiVerifyProofProofCptr` and the record literal at :402 writes that name. -/
theorem fromProtocol_proofCptr (protocol : ProtocolPlan) (numEvals numPointSets : Nat)
    (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol abiVerifyProofProofCptr numEvals
        numPointSets = .ok L) :
    L.proofCptr = abiVerifyProofProofCptr := by
  rw [ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, _, h1⟩ := except_bind_ok _ _ h
  obtain ⟨x2, _, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨x3, _, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨x4, _, h4⟩ := except_bind_ok _ _ h3
  obtain ⟨x5, _, h5⟩ := except_bind_ok _ _ h4
  obtain ⟨x6, _, h6⟩ := except_bind_ok _ _ h5
  by_cases hc : (x6.2.1 != protocol.proof.commitments.length) = true
  · rw [ite_eq_left hc] at h6
    obtain ⟨r, hr, _⟩ := except_bind_ok _ _ h6
    cases hr
  · rw [ite_eq_right (by simpa using hc)] at h6
    cases h6
    rfl

/-- **SIM.6.b, LANDED.** The two static halves of `abiHeadOk` for every generated plan: the proof
    pointer IS the ABI constant and the sections tile exactly. The second conjunct is
    `Calldata.proofLen_eq_repackedLen`'s second half spent on the layout `generated` produces -
    that lemma is PROVED and is the cursor invariant, so nothing new is assumed here. -/
theorem layout_static_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.plan.proofLayout.proofCptr = abiVerifyProofProofCptr ∧
      R.plan.proofLayout.proofEnd =
        R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := pfx_plan_of_generated hR.generated
  obtain ⟨meta_, L, hL, hLp⟩ :=
    pfx_newFromVk_proofLayout Features.solidity
      (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have h2 := (proofLen_eq_repackedLen meta_.protocol meta_.numEvals meta_.numPointSets L hL).2
  have h1 := fromProtocol_proofCptr meta_.protocol meta_.numEvals meta_.numPointSets L hL
  rw [← hp] at hLp
  rw [hLp]
  exact ⟨h1, h2⟩

/-- The three table names the prefix reads that `expectedConsts_lookups` does not cover: the instance
    cursor the ABI guard subtracts from, and the two error selectors the two revert arms store. -/
theorem expectedConsts_lookups_prefix (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "NUM_INSTANCE_CPTR" = some pv.proofLayout.proofEnd ∧
      (expectedConsts pv m).lookup "ERR_BAD_CALLDATA_SHAPE" = some 0x1b99e37c ∧
      (expectedConsts pv m).lookup "ERR_MEMORY_LAYOUT_VIOLATED" = some 0xc9888d23 := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `NUM_INSTANCE_CPTR` at a valid render is the proof end: the guard's subtraction is a Nat
    subtraction on `proofEnd`, which is what makes it match `abiHeadOk`'s third word. -/
theorem numInstCptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.consts.lookup "NUM_INSTANCE_CPTR" = some R.pv.proofLayout.proofEnd :=
  (lookup_expectedConsts_of_programOkB hR.program.1 _).trans
    ((expectedConsts_lookups_prefix R.pv R.model).1)

/-- The render's table carries the transcript base: the site the memory guard reads. -/
theorem transcriptMptrConst_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.consts.lookup "TRANSCRIPT_MPTR" = some R.pv.memory.transcriptMptr :=
  ((lookup_expectedConsts_of_programOkB hR.program.1 _).trans
    ((expectedConsts_lookups R.pv R.model).2.2))

/-- The render's table carries the field modulus: the site the main block's let r reads. -/
theorem frModulusConst_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.consts.lookup "FR_MODULUS" = some frModulusConstant :=
  ((lookup_expectedConsts_of_programOkB hR.program.1 _).trans
    ((expectedConsts_lookups R.pv R.model).1))

theorem errBadCalldata_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some 0x1b99e37c :=
  (lookup_expectedConsts_of_programOkB hR.program.1 _).trans
    ((expectedConsts_lookups_prefix R.pv R.model).2.1)

theorem errMemoryLayout_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.consts.lookup "ERR_MEMORY_LAYOUT_VIOLATED" = some 0xc9888d23 :=
  (lookup_expectedConsts_of_programOkB hR.program.1 _).trans
    ((expectedConsts_lookups_prefix R.pv R.model).2.2)

/-- **SIM.6.a, LANDED.** The two shape flags `wrapperLocals` reads. `supported.separateVk` and
    `supported.embeddedQuotient` are the clauses; `generated` supplies the equations
    (Artifacts.lean:576, :580 and the `intoTemplateParts` arm). -/
theorem model_flags_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.model.embeddedVk.isNone = true ∧ R.model.quotientExternal.isSome = false := by
  have hf := pfx_model_prefix_facts hR.generated
  have h1 : R.model.embeddedVk = none := by
    rw [hf.2.2.2.1, hR.supported.separateVk]
    exact ite_eq_left rfl
  have h2 : R.model.quotientExternal = none := hf.2.2.2.2 hR.supported.embeddedQuotient.1
  exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩

/-- The two `generated` numerals the ABI guard needs, as render facts. -/
theorem abiNumerals_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.model.abiSelectorBytes = 4 ∧ R.model.abiProofHeadOffset = 0x40 ∧
      R.model.abiInstancesHeadCptr = 0x24 := by
  have hf := pfx_model_prefix_facts hR.generated
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-! ### The prefix in statement-list form

  The `vkSite` / `vk_slice_raw` pattern of `Blocks/VkLoading.lean`, applied to the three statements
  the prefix runs before the helpers: the fold is written to be STUCK at a symbolic constant table, so
  the shape lemma is `rfl` and each site's VALUE is supplied separately from the table projection.
  This is why SIM.6 step 1's `inline_append` (ST.11, still a sorry) is not needed here: no `++` is
  ever pushed through the inliner - the whole `preSlice` is folded at once. -/

/-- The inliner's stuck term at a symbolic table: the table's word where the table binds the name,
    otherwise the name itself (InlineConstants.lean:290-294, the `Expr.var` arm at an unshadowed
    position). -/
def pfxSite (x : String) (consts : Inline.Consts) : Expr EVM.Op :=
  match consts.lookup x with
  | some v => Expr.lit (.number v)
  | none => Expr.var x

/-- A table that binds `x` to `v` makes the site the literal. -/
theorem pfx_site_eq (x : String) (consts : Inline.Consts) (v : Nat)
    (h : consts.lookup x = some v) : pfxSite x consts = Expr.lit (.number v) := by
  simp [pfxSite, h]

/-- `iszero (and (eq (calldataload a) b) (eq (calldataload c) (NUM_INSTANCE_CPTR - a)))`, inlined. -/
def pfxAbiCond (m : Model) (consts : Inline.Consts) : Expr EVM.Op :=
  Expr.builtin Op.iszero [Expr.builtin Op.and
    [Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit m.abiSelectorBytes],
        lit m.abiProofHeadOffset],
     Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit m.abiInstancesHeadCptr],
        Expr.builtin Op.sub [pfxSite "NUM_INSTANCE_CPTR" consts,
          lit m.abiSelectorBytes]]]]

/-- `fail(ERR_BAD_CALLDATA_SHAPE)` inlined: `mstore(0, ERR << 224); revert(0, 4)`. -/
def pfxAbiBody (m : Model) (consts : Inline.Consts) : Block EVM.Op :=
  [Stmt.exprStmt (Expr.builtin Op.mstore
      [lit 0, Expr.builtin Op.shl [lit 224, pfxSite "ERR_BAD_CALLDATA_SHAPE" consts]]),
   Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])]

/-- `gt (mload 0x40) TRANSCRIPT_MPTR`, inlined (`mainGuardBlock`). -/
def pfxMemCond (consts : Inline.Consts) : Expr EVM.Op :=
  Expr.builtin Op.gt [Expr.builtin Op.mload [lit 0x40], pfxSite "TRANSCRIPT_MPTR" consts]

def pfxMemBody (consts : Inline.Consts) : Block EVM.Op :=
  [Stmt.exprStmt (Expr.builtin Op.mstore
      [lit 0, Expr.builtin Op.shl [lit 224, pfxSite "ERR_MEMORY_LAYOUT_VIOLATED" consts]]),
   Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])]

/-- The ABI guard with the three model numerals and the instance cursor resolved. -/
def pfxAbiCondNum (proofEnd : Nat) : Expr EVM.Op :=
  Expr.builtin Op.iszero [Expr.builtin Op.and
    [Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 4], lit 0x40],
     Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 0x24],
       Expr.builtin Op.sub [lit proofEnd, lit 4]]]]

/-- The revert arm of both guards, at the error selector it stores. -/
def pfxRevertBody (err : Nat) : Block EVM.Op :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [lit 0, Expr.builtin Op.shl [lit 224, lit err]]),
   Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])]

/-- The memory guard with the transcript pointer resolved. -/
def pfxMemCondNum (t : Nat) : Expr EVM.Op :=
  Expr.builtin Op.gt [Expr.builtin Op.mload [lit 0x40], lit t]

/-- **SIM.6 STEP 1, LANDED.** The prefix in statement-list form: the ABI guard, the SINGLE `let vk`
    (`model_flags_of_valid` makes `wrapperLocals` one element and kills the `quotientEvaluator`
    arm), the memory guard. `rfl` at a symbolic table. -/
theorem preSlice_stmts {R : Render p G₁ G₂ Gₜ} (vkAddr : U256)
    (he : R.model.embeddedVk = none) (hq : R.model.quotientExternal = none) :
    R.preSlice vkAddr 0 =
      [Stmt.cond (pfxAbiCond R.model R.consts) (pfxAbiBody R.model R.consts),
       Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)),
       Stmt.cond (pfxMemCond R.consts) (pfxMemBody R.consts)] := by
  show Inline.inlineContractConstants R.consts
      (abiGuardBlock R.model ++ wrapperLocals R.model vkAddr 0 ++ mainGuardBlock) = _
  rw [wrapperLocals, he, hq]
  simp only [Option.isNone_none, Option.isSome_none, Bool.false_eq_true, ite_true, ite_false,
    List.append_nil]
  rfl

/-- The two main-block locals, inlined: `r` at the table's `FR_MODULUS` site, `success` at the
    literal `true`. -/
theorem mainLocals_stmts {R : Render p G₁ G₂ Gₜ} :
    R.mainLocalsInlined =
      [Stmt.letDecl ["r"] (some (pfxSite "FR_MODULUS" R.consts)),
       Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))] := by
  show Inline.inlineContractConstants R.consts mainLocals = _
  rw [mainLocals]
  rfl

/-! ### The pure fragment: what the two guards read, and what nothing else can answer

  `Bridge.dialect_deterministic` needs the call relation AND the gas oracle to be functional, and
  `prefix_sim` is stated for ARBITRARY `c` and `g` - so determinism of the whole dialect is not
  available here and is not needed: the prefix contains no call and no `gas()`. What is available is
  that each builtin the guards use is a `stepOp` graph, hence single-valued, one constructor at a
  time - the same argument `dialect_deterministic` makes 80 times over. -/

variable {c : ExternalCalls} {g : ExternalGas}

theorem pfxDetCalldataload : (Bridge.Dialect c g).Deterministic Op.calldataload :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetMload : (Bridge.Dialect c g).Deterministic Op.mload :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetEq : (Bridge.Dialect c g).Deterministic Op.eq :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetAnd : (Bridge.Dialect c g).Deterministic Op.and :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetIszero : (Bridge.Dialect c g).Deterministic Op.iszero :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetSub : (Bridge.Dialect c g).Deterministic Op.sub :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetGt : (Bridge.Dialect c g).Deterministic Op.gt :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetMstore : (Bridge.Dialect c g).Deterministic Op.mstore :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetShl : (Bridge.Dialect c g).Deterministic Op.shl :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)
theorem pfxDetRevert : (Bridge.Dialect c g).Deterministic Op.revert :=
  det_of_stepOp_graph (fun _ _ _ => Iff.rfl)

/-- The step equations of the ten builtins the prefix uses, as `rfl`. `stepOp` is a function, so
    each of these is also the proof that the builtin NEVER HALTS and never answers anything else. -/
theorem pfxOkCd {st : EvmState} (p : U256) :
    (Bridge.Dialect c g).Builtin Op.calldataload [p] st
      (.ok [wordFrom st.env.calldata p.toNat] st) := rfl
theorem pfxOkMload {st : EvmState} (p : U256) :
    (Bridge.Dialect c g).Builtin Op.mload [p] st
      (.ok [loadWord st.memory p.toNat] (touchMemory st p.toNat 32)) := rfl
theorem pfxOkEq {st : EvmState} (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.eq [a, b] st (.ok [b2w (a = b)] st) := rfl
theorem pfxOkAnd {st : EvmState} (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.and [a, b] st (.ok [a &&& b] st) := rfl
theorem pfxOkIszero {st : EvmState} (a : U256) :
    (Bridge.Dialect c g).Builtin Op.iszero [a] st (.ok [b2w (a = 0)] st) := rfl
theorem pfxOkSub {st : EvmState} (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.sub [a, b] st (.ok [a - b] st) := rfl
theorem pfxOkGt {st : EvmState} (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.gt [a, b] st (.ok [b2w (b.ult a)] st) := rfl
theorem pfxOkShl {st : EvmState} (a b : U256) :
    (Bridge.Dialect c g).Builtin Op.shl [a, b] st (.ok [b <<< a.toNat] st) := rfl
theorem pfxOkMstore {st : EvmState} (p v : U256) :
    (Bridge.Dialect c g).Builtin Op.mstore [p, v] st
      (.ok [] { touchMemory st p.toNat 32 with memory := storeWord st.memory p.toNat v }) := rfl
theorem pfxOkRevert {st : EvmState} (p s : U256) :
    (Bridge.Dialect c g).Builtin Op.revert [p, s] st
      (.halt { touchMemory st p.toNat s.toNat with
        halted := some (.revert, readBytes st.memory p.toNat s.toNat) }) := rfl

/-- **THE PURE-ANSWER BUNDLE** for one expression: it evaluates, to exactly one value at exactly one
    state, and it does not halt. Bundling the three is what makes the fragment closed under
    `pfxEv1`/`pfxEv2` below, so the two guards are six applications and not two inductions. -/
structure PfxEv (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    (st : EvmState) (e : Expr EVM.Op) (u : U256) (st' : EvmState) : Prop where
  ev : EvalExpr (Bridge.Dialect c g) funs V st e (.vals [u] st')
  uniq : ∀ {v st₂}, EvalExpr (Bridge.Dialect c g) funs V st e (.vals [v] st₂) → v = u ∧ st₂ = st'
  noHalt : ∀ {st₂}, ¬ EvalExpr (Bridge.Dialect c g) funs V st e (.halt st₂)

/-- A literal: the only answer is its word, at the state it was handed. -/
theorem pfxEvLit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (n : Nat) :
    PfxEv funs V st (lit n) (BitVec.ofNat 256 n) st :=
  ⟨Step.lit, by intro v st₂ h; cases h; exact ⟨rfl, rfl⟩,
    by intro st₂ h; cases h⟩

/-- One-argument builtin, composed over a pure argument. -/
theorem pfxEv1 {op : EVM.Op} {e : Expr EVM.Op} {v₀ : U256} {st₀ : EvmState} {u₀ : U256}
    {st₂ : EvmState} {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (hdet : (Bridge.Dialect c g).Deterministic op)
    (he : PfxEv funs V st e v₀ st₀)
    (hok : (Bridge.Dialect c g).Builtin op [v₀] st₀ (.ok [u₀] st₂)) :
    PfxEv funs V st (Expr.builtin op [e]) u₀ st₂ := by
  refine ⟨Step.builtinOk (Step.argsCons Step.argsNil he.ev) hok, ?_, ?_⟩
  · intro u st' h
    cases h with
    | builtinOk hargs hbi =>
        cases hargs with
        | argsCons hnil harg =>
            cases hnil with
            | argsNil =>
                obtain ⟨rfl, rfl⟩ := he.uniq harg
                have hd := hdet _ _ _ _ hbi hok
                cases hd
                exact ⟨rfl, rfl⟩
  · intro st' h
    cases h with
    | builtinHalt hargs hbi =>
        cases hargs with
        | argsCons hnil harg =>
            cases hnil with
            | argsNil =>
                obtain ⟨rfl, rfl⟩ := he.uniq harg
                have hd := hdet _ _ _ _ hbi hok
                cases hd
    | builtinArgsHalt hargs => cases hargs with
        | argsRestHalt hh => cases hh
        | argsHeadHalt hnil hh =>
            cases hnil with
            | argsNil => exact absurd hh he.noHalt

/-- Two-argument builtin over two pure arguments. Arguments evaluate RIGHT-TO-LEFT
    (Step.argsCons takes the tail first, BigStep.lean:209), so the second hypothesis below is the
    one about the FIRST source argument. -/
theorem pfxEv2 {op : EVM.Op} {e₁ e₂ : Expr EVM.Op} {v₁ v₂ : U256} {s₁ : EvmState}
    {u₀ : U256} {st₂ : EvmState} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hdet : (Bridge.Dialect c g).Deterministic op)
    (he₂ : PfxEv funs V st e₂ v₂ s₁)
    (he₁ : PfxEv funs V s₁ e₁ v₁ st₂)
    (hok : (Bridge.Dialect c g).Builtin op [v₁, v₂] st₂ (.ok [u₀] st₂)) :
    PfxEv funs V st (Expr.builtin op [e₁, e₂]) u₀ st₂ := by
  have hargs : EvalArgs (Bridge.Dialect c g) funs V st [e₁, e₂] (.vals [v₁, v₂] st₂) :=
    Step.argsCons (Step.argsCons Step.argsNil he₂.ev) he₁.ev
  refine ⟨Step.builtinOk hargs hok, ?_, ?_⟩
  · intro u st' h
    cases h with
    | builtinOk hargs' hbi =>
        cases hargs' with
        | argsCons hrest harg₁ =>
            cases hrest with
            | argsCons hnil harg₂ =>
                cases hnil with
                | argsNil =>
                    obtain ⟨rfl, rfl⟩ := he₂.uniq harg₂
                    obtain ⟨rfl, rfl⟩ := he₁.uniq harg₁
                    have hd := hdet _ _ _ _ hbi hok
                    cases hd
                    exact ⟨rfl, rfl⟩
  · intro st' h
    cases h with
    | builtinHalt hargs' hbi =>
        cases hargs' with
        | argsCons hrest harg₁ =>
            cases hrest with
            | argsCons hnil harg₂ =>
                cases hnil with
                | argsNil =>
                    obtain ⟨rfl, rfl⟩ := he₂.uniq harg₂
                    obtain ⟨rfl, rfl⟩ := he₁.uniq harg₁
                    have hd := hdet _ _ _ _ hbi hok
                    cases hd
    | builtinArgsHalt hargs' => cases hargs' with
        | argsRestHalt hh => cases hh with
            | argsHeadHalt hnil h2 =>
                cases hnil with
                | argsNil => exact absurd h2 he₂.noHalt
            | argsRestHalt h => cases h
        | argsHeadHalt hrest hh =>
            cases hrest with
            | argsCons hnil harg₂ =>
                cases hnil with
                | argsNil =>
                    obtain ⟨rfl, rfl⟩ := he₂.uniq harg₂
                    exact absurd hh he₁.noHalt

/-- The inliner rebuilds the SAME `funDef` constructor: it rewrites the body and threads the
    parameters and return slots into the shadow list (InlineConstants.lean:322-324). -/
theorem inlineStmtStep_funDef {rec : List String → List (Stmt EVM.Op) → Inline.SRes}
    (consts : Inline.Consts) (sh : List String) (n : String) (ps rs : List String)
    (body : Block EVM.Op) :
    (Inline.inlineStmtStep rec consts sh (Stmt.funDef n ps rs body)).1 =
      Stmt.funDef n ps rs ((rec (sh ++ ps ++ rs) body).blks) := rfl

/-- `isFunDef` as a Bool, so the raw helper block can be CHECKED rather than walked. -/
def isFunDefB (s : Stmt EVM.Op) : Bool :=
  match s with
  | .funDef _ _ _ _ => true
  | _ => false

theorem isFunDefB_true {s : Stmt EVM.Op} (h : isFunDefB s = true) :
    ∃ (n : String) (ps rs : List String) (body : Block EVM.Op), s = Stmt.funDef n ps rs body := by
  cases s
  · cases h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h

/-- The thirteen definitions `R.helpers` inlines are all definitions: the eight `AssemblyHelpers`
    ones and the five `AccumulatorHelpers` ones are `yfun` literals, and none of them is a function
    of the plan view in a way that can change the head constructor. Checked by `rfl` on the Bool
    fold, which is why no `pv`-dependent `decide` is needed. -/
theorem helpers_raw_isFunDefs (pv : PlanView) :
    (GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers).all isFunDefB = true := by
  show ((GenAst.emitFail ++ GenAst.emitScalarInvAt pv ++ GenAst.emitTranscriptHelpers
      ++ GenAst.emitBatchInvertAt ++ GenAst.emitEcPairingAt pv)
      ++ (GenAst.emitLoadAccCoordShifted ++ GenAst.emitIsBlsPMinusOne
        ++ GenAst.emitCheckAccCoordPacking ++ GenAst.emitLoadAccCoord
        ++ GenAst.emitLoadAccPoint templateConstantsDefault.accumulator.limbsPerWord)
      ).all isFunDefB = true
  rfl

theorem helpers_raw_funDefs (pv : PlanView) :
    ∀ s ∈ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers,
      ∃ (n : String) (ps rs : List String) (body : Block EVM.Op), s = Stmt.funDef n ps rs body := by
  have hall := helpers_raw_isFunDefs pv
  rw [List.all_eq_true] at hall
  intro s hs
  exact isFunDefB_true (hall s hs)

/-- **THE INLINER PRESERVES "EVERY STATEMENT IS A DEFINITION".** The fold appends exactly one
    rewritten statement per input statement, and the `funDef` arm rebuilds the same constructor, so
    the shape survives at any fuel. Proved by induction over the fold with the accumulator
    generalised - the only shape `inlineScan` has. -/
theorem inlineScan_all_funDefs {fuel : Nat} {consts : Inline.Consts} {sh : List String}
    {bl : List (Stmt EVM.Op)}
    (h : ∀ s ∈ bl, ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
      s = Stmt.funDef n ps rs body) :
    ∀ t ∈ (Inline.inlineScan (fuel+1) consts sh bl).blks,
      ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
        t = Stmt.funDef n ps rs body := by
  have key : ∀ (bl : List (Stmt EVM.Op)) (acc : Inline.Acc),
      (∀ x ∈ acc.blks, ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
          x = Stmt.funDef n ps rs body) →
      (∀ s ∈ bl, ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
          s = Stmt.funDef n ps rs body) →
      ∀ t ∈ (bl.foldl (fun acc s =>
        { blks := acc.blks ++
            [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).1],
          sh := acc.sh ++ Inline.boundOf s,
          exhausted := acc.exhausted ||
            (Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).2 }) acc).blks,
        ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
          t = Stmt.funDef n ps rs body := by
    intro bl
    induction bl with
    | nil =>
        intro acc ha _ t ht
        exact ha t ht
    | cons s rest ih =>
        intro acc ha hs t ht
        have hstep : ∀ x ∈ acc.blks ++
            [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).1],
            ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
              x = Stmt.funDef n ps rs body := by
          intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact ha x hx'
          · rw [List.mem_singleton] at hx'
            subst hx'
            obtain ⟨n, ps, rs, body, rfl⟩ := hs s (List.Mem.head rest)
            exact ⟨n, ps, rs, _, by rw [inlineStmtStep_funDef]⟩
        have hrest : ∀ x ∈ rest, ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
            x = Stmt.funDef n ps rs body := fun x hx => hs x (List.Mem.tail s hx)
        have hfold : (s :: rest).foldl (fun acc s =>
              { blks := acc.blks ++
                  [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).1],
                sh := acc.sh ++ Inline.boundOf s,
                exhausted := acc.exhausted ||
                  (Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).2 }) acc
            = rest.foldl (fun acc s =>
              { blks := acc.blks ++
                  [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).1],
                sh := acc.sh ++ Inline.boundOf s,
                exhausted := acc.exhausted ||
                  (Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).2 })
              { blks := acc.blks ++
                  [(Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).1],
                sh := acc.sh ++ Inline.boundOf s,
                exhausted := acc.exhausted ||
                  (Inline.inlineStmtStep (Inline.inlineScan fuel consts) consts acc.sh s).2 } := rfl
        rw [hfold] at ht
        exact ih _ hstep hrest t ht
  show ∀ t ∈ (Inline.inlineStep (Inline.inlineScan fuel consts) consts sh bl).blks, _
  simpa only [Inline.inlineStep] using
    key bl ⟨[], sh, false⟩ (by intro x hx; simp at hx) h

/-- **`helpers_funDefs`**: SIM.6's card cited it as "proved" in a file that is not in this tree.
    Every statement of `R.helpers` is a function definition, so `funDefs_noop` applies to the whole
block - the fact SIM.6 step 3 needs for `R.helpers`. -/
theorem helpers_funDefs {R : Render p G₁ G₂ Gₜ} :
    ∀ s ∈ R.helpers, ∃ (n : String) (ps rs : List String) (body : Block EVM.Op),
      s = Stmt.funDef n ps rs body := by
  intro x hx
  have hshow : R.helpers = (Inline.inlineScan 64 R.consts []
      (GenAst.emitHelpers R.pv ++ GenAst.emitAccumulatorHelpers)).blks := rfl
  rw [hshow] at hx
  exact @inlineScan_all_funDefs 63 R.consts []
      (GenAst.emitHelpers R.pv ++ GenAst.emitAccumulatorHelpers) (helpers_raw_funDefs R.pv) x hx
/-! ### The two guards: their value, and what their revert arm does -/

/-- The word the ABI guard answers at a frame: 1 exactly when one of the two head words is wrong.
    Written as the semantics writes it, so that pfxAbiEv below is a chain of pfxEv1/pfxEv2
    applications with no arithmetic step at all. -/
def pfxAbiWord (calldata : List UInt8) (proofEnd : Nat) : U256 :=
  b2w (b2w (wordFrom calldata 4 = BitVec.ofNat 256 0x40) &&&
    b2w (wordFrom calldata 0x24 = BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4) = 0)

/-- The guard is silent exactly when both head words are the layout's. -/
theorem pfxAbiWord_eq_zero (calldata : List UInt8) (proofEnd : Nat) :
    pfxAbiWord calldata proofEnd = 0 ↔
      (wordFrom calldata 4 = BitVec.ofNat 256 0x40 ∧
        wordFrom calldata 0x24 = BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4) := by
  by_cases hA : wordFrom calldata 4 = BitVec.ofNat 256 0x40 <;>
    by_cases hB : wordFrom calldata 0x24 = BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4 <;>
      simp [pfxAbiWord, b2w, hA, hB]

/-- The word the memory guard answers: 1 exactly when the free pointer is above the render's
    transcript base. -/
def pfxMemWord (mem : Nat → UInt8) (t : Nat) : U256 :=
  b2w ((BitVec.ofNat 256 t).ult (loadWord mem 0x40))

theorem pfxMemWord_eq_zero (mem : Nat → UInt8) (t : Nat) (ht : t < 2 ^ 256) :
    pfxMemWord mem t = 0 ↔ (loadWord mem 0x40).toNat ≤ t := by
  have hmod : (BitVec.ofNat 256 t).toNat = t := Nat.mod_eq_of_lt ht
  have hlt : (BitVec.ofNat 256 t).ult (loadWord mem 0x40) =
      decide (t < (loadWord mem 0x40).toNat) := by
    rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  rw [pfxMemWord, hlt, b2w]
  by_cases hc : t < (loadWord mem 0x40).toNat <;> simp [hc] <;> omega

/-- The ABI guard's condition is pure: it answers at the frame it was handed, and nothing else
    can. Six applications, the way Blocks/VkLoading.lean builds one builtin at a time. -/
theorem pfxAbiEv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (proofEnd : Nat) :
    PfxEv funs V st (pfxAbiCondNum proofEnd) (pfxAbiWord st.env.calldata proofEnd) st := by
  have hcd4 : PfxEv funs V st (Expr.builtin Op.calldataload [lit 4])
      (wordFrom st.env.calldata 4) st :=
    pfxEv1 pfxDetCalldataload (pfxEvLit 4) (pfxOkCd (BitVec.ofNat 256 4))
  have heq1 : PfxEv funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 4], lit 0x40])
      (b2w (wordFrom st.env.calldata 4 = BitVec.ofNat 256 0x40)) st :=
    pfxEv2 pfxDetEq (pfxEvLit 0x40) hcd4 (pfxOkEq _ _)
  have hsub : PfxEv funs V st (Expr.builtin Op.sub [lit proofEnd, lit 4])
      (BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4) st :=
    pfxEv2 pfxDetSub (pfxEvLit 4) (pfxEvLit proofEnd) (pfxOkSub _ _)
  have hcd24 : PfxEv funs V st (Expr.builtin Op.calldataload [lit 0x24])
      (wordFrom st.env.calldata 0x24) st :=
    pfxEv1 pfxDetCalldataload (pfxEvLit 0x24) (pfxOkCd (BitVec.ofNat 256 0x24))
  have heq2 : PfxEv funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 0x24],
        Expr.builtin Op.sub [lit proofEnd, lit 4]])
      (b2w (wordFrom st.env.calldata 0x24 = BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4)) st :=
    pfxEv2 pfxDetEq hsub hcd24 (pfxOkEq _ _)
  have hand : PfxEv funs V st (Expr.builtin Op.and
      [Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 4], lit 0x40],
       Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit 0x24],
         Expr.builtin Op.sub [lit proofEnd, lit 4]]])
      (b2w (wordFrom st.env.calldata 4 = BitVec.ofNat 256 0x40) &&&
        b2w (wordFrom st.env.calldata 0x24 = BitVec.ofNat 256 proofEnd - BitVec.ofNat 256 4)) st :=
    pfxEv2 pfxDetAnd heq2 heq1 (pfxOkAnd _ _)
  exact pfxEv1 pfxDetIszero hand (pfxOkIszero _)

/-- The memory guard: it reads the free pointer, so the state it answers at is the state with the
    memory high-water mark touched - and ONLY that. touchMemory leaves env, memory and the halt
    record alone, which is what makes BaseInv .start survive the read. -/
theorem pfxMemEv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} (t : Nat) :
    PfxEv funs V st (pfxMemCondNum t) (pfxMemWord st.memory t) (touchMemory st 0x40 32) := by
  have hml : PfxEv funs V st (Expr.builtin Op.mload [lit 0x40])
      (loadWord st.memory 0x40) (touchMemory st 0x40 32) :=
    pfxEv1 pfxDetMload (pfxEvLit 0x40) (pfxOkMload (BitVec.ofNat 256 0x40))
  exact pfxEv2 pfxDetGt (pfxEvLit t) hml (pfxOkGt _ _)

/-- touchMemory is a high-water mark only. -/
theorem touchMemory_env (st : EvmState) (p n : Nat) : (touchMemory st p n).env = st.env := rfl
theorem touchMemory_memory (st : EvmState) (p n : Nat) :
    (touchMemory st p n).memory = st.memory := rfl
theorem touchMemory_halted (st : EvmState) (p n : Nat) :
    (touchMemory st p n).halted = st.halted := rfl

/-- Reverted at an explicit revert record. -/
theorem pfxReverted {st : EvmState} {d : List UInt8} (h : st.halted = some (.revert, d)) :
    Reverted st := by
  show revertedOf st.halted = true
  rw [h]
  rfl

/-- revert(0, 4) INVERTED as a statement step: the outcome is halt and the record is a revert.
    The payload is the four scratch bytes and is NOT named here - the post needs only that the kind
    is revert, which is what makes the lemma selector-independent. -/
theorem pfxRevertStmt {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])) V' st' o) :
    o = .halt ∧ Reverted st' := by
  have hok : (Bridge.Dialect c g).Builtin Op.revert [(0 : U256), (4 : U256)] st
      (.halt { touchMemory st 0 4 with halted := some (.revert, readBytes st.memory 0 4) }) :=
    pfxOkRevert 0 4
  have hnotok : ¬ ∃ (st₂ : EvmState),
      (Bridge.Dialect c g).Builtin Op.revert [(0 : U256), (4 : U256)] st (.ok [] st₂) := by
    rintro ⟨st₂, hu⟩
    have hd := pfxDetRevert _ _ _ _ hu hok
    cases hd

  cases h with
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hrest h0 =>
              cases hrest with
              | argsCons hnil h4 =>
                  cases hnil with
                  | argsNil =>
                      cases h0 with
                      | lit =>
                          cases h4 with
                          | lit =>
                              refine ⟨rfl, ?_⟩
                              have hd := pfxDetRevert _ _ _ _ hbi hok
                              cases hd
                              exact pfxReverted rfl
      | builtinArgsHalt hargs => cases hargs with
          | argsRestHalt hh => cases hh with
              | argsHeadHalt hn h2 => cases hn with
                  | argsNil => cases h2
              | argsRestHalt h2 => cases h2
          | argsHeadHalt hrest hh =>
              cases hrest with
              | argsCons hnil h4 =>
                  cases hnil with
                  | argsNil => cases hh
  | exprStmt hex =>
      cases hex with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hrest h0 =>
              cases hrest with
              | argsCons hnil h4 =>
                  cases hnil with
                  | argsNil =>
                      cases h0 with
                      | lit =>
                          cases h4 with
                          | lit =>
                              exfalso
                              exact hnotok ⟨st', by simpa [litValue] using hbi⟩

/-- **A BUILTIN OF THE FRAGMENT NEVER HALTS.** Every builtin the prefix uses is a stepOp graph whose
    arm answers .ok at the right arity and none at any other, so no argument values and no state make
    it halt. Stated at a fixed arity, because that is the only form stepOp can reduce. -/
theorem pfxBNoHalt1 (op : EVM.Op)
    (hop : op = Op.calldataload ∨ op = Op.mload ∨ op = Op.iszero)
    {a : U256} {s s' : EvmState} :
    ¬ (Bridge.Dialect c g).Builtin op [a] s (.halt s') := by
  intro h
  rcases hop with rfl | rfl | rfl
  all_goals
    simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin, un, rd1, rd0] at h
    cases h

theorem pfxBNoHalt2 (op : EVM.Op)
    (hop : op = Op.eq ∨ op = Op.and ∨ op = Op.sub ∨ op = Op.gt ∨ op = Op.mstore ∨ op = Op.shl)
    {a b : U256} {s s' : EvmState} :
    ¬ (Bridge.Dialect c g).Builtin op [a, b] s (.halt s') := by
  intro h
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Bridge.Dialect, builtinWithExternal, stepOp, bin, un, rd1, rd0] at h
    cases h

/-- A literal cannot halt. -/
theorem pfxLitNoHalt {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st (lit n) (.halt st') := by
  intro h
  cases h

/-- One-argument builtin over a non-halting argument: the whole thing cannot halt. -/
theorem pfxNoHalt1 {op : EVM.Op} {e : Expr EVM.Op}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (hop : ∀ {a : U256} {s s₁ : EvmState},
        ¬ (Bridge.Dialect c g).Builtin op [a] s (.halt s₁))
    (he : ∀ {s₁ s₂ : EvmState}, ¬ EvalExpr (Bridge.Dialect c g) funs V s₁ e (.halt s₂)) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op [e]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil harg =>
          cases hnil with
          | argsNil => exact hop hbi
  | builtinArgsHalt hargs => cases hargs with
      | argsRestHalt hh => cases hh
      | argsHeadHalt hnil hh =>
          cases hnil with
          | argsNil => exact he hh

/-- Two-argument builtin over two non-halting arguments. -/
theorem pfxNoHalt2 {op : EVM.Op} {e₁ e₂ : Expr EVM.Op}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (hop : ∀ {a b : U256} {s s₁ : EvmState},
        ¬ (Bridge.Dialect c g).Builtin op [a, b] s (.halt s₁))
    (he₁ : ∀ {s₁ s₂ : EvmState}, ¬ EvalExpr (Bridge.Dialect c g) funs V s₁ e₁ (.halt s₂))
    (he₂ : ∀ {s₁ s₂ : EvmState}, ¬ EvalExpr (Bridge.Dialect c g) funs V s₁ e₂ (.halt s₂)) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op [e₁, e₂]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest harg₁ =>
          cases hrest with
          | argsCons hnil harg₂ =>
              cases hnil with
              | argsNil => exact hop hbi
  | builtinArgsHalt hargs => cases hargs with
      | argsRestHalt hh => cases hh with
          | argsRestHalt h₂ => cases h₂
          | argsHeadHalt hnil h₂ =>
              cases hnil with
              | argsNil => exact he₂ h₂
      | argsHeadHalt hrest hh =>
          cases hrest with
          | argsCons hnil harg₂ =>
              cases hnil with
              | argsNil => exact he₁ hh
/-- mstore(0, ERR << 224) as a statement step: it always continues normally, whatever the selector. -/
theorem pfxMstoreStmt {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} (err : Nat)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.mstore [lit 0, Expr.builtin Op.shl [lit 224, lit err]]))
        V' st' o) : o = .normal := by
  have hopshl : Op.shl = Op.eq ∨ Op.shl = Op.and ∨ Op.shl = Op.sub ∨ Op.shl = Op.gt ∨
      Op.shl = Op.mstore ∨ Op.shl = Op.shl :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hopms : Op.mstore = Op.eq ∨ Op.mstore = Op.and ∨ Op.mstore = Op.sub ∨
      Op.mstore = Op.gt ∨ Op.mstore = Op.mstore ∨ Op.mstore = Op.shl :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hshl : ∀ {s₁ s₂ : EvmState}, ¬ EvalExpr (Bridge.Dialect c g) funs V s₁
      (Expr.builtin Op.shl [lit 224, lit err]) (.halt s₂) :=
    pfxNoHalt2 (fun {a b s s'} => pfxBNoHalt2 Op.shl hopshl (a := a) (b := b) (s := s) (s' := s'))
      (pfxLitNoHalt 224) (pfxLitNoHalt err)
  have hms : ∀ (a b : U256) (s s₁ : EvmState),
      ¬ (Bridge.Dialect c g).Builtin Op.mstore [a, b] s (.halt s₁) :=
    fun a b s s₁ => pfxBNoHalt2 Op.mstore hopms
  have hargs : ∀ {s₁ s₂ : EvmState}, ¬ EvalArgs (Bridge.Dialect c g) funs V s₁
      [lit 0, Expr.builtin Op.shl [lit 224, lit err]] (.halt s₂) := by
    intro s₁ s₂ hh
    cases hh with
    | argsRestHalt h2 => cases h2 with
        | argsRestHalt h3 => cases h3
        | argsHeadHalt hnil h3 => cases hnil with
            | argsNil => exact hshl h3
    | argsHeadHalt hnil h3 =>
        cases hnil with
        | argsCons hz hshl' => cases hz with
            | argsNil => exact pfxLitNoHalt 0 h3
  cases h with
  | exprStmt hex =>
      cases hex with
      | builtinOk _ hbi => rfl
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs' hbi =>
          cases hargs' with
          | argsCons hrest h0 =>
              cases hrest with
              | argsCons hnil h4 =>
                  cases hnil with
                  | argsNil => exact absurd hbi (hms _ _ _ _)
      | builtinArgsHalt hargs' => exact absurd hargs' hargs
/-- **THE REVERT ARM, RUN.** mstore(0, ERR << 224); revert(0, 4) halts with a revert record from
    every state, and the halt kind is revert whatever the selector was - which is what makes the two
    guards' bodies one lemma. -/
theorem pfxFailBody_run {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} (err : Nat)
    (h : ExecStmts (Bridge.Dialect c g) funs V st (pfxRevertBody err) V' st' o) :
    o = .halt ∧ Reverted st' := by
  rcases Step.stmts_cons_inv h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · have hn : (Outcome.normal : Outcome) = Outcome.normal := pfxMstoreStmt err h₁
    rcases Step.stmts_cons_inv hrest with ⟨V₂, st₂, h₂, hnil⟩ | ⟨h₂, hne₂⟩
    · exact absurd (pfxRevertStmt h₂).1 (by decide)
    · exact pfxRevertStmt h₂
  · exact absurd (pfxMstoreStmt err h₁) hne



/-! ## 3C. THE PREFIX RUN, ASSEMBLED -/

/-- The two guards with the sites and the model numerals resolved at a valid render. -/
theorem pfx_abiCond_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    pfxAbiCond R.model R.consts =
      pfxAbiCondNum R.pv.proofLayout.proofEnd := by
  have hf := pfx_model_prefix_facts hR.generated
  show Expr.builtin Op.iszero [Expr.builtin Op.and
        [Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit R.model.abiSelectorBytes],
          lit R.model.abiProofHeadOffset],
         Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit R.model.abiInstancesHeadCptr],
           Expr.builtin Op.sub [pfxSite "NUM_INSTANCE_CPTR" R.consts,
             lit R.model.abiSelectorBytes]]]] = _
  rw [hf.1, hf.2.1, hf.2.2.1,
    pfx_site_eq "NUM_INSTANCE_CPTR" R.consts R.pv.proofLayout.proofEnd
      (numInstCptr_of_valid hR)]
  rfl

theorem pfx_abiBody_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    pfxAbiBody R.model R.consts = pfxRevertBody 0x1b99e37c := by
  show [Stmt.exprStmt (Expr.builtin Op.mstore [lit 0,
          Expr.builtin Op.shl [lit 224, pfxSite "ERR_BAD_CALLDATA_SHAPE" R.consts]]),
        Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])] = _
  rw [pfx_site_eq "ERR_BAD_CALLDATA_SHAPE" R.consts 0x1b99e37c (errBadCalldata_of_valid hR)]
  rfl

theorem pfx_memCond_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    pfxMemCond R.consts = pfxMemCondNum R.pv.memory.transcriptMptr := by
  show Expr.builtin Op.gt [Expr.builtin Op.mload [lit 0x40],
    pfxSite "TRANSCRIPT_MPTR" R.consts] = _
  rw [pfx_site_eq "TRANSCRIPT_MPTR" R.consts R.pv.memory.transcriptMptr
    (transcriptMptrConst_of_valid hR)]
  rfl

theorem pfx_memBody_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    pfxMemBody R.consts = pfxRevertBody 0xc9888d23 := by
  show [Stmt.exprStmt (Expr.builtin Op.mstore [lit 0,
          Expr.builtin Op.shl [lit 224, pfxSite "ERR_MEMORY_LAYOUT_VIOLATED" R.consts]]),
        Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])] = _
  rw [pfx_site_eq "ERR_MEMORY_LAYOUT_VIOLATED" R.consts 0xc9888d23
    (errMemoryLayout_of_valid hR)]
  rfl

theorem pfx_mainLocals_of_valid {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.mainLocalsInlined =
      [Stmt.letDecl ["r"] (some (lit frModulusConstant)),
       Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))] := by
  rw [mainLocals_stmts,
    pfx_site_eq "FR_MODULUS" R.consts frModulusConstant (frModulusConst_of_valid hR)]
  rfl

/-- The wrapper-locals flag, as an equation with the model field on the left. -/
theorem h1peel {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) :
    R.model.embeddedVk = (if R.flags.separate = true then none else some R.plan.vk) :=
  (pfx_model_prefix_facts hR.generated).2.2.2.1

/-- **THE PREFIX IN STATEMENT-LIST FORM, AT A VALID RENDER** (SIM.6 step 1, fully resolved): the two
    guards with their sites and numerals, the single let vk, the hoisted helper definitions, and the
    two main locals. -/
theorem preBlock_stmts {R : Render p G₁ G₂ Gₜ} (hR : R.Valid) (vkAddr : U256) :
    R.preBlock vkAddr =
      [Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c),
       Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)),
       Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)] ++
      R.helpers ++
      [Stmt.letDecl ["r"] (some (lit frModulusConstant)),
       Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))] := by
  have h1 : R.model.embeddedVk = none := by
    rw [h1peel hR]
    rw [hR.supported.separateVk]
    exact ite_eq_left rfl
  have h2 : R.model.quotientExternal = none :=
    pfx_model_prefix_facts hR.generated |>.2.2.2.2 hR.supported.embeddedQuotient.1
  show R.preSlice vkAddr 0 ++ R.helpers ++ R.mainLocalsInlined = _
  rw [preSlice_stmts vkAddr h1 h2, pfx_abiCond_of_valid hR, pfx_abiBody_of_valid hR,
    pfx_memCond_of_valid hR, pfx_memBody_of_valid hR, pfx_mainLocals_of_valid hR]

/-- **THE g1_identity WINDOW IS ZERO.** The third clause of `Inv .start` is
    `bytesAt st (ptrAddr M.g1IdentityMptr) 128 == natToBytesBE 0 128`, and the right-hand side is NOT
    reducible: `decide` proves the equation at 64 bytes and fails at 128 with
    `maximum recursion depth has been reached`, because `Midfall.natToBytesLowFirst` is a 128-step
    `ByteArray.push` fold and the WP rules forbid raising `maxRecDepth`. So the window is proved
    equal to the all-zero array by induction on the fold instead of by computation - `go_data` is the
    fold's `data.toList` invariant, `lowFirst_zero` instantiates it at the empty accumulator, and the
    reversal is `List.reverse_replicate`. Nothing here is a hypothesis: it is a theorem of the frame's
    own `ZeroAbove` together with the D-P71 addition 3 floor `g1IdentityFloor`. -/
theorem go_data : ∀ (k : Nat) (acc : ByteArray),
    (Midfall.natToBytesLowFirst.go 0 k acc).data.toList =
      acc.data.toList ++ List.replicate k 0 := by
  intro k
  induction k with
  | zero => intro acc; simp [Midfall.natToBytesLowFirst.go]
  | succ k ih =>
      intro acc
      show (Midfall.natToBytesLowFirst.go 0 k (ByteArray.push acc 0)).data.toList = _
      rw [ih]
      have key : (ByteArray.push acc 0).data.toList = acc.data.toList ++ [0] := by
        show (acc.data.push 0).toList = acc.data.toList ++ [0]
        rw [Array.toList_push]
      rw [key]
      simp [List.replicate_succ, List.append_assoc]

theorem lowFirst_zero (n : Nat) :
    Midfall.natToBytesLowFirst 0 n = ByteArray.mk (List.replicate n 0).toArray := by
  refine ByteArray.ext ?_
  show (Midfall.natToBytesLowFirst.go 0 n ByteArray.empty).data = (List.replicate n 0).toArray
  rw [← Array.toList_inj, go_data]
  show ([] ++ List.replicate n 0) = (List.replicate n 0).toArray.toList
  simp

theorem natToBytesBE_zero128 :
    Midfall.natToBytesBE 0 128 = ByteArray.mk (List.replicate 128 0).toArray := by
  show ByteArray.mk (Midfall.natToBytesLowFirst 0 128).data.toList.reverse.toArray = _
  rw [lowFirst_zero]
  show ByteArray.mk ((ByteArray.mk ((List.replicate 128 0).toArray)).data.toList.reverse.toArray) = _
  show ByteArray.mk ((List.replicate 128 0).reverse.toArray) = _
  rw [List.reverse_replicate]

theorem bytesAt_zero_above (st : EvmState) (a : Nat)
    (h : ∀ x, 0x80 ≤ x → st.memory x = 0) (ha : 0x80 ≤ a) :
    bytesAt st a 128 = Midfall.natToBytesBE 0 128 := by
  have key : readBytes st.memory a 128 = List.replicate 128 0 := by
    show (List.range 128).map (fun i => st.memory (a + i)) = List.replicate 128 0
    apply List.eq_replicate_of_mem
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hi
      exact h (a + i) (by omega)
  show ByteArray.mk (readBytes st.memory a 128).toArray = _
  rw [key, natToBytesBE_zero128]
/-! ### The prefix run -/

/-- A let of a literal, inverted: normal outcome, state unchanged, environment extended by the zip. -/
theorem pfxLetInv {xs : List String} {l : Literal} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.letDecl xs (some (Expr.lit l))) V' st' o) :
    o = .normal ∧ st' = st ∧ V' = xs.zip [(Bridge.Dialect c g).litValue l] ++ V := by
  cases h with
  | letVal he hlen =>
      cases he with
      | lit => cases xs with
          | nil => exact absurd hlen (by simp)
          | cons y ys => cases ys with
              | cons c d => exact absurd hlen (by simp)
              | nil => exact ⟨rfl, rfl, rfl⟩
  | letHalt he => cases he

/-- The two lets of the main block, run and inverted: r at the modulus word, success at 1, the state
    untouched (both right-hand sides are literals), and no other local disturbed. -/
theorem pfx_mainLocals_run {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
        [Stmt.letDecl ["r"] (some (lit frModulusConstant)),
         Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))] V' st' o) :
    o = .normal ∧ st' = st ∧
      VEnv.get V' "r" = some (BitVec.ofNat 256 frModulusConstant) ∧
      VEnv.get V' "success" = some (1 : U256) ∧
      VEnv.get V' "vk" = VEnv.get V "vk" ∧
      VEnv.get V' "quotientEvaluator" = VEnv.get V "quotientEvaluator" := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · rcases pfxLetInv h₁ with ⟨-, rfl, rfl⟩
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest with ⟨V₂, st₂, h₂, hnil⟩ | ⟨h₂, hne₂⟩
    · rcases pfxLetInv h₂ with ⟨-, rfl, rfl⟩
      cases hnil with
      | seqNil =>
          refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
          · simp [VEnv.get, List.lookup, List.zip, Bridge.Dialect, YulSemantics.EVM.litValue]
          · simp [VEnv.get, List.lookup, List.zip, Bridge.Dialect, YulSemantics.EVM.litValue,
              YulSemantics.EVM.b2w]
          · simp [VEnv.get, List.lookup, List.zip, Bridge.Dialect, YulSemantics.EVM.litValue]
          · simp [VEnv.get, List.lookup, List.zip, Bridge.Dialect, YulSemantics.EVM.litValue]
    · rcases pfxLetInv h₂ with ⟨rfl, -, -⟩
      exact (hne₂ rfl).elim
  · rcases pfxLetInv h₁ with ⟨rfl, -, -⟩
    exact (hne rfl).elim

/-- The helpers block runs: it is a no-op on both halves, and a run of it EXISTS. -/
theorem execStmts_of_funDefs {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State} {b : Block D.Op}
    (hb : ∀ s ∈ b, ∃ (n : String) (ps rs : List String) (body : Block D.Op),
      s = Stmt.funDef n ps rs body) :
    ExecStmts D funs V st b V st .normal := by
  induction b with
  | nil => exact Step.seqNil
  | cons sd rest ih =>
      have hrest : ∀ x ∈ rest, ∃ (n : String) (ps rs : List String) (body : Block D.Op),
          x = Stmt.funDef n ps rs body := fun x hx => hb x (List.Mem.tail sd hx)
      obtain ⟨n, ps, rs, body, rfl⟩ := hb sd (List.Mem.head rest)
      exact Step.seqCons Step.funDef (ih hrest)

theorem pfx_helpers_exec {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} :
    ExecStmts (Bridge.Dialect c g) funs V st R.helpers V st .normal :=
  execStmts_of_funDefs (helpers_funDefs (R := R))

/-- The memory guard does not fire at a frame whose free pointer is at or below the table's
    transcript base, PROVIDED the base is a word-sized number: (ofNat 256 t).ult w needs
    t % 2^256 ≥ w.toNat, which fmp gives as soon as t < 2^256. -/
theorem pfxMemWord_zero_of_le {mem : Nat → UInt8} (t : Nat) (hlt : t < 2 ^ 256) (h : (loadWord mem 0x40).toNat ≤ t) :
    pfxMemWord mem t = 0 := (pfxMemWord_eq_zero mem t hlt).mpr h

/-! ### The staged boundary at `.start` -/

/-- The three frame facts `Frame` reads off the entry state are `initState` fields, so each is one
    projection of `EntryFrame.shape`. -/
theorem entryFrame_calldata {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st₀ : EvmState} (hentry : EntryFrame R W Lyt H cd st₀) :
    st₀.env.calldata = cd.data.toList := by
  obtain ⟨mem₀, aw, rfl⟩ := hentry.shape
  rfl

theorem entryFrame_keccak {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st₀ : EvmState} (hentry : EntryFrame R W Lyt H cd st₀) :
    st₀.env.keccakOf = hashOfBytes H := by
  obtain ⟨mem₀, aw, rfl⟩ := hentry.shape
  rfl

theorem entryFrame_extCode {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {vkAddr : U256} {cd : Bytes} {st₀ : EvmState} (hdep : DeploymentV2 R W H vkAddr)
    (hentry : EntryFrame R W Lyt H cd st₀) :
    st₀.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList := by
  obtain ⟨mem₀, aw, rfl⟩ := hentry.shape
  exact hdep.vkCode

/-- `Agree .start`: `leanStage .start` is `.ok witnessSnapshot` by definition and `Inv .start` for
    that snapshot IS `BaseInv .start`, so no second proof is needed. This is SIM.6 step 4's
    "`Agree .start` and `Mirror .start` are immediate", and the card's Stop-if does NOT fire. -/
theorem pfx_agree_start {R : Render p G₁ G₂ Gₜ} (H : Hash) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (h : BaseInv R .start V st) : Agree R H cd .start V st := by
  intro ms instW inst _hdec
  refine ⟨witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ), rfl, ?_⟩
  exact h
/-! ## 3D. WHAT STILL BLOCKS THE TWO ROWS -/

/- **PG-G1BEQ128 - THE ONE REMAINING FACT, MEASURED, NOT ASSUMED.** Everything the prefix walk needs is
   proved above EXCEPT one Bool. `BaseInv R .start V st` reduces (`pfx_agree_start` and the
   `InvAt` unfolding) to three clauses; two are frame facts and close. The third is `Inv`'s
   g1_identity window, and `bytesAt_zero_above` proves the WINDOW EQUALITY

       bytesAt st (ptrAddr R.pv.memory.g1IdentityMptr) 128 = Midfall.natToBytesBE 0 128

   for any memory that is zero above 0x80 (the `go_data` induction: the RHS is NOT kernel-reducible -
   `decide` proves the equation at 64 bytes and fails at 128 with `maximum recursion depth has been
   reached`, and raising maxRecDepth is forbidden by the WP rules). But `InvAt` asks for the BEq
   FORM, `(bytesAt st a 128 == natToBytesBE 0 128) = true`, and rewriting with the equality leaves

       (Midfall.natToBytesBE 0 128 == Midfall.natToBytesBE 0 128) = true

   which is not provable either: `beq_self_eq_true` needs `ReflBEq ByteArray` and no such instance is
   in scope (`failed to synthesize instance of type class ReflBEq ByteArray`), and `rfl`, `decide` and
   `simp` all fail on it - `rfl` and `decide` with the same maxRecDepth wall, because the derived
   `BEq| on `ByteArray` walks the 128-byte payload. So the row is ONE Bool away, and the missing fact
   is a BEq-reflexivity instance for `ByteArray`, not a property of the program. NOTHING WAS ADDED to
   `Render.Valid`, to `ValidV3`, to a row or to the root to buy it: the two rows stay sorried and the
   register is unchanged. The fix is a one-line instance (or a `ReflBEq ByteArray` proof) in
   `Midfall/Common/Bytes.lean`, which is not this WP's file; it is recorded here rather than worked
   around. Exact goal state, after `rw [baseCk]; simp only [InvAt, witnessSnapshot, hh, hg1, hloc]`:

       h✝ : Checkpoint.vk ≤ Checkpoint.start     -- discharged by `decide`
       ⊢ ((((((((bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len == R.pv.vk.bytes) = true ∧ ...
            ... (bytesAt st (ptrAddr M.g1IdentityMptr) 128 == natToBytesBE 0 128) = true ...

-/

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

#print axioms Midfall.LoweringV2.layout_static_of_valid
#cone_sorries Midfall.LoweringV2.layout_static_of_valid
#print axioms Midfall.LoweringV2.model_flags_of_valid
#cone_sorries Midfall.LoweringV2.model_flags_of_valid
#print axioms Midfall.LoweringV2.preBlock_stmts
#cone_sorries Midfall.LoweringV2.preBlock_stmts
#print axioms Midfall.LoweringV2.helpers_funDefs
#cone_sorries Midfall.LoweringV2.helpers_funDefs
#print axioms Midfall.LoweringV2.bytesAt_zero_above
#cone_sorries Midfall.LoweringV2.bytesAt_zero_above
#print axioms Midfall.LoweringV2.pfxAbiEv
#cone_sorries Midfall.LoweringV2.pfxAbiEv
#print axioms Midfall.LoweringV2.pfxFailBody_run
#cone_sorries Midfall.LoweringV2.pfxFailBody_run
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
