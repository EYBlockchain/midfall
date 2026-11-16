/-
  Midfall.LoweringV2.Blocks

  THE REFINABLE HALF OF THE V2 SURFACE: the per-block contract layer (original `Statements.lean`
  §6), the theorems that compose them (§7), and the two claimed theorems `entryFrame_inhabited`
  and `end_to_end`.

  This file is NOT hashed in `Frozen.sha256`, on purpose. §6 is the proof architecture WP-M0
  refines, and §7 is a bundle of sorried obligations: freezing them would freeze a hole. What
  they may not do is change a FROZEN statement - so the two headline theorems are stated here as
  the Props `EntryFrameInhabited` and `EndToEnd` of `Statements.lean` §8/§9, which are the
  original statements up to delta. Everything below is moved verbatim from `Statements.lean`
  except those two conclusion lines, which name the wrapper.

  IMPORT RULE: nothing frozen may import this file.
-/
import Midfall.LoweringV2.Statements
import Midfall.LoweringV2.Shared
import Midfall.LoweringV2.Program
import Midfall.Lowering.Snapshot
import Midfall.Lowering.Calldata
import Midfall.Assumptions.Eip2537
import Midfall.Assumptions.Codec
import Midfall.Halo2.Exec.Native

namespace Midfall.LoweringV2

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 6. Per-block contracts over the CLOSED program (PROPOSED INTERNAL SHAPE)

  §1-§5 are the FROZEN statement surface. This section is the proof architecture WP-M0 starts
  from. It may be refined (in particular the rejection side, which needs staged invariants), but
  every refinement must keep four properties, each of which v1 violated:
  (i)   blocks are `R.slice q` run in `R.scope` - slices of the CLOSED (inlined) program;
  (ii)  progress is TOTAL: a run exists, and every run is good;
  (iii) soundness covers a POISONED `success` (a failed precompile is only caught by a later
        check, e.g. at the top of FinalPairing);
  (iv)  world, keccak and local facts enter through `Frame`, never as a free hypothesis. -/

/-- Total correctness: a run exists, and every run satisfies `post`. -/
def StmtsTotal {D : YulSemantics.Dialect} [DecidableEq D.Value] (funs : FunEnv D)
    (b : Block D.Op) (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  StmtsContract funs b pre post ∧ StmtsContractAll funs b pre post

/-- What every block boundary carries besides `Inv`: the call's calldata, the frame's hash, the
    deployed VK runtime, and the two main-block locals no block assigns (`r`, `vk`). -/
structure Frame (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop where
  calldata : st.env.calldata = cd.data.toList
  keccak : st.env.keccakOf = hashOfBytes H
  vkCode : st.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList
  vkHash : H R.plan.vk.runtimeBytes = keccak256 R.plan.vk.runtimeBytes
  vkNonEmpty : R.plan.vk.runtimeBytes.size ≠ 0
  r : ∃ rv, R.consts.lookup "FR_MODULUS" = some rv ∧ VEnv.get V "r" = some (BitVec.ofNat 256 rv)
  vk : VEnv.get V "vk" = some vkAddr

/-- A clean boundary: `Inv` at checkpoint `k` for the Lean snapshot, the frame, `success = 1`. -/
def Clean (R : Render p G₁ G₂ Gₜ) (k : Checkpoint) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Inv (calls := c) (gas := g) R.E R.params k R.pv Snap V st ∧ Frame R H vkAddr cd V st ∧
    VEnv.get V "success" = some (1 : U256)

/-- A poisoned boundary: an earlier precompile failed and the check is still pending. -/
def Poisoned (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (0 : U256)

/-- How block `q` may finish when nothing failed: clean at the next checkpoint, except TraceReturn,
    which finishes by returning ABI `true`. -/
def exitOk (R : Render p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue)
  | _ => o = .normal ∧ Clean R q.pre.next Snap H vkAddr cd V' st'

/-- SOUNDNESS CONTRACT. From a clean boundary every run reverts, exits clean, or exits poisoned;
    from a poisoned boundary every run reverts or stays poisoned (so a pending failure can never be
    laundered into a return). -/
def BlockSound (R : Render p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Clean R q.pre Snap H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitOk R q Snap H vkAddr cd V' st' o ∨
        (o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ Poisoned R H vkAddr cd V' st'))

/-- PROGRESS CONTRACT, TOTAL: under the honest precompiles, from a clean boundary a run EXISTS and
    every run exits clean. (v1's `PartialProgress` asserted no existence and was vacuous on stuck
    code.) -/
def BlockProgress (R : Render p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (product : PairingProduct) (cd : Bytes) : Prop :=
  StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => Clean R q.pre Snap H vkAddr cd V st)
    (fun _ _ V' st' o => exitOk R q Snap H vkAddr cd V' st' o)

/-- The block contracts of a render at the partials satisfying `P`, for every calldata on which
    the Lean pipeline produces a snapshot. Progress is only claimed where it can hold: the proof
    is accepted by Lean (`DualMSM.check`) and the challenges avoid the completeness bad set. -/
def Render.BlockContractsAt (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (P : Partial → Prop) : Prop :=
  Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product →
  ∀ (H : Hash) (vkAddr : U256) (cd : Bytes) (ms : List (Msg (Fr p) G₁))
    (instW : Array Word256) (inst : Array (Fr p)) (Snap : Snapshot p G₁ G₂ Gₜ),
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst →
    snapshotOf R.E H R.vk inst ms none = .ok Snap →
    ∀ q : Partial, P q →
      (∀ g : ExternalGas, BlockSound R q Snap H vkAddr (permissive (callsOf product)) g cd) ∧
      (G1CodecLaws R.E.g1 → ChallengesGood R.vk Snap → DualMSM.check Snap.c.dual R.params = true →
        BlockProgress R q Snap H vkAddr product cd)

/-- PROGRAM-LEVEL REJECTION: if the Lean verifier does not accept (outside the logup-panic bad set),
    every run of the program reverts or halts. This is the half of soundness the block contracts do
    not cover (they assume a snapshot exists). WP-M0 decomposes it into STAGED per-block rejection
    contracts (the Lean state reached so far, from `snapshotOfTrace` .. `snapshotOfPcs`, and the
    stage fault each block is responsible for); this program-level form is what composition uses. -/
def Render.Rejects (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs),
    DeploymentV2 R W H vkAddr → EntryFrame R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → SoundSide R H cd → ¬ LeanAccepts R H cd →
    RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → obs.isRevertOrHalt

/-! ## 7. The theorems to prove -/

/-- The block scope does not depend on the addresses the wrapper binds (they only change `let`
    literals; `hoist` collects function definitions). OBLIGATION (WP-A2). -/
theorem hoist_prog_addr_indep (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas)
    (a b a' b' : U256) :
    hoist (Bridge.Dialect c g) (R.prog a b) = hoist (Bridge.Dialect c g) (R.prog a' b') := by
  sorry

/-- THE SIX PLAN-VIEW BLOCKS, generic in the render (WP-M1..M4): every block except the quotient
    one, whose code also depends on `R.qblocks` (GAP G3). -/
theorem blockContracts_of_valid (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) : R.BlockContractsAt product (· ≠ .quotientLin) := by
  sorry

/-- COMPOSITION (WP-M5): a valid render whose blocks satisfy their contracts and whose program
    rejects what Lean rejects satisfies the headline. Uses `emitSlices_eq`, `inline_append`,
    `hoist_prog_addr_indep`, `NoWriters` with `Bridge.Run_worldEq_of_noWriters`, and the view
    lemmas of `Bridge` (`halted_of_view_eq`, `worldEq_of_view_eq`, ...). This is a LEMMA: its two
    bundle hypotheses are discharged per deployment, and the headline that is claimed (below) has
    neither. -/
theorem lowering_equivalence_of_blocks (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hB : R.BlockContractsAt product (fun _ => True)) (hrej : R.Rejects product) :
    LoweringEquivalence R product := by
  sorry

/-! ### The claimed headline is PER DEPLOYMENT (D-P24)

  `Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon :
      LoweringEquivalence poseidonRender poseidonProduct`

  proved, with NO hypothesis, from: `poseidon_valid : poseidonRender.Valid` (computation),
  `blockContracts_of_valid` plus a per-deployment proof of the quotient block, and a
  per-deployment `Rejects` from WP-M0's staged contracts. Acceptance (PLAN-V2 §5):
  `#print axioms` on it shows no `sorryAx`. The generic `∀ R, R.Valid → LoweringEquivalence R`
  becomes provable once WP-G3 ports QRS:2000 and `Valid` gains the generator fact
  `R.qblocks = <port> R.plan` - a decidable fact, never a semantic hypothesis. -/

/-- An entry frame exists for every calldata carrying the selector, in a world that sends no
    value. OBLIGATION (WP-I2); it is what keeps `end_to_end`'s right-hand side from being vacuous. -/
theorem entryFrame_inhabited (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hcv : W.callvalue = 0)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) :
    EntryFrameInhabited R W Lyt H cd hsel hcv ht := by
  refine ⟨initState W Lyt H cd (fun _ => 0), ⟨fun _ => 0, 0, rfl⟩, ?_, ?_, hcv, hsel⟩
  · exact fun a _ => rfl
  · obtain ⟨t, ht₁, ht₂⟩ := ht
    refine ⟨t, ht₁, ?_⟩
    have h0 : (loadWord ((initState W Lyt H cd (fun _ : Nat => (0 : UInt8)))).memory 0x40).toNat = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; omega

/-- **END TO END (no accumulator).** Given the headline at this render, Lean's byte-level verifier
    accepts the compressed Rust proof iff the encoder produces calldata on which, from every entry
    frame, an honest run exists and every honest run returns ABI `true`. Derived (WP-E1) from the
    headline, the PROVED `Lowering.verifyNative_iff_msgs_codec` (move it out of `Obligations.lean`
    when retiring v1), `entryFrame_inhabited`, and the calldata round-trip lemmas. The selector and
    zero call value make the entry frame exist, so neither side is vacuous. -/
theorem end_to_end (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hEq : LoweringEquivalence R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLaws R.E.g1)
    (hcomp : R.E.g1.compressedRoundtrip)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOf R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd) :
    EndToEnd R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec hcomp inst π hn hside := by
  sorry

end Midfall.LoweringV2