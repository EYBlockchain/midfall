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
  /-- **RECON.2 step 2 - the §6 refinement "a field added to `Frame`".** The calldata size bound
      reaches EVERY row this way, and not as a free hypothesis: §6 property (iv) says world, keccak
      and local facts enter through `Frame`. Without it the vkLoading row of the staged simulation
      contract is FALSE as stated - `calldatasize` is `BitVec.ofNat 256 st.env.calldata.length`
      (`EVMExec.lean:792`) while `decodeCalldata` compares `cd.size` in `Nat`
      (`Calldata.lean:341`), so `cd ++ (2^256 zero bytes)` has the same `calldatasize`, the same
      `calldataload`/`calldatacopy` and therefore the same `Frame` as far as the program can tell,
      but is rejected by the Lean verifier. `Frame.cdSize_falsifier` in
      `Midfall/LoweringV3/Composition.lean` exhibits it. The bound is a fact about every EVM frame
      and every row reads it off `EntryFrameV3.cdSize`
      (`LoweringV3/Statements.lean:1227`), so no row has to prove it. -/
  cdSize : cd.size < 2 ^ 256

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

/-- SOUNDNESS CONTRACT. From a clean boundary every run reverts, exits clean, or - only when
    `q ≠ .traceReturn` (D-P49, S.3: at traceReturn the guard reverts, so the arm is not offered)
    exits poisoned; from a poisoned boundary every run reverts or stays poisoned, never laundered. -/
def BlockSound (R : Render p G₁ G₂ Gₜ) (q : Partial) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Clean R q.pre Snap H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitOk R q Snap H vkAddr cd V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))

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
      (G1CodecHeadlineLaws R.E.g1 → ChallengesGood R.vk Snap →
        DualMSM.check Snap.c.dual R.params = true →
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

/-! ### 7.1 The named obligations WP-M5 composes from

  `lowering_equivalence_of_blocks` is proved below from the lemmas of this section. Seven are named
  `sorry`s with pinned interfaces; the transport facts are PROVED here, so the composition itself
  contains no `sorry`. The requirements table in `docs/QUEUE.md` has one row per name.

  THE FOUR GROUPS.
  * PREFIX (`prog_slices_decomp`, `prefix_run_clean`): the closed program is the prefix, the
    helpers, the main locals and the seven slices; and the prefix run from an `EntryFrame` on
    calldata the Lean verifier accepts ends at a `Clean` boundary at `.start`.
  * GLUE (`runBody_iff_slices`): a run of the program is a prefix run followed by a run of
    `R.slices` in `R.scope`, and conversely.
  * SEQUENCING (`slices_seq_sound`, `slices_seq_progress`): the seven per-slice contracts compose to
    one contract for `R.slices`, by `StmtsContractAll.append`.
  * REJECTION + TRANSPORT (`rejects_of_not_accepts`, `noWriters_prog`, `worldEq_of_runBody`).

  WHAT THE M0.1 TABLE FORCES ON THESE STATEMENTS (docs/QUEUE.md, M0.1 RESULT).
  * The only cross-slice locals are `vk`, `r`, `success`, and all three are declared OUTSIDE every
    slice (`wrapperLocals`, `mainLocals`). That is why a prefix lemma is needed at all: no slice
    establishes its own shared locals, and `Frame` carries `vk` and `r` while `Clean`/`Poisoned`
    carry `success`.
  * `fail()` REVERTS (mstore 0x0, revert(0,4)) and does NOT set `success := 0`. So the revert arm
    and the poisoned arm of `BlockSound`'s postcondition are SEPARATE requirements, and
    `slices_seq_sound` has to keep both: 5 of the 7 slices can take the revert arm, and the
    poisoned arm is only reachable from a failed precompile.
  * `quotientLin` emits 122 of 6572 tokens and `pcs` is EMPTY at the plan level, so two of the
    seven sequenced contracts are near-vacuous. The sequencing lemmas still compose by 7
    applications of `StmtsContractAll.append`, which is why this section is cheap and the block
    contracts behind it are not: the cost of the cone is not in this file.
  * Only `lagrange` calls a looping helper (`batch_invert`), so of the seven slices six have a
    fuel-free step argument and one does not; `slices_seq_*` are stated so that the loop cost lands
    in the per-slice contracts, not in the composition. -/

/-- The statements the closed program runs before the first slice: the ABI-shape guard, the two
    wrapper locals, and the main block's memory-layout guard, constant-inlined. -/
def Render.preSlice (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256) : YulBlock :=
  Inline.inlineContractConstants R.consts
    (abiGuardBlock R.model ++ wrapperLocals R.model vkAddr qAddr ++ mainGuardBlock)

/-- `mainLocals` after constant inlining: `let r := FR_MODULUS`, `let success := true`. These are
    the two declarations the M0.1 table counts as living outside every slice. -/
def Render.mainLocalsInlined (R : Render p G₁ G₂ Gₜ) : YulBlock :=
  Inline.inlineContractConstants R.consts mainLocals

-- `Render.slices` MOVED TO `Statements.lean` section 1 (ST.3, D-P65), same text: the frozen
-- `Render.scope` now concatenates the hoisted slices, and a frozen statement may not rest on a
-- definition living in this refinable file. Every use below resolves through `Render`.

/-- **PREFIX LEMMA, STRUCTURAL HALF** (WP-M5a). The closed program IS the prefix, the hoisted
    helpers, the main locals and the seven slices in include order, and its function definitions are
    the helpers' followed by the slices' — so its hoisted scope is exactly the block scope `R.scope`.
    (ST.3 restated this conjunct: since G1.2 puts `q_program_fail` and `q_pow5` inside the
    `.quotientLin` slice the slices DO contribute definitions, and the pre-ST.3 form
    `hoist prog = hoist helpers` was FALSE at any render where the splice had landed.)

    This is the named obligation `Statements.lean:108` advertises as `hoist_prog_eq_helpers` and
    which does not exist anywhere in the tree: the second conjunct IS that missing lemma. It is what
    licenses reading a `Run` of `R.prog` as a run of `R.slices` in `R.scope`, i.e. what makes the §6
    contracts usable at all.

    COST EVIDENCE: `emitSlices_eq` is proved by one `simp` (ProgramLemmas.lean:35, no sorry). The
    missing work is pushing `Inline.inlineContractConstants` through the five `++` of `asmOf`, which
    is `inline_append` (SORRIED, ProgramLemmas.lean:27) discharged a handful of times against the
    `topBinders` side condition, plus `hoist`'s `filterMap` over a concatenation. No semantic
    content: this is a fact about the emitter. -/
theorem prog_slices_decomp (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) :
    R.prog vkAddr qAddr =
        R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ R.slices ∧
      [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = R.scope c g := by
  sorry

/-- **PREFIX LEMMA, SEMANTIC HALF** (WP-M5a). From an `EntryFrame` on calldata the Lean verifier
    accepts, the prefix run EXISTS and ends at a `Clean` boundary at `.start` — and the calldata
    decodes to a snapshot, which is the hypothesis set `BlockContractsAt` needs.

    WHY THE SNAPSHOT FACTS ARE IN THE CONCLUSION. `Render.BlockContractsAt` is stated under
    `decodeCalldata = some` / `instOfWords? = some` / `snapshotOf = .ok`, and the headline only ever
    has `LeanAccepts`. The ok-value bridge is now the PROVED
    `Snapshot.snapshotOf_prepareMsgs_ok` (D-GATE1 item 3 retired the old
    `snapshotOf_prepareMsgs` row): on a successful snapshot it turns the `prepareMsgs = .ok` that
    `LeanAccepts` carries into the same dual and, with the unfolding of `verifyMsgs`, the
    `DualMSM.check` clause that `BlockProgress` is gated on. The old row's `isOk` equality is NOT
    available as a lemma: `snapshotOf` runs `lagrangeTriple`, which `prepareMsgs` does not, so at an
    arbitrary key the two `isOk` flags can differ. This row's remaining work therefore includes
    deriving `snapshotOf = .ok` from the phase schedule / the D6 replay evidence, not from an
    `isOk` transfer. The conclusion is unchanged and no hypothesis was added; the requirements
    table still records this row as not free.

    WHY `Clean .start` IS NOT TRIVIAL. `Inv .start` is `st.halted == none && LocalsOk V &&
    bytesAt st g1IdentityMptr 128 == 0`, and `Frame` additionally asks for `VEnv.get V "vk" = some
    vkAddr` and the `FR_MODULUS` read of `r`. The first two are entry-frame and deployment facts
    (`zeroAbove`, `DeploymentV2.vkCode`); the last two are the `let vk = AUTHORIZED_VK` / `let r :=
    FR_MODULUS` statements of the prefix — the M0.1 finding that the shared locals are declared
    outside every slice. -/
theorem prefix_run_clean (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (c : ExternalCalls) (g : ExternalGas) (hacc : LeanAccepts R H cd) :
    ∃ (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
        (Snap : Snapshot p G₁ G₂ Gₜ) (V₁ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
      decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
      instOfWords? (p := p) instW = some inst ∧
      snapshotOf R.E H R.vk inst ms none = .ok Snap ∧
      DualMSM.check Snap.c.dual R.params = true ∧
      Clean R .start Snap H vkAddr cd V₁ st₁ ∧
      ExecStmts (D := Bridge.Dialect c g) (R.scope c g) [] st₀
        (R.preSlice vkAddr 0 ++ R.mainLocalsInlined) V₁ st₁ .normal := by
  sorry

/-- **GLUE** (WP-M5a): a run of the program is exactly a prefix run followed by a run of `R.slices`
    in `R.scope`, up to the observation boundary `committedState`. Both directions are needed: the
    forward one to spend a per-slice contract on a `RunBody` hypothesis, the backward one to turn
    the existence half of `StmtsTotal` into the existence half of the headline's completeness
    conjunct.

    COST EVIDENCE: `Run D prog st₀ V' st' o` unfolds to `Step D [] [] st₀ (.block prog) V' st' o`
    (BigStep.lean:366-368), `Step.block` puts `hoist D prog` on the function stack and runs the
    WHOLE statement list (BigStep.lean:225-227), and every `funDef` statement is a no-op step
    (`Step.funDef`). So the proof is: rewrite by `prog_slices_decomp`, reassociate the `ExecStmts`
    run over `++` with `Step.stmts_append_inv` (PROVED, Contracts.lean:115), and discharge the
    helper statements as `Step.funDef`. The `restore [] Vb = []` collapse is what forces a `Run`'s
    final `VEnv` to be empty, which is why the statement quantifies the intermediate `V₁` rather
    than the final one. -/
theorem runBody_iff_slices (R : Render p G₁ G₂ Gₜ) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState)
    (V₁ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState)
    (hp : ExecStmts (D := Bridge.Dialect c g) (R.scope c g) [] st₀
        (R.preSlice vkAddr 0 ++ R.mainLocalsInlined) V₁ st₁ .normal) (obs : Obs) :
    RunBody R vkAddr 0 c g st₀ obs ↔
      ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome),
        obs = ⟨committedState st₀ st', o⟩ ∧
          ExecStmts (D := Bridge.Dialect c g) (R.scope c g) V₁ st₁ R.slices V' st' o := by
  sorry

/-! #### Sequencing plumbing: the two composition facts the vendored layer lacks

  `StmtsContractAll.append` (Contracts.lean:156) composes the FORALL-RUNS half of a block
  contract over `++`. `StmtsTotal` also carries an EXISTENTIAL half (`StmtsContract`, vendor
  `Contract.lean:94`) and that layer has no `++` rule for it: `StmtsContract.cons`
  (Contract.lean:143) is over `::`, so it cannot express a multi-statement slice. The two
  lemmas below are the missing rule and the run composition it needs. Both are big-step
  plumbing with no render content in them, which is why they live here and not in a block.
-/

/-- Forward run composition over `++`: the mirror of `Step.stmts_append_inv`
    (Contracts.lean:115). A normal run of `ss₁` followed by a run of `ss₂` is a run of the
    concatenation. -/
theorem ExecStmts.append {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {ss₁ ss₂ : Block D.Op}
    {V V₁ V' : VEnv D} {st st₁ st' : D.State} {o : Outcome}
    (h₁ : ExecStmts D funs V st ss₁ V₁ st₁ .normal)
    (h₂ : ExecStmts D funs V₁ st₁ ss₂ V' st' o) :
    ExecStmts D funs V st (ss₁ ++ ss₂) V' st' o := by
  revert V st h₂
  induction ss₁ with
  | nil =>
      intro V st h₁ h₂
      cases h₁ with | seqNil => exact h₂
  | cons s rest ih =>
      intro V st h₁ h₂
      rcases Step.stmts_cons_inv h₁ with ⟨V₂, st₂, hs, hr⟩ | ⟨hs, hne⟩
      · exact Step.seqCons hs (ih hr h₂)
      · exact absurd rfl hne

/-- Existential sequencing over `++`: the mirror of `StmtsContractAll.append`. The head must
    finish `.normal` at `mid`, which is exactly what a `BlockProgress` handoff gives. -/
theorem StmtsContract.append {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {ss₁ ss₂ : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h₁ : StmtsContract funs ss₁ pre (fun _ _ V' st' o => o = .normal ∧ mid V' st'))
    (h₂ : ∀ V st, pre V st →
      StmtsContract funs ss₂ mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContract funs (ss₁ ++ ss₂) pre post := by
  intro V st hpre
  obtain ⟨V₁, st₁, o₁, hrun, hon, hmid⟩ := h₁ V st hpre
  subst hon
  obtain ⟨V', st', o, hrun', hpost⟩ := h₂ V st hpre V₁ st₁ hmid
  exact ⟨V', st', o, ExecStmts.append hrun hrun', hpost⟩

/-- At any block other than `traceReturn`, `exitOk` IS the clean handoff: the `match` of §6:85
    takes its catch-all arm, so the post is `o = .normal ∧ Clean R q.pre.next`. Read the other
    way this is the fact the sequencing chain spends at every handoff except the last. -/
theorem exitOk_of_ne {R : Render p G₁ G₂ Gₜ} {q : Partial} (hq : q ≠ .traceReturn)
    {Snap : Snapshot p G₁ G₂ Gₜ} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {c : ExternalCalls} {g : ExternalGas} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    {o : Outcome} :
    exitOk R q Snap H vkAddr cd V' st' o →
      o = .normal ∧ Clean R q.pre.next Snap H vkAddr cd V' st' := by
  cases q
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun h => h
  · exact fun _ => absurd rfl hq

/-- **PER-BLOCK SEQUENCING, SOUNDNESS HALF** (WP-M5b). Seven `BlockSound`s compose to one contract
    for the concatenation: from a `Clean` boundary at `.start`, every run of the whole slice list
    either reverts or finishes the way `traceReturn` finishes.

    THE MID PREDICATES ARE THE POINT OF THE LEMMA. `StmtsContractAll.append` needs, at each of the
    six handoffs, a `mid` that the finished block establishes AND the next block consumes.
    `BlockSound`'s post gives `Clean R k.next` (through `exitOk`), `Poisoned`, or a revert, so the
    mid at boundary `k` is `fun V st => Clean R k Snap H vkAddr cd V st ∨ Poisoned R H vkAddr cd V
    st` — expressible with the §6 shapes as they stand, with no new field. The chain is `.start` →
    `.vk` → `.transcript` → `.lagrange` → `.quotient` → `.pcs` → `.pairing`, which is
    `Partial.pre` applied to the tail of `Render.slices`'s own concatenation order.

    THE ARM THAT USED TO BLOCK THIS LEMMA IS NOW GATED AWAY (D-P49, S.3). The postcondition here
    has NO `o = .normal ∧ Poisoned` arm: after `traceReturn` there is no fall-through, because
    `traceReturn` reverts on `iszero(success)` and otherwise returns. Before the gate, §6 offered
    that arm at `.traceReturn` too — it is satisfiable on paper — so the lemma was NOT derivable
    from seven copies of `BlockSound` and S.1 proved the ceiling. §6:97 and §6:101 now gate both
    poisoned arms on `q ≠ .traceReturn`, which deletes the arm at exactly the one block that has
    no successor to hand it to. With that in place this lemma IS seven copies of `BlockSound` plus
    `StmtsContractAll.append`: no block card owes a new fact and nothing was added to
    `Frame`/`Clean`. The expressiveness lesson stands as S.1 recorded it: the hole was about a
    POST, not about a boundary predicate, so no field could ever have fixed it. -/
theorem slices_seq_sound (R : Render p G₁ G₂ Gₜ) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (c : ExternalCalls) (g : ExternalGas)
    (h7 : ∀ q : Partial, BlockSound R q Snap H vkAddr c g cd) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) R.slices
        (fun V st => Clean R .start Snap H vkAddr cd V st)
        (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
          exitOk R .traceReturn Snap H vkAddr cd V' st' o) := by
  let DD := Bridge.Dialect c g
  let funs : FunEnv DD := R.scope c g
  -- the handoff predicate at boundary k, named in the docstring: clean, or poisoned by an
  -- earlier block. Both halves are needed because a failed precompile is only caught later.
  let midAt (k : Checkpoint) : VEnv DD → EvmState → Prop :=
    fun V st => Clean R k Snap H vkAddr cd V st ∨ Poisoned R H vkAddr cd V st
  -- what the whole list must establish: the revert arm, or the way traceReturn finishes
  let FINAL : VEnv DD → EvmState → Outcome → Prop :=
    fun V' st' o => (o = .halt ∧ Reverted st') ∨ exitOk R .traceReturn Snap H vkAddr cd V' st' o
  -- the post a handoff at k must satisfy: continue clean-or-poisoned at k, or stop now
  let endAt (k : Checkpoint) : VEnv DD → EvmState → VEnv DD → EvmState → Outcome → Prop :=
    fun _ _ V' st' o => (o = .normal ∧ midAt k V' st') ∨ (o ≠ .normal ∧ FINAL V' st' o)
  -- one slice, entered at its own boundary: BlockSound's two conjuncts are read together,
  -- the clean one by §6's exitOk arm and the poisoned one by its surviving arm.
  have hand (q : Partial) (hq : q ≠ .traceReturn) :
      StmtsContractAll (D := DD) funs (R.slice q) (midAt q.pre) (endAt q.pre.next) := by
    intro V st hpre V' st' o hrun
    rcases hpre with hc | hp
    · rcases ((h7 q).1 V st hc V' st' o hrun) with ⟨rfl, hrev⟩ | hok | ⟨_, rfl, hpo⟩
      · exact Or.inr ⟨by simp, Or.inl ⟨rfl, hrev⟩⟩
      · obtain ⟨hon, hcl⟩ := exitOk_of_ne hq hok
        exact Or.inl ⟨hon, Or.inl hcl⟩
      · exact Or.inl ⟨rfl, Or.inr hpo⟩
    · rcases ((h7 q).2 V st hp V' st' o hrun) with ⟨rfl, hrev⟩ | ⟨_, rfl, hpo⟩
      · exact Or.inr ⟨by simp, Or.inl ⟨rfl, hrev⟩⟩
      · exact Or.inl ⟨rfl, Or.inr hpo⟩
  -- the terminal slice. THIS is where the D-P49 gate is spent: at .traceReturn both
  -- poisoned arms of §6:97/:101 are gated off, so the only arms offered are the two the
  -- conclusion asks for, and the impossible ones close on q ≠ .traceReturn by reflexivity.
  have hlast : StmtsContractAll (D := DD) funs (R.slice .traceReturn) (midAt .pairing)
      (fun _ _ V' st' o => FINAL V' st' o) := by
    intro V st hpre V' st' o hrun
    rcases hpre with hc | hp
    · rcases ((h7 .traceReturn).1 V st hc V' st' o hrun) with hrev | hok | ⟨hne, _, _⟩
      · exact Or.inl hrev
      · exact Or.inr hok
      · exact absurd rfl hne
    · rcases ((h7 .traceReturn).2 V st hp V' st' o hrun) with hrev | ⟨hne, _, _⟩
      · exact Or.inl hrev
      · exact absurd rfl hne
  -- two plumbing steps, used once per handoff
  have post_mono {ss : Block DD.Op} {pre : VEnv DD → EvmState → Prop}
      {P Q : VEnv DD → EvmState → VEnv DD → EvmState → Outcome → Prop}
      (h : StmtsContractAll (D := DD) funs ss pre P)
      (hPQ : ∀ V st V' st' o, P V st V' st' o → Q V st V' st' o) :
      StmtsContractAll (D := DD) funs ss pre Q :=
    fun V st hp V' st' o hrun => hPQ V st V' st' o (h V st hp V' st' o hrun)
  have lift (k k' : Checkpoint) (V st V' st' o) (h : endAt k V st V' st' o) :
      (o = .normal ∧ midAt k V' st') ∨ (o ≠ .normal ∧ endAt k' V st V' st' o) :=
    h.elim (fun hm => Or.inl hm) (fun hn => Or.inr ⟨hn.1, Or.inr ⟨hn.1, hn.2⟩⟩)
  -- the six handoffs, in Render.slices' own order: .start → .vk → .transcript → .lagrange
  -- → .quotient → .pcs → .pairing. The first is entered at Clean alone (nothing has failed
  -- yet); the rest are entered at the disjunction, which is why hand carries both arms.
  have c1 : StmtsContractAll (D := DD) funs (R.slice .vkLoading)
      (fun V st => Clean R .start Snap H vkAddr cd V st) (endAt .vk) :=
    fun V st hc => hand .vkLoading (by decide) V st (Or.inl hc)
  have c2 := StmtsContractAll.append
    (post_mono c1 (fun V st V' st' h' => lift .vk .transcript V st V' st' h'))
    (fun _ _ _ => hand .transcriptParser (by decide))
  have c3 := StmtsContractAll.append
    (post_mono c2 (fun V st V' st' h' => lift .transcript .lagrange V st V' st' h'))
    (fun _ _ _ => hand .lagrange (by decide))
  have c4 := StmtsContractAll.append
    (post_mono c3 (fun V st V' st' h' => lift .lagrange .quotient V st V' st' h'))
    (fun _ _ _ => hand .quotientLin (by decide))
  have c5 := StmtsContractAll.append
    (post_mono c4 (fun V st V' st' h' => lift .quotient .pcs V st V' st' h'))
    (fun _ _ _ => hand .pcs (by decide))
  have c6 := StmtsContractAll.append
    (post_mono c5 (fun V st V' st' h' => lift .pcs .pairing V st V' st' h'))
    (fun _ _ _ => hand .finalPairing (by decide))
  exact StmtsContractAll.append c6 (fun _ _ _ => hlast)

/-- **PER-BLOCK SEQUENCING, PROGRESS HALF** (WP-M5b): the seven `BlockProgress`es compose to a
    TOTAL contract for the concatenation — a run exists, and every run finishes the `traceReturn`
    way. Under the honest calls nothing fails, so the mid at each handoff is `Clean R k` alone and
    no `Poisoned` disjunct is needed; that is the only difference from `slices_seq_sound`.

    COST EVIDENCE, MEASURED AFTER THE PROOF (F.1): 66 lines, UNDER C.2's 90-130 estimate, and the
    file still elaborates in about two seconds with no heartbeat change. `StmtsTotal = StmtsContract
    ∧ StmtsContractAll` (Blocks.lean:49), so the proof IS the same six handoffs twice. But the
    existential half does NOT need the prefix run to exist: this statement is about `R.slices` from
    a `Clean R .start` boundary, so each link is one `BlockProgress` existence half re-read through
    `exitOk_of_ne`. Exhibiting a run of the PREFIX is `prefix_run_clean` and `runBody_iff_slices`'
    job, not this lemma's — the earlier note claiming otherwise over-costed this card. What the
    vendored layer really lacked was an `++` rule for `StmtsContract` at all (`StmtsContract.cons`,
    Contract.lean:143, is over `::`), so `StmtsContract.append` and the forward `ExecStmts.append`
    it needs are proved above. Note the hypothesis is gated on `DualMSM.check = true` inside
    `BlockContractsAt`, which is where the `.pairing` arm of `Inv` gets its decision clause. -/
theorem slices_seq_progress (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (h7 : ∀ q : Partial, BlockProgress R q Snap H vkAddr product cd) :
    StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
        (R.scope _ _) R.slices
        (fun V st => Clean R .start Snap H vkAddr cd V st)
        (fun _ _ V' st' o => exitOk R .traceReturn Snap H vkAddr cd V' st' o) := by
  let DD := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)
  let funs : FunEnv DD := R.scope _ _
  -- Under the honest calls nothing fails, so the handoff is Clean alone: no Poisoned
  -- disjunct, which is the only difference from slices_seq_sound.
  let midAt (k : Checkpoint) : VEnv DD → EvmState → Prop :=
    fun V st => Clean R k Snap H vkAddr cd V st
  let FINAL : VEnv DD → EvmState → Outcome → Prop :=
    fun V' st' o => exitOk R .traceReturn Snap H vkAddr cd V' st' o
  let endAt (k : Checkpoint) : VEnv DD → EvmState → VEnv DD → EvmState → Outcome → Prop :=
    fun _ _ V' st' o => (o = .normal ∧ midAt k V' st') ∨ (o ≠ .normal ∧ FINAL V' st' o)
  have post_mono {ss : Block DD.Op} {pre : VEnv DD → EvmState → Prop}
      {P Q : VEnv DD → EvmState → VEnv DD → EvmState → Outcome → Prop}
      (h : StmtsContractAll (D := DD) funs ss pre P)
      (hPQ : ∀ V st V' st' o, P V st V' st' o → Q V st V' st' o) :
      StmtsContractAll (D := DD) funs ss pre Q :=
    fun V st hp V' st' o hrun => hPQ V st V' st' o (h V st hp V' st' o hrun)
  have lift (k k' : Checkpoint) (V st V' st' o) (h : endAt k V st V' st' o) :
      (o = .normal ∧ midAt k V' st') ∨ (o ≠ .normal ∧ endAt k' V st V' st' o) :=
    h.elim (fun hm => Or.inl hm) (fun hn => Or.inr ⟨hn.1, Or.inr ⟨hn.1, hn.2⟩⟩)
  -- HALF 1 OF 2, EVERY RUN IS GOOD: the six handoffs over the disjunction-free mid.
  have hand (q : Partial) (hq : q ≠ .traceReturn) :
      StmtsContractAll (D := DD) funs (R.slice q) (midAt q.pre) (endAt q.pre.next) := by
    intro V st hpre V' st' o hrun
    obtain ⟨hon, hcl⟩ := exitOk_of_ne hq ((h7 q).2 V st hpre V' st' o hrun)
    exact Or.inl ⟨hon, hcl⟩
  have hlast : StmtsContractAll (D := DD) funs (R.slice .traceReturn) (midAt .pairing)
      (fun _ _ V' st' o => FINAL V' st' o) := (h7 .traceReturn).2
  have c1 : StmtsContractAll (D := DD) funs (R.slice .vkLoading) (midAt .start) (endAt .vk) :=
    hand .vkLoading (by decide)
  have c2 := StmtsContractAll.append
    (post_mono c1 (fun V st V' st' h' => lift .vk .transcript V st V' st' h'))
    (fun _ _ _ => hand .transcriptParser (by decide))
  have c3 := StmtsContractAll.append
    (post_mono c2 (fun V st V' st' h' => lift .transcript .lagrange V st V' st' h'))
    (fun _ _ _ => hand .lagrange (by decide))
  have c4 := StmtsContractAll.append
    (post_mono c3 (fun V st V' st' h' => lift .lagrange .quotient V st V' st' h'))
    (fun _ _ _ => hand .quotientLin (by decide))
  have c5 := StmtsContractAll.append
    (post_mono c4 (fun V st V' st' h' => lift .quotient .pcs V st V' st' h'))
    (fun _ _ _ => hand .pcs (by decide))
  have c6 := StmtsContractAll.append
    (post_mono c5 (fun V st V' st' h' => lift .pcs .pairing V st V' st' h'))
    (fun _ _ _ => hand .finalPairing (by decide))
  have hall := StmtsContractAll.append c6 (fun _ _ _ => hlast)
  -- HALF 2 OF 2, A RUN EXISTS. StmtsContract has no ++ rule in the vendored layer (that is
  -- why StmtsContract.append is proved above), so the existential chain is built here with
  -- the same six handoffs. Each link is the BlockProgress existence half, re-read through
  -- exitOk_of_ne; nothing about the prefix run is needed — the statement is about R.slices.
  have hex (q : Partial) (hq : q ≠ .traceReturn) :
      StmtsContract (D := DD) funs (R.slice q) (midAt q.pre)
        (fun _ _ V' st' o => o = .normal ∧ midAt q.pre.next V' st') := by
    intro V st h
    obtain ⟨V', st', o, hrun, hok⟩ := (h7 q).1 V st h
    exact ⟨V', st', o, hrun, exitOk_of_ne hq hok⟩
  have hlex : StmtsContract (D := DD) funs (R.slice .traceReturn) (midAt .pairing)
      (fun _ _ V' st' o => FINAL V' st' o) := (h7 .traceReturn).1
  have d1 : StmtsContract (D := DD) funs (R.slice .vkLoading) (midAt .start)
      (fun _ _ V' st' o => o = .normal ∧ midAt .vk V' st') := hex .vkLoading (by decide)
  have d2 := StmtsContract.append d1 (fun _ _ _ => hex .transcriptParser (by decide))
  have d3 := StmtsContract.append d2 (fun _ _ _ => hex .lagrange (by decide))
  have d4 := StmtsContract.append d3 (fun _ _ _ => hex .quotientLin (by decide))
  have d5 := StmtsContract.append d4 (fun _ _ _ => hex .pcs (by decide))
  have d6 := StmtsContract.append d5 (fun _ _ _ => hex .finalPairing (by decide))
  have hcon := StmtsContract.append d6 (fun _ _ _ => hlex)
  exact ⟨hcon, hall⟩

/-- **TRANSPORT, HYPOTHESIS HALF** (WP-M5c): the `noWritersFuel` scan is insensitive to the two
    addresses the wrapper binds. `Render.Valid.noWriters` pins `NoWriters (R.prog 0 0)` and the
    headline runs `R.prog vkAddr 0`, so `Bridge.Run_worldEq_of_noWriters` cannot be cited without
    this step. The two addresses occur only as `Stmt.letDecl ... (some (lit ...))` right-hand sides
    in `wrapperLocals` (Program.lean:105-108), and `noWritersScan` classifies ops, not literal values.
    Same cost class as `hoist_prog_addr_indep` (sorried, Blocks.lean:158). Subsumed by
    `scans_prog_addr_indep` (`LoweringV3/Statements.lean:578`, ST.12), which lands the same
    address-independence for BOTH scans and so retires this one; see `SORRY.md`. -/
theorem noWriters_prog (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (vkAddr qAddr : U256) :
    NoWriters (R.prog vkAddr qAddr) := by
  sorry

/-- **REJECTION COMPOSITION, THE HALF `Render.Rejects` DOES NOT SUPPLY** (WP-M5c).

    PREMISE GAP, FOUND BY THIS CARD. The brief says composition reuses `Render.Rejects`. It cannot
    stand alone: `Rejects` demands `SoundSide R H cd` as a hypothesis, and the THIRD conjunct of the
    frozen `LoweringEquivalence` (`LoweringV2/Statements.lean:1234-1236`) carries no `SoundSide` at
    all. So the case split in conjunct 3 has a branch — `¬ LeanAccepts` with no `SoundSide` — that
    `hrej` cannot reach, and it is named here as a separate obligation. Conjunct 1 below DOES use
    `hrej` directly, where `SoundSide` is available.

    **THE SENTENCE THIS CARD GOT WRONG, CORRECTED BY ST.5.** The text above it claimed `SoundSide` is
    "a COMPLETENESS side condition", spurious for this use, and so droppable from a rejection
    obligation. It is the opposite: `SoundSide` is what keeps the rejection direction TRUE. On the
    logup-panic bad set the contract RETURNS while the Lean verifier does not accept, so "Lean
    rejects, therefore the contract reverts" is FALSE there — and this statement, which drops
    `SoundSide` and carries no `R.Valid` either, is refutable: `rejects_of_not_accepts_contradiction`
    (`Instances/StatementsV3Falsifiers.lean:476`, F9) derives `False` from it plus ONE accepting
    calldata with a returning permissive run, at any render whatever. The landed V3 text says so
    explicitly: `RejectsV3` (`LoweringV3/Statements.lean:1413`) KEEPS `SoundSide` and gains nothing
    else. (ST.5 Guidance: "the frozen docstring calling SoundSide a completeness condition is wrong;
    do not carry it".)

    **ITS REPLACEMENT HAS LANDED (RECON.2, `61b4f5e`).** `rejectsV3_of_sims`
    (`LoweringV3/Composition.lean:192`) concludes `RejectsV3` from `ValidV3` and the staged
    simulation rows, and V3 needs no rejection lemma for conjunct 3 at all: conjunct 3 is an instance
    of `TwoOutcomes` (`conj3_of_twoOutcomes`, `LoweringV3/Statements.lean:1395`, PROVED). ST.5's
    step 1 ("add the TwoOutcomes definitions and the three sorried obligations") and step 2 ("replace
    `lowering_equivalence_of_blocks`") are therefore RECON.2's landed work and are NOT restated here:
    RECON.2's Goal is ONE composition and ONE `ValidV3` in the tree, and a second statement of any of
    the four obligations in this file is exactly the duplicate it forbids.

    **WHY ST.5 DOES NOT DELETE THIS LEMMA.** Its only proof consumer is conjunct 3's `¬ LeanAccepts`
    branch below, and that branch cannot be re-sourced from inside this file.
    `LoweringV3/Statements.lean:32` imports `Midfall.LoweringV2.Blocks`, so this module cannot import
    anything under `LoweringV3/` without a cycle: `TwoOutcomes` is unreachable from here. And the two
    copies of the exit scan (`LoweringV2/Statements.lean:464` and `LoweringV3/Statements.lean:529`,
    same text, different constants) mean `exitDiscipline_of_valid` at the V2 `Render.Valid` does not
    feed `twoOutcomes_of_scans` without a new scan-agreement proof — a fresh obligation, not a wiring.
    So the deletion goes in the same commit as the retirement of the consumer it breaks (W13), which is
    SIM.7's registered work on this composition; see the `removed by` column of `SORRY.md` for
    `Midfall.LoweringV2.rejects_of_not_accepts`. -/
theorem rejects_of_not_accepts (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hna : ¬ LeanAccepts R H cd)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs) :
    obs.isRevertOrHalt := by
  sorry

/-! #### Transport facts that are PROVED here (no new holes) -/

/-- `WorldEq` is symmetric: it is eleven component equalities. Needed because the Bridge view lemma
    consumes `WorldEq o₁.state o₂.state` in the direction `run → entry`, while `Run_worldEq_of_noWriters`
    produces `entry → run`. -/
theorem worldEq_symm {a b : EvmState} (h : WorldEq a b) : WorldEq b a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm,
    h10.symm, h11.symm⟩

/-- A revert record is a non-committing halt. -/
theorem exists_revert_of_Reverted {st : EvmState} (h : Reverted st) :
    ∃ d, st.halted = some (.revert, d) := by
  cases hst : st.halted with
  | none => exact absurd h (by simp [Reverted, revertedOf, hst])
  | some kd =>
      cases kd with
      | mk k d =>
          cases k with
          | revert => exact ⟨d, rfl⟩
          | _ => exact absurd h (by simp [Reverted, revertedOf, hst])

/-- `committedState` never changes the halt record: a committing halt keeps `st'` and a rolling-back
    one copies `st'.halted` into the rollback record. -/
theorem halted_committedState (st₀ st' : EvmState) : (committedState st₀ st').halted = st'.halted := by
  cases hst : st'.halted with
  | none => simp [committedState, hst]
  | some kd =>
      cases kd with
      | mk k d =>
          by_cases hk : k.commits
          · simp [committedState, hst, hk]
          · simp [committedState, hst, hk]

/-- `committedState` never changes the world relative to `st₀`: it either keeps `st'` (a committing
    halt, where `WorldEq` transfers) or rolls back to `st₀` itself. -/
theorem worldEq_committedState (st₀ st' : EvmState) (h : WorldEq st₀ st') :
    WorldEq st₀ (committedState st₀ st') := by
  cases hst : st'.halted with
  | none =>
      simp only [committedState, hst]
      exact h
  | some kd =>
      cases kd with
      | mk k d =>
          by_cases hk : k.commits
          · simp only [committedState, hst, hk]
            exact h
          · simp only [committedState, hst, hk]
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE NO-WRITERS TRANSPORT THE COMPOSITION CITES: `Bridge.Run_worldEq_of_noWriters` (a registered
    sorry, Bridge.lean:1221) applied to a `RunBody` hypothesis. This is the exact no-writers
    transport the soundness claim depends on — the syntactic `NoWriters` scan on the program plus
    the per-op "non-writer implies WorldEq-preserving" table the Bridge docstring records as a
    77-constructor obligation. -/
theorem worldEq_of_runBody (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (vkAddr : U256)
    (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs)
    (hobs : RunBody R vkAddr 0 c g st₀ obs) : WorldEq st₀ obs.state := by
  obtain ⟨V', st', hrun, heq⟩ := hobs
  have hw := Bridge.Run_worldEq_of_noWriters (noWriters_prog R hR vkAddr 0) hrun
  rw [heq]
  exact worldEq_committedState st₀ st' hw

/-- Returning and reverting-or-halting are exclusive. -/
theorem not_isRevertOrHalt_of_isReturn {o : Obs} (h : o.isReturn) : ¬ o.isRevertOrHalt := by
  obtain ⟨d, hd⟩ := h
  rintro ⟨k, e, hk, hcomm⟩
  rw [hk] at hd
  cases hd
  exact absurd hcomm (by decide)

/-- A reverted run's observation is a non-committing halt: `committedState` keeps the halt record. -/
theorem isRevertOrHalt_of_Reverted (st₀ st' : EvmState) (h : Reverted st') :
    (⟨committedState st₀ st', .halt⟩ : Obs).isRevertOrHalt := by
  obtain ⟨d, hd⟩ := exists_revert_of_Reverted h
  refine ⟨.revert, d, ?_, by decide⟩
  rw [halted_committedState, hd]

/-- The view transport, and the reason R-60 S6 added `selfBalance` and `extCodeHashOf` to the view:
    once the world, the halt record and the outcome agree the VIEWS agree, by the PROVED
    `Bridge.view_eq_of_worldEq_and_halt`. No determinism hypothesis is used anywhere in this file. -/
theorem obs_view_eq_returnView (obs : Obs) (st₀ : EvmState)
    (hw : WorldEq obs.state st₀) (hh : obs.state.halted = some (.ret, abiTrue))
    (ho : obs.outcome = .halt) : obs.view = returnView st₀ :=
  view_eq_of_worldEq_and_halt hw hh ho

/-- The same transport for a committed observation of a returning run. -/
theorem view_eq_returnView_of_committed (st₀ st' : EvmState)
    (hw : WorldEq st₀ (committedState st₀ st')) (hh : st'.halted = some (.ret, abiTrue)) :
    (⟨committedState st₀ st', .halt⟩ : Obs).view = returnView st₀ := by
  refine obs_view_eq_returnView ⟨committedState st₀ st', .halt⟩ st₀ (worldEq_symm hw) ?_ rfl
  rw [halted_committedState, hh]

/-- The `exitOk` arm of the last slice, read as the two facts the composition needs. -/
theorem exitOk_traceReturn_apply {c : ExternalCalls} {g : ExternalGas}
    {R : Render p G₁ G₂ Gₜ} {Snap : Snapshot p G₁ G₂ Gₜ} {H : Hash}
    {vkAddr : U256} {cd : Bytes} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : exitOk R .traceReturn Snap H vkAddr cd V' st' o) :
    o = .halt ∧ st'.halted = some (.ret, abiTrue) := by
  simpa [exitOk] using h

/-- The bytes a committed returning observation exposes. -/
theorem returnData_of_committed_ret (st₀ st' : EvmState)
    (hh : st'.halted = some (.ret, abiTrue)) :
    (⟨committedState st₀ st', .halt⟩ : Obs).returnData = abiTrue := by
  simp only [Obs.returnData, halted_committedState, hh]

/-- **TOTALITY, THE FOURTH CONJUNCT OF THE HEADLINE** (D-P64, landed by ST.4). From every entry
    frame of a deployed valid render, under the honest precompiles and any TOTAL gas oracle, a run
    of the body exists - whatever the calldata. Nothing in the frozen text before ST.4 said this,
    which is why conjuncts 1 and 3 were satisfiable by a program that gets stuck.

    OBLIGATION (ST.5, whose `TotalV3` is this statement generalised over the frame and paired with
    the other three obligations). WHAT WOULD DISCHARGE IT: the scan that the program never reaches
    a stuck state - `ExitDiscipline` plus `NoWriters` over the closed program (staging §I), which
    is ST.10's and ST.12's work. The interface is pinned here so the composition has a named hole,
    registered in SORRY.md, and not a silent one. -/
theorem bodyTotal_of_valid (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) :
    BodyTotal R product vkAddr st₀ := by
  sorry

/-- **COMPOSITION (WP-M5).** A valid render whose blocks satisfy their contracts and whose program
    rejects what Lean rejects satisfies the headline. Everything semantic is in the seven named
    obligations of §7.1 plus `bodyTotal_of_valid` above; what is proved here is the `∀`/`∃`/`∨`
    plumbing that wires them to the frozen `LoweringEquivalence`, and it contains no `sorry`.

    THE THREE COMPOSITION STEPS, in the order the brief asks for them.
    1. PREFIX: `prog_slices_decomp` + `prefix_run_clean` + `runBody_iff_slices` turn a `RunBody`
       hypothesis into a run of `R.slices` from a `Clean` boundary at `.start`, and back.
    2. SEQUENCING: `slices_seq_sound` / `slices_seq_progress` spend the seven contracts of `hB` at
       that boundary and hand back one contract for the whole slice list.
    3. REJECTION: `hrej` closes conjunct 1's `¬ LeanAccepts` branch (where `SoundSide` IS a
       hypothesis); `rejects_of_not_accepts` closes conjunct 3's, where it is not.
    TRANSPORT throughout: `worldEq_of_runBody` (citing the registered
    `Bridge.Run_worldEq_of_noWriters`) and `view_eq_returnView_of_committed` (citing the PROVED
    `Bridge.view_eq_of_worldEq_and_halt`).

    NOTE ON WHAT `hB` IS ASKED FOR: the predicate is `fun _ => True`, i.e. ALL SEVEN blocks,
    including `.quotientLin` — which is the block C.1 sorried separately as
    `poseidon_quotient_block`, and whose emitted region is 122 of 6572 tokens (M0.1). The
    composition does not get to skip it: `slices_seq_sound` chains over all seven.

    WHAT ST.4 CHANGED HERE. The headline now takes `G1CodecHeadlineLaws` (four laws) as a
    hypothesis of ALL FOUR conjuncts and conjunct 2 carries no codec premise of its own, so the
    bundle arrives once, at the top, and is what `seqProgress` feeds to the rows. That moved the
    progress gate of `BlockContractsAt` and `BlockRow` from the frozen seven to these four (ST.5
    step 3, pulled forward: four do not give seven, and the only in-tree witness at a real codec,
    `CurveSurface.g1CodecZ_laws`, sits behind the `imports_avoid` wall of
    `Tools/ConeReport.lean`). Every row on the progress half is a REGISTERED sorry, so the
    stronger demand costs no proof today - it is a harder obligation, not an easier one. Conjunct
    4 is `bodyTotal_of_valid` above, a registered sorry, not a gap in the plumbing.

    WHAT ST.5 FOUND (after RECON.2, `61b4f5e`). ST.5's step 1 and step 2 are RECON.2's landed work,
    not this file's: the four V3 obligations and the one V3 composition are
    `Midfall/LoweringV3/Composition.lean` (`twoOutcomesV3_of_valid` :178 PROVED,
    `rejectsV3_of_sims` :192, `completeV3_of_progs` :202, `totalV3_of_stages` :214, and
    `lowering_equivalenceV3_of_rows` :225 - each stated exactly ONCE, each against the single
    `ValidV3` at `LoweringV3/Statements.lean:1116`), glued by the already-proved
    `lowering_equivalenceV3_of`. Nothing of theirs is restated here: a second statement in this file
    is the duplicate RECON.2's Goal forbids, and it would look green. Step 3 is complete: no
    `G1CodecLaws` (seven-law) demand survives in this file or in `Blocks/*.lean` - the progress halves
    of `BlockContractsAt` (:128) and `BlockRow` (:988) are on `G1CodecHeadlineLaws`, and the soundness
    halves carry no codec premise, which is not a gap: `BlockSound` constrains the run, not the codec,
    so gating it would add a vacuous premise and move a registered statement hash for nothing. What
    remains of ST.5 is the deletion of `rejects_of_not_accepts` (:609), and it is BLOCKED HERE: the
    conjunct-3 branch below is its only consumer, this module cannot reach `TwoOutcomes` (import cycle,
    `LoweringV3/Statements.lean:32`), and the V2/V3 copies of `ExitDiscipline` are different constants.
    It goes in the same commit as the retirement of this composition - SIM.7 - per W13. -/
theorem lowering_equivalence_of_blocks (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hB : R.BlockContractsAt product (fun _ => True)) (hrej : R.Rejects product) :
    LoweringEquivalence R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec
  /- STEP 0. Unpack `hB` at an explicit snapshot witness: the two families of per-block contracts,
     for the permissive dialect (soundness) and the honest one (progress). -/
  have hcontracts (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
      (Snap : Snapshot p G₁ G₂ Gₜ)
      (hdec : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instW))
      (hinst : instOfWords? (p := p) instW = some inst)
      (hsnap : snapshotOf R.E H R.vk inst ms none = .ok Snap) :
      (∀ (q : Partial) (gg : ExternalGas),
          BlockSound R q Snap H vkAddr (permissive (callsOf product)) gg cd) ∧
        (∀ (q : Partial), G1CodecHeadlineLaws R.E.g1 → ChallengesGood R.vk Snap →
          DualMSM.check Snap.c.dual R.params = true → BlockProgress R q Snap H vkAddr product cd) :=
    ⟨fun q gg => (hB hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap q trivial).1 gg,
      fun q => (hB hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap q trivial).2⟩
  /- STEP 2 (SEQUENCING), specialised to this deployment: one contract for `R.slices`. -/
  have seqSound (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
      (Snap : Snapshot p G₁ G₂ Gₜ)
      (hdec : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instW))
      (hinst : instOfWords? (p := p) instW = some inst)
      (hsnap : snapshotOf R.E H R.vk inst ms none = .ok Snap) (gg : ExternalGas) :
      StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) gg) (R.scope _ _) R.slices
          (fun V st => Clean R .start Snap H vkAddr cd V st)
          (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
            exitOk R .traceReturn Snap H vkAddr cd V' st' o) :=
    fun V st hpre V' st' o hrun =>
      slices_seq_sound R Snap H vkAddr cd (permissive (callsOf product)) gg
        (fun q => ((hcontracts ms instW inst Snap hdec hinst hsnap).1 q) gg) V st hpre V' st' o hrun
  have seqProgress (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
      (Snap : Snapshot p G₁ G₂ Gₜ)
      (hdec : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instW))
      (hinst : instOfWords? (p := p) instW = some inst)
      (hsnap : snapshotOf R.E H R.vk inst ms none = .ok Snap)
      (hcodec : G1CodecHeadlineLaws R.E.g1) (hcg : ChallengesGood R.vk Snap)
      (hdual : DualMSM.check Snap.c.dual R.params = true) :
      StmtsTotal (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
          (R.scope _ _) R.slices
          (fun V st => Clean R .start Snap H vkAddr cd V st)
          (fun _ _ V' st' o => exitOk R .traceReturn Snap H vkAddr cd V' st' o) :=
    slices_seq_progress R product Snap H vkAddr cd
      (fun q => (hcontracts ms instW inst Snap hdec hinst hsnap).2 q hcodec hcg hdual)

  refine ⟨?_, ?_, ?_, bodyTotal_of_valid R product hR W Lyt H vkAddr cd st₀ hdep hentry hpc⟩
  · -- (1) SOUNDNESS: a returning run under permissive calls returns ABI `true`, and Lean accepts.
    intro gg obs hobs hret hside
    by_cases hacc : LeanAccepts R H cd
    · -- Steps 1+2: factor the run, spend the sequenced contract, read off the return.
      obtain ⟨ms, instW, inst, Snap, V₁, st₁, hdec, hinst, hsnap, hdual, hclean, hpre⟩ :=
        prefix_run_clean R product hR W Lyt H vkAddr cd st₀ hdep hentry hpc
          (permissive (callsOf product)) gg hacc
      obtain ⟨V', st', o, heq, hsl⟩ :=
        (runBody_iff_slices R vkAddr (permissive (callsOf product)) gg st₀ V₁ st₁ hpre obs).1 hobs
      rw [heq] at hret ⊢
      have hpost := seqSound ms instW inst Snap hdec hinst hsnap gg V₁ st₁ hclean V' st' o hsl
      rcases hpost with ⟨rfl, hrev⟩ | hok
      · exact absurd (isRevertOrHalt_of_Reverted st₀ st' hrev)
          (not_isRevertOrHalt_of_isReturn hret)
      · obtain ⟨ho, hh⟩ := exitOk_traceReturn_apply hok
        subst ho
        exact ⟨returnData_of_committed_ret st₀ st' hh, hacc⟩
    · -- REJECTION: `Rejects` applies here because `SoundSide` is a hypothesis of this conjunct.
      exact absurd (hrej W Lyt H vkAddr cd st₀ gg obs hdep hentry hpc hside hacc hobs)
        (not_isRevertOrHalt_of_isReturn hret)
  · -- (2) COMPLETENESS: if Lean accepts, an honest run exists and every honest run returns.
    intro hacc hcomp
    obtain ⟨ms, instW, inst, Snap, V₁, st₁, hdec, hinst, hsnap, hdual, hclean, hpre⟩ :=
      prefix_run_clean R product hR W Lyt H vkAddr cd st₀ hdep hentry hpc
        (callsOf product) (ExternalGas.ofFun fun _ => 0) hacc
    obtain ⟨hcon, hall⟩ :=
      seqProgress ms instW inst Snap hdec hinst hsnap hcodec
        (hcomp ms instW inst Snap hdec hinst hsnap) hdual
    refine ⟨?_, ?_⟩
    · obtain ⟨V', st', o, hsl, _⟩ := hcon V₁ st₁ hclean
      exact ⟨⟨committedState st₀ st', o⟩,
        (runBody_iff_slices R vkAddr (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ V₁ st₁
          hpre ⟨committedState st₀ st', o⟩).2 ⟨V', st', o, rfl, hsl⟩⟩
    · intro obs hobs
      obtain ⟨V', st', o, heq, hsl⟩ :=
        (runBody_iff_slices R vkAddr (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ V₁ st₁
          hpre obs).1 hobs
      have hpost := hall V₁ st₁ hclean V' st' o hsl
      have hw : WorldEq st₀ (committedState st₀ st') := by
        have h2 := worldEq_of_runBody R hR vkAddr (callsOf product)
          (ExternalGas.ofFun fun _ => 0) st₀ obs hobs
        rwa [heq] at h2
      obtain ⟨ho, hh⟩ := exitOk_traceReturn_apply hpost
      subst ho
      rw [heq]
      exact view_eq_returnView_of_committed st₀ st' hw hh
  · -- (3) TWO OUTCOMES: every permissive run returns ABI `true` or reverts with the world alone.
    intro gg obs hobs
    have hw : WorldEq st₀ obs.state :=
      worldEq_of_runBody R hR vkAddr (permissive (callsOf product)) gg st₀ obs hobs
    by_cases hacc : LeanAccepts R H cd
    · obtain ⟨ms, instW, inst, Snap, V₁, st₁, hdec, hinst, hsnap, hdual, hclean, hpre⟩ :=
        prefix_run_clean R product hR W Lyt H vkAddr cd st₀ hdep hentry hpc
          (permissive (callsOf product)) gg hacc
      obtain ⟨V', st', o, heq, hsl⟩ :=
        (runBody_iff_slices R vkAddr (permissive (callsOf product)) gg st₀ V₁ st₁ hpre obs).1 hobs
      rw [heq] at hw ⊢
      have hpost := seqSound ms instW inst Snap hdec hinst hsnap gg V₁ st₁ hclean V' st' o hsl
      rcases hpost with ⟨rfl, hrev⟩ | hok
      · right
        exact ⟨isRevertOrHalt_of_Reverted st₀ st' hrev, hw⟩
      · left
        obtain ⟨ho, hh⟩ := exitOk_traceReturn_apply hok
        subst ho
        exact view_eq_returnView_of_committed st₀ st' hw hh
    · right
      exact ⟨rejects_of_not_accepts R product W Lyt H vkAddr cd st₀ gg obs hdep hentry hpc hacc hobs,
        hw⟩

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
    value, whose length is a word. OBLIGATION (WP-I2); it is what keeps `end_to_end`'s right-hand
    side from being vacuous. The extra premise `hcd` is D-P64/ST.4 (`EntryFrame.cdSize`); every
    EVM frame satisfies it, and `Instances/StatementsV3Falsifiers.lean` F3 is the exhibit that
    without it the frame admits a calldata the Lean verifier cannot accept. -/
theorem entryFrame_inhabited (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hcv : W.callvalue = 0)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t)
    (hcd : cd.size < 2 ^ 256) :
    EntryFrameInhabited R W Lyt H cd hsel hcv ht hcd := by
  refine ⟨initState W Lyt H cd (fun _ => 0), ⟨fun _ => 0, 0, rfl⟩, ?_, ?_, hcv, hsel, hcd⟩
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
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOf R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd) :
    EndToEnd R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hside := by
  sorry

/-! ### 7.0 M.1's reduction: the hinge is SIX ROWS, and here is their shape

  M.1 read the composition before proving anything. `hB : R.BlockContractsAt product (fun _ => True)`
  is used at EXACTLY ONE place, Blocks.lean:509-510, where it is applied at a BOUND `q` with
  `trivial`; the two lemmas that receive the result are `slices_seq_sound` (:307) and
  `slices_seq_progress` (:325), whose hypotheses are `h7 : ∀ q : Partial, BlockSound R q ...` and
  `∀ q : Partial, BlockProgress R q ...`. So the headline consumes all SEVEN `q`, and the only `q` it
  names literally is `.traceReturn` (in the two sequencing CONCLUSIONS, through `exitOk`) together
  with `.start` as the shared pre. Two consequences are recorded below as code, not prose.

  * NARROWING the hinge TO A PROPER SUBSET MOVES NOTHING. The predicate is not where the cost sits:
    `Render.slices` (Statements.lean, section 1) concatenates seven slices, so a sequencing lemma over `R.slices` cannot be
    handed a partial function, and any `BlockContractsAt P` with `P` smaller than `(· ≠ .quotientLin)` does
    not even reach C.1's glue `poseidon_block_contracts` (`Instances/PoseidonV2.lean:229`), which needs
    `(· ≠ .quotientLin)` to pair with the quotient row. The hinge contributes ONE sorry to the headline cone
    however many rows it covers, so a partial M.1 cannot reduce
    `cone_sorries lowering_equivalence_poseidon` (11) by even one.
  * THE HINGE IS SIX INDEPENDENT ROWS, one per `q ≠ .quotientLin`, each of the shape `BlockRow` below and
    nothing more. `blockContracts_of_valid_of_rows` is the honest decomposition and it is SORRY-FREE: the
    whole remaining cost of M.1 is visible as six named hypotheses, FOUR of which no card has ever
    proved (`vkLoading`, `transcriptParser`, `lagrange`, `pcs`) and two of which exist but carry a
    render hypothesis that `Valid` does not supply (`trRetMptr`, `fpG2Slots`).

  WHY THE ROWS CANNOT BE CITED FROM THIS FILE. `Blocks/TraceReturn.lean:68` and
  `Blocks/FinalPairing.lean:117` both `import Midfall.LoweringV2.Blocks`, so the two proved rows are
  DOWNSTREAM of this file. The composition that consumes them has to live in a module that imports
  all three: `Blocks/Compose.lean`. -/

/-- **THE SHAPE OF ONE PER-BLOCK ROW.** `BlockRow R product q` is what
    `Render.BlockContractsAt product P` asks for at a single `q` with `P q` proved: the same two
    families as §6:118-127, with `Eip2537.Holds` CARRIED (a row may need it — `ec_pairing_contract`
    does) and `R.Valid` CARRIED (FP.0's row needs it). A block card that produces a
    `BlockRow R product q` is by construction usable by M.1; nothing else is asked of it. -/
def BlockRow (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (q : Partial) : Prop :=
  (R.Valid) →
  ∀ (_hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (Snap : Snapshot p G₁ G₂ Gₜ),
    decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) →
    instOfWords? (p := p) instW = some inst →
    snapshotOf R.E H R.vk inst ms none = .ok Snap →
    (∀ g : ExternalGas, BlockSound R q Snap H vkAddr (permissive (callsOf product)) g cd) ∧
    (G1CodecHeadlineLaws R.E.g1 → ChallengesGood R.vk Snap →
      DualMSM.check Snap.c.dual R.params = true →
      BlockProgress R q Snap H vkAddr product cd)

/-- Rows to `BlockContractsAt`: re-association only, no content, no `sorry`. -/
theorem blockContractsAt_of_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (P : Partial → Prop)
    (hrows : ∀ q : Partial, P q → BlockRow R product q) :
    R.BlockContractsAt product P := by
  intro hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap q hP
  exact hrows q hP hR hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap

/-- **M.1 AS SIX CARDS, NOT ONE.** The hinge is exactly these six rows: this lemma is sorry-free, so
    `blockContracts_of_valid` closes the moment the six are supplied and cannot close before the four that
    do not exist are written. Note what is NOT here: no row for `.quotientLin` (GAP G3, C.1's separate
    `poseidon_quotient_block`), and neither `fpG2Slots` nor `trRetMptr` discharged — those two render
    facts are the price of the two rows that do exist. -/
theorem blockContracts_of_valid_of_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid)
    (hvk : BlockRow R product .vkLoading)
    (hparser : BlockRow R product .transcriptParser)
    (hlag : BlockRow R product .lagrange)
    (hpcs : BlockRow R product .pcs)
    (hfp : BlockRow R product .finalPairing)
    (hret : BlockRow R product .traceReturn) :
    R.BlockContractsAt product (· ≠ .quotientLin) :=
  blockContractsAt_of_rows R product hR (· ≠ .quotientLin) fun q hq => by
    cases q
    · exact hvk
    · exact hparser
    · exact hlag
    · exact absurd rfl hq
    · exact hpcs
    · exact hfp
    · exact hret

end Midfall.LoweringV2