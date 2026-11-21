/-
  Midfall.LoweringV3.Totality

  PL.H0 step 3(c) - **OBLIGATION 4 AS ITS OWN TREE.** `totalV3_of_stages` (RECON.2,
  Composition.lean) is DELETED here: `BodyTotal` asks for a run at EVERY calldata, while
  `ProgRowsV3` assumes `LeanAccepts`, so the sequenced progress rows cannot supply conjunct 4 at a
  REJECTING calldata. Confirmed by unfolding `TotalV3`/`BodyTotal` (Statements.lean:1432, :1318):
  the hypothesis a row needs is not derivable from the hypothesis the obligation quantifies over.
  So totality is ported from the evidence instead - `GeneratorRows.lean` section 10 - as
  `totalV3_correct`, proved from FOUR named leaves and nothing else.

  THE FOUR LEAVES (owners TOT.1, TOT.1.a):
    * `gasFree_of_valid`      - the program executes no `gas()` (decidable scan);
    * `runBody_gas_oblivious` - a gas-free program has the same runs under every gas oracle;
    * `block_live`            - per block, a run exists from a boundary a run can actually be at;
    * `prefix_live`           - the same for the prefix.
  `live_append`, `slices_live`, `stmts_append_stop` and `totalV3_correct` itself are PROVED glue.

  D-P71: every statement here is generic in the render and carries no fixture. The evidence's
  `hR : R.Valid` is read as `ValidV3 R` and its `SimPins R` as `G1CodecHeadlineLaws` - the same
  dissolution RECON.2 applied to the row bundles.
-/
import Midfall.LoweringV3.Statements
import Midfall.LoweringV3.PrefixV3
import Midfall.LoweringV2.Stages
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done
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

/-! ## 1. The `gas()` scan: a program that never asks for gas has the same runs under any oracle -/

/-- The scan that replaces TOT.1's "decidable scan of the literal program": no `gas()` anywhere,
    function bodies included. Structural in the fuel, like `Bridge.noWritersScan`, so `decide`
    reduces it. Ported verbatim from the evidence (`GeneratorRows.lean:1215`). -/
def gasFreeScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !(op == EVM.Op.gas) && gasFreeScan n (.es args)
    | .e (.call _ args) => gasFreeScan n (.es args)
    | .es [] => true
    | .es (e :: rest) => gasFreeScan n (.e e) && gasFreeScan n (.es rest)
    | .s (.block body) => gasFreeScan n (.b body)
    | .s (.funDef _ _ _ body) => gasFreeScan n (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => gasFreeScan n (.e e)
    | .s (.assign _ e) => gasFreeScan n (.e e)
    | .s (.cond c body) => gasFreeScan n (.e c) && gasFreeScan n (.b body)
    | .s (.switch c cases dflt) =>
        gasFreeScan n (.e c) && gasFreeScan n (.cs cases) &&
          (match dflt with | none => true | some d => gasFreeScan n (.b d))
    | .s (.forLoop init c post body) =>
        gasFreeScan n (.b init) && gasFreeScan n (.e c) &&
          gasFreeScan n (.b post) && gasFreeScan n (.b body)
    | .s (.exprStmt e) => gasFreeScan n (.e e)
    | .s .break => true
    | .s .continue => true
    | .s .leave => true
    | .b [] => true
    | .b (s :: ss) => gasFreeScan n (.s s) && gasFreeScan n (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => gasFreeScan n (.b b) && gasFreeScan n (.cs rest)

/-- A block executes no `gas()`. -/
def GasFree (b : Block EVM.Op) : Prop := ∃ n, gasFreeScan n (.b b) = true

/-- **NON-VACUITY OF THE SCAN (W12 falsifier for `gasFree_of_valid`).** The scan is not the constant
    `true`: it refuses a `gas()` and accepts a `msize()`, both PROVED by `decide` at fuel 20 with
    no render content. Ported from the evidence (`GeneratorRows.lean:1249`). -/
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.gas []])]) = false := by decide

/-- The accepting arm of the same pair: a builtin that is not `gas()` passes the scan. -/
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.msize []])]) = true := by decide

/-- **LEAF (TOT.1): THE PROGRAM OF A VALID RENDER EXECUTES NO `gas()`.** PREMISE GAP PG-GAS in the
    evidence: `SupportedV2` excludes the three features that print `gas()`, but no clause says the
    program is free of it. Owner: TOT.1 (WP A12). WITNESS: the named gap
    `gap_lowering_correct_witness_unexhibited` - `ValidV3` has no inhabitant the tree can name until
    WP B4 (D-P75 item 5). FALSIFIER: the two `example`s above. -/
theorem gasFree_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (vkAddr : U256) :
    GasFree (R.prog vkAddr 0) := by
  sorry

/-- **LEAF (TOT.1.a): A GAS-FREE PROGRAM HAS THE SAME RUNS UNDER EVERY GAS ORACLE.** One `Step`
    induction in the shape of `Bridge.Run_worldEq_of_noWriters`; generic in the block. Owner:
    TOT.1.a (WP A12). WITNESS: `gap_lowering_correct_witness_unexhibited`. FALSIFIER:
    `mid_start_not_vacuous` (Stages.lean:672, PROVED) - the boundary the run starts from is not
    `True`, so the runs compared are runs of this program and not of an arbitrary one. -/
theorem runBody_gas_oblivious (R : Render p G₁ G₂ Gₜ) (vkAddr : U256)
    (hgas : GasFree (R.prog vkAddr 0)) (c : ExternalCalls) (g g' : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (h : RunBody R vkAddr 0 c g st₀ obs) :
    RunBody R vkAddr 0 c g' st₀ obs := by
  sorry

/-! ## 2. Liveness: a run EXISTS and either continues at the next boundary or stops -/

section Live

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- A run that stops early is a run of any extension. PROVED (evidence `GeneratorRows.lean:1277`). -/
theorem stmts_append_stop {funs : FunEnv D} {a b : Block D.Op} :
    ∀ {V : VEnv D} {st : D.State} {V' : VEnv D} {st' : D.State} {o : Outcome},
      ExecStmts D funs V st a V' st' o → o ≠ .normal →
        ExecStmts D funs V st (a ++ b) V' st' o := by
  induction a with
  | nil =>
      intro V st V' st' o h hne
      cases h
      exact absurd rfl hne
  | cons s rest ih =>
      intro V st V' st' o h hne
      cases h with
      | seqCons hs hrest => exact Step.seqCons hs (ih hrest hne)
      | seqStop hs hne' => exact Step.seqStop hs hne'

/-- A run exists, and it ends normally at `mid` or stops. -/
def LiveTo (funs : FunEnv D) (b : Block D.Op) (pre mid : VEnv D → D.State → Prop) : Prop :=
  StmtsContract funs b pre (fun _ _ V' st' o => (o = .normal ∧ mid V' st') ∨ o ≠ .normal)

/-- Liveness composes. PROVED (evidence `GeneratorRows.lean:1297`), with the tree's
    `ExecStmts.append` in place of the evidence's `stmts_append_run`. -/
theorem live_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid mid' : VEnv D → D.State → Prop}
    (ha : LiveTo funs a pre mid) (hb : LiveTo funs b mid mid') :
    LiveTo funs (a ++ b) pre mid' := by
  intro V st hpre
  obtain ⟨V₁, st₁, o₁, h₁, hpost⟩ := ha V st hpre
  rcases hpost with ⟨ho, hmid⟩ | hne
  · subst ho
    obtain ⟨V', st', o, h₂, hpost₂⟩ := hb V₁ st₁ hmid
    exact ⟨V', st', o, ExecStmts.append h₁ h₂, hpost₂⟩
  · exact ⟨V₁, st₁, o₁, stmts_append_stop h₁ hne, Or.inr hne⟩

end Live

/-- The boundary a run can be at: clean up to `.quotient`, possibly poisoned from `.pcs` on.
    Ported verbatim (`GeneratorRows.lean:1316`). -/
def LivePre (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  match k with
  | .pcs | .pairing => Mid R H vkAddr cd k V st
  | _ => StageInv R H vkAddr cd k V st

/-- One block is live under the honest precompiles. -/
def BlockLive (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => LivePre R H vkAddr cd q.pre V st)
    (fun V st => LivePre R H vkAddr cd q.pre.next V st)

/-- **LEAF (TOT.1): PER-BLOCK EXISTENCE, FOR EVERY RENDER.** Leaves TOT.1.b-h, one per block: the
    existence form of the loop rule (GEN.3) at each loop, of each helper summary, the honest relation
    answering at the four precompile addresses, and the block's all-runs row to classify the
    exhibited run. Owner: TOT.1 (WP A12). WITNESS: `gap_lowering_correct_witness_unexhibited`.
    FALSIFIER: `mid_start_not_vacuous` (Stages.lean:672, PROVED). -/
theorem block_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hcodec : G1CodecHeadlineLaws R.E.g1)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (q : Partial) : BlockLive R q H vkAddr product cd := by
  sorry

/-! ### 2b. THE REVERT RUNS THE PREFIX LEAVES TOT.1 NEEDS

`pfxFailBody_run` (Stages.lean:1505) classifies a run of the guard body; it does not construct one.
The two constructions below are the missing existence half, built from the same `pfxOk*` step
equations the classification uses. Together with `prefix_prog_core` (the both-guards-silent case,
PROVED) they cover all three cases of the prefix: ABI guard fires, memory guard fires, or both are
silent. -/

/-- The guard body `mstore(0, shl(224, err)); revert(0, 4)` HAS a run: two `Step` constructors and
    the pure builtins. Proved, no `wp_run`, no fuel. -/
theorem pfxRevertBody_exists {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    (err : Nat) (st : EvmState) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st (pfxRevertBody err) V' st' .halt := by
  let shlE : Expr EVM.Op := Expr.builtin Op.shl [lit 224, lit err]
  let stM : EvmState :=
    { touchMemory st 0 32 with memory := storeWord st.memory 0 (BitVec.ofNat 256 err <<< 224) }
  let stR : EvmState :=
    { touchMemory stM 0 4 with halted := some (.revert, readBytes stM.memory 0 4) }
  have hShl : PfxEv funs V st shlE
      (BitVec.ofNat 256 err <<< 224) st := by
    exact pfxEv2 pfxDetShl (pfxEvLit err) (pfxEvLit 224)
      (pfxOkShl (BitVec.ofNat 256 224) (BitVec.ofNat 256 err))
  have hMstore : Step (Bridge.Dialect c g) funs V st
      (.expr (Expr.builtin Op.mstore [lit 0, shlE])) (.eres (.vals [] stM)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [lit 0, shlE])
      (argvals := [(0 : U256), (BitVec.ofNat 256 err <<< 224)]) (st1 := st) (rets := []) (st2 := stM) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [shlE])
        (restvals := [BitVec.ofNat 256 err <<< 224])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g)) hShl.ev)
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.mstore [0, BitVec.ofNat 256 err <<< 224] st (.ok [] stM)
      rfl
  have hMstoreStmt : Step (Bridge.Dialect c g) funs V st
      (.stmt (.exprStmt (Expr.builtin Op.mstore [lit 0, shlE]))) (.sres V stM .normal) :=
    Step.exprStmt hMstore
  have hRevert : Step (Bridge.Dialect c g) funs V stM
      (.expr (Expr.builtin Op.revert [lit 0, lit 4])) (.eres (.halt stR)) := by
    refine Step.builtinHalt (D := Bridge.Dialect c g) (args := [lit 0, lit 4])
      (argvals := [(0 : U256), (4 : U256)]) (st1 := stM) (st2 := stR) ?_ ?_
    · exact Step.argsCons (D := Bridge.Dialect c g) (rest := [lit 4]) (restvals := [(4 : U256)])
        (Step.argsCons (D := Bridge.Dialect c g) (rest := [])
          (Step.argsNil (D := Bridge.Dialect c g))
          (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 4)))
        (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0))
    · show (Bridge.Dialect c g).Builtin Op.revert [0, 4] stM (.halt stR)
      rfl
  have hRevertStmt : Step (Bridge.Dialect c g) funs V stM
      (.stmt (.exprStmt (Expr.builtin Op.revert [lit 0, lit 4]))) (.sres V stR .halt) :=
    Step.exprStmtHalt hRevert
  refine ⟨V, stR, ?_⟩
  show Step (Bridge.Dialect c g) funs V st
      (.stmts (pfxRevertBody err)) (.sres V stR .halt)
  simp only [pfxRevertBody, shlE, stM, stR] at hMstoreStmt hRevertStmt ⊢
  exact Step.seqCons hMstoreStmt (Step.seqStop hRevertStmt (by decide))

theorem pfxHead_eq (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) :
    pfxHead R vkAddr =
      [Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c),
       Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)),
       Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)] := rfl

/-- THE ABI GUARD FIRES: the head has a run that halts at the revert. -/
theorem pfxHead_abi_revert_exists {R : Render p G₁ G₂ Gₜ} {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {vkAddr : U256} {st₀ : EvmState}
    (h : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd ≠ 0) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st₀ (pfxHead R vkAddr) V' st' .halt := by
  obtain ⟨Vb, stR, hbody⟩ := pfxRevertBody_exists (c := c) (g := g)
    (hoist (Bridge.Dialect c g) (pfxRevertBody 0x1b99e37c) :: funs) V 0x1b99e37c st₀
  have hcond : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c)))
      (.sres (restore V Vb) stR .halt) :=
    Step.ifTrue (pfxAbiEv R.pv.proofLayout.proofEnd).ev h
      (Step.block (D := Bridge.Dialect c g) hbody)
  refine ⟨restore V Vb, stR, ?_⟩
  rw [pfxHead_eq]
  exact Step.seqStop hcond (by decide)

/-- THE MEMORY GUARD FIRES: the ABI guard is silent, the `let vk` runs, then the second guard halts. -/
theorem pfxHead_mem_revert_exists {R : Render p G₁ G₂ Gₜ} {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {vkAddr : U256} {st₀ : EvmState}
    (ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0)
    (hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr ≠ 0) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st₀ (pfxHead R vkAddr) V' st' .halt := by
  have h1 : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c)))
      (.sres V st₀ .normal) :=
    Step.ifFalse (pfxAbiEv R.pv.proofLayout.proofEnd).ev ha
  have h2 : Step (Bridge.Dialect c g) funs V st₀
      (.stmt (Stmt.letDecl ["vk"] (some (lit vkAddr.toNat))))
      (.sres (List.zip ["vk"] [vkAddr] ++ V) st₀ .normal) := by
    have hh := Step.letVal (D := Bridge.Dialect c g) (funs := funs) (V := V) (st := st₀)
      (vars := ["vk"]) (e := lit vkAddr.toNat)
      (vals := [(Bridge.Dialect c g).litValue (Literal.number vkAddr.toNat)])
      (Step.lit (D := Bridge.Dialect c g) (V := V) (st := st₀)) (by simp)
    rw [litValue_number vkAddr] at hh
    exact hh
  obtain ⟨Vb, stR, hbody⟩ :=
    pfxRevertBody_exists (c := c) (g := g)
      (hoist (Bridge.Dialect c g) (pfxRevertBody 0xc9888d23) :: funs)
      (List.zip ["vk"] [vkAddr] ++ V) 0xc9888d23 (touchMemory st₀ 0x40 32)
  have h3 : Step (Bridge.Dialect c g) funs (List.zip ["vk"] [vkAddr] ++ V) st₀
      (.stmt (Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)))
      (.sres (restore (List.zip ["vk"] [vkAddr] ++ V) Vb) stR .halt) :=
    Step.ifTrue (pfxMemEv (funs := funs) (V := List.zip ["vk"] [vkAddr] ++ V)
      R.pv.memory.transcriptMptr).ev hm
      (Step.block (D := Bridge.Dialect c g) hbody)
  refine ⟨restore (List.zip ["vk"] [vkAddr] ++ V) Vb, stR, ?_⟩
  rw [pfxHead_eq]
  exact Step.seqCons h1 (Step.seqCons h2 (Step.seqStop h3 (by decide)))

/-- **LEAF (TOT.1 with SIM.6): PREFIX EXISTENCE.** The ABI guard and the memory guard each revert or
    pass, and both are runs. Owner: TOT.1 (WP A12) with SIM.6 (WP A1). WITNESS:
    `gap_lowering_correct_witness_unexhibited`. FALSIFIER: `stageInv_start_not_vacuous`
    (Stages.lean:663, PROVED). -/
theorem prefix_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrameV3 R W Lyt H cd st₀) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st) := by
  intro V st hpre
  obtain ⟨hV, hst⟩ := hpre
  subst V
  subst st
  have hf := pfxFacts_of_validV3 hR
  by_cases ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0
  · by_cases hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0
    · -- both guards silent: the PROVED progress core supplies the normal run at `.start`
      have htotal := prefix_prog_core (c := callsOf product)
        (g := ExternalGas.ofFun fun _ => 0) hf hdep hentry.toV2 ha hm
      obtain ⟨V', st', o, hrun, hpost⟩ := htotal.1 [] st₀ ⟨rfl, rfl⟩
      exact ⟨V', st', o, hrun, Or.inl ⟨hpost.1, by simpa [LivePre] using hpost.2⟩⟩
    · -- the memory guard fires
      obtain ⟨V', st', hrun⟩ :=
        pfxHead_mem_revert_exists (c := callsOf product)
          (g := ExternalGas.ofFun fun _ => 0) (R.scope _ _) [] (vkAddr := vkAddr) ha hm
      rw [preBlock_of_facts hf vkAddr, List.append_assoc]
      exact ⟨V', st', .halt, stmts_append_stop hrun (by decide), Or.inr (by decide)⟩
  · -- the ABI guard fires
    obtain ⟨V', st', hrun⟩ :=
      pfxHead_abi_revert_exists (c := callsOf product)
        (g := ExternalGas.ofFun fun _ => 0) (R.scope _ _) [] (vkAddr := vkAddr) ha
    rw [preBlock_of_facts hf vkAddr, List.append_assoc]
    exact ⟨V', st', .halt, stmts_append_stop hrun (by decide), Or.inr (by decide)⟩

/-- The seven slices are live. PROVED from `block_live` (evidence `GeneratorRows.lean:1352`). -/
theorem slices_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (h7 : ∀ q : Partial, BlockLive R q H vkAddr product cd) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st)
      (fun V st => LivePre R H vkAddr cd Checkpoint.pairing V st) :=
  live_append (live_append (live_append (live_append (live_append (live_append
    (h7 .vkLoading) (h7 .transcriptParser)) (h7 .lagrange)) (h7 .quotientLin)) (h7 .pcs))
    (h7 .finalPairing)) (h7 .traceReturn)

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

/-! ## 3. Cone lists and axiom prints -/

#cone_sorries Midfall.LoweringV3.totalV3_correct
#cone_sorries Midfall.LoweringV3.prefix_live
#cone_sorries Midfall.LoweringV3.slices_live
#cone_sorries Midfall.LoweringV3.live_append
#print axioms Midfall.LoweringV3.prefix_live
#print axioms Midfall.LoweringV3.pfxRevertBody_exists
#print axioms Midfall.LoweringV3.pfxHead_abi_revert_exists
#print axioms Midfall.LoweringV3.pfxHead_mem_revert_exists
#assert_axioms Midfall.LoweringV3.prefix_live [propext, Classical.choice, Quot.sound] native []

#print axioms Midfall.LoweringV3.totalV3_correct
#print axioms Midfall.LoweringV3.slices_live
#print axioms Midfall.LoweringV3.live_append
#print axioms Midfall.LoweringV3.stmts_append_stop
#print axioms Midfall.LoweringV3.gasFreeScan

end Midfall.LoweringV3
