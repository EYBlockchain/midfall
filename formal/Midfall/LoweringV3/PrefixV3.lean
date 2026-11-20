/-
  Midfall.LoweringV3.PrefixV3

  WP A1b - THE TWO PREFIX ROWS CLOSED. SIM.6's prefix walk, assembled out of A1's pieces
  (`LoweringV2/Stages.lean` §3B-§3D) over the namespace-free facts BEQ supplied the last Bool for.

  WHY HERE AND NOT IN Stages.lean. The walk needs ONE fact that lives on the V3 side:
  `VkWindow.wordFrom_cdWord` (`wordFrom cd.data.toList i = cdWord cd i`), which is what turns the
  guard's `calldataload` answer into the `cdWord` reads `abiHeadOk` is written with. Stages.lean's
  header records the V2->V3 import as forced-not, so the core goes where the import is legal and
  Composition.lean - which imports both - spends it. Nothing is restated: every guard, run and
  boundary fact below is A1's.

  D-P71. `PfxFacts` is a bundle of PROJECTIONS of clauses both `Render.Valid` and `ValidV3` already
  carry (`pfxFacts_of_validV3` builds it from `ValidV3` alone); no clause was added to `ValidV3`, to
  a row, to a bundle or to the root. No fixture appears in any statement. No `native_decide`.
-/
import Midfall.LoweringV3.Statements
import Midfall.LoweringV3.VkWindow
import Midfall.LoweringV2.Stages
import Midfall.Lowering.Stage
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

variable {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. THE NAMESPACE-FREE FACTS THE WALK CONSUMES -/

/-- **THE PROJECTION BUNDLE.** Fifteen facts about `R`'s OWN fields - five constant-table lookups,
    three model numerals, two wrapper flags, two `proofLayout` statics, the g1 floor, the field
    modulus and the calldata bound. Every one is a theorem of `ValidV3` (`pfxFacts_of_validV3`), and
    every one is a theorem of the frozen `Render.Valid` (A1's §3B lemmas are exactly these), which is
    what lets ONE core serve both rows without a `programOk` bridge. Nothing here is a new
    assumption about the render: it is a re-packing of clauses the validity already carries. -/
structure PfxFacts (R : Render p G₁ G₂ Gₜ) : Prop where
  cNUM : R.consts.lookup "NUM_INSTANCE_CPTR" = some R.pv.proofLayout.proofEnd
  cTRANSCRIPT : R.consts.lookup "TRANSCRIPT_MPTR" = some R.pv.memory.transcriptMptr
  cFR : R.consts.lookup "FR_MODULUS" = some frModulusConstant
  cERRABI : R.consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some 0x1b99e37c
  cERRMEM : R.consts.lookup "ERR_MEMORY_LAYOUT_VIOLATED" = some 0xc9888d23
  mSEL : R.model.abiSelectorBytes = 4
  mHEAD : R.model.abiProofHeadOffset = 0x40
  mINST : R.model.abiInstancesHeadCptr = 0x24
  fVK : R.model.embeddedVk = none
  fQ : R.model.quotientExternal = none
  lCptr : R.plan.proofLayout.proofCptr = abiVerifyProofProofCptr
  lEnd : R.plan.proofLayout.proofEnd =
    R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen
  g1Floor : 0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr
  modulus : p = frModulusConstant
  cdBound : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256

/-- `layout_static_of_valid` restated over the bare `generated` clause: the peel never used anything
    else, which is what lets BOTH validities spend it. PROVED. -/
theorem layout_static_of_generated {R : Render p G₁ G₂ Gₜ} (h : GeneratedBy R) :
    R.plan.proofLayout.proofCptr = abiVerifyProofProofCptr ∧
      R.plan.proofLayout.proofEnd =
        R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen := by
  obtain ⟨rawMeta, plan, hraw, hpl, hp⟩ := pfx_plan_of_generated h
  obtain ⟨meta_, L, hL, hLp⟩ :=
    pfx_newFromVk_proofLayout Features.solidity
      (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have h2 := (proofLen_eq_repackedLen meta_.protocol meta_.numEvals meta_.numPointSets L hL).2
  have h1 := fromProtocol_proofCptr meta_.protocol meta_.numEvals meta_.numPointSets L hL
  rw [← hp] at hLp
  rw [hLp]
  exact ⟨h1, h2⟩

/-- **`ValidV3` PROJECTS EVERY FIELD OF THE BUNDLE.** One line each for the five table lookups (the
    consts-coherence projection plus the data-table lemma), the three numerals and two flags (the
    `generated` peel), the two layout statics (the `newFromVk` / `fromProtocol` peel), the g1 floor,
    the modulus and the calldata bound. PROVED. -/
theorem pfxFacts_of_validV3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : PfxFacts R := by
  have hp := programOkB_of_valid hR
  have hf := pfx_model_prefix_facts hR.generated
  have hfvk : R.model.embeddedVk = none := by
    rw [hf.2.2.2.1, hR.supported.separateVk]
    exact ite_eq_left rfl
  exact
    { cNUM := ((lookup_expectedConsts_of_programOkB hp "NUM_INSTANCE_CPTR").trans
        (Midfall.LoweringV2.expectedConsts_lookups_prefix R.pv R.model).1),
      cTRANSCRIPT := ((lookup_expectedConsts_of_programOkB hp "TRANSCRIPT_MPTR").trans
        (expectedConsts_lookups R.pv R.model).2.2),
      cFR := ((lookup_expectedConsts_of_programOkB hp "FR_MODULUS").trans
        (expectedConsts_lookups R.pv R.model).1),
      cERRABI := ((lookup_expectedConsts_of_programOkB hp "ERR_BAD_CALLDATA_SHAPE").trans
        (Midfall.LoweringV2.expectedConsts_lookups_prefix R.pv R.model).2.1),
      cERRMEM := ((lookup_expectedConsts_of_programOkB hp "ERR_MEMORY_LAYOUT_VIOLATED").trans
        (Midfall.LoweringV2.expectedConsts_lookups_prefix R.pv R.model).2.2),
      mSEL := hf.1, mHEAD := hf.2.1, mINST := hf.2.2.1,
      fVK := hfvk,
      fQ := hf.2.2.2.2 hR.supported.embeddedQuotient.1,
      lCptr := (layout_static_of_generated hR.generated).1,
      lEnd := (layout_static_of_generated hR.generated).2,
      g1Floor := g1IdentityFloor_of_valid hR,
      modulus := hR.env.modulus,
      cdBound := cdBound_of_valid hR }
/-! ## 2. THE PREFIX IN STATEMENT FORM, OVER THE BUNDLE -/

/-- The three statements before the helpers: the ABI guard, the single `let vk`, the memory guard. -/
def pfxHead (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) : Block EVM.Op :=
  [Stmt.cond (pfxAbiCondNum R.pv.proofLayout.proofEnd) (pfxRevertBody 0x1b99e37c),
   Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)),
   Stmt.cond (pfxMemCondNum R.pv.memory.transcriptMptr) (pfxRevertBody 0xc9888d23)]

/-- The two main-block locals. -/
def pfxTail : Block EVM.Op :=
  [Stmt.letDecl ["r"] (some (lit frModulusConstant)),
   Stmt.letDecl ["success"] (some (Expr.lit (.bool true)))]

/-- The environment the head leaves behind: `vk` bound, nothing else. -/
def pfxVkEnv (vkAddr : U256) : VEnv (Bridge.Dialect c g) :=
  List.zip ["vk"] [vkAddr] ++ []

theorem pfxVkEnv_get_vk (vkAddr : U256) :
    VEnv.get (pfxVkEnv (c := c) (g := g) vkAddr) "vk" = some vkAddr := by
  simp [pfxVkEnv, VEnv.get]

/-- THE GUARD SITES RESOLVED AT THE BUNDLE - A1's five §3C lemmas with `R.Valid` replaced by the
    projections it was reading. PROVED. -/
theorem pfxAbiCond_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    pfxAbiCond R.model R.consts =
      pfxAbiCondNum R.pv.proofLayout.proofEnd := by
  show Expr.builtin Op.iszero [Expr.builtin Op.and
        [Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit R.model.abiSelectorBytes],
          lit R.model.abiProofHeadOffset],
         Expr.builtin Op.eq [Expr.builtin Op.calldataload [lit R.model.abiInstancesHeadCptr],
           Expr.builtin Op.sub [pfxSite "NUM_INSTANCE_CPTR" R.consts,
             lit R.model.abiSelectorBytes]]]] = _
  rw [hf.mSEL, hf.mHEAD, hf.mINST,
    pfx_site_eq "NUM_INSTANCE_CPTR" R.consts R.pv.proofLayout.proofEnd hf.cNUM]
  rfl

theorem pfxAbiBody_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    pfxAbiBody R.model R.consts = pfxRevertBody 0x1b99e37c := by
  show [Stmt.exprStmt (Expr.builtin Op.mstore [lit 0,
          Expr.builtin Op.shl [lit 224, pfxSite "ERR_BAD_CALLDATA_SHAPE" R.consts]]),
        Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])] = _
  rw [pfx_site_eq "ERR_BAD_CALLDATA_SHAPE" R.consts 0x1b99e37c hf.cERRABI]
  rfl

theorem pfxMemCond_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    pfxMemCond R.consts = pfxMemCondNum R.pv.memory.transcriptMptr := by
  show Expr.builtin Op.gt [Expr.builtin Op.mload [lit 0x40],
    pfxSite "TRANSCRIPT_MPTR" R.consts] = _
  rw [pfx_site_eq "TRANSCRIPT_MPTR" R.consts R.pv.memory.transcriptMptr hf.cTRANSCRIPT]
  rfl

theorem pfxMemBody_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    pfxMemBody R.consts = pfxRevertBody 0xc9888d23 := by
  show [Stmt.exprStmt (Expr.builtin Op.mstore [lit 0,
          Expr.builtin Op.shl [lit 224, pfxSite "ERR_MEMORY_LAYOUT_VIOLATED" R.consts]]),
        Stmt.exprStmt (Expr.builtin Op.revert [lit 0, lit 4])] = _
  rw [pfx_site_eq "ERR_MEMORY_LAYOUT_VIOLATED" R.consts 0xc9888d23 hf.cERRMEM]
  rfl

theorem pfxTail_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    R.mainLocalsInlined = pfxTail := by
  rw [Midfall.LoweringV2.mainLocals_stmts,
    pfx_site_eq "FR_MODULUS" R.consts frModulusConstant hf.cFR]
  rfl

/-- **THE PREFIX IN STATEMENT FORM OVER THE BUNDLE** (A1's `preBlock_stmts` with the validity
    replaced by the projections it read). PROVED. -/
theorem preBlock_of_facts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) (vkAddr : U256) :
    R.preBlock vkAddr = pfxHead R vkAddr ++ R.helpers ++ pfxTail := by
  show R.preSlice vkAddr 0 ++ R.helpers ++ R.mainLocalsInlined = _
  rw [Midfall.LoweringV2.preSlice_stmts vkAddr hf.fVK hf.fQ, pfxTail_of_facts hf,
    pfxAbiCond_of_facts hf, pfxAbiBody_of_facts hf, pfxMemCond_of_facts hf,
    pfxMemBody_of_facts hf]
  rfl

/-! ## 3. THE GUARDS, RUN -/

/-- **ONE GUARD, RUN.** Either it is silent - the statement ends normally, the environment is
    untouched and the state is the condition's own answer state - or its revert arm ran and the
    statement halted with a revert record AND the guard word is nonzero. A1's `PfxEv` bundle
    (`ev`/`uniq`/`noHalt`) is what makes this three lines instead of an induction. -/
theorem pfxCondRun {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {e : Expr EVM.Op} {u : U256} (err : Nat)
    (he : PfxEv funs V st e u st₁)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond e (pfxRevertBody err)) V' st' o) :
    (o = .normal /\ u = 0 /\ V' = V /\ st' = st₁) \/
      (o = .halt /\ Reverted st' /\ u ≠ 0) := by
  cases h with
  | ifTrue hcv hne hbody =>
      obtain ⟨hcu, hst⟩ := he.uniq hcv
      cases hbody with
      | block hstmts =>
          obtain ⟨ho, hrev⟩ := pfxFailBody_run err hstmts
          refine Or.inr ⟨ho, hrev, ?_⟩
          intro hu
          exact hne (hcu.trans hu)
  | ifFalse hcv heq =>
      obtain ⟨hcu, hst⟩ := he.uniq hcv
      exact Or.inl ⟨rfl, hcu.symm.trans heq, rfl, hst⟩
  | ifHalt hcv => exact absurd hcv he.noHalt

/-- **THE THREE-STATEMENT HEAD, RUN.** Either the head ends normally - at the state the memory
    guard's `mload` left, with `vk` bound and BOTH guards silent - or it halts reverted and one of
    the two guard words is nonzero. This ONE dichotomy is what both rows read: `prefix_sim` spends
    the disjunction, `prefix_prog` spends the silence. -/
theorem pfxHeadRun {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {st₀ : EvmState} {vkAddr : U256}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs [] st₀ (pfxHead R vkAddr) V' st' o) :
    (o = .normal /\ V' = pfxVkEnv (c := c) (g := g) vkAddr /\ st' = touchMemory st₀ 0x40 32 /\
      pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0 /\
      pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0) \/
    (o = .halt /\ Reverted st' /\
      (pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd ≠ 0 \/
        pfxMemWord st₀.memory R.pv.memory.transcriptMptr ≠ 0)) := by
  simp only [pfxHead] at h
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨Va, sa, h1, h2⟩ | ⟨h1, hne⟩
  · rcases pfxCondRun 0x1b99e37c (pfxAbiEv R.pv.proofLayout.proofEnd) h1 with
        ⟨_, ha, hVa, hsa⟩ | ⟨ho, -, -⟩
    · -- the ABI guard is silent: `Va = []`, `sa = st₀`
      subst hVa
      subst hsa
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h2 with ⟨Vb, sb, h3, h4⟩ | ⟨h3, hne'⟩
      · rcases pfxLetInv h3 with ⟨_, hsbb, hVb⟩
        subst hsbb
        have e1 : (Bridge.Dialect c g).litValue (Literal.number vkAddr.toNat) = vkAddr := by
          show BitVec.ofNat 256 vkAddr.toNat = vkAddr
          refine BitVec.eq_of_toNat_eq ?_
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt vkAddr)]
        have hvb : Vb = pfxVkEnv (c := c) (g := g) vkAddr := by
          rw [hVb, e1]
          rfl
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h4 with ⟨Vc, sc, h5, h6⟩ | ⟨h5, hne''⟩
        · rcases pfxCondRun 0xc9888d23 (pfxMemEv R.pv.memory.transcriptMptr) h5 with
              ⟨_, hm, hVc, hsc⟩ | ⟨ho, -, -⟩
          · subst hVc
            subst hsc
            cases h6 with
            | seqNil => left; exact ⟨rfl, hvb, rfl, ha, hm⟩
          · exact absurd ho (by decide)
        · rcases pfxCondRun 0xc9888d23 (pfxMemEv R.pv.memory.transcriptMptr) h5 with
              ⟨hn5, -, -, -⟩ | ⟨ho, hrev, hnm⟩
          · exact absurd hn5 hne''
          · refine Or.inr ⟨ho, hrev, Or.inr hnm⟩
      · rcases pfxLetInv h3 with ⟨hn3, -, -⟩
        exact absurd hn3 hne'
    · exact absurd ho (by decide)
  · -- the head stopped at the ABI guard: it fired, so the revert arm ran
    rcases pfxCondRun 0x1b99e37c (pfxAbiEv R.pv.proofLayout.proofEnd) h1 with
          ⟨hn, -, -, -⟩ | ⟨ho, hrev, hna⟩
    · exact absurd hn hne
    · refine Or.inr ⟨ho, hrev, Or.inl hna⟩
/-- The two main locals, run, stated over `pfxTail`. -/
theorem pfxTailRun {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st pfxTail V' st' o) :
    o = .normal /\ st' = st /\
      VEnv.get V' "r" = some (BitVec.ofNat 256 frModulusConstant) /\
      VEnv.get V' "success" = some (1 : U256) /\ VEnv.get V' "vk" = VEnv.get V "vk" := by
  simp only [pfxTail] at h
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := pfx_mainLocals_run h
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## 4. THE `.start` BOUNDARY, ASSEMBLED -/

/-- The two arithmetic facts the `abiHeadOk` reassembly needs, both read off the bundle's own
    statics and the calldata bound. PROVED. -/
theorem proofEnd_ge_four {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    4 ≤ R.plan.proofLayout.proofEnd := by
  rw [hf.lEnd, hf.lCptr]
  have h : 4 ≤ abiVerifyProofProofCptr := by decide
  exact Nat.le_trans h (Nat.le_add_right _ _)

theorem proofEnd_lt {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R) :
    R.plan.proofLayout.proofEnd < 2 ^ 256 := by
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hf.cdBound

/-- `(ofNat 256 a - ofNat 256 4).toNat` is the NATURAL subtraction when `a` is a word-sized
    number at or above 4. Stated as a lemma because the kernel will not do it: `decide` on the
    instance hits the recursion wall at 256 bits. -/
theorem toNat_sub_four (a : ℕ) (h4 : 4 ≤ a) (ha : a < 2 ^ 256) :
    (BitVec.ofNat 256 a - BitVec.ofNat 256 4).toNat = a - 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, 4 + k = a := ⟨a - 4, Nat.add_sub_cancel' h4⟩
  have hk : 4 + k < 2 ^ 256 := by simpa using ha
  have hkw : k < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_add_left k 4) hk
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 4 < 2 ^ 256), Nat.mod_eq_of_lt hk,
    ← Nat.add_assoc, Nat.sub_add_cancel (by norm_num : 4 ≤ 2 ^ 256),
    Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hkw, Nat.mod_eq_of_lt hkw,
    Nat.add_sub_cancel_left]

/-- **THE `LeanRaw .start` REASSEMBLY.** The ABI guard's own answer word, read back as the four
    `abiHeadOk` checks: the selector is `EntryFrame.selector`, the two layout statics are the
    bundle's, and the two head words are the guard's silence transported along
    `VkWindow.wordFrom_cdWord` (the reason this file is on the V3 side). PROVED. -/
theorem abiHeadOk_of_abiWord_zero {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {cd : Bytes} {st₀ : EvmState}
    (hentry : EntryFrame R W Lyt H cd st₀)
    (habih : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0) :
    abiHeadOk R.plan.proofLayout cd = true := by
  obtain ⟨hA, hB⟩ :=
    (pfxAbiWord_eq_zero st₀.env.calldata R.pv.proofLayout.proofEnd).mp habih
  have hpe := proofEnd_lt hf
  have h4 := proofEnd_ge_four hf
  have hw4' : wordFrom cd.data.toList 4 = BitVec.ofNat 256 0x40 := by
    rw [← entryFrame_calldata hentry]
    exact hA
  have hw24' : wordFrom cd.data.toList 0x24 =
      BitVec.ofNat 256 R.pv.proofLayout.proofEnd - BitVec.ofNat 256 4 := by
    rw [← entryFrame_calldata hentry]
    exact hB
  have hw4 : cdWord cd 4 = BitVec.ofNat 256 0x40 :=
    (VkWindow.wordFrom_cdWord cd 4).symm.trans hw4'
  have hw24 : cdWord cd 0x24 =
      BitVec.ofNat 256 R.plan.proofLayout.proofEnd - BitVec.ofNat 256 4 :=
    (VkWindow.wordFrom_cdWord cd 0x24).symm.trans hw24'
  have h1 : (bytesTake cd 0 4 == some fnSigVerifyProof) = true := by
    rw [hentry.selector]
    simp
  have h2 : (R.plan.proofLayout.proofCptr == abiVerifyProofProofCptr) = true := by
    rw [hf.lCptr]
    simp
  have h3 : (R.plan.proofLayout.proofEnd ==
      R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen) = true := by
    rw [hf.lEnd]
    simp
  have h4b : ((cdWord cd 4).toNat == 0x40) = true := by
    rw [hw4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num : 0x40 < 2 ^ 256)]
    simp
  have h5b : ((cdWord cd 0x24).toNat ==
      R.plan.proofLayout.proofEnd - 4) = true := by
    rw [hw24, toNat_sub_four _ h4 hpe]
    simp
  simp only [abiHeadOk]
  rw [h1, h2, h3, h4b, h5b]
  rfl
/-- **THE STAGED BOUNDARY AT `.start`, AFTER A SILENT PREFIX.** The six conjuncts of
    `StageInv .start`: `Frame` from the entry facts plus the two lets, `success = 1` from the tail,
    `BaseInv .start` = `Inv .start` for the witness snapshot (halt record, `LocalsOk`, and the
    g1_identity window - the clause PG-G1BEQ128 recorded, now closed by BEQ's `ReflBEq ByteArray`),
    `LeanRaw .start` from the reassembly above, `Mirror .start = True`, and `Agree .start` from
    A1's `pfx_agree_start`. PROVED. -/
theorem pfx_stageInv_start {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {st₀ : EvmState} (hdep : DeploymentV2 R W H vkAddr)
    (hentry : EntryFrame R W Lyt H cd st₀)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    (hst : st' = touchMemory st₀ 0x40 32)
    (hvk : VEnv.get V' "vk" = some vkAddr)
    (hr : VEnv.get V' "r" = some (BitVec.ofNat 256 frModulusConstant))
    (hsucc : VEnv.get V' "success" = some (1 : U256))
    (habih : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0) :
    StageInv R H vkAddr cd Checkpoint.start V' st' := by
  have hhalt₀ : st₀.halted = none := by
    obtain ⟨mem₀, aw, rfl⟩ := hentry.shape
    rfl
  have hcal : st'.env.calldata = cd.data.toList := by
    rw [hst, touchMemory_env]; exact entryFrame_calldata hentry
  have hkec : st'.env.keccakOf = hashOfBytes H := by
    rw [hst, touchMemory_env]; exact entryFrame_keccak hentry
  have hxcd : st'.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList := by
    rw [hst, touchMemory_env]; exact entryFrame_extCode hdep hentry
  have hzero : ∀ x, 0x80 ≤ x → st'.memory x = 0 := by
    intro x hx; rw [hst, touchMemory_memory]; exact hentry.zeroAbove x hx
  have hhalt : st'.halted = none := by rw [hst, touchMemory_halted, hhalt₀]
  have hbase : BaseInv R Checkpoint.start V' st' := by
    show Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params
      (baseCk Checkpoint.start) R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) V' st'
    rw [baseCk]
    have k1 : ¬ (Checkpoint.vk ≤ Checkpoint.start) := by decide
    have k2 : ¬ (Checkpoint.transcript ≤ Checkpoint.start) := by decide
    have k3 : ¬ (Checkpoint.lagrange ≤ Checkpoint.start) := by decide
    have k4 : ¬ (Checkpoint.quotient ≤ Checkpoint.start) := by decide
    have k5 : ¬ (Checkpoint.pcs ≤ Checkpoint.start) := by decide
    have k6 : ¬ ((Checkpoint.start == Checkpoint.pairing) = true) := by decide
    simp only [Midfall.Lowering.Inv, Midfall.Lowering.InvAt, witnessSnapshot]
    rw [ite_eq_right k1, ite_eq_right k2, ite_eq_right k3, ite_eq_right k4,
      ite_eq_right k5, ite_eq_right k6]
    simp only [Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hhalt]
      simp
    · show (match VEnv.get V' "r" with
          | none => true
          | some w => w == BitVec.ofNat 256 p) = true
      rw [hr]
      simp [← hf.modulus]
    · rw [Midfall.LoweringV2.bytesAt_zero_above st' (ptrAddr R.pv.memory.g1IdentityMptr) hzero
        hf.g1Floor]
      simp
  refine ⟨⟨hcal, hkec, hxcd, hdep.vkHash, hdep.vkNonEmpty,
      ⟨frModulusConstant, hf.cFR, hr⟩, hvk, hentry.cdSize⟩,
    hsucc, hbase, abiHeadOk_of_abiWord_zero hf hentry habih, trivial,
    pfx_agree_start H cd hbase⟩

/-! ## 5. THE WALK -/

/-- **THE PREFIX WALK, ONCE, FOR BOTH ROWS.** From an entry frame and a deployment, any run of
    `R.preBlock vkAddr` from the empty environment either ends normally at the `.start` staged
    boundary - and then both guards were silent - or halts reverted, and then one of the two guard
    words was nonzero. Everything it uses is A1's: `preBlock_of_facts`, `pfxHeadRun`,
    `funDefs_noop`/`helpers_funDefs`, `pfxTailRun`, `pfx_stageInv_start`. -/
theorem prefix_walk {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {st₀ : EvmState} (hdep : DeploymentV2 R W H vkAddr)
    (hentry : EntryFrame R W Lyt H cd st₀)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀ (R.preBlock vkAddr) V' st' o) :
    (o = .normal /\ StageInv R H vkAddr cd Checkpoint.start V' st' /\
      pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0 /\
      pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0) \/
    (o = .halt /\ Reverted st' /\
      (pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd ≠ 0 \/
        pfxMemWord st₀.memory R.pv.memory.transcriptMptr ≠ 0)) := by
  rw [preBlock_of_facts hf vkAddr] at hrun
  -- `++` associates to the LEFT here, so the top split is `(head ++ helpers) | tail`.
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
      ⟨V₁, st₁, hHh, htail⟩ | ⟨hHh, hne⟩
  · rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hHh with
        ⟨V₂, st₂, hA, hb⟩ | ⟨hA, hne'⟩
    · rcases pfxHeadRun hA with ⟨_, hV₂, hst₂, ha, hm⟩ | ⟨ho, -, -⟩
      · subst hV₂
        subst hst₂
        obtain ⟨hV₁, hst₁, -⟩ :=
          funDefs_noop (funs := R.scope c g) (b := R.helpers)
            (helpers_funDefs (R := R)) hb
        subst hV₁
        subst hst₁
        obtain ⟨hn, hst', hr, hsucc, hvk⟩ := pfxTailRun htail
        have hvk' : VEnv.get V' "vk" = some vkAddr :=
          hvk.trans (pfxVkEnv_get_vk (c := c) (g := g) vkAddr)
        refine Or.inl ⟨hn,
          pfx_stageInv_start hf hdep hentry hst' hvk' hr hsucc ha, ha, hm⟩
      · exact absurd ho (by decide)
    · rcases pfxHeadRun hA with ⟨hn, -, -, -, -⟩ | ⟨ho, -, -⟩
      · exact absurd hn hne'
      · exact absurd ho (by decide)
  · rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hHh with
        ⟨V₂, st₂, hA, hb⟩ | ⟨hA, hne'⟩
    · rcases pfxHeadRun hA with ⟨_, -, -, -, -⟩ | ⟨ho, -, -⟩
      · obtain ⟨-, -, hon⟩ :=
          funDefs_noop (funs := R.scope c g) (b := R.helpers)
            (helpers_funDefs (R := R)) hb
        exact absurd hon hne
      · exact absurd ho (by decide)
    · rcases pfxHeadRun hA with ⟨hn, -, -, -, -⟩ | ⟨ho, hrev, hx⟩
      · exact absurd hn hne'
      · exact Or.inr ⟨ho, hrev, hx⟩
/-! ## 6. THE TWO GUARD SILENCES, AND THE PROGRESS SIDE -/

/-- **THE TRANSCRIPT POINTER IS A WORD.** `SupportedV2.layout` pins `R.plan.memory.validate.isOk =
    true`, and `validate`'s `fixedLowMemory` loop rejects ANY drift of `transcript_mptr` from the
    generator's own `transcriptBufferStart` (`Layout.lean:1029`), so the pointer IS that literal and
    is far below `2 ^ 256`. The loop is peeled by unfolding `validate` and `ForIn.forIn` and
    `simp`ing the concrete seven-element list into a `do` chain: if either of the first two checks
    failed the whole `Except` would be an `error`, contradicting `h`. This is the fact the memory
    guard's silence needs (`pfxMemWord_eq_zero` asks `t < 2 ^ 256`), and it is a theorem of the
    validity, not a hypothesis: nothing was added. PROVED. -/
theorem transcriptMptr_lt {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.pv.memory.transcriptMptr < 2 ^ 256 := by
  show R.plan.memory.transcriptMptr < 2 ^ 256
  cases h : R.plan.memory.validate with
  | error e =>
      have hs := hR.supported.layout.2
      rw [h] at hs
      exact absurd hs (by simp [Except.isOk, Except.toBool])
  | ok u =>
      unfold Midfall.Generator.VerifierMemoryLayout.validate at h
      simp only [Bind.bind, Except.bind, pure] at h
      simp at h
      by_cases hc0 :
          (R.plan.memory.constructorSmokeScratchMptr = lowMemoryScratchStart)
      · by_cases hc1 : (R.plan.memory.transcriptMptr = transcriptBufferStart)
        · rw [hc1]
          decide
        · rw [ite_eq_right hc1, ite_eq_left hc0] at h
          cases h
      · rw [ite_eq_right hc0] at h
        cases h

/-- The memory guard is silent at an entry frame: `fmp` bounds the free pointer by the table's
    `TRANSCRIPT_MPTR`, the table's value IS the render's transcript base (the bundle), and the base
    is a word (`transcriptMptr_lt`). PROVED. -/
theorem pfxMemWord_zero_of_entry {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {cd : Bytes} {st₀ : EvmState}
    (hentry : EntryFrame R W Lyt H cd st₀)
    (htm : R.pv.memory.transcriptMptr < 2 ^ 256) :
    pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0 := by
  obtain ⟨t, ht, hle⟩ := hentry.fmp
  have ht' : t = R.pv.memory.transcriptMptr :=
    Option.some.inj (ht.symm.trans hf.cTRANSCRIPT)
  subst ht'
  exact pfxMemWord_zero_of_le _ htm hle

/-- **THE ABI GUARD IS SILENT ON A CALADATA THAT DECODES.** `LeanAccepts` gives
    `decodeCalldata = some`; `decodeCalldata_eq_raw` moves that to `rawDecode = some`, whose
    `if envelopeOk` can only be the `then` branch, and `envelopeOk` begins with `abiHeadOk`. The two
    head words are then read back as `wordFrom` along `VkWindow.wordFrom_cdWord` - the same bridge
    as §4, run the other way. PROVED. -/
theorem pfxAbiWord_zero_of_leanAccepts {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {cd : Bytes} {st₀ : EvmState}
    (hentry : EntryFrame R W Lyt H cd st₀) (hacc : LeanAccepts R H cd) :
    pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0 := by
  obtain ⟨ms, instW, inst, hdec, -, -⟩ := hacc
  rw [decodeCalldata_eq_raw] at hdec
  obtain ⟨r, hr⟩ : ∃ r, rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd = some r := by
    cases hr : rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd with
    | none => rw [hr, Option.bind] at hdec; exact absurd hdec (by simp)
    | some r => exact ⟨r, rfl⟩
  have henv : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true := by
    unfold rawDecode at hr
    by_cases h : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true
    · exact h
    · rw [ite_eq_right h] at hr
      exact absurd hr (by simp)
  have hab : abiHeadOk R.plan.proofLayout cd = true := by
    simp only [envelopeOk, Bool.and_eq_true] at henv
    exact henv.1.1.1
  have hab' := hab
  simp only [abiHeadOk, Bool.and_eq_true] at hab'
  have h4w : ((cdWord cd 4).toNat == 0x40) = true := hab'.2.1
  have h24w : ((cdWord cd 0x24).toNat ==
      R.plan.proofLayout.proofEnd - 4) = true := hab'.2.2
  have hpe := proofEnd_lt hf
  have h4 := proofEnd_ge_four hf
  refine (pfxAbiWord_eq_zero st₀.env.calldata R.pv.proofLayout.proofEnd).mpr ⟨?_, ?_⟩
  · refine BitVec.eq_of_toNat_eq ?_
    rw [entryFrame_calldata hentry, VkWindow.wordFrom_cdWord cd 4, eq_of_beq h4w,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num : 0x40 < 2 ^ 256)]
  · refine BitVec.eq_of_toNat_eq ?_
    rw [entryFrame_calldata hentry, VkWindow.wordFrom_cdWord cd 0x24]
    show (cdWord cd 0x24).toNat =
      (BitVec.ofNat 256 R.plan.proofLayout.proofEnd - BitVec.ofNat 256 4).toNat
    rw [toNat_sub_four _ h4 hpe, eq_of_beq h24w]

/-- **THE PROGRESS SIDE, EVERY RUN.** Under both silences every prefix run is normal and ends at the
    `.start` boundary: the halt arm of `prefix_walk` carries the disjunction that one of the two
    guards fired, and both are silent. PROVED. -/
theorem prefix_prog_run {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {st₀ : EvmState} (hdep : DeploymentV2 R W H vkAddr)
    (hentry : EntryFrame R W Lyt H cd st₀)
    (ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0)
    (hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀ (R.preBlock vkAddr) V' st' o) :
    o = .normal /\ StageInv R H vkAddr cd Checkpoint.start V' st' := by
  rcases prefix_walk hf hdep hentry hrun with ⟨hn, hsi, -, -⟩ | ⟨-, -, hna | hnm⟩
  · exact ⟨hn, hsi⟩
  · exact absurd ha hna
  · exact absurd hm hnm

/-- The `litValue` of a number literal is the word, and `ofNat 256 (a.toNat)` is `a`. -/
theorem litValue_number (n : U256) :
    (Bridge.Dialect c g).litValue (Literal.number n.toNat) = n := by
  show BitVec.ofNat 256 n.toNat = n
  exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt n))

/-- **THE PREFIX RUN EXISTS** under the two silences: the head is three `Step` applications (two
    `ifFalse` and one `letVal`), the helper block is `pfx_helpers_exec`, and the tail is two
    `letVal`s. Assembled with `ExecStmts.append`. PROVED. -/
theorem prefix_prog_exists {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {vkAddr : U256} {st₀ : EvmState}
    (ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0)
    (hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀ (R.preBlock vkAddr) V' st' .normal := by
  rw [preBlock_of_facts hf vkAddr]
  have hHead : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀ (pfxHead R vkAddr)
      (pfxVkEnv (c := c) (g := g) vkAddr) (touchMemory st₀ 0x40 32) .normal := by
    simp only [pfxHead]
    refine Step.seqCons (Step.ifFalse (pfxAbiEv R.pv.proofLayout.proofEnd).ev ha)
      (Step.seqCons ?_ (Step.seqCons
        (Step.ifFalse (pfxMemEv R.pv.memory.transcriptMptr).ev hm) Step.seqNil))
    · have hh : ExecStmt (Bridge.Dialect c g) (R.scope c g) [] st₀
          (Stmt.letDecl ["vk"] (some (lit vkAddr.toNat)))
          (List.zip ["vk"] [(Bridge.Dialect c g).litValue (Literal.number vkAddr.toNat)] ++ [])
          st₀ .normal :=
        Step.letVal (D := Bridge.Dialect c g) Step.lit (by simp)
      rw [litValue_number vkAddr] at hh
      exact hh
  have hTailEx : ∃ V', ExecStmts (Bridge.Dialect c g) (R.scope c g)
      (pfxVkEnv (c := c) (g := g) vkAddr) (touchMemory st₀ 0x40 32) pfxTail V'
      (touchMemory st₀ 0x40 32) .normal := by
    simp only [pfxTail]
    refine ⟨_, Step.seqCons (Step.letVal (D := Bridge.Dialect c g) Step.lit (by simp))
      (Step.seqCons (Step.letVal (D := Bridge.Dialect c g) Step.lit (by simp)) Step.seqNil)⟩
  obtain ⟨V', hTail⟩ := hTailEx
  exact ⟨V', touchMemory st₀ 0x40 32,
    ExecStmts.append (ExecStmts.append hHead pfx_helpers_exec) hTail⟩

/-- **THE PROGRESS ROW, EVERY RUN AND EXISTENCE, OVER THE BUNDLE.** -/
theorem prefix_prog_core {R : Render p G₁ G₂ Gₜ} (hf : PfxFacts R)
    {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash} {vkAddr : U256} {cd : Bytes}
    {st₀ : EvmState} (hdep : DeploymentV2 R W H vkAddr)
    (hentry : EntryFrame R W Lyt H cd st₀)
    (ha : pfxAbiWord st₀.env.calldata R.pv.proofLayout.proofEnd = 0)
    (hm : pfxMemWord st₀.memory R.pv.memory.transcriptMptr = 0) :
    StmtsTotal (D := Bridge.Dialect c g) (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] /\ st = st₀)
      (fun _ _ V' st' o => o = .normal /\ StageInv R H vkAddr cd Checkpoint.start V' st') := by
  refine ⟨?_, ?_⟩
  · intro V st ⟨hV, hst⟩
    subst hV
    subst hst
    obtain ⟨V', st', hrun⟩ := prefix_prog_exists hf ha hm
    exact ⟨V', st', .normal, hrun, rfl,
      (prefix_prog_run hf hdep hentry ha hm hrun).2⟩
  · intro V st ⟨hV, hst⟩ V' st' o hrun
    subst hV
    subst hst
    exact prefix_prog_run hf hdep hentry ha hm hrun

/-! ## 5. THE RUN DECOMPOSITION, V3-SIDE (ST.11 re-point) -/

/- **THE RE-POINT.** A1's `run_split` and `run_join` (`LoweringV2/Stages.lean:521`, `:547`) are
    the statements the composition spends, and they are PROVED from the V2 leaf
    `Midfall.LoweringV2.prog_slices_decomp` - which carries NO shadow hypothesis and is therefore
    FALSE for a valid render (findings B-5/D-13, STATUS entry 8: `constTableOf` filters only `vk`
    and `success`, while the third cut of `asmOf` binds `r` at top level, so a model that declares
    a constant named `r` or `quotientEvaluator` breaks it). The repair is the V3 text
    `prog_slices_decompV3`, which ST.11 now PROVES with `hns : noShadowB R = true` - and that
    hypothesis is PROJECTED from `ValidV3.program` by `noShadow_of_programOk`, never postulated.

    `Stages.lean` may NOT import `LoweringV3` (A1b measured that import as forced-not and put its
    own core here instead), so the re-point lives HERE and `Composition.lean`/`Totality.lean` -
    which import both - spend it. NOTHING IS RESTATED: `scopeV3 R c g` is `R.scope c g` and
    `slicesV3 R` is `R.slices` by `rfl`, so these two theorems have the same proposition as A1's
    and the same proof, one premise deeper. -/

/-- A1's `run_split` (`Stages.lean:521`), same statement, proved from `prog_slices_decompV3`
    instead of the V2 leaf. PROVED. -/
theorem run_splitV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (hobs : RunBody R vkAddr 0 c g st₀ obs) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome),
      obs = ⟨committedState st₀ st', o⟩ ∧
        ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
          (R.preBlock vkAddr ++ R.slices) V' st' o := by
  obtain ⟨V', st', hrun, heq⟩ := hobs
  obtain ⟨hprog, hhoist⟩ := prog_slices_decompV3 R hns vkAddr 0 c g
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

/-- A1's `run_join` (`Stages.lean:547`), same statement, same re-point. PROVED. -/
theorem run_joinV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas)
    (st₀ : EvmState) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) [] st₀
      (R.preBlock vkAddr ++ R.slices) V' st' o) :
    RunBody R vkAddr 0 c g st₀ ⟨committedState st₀ st', o⟩ := by
  obtain ⟨hprog, hhoist⟩ := prog_slices_decompV3 R hns vkAddr 0 c g
  have hscope : R.scope c g = [hoist (Bridge.Dialect c g) (R.prog vkAddr 0)] := hhoist.symm
  have hbody : R.preBlock vkAddr ++ R.slices = R.prog vkAddr 0 := by
    rw [hprog]; rfl
  rw [hscope, hbody] at hrun
  exact ⟨restore [] V', st', Step.block hrun, rfl⟩

/-- The shadow hypothesis the two lemmas above want, read off the ONE text. PROVED - it is the
    projection `noShadow_of_programOk` of `ValidV3.program`, restated at the render. -/
theorem noShadowB_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : noShadowB R = true :=
  noShadow_of_programOk (programOkB_of_valid hR)

#check Midfall.LoweringV3.prog_slices_decompV3
#print axioms Midfall.LoweringV3.prog_slices_decompV3
#cone_sorries Midfall.LoweringV3.prog_slices_decompV3
#print axioms Midfall.LoweringV3.run_splitV3
#print axioms Midfall.LoweringV3.run_joinV3
#cone_sorries Midfall.LoweringV3.run_splitV3
#cone_sorries Midfall.LoweringV3.run_joinV3

end Midfall.LoweringV3
