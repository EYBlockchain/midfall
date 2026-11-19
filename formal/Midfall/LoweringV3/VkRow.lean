/-
  Midfall.LoweringV3.VkRow

  **WP A3 (GEN.1 + SIM.8 + T3.6): the vkLoading row of EVERY render, at the ONE row shape.**
  This is the proof half of the two vk_* leaves in Midfall/LoweringV3/Rows.lean.

  WHAT THE CARDS ASSUMED AND THE TREE DOES NOT HAVE (re-derived here, D-P75 item 3):
  * StageBnd, BlockSimV3, exitSimBnd are DELETED (D-P74 item 2). The row is
    BlockSim R Partial.vkLoading over StageInv: TWO StmtsContractAlls over the closed slice.
  * The three V2 gaps vk_sound_clean / vk_poison_walk / vk_progress
    (LoweringV2/Blocks/VkLoading.lean:753, :770, :787) are sorry AND are stated over the FROZEN
    Clean R .start Snap with a snapshot argument, not over StageInv. They are NOT consumed here: a
    row proved from them would not shrink the cone. What IS consumed is their snapshot-free
    section 1-4 interface.
  * vk_slice and pv_hasAcc_false take the frozen R.Valid; ValidV3 is a parallel copy and is NOT
    defeq, so both are restated over ValidV3 in section 0, reading hR.supported.noAcc, which
    ValidV3 carries verbatim.
  * THE PINS. GEN.1 was written when vkPins/vkProgressPins were clauses 12-13 of Valid
    (D-P50/S.9). OBJ.8 deleted the clauses and OBJ.4 proved numInst and disjoint are not table
    facts. They are still NEEDED - Inv .vk's payload clause is about ptrAddr R.pv.memory.vkMptr
    while the block writes to the table's VK_MPTR, and LeanRaw .vk is envelopeOk at
    R.cfg.numInstances while the block checks R.pv.numInstances - but they are NOT free premises:
    the row's only hypotheses are ValidV3, G1CodecHeadlineLaws and Eip2537.Holds.

  THE WALK. Thirteen statements, inverted with Step.stmts_cons_inv - the route section 6 of
  Blocks/VkLoading.lean names and GEN.1 step 2 prescribes. No wp_run in the soundness walk: wp
  executes a CONCRETE environment and BlockSim quantifies over every V that satisfies StageInv, so
  the only sound route is inversion of the given run. Midfall/Yul/VKP.lean's vk_all_param is the
  forward counterpart and is used for the PROGRESS half, where a run must be exhibited.

  WALK STYLE. Each statement class gets a PEEL lemma whose conclusion is a disjunction: either the
  sequence stopped with a revert, or it continues with the tail from a named environment and
  state. That is what keeps the thirteen-step walk FLAT. A naive rcases at every statement nests
  2^13 ways and, worse, destroys the environment names the next peel needs: cases substitutes
  V' and st' away on the branches where the constructor pins them.

  TWO LEAN TRAPS PAID FOR HERE, both worth recording for the next row card.
  * cases h with | builtinHalt .. on a Step whose result index is .halt FAILS with dependent
    elimination failed for a builtin whose stepOp arm matches on the ARGUMENT LIST (extcodecopy
    is [a, dst, src, n]): the equation solver has to invert the match with argvals still a
    metavar. Plain cases h succeeds, leaves the equation as a hypothesis, and next a b names the
    two fields. That is the shape of vkS2_expr_ne_halts.
  * An abbrev defined from the section's implicit variables (Dc := Bridge.Dialect c g) cannot be
    applied in a theorem HEADER: the header is resolved before the binders exist and the error is
    dont know how to synthesize implicit argument c. Spell the dialect out.

  NO FIXTURE (D-P71): every statement here is generic in the render. No native_decide, no
  heartbeat or recursion raise.
-/
import Midfall.LoweringV2.Stages
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.LoweringV3.Statements
import Midfall.Yul.VKP
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.VkRow

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.Stage
open Midfall.LoweringV2.Blocks.VkLoading Midfall.LoweringV2.Blocks.TraceReturn

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
  {c : ExternalCalls} {g : ExternalGas}

/-- The revert predicate, spelled out: Midfall.Lowering.Reverted is a parallel copy and both
    namespaces are open here, so the short name is ambiguous. -/
abbrev Rev (st : EvmState) : Prop := Midfall.LoweringV2.Reverted st

/-! ## 0. THE SLICE AND THE SCOPE OVER ValidV3 -/

/-- pv_hasAcc_false (Blocks/VkLoading.lean:179) at the V3 clause bundle. -/
theorem pv_hasAccV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.pv.hasAccumulator = false := by
  classical
  have h : R.cfg.accumulator = none := hR.supported.noAcc
  have h1 : R.pv = planViewOf R.plan R.model none := by
    show planViewOf R.plan R.model R.cfg.accumulator = _
    rw [h]
  rw [h1, planViewOf, planViewWithAccumulator]
  rfl

/-- **vk_slice over ValidV3.** -/
theorem vk_sliceV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.slice Partial.vkLoading =
      [Stmt.block (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
        R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
        R.pv.proofLayout.proofLen)] := by
  have hacc : R.pv.hasAccumulator = false := pv_hasAccV3 R hR
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.vkLoading) = _
  rw [GenAst.emitPartial, GenAst.emitVkLoading, hacc, vk_slice_raw]

/-- The thirteen statements as a list of named sites: the rfl that lets the walk peel by name. -/
theorem vkBody_nil (R : Render p G₁ G₂ Gₜ) (n k w o l b q : Nat) :
    vkBody R.consts n k w o l b q =
      [vkS1 R.consts, vkS2 R.consts,
        vkHdr "NUM_INSTANCES_MPTR" n R.consts (vkSucc0 R.consts),
        vkHdr "K_MPTR" k R.consts vkSucc,
        vkHdr "HAS_ACCUMULATOR_MPTR" w R.consts vkSucc,
        vkHdr "ACC_OFFSET_MPTR" o R.consts vkSucc,
        vkHdr "NUM_ACC_LIMBS_MPTR" l R.consts vkSucc,
        vkHdr "NUM_ACC_LIMB_BITS_MPTR" b R.consts vkSucc,
        vkS9 R.consts, vkS10 R.consts q, vkS11 R.consts n, vkS12 R.consts n,
        vkS13 R.consts] := rfl

/-! ## 1. SCOPE, SITE AND NON-HALTING FACTS -/

/-- fail resolves inside a one-statement fail arm: the arm declares no functions, so hoist is the
    empty scope and the lookup is the outer one by defeq (T.1's tr_guard_reverts trick). -/
theorem vkArm_fail_lookup {funs funs' : FunEnv (Bridge.Dialect c g)} {e : Expr EVM.Op}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs')) :
    lookupFun (hoist (Bridge.Dialect c g) [Stmt.exprStmt (Expr.call "fail" [e])] :: funs) "fail" =
      some (failFDecl, funs') := by
  show lookupFun funs "fail" = some (failFDecl, funs')
  exact hfail

/-- fail resolves inside the vkBody block: vkBody declares no functions either. -/
theorem vkBody_fail_lookup {funs funs' : FunEnv (Bridge.Dialect c g)} (R : Render p G₁ G₂ Gₜ)
    (n k w o l b q : Nat)
    (hfail : lookupFun funs "fail" = some (failFDecl, funs')) :
    lookupFun (hoist (Bridge.Dialect c g) (vkBody R.consts n k w o l b q) :: funs) "fail" =
      some (failFDecl, funs') := by
  show lookupFun funs "fail" = some (failFDecl, funs')
  exact hfail

/-- A raw variable occurrence evaluates to the binding it names. -/
theorem vk_var_hsite {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {x : Ident} {st₀ st₁ : EvmState} {av : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st₀ (Expr.var x) (.vals [av] st₁)) :
    VEnv.get V x = some av := by
  cases h with | var hget => exact hget

/-- vkSucc0 at a render's table IS the variable success (consts_succ_none). -/
theorem vkSucc0_hsite {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st₀ st₁ : EvmState} {av : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st₀ (vkSucc0 R.consts) (.vals [av] st₁)) :
    VEnv.get V "success" = some av := by
  rw [vkSucc0_var R] at h
  exact vk_var_hsite h

/-- vkSucc0 and vkSucc cannot halt. -/
theorem vkSucc_ne_halts {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (vkSucc0 R.consts) (.halt st')) : False := by
  rw [vkSucc0_var R] at h
  exact vkVar_ne_halts h

theorem vkSucc2_ne_halts {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st vkSucc (.halt st')) : False :=
  vkVar_ne_halts h

/-- The mload of an inlined site cannot halt: the site cannot and mload is total. -/
theorem vk_mload_ne_halts {R : Render p G₁ G₂ Gₜ} (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.mload [vkSite slot R.consts]) (.halt st')) : False :=
  vk_nh_unary (op := Op.mload) (fun _ _ _ h' => vk_ok_mload h')
    (fun _ _ hh => vkSite_ne_halts hh) h

/-- The calldataload of an inlined site cannot halt. -/
theorem vk_cdl_ne_halts {R : Render p G₁ G₂ Gₜ} (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.calldataload [vkSite slot R.consts]) (.halt st')) : False :=
  vk_nh_unary (op := Op.calldataload) (fun _ _ _ h' => vk_ok_calldataload h')
    (fun _ _ hh => vkSite_ne_halts hh) h

/-- extcodecopy answers .ok for EVERY argument list: the four-arity arm of stepOp is a .ok and
    the other arities are none, so the relation cannot produce a halt at all (EVMExec.lean:854). -/
theorem vkS2_bi {argvals : List U256} {st₁ : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.extcodecopy argvals st₁ r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  cases argvals with
  | nil => cases h
  | cons a r1 => cases r1 with
    | nil => cases h
    | cons b r2 => cases r2 with
      | nil => cases h
      | cons c' r3 => cases r3 with
        | nil => simp only [builtinWithExternal, stepOp] at h; cases h
        | cons d r4 => cases r4 with
          | nil => simp only [builtinWithExternal, stepOp] at h; exact ⟨_, _, (Option.some.inj h).symm⟩
          | cons e r5 => cases h

/-- The extcodecopy expression cannot halt: neither its four arguments nor the builtin itself. -/
theorem vkS2_expr_ne_halts {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.extcodecopy [vkVk0 R.consts, vkSite "VK_MPTR" R.consts,
          Expr.lit (.number 1), vkSite "EXPECTED_VK_PAYLOAD_LENGTH" R.consts]) (.halt st')) :
    False := by
  cases h
  · next hargs hbi =>
      obtain ⟨_, _, hr⟩ := vkS2_bi hbi
      cases hr
  · next hargs =>
      cases hargs with
      | argsRestHalt h' => cases h' with
        | argsRestHalt h2 => cases h2 with
          | argsRestHalt h3 => cases h3 with
            | argsRestHalt h4 => cases h4
            | argsHeadHalt _ h4 => exact vkSite_ne_halts h4
          | argsHeadHalt _ h2 => exact vkLit_ne_halts h2
        | argsHeadHalt _ h' => exact vkSite_ne_halts h'
      | argsHeadHalt _ h' => exact vkSite_ne_halts h'

/-- The one-statement fail arm, at any outcome: it halts reverted. -/
theorem vk_arm_reverts {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {e : Expr EVM.Op}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (hne : ∀ (st₁ st₂ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₂) → False)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st [Stmt.exprStmt (Expr.call "fail" [e])] V' st' o) :
    o = .halt ∧ Rev st' := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne'⟩
  · have h2 := vk_fail_reverts hlookup hne h₁
    cases hnil
    exact absurd h2.1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  · exact vk_fail_reverts hlookup hne h₁

/-- The arm of vkS1, at the selector site that block uses. -/
theorem vkS1_arm_reverts {R : Render p G₁ G₂ Gₜ} {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmts (Bridge.Dialect c g) funs V st
        [Stmt.exprStmt (Expr.call "fail" [vkSite "ERR_VK_MISMATCH" R.consts])] V' st' o) :
    o = .halt ∧ Rev st' :=
  vk_arm_reverts hlookup (fun _ _ hh => vkSite_ne_halts hh) h

/-! ## 2. THE PEELS -/

/-- **S1.** Either the VK-presence guard fires and the run reverts, or the guard is skipped and
    the tail runs from the SAME environment (ifFalse leaves V alone) at some state. -/
theorem vkS1_peel (R : Render p G₁ G₂ Gₜ)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkS1 R.consts :: ss) Vb stb ob) :
    (ob = .halt ∧ Rev stb) ∨
      (∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts =>
            exact absurd (vkS1_arm_reverts (vkArm_fail_lookup hfail) hstmts).1
              (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
    | ifFalse _ _ => exact Or.inr ⟨st₁, hrest⟩
  · cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts => exact Or.inl (vkS1_arm_reverts (vkArm_fail_lookup hfail) hstmts)
    | ifHalt hc => exact (vkGuard_ne_halts hc).elim
    | ifFalse _ hz => exact absurd rfl hne

/-- **S2.** The copy cannot halt, and it leaves the environment alone (vk_extcodecopy_normal), so
    the tail runs from the SAME environment at some state. -/
theorem vkS2_peel (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkS2 R.consts :: ss) Vb stb ob) :
    ∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · exact ⟨st₁, by rw [vk_extcodecopy_normal h₁] at hrest; exact hrest⟩
  · cases h₁ with
    | exprStmtHalt hex => exact (vkS2_expr_ne_halts hex).elim
    | exprStmt _ => exact absurd rfl hne

/-- **One header cross-check on a poisoned boundary** (vk_poison_step at the vkHdr shape). -/
theorem vkHdr_poison (R : Render p G₁ G₂ Gₜ) (slot : String) (n : Nat) (succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (hsucc : VEnv.get V "success" = some (0 : U256))
    (hsite : ∀ {st₀ : EvmState} {av : U256} {st₁ : EvmState},
        EvalExpr (Bridge.Dialect c g) funs V st₀ succExpr (.vals [av] st₁) →
          VEnv.get V "success" = some av)
    (h : ExecStmt (Bridge.Dialect c g) funs V st (vkHdr slot n R.consts succExpr) V' st' .normal) :
    VEnv.get V' "success" = some (0 : U256) :=
  vk_poison_step hsucc hsite h

/-- **The peel of one poisoned cross-check.** The sequence cannot stop at an assign - none of the
    three sub-expressions halts - so the tail run exists and still carries the 0 bit. -/
theorem vk_hdr_tail (R : Render p G₁ G₂ Gₜ) (slot : String) (n : Nat) (succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hneS : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    (hsucc : VEnv.get V "success" = some (0 : U256))
    (hsite : ∀ {st₀ : EvmState} {av : U256} {st₁ : EvmState},
        EvalExpr (Bridge.Dialect c g) funs V st₀ succExpr (.vals [av] st₁) →
          VEnv.get V "success" = some av)
    (h : ExecStmts (Bridge.Dialect c g) funs V st
        (vkHdr slot n R.consts succExpr :: ss) Vb stb ob) :
    ∃ V₁ st₁, ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb ob ∧
      VEnv.get V₁ "success" = some (0 : U256) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · exact ⟨V₁, st₁, hrest, vkHdr_poison R slot n succExpr hsucc hsite h₁⟩
  · cases h₁ with
    | assignVal _ _ => exact absurd rfl hne
    | assignHalt he =>
        exact (vk_assign_nh hneS (fun _ _ hh => vk_mload_ne_halts slot hh)
          (fun _ _ hh => vkLit_ne_halts hh) he).elim

/-- **S9 / S13 on a poisoned boundary: the guard fires and the arm reverts.** -/
theorem vkS9_fires (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (hsucc : VEnv.get V "success" = some (0 : U256))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
          [Stmt.exprStmt (Expr.call "fail" [vkSite err R.consts])]) V' st' o) :
    o = .halt ∧ Rev st' :=
  vk_guard_fires hfail (fun _ _ _ hh => vkSite_ne_halts hh) hsucc h

/-! ## 3. CONJUNCT 2 - THE POISONED WALK -/

/-- The thirteen-statement walk itself, at an abstract scope that resolves fail. Statements S10-S13
    are never reached: S9 fires on the poisoned bit. -/
theorem vkBody_poison_walk (R : Render p G₁ G₂ Gₜ)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (hsucc : VEnv.get V "success" = some (0 : U256))
    {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome} {n k w o l b q : Nat}
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkBody R.consts n k w o l b q) Vb stb ob) :
    ob = .halt ∧ Rev stb := by
  rw [vkBody_nil] at h
  rcases vkS1_peel R hfail h with hrev | ⟨st₁, h₁⟩
  · exact hrev
  · obtain ⟨st₂, h₂⟩ := vkS2_peel R h₁
    obtain ⟨V₃, st₃, h₃, hs3⟩ :=
      vk_hdr_tail R "NUM_INSTANCES_MPTR" n (vkSucc0 R.consts)
        (fun _ _ hh => vkSucc_ne_halts hh) hsucc (fun hh => vkSucc0_hsite hh) h₂
    obtain ⟨V₄, st₄, h₄, hs4⟩ :=
      vk_hdr_tail R "K_MPTR" k vkSucc (fun _ _ hh => vkSucc2_ne_halts hh) hs3 (fun hh => vk_var_hsite hh) h₃
    obtain ⟨V₅, st₅, h₅, hs5⟩ :=
      vk_hdr_tail R "HAS_ACCUMULATOR_MPTR" w vkSucc (fun _ _ hh => vkSucc2_ne_halts hh) hs4
        (fun hh => vk_var_hsite hh) h₄
    obtain ⟨V₆, st₆, h₆, hs6⟩ :=
      vk_hdr_tail R "ACC_OFFSET_MPTR" o vkSucc (fun _ _ hh => vkSucc2_ne_halts hh) hs5
        (fun hh => vk_var_hsite hh) h₅
    obtain ⟨V₇, st₇, h₇, hs7⟩ :=
      vk_hdr_tail R "NUM_ACC_LIMBS_MPTR" l vkSucc (fun _ _ hh => vkSucc2_ne_halts hh) hs6
        (fun hh => vk_var_hsite hh) h₆
    obtain ⟨V₈, st₈, h₈, hs8⟩ :=
      vk_hdr_tail R "NUM_ACC_LIMB_BITS_MPTR" b vkSucc (fun _ _ hh => vkSucc2_ne_halts hh) hs7
        (fun hh => vk_var_hsite hh) h₇
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h₈ with ⟨_, _, h₉, _⟩ | ⟨h₉, _⟩
    · exact absurd (vkS9_fires R "ERR_VK_MISMATCH" hfail hs8 h₉).1
        (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
    · exact vkS9_fires R "ERR_VK_MISMATCH" hfail hs8 h₉

/-- **CONJUNCT 2 OF BlockSim R .vkLoading, THE POISONED WALK.** From a poisoned boundary EVERY run
    of the closed slice halts with a revert record: success is 0, and short-circuits on the bit, so
    all seven cross-checks leave it 0 and the guard after the sixth fires. The row's second conjunct
    also allows normal ∧ Poisoned; that arm is not reached, so the walk is stronger than the
    contract asks. -/
theorem vk_poison_walkV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hpois : Poisoned R H vkAddr cd V st)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Bridge.Dialect c g) (R.scope c g) V st (R.slice Partial.vkLoading) V' st' o) :
    o = .halt ∧ Rev st' := by
  rw [vk_sliceV3 R hR] at hrun
  have hfail : lookupFun (R.scope c g) "fail" = some (failFDecl, R.scope c g) := fail_lookup R
  have hbody_fail := vkBody_fail_lookup R R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
    R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
    R.pv.proofLayout.proofLen hfail
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | block hbody =>
        have hh := vkBody_poison_walk R hbody_fail hpois.2 hbody
        cases hnil
        exact absurd hh.1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  · cases h₁ with
    | block hbody => exact vkBody_poison_walk R hbody_fail hpois.2 hbody

#print axioms Midfall.LoweringV3.VkRow.vk_poison_walkV3
#print axioms Midfall.LoweringV3.VkRow.vkBody_poison_walk
#print axioms Midfall.LoweringV3.VkRow.vkS1_peel
#print axioms Midfall.LoweringV3.VkRow.vkS2_peel
#print axioms Midfall.LoweringV3.VkRow.vkS2_expr_ne_halts
#print axioms Midfall.LoweringV3.VkRow.vkS2_bi
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vkSite_ne_halts
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts
#print axioms Midfall.LoweringV2.Blocks.TraceReturn.trExprLit_ne_halts
#print axioms Midfall.LoweringV2.Blocks.TraceReturn.trExprVar_ne_halts
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vkSite_val
#print axioms Midfall.LoweringV3.VkRow.vk_hdr_tail
#print axioms Midfall.LoweringV3.VkRow.vkS9_fires
#print axioms Midfall.LoweringV3.VkRow.vk_sliceV3
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_poison_step
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_slice_raw
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_extcodecopy_normal
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_guard_fires
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_fail_reverts

/-! ## 4. THE PINS, DERIVED FROM ValidV3 (GEN.1 step 1, re-derived for the post-OBJ.8 text)

  GEN.1 was written when vkPins/vkProgressPins were clauses 12-13 of Render.Valid. They are not
  clauses (D-P67/OBJ.8), and OBJ.4 proved numInst and disjoint are not table facts.
  Instances/PoseidonValid.lean:843-860 names the three generic residuals and their owners. TWO of
  the three are one unfolding of generateVerifierFromPlan; the third is a layout card.

  THE GAP, EXACTLY. The clean half of vk_blockSim needs, for every R with ValidV3 R,

    ptrAddr R.pv.memory.g1IdentityMptr + 128 <= ptrAddr R.pv.memory.vkMptr OR
    ptrAddr R.pv.memory.vkMptr + R.pv.vk.len <= ptrAddr R.pv.memory.g1IdentityMptr

  from hR.supported.layout. It is TRUE of every valid render - both regions are allocated with
  MemoryLifetime.permanent (LayoutMemory.lean:191 vk_payload, :237 g1_identity) and
  memoryRegionsPairwiseDisjoint (Layout.lean:1100) forbids two permanent regions from overlapping -
  but NO lemma in the tree gets a NAMED PAIR out of that Bool. Doing it needs the region list of a
  GENERIC plan view: VerifierMemoryLayout.new (LayoutMemory.lean:139) is a thirty-allocation arena
  chain, and the g1_identity region is allocated at atTheta thetaWindows.g1IdentityWord rather than
  at ptrAddr g1IdentityMptr, so relating the two is a layout card, not a projection. OWNER: the
  WellFormed repair area (R.7's neighbours), exactly as PoseidonValid.lean:854 records. At the
  fixture the inequality is proved by native_decide (PoseidonValid.lean:909), which D-P71 forbids
  inside lowering_correct's cone, so the fixture proof is not a route either.
-/


/-! ## 4. THE CLEAN WALK: HELPERS -/

/-- Setting one variable leaves every OTHER binding alone: the VEnv fact the clean walk needs at
    every assign, so the frame's r and vk lookups survive all seven cross-checks. -/
theorem find?_set_success {V : VEnv (Bridge.Dialect c g)} {v : U256} {nm : Ident}
    (h : nm ≠ "success") :
    V.find? (fun q => decide (q.1 = nm)) =
      (VEnv.set V "success" v).find? (fun q => decide (q.1 = nm)) := by
  classical
  induction V with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk z w =>
          by_cases hz : z = "success"
          · subst hz
            simp only [VEnv.set, List.find?]
            split <;> simp_all
          · simp [VEnv.set, List.find?, hz, ← ih]

theorem set_success_other {V : VEnv (Bridge.Dialect c g)} {v : U256} {nm : Ident}
    (h : nm ≠ "success") :
    VEnv.get (VEnv.set V "success" v) nm = VEnv.get V nm := by
  classical
  simp only [VEnv.get]
  rw [← find?_set_success h]

/-- A bit is 0 or 1 (Midfall.Yul.VKP.IsBit), and a bitwise and of two bits is 1 only when both are. -/
theorem isBit_and_eq_one {x y : U256} (hx : Midfall.Yul.VKP.IsBit x) (hy : Midfall.Yul.VKP.IsBit y)
    (h : x &&& y = 1) : x = 1 ∧ y = 1 := by
  have key : ∀ (a b : U256), a = 0 ∨ a = 1 → b = 0 ∨ b = 1 → a &&& b = 1 → a = 1 ∧ b = 1 := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> intro hh
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact ⟨rfl, rfl⟩
  exact key x y hx hy h

/-- Reading a word that is 0 or 1: the and-chain keeps the bit. -/
theorem isBit_b2w (b : Bool) : Midfall.Yul.VKP.IsBit (b2w b) := by
  unfold Midfall.Yul.VKP.IsBit
  cases b <;> simp [b2w]

/-! ## 5. THE CLEAN WALK: VALUE EXTRACTION

  Three small inversions the clean walk needs and no existing file states at the shape it wants:
  the iszero guard's value, the eq builtin's value, and the recurring assign with its RESULT STATE
  as an index rather than a fresh existential (Blocks/VkLoading.lean:554 vk_assign_inv hides the
  state equation, which is what makes it awkward to chain).
-/

/-- The iszero(success) guard value, read off the step: b2w of the bit test on the binding. -/
theorem vk_iszero_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.iszero [vkSucc]) (.vals [cv] st₁)) :
    cv = b2w (decide (VEnv.get V "success" = (0 : U256))) := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hvar => cases hnil with
        | argsNil => cases hvar with
          | var hg =>
              simp only [builtinWithExternal, stepOp, un] at hbi
              cases hbi
              rw [hg]
              simp

/-- An eq step answers the bit of the equality of its two argument values, in the order the
    semantics imposes (argsCons takes the tail first, BigStep.lean:209): B from st, then A. -/
theorem vk_eq_val {A B : Expr EVM.Op}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.eq [A, B]) (.vals [cv] st₁)) :
    ∃ (av bv : U256) (st₀ st₂ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st B (.vals [bv] st₀)
      ∧ EvalExpr (Bridge.Dialect c g) funs V st₀ A (.vals [av] st₂)
      ∧ st₂ = st₁ ∧ cv = b2w (decide (av = bv)) := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hx => cases hrest with
        | argsCons hnil h2 => cases hnil with
          | argsNil =>
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, _, _, h2, hx, rfl, rfl⟩

/-- **The recurring assign, inverted with the RESULT STATE as an index.** -/
theorem vk_assign_inv2 {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {A B succExpr : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
          Expr.builtin Op.eq [A, B]])) V' st' .normal) :
    ∃ (yv xv : U256) (st₀ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin Op.eq [A, B]) (.vals [yv] st₀)
      ∧ EvalExpr (Bridge.Dialect c g) funs V st₀ succExpr (.vals [xv] st')
      ∧ V' = VEnv.set V "success" (xv &&& yv) := by
  cases h with
  | assignVal he hlen =>
      cases he with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hrest hx => cases hrest with
            | argsCons hnil h2 => cases hnil with
              | argsNil =>
                  simp only [builtinWithExternal, stepOp, bin] at hbi
                  cases hbi
                  exact ⟨_, _, _, h2, hx, rfl⟩

/-- A cross-check peeled on a NORMAL run: the tail runs from the updated environment, and the value
    it writes is (what succExpr read) and (the bit of the comparison). -/
theorem vk_hdr_bit (R : Render p G₁ G₂ Gₜ) (A B succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
            Expr.builtin Op.eq [A, B]]) :: ss) Vb stb .normal) :
    ∃ (x av bv : U256) (V₁ : VEnv (Bridge.Dialect c g)),
        V₁ = VEnv.set V "success" (x &&& b2w (decide (av = bv)))
      ∧ ∃ (st₁ st₂ : EvmState),
          ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb .normal
        ∧ EvalExpr (Bridge.Dialect c g) funs V st₂ succExpr (.vals [x] st₁) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · obtain ⟨yv, xv, st₀, heq, hxv, hV⟩ := vk_assign_inv2 h₁
    obtain ⟨av, bv, sta, stb', hbv, hav, hst, hyv⟩ := vk_eq_val heq
    subst hyv
    exact ⟨xv, av, bv, V₁, hV, st₁, st₀, hrest, hxv⟩
  · exact absurd rfl hne

/-- Reading a variable right after setting it, when it was bound: the last write wins. -/
theorem vk_get_set {V : VEnv (Bridge.Dialect c g)} {x : Ident} {w v : U256}
    (h : VEnv.get V x = some w) : VEnv.get (VEnv.set V x v) x = some v := by
  classical
  induction V with
  | nil => cases h
  | cons p rest ih =>
      cases p with
      | mk z u =>
          by_cases hz : z = x
          . subst hz
            simp [VEnv.get, VEnv.set]
          . rw [show VEnv.set ((z, u) :: rest) x v = (z, u) :: VEnv.set rest x v from
                  by simp [VEnv.set, hz]]
            simpa [VEnv.get, List.find?, hz] using ih (by
              have h2 : VEnv.get ((z, u) :: rest) x = some w := h
              simpa [VEnv.get, List.find?, hz] using h2)

/-! ## 6. THE CLEAN WALK - THE SUCCESS BIT SURVIVES ALL THIRTEEN STATEMENTS -/

/-- One clean cross-check: the tail runs from an environment whose success is STILL a bit. The
    comparison is never analysed - only the fact that this dialect answers eq with a bit, so the
    and-chain cannot leave {0,1}. -/
theorem vk_hdr_step (R : Render p G₁ G₂ Gₜ) (A B : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {s : U256} (hget : VEnv.get V "success" = some s)
    (hbit : Midfall.Yul.VKP.IsBit s)
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
            Expr.builtin Op.eq [A, B]]) :: ss) Vb stb .normal) :
    ∃ (V₁ : VEnv (Bridge.Dialect c g)) (s₁ : U256),
        (∃ st₁, ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb .normal)
      ∧ VEnv.get V₁ "success" = some s₁
      ∧ Midfall.Yul.VKP.IsBit s₁ := by
  obtain ⟨x, av, bv, V₁, hV, st₁, st₂, hrest, hxv⟩ := vk_hdr_bit R A B vkSucc h
  have hxs : x = s := Option.some.inj ((vk_var_hsite hxv).symm.trans hget)
  have hg1 : VEnv.get V₁ "success" = some (x &&& b2w (decide (av = bv))) :=
    hV ▸ vk_get_set hget
  have hb1 : Midfall.Yul.VKP.IsBit (x &&& b2w (decide (av = bv))) := by
    rw [hxs]
    exact Midfall.Yul.VKP.isBit_and_b2w _ hbit
  exact ⟨V₁, x &&& b2w (decide (av = bv)), ⟨st₁, hrest⟩, hg1, hb1⟩

/-- The guard iszero(success) SKIPPED (normal outcome, environment unchanged): the bit is 1. -/
theorem vkS9_skip (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {s : U256} (hget : VEnv.get V "success" = some s) (hbit : Midfall.Yul.VKP.IsBit s)
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
          [Stmt.exprStmt (Expr.call "fail" [vkSite err R.consts])]) V' st' .normal) :
    V' = V ∧ s = 1 := by
  cases h with
  | ifFalse hc hz =>
      refine ⟨rfl, ?_⟩
      have hv := vk_iszero_val hc
      rw [hv] at hz
      rw [hget] at hz
      rcases hbit with hs | hs
      · exact absurd hs (by
          intro hh
          rw [hh] at hz
          have hz' : (1 : U256) = (0 : U256) := hz
          exact absurd hz' (by decide))
      · exact hs
  | ifTrue _ _ hbody =>
      cases hbody with
      | block hstmts =>
          exact absurd (vk_arm_reverts (vkArm_fail_lookup hfail)
            (fun _ _ hh => vkSite_ne_halts hh) hstmts).1
            (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)

/-- **The clean walk's core.** From success = 1, every NORMAL run of the closed vkLoading body ends
    with success = 1: the three guards cannot have fired (their arms revert), and each of the nine
    cross-checks replaces the bit by (the bit) and (a bit), so the chain cannot leave {0,1} and the
    last skip forces it back to 1. No pin is needed for THIS fact - the pins are what turn it into
    StageInv .vk, and section 4 records why that part is blocked. -/
theorem vkBody_clean_success (R : Render p G₁ G₂ Gₜ)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (hsucc : VEnv.get V "success" = some (1 : U256))
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {n k w o l b q : Nat}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
        (vkBody R.consts n k w o l b q) V' st' .normal) :
    VEnv.get V' "success" = some (1 : U256) := by
  rw [vkBody_nil] at h
  rcases vkS1_peel R hfail h with ⟨ho, _⟩ | ⟨st₁, h₁⟩
  · exact absurd ho (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  · obtain ⟨st₂, h₂⟩ := vkS2_peel R h₁
    rw [show vkSucc0 R.consts = vkSucc from vkSucc0_var R] at h₂
    obtain ⟨V₃, s₃, ⟨st₃, h₃⟩, hg₃, hb₃⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "NUM_INSTANCES_MPTR" R.consts])
        (Expr.lit (.number n)) hsucc Midfall.Yul.VKP.isBit_one h₂
    obtain ⟨V₄, s₄, ⟨st₄, h₄⟩, hg₄, hb₄⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "K_MPTR" R.consts]) (Expr.lit (.number k))
        hg₃ hb₃ h₃
    obtain ⟨V₅, s₅, ⟨st₅, h₅⟩, hg₅, hb₅⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "HAS_ACCUMULATOR_MPTR" R.consts])
        (Expr.lit (.number w)) hg₄ hb₄ h₄
    obtain ⟨V₆, s₆, ⟨st₆, h₆⟩, hg₆, hb₆⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "ACC_OFFSET_MPTR" R.consts])
        (Expr.lit (.number o)) hg₅ hb₅ h₅
    obtain ⟨V₇, s₇, ⟨st₇, h₇⟩, hg₇, hb₇⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "NUM_ACC_LIMBS_MPTR" R.consts])
        (Expr.lit (.number l)) hg₆ hb₆ h₆
    obtain ⟨V₈, s₈, ⟨st₈, h₈⟩, hg₈, hb₈⟩ :=
      vk_hdr_step R (Expr.builtin Op.mload [vkSite "NUM_ACC_LIMB_BITS_MPTR" R.consts])
        (Expr.lit (.number b)) hg₇ hb₇ h₇
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h₈ with
        ⟨V₉, st₉, h₉, hrest₉⟩ | ⟨h₉, hne₉⟩
    · obtain ⟨hV₉, hs₉⟩ := vkS9_skip R "ERR_VK_MISMATCH" hg₈ hb₈ hfail h₉
      rw [hV₉] at hrest₉
      obtain ⟨V₁₀, s₁₀, ⟨st₁₀, h₁₀⟩, hg₁₀, hb₁₀⟩ :=
        vk_hdr_step R (Expr.lit (.number q))
          (Expr.builtin Op.calldataload [vkSite "PROOF_LEN_CPTR" R.consts]) hg₈ hb₈ hrest₉
      obtain ⟨V₁₁, s₁₁, ⟨st₁₁, h₁₁⟩, hg₁₁, hb₁₁⟩ :=
        vk_hdr_step R (Expr.lit (.number n))
          (Expr.builtin Op.calldataload [vkSite "NUM_INSTANCE_CPTR" R.consts]) hg₁₀ hb₁₀ h₁₀
      obtain ⟨V₁₂, s₁₂, ⟨st₁₂, h₁₂⟩, hg₁₂, hb₁₂⟩ :=
        vk_hdr_step R (Expr.builtin Op.calldatasize [])
          (Expr.builtin Op.add [vkSite "INSTANCE_CPTR" R.consts, Expr.lit (.number (n * 32))])
          hg₁₁ hb₁₁ h₁₁
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h₁₂ with
          ⟨V₁₃, st₁₃, h₁₃, hnil⟩ | ⟨h₁₃, hne₁₃⟩
      · obtain ⟨hV₁₃, hs₁₃⟩ :=
          vkS9_skip R "ERR_BAD_CALLDATA_SHAPE" hg₁₂ hb₁₂ hfail h₁₃
        cases hnil
        rw [hV₁₃, ← hs₁₃]
        exact hg₁₂
      · exact absurd rfl hne₁₃
    · exact absurd rfl hne₉

#print axioms Midfall.LoweringV3.VkRow.vkBody_clean_success
#print axioms Midfall.LoweringV3.VkRow.vk_poison_walkV3

/-! ## 7. THE STATE TRANSFER: WHAT THE SLICE DOES AND DOES NOT TOUCH

  Every builtin this slice reads leaves the environment record, the halt record and memory exactly
  alone; the mload and calldataload reads move only the active-word high-water mark
  (touchMemory_proj); and the single write is the extcodecopy, whose effect is the copyInto window.
  That is the whole of the Frame transfer and of the memory half of Inv .vk, and it needs no pin.
-/

/-- touchMemory moves activeWords and nothing else. -/
theorem touchMemory_proj (st : EvmState) (o n : Nat) :
    (touchMemory st o n).env = st.env ∧ (touchMemory st o n).halted = st.halted ∧
      (touchMemory st o n).memory = st.memory :=
  ⟨rfl, rfl, rfl⟩

/-- mload touches the word window and nothing else. -/
theorem vk_st_mload {a : U256} {st st₂ : EvmState} {rets : List U256}
    (h : (Bridge.Dialect c g).Builtin Op.mload [a] st (.ok rets st₂)) :
    st₂.env = st.env ∧ st₂.halted = st.halted ∧ st₂.memory = st.memory := by
  simp only [builtinWithExternal, stepOp] at h
  cases h
  exact touchMemory_proj _ _ _

/-- calldataload reads calldata and changes no state at all. -/
theorem vk_st_calldataload {a : U256} {st st₂ : EvmState} {rets : List U256}
    (h : (Bridge.Dialect c g).Builtin Op.calldataload [a] st (.ok rets st₂)) :
    st₂.env = st.env ∧ st₂.halted = st.halted ∧ st₂.memory = st.memory := by
  simp only [builtinWithExternal, stepOp, rd1] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- calldatasize and the two extcode reads: no state change. -/
theorem vk_st_rd1 {op : EVM.Op} (hop : op = Op.calldatasize \/ op = Op.extcodesize \/
      op = Op.extcodehash) {a : U256} {st st₂ : EvmState} {rets : List U256}
    (h : (Bridge.Dialect c g).Builtin op [a] st (.ok rets st₂)) :
    st₂.env = st.env ∧ st₂.halted = st.halted ∧ st₂.memory = st.memory := by
  rcases hop with rfl | rfl | rfl
  · simp only [builtinWithExternal, stepOp, rd0] at h; cases h <;> (try exact ⟨rfl, rfl, rfl⟩)
  · simp only [builtinWithExternal, stepOp, rd1] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  · simp only [builtinWithExternal, stepOp, rd1] at h; cases h; exact ⟨rfl, rfl, rfl⟩

theorem vk_st_pure1 {op : EVM.Op} (hop : op = Op.iszero) {a : U256} {st st₂ : EvmState}
    {rets : List U256} (h : (Bridge.Dialect c g).Builtin op [a] st (.ok rets st₂)) :
    st₂.env = st.env ∧ st₂.halted = st.halted ∧ st₂.memory = st.memory := by
  subst hop
  simp only [builtinWithExternal, stepOp, un] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem vk_st_pure2 {op : EVM.Op} (hop : op = Op.eq \/ op = Op.and \/ op = Op.add)
    {a b : U256} {st st₂ : EvmState} {rets : List U256}
    (h : (Bridge.Dialect c g).Builtin op [a, b] st (.ok rets st₂)) :
    st₂.env = st.env ∧ st₂.halted = st.halted ∧ st₂.memory = st.memory := by
  rcases hop with rfl | rfl | rfl
  all_goals
    simp only [builtinWithExternal, stepOp, bin] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-- **The extcodecopy step, memory half.** The window the block writes, read off the run at a
    render's table: the four argument sites are pure reads, so the state the copy starts from has
    the same memory as the state the statement started from, and the copy touches neither env nor
    the halt record. -/
theorem vkS2_memory {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (vkS2 R.consts) V st' .normal) :
    st'.env = st.env ∧ st'.halted = st.halted ∧
      ∃ (dst src n : Nat) (code : List UInt8), st'.memory = copyInto st.memory dst src n code := by
  cases h with
  | exprStmt hex =>
      cases hex with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hrest hx => cases hrest with
            | argsCons hrest2 h2 => cases hrest2 with
              | argsCons hrest3 h3 => cases hrest3 with
                | argsCons hnil h4 => cases hnil with
                  | argsNil =>
                      obtain ⟨_, he4⟩ := vkSite_val h4
                      subst he4
                      cases h3 with
                      | lit =>
                          obtain ⟨_, he2⟩ := vkSite_val h2
                          subst he2
                          obtain ⟨_, hex⟩ := vkSite_val hx
                          subst hex
                          simp only [builtinWithExternal, stepOp] at hbi
                          cases hbi
                          exact ⟨rfl, rfl, _, _, _, _, rfl⟩

end Midfall.LoweringV3.VkRow

