/-
  Midfall.LoweringV2.Blocks.VkLoading

  S.4 (SEM / PROOF): the `vkLoading` row of §6's per-block contract table - the FIRST of the four
  rows S.1 identified as required and 1 of the 6 the hinge needs.

  WHAT THIS IS WORTH, STATED PLAINLY. `slices_seq_sound` / `slices_seq_progress`
  (Blocks.lean:307, :325) consume `∀ q : Partial, BlockSound R q ...` over all SEVEN slices and
  `Render.slices` concatenates seven slices, so ONE row discharges nothing:
  `cone_sorries lowering_equivalence_poseidon` does not move (measured 11 before, 11 after) and
  cannot move until all six non-quotient rows exist. This card does not dress that up.

  THE BLOCK, AS READ OFF THE EMITTER (a reading of the statement order, not a proved fact - the
  walks that would establish it are named in §6). `R.slice .vkLoading` is ONE top-level statement -
  a `Stmt.block` of THIRTEEN (M0.1's "1 statement" is the top-level count). It reads `vk` and
  `success`, writes only `success`, and copies the deployed VK runtime into memory with
  `extcodecopy`. Nine statements are `success := and(success, eq(...))` and three are
  `if iszero(...) { fail(...) }`. M0.1's note that the nine guards let `success` reach 0 is right,
  and the ordering says more: every group of `and`-guards is immediately followed by an
  `iszero(success)` check that calls `fail`. On the reading that ordering gives, (i) a NORMAL exit
  has `success = 1`, so the clean walk should not need the `normal ∧ Poisoned` arm, and (ii) from a
  POISONED boundary `success` stays 0 through all nine guards (`and` short-circuits on the bit -
  that half IS proved, §4 `vk_poison_step`) and the second check always fires, so every run should
  revert and the poisoned arm of conjunct 2 is not reached either. The S.3 gate (poisoned arms
  offered iff `q ≠ .traceReturn`) is therefore satisfied by construction and, on this reading, not
  needed; the gate is not fought anywhere in this file.

  PREMISE GAP FOUND - `vkPins` (§5) - CLOSED BY D-P50/S.9: the six clauses are now
  `Render.Valid` clauses 12-13 (`Statements.lean` §2, FROZEN, re-hashed in the same commit) and S.8
  PROVED all six at the deployment sorry-free, so `vk_blockRow` takes no pin hypothesis. The finding
  is kept verbatim below and in §5 because it is WHY the frozen edit was needed.

  `Clean R .vk` postulates `Inv .vk`, whose first clause pins
  MEMORY AT `PV.memory.vkMptr` TO `PV.vk.bytes`. The block writes to the inlined `VK_MPTR` constant
  and copies `EXPECTED_VK_PAYLOAD_LENGTH` bytes from byte 1 of `extCodeOf vk`. THE LINK THE BRIEF
  ASKED ABOUT HOLDS: `Frame.vkCode` (Blocks.lean:61) is exactly `extCodeOf vkAddr =
  R.plan.vk.runtimeBytes.data.toList`, `Frame.vk` pins the `vk` local to `vkAddr`, and §4's
  `vk_extcodecopy_normal` shows the copy leaves `st.env` and the halt record alone - so the
  `extcodecopy` source IS the deployed runtime and `Frame.vkCode` CONNECTS. What nothing in
  `Frame`/`Clean`/`Inv`/`Valid` supplies is that the render's CONSTANT TABLE agrees with its own
  PLAN VIEW about where that window is, how long the payload is, and how many instances the
  calldata carries - plus a layout disjointness fact. Those four are `vkPins`. Each is a computation
  at a real deployment, not a free hypothesis - the same shape as T.1's `trRetMptr` and FP.0's
  `fpG2Slots`, and `Valid.slots` is `EnvAgrees`, whose eleven fields are field-constant facts
  (Inv.lean:533-579) and none of them mentions VK_MPTR. Without them `BlockSound R .vkLoading` is
  FALSE, not merely unproved: a render whose table points VK_MPTR elsewhere copies the payload to
  the wrong address, exits `normal` with `success = 1`, and satisfies neither `Clean .vk` nor
  `Poisoned`. That is a §6-shape question for the orchestrator, not a proof obligation of this card.

  TWO TRAPS THE BRIEF NAMED, BOTH HIT. (i) The slice does not reduce by `simp`/`unfold`: §1 is the
  `show` + `rfl`-against-stuck-sites route, and it needed one refinement T.1 did not - the inliner's
  SHADOW LIST. `boundOf (Stmt.assign ["success"] _) = ["success"]` (InlineConstants.lean:262), so
  from the fourth statement onward `success` is shadowed and stays a raw variable while in the third
  it is still a stuck `lookup`. One uniform site for all ten occurrences is NOT definitional
  (measured: the single-site version fails `rfl`); §1 states the site per position, and the walk
  reads each through `vkVal` rather than rewriting it away. (ii) `classical` appears only inside
  inversions of an existing run hypothesis, never before a forward `Step` construction.

  WHAT IS PROVED AND WHAT IS NAMED - read this before citing anything below as a result. PROVED,
  sorry-free: §1 the slice in statement-list form; §2 the site value inversion, the site
  non-halting, the VK guard's non-halting and the four total local reads of §4; §3 the fail helper
  at an ARBITRARY selector site (T.1's S6 was pinned to ERR_PROOF_REJECTED; this block calls fail
  at three sites with two selectors) and the guard-fires dual of `tr_guard_skip`; §4 the recurring
  assign inversion, the assign non-halting, the extcodecopy step, the poisoned assign step and the
  `VEnv` set/get fact that no existing layer states. NAMED WITH A SORRY, §6: `vk_sound_clean`
  (BlockSound conjunct 1), `vk_poison_walk` (conjunct 2) and `vk_progress` (BlockProgress).
  `vk_blockRow` is the sorry-free RE-ASSEMBLY of those three, so THE ROW IS NOT CLOSED:
  `#cone_sorries vk_blockRow` prints 3 and it depends on sorryAx. Nothing here is called proved
  that is not.

  THREE `sorry` IN THIS FILE, ALL IN §6, ALL NAMED ABOVE.
-/
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Blocks.TraceReturn

namespace Midfall.LoweringV2.Blocks.VkLoading

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2
open Midfall.LoweringV2.Blocks.TraceReturn

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
  {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. INTERFACE STEP 1 (T.1's S1): the slice in statement-list form -/

/-- A constant use site as the inliner leaves it where nothing shadows it: the table's literal if
    the table binds the name, the free variable if it does not. -/
def vkSite (x : String) (consts : Inline.Consts) : Expr EVM.Op :=
  match consts.lookup x with
  | some v => Expr.lit (.number v)
  | none => Expr.var x

/-- The `vk` occurrence of the first two statements: unshadowed, so a stuck site. -/
def vkVk0 (consts : Inline.Consts) : Expr EVM.Op := vkSite "vk" consts

/-- The `success` occurrence inside the FIRST assign's right-hand side: unshadowed there, because
    `inlineStmtStep` threads `boundOf` only for the statements that FOLLOW. -/
def vkSucc0 (consts : Inline.Consts) : Expr EVM.Op := vkSite "success" consts

/-- `success` from the second assign onward: shadowed by the first, so a raw variable at every
    render whatever the table says. -/
def vkSucc : Expr EVM.Op := Expr.var "success"

/-- The VK-presence guard. -/
def vkGuard (consts : Inline.Consts) : Expr EVM.Op :=
  Expr.builtin Op.iszero [Expr.builtin Op.and
    [Expr.builtin Op.eq [Expr.builtin Op.extcodesize [vkVk0 consts],
                         vkSite "EXPECTED_VK_LENGTH" consts],
     Expr.builtin Op.eq [Expr.builtin Op.extcodehash [vkVk0 consts],
                         vkSite "EXPECTED_VK_CODEHASH_WORD" consts]]]

/-- One of the six header cross-checks: `success := and(success, eq(mload(SLOT), lit n))`. -/
def vkHdr (slot : String) (n : Nat) (consts : Inline.Consts) (succ : Expr EVM.Op) :
    Stmt EVM.Op :=
  Stmt.assign ["success"] (Expr.builtin Op.and [succ,
    Expr.builtin Op.eq [Expr.builtin Op.mload [vkSite slot consts], Expr.lit (.number n)]])

/-- The thirteen statements, by position. -/
def vkS1 (consts : Inline.Consts) : Stmt EVM.Op :=
  Stmt.cond (vkGuard consts) [Stmt.exprStmt (Expr.call "fail" [vkSite "ERR_VK_MISMATCH" consts])]
def vkS2 (consts : Inline.Consts) : Stmt EVM.Op :=
  Stmt.exprStmt (Expr.builtin Op.extcodecopy [vkVk0 consts, vkSite "VK_MPTR" consts,
    Expr.lit (.number 1), vkSite "EXPECTED_VK_PAYLOAD_LENGTH" consts])
def vkS9 (consts : Inline.Consts) : Stmt EVM.Op :=
  Stmt.cond (Expr.builtin Op.iszero [vkSucc])
    [Stmt.exprStmt (Expr.call "fail" [vkSite "ERR_VK_MISMATCH" consts])]
def vkS10 (consts : Inline.Consts) (p : Nat) : Stmt EVM.Op :=
  Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
    Expr.builtin Op.eq [Expr.lit (.number p),
      Expr.builtin Op.calldataload [vkSite "PROOF_LEN_CPTR" consts]]])
def vkS11 (consts : Inline.Consts) (n : Nat) : Stmt EVM.Op :=
  Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
    Expr.builtin Op.eq [Expr.lit (.number n),
      Expr.builtin Op.calldataload [vkSite "NUM_INSTANCE_CPTR" consts]]])
def vkS12 (consts : Inline.Consts) (n : Nat) : Stmt EVM.Op :=
  Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
    Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
      Expr.builtin Op.add [vkSite "INSTANCE_CPTR" consts,
        Expr.lit (.number (n * 32))]]])
def vkS13 (consts : Inline.Consts) : Stmt EVM.Op :=
  Stmt.cond (Expr.builtin Op.iszero [vkSucc])
    [Stmt.exprStmt (Expr.call "fail" [vkSite "ERR_BAD_CALLDATA_SHAPE" consts])]

/-- The thirteen-statement body, at the NO-ACCUMULATOR arm - the only arm a `Valid` render emits
    (`SupportedV2.noAcc`, consumed by `pv_hasAcc_false`). -/
def vkBody (consts : Inline.Consts) (n k w o l b q : Nat) : List (Stmt EVM.Op) :=
  [ vkS1 consts, vkS2 consts,
    vkHdr "NUM_INSTANCES_MPTR" n consts (vkSucc0 consts),
    vkHdr "K_MPTR" k consts vkSucc,
    vkHdr "HAS_ACCUMULATOR_MPTR" w consts vkSucc,
    vkHdr "ACC_OFFSET_MPTR" o consts vkSucc,
    vkHdr "NUM_ACC_LIMBS_MPTR" l consts vkSucc,
    vkHdr "NUM_ACC_LIMB_BITS_MPTR" b consts vkSucc,
    vkS9 consts, vkS10 consts q, vkS11 consts n, vkS12 consts n, vkS13 consts ]

/-- The fold at a symbolic table: the `rfl` the `simp`/`unfold` route cannot reach (T.1's finding),
    with every stuck site named by a def above. -/
theorem vk_slice_raw (consts : Inline.Consts) (n k w o l b q : Nat) :
    Inline.inlineContractConstants consts (GenAst.emitVkLoadingArms false n k w o l b q)
      = [Stmt.block (vkBody consts n k w o l b q)] := rfl

/-- `constTableOf` filters exactly `vk` and `success` out of every render's table
    (Program.lean:60), so both stuck sites reduce to the variable. -/
theorem consts_vk_none (R : Render p G₁ G₂ Gₜ) : R.consts.lookup "vk" = none :=
  lookup_none_of_ne "vk" _ (by
    intro x hx
    rcases List.mem_filter.mp hx with ⟨_, h2⟩
    simp at h2
    exact h2.1)

/-- The plan view of a `Valid` render carries no accumulator. -/
theorem pv_hasAcc_false (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    R.pv.hasAccumulator = false := by
  classical
  have h : R.cfg.accumulator = none := hR.supported.noAcc
  have h1 : R.pv = planViewOf R.plan R.model none := by
    show planViewOf R.plan R.model R.cfg.accumulator = _
    rw [h]
  rw [h1, planViewOf, planViewWithAccumulator]
  rfl

/-- **S1 FOR `vkLoading`:** the closed slice is one `Stmt.block` of thirteen statements. -/
theorem vk_slice (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    R.slice Partial.vkLoading =
      [Stmt.block (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
        R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
        R.pv.proofLayout.proofLen)] := by
  have hacc : R.pv.hasAccumulator = false := pv_hasAcc_false R hR
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.vkLoading) = _
  rw [GenAst.emitPartial, GenAst.emitVkLoading, hacc, vk_slice_raw]

/-- The two filtered names: at a render's table the stuck sites ARE the variables. -/
theorem vkVk0_var (R : Render p G₁ G₂ Gₜ) : vkVk0 R.consts = Expr.var "vk" := by
  show vkSite "vk" R.consts = _
  simp [vkSite, consts_vk_none R]

theorem vkSucc0_var (R : Render p G₁ G₂ Gₜ) : vkSucc0 R.consts = Expr.var "success" := by
  show vkSite "success" R.consts = _
  simp [vkSite, consts_succ_none R]

/-! ## 2. THE SITES: value inversion and non-halting -/

/-- The value an inlined site carries at an environment: the table's word where the table binds the
    name, otherwise whatever the caller's `VEnv` binds. Reading it off the run rather than assuming
    it is what keeps the soundness halves free of a table hypothesis (T.1's asymmetry). -/
def vkVal (x : String) (R : Render p G₁ G₂ Gₜ) (V : VEnv (Bridge.Dialect c g)) : Option U256 :=
  match R.consts.lookup x with
  | some v => some (BitVec.ofNat 256 v)
  | none => VEnv.get V x

/-- A site evaluates to exactly one word at an unchanged state, and that word is `vkVal`. -/
theorem vkSite_val {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState} {x : String} {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (vkSite x R.consts) (.vals [a] st₂)) :
    vkVal x R V = some a ∧ st₂ = st := by
  classical
  cases hmv : R.consts.lookup x with
  | some v =>
      rw [show vkSite x R.consts = Expr.lit (.number v) from by simp [vkSite, hmv]] at h
      cases h with
      | lit => refine ⟨by rw [vkVal, hmv, tr_lit_number], rfl⟩
  | none =>
      rw [show vkSite x R.consts = Expr.var x from by simp [vkSite, hmv]] at h
      cases h with
      | var hget => refine ⟨by simpa [vkVal, hmv] using hget, rfl⟩

/-- A site never halts: a literal and a bound variable are both value steps, and an UNBOUND
    variable is stuck rather than halted. -/
theorem vkSite_ne_halts {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState} {x : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (vkSite x R.consts) (.halt st₂)) : False := by
  classical
  cases hmv : R.consts.lookup x with
  | some v =>
      rw [show vkSite x R.consts = Expr.lit (.number v) from by simp [vkSite, hmv]] at h
      exact trExprLit_ne_halts h
  | none =>
      rw [show vkSite x R.consts = Expr.var x from by simp [vkSite, hmv]] at h
      exact trExprVar_ne_halts h

/-- A raw variable occurrence never halts (stuck when unbound). -/
theorem vkVar_ne_halts {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₂ : EvmState} {x : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.halt st₂)) : False :=
  trExprVar_ne_halts h

/-- A literal never halts. -/
theorem vkLit_ne_halts {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₂ : EvmState} {n : Nat}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n)) (.halt st₂)) : False :=
  trExprLit_ne_halts h

/-- **A ONE-ARGUMENT LOCAL BUILTIN NEVER HALTS** provided its argument does not and its builtin
    relation always answers '.ok'. Every unary read this slice's guard uses is of that shape. The
    'hop' hypothesis is discharged at each USE site by simp: it cannot be discharged once for all
    inside this lemma, because 'op' is a variable there and 'builtinWithExternal' matches on it. -/
theorem vk_nh_unary {op : EVM.Op}
    (hop : ∀ (a : U256) (st : EvmState) (r : BuiltinResult U256 EvmState),
        (Bridge.Dialect c g).Builtin op [a] st r →
          ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState}
    {e : Expr EVM.Op}
    (hne : ∀ (st₁ st₃ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₃) → False)
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op [e]) (.halt st₂)) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil he =>
          cases hnil with
          | argsNil =>
              obtain ⟨_, _, hr⟩ := hop _ _ _ hbi
              cases hr
  | builtinArgsHalt hargs =>
      exact (trArgs1_halt_inv hargs (fun st₁ hh => hne st₁ st₂ hh)).elim

/-- The two-argument case of the same argument. -/
theorem vk_nh_binary {op : EVM.Op}
    (hop : ∀ (a b : U256) (st : EvmState) (r : BuiltinResult U256 EvmState),
        (Bridge.Dialect c g).Builtin op [a, b] st r →
          ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState}
    {a b : Expr EVM.Op}
    (hne : ∀ (st₁ st₃ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ a (.halt st₃) → False)
    (hne' : ∀ (st₁ st₃ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ b (.halt st₃) → False)
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op [a, b]) (.halt st₂)) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest he =>
          cases hrest with
          | argsCons hnil h2 =>
              cases hnil with
              | argsNil =>
                  obtain ⟨_, _, hr⟩ := hop _ _ _ _ hbi
                  cases hr
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h' =>
          exact (trArgs1_halt_inv h' (fun st₁ hb => hne' st₁ st₂ hb)).elim
      | argsHeadHalt _ h' => exact hne _ _ h'

/-- The nullary case: a total read of the environment with no argument to halt in. -/
theorem vk_nh_nullary {op : EVM.Op}
    (hop : ∀ (st : EvmState) (r : BuiltinResult U256 EvmState),
        (Bridge.Dialect c g).Builtin op [] st r →
          ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op []) (.halt st₂)) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsNil =>
          obtain ⟨_, _, hr⟩ := hop _ _ hbi
          cases hr
  | builtinArgsHalt hargs => cases hargs

/-- The five local reads the VK guard is built from answer '.ok' unconditionally, so a halt can only
    come from an argument. Each is three lines: reduce the relation to 'stepOp', which is a function
    into '.ok', and read the equation back. -/
theorem vk_ok_extcodesize {a : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.extcodesize [a] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, rd1] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_extcodehash {a : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.extcodehash [a] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, rd1] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_eq {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.eq [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, bin] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_and {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.and [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, bin] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_iszero {a : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.iszero [a] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, un] at h
  cases h
  exact ⟨_, _, rfl⟩

/-- The VK guard cannot halt: five total local reads over three sites that cannot halt. -/
theorem vkGuard_ne_halts {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (vkGuard R.consts) (.halt st₂)) : False := by
  have hcs : ∀ st₁ st₃ : EvmState,
      EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.extcodesize [vkVk0 R.consts]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    refine vk_nh_unary (op := Op.extcodesize) (fun _ _ _ h' => vk_ok_extcodesize h') ?_ hh
    intro a b hb
    exact vkSite_ne_halts hb
  have hch : ∀ st₁ st₃ : EvmState,
      EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.extcodehash [vkVk0 R.consts]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    refine vk_nh_unary (op := Op.extcodehash) (fun _ _ _ h' => vk_ok_extcodehash h') ?_ hh
    intro a b hb
    exact vkSite_ne_halts hb
  have he1 : ∀ st₁ st₃ : EvmState,
      EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.eq [Expr.builtin Op.extcodesize [vkVk0 R.consts],
          vkSite "EXPECTED_VK_LENGTH" R.consts]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    refine vk_nh_binary (op := Op.eq) (fun _ _ _ _ h' => vk_ok_eq h') hcs ?_ hh
    intro a b hb
    exact vkSite_ne_halts hb
  have he2 : ∀ st₁ st₃ : EvmState,
      EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.eq [Expr.builtin Op.extcodehash [vkVk0 R.consts],
          vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    refine vk_nh_binary (op := Op.eq) (fun _ _ _ _ h' => vk_ok_eq h') hch ?_ hh
    intro a b hb
    exact vkSite_ne_halts hb
  have hand : ∀ st₁ st₃ : EvmState,
      EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.and [Expr.builtin Op.eq
            [Expr.builtin Op.extcodesize [vkVk0 R.consts],
             vkSite "EXPECTED_VK_LENGTH" R.consts],
         Expr.builtin Op.eq [Expr.builtin Op.extcodehash [vkVk0 R.consts],
             vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    refine vk_nh_binary (op := Op.and) (fun _ _ _ _ h' => vk_ok_and h') he1 he2 hh
  exact vk_nh_unary (op := Op.iszero) (fun _ _ _ h' => vk_ok_iszero h')
    (fun st₁ st₃ hh => hand st₁ st₃ hh) h

/-! ## 3. THE `fail` HELPER AT AN ARBITRARY SELECTOR SITE

  T.1's S6 is stated at ERR_PROOF_REJECTED. `vkLoading` calls `fail` at THREE sites with TWO
  different selectors, so the same three facts are restated with the selector left abstract: only
  its NON-HALTING is used, never its value - which is what T.1's §3 header already observed and what
  makes the generalisation free. -/

/-- The call inversion at an abstract selector site. -/
theorem vk_fail_expr {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {r : EResult (Bridge.Dialect c g)}
    {e : Expr EVM.Op}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (hne : ∀ (st₁ st₂ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₂) → False)
    (h : Step (Bridge.Dialect c g) funs V st (Code.expr (Expr.call "fail" [e])) (Res.eres r)) :
    ∃ st₂, r = .halt st₂ ∧ Reverted st₂ := by
  cases h with
  | callOk hargs hlookup' hlen hbody ho =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          obtain ⟨ho', hrev⟩ := tr_fail_body hstmts
          cases ho with
          | inl hn =>
              exact absurd (hn.symm.trans ho')
                (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
          | inr hl =>
              exact absurd (hl.symm.trans ho')
                (by decide : (Outcome.leave : Outcome) ≠ Outcome.halt)
  | callHalt hargs hlookup' hlen hbody =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts => exact ⟨_, rfl, (tr_fail_body hstmts).2⟩
  | callArgsHalt hargs =>
      exact (trArgs1_halt_inv hargs (fun st₁ hh => hne st₁ _ hh)).elim

/-- A run of `fail(<site>)` in any scope stack that resolves `fail` to the helper halts reverted. -/
theorem vk_fail_reverts {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {e : Expr EVM.Op}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (hne : ∀ (st₁ st₂ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ e (.halt st₂) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.exprStmt (Expr.call "fail" [e])) V' st' o) :
    o = .halt ∧ Reverted st' := by
  cases h with
  | exprStmt hex =>
      obtain ⟨st₂, hr, hrev⟩ := vk_fail_expr hlookup hne hex
      exact absurd hr (by simp)
  | exprStmtHalt hex =>
      obtain ⟨st₂, hr, hrev⟩ := vk_fail_expr hlookup hne hex
      cases hr
      exact ⟨rfl, hrev⟩

/-- **THE GUARD FIRES, AT AN ARBITRARY SELECTOR SITE.** The dual of `tr_guard_skip`, which this
    file reuses verbatim for the two `iszero(success)` checks on the clean path. -/
theorem vk_guard_fires {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {e : Expr EVM.Op}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (hne : ∀ (fs : FunEnv (Bridge.Dialect c g)) (st₁ st₂ : EvmState),
      EvalExpr (Bridge.Dialect c g) fs V st₁ e (.halt st₂) → False)
    (hs : VEnv.get V "success" = some (0 : U256))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
          [Stmt.exprStmt (Expr.call "fail" [e])]) V' st' o) :
    o = .halt ∧ Reverted st' := by
  have hnz1 : ¬((1 : U256) = (Bridge.Dialect c g).zero) := by
    show (1 : U256) ≠ 0
    decide
  cases h with
  | ifTrue hc hnz hbody =>
      have h1 := tr_iszero_zero hs hc
      cases h1
      cases hbody with
      | block hstmts =>
          have hl : lookupFun
              (hoist (Bridge.Dialect c g)
                [Stmt.exprStmt (Expr.call "fail" [e])] :: funs) "fail" =
              some (failFDecl, funs') := by
            show lookupFun funs "fail" = some (failFDecl, funs')
            exact hlookup
          have hne2 : ∀ (st₁ st₂ : EvmState),
              EvalExpr (Bridge.Dialect c g)
                (hoist (Bridge.Dialect c g) [Stmt.exprStmt (Expr.call "fail" [e])] :: funs)
                  V st₁ e (.halt st₂) → False :=
            fun st₁ st₂ hh => hne _ st₁ st₂ hh
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hstmts with
              ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne'⟩
          · exact absurd (vk_fail_reverts hl hne2 h₁).1
              (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
          · exact vk_fail_reverts hl hne2 h₁
  | ifFalse hc hz =>
      have h1 := tr_iszero_zero hs hc
      cases h1
      exact absurd hz hnz1
  | ifHalt hc =>
      have h1 := tr_iszero_zero hs hc
      cases h1
/-! ## 4. THE TWO STATEMENT SHAPES THIS SLICE ADDS TO THE INTERFACE

  T.1's S4 covered a word store. vkLoading adds an extcodecopy and the recurring
  success := and(success, eq(A, B)), each stated general in its argument expressions so the ten
  use sites share one lemma. Note the evaluation ORDER the semantics imposes (argsCons takes the
  tail first, BigStep.lean:209): in and [succExpr, eq [A, B]] the comparison is evaluated before
  success, and inside eq [A, B] the second argument is evaluated first. -/

abbrev Dperm (product : PairingProduct) (g : ExternalGas) :=
  Bridge.Dialect (permissive (callsOf product)) g

/-- The four remaining local reads of this slice answer .ok unconditionally. -/
theorem vk_ok_mload {a : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.mload [a] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_calldataload {a : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.calldataload [a] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, rd1] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_calldatasize {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.calldatasize [] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, rd0] at h
  cases h
  exact ⟨_, _, rfl⟩

theorem vk_ok_add {a b : U256} {st : EvmState} {r : BuiltinResult U256 EvmState}
    (h : (Bridge.Dialect c g).Builtin Op.add [a, b] st r) :
    ∃ (rets : List U256) (st₂ : EvmState), r = .ok rets st₂ := by
  simp only [builtinWithExternal, stepOp, bin] at h
  cases h
  exact ⟨_, _, rfl⟩

/-- **THE RECURRING ASSIGN, INVERTED.** success := and(succExpr, eq(A, B)) at a normal outcome:
    the comparison value, the succExpr value, and the environment rewrite. Nothing else is forced,
    which is what lets the nine guards share one lemma - and what makes the POISONED path need no
    value analysis at all (0 &&& x = 0 for every x). -/
theorem vk_assign_inv {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {A B succExpr : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
          Expr.builtin Op.eq [A, B]])) V' st' .normal) :
    ∃ (yv xv : U256) (st₁ st₂ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.eq [A, B]) (.vals [yv] st₁) ∧
      EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.vals [xv] st₂) ∧
      V' = VEnv.set V "success" (xv &&& yv) := by
  cases h with
  | assignVal he hlen =>
      cases he with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hrest hx =>
              cases hrest with
              | argsCons hnil h2 =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, bin] at hbi
                      cases hbi
                      exact ⟨_, _, _, _, h2, hx, rfl⟩

/-- The assign expression cannot halt, given its three leaves cannot. -/
theorem vk_assign_nh {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₂ : EvmState} {A B succExpr : Expr EVM.Op}
    (hne1 : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    (hne2 : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ A (.halt st₃) → False)
    (hne3 : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ B (.halt st₃) → False)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.and [succExpr, Expr.builtin Op.eq [A, B]]) (.halt st₂)) : False := by
  have heq : ∀ (st₁ st₃ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ (Expr.builtin Op.eq [A, B]) (.halt st₃) → False := by
    intro st₁ st₃ hh
    exact vk_nh_binary (op := Op.eq) (fun _ _ _ _ h' => vk_ok_eq h') hne2 hne3 hh
  exact vk_nh_binary (op := Op.and) (fun _ _ _ _ h' => vk_ok_and h') hne1 heq h

/-- **THE extcodecopy STEP, ENVIRONMENT HALF.** Only what both walks need first: the environment is
    untouched, so success survives the copy. -/
theorem vk_extcodecopy_normal {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (vkS2 R.consts) V' st' .normal) :
    V' = V := by
  cases h with
  | exprStmt hex => cases hex with
      | builtinOk hargs hbi => cases hargs with
          | argsCons hrest hx => cases hrest with
              | argsCons hrest2 h3 => cases hrest2 with
                  | argsCons hrest3 h4 => cases hrest3 with
                      | argsCons hnil h5 => cases hnil with
                          | argsNil => rfl

/-- Setting a variable that IS bound reads back the new value: the one `VEnv` fact every assign
    needs and neither the vendored layer nor `Bridge` states. -/
theorem vk_get_set_of_some {V : VEnv (Bridge.Dialect c g)} {x : Ident} {v w : U256}
    (h : VEnv.get V x = some v) : VEnv.get (VEnv.set V x w) x = some w := by
  classical
  induction V with
  | nil => cases h
  | cons p rest ih =>
      cases p with
      | mk y u =>
      by_cases hy : y = x
      · subst hy
        simp [VEnv.set, VEnv.get]
      · have hget : VEnv.get rest x = some v := by
            have h2 : VEnv.get ((y, u) :: rest) x = some v := h
            simpa [VEnv.get, List.find?, hy] using h2
        have h3 := ih hget
        simpa [VEnv.set, VEnv.get, hy] using h3

/-- `success` is 0 after one guard on a poisoned boundary, whatever the comparison says: the
    conjunction short-circuits on the bit, so the nine guards need NO value analysis on this path.
    That is the whole reason conjunct 2 of `BlockSound` is cheap here. -/
theorem vk_poison_step {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {A B succExpr : Expr EVM.Op}
    (hsucc : VEnv.get V "success" = some (0 : U256))
    (hsite : ∀ {st₀ : EvmState} {av : U256} {st₁ : EvmState},
        EvalExpr (Bridge.Dialect c g) funs V st₀ succExpr (.vals [av] st₁) →
          VEnv.get V "success" = some av)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
          Expr.builtin Op.eq [A, B]])) V' st' .normal) :
    VEnv.get V' "success" = some (0 : U256) := by
  obtain ⟨yv, xv, st₁, st₂, heq, hxv, hV⟩ := vk_assign_inv h
  have hxv0 : xv = 0 := by
    have := hsite hxv
    rw [hsucc] at this
    exact Option.some.inj this.symm
  rw [hV, hxv0]
  have h0 : ((0 : U256) &&& yv) = 0 := by simp
  rw [h0]
  exact vk_get_set_of_some hsucc


/-! ## 5. THE PREMISE GAP: `vkPins` - CLOSED BY D-P50, IT IS NOW CLAUSES 12-13 OF `Valid`

  `Clean R .vk` postulates `Inv .vk`, whose first clause is
  `bytesAt st (ptrAddr PV.memory.vkMptr) PV.vk.len == PV.vk.bytes` (Inv.lean:741). The block writes
  to the inlined `VK_MPTR` and copies `EXPECTED_VK_PAYLOAD_LENGTH` bytes from byte 1 of
  `extCodeOf vk`. `Frame.vkCode` supplies the SOURCE of that copy - the link the brief asked about,
  and it holds - but nothing in `Frame`, `Clean`, `Inv` or `Valid` says the render's CONSTANT TABLE
  agrees with its own PLAN VIEW about where the window is, how long the payload is, or how many
  instances the calldata carries. Those are `vkPins`. Each is a computation at a real deployment
  (the deployed table binds VK_MPTR = 0x2900 = ptrAddr pv.memory.vkMptr and
  EXPECTED_VK_PAYLOAD_LENGTH = 4576 = pv.vk.len), and `Valid.slots` is `EnvAgrees`, whose eleven
  fields are field-constant facts and none of them mentions VK_MPTR. Same shape as T.1's `trRetMptr`
  and FP.0's `fpG2Slots`: a fourth per-render pin the M.1 brief did not list.

  WHY THEY ARE NOT OPTIONAL. Without pin 1 and 2 `BlockSound R .vkLoading` is FALSE, not unproved:
  a render whose table points VK_MPTR elsewhere copies the payload to the wrong address, exits
  `normal` with `success = 1`, and satisfies neither `Clean .vk` nor `Poisoned`. Pin 4 is what keeps
  the copy from clobbering the g1_identity window that `Inv`'s unconditional clause pins to zero.
  Pin 3 is what turns `decodeCalldata = some …` into `Inv .vk`'s calldata-length clause. -/

/- **D-P50 / S.9: THE TWO STRUCTURES MOVED, THEY ARE NOT RELAXED.** `vkPins` and
    `vkProgressPins` now live in `Statements.lean` section 2 (FROZEN - re-hashed in the same commit)
    as `Midfall.LoweringV2.vkPins` / `Midfall.LoweringV2.vkProgressPins`, and are clauses 12 and 13
    of `Render.Valid`. The six clauses are the SAME SIX, in the same order, with the same names and
    the same text: nothing was weakened, dropped, or turned into a semantic obligation. They moved
    because the hinge `blockContracts_of_valid` (Blocks.lean:152) takes `hR : R.Valid` and must
    yield a row for EVERY `Partial`, so while the pins were free premises of `vk_blockRow` the hinge
    could not be proved from its own stated hypothesis. What made the frozen edit admissible is that
    the pins are PROVED, not guessed: S.8 constructed `vkPins poseidonRender` and
    `vkProgressPins poseidonRender` sorry-free (S.8's probes), landed by S.9 in
    `Instances/PoseidonPins.lean`. -/

/-- **THE PINS ARE A PROJECTION NOW, NOT A HYPOTHESIS (D-P50).** -/
theorem vkPins_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) : vkPins R := hR.vkPins

/-- The progress half, likewise (D-P50). -/
theorem vkProgressPins_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) : vkProgressPins R :=
  hR.vkProgressPins

/-! ## 6. WHAT THIS CARD DID NOT CLOSE, STATED AT EXACTLY THE SHAPE THE CONSUMER ASKS FOR

  Three obligations remain and they are named here rather than hidden. Each is stated at the
  `StmtsContractAll` / `BlockProgress` shape §6:92-111 wants, so `vk_blockSound` and `vk_blockRow`
  below are re-assembly and nothing else, and the next card can pick any one of them up without
  re-deriving the interface.

  WHAT IS MISSING, CONCRETELY. The interface (§1-§4) is complete: the slice is in statement-list
  form, every site inverts to a value, the fail helper reverts at an arbitrary selector, the
  recurring assign inverts, the copy inverts, and the guard cannot halt. What is left is the
  THIRTEEN-STEP SEQUENCE WALK plus the `Inv` transfer:
  * the walk itself is ~120 lines of `Step.stmts_cons_inv` over thirteen statements with the
    `restore V Vb` bookkeeping at the block exit (the block's `V'` is `restore V Vb`, and reading
    `success` back through it needs `VEnv.set` length-preservation - `vk_get_set_of_some` is the
    first piece of that);
  * the clean half additionally needs `Inv .start → Inv .vk`, i.e. the three `.vk` clauses of
    `InvAt` (payload bytes via `vkPins.vkMptr`/`payloadLen` and `Frame.vkCode`; calldata length via
    `decodeCalldata`'s own guard plus `vkPins.numInst`; `hasAccumulator = false` via
    `pv_hasAcc_false`) AND preservation of the two unconditional clauses across the copy
    (`vkPins.disjoint` for g1_identity). FP.0 measured that normalising the whole `InvAt` chain
    exceeds the default heartbeat budget; the cheap route is to assemble the chain clause by clause
    with `if_pos`/`if_neg` on the `Checkpoint.idx` guards, which this card did not get to.
  * the progress half needs a run EXHIBITED, hence `vkProgressPins`. -/

/-- **GAP 1 OF 3 - `BlockSound`'s FIRST conjunct at `.vkLoading`.** Missing: the thirteen-step walk
    and the `Inv .start → Inv .vk` transfer described in §6's header. Everything it needs from the
    semantics is proved in §2-§4. -/
theorem vk_sound_clean (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : vkPins R) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (g : ExternalGas) :
    StmtsContractAll (D := Dperm product g) (R.scope (permissive (callsOf product)) g)
        (R.slice Partial.vkLoading)
        (fun V st => Clean R Checkpoint.start Snap H vkAddr cd V st)
        (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
          exitOk R Partial.vkLoading Snap H vkAddr cd V' st' o ∨
          (Partial.vkLoading ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) := by
  sorry

/-- **GAP 2 OF 3 - `BlockSound`'s SECOND conjunct at `.vkLoading`.** The walk is shorter here (from
    a poisoned boundary every run reverts, so no `Inv` and no `Frame` preservation is needed and the
    `normal ∧ Poisoned` arm is never used), and §4's `vk_poison_step` is the whole content of the
    six header guards. Missing: the same `Step.stmts_cons_inv` scaffolding over thirteen statements
    and the `assignHalt` / `exprStmtHalt` prunings, all of which §2-§4 supply the pieces for. -/
theorem vk_poison_walk (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    StmtsContractAll (D := Dperm product g) (R.scope (permissive (callsOf product)) g)
        (R.slice Partial.vkLoading)
        (fun V st => Poisoned R H vkAddr cd V st)
        (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
          (Partial.vkLoading ≠ Partial.traceReturn ∧ o = .normal ∧
            Poisoned R H vkAddr cd V' st')) := by
  sorry

/-- **GAP 3 OF 3 - `BlockProgress R .vkLoading`.** `StmtsTotal` is `StmtsContract ∧ StmtsContractAll`,
    so this needs a run EXHIBITED from a clean boundary, which needs the guard of statement 1 to be
    passable: hence `vkProgressPins`. Note the honest gate it is put under is §6's
    `G1CodecHeadlineLaws ∧ ChallengesGood ∧ DualMSM.check` (ST.4 moved the progress gate to the
    headline bundle, D-P64), and `.vkLoading` reads none of the three - the
    VK block's progress does not depend on the pairing at all, which is worth saying because it
    means this gap is independent of P.1 and T.4. -/
theorem vk_progress (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : vkPins R) (hppins : vkProgressPins R) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash)
    (vkAddr : U256) (cd : Bytes) :
    G1CodecHeadlineLaws R.E.g1 → ChallengesGood R.vk Snap →
      DualMSM.check Snap.c.dual R.params = true →
      BlockProgress R Partial.vkLoading Snap H vkAddr product cd := by
  sorry

/-- **THE ROW, ASSEMBLED FROM THE THREE GAPS.** Sorry-free given them: this is re-association only,
    exactly the shape `tr_blockRow` / `fp_blockRow` have in `Blocks/Compose.lean`, and it is what
    `blockContracts_of_valid_of_rows` (Blocks.lean:713) consumes as its `hvk` argument. SINCE D-P50 IT
    CARRIES NO PIN HYPOTHESES AT ALL: `vkPins` and `vkProgressPins` are clauses 12 and 13 of `Valid`,
    so the row is `BlockRow R product .vkLoading` outright and the pins arrive through the `hR` the
    row already takes - which is exactly what the hinge needed and what distinguishes this row from
    `tr_blockRow` / `fp_blockRow`, which still carry `trRetMptr` / `fpG2Slots` as free premises. The
    three gaps are still `sorry`, so THE ROW IS STILL NOT CLOSED. -/
theorem vk_blockRow (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    BlockRow R product Partial.vkLoading := by
  intro hR _hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap
  refine ⟨fun g => ⟨vk_sound_clean R product hR hR.vkPins Snap H vkAddr cd g,
      vk_poison_walk R product hR Snap H vkAddr cd g⟩, fun _hcodec _hcg _hdual =>
      vk_progress R product hR hR.vkPins hR.vkProgressPins Snap H vkAddr cd _hcodec _hcg _hdual⟩

#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_slice
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_assign_inv
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_extcodecopy_normal
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_fail_reverts
#print axioms Midfall.LoweringV2.Blocks.VkLoading.vk_get_set_of_some

end Midfall.LoweringV2.Blocks.VkLoading
