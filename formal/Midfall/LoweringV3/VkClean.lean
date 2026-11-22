/-
  Midfall.LoweringV3.VkClean

  **WP A3b: the clean half of the vkLoading row, assembled.** See VkWindow.lean for gap (i) and the
  header of VkRow.lean for the walk's shape. This file adds what neither has:

  * §1 'PureRead': every expression the slice evaluates is a pure read, so env, the halt record and
    memory ride through all thirteen statements except the copy - gap (iii)'s content, and the
    reason no pin is needed for the Frame transfer;
  * §2 the value inversions 'calldataload', 'calldatasize' and 'add' answer, which gap (ii) reads;
  * §3 the peels with their transfer, and §4 the thirteen-statement walk itself, which is gap (iv):
    it ends with 'V' = VEnv.set V "success" 1' (the nine assigns collapse to one because 'set'
    updates the innermost binding and preserves length, so 'restore V V' = V''), the state transfer,
    the copy's window equation and the three calldata equalities;
  * §5 the wrap refutation: PG-VKMEMORYFIT's mechanism, and §5b the record of the three refused
    routes; D-QVM1's `programFits` closes the gap they left;
  * §6 `StageInv .vk` assembled from the walk plus D-QVM1's `fit1_of_valid`/`fit2_of_valid`, the
    `bytesAt` window lemmas of VkWindow and `vkPins_disjoint_of_generated`, and `vk_blockSimV3`:
    BOTH conjuncts of `BlockSim R Partial.vkLoading` over `StageInv`, generic in the render.

  D-P71: generic in the render; no fixture, no 'native_decide', nothing added to 'ValidV3', to a row,
  to a bundle or to the root.
-/
import Midfall.LoweringV3.VkWindow
import Midfall.LoweringV3.VkRow
import Midfall.LoweringV3.MemoryPairs
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.VkClean

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.Stage
open Midfall.LoweringV2.Blocks.VkLoading Midfall.LoweringV2.Blocks.TraceReturn
open Midfall.LoweringV3.VkRow Midfall.LoweringV3.VkWindow
open Midfall.LoweringV3.VkWindow

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
  {c : ExternalCalls} {g : ExternalGas}

abbrev Rev (st : EvmState) : Prop := Midfall.LoweringV2.Reverted st

/-! ## 1. PURE READS -/

/-- A read leaves the state where it found it: env, halt record and memory. This is what 'Frame' and
    two of the three 'Inv' clauses need to survive a statement, and it is strictly weaker than
    'st' = st' - the mload family also moves the active-word high-water mark. -/
def Same (st st₁ : EvmState) : Prop :=
  st₁.env = st.env ∧ st₁.halted = st.halted ∧ st₁.memory = st.memory

theorem Same.trans {st₁ st₂ st₃ : EvmState} (h₁₂ : Same st₁ st₂) (h₂₃ : Same st₂ st₃) :
    Same st₁ st₃ :=
  ⟨h₂₃.1.trans h₁₂.1, h₂₃.2.1.trans h₁₂.2.1, h₂₃.2.2.trans h₁₂.2.2⟩

/-- An expression is a pure read at a scope and an environment: every evaluation of it leaves env,
    the halt record and memory exactly as they were. -/
def PureRead (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    (e : Expr EVM.Op) : Prop :=
  ∀ (st₀ st₁ : EvmState) (cv : U256),
      EvalExpr (Bridge.Dialect c g) funs V st₀ e (.vals [cv] st₁) → Same st₀ st₁

theorem pureLit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {n : Nat} :
    PureRead funs V (Expr.lit (.number n)) := by
  intro st₀ st₁ cv h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem pureVar {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {x : Ident} :
    PureRead funs V (Expr.var x) := by
  intro st₀ st₁ cv h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- An inlined constant site is a literal or a variable, and both are pure. -/
theorem pureSite (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} (x : String) :
    PureRead funs V (vkSite x R.consts) := by
  classical
  cases hmv : R.consts.lookup x with
  | some v =>
      rw [show vkSite x R.consts = Expr.lit (.number v) from by simp [vkSite, hmv]]
      exact pureLit
  | none =>
      rw [show vkSite x R.consts = Expr.var x from by simp [vkSite, hmv]]
      exact pureVar

/-- A unary builtin whose own step is pure is pure over a pure argument. -/
theorem pureUn {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {op : EVM.Op} {a : Expr EVM.Op}
    (hbi : ∀ (x : U256) (st₀ st₁ : EvmState) (rets : List U256),
        (Bridge.Dialect c g).Builtin op [x] st₀ (.ok rets st₁) → Same st₀ st₁)
    (ha : PureRead funs V a) : PureRead funs V (Expr.builtin op [a]) := by
  intro st₀ st₁ cv h
  cases h with
  | builtinOk hargs hbi' =>
      cases hargs with
      | argsCons hnil hx =>
          cases hnil with
          | argsNil =>
              obtain ⟨p₁, p₂, p₃⟩ := ha st₀ _ _ hx
              obtain ⟨q₁, q₂, q₃⟩ := hbi _ _ st₁ _ hbi'
              exact ⟨q₁.trans p₁, q₂.trans p₂, q₃.trans p₃⟩

/-- A binary builtin whose own step is pure is pure over two pure arguments. The semantics evaluates
    the SECOND argument first (BigStep.lean:209, 'argsCons' takes the tail). -/
theorem pureBin {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {op : EVM.Op} {a b : Expr EVM.Op}
    (hbi : ∀ (x y : U256) (st₀ st₁ : EvmState) (rets : List U256),
        (Bridge.Dialect c g).Builtin op [x, y] st₀ (.ok rets st₁) → Same st₀ st₁)
    (ha : PureRead funs V a) (hb : PureRead funs V b) :
    PureRead funs V (Expr.builtin op [a, b]) := by
  intro st₀ st₁ cv h
  cases h with
  | builtinOk hargs hbi' =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hnil ha' =>
              cases hnil with
              | argsNil =>
                  obtain ⟨p₁, p₂, p₃⟩ := hb st₀ _ _ ha'
                  obtain ⟨q₁, q₂, q₃⟩ := ha _ _ _ hx
                  obtain ⟨r₁, r₂, r₃⟩ := hbi _ _ _ st₁ _ hbi'
                  exact ⟨r₁.trans (q₁.trans p₁), r₂.trans (q₂.trans p₂), r₃.trans (q₃.trans p₃)⟩

/-- 'calldatasize' is nullary and reads nothing but the calldata length. -/
theorem pureCdsz {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    PureRead funs V (Expr.builtin Op.calldatasize []) := by
  intro st₀ st₁ cv h
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsNil =>
          simp only [builtinWithExternal, stepOp, rd0] at hbi
          cases hbi
          exact ⟨rfl, rfl, rfl⟩

/-- The five builtin arms this slice reads, one at a time, from VkRow's state lemmas. -/
theorem pr_mload (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} (slot : String) :
    PureRead funs V (Expr.builtin Op.mload [vkSite slot R.consts]) :=
  pureUn (fun x st₀ st₁ rets hbi => vk_st_mload hbi) (pureSite R slot)

theorem pr_cdl (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} (slot : String) :
    PureRead funs V (Expr.builtin Op.calldataload [vkSite slot R.consts]) :=
  pureUn (fun x st₀ st₁ rets hbi => vk_st_calldataload hbi) (pureSite R slot)

theorem pr_eq (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A B : Expr EVM.Op}
    (hA : PureRead funs V A) (hB : PureRead funs V B) :
    PureRead funs V (Expr.builtin Op.eq [A, B]) :=
  pureBin (fun x y st₀ st₁ rets hbi => vk_st_pure2 (Or.inl rfl) hbi) hA hB

theorem pr_and (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A B : Expr EVM.Op}
    (hA : PureRead funs V A) (hB : PureRead funs V B) :
    PureRead funs V (Expr.builtin Op.and [A, B]) :=
  pureBin (fun x y st₀ st₁ rets hbi => vk_st_pure2 (Or.inr (Or.inl rfl)) hbi) hA hB

theorem pr_add (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A B : Expr EVM.Op}
    (hA : PureRead funs V A) (hB : PureRead funs V B) :
    PureRead funs V (Expr.builtin Op.add [A, B]) :=
  pureBin (fun x y st₀ st₁ rets hbi => vk_st_pure2 (Or.inr (Or.inr rfl)) hbi) hA hB

theorem pr_iszero (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A : Expr EVM.Op}
    (hA : PureRead funs V A) : PureRead funs V (Expr.builtin Op.iszero [A]) :=
  pureUn (fun x st₀ st₁ rets hbi => vk_st_pure1 rfl hbi) hA

theorem pr_ecs (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A : Expr EVM.Op}
    (hA : PureRead funs V A) : PureRead funs V (Expr.builtin Op.extcodesize [A]) :=
  pureUn (fun x st₀ st₁ rets hbi => vk_st_rd1 (Or.inr (Or.inl rfl)) hbi) hA

theorem pr_ech (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {A : Expr EVM.Op}
    (hA : PureRead funs V A) : PureRead funs V (Expr.builtin Op.extcodehash [A]) :=
  pureUn (fun x st₀ st₁ rets hbi => vk_st_rd1 (Or.inr (Or.inr rfl)) hbi) hA

/-- The guard of statement 1: two extcode reads, an eq each, an and, an iszero. -/
theorem pr_guard (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    PureRead funs V (vkGuard R.consts) := by
  show PureRead funs V (Expr.builtin Op.iszero [Expr.builtin Op.and
    [Expr.builtin Op.eq [Expr.builtin Op.extcodesize [vkVk0 R.consts],
                         vkSite "EXPECTED_VK_LENGTH" R.consts],
     Expr.builtin Op.eq [Expr.builtin Op.extcodehash [vkVk0 R.consts],
                         vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]]])
  exact pr_iszero R (pr_and R
    (pr_eq R (pr_ecs R (pureSite R "vk")) (pureSite R "EXPECTED_VK_LENGTH"))
    (pr_eq R (pr_ech R (pureSite R "vk")) (pureSite R "EXPECTED_VK_CODEHASH_WORD")))

/-- The 'success' occurrence both walks read: a raw variable, so pure. -/
theorem pr_succ {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    PureRead funs V vkSucc := pureVar

/-! ## 2. THE VALUE INVERSIONS GAP (ii) READS -/

/-- A literal's value and the state it leaves. -/
theorem vk_lit_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {n : Nat} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n)) (.vals [cv] st₁)) :
    cv = BitVec.ofNat 256 n ∧ st₁ = st := by
  cases h
  exact ⟨rfl, rfl⟩

/-- 'calldataload' at an inlined site answers the 'wordFrom' of the site's value and leaves the
    state alone. -/
theorem vk_cdl_val (R : Render p G₁ G₂ Gₜ) (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.calldataload [vkSite slot R.consts]) (.vals [cv] st₁)) :
    ∃ a : U256, vkVal slot R V = some a ∧
      cv = wordFrom st.env.calldata a.toNat ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hx =>
          cases hnil with
          | argsNil =>
              obtain ⟨hval, hst⟩ := vkSite_val hx
              subst hst
              simp only [builtinWithExternal, stepOp, rd1] at hbi
              cases hbi
              exact ⟨_, hval, rfl, rfl⟩

/-- 'calldatasize' answers the calldata length as a word and leaves the state alone. -/
theorem vk_cdsz_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.calldatasize []) (.vals [cv] st₁)) :
    cv = BitVec.ofNat 256 st.env.calldata.length ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsNil =>
          simp only [builtinWithExternal, stepOp, rd0] at hbi
          cases hbi
          exact ⟨rfl, rfl⟩

/-- 'add' answers the word sum and leaves the state alone. -/
theorem vk_add_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {a b : Nat} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.add [Expr.lit (.number a), Expr.lit (.number b)])
        (.vals [cv] st₁)) :
    cv = BitVec.ofNat 256 a + BitVec.ofNat 256 b ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hnil h2 =>
              cases hnil with
              | argsNil =>
                  cases hx with
                  | lit =>
                      cases h2 with
                      | lit =>
                          simp only [builtinWithExternal, stepOp, bin] at hbi
                          cases hbi
                          exact ⟨rfl, rfl⟩

/-! ## 3. THE PEELS WITH THEIR TRANSFER, AT A GENERAL OUTCOME -/

/-- Setting a variable twice is setting it once: 'VEnv.set' updates the INNERMOST binding and
    preserves length and order, so the nine assigns of this slice collapse to one. -/
theorem VEnv.set_set_set {V : VEnv (Bridge.Dialect c g)} {x : Ident} {a b : U256} :
    VEnv.set (VEnv.set V x a) x b = VEnv.set V x b := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk y w =>
          by_cases hy : y = x
          · subst hy
            simp [VEnv.set]
          · simp [VEnv.set, hy, ih]

/-- Reading a variable right after setting it, at the 'success' spelling. -/
theorem get_set_succ {V : VEnv (Bridge.Dialect c g)} {s y : U256}
    (h : VEnv.get V "success" = some s) : VEnv.get (VEnv.set V "success" y) "success" = some y :=
  vk_get_set h

/-- 'VEnv.set' preserves the length: what makes 'restore' the identity at a block exit. -/
theorem VEnv.set_length {V : VEnv (Bridge.Dialect c g)} {x : Ident} {a : U256} :
    (VEnv.set V x a).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk y w =>
          by_cases hy : y = x
          · subst hy
            simp [VEnv.set]
          · simp [VEnv.set, hy, ih]

/-- The non-halting facts the cross-checks need, in the '∀ states' shape 'vk_assign_nh' asks for. -/
theorem nh_mload_site (R : Render p G₁ G₂ Gₜ) (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    ∀ (st₁ st₃ : EvmState), EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.mload [vkSite slot R.consts]) (.halt st₃) → False :=
  fun _ _ h => vk_mload_ne_halts slot h

theorem nh_cdl_site (R : Render p G₁ G₂ Gₜ) (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    ∀ (st₁ st₃ : EvmState), EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.calldataload [vkSite slot R.consts]) (.halt st₃) → False :=
  fun _ _ h => vk_cdl_ne_halts slot h

theorem nh_lit {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st₁ st₃ : EvmState} {m : Nat} :
    EvalExpr (Bridge.Dialect c g) funs V st₁ (Expr.lit (.number m)) (.halt st₃) → False :=
  vkLit_ne_halts

theorem nh_succ {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    ∀ (st₁ st₃ : EvmState),
      EvalExpr (Bridge.Dialect c g) funs V st₁ vkSucc (.halt st₃) → False :=
  fun _ _ h => vkSucc2_ne_halts h

theorem nh_cdsz {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st₁ st₃ : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.calldatasize []) (.halt st₃)) : False :=
  vk_nh_nullary (op := Op.calldatasize) (fun _ _ h' => vk_ok_calldatasize h') h

theorem nh_add_site_lit (R : Render p G₁ G₂ Gₜ) (slot : String) (m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} :
    ∀ (st₁ st₃ : EvmState), EvalExpr (Bridge.Dialect c g) funs V st₁
        (Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]) (.halt st₃) → False :=
  fun _ _ h =>
    vk_nh_binary (op := Op.add) (fun _ _ _ _ h' => vk_ok_add h')
      (fun _ _ hh => vkSite_ne_halts hh) (fun _ _ hh => vkLit_ne_halts hh) h

/-- **S1 with its transfer, at a general outcome.** Either the VK-presence guard fires and the run
    reverts, or the guard is skipped - a pure read, so the state it leaves has the same env, halt
    record and memory - and the tail runs from the SAME environment. -/
theorem vkS1_peelT (R : Render p G₁ G₂ Gₜ)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkS1 R.consts :: ss) Vb stb ob) :
    (ob = .halt ∧ Rev stb) ∨
      (∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob ∧ Same st st₁) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts =>
            exact absurd (vkS1_arm_reverts (vkArm_fail_lookup hfail) hstmts).1
              (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
    | ifFalse hc _ =>
        exact Or.inr ⟨st₁, hrest, pr_guard R _ st₁ _ hc⟩
  · cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts => exact Or.inl (vkS1_arm_reverts (vkArm_fail_lookup hfail) hstmts)
    | ifHalt hc => exact (vkGuard_ne_halts hc).elim
    | ifFalse _ _ => exact absurd rfl hne

/-- **S2 with its window, at a general outcome.** The copy cannot halt and leaves the environment
    alone; the state it produces has the same env and halt record, and its memory is the copy of the
    deployed runtime over the window the constant table names. The four argument sites are pure
    reads, so the state the copy starts from agrees with the state the statement started from - that
    is what turns the semantics' anonymous 'copyInto' into the equation gap (i) can use. -/
theorem vkS2_peelT (R : Render p G₁ G₂ Gₜ) (vkAddr : U256) (mVk payLen : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hvkloc : VEnv.get V "vk" = some vkAddr)
    (hVK : R.consts.lookup "VK_MPTR" = some mVk)
    (hPL : R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkS2 R.consts :: ss) Vb stb ob) :
    ∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob ∧
      st₁.env = st.env ∧ st₁.halted = st.halted ∧
      st₁.memory = copyInto st.memory (BitVec.ofNat 256 mVk).toNat 1
        (BitVec.ofNat 256 payLen).toNat (st.env.extCodeOf vkAddr) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | exprStmt hex =>
        cases hex with
        | builtinOk hargs hbi =>
            cases hargs with
            | argsCons hrest2 hx =>
                cases hrest2 with
                | argsCons hrest3 h2 =>
                    cases hrest3 with
                    | argsCons hnil h3 =>
                        cases hnil with
                        | argsCons hnil2 h4 =>
                            cases hnil2 with
                            | argsNil =>
                                obtain ⟨hv4, he4⟩ := vkSite_val h4
                                subst he4
                                cases h3 with
                                | lit =>
                                    obtain ⟨hv2, he2⟩ := vkSite_val h2
                                    subst he2
                                    obtain ⟨hvx, hex⟩ := vkSite_val hx
                                    subst hex
                                    have hx1 : vkVal "vk" R V = some vkAddr := by
                                      simp only [vkVal, consts_vk_none R]
                                      exact hvkloc
                                    have e4 : vkVal "EXPECTED_VK_PAYLOAD_LENGTH" R V =
                                        some (BitVec.ofNat 256 payLen) := by
                                      simp only [vkVal, hPL]
                                    have e2 : vkVal "VK_MPTR" R V =
                                        some (BitVec.ofNat 256 mVk) := by
                                      simp only [vkVal, hVK]
                                    obtain ⟨rfl⟩ := Option.some.inj (e2.symm.trans hv2)
                                    obtain ⟨rfl⟩ := Option.some.inj (hx1.symm.trans hvx)
                                    obtain ⟨rfl⟩ := Option.some.inj (e4.symm.trans hv4)
                                    simp only [builtinWithExternal, stepOp] at hbi
                                    cases hbi
                                    refine ⟨_, hrest, ?_, ?_, ?_⟩
                                    · rfl
                                    · rfl
                                    · rfl
  · cases h₁ with
    | exprStmtHalt hex => exact (vkS2_expr_ne_halts hex).elim
    | exprStmt _ => exact absurd rfl hne

/-- One clean cross-check, peeled at a GENERAL outcome, with the two argument evaluations named and
    the state transfer. 'vk_hdr_bit' (VkRow §5) hides the argument evaluations and 'vk_hdr_step'
    (§6) hides the values; gap (ii) is exactly what both throw away, and gap (iii) is the 'Same'
    this adds. -/
theorem vk_hdr_peelT (R : Render p G₁ G₂ Gₜ) (A B succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hA : PureRead funs V A) (hB : PureRead funs V B) (hS : PureRead funs V succExpr)
    (hnA : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ A (.halt st₃) → False)
    (hnB : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ B (.halt st₃) → False)
    (hnS : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
            Expr.builtin Op.eq [A, B]]) :: ss) Vb stb ob) :
    ∃ (x av bv : U256) (V₁ : VEnv (Bridge.Dialect c g)) (st₁ sB sA : EvmState),
        V₁ = VEnv.set V "success" (x &&& b2w (decide (av = bv)))
      ∧ EvalExpr (Bridge.Dialect c g) funs V st B (.vals [bv] sB)
      ∧ EvalExpr (Bridge.Dialect c g) funs V sB A (.vals [av] sA)
      ∧ EvalExpr (Bridge.Dialect c g) funs V sA succExpr (.vals [x] st₁)
      ∧ ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb ob
      ∧ Same st st₁ := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · obtain ⟨yv, xv, st₀, heq, hxv, hV⟩ := vk_assign_inv2 h₁
    obtain ⟨av, bv, sB, sA, hbv, hav, hst, hyv⟩ := vk_eq_val heq
    subst hyv
    subst hst
    refine ⟨xv, av, bv, V₁, st₁, sB, sA, hV, hbv, hav, hxv, hrest, ?_⟩
    exact Same.trans (hB st _ _ hbv) (Same.trans (hA _ _ _ hav) (hS _ _ _ hxv))
  · cases h₁ with
    | assignVal _ _ => exact absurd rfl hne
    | assignHalt he => exact (vk_assign_nh hnS hnA hnB he).elim

/-- A guard on the clean path, at a GENERAL outcome: either it fired and the run reverted, or it was
    skipped - so the bit was 1, the environment is unchanged and the state transfer holds. -/
theorem vkS9_peelT (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {s : U256} (hget : VEnv.get V "success" = some s) (hbit : Midfall.Yul.VKP.IsBit s)
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
            [Stmt.exprStmt (Expr.call "fail" [vkSite err R.consts])] :: ss) Vb stb ob) :
    (ob = .halt ∧ Rev stb) ∨
      (∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob ∧ Same st st₁ ∧
        VEnv.get V "success" = some (1 : U256)) := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · have hskip := vkS9_skip R err hget hbit hfail h₁
    cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts =>
            exact absurd (vk_arm_reverts (vkArm_fail_lookup hfail)
              (fun _ _ hh => vkSite_ne_halts hh) hstmts).1
              (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
    | ifFalse hc _ =>
        exact Or.inr ⟨st₁, hrest, (pr_iszero R pr_succ) st st₁ _ hc, by rw [hget, hskip.2]⟩
  · cases h₁ with
    | ifTrue _ _ hbody =>
        cases hbody with
        | block hstmts =>
            exact Or.inl (vk_arm_reverts (vkArm_fail_lookup hfail)
              (fun _ _ hh => vkSite_ne_halts hh) hstmts)
    | ifHalt hc =>
        exact (vk_nh_unary (op := Op.iszero) (fun _ _ _ h' => vk_ok_iszero h')
          (fun _ _ hh => vkVar_ne_halts hh) hc).elim
    | ifFalse _ _ => exact absurd rfl hne
/-! ## 4. THE THIRTEEN-STATEMENT CLEAN WALK -/

/-- **THE HELPER A3 NAMED AS MISSING**: 'IsBit (x &&& y)' from 'IsBit x' and 'IsBit y'. Not
    reachable by 'rfl': 'Nat.land = Nat.bitwise' does not reduce on a symbolic successor, so the
    cases are closed one at a time. -/
theorem isBit_and {x y : U256} (hx : Midfall.Yul.VKP.IsBit x) (hy : Midfall.Yul.VKP.IsBit y) :
    Midfall.Yul.VKP.IsBit (x &&& y) := by
  rcases hx with rfl | rfl
  · exact Or.inl BitVec.zero_and
  · rcases hy with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr rfl

/-- 'add' at a site and a literal: the sum of the two values, state unchanged. -/
theorem vk_add_site_val (R : Render p G₁ G₂ Gₜ) (slot : String) (m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]) (.vals [cv] st₁)) :
    ∃ a : U256, vkVal slot R V = some a ∧ cv = a + BitVec.ofNat 256 m ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hnil h2 =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hb, hst2⟩ := vk_lit_val h2
                  subst hst2
                  obtain ⟨hval, hst⟩ := vkSite_val hx
                  subst hst
                  simp only [builtinWithExternal, stepOp, bin] at hbi
                  cases hbi
                  refine ⟨_, hval, ?_, rfl⟩
                  rw [← hb]

/-- **THE CLEAN WALK.** Thirteen statements, inverted with 'Step.stmts_cons_inv' - the route
    'Blocks/VkLoading.lean' §6 names and GEN.1 step 2 prescribes, and the shape 'vkBody_poison_walk'
    already uses. Either the run halted with a revert (one of the three guards fired) or it ended
    normally with 'success' still 1, the state transfer of gap (iii), the copy window of gap (i) and
    the three calldata equalities of gap (ii). The nine assigns all write 'success' and nothing
    else, so the environment collapses to 'VEnv.set V "success" 1': that is what makes
    'restore V Vb = Vb' at the block exit and what carries 'Frame.r' and 'Frame.vk' across all
    thirteen statements. -/
theorem vkBody_clean_walk (R : Render p G₁ G₂ Gₜ) (vkAddr : U256)
    (mVk payLen a1 a2 a3 : Nat)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hvkloc : VEnv.get V "vk" = some vkAddr)
    (hVK : R.consts.lookup "VK_MPTR" = some mVk)
    (hPL : R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (hP1 : R.consts.lookup "PROOF_LEN_CPTR" = some a1)
    (hP2 : R.consts.lookup "NUM_INSTANCE_CPTR" = some a2)
    (hP3 : R.consts.lookup "INSTANCE_CPTR" = some a3)
    {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome} {n k w o l b q : Nat}
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkBody R.consts n k w o l b q) Vb stb ob) :
    (ob = .halt ∧ Rev stb) ∨
      (ob = .normal ∧ VEnv.get Vb "success" = some (1 : U256) ∧
        VEnv.get Vb "r" = VEnv.get V "r" ∧ VEnv.get Vb "vk" = VEnv.get V "vk" ∧
        Vb.length = V.length ∧ stb.env = st.env ∧ stb.halted = st.halted ∧
        stb.memory = copyInto st.memory (BitVec.ofNat 256 mVk).toNat 1
          (BitVec.ofNat 256 payLen).toNat (st.env.extCodeOf vkAddr) ∧
        wordFrom st.env.calldata (BitVec.ofNat 256 a1).toNat = BitVec.ofNat 256 q ∧
        wordFrom st.env.calldata (BitVec.ofNat 256 a2).toNat = BitVec.ofNat 256 n ∧
        BitVec.ofNat 256 st.env.calldata.length =
          BitVec.ofNat 256 a3 + BitVec.ofNat 256 (n * 32)) := by
  rw [vkBody_nil] at h
  rcases vkS1_peelT R hfail h with hleft | ⟨st₁, h₁, tr₁⟩
  · exact Or.inl hleft
  · obtain ⟨st₂, h₂, e₂, h₂', hmem⟩ := vkS2_peelT R vkAddr mVk payLen hvkloc hVK hPL h₁
    rw [show vkSucc0 R.consts = vkSucc from vkSucc0_var R] at h₂
    obtain ⟨x₃, av₃, bv₃, V₃, st₃, sB₃, sA₃, hV₃, hbv₃, hav₃, hxv₃, h₃, tr₃⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "NUM_INSTANCES_MPTR" R.consts]) (Expr.lit (.number n)) vkSucc
        (pr_mload R "NUM_INSTANCES_MPTR") pureLit pr_succ (nh_mload_site R "NUM_INSTANCES_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₂
    have hx₃ : x₃ = (1 : U256) :=
      Option.some.inj ((vk_var_hsite hxv₃).symm.trans hsucc)
    have bit₃ : Midfall.Yul.VKP.IsBit x₃ := by
      rw [hx₃]
      exact Midfall.Yul.VKP.isBit_one
    have wb₃ : Midfall.Yul.VKP.IsBit (x₃ &&& b2w (decide (av₃ = bv₃))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₃
    have hg₃ : VEnv.get V₃ "success" = some (x₃ &&& b2w (decide (av₃ = bv₃))) :=
      hV₃ ▸ get_set_succ hsucc
    obtain ⟨x₄, av₄, bv₄, V₄, st₄, sB₄, sA₄, hV₄, hbv₄, hav₄, hxv₄, h₄, tr₄⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "K_MPTR" R.consts]) (Expr.lit (.number k)) vkSucc
        (pr_mload R "K_MPTR") pureLit pr_succ (nh_mload_site R "K_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₃
    have hx₄ : x₄ = x₃ &&& b2w (decide (av₃ = bv₃)) :=
      Option.some.inj ((vk_var_hsite hxv₄).symm.trans hg₃)
    have bit₄ : Midfall.Yul.VKP.IsBit x₄ := by
      rw [hx₄]
      exact wb₃
    have wb₄ : Midfall.Yul.VKP.IsBit (x₄ &&& b2w (decide (av₄ = bv₄))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₄
    have hg₄ : VEnv.get V₄ "success" = some (x₄ &&& b2w (decide (av₄ = bv₄))) :=
      hV₄ ▸ get_set_succ hg₃
    obtain ⟨x₅, av₅, bv₅, V₅, st₅, sB₅, sA₅, hV₅, hbv₅, hav₅, hxv₅, h₅, tr₅⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "HAS_ACCUMULATOR_MPTR" R.consts]) (Expr.lit (.number w)) vkSucc
        (pr_mload R "HAS_ACCUMULATOR_MPTR") pureLit pr_succ (nh_mload_site R "HAS_ACCUMULATOR_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₄
    have hx₅ : x₅ = x₄ &&& b2w (decide (av₄ = bv₄)) :=
      Option.some.inj ((vk_var_hsite hxv₅).symm.trans hg₄)
    have bit₅ : Midfall.Yul.VKP.IsBit x₅ := by
      rw [hx₅]
      exact wb₄
    have wb₅ : Midfall.Yul.VKP.IsBit (x₅ &&& b2w (decide (av₅ = bv₅))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₅
    have hg₅ : VEnv.get V₅ "success" = some (x₅ &&& b2w (decide (av₅ = bv₅))) :=
      hV₅ ▸ get_set_succ hg₄
    obtain ⟨x₆, av₆, bv₆, V₆, st₆, sB₆, sA₆, hV₆, hbv₆, hav₆, hxv₆, h₆, tr₆⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "ACC_OFFSET_MPTR" R.consts]) (Expr.lit (.number o)) vkSucc
        (pr_mload R "ACC_OFFSET_MPTR") pureLit pr_succ (nh_mload_site R "ACC_OFFSET_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₅
    have hx₆ : x₆ = x₅ &&& b2w (decide (av₅ = bv₅)) :=
      Option.some.inj ((vk_var_hsite hxv₆).symm.trans hg₅)
    have bit₆ : Midfall.Yul.VKP.IsBit x₆ := by
      rw [hx₆]
      exact wb₅
    have wb₆ : Midfall.Yul.VKP.IsBit (x₆ &&& b2w (decide (av₆ = bv₆))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₆
    have hg₆ : VEnv.get V₆ "success" = some (x₆ &&& b2w (decide (av₆ = bv₆))) :=
      hV₆ ▸ get_set_succ hg₅
    obtain ⟨x₇, av₇, bv₇, V₇, st₇, sB₇, sA₇, hV₇, hbv₇, hav₇, hxv₇, h₇, tr₇⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "NUM_ACC_LIMBS_MPTR" R.consts]) (Expr.lit (.number l)) vkSucc
        (pr_mload R "NUM_ACC_LIMBS_MPTR") pureLit pr_succ (nh_mload_site R "NUM_ACC_LIMBS_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₆
    have hx₇ : x₇ = x₆ &&& b2w (decide (av₆ = bv₆)) :=
      Option.some.inj ((vk_var_hsite hxv₇).symm.trans hg₆)
    have bit₇ : Midfall.Yul.VKP.IsBit x₇ := by
      rw [hx₇]
      exact wb₆
    have wb₇ : Midfall.Yul.VKP.IsBit (x₇ &&& b2w (decide (av₇ = bv₇))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₇
    have hg₇ : VEnv.get V₇ "success" = some (x₇ &&& b2w (decide (av₇ = bv₇))) :=
      hV₇ ▸ get_set_succ hg₆
    obtain ⟨x₈, av₈, bv₈, V₈, st₈, sB₈, sA₈, hV₈, hbv₈, hav₈, hxv₈, h₈, tr₈⟩ :=
      vk_hdr_peelT R (Expr.builtin Op.mload [vkSite "NUM_ACC_LIMB_BITS_MPTR" R.consts]) (Expr.lit (.number b)) vkSucc
        (pr_mload R "NUM_ACC_LIMB_BITS_MPTR") pureLit pr_succ (nh_mload_site R "NUM_ACC_LIMB_BITS_MPTR") (fun st₁ st₃ h => nh_lit h)
        nh_succ h₇
    have hx₈ : x₈ = x₇ &&& b2w (decide (av₇ = bv₇)) :=
      Option.some.inj ((vk_var_hsite hxv₈).symm.trans hg₇)
    have bit₈ : Midfall.Yul.VKP.IsBit x₈ := by
      rw [hx₈]
      exact wb₇
    have wb₈ : Midfall.Yul.VKP.IsBit (x₈ &&& b2w (decide (av₈ = bv₈))) :=
      Midfall.Yul.VKP.isBit_and_b2w _ bit₈
    have hg₈ : VEnv.get V₈ "success" = some (x₈ &&& b2w (decide (av₈ = bv₈))) :=
      hV₈ ▸ get_set_succ hg₇
    rcases vkS9_peelT R "ERR_VK_MISMATCH" hg₈ wb₈ hfail h₈ with hleft | ⟨st₉, h₉, tr₉, hs₈⟩
    · exact Or.inl hleft
    · obtain ⟨x₁₀, av₁₀, bv₁₀, V₁₀, st₁₀, sB₁₀, sA₁₀, hV₁₀, hbv₁₀, hav₁₀, hxv₁₀, h₁₀, tr₁₀⟩ :=
        vk_hdr_peelT R (Expr.lit (.number q)) (Expr.builtin Op.calldataload [vkSite "PROOF_LEN_CPTR" R.consts]) vkSucc pureLit (pr_cdl R "PROOF_LEN_CPTR") pr_succ (fun st₁ st₃ h => nh_lit h) (nh_cdl_site R "PROOF_LEN_CPTR") nh_succ h₉
      have hx₁₀ : x₁₀ = (1 : U256) :=
        Option.some.inj ((vk_var_hsite hxv₁₀).symm.trans hs₈)
      have bit₁₀ : Midfall.Yul.VKP.IsBit x₁₀ := by
        rw [hx₁₀]
        exact Midfall.Yul.VKP.isBit_one
      have wb₁₀ : Midfall.Yul.VKP.IsBit (x₁₀ &&& b2w (decide (av₁₀ = bv₁₀))) :=
        Midfall.Yul.VKP.isBit_and_b2w _ bit₁₀
      have hg₁₀ : VEnv.get V₁₀ "success" = some (x₁₀ &&& b2w (decide (av₁₀ = bv₁₀))) :=
        hV₁₀ ▸ get_set_succ hs₈
      obtain ⟨x₁₁, av₁₁, bv₁₁, V₁₁, st₁₁, sB₁₁, sA₁₁, hV₁₁, hbv₁₁, hav₁₁, hxv₁₁, h₁₁, tr₁₁⟩ :=
        vk_hdr_peelT R (Expr.lit (.number n)) (Expr.builtin Op.calldataload [vkSite "NUM_INSTANCE_CPTR" R.consts]) vkSucc pureLit (pr_cdl R "NUM_INSTANCE_CPTR") pr_succ (fun st₁ st₃ h => nh_lit h) (nh_cdl_site R "NUM_INSTANCE_CPTR") nh_succ h₁₀
      have hx₁₁ : x₁₁ = x₁₀ &&& b2w (decide (av₁₀ = bv₁₀)) :=
        Option.some.inj ((vk_var_hsite hxv₁₁).symm.trans hg₁₀)
      have bit₁₁ : Midfall.Yul.VKP.IsBit x₁₁ := by
        rw [hx₁₁]
        exact wb₁₀
      have wb₁₁ : Midfall.Yul.VKP.IsBit (x₁₁ &&& b2w (decide (av₁₁ = bv₁₁))) :=
        Midfall.Yul.VKP.isBit_and_b2w _ bit₁₁
      have hg₁₁ : VEnv.get V₁₁ "success" = some (x₁₁ &&& b2w (decide (av₁₁ = bv₁₁))) :=
        hV₁₁ ▸ get_set_succ hg₁₀
      obtain ⟨x₁₂, av₁₂, bv₁₂, V₁₂, st₁₂, sB₁₂, sA₁₂, hV₁₂, hbv₁₂, hav₁₂, hxv₁₂, h₁₂, tr₁₂⟩ :=
        vk_hdr_peelT R (Expr.builtin Op.calldatasize []) (Expr.builtin Op.add [vkSite "INSTANCE_CPTR" R.consts, Expr.lit (.number (n * 32))]) vkSucc pureCdsz (pr_add R (pureSite R "INSTANCE_CPTR") pureLit) pr_succ (fun st₁ st₃ h => nh_cdsz h) (nh_add_site_lit R "INSTANCE_CPTR" (n * 32)) nh_succ h₁₁
      have hx₁₂ : x₁₂ = x₁₁ &&& b2w (decide (av₁₁ = bv₁₁)) :=
        Option.some.inj ((vk_var_hsite hxv₁₂).symm.trans hg₁₁)
      have bit₁₂ : Midfall.Yul.VKP.IsBit x₁₂ := by
        rw [hx₁₂]
        exact wb₁₁
      have wb₁₂ : Midfall.Yul.VKP.IsBit (x₁₂ &&& b2w (decide (av₁₂ = bv₁₂))) :=
        Midfall.Yul.VKP.isBit_and_b2w _ bit₁₂
      have hg₁₂ : VEnv.get V₁₂ "success" = some (x₁₂ &&& b2w (decide (av₁₂ = bv₁₂))) :=
        hV₁₂ ▸ get_set_succ hg₁₁
      rcases vkS9_peelT R "ERR_BAD_CALLDATA_SHAPE" hg₁₂ wb₁₂ hfail h₁₂ with hleft |
          ⟨st₁₃, h₁₃, tr₁₃, hs₁₂⟩
      · exact Or.inl hleft
      · have h12val : x₁₂ &&& b2w (decide (av₁₂ = bv₁₂)) = 1 :=
          (Option.some.inj (hs₁₂.symm.trans hg₁₂)).symm
        cases h₁₃
        -- GAP (ii): the last guard forces the chain to 1, and an 'and' of two bits is 1 only when
        -- both are, so all three comparisons held. Read BACKWARDS: S12, then S11, then S10.
        obtain ⟨hx₁₂', hy₁₂'⟩ := isBit_and_eq_one bit₁₂ (isBit_b2w _) h12val
        obtain ⟨hx₁₁', hy₁₁'⟩ := isBit_and_eq_one bit₁₁ (isBit_b2w _)
          (by rw [hx₁₂] at hx₁₂'; exact hx₁₂')
        obtain ⟨hx₁₀', hy₁₀'⟩ := isBit_and_eq_one bit₁₀ (isBit_b2w _)
          (by rw [hx₁₁] at hx₁₁'; exact hx₁₁')
        have eq₁₂ : av₁₂ = bv₁₂ := (Midfall.Yul.Word.b2w_decide_eq_one_iff _).mp hy₁₂'
        have eq₁₁ : av₁₁ = bv₁₁ := (Midfall.Yul.Word.b2w_decide_eq_one_iff _).mp hy₁₁'
        have eq₁₀ : av₁₀ = bv₁₀ := (Midfall.Yul.Word.b2w_decide_eq_one_iff _).mp hy₁₀'
        -- the three values, read off the run
        obtain ⟨aP, hvalP, heqP, hstP⟩ := vk_cdl_val R "PROOF_LEN_CPTR" hbv₁₀
        have hP : vkVal "PROOF_LEN_CPTR" R V₈ = some (BitVec.ofNat 256 a1) := by
          simp only [vkVal, hP1]
        obtain ⟨rfl⟩ := Option.some.inj (hP.symm.trans hvalP)
        obtain ⟨he₁₀, _⟩ := vk_lit_val hav₁₀
        obtain ⟨aN, hvalN, heqN, hstN⟩ := vk_cdl_val R "NUM_INSTANCE_CPTR" hbv₁₁
        have hN : vkVal "NUM_INSTANCE_CPTR" R V₁₀ = some (BitVec.ofNat 256 a2) := by
          simp only [vkVal, hP2]
        obtain ⟨rfl⟩ := Option.some.inj (hN.symm.trans hvalN)
        obtain ⟨he₁₁, _⟩ := vk_lit_val hav₁₁
        obtain ⟨he₁₂, _⟩ := vk_cdsz_val hav₁₂
        obtain ⟨hvs, hvalI, he₁₃, _⟩ := vk_add_site_val R "INSTANCE_CPTR" (n * 32) hbv₁₂
        have hI : vkVal "INSTANCE_CPTR" R V₁₁ = some (BitVec.ofNat 256 a3) := by
          simp only [vkVal, hP3]
        obtain ⟨rfl⟩ := Option.some.inj (hI.symm.trans hvalI)
        -- GAP (iii): the state transfer, chained through all thirteen statements
        have S₂ : st₂.env = st₁.env ∧ st₂.halted = st₁.halted := ⟨e₂, h₂'⟩
        have E₈ : st₈.env = st.env :=
          tr₈.1.trans (tr₇.1.trans (tr₆.1.trans (tr₅.1.trans (tr₄.1.trans (tr₃.1.trans
            (S₂.1.trans tr₁.1))))))
        have E₁₁ : st₁₁.env = st.env := tr₁₁.1.trans (tr₁₀.1.trans (tr₉.1.trans E₈))
        have SB₁₀ : sB₁₀.env = st.env :=
          (pr_cdl R "PROOF_LEN_CPTR" st₉ sB₁₀ bv₁₀ hbv₁₀).1.trans (tr₉.1.trans E₈)
        have SB₁₁ : sB₁₁.env = st.env :=
          (pr_cdl R "NUM_INSTANCE_CPTR" st₁₀ sB₁₁ bv₁₁ hbv₁₁).1.trans
            (tr₁₀.1.trans (tr₉.1.trans E₈))
        have hneS : ("r" : Ident) ≠ "success" := by decide
        have hneV : ("vk" : Ident) ≠ "success" := by decide
        have q3 : VEnv.get V₃ "r" = VEnv.get V "r" := hV₃ ▸ set_success_other hneS
        have q4 : VEnv.get V₄ "r" = VEnv.get V "r" := hV₄ ▸ (set_success_other hneS).trans q3
        have q5 : VEnv.get V₅ "r" = VEnv.get V "r" := hV₅ ▸ (set_success_other hneS).trans q4
        have q6 : VEnv.get V₆ "r" = VEnv.get V "r" := hV₆ ▸ (set_success_other hneS).trans q5
        have q7 : VEnv.get V₇ "r" = VEnv.get V "r" := hV₇ ▸ (set_success_other hneS).trans q6
        have q8 : VEnv.get V₈ "r" = VEnv.get V "r" := hV₈ ▸ (set_success_other hneS).trans q7
        have q10 : VEnv.get V₁₀ "r" = VEnv.get V "r" :=
          hV₁₀ ▸ (set_success_other hneS).trans q8
        have q11 : VEnv.get V₁₁ "r" = VEnv.get V "r" :=
          hV₁₁ ▸ (set_success_other hneS).trans q10
        have q12 : VEnv.get Vb "r" = VEnv.get V "r" :=
          hV₁₂ ▸ (set_success_other hneS).trans q11
        have w3 : VEnv.get V₃ "vk" = VEnv.get V "vk" := hV₃ ▸ set_success_other hneV
        have w4 : VEnv.get V₄ "vk" = VEnv.get V "vk" := hV₄ ▸ (set_success_other hneV).trans w3
        have w5 : VEnv.get V₅ "vk" = VEnv.get V "vk" := hV₅ ▸ (set_success_other hneV).trans w4
        have w6 : VEnv.get V₆ "vk" = VEnv.get V "vk" := hV₆ ▸ (set_success_other hneV).trans w5
        have w7 : VEnv.get V₇ "vk" = VEnv.get V "vk" := hV₇ ▸ (set_success_other hneV).trans w6
        have w8 : VEnv.get V₈ "vk" = VEnv.get V "vk" := hV₈ ▸ (set_success_other hneV).trans w7
        have w10 : VEnv.get V₁₀ "vk" = VEnv.get V "vk" :=
          hV₁₀ ▸ (set_success_other hneV).trans w8
        have w11 : VEnv.get V₁₁ "vk" = VEnv.get V "vk" :=
          hV₁₁ ▸ (set_success_other hneV).trans w10
        have w12 : VEnv.get Vb "vk" = VEnv.get V "vk" :=
          hV₁₂ ▸ (set_success_other hneV).trans w11
        have z3 : V₃.length = V.length := hV₃ ▸ VEnv.set_length
        have z4 : V₄.length = V.length := hV₄ ▸ (VEnv.set_length (x := "success")).trans z3
        have z5 : V₅.length = V.length := hV₅ ▸ (VEnv.set_length (x := "success")).trans z4
        have z6 : V₆.length = V.length := hV₆ ▸ (VEnv.set_length (x := "success")).trans z5
        have z7 : V₇.length = V.length := hV₇ ▸ (VEnv.set_length (x := "success")).trans z6
        have z8 : V₈.length = V.length := hV₈ ▸ (VEnv.set_length (x := "success")).trans z7
        have z10 : V₁₀.length = V.length := hV₁₀ ▸ (VEnv.set_length (x := "success")).trans z8
        have z11 : V₁₁.length = V.length := hV₁₁ ▸ (VEnv.set_length (x := "success")).trans z10
        have z12 : Vb.length = V.length := hV₁₂ ▸ (VEnv.set_length (x := "success")).trans z11
        have e10 : st₁₀.env = st.env := tr₁₀.1.trans (tr₉.1.trans E₈)
        have e11 : st₁₁.env = st.env := tr₁₁.1.trans e10
        have e12 : st₁₂.env = st.env := tr₁₂.1.trans e11
        have k3 : st₃.halted = st.halted := tr₃.2.1.trans (S₂.2.trans tr₁.2.1)
        have k10 : st₁₀.halted = st.halted :=
          tr₁₀.2.1.trans (tr₉.2.1.trans (tr₈.2.1.trans (tr₇.2.1.trans (tr₆.2.1.trans
            (tr₅.2.1.trans (tr₄.2.1.trans k3))))))
        have k11 : st₁₁.halted = st.halted := tr₁₁.2.1.trans k10
        have k12 : st₁₂.halted = st.halted := tr₁₂.2.1.trans k11
        have m10 : st₁₀.memory = st₂.memory :=
          tr₁₀.2.2.trans (tr₉.2.2.trans (tr₈.2.2.trans (tr₇.2.2.trans (tr₆.2.2.trans
            (tr₅.2.2.trans (tr₄.2.2.trans tr₃.2.2))))))
        have m11 : st₁₁.memory = st₂.memory := tr₁₁.2.2.trans m10
        have m12 : st₁₂.memory = st₂.memory := tr₁₂.2.2.trans m11
        have e9 : st₉.env = st.env := tr₉.1.trans E₈
        have C1 : wordFrom st.env.calldata (BitVec.ofNat 256 a1).toNat = BitVec.ofNat 256 q := by
          rw [← e9, heqP.symm, eq₁₀.symm, he₁₀]
        have C2 : wordFrom st.env.calldata (BitVec.ofNat 256 a2).toNat = BitVec.ofNat 256 n := by
          rw [← e10, heqN.symm, eq₁₁.symm, he₁₁]
        have SB₁₂ : sB₁₂.env = st.env :=
          ((pr_add R (pureSite R "INSTANCE_CPTR") pureLit) st₁₁ sB₁₂ bv₁₂ hbv₁₂).1.trans e11
        have C3 : BitVec.ofNat 256 st.env.calldata.length =
            BitVec.ofNat 256 a3 + BitVec.ofNat 256 (n * 32) := by
          rw [← SB₁₂, he₁₂.symm, eq₁₂, he₁₃]
        refine Or.inr ⟨rfl, hs₁₂, q12, w12, z12, ?_, ?_, ?_, C1, C2, C3⟩
        · exact tr₁₃.1.trans e12
        · exact tr₁₃.2.1.trans k12
        · rw [tr₁₃.2.2, m12, hmem, tr₁.2.2, tr₁.1]

/-! ## 5. THE WRAP REFUTATION - PG-VKMEMORYFIT -/

/- **THE REFUTATION, PROVED: the copy does not establish the payload clause when the destination
    wraps, and 'ValidV3' carries nothing that rules the wrap out.**

    THE MECHANISM. 'vkS2' is 'extcodecopy(vk, VK_MPTR, 1, EXPECTED_VK_PAYLOAD_LENGTH)'. Both the
    destination and the length are Yul *words*: the argument evaluates to 'BitVec.ofNat 256 m' and
    the semantics (EVMExec.lean:854) writes at 'dst.toNat = m % 2 ^ 256'. 'Inv .vk' then reads the
    payload window at the *Nat* 'ptrAddr pv.memory.vkMptr' (Inv.lean:741). The two addresses agree
    exactly when the address fits a word. Here is a memory, an address, a length and a payload for
    which they do not: the bytes land at address 0, the window 'Inv' reads is untouched, and the
    clause is false. The instance is deliberately render-free - the failure is in the semantics of
    the write, not in any render - and it is what makes the walk's conclusion
    'memory = copyInto ... (BitVec.ofNat 256 mVk).toNat ...' NOT rewrite to the clause 'Inv .vk'
    asks for.

    WHY THIS IS A CLASS-WIDTH FINDING AND NOT A MISSING LEMMA. 'programOkCore'
    (LoweringV3/Statements.lean:983) bounds the CALLDATA length ('cdBoundB'), the transcript region
    ('transcriptRegionOk'), the g1_identity FLOOR ('g1IdentityFloor') and the neg-Lagrange count
    ('negLagrangesFloor'). NOTHING in 'ValidV3', 'Render.Valid', a row, a bundle or the root bounds
    a memory address or a payload size: 'Value.asUsizeNat' (Generator/Layout.lean:1010) returns an
    arbitrary 'Nat' for a non-negative 'Int', and 'Halo2VerifyingKey.len' (Generator/Models.lean:462)
    is a sum of list lengths no clause constrains. So either the class is too wide - a render with
    'ptrAddr pv.memory.vkMptr >= 2 ^ 256' would admit a clean exit that satisfies neither 'Inv .vk'
    nor 'Poisoned' - or a bound is missing from the clause table. Per D-P71 nothing was added to
    'ValidV3', to a row, to a bundle or to the root, and per the objective's rule for this case no
    counter-hypothesis was attached to the row either.

    WHAT IS NOT CLAIMED. No render is exhibited, because none can be: 'ValidV3' has no named
    inhabitant until WP B4 ('gap_lowering_correct_witness_unexhibited'), so the full counterexample
    'ValidV3 R /\ 2 ^ 256 <= ptrAddr pv.memory.vkMptr /\ the block exits normal and neither arm
    holds' cannot be closed by a witness in this tree. What is proved here is the mechanism, which
    is the half the human needs to decide the class-width question.

    NAMED GAP: **PG-VKMEMORYFIT** - owner blank pending the human. Exact goal state, at the point
    where the assembly stops (with 'hmem' the walk's copy equation and 'hdisj' from
    'MemoryPairs.row_premises_of_generated'):

      bytesAt st' (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len == R.pv.vk.bytes
      st'.memory = copyInto st.memory (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat 1
        (BitVec.ofNat 256 R.pv.vk.len).toNat (st.env.extCodeOf vkAddr)

    and the two missing facts are

      (fit1) (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat = ptrAddr R.pv.memory.vkMptr
      (fit2) (BitVec.ofNat 256 R.pv.vk.len).toNat = R.pv.vk.len -/
/-- The all-zero memory and the state that carries it: the two helpers exist so the refutation below
    fits on lines the parser can read (a structure-update whose field value starts a new line at a
    column shallower than the opening brace is a parse error). -/
def zeroMem : Nat → UInt8 := fun _ => (0 : UInt8)

def stWithMem (mem : Nat → UInt8) : EvmState := { EvmState.init with memory := mem }

theorem wrap_breaks_payload_clause :
    ∃ (m n : Nat) (code : List UInt8) (payload : Bytes),
      2 ^ 256 ≤ m ∧ 0 < n ∧ code.length = n + 1 ∧ payload.size = n ∧
        bytesAt (stWithMem (copyInto zeroMem (BitVec.ofNat 256 m).toNat 1 n code)) m n ≠ payload := by
  refine ⟨2 ^ 256, 1, [0, 1], ByteArray.mk #[(1 : UInt8)], by omega, by decide, by decide,
    by decide, ?_⟩
  have hw : (BitVec.ofNat 256 (2 ^ 256)).toNat = 0 := by decide
  rw [hw]
  decide

/-! ## 5b. PG-VKMEMORYFIT - SETTLED: 'fit1' AND 'fit2' ARE NOT THEOREMS OF 'generated' (WP VKFIT).

  The card that opened this gap recorded it as needing a HUMAN CHOICE between '(1) derive the two
  fits from the `generated` clause' and '(2) add a frozen conjunct', and flagged (1) as viable
  because LAYOUT had just derived three facts of the same species from the same clause. This card
  tried (1) and PROVED IT FALSE. All three routes the brief named are now closed:

  * ROUTE 1, THE ARENA CHAIN - REFUTED at `MemoryPairs.new_vkMptr_image_unbounded`. The premise
    was that `VerifierMemoryLayout.new` emits only sums of small literals, so every `ptrAddr` is
    below `2 ^ 256` by arithmetic. `vkMptr` is not emitted by the arena: `new_vkMptr` is `rfl`, the
    field is the ARGUMENT, and `ptrAddr_valueFromNat` makes `ptrAddr` surjective onto `Nat`. For
    every bound `B` the constructor image contains a layout with `B <= ptrAddr L.vkMptr`, so the
    equation `plan_memory_eq_new` - which is the whole of what `generated` says about the memory -
    cannot bound `fit1`. `generated_face_allows_fit1_to_fail` states the wrap outright.
  * ROUTE 1 DEEPER - the pointer the planner hands `new` is `ptrMemory (valueFromNat n)` where `n`
    is `staticWorkingMemorySizeForMeta` (Vk.lean:971-990, reached through
    `metaDataForStableStaticLayout` at VK:535 and the loop's rebind at :543), i.e. a maximum of six
    ends of the shape `literal + (Nat field of the meta) * 32`. Those fields are `Nat`s and `List`
    lengths of an arbitrary constraint system, so no peel of `generated` bounds them either. NOT
    formalised as a theorem: the witness would need a constraint system with `2 ^ 256` selectors,
    which no decidable procedure in this tree can evaluate. Stated as the measured reason, not as a
    claim.
  * ROUTE 2, `supported.layout` - REFUTED by LAYOUT at `MemoryPairs.layout_windows_not_tied_to_the_map`.
    `MemoryMap.wellFormedBool` (Layout.lean:1114)
    bounds a region START only from BELOW (`solidityReservedMemoryBytes <= start`) and by alignment,
    and `validate` (Layout.lean:1023) compares the seven fixed low pointers, the spill floor, the
    scalar-inversion scratch and four PCS capacities. Nothing bounds an address from above.
  * ROUTE 3, THE PAYLOAD LENGTH - REFUTED at `MemoryPairs.vkLen_unbounded`.
    `Halo2VerifyingKey.len` is three `List.length`s (`Models.lean:461-462`) and `List.replicate`
    shows the type carries no size bound; `extendVk` appends to the constant table and raises `len`
    by 32 bytes per word (`extendVk_len`), and `fit2_can_fail` crosses the boundary. OBJ.4's
    `payloadLen`/`vkLen` route proves `runtimeBytes.size = vk.len + 1` FROM `constsCoherent` - an
    equation between two unbounded `Nat`s, not a bound on either. And the ONE payload gate the
    generator's ok-path enforces cannot see the growth: `MemoryPairs.vkCarriesBuild_extend` proves
    `vkCarriesBuild` is INVARIANT under `extendVk` whenever the two quotient slices end inside the
    original prefix. So nothing on the generated path bounds `vk.len`.
  * THE CONTRAST THAT MAKES IT PRECISE. The tree already bounds a layout pointer from above:
    `PrefixV3.transcriptMptr_lt` gets `R.pv.memory.transcriptMptr < 2 ^ 256` from `validate`'s
    `fixedLowMemory` loop, because the constructor EMITS the literal for that pointer
    (`MemoryPairs.new_transcriptMptr_eq`, `rfl`). It EMITS THE ARGUMENT for the VK pointer
    (`MemoryPairs.new_vkMptr_eq_arg`, also `rfl`): `vk_mptr` is the eighth pointer, the output of
    the reservation loop at VK:535-544, and `validate` ties it only to `scalarInvScratchMptr`, which
    `new` builds from the same `vkStart` (LayoutMemory.lean:190-194) - a tautology, not a bound.
    That is the exact reason the class is too wide, and it is a faithful-port fact: rule R5 made the
    reference's `usize` into `Nat`, and a 64-bit `usize` could not wrap a 256-bit word.

  THE ONLY `2 ^ 256` FACT IN THE CLAUSE TABLE is `cdBoundB` (Statements.lean:2057-2058, projected as
  `cdBound_of_valid`), and it bounds `R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances` -
  the CALLDATA layout, a different field of the plan from `memory.vkMptr`. So the gap is real class
  width, not a missing lemma.

  WHAT IS, AND IS NOT, CLAIMED. What is proved is that NOTHING IN `ValidV3` RULES THE WRAP OUT: the
  clause's own content about the memory is the constructor equation, and the constructor image
  contains wrapping addresses (`generated_face_allows_fit1_to_fail`), while the payload gate is blind
  to the growth (`vkCarriesBuild_extend`). What is NOT proved - and cannot be, until WP B4 exhibits a
  render - is that a `ValidV3` render with `2 ^ 256 <= ptrAddr pv.memory.vkMptr` EXISTS. STATUS.md
  row 7 currently says `vk_blockSim` 'is FALSE for some valid render'; the defensible form is 'is not
  provable from `ValidV3` as written, because `ValidV3` carries no bound that would make it true'.
  `wrap_breaks_payload_clause` above is the mechanism that makes the row false of any such render.

  WHAT THIS DOES NOT DO. No hypothesis was added to `ValidV3`, to `programOkCore`, to a row, to a
  pin bundle or to the root, and no frozen file was touched: the fix is a new `memoryFitB`-style
  conjunct, which is a signed decision plus one of W15's two remaining re-hashes and therefore the
  human's call. Nor is the row stated with the bound as a hypothesis - option (3) is refused on the
  record. What IS left ready for whoever closes it: `MemoryPairs.fit1_of_bound` and
  `MemoryPairs.fit2_of_bound` turn the two `2 ^ 256` bounds into exactly the two equations this
  walk stops on, and `MemoryPairs.row_premises_of_generated` already supplies hdisj, hnum and hcode.
  No new `sorry` is introduced anywhere in this section, so W12 does not bite.

  **UPDATE - D-QVM1 WAS SIGNED 2026-11-21 AND THIS GAP IS CLOSED.** `programOk` now carries
  `programFits`, whose VK half is `ptrAddr pv.memory.vkMptr + pv.vk.len < 2 ^ 256` and the runtime
  length bound. `MemoryPairs.fit1_of_valid` and `fit2_of_valid` are therefore THEOREMS of `ValidV3`
  (proved, cone 0, standard three), and the reassembly this section said was waiting on the
  decision can read them directly. The two `..._can_fail` refutations stay: they show why the
  clause, not `generated`, has to carry the bound. -/
#print axioms Midfall.LoweringV3.VkClean.wrap_breaks_payload_clause
#print axioms Midfall.LoweringV3.VkClean.vkBody_clean_walk
#print axioms Midfall.LoweringV3.VkClean.vkS1_peelT
#print axioms Midfall.LoweringV3.VkClean.vkS2_peelT
#print axioms Midfall.LoweringV3.VkClean.vk_hdr_peelT
#print axioms Midfall.LoweringV3.VkClean.vkS9_peelT
#print axioms Midfall.LoweringV3.VkClean.isBit_and
#print axioms Midfall.LoweringV3.VkClean.vk_cdl_val
#print axioms Midfall.LoweringV3.VkClean.vk_add_site_val
#cone_sorries Midfall.LoweringV3.VkClean.vkBody_clean_walk

/-! ## 6. STAGEINV .vk FROM THE CLEAN WALK (D-QVM1's fit, consumed)

  This is the reassembly sections 5 and 5b said was waiting on a bound. D-QVM1 signed the bound
  (`programFits`) and `MemoryPairs.fit1_of_valid` / `fit2_of_valid` are its theorems, so the two
  equations the walk stops on are no longer hypotheses:

    (fit1) the copy destination `BitVec.ofNat 256 (ptrAddr vkMptr)` reads back the Nat address;
    (fit2) the copy length `BitVec.ofNat 256 vk.len` reads back the Nat length.

  With those, the walk's memory equation is a copy of the deployed runtime at exactly the window
  `Inv .vk` reads, and section 2's `bytesAt_copyInto_window` turns it into the payload clause;
  `bytesAt_copyInto_disjoint` plus `MemoryPairs.vkPins_disjoint_of_generated` keep the g1_identity
  clause; the walk's third calldata equality plus `cdBound_of_valid` give the calldata-length
  clause; and the three words `envelopeOk` wants are the walk's first two equalities plus
  `abiHeadOk`'s own static facts. No hypothesis is added anywhere. -/

/-- A word-level equation whose right side is a sum below `2 ^ 256` is a `Nat` equation when the
    left side already fits. This is the single arithmetic step the calldata clause needs; `omega`
    is not used because `2 ^ 256` is in the statement. -/
theorem ofNat_eq_ofNat_add {L A B : Nat} (hL : L < 2 ^ 256) (hAB : A + B < 2 ^ 256)
    (h : BitVec.ofNat 256 L = BitVec.ofNat 256 A + BitVec.ofNat 256 B) : L = A + B := by
  have ht := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  rw [Nat.mod_eq_of_lt hL,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right A B) hAB),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left B A) hAB),
    Nat.mod_eq_of_lt hAB] at ht
  exact ht

/-- **THE CLEAN EXIT IS `StageInv .vk`.** Everything is read off the walk's conclusion plus
    `ValidV3`; the only state facts used are env/halted/memory and the `r`/`vk` lookup transfer. -/
theorem stageInv_vk_of_clean (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash)
    (vkAddr : U256) (cd : Bytes)
    {V Vb : VEnv (Bridge.Dialect c g)} {st stb : EvmState}
    (hbase : BaseInv R Checkpoint.start V st)
    (hframe : Frame R H vkAddr cd V st)
    (hraw : abiHeadOk R.plan.proofLayout cd = true)
    (hsucc : VEnv.get Vb "success" = some (1 : U256))
    (hr : VEnv.get Vb "r" = VEnv.get V "r")
    (hvk : VEnv.get Vb "vk" = VEnv.get V "vk")
    (henv : stb.env = st.env)
    (hhalt : stb.halted = st.halted)
    (hmem : stb.memory = copyInto st.memory
      (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat 1
      (BitVec.ofNat 256 R.pv.vk.len).toNat (st.env.extCodeOf vkAddr))
    (C1 : wordFrom st.env.calldata
      (BitVec.ofNat 256 (R.pv.proofLayout.proofCptr - 32)).toNat =
        BitVec.ofNat 256 R.pv.proofLayout.proofLen)
    (C2 : wordFrom st.env.calldata (BitVec.ofNat 256 R.pv.proofLayout.proofEnd).toNat =
        BitVec.ofNat 256 R.pv.numInstances)
    (C3 : BitVec.ofNat 256 st.env.calldata.length =
        BitVec.ofNat 256 (R.pv.proofLayout.proofEnd + 32) +
          BitVec.ofNat 256 (R.pv.numInstances * 32)) :
    StageInv R H vkAddr cd Checkpoint.vk Vb stb := by
  -- the plan view is the no-accumulator view of the plan, so its layout IS the plan's
  have hpv : R.pv = planViewOf R.plan R.model none := by
    show planViewOf R.plan R.model R.cfg.accumulator = _
    rw [hR.supported.noAcc]
  have hpl : R.pv.proofLayout = R.plan.proofLayout := by rw [hpv]; rfl
  -- the two row premises `ValidV3` carries: instance count and the calldata bound
  have hnum : R.pv.numInstances = R.cfg.numInstances :=
    (Midfall.LoweringV3.MemoryPairs.row_premises_of_generated R hR.generated hR.inputs.1
      hR.supported.separateVk).1
  have hbnd : R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances < 2 ^ 256 := by
    have h := cdBound_of_valid hR
    rw [hpl, hnum]
    exact h
  -- the Frame transfer
  have hfr : Frame R H vkAddr cd Vb stb := by
    refine ⟨?_, ?_, ?_, hframe.vkHash, hframe.vkNonEmpty, ?_, ?_, hframe.cdSize⟩
    · rw [henv]; exact hframe.calldata
    · rw [henv]; exact hframe.keccak
    · rw [henv]; exact hframe.vkCode
    · obtain ⟨rv, hl, hg⟩ := hframe.r
      exact ⟨rv, hl, by rw [hr]; exact hg⟩
    · rw [hvk]; exact hframe.vk
  -- the three `Inv .start` clauses the `.vk` clauses inherit
  have hstart : ((st.halted == none) = true ∧ LocalsOk (p := p) V = true) ∧
      (bytesAt st (ptrAddr R.pv.memory.g1IdentityMptr) 128 ==
        Midfall.natToBytesBE 0 128) = true := by
    have h := hbase
    change Midfall.Lowering.InvAt (calls := c) (gas := g) R.E R.params Checkpoint.start R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) V st = true at h
    simp only [Midfall.Lowering.InvAt] at h
    rw [ite_eq_right (by decide : ¬ (Checkpoint.vk ≤ Checkpoint.start)),
      ite_eq_right (by decide : ¬ (Checkpoint.transcript ≤ Checkpoint.start)),
      ite_eq_right (by decide : ¬ (Checkpoint.lagrange ≤ Checkpoint.start)),
      ite_eq_right (by decide : ¬ (Checkpoint.quotient ≤ Checkpoint.start)),
      ite_eq_right (by decide : ¬ (Checkpoint.pcs ≤ Checkpoint.start)),
      ite_eq_right (by decide : ¬ ((Checkpoint.start == Checkpoint.pairing) = true))] at h
    simpa only [Bool.and_true, Bool.and_eq_true] using h
  have hHaltB : (stb.halted == none) = true := by rw [hhalt]; exact hstart.1.1
  have hLocB : LocalsOk (p := p) Vb = true := by
    have hEq : LocalsOk (p := p) Vb = LocalsOk (p := p) V := by
      unfold LocalsOk
      rw [hr]
    rw [hEq, hstart.1.2]
  -- the memory equation, with the D-QVM1 fits
  have hmem' : stb.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
      (st.env.extCodeOf vkAddr) := by
    rw [hmem, Midfall.LoweringV3.MemoryPairs.fit1_of_valid hR,
      Midfall.LoweringV3.MemoryPairs.fit2_of_valid hR]
  -- the g1_identity window is disjoint from the copy, so it survives
  have hgiEq : bytesAt stb (ptrAddr R.pv.memory.g1IdentityMptr) 128 =
      bytesAt st (ptrAddr R.pv.memory.g1IdentityMptr) 128 := by
    have hread : readBytes stb.memory (ptrAddr R.pv.memory.g1IdentityMptr) 128 =
        readBytes st.memory (ptrAddr R.pv.memory.g1IdentityMptr) 128 := by
      rw [hmem']
      refine Midfall.LoweringV3.VkWindow.readBytes_copyInto_disjoint st.memory
        (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
        (ptrAddr R.pv.memory.g1IdentityMptr) 128 (st.env.extCodeOf vkAddr) ?_
      rcases Midfall.LoweringV3.MemoryPairs.vkPins_disjoint_of_generated hR.generated with
        h | h
      · exact Or.inr h
      · exact Or.inl h
    show ByteArray.mk (readBytes stb.memory (ptrAddr R.pv.memory.g1IdentityMptr) 128).toArray =
      ByteArray.mk (readBytes st.memory (ptrAddr R.pv.memory.g1IdentityMptr) 128).toArray
    rw [hread]
  have hgiB : (bytesAt stb (ptrAddr R.pv.memory.g1IdentityMptr) 128 ==
      Midfall.natToBytesBE 0 128) = true := by
    rw [hgiEq]; exact hstart.2
  -- the payload window: the copy's destination is the Nat address and the source is the runtime
  have hvkPv : R.pv.vk = R.plan.vk := by rw [hpv]; rfl
  have hpay : bytesAt stb (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes := by
    have hread : readBytes stb.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len =
        ((st.env.extCodeOf vkAddr).drop 1).take R.pv.vk.len := by
      rw [hmem']
      have h3 : 1 + (ptrAddr R.pv.memory.vkMptr - ptrAddr R.pv.memory.vkMptr) +
          R.pv.vk.len ≤ (st.env.extCodeOf vkAddr).length := by
        rw [Nat.sub_self, hframe.vkCode,
          Midfall.LoweringV3.VkWindow.runtimeBytes_length, hvkPv]
        omega
      simpa using Midfall.LoweringV3.VkWindow.readBytes_copyInto_window st.memory
        (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len
        (st.env.extCodeOf vkAddr) (Nat.le_refl _) (Nat.le_refl _) h3
    show ByteArray.mk (readBytes stb.memory (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len).toArray =
      R.pv.vk.bytes
    rw [hread, hframe.vkCode, hvkPv,
      Midfall.LoweringV3.VkWindow.runtimeBytes_drop_one_take]
  have hpayB : (bytesAt stb (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len == R.pv.vk.bytes) = true := by
    rw [hpay]; simp
  -- the calldata-length clause: the walk's third equality, read as a Nat equation
  have hL_lt : st.env.calldata.length < 2 ^ 256 := by
    rw [hframe.calldata]
    rw [← Array.size_eq_length_toList (xs := cd.data)]
    exact hframe.cdSize
  have hcdlen : st.env.calldata.length =
      R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances := by
    have hAB : (R.pv.proofLayout.proofEnd + 32) + R.pv.numInstances * 32 < 2 ^ 256 := by
      have h := hbnd
      rw [Nat.mul_comm 32 R.pv.numInstances] at h
      simpa [Nat.add_assoc] using h
    have h := ofNat_eq_ofNat_add hL_lt hAB C3
    rw [Nat.mul_comm (R.pv.numInstances) 32] at h
    simpa [Nat.add_assoc] using h
  have hcdB : (stb.env.calldata.length ==
      R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances) = true := by
    have hlen : stb.env.calldata.length =
        R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances := by
      rw [henv]; exact hcdlen
    rw [hlen]; simp
  have haccB : (R.pv.hasAccumulator == false ||
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)).acc.isSome) = true := by
    rw [pv_hasAccV3 R hR]
    rfl
  -- the `.vk` invariant: the three inherited clauses and the three `.vk` clauses
  have hbase_vk : Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params Checkpoint.vk
      R.pv (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) Vb stb := by
    show Midfall.Lowering.InvAt (calls := c) (gas := g) R.E R.params Checkpoint.vk R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) Vb stb = true
    simp only [Midfall.Lowering.InvAt]
    rw [ite_eq_left (by decide : Checkpoint.vk ≤ Checkpoint.vk),
      ite_eq_right (by decide : ¬ (Checkpoint.transcript ≤ Checkpoint.vk)),
      ite_eq_right (by decide : ¬ (Checkpoint.lagrange ≤ Checkpoint.vk)),
      ite_eq_right (by decide : ¬ (Checkpoint.quotient ≤ Checkpoint.vk)),
      ite_eq_right (by decide : ¬ (Checkpoint.pcs ≤ Checkpoint.vk)),
      ite_eq_right (by decide : ¬ ((Checkpoint.vk == Checkpoint.pairing) = true))]
    simp only [Bool.and_true]
    rw [hHaltB, hLocB, hgiB, hpayB, hcdB, haccB]
    rfl
  -- `envelopeOk`: `abiHeadOk` was the `.start` raw clause; the three words are C1, C2 and C3
  have hAbi' := hraw
  simp only [abiHeadOk, Bool.and_eq_true] at hAbi'
  have hcptrb : (R.plan.proofLayout.proofCptr == abiVerifyProofProofCptr) = true :=
    hAbi'.1.1.2
  have hendb : (R.plan.proofLayout.proofEnd ==
      R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen) = true := hAbi'.1.2
  have hcptrLit : abiVerifyProofProofCptr = 0x64 := by
    norm_num [abiVerifyProofProofCptr, abiSelectorBytes, abiVerifyProofHeadBytes,
      abiVerifyProofHeadWords, Midfall.Generator.wordBytes]
  have hcptr : R.plan.proofLayout.proofCptr = 0x64 := by
    have h := hcptrb
    rw [hcptrLit] at h
    exact eq_of_beq h
  have hend : R.plan.proofLayout.proofEnd =
      R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen := eq_of_beq hendb
  have hpe_lt : R.pv.proofLayout.proofEnd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hbnd)
  have hpl_lt : R.pv.proofLayout.proofLen < 2 ^ 256 := by
    rw [hpl]
    have h := hpe_lt
    rw [hpl, hend, hcptr] at h
    exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
  have hfitCptr : (BitVec.ofNat 256 (R.pv.proofLayout.proofCptr - 32)).toNat =
      R.pv.proofLayout.proofCptr - 32 := by
    rw [hpl, hcptr, BitVec.toNat_ofNat]
  have hfitEnd : (BitVec.ofNat 256 R.pv.proofLayout.proofEnd).toNat =
      R.pv.proofLayout.proofEnd := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hpe_lt
  have hC1' : wordFrom st.env.calldata (R.pv.proofLayout.proofCptr - 32) =
      BitVec.ofNat 256 R.pv.proofLayout.proofLen := by
    rw [hfitCptr] at C1
    exact C1
  have hC1w : cdWord cd 0x44 = BitVec.ofNat 256 R.pv.proofLayout.proofLen := by
    have h := hC1'
    rw [hframe.calldata, Midfall.LoweringV3.VkWindow.wordFrom_cdWord] at h
    have hidx : R.pv.proofLayout.proofCptr - 32 = 0x44 := by
      rw [hpl, hcptr]
    rwa [hidx] at h
  have hC1nat : (cdWord cd 0x44).toNat = R.pv.proofLayout.proofLen := by
    have h := congrArg BitVec.toNat hC1w
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl_lt] at h
    exact h
  have hfitEnd' : (BitVec.ofNat 256 R.pv.proofLayout.proofEnd).toNat =
      R.pv.proofLayout.proofEnd := hfitEnd
  have hC2' : wordFrom st.env.calldata R.pv.proofLayout.proofEnd =
      BitVec.ofNat 256 R.pv.numInstances := by
    rw [hfitEnd'] at C2
    exact C2
  have hC2w : cdWord cd R.pv.proofLayout.proofEnd =
      BitVec.ofNat 256 R.pv.numInstances := by
    have h := hC2'
    rw [hframe.calldata, Midfall.LoweringV3.VkWindow.wordFrom_cdWord] at h
    exact h
  have h32n_lt : 32 * R.pv.numInstances < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbnd
  have hnum_lt : R.pv.numInstances < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left R.pv.numInstances (by decide : 0 < 32)) h32n_lt
  have hC2nat : (cdWord cd R.pv.proofLayout.proofEnd).toNat = R.pv.numInstances := by
    have h := congrArg BitVec.toNat hC2w
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnum_lt] at h
    exact h
  have hp1 : ((cdWord cd 0x44).toNat == R.plan.proofLayout.proofLen) = true := by
    rw [hC1nat, hpl]; simp
  have hC2natL : (cdWord cd R.plan.proofLayout.proofEnd).toNat = R.pv.numInstances := by
    rw [← hpl]; exact hC2nat
  have hp2 : ((cdWord cd R.plan.proofLayout.proofEnd).toNat == R.cfg.numInstances) = true := by
    rw [hC2natL, hnum]; simp
  have hp3 : (cd.size == R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances) = true := by
    have hsize : cd.size = st.env.calldata.length := by
      rw [hframe.calldata]
      exact (Array.size_eq_length_toList (xs := cd.data)).symm
    have hlen' : st.env.calldata.length =
        R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances := by
      have h := hcdlen
      rw [hnum] at h
      rw [← hpl]
      exact h
    rw [hsize, hlen']; simp
  have henvOk : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true := by
    simp only [envelopeOk]
    rw [hraw, hp1, hp2, hp3]
    rfl
  refine ⟨hfr, hsucc, ?_, henvOk, trivial, ?_⟩
  · show Midfall.Lowering.Inv (calls := c) (gas := g) R.E R.params Checkpoint.vk R.pv
      (witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ)) Vb stb
    exact hbase_vk
  · intro ms instW inst hdec
    exact ⟨witnessSnapshot (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ), rfl, hbase_vk⟩

/-- **THE CLEAN HALF OF `BlockSim R .vkLoading`.** From `StageInv .start` every run either reverts
    or exits normally at `StageInv .vk`; the walk is `vkBody_clean_walk`, the reassembly is
    `stageInv_vk_of_clean`. -/
theorem vk_clean_walkV3 (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g)
      (R.scope c g) (R.slice Partial.vkLoading)
      (fun V st => StageInv R H vkAddr cd Checkpoint.start V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ StageInv R H vkAddr cd Checkpoint.vk V' st')) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hframe, hsucc, hbase, hraw, -, -⟩ := hpre
  have hcode : vkCodehashArm R.model :=
    (Midfall.LoweringV3.MemoryPairs.generated_model_facts hR.generated).2
      hR.supported.separateVk
  obtain ⟨hVK, hPL, hP1, hP2, hP3⟩ :=
    Midfall.LoweringV3.VkWindow.vkTableV3 hR hcode
  rw [vk_sliceV3 R hR] at hrun
  have hfail : lookupFun (R.scope (c) g) "fail" =
      some (failFDecl, R.scope (c) g) := fail_lookup R
  rcases Step.stmts_cons_inv
      (D := Bridge.Dialect (c) g) hrun with
    ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne⟩
  · cases hnil
    cases h₁ with
    | block hbody =>
        rename_i Vb
        have hfail' : lookupFun (hoist (Bridge.Dialect (c) g)
            (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
              R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
              R.pv.proofLayout.proofLen) ::
              R.scope (c) g) "fail" =
            some (failFDecl, R.scope (c) g) :=
          vkBody_fail_lookup R _ _ _ _ _ _ _ hfail
        rcases vkBody_clean_walk R vkAddr (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len
            (R.pv.proofLayout.proofCptr - 32) R.pv.proofLayout.proofEnd
            (R.pv.proofLayout.proofEnd + 32) hfail' hsucc hframe.vk hVK hPL hP1 hP2 hP3
            hbody with hrev | hclean
        · exact Or.inl hrev
        · obtain ⟨-, hsucc', hr', hvk', hlen', henv', hhalt', hmem', C1, C2, C3⟩ := hclean
          refine Or.inr ⟨rfl, ?_⟩
          have hres : restore V Vb = Vb := by
            show Vb.drop (Vb.length - V.length) = Vb
            rw [hlen', Nat.sub_self, List.drop_zero]
          rw [hres]
          exact stageInv_vk_of_clean R hR H vkAddr cd hbase hframe hraw hsucc' hr' hvk'
            henv' hhalt' hmem' C1 C2 C3
  · cases h₁ with
    | block hbody =>
        rename_i Vb
        have hfail' : lookupFun (hoist (Bridge.Dialect (c) g)
            (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
              R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
              R.pv.proofLayout.proofLen) ::
              R.scope (c) g) "fail" =
            some (failFDecl, R.scope (c) g) :=
          vkBody_fail_lookup R _ _ _ _ _ _ _ hfail
        rcases vkBody_clean_walk R vkAddr (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len
            (R.pv.proofLayout.proofCptr - 32) R.pv.proofLayout.proofEnd
            (R.pv.proofLayout.proofEnd + 32) hfail' hsucc hframe.vk hVK hPL hP1 hP2 hP3
            hbody with hrev | hclean
        · exact Or.inl hrev
        · exact absurd hclean.1 hne

/-- **CONJUNCT 2 OF `BlockSim R .vkLoading`, RESTATED FOR THE ROW.** `VkRow.vk_poison_walkV3`
    already proves the stronger statement (every run halts reverted), so the conjunct is one
    application; no `normal ∧ Poisoned` arm is needed. -/
theorem vk_poison_walkV3' (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
      (R.scope (permissive (callsOf product)) g) (R.slice Partial.vkLoading)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (Partial.vkLoading ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) := by
  intro V st hpois V' st' o hrun
  exact Or.inl (vk_poison_walkV3 R hR H vkAddr cd hpois hrun)

/-- **THE `vkLoading` SIMULATION ROW, PROVED FOR EVERY RENDER.** The two conjuncts of `BlockSim`
    over `StageInv`: the clean walk (`vk_clean_walkV3`) and the poisoned walk
    (`vk_poison_walkV3'`). Standard three, no `sorryAx`, no `native_decide`; `D-QVM1`'s
    `programFits` supplies the address and length fits the clean exit reads. -/
theorem vk_blockSimV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.vkLoading H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, vk_poison_walkV3' R product hR H vkAddr cd g⟩
  intro V st hpre V' st' o hrun
  rcases vk_clean_walkV3 (c := permissive (callsOf product)) R hR H vkAddr cd g V st hpre V' st' o hrun with hrev | hok
  · exact Or.inl hrev
  · exact Or.inr (Or.inl hok)

#print axioms Midfall.LoweringV3.VkClean.ofNat_eq_ofNat_add
#print axioms Midfall.LoweringV3.VkClean.stageInv_vk_of_clean
#print axioms Midfall.LoweringV3.VkClean.vk_clean_walkV3
#print axioms Midfall.LoweringV3.VkClean.vk_poison_walkV3'
#print axioms Midfall.LoweringV3.VkClean.vk_blockSimV3
#cone_sorries Midfall.LoweringV3.VkClean.vk_blockSimV3
#assert_axioms Midfall.LoweringV3.VkClean.vk_blockSimV3
  [propext, Classical.choice, Quot.sound] native []

/-! ## 7. THE PROGRESS ROW'S TWO VK PINS AT ValidV3, AND PG-VKHEADER

  `vk_blockProgS` differs from `vk_blockSim` in one decisive way: `exitProgAt` for a
  non-`traceReturn` block offers NO revert arm, so the progress row needs every run under
  `LeanAccepts` to exit NORMALLY. The clean walk (`vk_clean_walkV3`) already gives
  `halt ∧ Reverted ∨ normal ∧ StageInv .vk`, so the whole obligation is to rule out the halt.
  A halt of the vkLoading slice is always one of four guards firing:

  * S1 `iszero(and(eq(extcodesize(vk), EXPECTED_VK_LENGTH),
                    eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)))`;
  * S9 (after the six header checks) and S13 (after the three calldata checks):
    `iszero(success)`.

  The TABLE half of S1 is already a theorem of `ValidV3` (the two `vkProgressPins` fields,
  `consts_lookup_EXPECTED_VK_LENGTH_V3` / `_CODEHASH_WORD_V3` below); the calldata checks are
  forced by `LeanAccepts`'s `Decoded` through `envelopeOk`. The SIX HEADER CHECKS ARE NOT,
  and the exact missing fact is recorded at the end of this section as **PG-VKHEADER**. -/

/-- The derived `vkProgressPins.vkLen` at `ValidV3` (the `LoweringV2.Consts` proof runs on the
    frozen `Render.Valid`; `ValidV3` is a parallel copy, so the row needs this face). -/
theorem consts_lookup_EXPECTED_VK_LENGTH_V3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R)
    (h : vkCodehashArm R.model) :
    R.consts.lookup "EXPECTED_VK_LENGTH" = some R.plan.vk.runtimeBytes.size := by
  have hvk : R.pv.vk = R.plan.vk := rfl
  have hl := Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR "EXPECTED_VK_LENGTH"
    R.pv.vk.runtimeBytes.size
    (Midfall.LoweringV2.expectedConsts_lookup_EXPECTED_VK_LENGTH R.pv R.model h)
  rwa [hvk] at hl

/-- The derived `vkProgressPins.vkHash` at `ValidV3`. -/
theorem consts_lookup_EXPECTED_VK_CODEHASH_WORD_V3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R)
    (h : vkCodehashArm R.model) :
    R.consts.lookup "EXPECTED_VK_CODEHASH_WORD" =
      some (keccak256 R.plan.vk.runtimeBytes).toNat := by
  have hvk : R.pv.vk = R.plan.vk := rfl
  have hl := Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR
    "EXPECTED_VK_CODEHASH_WORD" (keccak256 R.pv.vk.runtimeBytes).toNat
    (Midfall.LoweringV2.expectedConsts_lookup_EXPECTED_VK_CODEHASH_WORD R.pv R.model h)
  rwa [hvk] at hl

/-- A nonzero `Fr` element is a nonzero word: `frWord` reduces modulo `2^256`, and
    `p = frModulusConstant < 2^256` keeps the residue nonzero. -/
theorem frWord_ne_zero_of_ne_zero {x : Fr p} (hmod : p = frModulusConstant) (hx : x ≠ 0) :
    frWord x ≠ 0 := by
  intro h
  apply hx
  have hval : x.val = 0 := by
    have ht := congrArg BitVec.toNat h
    simp only [frWord] at ht
    rw [BitVec.toNat_ofNat] at ht
    have hp2 : p < 2 ^ 256 := by rw [hmod]; norm_num [frModulusConstant]
    have hx2 : x.val < 2 ^ 256 := Nat.lt_trans (ZMod.val_lt x) hp2
    rw [Nat.mod_eq_of_lt hx2] at ht
    simpa using ht
  exact (ZMod.val_eq_zero x).mp hval

/-- `getD` past the end is the default; the tree's `List.getD_eq_default` is not imported on this
    path, so the two-line induction is local. -/
theorem getD_default_of_length_le : ∀ (l : List (String × Word256)) (n : Nat)
    (d : String × Word256), l.length ≤ n → l.getD n d = d
  | [], _, d, _ => rfl
  | _ :: _, 0, d, h => absurd h (by simp)
  | _ :: t, k + 1, d, h => getD_default_of_length_le t k d (by simpa using h)

/-- A copy leaves a byte above its window untouched. The progress row's slot-7 read is this
    case: with seven constants and no commitments the copy is 224 bytes, so the word at
    `vkMptr + 224` is the pre-state's memory, which no clause pins. -/
theorem copyInto_untouched (mem : Nat → UInt8) (dst src n : Nat) (bs : List UInt8) (a : Nat)
    (h : a < dst ∨ dst + n ≤ a) : copyInto mem dst src n bs a = mem a := by
  unfold copyInto
  rw [if_neg]
  omega

/-- A payload with exactly seven constants and no commitments is 224 bytes. -/
theorem vkLen_of_seven_constants (vk : Halo2VerifyingKey) (hc : vk.constants.length = 7)
    (hf : vk.fixedComms = []) (hp : vk.permutationComms = []) : vk.len = 224 := by
  simp [Halo2VerifyingKey.len, hc, hf, hp]

/-- The copy of a 224-byte payload leaves the slot-7 word (bytes 224..255) untouched. -/
theorem copyInto_224_slot7 (mem : Nat → UInt8) (dst src : Nat) (bs : List UInt8) :
    copyInto mem dst src 224 bs (dst + 224) = mem (dst + 224) :=
  copyInto_untouched mem dst src 224 bs (dst + 224) (Or.inr (Nat.le_refl _))

/-- With seven constants the slot-7 payload word is the default 0, while the copy never wrote
    the slot; the S7 check compares the pre-state's memory word to 0. -/
theorem payloadWord_slot7_zero_of_length_seven (pv : PlanView)
    (h : pv.vk.constants.length = 7) :
    payloadWord pv vkHeaderTemplateSlotsDefault.hasAccumulator = 0 := by
  show (pv.vk.constants.getD vkHeaderTemplateSlotsDefault.hasAccumulator ("", 0)).2 = 0
  rw [getD_default_of_length_le _ _ _
    (by simpa [vkHeaderTemplateSlotsDefault] using Nat.le_of_eq h)]

/-- **PG-VKHEADER: `PayloadAgrees` FORCES SEVEN CONSTANTS, NOT ELEVEN.** Slot 6 is
    `omegaInvToL`, the word `frWord (omegaInv ^ |rotationLast|)`, a unit and hence nonzero; a
    constants list of length ≤ 6 would make `getD 6` the default `0`. The vkLoading header
    cross-checks read slots 1, 2 and 7-10, so slot 6 is exactly the last one `PayloadAgrees`
    pins: the clause says nothing about the three accumulator-window slots 7-10 or about a
    copy window that stops before them.

    THIS IS THE MISSING FACT OF `vk_blockProgS`. At the point between S2 (the copy) and S3
    (the first header check), for `i ∈ {1, 2, 7, 8, 9, 10}` the row needs

      loadWord
        { st with memory := copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
            R.plan.vk.runtimeBytes.data.toList }
        (ptrAddr (Ptr.add R.pv.memory.vkMptr i))
        = (R.plan.vk.constants.getD i ("", 0)).2,

    while `PayloadAgrees` gives only the right-hand `payloadWord` values. The left-hand word is
    the i-th 32-byte word of the SERIALIZED payload (`Halo2VerifyingKey.bytes`: constants
    first, then fixed and permutation commitments), so the equation holds only when
    `i < constants.length` AND `32 * (i + 1) ≤ vk.len`. `ValidV3` carries neither: with
    `constants.length = 7` and no commitments, `vk.len = 224` (`Halo2VerifyingKey.len`), the
    copy ends exactly at the slot-7 word, and `copyInto_untouched` makes that word the
    pre-state's memory. `Inv .start`'s only memory clause is the 128-byte g1_identity window,
    which `vkPins_disjoint_of_generated` puts outside the payload, so for such a payload a
    `StageInv .start` state with a nonzero word at `vkMptr + 224` is admissible and the S8
    check (accumulator limb bits vs 0) is then false. No `ValidV3` inhabitant is exhibited
    (B4 has not run): what is proved is that the clause table does not exclude this shape.
    A real deployment has the eleven header constants, but that is a fact about the
    INPUT `R.plan.vk` (`generateAll` takes it as `planVk`), not a consequence of `generated`,
    and `PayloadAgrees` is a word-level equation, not a byte-window one. The minimal repair is
    one conjunct on the payload clause (`11 ≤ R.pv.vk.constants.length`, or the window equation
    above); `PayloadAgrees` is frozen, so it is a signed statement change. Per D-P71 no
    hypothesis is attached to the row and the leaf stays OPEN.

    **UPDATE - D-GATE1 SIGNED AND LANDED (2026-11-22).** `PayloadAgrees` now carries
    `constantsLength : 11 ≤ R.pv.vk.constants.length` in both the frozen `LoweringV2` structure
    (re-hashed) and its `LoweringV3` copy. §8's `pg_vkheader_of_valid` is the projection and
    `vk_hdr_word_read_of_valid` is the header-window equation with both arm hypotheses discharged;
    `MemoryPairs.vkMptr_shape_of_generated` supplies the pointer shape. The narrative above is kept
    as the record of why the clause was needed; the row's remaining work is the total walk and the
    existence run, not a premise. -/
theorem payloadAgrees_constants_length {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R)
    (h : PayloadAgrees R) : 7 ≤ R.pv.vk.constants.length := by
  by_contra hlt
  have hle : R.pv.vk.constants.length ≤ 6 := by omega
  have hget : R.pv.vk.constants.getD vkHeaderTemplateSlotsDefault.omegaInvToL ("", 0) =
      ("", 0) :=
    getD_default_of_length_le _ _ _ (by simpa [vkHeaderTemplateSlotsDefault] using hle)
  have hz : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInvToL = 0 := by
    show (R.pv.vk.constants.getD vkHeaderTemplateSlotsDefault.omegaInvToL ("", 0)).2 = 0
    rw [hget]
  have hval := h.omegaInvToL
  rw [hz] at hval
  have hne : frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs) ≠ 0 := by
    refine frWord_ne_zero_of_ne_zero hR.env.modulus (pow_ne_zero _ ?_)
    intro h0
    have hm := hR.env.omegaInvMul
    rw [h0, zero_mul] at hm
    exact zero_ne_one hm
  exact hne hval.symm

#print axioms Midfall.LoweringV3.VkClean.consts_lookup_EXPECTED_VK_LENGTH_V3
#print axioms Midfall.LoweringV3.VkClean.consts_lookup_EXPECTED_VK_CODEHASH_WORD_V3
#print axioms Midfall.LoweringV3.VkClean.copyInto_untouched
#print axioms Midfall.LoweringV3.VkClean.payloadAgrees_constants_length
#assert_axioms Midfall.LoweringV3.VkClean.payloadAgrees_constants_length
  [propext, Classical.choice, Quot.sound] native []


/-! ## 8. PG-VKHEADER: WHAT THE ONE MISSING CLAUSE BUYS, PROVED (WP VKPROG)

  Section 7 records the gap and proves that 'ValidV3' forces only '7 <= constants.length'. This
  section proves the OTHER direction, which is what turns the escalation into a decision rather
  than a guess: the eleven-constant window is not merely what the clause table lacks, it is
  SUFFICIENT. Under it, for every header slot 'i <= numAccLimbBits' the word the six VK-header
  cross-checks read out of the copied memory IS 'payloadWord R.pv i' - the word 'PayloadAgrees'
  pins to the emitted literal. With that equation every guard of the 'vkLoading' slice passes at a
  clean boundary, so the section-4 walk cannot take its revert arm and 'vk_blockProgS' is that walk
  plus section 6's reassembly and nothing else.

  THE NEW BRIDGES. 'wordFrom' at an offset is 'wordFrom' at zero of the suffix, so a copy's window
  arithmetic is a 'drop'; the 32 big-endian bytes of a word read back that word; the word at byte
  offset '32 * i' of the EMITTER'S OWN 'foldl' of chunks is the 'i'-th word of its word list - so
  the SERIALIZED payload and the 'constants' LIST are the same object, which is exactly what
  'PayloadAgrees', a word-level equation over the list, could not say; and
  'ptrAddr (Ptr.add q i) = ptrAddr q + 32 * i' for a pointer the planner built from a 'Nat' (the
  'Value.identifier' arm of 'asUsizeNat' maps every offset to 0, so this is a property of the
  planner's pointer and is a hypothesis of an ARM lemma, never of the row). D-P71: generic in the
  render; nothing added to 'ValidV3', to a row, to a bundle or to the root. -/

/-- **PG-VKHEADER - WAS THE NAMED MISSING PREMISE; D-GATE1 LANDED IT AS A CLAUSE.** Eleven header
    constants: the eleven scalars of 'vkHeaderTemplateSlotsDefault' (slots 0-10), which is what a
    real deployment's payload carries and what 'generateVk' writes with 'headerWords :=
    vk0.constants.length'. Before D-GATE1 it was NOT a theorem of 'ValidV3' ('generated' takes
    'R.plan.vk' as an INPUT to 'generateAll', and 'PayloadAgrees' forced only seven -
    'payloadAgrees_constants_length', section 7). D-GATE1 (design.md) added exactly
    'PayloadAgrees.constantsLength : 11 ≤ R.pv.vk.constants.length'; 'pg_vkheader_of_valid' above is
    its projection and 'vk_hdr_word_read' below proves the conjunct SUFFICIENT. -/
def pg_vkheader (R : Render p G₁ G₂ Gₜ) : Prop :=
  11 ≤ R.pv.vk.constants.length

/-- **D-GATE1: the new `PayloadAgrees` conjunct is the missing premise.** The row can now read
    `pg_vkheader` straight off `ValidV3.payload`; no hypothesis is added to the row. -/
theorem pg_vkheader_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : pg_vkheader R :=
  hR.payload.constantsLength

/-- Two byte lists whose zero-padded reads agree on a 32-byte window read the same word: the
    'wordFrom' face of 'Midfall.Yul.Word.loadWord_congr', with the two offsets separate because a
    copy shifts every read by its own base. -/
theorem wordFrom_congr (l₁ l₂ : List UInt8) (p₁ p₂ : Nat)
    (h : ∀ i, i < 32 → byteFrom l₁ (p₁ + i) = byteFrom l₂ (p₂ + i)) :
    wordFrom l₁ p₁ = wordFrom l₂ p₂ := by
  unfold wordFrom
  refine Midfall.Yul.Word.foldl_congr _ _ _ (fun i hi acc =>
    congrArg (fun x : UInt8 => (acc : U256) <<< 8 ||| BitVec.ofNat 256 x.toNat)
      (h i (List.mem_range.mp hi))) _

/-- 'wordFrom' at an offset is 'wordFrom' at zero of the suffix. -/
theorem wordFrom_drop (l : List UInt8) (p : Nat) :
    wordFrom l p = wordFrom (l.drop p) 0 :=
  wordFrom_congr l (l.drop p) p 0 (fun i _ => by
    rw [Midfall.LoweringV3.VkWindow.byteFrom_drop,
      Midfall.LoweringV3.VkWindow.byteFrom_drop, List.drop_drop, Nat.zero_add])

/-- A 32-byte chunk at the head of a list is what 'wordFrom' reads at offset zero: the bytes past
    the chunk are never reached. -/
theorem wordFrom_append_head (a b : List UInt8) (h : a.length = 32) :
    wordFrom (a ++ b) 0 = wordFrom a 0 :=
  wordFrom_congr (a ++ b) a 0 0 (fun i hi => by
    simp only [Nat.zero_add]
    have hlt : i < a.length := by omega
    have hne : a.drop i ≠ [] := by
      intro h2
      have h3 : (a.drop i).length = a.length - i := List.length_drop
      rw [h2, List.length_nil] at h3
      omega
    rw [Midfall.LoweringV3.VkWindow.byteFrom_drop,
      Midfall.LoweringV3.VkWindow.byteFrom_drop, List.drop_append,
      show i - a.length = 0 by omega, List.drop_zero]
    cases h4 : a.drop i with
    | nil => exact absurd h4 hne
    | cons c t => rfl)

/-- The big-endian fold of a 32-byte list is the 'bytesToNatBE' fold of the same bytes. Stated for
    an abstract list so the kernel never has to reduce a 'drop' through an emitter term. -/
theorem wordFrom_len32 (l : List UInt8) (h : l.length = 32) :
    wordFrom l 0 =
      BitVec.ofNat 256 (l.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0) := by
  unfold wordFrom
  have key (o : Option UInt8) : (o.getD 0).toNat = (o.map UInt8.toNat).getD 0 := by
    cases o <;> rfl
  have hb : ∀ x : Nat, ((l.drop (0 + x)).head?.map UInt8.toNat).getD 0 < 256 := by
    intro x
    cases hx : (l.drop (0 + x)).head? with
    | none => simp [hx]
    | some u =>
        have hu := UInt8.toNat_lt_size u
        simpa using hu
  have hpt : ∀ x ∈ List.range 32,
      (byteFrom l (0 + x)).toNat = ((l.drop (0 + x)).head?.map UInt8.toNat).getD 0 := by
    intro x _
    rw [Midfall.LoweringV3.VkWindow.byteFrom_drop, key]
  have h1 : (List.range 32).foldl
        (fun (acc : U256) x => acc <<< 8 ||| BitVec.ofNat 256 (byteFrom l (0 + x)).toNat) 0
      = (List.range 32).foldl
          (fun (acc : U256) x => acc <<< 8 |||
            BitVec.ofNat 256 (((l.drop (0 + x)).head?.map UInt8.toNat).getD 0)) 0 :=
    Midfall.Yul.Word.foldl_congr
      (fun (acc : U256) (x : Nat) => acc <<< 8 ||| BitVec.ofNat 256 (byteFrom l (0 + x)).toNat)
      (fun (acc : U256) (x : Nat) =>
        acc <<< 8 ||| BitVec.ofNat 256 (((l.drop (0 + x)).head?.map UInt8.toNat).getD 0))
      (List.range 32) (fun x hx acc =>
        congrArg (fun y : Nat => acc <<< 8 ||| BitVec.ofNat 256 y) (hpt x hx)) 0
  have h0 : (0 : U256) = BitVec.ofNat 256 0 := rfl
  have h2 : (List.range 32).foldl
        (fun (acc : U256) x => acc <<< 8 |||
          BitVec.ofNat 256 (((l.drop (0 + x)).head?.map UInt8.toNat).getD 0)) 0
      = BitVec.ofNat 256 ((List.range 32).foldl
          (fun (acc : Nat) x => acc * 256 + ((l.drop (0 + x)).head?.map UInt8.toNat).getD 0) 0) := by
    rw [h0, fold_be_eq (fun x => ((l.drop (0 + x)).head?.map UInt8.toNat).getD 0) hb
      (List.range 32) 0]
  rw [h1, h2]
  have htake : (List.range 32).map (fun i => byteFrom l (0 + i)) = l := by
    have h32 : 0 + 32 ≤ l.length := by omega
    have h32b : (List.drop 0 l).length ≤ 32 := by rw [List.drop_zero, h]
    rw [Midfall.LoweringV3.VkWindow.map_byteFrom_take l 0 32 h32,
      List.take_of_length_le h32b, List.drop_zero]
  have h3 : (List.range 32).foldl
        (fun (acc : Nat) x => acc * 256 + ((l.drop (0 + x)).head?.map UInt8.toNat).getD 0) 0
      = l.foldl (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 := by
    have h5 : (fun i => ((l.drop (0 + i)).head?.map UInt8.toNat).getD 0)
        = (fun x => x.toNat) ∘ (fun i => byteFrom l (0 + i)) := by
      funext i
      show ((l.drop (0 + i)).head?.map UInt8.toNat).getD 0 = (byteFrom l (0 + i)).toNat
      rw [Midfall.LoweringV3.VkWindow.byteFrom_drop]
      exact (key ((l.drop (0 + i)).head?)).symm
    rw [← List.foldl_map, h5, ← List.map_map, htake, List.foldl_map]
  rw [h3]

/-- **THE BRIDGE 'PayloadAgrees' COULD NOT CROSS.** The 32 big-endian bytes of a word, read at
    offset zero, are that word. -/
theorem wordFrom_wordToBytesBE (w : Word256) :
    wordFrom (Midfall.wordToBytesBE w).data.toList 0 = w := by
  have hlen : ((Midfall.wordToBytesBE w).data.toList).length = 32 :=
    Midfall.LoweringV2.wordToBytesBE_size w
  rw [wordFrom_len32 _ hlen, ← Midfall.bytesToNatBE_toList,
    ← Midfall.bytesToWordBE_eq_bytesToNatBE, Midfall.bytesToWordBE_wordToBytesBE]

/-- 'Midfall.Bytes.empty' is a left identity for 'ByteArray.append'. -/
theorem bytes_empty_append (a : Bytes) : Midfall.Bytes.empty.append a = a := by
  show ByteArray.empty ++ a = a
  rw [ByteArray.empty_append]

/-- The emitter's 'foldl' of 32-byte chunks: an accumulator is exactly a prefix of the byte list. -/
theorem foldlA : ∀ (ws : List Word256) (acc : Bytes),
    (ws.foldl (fun (a : Bytes) (w : Word256) => a.append (Midfall.wordToBytesBE w)) acc).data.toList
      = acc.data.toList ++
        (ws.foldl (fun (a : Bytes) (w : Word256) => a.append (Midfall.wordToBytesBE w))
          Midfall.Bytes.empty).data.toList := by
  intro ws
  induction ws with
  | nil =>
      intro acc
      rw [List.foldl_nil, List.foldl_nil,
        show (Midfall.Bytes.empty : Bytes).data.toList = [] from rfl, List.append_nil]
  | cons w ws ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih (acc.append (Midfall.wordToBytesBE w)),
        ByteArray.toList_data_append', Midfall.LoweringV3.VkClean.bytes_empty_append,
        ih (Midfall.wordToBytesBE w), List.append_assoc]

/-- **THE SERIALIZED PAYLOAD IS THE CONSTANT LIST.** The word at byte offset '32 * i' of the
    payload the emitter wrote is the 'i'-th word of the list it folded. This is the bridge from
    'PayloadAgrees', which speaks of 'constants.getD i', to the memory the block reads. -/
theorem wordFrom_foldl_chunks : ∀ (ws : List Word256) (i : Nat), i < ws.length →
    wordFrom ((ws.foldl (fun (a : Bytes) (w : Word256) =>
        a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList) (32 * i)
      = ws.getD i 0 := by
  intro ws
  induction ws with
  | nil => intro i h; exact absurd h (by simp)
  | cons w ws ih =>
      intro i h
      have hlen : ((Midfall.wordToBytesBE w).data.toList).length = 32 :=
        Midfall.LoweringV2.wordToBytesBE_size w
      have hcs : ((w :: ws).foldl (fun (a : Bytes) (x : Word256) =>
          a.append (Midfall.wordToBytesBE x)) Midfall.Bytes.empty).data.toList
          = (Midfall.wordToBytesBE w).data.toList
            ++ ((ws.foldl (fun (a : Bytes) (x : Word256) =>
                a.append (Midfall.wordToBytesBE x)) Midfall.Bytes.empty).data.toList) := by
        rw [List.foldl_cons, Midfall.LoweringV3.VkClean.bytes_empty_append, foldlA]
      cases i with
      | zero =>
          rw [hcs, wordFrom_append_head _ _ hlen, wordFrom_wordToBytesBE, List.getD_cons_zero]
      | succ k =>
          have hrest : List.drop (32 * (k + 1))
              (Midfall.wordToBytesBE w).data.toList = [] :=
            List.drop_eq_nil_of_le (by rw [hlen]; omega)
          have hdrop : List.drop (32 * (k + 1))
                ((Midfall.wordToBytesBE w).data.toList ++
                  ((ws.foldl (fun (a : Bytes) (x : Word256) =>
                      a.append (Midfall.wordToBytesBE x)) Midfall.Bytes.empty).data.toList))
              = List.drop (32 * k)
                ((ws.foldl (fun (a : Bytes) (x : Word256) =>
                    a.append (Midfall.wordToBytesBE x)) Midfall.Bytes.empty).data.toList) := by
            rw [List.drop_append, hrest, List.nil_append, hlen,
              show 32 * (k + 1) - 32 = 32 * k by omega]
          rw [hcs, wordFrom_drop, hdrop, List.getD_cons_succ, ← wordFrom_drop]
          exact ih k (by simpa using h)

/-- 'getD' through a map followed by an append: below the mapped list's length the tail is
    invisible, and the pair list's default is the zero word. -/
theorem getD_map_append : ∀ (l : List (String × Word256)) (rest : List Word256) (i : Nat),
    i < l.length → ((l.map (·.2)) ++ rest).getD i 0 = (l.getD i ("", 0)).2
  | [], _, i, h => absurd h (by simp)
  | x :: _, _, 0, _ => rfl
  | _ :: xs, rest, i + 1, h => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact getD_map_append xs rest i (by simpa using h)

/-- The header slot 'i' sits '32 * i' bytes above the payload base, for a pointer the planner built
    from a 'Nat' ('ptrMemory (valueFromNat n)', which is the only shape 'newFromVk' ever stores). -/
theorem ptrAddr_ptr_add_of_integer (q : Ptr) (i : Nat)
    (h : ∃ n : Nat, ptrValue q = Value.integer n) :
    ptrAddr (Ptr.add q i) = ptrAddr q + Midfall.Generator.wordBytes * i := by
  obtain ⟨n, hn⟩ := h
  show Value.asUsizeNat (Value.add (ptrValue q) i) =
    Value.asUsizeNat (ptrValue q) + Midfall.Generator.wordBytes * i
  rw [hn]
  have hw : (Midfall.Generator.wordBytes : Int) = 32 := by exact_mod_cast rfl
  rw [Value.add, hw, Value.asUsizeNat, Value.asUsizeNat]
  have h1 : (0 : Int) ≤ (n : Int) + (i : Int) * 32 := by
    have hi : (0 : Int) ≤ (i : Int) * 32 := mul_nonneg (Int.natCast_nonneg i) (by decide)
    omega
  have h2 : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg _
  rw [if_pos h1, if_pos h2]
  have hw2 : Midfall.Generator.wordBytes = 32 := rfl
  rw [hw2]
  push_cast
  omega

/-- **PG-VKHEADER, THE SUFFICIENCY HALF.** Under the eleven-constant window the copied payload word
    at header slot 'i' IS the word 'PayloadAgrees' pins - for every slot the vkLoading cross-checks
    read ('numInstances' = 1, 'k' = 2 and the accumulator quadruple 7, 8, 9, 10), and indeed for
    every slot at or below 'numAccLimbBits'. This is the equation section 7 names as the row's only
    missing premise, proved FROM the premise: 'hmem' is the walk's own copy equation with D-QVM1's
    fits already applied (section 6), 'hcode' is 'Frame.vkCode', and the address is the one
    'expectedConsts' puts in the table. -/
theorem vk_hdr_word_read (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hptr : ∃ n : Nat, ptrValue R.pv.memory.vkMptr = Value.integer n)
    (st stb : EvmState) (vkAddr : U256)
    (hcode : st.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList)
    (hmem : stb.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
      (st.env.extCodeOf vkAddr))
    (hlen : pg_vkheader R) (i : Nat)
    (hi : i ≤ vkHeaderTemplateSlotsDefault.numAccLimbBits) :
    loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) = payloadWord R.pv i := by
  have hlen' : 11 ≤ R.pv.vk.constants.length := hlen
  have hslot : vkHeaderTemplateSlotsDefault.numAccLimbBits = 10 := rfl
  have hi10 : i ≤ 10 := by omega
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  have hlenGe : 352 ≤ R.pv.vk.len := by
    show 352 ≤ R.pv.vk.constants.length * 32 + _
    omega
  have ha : ptrAddr (Ptr.add R.pv.memory.vkMptr i)
      = ptrAddr R.pv.memory.vkMptr + Midfall.Generator.wordBytes * i :=
    ptrAddr_ptr_add_of_integer R.pv.memory.vkMptr i hptr
  rw [ha, hw, hmem]
  have hwin : ptrAddr R.pv.memory.vkMptr ≤ ptrAddr R.pv.memory.vkMptr + 32 * i ∧
      ptrAddr R.pv.memory.vkMptr + 32 * i + 32 ≤ ptrAddr R.pv.memory.vkMptr + R.pv.vk.len := by
    omega
  rw [Midfall.Yul.Word.loadWord_copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
    (ptrAddr R.pv.memory.vkMptr + 32 * i) (st.env.extCodeOf vkAddr) hwin]
  rw [Nat.add_sub_cancel_left, hcode,
    Midfall.LoweringV3.VkWindow.runtimeBytes_toList]
  have hpt : ∀ j, j < 32 → byteFrom (Nat.toUInt8 vkRuntimePrefix ::
      R.plan.vk.bytes.data.toList) (1 + 32 * i + j)
      = byteFrom (R.plan.vk.bytes.data.toList) (32 * i + j) := by
    intro j hj
    rw [Midfall.LoweringV3.VkWindow.byteFrom_drop,
      Midfall.LoweringV3.VkWindow.byteFrom_drop,
      List.drop_cons (by omega : 0 < 1 + 32 * i + j),
      show 1 + 32 * i + j - 1 = 32 * i + j by omega]
  rw [wordFrom_congr _ _ _ _ hpt]
  have hvk : R.plan.vk = R.pv.vk := rfl
  rw [hvk]
  have hlt : i < (R.pv.vk.constants.map (·.2) ++
      R.pv.vk.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo]) ++
      R.pv.vk.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])).length := by
    have h1 : (R.pv.vk.constants.map (·.2)).length = R.pv.vk.constants.length := by
      rw [List.length_map]
    simp only [List.length_append, h1]
    omega
  have hb : R.pv.vk.bytes.data.toList = ((R.pv.vk.constants.map (·.2) ++
      R.pv.vk.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo]) ++
      R.pv.vk.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])).foldl
      (fun (a : Bytes) (w : Word256) => a.append (Midfall.wordToBytesBE w))
      Midfall.Bytes.empty).data.toList := rfl
  have hlt2 : i < R.pv.vk.constants.length := by omega
  rw [hb, wordFrom_foldl_chunks _ _ hlt]
  rw [List.append_assoc, getD_map_append R.pv.vk.constants _ i hlt2]
  rfl

/-- The plan view's accumulator literals are all zero on the no-accumulator class `ValidV3`
    carries (`SupportedV2.noAcc`). -/
theorem pv_acc_words_zero {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.pv.expectedHasAccumulatorWord = 0 ∧ R.pv.expectedAccOffset = 0 ∧
      R.pv.expectedNumAccLimbs = 0 ∧ R.pv.expectedNumAccLimbBits = 0 := by
  have hpv : R.pv = planViewOf R.plan R.model none := by
    show planViewOf R.plan R.model R.cfg.accumulator = _
    rw [hR.supported.noAcc]
  rw [hpv]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The six VkLoading header offsets, at the model's own header table. The `h` argument is
    `vkHeader_default_of_generated`; it is what makes the `expectedConsts` offsets the template's
    slots the payload pins use. -/
theorem expectedConsts_lookup_hdr_numInstances (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "NUM_INSTANCES_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numInstances)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_hdr_k (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "K_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.k)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_hdr_hasAccumulator (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "HAS_ACCUMULATOR_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.hasAccumulator)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_hdr_accOffset (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "ACC_OFFSET_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.accOffset)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_hdr_numAccLimbs (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "NUM_ACC_LIMBS_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbs)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

theorem expectedConsts_lookup_hdr_numAccLimbBits (pv : PlanView) (m : Model)
    (h : m.vkHeader = vkHeaderTemplateSlotsDefault) :
    (Midfall.LoweringV2.expectedConsts pv m).lookup "NUM_ACC_LIMB_BITS_MPTR" =
      some (Midfall.LoweringV2.cAddr (Ptr.add pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbBits)) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
  cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
    simp [Midfall.LoweringV2.expectedConsts, h, h1, h2, h3, h4, List.lookup]

/-- **THE SIX HEADER TABLE LOOKUPS AT `ValidV3`.** Slots 1, 2, 7, 8, 9, 10 of the emitter's own
    `vkHeaderTemplateSlotsDefault`, at the render's constant table. The model's header table is the
    template's (`MemoryPairs.vkHeader_default_of_generated`), so these are the offsets the S3-S8
    `mload`s read. -/
theorem vkHeaderLookupsV3 {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.consts.lookup "NUM_INSTANCES_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numInstances)) ∧
      R.consts.lookup "K_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.k)) ∧
      R.consts.lookup "HAS_ACCUMULATOR_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.hasAccumulator)) ∧
      R.consts.lookup "ACC_OFFSET_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.accOffset)) ∧
      R.consts.lookup "NUM_ACC_LIMBS_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbs)) ∧
      R.consts.lookup "NUM_ACC_LIMB_BITS_MPTR" =
        some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbBits)) := by
  have hh := Midfall.LoweringV3.MemoryPairs.vkHeader_default_of_generated hR.generated
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_numInstances R.pv R.model hh)
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_k R.pv R.model hh)
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_hasAccumulator R.pv R.model hh)
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_accOffset R.pv R.model hh)
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_numAccLimbs R.pv R.model hh)
  · exact Midfall.LoweringV3.VkWindow.consts_lookup_of_validV3 hR _ _
      (expectedConsts_lookup_hdr_numAccLimbBits R.pv R.model hh)

/-- **THE HEADER WORD, WITH NO ARM HYPOTHESIS.** D-GATE1's `PayloadAgrees.constantsLength` supplies
    the eleven-constant window and `MemoryPairs.vkMptr_shape_of_generated` supplies the `Nat`-built
    pointer shape; this is `vk_hdr_word_read` with both discharged, ready for the `vkLoading` walk. -/
theorem vk_hdr_word_read_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (st stb : EvmState) (vkAddr : U256)
    (hcode : st.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList)
    (hmem : stb.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
      (st.env.extCodeOf vkAddr))
    (i : Nat) (hi : i ≤ vkHeaderTemplateSlotsDefault.numAccLimbBits) :
    loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) = payloadWord R.pv i :=
  vk_hdr_word_read R hR (Midfall.LoweringV3.MemoryPairs.vkMptr_shape_of_generated hR.generated)
    st stb vkAddr hcode hmem (pg_vkheader_of_valid hR) i hi

/-- **THE SIX WORDS S3-S8 READ, AS THE LITERALS `vk_sliceV3` COMPARES THEM TO.** This is the
    value half of the progress walk: each `loadWord` at the emitter's header slot is the plan's
    number, so the `eq` of each cross-check is 1 and `success` cannot leave 1. -/
theorem vk_hdr_read_values (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (st stb : EvmState) (vkAddr : U256)
    (hcode : st.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList)
    (hmem : stb.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
      (st.env.extCodeOf vkAddr)) :
    loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.numInstances)) = BitVec.ofNat 256 R.cfg.numInstances ∧
      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.k)) = BitVec.ofNat 256 R.vk.domain.k ∧
      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.hasAccumulator)) = 0 ∧
      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.accOffset)) = 0 ∧
      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.numAccLimbs)) = 0 ∧
      loadWord stb.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr
        vkHeaderTemplateSlotsDefault.numAccLimbBits)) = 0 := by
  have h1 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.numInstances (by decide)
  have h2 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.k (by decide)
  have h7 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.hasAccumulator (by decide)
  have h8 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.accOffset (by decide)
  have h9 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.numAccLimbs (by decide)
  have h10 := vk_hdr_word_read_of_valid R hR st stb vkAddr hcode hmem
    vkHeaderTemplateSlotsDefault.numAccLimbBits (by decide)
  have hacc := hR.payload.accWords
  rw [show accWordsOfEncoding R.cfg.accumulator = (0, 0, 0, 0) from by
    rw [hR.supported.noAcc]; rfl] at hacc
  have hz7 : payloadWord R.pv vkHeaderTemplateSlotsDefault.hasAccumulator = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := congrArg Prod.fst hacc
    simpa using h
  have hz8 : payloadWord R.pv vkHeaderTemplateSlotsDefault.accOffset = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := congrArg (fun p => p.2.1) hacc
    simpa using h
  have hz9 : payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbs = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := congrArg (fun p => p.2.2.1) hacc
    simpa using h
  have hz10 : payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbBits = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h := congrArg (fun p => p.2.2.2) hacc
    simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact hR.payload.numInstances
  · rw [h2, hR.payload.k, hR.env.domainN.2]
  · rw [h7, hz7]
  · rw [h8, hz8]
  · rw [h9, hz9]
  · rw [h10, hz10]

#print axioms Midfall.LoweringV3.VkClean.wordFrom_congr
#print axioms Midfall.LoweringV3.VkClean.wordFrom_append_head
#print axioms Midfall.LoweringV3.VkClean.wordFrom_len32
#print axioms Midfall.LoweringV3.VkClean.wordFrom_wordToBytesBE
#print axioms Midfall.LoweringV3.VkClean.wordFrom_foldl_chunks
#print axioms Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer
#print axioms Midfall.LoweringV3.VkClean.vk_hdr_word_read
#cone_sorries Midfall.LoweringV3.VkClean.vk_hdr_word_read
#assert_axioms Midfall.LoweringV3.VkClean.vk_hdr_word_read
  [propext, Classical.choice, Quot.sound] native []


/-! ## 9. THE PROGRESS WALK'S VALUE AND GUARD LEMMAS

  `vk_blockProgS` has no revert arm, so every run must be shown normal. The clean walk's halt arm
  can only be an S1/S9/S13 guard, and the four guards fire only if their comparisons fail. This
  section lands the value inversions and the three skips; §10 then carries them through the
  thirteen statements. -/

/-- The mload answer at an inlined site: the word at the site's value, and the state is the
    active-word touch. -/
theorem vk_mload_val (R : Render p G₁ G₂ Gₜ) (slot : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.mload [vkSite slot R.consts]) (.vals [cv] st₁)) :
    ∃ a : U256, vkVal slot R V = some a ∧ cv = loadWord st.memory a.toNat ∧
      st₁ = touchMemory st a.toNat 32 := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hx => cases hnil with
        | argsNil =>
            obtain ⟨hval, hst⟩ := vkSite_val hx
            subst hst
            simp only [builtinWithExternal, stepOp] at hbi
            cases hbi
            exact ⟨_, hval, rfl, rfl⟩

/-- The `extcodesize` value: the code list's length at the `vk` local. -/
theorem vk_ecs_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {a cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.extcodesize [Expr.var "vk"]) (.vals [cv] st₁))
    (ha : VEnv.get V "vk" = some a) :
    cv = BitVec.ofNat 256 (st.env.extCodeOf a).length ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hv => cases hnil with
        | argsNil => cases hv with
          | var hget =>
              rw [ha] at hget
              cases hget
              simp only [builtinWithExternal, stepOp, rd1] at hbi
              cases hbi
              exact ⟨rfl, rfl⟩

/-- The `extcodehash` value: the projected code hash at the `vk` local. -/
theorem vk_ech_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {a cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.extcodehash [Expr.var "vk"]) (.vals [cv] st₁))
    (ha : VEnv.get V "vk" = some a) :
    cv = projectedCodeHash st.env st.env.balanceOf a ∧ st₁ = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hv => cases hnil with
        | argsNil => cases hv with
          | var hget =>
              rw [ha] at hget
              cases hget
              simp only [builtinWithExternal, stepOp, rd1] at hbi
              cases hbi
              exact ⟨rfl, rfl⟩

/-- The `and` value: the two argument values, in the semantics' order. -/
theorem vk_and_val {A B : Expr EVM.Op}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.and [A, B]) (.vals [cv] st₁)) :
    ∃ (av bv : U256) (st₀ st₂ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st B (.vals [bv] st₀)
      ∧ EvalExpr (Bridge.Dialect c g) funs V st₀ A (.vals [av] st₂)
      ∧ st₂ = st₁ ∧ cv = av &&& bv := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hrest hx => cases hrest with
        | argsCons hnil h2 => cases hnil with
          | argsNil =>
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, _, _, h2, hx, rfl, rfl⟩

/-- The generic `iszero` value. -/
theorem vk_iszero_val' {A : Expr EVM.Op}
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₁ : EvmState} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
        (Expr.builtin Op.iszero [A]) (.vals [cv] st₁)) :
    ∃ (av : U256) (st₀ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st A (.vals [av] st₀)
      ∧ st₀ = st₁ ∧ cv = b2w (decide (av = 0)) := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hx => cases hnil with
        | argsNil =>
            simp only [builtinWithExternal, stepOp, un] at hbi
            cases hbi
            exact ⟨_, _, hx, rfl, rfl⟩

/-- With non-empty code the projected code hash is the keccak of that code. -/
theorem projectedCodeHash_eq_keccak (env : YulSemantics.EVM.ExecEnv) (a : U256)
    (h : (env.extCodeOf a).length ≠ 0) :
    YulSemantics.EVM.projectedCodeHash env env.balanceOf a =
      env.keccakOf (env.extCodeOf a) := by
  unfold YulSemantics.EVM.projectedCodeHash
  rw [ite_eq_right]
  intro hc
  exact h hc.2.2

/-- **THE S1 GUARD IS SILENT.** At `StageInv .start` the deployed runtime is the render's own
    runtime (`Frame.vkCode`/`vkHash`/`vkNonEmpty`) and the two `vkProgressPins` are theorems of
    `ValidV3`, so the `extcodesize`/`extcodehash` pair is exactly the two table literals. -/
theorem vkGuard_zero (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (hcode : vkCodehashArm R.model)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hframe : Frame R H vkAddr cd V st) :
    ∀ {st' : EvmState} {cv : U256},
      EvalExpr (Bridge.Dialect c g) funs V st (vkGuard R.consts) (.vals [cv] st') →
        cv = 0 := by
  intro st' cv h
  obtain ⟨andv, s1, hAnd, hs1, hcv⟩ := vk_iszero_val' h
  obtain ⟨av, bv, s0, s2, hb, ha, hs2, hand⟩ := vk_and_val hAnd
  obtain ⟨av2, bv2, t0, t2, hb2, ha2, ht2, hc2⟩ := vk_eq_val hb
  obtain ⟨av1, bv1, u0, u2, hb1, ha1, hu2, hc1⟩ := vk_eq_val ha
  rw [vkVk0_var R] at ha2
  rw [vkVk0_var R] at ha1
  obtain ⟨hvalHash, hstHash⟩ := vkSite_val hb2
  obtain ⟨hvalLen, hstLen⟩ := vkSite_val hb1
  obtain ⟨h2v, ht2'⟩ := vk_ech_val ha2 hframe.vk
  have hs0 : s0 = st := ht2.symm.trans (ht2'.trans hstHash)
  rw [hs0] at hstLen
  rw [hstLen] at ha1
  have hvk0 : vkVal "vk" R V = some vkAddr := by
    simp only [vkVal, consts_vk_none R]
    exact hframe.vk
  have eLen : vkVal "EXPECTED_VK_LENGTH" R V =
      some (BitVec.ofNat 256 R.plan.vk.runtimeBytes.size) := by
    simp only [vkVal, consts_lookup_EXPECTED_VK_LENGTH_V3 hR hcode]
  have eHash : vkVal "EXPECTED_VK_CODEHASH_WORD" R V =
      some (BitVec.ofNat 256 (keccak256 R.plan.vk.runtimeBytes).toNat) := by
    simp only [vkVal, consts_lookup_EXPECTED_VK_CODEHASH_WORD_V3 hR hcode]
  have hbv1' : bv1 = BitVec.ofNat 256 R.plan.vk.runtimeBytes.size :=
    Option.some.inj (hvalLen.symm.trans eLen)
  have hbv2' : bv2 = BitVec.ofNat 256 (keccak256 R.plan.vk.runtimeBytes).toNat :=
    Option.some.inj (hvalHash.symm.trans eHash)
  have hcodeLen : (st.env.extCodeOf vkAddr).length = R.plan.vk.runtimeBytes.size := by
    rw [hframe.vkCode]
    exact Array.size_eq_length_toList
  have hav1' : av1 = bv1 := by
    obtain ⟨h1v, _⟩ := vk_ecs_val ha1 hframe.vk
    rw [h1v, hbv1', hcodeLen]
  have hcv1' : b2w (decide (av1 = bv1)) = 1 := by rw [hav1']; simp [b2w]
  have hne : (st.env.extCodeOf vkAddr).length ≠ 0 := by
    rw [hframe.vkCode]; exact hframe.vkNonEmpty
  have hav2' : av2 = bv2 := by
    rw [h2v, hstHash, projectedCodeHash_eq_keccak _ vkAddr hne, hframe.keccak,
      hframe.vkCode, hbv2']
    change H (ByteArray.mk R.plan.vk.runtimeBytes.data.toList.toArray) =
      BitVec.ofNat 256 (keccak256 R.plan.vk.runtimeBytes).toNat
    rw [Midfall.LoweringV3.VkWindow.bytes_mk_toList, hframe.vkHash]
    simpa using (BitVec.ofNat_toNat (keccak256 R.plan.vk.runtimeBytes)).symm
  have hcv2' : b2w (decide (av2 = bv2)) = 1 := by rw [hav2']; simp [b2w]
  have hand1 : andv = 1 := by
    rw [hand, hc1, hc2, hcv1', hcv2']
    decide
  rw [hcv, hand1]
  decide

/-- The address of header slot `i` fits a word: `programFits` bounds the VK window and the
    eleven-constant clause makes `32*i` lie inside it. -/
theorem vk_hdr_addr_fit (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (i : Nat)
    (hi : i ≤ vkHeaderTemplateSlotsDefault.numAccLimbBits) :
    Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i) < 2 ^ 256 := by
  have hptr := Midfall.LoweringV3.MemoryPairs.vkMptr_shape_of_generated hR.generated
  rw [Midfall.LoweringV2.cAddr_eq_ptrAddr,
    Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer _ _ hptr]
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  rw [hw]
  have hb := (programFit_of_valid hR).1
  have hlen : 32 * i ≤ R.pv.vk.len := by
    have hcl := hR.payload.constantsLength
    have hlen' : R.pv.vk.constants.length * 32 ≤ R.pv.vk.len := by
      show _ ≤ R.pv.vk.constants.length * 32 + _
      omega
    have hi10 : i ≤ 10 := by
      simpa [vkHeaderTemplateSlotsDefault] using hi
    omega
  omega

/-- One cross-check on `mload(slot)` keeps `success = 1`: the loaded word is the literal. -/
theorem vk_hdr_succ_one (R : Render p G₁ G₂ Gₜ) (slot : String) (i n : Nat)
    (succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hS : PureRead funs V succExpr)
    (hnS : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    (hxval : ∀ (st₁ st₂ : EvmState) {av : U256},
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.vals [av] st₂) →
          VEnv.get V "success" = some av)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot = some
      (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i)))
    (hfit : Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i) < 2 ^ 256)
    (hword : loadWord st.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) =
      BitVec.ofNat 256 n)
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (vkHdr slot n R.consts succExpr :: ss) Vb stb ob) :
    ∃ (V₁ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb ob ∧
        VEnv.get V₁ "success" = some (1 : U256) ∧ Same st st₁ := by
  obtain ⟨x, av, bv, V₁, st₁, sB, sA, hV₁, hbv, hav, hxv, hrest, hSame⟩ :=
    vk_hdr_peelT R (Expr.builtin Op.mload [vkSite slot R.consts]) (Expr.lit (.number n))
      succExpr (pr_mload R slot) pureLit hS (nh_mload_site R slot)
      (fun st₁ st₃ hh => nh_lit hh) hnS h
  have hx1 : x = (1 : U256) := Option.some.inj ((hxval _ _ hxv).symm.trans hsucc)
  obtain ⟨a, hva, havEq, hstA⟩ := vk_mload_val R slot hav
  have hsite : vkVal slot R V =
      some (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))) := by
    simp only [vkVal, hlookup]
  have haEq : a = BitVec.ofNat 256
      (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i)) :=
    Option.some.inj (hva.symm.trans hsite)
  have hsB : Same st sB := pureLit st _ _ hbv
  have hfit' : (BitVec.ofNat 256
      (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat =
      ptrAddr (Ptr.add R.pv.memory.vkMptr i) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa [Midfall.LoweringV2.cAddr_eq_ptrAddr] using hfit)
  have hbv' : bv = BitVec.ofNat 256 n := (vk_lit_val hbv).1
  have havbv : av = bv := by
    rw [havEq, haEq, hfit', hbv']
    show loadWord sB.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) = BitVec.ofNat 256 n
    rw [hsB.2.2]
    exact hword
  have hget : VEnv.get V₁ "success" = some (x &&& b2w (decide (av = bv))) :=
    hV₁ ▸ vk_get_set_of_some hsucc
  refine ⟨V₁, st₁, hrest, ?_, ?_⟩
  · rw [hget, hx1, havbv]
    simp [b2w]
  · exact hSame

/-- S1 is skipped when its guard word is zero. -/
theorem vkS1_skipT (R : Render p G₁ G₂ Gₜ)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hguard : ∀ {st₁ : EvmState} {cv : U256},
        EvalExpr (Bridge.Dialect c g) funs V st (vkGuard R.consts) (.vals [cv] st₁) → cv = 0)
    (h : ExecStmts (Bridge.Dialect c g) funs V st (vkS1 R.consts :: ss) Vb stb ob) :
    ∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob ∧ Same st st₁ := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | ifTrue hc hnonzero hbody => exact absurd (hguard hc) hnonzero
    | ifFalse hc _ => exact ⟨st₁, hrest, pr_guard R st st₁ _ hc⟩
  · cases h₁ with
    | ifTrue hc hnonzero hbody => exact absurd (hguard hc) hnonzero
    | ifHalt hc => exact (vkGuard_ne_halts hc).elim
    | ifFalse _ _ => exact absurd rfl hne

/-- An `iszero(success)` guard is skipped when `success = 1`. -/
theorem vkS9_skipT (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (h : ExecStmts (Bridge.Dialect c g) funs V st
        (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
          [Stmt.exprStmt (Expr.call "fail" [vkSite err R.consts])] :: ss) Vb stb ob) :
    ∃ st₁, ExecStmts (Bridge.Dialect c g) funs V st₁ ss Vb stb ob ∧ Same st st₁ := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · cases h₁ with
    | ifTrue hc hnonzero hbody =>
        have hz := vk_iszero_val hc
        rw [hsucc] at hz
        simp at hz
        exact absurd hz hnonzero
    | ifFalse hc _ => exact ⟨st₁, hrest, pr_iszero R pr_succ st st₁ _ hc⟩
  · cases h₁ with
    | ifTrue hc hnonzero hbody =>
        have hz := vk_iszero_val hc
        rw [hsucc] at hz
        simp at hz
        exact absurd hz hnonzero
    | ifHalt hc =>
        exact (vk_nh_unary (op := Op.iszero) (fun _ _ _ h' => vk_ok_iszero h')
          (fun _ _ hh => vkVar_ne_halts hh) hc).elim
    | ifFalse _ _ => exact absurd rfl hne

theorem envelope_calldata_facts (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (cd : Bytes)
    {st : EvmState}
    (henv : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true)
    (hcal : st.env.calldata = cd.data.toList) :
    wordFrom st.env.calldata (R.pv.proofLayout.proofCptr - 32) =
        BitVec.ofNat 256 R.pv.proofLayout.proofLen ∧
      wordFrom st.env.calldata R.pv.proofLayout.proofEnd =
        BitVec.ofNat 256 R.pv.numInstances ∧
      BitVec.ofNat 256 st.env.calldata.length =
        BitVec.ofNat 256 (R.pv.proofLayout.proofEnd + 32) +
          BitVec.ofNat 256 (R.pv.numInstances * 32) := by
  have hpl : R.pv.proofLayout = R.plan.proofLayout := rfl
  have hnum : R.pv.numInstances = R.cfg.numInstances :=
    (Midfall.LoweringV3.MemoryPairs.row_premises_of_generated R hR.generated hR.inputs.1
      hR.supported.separateVk).1
  -- decompose envelopeOk
  have he := henv
  simp only [envelopeOk, Bool.and_eq_true] at he
  obtain ⟨⟨⟨hab, hp1⟩, hp2⟩, hp3⟩ := he
  have habi := hab
  simp only [abiHeadOk, Bool.and_eq_true] at habi
  obtain ⟨⟨⟨hsel, hcptrb⟩, hendb⟩, _⟩ := habi
  have hcptr : R.plan.proofLayout.proofCptr = 0x64 := by
    have h := hcptrb
    rw [show abiVerifyProofProofCptr = 0x64 from by
      norm_num [abiVerifyProofProofCptr, abiSelectorBytes, abiVerifyProofHeadBytes,
        abiVerifyProofHeadWords, Midfall.Generator.wordBytes]] at h
    exact eq_of_beq h
  have hend : R.plan.proofLayout.proofEnd =
      R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen := eq_of_beq hendb
  have hbnd : R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances < 2 ^ 256 := by
    have h := cdBound_of_valid hR
    rw [hpl, hnum]; exact h
  have hpe_lt : R.pv.proofLayout.proofEnd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hbnd)
  have hpl_lt : R.pv.proofLayout.proofLen < 2 ^ 256 := by
    rw [hpl]
    have h := hpe_lt
    rw [hpl, hend, hcptr] at h
    exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
  have hfitCptr : (BitVec.ofNat 256 (R.pv.proofLayout.proofCptr - 32)).toNat =
      R.pv.proofLayout.proofCptr - 32 := by
    rw [hpl, hcptr, BitVec.toNat_ofNat]
  have hidx : R.pv.proofLayout.proofCptr - 32 = 0x44 := by rw [hpl, hcptr]
  -- word 1
  have hp1' : (cdWord cd 0x44).toNat = R.plan.proofLayout.proofLen := by
    simpa using hp1
  have hc1 : wordFrom st.env.calldata (R.pv.proofLayout.proofCptr - 32) =
      BitVec.ofNat 256 R.pv.proofLayout.proofLen := by
    rw [hidx, hcal, Midfall.LoweringV3.VkWindow.wordFrom_cdWord, hpl]
    apply BitVec.eq_of_toNat_eq
    rw [hp1', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hpl_lt).symm
  -- word 2
  have hp2' : (cdWord cd R.plan.proofLayout.proofEnd).toNat =
      R.cfg.numInstances := by
    simpa using hp2
  have h32n : 32 * R.pv.numInstances < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbnd
  have hnum_lt : R.pv.numInstances < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left R.pv.numInstances (by decide : 0 < 32)) h32n
  have hc2 : wordFrom st.env.calldata R.pv.proofLayout.proofEnd =
      BitVec.ofNat 256 R.pv.numInstances := by
    rw [hcal, Midfall.LoweringV3.VkWindow.wordFrom_cdWord, hpl, hnum]
    apply BitVec.eq_of_toNat_eq
    rw [hp2', BitVec.toNat_ofNat]
    have hcfg_lt : R.cfg.numInstances < 2 ^ 256 := by simpa [hnum] using hnum_lt
    exact (Nat.mod_eq_of_lt hcfg_lt).symm
  -- length
  have hp3' : cd.size = R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances := by
    have h := hp3
    rw [hpl, hnum]
    simpa using h
  have hlen : st.env.calldata.length = cd.size := by
    rw [hcal]
    exact (Array.size_eq_length_toList (xs := cd.data)).symm
  have hc3 : BitVec.ofNat 256 st.env.calldata.length =
      BitVec.ofNat 256 (R.pv.proofLayout.proofEnd + 32) +
        BitVec.ofNat 256 (R.pv.numInstances * 32) := by
    rw [hlen, hp3']
    rw [show R.pv.proofLayout.proofEnd + 32 + 32 * R.pv.numInstances =
      (R.pv.proofLayout.proofEnd + 32) + R.pv.numInstances * 32 by omega]
    exact (BitVec.ofNat_add_ofNat _ _).symm
  exact ⟨hc1, hc2, hc3⟩

theorem vk_cdl_succ_one (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    (succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hS : PureRead funs V succExpr)
    (hnS : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    (hxval : ∀ (st₁ st₂ : EvmState) {av : U256},
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.vals [av] st₂) →
          VEnv.get V "success" = some av)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot = some aVal)
    (hfit : aVal < 2 ^ 256)
    (hword : wordFrom st.env.calldata aVal = BitVec.ofNat 256 m)
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
            Expr.builtin Op.eq [Expr.lit (.number m),
              Expr.builtin Op.calldataload [vkSite slot R.consts]]]) :: ss) Vb stb ob) :
    ∃ (V₁ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb ob ∧
        VEnv.get V₁ "success" = some (1 : U256) ∧ Same st st₁ := by
  obtain ⟨x, av, bv, V₁, st₁, sB, sA, hV₁, hbv, hav, hxv, hrest, hSame⟩ :=
    vk_hdr_peelT R (Expr.lit (.number m))
      (Expr.builtin Op.calldataload [vkSite slot R.consts]) succExpr
      pureLit (pr_cdl R slot) hS (fun st₁ st₃ hh => nh_lit hh) (nh_cdl_site R slot) hnS h
  have hx1 : x = (1 : U256) := Option.some.inj ((hxval _ _ hxv).symm.trans hsucc)
  have hav' : av = BitVec.ofNat 256 m := (vk_lit_val hav).1
  obtain ⟨a, hva, hbvEq, hstB⟩ := vk_cdl_val R slot hbv
  have hsite : vkVal slot R V = some (BitVec.ofNat 256 aVal) := by
    simp only [vkVal, hlookup]
  have haEq : a = BitVec.ofNat 256 aVal := Option.some.inj (hva.symm.trans hsite)
  have hfit' : (BitVec.ofNat 256 aVal).toNat = aVal := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hfit
  have havbv : av = bv := by
    rw [hav', hbvEq, haEq, hfit']
    exact hword.symm
  have hget : VEnv.get V₁ "success" = some (x &&& b2w (decide (av = bv))) :=
    hV₁ ▸ vk_get_set_of_some hsucc
  refine ⟨V₁, st₁, hrest, ?_, ?_⟩
  · rw [hget, hx1, havbv]
    simp [b2w]
  · exact hSame

theorem vk_cdsz_succ_one (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    (succExpr : Expr EVM.Op)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (hS : PureRead funs V succExpr)
    (hnS : ∀ (st₁ st₃ : EvmState),
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.halt st₃) → False)
    (hxval : ∀ (st₁ st₂ : EvmState) {av : U256},
        EvalExpr (Bridge.Dialect c g) funs V st₁ succExpr (.vals [av] st₂) →
          VEnv.get V "success" = some av)
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot = some aVal)
    (hfit : aVal < 2 ^ 256)
    (hword : BitVec.ofNat 256 st.env.calldata.length =
      BitVec.ofNat 256 aVal + BitVec.ofNat 256 m)
    (h : ExecStmts (Bridge.Dialect c g) funs V st
          (Stmt.assign ["success"] (Expr.builtin Op.and [succExpr,
            Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
              Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]]]) :: ss)
          Vb stb ob) :
    ∃ (V₁ : VEnv (Bridge.Dialect c g)) (st₁ : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V₁ st₁ ss Vb stb ob ∧
        VEnv.get V₁ "success" = some (1 : U256) ∧ Same st st₁ := by
  obtain ⟨x, av, bv, V₁, st₁, sB, sA, hV₁, hbv, hav, hxv, hrest, hSame⟩ :=
    vk_hdr_peelT R (Expr.builtin Op.calldatasize [])
      (Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]) succExpr
      pureCdsz (pr_add R (pureSite R slot) pureLit) hS (fun st₁ st₃ hh => nh_cdsz hh) (nh_add_site_lit R slot m) hnS h
  have hx1 : x = (1 : U256) := Option.some.inj ((hxval _ _ hxv).symm.trans hsucc)
  obtain ⟨a, hva, hbvEq, hstB⟩ := vk_add_site_val R slot m hbv
  have hav' : av = BitVec.ofNat 256 st.env.calldata.length := by
    rw [(vk_cdsz_val hav).1, hstB]
  have hsite : vkVal slot R V = some (BitVec.ofNat 256 aVal) := by
    simp only [vkVal, hlookup]
  have haEq : a = BitVec.ofNat 256 aVal := Option.some.inj (hva.symm.trans hsite)
  have havbv : av = bv := by
    rw [hav', hbvEq, haEq]
    exact hword
  have hget : VEnv.get V₁ "success" = some (x &&& b2w (decide (av = bv))) :=
    hV₁ ▸ vk_get_set_of_some hsucc
  refine ⟨V₁, st₁, hrest, ?_, ?_⟩
  · rw [hget, hx1, havbv]
    simp [b2w]
  · exact hSame

theorem vkBody_normal (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (mVk payLen : Nat)
    {funs funs' : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hvkloc : VEnv.get V "vk" = some vkAddr)
    (hcode : st.env.extCodeOf vkAddr = R.plan.vk.runtimeBytes.data.toList)
    (hg1 : ∀ {st₁ : EvmState} {cv : U256},
        EvalExpr (Bridge.Dialect c g) funs V st (vkGuard R.consts) (.vals [cv] st₁) → cv = 0)
    (hmVk : mVk = ptrAddr R.pv.memory.vkMptr)
    (hpay : payLen = R.pv.vk.len)
    (hVK : R.consts.lookup "VK_MPTR" = some mVk)
    (hPL : R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (hP1 : R.consts.lookup "PROOF_LEN_CPTR" = some (R.pv.proofLayout.proofCptr - 32))
    (hP2 : R.consts.lookup "NUM_INSTANCE_CPTR" = some R.pv.proofLayout.proofEnd)
    (hP3 : R.consts.lookup "INSTANCE_CPTR" = some (R.pv.proofLayout.proofEnd + 32))
    (henv : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true)
    (hcal : st.env.calldata = cd.data.toList)
    (hfit1 : R.pv.proofLayout.proofCptr - 32 < 2 ^ 256)
    (hfit2 : R.pv.proofLayout.proofEnd < 2 ^ 256)
    (hfit3 : R.pv.proofLayout.proofEnd + 32 < 2 ^ 256)
    {Vb : VEnv (Bridge.Dialect c g)} {stb : EvmState} {ob : Outcome}
    (h : ExecStmts (Bridge.Dialect c g) funs V st
      (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
        R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
        R.pv.proofLayout.proofLen) Vb stb ob) :
    ob = .normal := by
  rw [vkBody_nil] at h
  rcases vkS1_skipT R hg1 h with ⟨st₁, h₁, tr₁⟩
  obtain ⟨st₂, h₂, e₂, k₂, hmem⟩ :=
    vkS2_peelT R vkAddr mVk payLen hvkloc hVK hPL h₁
  have hmem' : st₂.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1
      R.pv.vk.len (st.env.extCodeOf vkAddr) := by
    rw [tr₁.2.2, tr₁.1, hmVk, hpay] at hmem
    rw [hmem, Midfall.LoweringV3.MemoryPairs.fit1_of_valid hR,
      Midfall.LoweringV3.MemoryPairs.fit2_of_valid hR]
  rw [show vkSucc0 R.consts = vkSucc from vkSucc0_var R] at h₂
  have hnum : R.pv.numInstances = R.cfg.numInstances :=
    (Midfall.LoweringV3.MemoryPairs.row_premises_of_generated R hR.generated hR.inputs.1
      hR.supported.separateVk).1
  have hdrVals := vk_hdr_read_values R hR st st₂ vkAddr hcode hmem'
  have pz := pv_acc_words_zero hR
  have env2 : st₂.env = st.env := e₂.trans tr₁.1
  -- header 1
  obtain ⟨V₃, st₃, h₃, hs₃, same₃⟩ :=
    vk_hdr_succ_one R "NUM_INSTANCES_MPTR" vkHeaderTemplateSlotsDefault.numInstances
      R.pv.numInstances vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hsucc (vkHeaderLookupsV3 hR).1
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [hnum]; exact hdrVals.1) h₂
  have env3 : st₃.env = st.env := same₃.1.trans env2
  -- header 2
  obtain ⟨V₄, st₄, h₄, hs₄, same₄⟩ :=
    vk_hdr_succ_one R "K_MPTR" vkHeaderTemplateSlotsDefault.k
      R.pv.k vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₃ (vkHeaderLookupsV3 hR).2.1
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [same₃.2.2, ← hR.env.domainN.2]; exact hdrVals.2.1) h₃
  have env4 : st₄.env = st.env := same₄.1.trans env3
  have mem4 : st₄.memory = st₂.memory := same₄.2.2.trans same₃.2.2
  -- header 3
  obtain ⟨V₅, st₅, h₅, hs₅, same₅⟩ :=
    vk_hdr_succ_one R "HAS_ACCUMULATOR_MPTR" vkHeaderTemplateSlotsDefault.hasAccumulator
      R.pv.expectedHasAccumulatorWord vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₄ (vkHeaderLookupsV3 hR).2.2.1
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [mem4, pz.1]; simpa using hdrVals.2.2.1) h₄
  have env5 : st₅.env = st.env := same₅.1.trans env4
  have mem5 : st₅.memory = st₂.memory := same₅.2.2.trans mem4
  -- header 4
  obtain ⟨V₆, st₆, h₆, hs₆, same₆⟩ :=
    vk_hdr_succ_one R "ACC_OFFSET_MPTR" vkHeaderTemplateSlotsDefault.accOffset
      R.pv.expectedAccOffset vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₅ (vkHeaderLookupsV3 hR).2.2.2.1
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [mem5, pz.2.1]; simpa using hdrVals.2.2.2.1) h₅
  have env6 : st₆.env = st.env := same₆.1.trans env5
  have mem6 : st₆.memory = st₂.memory := same₆.2.2.trans mem5
  -- header 5
  obtain ⟨V₇, st₇, h₇, hs₇, same₇⟩ :=
    vk_hdr_succ_one R "NUM_ACC_LIMBS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbs
      R.pv.expectedNumAccLimbs vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₆ (vkHeaderLookupsV3 hR).2.2.2.2.1
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [mem6, pz.2.2.1]; simpa using hdrVals.2.2.2.2.1) h₆
  have env7 : st₇.env = st.env := same₇.1.trans env6
  have mem7 : st₇.memory = st₂.memory := same₇.2.2.trans mem6
  -- header 6
  obtain ⟨V₈, st₈, h₈, hs₈, same₈⟩ :=
    vk_hdr_succ_one R "NUM_ACC_LIMB_BITS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbBits
      R.pv.expectedNumAccLimbBits vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₇ (vkHeaderLookupsV3 hR).2.2.2.2.2
      (vk_hdr_addr_fit R hR _ (by decide))
      (by rw [mem7, pz.2.2.2]; simpa using hdrVals.2.2.2.2.2) h₇
  have env8 : st₈.env = st.env := same₈.1.trans env7
  -- S9
  obtain ⟨st₉, h₉, same₉⟩ := vkS9_skipT R "ERR_VK_MISMATCH" hs₈ h₈
  have env9 : st₉.env = st.env := same₉.1.trans env8
  -- the three calldata checks
  obtain ⟨hC1, hC2, hC3⟩ := envelope_calldata_facts R hR cd henv hcal
  obtain ⟨V₁₀, st₁₀, h₁₀, hs₁₀, same₁₀⟩ :=
    vk_cdl_succ_one R "PROOF_LEN_CPTR" (R.pv.proofLayout.proofCptr - 32)
      R.pv.proofLayout.proofLen vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₈ hP1 hfit1
      (by rw [env9]; exact hC1) h₉
  have env10 : st₁₀.env = st.env := same₁₀.1.trans env9
  obtain ⟨V₁₁, st₁₁, h₁₁, hs₁₁, same₁₁⟩ :=
    vk_cdl_succ_one R "NUM_INSTANCE_CPTR" R.pv.proofLayout.proofEnd
      R.pv.numInstances vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₁₀ hP2 hfit2
      (by rw [env10]; exact hC2) h₁₀
  have env11 : st₁₁.env = st.env := same₁₁.1.trans env10
  obtain ⟨V₁₂, st₁₂, h₁₂, hs₁₂, same₁₂⟩ :=
    vk_cdsz_succ_one R "INSTANCE_CPTR" (R.pv.proofLayout.proofEnd + 32)
      (R.pv.numInstances * 32) vkSucc pr_succ (fun _ _ hh => vkSucc2_ne_halts hh)
      (fun _ _ _ hh => vk_var_hsite hh) hs₁₁ hP3 hfit3
      (by rw [env11]; exact hC3) h₁₁
  obtain ⟨st₁₃, h₁₃, _⟩ := vkS9_skipT R "ERR_BAD_CALLDATA_SHAPE" hs₁₂ h₁₂
  cases h₁₃
  rfl

theorem vk_all_normal (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas)
    (hacc : LeanAccepts R H cd) :
    StmtsContractAll (D := Bridge.Dialect (c) g)
      (R.scope (c) g) (R.slice Partial.vkLoading)
      (fun V st => StageInv R H vkAddr cd Checkpoint.start V st)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd Checkpoint.vk V' st') := by
  intro V st hpre V' st' o hrun
  have hpre' := hpre
  obtain ⟨hframe, hsucc, hbase, hraw, -, -⟩ := hpre
  -- the S1 guard is silent
  have hcodec : vkCodehashArm R.model :=
    (Midfall.LoweringV3.MemoryPairs.generated_model_facts hR.generated).2
      hR.supported.separateVk
  -- table lookups
  obtain ⟨hVK, hPL, hP1, hP2, hP3⟩ := Midfall.LoweringV3.VkWindow.vkTableV3 hR hcodec
  -- the envelope from LeanAccepts
  obtain ⟨ms, instW, inst, hdec, -, -⟩ := hacc
  rw [Midfall.Lowering.Stage.decodeCalldata_eq_raw] at hdec
  have henv : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true := by
    obtain ⟨r, hr⟩ : ∃ r,
        Midfall.Lowering.Stage.rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd =
          some r := by
      cases hr : Midfall.Lowering.Stage.rawDecode (p := p) R.plan.proofLayout
          R.cfg.numInstances cd with
      | none => rw [hr, Option.bind] at hdec; exact absurd hdec (by simp)
      | some r => exact ⟨r, rfl⟩
    unfold Midfall.Lowering.Stage.rawDecode at hr
    by_cases h : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true
    · exact h
    · rw [ite_eq_right h] at hr
      exact absurd hr (by simp)
  -- fits
  have he := henv
  simp only [envelopeOk, Bool.and_eq_true] at he
  have habi := he.1.1.1
  simp only [abiHeadOk, Bool.and_eq_true] at habi
  obtain ⟨⟨⟨hsel, hcptrb⟩, hendb⟩, _⟩ := habi
  have hcptr : R.plan.proofLayout.proofCptr = 0x64 := by
    have h := hcptrb
    rw [show abiVerifyProofProofCptr = 0x64 from by
      norm_num [abiVerifyProofProofCptr, abiSelectorBytes, abiVerifyProofHeadBytes,
        abiVerifyProofHeadWords, Midfall.Generator.wordBytes]] at h
    exact eq_of_beq h
  have hnum : R.pv.numInstances = R.cfg.numInstances :=
    (Midfall.LoweringV3.MemoryPairs.row_premises_of_generated R hR.generated hR.inputs.1
      hR.supported.separateVk).1
  have hb := cdBound_of_valid hR
  have hb' : R.pv.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256 := by
    rw [show R.pv.proofLayout = R.plan.proofLayout from rfl]
    exact hb
  have hfit1 : R.pv.proofLayout.proofCptr - 32 < 2 ^ 256 := by
    show R.plan.proofLayout.proofCptr - 32 < 2 ^ 256
    rw [hcptr]; norm_num
  have hfit2 : R.pv.proofLayout.proofEnd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hb')
  have hfit3 : R.pv.proofLayout.proofEnd + 32 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hb')
  have hrun0 := hrun
  rw [vk_sliceV3 R hR] at hrun
  have hfail : lookupFun (R.scope (c) g) "fail" =
      some (failFDecl, R.scope (c) g) := fail_lookup R
  rcases Step.stmts_cons_inv
      (D := Bridge.Dialect (c) g) hrun with
    ⟨V₁, st₁, h₁, hnil⟩ | ⟨h₁, hne⟩
  · cases hnil
    cases h₁ with
    | block hbody =>
        rename_i Vb
        have hfail' := vkBody_fail_lookup R R.pv.numInstances R.pv.k
          R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
          R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen hfail
        have hnorm := vkBody_normal R hR H vkAddr cd (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len
          hfail' hsucc hframe.vk hframe.vkCode
          (vkGuard_zero R hR hcodec H vkAddr cd hframe)
          rfl rfl hVK hPL hP1 hP2 hP3 henv
          hframe.calldata hfit1 hfit2 hfit3 hbody
        have hclean := vk_clean_walkV3 (c := c) R hR H vkAddr cd g V st hpre'
          (restore V Vb) st' .normal hrun0
        rcases hclean with hrev | ⟨ho, hst⟩
        · exact absurd (hrev.1.symm.trans hnorm) (by decide)
        · exact ⟨rfl, hst⟩
  · cases h₁ with
    | block hbody =>
        have hfail' := vkBody_fail_lookup R R.pv.numInstances R.pv.k
          R.pv.expectedHasAccumulatorWord R.pv.expectedAccOffset R.pv.expectedNumAccLimbs
          R.pv.expectedNumAccLimbBits R.pv.proofLayout.proofLen hfail
        have hnorm := vkBody_normal R hR H vkAddr cd (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len
          hfail' hsucc hframe.vk hframe.vkCode
          (vkGuard_zero R hR hcodec H vkAddr cd hframe)
          rfl rfl hVK hPL hP1 hP2 hP3 henv
          hframe.calldata hfit1 hfit2 hfit3 hbody
        exact absurd hnorm hne

#print axioms Midfall.LoweringV3.VkClean.vkBody_normal
#print axioms Midfall.LoweringV3.VkClean.vk_all_normal
#cone_sorries Midfall.LoweringV3.VkClean.vk_all_normal
#assert_axioms Midfall.LoweringV3.VkClean.vk_all_normal
  [propext, Classical.choice, Quot.sound] native []

theorem vkGuard_eval_zero (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hcode : vkCodehashArm R.model) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hframe : Frame R H vkAddr cd V st) :
    EvalExpr (Bridge.Dialect c g) funs V st (vkGuard R.consts) (.vals [0] st) := by
  have hvk : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var "vk") (.vals [vkAddr] st) :=
    Step.var hframe.vk
  have hecs : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.extcodesize [Expr.var "vk"])
      (.vals [BitVec.ofNat 256 (st.env.extCodeOf vkAddr).length] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil hvk)
      (by simp [builtinWithExternal, stepOp, rd1])
  have hcodeLen : (st.env.extCodeOf vkAddr).length = R.plan.vk.runtimeBytes.size := by
    rw [hframe.vkCode]; exact Array.size_eq_length_toList
  have hLenLit : EvalExpr (Bridge.Dialect c g) funs V st
      (vkSite "EXPECTED_VK_LENGTH" R.consts)
      (.vals [BitVec.ofNat 256 R.plan.vk.runtimeBytes.size] st) := by
    rw [show vkSite "EXPECTED_VK_LENGTH" R.consts =
      Expr.lit (.number R.plan.vk.runtimeBytes.size) from by
      simp [vkSite, consts_lookup_EXPECTED_VK_LENGTH_V3 hR hcode]]
    exact Step.lit
  have heq1 : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
        vkSite "EXPECTED_VK_LENGTH" R.consts]) (.vals [1] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hLenLit) hecs)
      (by simp [builtinWithExternal, stepOp, bin, hcodeLen, b2w])
  have hech : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.extcodehash [Expr.var "vk"])
      (.vals [projectedCodeHash st.env st.env.balanceOf vkAddr] st) :=
    Step.builtinOk (Step.argsCons Step.argsNil hvk)
      (by simp [builtinWithExternal, stepOp, rd1])
  have hne : (st.env.extCodeOf vkAddr).length ≠ 0 := by
    rw [hframe.vkCode]; exact hframe.vkNonEmpty
  have hHashVal : projectedCodeHash st.env st.env.balanceOf vkAddr =
      keccak256 R.plan.vk.runtimeBytes := by
    rw [projectedCodeHash_eq_keccak _ vkAddr hne, hframe.keccak, hframe.vkCode]
    change H (ByteArray.mk R.plan.vk.runtimeBytes.data.toList.toArray) = _
    rw [Midfall.LoweringV3.VkWindow.bytes_mk_toList, hframe.vkHash]
  have hHashLit : EvalExpr (Bridge.Dialect c g) funs V st
      (vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts)
      (.vals [BitVec.ofNat 256 (keccak256 R.plan.vk.runtimeBytes).toNat] st) := by
    rw [show vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts =
      Expr.lit (.number (keccak256 R.plan.vk.runtimeBytes).toNat) from by
      simp [vkSite, consts_lookup_EXPECTED_VK_CODEHASH_WORD_V3 hR hcode]]
    exact Step.lit
  have hhashEq : projectedCodeHash st.env st.env.balanceOf vkAddr =
      BitVec.ofNat 256 (keccak256 R.plan.vk.runtimeBytes).toNat := by
    rw [hHashVal]
    simpa using (BitVec.ofNat_toNat (keccak256 R.plan.vk.runtimeBytes)).symm
  have heq2 : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
        vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]) (.vals [1] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hHashLit) hech)
      (by simp [builtinWithExternal, stepOp, bin, hhashEq, b2w])
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [
        Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
          vkSite "EXPECTED_VK_LENGTH" R.consts],
        Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
          vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]]) (.vals [1] st) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil heq2) heq1)
      (by simp [builtinWithExternal, stepOp, bin, b2w])
  have hguardEq : vkGuard R.consts = Expr.builtin Op.iszero [Expr.builtin Op.and [
      Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
        vkSite "EXPECTED_VK_LENGTH" R.consts],
      Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
        vkSite "EXPECTED_VK_CODEHASH_WORD" R.consts]]] := by
    simp [vkGuard, vkVk0_var R]
  rw [hguardEq]
  exact Step.builtinOk (Step.argsCons Step.argsNil hand)
    (by simp [builtinWithExternal, stepOp, un, b2w])

theorem vk_step_s1 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (hcode : vkCodehashArm R.model)
    (H : Hash) (vkAddr : U256) (cd : Bytes)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hframe : Frame R H vkAddr cd V st) :
    ExecStmt (Bridge.Dialect c g) funs V st (vkS1 R.consts) V st .normal :=
  Step.ifFalse (vkGuard_eval_zero R hR hcode H vkAddr cd hframe) (by rfl)

theorem vk_step_s2 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (vkAddr : U256)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hvkloc : VEnv.get V "vk" = some vkAddr)
    (hVK : R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr))
    (hPL : R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some R.pv.vk.len) :
    ExecStmt (Bridge.Dialect c g) funs V st (vkS2 R.consts) V
      { touchMemory st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len with
        memory := copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
          (st.env.extCodeOf vkAddr) } .normal := by
  have hvk : EvalExpr (Bridge.Dialect c g) funs V st (vkVk0 R.consts) (.vals [vkAddr] st) := by
    rw [vkVk0_var R]; exact Step.var hvkloc
  have hVKs : EvalExpr (Bridge.Dialect c g) funs V st (vkSite "VK_MPTR" R.consts)
      (.vals [BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)] st) := by
    rw [show vkSite "VK_MPTR" R.consts = Expr.lit (.number (ptrAddr R.pv.memory.vkMptr)) from by
      simp [vkSite, hVK]]
    exact Step.lit
  have h1 : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number 1))
      (.vals [(1 : U256)] st) := Step.lit
  have hPLs : EvalExpr (Bridge.Dialect c g) funs V st (vkSite "EXPECTED_VK_PAYLOAD_LENGTH" R.consts)
      (.vals [BitVec.ofNat 256 R.pv.vk.len] st) := by
    rw [show vkSite "EXPECTED_VK_PAYLOAD_LENGTH" R.consts =
      Expr.lit (.number R.pv.vk.len) from by simp [vkSite, hPL]]
    exact Step.lit
  have hfit1 : (BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr)).toNat = ptrAddr R.pv.memory.vkMptr :=
    Midfall.LoweringV3.MemoryPairs.fit1_of_valid hR
  have hfit2 : (BitVec.ofNat 256 R.pv.vk.len).toNat = R.pv.vk.len :=
    Midfall.LoweringV3.MemoryPairs.fit2_of_valid hR
  refine Step.exprStmt (D := Bridge.Dialect c g) (Step.builtinOk (D := Bridge.Dialect c g) (st1 := st)
    (argvals := [vkAddr, BitVec.ofNat 256 (ptrAddr R.pv.memory.vkMptr), (1 : U256),
      BitVec.ofNat 256 R.pv.vk.len])
    (st2 := { touchMemory st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len with
      memory := copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
        (st.env.extCodeOf vkAddr) }) ?_ ?_)
  · exact Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hPLs) h1)
      hVKs) hvk
  · simp [builtinWithExternal, stepOp, hfit1, hfit2]


theorem vk_step_hdr (R : Render p G₁ G₂ Gₜ) (slot : String) (i n : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot =
      some (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i)))
    (hfit : Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i) < 2 ^ 256)
    (hword : loadWord st.memory (ptrAddr (Ptr.add R.pv.memory.vkMptr i)) =
      BitVec.ofNat 256 n) :
    ExecStmt (Bridge.Dialect c g) funs V st (vkHdr slot n R.consts vkSucc)
      (VEnv.set V "success" ((1 : U256) &&& 1))
      (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32) .normal := by
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st (vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))] st) := by
    rw [show vkSite slot R.consts =
      Expr.lit (.number (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))) from by
      simp [vkSite, hlookup]]
    exact Step.lit
  have hmload : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mload [vkSite slot R.consts])
      (.vals [loadWord st.memory
        (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat]
        (touchMemory st
          (BitVec.ofNat 256 (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons Step.argsNil hsite)
      (by simp [builtinWithExternal, stepOp])
  have hfit' : (BitVec.ofNat 256
      (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat =
      ptrAddr (Ptr.add R.pv.memory.vkMptr i) := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simpa [Midfall.LoweringV2.cAddr_eq_ptrAddr] using hfit)
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n))
      (.vals [BitVec.ofNat 256 n] st) := Step.lit
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.mload [vkSite slot R.consts],
        Expr.lit (.number n)]) (.vals [1] (touchMemory st (BitVec.ofNat 256
          (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil hlit) hmload)
      (by simp [builtinWithExternal, stepOp, bin, hword, hfit', b2w])
  have hsuccE : EvalExpr (Bridge.Dialect c g) funs V
      (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32) vkSucc (.vals [1]
      (touchMemory st (BitVec.ofNat 256
        (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.var hsucc
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [vkSucc,
        Expr.builtin Op.eq [Expr.builtin Op.mload [vkSite slot R.consts],
          Expr.lit (.number n)]]) (.vals [(1 : U256) &&& 1] (touchMemory st (BitVec.ofNat 256
            (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr i))).toNat 32)) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil heq) hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)


theorem vk_step_gate (R : Render p G₁ G₂ Gₜ) (err : String)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hsucc : VEnv.get V "success" = some (1 : U256)) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [vkSucc])
        [Stmt.exprStmt (Expr.call "fail" [vkSite err R.consts])]) V st .normal := by
  have hvar : EvalExpr (Bridge.Dialect c g) funs V st vkSucc (.vals [1] st) := Step.var hsucc
  have hz : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [vkSucc]) (.vals [0] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil hvar)
      (by simp [builtinWithExternal, stepOp, un, b2w])
  exact Step.ifFalse hz rfl

theorem vk_step_cdl (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot = some aVal)
    (hfit : aVal < 2 ^ 256)
    (hword : wordFrom st.env.calldata aVal = BitVec.ofNat 256 m) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
        Expr.builtin Op.eq [Expr.lit (.number m),
          Expr.builtin Op.calldataload [vkSite slot R.consts]]]))
      (VEnv.set V "success" ((1 : U256) &&& 1)) st .normal := by
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st (vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 aVal] st) := by
    rw [show vkSite slot R.consts = Expr.lit (.number aVal) from by simp [vkSite, hlookup]]
    exact Step.lit
  have hcdl : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.calldataload [vkSite slot R.consts])
      (.vals [wordFrom st.env.calldata (BitVec.ofNat 256 aVal).toNat] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) (Step.argsCons Step.argsNil hsite)
      (by simp [builtinWithExternal, stepOp, rd1])
  rw [show (BitVec.ofNat 256 aVal).toNat = aVal from by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hfit] at hcdl
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number m))
      (.vals [BitVec.ofNat 256 m] st) := Step.lit
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.lit (.number m),
        Expr.builtin Op.calldataload [vkSite slot R.consts]]) (.vals [1] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil hcdl) hlit)
      (by simp [builtinWithExternal, stepOp, bin, hword, b2w])
  have hsuccE : EvalExpr (Bridge.Dialect c g) funs V st vkSucc (.vals [1] st) := Step.var hsucc
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [vkSucc,
        Expr.builtin Op.eq [Expr.lit (.number m),
          Expr.builtin Op.calldataload [vkSite slot R.consts]]])
      (.vals [(1 : U256) &&& 1] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil heq) hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)

theorem vk_step_cdsz (R : Render p G₁ G₂ Gₜ) (slot : String) (aVal m : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hlookup : R.consts.lookup slot = some aVal)
    (hfit : aVal < 2 ^ 256)
    (hword : BitVec.ofNat 256 st.env.calldata.length =
      BitVec.ofNat 256 aVal + BitVec.ofNat 256 m) :
    ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["success"] (Expr.builtin Op.and [vkSucc,
        Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
          Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]]]))
      (VEnv.set V "success" ((1 : U256) &&& 1)) st .normal := by
  have hsize : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin Op.calldatasize [])
      (.vals [BitVec.ofNat 256 st.env.calldata.length] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) Step.argsNil
      (by simp [builtinWithExternal, stepOp, rd0])
  have hsite : EvalExpr (Bridge.Dialect c g) funs V st (vkSite slot R.consts)
      (.vals [BitVec.ofNat 256 aVal] st) := by
    rw [show vkSite slot R.consts = Expr.lit (.number aVal) from by simp [vkSite, hlookup]]
    exact Step.lit
  have hlit : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number m))
      (.vals [BitVec.ofNat 256 m] st) := Step.lit
  have hadd : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)])
      (.vals [BitVec.ofNat 256 aVal + BitVec.ofNat 256 m] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil hlit) hsite)
      (by simp [builtinWithExternal, stepOp, bin])
  have heq : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
        Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]]) (.vals [1] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil hadd) hsize)
      (by simp [builtinWithExternal, stepOp, bin, hword, b2w])
  have hsuccE : EvalExpr (Bridge.Dialect c g) funs V st vkSucc (.vals [1] st) := Step.var hsucc
  have hand : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [vkSucc,
        Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
          Expr.builtin Op.add [vkSite slot R.consts, Expr.lit (.number m)]]])
      (.vals [(1 : U256) &&& 1] st) :=
    Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (Step.argsCons Step.argsNil heq) hsuccE)
      (by simp [builtinWithExternal, stepOp, bin])
  exact Step.assignVal (D := Bridge.Dialect c g) (vars := ["success"]) hand (by rfl)

theorem vk_exists_run (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} (hR : ValidV3 R)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas)
    (hacc : LeanAccepts R H cd) :
    StmtsContract (D := Bridge.Dialect (c) g)
      (R.scope (c) g) (R.slice Partial.vkLoading)
      (fun V st => StageInv R H vkAddr cd Checkpoint.start V st)
      (fun _ _ V' st' o => o = .normal ∧ StageInv R H vkAddr cd Checkpoint.vk V' st') := by
  intro V st hpre
  have hpre' := hpre
  have hacc' := hacc
  obtain ⟨hframe, hsucc, hbase, hraw, -, -⟩ := hpre
  have hcodec : vkCodehashArm R.model :=
    (Midfall.LoweringV3.MemoryPairs.generated_model_facts hR.generated).2
      hR.supported.separateVk
  obtain ⟨hVK, hPL, hP1, hP2, hP3⟩ := Midfall.LoweringV3.VkWindow.vkTableV3 hR hcodec
  obtain ⟨hSN, hSK, hSA, hSO, hSL, hSB⟩ := vkHeaderLookupsV3 hR
  -- envelope and calldata facts
  obtain ⟨ms, instW, inst, hdec, -, -⟩ := hacc
  rw [Midfall.Lowering.Stage.decodeCalldata_eq_raw] at hdec
  have henv : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true := by
    obtain ⟨r, hr⟩ : ∃ r,
        Midfall.Lowering.Stage.rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd =
          some r := by
      cases hr : Midfall.Lowering.Stage.rawDecode (p := p) R.plan.proofLayout
          R.cfg.numInstances cd with
      | none => rw [hr, Option.bind] at hdec; exact absurd hdec (by simp)
      | some r => exact ⟨r, rfl⟩
    unfold Midfall.Lowering.Stage.rawDecode at hr
    by_cases h : envelopeOk R.plan.proofLayout R.cfg.numInstances cd = true
    · exact h
    · rw [ite_eq_right h] at hr
      exact absurd hr (by simp)
  obtain ⟨hC1, hC2, hC3⟩ := envelope_calldata_facts R hR cd henv hframe.calldata
  have he := henv
  simp only [envelopeOk, Bool.and_eq_true] at he
  have habi := he.1.1.1
  simp only [abiHeadOk, Bool.and_eq_true] at habi
  obtain ⟨⟨⟨hsel, hcptrb⟩, hendb⟩, _⟩ := habi
  have hcptr : R.plan.proofLayout.proofCptr = 0x64 := by
    have h := hcptrb
    rw [show abiVerifyProofProofCptr = 0x64 from by
      norm_num [abiVerifyProofProofCptr, abiSelectorBytes, abiVerifyProofHeadBytes,
        abiVerifyProofHeadWords, Midfall.Generator.wordBytes]] at h
    exact eq_of_beq h
  have hnum : R.pv.numInstances = R.cfg.numInstances :=
    (Midfall.LoweringV3.MemoryPairs.row_premises_of_generated R hR.generated hR.inputs.1
      hR.supported.separateVk).1
  have hb := cdBound_of_valid hR
  have hb' : R.pv.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256 := by
    rw [show R.pv.proofLayout = R.plan.proofLayout from rfl]; exact hb
  have hfit1 : R.pv.proofLayout.proofCptr - 32 < 2 ^ 256 := by
    show R.plan.proofLayout.proofCptr - 32 < 2 ^ 256; rw [hcptr]; norm_num
  have hfit2 : R.pv.proofLayout.proofEnd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hb')
  have hfit3 : R.pv.proofLayout.proofEnd + 32 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by simpa [Nat.add_assoc] using hb')
  -- the copy state and the six header states
  let st2 : EvmState :=
    { touchMemory st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len with
      memory := copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
        (st.env.extCodeOf vkAddr) }
  let st3 : EvmState := touchMemory st2 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numInstances))).toNat 32
  let st4 : EvmState := touchMemory st3 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.k))).toNat 32
  let st5 : EvmState := touchMemory st4 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.hasAccumulator))).toNat 32
  let st6 : EvmState := touchMemory st5 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.accOffset))).toNat 32
  let st7 : EvmState := touchMemory st6 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbs))).toNat 32
  let st8 : EvmState := touchMemory st7 (BitVec.ofNat 256
    (Midfall.LoweringV2.cAddr (Ptr.add R.pv.memory.vkMptr vkHeaderTemplateSlotsDefault.numAccLimbBits))).toNat 32
  let V3 : VEnv (Bridge.Dialect (c) g) := VEnv.set V "success" ((1 : U256) &&& 1)
  let V4 := VEnv.set V3 "success" ((1 : U256) &&& 1)
  let V5 := VEnv.set V4 "success" ((1 : U256) &&& 1)
  let V6 := VEnv.set V5 "success" ((1 : U256) &&& 1)
  let V7 := VEnv.set V6 "success" ((1 : U256) &&& 1)
  let V8 := VEnv.set V7 "success" ((1 : U256) &&& 1)
  let V9 := VEnv.set V8 "success" ((1 : U256) &&& 1)
  let V10 := VEnv.set V9 "success" ((1 : U256) &&& 1)
  let V11 := VEnv.set V10 "success" ((1 : U256) &&& 1)
  have hnext : ∀ {W : VEnv (Bridge.Dialect (c) g)},
      VEnv.get W "success" = some (1 : U256) →
        VEnv.get (VEnv.set W "success" ((1 : U256) &&& 1)) "success" = some (1 : U256) := by
    intro W hw
    have hone : ((1 : U256) &&& 1) = 1 := by decide
    rw [vk_get_set_of_some hw, hone]
  have hs3 : VEnv.get V3 "success" = some (1 : U256) := hnext hsucc
  have hs4 : VEnv.get V4 "success" = some (1 : U256) := hnext hs3
  have hs5 : VEnv.get V5 "success" = some (1 : U256) := hnext hs4
  have hs6 : VEnv.get V6 "success" = some (1 : U256) := hnext hs5
  have hs7 : VEnv.get V7 "success" = some (1 : U256) := hnext hs6
  have hs8 : VEnv.get V8 "success" = some (1 : U256) := hnext hs7
  have hs9 : VEnv.get V9 "success" = some (1 : U256) := hnext hs8
  have hs10 : VEnv.get V10 "success" = some (1 : U256) := hnext hs9
  have hs11 : VEnv.get V11 "success" = some (1 : U256) := hnext hs10
  have hhmem : st2.memory = copyInto st.memory (ptrAddr R.pv.memory.vkMptr) 1 R.pv.vk.len
      (st.env.extCodeOf vkAddr) := rfl
  have hdrVals := vk_hdr_read_values R hR st st2 vkAddr hframe.vkCode hhmem
  let funs : FunEnv (Bridge.Dialect (c) g) :=
    hoist (Bridge.Dialect (c) g)
        (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
          R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
          R.pv.proofLayout.proofLen) ::
      R.scope (c) g
  have h1 := vk_step_s1 (funs := funs) R hR hcodec H vkAddr cd hframe
  have h2 := vk_step_s2 (funs := funs) (st := st) R hR vkAddr hframe.vk hVK hPL
  have h3 := vk_step_hdr (funs := funs) R "NUM_INSTANCES_MPTR" vkHeaderTemplateSlotsDefault.numInstances
    R.pv.numInstances hsucc hSN (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [hnum]; exact hdrVals.1)
  have h3' : ExecStmt (Bridge.Dialect (c) g) funs V st2
      (vkHdr "NUM_INSTANCES_MPTR" R.pv.numInstances R.consts (vkSucc0 R.consts))
      (VEnv.set V "success" ((1 : U256) &&& 1)) st3 .normal := by
    rw [show vkHdr "NUM_INSTANCES_MPTR" R.pv.numInstances R.consts (vkSucc0 R.consts) =
      vkHdr "NUM_INSTANCES_MPTR" R.pv.numInstances R.consts vkSucc from by
        rw [vkSucc0_var R]; rfl]
    exact h3
  have h4 := vk_step_hdr (funs := funs) (st := st3) R "K_MPTR" vkHeaderTemplateSlotsDefault.k
    R.pv.k hs3 hSK (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [show st3.memory = st2.memory from rfl, ← hR.env.domainN.2]; exact hdrVals.2.1)
  have h5 := vk_step_hdr (funs := funs) (st := st4) R "HAS_ACCUMULATOR_MPTR" vkHeaderTemplateSlotsDefault.hasAccumulator
    R.pv.expectedHasAccumulatorWord hs4 hSA (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [show st4.memory = st2.memory from rfl, pv_acc_words_zero hR |>.1]; simpa using hdrVals.2.2.1)
  have h6 := vk_step_hdr (funs := funs) (st := st5) R "ACC_OFFSET_MPTR" vkHeaderTemplateSlotsDefault.accOffset
    R.pv.expectedAccOffset hs5 hSO (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [show st5.memory = st2.memory from rfl, pv_acc_words_zero hR |>.2.1]; simpa using hdrVals.2.2.2.1)
  have h7 := vk_step_hdr (funs := funs) (st := st6) R "NUM_ACC_LIMBS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbs
    R.pv.expectedNumAccLimbs hs6 hSL (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [show st6.memory = st2.memory from rfl, pv_acc_words_zero hR |>.2.2.1]; simpa using hdrVals.2.2.2.2.1)
  have h8 := vk_step_hdr (funs := funs) (st := st7) R "NUM_ACC_LIMB_BITS_MPTR" vkHeaderTemplateSlotsDefault.numAccLimbBits
    R.pv.expectedNumAccLimbBits hs7 hSB (vk_hdr_addr_fit R hR _ (by decide))
    (by rw [show st7.memory = st2.memory from rfl, pv_acc_words_zero hR |>.2.2.2]; simpa using hdrVals.2.2.2.2.2)
  have h9 := vk_step_gate (funs := funs) (st := st8) R "ERR_VK_MISMATCH" hs8
  have h10 := vk_step_cdl (funs := funs) (st := st8) R "PROOF_LEN_CPTR" (R.pv.proofLayout.proofCptr - 32)
    R.pv.proofLayout.proofLen hs8 hP1 hfit1 hC1
  have h11 := vk_step_cdl (funs := funs) (st := st8) R "NUM_INSTANCE_CPTR" R.pv.proofLayout.proofEnd
    R.pv.numInstances hs9 hP2 hfit2 hC2
  have h12 := vk_step_cdsz (funs := funs) (st := st8) R "INSTANCE_CPTR" (R.pv.proofLayout.proofEnd + 32)
    (R.pv.numInstances * 32) hs10 hP3 hfit3 hC3
  have h13 := vk_step_gate (funs := funs) (st := st8) R "ERR_BAD_CALLDATA_SHAPE" hs11
  -- chain the body, at the hoisted scope
  have hbody : ExecStmts (Bridge.Dialect (c) g) funs V st
      (vkBody R.consts R.pv.numInstances R.pv.k R.pv.expectedHasAccumulatorWord
        R.pv.expectedAccOffset R.pv.expectedNumAccLimbs R.pv.expectedNumAccLimbBits
        R.pv.proofLayout.proofLen) V11 st8 .normal :=
    Step.seqCons h1 (Step.seqCons h2 (Step.seqCons h3' (Step.seqCons h4
      (Step.seqCons h5 (Step.seqCons h6 (Step.seqCons h7 (Step.seqCons h8
        (Step.seqCons h9 (Step.seqCons h10 (Step.seqCons h11 (Step.seqCons h12
          (Step.seqCons h13 Step.seqNil))))))))))))
  -- the slice run
  have hslice : ExecStmts (Bridge.Dialect (c) g)
      (R.scope (c) g) V st (R.slice Partial.vkLoading)
      (restore V V11) st8 .normal := by
    rw [vk_sliceV3 R hR]
    exact Step.seqCons (Step.block hbody) Step.seqNil
  have hpost := vk_all_normal R hR H vkAddr cd g hacc' V st hpre'
    (restore V V11) st8 .normal hslice
  exact ⟨restore V V11, st8, .normal, hslice, hpost⟩

end Midfall.LoweringV3.VkClean
