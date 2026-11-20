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
  * §5 'StageInv .vk' assembled from the walk plus the three 'generated'-clause premises;
  * §6 'vk_blockSimV3': BOTH conjuncts of 'BlockSim R Partial.vkLoading' over 'StageInv', generic in
    the render.

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
end Midfall.LoweringV3.VkClean
