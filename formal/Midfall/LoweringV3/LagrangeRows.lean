-- |
-- Midfall.LoweringV3.LagrangeRows
--
-- T3.9 (WP A4), RENDER-FREE TRANCHE: the Lagrange block's five symbolic loops, proved FOR EVERY
-- RENDER, and the section-0 vocabulary they are stated in. PORTED from
-- 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean' section 5 (:441-590), which does not
-- compile (RECON.3) - a copy, not an import, exactly as QuotientRows.lean does for ROW.Q.
--
-- WHAT THIS FILE IS. The render-free half of T3.9: the vocabulary and the three kernel-reduction
-- statements (:442 'lag_slice', :455 'lagInner_length', :461 'lag_sq_loop_form'), then the loops
-- that need NO fixture, NO table value and NO row wiring:
--   * T3.9.a 'lag_sq_loop'     - k squarings, the first use of GEN.3's loop rule;
--   * T3.9.b 'lag_denoms_loop' - the shared denominator window, both guard branches; its
--     vocabulary (denomVal/writeWords/loadWord_writeWords_lt/writeWords_outside) and form lemma
--     are here, and the loop is proved by the semantic `allRuns_loop` route (PG-LAG-HEARTBEAT);
--   * T3.9.c 'lag_second_pass_loop' - the second pass, by the same semantic route;
--   * T3.9.d 'lag_lblind_loop' - the blind sum (the cheapest independent leaf);
--   * T3.9.e 'lag_instance_loop' - the instance sum.
-- The remaining child (T3.9.g/h) and the row glue are NOT in this file. Nothing here is
-- wired into Rows.lean, so no root/register/cones move; 'Rows.lean' is untouched.
--
-- PORT CHANGES. Two, both forced by the landed tree and both purely naming:
--   (a) 'wMulmod' -> 'wMulmodAt' and 'wAddmod' -> 'wAddmodAt'. The tree's 'WpX.wMulmod'/'wAddmod'
--       are two-argument functions fixed at the field modulus; the evidence's are three-argument
--       functions at a symbolic 'r'. Same definitions, different functions (QuotientRows header
--       change (c) for 'wMulmod'; 'wAddmodAt' is the same rename on the addmod side).
--   (b) the rows' '(hR : R.Valid)' is not used here: every lemma below is stated at the render's
--       program, table and layout values, so it needs no validity bundle at all.
--
-- NO FIXTURE (D-P71). Every statement is quantified over the table, the bound and the window.
-- 'poseidonRender' appears nowhere.
--
-- AXIOMS. Everything proved here is on [propext, Classical.choice, Quot.sound]; no
-- 'native_decide' (D-P17), no 'maxHeartbeats' or 'maxRecDepth' raise.
--
-- PROVENANCE OF THE PROOFS. This file's proofs are new; the STATEMENTS are the evidence file's,
-- verbatim modulo the two names above. 'lag_sq_loop' applies
-- 'Midfall.Yul.LoopRule.allRuns_for_cons_wp' (GEN.3), which is the rule T3.9.a is the first use of.
import Midfall.LoweringV3.QuotientRows
import Midfall.LoweringV3.LagrangeAlg
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Yul.LoopRule
import Midfall.Yul.Word
import Midfall.LoweringV3.VkWindow
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.LagrangeRows

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst
open Midfall.LoweringV3.QuotientRows
open Midfall.Yul.Wp Midfall.Yul.LoopRule Midfall.Yul.WpBridge
open Midfall.LoweringV3.LagrangeAlg

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

variable {c : ExternalCalls} {g : ExternalGas}

open Lean Elab Tactic Meta in
/-- Close an equality by 'Eq.refl', leaving the definitional check to the KERNEL. VERBATIM port from
the evidence file's section 0 (:83-87), as in QuotientRows: the elaborator's 'rfl' runs 'Meta.whnf',
which exceeds the default heartbeats on an inlined block; the kernel reducer does not. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, _, rhs) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  goal.assign (← mkEqRefl rhs)

/-! ## 1. VOCABULARY, PORTED VERBATIM (GeneratorRows.lean sections 0 and 5) -/

/-- EVM 'addmod' at an ARBITRARY modulus word, as the dialect computes it ('EVMExec.lean:721'). The
evidence file's 'wAddmod' (:99) verbatim, renamed 'wAddmodAt' for the same reason as 'wMulmodAt'
(file header, port change (a)). -/
def wAddmodAt (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)

/-- 'k' squarings: the word the loop 'x_n := mulmod(x_n, x_n, r)' leaves after 'k' iterations.
VERBATIM (:103-105). Note the recursion is on the INPUT, so the round trip to the invariant's
orientation is 'wPow2_succ_outer' below. -/
def wPow2 (r : U256) : Nat → U256 → U256
  | 0, x => x
  | k + 1, x => wPow2 r k (wMulmodAt x x r)

/-- The walk 'w, w·ω, w·ω², …' of 'pow_of_omega := mulmod(pow_of_omega, omega, r)'. VERBATIM
(:108-110). -/
def omegaPows (r omega w0 : U256) : Nat → U256
  | 0 => w0
  | i + 1 => wMulmodAt (omegaPows r omega w0 i) omega r

/-- Memory agrees outside the window '[lo, lo + len)'. VERBATIM (:113-114). -/
def MemSameOutside (st st' : EvmState) (lo len : Nat) : Prop :=
  ∀ a, (a < lo ∨ lo + len ≤ a) → st'.memory a = st.memory a

/-- The state is unchanged EXCEPT for the memory high-water mark 'activeWords'. VERBATIM (:116-122);
the shape an 'mload'-only body leaves ('touchMemory' rewrites 'activeWords' and nothing else). -/
def SameUpToActive (st st' : EvmState) : Prop := ∃ aw, st' = { st with activeWords := aw }

/-- What 'SameUpToActive' gives a caller that only reads memory, the frame and the halt record.
PROVED, VERBATIM (:126-129). -/
theorem SameUpToActive.frame {st st' : EvmState} (h : SameUpToActive st st') :
    st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  obtain ⟨aw, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- The running sum 'acc + Σ_{i < j} f i' modulo 'r', as 'addmod' folds it. VERBATIM (:526-528). -/
def wSum (r : U256) (f : Nat → U256) : Nat → U256 → U256
  | 0, acc => acc
  | j + 1, acc => wAddmodAt (wSum r f j acc) (f j) r

/-- The five words the block persists, as a relation on words (the SEM/ALG interface). VERBATIM
(:571-576). -/
structure LagWords where
  xn : U256
  lLast : U256
  lBlind : U256
  l0 : U256
  instEval : U256

/-- What the block computes from '(r, x, ω, ω⁻ᴸ, n⁻¹)' and the instance words. VERBATIM (:579-590),
with the two renames of port change (a).

**DO NOT READ THIS AS THE T3.9.g RELATION YET.** The evidence's 'lag_agrees' (:595-607) supplies
'w0 = frWord (ω⁻¹ ^ (numNegLagranges - 1))', while the tree's own three statements of the same
quantity - 'PayloadAgrees.omegaInvToL' (LoweringV3/Statements.lean:671-675), 'Protocol.lean:675'
and 'Vk.lean:777-780' - give 'ω⁻¹ ^ numNegLagranges'. The two differ by one factor of ω (the
evidence's starts one word in; see 'lag_lblind_loop'"'"'s 'D + 64' and 'L 1'). T3.9.g is therefore
OFF BY ONE and false as written; it is NOT ported here. 'LagRel' itself is the evidence's relation
and is left unchanged, as the card instructs. -/
def LagRel (rw x om w0 nInv : U256) (k n m : Nat) (inst : Nat → U256) (W : LagWords) : Prop :=
  W.xn = wPow2 rw k x ∧
  ∃ inv : Nat → U256,
    (∀ i, i < n + m →
      wMulmodAt (inv i) (wAddmodAt x (rw - omegaPows rw om w0 i) rw) rw = 1 ∧
      (inv i).toNat < rw.toNat) ∧
    let L : Nat → U256 := fun i =>
      wMulmodAt (wMulmodAt (wAddmodAt W.xn (rw - 1) rw) nInv rw)
        (wMulmodAt (inv i) (omegaPows rw om w0 i) rw) rw
    W.lLast = L 0 ∧ W.l0 = L m ∧
    W.lBlind = wSum rw (fun i => L (2 + i)) (m - 2) (L 1) ∧
    W.instEval = wSum rw (fun j => wMulmodAt (L (m + j)) (inst j) rw) n 0

/-! ## 2. THE KERNEL-REDUCTION STATEMENTS (evidence :442, :455, :461) -/

/-- The slice is the inlined emitter output. PROVED. VERBATIM (:442-444). -/
theorem lag_slice (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.lagrange = Inline.inlineContractConstants R.consts
      (GenAst.emitLagrangeAt R.pv.k R.pv.numInstances R.pv.numNegLagranges) := rfl

/-- The 28 statements of the block's inner scope, constants inlined. VERBATIM (:447-450). -/
def lagInner (consts : Inline.Consts) (k n m : Nat) : Block EVM.Op :=
  match Inline.inlineContractConstants consts (GenAst.emitLagrangeAt k n m) with
  | [_, Stmt.block body, _] => body
  | _ => []

/-- The inner scope has 28 statements at every table and every layout. PROVED by kernel evaluation
('kernel_rfl', no axiom). VERBATIM (:455-456). -/
theorem lagInner_length (consts : Inline.Consts) (k n m : Nat) :
    (lagInner consts k n m).length = 28 := by kernel_rfl

/-- Statement 3 of the inner scope, at EVERY table and layout, is the squaring loop; the only site
left for the table is 'r'. PROVED by kernel reduction. VERBATIM (:461-468). -/
theorem lag_sq_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 3 1 =
      [GenAst.yfor [GenAst.ylet "idx" (GenAst.ylit 0)]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "idx", GenAst.yvar "k"])
        [GenAst.yset "idx" (GenAst.yop EVM.Op.add [GenAst.yvar "idx", GenAst.ylit 1])]
        [GenAst.yset "x_n" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "x_n", GenAst.yvar "x_n", Blocks.VkLoading.vkSite "r" consts])]] := by
  kernel_rfl

/-! ## 3. THE VOCABULARY'S ONE ORIENTATION LEMMA (T3.9.a guidance) -/

/-- The definition's own equation, stated as a rewrite rule: 'wPow2' recurses on the INPUT. -/
theorem wPow2_succ (r x : U256) (j : Nat) :
    wPow2 r (j + 1) x = wPow2 r j (wMulmodAt x x r) := rfl

/-- **THE ORIENTATION THE INVARIANT NEEDS.** After 'j' squarings the register holds 'wPow2 r j x',
and the next body step squares THAT word. The definition recurses on the input instead, so the
round trip is a genuine induction (squaring maps commute with themselves). T3.9.a's guidance names
this lemma as the step to prove first. -/
theorem wPow2_succ_outer (r x : U256) : ∀ j : Nat,
    wPow2 r (j + 1) x = wMulmodAt (wPow2 r j x) (wPow2 r j x) r
  | 0 => rfl
  | j + 1 => by
      show wPow2 r (j + 1) (wMulmodAt x x r) =
        wMulmodAt (wPow2 r (j + 1) x) (wPow2 r (j + 1) x) r
      rw [wPow2_succ_outer r (wMulmodAt x x r) j]
      rfl

/-! ## 4. THE VEnv FACTS THE LOOP PROOFS USE -/

/-- 'VEnv.set' preserves the length: what makes 'restore' the identity at a block exit. PROVED by
induction; the tree has the same fact only at the Bridge dialect (VkClean's
'VEnv.set_length'), and this port is dialect-generic like the rest of the vocabulary. -/
theorem venv_set_length {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (a : D.Value) : (VEnv.set V x a).length = V.length := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

/-- Setting a variable twice is setting it once. PROVED by induction. (VkClean proves the same fact
at the Bridge dialect and its own namespace; this is the generic copy the vocabulary needs.) -/
theorem venv_set_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D} {x : Ident}
    {a b : D.Value} : VEnv.set (VEnv.set V x a) x b = VEnv.set V x b := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x <;> simp [VEnv.set, hy, ih]

/-- Reading back a variable just set, when it IS bound: the 'assign' fact. PROVED by induction. -/
theorem venv_get_set_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {v w : D.Value} (h : VEnv.get V x = some v) :
    VEnv.get (VEnv.set V x w) x = some w := by
  induction V with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x
      · subst hy
        simp [VEnv.set, VEnv.get]
      · have hget : VEnv.get rest x = some v := by
          have h2 : VEnv.get ((y, u) :: rest) x = some v := h
          simpa [VEnv.get, List.find?, hy] using h2
        have h3 := ih hget
        simpa [VEnv.set, VEnv.get, List.find?, hy] using h3

/-- Reading a DIFFERENT variable from a cons: the frame fact for the prepends the emitter makes. -/
theorem venv_get_cons_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get ((x, v) :: V) y = VEnv.get V y := by
  have hd : decide (x = y) = false := decide_eq_false (fun h' => h h'.symm)
  simp only [VEnv.get, List.find?, hd]

/-- Reading the loop's own counter from the head binding: the ONE get the kernel can reduce. -/
theorem venv_get_cons_self_idx (V : VEnv (Bridge.Dialect c g)) (v : U256) :
    VEnv.get (("idx", v) :: V) "idx" = some v := rfl

/-- Reading a DIFFERENT variable after a set: the frame fact. PROVED by induction. -/
theorem venv_get_set_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨y', u⟩ := p
      by_cases hyx : y' = x
      · subst hyx
        have hyy : ¬ (y' = y) := fun h' => h h'.symm
        simp [VEnv.set, VEnv.get, List.find?, hyy]
      · have hset : VEnv.set ((y', u) :: rest) x v = (y', u) :: VEnv.set rest x v := by
          simp [VEnv.set, hyx]
        rw [hset]
        by_cases hyy : y' = y
        · subst hyy
          simp [VEnv.get, List.find?]
        · simpa [VEnv.get, List.find?, hyy] using ih

/-- A loop-exit environment is the outer environment with the inner binding dropped and the
in-place updates kept. This is the 'restore' equation the loop exits need. -/
theorem restore_cons_set {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {y x : Ident} {a b : D.Value} :
    restore V ((y, b) :: VEnv.set V x a) = VEnv.set V x a := by
  simp [restore, venv_set_length]

/-- A loop body that only assigns leaves the environment length unchanged, so its block exit is
the identity: the 'restore' fact every 'wpS (.block …)' needs. -/
theorem restore_set_same {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x : Ident} {a : D.Value} : restore V (VEnv.set V x a) = VEnv.set V x a := by
  simp [restore, venv_set_length]

/-- Setting two DISTINCT variables commutes. PROVED by induction; the loop bodies of the Lagrange
window set `l_blind` and `l_i_cptr`, and the invariant has to agree with both orders. -/
theorem venv_set_comm {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D} {x y : Ident}
    {a b : D.Value} (h : x ≠ y) :
    VEnv.set (VEnv.set V x a) y b = VEnv.set (VEnv.set V y b) x a := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨z, u⟩ := p
      by_cases hzx : z = x
      · subst hzx
        have hzy : ¬ (z = y) := fun h' => h h'
        simp [VEnv.set, hzy]
      · by_cases hzy : z = y
        · subst hzy
          have hzx' : ¬ (z = x) := fun h' => hzx h'
          simp [VEnv.set, hzx']
        · simp [VEnv.set, hzx, hzy, ih]

/-- One iteration of the `l_blind` walk, environment half: the two in-place updates commute past
the loop's own `l_i_cptr_end` binding and collapse. -/
theorem lblind_env_step {V : VEnv (Bridge.Dialect c g)} {e w w' mp mp' : U256} :
    VEnv.set (VEnv.set (("l_i_cptr_end", e) ::
        (VEnv.set V "l_blind" w).set "l_i_cptr" mp) "l_blind" w') "l_i_cptr" mp' =
      ("l_i_cptr_end", e) :: (VEnv.set V "l_blind" w').set "l_i_cptr" mp' := by
  have h1 : VEnv.set (("l_i_cptr_end", e) ::
      (VEnv.set V "l_blind" w).set "l_i_cptr" mp) "l_blind" w' =
      ("l_i_cptr_end", e) :: VEnv.set ((VEnv.set V "l_blind" w).set "l_i_cptr" mp)
        "l_blind" w' := by simp [VEnv.set]
  have h2 : VEnv.set (("l_i_cptr_end", e) ::
      VEnv.set ((VEnv.set V "l_blind" w).set "l_i_cptr" mp) "l_blind" w') "l_i_cptr" mp' =
      ("l_i_cptr_end", e) :: VEnv.set (VEnv.set ((VEnv.set V "l_blind" w).set "l_i_cptr" mp)
        "l_blind" w') "l_i_cptr" mp' := by simp [VEnv.set]
  rw [h1, h2,
    venv_set_comm (D := Bridge.Dialect c g) (V := VEnv.set V "l_blind" w)
      (x := "l_i_cptr") (y := "l_blind") (by decide),
    venv_set_set (D := Bridge.Dialect c g), venv_set_set (D := Bridge.Dialect c g)]

/-- A scope that adds one binding and leaves the rest length-preserved exits by dropping that one
binding: the general form of `restore_cons_set` the multi-target loops need. -/
theorem restore_cons_length {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    {y : Ident} {b : D.Value} (h : W.length = V.length) :
    restore V ((y, b) :: W) = W := by
  simp [restore, h]

/-! ## 5. T3.9.a: THE SQUARING LOOP (first use of GEN.3's rule) -/

/-- **LOOP 1** (statement 3, GenAst.lean:872-874): 'k' squarings. Bound = 'k'. LEAF T3.9.a.
VERBATIM from the evidence (:471-478), with 'wMulmod' -> 'wMulmodAt' (port change (a)).

The rule is 'Midfall.Yul.LoopRule.allRuns_for_cons_wp' with the invariant "after 'j' iterations:
'idx = j' and 'x_n = wPow2 rw j x'"; the body's two assignments are the 'wp' cut and the two
guards are decided by the bound 'hk'. The invariant carries the environment EQUATION because the
post is stated with 'VEnv.set V "x_n"', and it carries the 'VEnv.get' facts as well because the
environment has an arbitrary (symbolic) tail, which 'wp_run' cannot read through. -/
theorem lag_sq_loop {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (consts : Inline.Consts) (hr : consts.lookup "r" = none) (k n m : Nat) (hk : k < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 3 1)
      (fun V _ => VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧ (VEnv.get V "x_n").isSome ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        ∃ x rw, VEnv.get V "x_n" = some x ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "x_n" (wPow2 rw k x)) := by
  rw [lag_sq_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    Blocks.VkLoading.vkSite, hr]
  intro V st hpre
  obtain ⟨hkget, hxsome, hrsome⟩ := hpre
  obtain ⟨x, hx⟩ := QuotientRows.isSome_elim hxsome
  obtain ⟨rw, hrw⟩ := QuotientRows.isSome_elim hrsome
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧ st' = st ∧
      ∃ x rw, VEnv.get V "x_n" = some x ∧ VEnv.get V "r" = some rw ∧
        V' = VEnv.set V "x_n" (wPow2 rw k x)
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop [Stmt.letDecl ["idx"] (some (Expr.lit (Literal.number 0)))]
      (Expr.builtin Op.lt [Expr.var "idx", Expr.var "k"])
      [Stmt.assign ["idx"] (Expr.builtin Op.add [Expr.var "idx", Expr.lit (Literal.number 1)])]
      [Stmt.assign ["x_n"] (Expr.builtin Op.mulmod
        [Expr.var "x_n", Expr.var "x_n", Expr.var "r"])]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j, j ≤ k ∧ st' = st ∧
      V' = ("idx", BitVec.ofNat 256 j) :: VEnv.set V "x_n" (wPow2 rw j x) ∧
      VEnv.get V' "idx" = some (BitVec.ofNat 256 j) ∧
      VEnv.get V' "k" = some (BitVec.ofNat 256 k) ∧
      VEnv.get V' "x_n" = some (wPow2 rw j x) ∧
      VEnv.get V' "r" = some rw
  have hmain : Midfall.Yul.WpTac.AllRuns funs V st
      [Stmt.forLoop [Stmt.letDecl ["idx"] (some (Expr.lit (Literal.number 0)))]
        (Expr.builtin Op.lt [Expr.var "idx", Expr.var "k"])
        [Stmt.assign ["idx"] (Expr.builtin Op.add [Expr.var "idx", Expr.lit (Literal.number 1)])]
        [Stmt.assign ["x_n"] (Expr.builtin Op.mulmod
          [Expr.var "x_n", Expr.var "x_n", Expr.var "r"])]] Q := by
    refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
      (Bopen_sound c g) (Cnone_sound _) (n := 20) Inv ?hinit ?hstep
    · -- init: 'idx := 0' establishes the invariant at j = 0
      refine ⟨rfl, ⟨?_⟩⟩
      show Inv (["idx"].zip [BitVec.ofNat 256 0] ++ V) st
      have hzip : (["idx"].zip [(BitVec.ofNat 256 0 : U256)]) ++ V =
          (("idx", (0 : U256)) :: V) := rfl
      rw [hzip]
      refine ⟨0, Nat.zero_le _, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · change ("idx", (0 : U256)) :: V =
          ("idx", (0 : U256)) :: VEnv.set V "x_n" x
        rw [venv_set_eq_self hx]
      · rfl
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "idx") (y := "k")
        (v := (0 : U256)) (by decide : ("k" : String) ≠ "idx")]
        exact hkget
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "idx") (y := "x_n")
        (v := (0 : U256)) (by decide : ("x_n" : String) ≠ "idx")]
        change VEnv.get V "x_n" = some x
        exact hx
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "idx") (y := "r")
        (v := (0 : U256)) (by decide : ("r" : String) ≠ "idx")]
        exact hrw
    · -- one iteration: guard, body, post
      intro Vi sti hInv
      simp only [Inv] at hInv
      obtain ⟨j, hj, hst, hV, hidx, hkg, hxng, hrg⟩ := hInv
      subst hst
      subst hV
      have hkgV : VEnv.get V "k" = some (BitVec.ofNat 256 k) := by
        have h1 := hkg
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "idx") (y := "k")
          (v := BitVec.ofNat 256 j) (by decide : ("k" : String) ≠ "idx")] at h1
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_n") (y := "k")
          (v := wPow2 rw j x) (by decide : ("k" : String) ≠ "x_n")] at h1
        exact h1
      have hrgV : VEnv.get V "r" = some rw := by
        have h1 := hrg
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "idx") (y := "r")
          (v := BitVec.ofNat 256 j) (by decide : ("r" : String) ≠ "idx")] at h1
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "x_n") (y := "r")
          (v := wPow2 rw j x) (by decide : ("r" : String) ≠ "x_n")] at h1
        exact h1
      simp only [wpIter, wpE, wpA, wpS, wpSS, hkg, hidx, hxng, hrg]
      simp only [Bopen, stepOp, bin]
      refine ⟨?_, ?_⟩
      · -- guard false: j = k, and the rest of the block (empty) holds the post at j
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 j).ult (BitVec.ofNat 256 k)) = (0 : U256) := hguard
        have hle : k ≤ j := LoopRule.lt_guard_false (Nat.lt_of_le_of_lt hj hk) hk h0
        have hjk : j = k := Nat.le_antisymm hj hle
        refine ⟨?allRuns⟩
        intro V' st' o hrun
        cases hrun with
        | seqNil =>
            refine ⟨rfl, rfl, x, rw, hx, hrw, ?_⟩
            rw [hjk]
            exact restore_cons_set (D := Bridge.Dialect c g) (V := V) (x := "x_n")
      · -- guard true: j < k, body and post hold the invariant at j + 1
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 j).ult (BitVec.ofNat 256 k)) ≠ (0 : U256) := hguard
        have hlt : j < k := LoopRule.lt_guard_true (Nat.lt_of_le_of_lt hj hk) hk h0
        simp only [ter, VEnv.setMany, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons,
          List.foldl_nil]
        set m : U256 := if rw = 0 then 0 else BitVec.ofNat 256
          (BitVec.toNat (wPow2 rw j x) * BitVec.toNat (wPow2 rw j x) % BitVec.toNat rw) with hm
        have hset : restore (("idx", BitVec.ofNat 256 j) :: VEnv.set V "x_n" (wPow2 rw j x))
            (VEnv.set (("idx", BitVec.ofNat 256 j) :: VEnv.set V "x_n" (wPow2 rw j x)) "x_n" m) =
            VEnv.set (("idx", BitVec.ofNat 256 j) :: VEnv.set V "x_n" (wPow2 rw j x)) "x_n" m :=
          restore_set_same
        have hset2 : VEnv.set (("idx", BitVec.ofNat 256 j) :: VEnv.set V "x_n" (wPow2 rw j x))
            "x_n" m = ("idx", BitVec.ofNat 256 j) ::
              VEnv.set (VEnv.set V "x_n" (wPow2 rw j x)) "x_n" m := rfl
        simp only [hset]
        simp only [hset2]
        rw [venv_get_cons_self_idx]
        dsimp only
        refine ⟨rfl, ?_⟩
        rw [restore_set_same (D := Bridge.Dialect c g)
          (V := ("idx", BitVec.ofNat 256 j) ::
            (VEnv.set V "x_n" (wPow2 rw j x)).set "x_n" m) (x := "idx")]
        have henv : VEnv.set (("idx", BitVec.ofNat 256 j) ::
              (VEnv.set V "x_n" (wPow2 rw j x)).set "x_n" m)
            "idx" (BitVec.ofNat 256 j + litValue (Literal.number 1)) =
            ("idx", BitVec.ofNat 256 (j + 1)) :: VEnv.set V "x_n" (wPow2 rw (j + 1) x) := by
          rw [show VEnv.set (("idx", BitVec.ofNat 256 j) ::
                (VEnv.set V "x_n" (wPow2 rw j x)).set "x_n" m)
              "idx" (BitVec.ofNat 256 j + litValue (Literal.number 1)) =
              ("idx", BitVec.ofNat 256 j + litValue (Literal.number 1)) ::
                (VEnv.set V "x_n" (wPow2 rw j x)).set "x_n" m from rfl]
          rw [venv_set_set (D := Bridge.Dialect c g) (V := V) (x := "x_n")
            (a := wPow2 rw j x) (b := m), hm]
          change ("idx", BitVec.ofNat 256 j + BitVec.ofNat 256 1) ::
              VEnv.set V "x_n" (if rw = 0 then 0 else
                BitVec.ofNat 256 (BitVec.toNat (wPow2 rw j x) *
                  BitVec.toNat (wPow2 rw j x) % BitVec.toNat rw)) =
            ("idx", BitVec.ofNat 256 (j + 1)) :: VEnv.set V "x_n" (wPow2 rw (j + 1) x)
          rw [wPow2_succ_outer rw x j, BitVec.ofNat_add]
          rfl
        refine ⟨⟨rfl, ⟨?_⟩⟩⟩
        refine ⟨j + 1, Nat.succ_le_of_lt hlt, rfl, henv, ?gidx, ?gk, ?gxn, ?gr⟩
        · rw [henv, venv_get_cons_self_idx]
        · rw [henv, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "x_n" (wPow2 rw (j + 1) x)) (x := "idx") (y := "k")
            (v := BitVec.ofNat 256 (j + 1)) (by decide : ("k" : String) ≠ "idx"),
            venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "k")
              (v := wPow2 rw (j + 1) x) (by decide : ("k" : String) ≠ "x_n")]
          exact hkgV
        · rw [henv, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "x_n" (wPow2 rw (j + 1) x)) (x := "idx") (y := "x_n")
            (v := BitVec.ofNat 256 (j + 1)) (by decide : ("x_n" : String) ≠ "idx")]
          exact venv_get_set_same (D := Bridge.Dialect c g) (V := V) (x := "x_n")
            (v := x) (w := wPow2 rw (j + 1) x) hx
        · rw [henv, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "x_n" (wPow2 rw (j + 1) x)) (x := "idx") (y := "r")
            (v := BitVec.ofNat 256 (j + 1)) (by decide : ("r" : String) ≠ "idx"),
            venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "r")
              (v := wPow2 rw (j + 1) x) (by decide : ("r" : String) ≠ "x_n")]
          exact hrgV
  intro V' st' o hrun
  exact hmain V' st' o hrun

/-! ## 6. THE DENOMINATOR WINDOW (T3.9.b) -/

/-- The word the denominator loop writes at step `i`: `addmod(x, sub(r, pow_i), r)`. -/
def denomVal (rw x : U256) (pows : Nat → U256) (i : Nat) : U256 :=
  wAddmodAt x (rw - pows i) rw

/-- The memory a run of `j` stores leaves: `f 0` at `D`, `f 1` at `D + 32`, …, `f (j-1)` at
`D + 32 (j-1)`. The denominator window is written LEFT TO RIGHT, so this is the shape the loop's
invariant carries. -/
def writeWords (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) : Nat → (Nat → UInt8)
  | 0 => mem
  | j + 1 => storeWord (writeWords mem D f j) (D + 32 * j) (f j)

/-- Reading back a word that was written: the `i`-th store is the value read at `D + 32 i`. -/
theorem loadWord_writeWords_lt (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) :
    ∀ {j i : Nat}, i < j → loadWord (writeWords mem D f j) (D + 32 * i) = f i
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | j + 1, i, h => by
      by_cases hij : i = j
      · subst hij
        rw [writeWords, Midfall.Yul.Word.loadWord_storeWord_same]
      · have hi : i < j := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hij
        have hne : D + 32 * i ≠ D + 32 * j := by omega
        have hdisj : D + 32 * i + 32 ≤ D + 32 * j := by omega
        rw [writeWords, show loadWord (storeWord (writeWords mem D f j) (D + 32 * j) (f j))
              (D + 32 * i) = loadWord (writeWords mem D f j) (D + 32 * i) from
            Midfall.Yul.Word.loadWord_storeWord_disjoint _ _ _ _ (Or.inl hdisj)]
        exact loadWord_writeWords_lt mem D f hi

/-- A store inside the window leaves every byte OUTSIDE the window where it was. This is the frame
half of the denominator loop's post. -/
theorem writeWords_outside (mem : Nat → UInt8) (D : Nat) (f : Nat → U256) :
    ∀ {j a : Nat}, (a < D ∨ D + 32 * j ≤ a) → writeWords mem D f j a = mem a
  | 0, a, _ => rfl
  | j + 1, a, h => by
      rw [writeWords]
      have hnot : ¬ (D + 32 * j ≤ a ∧ a < D + 32 * j + 32) := by
        rintro ⟨h1, h2⟩
        omega
      rw [storeWord, ite_eq_right hnot]
      exact writeWords_outside mem D f (j := j) (a := a) (by omega)

/-- Statement 7 of the inner scope, at every table and layout: the denominator walk. PROVED by
kernel reduction. (T3.9.b's "statement form by kernel_rfl".) -/
theorem lag_denoms_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 7 1 =
      [GenAst.yfor
        [GenAst.ylet "pow_of_omega" (GenAst.yop EVM.Op.mload [Blocks.VkLoading.vkSite "OMEGA_INV_TO_L_MPTR" consts])]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "mptr", GenAst.yvar "mptr_end"])
        [GenAst.yset "mptr" (GenAst.yop EVM.Op.add [GenAst.yvar "mptr", GenAst.ylit 32])]
        [ GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "mptr",
            GenAst.yop EVM.Op.addmod [GenAst.yvar "x",
              GenAst.yop EVM.Op.sub [Blocks.VkLoading.vkSite "r" consts, GenAst.yvar "pow_of_omega"],
              Blocks.VkLoading.vkSite "r" consts]])
        , GenAst.yset "pow_of_omega" (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar "pow_of_omega", GenAst.yvar "omega", Blocks.VkLoading.vkSite "r" consts]) ]] := by
  kernel_rfl

/-- The 256-bit embedding of a Nat below `2^256` is exact: the `toNat` that `stepOp`'s
`mstore`/`mload` compute. -/
theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 256) : (BitVec.ofNat 256 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## 6b. THE FIELD-WORD BRIDGE FOR T3.9.g -/

theorem ofNat_p_ne_zero {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) :
    (BitVec.ofNat 256 p : U256) ≠ 0 := by
  intro h0
  have h := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] at h
  exact (Fact.out : Nat.Prime p).ne_zero h

theorem wAddmodAt_toNat {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) (a b : U256) :
    (wAddmodAt a b (BitVec.ofNat 256 p : U256)).toNat = (a.toNat + b.toNat) % p := by
  rw [wAddmodAt, if_neg (ofNat_p_ne_zero hp), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hlt : (a.toNat + b.toNat) % p < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Fact.out : Nat.Prime p).pos) (Nat.le_of_lt hp)
  rw [Nat.mod_eq_of_lt hlt]

theorem wMulmodAt_toNat {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) (a b : U256) :
    (wMulmodAt a b (BitVec.ofNat 256 p : U256)).toNat = (a.toNat * b.toNat) % p := by
  rw [wMulmodAt, if_neg (ofNat_p_ne_zero hp), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hlt : (a.toNat * b.toNat) % p < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Fact.out : Nat.Prime p).pos) (Nat.le_of_lt hp)
  rw [Nat.mod_eq_of_lt hlt]

theorem frWord_add {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) (a b : Fr p) :
    Midfall.Halo2.frWord (a + b) =
      wAddmodAt (Midfall.Halo2.frWord a) (Midfall.Halo2.frWord b)
        (BitVec.ofNat 256 p : U256) := by
  apply BitVec.eq_of_toNat_eq
  rw [Midfall.Halo2.frWord_toNat hp, wAddmodAt_toNat hp, ZMod.val_add,
    Midfall.Halo2.frWord_toNat hp, Midfall.Halo2.frWord_toNat hp]

theorem frWord_mul {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) (a b : Fr p) :
    Midfall.Halo2.frWord (a * b) =
      wMulmodAt (Midfall.Halo2.frWord a) (Midfall.Halo2.frWord b)
        (BitVec.ofNat 256 p : U256) := by
  apply BitVec.eq_of_toNat_eq
  rw [Midfall.Halo2.frWord_toNat hp, wMulmodAt_toNat hp, ZMod.val_mul,
    Midfall.Halo2.frWord_toNat hp, Midfall.Halo2.frWord_toNat hp]

theorem frWord_sub {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) (a b : Fr p) :
    Midfall.Halo2.frWord (a - b) =
      wAddmodAt (Midfall.Halo2.frWord a) ((BitVec.ofNat 256 p : U256) - Midfall.Halo2.frWord b)
        (BitVec.ofNat 256 p : U256) := by
  apply BitVec.eq_of_toNat_eq
  rw [Midfall.Halo2.frWord_toNat hp, wAddmodAt_toNat hp]
  have hb : (Midfall.Halo2.frWord b).toNat < p := Midfall.Halo2.frWord_toNat_lt hp b
  have hsub : ((BitVec.ofNat 256 p : U256) - Midfall.Halo2.frWord b).toNat =
      p - (Midfall.Halo2.frWord b).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    omega
  rw [hsub, Midfall.Halo2.frWord_toNat hp]
  rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val]
  split
  · rename_i hb0
    have hbz : (Midfall.Halo2.frWord b).toNat = 0 := by
      rw [Midfall.Halo2.frWord_toNat hp b, hb0]
      exact ZMod.val_zero
    rw [hbz, Nat.sub_zero, Nat.add_zero, Nat.add_mod_right]
  · rw [Midfall.Halo2.frWord_toNat hp]

/-! ## 6c. THE RUNNING POWERS AND THE SQUARING LOOP, AT FIELD LEVEL -/

theorem wPow2_frWord {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    (x : Fr p) (k : Nat) :
    wPow2 (BitVec.ofNat 256 p : U256) k (Midfall.Halo2.frWord x) =
      Midfall.Halo2.frWord (x ^ (2 ^ k)) := by
  induction k generalizing x with
  | zero => simp [wPow2]
  | succ k ih =>
      rw [wPow2, ← frWord_mul hp, ih (x * x)]
      congr 1
      rw [mul_pow, ← pow_add]
      congr 1
      rw [pow_succ]
      ring

theorem omegaPows_frWord {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    (om w0 : Fr p) (i : Nat) :
    omegaPows (BitVec.ofNat 256 p : U256) (Midfall.Halo2.frWord om)
        (Midfall.Halo2.frWord w0) i =
      Midfall.Halo2.frWord (w0 * om ^ i) := by
  induction i with
  | zero => simp [omegaPows]
  | succ i ih =>
      rw [omegaPows, ih, frWord_mul hp]
      rw [show w0 * om ^ (i + 1) = (w0 * om ^ i) * om by rw [pow_succ]; ring]
      rw [frWord_mul hp, frWord_mul hp]

theorem frWord_one {p : ℕ} [Fact (Nat.Prime p)] :
    Midfall.Halo2.frWord (1 : Fr p) = (1 : U256) := by
  rw [Midfall.Halo2.frWord, ZMod.val_one]
  rfl

/-- A canonical word is the `frWord` of its own `toNat`. -/
theorem frWord_ofNat_toNat {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    {w : U256} (hw : w.toNat < p) :
    Midfall.Halo2.frWord ((w.toNat : Fr p)) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [Midfall.Halo2.frWord_toNat hp, ZMod.val_natCast, Nat.mod_eq_of_lt hw]

/-- The `LagRel` value `L i`, as a field element. -/
theorem lagWord_eq_frWord {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    (xnW nInvW invW omW : U256) (xnF nInvF invF omF : Fr p)
    (hxn : xnW = Midfall.Halo2.frWord xnF) (hn : nInvW = Midfall.Halo2.frWord nInvF)
    (hi : invW = Midfall.Halo2.frWord invF) (ho : omW = Midfall.Halo2.frWord omF) :
    wMulmodAt (wMulmodAt (wAddmodAt xnW ((BitVec.ofNat 256 p : U256) - 1)
        (BitVec.ofNat 256 p : U256)) nInvW (BitVec.ofNat 256 p : U256))
      (wMulmodAt invW omW (BitVec.ofNat 256 p : U256)) (BitVec.ofNat 256 p : U256) =
    Midfall.Halo2.frWord ((xnF - 1) * nInvF * invF * omF) := by
  rw [hxn, hn, hi, ho]
  rw [show (1 : U256) = Midfall.Halo2.frWord (1 : Fr p) from (frWord_one (p := p)).symm]
  rw [← frWord_sub hp xnF 1]
  rw [show (xnF - 1) * nInvF * invF * omF = ((xnF - 1) * nInvF) * (invF * omF) by ring]
  rw [frWord_mul hp, frWord_mul hp, frWord_mul hp]

/-! ## 7. INVERSION HELPERS FOR THE SEMANTIC LOOP PROOFS (T3.9.b/d) -/

theorem eval_var_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : Ident} {av : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.vals [av] st')) :
    VEnv.get V x = some av ∧ st' = st := by
  cases h with
  | var hget => exact ⟨hget, rfl⟩

theorem eval_lit_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {n : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number n)) (.vals [cv] st')) :
    cv = BitVec.ofNat 256 n ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

theorem eval_builtin_vals_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {op : EVM.Op} {args : List (Expr EVM.Op)}
    {vals : List U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.builtin op args) (.vals vals st')) :
    ∃ argvals st1, EvalArgs (Bridge.Dialect c g) funs V st args (.vals argvals st1) ∧
      (Bridge.Dialect c g).Builtin op argvals st1 (.ok vals st') := by
  cases h with
  | builtinOk hargs hbi => exact ⟨_, _, hargs, hbi⟩

theorem eval_lt_mptr_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.lt [Expr.var "mptr", Expr.var "mptr_end"]) (.vals [cv] st')) :
    ∃ mp me, VEnv.get V "mptr" = some mp ∧ VEnv.get V "mptr_end" = some me ∧
      cv = b2w (mp.ult me) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil htail =>
          cases hnil with
          | argsNil =>
              obtain ⟨hme, rfl⟩ := eval_var_inv htail
              obtain ⟨hmp, rfl⟩ := eval_var_inv hhead
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, hmp, hme, rfl, rfl⟩


/-! ## 8. T3.9.d: THE BLIND SUM -/

/-- Statement 16 of the inner scope: the `l_blind` walk. PROVED by kernel reduction. -/
theorem lag_lblind_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 16 1 =
      [GenAst.yfor
        [GenAst.ylet "l_i_cptr_end" (GenAst.yop EVM.Op.add
          [Blocks.VkLoading.vkSite "LAGRANGE_DENOMS_MPTR" consts, GenAst.ylit (m * 32)])]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "l_i_cptr", GenAst.yvar "l_i_cptr_end"])
        [GenAst.yset "l_i_cptr" (GenAst.yop EVM.Op.add [GenAst.yvar "l_i_cptr", GenAst.ylit 0x20])]
        [GenAst.yset "l_blind" (GenAst.yop EVM.Op.addmod
          [GenAst.yvar "l_blind", GenAst.yop EVM.Op.mload [GenAst.yvar "l_i_cptr"],
            Blocks.VkLoading.vkSite "r" consts])]] := by
  kernel_rfl

/-- **LOOP 4** (statement 16, GenAst.lean:900-904): `l_blind`. Bound = `m - 2` (zero iterations when
`m ≤ 2`; see PG-NEGLAG). LEAF T3.9.d. VERBATIM from the evidence (:533-546), with the two renames.
The body executes `mload(l_i_cptr)`, so the state is preserved only up to `activeWords`
(`SameUpToActive`; `st' = st` is false for `m ≥ 3`). -/
theorem lag_lblind_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m D : Nat)
    (hDn : consts.lookup "LAGRANGE_DENOMS_MPTR" = some D) (hm : 2 ≤ m)
    (hD : D + 32 * m < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 16 1)
      (fun V _ => VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (D + 64)) ∧
        (VEnv.get V "l_blind").isSome ∧ (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ SameUpToActive st st' ∧
        ∃ lb rw, VEnv.get V "l_blind" = some lb ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "l_blind"
              (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) (m - 2) lb))
            "l_i_cptr" (BitVec.ofNat 256 (D + 32 * m))) := by
  rw [lag_lblind_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    Blocks.VkLoading.vkSite, hr, hDn]
  intro V st hpre
  obtain ⟨hlic, hlbsome, hrsome⟩ := hpre
  obtain ⟨lb, hlb⟩ := QuotientRows.isSome_elim hlbsome
  obtain ⟨rw, hrw⟩ := QuotientRows.isSome_elim hrsome
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧ SameUpToActive st st' ∧
      ∃ lb rw, VEnv.get V "l_blind" = some lb ∧ VEnv.get V "r" = some rw ∧
        V' = VEnv.set (VEnv.set V "l_blind"
            (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) (m - 2) lb))
          "l_i_cptr" (BitVec.ofNat 256 (D + 32 * m))
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop
      [Stmt.letDecl ["l_i_cptr_end"] (some (Expr.builtin Op.add
        [Expr.lit (Literal.number D), Expr.lit (Literal.number (m * 32))]))]
      (Expr.builtin Op.lt [Expr.var "l_i_cptr", Expr.var "l_i_cptr_end"])
      [Stmt.assign ["l_i_cptr"] (Expr.builtin Op.add
        [Expr.var "l_i_cptr", Expr.lit (Literal.number 32)])]
      [Stmt.assign ["l_blind"] (Expr.builtin Op.addmod
        [Expr.var "l_blind", Expr.builtin Op.mload [Expr.var "l_i_cptr"], Expr.var "r"])]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j, j ≤ m - 2 ∧
      V' = ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
        VEnv.set (VEnv.set V "l_blind"
          (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) j lb))
          "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)) ∧
      VEnv.get V' "l_i_cptr" = some (BitVec.ofNat 256 (D + 64 + 32 * j)) ∧
      VEnv.get V' "l_i_cptr_end" = some (BitVec.ofNat 256 (D + 32 * m)) ∧
      VEnv.get V' "l_blind" = some
        (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) j lb) ∧
      VEnv.get V' "r" = some rw ∧ SameUpToActive st st'
  have hmain : Midfall.Yul.WpTac.AllRuns funs V st
      [Stmt.forLoop
        [Stmt.letDecl ["l_i_cptr_end"] (some (Expr.builtin Op.add
          [Expr.lit (Literal.number D), Expr.lit (Literal.number (m * 32))]))]
        (Expr.builtin Op.lt [Expr.var "l_i_cptr", Expr.var "l_i_cptr_end"])
        [Stmt.assign ["l_i_cptr"] (Expr.builtin Op.add
          [Expr.var "l_i_cptr", Expr.lit (Literal.number 32)])]
        [Stmt.assign ["l_blind"] (Expr.builtin Op.addmod
          [Expr.var "l_blind", Expr.builtin Op.mload [Expr.var "l_i_cptr"], Expr.var "r"])]] Q := by
    refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
      (Bopen_sound c g) (Cnone_sound _) (n := 20) Inv ?hinit ?hstep
    · -- init: 'l_i_cptr_end := D + 32 m'
      refine ⟨rfl, ⟨?_⟩⟩
      show Inv (["l_i_cptr_end"].zip
          [BitVec.ofNat 256 D + BitVec.ofNat 256 (m * 32)] ++ V) st
      have hzip : (["l_i_cptr_end"].zip
          [BitVec.ofNat 256 D + BitVec.ofNat 256 (m * 32)]) ++ V =
          (("l_i_cptr_end", BitVec.ofNat 256 D + BitVec.ofNat 256 (m * 32)) :: V) := rfl
      rw [hzip]
      rw [show BitVec.ofNat 256 D + BitVec.ofNat 256 (m * 32) =
          BitVec.ofNat 256 (D + 32 * m) by
        rw [← BitVec.ofNat_add]
        congr 1
        omega]
      refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- the environment
        change ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) :: V =
          ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
            VEnv.set (VEnv.set V "l_blind" lb) "l_i_cptr" (BitVec.ofNat 256 (D + 64))
        rw [venv_set_eq_self hlb, venv_set_eq_self hlic]
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr_end")
          (y := "l_i_cptr") (v := BitVec.ofNat 256 (D + 32 * m)) (by decide)]
        exact hlic
      · rfl
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr_end")
          (y := "l_blind") (v := BitVec.ofNat 256 (D + 32 * m)) (by decide)]
        exact hlb
      · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr_end")
          (y := "r") (v := BitVec.ofNat 256 (D + 32 * m)) (by decide)]
        exact hrw
      · exact ⟨st.activeWords, rfl⟩
    · -- one iteration
      intro Vi sti hInv
      simp only [Inv] at hInv
      obtain ⟨j, hj, hV, hlicj, hliej, hlbj, hrj, aw, hst⟩ := hInv
      subst hV
      subst hst
      unfold wpIter
      simp only [wpE, wpA, hlicj, hliej]
      refine ⟨?_, ?_⟩
      · -- guard false: j = m - 2
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 (D + 64 + 32 * j)).ult
            (BitVec.ofNat 256 (D + 32 * m))) = (0 : U256) := hguard
        have hge : D + 32 * m ≤ D + 64 + 32 * j :=
          LoopRule.lt_guard_false (by omega) hD h0
        have hm2 : m - 2 + 2 = m := Nat.sub_add_cancel hm
        have hjk : j = m - 2 := by
          have hle2 : m - 2 ≤ j := by omega
          exact Nat.le_antisymm hj hle2
        refine ⟨?allRuns⟩
        intro V' st' o hrun
        cases hrun with
        | seqNil =>
            subst hjk
            refine ⟨rfl, ⟨aw, rfl⟩, lb, rw, hlb, hrw, ?_⟩
            rw [restore_cons_length (D := Bridge.Dialect c g) (V := V)
              (W := (VEnv.set V "l_blind"
                (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) (m - 2) lb)).set
                "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * (m - 2))))
              (y := "l_i_cptr_end") (b := BitVec.ofNat 256 (D + 32 * m)) (by
                simp only [venv_set_length (D := Bridge.Dialect c g)])]
            have hmm : 32 * (m - 2) + 64 = 32 * m := by
              have h1 : m - 2 + 2 = m := Nat.sub_add_cancel hm
              calc 32 * (m - 2) + 64 = 32 * (m - 2) + 32 * 2 := by norm_num
                _ = 32 * ((m - 2) + 2) := by ring
                _ = 32 * m := by rw [h1]
            have hv : D + 64 + 32 * (m - 2) = D + 32 * m := by omega
            rw [hv]
      · -- guard true: j < m - 2, one mload and one addmod
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 (D + 64 + 32 * j)).ult
            (BitVec.ofNat 256 (D + 32 * m))) ≠ (0 : U256) := hguard
        have hm2 : m - 2 + 2 = m := Nat.sub_add_cancel hm
        have hlt : j < m - 2 := by
          have := LoopRule.lt_guard_true (i := D + 64 + 32 * j)
            (n := D + 32 * m) (by omega) hD h0
          omega
        simp only [wpS, wpSS, wpE, wpA, Bopen, stepOp, bin, ter, hlicj, hlbj, hrj]
        have hDj : D + 64 + 32 * j < 2 ^ 256 := by omega
        rw [ofNat_toNat hDj]
        set w0 : U256 := wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) j lb with hw0
        set v : U256 := if rw = 0 then 0 else BitVec.ofNat 256
          ((BitVec.toNat w0 + BitVec.toNat (loadWord st.memory (D + 64 + 32 * j))) %
            BitVec.toNat rw) with hv
        have hv' : v = wAddmodAt w0 (loadWord st.memory (D + 64 + 32 * j)) rw := by
          rw [hv]; rfl
        set Venv : VEnv (Bridge.Dialect c g) :=
          ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
            (VEnv.set V "l_blind" w0).set "l_i_cptr"
              (BitVec.ofNat 256 (D + 64 + 32 * j)) with hVenv
        refine ⟨rfl, ?_⟩
        have hsm : VEnv.setMany Venv ["l_blind"] [v] = VEnv.set Venv "l_blind" v := rfl
        rw [hsm, restore_set_same (V := Venv) (x := "l_blind") (a := v)]
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := Venv) (x := "l_blind")
          (y := "l_i_cptr") (v := v) (by decide)]
        rw [show VEnv.get Venv "l_i_cptr" =
            some (BitVec.ofNat 256 (D + 64 + 32 * j)) from hlicj]
        dsimp only
        refine ⟨rfl, ?_⟩
        have hsm2 : VEnv.setMany (VEnv.set Venv "l_blind" v) ["l_i_cptr"]
            [BitVec.ofNat 256 (D + 64 + 32 * j) + litValue (Literal.number 32)] =
            VEnv.set (VEnv.set Venv "l_blind" v) "l_i_cptr"
              (BitVec.ofNat 256 (D + 64 + 32 * j) + litValue (Literal.number 32)) := rfl
        rw [hsm2, restore_set_same (V := VEnv.set Venv "l_blind" v) (x := "l_i_cptr")]
        have hmp' : BitVec.ofNat 256 (D + 64 + 32 * j) + litValue (Literal.number 32) =
            BitVec.ofNat 256 (D + 64 + 32 * (j + 1)) := by
          rw [show litValue (Literal.number 32) = BitVec.ofNat 256 32 from rfl,
            ← BitVec.ofNat_add]
          congr 1
        rw [hmp']
        simp only [Inv]
        refine ⟨j + 1, Nat.succ_le_of_lt hlt, ?eq, ?g1, ?g2, ?g3, ?g4, ?state⟩
        · -- the environment equation: push the two in-place updates through the loop cons
          rw [hVenv, lblind_env_step (V := V)
            (e := BitVec.ofNat 256 (D + 32 * m)) (w := w0) (w' := v)
            (mp := BitVec.ofNat 256 (D + 64 + 32 * j))
            (mp' := BitVec.ofNat 256 (D + 64 + 32 * (j + 1))),
            hv', hw0]
          rfl
        · -- l_i_cptr read back
          rw [venv_get_set_same (D := Bridge.Dialect c g)
            (V := VEnv.set (("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
              "l_blind" v)
            (x := "l_i_cptr") (v := BitVec.ofNat 256 (D + 64 + 32 * j))
            (w := BitVec.ofNat 256 (D + 64 + 32 * (j + 1))) (by
              rw [venv_get_set_ne (D := Bridge.Dialect c g)
                (V := ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
                  (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
                (x := "l_blind") (y := "l_i_cptr")
                (v := v) (by decide)]
              exact hlicj)]
        · -- l_i_cptr_end read back (the loop's own binding, at the cons head)
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
              "l_blind" v)
            (x := "l_i_cptr") (y := "l_i_cptr_end") (v := BitVec.ofNat 256 (D + 64 + 32 * (j + 1)))
            (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
            (x := "l_blind") (y := "l_i_cptr_end") (v := v) (by decide)]
          rfl
        · -- l_blind read back
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
              "l_blind" v)
            (x := "l_i_cptr") (y := "l_blind") (v := BitVec.ofNat 256 (D + 64 + 32 * (j + 1)))
            (by decide)]
          rw [venv_get_set_same hlbj, hv', hw0]
          rfl
        · -- r read back
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
              "l_blind" v)
            (x := "l_i_cptr") (y := "r") (v := BitVec.ofNat 256 (D + 64 + 32 * (j + 1)))
            (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := ("l_i_cptr_end", BitVec.ofNat 256 (D + 32 * m)) ::
              (VEnv.set V "l_blind" w0).set "l_i_cptr" (BitVec.ofNat 256 (D + 64 + 32 * j)))
            (x := "l_blind") (y := "r") (v := v) (by decide)]
          exact hrj
        · -- SameUpToActive
          exact ⟨_, rfl⟩
  intro V' st' o hrun
  exact hmain V' st' o hrun

/-! ## 9. PREMISE GAPS HIT BY THIS TRANCHE (exact PG_* notes; no hypothesis added to any row)

  **PG-LAG-HEARTBEAT (T3.9.b, measured; RESOLVED).** The two-statement denominator body needs fuel
  13 for the nested `addmod(x, sub(r, pow), r)` (the expression depth is 12, and fuel 12 makes
  `wpA` hit `0`, which is `False`); at 13 the `simp only [wpS, wpSS, wpE, wpA, Bopen, stepOp, bin,
  ter, …]` unfolding of the body TOGETHER WITH the post exceeds the default 200000 heartbeats. The
  fix is the card's semantic `allRuns_loop` route (the inversion helpers of section 7 and the
  `exec_denoms_body_inv` block inversion are landed for it), not `maxHeartbeats`; that route is now
  the proof of `lag_denoms_loop`. The whole `l_blind` loop (T3.9.d), the second pass (T3.9.c), the
  instance loop (T3.9.e) and all of T3.9.a are PROVED.

  **PG-LAG-AGREES (T3.9.g, D-GATE2 correction).** The corrected statement is the evidence's
  `lag_agrees` (:595-607) with `hW`'s last-but-two argument changed from
  `frWord (ω⁻¹ ^ (numNegLagranges - 1))` to `frWord (ω⁻¹ ^ numNegLagranges)`:

      theorem lag_agrees (R) (hR : ValidV3 R) (hm : 2 ≤ R.pv.numNegLagranges)
        (s2 : SnapAlgebra p G₁) (l : SnapLagrange p G₁)
        (hl : snapshotLagrangeStep (G₁ := G₁) R.vk s2 = .ok l)
        (hxn : s2.alg.xn = s2.alg.x ^ (2 ^ R.pv.k)) (inst : Array (Fr p)) (W : LagWords)
        (hW : LagRel (BitVec.ofNat 256 p) (frWord s2.alg.x) (frWord R.vk.domain.omega)
          (frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges))
          (frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹) R.pv.k R.pv.numInstances
          R.pv.numNegLagranges (fun j => frWord (inst.getD j 0)) W) :
        W.xn = frWord s2.alg.xn ∧ W.lLast = frWord l.lagrange.lLast ∧
        W.lBlind = frWord l.lagrange.lBlind ∧ W.l0 = frWord l.lagrange.l0 ∧
        ∀ e, l.instanceEval = some e → W.instEval = frWord e

  IT IS NOT LANDED HERE, and no sorried copy is added: it has no proved falsifier yet (W12), and the
  proof rests on three things absent from the tree:
  (a) **PG-BATCHINVERT** - `batchInvert` (`Halo2/Exec/Arith.lean:99`) has KATs only, no spec. The
      proof needs: `batchInvert xs` returns entrywise inverses on a nonzero entry, zero at a zero
      entry, and `allInv = (∏ xs)⁻¹`. `LagRel`'s `inv` is a CHOICE of inverses; uniqueness in the
      field is what turns the batch result into it.
  (b) **PG-LIRANGE** - `lIRange`'s value (`Halo2/Exec/Domain.lean:245`) is
      `rotateOmega ((x - ω^r)⁻¹ * ((xn - 1) * barycentricWeight)) r`; matching `LagRel`'s
      `L i = (xn - 1) * n⁻¹ * inv i * ω^i` needs `barycentricWeight = n⁻¹` and
      `rotateOmega v r = v * ω^r`, plus the `x ∉ domain` side condition (the KAT at :356-359 shows
      the zero-entry degradation).
  (c) **PG-TRIPLE-RANGE** - `lagrangeTriple`'s `lLast = lEvals[0]`, `lBlind = Σ drop 1 take bf`,
      `l0 = lEvals[bf+1]` with `bf = numNegLagranges - 2` (from `EnvAgrees.negLagranges`), is
      `L 0 / Σ_{i< m-2} L(2+i) / L m` at `w0 = ω⁻ᴸ`; this is the index arithmetic that the
      `-1` exponent got wrong.
  (d) **PG-OMEGAINV-SLOT** - `PayloadAgrees.omegaInvToL` gives `ω⁻¹ ^ rotationLast.natAbs`; the
      corrected `hW` uses `ω⁻¹ ^ numNegLagranges`. The equality of those two exponents
      (`numNegLagranges = |rotationLast|`) is not a `ValidV3` clause; D-GATE2 corrects the
      *consumer*, so the caller must supply it, exactly as `hxn` is supplied.

  **PG-SNAPSHOT-LAG** - `snapshotLagrangeStep` (`Snapshot.lean:230`) returns `Except Fault`; the
  `.ok` success under `ValidV3` (the `blindingFactors`/`lIRange` length check at `Verifier.lean:252`)
  is not derivable from the validity bundle and is a hypothesis of T3.9.g's statement (`hl`), as
  the evidence has it.

  **PG-POWVARTIME** - `powVartime x (2^k - 1) = x^(2^k - 1)` for the `x^n - 1` numerator (used by
  the `LagRel` `L` and by the VK `xn` slot). The tree has `powVartime` (`Arith.lean`) but no such
  equation at a symbolic exponent; `hxn : s2.alg.xn = x^(2^k)` is supplied, so the proof needs the
  `xn - 1` step only, via `(x^(2^k) - 1)`.

  **PG-LOADWORD-BYTES / PG-CDWORD** - `loadWord` of `bytesAt` = `payloadWord` (the VK payload read
  bridge, shared with A3/VkClean) and `cdWord cd a = calldataload`-of-the-instance-word (the
  `lag_instance_loop` T3.9.e read). Neither is needed by a/b/d; they are T3.9.e/g's.

  **PG-FITS** - the `2^256` fits the loops need: `D + 32*(n+m) < 2^256` for the denominator window
  (`hD`, a hypothesis of T3.9.b, exactly as the evidence states it), `D + 32*m < 2^256` for the
  blind window (`hD`, T3.9.d), and the scratch-window fit for `batch_invert` (`hs`) which is
  HLP.1.b's, not this tranche's. `ValidV3` does not supply them: they are `PG-LAG-FITS`, caller
  side. The card's Stop condition (the fits come from `memory.map.WellFormed`) is NOT closed.

  **PG-BATCHINVERT-SUMMARY (A5)** - `batch_invert_summary` (`GeneratorRows.lean:317`) is absent
  from the tree; T3.9.h (the poisoned half) and the row's `success = 1` arm need it, and A5 is
  ordered AFTER A4. The loop work above does not depend on it.
-/

/-! ## 10. T3.9.e: THE INSTANCE POLYNOMIAL (semantic route additions) -/

theorem restore_two_cons_length {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    {y z : Ident} {b c : D.Value} (h : W.length = V.length) :
    restore V ((y, b) :: (z, c) :: W) = W := by
  simp only [restore, List.length_cons, h]
  have h2 : List.length V + 1 + 1 - List.length V = 2 := by omega
  rw [h2]
  rfl

theorem instance_env_step {V : VEnv (Bridge.Dialect c g)} {e mp lp v mp' lp' : U256} :
    VEnv.set (VEnv.set (VEnv.set (("instance_cptr_end", e) ::
        ("instance_cptr", mp) :: V) "instance_eval" v) "instance_cptr" mp') "l_i_cptr" lp' =
      ("instance_cptr_end", e) :: ("instance_cptr", mp') ::
        (VEnv.set V "instance_eval" v).set "l_i_cptr" lp' := by
  simp only [VEnv.set, venv_set_set,
    if_neg (by decide : ¬ (("instance_cptr_end" : String) = "instance_eval")),
    if_neg (by decide : ¬ (("instance_cptr" : String) = "instance_eval")),
    if_neg (by decide : ¬ (("instance_cptr_end" : String) = "instance_cptr")),
    if_neg (by decide : ¬ (("instance_cptr_end" : String) = "l_i_cptr")),
    if_neg (by decide : ¬ (("instance_cptr" : String) = "l_i_cptr")), ite_true]

/-! ## 8b. T3.9.e: THE INSTANCE POLYNOMIAL -/

/-- Statement 18 of the inner scope: the public-instance walk. PROVED by kernel reduction. -/
theorem lag_instance_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 18 1 =
      [GenAst.yfor
        [ GenAst.ylet "instance_cptr" (Blocks.VkLoading.vkSite "INSTANCE_CPTR" consts)
        , GenAst.ylet "instance_cptr_end" (GenAst.yop EVM.Op.add
            [GenAst.yvar "instance_cptr", GenAst.ylit (n * 32)]) ]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "instance_cptr", GenAst.yvar "instance_cptr_end"])
        [ GenAst.yset "instance_cptr" (GenAst.yop EVM.Op.add
            [GenAst.yvar "instance_cptr", GenAst.ylit 0x20])
        , GenAst.yset "l_i_cptr" (GenAst.yop EVM.Op.add
            [GenAst.yvar "l_i_cptr", GenAst.ylit 0x20]) ]
        [GenAst.yset "instance_eval" (GenAst.yop EVM.Op.addmod
          [GenAst.yvar "instance_eval",
            GenAst.yop EVM.Op.mulmod
              [GenAst.yop EVM.Op.mload [GenAst.yvar "l_i_cptr"],
                GenAst.yop EVM.Op.calldataload [GenAst.yvar "instance_cptr"],
                Blocks.VkLoading.vkSite "r" consts],
            Blocks.VkLoading.vkSite "r" consts])]] := by
  kernel_rfl


/-! ## 7b. INVERSIONS FOR THE INSTANCE LOOP (T3.9.e) -/

theorem list_length_one {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons b t => simp at h

/-- A pure comparison cannot halt: `stepOp lt` is always `.ok`. -/
theorem eval_lt_halt_false {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.lt [Expr.var x, Expr.var y]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := Op.lt)
    (fun a b st r hr => by
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    h

theorem eval_lt_vars_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.lt [Expr.var x, Expr.var y]) (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = b2w (xv.ult yv) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil htail =>
          cases hnil with
          | argsNil =>
              obtain ⟨hyv, rfl⟩ := eval_var_inv htail
              obtain ⟨hxv, rfl⟩ := eval_var_inv hhead
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem eval_mload_var_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mload [Expr.var x]) (.vals [cv] st')) :
    ∃ p, VEnv.get V x = some p ∧ cv = loadWord st.memory p.toNat ∧
      st' = touchMemory st p.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hhead =>
      cases hnil with
      | argsNil =>
          obtain ⟨hp, rfl⟩ := eval_var_inv hhead
          simp only [builtinWithExternal, stepOp, rd1] at hbi
          cases hbi
          exact ⟨_, hp, rfl, rfl⟩

theorem eval_calldataload_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.calldataload [Expr.var x]) (.vals [cv] st')) :
    ∃ p, VEnv.get V x = some p ∧ cv = wordFrom st.env.calldata p.toNat ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hhead =>
      cases hnil with
      | argsNil =>
          obtain ⟨hp, rfl⟩ := eval_var_inv hhead
          simp only [builtinWithExternal, stepOp, rd1] at hbi
          cases hbi
          exact ⟨_, hp, rfl, rfl⟩

theorem eval_mulmod_mload_cdl_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {mv rv : U256} {st' : EvmState}
    (hrv : VEnv.get V "r" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
          Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"])
      (.vals [mv] st')) :
    ∃ mp cp, VEnv.get V "l_i_cptr" = some mp ∧
      VEnv.get V "instance_cptr" = some cp ∧
      mv = wMulmodAt (loadWord st.memory mp.toNat) (wordFrom st.env.calldata cp.toNat) rv ∧
      st' = touchMemory st mp.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hmload =>
      cases hrest with
      | argsCons hrest2 hcdl =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hv, rfl⟩ := eval_var_inv hr
                  rw [hrv] at hv
                  injection hv with hvr
                  subst hvr
                  obtain ⟨hcp, hget, hcv, hst⟩ := eval_calldataload_var_inv hcdl
                  subst hst
                  obtain ⟨hmp, hmpget, hmv, htouch⟩ := eval_mload_var_inv hmload
                  simp only [builtinWithExternal, stepOp, ter, hcv, hmv] at hbi
                  cases hbi
                  exact ⟨_, _, hmpget, hget, rfl, htouch⟩

theorem eval_addmod_instance_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.addmod
        [Expr.var "instance_eval",
          Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
              Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
          Expr.var "r"]) (.vals [cv] st')) :
    ∃ iev mv rv mp cp, VEnv.get V "instance_eval" = some iev ∧
      VEnv.get V "l_i_cptr" = some mp ∧ VEnv.get V "instance_cptr" = some cp ∧
      VEnv.get V "r" = some rv ∧
      mv = wMulmodAt (loadWord st.memory mp.toNat) (wordFrom st.env.calldata cp.toNat) rv ∧
      cv = wAddmodAt iev mv rv ∧ st' = touchMemory st mp.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hrest2 hmul =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hrv, rfl⟩ := eval_var_inv hr
                  obtain ⟨mp, cp, hmm⟩ := eval_mulmod_mload_cdl_inv hrv hmul
                  obtain ⟨hmp, hcp, hmv, hstm⟩ := hmm
                  subst hstm
                  obtain ⟨hiev, rfl⟩ := eval_var_inv hhead
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨_, _, _, _, _, hiev, hmp, hcp, hrv, hmv, rfl, rfl⟩

theorem exec_exprStmt_inv {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {e : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.exprStmt e) V' st' .normal) :
    V' = V ∧ ∃ st1, EvalExpr (Bridge.Dialect c g) funs V st e (.vals [] st1) ∧ st' = st1 := by
  cases h with
  | exprStmt he => exact ⟨rfl, _, he, rfl⟩

theorem exec_assign_inv {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {x : String} {e : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.assign [x] e) V' st' .normal) :
    ∃ v, EvalExpr (Bridge.Dialect c g) funs V st e (.vals [v] st') ∧ V' = VEnv.set V x v := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      exact ⟨v, he, rfl⟩

theorem exec_block_inv {funs : FunEnv (Bridge.Dialect c g)} {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {body : Block EVM.Op} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.block body) V' st' o) :
    ∃ Vb stb, ExecStmts (Bridge.Dialect c g) (hoist (Bridge.Dialect c g) body :: funs)
      V st body Vb stb o ∧ V' = restore V Vb ∧ st' = stb := by
  cases h with
  | block hb => exact ⟨_, _, hb, rfl, rfl⟩

theorem eval_add_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x : String} {k : Nat} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number k)]) (.vals [cv] st')) :
    ∃ a, VEnv.get V x = some a ∧ cv = a + BitVec.ofNat 256 k ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hhead =>
      cases hrest with
      | argsCons hnil hlit =>
          cases hnil with
          | argsNil =>
              obtain ⟨hk, rfl⟩ := eval_lit_inv hlit
              obtain ⟨ha, rfl⟩ := eval_var_inv hhead
              simp only [builtinWithExternal, stepOp, bin, hk] at hbi
              cases hbi
              exact ⟨_, ha, rfl, rfl⟩

/-- A restore is the identity from any environment of the outer length: the set-chain form. -/
theorem restore_set_any {D : YulSemantics.Dialect} [DecidableEq D.Value] {V W : VEnv D}
    (h : W.length = V.length) (x : Ident) (a : D.Value) :
    restore V (VEnv.set W x a) = VEnv.set W x a := by
  simp [restore, venv_set_length, h]

/-- A block whose single statement is an assignment: its value, its state, and the environment it
leaves. The restoration is the identity because `VEnv.set` preserves length. -/
theorem exec_one_assign_block_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String} {e : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.block [Stmt.assign [x] e]) V' st' .normal) :
    ∃ v st1,
      EvalExpr (Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [Stmt.assign [x] e] :: funs)
        V st e (.vals [v] st1) ∧ V' = VEnv.set V x v ∧ st' = st1 := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons hassign hrest =>
          cases hrest with
          | seqNil =>
              obtain ⟨v, he, hset⟩ := exec_assign_inv hassign
              exact ⟨v, _, he, by rw [hset, restore_set_same (D := Bridge.Dialect c g)], rfl⟩
      | seqStop hassign hne => cases hne rfl

theorem exec_two_add_assigns_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String}
    (hyx : y ≠ x)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block
        [Stmt.assign [x] (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number 32)]),
         Stmt.assign [y] (Expr.builtin Op.add [Expr.var y, Expr.lit (Literal.number 32)])])
      V' st' .normal) :
    ∃ a b, VEnv.get V x = some a ∧ VEnv.get V y = some b ∧
      V' = VEnv.set (VEnv.set V x (a + BitVec.ofNat 256 32)) y (b + BitVec.ofNat 256 32) ∧
      st' = st := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons h1 hrest =>
          cases hrest with
          | seqCons h2 hnil =>
              cases hnil with
              | seqNil =>
                  obtain ⟨v1, he1, hV1⟩ := exec_assign_inv h1
                  obtain ⟨a, ha, hv1, hst1⟩ := eval_add_var_lit_inv he1
                  subst hv1
                  subst hst1
                  subst hV1
                  obtain ⟨v2, he2, hV2⟩ := exec_assign_inv h2
                  obtain ⟨b, hbV, hv2, hst2⟩ := eval_add_var_lit_inv he2
                  rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := x) (y := y)
                    (v := a + BitVec.ofNat 256 32) hyx] at hbV
                  subst hv2
                  subst hst2
                  refine ⟨a, b, ha, hbV, ?_, rfl⟩
                  rw [hV2]
                  exact restore_set_any (D := Bridge.Dialect c g)
                    (V := V) (W := VEnv.set V x (a + BitVec.ofNat 256 32))
                    (by rw [venv_set_length (D := Bridge.Dialect c g)]) y _
          | seqStop h2 hne => cases hne rfl
      | seqStop h1 hne => cases hne rfl



/-! ### 7c. TOTALLITY OF THE INSTANCE EXPRESSIONS (no halt, so the body/post end normally) -/

theorem eval_args_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {es : List (Expr EVM.Op)} {st' : EvmState}
    (hne : ∀ e ∈ es, ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False)
    (h : EvalArgs (Bridge.Dialect c g) funs V st es (.halt st')) : False := by
  induction es generalizing st with
  | nil => cases h
  | cons e rest ih =>
      cases h with
      | argsRestHalt h' =>
          exact ih (fun e' he' => hne e' (List.mem_cons_of_mem _ he')) h'
      | argsHeadHalt _ h' => exact hne e (by simp) _ _ h'

theorem eval_mload_var_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mload [Expr.var x]) (.halt st')) : False := by
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, rd1] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs =>
      exact Midfall.LoweringV2.Blocks.TraceReturn.trArgs1_halt_inv hargs
        (fun _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)

theorem eval_calldataload_var_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.calldataload [Expr.var x]) (.halt st')) : False := by
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, rd1] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs =>
      exact Midfall.LoweringV2.Blocks.TraceReturn.trArgs1_halt_inv hargs
        (fun _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)

theorem eval_mulmod_mload_cdl_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
          Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"])
      (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
      Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact eval_mload_var_halt_false hh
    · exact eval_calldataload_var_halt_false hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs =>
      exact eval_args_halt_false hne hargs

theorem eval_addmod_instance_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.addmod
        [Expr.var "instance_eval", Expr.builtin Op.mulmod
          [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
            Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
          Expr.var "r"]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "instance_eval", Expr.builtin Op.mulmod
      [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
        Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
      Expr.var "r"],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact eval_mulmod_mload_cdl_halt_false hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs =>
      exact eval_args_halt_false hne hargs

theorem eval_add_var_lit_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x : String} {k : Nat} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number k)]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var x, Expr.lit (Literal.number k)],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, bin] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs =>
      exact eval_args_halt_false hne hargs

theorem exec_one_total_assign_block_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String} {e : Expr EVM.Op}
    {o : Outcome}
    (hne : ∀ st0 st1, EvalExpr (Bridge.Dialect c g)
      (hoist (Bridge.Dialect c g) [Stmt.assign [x] e] :: funs) V st0 e (.halt st1) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.block [Stmt.assign [x] e]) V' st' o) :
    o = .normal ∧ ∃ v st1,
      EvalExpr (Bridge.Dialect c g) (hoist (Bridge.Dialect c g) [Stmt.assign [x] e] :: funs)
        V st e (.vals [v] st1) ∧ V' = VEnv.set V x v ∧ st' = st1 := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons hassign hrest =>
          cases hrest with
          | seqNil =>
              obtain ⟨v, he, hset⟩ := exec_assign_inv hassign
              exact ⟨rfl, v, _, he, by rw [hset, restore_set_same (D := Bridge.Dialect c g)], rfl⟩
      | seqStop hassign hne' =>
          cases hassign with
          | assignVal _ _ => cases hne' rfl
          | assignHalt he => exact (hne _ _ he).elim

theorem exec_two_total_add_assigns_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String} {o : Outcome}
    (hyx : y ≠ x)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block
        [Stmt.assign [x] (Expr.builtin Op.add [Expr.var x, Expr.lit (Literal.number 32)]),
         Stmt.assign [y] (Expr.builtin Op.add [Expr.var y, Expr.lit (Literal.number 32)])])
      V' st' o) :
    o = .normal ∧ ∃ a b, VEnv.get V x = some a ∧ VEnv.get V y = some b ∧
      V' = VEnv.set (VEnv.set V x (a + BitVec.ofNat 256 32)) y (b + BitVec.ofNat 256 32) ∧
      st' = st := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons h1 hrest =>
          cases hrest with
          | seqCons h2 hnil =>
              cases hnil with
              | seqNil =>
                  obtain ⟨v1, he1, hV1⟩ := exec_assign_inv h1
                  obtain ⟨a, ha, hv1, hst1⟩ := eval_add_var_lit_inv he1
                  subst hv1; subst hst1; subst hV1
                  obtain ⟨v2, he2, hV2⟩ := exec_assign_inv h2
                  obtain ⟨b, hbV, hv2, hst2⟩ := eval_add_var_lit_inv he2
                  rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := x) (y := y)
                    (v := a + BitVec.ofNat 256 32) hyx] at hbV
                  subst hv2; subst hst2
                  refine ⟨rfl, a, b, ha, hbV, ?_, rfl⟩
                  rw [hV2]
                  exact restore_set_any (D := Bridge.Dialect c g)
                    (V := V) (W := VEnv.set V x (a + BitVec.ofNat 256 32))
                    (by rw [venv_set_length (D := Bridge.Dialect c g)]) y _
          | seqStop h2 hne' =>
              cases h2 with
              | assignVal _ _ => cases hne' rfl
              | assignHalt he => exact (eval_add_var_lit_halt_false he).elim
      | seqStop h1 hne' =>
          cases h1 with
          | assignVal _ _ => cases hne' rfl
          | assignHalt he => exact (eval_add_var_lit_halt_false he).elim

/-- The inner `VEnv` algebra of one instance step: the body's `instance_eval` update and the post
block's `l_i_cptr` update collapse past each other. -/
theorem instance_set_flat {V : VEnv (Bridge.Dialect c g)} {w w' lp lp' : U256} :
    VEnv.set (VEnv.set (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)
        "instance_eval" w') "l_i_cptr" lp' =
      VEnv.set (VEnv.set V "instance_eval" w') "l_i_cptr" lp' := by
  rw [venv_set_comm (D := Bridge.Dialect c g) (V := VEnv.set V "instance_eval" w)
      (x := "l_i_cptr") (y := "instance_eval") (by decide),
    venv_set_set (D := Bridge.Dialect c g), venv_set_set (D := Bridge.Dialect c g)]

/-- The instance loop's environment after one iteration, in the invariant's normal form: both
in-place updates collapse past the loop's two bindings. -/
theorem instance_env_flat {V : VEnv (Bridge.Dialect c g)} {e w w' mp lp mp' lp' : U256} :
    VEnv.set (VEnv.set (VEnv.set (("instance_cptr_end", e) ::
        ("instance_cptr", mp) ::
        (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp))
      "instance_eval" w') "instance_cptr" mp') "l_i_cptr" lp' =
      ("instance_cptr_end", e) :: ("instance_cptr", mp') ::
        VEnv.set (VEnv.set V "instance_eval" w') "l_i_cptr" lp' := by
  have h1 : VEnv.set (("instance_cptr_end", e) ::
      ("instance_cptr", mp) ::
      (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w' =
      ("instance_cptr_end", e) ::
        VEnv.set (("instance_cptr", mp) ::
          (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w' := rfl
  have h2 : VEnv.set (("instance_cptr_end", e) ::
      VEnv.set (("instance_cptr", mp) ::
        (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w')
      "instance_cptr" mp' =
      ("instance_cptr_end", e) ::
        VEnv.set (VEnv.set (("instance_cptr", mp) ::
          (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w')
          "instance_cptr" mp' := rfl
  have h3 : VEnv.set (("instance_cptr_end", e) ::
      VEnv.set (VEnv.set (("instance_cptr", mp) ::
        (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w')
        "instance_cptr" mp') "l_i_cptr" lp' =
      ("instance_cptr_end", e) ::
        VEnv.set (VEnv.set (VEnv.set (("instance_cptr", mp) ::
          (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w')
          "instance_cptr" mp') "l_i_cptr" lp' := rfl
  have h4 : VEnv.set (VEnv.set (VEnv.set (("instance_cptr", mp) ::
        (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)) "instance_eval" w')
        "instance_cptr" mp') "l_i_cptr" lp' =
      ("instance_cptr", mp') ::
        VEnv.set (VEnv.set (VEnv.set (VEnv.set V "instance_eval" w) "l_i_cptr" lp)
          "instance_eval" w') "l_i_cptr" lp' := rfl
  rw [h1, h2, h3, h4, instance_set_flat]

theorem lag_instance_loop (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aI Lc : Nat) (cd : Bytes)
    (hI : consts.lookup "INSTANCE_CPTR" = some aI)
    (hIb : aI + 32 * n < 2 ^ 256) (hLb : Lc + 32 * n < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 18 1)
      (fun V st => st.env.calldata = cd.data.toList ∧
        VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 Lc) ∧
        VEnv.get V "instance_eval" = some 0 ∧ (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ SameUpToActive st st' ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "instance_eval"
              (wSum rw (fun j => wMulmodAt (loadWord st.memory (Lc + 32 * j))
                (cdWord cd (aI + 32 * j)) rw) n 0))
            "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * n))) := by
  rw [lag_instance_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    Blocks.VkLoading.vkSite, hr, hI]
  intro V st hpre
  obtain ⟨hcd, hlic, hie0, hrsome⟩ := hpre
  obtain ⟨rw, hrw⟩ := QuotientRows.isSome_elim hrsome
  let P : Nat → U256 := fun j => wMulmodAt (loadWord st.memory (Lc + 32 * j))
    (cdWord cd (aI + 32 * j)) rw
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧ SameUpToActive st st' ∧
      ∃ rw, VEnv.get V "r" = some rw ∧
        V' = VEnv.set (VEnv.set V "instance_eval"
            (wSum rw (fun j => wMulmodAt (loadWord st.memory (Lc + 32 * j))
              (cdWord cd (aI + 32 * j)) rw) n 0))
          "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * n))
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop
      [ Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI)))
      , Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
          [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))])) ]
      (Expr.builtin Op.lt [Expr.var "instance_cptr", Expr.var "instance_cptr_end"])
      [ Stmt.assign ["instance_cptr"] (Expr.builtin Op.add
          [Expr.var "instance_cptr", Expr.lit (Literal.number 32)])
      , Stmt.assign ["l_i_cptr"] (Expr.builtin Op.add
          [Expr.var "l_i_cptr", Expr.lit (Literal.number 32)]) ]
      [Stmt.assign ["instance_eval"] (Expr.builtin Op.addmod
        [Expr.var "instance_eval", Expr.builtin Op.mulmod
          [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
            Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
          Expr.var "r"])]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j, j ≤ n ∧
      V' = ("instance_cptr_end", BitVec.ofNat 256 (aI + 32 * n)) ::
        ("instance_cptr", BitVec.ofNat 256 (aI + 32 * j)) ::
        VEnv.set (VEnv.set V "instance_eval" (wSum rw P j 0))
          "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * j)) ∧
      VEnv.get V' "instance_cptr" = some (BitVec.ofNat 256 (aI + 32 * j)) ∧
      VEnv.get V' "instance_cptr_end" = some (BitVec.ofNat 256 (aI + 32 * n)) ∧
      VEnv.get V' "l_i_cptr" = some (BitVec.ofNat 256 (Lc + 32 * j)) ∧
      VEnv.get V' "instance_eval" = some (wSum rw P j 0) ∧
      VEnv.get V' "r" = some rw ∧ SameUpToActive st st'
  let Qloop : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun Vend stend o => Q (restore V Vend) stend o
  have hinit : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) 14
      (hoist (Bridge.Dialect c g)
        [Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI))),
         Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
          [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))]))] ::
        funs)
      V st
      [Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI))),
       Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
        [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))]))]
      (fun Vi sti oi =>
        match oi with
        | .normal => Inv Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False) := by
    refine ⟨rfl, ⟨⟨rfl, ⟨?_⟩⟩⟩⟩
    show Inv (("instance_cptr_end", BitVec.ofNat 256 aI + BitVec.ofNat 256 (n * 32)) ::
      ("instance_cptr", BitVec.ofNat 256 aI) :: V) st
    rw [show BitVec.ofNat 256 aI + BitVec.ofNat 256 (n * 32) =
        BitVec.ofNat 256 (aI + 32 * n) by
      rw [← BitVec.ofNat_add]
      congr 1
      omega]
    refine ⟨0, Nat.zero_le _, ?eq, ?g1, ?g2, ?g3, ?g4, ?g5, ?state⟩
    · change ("instance_cptr_end", BitVec.ofNat 256 (aI + 32 * n)) ::
          ("instance_cptr", BitVec.ofNat 256 aI) :: V =
        ("instance_cptr_end", BitVec.ofNat 256 (aI + 32 * n)) ::
          ("instance_cptr", BitVec.ofNat 256 aI) ::
          VEnv.set (VEnv.set V "instance_eval" 0) "l_i_cptr" (BitVec.ofNat 256 Lc)
      rw [venv_set_eq_self hie0, venv_set_eq_self hlic]
    · rfl
    · rfl
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g)
        (V := ("instance_cptr", BitVec.ofNat 256 aI) :: V) (x := "instance_cptr_end")
        (y := "l_i_cptr") (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "instance_cptr")
        (y := "l_i_cptr") (v := BitVec.ofNat 256 aI) (by decide)]
      exact hlic
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g)
        (V := ("instance_cptr", BitVec.ofNat 256 aI) :: V) (x := "instance_cptr_end")
        (y := "instance_eval") (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "instance_cptr")
        (y := "instance_eval") (v := BitVec.ofNat 256 aI) (by decide)]
      change VEnv.get V "instance_eval" = some 0
      exact hie0
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g)
        (V := ("instance_cptr", BitVec.ofNat 256 aI) :: V) (x := "instance_cptr_end")
        (y := "r") (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "instance_cptr")
        (y := "r") (v := BitVec.ofNat 256 aI) (by decide)]
      exact hrw
    · exact ⟨st.activeWords, rfl⟩
  have hloop : ∀ Vi sti, Inv Vi sti →
      ∀ V' st' o, ExecLoop (Bridge.Dialect c g)
        (hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI))),
           Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
            [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))]))] :: funs)
        Vi sti
        (Expr.builtin Op.lt [Expr.var "instance_cptr", Expr.var "instance_cptr_end"])
        [ Stmt.assign ["instance_cptr"] (Expr.builtin Op.add
            [Expr.var "instance_cptr", Expr.lit (Literal.number 32)])
        , Stmt.assign ["l_i_cptr"] (Expr.builtin Op.add
            [Expr.var "l_i_cptr", Expr.lit (Literal.number 32)]) ]
        [Stmt.assign ["instance_eval"] (Expr.builtin Op.addmod
          [Expr.var "instance_eval", Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "l_i_cptr"],
              Expr.builtin Op.calldataload [Expr.var "instance_cptr"], Expr.var "r"],
            Expr.var "r"])]
        V' st' o → Qloop V' st' o := by
    refine LoopRule.allRuns_loop (Inv := Inv) (Q := Qloop) ?_
    intro Vi sti hInv
    simp only [Inv] at hInv
    obtain ⟨j, hj, hV, hcpc, hcpe, hlicj, hiej, hrj, aw, hst⟩ := hInv
    refine ⟨?condHalt, ?exit, ?iter⟩
    · intro st1 hc
      exact (eval_lt_halt_false hc).elim
    · intro cv st1 hc hz
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (aI + 32 * j) :=
        Option.some.inj (hxget.symm.trans hcpc)
      have hyv : yv = BitVec.ofNat 256 (aI + 32 * n) :=
        Option.some.inj (hyget.symm.trans hcpe)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (aI + 32 * j)).ult
          (BitVec.ofNat 256 (aI + 32 * n))) = (0 : U256) := by
        rw [← hcv]; exact hz
      have hge : aI + 32 * n ≤ aI + 32 * j :=
        LoopRule.lt_guard_false (by omega) hIb h0
      have hjn : j = n := by
        have hle : n ≤ j := by omega
        exact Nat.le_antisymm hj hle
      change Q (restore V Vi) st1 .normal
      rw [hst1, hV, hjn]
      simp only [Q]
      refine ⟨trivial, ⟨aw, hst⟩, rw, hrw, ?_⟩
      rw [restore_two_cons_length (D := Bridge.Dialect c g) (V := V)
        (W := (VEnv.set V "instance_eval" (wSum rw P n 0)).set
          "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * n)))
        (y := "instance_cptr_end") (z := "instance_cptr")
        (b := BitVec.ofNat 256 (aI + 32 * n)) (c := BitVec.ofNat 256 (aI + 32 * n))
        (by simp only [venv_set_length (D := Bridge.Dialect c g)])]
    · intro cv st1 hc hnz Vb stb ob hbody
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (aI + 32 * j) :=
        Option.some.inj (hxget.symm.trans hcpc)
      have hyv : yv = BitVec.ofNat 256 (aI + 32 * n) :=
        Option.some.inj (hyget.symm.trans hcpe)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (aI + 32 * j)).ult
          (BitVec.ofNat 256 (aI + 32 * n))) ≠ (0 : U256) := by
        rw [← hcv]; exact hnz
      have hlt : j < n := by
        have := LoopRule.lt_guard_true (i := aI + 32 * j) (n := aI + 32 * n) (by omega) hIb h0
        omega
      obtain ⟨hob, v, st1b, heval, hVb, hstb⟩ :=
        exec_one_total_assign_block_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI))),
           Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
            [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))]))] :: funs)
          (hne := fun st0 st1 hh => eval_addmod_instance_halt_false hh) hbody
      subst hob
      obtain ⟨iev, mv, rv, mp, cp, hie, hlicb, hcpcb, hrv, hmv, hcvadd, hsttouch⟩ :=
        eval_addmod_instance_inv heval
      subst hstb
      subst hsttouch
      subst hVb
      intro Vp stp op hpost
      obtain ⟨hop, a, b, hcpcVb, hlicVb, hVp, hstp⟩ :=
        exec_two_total_add_assigns_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["instance_cptr"] (some (Expr.lit (Literal.number aI))),
           Stmt.letDecl ["instance_cptr_end"] (some (Expr.builtin Op.add
            [Expr.var "instance_cptr", Expr.lit (Literal.number (n * 32))]))] :: funs)
          (V := VEnv.set Vi "instance_eval" v) (x := "instance_cptr") (y := "l_i_cptr")
          (by decide) hpost
      subst hop
      subst hstp
      subst hVp
      have hcpcV : VEnv.get Vi "instance_cptr" = some a := by
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := Vi) (x := "instance_eval")
          (y := "instance_cptr") (v := v) (by decide)] at hcpcVb
        exact hcpcVb
      have hlicV : VEnv.get Vi "l_i_cptr" = some b := by
        rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := Vi) (x := "instance_eval")
          (y := "l_i_cptr") (v := v) (by decide)] at hlicVb
        exact hlicVb
      have ha : a = BitVec.ofNat 256 (aI + 32 * j) := Option.some.inj (hcpcV.symm.trans hcpc)
      have hb : b = BitVec.ofNat 256 (Lc + 32 * j) := Option.some.inj (hlicV.symm.trans hlicj)
      subst ha; subst hb
      refine ⟨?_, ?_⟩
      · intro _
        have hmpt : mp.toNat = Lc + 32 * j := by
          have hs : some mp = some (BitVec.ofNat 256 (Lc + 32 * j)) := by
            rw [← hlicb]; exact hlicj
          have h1 : mp = BitVec.ofNat 256 (Lc + 32 * j) := by cases hs; rfl
          rw [h1]; exact ofNat_toNat (by omega)
        have hcpt : cp.toNat = aI + 32 * j := by
          have hs : some cp = some (BitVec.ofNat 256 (aI + 32 * j)) := by
            rw [← hcpcb]; exact hcpc
          have h1 : cp = BitVec.ofNat 256 (aI + 32 * j) := by cases hs; rfl
          rw [h1]; exact ofNat_toNat (by omega)
        rw [hV] at hlicj hiej hrj hcpc hcpe hie hrv
        have hsti_mem : st1.memory = st.memory := by rw [hst1, hst]
        have hsti_cd : st1.env.calldata = cd.data.toList := by rw [hst1, hst]; exact hcd
        have hiev : iev = wSum rw P j 0 := Option.some.inj (hie.symm.trans hiej)
        have hrvj : rv = rw := Option.some.inj (hrv.symm.trans hrj)
        subst hiev
        have hrvj' : rw = rv := hrvj.symm
        subst hrvj'
        have hval : v = wSum rw P (j + 1) 0 := by
          rw [hcvadd, hmv, hmpt, hcpt, hsti_mem, hsti_cd,
            Midfall.LoweringV3.VkWindow.wordFrom_cdWord]
          change wAddmodAt (wSum rw P j 0)
            (wMulmodAt (loadWord st.memory (Lc + 32 * j)) (cdWord cd (aI + 32 * j)) rw) rw =
            wSum rw P (j + 1) 0
          rfl
        have henv : VEnv.set (VEnv.set (VEnv.set Vi "instance_eval" v)
              "instance_cptr" (BitVec.ofNat 256 (aI + 32 * j) + BitVec.ofNat 256 32))
              "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * j) + BitVec.ofNat 256 32) =
            ("instance_cptr_end", BitVec.ofNat 256 (aI + 32 * n)) ::
              ("instance_cptr", BitVec.ofNat 256 (aI + 32 * (j + 1))) ::
              VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
                "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))) := by
          rw [hV, hval,
            show BitVec.ofNat 256 (aI + 32 * j) + BitVec.ofNat 256 32 =
              BitVec.ofNat 256 (aI + 32 * (j + 1)) by
              rw [← BitVec.ofNat_add,
                show aI + 32 * j + 32 = aI + 32 * (j + 1) by omega],
            show BitVec.ofNat 256 (Lc + 32 * j) + BitVec.ofNat 256 32 =
              BitVec.ofNat 256 (Lc + 32 * (j + 1)) by
              rw [← BitVec.ofNat_add,
                show Lc + 32 * j + 32 = Lc + 32 * (j + 1) by omega],
            instance_env_flat (V := V)
              (e := BitVec.ofNat 256 (aI + 32 * n)) (w := wSum rw P j 0)
              (w' := wSum rw P (j + 1) 0)
              (mp := BitVec.ofNat 256 (aI + 32 * j)) (lp := BitVec.ofNat 256 (Lc + 32 * j))
              (mp' := BitVec.ofNat 256 (aI + 32 * (j + 1)))
              (lp' := BitVec.ofNat 256 (Lc + 32 * (j + 1)))]
        refine ⟨j + 1, Nat.succ_le_of_lt hlt, henv, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- instance_cptr (the loop's own cursor)
          rw [henv, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := ("instance_cptr", BitVec.ofNat 256 (aI + 32 * (j + 1))) ::
              VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
                "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr_end") (y := "instance_cptr")
            (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
          rfl
        · -- instance_cptr_end
          rw [henv]
          rfl
        · -- l_i_cptr
          rw [henv]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := ("instance_cptr", BitVec.ofNat 256 (aI + 32 * (j + 1))) ::
              VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
                "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr_end") (y := "l_i_cptr")
            (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
              "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr") (y := "l_i_cptr")
            (v := BitVec.ofNat 256 (aI + 32 * (j + 1))) (by decide)]
          exact venv_get_set_same (D := Bridge.Dialect c g)
            (V := VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
            (x := "l_i_cptr") (v := BitVec.ofNat 256 Lc)
            (w := BitVec.ofNat 256 (Lc + 32 * (j + 1))) (by
              rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
                (x := "instance_eval") (y := "l_i_cptr")
                (v := wSum rw P (j + 1) 0) (by decide)]
              exact hlic)
        · -- instance_eval
          rw [henv]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := ("instance_cptr", BitVec.ofNat 256 (aI + 32 * (j + 1))) ::
              VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
                "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr_end") (y := "instance_eval")
            (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
              "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr") (y := "instance_eval")
            (v := BitVec.ofNat 256 (aI + 32 * (j + 1))) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
            (x := "l_i_cptr") (y := "instance_eval")
            (v := BitVec.ofNat 256 (Lc + 32 * (j + 1))) (by decide)]
          exact venv_get_set_same (D := Bridge.Dialect c g) (V := V)
            (x := "instance_eval") (v := 0) (w := wSum rw P (j + 1) 0) hie0
        · -- r
          rw [henv]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := ("instance_cptr", BitVec.ofNat 256 (aI + 32 * (j + 1))) ::
              VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
                "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr_end") (y := "r")
            (v := BitVec.ofNat 256 (aI + 32 * n)) (by decide)]
          rw [venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set (VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
              "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * (j + 1))))
            (x := "instance_cptr") (y := "r")
            (v := BitVec.ofNat 256 (aI + 32 * (j + 1))) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "instance_eval" (wSum rw P (j + 1) 0))
            (x := "l_i_cptr") (y := "r") (v := BitVec.ofNat 256 (Lc + 32 * (j + 1)))
            (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "instance_eval")
            (y := "r") (v := wSum rw P (j + 1) 0) (by decide)]
          exact hrw
        · exact ⟨(touchMemory st1 mp.toNat 32).activeWords, by rw [hst1, hst]; rfl⟩
      · intro hop
        exact absurd hop (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  intro V' st' o hrun
  cases hrun with
  | seqCons hfor hrest =>
      cases hrest with
      | seqNil =>
          cases hfor with
          | forLoop hi hl =>
              have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
                (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
              exact hloop _ _ hi' _ _ _ hl
  | seqStop hfor hne =>
      cases hfor with
      | forLoop hi hl =>
          have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
          exact hloop _ _ hi' _ _ _ hl
      | forInitHalt hi =>
          exact wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi


/-! ## 11. T3.9.c: THE SECOND PASS (shared denominator window) -/

/-- Statement 13 of the inner scope: the second pass that turns each inverse into `L_i(x)`.
PROVED by kernel reduction. -/
theorem lag_second_pass_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 13 1 =
      [GenAst.yfor
        [GenAst.ylet "pow_of_omega" (GenAst.yop EVM.Op.mload
          [Blocks.VkLoading.vkSite "OMEGA_INV_TO_L_MPTR" consts])]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "mptr", GenAst.yvar "mptr_end"])
        [GenAst.yset "mptr" (GenAst.yop EVM.Op.add [GenAst.yvar "mptr", GenAst.ylit 0x20])]
        [ GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "mptr",
            GenAst.yop EVM.Op.mulmod [GenAst.yvar "l_i_common",
              GenAst.yop EVM.Op.mulmod
                [GenAst.yop EVM.Op.mload [GenAst.yvar "mptr"],
                  GenAst.yvar "pow_of_omega", Blocks.VkLoading.vkSite "r" consts],
              Blocks.VkLoading.vkSite "r" consts]])
        , GenAst.yset "pow_of_omega" (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar "pow_of_omega", GenAst.yvar "omega",
              Blocks.VkLoading.vkSite "r" consts]) ]] := by
  kernel_rfl

theorem eval_mulmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {x y z : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.var y, Expr.var z]) (.vals [cv] st')) :
    ∃ xv yv zv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      cv = wMulmodAt xv yv zv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hy =>
          cases hrest2 with
          | argsCons hnil hz =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hzv, rfl⟩ := eval_var_inv hz
                  obtain ⟨hyv, rfl⟩ := eval_var_inv hy
                  obtain ⟨hxv, rfl⟩ := eval_var_inv hx
                  simp only [builtinWithExternal, stepOp, ter] at hbi
                  cases hbi
                  exact ⟨_, _, _, hxv, hyv, hzv, rfl, rfl⟩

theorem eval_mulmod_mload_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p a z : String} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.builtin Op.mload [Expr.var p], Expr.var a, Expr.var z]) (.vals [cv] st')) :
    ∃ mp av zv, VEnv.get V p = some mp ∧ VEnv.get V a = some av ∧ VEnv.get V z = some zv ∧
      cv = wMulmodAt (loadWord st.memory mp.toNat) av zv ∧
      st' = touchMemory st mp.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hmload =>
      cases hrest with
      | argsCons hrest2 ha =>
          cases hrest2 with
          | argsCons hnil hz =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hzv, rfl⟩ := eval_var_inv hz
                  obtain ⟨hav, rfl⟩ := eval_var_inv ha
                  obtain ⟨hmp, hmpget, hmv, htouch⟩ := eval_mload_var_inv hmload
                  simp only [builtinWithExternal, stepOp, ter, hmv] at hbi
                  cases hbi
                  exact ⟨_, _, _, hmpget, hav, hzv, rfl, htouch⟩

theorem eval_mulmod_second_pass_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {mv rv : U256} {st' : EvmState}
    (hrv : VEnv.get V "r" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.var "l_i_common",
          Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
          Expr.var "r"]) (.vals [mv] st')) :
    ∃ lc mp pw, VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "mptr" = some mp ∧
      VEnv.get V "pow_of_omega" = some pw ∧
      mv = wMulmodAt lc (wMulmodAt (loadWord st.memory mp.toNat) pw rv) rv ∧
      st' = touchMemory st mp.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hlc =>
      cases hrest with
      | argsCons hrest2 hinner =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hv, rfl⟩ := eval_var_inv hr
                  rw [hrv] at hv
                  injection hv with hvr
                  subst hvr
                  -- inner mulmod
                  obtain ⟨aiv, ist1, hinargs, hinbi⟩ := eval_builtin_vals_inv hinner
                  cases hinargs with
                  | argsCons hinrest hmload =>
                      cases hinrest with
                      | argsCons hinrest2 hpw =>
                          cases hinrest2 with
                          | argsCons hinnil hinr =>
                              cases hinnil with
                              | argsNil =>
                                  obtain ⟨hrv2, rfl⟩ := eval_var_inv hinr
                                  rw [hrv] at hrv2
                                  injection hrv2 with hrv3
                                  subst hrv3
                                  obtain ⟨hpwv, rfl⟩ := eval_var_inv hpw
                                  obtain ⟨hmp, hmpget, hmv, htouch⟩ := eval_mload_var_inv hmload
                                  simp only [builtinWithExternal, stepOp, ter, hmv] at hinbi
                                  cases hinbi
                                  obtain ⟨hlcget, rfl⟩ := eval_var_inv hlc
                                  simp only [builtinWithExternal, stepOp, ter] at hbi
                                  cases hbi
                                  exact ⟨_, _, _, hlcget, hmpget, hpwv, rfl, htouch⟩

theorem eval_mstore_second_pass_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {rv : U256} {st' : EvmState}
    (hrv : VEnv.get V "r" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mstore
        [Expr.var "mptr", Expr.builtin Op.mulmod
          [Expr.var "l_i_common", Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
            Expr.var "r"]]) (.vals [] st')) :
    ∃ lc mp pw, VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "mptr" = some mp ∧
      VEnv.get V "pow_of_omega" = some pw ∧
      st' = { touchMemory (touchMemory st mp.toNat 32) mp.toNat 32 with
        memory := storeWord st.memory mp.toNat
          (wMulmodAt lc (wMulmodAt (loadWord st.memory mp.toNat) pw rv) rv) } := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hmp =>
      cases hrest with
      | argsCons hnil hmul =>
          cases hnil with
          | argsNil =>
              obtain ⟨hmpv, rfl⟩ := eval_var_inv hmp
              obtain ⟨lc, mp, pw, hmm⟩ := eval_mulmod_second_pass_inv hrv hmul
              obtain ⟨hlc, hmpv', hpw, hmv, htouch⟩ := hmm
              -- the mstore address is the evaluated mptr
              have hmp_eq := Option.some.inj (hmpv.symm.trans hmpv')
              subst hmp_eq
              simp only [builtinWithExternal, stepOp, hmv] at hbi
              cases hbi
              subst htouch
              exact ⟨_, _, _, hlc, hmpv', hpw, rfl⟩

theorem eval_mulmod_vars_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {x y z : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.var y, Expr.var z]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var x, Expr.var y, Expr.var z],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

theorem eval_mulmod_mload_var_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {p a z : String} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.builtin Op.mload [Expr.var p], Expr.var a, Expr.var z]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.builtin Op.mload [Expr.var p], Expr.var a, Expr.var z],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact eval_mload_var_halt_false hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

theorem eval_mulmod_second_pass_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod
        [Expr.var "l_i_common",
          Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
          Expr.var "r"]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "l_i_common", Expr.builtin Op.mulmod
      [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
      Expr.var "r"],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact eval_mulmod_mload_var_halt_false hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

theorem eval_mstore_second_pass_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mstore
        [Expr.var "mptr", Expr.builtin Op.mulmod
          [Expr.var "l_i_common", Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
            Expr.var "r"]]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "mptr", Expr.builtin Op.mulmod
      [Expr.var "l_i_common", Expr.builtin Op.mulmod
        [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
        Expr.var "r"]],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact eval_mulmod_second_pass_halt_false hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs


/-- The second-pass body block, inverted: it ends normally and leaves the updated environment and
the store over the mload word. -/
theorem exec_second_pass_body_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V Vb : VEnv (Bridge.Dialect c g)} {st stb : EvmState} {rv : U256} {o : Outcome}
    (hrv : VEnv.get V "r" = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block
        [ Stmt.exprStmt (Expr.builtin Op.mstore
            [Expr.var "mptr", Expr.builtin Op.mulmod
              [Expr.var "l_i_common", Expr.builtin Op.mulmod
                [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
                Expr.var "r"]]),
          Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
            [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"])])
      Vb stb o) :
    o = .normal ∧ ∃ lc mp pw om,
      VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "mptr" = some mp ∧
      VEnv.get V "pow_of_omega" = some pw ∧ VEnv.get V "omega" = some om ∧
      Vb = VEnv.set V "pow_of_omega" (wMulmodAt pw om rv) ∧
      stb = { touchMemory (touchMemory st mp.toNat 32) mp.toNat 32 with
        memory := storeWord st.memory mp.toNat
          (wMulmodAt lc (wMulmodAt (loadWord st.memory mp.toNat) pw rv) rv) } := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons h1 hrest =>
          cases hrest with
          | seqCons h2 hnil =>
              cases hnil with
              | seqNil =>
                  obtain ⟨rfl, st1, hm, hst1⟩ := exec_exprStmt_inv h1
                  obtain ⟨lc, mp, pw, hlc, hmp, hpw, hstm⟩ :=
                    eval_mstore_second_pass_inv hrv hm
                  obtain ⟨v2, he2, hV2⟩ := exec_assign_inv h2
                  obtain ⟨pwm, om, rvm, hpwm, hom, hrvm, hv2, hst2⟩ :=
                    eval_mulmod_vars_inv he2
                  have hpw_eq : pwm = pw := Option.some.inj (hpwm.symm.trans hpw)
                  have hrv_eq : rvm = rv := Option.some.inj (hrvm.symm.trans hrv)
                  have hpw_eq' : pw = pwm := hpw_eq.symm
                  have hrv_eq' : rv = rvm := hrv_eq.symm
                  subst hpw_eq'
                  subst hrv_eq'
                  subst hv2
                  refine ⟨rfl, lc, mp, pw, om, hlc, hmp, hpw, hom, ?_, ?_⟩
                  · rw [hV2, restore_set_same (D := Bridge.Dialect c g)]
                  · rw [hst2, hst1, hstm]
          | seqStop h2 hne =>
              cases h2 with
              | assignVal _ _ => cases hne rfl
              | assignHalt he => exact (eval_mulmod_vars_halt_false he).elim
      | seqStop h1 hne =>
          cases h1 with
          | exprStmt he => cases hne rfl
          | exprStmtHalt he => exact (eval_mstore_second_pass_halt_false he).elim

/-- A store leaves every byte outside its 32-byte window where it was. -/
theorem storeWord_outside (mem : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : a < p ∨ p + 32 ≤ a) : storeWord mem p v a = mem a := by
  simp only [storeWord]
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  omega

/-- The `omegaPows` step, as a rewrite rule. -/
theorem omegaPows_succ (r om w0 : U256) (i : Nat) :
    omegaPows r om w0 (i + 1) = wMulmodAt (omegaPows r om w0 i) om r := rfl

/-- Read over write at a disjoint word: the two named helpers the window invariant uses. -/
theorem loadWord_storeWord_at {mem : Nat → UInt8} {p q : Nat} {v : U256}
    (h : q + 32 ≤ p ∨ p + 32 ≤ q) :
    loadWord (storeWord mem p v) q = loadWord mem q :=
  Midfall.Yul.Word.loadWord_storeWord_disjoint mem p q v h

/-- Read back the word just stored. -/
theorem loadWord_storeWord_same_at (mem : Nat → UInt8) (p : Nat) (v : U256) :
    loadWord (storeWord mem p v) p = v :=
  Midfall.Yul.Word.loadWord_storeWord_same mem p v

/-- One second-pass iteration, environment half: the body's `pow_of_omega` update and the post
block's `mptr` update collapse to the invariant's normal form. -/
theorem second_pass_env_step {V : VEnv (Bridge.Dialect c g)} {p pw mp vmp : U256} :
    VEnv.set (VEnv.set (("pow_of_omega", p) :: VEnv.set V "mptr" mp)
      "pow_of_omega" pw) "mptr" vmp =
      ("pow_of_omega", pw) :: VEnv.set V "mptr" vmp := by
  have h1 : VEnv.set (("pow_of_omega", p) :: VEnv.set V "mptr" mp)
      "pow_of_omega" pw = ("pow_of_omega", pw) :: VEnv.set V "mptr" mp := by
    simp [VEnv.set]
  have h2 : VEnv.set (("pow_of_omega", pw) :: VEnv.set V "mptr" mp)
      "mptr" vmp = ("pow_of_omega", pw) :: VEnv.set (VEnv.set V "mptr" mp) "mptr" vmp := by
    simp [VEnv.set]
  rw [h1, h2, venv_set_set (D := Bridge.Dialect c g)]

/-- The second-pass loop invariant, as a structure so that every construction site names its
fields (no long `And` tuples and no metavariable leak from unfolding a let-bound `Inv`). -/
structure SecondPassInv {c : ExternalCalls} {g : ExternalGas}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {D n m : Nat}
    {lc om rw : U256} {P F : Nat → U256} (j : Nat) (mem : Nat → UInt8)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} : Prop where
  hj : j ≤ n + m
  env : V' = ("pow_of_omega", P j) :: VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * j))
  mptr : VEnv.get V' "mptr" = some (BitVec.ofNat 256 (D + 32 * j))
  mptrEnd : VEnv.get V' "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m)))
  powGet : VEnv.get V' "pow_of_omega" = some (P j)
  lcGet : VEnv.get V' "l_i_common" = some lc
  omGet : VEnv.get V' "omega" = some om
  rGet : VEnv.get V' "r" = some rw
  memEq : st'.memory = mem
  written : ∀ i, i < j → loadWord mem (D + 32 * i) = F i
  untouched : ∀ i, j ≤ i → i < n + m → loadWord mem (D + 32 * i) = loadWord st.memory (D + 32 * i)
  outside : MemSameOutside st st' D (32 * j)
  envSame : st'.env = st.env
  halted : st'.halted = st.halted

theorem lag_second_pass_loop (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aL : Nat)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some aL) (hLb : aL < 2 ^ 256)
    (D : Nat) (hD : D + 32 * (n + m) < 2 ^ 256)
    (hLD : aL + 32 ≤ D ∨ D + 32 * (n + m) ≤ aL) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 13 1)
      (fun V _ => VEnv.get V "mptr" = some (BitVec.ofNat 256 D) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (VEnv.get V "l_i_common").isSome ∧ (VEnv.get V "omega").isSome ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧
        ∃ lc om rw, VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "omega" = some om ∧
          VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
          (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
            wMulmodAt lc (wMulmodAt (loadWord st.memory (D + 32 * i))
              (omegaPows rw om (loadWord st.memory aL) i) rw) rw) ∧
          MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
          st'.halted = st.halted) := by
  rw [lag_second_pass_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    GenAst.yexpr, Blocks.VkLoading.vkSite, hr, hL]
  intro V st hpre
  obtain ⟨hmp, hme, hlcsome, homsome, hrsome⟩ := hpre
  obtain ⟨lc, hlc⟩ := QuotientRows.isSome_elim hlcsome
  obtain ⟨om, hom⟩ := QuotientRows.isSome_elim homsome
  obtain ⟨rw, hrw⟩ := QuotientRows.isSome_elim hrsome
  let w0 : U256 := loadWord st.memory aL
  let P : Nat → U256 := omegaPows rw om w0
  let F : Nat → U256 := fun i => wMulmodAt lc (wMulmodAt (loadWord st.memory (D + 32 * i)) (P i) rw) rw
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧
      ∃ lc om rw, VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "omega" = some om ∧
        VEnv.get V "r" = some rw ∧
        V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
          wMulmodAt lc (wMulmodAt (loadWord st.memory (D + 32 * i))
            (omegaPows rw om (loadWord st.memory aL) i) rw) rw) ∧
        MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
        st'.halted = st.halted
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop
      [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
        [Expr.lit (Literal.number aL)]))]
      (Expr.builtin Op.lt [Expr.var "mptr", Expr.var "mptr_end"])
      [Stmt.assign ["mptr"] (Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])]
      [ Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr",
          Expr.builtin Op.mulmod [Expr.var "l_i_common", Expr.builtin Op.mulmod
            [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
            Expr.var "r"]])
      , Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
          [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"]) ]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j mem, SecondPassInv (V := V) (st := st) (D := D) (n := n) (m := m)
      (lc := lc) (om := om) (rw := rw) (P := P) (F := F) j mem (V' := V') (st' := st')
  let Qloop : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun Vend stend o => Q (restore V Vend) stend o
  have hinit : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) 14
      (hoist (Bridge.Dialect c g)
        [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
          [Expr.lit (Literal.number aL)]))] :: funs)
      V st
      [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
        [Expr.lit (Literal.number aL)]))]
      (fun Vi sti oi =>
        match oi with
        | .normal => Inv Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False) := by
    refine ⟨rfl, ⟨?_⟩⟩
    show Inv (["pow_of_omega"].zip
      [loadWord st.memory (BitVec.ofNat 256 aL).toNat] ++ V)
      (touchMemory st (BitVec.ofNat 256 aL).toNat 32)
    rw [ofNat_toNat hLb]
    have hzip : (["pow_of_omega"].zip [loadWord st.memory aL]) ++ V =
        (("pow_of_omega", loadWord st.memory aL) :: V) := rfl
    rw [hzip]
    refine ⟨0, st.memory, ?_⟩
    refine SecondPassInv.mk (j := 0) (mem := st.memory) (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl ?_ ?_ ?_ rfl rfl
    · change ("pow_of_omega", w0) :: V =
        ("pow_of_omega", P 0) :: VEnv.set V "mptr" (BitVec.ofNat 256 D)
      rw [venv_set_eq_self hmp]
      rfl
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "mptr") (v := w0) (by decide)]
      exact hmp
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "mptr_end") (v := w0) (by decide)]
      exact hme
    · rfl
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "l_i_common") (v := w0) (by decide)]
      exact hlc
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "omega") (v := w0) (by decide)]
      exact hom
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "r") (v := w0) (by decide)]
      exact hrw
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro i _ _; rfl
    · intro a _; rfl
  have hloop : ∀ Vi sti, Inv Vi sti →
      ∀ V' st' o, ExecLoop (Bridge.Dialect c g)
        (hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs)
        Vi sti
        (Expr.builtin Op.lt [Expr.var "mptr", Expr.var "mptr_end"])
        [Stmt.assign ["mptr"] (Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])]
        [ Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr",
            Expr.builtin Op.mulmod [Expr.var "l_i_common", Expr.builtin Op.mulmod
              [Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "pow_of_omega", Expr.var "r"],
              Expr.var "r"]])
        , Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
            [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"]) ]
        V' st' o → Qloop V' st' o := by
    refine LoopRule.allRuns_loop (Inv := Inv) (Q := Qloop) ?_
    intro Vi sti hInv
    rcases hInv with ⟨j, mem', hInv⟩
    have hj' : j ≤ n + m := hInv.hj
    have hDj : D + 32 * j < 2 ^ 256 := by omega
    refine ⟨?condHalt, ?exit, ?iter⟩
    · intro st1 hc
      exact (eval_lt_halt_false hc).elim
    · intro cv st1 hc hz
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hxget.symm.trans hInv.mptr)
      have hyv : yv = BitVec.ofNat 256 (D + 32 * (n + m)) :=
        Option.some.inj (hyget.symm.trans hInv.mptrEnd)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (D + 32 * j)).ult
          (BitVec.ofNat 256 (D + 32 * (n + m)))) = (0 : U256) := by
        rw [← hcv]; exact hz
      have hge : D + 32 * (n + m) ≤ D + 32 * j :=
        LoopRule.lt_guard_false hDj hD h0
      have hjn : j = n + m := by
        have hle : n + m ≤ j := by omega
        exact Nat.le_antisymm hj' hle
      subst hjn
      change Q (restore V Vi) st1 .normal
      rw [hst1, hInv.env]
      simp only [Q]
      refine ⟨trivial, lc, om, rw, hlc, hom, hrw, ?_, ?_, ?_, ?_, ?_⟩
      · rw [restore_cons_length (D := Bridge.Dialect c g) (V := V)
          (W := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))))
          (y := "pow_of_omega") (b := P (n + m))
          (by simp only [venv_set_length (D := Bridge.Dialect c g)])]
      · intro i hi
        rw [hInv.memEq]
        exact hInv.written i hi
      · intro a ha; exact hInv.outside a ha
      · exact hInv.envSame
      · exact hInv.halted
    · intro cv st1 hc hnz Vb stb ob hbody
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hxget.symm.trans hInv.mptr)
      have hyv : yv = BitVec.ofNat 256 (D + 32 * (n + m)) :=
        Option.some.inj (hyget.symm.trans hInv.mptrEnd)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (D + 32 * j)).ult
          (BitVec.ofNat 256 (D + 32 * (n + m)))) ≠ (0 : U256) := by
        rw [← hcv]; exact hnz
      have hlt : j < n + m := by
        have h1 : D + 32 * j < D + 32 * (n + m) :=
          LoopRule.lt_guard_true (i := D + 32 * j) (n := D + 32 * (n + m)) hDj hD h0
        nlinarith
      obtain ⟨rfl, lc', mp, pw, om', hlc', hmp', hpw, hom', hVb, hstb⟩ :=
        exec_second_pass_body_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs) (V := Vi) (rv := rw) hInv.rGet hbody
      have hlc_eq : lc = lc' := Option.some.inj (hInv.lcGet.symm.trans hlc')
      have hom_eq : om = om' := Option.some.inj (hInv.omGet.symm.trans hom')
      subst hlc_eq; subst hom_eq
      have hmpj : VEnv.get Vi "mptr" = some (BitVec.ofNat 256 (D + 32 * j)) := hInv.mptr
      have hmp_eq : mp = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hmp'.symm.trans hmpj)
      have hpw_eq : pw = P j := Option.some.inj (hpw.symm.trans hInv.powGet)
      have hbody_mem : stb.memory = storeWord mem' (D + 32 * j)
          (wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw) := by
        rw [hstb, hst1]
        rw [hInv.memEq]
        rw [show (BitVec.toNat mp) = D + 32 * j by
          rw [hmp_eq]; exact ofNat_toNat (by omega)]
      subst hmp_eq
      intro Vp stp op hpost
      obtain ⟨hop, vmp, stmp, heval, hVp, hstp⟩ :=
        exec_one_total_assign_block_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs)
          (x := "mptr") (e := Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])
          (hne := fun st0 st1 hh => eval_add_var_lit_halt_false hh) hpost
      subst hop
      obtain ⟨amp, hamp, hvmp, hstmp⟩ := eval_add_var_lit_inv heval
      subst hstmp
      subst hVp
      have hampV : VEnv.get Vb "mptr" = some amp := hamp
      rw [hVb] at hampV
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := Vi) (x := "pow_of_omega")
        (y := "mptr") (v := wMulmodAt pw om rw) (by decide)] at hampV
      have hamp_eq : amp = BitVec.ofNat 256 (D + 32 * j) := by
        have hmpV : VEnv.get Vi "mptr" = some (BitVec.ofNat 256 (D + 32 * j)) := hInv.mptr
        exact Option.some.inj (hampV.symm.trans hmpV)
      subst hamp_eq
      have hvmp_eq : vmp = BitVec.ofNat 256 (D + 32 * (j + 1)) := by
        rw [hvmp, ← BitVec.ofNat_add]; congr 1
      subst hvmp_eq
      have hval : wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw = F j := by
        rw [hpw_eq, hInv.untouched j (Nat.le_refl j) hlt]
      refine ⟨?_, ?_⟩
      · intro _
        refine ⟨j + 1, storeWord mem' (D + 32 * j)
          (wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw), ?_⟩
        have henvNew : VEnv.set Vb "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))) =
            ("pow_of_omega", P (j + 1)) ::
              VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))) := by
          rw [hVb, hInv.env]
          have hval2 : wMulmodAt pw om rw = P (j + 1) := by
            rw [hpw_eq]
            rfl
          rw [hval2]
          rw [second_pass_env_step
            (p := P j) (pw := P (j + 1)) (mp := BitVec.ofNat 256 (D + 32 * j))
            (vmp := BitVec.ofNat 256 (D + 32 * (j + 1)))]
        refine SecondPassInv.mk (j := j + 1)
          (mem := storeWord mem' (D + 32 * j)
            (wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw))
          (Nat.succ_le_of_lt hlt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · exact henvNew
        · -- mptr
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "mptr")
            (v := P (j + 1)) (by decide)]
          exact venv_get_set_same (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (v := BitVec.ofNat 256 D)
            (w := BitVec.ofNat 256 (D + 32 * (j + 1))) hmp
        · -- mptr_end
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "mptr_end")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "mptr_end")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hme
        · -- pow
          rw [henvNew]
          rfl
        · -- l_i_common
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "l_i_common")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "l_i_common")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hlc
        · -- omega
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "omega")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "omega")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hom
        · -- r
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "r")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "r")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hrw
        · rw [hstp, hbody_mem]
        · intro i hi
          by_cases hij : i = j
          · subst hij
            rw [loadWord_storeWord_same_at, hval]
          · have hi' : i < j := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hij
            have hdisj : D + 32 * i + 32 ≤ D + 32 * j := by omega
            rw [loadWord_storeWord_at (Or.inl hdisj)]
            exact hInv.written i hi'
        · intro i hji hi
          have hdisj : D + 32 * j + 32 ≤ D + 32 * i := by omega
          rw [loadWord_storeWord_at (Or.inr hdisj)]
          exact hInv.untouched i (by omega) hi
        · intro a ha
          rw [hstp, hstb, hst1, hInv.memEq, ofNat_toNat (by omega)]
          change storeWord mem' (D + 32 * j)
            (wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw) a = st.memory a
          have hstore : storeWord mem' (D + 32 * j)
              (wMulmodAt lc (wMulmodAt (loadWord mem' (D + 32 * j)) pw rw) rw) a = mem' a := by
            apply storeWord_outside
            omega
          rw [hstore, ← hInv.memEq]
          exact hInv.outside a (by omega)
        · rw [hstp, hstb, hst1]
          exact hInv.envSame
        · rw [hstp, hstb, hst1]
          exact hInv.halted
      · intro hop
        exact absurd hop (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  intro V' st' o hrun
  cases hrun with
  | seqCons hfor hrest =>
      cases hrest with
      | seqNil =>
          cases hfor with
          | forLoop hi hl =>
              have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
                (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
              exact hloop _ _ hi' _ _ _ hl
  | seqStop hfor hne =>
      cases hfor with
      | forLoop hi hl =>
          have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
          exact hloop _ _ hi' _ _ _ hl
      | forInitHalt hi =>
          exact wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi


/-! ## 11. T3.9.b: THE DENOMINATOR LOOP (semantic route) -/

theorem eval_sub_r_pow_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {cv : U256} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"]) (.vals [cv] st')) :
    ∃ rv pw, VEnv.get V "r" = some rv ∧ VEnv.get V "pow_of_omega" = some pw ∧
      cv = rv - pw ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hr =>
      cases hrest with
      | argsCons hnil hpw =>
          cases hnil with
          | argsNil =>
              obtain ⟨hpwv, rfl⟩ := eval_var_inv hpw
              obtain ⟨hrv, rfl⟩ := eval_var_inv hr
              simp only [builtinWithExternal, stepOp, bin] at hbi
              cases hbi
              exact ⟨_, _, hrv, hpwv, rfl, rfl⟩

theorem eval_addmod_denom_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {cv rv : U256} {st' : EvmState}
    (hrv : VEnv.get V "r" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.addmod
        [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
          Expr.var "r"]) (.vals [cv] st')) :
    ∃ xv pw, VEnv.get V "x" = some xv ∧ VEnv.get V "pow_of_omega" = some pw ∧
      cv = wAddmodAt xv (rv - pw) rv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hrest with
      | argsCons hrest2 hsub =>
          cases hrest2 with
          | argsCons hnil hr =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hv, rfl⟩ := eval_var_inv hr
                  rw [hrv] at hv
                  injection hv with hvr
                  subst hvr
                  obtain ⟨sr, sp, hsr, hsp, hsubv, hstsub⟩ :=
                    eval_sub_r_pow_inv hsub
                  have hsr_eq : sr = rv := Option.some.inj (hsr.symm.trans hrv)
                  subst hsr_eq
                  subst hstsub
                  obtain ⟨hxv, rfl⟩ := eval_var_inv hx
                  simp only [builtinWithExternal, stepOp, ter, hsubv] at hbi
                  cases hbi
                  exact ⟨_, _, hxv, hsp, rfl, rfl⟩

theorem eval_mstore_denom_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {rv : U256} {st' : EvmState}
    (hrv : VEnv.get V "r" = some rv)
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mstore
        [Expr.var "mptr", Expr.builtin Op.addmod
          [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
            Expr.var "r"]]) (.vals [] st')) :
    ∃ xv mp pw, VEnv.get V "x" = some xv ∧ VEnv.get V "mptr" = some mp ∧
      VEnv.get V "pow_of_omega" = some pw ∧
      st' = { touchMemory st mp.toNat 32 with
        memory := storeWord st.memory mp.toNat (wAddmodAt xv (rv - pw) rv) } := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hmp =>
      cases hrest with
      | argsCons hnil hadd =>
          cases hnil with
          | argsNil =>
              obtain ⟨hmpv, rfl⟩ := eval_var_inv hmp
              obtain ⟨xv, pw, hxv, hpw, hvadd, hstadd⟩ :=
                eval_addmod_denom_inv hrv hadd
              subst hstadd
              simp only [builtinWithExternal, stepOp, hvadd] at hbi
              cases hbi
              exact ⟨_, _, _, hxv, hmpv, hpw, rfl⟩

theorem eval_sub_r_pow_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "r", Expr.var "pow_of_omega"],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, bin] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

theorem eval_addmod_denom_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.addmod
        [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
          Expr.var "r"]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
      Expr.var "r"],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact eval_sub_r_pow_halt_false hh
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp, ter] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

theorem eval_mstore_denom_halt_false {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {st' : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mstore
        [Expr.var "mptr", Expr.builtin Op.addmod
          [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
            Expr.var "r"]]) (.halt st')) : False := by
  have hne : ∀ e ∈ [Expr.var "mptr", Expr.builtin Op.addmod
      [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
        Expr.var "r"]],
      ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 e (.halt st1) → False := by
    intro e he st0 st1 hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
    · exact eval_addmod_denom_halt_false hh
  cases h with
  | builtinHalt _ hbi =>
      simp only [builtinWithExternal, stepOp] at hbi
      split at hbi <;> simp at hbi
  | builtinArgsHalt hargs => exact eval_args_halt_false hne hargs

/-- The denominator body block, inverted: `mstore(mptr, addmod(x, sub(r, pow), r))` then
`pow := mulmod(pow, omega, r)`. -/
theorem exec_denoms_body_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V Vb : VEnv (Bridge.Dialect c g)} {st stb : EvmState} {rv : U256} {o : Outcome}
    (hrv : VEnv.get V "r" = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block
        [ Stmt.exprStmt (Expr.builtin Op.mstore
            [Expr.var "mptr", Expr.builtin Op.addmod
              [Expr.var "x", Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"],
                Expr.var "r"]]),
          Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
            [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"])])
      Vb stb o) :
    o = .normal ∧ ∃ x mp pw om,
      VEnv.get V "x" = some x ∧ VEnv.get V "mptr" = some mp ∧
      VEnv.get V "pow_of_omega" = some pw ∧ VEnv.get V "omega" = some om ∧
      Vb = VEnv.set V "pow_of_omega" (wMulmodAt pw om rv) ∧
      stb = { touchMemory st mp.toNat 32 with
        memory := storeWord st.memory mp.toNat (wAddmodAt x (rv - pw) rv) } := by
  cases h with
  | block hb =>
      cases hb with
      | seqCons h1 hrest =>
          cases hrest with
          | seqCons h2 hnil =>
              cases hnil with
              | seqNil =>
                  obtain ⟨rfl, st1, hm, hst1⟩ := exec_exprStmt_inv h1
                  obtain ⟨x, mp, pw, hx, hmp, hpw, hstm⟩ :=
                    eval_mstore_denom_inv hrv hm
                  obtain ⟨v2, he2, hV2⟩ := exec_assign_inv h2
                  obtain ⟨pwm, om, rvm, hpwm, hom, hrvm, hv2, hst2⟩ :=
                    eval_mulmod_vars_inv he2
                  have hpw_eq : pwm = pw := Option.some.inj (hpwm.symm.trans hpw)
                  have hrv_eq : rvm = rv := Option.some.inj (hrvm.symm.trans hrv)
                  have hpw_eq' : pw = pwm := hpw_eq.symm
                  have hrv_eq' : rv = rvm := hrv_eq.symm
                  subst hpw_eq'
                  subst hrv_eq'
                  subst hv2
                  refine ⟨rfl, x, mp, pw, om, hx, hmp, hpw, hom, ?_, ?_⟩
                  · rw [hV2, restore_set_same (D := Bridge.Dialect c g)]
                  · rw [hst2, hst1, hstm]
          | seqStop h2 hne =>
              cases h2 with
              | assignVal _ _ => cases hne rfl
              | assignHalt he => exact (eval_mulmod_vars_halt_false he).elim
      | seqStop h1 hne =>
          cases h1 with
          | exprStmt he => cases hne rfl
          | exprStmtHalt he => exact (eval_mstore_denom_halt_false he).elim

/-- The denominator loop invariant, as a structure so every construction site names its fields. -/
structure DenomsInv {c : ExternalCalls} {g : ExternalGas}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {D n m : Nat}
    {x om rw : U256} {P F : Nat → U256} (j : Nat) (mem : Nat → UInt8)
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} : Prop where
  hj : j ≤ n + m
  env : V' = ("pow_of_omega", P j) :: VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * j))
  mptr : VEnv.get V' "mptr" = some (BitVec.ofNat 256 (D + 32 * j))
  mptrEnd : VEnv.get V' "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m)))
  powGet : VEnv.get V' "pow_of_omega" = some (P j)
  xGet : VEnv.get V' "x" = some x
  omGet : VEnv.get V' "omega" = some om
  rGet : VEnv.get V' "r" = some rw
  memEq : st'.memory = mem
  written : ∀ i, i < j → loadWord mem (D + 32 * i) = F i
  untouched : ∀ i, j ≤ i → i < n + m → loadWord mem (D + 32 * i) = loadWord st.memory (D + 32 * i)
  outside : MemSameOutside st st' D (32 * j)
  envSame : st'.env = st.env
  halted : st'.halted = st.halted

/-- **LOOP 2** (statement 7): the denominators `x - ω_i`. Bound = `n + m`, shared window at `D`.
The proof is semantic (`allRuns_loop`): the body block is inverted by `exec_denoms_body_inv`, and
the invariant carries the running power `omegaPows`, the first `j` writes (`written`), the
not-yet-written words (`untouched`) and the frame outside the window (`outside`). -/
theorem lag_denoms_loop (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aL : Nat)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some aL) (hLb : aL < 2 ^ 256)
    (D : Nat) (hD : D + 32 * (n + m) < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 7 1)
      (fun V _ => VEnv.get V "mptr" = some (BitVec.ofNat 256 D) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (VEnv.get V "x").isSome ∧ (VEnv.get V "omega").isSome ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧
        ∃ x om rw, VEnv.get V "x" = some x ∧ VEnv.get V "omega" = some om ∧
          VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
          (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
            wAddmodAt x (rw - omegaPows rw om (loadWord st.memory aL) i) rw) ∧
          MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
          st'.halted = st.halted) := by
  rw [lag_denoms_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    GenAst.yexpr, Blocks.VkLoading.vkSite, hr, hL]
  intro V st hpre
  obtain ⟨hmp, hme, hxsome, homsome, hrsome⟩ := hpre
  obtain ⟨x, hx⟩ := QuotientRows.isSome_elim hxsome
  obtain ⟨om, hom⟩ := QuotientRows.isSome_elim homsome
  obtain ⟨rw, hrw⟩ := QuotientRows.isSome_elim hrsome
  let w0 : U256 := loadWord st.memory aL
  let P : Nat → U256 := omegaPows rw om w0
  let F : Nat → U256 := fun i => denomVal rw x P i
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧
      ∃ x om rw, VEnv.get V "x" = some x ∧ VEnv.get V "omega" = some om ∧
        VEnv.get V "r" = some rw ∧
        V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
          wAddmodAt x (rw - omegaPows rw om (loadWord st.memory aL) i) rw) ∧
        MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
        st'.halted = st.halted
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop
      [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
        [Expr.lit (Literal.number aL)]))]
      (Expr.builtin Op.lt [Expr.var "mptr", Expr.var "mptr_end"])
      [Stmt.assign ["mptr"] (Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])]
      [ Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr",
          Expr.builtin Op.addmod [Expr.var "x",
            Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"], Expr.var "r"]])
      , Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
          [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"]) ]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j mem, DenomsInv (V := V) (st := st) (D := D) (n := n) (m := m)
      (x := x) (om := om) (rw := rw) (P := P) (F := F) j mem (V' := V') (st' := st')
  let Qloop : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun Vend stend o => Q (restore V Vend) stend o
  have hinit : wpSS (Bridge.Dialect c g) (Bopen c g) (Cnone _) 14
      (hoist (Bridge.Dialect c g)
        [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
          [Expr.lit (Literal.number aL)]))] :: funs)
      V st
      [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
        [Expr.lit (Literal.number aL)]))]
      (fun Vi sti oi =>
        match oi with
        | .normal => Inv Vi sti
        | .halt => Q (restore V Vi) sti .halt
        | _ => False) := by
    refine ⟨rfl, ⟨?_⟩⟩
    show Inv (["pow_of_omega"].zip
      [loadWord st.memory (BitVec.ofNat 256 aL).toNat] ++ V)
      (touchMemory st (BitVec.ofNat 256 aL).toNat 32)
    rw [ofNat_toNat hLb]
    have hzip : (["pow_of_omega"].zip [loadWord st.memory aL]) ++ V =
        (("pow_of_omega", loadWord st.memory aL) :: V) := rfl
    rw [hzip]
    refine ⟨0, st.memory, ?_⟩
    refine DenomsInv.mk (j := 0) (mem := st.memory) (Nat.zero_le _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl ?_ ?_ ?_ rfl rfl
    · change ("pow_of_omega", w0) :: V =
        ("pow_of_omega", P 0) :: VEnv.set V "mptr" (BitVec.ofNat 256 D)
      rw [venv_set_eq_self hmp]
      rfl
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "mptr") (v := w0) (by decide)]
      exact hmp
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "mptr_end") (v := w0) (by decide)]
      exact hme
    · rfl
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "x") (v := w0) (by decide)]
      exact hx
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "omega") (v := w0) (by decide)]
      exact hom
    · rw [venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "pow_of_omega")
        (y := "r") (v := w0) (by decide)]
      exact hrw
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro i _ _; rfl
    · intro a _; rfl
  have hloop : ∀ Vi sti, Inv Vi sti →
      ∀ V' st' o, ExecLoop (Bridge.Dialect c g)
        (hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs)
        Vi sti
        (Expr.builtin Op.lt [Expr.var "mptr", Expr.var "mptr_end"])
        [Stmt.assign ["mptr"] (Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])]
        [ Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr",
            Expr.builtin Op.addmod [Expr.var "x",
              Expr.builtin Op.sub [Expr.var "r", Expr.var "pow_of_omega"], Expr.var "r"]])
        , Stmt.assign ["pow_of_omega"] (Expr.builtin Op.mulmod
            [Expr.var "pow_of_omega", Expr.var "omega", Expr.var "r"]) ]
        V' st' o → Qloop V' st' o := by
    refine LoopRule.allRuns_loop (Inv := Inv) (Q := Qloop) ?_
    intro Vi sti hInv
    rcases hInv with ⟨j, mem', hInv⟩
    have hj' : j ≤ n + m := hInv.hj
    have hDj : D + 32 * j < 2 ^ 256 := by omega
    refine ⟨?condHalt, ?exit, ?iter⟩
    · intro st1 hc
      exact (eval_lt_halt_false hc).elim
    · intro cv st1 hc hz
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hxget.symm.trans hInv.mptr)
      have hyv : yv = BitVec.ofNat 256 (D + 32 * (n + m)) :=
        Option.some.inj (hyget.symm.trans hInv.mptrEnd)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (D + 32 * j)).ult
          (BitVec.ofNat 256 (D + 32 * (n + m)))) = (0 : U256) := by
        rw [← hcv]; exact hz
      have hge : D + 32 * (n + m) ≤ D + 32 * j :=
        LoopRule.lt_guard_false hDj hD h0
      have hjn : j = n + m := by
        have hle : n + m ≤ j := by omega
        exact Nat.le_antisymm hj' hle
      subst hjn
      change Q (restore V Vi) st1 .normal
      rw [hst1, hInv.env]
      simp only [Q]
      refine ⟨trivial, x, om, rw, hx, hom, hrw, ?_, ?_, ?_, ?_, ?_⟩
      · rw [restore_cons_length (D := Bridge.Dialect c g) (V := V)
          (W := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))))
          (y := "pow_of_omega") (b := P (n + m))
          (by simp only [venv_set_length (D := Bridge.Dialect c g)])]
      · intro i hi
        rw [hInv.memEq]
        exact hInv.written i hi
      · intro a ha; exact hInv.outside a ha
      · exact hInv.envSame
      · exact hInv.halted
    · intro cv st1 hc hnz Vb stb ob hbody
      obtain ⟨xv, yv, hxget, hyget, hcv, hst1⟩ := eval_lt_vars_inv hc
      have hxv : xv = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hxget.symm.trans hInv.mptr)
      have hyv : yv = BitVec.ofNat 256 (D + 32 * (n + m)) :=
        Option.some.inj (hyget.symm.trans hInv.mptrEnd)
      rw [hxv, hyv] at hcv
      have h0 : b2w ((BitVec.ofNat 256 (D + 32 * j)).ult
          (BitVec.ofNat 256 (D + 32 * (n + m)))) ≠ (0 : U256) := by
        rw [← hcv]; exact hnz
      have hlt : j < n + m := by
        have h1 : D + 32 * j < D + 32 * (n + m) :=
          LoopRule.lt_guard_true (i := D + 32 * j) (n := D + 32 * (n + m)) hDj hD h0
        nlinarith
      obtain ⟨rfl, x', mp, pw, om', hx', hmp', hpw, hom', hVb, hstb⟩ :=
        exec_denoms_body_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs) (V := Vi) (rv := rw) hInv.rGet hbody
      have hx_eq : x = x' := Option.some.inj (hInv.xGet.symm.trans hx')
      have hom_eq : om = om' := Option.some.inj (hInv.omGet.symm.trans hom')
      subst hx_eq; subst hom_eq
      have hmpj : VEnv.get Vi "mptr" = some (BitVec.ofNat 256 (D + 32 * j)) := hInv.mptr
      have hmp_eq : mp = BitVec.ofNat 256 (D + 32 * j) :=
        Option.some.inj (hmp'.symm.trans hmpj)
      have hpw_eq : pw = P j := Option.some.inj (hpw.symm.trans hInv.powGet)
      have hbody_mem : stb.memory = storeWord mem' (D + 32 * j)
          (wAddmodAt x (rw - pw) rw) := by
        rw [hstb, hst1]
        rw [hInv.memEq]
        rw [show (BitVec.toNat mp) = D + 32 * j by
          rw [hmp_eq]; exact ofNat_toNat (by omega)]
      subst hmp_eq
      intro Vp stp op hpost
      obtain ⟨hop, vmp, stmp, heval, hVp, hstp⟩ :=
        exec_one_total_assign_block_inv (funs := hoist (Bridge.Dialect c g)
          [Stmt.letDecl ["pow_of_omega"] (some (Expr.builtin Op.mload
            [Expr.lit (Literal.number aL)]))] :: funs)
          (x := "mptr") (e := Expr.builtin Op.add [Expr.var "mptr", Expr.lit (Literal.number 32)])
          (hne := fun st0 st1 hh => eval_add_var_lit_halt_false hh) hpost
      subst hop
      obtain ⟨amp, hamp, hvmp, hstmp⟩ := eval_add_var_lit_inv heval
      subst hstmp
      subst hVp
      have hampV : VEnv.get Vb "mptr" = some amp := hamp
      rw [hVb] at hampV
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := Vi) (x := "pow_of_omega")
        (y := "mptr") (v := wMulmodAt pw om rw) (by decide)] at hampV
      have hamp_eq : amp = BitVec.ofNat 256 (D + 32 * j) := by
        have hmpV : VEnv.get Vi "mptr" = some (BitVec.ofNat 256 (D + 32 * j)) := hInv.mptr
        exact Option.some.inj (hampV.symm.trans hmpV)
      subst hamp_eq
      have hvmp_eq : vmp = BitVec.ofNat 256 (D + 32 * (j + 1)) := by
        rw [hvmp, ← BitVec.ofNat_add]; congr 1
      subst hvmp_eq
      refine ⟨?_, ?_⟩
      · intro _
        refine ⟨j + 1, storeWord mem' (D + 32 * j)
          (wAddmodAt x (rw - pw) rw), ?_⟩
        have henvNew : VEnv.set Vb "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))) =
            ("pow_of_omega", P (j + 1)) ::
              VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))) := by
          rw [hVb, hInv.env]
          have hval2 : wMulmodAt pw om rw = P (j + 1) := by
            rw [hpw_eq]
            rfl
          rw [hval2]
          rw [second_pass_env_step
            (p := P j) (pw := P (j + 1)) (mp := BitVec.ofNat 256 (D + 32 * j))
            (vmp := BitVec.ofNat 256 (D + 32 * (j + 1)))]
        refine DenomsInv.mk (j := j + 1)
          (mem := storeWord mem' (D + 32 * j) (wAddmodAt x (rw - pw) rw))
          (Nat.succ_le_of_lt hlt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · exact henvNew
        · -- mptr
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "mptr")
            (v := P (j + 1)) (by decide)]
          exact venv_get_set_same (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (v := BitVec.ofNat 256 D)
            (w := BitVec.ofNat 256 (D + 32 * (j + 1))) hmp
        · -- mptr_end
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "mptr_end")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "mptr_end")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hme
        · -- pow
          rw [henvNew]
          rfl
        · -- x
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "x")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "x")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hx
        · -- omega
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "omega")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "omega")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hom
        · -- r
          rw [henvNew, venv_get_cons_ne (D := Bridge.Dialect c g)
            (V := VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (j + 1))))
            (x := "pow_of_omega") (y := "r")
            (v := P (j + 1)) (by decide)]
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (V := V)
            (x := "mptr") (y := "r")
            (v := BitVec.ofNat 256 (D + 32 * (j + 1))) (by decide)]
          exact hrw
        · rw [hstp, hbody_mem]
        · intro i hi
          by_cases hij : i = j
          · subst hij
            rw [loadWord_storeWord_same_at, hpw_eq]
            rfl
          · have hi' : i < j := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hij
            have hdisj : D + 32 * i + 32 ≤ D + 32 * j := by omega
            rw [loadWord_storeWord_at (Or.inl hdisj)]
            exact hInv.written i hi'
        · intro i hji hi
          have hdisj : D + 32 * j + 32 ≤ D + 32 * i := by omega
          rw [loadWord_storeWord_at (Or.inr hdisj)]
          exact hInv.untouched i (by omega) hi
        · intro a ha
          rw [hstp, hstb, hst1, hInv.memEq, ofNat_toNat (by omega)]
          change storeWord mem' (D + 32 * j) (wAddmodAt x (rw - pw) rw) a = st.memory a
          have hstore : storeWord mem' (D + 32 * j) (wAddmodAt x (rw - pw) rw) a = mem' a := by
            apply storeWord_outside
            omega
          rw [hstore, ← hInv.memEq]
          exact hInv.outside a (by omega)
        · rw [hstp, hstb, hst1]
          exact hInv.envSame
        · rw [hstp, hstb, hst1]
          exact hInv.halted
      · intro hop
        exact absurd hop (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
  intro V' st' o hrun
  cases hrun with
  | seqCons hfor hrest =>
      cases hrest with
      | seqNil =>
          cases hfor with
          | forLoop hi hl =>
              have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
                (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
              exact hloop _ _ hi' _ _ _ hl
  | seqStop hfor hne =>
      cases hfor with
      | forLoop hi hl =>
          have hi' := wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi
          exact hloop _ _ hi' _ _ _ hl
      | forInitHalt hi =>
          exact wpSS_sound (Bridge.Dialect c g) (Bopen c g) (Cnone _)
            (Bopen_sound c g) (Cnone_sound _) hinit _ _ _ hi

/-! ## 11. T3.9.g: THE ALG LEAF, FIRST CONJUNCT -/

/-- The `xn` projection of `lag_agrees`, with the D-GATE2-corrected `omegaInvToL` exponent
(`numNegLagranges`, not `numNegLagranges - 1`). -/
theorem lag_agrees_xn (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (s2 : SnapAlgebra p G₁) (hxn : s2.alg.xn = s2.alg.x ^ (2 ^ R.pv.k))
    (W : LagWords)
    (hW : LagRel (BitVec.ofNat 256 p) (Midfall.Halo2.frWord s2.alg.x)
      (Midfall.Halo2.frWord R.vk.domain.omega)
      (Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges))
      (Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)) R.pv.k R.pv.numInstances
      R.pv.numNegLagranges (fun j => Midfall.Halo2.frWord (0 : Fr p)) W) :
    W.xn = Midfall.Halo2.frWord s2.alg.xn := by
  have hp : p < 2 ^ 256 := by
    rw [hR.env.modulus]
    norm_num [Midfall.Generator.frModulusConstant]
  rw [hW.1, wPow2_frWord hp, hxn]

/-! **T3.9.g STATUS (exact residual).** The render-free algebra is landed:
`powVartime_eq_pow`, the entrywise `batchInvert` spec and `lIRange_toList_of_ne_zero`
(`LagrangeAlg.lean`), the `frWord` ring bridge, `wPow2_frWord`, `omegaPows_frWord`,
`rotateOmega_{neg,mul_neg}_range`, `lagWord_eq_frWord`, and `lag_agrees_xn` above.

The remaining assembly is the three value projections (`lLast`, `lBlind`, `l0`) plus the
instance conjunct, and it needs one premise the evidence statement omits: the `inst` array
used by `hW` must be the row `instanceEvalOf` reads. Without a link such as
`s2.alg.instanceEvals.getD 0 #[] = inst`, the last conjunct is FALSE (take `inst := 0` and a
`snapshotLagrangeStep` whose selected `instanceEval` is nonzero). This is a missing LEAF
premise (like `hl`/`hxn`), not a row hypothesis; the next lane must add it and document it.
-/

/-! ## 12. T3.9.g: CANONICAL WORDS, INVERSES AND THE ROTATION INDEX -/

theorem frWord_inj {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256) :
    Function.Injective (Midfall.Halo2.frWord (p := p)) := by
  intro a b h
  apply ZMod.val_injective p
  have := congrArg BitVec.toNat h
  rwa [Midfall.Halo2.frWord_toNat hp, Midfall.Halo2.frWord_toNat hp] at this

theorem wMulmodAt_zero_right (a r : U256) : wMulmodAt a 0 r = 0 := by
  simp [wMulmodAt]

theorem wMulmodAt_zero_left (a r : U256) : wMulmodAt 0 a r = 0 := by
  simp [wMulmodAt]

theorem wMulmodAt_eq_one_field {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    {iw dw : U256} {iF dF : Fr p}
    (hi : iw = Midfall.Halo2.frWord iF) (hd : dw = Midfall.Halo2.frWord dF)
    (h : wMulmodAt iw dw (BitVec.ofNat 256 p : U256) = 1) : iF * dF = 1 := by
  apply frWord_inj hp
  rw [frWord_mul hp, ← hi, ← hd, h, frWord_one]

/-- The rotations `lagrangeTriple` uses, indexed by `L = numNegLagranges`. -/
def gRots (L : Nat) : List Int :=
  List.map (fun i => -((L : Nat) : Int) + (i : Int))
    (List.flatMap (fun a => pure ((a : Nat) : Int)) (List.range (L + 1)))

theorem gRots_length (L : Nat) : (gRots L).length = L + 1 := by
  simp [gRots, List.length_map, List.length_range]

theorem gRots_mem {L : Nat} {r : Int} :
    r ∈ gRots L ↔ ∃ i, i ≤ L ∧ r = -((L : Nat) : Int) + (i : Int) := by
  unfold gRots
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [List.mem_flatMap] at ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [List.mem_range] at hb
    have hba : a = ((b : Nat) : Int) := by simpa using hab
    exact ⟨b, by omega, by rw [hba]⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨((i : Nat) : Int), ?_, rfl⟩
    rw [List.mem_flatMap]
    exact ⟨i, by rw [List.mem_range]; omega, by simp⟩

theorem gRots_get? (L i : Nat) :
    (gRots L)[i]? = if i ≤ L then some (-((L : Nat) : Int) + (i : Int)) else none := by
  by_cases hi : i ≤ L
  · rw [if_pos hi]
    unfold gRots
    rw [flatMap_pure, List.map_map, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rw [if_neg hi]
    rw [List.getElem?_eq_none_iff, gRots_length]
    omega

/-! **T3.9.g SNAPSHOT/INSTANCE GAP (discovered).** `l.instanceEval` is
`instanceEvalOf vk s2.alg`, which selects one entry of `s2.alg.instanceEvals`; for a public
column that entry is `computeInnerProduct col slice` (`Verifier.lean:893-920`). The evidence's
`hW` is stated over a *separate* `inst : Array (Fr p)`. A link
`s2.alg.instanceEvals.getD 0 #[] = inst` is necessary but NOT sufficient: the selected entry is
an inner product of `inst` against the `lIS` slice, not `inst i`. The leaf therefore also needs
the snapshot/query linkage (selected public query at rotation 0, its column is `inst`, and its
`instanceEvals` entry is `computeInnerProduct inst (slice of lIS)`). This is a leaf premise,
not a row hypothesis; the evidence statement omitted it. `hn : 1 ≤ numInstances` is also
needed for the `i = m` inverse (`LagRel` only covers `i < n + m`); without it `l0` can differ
from `L m` when `x - 1 ≠ 0`. -/

theorem wSum_eq_foldl (r : U256) (f : Nat → U256) (n : Nat) (acc : U256) :
    wSum r f n acc = (List.range n).foldl (fun a i => wAddmodAt a (f i) r) acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      rw [wSum, ih, List.range_succ, List.foldl_append]
      simp

theorem frWord_foldl_add {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    (xs : List (Fr p)) (a : Fr p) :
    Midfall.Halo2.frWord (xs.foldl (· + ·) a) =
      xs.foldl (fun acc x => wAddmodAt acc (Midfall.Halo2.frWord x)
        (BitVec.ofNat 256 p : U256)) (Midfall.Halo2.frWord a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (a + x), frWord_add hp]


/-- The two value projections of `lag_agrees` (D-GATE2 exponent): `lLast` and `l0`.
`hn` is the leaf premise `1 ≤ numInstances` (the `LagRel` inverse clause covers `i < n + m`);
`hinst` is recorded for the eventual instance conjunct. -/
theorem lag_agrees_lLast_l0 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (hm : 2 ≤ R.pv.numNegLagranges) (hn : 1 ≤ R.pv.numInstances)
    (s2 : SnapAlgebra p G₁) (l : SnapLagrange p G₁)
    (hl : snapshotLagrangeStep (G₁ := G₁) R.vk s2 = .ok l)
    (hxn : s2.alg.xn = s2.alg.x ^ (2 ^ R.pv.k))
    (inst : Array (Fr p)) (W : LagWords)
    (hinst : s2.alg.instanceEvals.getD 0 #[] = inst)
    (hW : LagRel (BitVec.ofNat 256 p) (Midfall.Halo2.frWord s2.alg.x)
      (Midfall.Halo2.frWord R.vk.domain.omega)
      (Midfall.Halo2.frWord (R.vk.domain.omegaInv ^ R.pv.numNegLagranges))
      (Midfall.Halo2.frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)) R.pv.k R.pv.numInstances
      R.pv.numNegLagranges (fun j => Midfall.Halo2.frWord (inst.getD j 0)) W) :
    W.lLast = Midfall.Halo2.frWord l.lagrange.lLast ∧
      W.l0 = Midfall.Halo2.frWord l.lagrange.l0 := by
  have hp : p < 2 ^ 256 := by
    rw [hR.env.modulus]
    norm_num [frModulusConstant]
  -- Destruct the snapshot step and the triple.
  obtain ⟨tri, htri, hltri, hlinst⟩ := snapshotLagrangeStep_ok (G := G₁) R.vk s2 hl
  -- The blinding factors.
  cases hbf : R.vk.cs.blindingFactors with
  | error e =>
      unfold lagrangeTriple at htri
      rw [hbf] at htri
      dsimp only [Bind.bind, Except.bind] at htri
      simp at htri
  | ok bf =>
      have hneg : R.pv.numNegLagranges = bf + 1 := by
        have h := hR.env.negLagranges
        rw [hbf] at h
        simp [Except.toOption] at h
        exact h
      obtain ⟨hsize, hLast, hBlind, h0⟩ :=
        lagrangeTriple_ok (G := G₁) R.vk s2.alg.x s2.alg.xn hbf htri
      -- `hW` at the same `m = bf+1`.
      rw [hneg] at hW
      obtain ⟨hxnW, inv, hinv, hWlast, hW0, hWblind, hWinst⟩ := hW
      -- Fields and words.
      let xF : Fr p := s2.alg.x
      let xnF : Fr p := s2.alg.xn
      let nInvF : Fr p := (((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹
      let ivF : Nat → Fr p := fun i => ((inv i).toNat : Fr p)
      let rw : U256 := BitVec.ofNat 256 p
      let w0 : U256 := frWord (R.vk.domain.omegaInv ^ (bf + 1))
      let omF : Fr p := R.vk.domain.omega
      let wiF : Fr p := R.vk.domain.omegaInv
      have hxnW' : W.xn = frWord xnF := by
        dsimp only [xnF, xF]
        rw [hxnW, hxn]
        exact wPow2_frWord hp s2.alg.x R.pv.k
      -- The canonical word `inv i` and its field inverse.
      have hivWord (i : Nat) (hi : i < R.pv.numInstances + (bf + 1)) :
          inv i = frWord (ivF i) := by
        exact (frWord_ofNat_toNat hp (w := inv i) (by
          have h := (hinv i hi).2
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] at h)).symm
      have hivField (i : Nat) (hile : i ≤ bf + 1) :
          ivF i * (s2.alg.x - (wiF ^ (bf + 1) * omF ^ i)) = 1 := by
        dsimp only [wiF, omF]
        have hiW : i < R.pv.numInstances + (bf + 1) := by omega
        have hd : wAddmodAt (frWord s2.alg.x)
            (BitVec.ofNat 256 p - omegaPows (BitVec.ofNat 256 p) (frWord R.vk.domain.omega)
              (frWord (R.vk.domain.omegaInv ^ (bf + 1))) i)
            (BitVec.ofNat 256 p) = frWord (s2.alg.x - (wiF ^ (bf + 1) * omF ^ i)) := by
          rw [omegaPows_frWord hp omF (wiF ^ (bf + 1)) i]
          rw [frWord_sub hp]
        exact wMulmodAt_eq_one_field hp (hivWord i hiW) hd (hinv i hiW).1
      have hivEq (i : Nat) (hile : i ≤ bf + 1) :
          ivF i = (s2.alg.x - (wiF ^ (bf + 1) * omF ^ i))⁻¹ :=
        eq_inv_of_mul_eq_one_left (hivField i hile)
      -- Every denominator in the rotation list is non-zero.
      have hdenAll : ∀ r ∈ gRots (bf + 1),
          s2.alg.x - R.vk.domain.rotateOmega 1 (Rotation.value r) ≠ 0 := by
        intro r hr
        rw [gRots_mem] at hr
        obtain ⟨i, hile, rfl⟩ := hr
        rw [rotateOmega_neg_range (d := R.vk.domain) hile]
        have hneq : s2.alg.x - (wiF ^ (bf + 1) * omF ^ i) ≠ 0 := by
          intro hzero
          have h := hivField i hile
          rw [hzero, mul_zero] at h
          exact zero_ne_one h
        rwa [omegaInv_pow_mul_omega_pow (h := hR.env.omegaInvMul) (L := bf + 1) (i := i) hile] at hneq
      -- The lIRange value at index `i`, at field level.
      have hEval (i : Nat) (hile : i ≤ bf + 1) :
          (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1))).toList[i]? =
            some (ivF i * ((s2.alg.xn - 1) * nInvF) * (wiF ^ (bf + 1) * omF ^ i)) := by
        have hget := lIRange_toList_get? R.vk.domain s2.alg.x s2.alg.xn (gRots (bf + 1)) i hdenAll
        rw [hget, gRots_get? (bf + 1) i, if_pos hile]
        simp only [Option.map_some]
        congr 1
        rw [rotateOmega_mul_neg_range (d := R.vk.domain) (v := (s2.alg.x -
            R.vk.domain.rotateOmega 1 (Rotation.value (-((bf + 1 : Nat) : Int) + (i : Int))))⁻¹ *
            ((s2.alg.xn - 1) * R.vk.domain.barycentricWeight))
            (L := bf + 1) (i := i) hile]
        rw [rotateOmega_neg_range (d := R.vk.domain) (L := bf + 1) (i := i) hile]
        rw [hivEq i hile, hR.env.baryWeight]
        rw [show wiF ^ (bf + 1) * omF ^ i = wiF ^ ((bf + 1) - i) from
          omegaInv_pow_mul_omega_pow (h := hR.env.omegaInvMul) (L := bf + 1) (i := i) hile]
      have hE0 : (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1)))[0]! =
          ivF 0 * ((s2.alg.xn - 1) * nInvF) * (wiF ^ (bf + 1) * omF ^ 0) := by
        have hsize' : (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1))).size = bf + 2 := by
          simpa only [gRots] using hsize
        have h0lt : 0 < (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1))).size := by omega
        rw [getElem!_pos _ 0 h0lt]
        rw [← Array.getElem_toList (h := by simpa using h0lt)]
        obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp (hEval 0 (by omega))
        exact hval
      have hEL : (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1)))[bf + 1]! =
          ivF (bf + 1) * ((s2.alg.xn - 1) * nInvF) * (wiF ^ (bf + 1) * omF ^ (bf + 1)) := by
        have h0lt : bf + 1 < (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1))).size := by
          have hsize' : (R.vk.domain.lIRange s2.alg.x s2.alg.xn (gRots (bf + 1))).size = bf + 2 := by
            simpa only [gRots] using hsize
          omega
        rw [getElem!_pos _ (bf + 1) h0lt]
        rw [← Array.getElem_toList (h := by simpa using h0lt)]
        obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp (hEval (bf + 1) (by omega))
        exact hval
      refine ⟨?_, ?_⟩
      · -- lLast
        rw [hltri, hLast, hWlast]
        dsimp only
        rw [lagWord_eq_frWord hp (xnW := W.xn) (xnF := s2.alg.xn)
          (nInvW := frWord nInvF) (nInvF := nInvF)
          (invW := inv 0) (invF := ivF 0)
          (omW := omegaPows (BitVec.ofNat 256 p) (frWord R.vk.domain.omega)
            (frWord (R.vk.domain.omegaInv ^ (bf + 1))) 0)
          (omF := wiF ^ (bf + 1) * omF ^ 0)
          hxnW' rfl (hivWord 0 (by omega))
          (omegaPows_frWord hp omF (wiF ^ (bf + 1)) 0)]
        apply (frWord_inj hp).eq_iff.mpr
        dsimp only [gRots] at hE0 ⊢
        rw [hE0]
        ring
      · -- l0
        rw [hltri, h0, hW0]
        dsimp only
        rw [lagWord_eq_frWord hp (xnW := W.xn) (xnF := s2.alg.xn)
          (nInvW := frWord nInvF) (nInvF := nInvF)
          (invW := inv (bf + 1)) (invF := ivF (bf + 1))
          (omW := omegaPows (BitVec.ofNat 256 p) (frWord R.vk.domain.omega)
            (frWord (R.vk.domain.omegaInv ^ (bf + 1))) (bf + 1))
          (omF := wiF ^ (bf + 1) * omF ^ (bf + 1))
          hxnW' rfl (hivWord (bf + 1) (by omega))
          (omegaPows_frWord hp omF (wiF ^ (bf + 1)) (bf + 1))]
        apply (frWord_inj hp).eq_iff.mpr
        dsimp only [gRots] at hEL ⊢
        rw [hEL]
        ring

