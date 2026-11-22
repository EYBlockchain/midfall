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
--   * T3.9.b 'lag_denoms_loop' - the shared denominator window;
--   * T3.9.d 'lag_lblind_loop' - the blind sum (the cheapest independent leaf).
-- The remaining children (T3.9.c/e/g/h) and the row glue are NOT in this file. Nothing here is
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
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Yul.LoopRule
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

set_option autoImplicit false

namespace Midfall.LoweringV3.LagrangeRows

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst
open Midfall.LoweringV3.QuotientRows
open Midfall.Yul.Wp Midfall.Yul.LoopRule Midfall.Yul.WpBridge

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
        simp [VEnv.set, VEnv.get, List.find?]
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
