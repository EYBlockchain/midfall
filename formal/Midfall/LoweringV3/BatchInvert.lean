-- |
-- Midfall.LoweringV3.BatchInvert
--
-- A5 (HLP.1.b / HLP.1.c), RENDER-FREE: the vocabulary, the two loop FORM lemmas, the window and
-- arithmetic facts the two `for` loops of `batch_invert` need, and the exact PREMISE GAP that stops
-- the loop statements at this tip. PORTED from
-- 'docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean' sections 2-3 (:298-359), which does
-- not compile in the tree (RECON.3) - a copy, not an import, exactly as LagrangeRows.lean does
-- for T3.9.
--
-- WHAT THIS FILE IS. A5's deliverable is the pair of symbolic loops of the emitted helper
-- 'batch_invert' and the helper's all-runs summary:
--   * HLP.1.b 'bi_forward_loop'  (forward prefix-product pass, evidence :336-359);
--   * HLP.1.c 'bi_backward_loop' (the backward recovery pass, NOT stated in the evidence);
--   * HLP.1.c 'batch_invert_summary' (evidence :317-330) over 'BatchInvertPost' (:300-311).
-- This file lands the parts of that work that are TRUE AND PROVED at this tip:
--   (a) 'helperBody' (evidence :132-135) and its 34-statement length at every table;
--   (b) the two loop FORM lemmas, by kernel reduction at every table ('kernel_rfl', no axiom);
--   (c) 'BatchInvertPost' ported verbatim except the evidence's three-argument 'wMulmod', which the
--       tree spells 'wMulmodAt' (LagrangeRows header, port change (a); 'wMulmod' in this tree is
--       the two-argument fixed-at-Fr one, 'WpX.wMulmod');
--   (d) the forward pass's word algebra: 'fwdProd'/'fwdWords' (the evidence's 'P'), the
--       read-over-window lemma for its stores, and the field fact that a product of two canonical
--       words is zero only when a factor is ('wMulmodAt_eq_zero_iff');
--   (e) the exact PG-BATCHINVERT record at the end of the file.
--
-- WHY THE TWO LOOP THEOREMS ARE NOT IN THIS FILE. The evidence's 'bi_forward_loop' is FALSE AS
-- STATED: its pre gives 'VEnv.get V "gp" = some (loadWord st.memory a)' and NOTHING about whether
-- that word is canonical, while its post demands
-- 'a + 32 * 0 + 32 < e -> (loadWord st.memory a).toNat < rw.toNat'. The loop never reads word 0
-- (its cursor starts at 'mptr = a + 32'), so at 'a = 0, e = 64, rw = 7, loadWord st.memory a = 10'
-- the loop runs ZERO times (the guard is '32 < 64 - 32', false) and the post's 'i = 0' clause is
-- '10 < 7'. The missing premise is the statement-9 guard of the emitter
-- ('if iszero(lt(gp, r)) { ret := 0; leave }', GenAst.lean:498), which the caller has but the
-- evidence's pre does not carry; with
--   '(loadWord st.memory a).toNat < rw.toNat'
-- added to the pre the statement is true (and the caller below discharges it). An arm lemma's pre
-- may be strengthened (W12: no row/bundle/root hypothesis was touched); it is recorded as
-- PG-BATCHINVERT(1) instead of silently restated.
--
-- The summary is additionally missing a lemma the tree does not have at an ARBITRARY prime: the
-- modexp frame of the helper is 'blsR'-shaped in 'modexpInvFrame', and the byte-parse +
-- 'modPow_inv' proof in 'Assumptions/Eip2537.lean:825' ('modexpInv_correct') is stated and proved
-- for 'blsR' only, with all its slice plumbing 'private'. 'batch_invert_summary' is generic in
-- 'rw' with only 'Nat.Prime rw.toNat', so the parse must be re-proved for the parameterised frame
-- before the staticcall's honest answer can be identified with the inverse. PG-BATCHINVERT(2).
--
-- NO FIXTURE (D-P71). Every statement is quantified over the table and the bounds.
--
-- AXIOMS. Everything proved here is on the standard three or fewer; no 'sorryAx', no
-- 'native_decide' (D-P17), no 'maxHeartbeats' or 'maxRecDepth' raise. The 'kernel_rfl' lemmas are
-- Eq.refl and use none.
import Midfall.LoweringV3.LagrangeRows

set_option autoImplicit false

namespace Midfall.LoweringV3.BatchInvert

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst
open Midfall.LoweringV3.QuotientRows
open Midfall.LoweringV3.LagrangeRows
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.LoopRule Midfall.Yul.WpTac

variable {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. THE HELPER BODY (evidence :132-135) -/

/-- The single function body an emitter prints, constants inlined (a helper's code). VERBATIM
(evidence :132-135). The match is the definition: it does NOT reduce the inliner, it names the body
the inliner produced, which is what lets every statement below be quantified over the TABLE. -/
def helperBody (consts : Inline.Consts) (emit : Block EVM.Op) : Block EVM.Op :=
  match Inline.inlineContractConstants consts emit with
  | [Stmt.funDef _ _ _ body] => body
  | _ => []

/-- **THE BODY IS 34 TOP-LEVEL STATEMENTS, AT EVERY TABLE.** PROVED by kernel reduction
('kernel_rfl', no axiom): the inliner may turn 'MODEXP_GAS' into a literal, but it neither adds nor
drops a statement of the helper. This is the count the card reads
('THIRTY-FOUR top-level statements', GenAst.lean:456). -/
theorem helperBody_length (consts : Inline.Consts) :
    (helperBody consts GenAst.emitBatchInvertAt).length = 34 := by
  kernel_rfl

/-! ## 2. THE TWO LOOP FORMS (by kernel reduction, at every table)

  Statement 10 of the body is the forward pass and statement 29 the backward pass (0-based; the
  evidence's HLP.1.b cites "10" for the forward loop and HLP.1.c's statement 29 is the backward
  loop). Both are independent of the table: 'MODEXP_GAS' is the only name the backend interpolates
  that the inliner can touch, and it occurs in statement 21 (the staticcall), not in either loop. -/

/-- Statement 10 of the helper body, at EVERY table: the forward prefix-product walk. PROVED by
kernel reduction. -/
theorem bi_forward_loop_form (consts : Inline.Consts) :
    seg (helperBody consts GenAst.emitBatchInvertAt) 10 1 =
      [GenAst.yfor []
        (GenAst.yop EVM.Op.lt [GenAst.yvar "mptr",
          GenAst.yop EVM.Op.sub [GenAst.yvar "mptr_end", GenAst.ylit 0x20]])
        []
        [ GenAst.ylet "x" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr"])
        , GenAst.yif (GenAst.yop EVM.Op.iszero
            [GenAst.yop EVM.Op.lt [GenAst.yvar "x", GenAst.yvar "r"]])
            [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave]
        , GenAst.yset "gp"
            (GenAst.yop EVM.Op.mulmod [GenAst.yvar "gp", GenAst.yvar "x", GenAst.yvar "r"])
        , GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "gp_mptr", GenAst.yvar "gp"])
        , GenAst.yset "mptr" (GenAst.yop EVM.Op.add [GenAst.yvar "mptr", GenAst.ylit 0x20])
        , GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.add
            [GenAst.yvar "gp_mptr", GenAst.ylit 0x20]) ]] := by
  kernel_rfl

/-- Statement 29 of the helper body, at EVERY table: the backward recovery walk. PROVED by kernel
reduction. This is the LOOP THE EVIDENCE NEVER STATES (HLP.1.c's statement is absent from
'GeneratorRows.lean'); it is named here so the statement and its bound live in the tree even while
the proof is blocked on PG-BATCHINVERT(2). -/
theorem bi_backward_loop_form (consts : Inline.Consts) :
    seg (helperBody consts GenAst.emitBatchInvertAt) 29 1 =
      [GenAst.yfor []
        (GenAst.yop EVM.Op.lt [GenAst.yvar "second_mptr", GenAst.yvar "mptr"])
        []
        [ GenAst.ylet "inv" (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar "all_inv", GenAst.yop EVM.Op.mload [GenAst.yvar "gp_mptr"],
              GenAst.yvar "r"])
        , GenAst.yset "all_inv" (GenAst.yop EVM.Op.mulmod
            [GenAst.yvar "all_inv", GenAst.yop EVM.Op.mload [GenAst.yvar "mptr"],
              GenAst.yvar "r"])
        , GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "mptr", GenAst.yvar "inv"])
        , GenAst.yset "mptr" (GenAst.yop EVM.Op.sub [GenAst.yvar "mptr", GenAst.ylit 0x20])
        , GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.sub
            [GenAst.yvar "gp_mptr", GenAst.ylit 0x20]) ]] := by
  kernel_rfl

/-! ## 3. THE SUMMARY'S POST (evidence :298-311) -/

/-- What `batch_invert(success, a, e, s, r)` leaves behind, at word level. `ret ≠ 0` means every
    word of `[a, e)` was canonical and non-zero and now holds its inverse modulo `r`. VERBATIM from
    the evidence (:300-311), with the evidence's three-argument `wMulmod` renamed `wMulmodAt`
    (LagrangeRows header port change (a)). -/
def BatchInvertPost (st : EvmState) (succ : U256) (a e s : Nat) (rw : U256)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) : Prop :=
  ∃ ret pf, VEnv.get V' "ret" = some ret ∧ VEnv.get V' "precompile_failed" = some pf ∧
    st'.env = st.env ∧ st'.halted = st.halted ∧
    (∀ x, (x < a ∨ e ≤ x) → (x < s ∨ s + (e - a) + 0xc0 ≤ x) → st'.memory x = st.memory x) ∧
    (succ = 0 → ret = 0 ∧ pf = 0 ∧ st'.memory = st.memory) ∧
    (pf ≠ 0 → ret = 0) ∧
    (ret ≠ 0 → pf = 0 ∧ ∀ i, a + 32 * i < e →
      (loadWord st.memory (a + 32 * i)).toNat < rw.toNat ∧
      loadWord st.memory (a + 32 * i) ≠ 0 ∧
      (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat ∧
      wMulmodAt (loadWord st'.memory (a + 32 * i)) (loadWord st.memory (a + 32 * i)) rw = 1)

/-! ## 4. THE FORWARD PASS'S WORD ALGEBRA (the evidence's `P`, :354-358)

  The evidence states its prefix product as an existential `P : Nat → U256` with
  `P 0 = loadWord st.memory a` and `P (i+1) = wMulmod (P i) (loadWord st.memory (a + 32*(i+1))) rw`.
  The named function below is that family, so both loop invariants and the summary can refer to it
  without re-quantifying. -/

/-- The prefix product after `i` steps: `P 0 = w₀`, `P (i+1) = P i * w_{i+1}` modulo `rw`. VERBATIM
shape from the evidence (:354-357), named so the invariant is a function rather than an
existential. -/
def fwdProd (mem : Nat → UInt8) (a : Nat) (rw : U256) : Nat → U256
  | 0 => loadWord mem a
  | i + 1 => wMulmodAt (fwdProd mem a rw i) (loadWord mem (a + 32 * (i + 1))) rw

/-- The value the forward loop stores at scratch word `i`: it has folded `w₀ … w_{i+1}`, i.e.
`fwdProd … (i+1)`. -/
def fwdWords (mem : Nat → UInt8) (a : Nat) (rw : U256) (i : Nat) : U256 :=
  fwdProd mem a rw (i + 1)

/-- The definition's own equation, as a rewrite rule. -/
theorem fwdProd_succ (mem : Nat → UInt8) (a : Nat) (rw : U256) (i : Nat) :
    fwdProd mem a rw (i + 1) =
      wMulmodAt (fwdProd mem a rw i) (loadWord mem (a + 32 * (i + 1))) rw := rfl

/-- The definition's equation for the value the loop stores. -/
theorem fwdWords_eq (mem : Nat → UInt8) (a : Nat) (rw : U256) (i : Nat) :
    fwdWords mem a rw i =
      wMulmodAt (fwdProd mem a rw i) (loadWord mem (a + 32 * (i + 1))) rw := rfl

/-- Reading a word after `j` stores at `D, D+32, …` is reading the ORIGINAL memory when the
32-byte window is disjoint from `[D, D + 32j)`. Lifts `writeWords_outside` (LagrangeRows) from
bytes to words: this is the fact that lets the forward loop read the batch while writing scratch,
and the reason the summary's `hdisj` is load-bearing. -/
theorem loadWord_writeWords_outside (mem : Nat → UInt8) (D : Nat) (f : Nat → U256)
    {j q : Nat} (h : q + 32 ≤ D ∨ D + 32 * j ≤ q) :
    loadWord (writeWords mem D f j) q = loadWord mem q := by
  refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
  exact writeWords_outside mem D f (j := j) (a := q + i) (by omega)

/-- **A PRODUCT OF TWO CANONICAL WORDS IS ZERO ONLY WHEN A FACTOR IS.** For prime `r` and
`x, y < r`, EVM `mulmod x y r` vanishes exactly at a zero factor. This is the bridge from the
forward pass's `iszero(gp)` guard to the summary's "every word of `[a,e)` is non-zero" clause,
and it is where `Nat.Prime rw.toNat` enters (no other step of the loops needs primality). -/
theorem wMulmodAt_eq_zero_iff {r x y : U256} (hp : Nat.Prime r.toNat)
    (hx : x.toNat < r.toNat) (hy : y.toNat < r.toNat) :
    wMulmodAt x y r = 0 ↔ x = 0 ∨ y = 0 := by
  have hr : r ≠ 0 := by
    intro h
    exact hp.ne_zero (by rw [h]; rfl)
  rw [wMulmodAt, ite_eq_right hr]
  have hlt : r.toNat < 2 ^ 256 := by
    have := BitVec.isLt r
    simpa using this
  have hm : (x.toNat * y.toNat) % r.toNat < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_lt hlt)
  have hof : (BitVec.ofNat 256 ((x.toNat * y.toNat) % r.toNat) = (0 : U256)) ↔
      (x.toNat * y.toNat) % r.toNat = 0 := by
    constructor
    · intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at hh
      simpa using hh
    · intro h
      rw [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, h]
      rfl
  rw [hof]
  constructor
  · intro h
    have hd : r.toNat ∣ x.toNat * y.toNat := Nat.dvd_of_mod_eq_zero h
    rcases (hp.dvd_mul).mp hd with hdx | hdy
    · left
      rw [show x = 0 ↔ x.toNat = 0 by
        simpa using (BitVec.toNat_eq (x := x) (y := (0 : U256)))]
      exact Nat.eq_zero_of_dvd_of_lt hdx hx
    · right
      rw [show y = 0 ↔ y.toNat = 0 by
        simpa using (BitVec.toNat_eq (x := y) (y := (0 : U256)))]
      exact Nat.eq_zero_of_dvd_of_lt hdy hy
  · rintro (rfl | rfl) <;> simp


/-- A non-zero modulus makes `mulmod` canonical: the result is `< r`. This is what turns the
backward pass's stored inverses into the summary's "output word `< r`" clause. -/
theorem wMulmodAt_toNat_lt {r a b : U256} (hr : r ≠ 0) :
    (wMulmodAt a b r).toNat < r.toNat := by
  have hrpos : 0 < r.toNat := by
    have h : r.toNat ≠ 0 := by
      intro h0
      exact hr (BitVec.eq_of_toNat_eq (by simpa using h0))
    omega
  rw [wMulmodAt, ite_eq_right hr]
  rw [BitVec.toNat_ofNat]
  have hlt : r.toNat < 2 ^ 256 := by simpa using BitVec.isLt r
  have := Nat.mod_lt (a.toNat * b.toNat) hrpos
  omega

/-- The non-zero form the summary's `ret ≠ 0` arm consumes. -/
theorem wMulmodAt_ne_zero_iff {r x y : U256} (hp : Nat.Prime r.toNat)
    (hx : x.toNat < r.toNat) (hy : y.toNat < r.toNat) :
    wMulmodAt x y r ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  rw [Ne, wMulmodAt_eq_zero_iff hp hx hy, not_or]


/-- **ASSOCIATIVITY OF EVM `mulmod` AT A NON-ZERO MODULUS.** For any `a b c` and `r ≠ 0`,
`(a*b mod r)*c mod r = a*(b*c mod r) mod r`: both sides are `(a*b*c) mod r`. This is the one
arithmetic fact the backward pass needs (it multiplies the running inverse by a word and then by
the next), and it is stated at any non-zero `r` - prime is not needed for this step. PROVED from
`Nat.mod_mul_mod` / `Nat.mul_mod_mod` (`Init/Data/Nat/Lemmas.lean`). -/
theorem wMulmodAt_assoc {r a b cc : U256} (hr : r ≠ 0) :
    wMulmodAt (wMulmodAt a b r) cc r = wMulmodAt a (wMulmodAt b cc r) r := by
  have hrpos : 0 < r.toNat := by
    have h : r.toNat ≠ 0 := by
      intro h0
      exact hr (BitVec.eq_of_toNat_eq (by simpa using h0))
    omega
  rw [wMulmodAt, ite_eq_right hr, wMulmodAt, ite_eq_right hr,
    wMulmodAt, ite_eq_right hr, wMulmodAt, ite_eq_right hr]
  apply BitVec.eq_of_toNat_eq
  have hbc : (b.toNat * cc.toNat) % r.toNat < 2 ^ 256 := by
    have := Nat.mod_lt (b.toNat * cc.toNat) hrpos
    have := BitVec.isLt r
    omega
  have hab : (a.toNat * b.toNat) % r.toNat < 2 ^ 256 := by
    have := Nat.mod_lt (a.toNat * b.toNat) hrpos
    have := BitVec.isLt r
    omega
  have h2 : ((a.toNat * b.toNat) % r.toNat * cc.toNat) % r.toNat < 2 ^ 256 := by
    have := Nat.mod_lt (((a.toNat * b.toNat) % r.toNat) * cc.toNat) hrpos
    have := BitVec.isLt r
    omega
  have h4 : (a.toNat * ((b.toNat * cc.toNat) % r.toNat)) % r.toNat < 2 ^ 256 := by
    have := Nat.mod_lt (a.toNat * ((b.toNat * cc.toNat) % r.toNat)) hrpos
    have := BitVec.isLt r
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbc, Nat.mod_eq_of_lt hab,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h4]
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-! ## 4b. THE FORWARD LOOP (HLP.1.b), WITH THE STATEMENT-9 CANONICALITY PRE

  The evidence's pre (`GeneratorRows.lean:342`) omits the statement-9 guard's result; `bi_forward_loop`
  below carries it as `(loadWord st.memory a).toNat < rw.toNat` (an ARM-LEMMA pre, never a row,
  bundle or root). The invariant is the environment EQUATION `V' = fwdEnv ... j`, which is what
  makes the next iteration's guard and body reduce. `fwdEnv` and its six `get` lemmas are the
  bookkeeping; `restore_x_sets` is the body-block exit. -/

def fwdEnv (mem : Nat → UInt8) (a s : Nat) (rw : U256) (V : VEnv (Bridge.Dialect c g)) :
    Nat → VEnv (Bridge.Dialect c g)
  | 0 => V
  | j + 1 => VEnv.set (VEnv.set (VEnv.set (fwdEnv mem a s rw V j) "gp"
      (fwdProd mem a rw (j + 1))) "mptr" (BitVec.ofNat 256 (a + 32 + 32 * (j + 1))))
      "gp_mptr" (BitVec.ofNat 256 (s + 32 * (j + 1)))

theorem fwdEnv_length (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (j : Nat) :
    (fwdEnv mem a s rw V j).length = V.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [fwdEnv, venv_set_length (D := Bridge.Dialect c g), ih]

theorem fwdEnv_get_mptr (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (hmptr : VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32)))
    (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "mptr" = some (BitVec.ofNat 256 (a + 32 + 32 * j)) := by
  induction j with
  | zero => simp only [fwdEnv]; exact hmptr
  | succ j ih =>
      simp only [fwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr") (by decide)]
      refine venv_get_set_same (D := Bridge.Dialect c g)
        (v := BitVec.ofNat 256 (a + 32 + 32 * j))
        (w := BitVec.ofNat 256 (a + 32 + 32 * (j + 1))) ?_
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr") (by decide)]
      exact ih

theorem fwdEnv_get_mptr_end (mem : Nat → UInt8) (a s : Nat) (rw : U256) (me : U256)
    (V : VEnv (Bridge.Dialect c g)) (h : VEnv.get V "mptr_end" = some me) (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "mptr_end" = some me := by
  induction j with
  | zero => simp only [fwdEnv]; exact h
  | succ j ih =>
      simp only [fwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr_end") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "mptr_end") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr_end") (by decide)]
      exact ih

theorem fwdEnv_get_r (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (h : VEnv.get V "r" = some rw) (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "r" = some rw := by
  induction j with
  | zero => simp only [fwdEnv]; exact h
  | succ j ih =>
      simp only [fwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "r") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "r") (by decide)]
      exact ih

theorem fwdEnv_get_ret (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "ret" = VEnv.get V "ret" := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [fwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "ret") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "ret") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "ret") (by decide)]
      exact ih

theorem fwdEnv_get_gp (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (h : VEnv.get V "gp" = some (fwdProd mem a rw 0)) (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "gp" = some (fwdProd mem a rw j) := by
  induction j with
  | zero => simp only [fwdEnv]; exact h
  | succ j ih =>
      simp only [fwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "gp") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp") (by decide)]
      exact venv_get_set_same (D := Bridge.Dialect c g)
        (v := fwdProd mem a rw j) (w := fwdProd mem a rw (j + 1)) ih

theorem fwdEnv_get_gp_mptr (mem : Nat → UInt8) (a s : Nat) (rw : U256)
    (V : VEnv (Bridge.Dialect c g)) (h : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 s)) (j : Nat) :
    VEnv.get (fwdEnv mem a s rw V j) "gp_mptr" = some (BitVec.ofNat 256 (s + 32 * j)) := by
  induction j with
  | zero => simp only [fwdEnv]; exact h
  | succ j ih =>
      simp only [fwdEnv]
      exact venv_get_set_same (D := Bridge.Dialect c g)
        (v := BitVec.ofNat 256 (s + 32 * j))
        (w := BitVec.ofNat 256 (s + 32 * (j + 1))) (by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
            venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "gp_mptr") (by decide)]
          exact ih)

theorem ult_true_of_b2w_ne {x y : U256} (h : b2w (x.ult y) ≠ 0) : x.toNat < y.toNat := by
  cases hx : x.ult y with
  | true => simpa [BitVec.ult] using hx
  | false => exact absurd (by rw [hx]; rfl) h

theorem lt_of_iszero_eq_zero {x y : U256}
    (h : b2w (decide (b2w (x.ult y) = 0)) = (0 : U256)) : x.toNat < y.toNat := by
  have h1 : decide (b2w (x.ult y) = 0) = false := (b2w_eq_zero_iff _).mp h
  have h2 : b2w (x.ult y) ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  exact ult_true_of_b2w_ne h2

theorem restore_reject_ret (V Vi : VEnv (Bridge.Dialect c g)) (xv r : U256)
    (hl : Vi.length = V.length) :
    restore V (restore Vi (restore (("x", xv) :: Vi)
      (VEnv.set (("x", xv) :: Vi) "ret" r))) = VEnv.set Vi "ret" r := by
  simp [restore, VEnv.set, venv_set_length (D := Bridge.Dialect c g), hl]

theorem get_cons_self_x (V : VEnv (Bridge.Dialect c g)) (v : U256) :
    VEnv.get (("x", v) :: V) "x" = some v := rfl

theorem get_set_gp_same {V : VEnv (Bridge.Dialect c g)} {xv gv u : U256}
    (h : VEnv.get V "gp" = some u) :
    VEnv.get (VEnv.set (("x", xv) :: V) "gp" gv) "gp" = some gv := by
  rw [show VEnv.set (("x", xv) :: V) "gp" gv = ("x", xv) :: VEnv.set V "gp" gv by
    simp [VEnv.set]]
  rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "gp") (by decide)]
  exact venv_get_set_same (D := Bridge.Dialect c g) h

theorem get_set_mptr_same {V : VEnv (Bridge.Dialect c g)} {xv gv mp mp' : U256}
    (h : VEnv.get V "mptr" = some mp) :
    VEnv.get (VEnv.set (VEnv.set (("x", xv) :: V) "gp" gv) "mptr" mp') "mptr" = some mp' := by
  rw [venv_get_set_same (D := Bridge.Dialect c g)]
  rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr") (by decide),
    venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "mptr") (by decide)]
  exact h

theorem get_set_gp_mptr_same {V : VEnv (Bridge.Dialect c g)} {xv gv mp gmp gmpNew : U256}
    (h : VEnv.get V "gp_mptr" = some gmp) :
    VEnv.get (VEnv.set (VEnv.set (VEnv.set (("x", xv) :: V) "gp" gv) "mptr" mp)
      "gp_mptr" gmpNew) "gp_mptr" = some gmpNew := by
  rw [venv_get_set_same (D := Bridge.Dialect c g)]
  rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
    venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "gp_mptr") (by decide),
    venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "gp_mptr") (by decide)]
  exact h

theorem restore_x_sets (V : VEnv (Bridge.Dialect c g)) (xv gv mp gmp : U256) :
    restore V (VEnv.set (VEnv.set (VEnv.set (("x", xv) :: V) "gp" gv) "mptr" mp)
      "gp_mptr" gmp) =
      VEnv.set (VEnv.set (VEnv.set V "gp" gv) "mptr" mp) "gp_mptr" gmp := by
  simp [restore, VEnv.set, venv_set_length (D := Bridge.Dialect c g)]

theorem bi_forward_loop (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (rw : U256) (a e s : Nat) (hae : a + 64 ≤ e) (hal : (e - a) % 32 = 0)
    (he : e < 2 ^ 256) (hs : s + (e - a) < 2 ^ 256)
    (hdisj : e ≤ s ∨ s + (e - a) ≤ a) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts GenAst.emitBatchInvertAt) 10 1)
      (fun V st => VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 e) ∧
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "gp" = some (loadWord st.memory a) ∧ VEnv.get V "r" = some rw ∧
        (VEnv.get V "ret").isSome ∧ (loadWord st.memory a).toNat < rw.toNat)
      (fun _ st V' st' o =>
        (o = .leave ∧ VEnv.get V' "ret" = some 0) ∨
        (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          MemSameOutside st st' s (e - a - 64) ∧
          VEnv.get V' "mptr" = some (BitVec.ofNat 256 (e - 32)) ∧
          VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 (s + (e - a - 64))) ∧
          (∀ i, a + 32 * i + 32 < e → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
          ∃ P : Nat → U256, P 0 = loadWord st.memory a ∧
            (∀ i, a + 32 * (i + 1) + 32 < e →
              P (i + 1) = wMulmodAt (P i) (loadWord st.memory (a + 32 * (i + 1))) rw ∧
              loadWord st'.memory (s + 32 * i) = P (i + 1)) ∧
            VEnv.get V' "gp" = some (P ((e - a) / 32 - 2)))) := by
  rw [bi_forward_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    GenAst.yif, GenAst.yexpr]
  intro V st hpre
  obtain ⟨hmptr, hmend, hgpm, hgp, hr, hret, hw0⟩ := hpre
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hal
  have hkdef : (e - a) / 32 = k := by
    rw [hk, Nat.mul_comm 32 k]
    exact Nat.mul_div_left k (by norm_num : 0 < 32)
  have he' : e = a + 32 * k := by omega
  have hk2 : 2 ≤ k := by omega
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o =>
      (o = .leave ∧ VEnv.get V' "ret" = some 0) ∨
      (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
        MemSameOutside st st' s (e - a - 64) ∧
        VEnv.get V' "mptr" = some (BitVec.ofNat 256 (e - 32)) ∧
        VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 (s + (e - a - 64))) ∧
        (∀ i, a + 32 * i + 32 < e → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
        ∃ P : Nat → U256, P 0 = loadWord st.memory a ∧
          (∀ i, a + 32 * (i + 1) + 32 < e →
            P (i + 1) = wMulmodAt (P i) (loadWord st.memory (a + 32 * (i + 1))) rw ∧
            loadWord st'.memory (s + 32 * i) = P (i + 1)) ∧
          VEnv.get V' "gp" = some (P ((e - a) / 32 - 2)))
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop []
      (Expr.builtin Op.lt [Expr.var "mptr", Expr.builtin Op.sub
        [Expr.var "mptr_end", Expr.lit (Literal.number 0x20)]])
      []
      [ Stmt.letDecl ["x"] (some (Expr.builtin Op.mload [Expr.var "mptr"]))
      , Stmt.cond (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var "x", Expr.var "r"]])
          [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]
      , Stmt.assign ["gp"] (Expr.builtin Op.mulmod
          [Expr.var "gp", Expr.var "x", Expr.var "r"])
      , Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "gp_mptr", Expr.var "gp"])
      , Stmt.assign ["mptr"] (Expr.builtin Op.add
          [Expr.var "mptr", Expr.lit (Literal.number 0x20)])
      , Stmt.assign ["gp_mptr"] (Expr.builtin Op.add
          [Expr.var "gp_mptr", Expr.lit (Literal.number 0x20)]) ]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j, j ≤ k - 2 ∧ V' = fwdEnv st.memory a s rw V j ∧
      (∀ i, i ≤ j → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
      ∃ aw, st' = { st with
        memory := writeWords st.memory s (fwdWords st.memory a rw) j, activeWords := aw }
  have hmain : Midfall.Yul.WpTac.AllRuns funs V st
      [Stmt.forLoop []
        (Expr.builtin Op.lt [Expr.var "mptr", Expr.builtin Op.sub
          [Expr.var "mptr_end", Expr.lit (Literal.number 0x20)]])
        []
        [ Stmt.letDecl ["x"] (some (Expr.builtin Op.mload [Expr.var "mptr"]))
        , Stmt.cond (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var "x", Expr.var "r"]])
            [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]
        , Stmt.assign ["gp"] (Expr.builtin Op.mulmod
            [Expr.var "gp", Expr.var "x", Expr.var "r"])
        , Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "gp_mptr", Expr.var "gp"])
        , Stmt.assign ["mptr"] (Expr.builtin Op.add
            [Expr.var "mptr", Expr.lit (Literal.number 0x20)])
        , Stmt.assign ["gp_mptr"] (Expr.builtin Op.add
            [Expr.var "gp_mptr", Expr.lit (Literal.number 0x20)]) ]] Q := by
    refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
      (Bopen_sound c g) (Cnone_sound _) (n := 40) Inv ?hinit ?hstep
    · refine ⟨0, by omega, ?_, ?_, ?_⟩
      · rfl
      · intro i hi
        interval_cases i
        exact hw0
      · exact ⟨st.activeWords, rfl⟩
    · intro Vi sti hInv
      obtain ⟨j, hj, hV, hcanon, aw, hst⟩ := hInv
      subst hV
      subst hst
      have hmptrj := fwdEnv_get_mptr st.memory a s rw V hmptr j
      have hmendj := fwdEnv_get_mptr_end st.memory a s rw (BitVec.ofNat 256 e) V hmend j
      have hgpmj := fwdEnv_get_gp_mptr st.memory a s rw V hgpm j
      have hgpj := fwdEnv_get_gp st.memory a s rw V hgp j
      have hrj := fwdEnv_get_r st.memory a s rw V hr j
      unfold wpIter
      simp only [wpE, wpA, Bopen, stepOp, bin, ter, un, hmptrj, hmendj, hgpmj, hgpj, hrj]
      refine ⟨?guardFalse, ?guardTrue⟩
      · -- guard false
        intro hguard
        have hsub : BitVec.ofNat 256 e - BitVec.ofNat 256 0x20 = BitVec.ofNat 256 (e - 32) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : 0x20 < 2 ^ 256),
            Nat.mod_eq_of_lt (by omega : e < 2 ^ 256),
            Nat.mod_eq_of_lt (by omega : e - 32 < 2 ^ 256)]
          omega
        have hsubL : BitVec.ofNat 256 e - litValue (Literal.number 32) =
            BitVec.ofNat 256 (e - 32) := by
          rw [show litValue (Literal.number 32) = BitVec.ofNat 256 0x20 from rfl]
          exact hsub
        have h0' : b2w ((BitVec.ofNat 256 (a + 32 + 32 * j)).ult
            (BitVec.ofNat 256 (e - 32))) = (0 : U256) := by
          have hz : (Bridge.Dialect c g).zero = (0 : U256) := rfl
          simpa [hsubL, hz] using hguard
        have hge : e - 32 ≤ a + 32 + 32 * j :=
          LoopRule.lt_guard_false (by omega) (by omega) h0'
        have hjk : j = k - 2 := by omega
        subst hjk
        refine ⟨?allRuns⟩
        intro V' st' o hrun
        cases hrun with
        | seqNil =>
        have hl := fwdEnv_length st.memory a s rw V (k - 2)
        have hres : restore V (fwdEnv st.memory a s rw V (k - 2)) =
            fwdEnv st.memory a s rw V (k - 2) := by
          simp [restore, hl]
        rw [hres]
        dsimp only [Q]
        refine Or.inr ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · -- MemSameOutside
          intro x hx
          show writeWords st.memory s (fwdWords st.memory a rw) (k - 2) x = st.memory x
          exact writeWords_outside st.memory s (fwdWords st.memory a rw) (by omega)
        · -- mptr
          have harith : a + 32 + 32 * (k - 2) = e - 32 := by omega
          rw [hmptrj, harith]
        · -- gp_mptr
          have harith : s + 32 * (k - 2) = s + (e - a - 64) := by omega
          rw [hgpmj, harith]
        · -- canonical words
          intro i hi
          exact hcanon i (by omega)
        · -- product
          refine ⟨fwdProd st.memory a rw, rfl, ?_, ?_⟩
          · intro i hi
            have hik : i < k - 2 := by omega
            refine ⟨rfl, ?_⟩
            show loadWord (writeWords st.memory s (fwdWords st.memory a rw) (k - 2))
              (s + 32 * i) = fwdProd st.memory a rw (i + 1)
            exact loadWord_writeWords_lt st.memory s (fwdWords st.memory a rw) hik
          · rw [hgpj, hkdef]
      · -- guard true
        intro hguard
        have hsub : BitVec.ofNat 256 e - BitVec.ofNat 256 0x20 = BitVec.ofNat 256 (e - 32) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : 0x20 < 2 ^ 256),
            Nat.mod_eq_of_lt (by omega : e < 2 ^ 256),
            Nat.mod_eq_of_lt (by omega : e - 32 < 2 ^ 256)]
          omega
        have hsubL : BitVec.ofNat 256 e - litValue (Literal.number 32) =
            BitVec.ofNat 256 (e - 32) := by
          rw [show litValue (Literal.number 32) = BitVec.ofNat 256 0x20 from rfl]
          exact hsub
        have h0' : b2w ((BitVec.ofNat 256 (a + 32 + 32 * j)).ult
            (BitVec.ofNat 256 (e - 32))) ≠ (0 : U256) := by
          have hz : (Bridge.Dialect c g).zero = (0 : U256) := rfl
          simpa [hsubL, hz] using hguard
        have hlt : j < k - 2 := by
          have := LoopRule.lt_guard_true (i := a + 32 + 32 * j) (n := e - 32)
            (by omega) (by omega) h0'
          omega
        simp only [wpS, wpSS, wpE, wpA, Bopen, stepOp, bin, ter, un,
          hmptrj, hmendj, hgpmj, hgpj, hrj,
          ofNat_toNat (by omega : a + 32 + 32 * j < 2 ^ 256)]
        simp only [List.zip_cons_cons, List.zip_nil_left, List.cons_append, List.nil_append,
          List.length_cons, List.length_nil,
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "r") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "gp") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "gp_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "mptr_end") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "ret") (by decide)]
        rw [get_cons_self_x]
        simp only [VEnv.setMany, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons,
          List.foldl_nil,
          get_set_gp_same (h := hgpj), get_set_mptr_same (h := hmptrj),
          get_set_gp_mptr_same (h := hgpmj),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "gp_mptr") (by decide),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr") (by decide),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp") (by decide),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "gp") (by decide),
          venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr") (by decide),
          hmptrj, hgpmj, hgpj, hrj, hmendj]
        simp only [
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "gp_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "mptr") (by decide),
          hgpmj, hmptrj]
        refine ⟨trivial, ?_⟩
        refine Stop.intro ?_
        refine ⟨?gFalse, ?gTrue⟩
        · -- guard false: continue the body
          intro hcv
          repeat' first | refine ⟨trivial, ?_⟩ | refine Stop.intro ?_
          · -- Inv at j + 1
            simp only [Inv]
            have hl := fwdEnv_length st.memory a s rw V j
            have hload : loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                (a + 32 + 32 * j) = loadWord st.memory (a + 32 + 32 * j) := by
              apply loadWord_writeWords_outside
              rcases hdisj with h | h
              · left; omega
              · right; omega
            have hgv : (if rw = 0 then 0 else BitVec.ofNat 256
                (BitVec.toNat (fwdProd st.memory a rw j) *
                  BitVec.toNat (loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                    (a + 32 + 32 * j)) % BitVec.toNat rw)) =
                fwdProd st.memory a rw (j + 1) := by
              have hsucc : fwdProd st.memory a rw (j + 1) =
                  wMulmodAt (fwdProd st.memory a rw j)
                    (loadWord st.memory (a + 32 + 32 * j)) rw := by
                rw [fwdProd_succ, show a + 32 * (j + 1) = a + 32 + 32 * j by ring]
              show wMulmodAt (fwdProd st.memory a rw j)
                (loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                  (a + 32 + 32 * j)) rw = fwdProd st.memory a rw (j + 1)
              rw [hload]
              exact hsucc.symm
            have hmp : BitVec.ofNat 256 (a + 32 + 32 * j) + litValue (Literal.number 32) =
                BitVec.ofNat 256 (a + 32 + 32 * (j + 1)) := by
              rw [show litValue (Literal.number 32) = BitVec.ofNat 256 32 from rfl,
                ← BitVec.ofNat_add]
              congr 1
            have hgmp : BitVec.ofNat 256 (s + 32 * j) + litValue (Literal.number 32) =
                BitVec.ofNat 256 (s + 32 * (j + 1)) := by
              rw [show litValue (Literal.number 32) = BitVec.ofNat 256 32 from rfl,
                ← BitVec.ofNat_add]
              congr 1
            refine ⟨j + 1, by omega, ?_, ?_, ?_⟩
            · -- environment
              have hAA : ∀ (A : VEnv (Bridge.Dialect c g)), restore A A = A := by
                intro A
                simp [restore]
              rw [hAA]
              refine (restore_x_sets (V := fwdEnv st.memory a s rw V j)
                (xv := loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                  (a + 32 + 32 * j))
                (gv := (if rw = 0 then 0 else BitVec.ofNat 256
                  (BitVec.toNat (fwdProd st.memory a rw j) *
                    BitVec.toNat (loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                      (a + 32 + 32 * j)) % BitVec.toNat rw)))
                (mp := BitVec.ofNat 256 (a + 32 + 32 * j) + litValue (Literal.number 32))
                (gmp := BitVec.ofNat 256 (s + 32 * j) + litValue (Literal.number 32))).trans ?_
              rw [hgv, hmp, hgmp]
              rfl
            · -- canonical
              intro i hi
              by_cases hij : i = j + 1
              · subst hij
                have hx0 : (loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
                    (a + 32 + 32 * j)).toNat < rw.toNat :=
                  lt_of_iszero_eq_zero (by
                    have hz : (Bridge.Dialect c g).zero = (0 : U256) := rfl
                    simpa [hz] using hcv)
                have hx1 : (loadWord st.memory (a + 32 + 32 * j)).toNat < rw.toNat := by
                  rwa [hload] at hx0
                rw [show a + 32 * (j + 1) = a + 32 + 32 * j by ring]
                exact hx1
              · exact hcanon i (by omega)
            · -- state
              refine ⟨(touchMemory
                  (touchMemory
                    { memory := writeWords st.memory s (fwdWords st.memory a rw) j,
                      activeWords := aw, storage := st.storage, transient := st.transient,
                      env := st.env, returndata := st.returndata, logs := st.logs,
                      selfdestructs := st.selfdestructs, halted := st.halted }
                    (a + 32 + 32 * j) 32)
                  (BitVec.ofNat 256 (s + 32 * j)).toNat 32).activeWords, ?_⟩
              simp only [writeWords, fwdWords]
              rw [hgv]
              rw [show (BitVec.ofNat 256 (s + 32 * j)).toNat = s + 32 * j from
                ofNat_toNat (by omega)]
              rfl
        · -- guard true: reject and leave
          intro hcv
          refine ⟨trivial, ?_⟩
          refine Stop.intro ?_
          unfold Q
          refine Or.inl ⟨rfl, ?_⟩
          have hretj := fwdEnv_get_ret st.memory a s rw V j
          obtain ⟨r0, hr0⟩ := Midfall.LoweringV3.QuotientRows.isSome_elim hret
          have hreti : VEnv.get (fwdEnv st.memory a s rw V j) "ret" = some r0 := by
            rw [hretj]; exact hr0
          have hl := fwdEnv_length st.memory a s rw V j
          rw [restore_reject_ret (V := V) (Vi := fwdEnv st.memory a s rw V j)
            (xv := loadWord (writeWords st.memory s (fwdWords st.memory a rw) j)
              (a + 32 + 32 * j)) (r := litValue (Literal.number 0)) hl]
          exact venv_get_set_same (D := Bridge.Dialect c g) hreti
  intro V' st' o hrun
  exact hmain V' st' o hrun

/-! ## 4c. BACKWARD-PASS INFRASTRUCTURE (HLP.1.c, partial)

  The running inverse `bwdAll`, the stored value `bwdInvVal`, the two pointer walks `bwdMptr` /
  `bwdGp`, the loop-head environment `bwdEnv` and its six `get` lemmas, plus the two field facts the
  iteration needs: `wMulmodAt_comm` and the inductions `bwdAll_inv` (the running inverse of
  `fwdProd (k-1-j)`) and `bwdInvVal_inv` (the stored word is the inverse of `w_{k-1-j}`). The loop
  THEOREM is not yet in this file; the remaining piece is the `bwdMem` store-chain bookkeeping
  (the `k-1-j` truncated-subtraction arithmetic in `loadWord_bwdMem_*`). -/

def bwdAll (mem : Nat → UInt8) (a k : Nat) (rw invAll : U256) : Nat → U256
  | 0 => invAll
  | j + 1 => wMulmodAt (bwdAll mem a k rw invAll j) (loadWord mem (a + 32 * (k - 1 - j))) rw

/-- The value stored at word `k-1-j` by iteration `j`. -/
def bwdInvVal (mem : Nat → UInt8) (a k : Nat) (rw invAll : U256) (j : Nat) : U256 :=
  wMulmodAt (bwdAll mem a k rw invAll j) (fwdProd mem a rw (k - 2 - j)) rw

/-- `mptr` after `j` iterations. -/
def bwdMptr (a k : Nat) (j : Nat) : U256 :=
  BitVec.ofNat 256 (a + 32 * (k - 1)) - BitVec.ofNat 256 (32 * j)

/-- `gp_mptr` after `j` iterations. -/
def bwdGp (s k : Nat) (j : Nat) : U256 :=
  BitVec.ofNat 256 (s + 32 * (k - 3)) - BitVec.ofNat 256 (32 * j)

/-- The loop-head environment after `j` iterations, anchored at `V`. -/
def bwdEnv (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) : Nat → VEnv (Bridge.Dialect c g)
  | 0 => V
  | j + 1 => VEnv.set (VEnv.set (VEnv.set (bwdEnv mem a s k rw invAll V j) "all_inv"
      (bwdAll mem a k rw invAll (j + 1))) "mptr" (bwdMptr a k (j + 1)))
      "gp_mptr" (bwdGp s k (j + 1))

theorem bwdEnv_length (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) (j : Nat) :
    (bwdEnv mem a s k rw invAll V j).length = V.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [bwdEnv, venv_set_length (D := Bridge.Dialect c g), ih]

theorem bwdEnv_get_mptr (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g))
    (hmptr : VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32 * (k - 1)))) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "mptr" = some (bwdMptr a k j) := by
  induction j with
  | zero => simpa [bwdEnv, bwdMptr] using hmptr
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr") (by decide)]
      refine venv_get_set_same (D := Bridge.Dialect c g) (v := bwdMptr a k j)
        (w := bwdMptr a k (j + 1)) ?_
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "mptr") (by decide)]
      exact ih

theorem bwdEnv_get_gp_mptr (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g))
    (hgp : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 (s + 32 * (k - 3)))) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "gp_mptr" = some (bwdGp s k j) := by
  induction j with
  | zero => simpa [bwdEnv, bwdGp] using hgp
  | succ j ih =>
      simp only [bwdEnv]
      refine venv_get_set_same (D := Bridge.Dialect c g) (v := bwdGp s k j)
        (w := bwdGp s k (j + 1)) ?_
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "gp_mptr") (by decide)]
      exact ih

theorem bwdEnv_get_all_inv (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g))
    (h : VEnv.get V "all_inv" = some invAll) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "all_inv" =
      some (bwdAll mem a k rw invAll j) := by
  induction j with
  | zero => simpa [bwdEnv, bwdAll] using h
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "all_inv") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "all_inv") (by decide)]
      exact venv_get_set_same (D := Bridge.Dialect c g) ih

theorem bwdEnv_get_second_mptr (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) (v : U256)
    (h : VEnv.get V "second_mptr" = some v) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "second_mptr" = some v := by
  induction j with
  | zero => exact h
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "second_mptr") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "second_mptr") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "second_mptr") (by decide)]
      exact ih

theorem bwdEnv_get_r (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) (h : VEnv.get V "r" = some rw) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "r" = some rw := by
  induction j with
  | zero => exact h
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "r") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "r") (by decide)]
      exact ih

theorem bwdEnv_get_ret (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "ret" = VEnv.get V "ret" := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "ret") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "ret") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "ret") (by decide)]
      exact ih

/-- `wMulmodAt` is commutative at a non-zero modulus. -/
theorem wMulmodAt_comm {r a b : U256} (hr : r ≠ 0) :
    wMulmodAt a b r = wMulmodAt b a r := by
  rw [wMulmodAt, wMulmodAt, ite_eq_right hr, ite_eq_right hr, Nat.mul_comm]

/-- The running inverse: `all_inv` after `j` steps is the inverse of `fwdProd (k-1-j)`. -/
theorem bwdAll_inv (mem : Nat → UInt8) (a k : Nat) (rw invAll : U256)
    (hr : rw ≠ 0) (hk : 2 ≤ k)
    (hinv : wMulmodAt invAll (fwdProd mem a rw (k - 1)) rw = 1)
    (j : Nat) (hj : j ≤ k - 2) :
    wMulmodAt (bwdAll mem a k rw invAll j) (fwdProd mem a rw (k - 1 - j)) rw = 1 := by
  induction j with
  | zero => simpa [bwdEnv, bwdAll] using hinv
  | succ j ih =>
      simp only [bwdAll]
      have hstep : fwdProd mem a rw (k - 1 - j) =
          wMulmodAt (fwdProd mem a rw (k - 2 - j))
            (loadWord mem (a + 32 * (k - 1 - j))) rw := by
        have h := fwdProd_succ mem a rw (k - 2 - j)
        rwa [show k - 2 - j + 1 = k - 1 - j by omega] at h
      rw [show k - 1 - (j + 1) = k - 2 - j by omega, wMulmodAt_assoc hr,
        show wMulmodAt (loadWord mem (a + 32 * (k - 1 - j))) (fwdProd mem a rw (k - 2 - j)) rw =
          wMulmodAt (fwdProd mem a rw (k - 2 - j)) (loadWord mem (a + 32 * (k - 1 - j))) rw
          from wMulmodAt_comm hr,
        ← hstep]
      exact ih (by omega)

/-- The word stored at iteration `j` is the inverse of `w_{k-1-j}`. -/
theorem bwdInvVal_inv (mem : Nat → UInt8) (a k : Nat) (rw invAll : U256)
    (hr : rw ≠ 0) (hk : 2 ≤ k)
    (hinv : wMulmodAt invAll (fwdProd mem a rw (k - 1)) rw = 1)
    (j : Nat) (hj : j ≤ k - 2) :
    wMulmodAt (bwdInvVal mem a k rw invAll j)
      (loadWord mem (a + 32 * (k - 1 - j))) rw = 1 := by
  have hstep : fwdProd mem a rw (k - 1 - j) =
      wMulmodAt (fwdProd mem a rw (k - 2 - j))
        (loadWord mem (a + 32 * (k - 1 - j))) rw := by
    have h := fwdProd_succ mem a rw (k - 2 - j)
    rwa [show k - 2 - j + 1 = k - 1 - j by omega] at h
  rw [bwdInvVal, wMulmodAt_assoc hr, ← hstep]
  exact bwdAll_inv mem a k rw invAll hr hk hinv j hj

/-! ## 4d. THE BACKWARD STORE CHAIN (`bwdMem`)

  `bwdMem` writes `I j` at `a + 32*(k-(j+1))` (descending from `a+32*(k-1)`), exactly the backward
  pass's stores. The four lemmas are the read/window facts the loop invariant needs: words not yet
  reached are original (`untouched`), reached words hold `I (k-1-i)` (`written`), and memory outside
  the batch and the forward scratch is untouched (`outside`, `scratch`). -/

def bwdMem (mem : Nat → UInt8) (a k : Nat) (I : Nat → U256) : Nat → (Nat → UInt8)
  | 0 => mem
  | j + 1 => storeWord (bwdMem mem a k I j) (a + 32 * (k - (j + 1))) (I j)

theorem storeWord_outside (mem : Nat → UInt8) (p x : Nat) (v : U256)
    (h : x < p ∨ p + 32 ≤ x) : storeWord mem p v x = mem x := by
  unfold storeWord
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  omega

theorem loadWord_bwdMem_untouched (mem : Nat → UInt8) (a k : Nat) (I : Nat → U256) :
    ∀ (j i : Nat), 1 ≤ k → j ≤ k - 1 → i < k - j →
      loadWord (bwdMem mem a k I j) (a + 32 * i) = loadWord mem (a + 32 * i) := by
  intro j
  induction j with
  | zero => intro i hk hj hi; rfl
  | succ j ih =>
      intro i hk hj hi
      simp only [bwdMem]
      have hdisj : a + 32 * i + 32 ≤ a + 32 * (k - (j + 1)) := by omega
      rw [Midfall.Yul.Word.loadWord_storeWord_disjoint _ _ _ _ (Or.inl hdisj)]
      exact ih i hk (by omega) (by omega)

theorem loadWord_bwdMem_written (mem : Nat → UInt8) (a k : Nat) (I : Nat → U256) :
    ∀ (j i : Nat), 1 ≤ k → j ≤ k - 1 → k - j ≤ i → i < k →
      loadWord (bwdMem mem a k I j) (a + 32 * i) = I (k - 1 - i) := by
  intro j
  induction j with
  | zero => intro i hk hj hlo hhi; omega
  | succ j ih =>
      intro i hk hj hlo hhi
      simp only [bwdMem]
      by_cases hnew : i = k - (j + 1)
      · subst hnew
        rw [Midfall.Yul.Word.loadWord_storeWord_same]
        rw [show k - 1 - (k - (j + 1)) = j by omega]
      · have hdisj : a + 32 * (k - (j + 1)) + 32 ≤ a + 32 * i := by omega
        rw [Midfall.Yul.Word.loadWord_storeWord_disjoint _ _ _ _ (Or.inr hdisj)]
        exact ih i hk (by omega) (by omega) (by omega)

theorem bwdMem_outside (mem : Nat → UInt8) (a k : Nat) (I : Nat → U256) :
    ∀ (j : Nat) (x : Nat), 1 ≤ k → j ≤ k - 1 → (x < a ∨ a + 32 * k ≤ x) →
      bwdMem mem a k I j x = mem x := by
  intro j
  induction j with
  | zero => intro x hk hj hx; rfl
  | succ j ih =>
      intro x hk hj hx
      simp only [bwdMem]
      rw [storeWord_outside _ _ _ _ (by
        rcases hx with h | h
        · left; omega
        · right; omega)]
      exact ih x hk (by omega) hx

theorem bwdMem_scratch (mem : Nat → UInt8) (a k s : Nat) (I : Nat → U256) :
    ∀ (j : Nat) (x : Nat), 1 ≤ k → j ≤ k - 1 →
      ((a + 32 * k ≤ s) ∨ (s + 32 * k ≤ a)) → s ≤ x → x < s + 32 * k →
      bwdMem mem a k I j x = mem x := by
  intro j
  induction j with
  | zero => intro x hk hj hdisj hx hx2; rfl
  | succ j ih =>
      intro x hk hj hdisj hx hx2
      simp only [bwdMem]
      rw [storeWord_outside _ _ _ _ (by
        rcases hdisj with h | h
        · right; omega
        · left; omega)]
      exact ih x hk (by omega) hdisj hx hx2



/-- The closed form of the `mptr` walk: for `j ≤ k-1`, `bwdMptr a k j` is the word
`a + 32*(k-1-j)`. -/
theorem bwdMptr_eq (a k j : Nat) (he : a + 32 * k < 2 ^ 256) (hj : j ≤ k - 1) :
    bwdMptr a k j = BitVec.ofNat 256 (a + 32 * (k - 1 - j)) := by
  unfold bwdMptr
  have hX : a + 32 * (k - 1) < 2 ^ 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * j < 2 ^ 256),
    Nat.mod_eq_of_lt hX,
    Nat.mod_eq_of_lt (by omega : a + 32 * (k - 1 - j) < 2 ^ 256)]
  omega

/-- The closed form of the `gp_mptr` walk: for `j ≤ k-3`, it is `s + 32*(k-3-j)`. -/
theorem bwdGp_eq (s k j : Nat) (hs : s + 32 * k < 2 ^ 256) (hj : j ≤ k - 3) :
    bwdGp s k j = BitVec.ofNat 256 (s + 32 * (k - 3 - j)) := by
  unfold bwdGp
  have hX : s + 32 * (k - 3) < 2 ^ 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * j < 2 ^ 256),
    Nat.mod_eq_of_lt hX,
    Nat.mod_eq_of_lt (by omega : s + 32 * (k - 3 - j) < 2 ^ 256)]
  omega

/-! ## 5. PREMISE GAP PG-BATCHINVERT (exact statements; no hypothesis added to a row)

  **(1) CLOSED at §4b: `bi_forward_loop` IS PROVED, with the statement-9 canonicality pre.**
  The evidence's version is FALSE AS STATED, which is why the pre below carries one more conjunct
  than `GeneratorRows.lean:342`. Its pre (`GeneratorRows.lean:342`)
  carries `VEnv.get V "gp" = some (loadWord st.memory a)` and the returned-word `isSome` fact, and
  its post (:353) carries `∀ i, a + 32*i + 32 < e → (loadWord st.memory (a+32*i)).toNat < rw.toNat`.
  At `i = 0` that clause is `(loadWord st.memory a).toNat < rw.toNat`, but the loop's cursor starts
  at `mptr = a + 32` and never re-reads word 0. Counterexample: `a = 0, e = 64, s = 1000,
  rw = 7, loadWord st.memory 0 = 10`. Then `hae`, `hal`, `he`, `hs`, `hdisj` hold
  (`0 + 64 ≤ 64`, `(64-0) % 32 = 0`, `64 < 2^256`, `1000 + 64 < 2^256`, `64 ≤ 1000`), the pre
  holds (`mptr = 32`, `mptr_end = 64`, `gp_mptr = 1000`, `gp = 10`, `r = 7`), the guard
  `lt(32, 64 - 32)` is FALSE, so the loop runs zero times and exits `.normal` with
  `st' = st`; the post's `i = 0` clause is `10 < 7`. The missing premise is the emitter's
  statement-9 guard, `if iszero(lt(gp, r)) { ret := 0; leave }` (GenAst.lean:498): its false
  branch is exactly `(loadWord st.memory a).toNat < rw.toNat`. THE FIX (for the next session) is
  to add that conjunct to the loop's pre - an ARM-LEMMA pre, never a row, bundle or root
  (WORKER-RULES "Hard bounds") - and the caller (the 9-statement forward prelude) discharges it.
  Exact goal state at the blocked step: after `rw [bi_forward_loop_form]` and the loop-rule cut,
  the guard-FALSE branch is
  `Stop (AllRuns funs (restore V Vend) stend [] Q)` with
  `Q V' st' o = (o = .leave ∧ V'.get "ret" = some 0) ∨ (o = .normal ∧ … ∧
   (∀ i, a + 32*i + 32 < e → (loadWord st.memory (a+32*i)).toNat < rw.toNat) ∧
   ∃ P, P 0 = loadWord st.memory a ∧ …)`, and the `i = 0` clause has no derivation from the pre.

  **(2) `batch_invert_summary` STILL NEEDS THE ARBITRARY-PRIME MODEXP BRIDGE (and the backward
  loop: `BatchInvertPost`'s `ret ≠ 0` arm is exactly the backward loop's post, so the order is
  `bi_backward_loop` first, then the staticcall/modexp, then the summary).**
  The remaining byte work can be done ENTIRELY AT THE MEMORY LEVEL, without generalising the
  `blsR`-specific abstract `modexpInvFrame`: the helper stores six 32-byte words at
  `p, p+32, …, p+160` (`modexpFrameStores`, GenAst.lean:408-417), so if
    (i) `readBytes (storeWord mem p v) p 32 = (bytesNatBE v.toNat 32).data.toList`
        (the store/read bridge; `byteAt_eq_toUInt8` is the only byte arithmetic: the emitted byte
        at `p+i` is `Nat.toUInt8 ((v.toNat / 256^(31-i)) % 256)` while `bytesNatBE` writes the
        reversed digit list), and
    (ii) `bytesToNatBE (ByteArray.mk (readBytes mem q 32).toArray) = (loadWord mem q).toNat`
        (the 32-byte fold is the same big-endian fold; `bytesToNatBE` is a `Nat` fold and
        `loadWord` a `U256` fold, so the only lemma is
        `(l.foldl (fun acc b => (acc <<< 8) ||| b) 0).toNat = l.foldl (fun acc b => acc*256 + b) 0`
        for `l.length ≤ 32`, by induction with the accumulator bound `acc < 256^(32 - l.length)`),
  then `modexpSizes input = (32,32,32)`, `modexpParse?` gives the three stored operand words, and
  `modexpOutput` is `bytesNatBE (modPow base (rw-2) rw) 32`; `modPow_inv` at `p := rw.toNat`
  (`Assumptions/Eip2537.lean:319`, general in `p`) finishes. The old plan - re-proving the private
  `modexpInvFrame_slices` for an arbitrary modulus - is NOT needed and should not be attempted.

  **PLAN FOR `bi_backward_loop` (HLP.1.c), the next leaf.** With `k = (e-a)/32` and
  `hae : a + 96 ≤ e` (so `3 ≤ k`), the loop is statement 29 and starts after the `sub(gp_mptr, 32)`:
  pre `mptr = ofNat (a + 32*(k-1))`, `second_mptr = ofNat (a+32)`,
  `gp_mptr = ofNat (s + 32*(k-3))`, `all_inv = some invAll`,
  `hinv : wMulmodAt invAll (fwdProd st.memory a rw (k-1)) rw = 1`, every batch word and every
  `fwdProd` canonical/non-zero, and the forward scratch `loadWord st.memory (s+32*i) = fwdProd (i+1)`.
  Invariant after `j` iterations: `all_inv` is the inverse of `fwdProd (k-1-j)`,
  `mptr = ofNat (a + 32*(k-1-j))`, words `k-j … k-1` hold inverses, words `< k-j` are untouched,
  memory outside `[a,e)` and the scratch window is unchanged. The iteration stores
  `w_{k-1-j}⁻¹ = wMulmodAt all_inv (fwdProd (k-2-j)) rw`; the one missing arithmetic lemma is
  associativity of `wMulmodAt` on canonical words,
  `wMulmodAt (wMulmodAt a b r) c r = wMulmodAt a (wMulmodAt b c r) r` for `a,b,c < r`, which is
  `Nat.mul_assoc` through `Nat.mul_mod`. The post is exactly `BatchInvertPost`'s `ret ≠ 0` arm for
  `i ≥ 2`; the tail (statements 30-33) supplies `i = 0,1`.

  **(2, original note) `batch_invert_summary` NEEDS AN ARBITRARY-PRIME MODEXP LEMMA THE TREE DOES
  NOT HAVE.**
  The summary (`GeneratorRows.lean:317-330`) is generic in `rw : U256` with `hrw : Nat.Prime rw.toNat`
  and only `BatchInvertPost` as post. Its `ret ≠ 0` arm must identify the staticcall's honest
  32-byte output with `(loadWord st.memory (a+32i))⁻¹`. The tree's byte-parse + Fermat proof is
  `Midfall.Assumptions.Eip2537.modexpInv_correct` (:825), which is stated for `modexpInvFrame x`
  with the modulus HARD-WIRED to `blsR` (:560-563), and all of its slice plumbing
  (`modexpInvFrame_slices`, `modexpInvFrame_operands`, … :640-843) is `private`. The frame the
  helper writes is the PARAMETERISED one (`modexpFrameStores`, GenAst.lean:408-417), with modulus
  `rw` and exponent `rw - 2`. So before the summary's staticcall step can be proved, the
  `blsR`-specific parse must be re-proved for `modexpFrame wordBytes wordBytes wordBytes
  (bytesNatBE x 32) (bytesNatBE (rw.toNat - 2) 32) (bytesNatBE rw.toNat 32)`, and the resulting
  `modexpOutput` value must be fed through `modPow_inv` at `p := rw.toNat`. The arithmetic half is
  available (`Assumptions/Eip2537.modPow_inv`, :319); the byte-parse half is not. THE FIX is a
  new file (or a non-private generalisation in Eip2537) with that parse; the summary's statement
  itself is otherwise consistent with the tree (the emitter body, window stores and `hdisj` all
  match).

  THE CORRECTED STATEMENT (now PROVED at §4b; an arm lemma, so the extra pre conjunct is legal):

    theorem bi_forward_loop (consts : Inline.Consts) {c : ExternalCalls} {g : ExternalGas}
        (funs : FunEnv (Bridge.Dialect c g)) (rw : U256) (a e s : Nat)
        (hae : a + 64 ≤ e) (hal : (e - a) % 32 = 0) (he : e < 2 ^ 256)
        (hs : s + (e - a) < 2 ^ 256) (hdisj : e ≤ s ∨ s + (e - a) ≤ a) :
        StmtsContractAll (D := Bridge.Dialect c g) funs
          (seg (helperBody consts GenAst.emitBatchInvertAt) 10 1)
          (fun V st => VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
            VEnv.get V "mptr_end" = some (BitVec.ofNat 256 e) ∧
            VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 s) ∧
            VEnv.get V "gp" = some (loadWord st.memory a) ∧ VEnv.get V "r" = some rw ∧
            (VEnv.get V "ret").isSome ∧ (loadWord st.memory a).toNat < rw.toNat)
          (fun _ st V' st' o =>
            (o = .leave ∧ VEnv.get V' "ret" = some 0) ∨
            (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
              MemSameOutside st st' s (e - a - 64) ∧
              VEnv.get V' "mptr" = some (BitVec.ofNat 256 (e - 32)) ∧
              VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 (s + (e - a - 64))) ∧
              (∀ i, a + 32 * i + 32 < e → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
              ∃ P : Nat → U256, P 0 = loadWord st.memory a ∧
                (∀ i, a + 32 * (i + 1) + 32 < e →
                  P (i + 1) = wMulmodAt (P i) (loadWord st.memory (a + 32 * (i + 1))) rw ∧
                  loadWord st'.memory (s + 32 * i) = P (i + 1)) ∧
                VEnv.get V' "gp" = some (P ((e - a) / 32 - 2))))

  THE INVARIANT IS THE ENVIRONMENT EQUATION `V' = fwdEnv st.memory a s rw V j` (NOT a bundle of
  `VEnv.get`s): it is what makes the next iteration's guard and body reduce. `fwdEnv` and its six
  `get` lemmas are the bookkeeping; `restore_x_sets` is the block-exit step; the guard-FALSE branch
  needs `venv_get_set_*` on the anchored chain and the `fwdProd`/`writeWords` facts above; the
  `i = 0` clause is `hw0` (the added pre conjunct).

  NOTHING IN THIS FILE IS WIRED INTO A ROW. No root, register, SORRY.md or cone moves. -/

#assert_axioms helperBody_length [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_length [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_mptr_end [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_r [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_ret [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_gp [propext, Classical.choice, Quot.sound]
#assert_axioms fwdEnv_get_gp_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms ult_true_of_b2w_ne [propext, Classical.choice, Quot.sound]
#assert_axioms lt_of_iszero_eq_zero [propext, Classical.choice, Quot.sound]
#assert_axioms restore_reject_ret [propext, Classical.choice, Quot.sound]
#assert_axioms get_cons_self_x [propext, Classical.choice, Quot.sound]
#assert_axioms get_set_gp_same [propext, Classical.choice, Quot.sound]
#assert_axioms get_set_mptr_same [propext, Classical.choice, Quot.sound]
#assert_axioms get_set_gp_mptr_same [propext, Classical.choice, Quot.sound]
#assert_axioms restore_x_sets [propext, Classical.choice, Quot.sound]
#assert_axioms bi_forward_loop [propext, Classical.choice, Quot.sound]
#assert_axioms bi_forward_loop_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_backward_loop_form [propext, Classical.choice, Quot.sound]
#assert_axioms fwdProd_succ [propext, Classical.choice, Quot.sound]
#assert_axioms fwdWords_eq [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_writeWords_outside [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_eq_zero_iff [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_ne_zero_iff [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_toNat_lt [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_assoc [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_comm [propext, Classical.choice, Quot.sound]
#assert_axioms bwdAll_inv [propext, Classical.choice, Quot.sound]
#assert_axioms bwdInvVal_inv [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_length [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_gp_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_all_inv [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_second_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_r [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_ret [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMem_outside [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMem_scratch [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_bwdMem_untouched [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_bwdMem_written [propext, Classical.choice, Quot.sound]
#assert_axioms storeWord_outside [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMptr_eq [propext, Classical.choice, Quot.sound]
#assert_axioms bwdGp_eq [propext, Classical.choice, Quot.sound]



end Midfall.LoweringV3.BatchInvert
