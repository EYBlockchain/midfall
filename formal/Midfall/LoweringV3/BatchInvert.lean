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

theorem BatchInvertPost_zero {V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (succ rw : U256) (a e s : Nat) (hsucc : succ ≠ 0)
    (hret : VEnv.get V' "ret" = some 0)
    (hpf_some : (VEnv.get V' "precompile_failed").isSome)
    (henv : st'.env = st.env) (hhalt : st'.halted = st.halted)
    (hout : ∀ x, (x < a ∨ e ≤ x) → (x < s ∨ s + (e - a) + 0xc0 ≤ x) →
      st'.memory x = st.memory x) :
    BatchInvertPost (c := c) (g := g) st succ a e s rw V' st' := by
  obtain ⟨pf, hpf⟩ := Option.isSome_iff_exists.mp hpf_some
  refine ⟨0, pf, hret, hpf, henv, hhalt, hout, ?_, ?_, ?_⟩
  · intro hs
    exact absurd hs hsucc
  · intro hpfne
    rfl
  · intro hretne
    exact absurd hretne (by simp)

theorem BatchInvertPost_succ {V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (succ rw : U256) (a e s : Nat) (hsucc : succ ≠ 0)
    (hret : VEnv.get V' "ret" = some 1)
    (hpf : VEnv.get V' "precompile_failed" = some 0)
    (henv : st'.env = st.env) (hhalt : st'.halted = st.halted)
    (hout : ∀ x, (x < a ∨ e ≤ x) → (x < s ∨ s + (e - a) + 0xc0 ≤ x) →
      st'.memory x = st.memory x)
    (hcanon : ∀ i, a + 32 * i < e →
      (loadWord st.memory (a + 32 * i)).toNat < rw.toNat ∧
      loadWord st.memory (a + 32 * i) ≠ 0)
    (hinv : ∀ i, a + 32 * i < e →
      (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat ∧
      wMulmodAt (loadWord st'.memory (a + 32 * i)) (loadWord st.memory (a + 32 * i)) rw = 1) :
    BatchInvertPost (c := c) (g := g) st succ a e s rw V' st' := by
  refine ⟨1, 0, hret, hpf, henv, hhalt, hout, ?_, ?_, ?_⟩
  · intro hs
    exact absurd hs hsucc
  · intro hpfne
    exact absurd hpfne (by simp)
  · intro hretne
    refine ⟨rfl, ?_⟩
    intro i hi
    exact ⟨(hcanon i hi).1, (hcanon i hi).2, (hinv i hi).1, (hinv i hi).2⟩


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

/-- The last prefix product is the bridge product: `P(k-1) = mulmod (P(k-2)) x_last`. -/
theorem fwdProd_last (mem : Nat → UInt8) (a k : Nat) (rw : U256) (hk : 2 ≤ k) :
    fwdProd mem a rw (k - 1) =
      wMulmodAt (fwdProd mem a rw (k - 2)) (loadWord mem (a + 32 * (k - 1))) rw := by
  have hk' : k - 2 + 1 = k - 1 := by
    cases k with
    | zero => omega
    | succ k =>
        cases k with
        | zero => omega
        | succ k => omega
  have h := fwdProd_succ mem a rw (k - 2)
  rwa [hk'] at h

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

/-- A prefix product of canonical, non-zero words remains canonical and non-zero. -/
theorem fwdProd_canonical_nonzero (mem : Nat → UInt8) (a : Nat) (rw : U256)
    (hp : Nat.Prime rw.toNat) (n j : Nat)
    (hcanon : ∀ i, i ≤ n → (loadWord mem (a + 32 * i)).toNat < rw.toNat)
    (hne : ∀ i, i ≤ n → loadWord mem (a + 32 * i) ≠ 0) (hj : j ≤ n) :
    (fwdProd mem a rw j).toNat < rw.toNat ∧ fwdProd mem a rw j ≠ 0 := by
  have hr : rw ≠ 0 := by
    intro h0
    have : rw.toNat = 0 := by rw [h0]; rfl
    exact hp.ne_zero this
  induction j with
  | zero =>
      simpa [fwdProd] using ⟨hcanon 0 (by omega), hne 0 (by omega)⟩
  | succ j ih =>
      have hj' : j ≤ n := by omega
      obtain ⟨hcj, hnj⟩ := ih hj'
      have hc1 : (loadWord mem (a + 32 * (j + 1))).toNat < rw.toNat := hcanon (j + 1) (by omega)
      have hn1 : loadWord mem (a + 32 * (j + 1)) ≠ 0 := hne (j + 1) (by omega)
      rw [fwdProd_succ]
      exact ⟨wMulmodAt_toNat_lt hr,
        (wMulmodAt_ne_zero_iff hp hcj hc1).mpr ⟨hnj, hn1⟩⟩


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


theorem bwdEnv_get_first_mptr (mem : Nat → UInt8) (a s k : Nat) (rw invAll : U256)
    (V : VEnv (Bridge.Dialect c g)) (v : U256)
    (h : VEnv.get V "first_mptr" = some v) (j : Nat) :
    VEnv.get (bwdEnv mem a s k rw invAll V j) "first_mptr" = some v := by
  induction j with
  | zero => exact h
  | succ j ih =>
      simp only [bwdEnv]
      rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "first_mptr") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "first_mptr") (by decide),
        venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "first_mptr") (by decide)]
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


/-- One iteration of the `mptr` walk: `bwdMptr (j+1) = bwdMptr j - 32`. -/
theorem bwdMptr_succ (a k j : Nat) : bwdMptr a k (j + 1) = bwdMptr a k j - 32 := by
  unfold bwdMptr
  rw [show 32 * (j + 1) = 32 * j + 32 by ring]
  rw [BitVec.sub_sub]
  conv_rhs => rw [show (32 : U256) = BitVec.ofNat 256 32 from rfl, ← BitVec.ofNat_add]

/-- One iteration of the `gp_mptr` walk: `bwdGp (j+1) = bwdGp j - 32`. -/
theorem bwdGp_succ (s k j : Nat) : bwdGp s k (j + 1) = bwdGp s k j - 32 := by
  unfold bwdGp
  rw [show 32 * (j + 1) = 32 * j + 32 by ring]
  rw [BitVec.sub_sub]
  conv_rhs => rw [show (32 : U256) = BitVec.ofNat 256 32 from rfl, ← BitVec.ofNat_add]

/-! ## 4e. THE BACKWARD LOOP (HLP.1.c), PROVED

  Statement 29 with the §5 invariant. The statement takes `k` explicitly with `e - a = 32*k`
  (the caller supplies it from `(e-a) % 32 = 0`), which keeps the `bwdEnv_get_*` lemmas on the
  explicit `k` and avoids the `(e-a)/32` rewrite. The running inverse `all_inv` is
  `bwdAll … j`, the stored word is `bwdInvVal … (k-1-i)`, and the state is the `bwdMem` store
  chain. The tail (statements 30-33) and the summary are not in this file. -/

theorem get_cons_self_inv (V : VEnv (Bridge.Dialect c g)) (v : U256) :
    VEnv.get (("inv", v) :: V) "inv" = some v := rfl

theorem bi_backward_loop (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (rw : U256) (a e s k : Nat) (hae : a + 96 ≤ e) (hal : (e - a) % 32 = 0)
    (hk : e - a = 32 * k) (he : e < 2 ^ 256) (hs : s + (e - a) < 2 ^ 256)
    (hdisj : e ≤ s ∨ s + (e - a) ≤ a)
    (invAll : U256) (hrw : Nat.Prime rw.toNat) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts GenAst.emitBatchInvertAt) 29 1)
      (fun V st =>
        VEnv.get V "mptr" = some (bwdMptr a k 0) ∧
        VEnv.get V "gp_mptr" = some (bwdGp s k 0) ∧
        VEnv.get V "first_mptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "second_mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V "all_inv" = some invAll ∧ VEnv.get V "r" = some rw ∧
        (VEnv.get V "ret").isSome ∧
        (∀ i, i ≤ k - 3 → loadWord st.memory (s + 32 * i) = fwdProd st.memory a rw (i + 1)) ∧
        (∀ i, i < k → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
        wMulmodAt invAll (fwdProd st.memory a rw (k - 1)) rw = 1)
      (fun _ st V' st' o => o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
        VEnv.get V' "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        (∃ ai, VEnv.get V' "all_inv" = some ai ∧
          wMulmodAt ai (fwdProd st.memory a rw 1) rw = 1) ∧
        (∀ i, 2 ≤ i → i < k → loadWord st'.memory (a + 32 * i) =
          bwdInvVal st.memory a k rw invAll (k - 1 - i)) ∧
        (∀ i, i < 2 → loadWord st'.memory (a + 32 * i) = loadWord st.memory (a + 32 * i)) ∧
        (∀ x, (x < a ∨ a + 32 * k ≤ x) → (x < s ∨ s + 32 * k ≤ x) →
          st'.memory x = st.memory x) ∧
        (∀ i, i < k → (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat) ∧
        VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V' "r" = some rw) := by
  rw [bi_backward_loop_form]
  simp only [GenAst.yfor, GenAst.ylet, GenAst.ylit, GenAst.yvar, GenAst.yop, GenAst.yset,
    GenAst.yexpr]
  intro V st hpre
  obtain ⟨hmptr, hgpm, hfirst, hsecond, hinv0, hr, hret, hscratch, hcanon, hinvAll⟩ := hpre
  have he' : e = a + 32 * k := by omega
  have hsubea : e - a = 32 * k := by omega
  have hk3 : 3 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hek : a + 32 * k < 2 ^ 256 := by omega
  have hsk : s + 32 * k < 2 ^ 256 := by omega
  have hdisj' : a + 32 * k ≤ s ∨ s + 32 * k ≤ a := by
    simpa [he', hsubea] using hdisj
  let Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop :=
    fun V' st' o => o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
      VEnv.get V' "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
      (∃ ai, VEnv.get V' "all_inv" = some ai ∧
        wMulmodAt ai (fwdProd st.memory a rw 1) rw = 1) ∧
      (∀ i, 2 ≤ i → i < k → loadWord st'.memory (a + 32 * i) =
        bwdInvVal st.memory a k rw invAll (k - 1 - i)) ∧
      (∀ i, i < 2 → loadWord st'.memory (a + 32 * i) = loadWord st.memory (a + 32 * i)) ∧
      (∀ x, (x < a ∨ a + 32 * k ≤ x) → (x < s ∨ s + 32 * k ≤ x) → st'.memory x = st.memory x) ∧
      (∀ i, i < k → (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat) ∧
      VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a) ∧
      VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
      VEnv.get V' "r" = some rw
  change Midfall.Yul.WpTac.AllRuns funs V st
    [Stmt.forLoop []
      (Expr.builtin Op.lt [Expr.var "second_mptr", Expr.var "mptr"])
      []
      [ Stmt.letDecl ["inv"] (some (Expr.builtin Op.mulmod
          [Expr.var "all_inv", Expr.builtin Op.mload [Expr.var "gp_mptr"], Expr.var "r"]))
      , Stmt.assign ["all_inv"] (Expr.builtin Op.mulmod
          [Expr.var "all_inv", Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "r"])
      , Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr", Expr.var "inv"])
      , Stmt.assign ["mptr"] (Expr.builtin Op.sub
          [Expr.var "mptr", Expr.lit (Literal.number 0x20)])
      , Stmt.assign ["gp_mptr"] (Expr.builtin Op.sub
          [Expr.var "gp_mptr", Expr.lit (Literal.number 0x20)]) ]] Q
  let Inv : VEnv (Bridge.Dialect c g) → EvmState → Prop :=
    fun V' st' => ∃ j, j ≤ k - 2 ∧ V' = bwdEnv st.memory a s k rw invAll V j ∧
      ∃ aw, st' = { st with
        memory := bwdMem st.memory a k (bwdInvVal st.memory a k rw invAll) j, activeWords := aw }
  have hmain : Midfall.Yul.WpTac.AllRuns funs V st
      [Stmt.forLoop []
        (Expr.builtin Op.lt [Expr.var "second_mptr", Expr.var "mptr"])
        []
        [ Stmt.letDecl ["inv"] (some (Expr.builtin Op.mulmod
            [Expr.var "all_inv", Expr.builtin Op.mload [Expr.var "gp_mptr"], Expr.var "r"]))
        , Stmt.assign ["all_inv"] (Expr.builtin Op.mulmod
            [Expr.var "all_inv", Expr.builtin Op.mload [Expr.var "mptr"], Expr.var "r"])
        , Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var "mptr", Expr.var "inv"])
        , Stmt.assign ["mptr"] (Expr.builtin Op.sub
            [Expr.var "mptr", Expr.lit (Literal.number 0x20)])
        , Stmt.assign ["gp_mptr"] (Expr.builtin Op.sub
            [Expr.var "gp_mptr", Expr.lit (Literal.number 0x20)]) ]] Q := by
    refine allRuns_for_cons_wp (Bridge.Dialect c g) (Bopen c g) (Cnone _)
      (Bopen_sound c g) (Cnone_sound _) (n := 40) Inv ?hinit ?hstep
    · refine ⟨0, by omega, ?_, ?_⟩
      · simp [bwdEnv]
      · exact ⟨st.activeWords, by simp [bwdMem]⟩
    · intro Vi sti hInv
      obtain ⟨j, hj, hV, aw, hst⟩ := hInv
      subst hV
      subst hst
      have hrw0 : rw ≠ 0 := by
        intro h
        exact hrw.ne_zero (by rw [h]; rfl)
      have hmptr0 : VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32 * (k - 1))) := by
        simpa [bwdMptr] using hmptr
      have hgpm0 : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 (s + 32 * (k - 3))) := by
        simpa [bwdGp] using hgpm
      have hmptrj := bwdEnv_get_mptr st.memory a s k rw invAll V hmptr0 j
      have hgpmj := bwdEnv_get_gp_mptr st.memory a s k rw invAll V hgpm0 j
      have hallj := bwdEnv_get_all_inv st.memory a s k rw invAll V hinv0 j
      have hsecondj := bwdEnv_get_second_mptr st.memory a s k rw invAll V
        (BitVec.ofNat 256 (a + 32)) hsecond j
      have hrj := bwdEnv_get_r st.memory a s k rw invAll V hr j
      have hbwdMptrj : (bwdMptr a k j).toNat = a + 32 * (k - 1 - j) := by
        rw [bwdMptr_eq a k j hek (by omega)]
        exact ofNat_toNat (by omega)
      have hloadmptr : loadWord (bwdMem st.memory a k (bwdInvVal st.memory a k rw invAll) j)
          (bwdMptr a k j).toNat = loadWord st.memory (a + 32 * (k - 1 - j)) := by
        rw [hbwdMptrj]
        exact loadWord_bwdMem_untouched st.memory a k (bwdInvVal st.memory a k rw invAll)
          j (k - 1 - j) hk1 (by omega) (by omega)
      unfold wpIter
      simp only [wpE, wpA, Bopen, stepOp, bin, ter, un, hmptrj, hgpmj, hallj, hsecondj, hrj]
      refine ⟨?guardFalse, ?guardTrue⟩
      · -- exit: j = k-2
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 (a + 32)).ult (bwdMptr a k j)) = (0 : U256) := hguard
        rw [bwdMptr_eq a k j hek (by omega)] at h0
        have hge : a + 32 * (k - 1 - j) ≤ a + 32 :=
          LoopRule.lt_guard_false (by omega) (by omega) h0
        have hjk : j = k - 2 := by omega
        subst hjk
        clear hbwdMptrj hloadmptr
        refine ⟨?allRuns⟩
        intro V' st' o hrun
        cases hrun with
        | seqNil =>
        have hl := bwdEnv_length st.memory a s k rw invAll V (k - 2)
        have hres : restore V (bwdEnv st.memory a s k rw invAll V (k - 2)) =
            bwdEnv st.memory a s k rw invAll V (k - 2) := by
          simp [restore, hl]
        rw [hres]
        dsimp only [Q]
        refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- mptr
          clear hs hsk hdisj' hgpm0 hdisj hgpm
          rw [bwdEnv_get_mptr st.memory a s k rw invAll V hmptr0 (k - 2)]
          rw [bwdMptr_eq a k (k - 2) hek (by omega)]
          congr 1
          have hk21 : k - 1 - (k - 2) = 1 := by
            rw [Nat.sub_sub]
            omega
          rw [hk21, Nat.mul_one]
        · -- all_inv inverse
          refine ⟨bwdAll st.memory a k rw invAll (k - 2),
            bwdEnv_get_all_inv st.memory a s k rw invAll V hinv0 (k - 2), ?_⟩
          have h := bwdAll_inv st.memory a k rw invAll hrw0 hk2 hinvAll (k - 2) (by omega)
          simpa [show k - 1 - (k - 2) = 1 by omega] using h
        · -- inverted words
          intro i hi2 hik
          rw [loadWord_bwdMem_written st.memory a k (bwdInvVal st.memory a k rw invAll)
            (k - 2) i hk1 (by omega) (by omega) hik]
        · -- untouched words
          intro i hi2
          rw [loadWord_bwdMem_untouched st.memory a k (bwdInvVal st.memory a k rw invAll)
            (k - 2) i hk1 (by omega) (by omega)]
        · -- outside
          intro x hx hx2
          rw [bwdMem_outside st.memory a k (bwdInvVal st.memory a k rw invAll) (k - 2) x hk1
            (by omega) hx]
        · -- canonical outputs
          intro i hik
          by_cases hi2 : i < 2
          · rw [loadWord_bwdMem_untouched st.memory a k (bwdInvVal st.memory a k rw invAll)
              (k - 2) i hk1 (by omega) (by omega)]
            exact hcanon i hik
          · rw [loadWord_bwdMem_written st.memory a k (bwdInvVal st.memory a k rw invAll)
              (k - 2) i hk1 (by omega) (by omega) hik]
            exact wMulmodAt_toNat_lt hrw0
        · -- first_mptr
          rw [bwdEnv_get_first_mptr st.memory a s k rw invAll V (BitVec.ofNat 256 a) hfirst (k - 2)]
        · -- second_mptr
          rw [bwdEnv_get_second_mptr st.memory a s k rw invAll V (BitVec.ofNat 256 (a + 32)) hsecond (k - 2)]
        · -- r
          rw [bwdEnv_get_r st.memory a s k rw invAll V hr (k - 2)]
      · -- iteration: j < k-2
        intro hguard
        have h0 : b2w ((BitVec.ofNat 256 (a + 32)).ult (bwdMptr a k j)) ≠ (0 : U256) := hguard
        rw [bwdMptr_eq a k j hek (by omega)] at h0
        have hlt : j < k - 2 := by
          have := LoopRule.lt_guard_true (i := a + 32) (n := a + 32 * (k - 1 - j))
            (by omega) (by omega) h0
          omega
        have hj3 : j ≤ k - 3 := by omega
        have hbwdGpj : (bwdGp s k j).toNat = s + 32 * (k - 3 - j) := by
          rw [bwdGp_eq s k j hsk hj3]
          exact ofNat_toNat (by omega)
        have hloadgp : loadWord (bwdMem st.memory a k (bwdInvVal st.memory a k rw invAll) j)
            (bwdGp s k j).toNat = fwdProd st.memory a rw (k - 2 - j) := by
          rw [hbwdGpj]
          have hmem : loadWord (bwdMem st.memory a k (bwdInvVal st.memory a k rw invAll) j)
              (s + 32 * (k - 3 - j)) = loadWord st.memory (s + 32 * (k - 3 - j)) := by
            refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
            exact bwdMem_scratch st.memory a k s (bwdInvVal st.memory a k rw invAll) j
              (s + 32 * (k - 3 - j) + i) hk1 (by omega) hdisj' (by omega) (by omega)
          rw [hmem]
          simpa [show k - 3 - j + 1 = k - 2 - j by omega]
            using hscratch (k - 3 - j) (by omega)
        have hbwdAll_succ : wMulmodAt (bwdAll st.memory a k rw invAll j)
            (loadWord st.memory (a + 32 * (k - 1 - j))) rw =
            bwdAll st.memory a k rw invAll (j + 1) := rfl
        simp only [wpS, wpSS, wpE, wpA, Bopen, stepOp, bin, ter, un,
          hmptrj, hgpmj, hallj, hsecondj, hrj, hloadgp, hloadmptr,
          hbwdAll_succ, bwdInvVal,
          ofNat_toNat (by omega : a + 32 * (k - 1 - j) < 2 ^ 256)]
        simp only [List.zip_cons_cons, List.zip_nil_left, List.cons_append, List.nil_append,
          List.length_cons, List.length_nil,
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "r") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "all_inv") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "gp_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "second_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "ret") (by decide),
          hrj, hmptrj, hallj, hgpmj, hsecondj, get_cons_self_inv]
        simp [VEnv.set, VEnv.setMany, touchMemory, hloadmptr, hloadgp]
        let newAll : U256 := if rw = 0#256 then 0#256 else
          BitVec.ofNat 256 (BitVec.toNat (bwdAll st.memory a k rw invAll j) *
            BitVec.toNat (loadWord st.memory (a + 32 * (k - 1 - j))) % BitVec.toNat rw)
        have hnew : (if rw = 0#256 then 0#256 else
            BitVec.ofNat 256 (BitVec.toNat (bwdAll st.memory a k rw invAll j) *
              BitVec.toNat (loadWord st.memory (a + 32 * (k - 1 - j))) % BitVec.toNat rw)) =
            newAll := rfl
        rw [hnew]
        rw [get_cons_self_inv]
        simp only [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "gp_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv") (y := "all_inv") (by decide)]
        have hget1 : VEnv.get ((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll)
            "mptr" = some (bwdMptr a k j) := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "mptr") (by decide)]
          exact hmptrj
        have hget2 : VEnv.get (((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
            "mptr" (bwdMptr a k j - 32)) "mptr" = some (bwdMptr a k j - 32) :=
          venv_get_set_same (D := Bridge.Dialect c g) hget1
        have hget3 : VEnv.get (((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
            "mptr" (bwdMptr a k j - litValue (Literal.number 32))) "gp_mptr" =
            some (bwdGp s k j) := by
          rw [venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
            venv_get_set_ne (D := Bridge.Dialect c g) (x := "all_inv") (y := "gp_mptr") (by decide)]
          exact hgpmj
        refine ⟨?_⟩
        refine ⟨?_⟩
        rw [hget1]
        dsimp only
        refine ⟨?_⟩
        rw [hget3]
        dsimp only
        refine ⟨?_⟩
        simp only [Inv]
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · -- environment
          have hAA : ∀ (A : VEnv (Bridge.Dialect c g)), restore A A = A := by
            intro A
            simp [restore]
          rw [hAA]
          have hl : ((((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
                "mptr" (bwdMptr a k j - litValue (Literal.number 32))).set "gp_mptr"
                (bwdGp s k j - litValue (Literal.number 32))).length =
              (bwdEnv st.memory a s k rw invAll V j).length := by
            simp [venv_set_length (D := Bridge.Dialect c g)]
          rw [show restore (bwdEnv st.memory a s k rw invAll V j)
                (("inv", (if rw = 0#256 then 0#256 else BitVec.ofNat 256
                    (BitVec.toNat (bwdAll st.memory a k rw invAll j) *
                      BitVec.toNat (fwdProd st.memory a rw (k - 2 - j)) %
                        BitVec.toNat rw))) ::
                  (((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
                      "mptr" (bwdMptr a k j - litValue (Literal.number 32))).set "gp_mptr"
                      (bwdGp s k j - litValue (Literal.number 32))) =
                (((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
                    "mptr" (bwdMptr a k j - litValue (Literal.number 32))).set "gp_mptr"
                    (bwdGp s k j - litValue (Literal.number 32)) from
              restore_cons_length (D := Bridge.Dialect c g) (V := bwdEnv st.memory a s k rw invAll V j)
                (W := (((bwdEnv st.memory a s k rw invAll V j).set "all_inv" newAll).set
                    "mptr" (bwdMptr a k j - 32)).set "gp_mptr" (bwdGp s k j - 32)) (y := "inv") hl]
          have hnewAll : newAll = bwdAll st.memory a k rw invAll (j + 1) := by
            show wMulmodAt (bwdAll st.memory a k rw invAll j)
              (loadWord st.memory (a + 32 * (k - 1 - j))) rw = bwdAll st.memory a k rw invAll (j + 1)
            exact hbwdAll_succ
          rw [hnewAll, show litValue (Literal.number 32) = (32 : U256) from rfl,
            ← bwdMptr_succ, ← bwdGp_succ]
          rfl
        · -- state
          refine ⟨BitVec.ofNat 256 (activeWordsAfter (activeWordsAfter
            (activeWordsAfter (BitVec.toNat aw) (BitVec.toNat (bwdGp s k j)) 32 % 2 ^ 256)
            (BitVec.toNat (bwdMptr a k j)) 32 % 2 ^ 256) (BitVec.toNat (bwdMptr a k j)) 32), ?_⟩
          simp only [bwdMem, bwdInvVal]
          rw [show BitVec.toNat (bwdMptr a k j) = a + 32 * (k - 1 - j) from hbwdMptrj]
          rw [show a + 32 * (k - (j + 1)) = a + 32 * (k - 1 - j) by omega]
          rfl
  intro V' st' o hrun
  exact hmain V' st' o hrun


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

  **`bi_backward_loop` (HLP.1.c) IS PROVED at §4e** (standard three axioms, no `sorryAx`). The
  statement takes `k` explicitly with `e - a = 32*k`; the invariant is `all_inv = bwdAll … j`,
  the stored word `bwdInvVal … (k-1-i)`, the state the `bwdMem` chain. The remaining summary work
  is the staticcall/modexp step and the tail (statements 30-33).

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

open Midfall.LoweringV2.Blocks.VkLoading

theorem eval_mulmod_mload_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y z : String} {v : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.builtin Op.mload [Expr.var y], Expr.var z])
      (.vals [v] st')) :
    ∃ xv yv zv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      v = wMulmodAt xv (loadWord st.memory yv.toNat) zv ∧ st' = touchMemory st yv.toNat 32 := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hx with
      | var hxv =>
          cases hrest with
          | argsCons hrest2 hmload =>
              obtain ⟨yv, hyv, hv, hst⟩ := eval_mload_var_inv hmload
              subst hst
              cases hrest2 with
              | argsCons hnil hz =>
                  cases hnil with
                  | argsNil =>
                      cases hz with
                      | var hzv =>
                          simp only [builtinWithExternal, stepOp, ter, hv] at hbi
                          cases hbi
                          exact ⟨_, _, _, hxv, hyv, hzv, rfl, rfl⟩

theorem eval_mulmod_mload_var_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y z : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.builtin Op.mload [Expr.var y], Expr.var z])
      (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hrest2 hmload =>
              cases hrest2 with
              | argsCons hnil hz =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact eval_args_halt_false (es := [Expr.var x, Expr.builtin Op.mload [Expr.var y],
        Expr.var z]) (by
        intro e he st0 st1 hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact vkVar_ne_halts hh
        · exact eval_mload_var_halt_false hh
        · exact vkVar_ne_halts hh) hargs

theorem exec_let_mulmod_mload_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {x y z : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin Op.mulmod
        [Expr.var y, Expr.builtin Op.mload [Expr.var z], Expr.var "r"]))) V' st' o) :
    ∃ yv zv rv, VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      VEnv.get V "r" = some rv ∧ o = .normal ∧
      V' = (x, wMulmodAt yv (loadWord st.memory zv.toNat) rv) :: V ∧
      st' = touchMemory st zv.toNat 32 := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨yv, zv, rv, hyv, hzv, hrv, hv, hst⟩ := eval_mulmod_mload_var_inv he
      subst hst
      subst hv
      exact ⟨yv, zv, rv, hyv, hzv, hrv, rfl, rfl, rfl⟩
  | letHalt he => exact (eval_mulmod_mload_var_no_halt he).elim

theorem exec_mstore_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {x y : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin Op.mstore [Expr.var x, Expr.var y])) V' st' o) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ o = .normal ∧
      V' = V ∧ st' = { touchMemory st xv.toNat 32 with
        memory := storeWord st.memory xv.toNat yv } := by
  cases h with
  | exprStmt he =>
      obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv he
      cases hargs with
      | argsCons hrest hx =>
          cases hx with
          | var hxv =>
              cases hrest with
              | argsCons hnil hy =>
                  cases hnil with
                  | argsNil =>
                      cases hy with
                      | var hyv =>
                          simp only [builtinWithExternal, stepOp] at hbi
                          cases hbi
                          exact ⟨_, _, hxv, hyv, rfl, rfl, rfl⟩
  | exprStmtHalt he =>
      cases he with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hrest hx =>
              cases hrest with
              | argsCons hnil hy =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp] at hbi
                      cases hbi
      | builtinArgsHalt hargs =>
          exact (eval_args_halt_false (es := [Expr.var x, Expr.var y]) (by
            intro e he st0 st1 hh
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl
            · exact vkVar_ne_halts hh
            · exact vkVar_ne_halts hh) hargs).elim

theorem bi_tail_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 30 4 =
      [ GenAst.ylet "inv_first" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "all_inv", GenAst.yop EVM.Op.mload [GenAst.yvar "second_mptr"],
            GenAst.yvar "r"]),
        GenAst.ylet "inv_second" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "all_inv", GenAst.yop EVM.Op.mload [GenAst.yvar "first_mptr"],
            GenAst.yvar "r"]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "first_mptr", GenAst.yvar "inv_first"]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore [GenAst.yvar "second_mptr", GenAst.yvar "inv_second"]) ] := by
  kernel_rfl



open Midfall.Yul.Word

theorem bi_tail_contract (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (rw : U256) (a : Nat) (w0 w1 invAll retv pfv : U256) (ha : a + 32 < 2 ^ 256) (hr : rw ≠ 0)
    (hinv : wMulmodAt invAll (wMulmodAt w0 w1 rw) rw = 1) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 30 4)
      (fun V st =>
        VEnv.get V "all_inv" = some invAll ∧
        VEnv.get V "first_mptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "second_mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V "r" = some rw ∧
        VEnv.get V "ret" = some retv ∧
        VEnv.get V "precompile_failed" = some pfv ∧
        loadWord st.memory a = w0 ∧ loadWord st.memory (a + 32) = w1)
      (fun _ st V' st' o => o = .normal ∧
        VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V' "r" = some rw ∧
        loadWord st'.memory a = wMulmodAt invAll w1 rw ∧
        loadWord st'.memory (a + 32) = wMulmodAt invAll w0 rw ∧
        wMulmodAt (wMulmodAt invAll w1 rw) w0 rw = 1 ∧
        wMulmodAt (wMulmodAt invAll w0 rw) w1 rw = 1 ∧
        st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, (x < a ∨ a + 64 ≤ x) → st'.memory x = st.memory x) ∧
        VEnv.get V' "ret" = some retv ∧
        VEnv.get V' "precompile_failed" = some pfv) := by
  rw [bi_tail_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hinvAll, hfirst, hsecond, hrget, hretv, hpfv, hw0, hw1⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨av, pv, rv, hav, hpv, hrv, -, hV1, hst1⟩ :=
      exec_let_mulmod_mload_inv (x := "inv_first") (y := "all_inv") (z := "second_mptr") h1
    rw [hinvAll] at hav; injection hav with hav'
    rw [hsecond] at hpv; injection hpv with hpv'
    rw [hrget] at hrv; injection hrv with hrv'
    subst hav' hpv' hrv' hV1 hst1
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨av2, pv2, rv2, hav2, hpv2, hrv2, -, hV2, hst2⟩ :=
        exec_let_mulmod_mload_inv (x := "inv_second") (y := "all_inv") (z := "first_mptr") h2
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "all_inv") (by decide)] at hav2
      rw [hinvAll] at hav2; injection hav2 with hav2'
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "first_mptr") (by decide)] at hpv2
      rw [hfirst] at hpv2; injection hpv2 with hpv2'
      rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "r") (by decide)] at hrv2
      rw [hrget] at hrv2; injection hrv2 with hrv2'
      subst hav2' hpv2' hrv2' hV2 hst2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨xv, yv, hxv, hyv, -, hV3, hst3⟩ := exec_mstore_var_inv (x := "first_mptr") (y := "inv_first") h3
        rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_second") (y := "first_mptr") (by decide),
          venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "first_mptr") (by decide)] at hxv
        rw [hfirst] at hxv; injection hxv with hxv'
        simp [VEnv.get, List.find?] at hyv
        subst hxv' hyv hV3 hst3
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨xv2, yv2, hxv2, hyv2, -, hV4, hst4⟩ := exec_mstore_var_inv (x := "second_mptr") (y := "inv_second") h4
          rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_second") (y := "second_mptr") (by decide),
            venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "second_mptr") (by decide)] at hxv2
          rw [hsecond] at hxv2; injection hxv2 with hxv2'
          simp [VEnv.get, List.find?] at hyv2
          subst hxv2' hyv2 hV4 hst4
          cases hrest4
          have htoNat_a : (BitVec.ofNat 256 a).toNat = a := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have htoNat_a32 : (BitVec.ofNat 256 (a + 32)).toNat = a + 32 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
          refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- first_mptr
            rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_second") (y := "first_mptr") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "first_mptr") (by decide)]
            exact hfirst
          · -- second_mptr
            rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_second") (y := "second_mptr") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "second_mptr") (by decide)]
            exact hsecond
          · -- r
            rw [venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_second") (y := "r") (by decide),
              venv_get_cons_ne (D := Bridge.Dialect c g) (x := "inv_first") (y := "r") (by decide)]
            exact hrget
          · -- loadWord a
            rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) = 2 ^ 256 from by norm_num]
            simp only [htoNat_a, htoNat_a32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : a < 2 ^ 256), touchMemory, hw0, hw1]
            rw [loadWord_storeWord_disjoint _ (a + 32) a _ (by omega)]
            rw [loadWord_storeWord_same]
          · -- loadWord a+32
            rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) = 2 ^ 256 from by norm_num]
            simp only [htoNat_a, htoNat_a32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : a < 2 ^ 256), touchMemory, hw0, hw1]
            rw [loadWord_storeWord_same]
          · -- first inverse
            rw [wMulmodAt_assoc hr]
            rw [show wMulmodAt w1 w0 rw = wMulmodAt w0 w1 rw from
              wMulmodAt_comm (r := rw) (a := w1) (b := w0) hr]
            exact hinv
          · -- second inverse
            rw [wMulmodAt_assoc hr]
            exact hinv
          · -- env
            rfl
          · -- halted
            rfl
          · -- outside memory
            intro x hx
            simp only [touchMemory]
            have h1 : (a + 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = a + 32 := by omega
            have h2 : a % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = a := by omega
            rw [h1, h2, hw1, hw0]
            change storeWord (storeWord st.memory (BitVec.ofNat 256 a).toNat
              (wMulmodAt invAll w1 rw)) (BitVec.ofNat 256 (a + 32)).toNat
              (wMulmodAt invAll w0 rw) x = st.memory x
            rw [show (BitVec.ofNat 256 a).toNat = a from htoNat_a,
              show (BitVec.ofNat 256 (a + 32)).toNat = a + 32 from htoNat_a32]
            rw [storeWord_outside _ (a + 32) x _ (by omega)]
            rw [storeWord_outside _ a x _ (by omega)]
          · -- ret
            rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "inv_second") (y := "ret") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "inv_first") (y := "ret") (by decide)]
            exact hretv
          · -- precompile_failed
            rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "inv_second") (y := "precompile_failed") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                  (x := "inv_first") (y := "precompile_failed") (by decide)]
            exact hpfv
        · obtain ⟨-, -, -, -, ho4, -, -⟩ := exec_mstore_var_inv (x := "second_mptr") (y := "inv_second") h4
          exact absurd ho4 hne4
      · obtain ⟨-, -, -, -, ho3, -, -⟩ := exec_mstore_var_inv (x := "first_mptr") (y := "inv_first") h3
        exact absurd ho3 hne3
    · obtain ⟨-, -, -, -, -, -, ho2, -, -⟩ :=
        exec_let_mulmod_mload_inv (x := "inv_second") (y := "all_inv") (z := "first_mptr") h2
      exact absurd ho2 hne2
  · obtain ⟨-, -, -, -, -, -, ho1, -, -⟩ :=
      exec_let_mulmod_mload_inv (x := "inv_first") (y := "all_inv") (z := "second_mptr") h1
    exact absurd ho1 hne1


theorem eval_iszero_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var x]) (.vals [cv] st')) :
    ∃ rv, VEnv.get V x = some rv ∧ st' = st ∧ cv = b2w (rv = 0) := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hvar =>
      cases hnil with
      | argsNil =>
          cases hvar with
          | var hget =>
              simp only [builtinWithExternal, stepOp, un] at hbi
              cases hbi
              exact ⟨_, hget, rfl, rfl⟩

theorem eval_iszero_var_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var x]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := .iszero)
    (by
      intro a st r hr
      simp only [builtinWithExternal, stepOp, un] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h

theorem exec_guard_iszero_var {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {x : String} {rv : U256}
    (hget : VEnv.get V x = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var x]) [Stmt.leave]) V' st' o) :
    (rv ≠ 0 → o = .normal ∧ V' = V ∧ st' = st) ∧
      (rv = 0 → o = .leave ∧ V' = V ∧ st' = st) := by
  constructor
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨vv, hgetv, hst, hcv⟩ := eval_iszero_var_inv hc
        rw [hget] at hgetv
        injection hgetv with hvv
        subst hvv
        subst hst
        subst hcv
        simp [b2w, hrv] at hnz
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨vv, hgetv, hst, hcv⟩ := eval_iszero_var_inv hc
        rw [hget] at hgetv
        injection hgetv with hvv
        subst hvv
        subst hst
        exact ⟨rfl, rfl, rfl⟩
    | ifHalt hc => exact (eval_iszero_var_no_halt hc).elim
  · intro hrv
    subst hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨vv, hgetv, hst, hcv⟩ := eval_iszero_var_inv hc
        rw [hget] at hgetv
        injection hgetv with hvv
        subst hvv
        subst hst
        cases hbody with
        | block hb =>
            cases hb with
            | seqCons hleave hrest => cases hleave
            | seqStop hleave hne =>
                cases hleave
                refine ⟨rfl, ?_, rfl⟩
                simp [restore]
    | ifFalse hc hz =>
        obtain ⟨vv, hgetv, hst, hcv⟩ := eval_iszero_var_inv hc
        rw [hget] at hgetv
        injection hgetv with hvv
        subst hvv
        subst hst
        subst hcv
        exfalso
        exact absurd (show (1 : U256) = 0 from hz) (by decide)
    | ifHalt hc => exact (eval_iszero_var_no_halt hc).elim

theorem bi_head_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 0 2 =
      [ GenAst.yset "ret" (GenAst.yvar "success"),
        GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]) [Stmt.leave] ] := by
  kernel_rfl



theorem bi_prelude_head (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (succ rv0 : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 0 2)
      (fun V _ => VEnv.get V "success" = some succ ∧ VEnv.get V "ret" = some rv0)
      (fun Vpre st V' st' o =>
        (succ ≠ 0 ∧ o = .normal ∧ V' = VEnv.set Vpre "ret" succ ∧ st' = st) ∨
        (succ = 0 ∧ o = .leave ∧ V' = VEnv.set Vpre "ret" 0 ∧ st' = st)) := by
  rw [bi_head_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hsucc, hrv0⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨v, he, hV1⟩ := exec_assign_inv h1
    obtain ⟨hsv, rfl⟩ := eval_var_inv he
    rw [hsucc] at hsv
    injection hsv with hv
    subst hv
    subst hV1
    have hget : VEnv.get (VEnv.set V "ret" succ) "ret" = some succ :=
      venv_get_set_same (D := Bridge.Dialect c g) hrv0
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · cases hrest2
      by_cases hs : succ = 0
      · obtain ⟨ho, -, -⟩ := (exec_guard_iszero_var (x := "ret") hget h2).2 hs
        exact absurd ho (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)
      · obtain ⟨ho, hV2, hst2⟩ := (exec_guard_iszero_var (x := "ret") hget h2).1 hs
        subst hV2
        subst hst2
        exact Or.inl ⟨hs, rfl, rfl, rfl⟩
    · by_cases hs : succ = 0
      · obtain ⟨ho, hV2, hst2⟩ := (exec_guard_iszero_var (x := "ret") hget h2).2 hs
        subst hV2
        subst hst2
        subst hs
        rw [ho]
        exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨ho, -, -⟩ := (exec_guard_iszero_var (x := "ret") hget h2).1 hs
        exact absurd ho hne2
  · cases h1 with
    | assignVal he hl => exact absurd rfl hne1
    | assignHalt he => cases he


theorem eval_sub_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.sub [Expr.var x, Expr.var y]) (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = xv - yv ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hx with
      | var hxv =>
          cases hrest with
          | argsCons hnil hy =>
              cases hnil with
              | argsNil =>
                  cases hy with
                  | var hyv =>
                      simp only [builtinWithExternal, stepOp, bin] at hbi
                      cases hbi
                      exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem eval_sub_vars_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.sub [Expr.var x, Expr.var y]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .sub)
    (by
      intro a b st r hr
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) h

theorem exec_let_sub_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y z : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin Op.sub [Expr.var y, Expr.var z]))) V' st' o) :
    ∃ yv zv, VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      o = .normal ∧ V' = (x, yv - zv) :: V ∧ st' = st := by
  cases h with
  | letVal he hlen =>
      obtain ⟨v, rfl⟩ := list_length_one hlen
      obtain ⟨yv, zv, hyv, hzv, hv, hst⟩ := eval_sub_vars_inv he
      subst hv hst
      exact ⟨yv, zv, hyv, hzv, rfl, rfl, rfl⟩
  | letHalt he => exact (eval_sub_vars_no_halt he).elim

theorem eval_eq_var_lit_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String} {k : Nat} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.var x, Expr.lit (Literal.number k)]) (.vals [cv] st')) :
    ∃ xv, VEnv.get V x = some xv ∧ cv = b2w (xv = BitVec.ofNat 256 k) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hx with
      | var hxv =>
          cases hrest with
          | argsCons hnil hlit =>
              cases hnil with
              | argsNil =>
                  obtain ⟨hk, rfl⟩ := eval_lit_inv hlit
                  simp only [builtinWithExternal, stepOp, bin, hk] at hbi
                  cases hbi
                  exact ⟨_, hxv, rfl, rfl⟩

theorem eval_eq_var_lit_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x : String} {k : Nat}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.var x, Expr.lit (Literal.number k)]) (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .eq)
    (by
      intro a b st r hr
      simp only [builtinWithExternal, stepOp, bin] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
    (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) h

theorem eval_iszero_lt_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String} {cv : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
      (.vals [cv] st')) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧
      cv = b2w (b2w (xv.ult yv) = 0) ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hnil hlt =>
      cases hnil with
      | argsNil =>
          obtain ⟨xv, yv, hxv, hyv, hcv, hst⟩ := eval_lt_vars_inv hlt
          subst hst
          simp only [builtinWithExternal, stepOp, un, hcv] at hbi
          cases hbi
          exact ⟨_, _, hxv, hyv, rfl, rfl⟩

theorem eval_iszero_lt_vars_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
      (.halt st')) : False :=
  Midfall.LoweringV2.Blocks.VkLoading.vk_nh_unary (op := .iszero)
    (by
      intro a st r hr
      simp only [builtinWithExternal, stepOp, un] at hr
      cases hr
      exact ⟨_, _, rfl⟩)
    (fun _ _ hh => eval_lt_halt_false hh) h

theorem exec_guard_ret0_false {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {cond : Expr EVM.Op}
    (hfalse : ∀ st1 cv, EvalExpr (Bridge.Dialect c g) funs V st cond (.vals [cv] st1) → cv = 0)
    (hstate : ∀ st1 cv, EvalExpr (Bridge.Dialect c g) funs V st cond (.vals [cv] st1) → st1 = st)
    (hne : ∀ st1, EvalExpr (Bridge.Dialect c g) funs V st cond (.halt st1) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond cond [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave])
      V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  cases h with
  | ifTrue hc hnz hbody =>
      exact absurd (hfalse _ _ hc) hnz
  | ifFalse hc hz => exact ⟨rfl, rfl, hstate _ _ hc⟩
  | ifHalt hc => exact (hne _ hc).elim


def biSingleArm (consts : Inline.Consts) : Block EVM.Op :=
  [ GenAst.ylet "x" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr_start"]),
    GenAst.yif (GenAst.yop EVM.Op.iszero
      [GenAst.yop EVM.Op.lt [GenAst.yvar "x", GenAst.yvar "r"]])
      [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
    GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "x"])
      [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
    GenAst.ylet "single_scratch" (GenAst.yvar "scratch_mptr") ] ++
  GenAst.modexpFrameStores "single_scratch" (GenAst.yvar "x") (GenAst.yvar "r")
    Midfall.Generator.templateConstantsDefault ++
  [ GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
      [ (match consts.lookup "MODEXP_GAS" with
          | some v => Expr.lit (Literal.number v)
          | none => Expr.var "MODEXP_GAS")
      , GenAst.ylit 5, GenAst.yvar "single_scratch", GenAst.ylit 192,
        GenAst.yvar "single_scratch", GenAst.ylit 32 ])
  , GenAst.yset "ret" (GenAst.yop EVM.Op.and
      [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
        [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]])
  , GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"])
  , GenAst.yif (GenAst.yvar "ret")
      [GenAst.yexpr (GenAst.yop EVM.Op.mstore
        [GenAst.yvar "mptr_start", GenAst.yop EVM.Op.mload [GenAst.yvar "single_scratch"]])]
  , Stmt.leave ]


def biSingleHead : Block EVM.Op :=
  [ GenAst.ylet "x" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr_start"]),
    GenAst.yif (GenAst.yop EVM.Op.iszero
      [GenAst.yop EVM.Op.lt [GenAst.yvar "x", GenAst.yvar "r"]])
      [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
    GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "x"])
      [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
    GenAst.ylet "single_scratch" (GenAst.yvar "scratch_mptr") ]

def biSingleFrame (_consts : Inline.Consts) : Block EVM.Op :=
  GenAst.modexpFrameStores "single_scratch" (GenAst.yvar "x") (GenAst.yvar "r")
    Midfall.Generator.templateConstantsDefault

def biSingleTail (consts : Inline.Consts) : Block EVM.Op :=
  [ GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
      [ (match consts.lookup "MODEXP_GAS" with
          | some v => Expr.lit (Literal.number v)
          | none => Expr.var "MODEXP_GAS")
      , GenAst.ylit 5, GenAst.yvar "single_scratch", GenAst.ylit 192,
        GenAst.yvar "single_scratch", GenAst.ylit 32 ])
  , GenAst.yset "ret" (GenAst.yop EVM.Op.and
      [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
        [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]])
  , GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"])
  , GenAst.yif (GenAst.yvar "ret")
      [GenAst.yexpr (GenAst.yop EVM.Op.mstore
        [GenAst.yvar "mptr_start", GenAst.yop EVM.Op.mload [GenAst.yvar "single_scratch"]])]
  , Stmt.leave ]

theorem biSingleArm_eq (consts : Inline.Consts) :
    biSingleArm consts = biSingleHead ++ (biSingleFrame consts ++ biSingleTail consts) := by
  rfl

theorem bi_prelude_single_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 2 8 =
      [ GenAst.yif (Expr.builtin EVM.Op.lt [Expr.var "mptr_end", Expr.var "mptr_start"])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
        GenAst.ylet "count_bytes" (GenAst.yop EVM.Op.sub
          [GenAst.yvar "mptr_end", GenAst.yvar "mptr_start"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "count_bytes"]) [Stmt.leave],
        GenAst.yif (Expr.builtin EVM.Op.eq
          [Expr.var "count_bytes", Expr.lit (Literal.number 32)]) (biSingleArm consts),
        GenAst.ylet "gp_mptr" (GenAst.yvar "scratch_mptr"),
        GenAst.ylet "gp" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr_start"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero
          [GenAst.yop EVM.Op.lt [GenAst.yvar "gp", GenAst.yvar "r"]])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
        GenAst.ylet "mptr" (GenAst.yop EVM.Op.add
          [GenAst.yvar "mptr_start", GenAst.ylit 32]) ] := by
  kernel_rfl


theorem bi_prelude_form (consts : Inline.Consts) :
    ∃ body : Block EVM.Op,
      seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 2 8 =
        [ GenAst.yif (Expr.builtin EVM.Op.lt [Expr.var "mptr_end", Expr.var "mptr_start"])
            [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
          GenAst.ylet "count_bytes" (GenAst.yop EVM.Op.sub
            [GenAst.yvar "mptr_end", GenAst.yvar "mptr_start"]),
          GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "count_bytes"]) [Stmt.leave],
          GenAst.yif (Expr.builtin EVM.Op.eq [Expr.var "count_bytes", Expr.lit (Literal.number 32)]) body,
          GenAst.ylet "gp_mptr" (GenAst.yvar "scratch_mptr"),
          GenAst.ylet "gp" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr_start"]),
          GenAst.yif (GenAst.yop EVM.Op.iszero
            [GenAst.yop EVM.Op.lt [GenAst.yvar "gp", GenAst.yvar "r"]])
            [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
          GenAst.ylet "mptr" (GenAst.yop EVM.Op.add
            [GenAst.yvar "mptr_start", GenAst.ylit 32]) ] := by
  refine ⟨(match seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 2 8 with
    | [_, _, _, Stmt.cond _ body, _, _, _, _] => body
    | _ => []), ?_⟩
  kernel_rfl

theorem ofNat_sub_of_le (a e : Nat) (hae : a ≤ e) (he : e < 2 ^ 256) :
    ((BitVec.ofNat 256 e : U256) - BitVec.ofNat 256 a) = BitVec.ofNat 256 (e - a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (by omega : a < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : e - a < 2 ^ 256)]
  omega

theorem ofNat_ne_zero_of_pos {n : Nat} (h : 0 < n) (hn : n < 2 ^ 256) : (BitVec.ofNat 256 n : U256) ≠ 0 := by
  intro hz
  have := congrArg BitVec.toNat hz
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  simp at this
  omega

theorem ofNat_ne_of_ne {n m : Nat} (h : n ≠ m) (hn : n < 2 ^ 256) (hm : m < 2 ^ 256) :
    (BitVec.ofNat 256 n : U256) ≠ BitVec.ofNat 256 m := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact h this

theorem exec_guard_false {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {cond : Expr EVM.Op} {body : Block EVM.Op}
    (hfalse : ∀ st1 cv, EvalExpr (Bridge.Dialect c g) funs V st cond (.vals [cv] st1) → cv = 0)
    (hstate : ∀ st1 cv, EvalExpr (Bridge.Dialect c g) funs V st cond (.vals [cv] st1) → st1 = st)
    (hne : ∀ st1, EvalExpr (Bridge.Dialect c g) funs V st cond (.halt st1) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st (Stmt.cond cond body) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  cases h with
  | ifTrue hc hnz hbody => exact absurd (hfalse _ _ hc) hnz
  | ifFalse hc hz => exact ⟨rfl, rfl, hstate _ _ hc⟩
  | ifHalt hc => exact (hne _ hc).elim

theorem ofNat_ult_ofNat_false (a e : Nat) (h : a ≤ e) (he : e < 2 ^ 256) :
    (BitVec.ofNat 256 e).ult (BitVec.ofNat 256 a) = false := by
  rw [BitVec.ult]
  have hlt : ¬ (BitVec.ofNat 256 e).toNat < (BitVec.ofNat 256 a).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : e < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : a < 2 ^ 256)]
    omega
  exact decide_eq_false hlt

theorem ult_of_toNat_lt {x y : U256} (h : x.toNat < y.toNat) : x.ult y = true := by
  rw [BitVec.ult]
  exact decide_eq_true h

/-- The converse of `ult_of_toNat_lt`. -/
theorem toNat_lt_of_ult {x y : U256} (h : x.ult y = true) : x.toNat < y.toNat := by
  rw [BitVec.ult] at h
  exact of_decide_eq_true h

theorem exec_guard_ret0_lt_vars_false {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y : String} {xv yv : U256}
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (hfalse : xv.ult yv = false)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.lt [Expr.var x, Expr.var y])
        [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  refine exec_guard_ret0_false ?_ ?_ ?_ h
  · intro st0 cv hc
    obtain ⟨x0, y0, hx0, hy0, hcv, hst0⟩ := eval_lt_vars_inv hc
    rw [hx] at hx0; rw [hy] at hy0
    injection hx0 with h1; injection hy0 with h2
    subst h1 h2
    rw [hcv, hfalse]
    rfl
  · intro st0 cv hc
    obtain ⟨-, -, -, -, -, hst0⟩ := eval_lt_vars_inv hc
    exact hst0
  · intro st0 hc
    exact eval_lt_halt_false hc

theorem exec_guard_ret0_iszero_lt_vars_false {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y : String} {xv yv : U256}
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (hlt : xv.ult yv = true)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.builtin Op.lt [Expr.var x, Expr.var y]])
        [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  refine exec_guard_ret0_false ?_ ?_ ?_ h
  · intro st0 cv hc
    obtain ⟨x0, y0, hx0, hy0, hcv, hst0⟩ := eval_iszero_lt_vars_inv hc
    rw [hx] at hx0; rw [hy] at hy0
    injection hx0 with h1; injection hy0 with h2
    subst h1 h2
    rw [hcv, hlt]
    rfl
  · intro st0 cv hc
    obtain ⟨-, -, -, -, -, hst0⟩ := eval_iszero_lt_vars_inv hc
    exact hst0
  · intro st0 hc
    exact eval_iszero_lt_vars_no_halt hc

theorem b2w_eq_false_of_ne {x y : U256} (h : x ≠ y) : b2w (x = y) = 0 := by
  rw [b2w, decide_eq_false h]
  rfl

theorem exec_guard_false_eq_var_lit {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {k : Nat} {xv : U256} {body : Block EVM.Op}
    (hx : VEnv.get V x = some xv) (hne : xv ≠ BitVec.ofNat 256 k)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.eq [Expr.var x, Expr.lit (Literal.number k)]) body)
      V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  cases h with
  | ifTrue hc hnz hbody =>
      obtain ⟨x0, hx0, hcv, hst0⟩ := eval_eq_var_lit_inv hc
      rw [hx] at hx0
      injection hx0 with h1
      subst h1
      rw [hcv, b2w_eq_false_of_ne hne] at hnz
      exact absurd rfl hnz
  | ifFalse hc hz =>
      obtain ⟨-, -, -, hst0⟩ := eval_eq_var_lit_inv hc
      exact ⟨rfl, rfl, hst0⟩
  | ifHalt hc => exact (eval_eq_var_lit_no_halt hc).elim



theorem exec_mstore_add_var_normal {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    {x : String} {k : Nat} {val : Expr EVM.Op}
    (hval : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0 val (.vals [vv] st1)) → st1 = st0)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.builtin EVM.Op.add [Expr.var x, Expr.lit (Literal.number k)], val])) V' st' .normal) :
    ∃ xv vv, VEnv.get V x = some xv ∧ V' = V ∧
      st' = { touchMemory st ((xv + BitVec.ofNat 256 k).toNat) 32 with
        memory := storeWord st.memory ((xv + BitVec.ofNat 256 k).toNat) vv } := by
  obtain ⟨hV, st1, he, hst⟩ := exec_exprStmt_inv h
  subst hV hst
  obtain ⟨argvals, sti, hargs, hbi⟩ := eval_builtin_vals_inv he
  cases hargs with
  | argsCons hrest haddr =>
      cases hrest with
      | argsCons hnil hvalue =>
          cases hnil with
          | argsNil =>
              obtain ⟨xv, hxv, hcv, hstadd⟩ := eval_add_var_lit_inv haddr
              have hstv := hval _ _ ⟨_, hvalue⟩
              subst hstadd
              subst hstv
              subst hcv
              simp only [builtinWithExternal, stepOp] at hbi
              cases hbi
              exact ⟨xv, _, hxv, rfl, rfl⟩


theorem exec_mstore_add_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {k : Nat} {val : Expr EVM.Op}
    (hval : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0 val (.vals [vv] st1)) → st1 = st0)
    (hne : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 val (.halt st1) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.builtin EVM.Op.add [Expr.var x, Expr.lit (Literal.number k)], val])) V' st' o) :
    ∃ xv vv, VEnv.get V x = some xv ∧ o = .normal ∧ V' = V ∧
      st' = { touchMemory st ((xv + BitVec.ofNat 256 k).toNat) 32 with
        memory := storeWord st.memory ((xv + BitVec.ofNat 256 k).toNat) vv } := by
  cases h with
  | exprStmt he =>
      obtain ⟨xv, vv, hxv, hV, hst⟩ := exec_mstore_add_var_normal (c := c) (g := g)
        (funs := funs) (x := x) (k := k) (val := val) hval (Step.exprStmt he)
      exact ⟨xv, vv, hxv, rfl, hV, hst⟩
  | exprStmtHalt he =>
      cases he with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hrest haddr =>
              cases hrest with
              | argsCons hnil hvalue =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp] at hbi
                      cases hbi
      | builtinArgsHalt hargs =>
          cases hargs with
          | argsRestHalt h' =>
              cases h' with
              | argsRestHalt h'' => cases h''
              | argsHeadHalt _ hvalue => exact (hne _ _ hvalue).elim
          | argsHeadHalt _ haddr =>
              exact (Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .add)
                (by
                  intro a b st r hr
                  simp only [builtinWithExternal, stepOp, bin] at hr
                  cases hr
                  exact ⟨_, _, rfl⟩)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) haddr).elim


theorem ofNat_add_ofNat_toNat (p k : Nat) (h : p + k < 2 ^ 256) :
    ((BitVec.ofNat 256 p + BitVec.ofNat 256 k : U256)).toNat = p + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : p < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 256),
    Nat.mod_eq_of_lt h]

theorem bi_bridge_stores_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 15 6 =
      [ GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 0], GenAst.ylit 32]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 32], GenAst.ylit 32]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 64], GenAst.ylit 32]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 96], GenAst.yvar "gp"]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 128],
            GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2]]),
        GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yop EVM.Op.add [GenAst.yvar "gp_mptr", GenAst.ylit 160], GenAst.yvar "r"]) ] := by
  kernel_rfl



theorem exec_mstore_add_var_inv_val {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {k : Nat} {val : Expr EVM.Op} {v0 : U256}
    (hval : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0 val (.vals [vv] st1)) → st1 = st0)
    (hvchar : ∀ vv st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 val (.vals [vv] st1) → vv = v0)
    (hne : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0 val (.halt st1) → False)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.builtin EVM.Op.add [Expr.var x, Expr.lit (Literal.number k)], val])) V' st' o) :
    ∃ xv, VEnv.get V x = some xv ∧ o = .normal ∧ V' = V ∧
      st' = { touchMemory st ((xv + BitVec.ofNat 256 k).toNat) 32 with
        memory := storeWord st.memory ((xv + BitVec.ofNat 256 k).toNat) v0 } := by
  cases h with
  | exprStmt he =>
      obtain ⟨hV, st1, hev, hst⟩ := exec_exprStmt_inv (Step.exprStmt he)
      subst hst
      obtain ⟨argvals, sti, hargs, hbi⟩ := eval_builtin_vals_inv hev
      cases hargs with
      | argsCons hrest haddr =>
          cases hrest with
          | argsCons hnil hvalue =>
              cases hnil with
              | argsNil =>
                  obtain ⟨xv, hxv, hcv, hstadd⟩ := eval_add_var_lit_inv haddr
                  have hstv := hval _ _ ⟨_, hvalue⟩
                  subst hstadd
                  subst hstv
                  subst hcv
                  have hv := hvchar _ _ _ hvalue
                  subst hv
                  simp only [builtinWithExternal, stepOp] at hbi
                  cases hbi
                  exact ⟨xv, hxv, rfl, hV, rfl⟩
  | exprStmtHalt he =>
      cases he with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hrest haddr =>
              cases hrest with
              | argsCons hnil hvalue =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp] at hbi
                      cases hbi
      | builtinArgsHalt hargs =>
          cases hargs with
          | argsRestHalt h' =>
              cases h' with
              | argsRestHalt h'' => cases h''
              | argsHeadHalt _ hvalue => exact (hne _ _ hvalue).elim
          | argsHeadHalt _ haddr =>
              exact (Midfall.LoweringV2.Blocks.VkLoading.vk_nh_binary (op := .add)
                (by
                  intro a b st r hr
                  simp only [builtinWithExternal, stepOp, bin] at hr
                  cases hr
                  exact ⟨_, _, rfl⟩)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh)
                (fun _ _ hh => Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts hh) haddr).elim


theorem eval_mulmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y z : String} {vals : List U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.var y, Expr.var z]) (.vals vals st')) :
    ∃ xv yv zv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ VEnv.get V z = some zv ∧
      vals = [Midfall.LoweringV3.QuotientRows.wMulmodAt xv yv zv] ∧ st' = st := by
  obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv h
  cases hargs with
  | argsCons hrest hx =>
      cases hx with
      | var hgx =>
          cases hrest with
          | argsCons hrest2 hy =>
              cases hy with
              | var hgy =>
                  cases hrest2 with
                  | argsCons hnil hz =>
                      cases hnil with
                      | argsNil =>
                          cases hz with
                          | var hgz =>
                              simp only [builtinWithExternal, stepOp, ter] at hbi
                              cases hbi
                              exact ⟨_, _, _, hgx, hgy, hgz, rfl, rfl⟩

theorem eval_mulmod_vars_no_halt {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {x y z : String}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.mulmod [Expr.var x, Expr.var y, Expr.var z]) (.halt st')) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hrest hx =>
          cases hrest with
          | argsCons hrest2 hy =>
              cases hrest2 with
              | argsCons hnil hz =>
                  cases hnil with
                  | argsNil =>
                      simp only [builtinWithExternal, stepOp, ter] at hbi
                      cases hbi
  | builtinArgsHalt hargs =>
      exact eval_args_halt_false (es := [Expr.var x, Expr.var y, Expr.var z]) (by
        intro e he st0 st1 hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh
        · exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hh) hargs

theorem exec_assign_mulmod_vars_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y z : String} {xv yv zv : U256}
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (hz : VEnv.get V z = some zv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign [x] (Expr.builtin Op.mulmod [Expr.var x, Expr.var y, Expr.var z]))
      V' st' o) :
    o = .normal ∧ V' = VEnv.set V x (Midfall.LoweringV3.QuotientRows.wMulmodAt xv yv zv) ∧
      st' = st := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨xv', yv', zv', hgx, hgy, hgz, hvals, hst⟩ := eval_mulmod_vars_inv he
      rw [hx] at hgx; injection hgx with h1; subst h1
      rw [hy] at hgy; injection hgy with h2; subst h2
      rw [hz] at hgz; injection hgz with h3; subst h3
      subst hvals hst
      refine ⟨rfl, ?_, rfl⟩
      simp only [VEnv.setMany]
      rfl
  | assignHalt he => exact (eval_mulmod_vars_no_halt he).elim

theorem exec_guard_ret0_iszero_var_false {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {rv : U256}
    (hget : VEnv.get V x = some rv) (hne0 : rv ≠ 0)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var x])
        [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    o = .normal ∧ V' = V ∧ st' = st := by
  refine exec_guard_ret0_false ?_ ?_ ?_ h
  · intro st0 cv hc
    obtain ⟨vv, hvv, hst, hcv⟩ := eval_iszero_var_inv hc
    rw [hget] at hvv
    injection hvv with hv
    subst hv
    rw [hcv, b2w_eq_false_of_ne hne0]
  · intro st0 cv hc
    obtain ⟨-, -, hst, -⟩ := eval_iszero_var_inv hc
    exact hst
  · intro st0 hc
    exact eval_iszero_var_no_halt hc


theorem exec_reject_block {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.block [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    o = .leave ∧ V' = VEnv.set V "ret" 0 ∧ st' = st := by
  obtain ⟨Vb, stb, hb, hV, hst⟩ := exec_block_inv (funs := funs) h
  subst hV hst
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hb with
    ⟨V1, st1, hassign, hrest⟩ | ⟨hassign, hne1⟩
  · obtain ⟨v, he, hV1⟩ := exec_assign_inv (funs := hoist (Bridge.Dialect c g)
      [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave] :: funs) hassign
    obtain ⟨hv, hst0⟩ := eval_lit_inv he
    subst hv hst0 hV1
    cases hrest with
    | seqCons hleave hrest2 => cases hleave
    | seqStop hleave hne2 =>
        cases hleave
        exact ⟨rfl, restore_set_same, rfl⟩
  · cases hassign with
    | assignVal he hl => exact absurd rfl hne1
    | assignHalt he => cases he

theorem exec_guard_iszero_reject {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {rv : U256}
    (hx : VEnv.get V x = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin EVM.Op.iszero [Expr.var x])
        [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    (rv ≠ 0 → o = .normal ∧ V' = V ∧ st' = st) ∧
      (rv = 0 → o = .leave ∧ V' = VEnv.set V "ret" 0 ∧ st' = st) := by
  constructor
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨vv, hget, hst, hcv⟩ := eval_iszero_var_inv (x := x) hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        subst hst
        rw [hcv, b2w_eq_false_of_ne hrv] at hnz
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨-, -, hst, -⟩ := eval_iszero_var_inv (x := x) hc
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (eval_iszero_var_no_halt (x := x) hc).elim
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨-, -, hst, -⟩ := eval_iszero_var_inv (x := x) hc
        subst hst
        exact exec_reject_block (funs := funs) hbody
    | ifFalse hc hz =>
        obtain ⟨vv, hget, hst, hcv⟩ := eval_iszero_var_inv (x := x) hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        subst hst
        subst hrv
        rw [hcv] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (eval_iszero_var_no_halt (x := x) hc).elim

theorem exec_guard_iszero_lt_reject {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x y : String} {xv yv : U256}
    (hx : VEnv.get V x = some xv) (hy : VEnv.get V y = some yv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin EVM.Op.iszero
        [Expr.builtin EVM.Op.lt [Expr.var x, Expr.var y]])
        [Stmt.assign ["ret"] (Expr.lit (Literal.number 0)), Stmt.leave]) V' st' o) :
    (xv.ult yv = true → o = .normal ∧ V' = V ∧ st' = st) ∧
      (xv.ult yv = false → o = .leave ∧ V' = VEnv.set V "ret" 0 ∧ st' = st) := by
  constructor
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨x0, y0, hx0, hy0, hcv, -⟩ := eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0
        rw [hy] at hy0
        injection hx0 with h1
        injection hy0 with h2
        subst h1 h2
        rw [hcv, hlt] at hnz
        change (0 : U256) ≠ 0 at hnz
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨-, -, -, -, -, hst⟩ := eval_iszero_lt_vars_inv (x := x) (y := y) hc
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim
  · intro hlt
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨-, -, -, -, -, hst⟩ := eval_iszero_lt_vars_inv (x := x) (y := y) hc
        subst hst
        exact exec_reject_block (funs := funs) hbody
    | ifFalse hc hz =>
        obtain ⟨x0, y0, hx0, hy0, hcv, hst⟩ := eval_iszero_lt_vars_inv (x := x) (y := y) hc
        rw [hx] at hx0; rw [hy] at hy0
        injection hx0 with h1; injection hy0 with h2
        subst h1 h2
        subst hst
        rw [hcv, hlt] at hz
        change (1 : U256) = (0 : U256) at hz
        exact absurd hz (by decide)
    | ifHalt hc => exact (eval_iszero_lt_vars_no_halt (x := x) (y := y) hc).elim


theorem bi_bridge_guard1_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 12 1 =
      [GenAst.yif (GenAst.yop EVM.Op.iszero
        [GenAst.yop EVM.Op.lt [GenAst.yvar "x_last", GenAst.yvar "r"]])
        [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave]] := by
  kernel_rfl

theorem bi_bridge_guard2_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 14 1 =
      [GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "gp"])
        [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave]] := by
  kernel_rfl

theorem bi_bridge_guard_xlast (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (xv rw : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 12 1)
      (fun V st => VEnv.get V "x_last" = some xv ∧ VEnv.get V "r" = some rw)
      (fun V0 st V' st' o =>
        (xv.ult rw = true → o = .normal ∧ V' = V0 ∧ st' = st) ∧
        (xv.ult rw = false → o = .leave ∧ V' = VEnv.set V0 "ret" 0 ∧ st' = st)) := by
  rw [bi_bridge_guard1_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hx, hr⟩ := hpre
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h, rest⟩ | ⟨h, _⟩
  · cases rest
    exact exec_guard_iszero_lt_reject (funs := funs) (x := "x_last") (y := "r") hx hr h
  · exact exec_guard_iszero_lt_reject (funs := funs) (x := "x_last") (y := "r") hx hr h

theorem bi_bridge_guard_gp (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (rv : U256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 14 1)
      (fun V st => VEnv.get V "gp" = some rv)
      (fun V0 st V' st' o =>
        (rv ≠ 0 → o = .normal ∧ V' = V0 ∧ st' = st) ∧
        (rv = 0 → o = .leave ∧ V' = VEnv.set V0 "ret" 0 ∧ st' = st)) := by
  rw [bi_bridge_guard2_form]
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h, rest⟩ | ⟨h, _⟩
  · cases rest
    exact exec_guard_iszero_reject (funs := funs) (x := "gp") hpre h
  · exact exec_guard_iszero_reject (funs := funs) (x := "gp") hpre h


theorem bi_bridge_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 10 =
      [GenAst.ylet "x_last" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero
          [GenAst.yop EVM.Op.lt [GenAst.yvar "x_last", GenAst.yvar "r"]])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
        GenAst.yset "gp" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "gp", GenAst.yvar "x_last", GenAst.yvar "r"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "gp"])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave]] ++
        seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 15 6 := by
  rw [bi_bridge_stores_form]
  kernel_rfl


#assert_axioms eval_mulmod_mload_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_mulmod_mload_var_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_let_mulmod_mload_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_mstore_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms bi_tail_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_tail_contract [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_var_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_iszero_var [propext, Classical.choice, Quot.sound]
#assert_axioms bi_head_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_prelude_head [propext, Classical.choice, Quot.sound]
#assert_axioms eval_sub_vars_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_sub_vars_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_let_sub_vars_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_eq_var_lit_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_eq_var_lit_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_lt_vars_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_iszero_lt_vars_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_ret0_false [propext, Classical.choice, Quot.sound]
#assert_axioms bi_prelude_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_prelude_single_form [propext, Classical.choice, Quot.sound]
#assert_axioms BatchInvertPost_zero [propext, Classical.choice, Quot.sound]
#assert_axioms BatchInvertPost_succ [propext, Classical.choice, Quot.sound]
#assert_axioms biSingleArm_eq [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_sub_of_le [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_ne_zero_of_pos [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_ne_of_ne [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_false [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_ult_ofNat_false [propext, Classical.choice, Quot.sound]
#assert_axioms ult_of_toNat_lt [propext, Classical.choice, Quot.sound]
#assert_axioms toNat_lt_of_ult [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_ret0_lt_vars_false [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_ret0_iszero_lt_vars_false [propext, Classical.choice, Quot.sound]
#assert_axioms b2w_eq_false_of_ne [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_false_eq_var_lit [propext, Classical.choice, Quot.sound]
#assert_axioms exec_mstore_add_var_normal [propext, Classical.choice, Quot.sound]
#assert_axioms exec_mstore_add_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_add_ofNat_toNat [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_stores_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_form [propext, Classical.choice, Quot.sound]
#assert_axioms exec_mstore_add_var_inv_val [propext, Classical.choice, Quot.sound]
#assert_axioms eval_mulmod_vars_inv [propext, Classical.choice, Quot.sound]
#assert_axioms eval_mulmod_vars_no_halt [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_mulmod_vars_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_ret0_iszero_var_false [propext, Classical.choice, Quot.sound]
#assert_axioms exec_reject_block [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_iszero_reject [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_iszero_lt_reject [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_guard1_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_guard2_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_guard_xlast [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_guard_gp [propext, Classical.choice, Quot.sound]
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
#assert_axioms fwdProd_canonical_nonzero [propext, Classical.choice, Quot.sound]
#assert_axioms fwdWords_eq [propext, Classical.choice, Quot.sound]
#assert_axioms fwdProd_last [propext, Classical.choice, Quot.sound]
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
#assert_axioms bwdEnv_get_first_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms bwdEnv_get_ret [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMem_outside [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMem_scratch [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_bwdMem_untouched [propext, Classical.choice, Quot.sound]
#assert_axioms loadWord_bwdMem_written [propext, Classical.choice, Quot.sound]
#assert_axioms storeWord_outside [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMptr_eq [propext, Classical.choice, Quot.sound]
#assert_axioms bwdGp_eq [propext, Classical.choice, Quot.sound]
#assert_axioms bwdMptr_succ [propext, Classical.choice, Quot.sound]
#assert_axioms bwdGp_succ [propext, Classical.choice, Quot.sound]
#assert_axioms bi_backward_loop [propext, Classical.choice, Quot.sound]



end Midfall.LoweringV3.BatchInvert
