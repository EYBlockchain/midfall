-- |
-- Midfall.LoweringV3.LagrangeBlock
--
-- T3.9.f (WP A4), THE WHOLE-BLOCK COMPOSITION OF THE LAGRANGE INNER SCOPE. This file states the
-- post the card names - `LagRel` at the block's own memory, the six slot stores, and the memory
-- outside the denominator window, the batch-inversion scratch window and the six slot windows - and
-- PROVES it from the landed one-statement and loop contracts of `LagrangeRows` / `BatchInvert`,
-- with ONE internal hypothesis for statement 10 only:
--
--   `BatchInvertCallSegment` - the `batch_invert` call's own segment contract, post
--   `BatchInvertCallPost` (the caller-side mirror of A5's `BatchInvertPost`: the callee's return
--   words are bound to the caller's `success` / `lagrange_precompile_failed`).
--
-- It is NOT a row, bundle or root hypothesis: `BatchInvertCallSegment` is a `StmtsContractAll` of
-- `seg (lagInner ...) 10 1`, i.e. the exact statement A5's `batch_invert_summary` will discharge.
--
-- No fixture (D-P71): every statement is quantified over the table, the layout values and the
-- window fits.
import Midfall.LoweringV3.BatchInvert

set_option autoImplicit false

namespace Midfall.LoweringV3.LagrangeBlock

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.Lowering.GenAst Midfall.LoweringV3.QuotientRows
open Midfall.LoweringV3.LagrangeRows Midfall.LoweringV3.BatchInvert

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

variable {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. THE CALL'S POST, CALLER-SIDE

`BatchInvertPost` (BatchInvert.lean:140) is stated over the CALLEE's environment: its return words
are `ret` / `precompile_failed`. The caller of `batch_invert` binds those two words to `success` /
`lagrange_precompile_failed`. This structure is the same post with the names the caller uses. -/

/-- The caller-side `BatchInvertPost`: what `success, lagrange_precompile_failed := batch_invert(..)`
    leaves in the CALLER's environment and state. `ret` is the callee's return word (the caller's
    new `success`), `pf` its second word. Every clause is a projection of `BatchInvertPost` once the
    two word equations `success = ret` / `failed = pf` are known. -/
def BatchInvertCallPost (V : VEnv (Bridge.Dialect c g)) (st st' : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (succ : U256) (a e s : Nat) (rw : U256) : Prop :=
  ∃ ret pf, VEnv.get V' "success" = some ret ∧
    VEnv.get V' "lagrange_precompile_failed" = some pf ∧
    V' = VEnv.set (VEnv.set V "success" ret) "lagrange_precompile_failed" pf ∧
    st'.env = st.env ∧ st'.halted = st.halted ∧
    (∀ x, (x < a ∨ e ≤ x) → (x < s ∨ s + (e - a) + 0xc0 ≤ x) → st'.memory x = st.memory x) ∧
    (succ = 0 → ret = 0 ∧ pf = 0 ∧ st'.memory = st.memory) ∧
    (pf ≠ 0 → ret = 0) ∧
    (ret ≠ 0 → pf = 0 ∧ ∀ i, a + 32 * i < e →
      (loadWord st.memory (a + 32 * i)).toNat < rw.toNat ∧
      loadWord st.memory (a + 32 * i) ≠ 0 ∧
      (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat ∧
      wMulmodAt (loadWord st'.memory (a + 32 * i)) (loadWord st.memory (a + 32 * i)) rw = 1)

/-- **STATEMENT 10'S SEGMENT CONTRACT, AS A NAMED INTERNAL HYPOTHESIS.** The segment is
    `seg (lagInner consts k n m) 10 1` (the two-value `batch_invert` call). Its pre pins the
    arguments (`mptr_end = D + 32(n+m)`, the denominator cursor the loop left); its post is
    `o = .normal` and `BatchInvertCallPost`. Discharged by A5's `batch_invert_summary` through
    `Step.callOk` plus the `ysetN` assignment's `VEnv.setMany`; nothing here restates that summary. -/
def BatchInvertCallSegment (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (k n m D aS : Nat) (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (succ rw : U256) : Prop :=
  StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
    (seg (lagInner consts k n m) 10 1)
    (fun V _ =>
      VEnv.get V "success" = some succ ∧ VEnv.get V "r" = some rw ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))))
    (fun V st V' st' o => o = .normal ∧
      BatchInvertCallPost (c := permissive (callsOf product)) (g := g) V st st' V' succ
        D (D + 32 * (n + m) + 32) aS rw)

/-! ## 2. THE MEMORY-OUTSIDE WINDOW VOCABULARY -/

/-- `st.memory` agrees with `m0` outside the denominator window `[D, D+lenS)`, the scratch window
    `[aScr, aScr+lenScr)` and each slot window `[q, q+32)`. -/
def MemSameOut (m0 : Nat → UInt8) (st : EvmState) (D lenS aScr lenScr : Nat)
    (slots : List Nat) : Prop :=
  ∀ a, (a < D ∨ D + lenS ≤ a) → (a < aScr ∨ aScr + lenScr ≤ a) →
    (∀ q ∈ slots, a < q ∨ q + 32 ≤ a) → st.memory a = m0 a

/-- A narrower window still implies the wider one: the only monotonicity `MemSameOut` needs. -/
theorem MemSameOut.mono {m0 : Nat → UInt8} {st : EvmState} {D lenS aScr lenScr D' lenS' aScr'
    lenScr' : Nat} {slots : List Nat}
    (h : MemSameOut m0 st D lenS aScr lenScr slots)
    (hD : D' ≤ D) (hDe : D + lenS ≤ D' + lenS') (hS : aScr' ≤ aScr)
    (hSe : aScr + lenScr ≤ aScr' + lenScr') :
    MemSameOut m0 st D' lenS' aScr' lenScr' slots := by
  intro a ha hb hs
  exact h a (by rcases ha with h' | h' <;> omega) (by rcases hb with h' | h' <;> omega) hs

theorem MemSameOut.trans {m0 : Nat → UInt8} {st₁ st₂ : EvmState} {D lenS aScr lenScr : Nat}
    {slots : List Nat}
    (h₁ : MemSameOut m0 st₁ D lenS aScr lenScr slots)
    (h₂ : MemSameOut st₁.memory st₂ D lenS aScr lenScr slots) :
    MemSameOut m0 st₂ D lenS aScr lenScr slots := by
  intro a ha hb hs
  rw [h₂ a ha hb hs, h₁ a ha hb hs]

/-- The state's memory is unchanged: the outside condition is vacuous. -/
theorem MemSameOut.of_memory_eq {m0 : Nat → UInt8} {st : EvmState} {D lenS aScr lenScr : Nat}
    {slots : List Nat} (h : st.memory = m0) :
    MemSameOut m0 st D lenS aScr lenScr slots := by
  intro a _ _ _; rw [h]

/-- A loop contract's `MemSameOutside` at a narrower window widens to `MemSameOut`. -/
theorem MemSameOut.of_outside {st st0 : EvmState} {lo len D lenS aScr lenScr : Nat}
    {slots : List Nat} (h : MemSameOutside st0 st lo len) (hD : D ≤ lo)
    (hDe : lo + len ≤ D + lenS) :
    MemSameOut st0.memory st D lenS aScr lenScr slots := by
  intro a ha hb hs
  exact h a (by rcases ha with h' | h' <;> omega)

/-- Reading a whole word through two outside windows. -/
theorem loadWord_of_outside {st st' : EvmState} {lo len so leno p : Nat}
    (h : ∀ a, (a < lo ∨ lo + len ≤ a) → (a < so ∨ so + leno ≤ a) →
      st'.memory a = st.memory a)
    (hp : p + 32 ≤ lo ∨ lo + len ≤ p) (hps : p + 32 ≤ so ∨ so + leno ≤ p) :
    loadWord st'.memory p = loadWord st.memory p := by
  refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
  exact h (p + i) (by rcases hp with h' | h' <;> omega) (by rcases hps with h' | h' <;> omega)

/-- Reading a whole word through a `MemSameOutside` window: a word fully outside the window reads
    the same. -/
theorem loadWord_of_memSameOutside {st st' : EvmState} {lo len p : Nat}
    (h : MemSameOutside st st' lo len) (hp : p + 32 ≤ lo ∨ lo + len ≤ p) :
    loadWord st'.memory p = loadWord st.memory p := by
  refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
  exact h (p + i) (by rcases hp with h' | h' <;> omega)

/-- A single store at a byte address strictly inside the denominator window keeps the outside
    condition. -/
theorem MemSameOut.store_inside {m0 : Nat → UInt8} {st : EvmState} {D lenS aScr lenScr : Nat}
    {slots : List Nat} {p : Nat} {v : U256}
    (h : MemSameOut m0 st D lenS aScr lenScr slots) (hp : D ≤ p) (hp2 : p + 32 ≤ D + lenS) :
    MemSameOut m0 { st with memory := storeWord st.memory p v } D lenS aScr lenScr slots := by
  intro a ha hb hs
  show storeWord st.memory p v a = m0 a
  rw [storeWord_outside st.memory p v a (by rcases ha with h' | h' <;> omega)]
  exact h a ha hb hs

/-- A single store at a slot address keeps the outside condition, provided a point outside every
    slot window is outside this slot's 32-byte window. -/
theorem MemSameOut.store_slot {m0 : Nat → UInt8} {st : EvmState} {D lenS aScr lenScr : Nat}
    {slots : List Nat} {q : Nat} {v : U256} (hq : q ∈ slots)
    (h : MemSameOut m0 st D lenS aScr lenScr slots) :
    MemSameOut m0 { st with memory := storeWord st.memory q v } D lenS aScr lenScr slots := by
  intro a ha hb hs
  show storeWord st.memory q v a = m0 a
  rw [storeWord_outside st.memory q v a (by rcases hs q hq with h' | h' <;> omega)]
  exact h a ha hb hs

/-! ## 3. THE PHASE RELATION

`LagG i` is the conjunction of facts at the boundary before statement group `i` (groups in §4).
Every group contract below lands exactly on the next. The phase-dependent values are parameters so
that no case has to quantify anything existentially. -/

/-- The denominator index `i` (for `i < n+m`) is `x - ωᵢ`. -/
def lagDen (rw xw omw w0 : U256) : Nat → U256 :=
  fun i => wAddmodAt xw (rw - omegaPows rw omw w0 i) rw

/-- The six slot store addresses, in statement order. -/
def lagSlots (aXN aXN1 aLL aLB aL0 aIE : Nat) : List Nat :=
  [aXN, aXN1, aLL, aLB, aL0, aIE]

/-- The static data of one `lagInner` instantiation (the table's site values and the block's
table words). Every field is a value the render supplies; the fits and disjointness facts are
hypotheses of the block contract, not fields. -/
structure LagCfg (consts : Inline.Consts) (cd : Bytes) (k n m : Nat) where
  D : Nat
  s : Nat
  aX : Nat
  aO : Nat
  aL : Nat
  aN : Nat
  aI : Nat
  aXN : Nat
  aXN1 : Nat
  aLL : Nat
  aLB : Nat
  aL0 : Nat
  aIE : Nat
  rw : U256
  succ : U256
  xw : U256
  omw : U256
  w0 : U256
  nInv : U256

/-- The phase relations, one plain definition per phase (0 = the block's pre-state, 15 = its
post after the six slot stores). The earlier single 16-branch `match` was rejected by the
elaborator: `whnf` of the match at phase >= 4 exceeded 1M heartbeats because the branch body is
substituted against the (large) growing `VEnv`. A plain `abbrev` per phase unfolds in one step,
with no match and no substitution. -/

def LagP0 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP1 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP2 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
    VEnv.get V "x" = some C.xw ∧ VEnv.get V "x_n" = some C.xw ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP3 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "x" = some C.xw ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP4 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x" = some C.xw ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP5 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x" = some C.xw ∧
    VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP6 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "mptr" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    (∀ i, i < n + m → loadWord st.memory (C.D + 32 * i) = lagDen C.rw C.xw C.omw C.w0 i) ∧
    loadWord st.memory C.aL = C.w0 ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP7 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (_ret _pf : U256) (_inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
    VEnv.get V "lagrange_precompile_failed" = some 0 ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    VEnv.get V "mptr" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
    loadWord st.memory (C.D + 32 * (n + m)) = wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw ∧
    (∀ i, i < n + m → loadWord st.memory (C.D + 32 * i) = lagDen C.rw C.xw C.omw C.w0 i) ∧
    loadWord st.memory C.aL = C.w0 ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP8 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "r" = some C.rw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    (VEnv.get V "mptr").isSome ∧
    VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
    loadWord st.memory C.aL = C.w0 ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0 ∧
      (∀ i, i < n + m → loadWord st.memory (C.D + 32 * i) = lagDen C.rw C.xw C.omw C.w0 i) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m + 1 → loadWord st.memory (C.D + 32 * i) = inv i) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      wMulmodAt (inv (n + m)) (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.rw = 1 ∧
      (inv (n + m)).toNat < C.rw.toNat ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP9 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "r" = some C.rw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
    VEnv.get V "l_i_common" =
      some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
    loadWord st.memory C.aL = C.w0 ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0 ∧
      (∀ i, i < n + m → loadWord st.memory (C.D + 32 * i) = lagDen C.rw C.xw C.omw C.w0 i) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m + 1 → loadWord st.memory (C.D + 32 * i) = inv i) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      wMulmodAt (inv (n + m)) (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.rw = 1 ∧
      (inv (n + m)).toNat < C.rw.toNat ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP10 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "r" = some C.rw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    VEnv.get V "l_i_common" =
      some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP11 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "r" = some C.rw ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "l_i_common" =
      some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
    VEnv.get V "l_blind" = some (loadWord st.memory (C.D + 32)) ∧
    VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (C.D + 64)) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP12 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "r" = some C.rw ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "l_i_common" =
      some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
    VEnv.get V "l_blind" =
      some (wSum C.rw (fun i => loadWord st.memory (C.D + 64 + 32 * i)) (m - 2)
        (loadWord st.memory (C.D + 32))) ∧
    VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (C.D + 32 * m)) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP13 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "instance_eval" =
      some (wSum C.rw (fun j => wMulmodAt (loadWord st.memory (C.D + 32 * m + 32 * j))
        (cdWord cd (C.aI + 32 * j)) C.rw) n 0) ∧
    VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (C.D + 32 * m + 32 * n)) ∧
    VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP14 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "omega" = some C.omw ∧
    VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
    VEnv.get V "x_n_minus_1_inv" = some (loadWord st.memory (C.D + 32 * (n + m))) ∧
    VEnv.get V "l_last" = some (loadWord st.memory C.D) ∧
    VEnv.get V "l_blind" =
      some (wSum C.rw (fun i => loadWord st.memory (C.D + 64 + 32 * i)) (m - 2)
        (loadWord st.memory (C.D + 32))) ∧
    VEnv.get V "l_0" = some (loadWord st.memory (C.D + 32 * m)) ∧
    VEnv.get V "instance_eval" =
      some (wSum C.rw (fun j => wMulmodAt (loadWord st.memory (C.D + 32 * m + 32 * j))
        (cdWord cd (C.aI + 32 * j)) C.rw) n 0) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)

def LagP15 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
      VEnv.get V "success" = some ret ∧
    VEnv.get V "lagrange_precompile_failed" = some pf ∧
    VEnv.get V "omega" = some C.omw ∧
    loadWord st.memory C.aXN = wPow2 C.rw k C.xw ∧
    loadWord st.memory C.aXN1 = loadWord st.memory (C.D + 32 * (n + m)) ∧
    loadWord st.memory C.aLL = loadWord st.memory C.D ∧
    loadWord st.memory C.aLB =
      wSum C.rw (fun i => loadWord st.memory (C.D + 64 + 32 * i)) (m - 2)
        (loadWord st.memory (C.D + 32)) ∧
    loadWord st.memory C.aL0 = loadWord st.memory (C.D + 32 * m) ∧
    loadWord st.memory C.aIE =
      wSum C.rw (fun j => wMulmodAt (loadWord st.memory (C.D + 32 * m + 32 * j))
        (cdWord cd (C.aI + 32 * j)) C.rw) n 0 ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 →
      (∀ i, i < n + m →
        loadWord st.memory (C.D + 32 * i) =
          wMulmodAt (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw)
            (wMulmodAt (inv i) (omegaPows C.rw C.omw C.w0 i) C.rw) C.rw) ∧
      (∀ i, i < n + m →
        wMulmodAt (inv i) (lagDen C.rw C.xw C.omw C.w0 i) C.rw = 1 ∧
        (inv i).toNat < C.rw.toNat) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = inv (n + m)) ∧
    st.env = st0.env ∧ st.halted = st0.halted ∧
    MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)


/-! ## 4. THE BLOCK'S PRE AND POST -/

/-- The block's pre: the three caller locals the slice has bound (`r`, `success`, the just-zeroed
    `lagrange_precompile_failed`), the four table words the block reads (`X_MPTR`, `OMEGA_MPTR`,
    `OMEGA_INV_TO_L_MPTR`, `N_INV_MPTR`) and the call's calldata. -/
def LagPre {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
  VEnv.get V "lagrange_precompile_failed" = some 0 ∧
  loadWord st.memory C.aX = C.xw ∧ loadWord st.memory C.aO = C.omw ∧
  loadWord st.memory C.aL = C.w0 ∧ loadWord st.memory C.aN = C.nInv ∧
  st.env.calldata = cd.data.toList

/-- **THE BLOCK'S POST (the card's T3.9.f statement).** `LagRel` at the block's own memory, the
    six slot stores holding the same words, and the memory outside the denominator window, the
    batch-inversion scratch window and the six slot windows unchanged. The reject arm carries
    `success = 0` (the last statement's guard then fires) and the progress arm carries
    `ret ≠ 0` with the `LagRel`/slot facts. -/
def LagInnerPost {consts : Inline.Consts} {cd : Bytes} {k n m : Nat}
    (C : LagCfg consts cd k n m) (V' : VEnv (Bridge.Dialect c g))
    (st st' : EvmState) : Prop :=
  ∃ ret pf, VEnv.get V' "success" = some ret ∧
    VEnv.get V' "lagrange_precompile_failed" = some pf ∧
    st'.env = st.env ∧ st'.halted = st.halted ∧
    MemSameOut st.memory st' C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
      (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE) ∧
    (C.succ = 0 → ret = 0 ∧ pf = 0) ∧
    (ret ≠ 0 → ∃ W : LagWords,
      LagRel C.rw C.xw C.omw C.w0 C.nInv k n m
        (fun j => cdWord cd (C.aI + 32 * j)) W ∧
      loadWord st'.memory C.aXN = W.xn ∧
      loadWord st'.memory C.aXN1 = loadWord st'.memory (C.D + 32 * (n + m)) ∧
      loadWord st'.memory C.aLL = W.lLast ∧
      loadWord st'.memory C.aLB = W.lBlind ∧
      loadWord st'.memory C.aL0 = W.l0 ∧
      loadWord st'.memory C.aIE = W.instEval)

/-- Splitting a segment at a boundary: `seg i (j+j') = seg i j ++ seg (i+j) j'`. -/
theorem seg_split (b : Block EVM.Op) (i j j' : Nat) :
    seg b i (j + j') = seg b i j ++ seg b (i + j) j' := by
  simp only [seg]
  rw [List.take_add]
  congr 1
  rw [List.drop_drop]

/-- Reading the head binding by its own name. -/
theorem venv_get_cons_self {D : YulSemantics.Dialect} [DecidableEq D.Value] (V : VEnv D)
    (x : Ident) (v : D.Value) : VEnv.get ((x, v) :: V) x = some v := by
  simp [VEnv.get, List.find?]

/-! ## 5. THE STATEMENT-GROUP CONTRACTS (PROVED FROM THE LANDED ONES) -/

/-- A normal head with a normal-only mid composes with the tail. -/
theorem StmtsContractAll.append_normal {D : YulSemantics.Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {ss₁ ss₂ : Block D.Op} {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (h₁ : StmtsContractAll funs ss₁ pre (fun _ _ V' st' o => o = .normal ∧ mid V' st'))
    (h₂ : ∀ V st, pre V st → StmtsContractAll funs ss₂ mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (ss₁ ++ ss₂) pre post :=
  StmtsContractAll.append (fun V st hp V' st' o h => by
    obtain ⟨ho, hm⟩ := h₁ V st hp V' st' o h
    exact Or.inl ⟨ho, hm⟩) h₂


/-! ## 5. THE WHOLE-SLICE CONTRACTS, AS PROPOSITIONS

The block composition itself is T3.9.f's remaining core. The two propositions below are the exact
targets, so the card's proof (and `Totality`'s `block_live_lagrange`) can be stated against them
without restating the emitter or the windows. `LagInnerContract` is the inner-scope half (the
card's step 1, statements 0-27 over `LagPre`/`LagInnerPost`); `LagBlockContract` is the whole
slice at the semantic boundary (the card's steps 2-3: the outer `let`, the final
`iszero(success)` guard and the `StageInv` transfer). -/

/-- The inner scope's all-runs contract: exactly the card's T3.9.f step-1 statement. -/
def LagInnerContract {consts : Inline.Consts} {cd : Bytes} {k n m : Nat}
    (C : LagCfg consts cd k n m) (funs : FunEnv (Bridge.Dialect c g)) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) funs (lagInner consts k n m)
    (LagPre C)
    (fun _ st V' st' o => o = .normal ∧ LagInnerPost C V' st st')

/-- The poison arm's inner-scope contract: from a caller with `success = 0` every run of the
    inner scope is `.normal` and leaves `success = 0`, the reject arm of the `batch_invert`
    call (`BatchInvertPost.succZero`). -/
def LagInnerContractZero {consts : Inline.Consts} {cd : Bytes} {k n m : Nat}
    (C : LagCfg consts cd k n m) (funs : FunEnv (Bridge.Dialect c g)) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) funs (lagInner consts k n m)
    (LagPre C)
    (fun _ st V' st' o => o = .normal ∧ LagInnerPost C V' st st' ∧
      VEnv.get V' "success" = some 0)

/-- **THE WHOLE-SLICE LAGRANGE CONTRACT AT THE SEMANTIC BOUNDARY** (`Totality`'s integration
    target, kept here so the block module does not import `Totality`). Clean arm: every run of
    `R.slice .lagrange` from `StageInv .transcript` exits `.normal` at `StageInv .lagrange`. -/
def LagBlockContract (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (g : ExternalGas)
    (H : Hash) (vkAddr : U256) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
    (R.scope (permissive (callsOf product)) g) (R.slice Partial.lagrange)
    (fun V st => StageInv (c := permissive (callsOf product)) (g := g) R H vkAddr cd
      Checkpoint.transcript V st)
    (fun _ _ V' st' o => o = .normal ∧
      StageInv (c := permissive (callsOf product)) (g := g) R H vkAddr cd
        Checkpoint.lagrange V' st')

/-- **THE POISONED ARM OF THE LAGRANGE SLICE** (T3.9.h): from a poisoned boundary every run of
    the slice halts by reverting (`ERR_PROOF_REJECTED`, the last statement's guard). -/
def LagBlockPoisonContract (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (g : ExternalGas)
    (H : Hash) (vkAddr : U256) (cd : Bytes) : Prop :=
  StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
    (R.scope (permissive (callsOf product)) g) (R.slice Partial.lagrange)
    (fun V st => Poisoned R H vkAddr cd V st)
    (fun _ _ _ st' o => o = .halt ∧ Midfall.LoweringV2.Reverted st')

/-! ## 5. THE STATEMENT-GROUP CONTRACTS (PROVED FROM THE LANDED ONES) -/

/-- Split a conjunction goal into one goal per conjunct. -/
macro "split_conj" : tactic => `(tactic| repeat' apply And.intro)

/-- **GROUP 1 (statements 0-2: `k`, `x`, `x_n`).** -/
theorem lag_group1 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hX : consts.lookup "X_MPTR" = some C.aX) (haX : C.aX < 2 ^ 256)
    (st0 : EvmState) (hx0 : loadWord st0.memory C.aX = C.xw) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 0 3)
      (LagP0 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP2 C 0 0 (fun _ => 0) st0 V' st') := by
  have hsplit1 : seg (lagInner consts k n m) 0 3 =
      seg (lagInner consts k n m) 0 1 ++ seg (lagInner consts k n m) 1 2 :=
    seg_split (lagInner consts k n m) 0 1 2
  have hsplit2 : seg (lagInner consts k n m) 1 2 =
      seg (lagInner consts k n m) 1 1 ++ seg (lagInner consts k n m) 2 1 :=
    seg_split (lagInner consts k n m) 1 1 1
  rw [hsplit1, hsplit2]
  have h0 : StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 0 1) (LagP0 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP1 C 0 0 (fun _ => 0) st0 V' st') := by
    intro V st hg V' st' o hrun
    obtain ⟨ho, hst, hV⟩ := lag_stmt0_contract (funs := funs) (consts := consts)
      (k := k) (n := n) (m := m) V st trivial V' st' o hrun
    obtain ⟨hr, hsucc, hpf, hmem, henv, hhalt, hout⟩ := hg
    refine ⟨ho, ?_⟩
    split_conj
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "k") (y := "r")
        (by decide)]; exact hr
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "k") (y := "success")
        (by decide)]; exact hsucc
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "k")
        (y := "lagrange_precompile_failed") (by decide)]; exact hpf
    · rw [hV]; exact venv_get_cons_self V "k" _
    · rw [hst]; exact hmem
    · rw [hst]; exact henv
    · rw [hst]; exact hhalt
    · rw [hst]; exact hout
  have h1 : StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 1 1) (LagP1 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧
        (LagP1 C 0 0 (fun _ => 0) st0 V' st' ∧ VEnv.get V' "x" = some C.xw)) := by
    intro V st hg V' st' o hrun
    obtain ⟨ho, hst, hV⟩ := lag_stmt1_contract (funs := funs) (consts := consts)
      (k := k) (n := n) (m := m) (aX := C.aX) hX haX V st trivial V' st' o hrun
    obtain ⟨hr, hsucc, hpf, hk, hmem, henv, hhalt, hout⟩ := hg
    have hxw : loadWord st.memory C.aX = C.xw := by rw [hmem]; exact hx0
    refine ⟨ho, ?_⟩
    split_conj
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x") (y := "r")
        (by decide)]; exact hr
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x") (y := "success")
        (by decide)]; exact hsucc
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x")
        (y := "lagrange_precompile_failed") (by decide)]; exact hpf
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x") (y := "k")
        (by decide)]; exact hk
    · rw [hst]; exact hmem
    · rw [hst]; exact henv
    · rw [hst]; exact hhalt
    · rw [hst]; exact hout
    · rw [hV, hxw]; exact venv_get_cons_self V "x" _
  have h2 : StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 2 1)
      (fun V st => LagP1 C 0 0 (fun _ => 0) st0 V st ∧ VEnv.get V "x" = some C.xw)
      (fun _ _ V' st' o => o = .normal ∧ LagP2 C 0 0 (fun _ => 0) st0 V' st') := by
    intro V st hg V' st' o hrun
    obtain ⟨hx, hxw⟩ := hg
    obtain ⟨ho, hst, hV⟩ := lag_stmt2_contract (funs := funs) (consts := consts)
      (k := k) (n := n) (m := m) (x := C.xw) V st hxw V' st' o hrun
    obtain ⟨hr, hsucc, hpf, hk, hmem, henv, hhalt, hout⟩ := hx
    refine ⟨ho, ?_⟩
    split_conj
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "r")
        (by decide)]; exact hr
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "success")
        (by decide)]; exact hsucc
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n")
        (y := "lagrange_precompile_failed") (by decide)]; exact hpf
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "k")
        (by decide)]; exact hk
    · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "x")
        (by decide)]; exact hxw
    · rw [hV]; exact venv_get_cons_self V "x_n" _
    · rw [hst]; exact hmem
    · rw [hst]; exact henv
    · rw [hst]; exact hhalt
    · rw [hst]; exact hout
  exact StmtsContractAll.append_normal h0 (fun _ _ _ => StmtsContractAll.append_normal h1
    (fun _ _ _ => h2))

/-- **GROUP 2 (statement 3: the squaring loop).** -/
theorem lag_group2 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none) (hk : k < 2 ^ 256)
    (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 3 1)
      (LagP2 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP3 C 0 0 (fun _ => 0) st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hrw, hsucc, hpf, hkget, hxget, hxn, hmem, henv, hhalt, hout⟩ := hg
  have hs := lag_sq_loop (funs := funs) (consts := consts) hr k n m hk V st
    ⟨hkget, (by rw [hxn]; rfl), (by rw [hrw]; rfl)⟩ V' st' o hrun
  have ho := hs.1
  have hst := hs.2.1
  obtain ⟨x, rw, hxn', hrw', hV⟩ := hs.2.2
  have hxv : x = C.xw := Option.some.inj (hxn'.symm.trans hxn)
  have hrv : rw = C.rw := Option.some.inj (hrw'.symm.trans hrw)
  subst hxv; subst hrv
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "r")
      (by decide)]; exact hrw
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV]; exact venv_get_set_same (D := Bridge.Dialect c g) hxn
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n") (y := "x")
      (by decide)]; exact hxget
  · rw [hst]; exact hmem
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout


/-- **GROUP 3a (statement 4: `omega`).** -/
theorem lag_step4 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hO : consts.lookup "OMEGA_MPTR" = some C.aO) (haO : C.aO < 2 ^ 256)
    (st0 : EvmState) (hOm : loadWord st0.memory C.aO = C.omw) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 4 1) (LagP3 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP4 C 0 0 (fun _ => 0) st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨ho, hst, hV⟩ := lag_stmt4_contract (funs := funs) (consts := consts)
    (k := k) (n := n) (m := m) (aO := C.aO) hO haO V st trivial V' st' o hrun
  obtain ⟨hr, hsucc, hpf, hxn, hx, hmem, henv, hhalt, hout⟩ := hg
  have hOm' : loadWord st.memory C.aO = C.omw := by rw [hmem]; exact hOm
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "omega") (y := "r")
      (by decide)]; exact hr
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "omega") (y := "success")
      (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "omega")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "omega") (y := "x_n")
      (by decide)]; exact hxn
  · rw [hV, hOm']; exact venv_get_cons_self V "omega" _
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "omega") (y := "x")
      (by decide)]; exact hx
  · rw [hst]; exact hmem
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout

/-- **GROUP 3b (statement 5: `mptr := LAGRANGE_DENOMS_MPTR`).** -/
theorem lag_step5 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 5 1) (LagP4 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ (LagP4 C 0 0 (fun _ => 0) st0 V' st' ∧
        VEnv.get V' "mptr" = some (BitVec.ofNat 256 C.D))) := by
  intro V st hg V' st' o hrun
  obtain ⟨ho, hst, hV⟩ := lag_stmt5_contract (funs := funs) (consts := consts)
    (k := k) (n := n) (m := m) (aD := C.D) hD V st trivial V' st' o hrun
  obtain ⟨hr, hsucc, hpf, hxn, hom, hx, hmem, henv, hhalt, hout⟩ := hg
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr") (y := "r")
      (by decide)]; exact hr
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr") (y := "success")
      (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr") (y := "x_n")
      (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr") (y := "omega")
      (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr") (y := "x")
      (by decide)]; exact hx
  · rw [hst]; exact hmem
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout
  · rw [hV]; exact venv_get_cons_self V "mptr" _

/-- **GROUP 3c (statement 6: `mptr_end := mptr + 32(n+m)`).** -/
theorem lag_step6 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 6 1)
      (fun V st => LagP4 C 0 0 (fun _ => 0) st0 V st ∧
        VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D))
      (fun _ _ V' st' o => o = .normal ∧ LagP5 C 0 0 (fun _ => 0) st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hLG, hmp⟩ := hg
  obtain ⟨ho, hst, hV⟩ := lag_stmt6_contract (funs := funs) (consts := consts)
    (k := k) (n := n) (m := m) (mp := BitVec.ofNat 256 C.D) V st hmp V' st' o hrun
  obtain ⟨hr, hsucc, hpf, hxn, hom, hx, hmem, henv, hhalt, hout⟩ := hLG
  have hadd : (BitVec.ofNat 256 C.D + BitVec.ofNat 256 ((n + m) * 32) : U256) =
      BitVec.ofNat 256 (C.D + 32 * (n + m)) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end") (y := "r")
      (by decide)]; exact hr
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end") (y := "x_n")
      (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end") (y := "omega")
      (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end") (y := "x")
      (by decide)]; exact hx
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "mptr_end") (y := "mptr")
      (by decide)]; exact hmp
  · rw [hV, hadd]; exact venv_get_cons_self V "mptr_end" _
  · rw [hst]; exact hmem
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout

/-- **GROUP 3 (statements 4-6).** -/
theorem lag_group3 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hO : consts.lookup "OMEGA_MPTR" = some C.aO) (haO : C.aO < 2 ^ 256)
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D)
    (st0 : EvmState) (hOm : loadWord st0.memory C.aO = C.omw) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 4 3) (LagP3 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP5 C 0 0 (fun _ => 0) st0 V' st') := by
  have hsplit : seg (lagInner consts k n m) 4 3 =
      seg (lagInner consts k n m) 4 1 ++ (seg (lagInner consts k n m) 5 1 ++
        seg (lagInner consts k n m) 6 1) := by
    rw [show (3 : Nat) = 1 + 2 from rfl, seg_split, show (2 : Nat) = 1 + 1 from rfl, seg_split]
  rw [hsplit]
  exact StmtsContractAll.append_normal (lag_step4 C funs hO haO st0 hOm) (fun _ _ _ =>
    StmtsContractAll.append_normal (lag_step5 C funs hD st0) (fun _ _ _ => lag_step6 C funs st0))

/-- **GROUP 5a (statement 8: `x_n_minus_1 := x^n - 1`).** -/
theorem lag_step8 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 8 1) (LagP6 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ (LagP6 C 0 0 (fun _ => 0) st0 V' st' ∧
        VEnv.get V' "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw))) := by
  intro V st hg V' st' o hrun
  obtain ⟨hrw, hsucc, hpf, hxn, hom, hmp, hmpe, hden, hw0lk, henv, hhalt, hout⟩ := hg
  have hs := lag_stmt8_contract (funs := funs) (consts := consts) (k := k) (n := n) (m := m)
    hr (wPow2 C.rw k C.xw) C.rw V st ⟨hxn, hrw⟩ V' st' o hrun
  obtain ⟨ho, hst, hV⟩ := hs
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1") (y := "r")
      (by decide)]; exact hrw
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "x_n") (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "omega") (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "mptr") (by decide)]; exact hmp
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "x_n_minus_1")
      (y := "mptr_end") (by decide)]; exact hmpe
  · rw [hst]; exact hden
  · rw [hst]; exact hw0lk
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout
  · rw [hV]; exact venv_get_cons_self V "x_n_minus_1" _

/-- **GROUP 5b (statement 9: the store at `mptr_end`).** -/
theorem lag_step9 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (st0 : EvmState)
    (hfitD : C.D + 32 * (n + m) < 2 ^ 256)
    (haLne : C.aL + 32 ≤ C.D ∨ C.D + 32 * (n + m) + 32 ≤ C.aL) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 9 1)
      (fun V st => LagP6 C 0 0 (fun _ => 0) st0 V st ∧
        VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw))
      (fun _ _ V' st' o => o = .normal ∧ LagP7 C 0 0 (fun _ => 0) st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hLG, hxn1⟩ := hg
  obtain ⟨hrw, hsucc, hpf, hxn, hom, hmp, hmpe, hden, hw0lk, henv, hhalt, hout⟩ := hLG
  obtain ⟨ho, hst, hV⟩ := lag_stmt9_contract (funs := funs) (consts := consts) (k := k) (n := n)
    (m := m) (mp := BitVec.ofNat 256 (C.D + 32 * (n + m)))
    (xn1 := wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) V st ⟨hmpe, hxn1⟩ V' st' o hrun
  have hmpNat : (BitVec.ofNat 256 (C.D + 32 * (n + m))).toNat = C.D + 32 * (n + m) :=
    ofNat_toNat hfitD
  rw [hst, hmpNat]
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV]; exact hrw
  · rw [hV]; exact hsucc
  · rw [hV]; exact hpf
  · rw [hV]; exact hxn
  · rw [hV]; exact hom
  · rw [hV]; exact hmpe
  · rw [hV]; exact hmp
  · rw [hV]; exact hxn1
  · exact loadWord_storeWord_same_at st.memory (C.D + 32 * (n + m)) _
  · intro i hi
    rw [loadWord_storeWord_at (by omega)]
    exact hden i hi
  · rw [loadWord_storeWord_at (by omega)]
    exact hw0lk
  · exact henv
  · exact hhalt
  · exact MemSameOut.store_inside hout (by omega) (by omega)

/-- **GROUP 5 (statements 8-9).** -/
theorem lag_group5 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none) (st0 : EvmState)
    (hfitD : C.D + 32 * (n + m) < 2 ^ 256)
    (haLne : C.aL + 32 ≤ C.D ∨ C.D + 32 * (n + m) + 32 ≤ C.aL) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 8 2) (LagP6 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP7 C 0 0 (fun _ => 0) st0 V' st') := by
  have hsplit : seg (lagInner consts k n m) 8 2 =
      seg (lagInner consts k n m) 8 1 ++ seg (lagInner consts k n m) 9 1 :=
    seg_split (lagInner consts k n m) 8 1 1
  rw [hsplit]
  exact StmtsContractAll.append_normal (lag_step8 C funs hr st0) (fun _ _ _ =>
    lag_step9 C funs st0 hfitD haLne)

/-- **GROUP 6 (statement 10: the `batch_invert` call).** -/
theorem lag_group6 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (hcall : BatchInvertCallSegment consts product g k n m C.D C.s funs C.succ C.rw)
    (haLne : C.aL + 32 ≤ C.D ∨ C.D + 32 * (n + m) + 32 ≤ C.aL)
    (haLs : C.aL + 32 ≤ C.s ∨ C.s + (32 * (n + m + 1) + 0xc0) ≤ C.aL)
    (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (seg (lagInner consts k n m) 10 1) (LagP7 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧
        ∃ ret pf inv, LagP8 C ret pf inv st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hrw, hsucc, hpf, hxn, hom, hmpe, hmp7, hxn1, hlastmem, hden, hw0lk, henv, hhalt, hout⟩ := hg
  have hs := hcall V st ⟨hsucc, hrw, hpf, hmpe⟩ V' st' o hrun
  obtain ⟨ho, hpost⟩ := hs
  obtain ⟨ret, pf, hsucc', hfailed, hVenv, henv', hhalt', houtside, hszero, hpfzero, hinv⟩ := hpost
  refine ⟨ho, ret, pf, (fun i => loadWord st'.memory (C.D + 32 * i)), ?_⟩
  split_conj
  · exact hsucc'
  · exact hfailed
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "r") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "r") (by decide)]
    exact hrw
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "x_n") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "x_n") (by decide)]
    exact hxn
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "omega") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "omega") (by decide)]
    exact hom
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "mptr_end") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "mptr_end") (by decide)]
    exact hmpe
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "mptr") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "mptr") (by decide)]
    rw [hmp7]; rfl
  · rw [hVenv]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "lagrange_precompile_failed") (y := "x_n_minus_1") (by decide)]
    rw [venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
      (x := "success") (y := "x_n_minus_1") (by decide)]
    exact hxn1
  · have hsub : C.D + 32 * (n + m) + 32 - C.D = 32 * (n + m) + 32 := by omega
    have hout' := houtside
    rw [hsub] at hout'
    have hlen : 32 * (n + m + 1) = 32 * (n + m) + 32 := by ring
    have hw : loadWord st'.memory C.aL = loadWord st.memory C.aL := by
      refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
      exact hout' (C.aL + i)
        (by rcases haLne with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
        (by rcases haLs with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
    rw [hw]
    exact hw0lk
  · intro hs0
    obtain ⟨hret0, hpf0, hmemEq⟩ := hszero hs0
    refine ⟨hret0, hpf0, ?_, ?_⟩
    · intro i hi
      rw [hmemEq]; exact hden i hi
    · rw [hmemEq]; exact hlastmem
  · intro hret
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact rfl
    · intro i hi
      have hi' : C.D + 32 * i < C.D + 32 * (n + m) + 32 := by omega
      obtain ⟨hA, hB, hC, hD⟩ := hinv hret |>.2 i hi'
      refine ⟨?_, hC⟩
      rw [hden i hi] at hD
      exact hD
    · have hlast : C.D + 32 * (n + m) < C.D + 32 * (n + m) + 32 := by omega
      obtain ⟨hA, hB, hC, hD⟩ := hinv hret |>.2 (n + m) hlast
      rw [hlastmem] at hD
      exact hD
    · have hlast : C.D + 32 * (n + m) < C.D + 32 * (n + m) + 32 := by omega
      exact (hinv hret |>.2 (n + m) hlast).2.2.1
    · exact rfl
  · exact henv'.trans henv
  · exact hhalt'.trans hhalt
  · intro a ha hb hs
    have hlen : 32 * (n + m + 1) = 32 * (n + m) + 32 := by ring
    have ha' : a < C.D ∨ C.D + 32 * (n + m) + 32 ≤ a := by
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hb' : a < C.s ∨ C.s + (32 * (n + m) + 32) + 0xc0 ≤ a := by
      rcases hb with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    have hsub : C.D + 32 * (n + m) + 32 - C.D = 32 * (n + m) + 32 := by omega
    have hout' := houtside
    rw [hsub] at hout'
    rw [hout' a ha' hb']
    exact hout a ha hb hs
/-- **GROUP 4 (statement 7: the denominator window).** -/
theorem lag_group4 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some C.aL) (haL : C.aL < 2 ^ 256)
    (hfitD : C.D + 32 * (n + m) < 2 ^ 256)
    (hLD : C.aL + 32 ≤ C.D ∨ C.D + 32 * (n + m) ≤ C.aL) (st0 : EvmState)
    (hw0 : loadWord st0.memory C.aL = C.w0) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 7 1) (LagP5 C 0 0 (fun _ => 0) st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP6 C 0 0 (fun _ => 0) st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hrw, hsucc, hpf, hxn, hom, hx, hmp, hmpe, hmem, henv, hhalt, hout⟩ := hg
  have hs := lag_denoms_loop (funs := funs) (consts := consts) hr k n m C.aL hL haL C.D hfitD
    V st ⟨hmp, hmpe, (by rw [hx]; rfl), (by rw [hom]; rfl), (by rw [hrw]; rfl)⟩ V' st' o hrun
  obtain ⟨ho, x, om, rw, hx', hom', hrw', hV', hden, houtside, henv', hhalt'⟩ := hs
  have hxv : x = C.xw := Option.some.inj (hx'.symm.trans hx)
  have homv : om = C.omw := Option.some.inj (hom'.symm.trans hom)
  have hrwv : rw = C.rw := Option.some.inj (hrw'.symm.trans hrw)
  subst hxv; subst homv; subst hrwv
  have hw0' : loadWord st.memory C.aL = C.w0 := by rw [hmem]; exact hw0
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide)]
    exact hrw
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "success") (by decide)]
    exact hsucc
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr")
      (y := "lagrange_precompile_failed") (by decide)]
    exact hpf
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "x_n") (by decide)]
    exact hxn
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "omega") (by decide)]
    exact hom
  · rw [hV']; exact venv_get_set_same (D := Bridge.Dialect c g) hmp
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "mptr_end")
      (by decide)]
    exact hmpe
  · intro i hi
    rw [hden i hi, hw0']
    rfl
  · rw [show loadWord st'.memory C.aL = loadWord st.memory C.aL from
      loadWord_of_memSameOutside houtside hLD, hmem]
    exact hw0
  · exact henv'.trans henv
  · exact hhalt'.trans hhalt
  · have hlen : 32 * (n + m + 1) = 32 * (n + m) + 32 := by ring
    intro a ha hb hs
    have ha' : a < C.D ∨ C.D + 32 * (n + m) ≤ a := by
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    rw [houtside a ha']
    exact hout a ha hb hs





/-- **GROUP 7a (statement 11: `mptr := LAGRANGE_DENOMS_MPTR`).** -/
theorem lag_step11 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D) (ret pf : U256) (inv : Nat → U256)
    (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 11 1) (LagP8 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ (LagP8 C ret pf inv st0 V' st' ∧
        VEnv.get V' "mptr" = some (BitVec.ofNat 256 C.D))) := by
  intro V st hg V' st' o hrun
  obtain ⟨ho, hst, hV⟩ := lag_stmt11_contract (funs := funs) (consts := consts)
    (k := k) (n := n) (m := m) (aD := C.D) hD V st trivial V' st' o hrun
  obtain ⟨hsucc, hpf, hrw, hxn, hom, hmpe, hmp8, hxn1, hw0lk, hszero, hinv, henv, hhalt, hout⟩ := hg
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "success") (by decide)]
    exact hsucc
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr")
      (y := "lagrange_precompile_failed") (by decide)]
    exact hpf
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide)]
    exact hrw
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "x_n") (by decide)]
    exact hxn
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "omega") (by decide)]
    exact hom
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "mptr_end")
      (by decide)]
    exact hmpe
  · obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hmp8
    rw [hV, venv_get_set_same (D := Bridge.Dialect c g) hmp]; rfl
  · rw [hV, venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "x_n_minus_1")
      (by decide)]
    exact hxn1
  · rw [hst]; exact hw0lk
  · rw [hst]; exact hszero
  · rw [hst]; exact hinv
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout
  · obtain ⟨mp, hmp⟩ := Option.isSome_iff_exists.mp hmp8
    rw [hV]; exact venv_get_set_same (D := Bridge.Dialect c g) hmp

/-- **GROUP 7b (statement 12: `l_i_common`).** -/
theorem lag_step12 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none)
    (hN : consts.lookup "N_INV_MPTR" = some C.aN) (haN : C.aN < 2 ^ 256)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (hnInv : loadWord st0.memory C.aN = C.nInv)
    (haNne : C.aN + 32 ≤ C.D ∨ C.D + 32 * (n + m) + 32 ≤ C.aN)
    (haNs : C.aN + 32 ≤ C.s ∨ C.s + (32 * (n + m + 1) + 0xc0) ≤ C.aN)
    (haNslot : ∀ q ∈ lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE,
      C.aN + 32 ≤ q ∨ q + 32 ≤ C.aN) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 12 1)
      (fun V st => LagP8 C ret pf inv st0 V st ∧
        VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D))
      (fun _ _ V' st' o => o = .normal ∧ LagP9 C ret pf inv st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hLG, hmp⟩ := hg
  obtain ⟨hsucc, hpf, hrw, hxn, hom, hmpe, hmpSome, hxn1, hw0lk, hszero, hinv, henv, hhalt, hout⟩ := hLG
  have haNv : loadWord st.memory C.aN = C.nInv := by
    have hword : loadWord st.memory C.aN = loadWord st0.memory C.aN := by
      refine Midfall.Yul.Word.loadWord_congr _ _ _ (fun i hi => ?_)
      exact hout (C.aN + i)
        (by rcases haNne with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
        (by rcases haNs with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
        (by
          intro q hq
          rcases haNslot q hq with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))
    rw [hword, hnInv]
  obtain ⟨ho, hst, hV⟩ := lag_stmt12_contract (funs := funs) (consts := consts) (k := k) (n := n)
    (m := m) (aN := C.aN) hN haN hr (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.rw
    V st ⟨hxn1, hrw⟩ V' st' o hrun
  rw [haNv] at hV
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "r") (by decide)]; exact hrw
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "x_n") (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "omega") (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "mptr") (by decide)]; exact hmp
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "mptr_end") (by decide)]; exact hmpe
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_common")
      (y := "x_n_minus_1") (by decide)]; exact hxn1
  · rw [hV]; exact venv_get_cons_self V "l_i_common" _
  · rw [hst]; exact hw0lk
  · rw [hst]; exact hszero
  · rw [hst]; exact hinv
  · rw [hst]; exact henv
  · rw [hst]; exact hhalt
  · rw [hst]; exact hout

/-- **GROUP 7 (statements 11-12).** -/
theorem lag_group7 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none)
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D)
    (hN : consts.lookup "N_INV_MPTR" = some C.aN) (haN : C.aN < 2 ^ 256)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState)
    (hnInv : loadWord st0.memory C.aN = C.nInv)
    (haNne : C.aN + 32 ≤ C.D ∨ C.D + 32 * (n + m) + 32 ≤ C.aN)
    (haNs : C.aN + 32 ≤ C.s ∨ C.s + (32 * (n + m + 1) + 0xc0) ≤ C.aN)
    (haNslot : ∀ q ∈ lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE,
      C.aN + 32 ≤ q ∨ q + 32 ≤ C.aN) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 11 2) (LagP8 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP9 C ret pf inv st0 V' st') := by
  rw [show (2 : Nat) = 1 + 1 from rfl, seg_split]
  exact StmtsContractAll.append_normal (lag_step11 C funs hD ret pf inv st0)
    (fun _ _ _ => lag_step12 C funs hr hN haN ret pf inv st0 hnInv haNne haNs haNslot)


/-- **GROUP 8 (statement 13: the second pass).** -/
theorem lag_group8 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g)) (hr : consts.lookup "r" = none)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some C.aL) (haL : C.aL < 2 ^ 256)
    (hfitD : C.D + 32 * (n + m) < 2 ^ 256)
    (hLD : C.aL + 32 ≤ C.D ∨ C.D + 32 * (n + m) ≤ C.aL)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 13 1) (LagP9 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP10 C ret pf inv st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hsucc, hpf, hrw, hxn, hom, hmp, hmpe, hxn1, hlic, hw0lk, hszero, hinv, henv, hhalt, hout⟩ := hg
  have hs := lag_second_pass_loop (funs := funs) (consts := consts) hr k n m C.aL hL haL C.D
    hfitD hLD V st ⟨hmp, hmpe, (by rw [hlic]; rfl), (by rw [hom]; rfl), (by rw [hrw]; rfl)⟩
    V' st' o hrun
  obtain ⟨ho, lc, om, rw, hlc', hom', hrw', hV', hLf, houtside, henv', hhalt'⟩ := hs
  have hlcv : lc = wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw :=
    Option.some.inj (hlc'.symm.trans hlic)
  have homv : om = C.omw := Option.some.inj (hom'.symm.trans hom)
  have hrwv : rw = C.rw := Option.some.inj (hrw'.symm.trans hrw)
  subst hlcv homv hrwv
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "success") (by decide)]
    exact hsucc
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr")
      (y := "lagrange_precompile_failed") (by decide)]
    exact hpf
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide)]
    exact hrw
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "x_n") (by decide)]
    exact hxn
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "omega") (by decide)]
    exact hom
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "mptr_end")
      (by decide)]
    exact hmpe
  · rw [hV', venv_get_set_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "l_i_common")
      (by decide)]
    exact hlic
  · intro hs0
    exact ⟨(hszero hs0).1, (hszero hs0).2.1⟩
  · intro hret
    have hinvF := hinv hret
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [hLf i hi]
      have hden := hinvF.1 i (by omega)
      rw [hden, hw0lk]
    · exact hinvF.2.1
    · have hwin : C.D + 32 * (n + m) ≤ C.D + 32 * (n + m) := Nat.le_refl _
      rw [loadWord_of_memSameOutside houtside (Or.inr hwin)]
      exact hinvF.2.2.2.2
  · exact henv'.trans henv
  · exact hhalt'.trans hhalt
  · intro a ha hb hs
    have hlen : 32 * (n + m + 1) = 32 * (n + m) + 32 := by ring
    have ha' : a < C.D ∨ C.D + 32 * (n + m) ≤ a := by
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    rw [houtside a ha']
    exact hout a ha hb hs

/-- **GROUP 9a (statement 14: `l_blind := mload(D+32)`).** -/
theorem lag_step14 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D) (haD : C.D < 2 ^ 256)
    (haD32 : C.D + 32 < 2 ^ 256) (ret pf : U256) (inv : Nat → U256) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 14 1) (LagP10 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ (LagP10 C ret pf inv st0 V' st' ∧
        VEnv.get V' "l_blind" = some (loadWord st'.memory (C.D + 32)))) := by
  intro V st hg V' st' o hrun
  obtain ⟨ho, hst, hV⟩ := lag_stmt14_contract (funs := funs) (consts := consts) (k := k) (n := n)
    (m := m) (aD := C.D) hD haD haD32 V st trivial V' st' o hrun
  obtain ⟨hsucc, hpf, hrw, hxn, hom, hmpe, hlic, hszero, hinv, henv, hhalt, hout⟩ := hg
  rw [hst]
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "r") (by decide)]; exact hrw
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "x_n") (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "omega") (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "mptr_end") (by decide)]; exact hmpe
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_blind")
      (y := "l_i_common") (by decide)]; exact hlic
  · exact hszero
  · exact hinv
  · exact henv
  · exact hhalt
  · exact hout
  · rw [hV]; exact venv_get_cons_self V "l_blind" _

/-- **GROUP 9b (statement 15: `l_i_cptr := D + 64`).** -/
theorem lag_step15 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D) (ret pf : U256)
    (inv : Nat → U256) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 15 1)
      (fun V st => LagP10 C ret pf inv st0 V st ∧
        VEnv.get V "l_blind" = some (loadWord st.memory (C.D + 32)))
      (fun _ _ V' st' o => o = .normal ∧ LagP11 C ret pf inv st0 V' st') := by
  intro V st hg V' st' o hrun
  obtain ⟨hLG, hlb⟩ := hg
  obtain ⟨ho, hst, hV⟩ := lag_stmt15_contract (funs := funs) (consts := consts) (k := k) (n := n)
    (m := m) (aD := C.D) hD V st trivial V' st' o hrun
  obtain ⟨hsucc, hpf, hrw, hxn, hom, hmpe, hlic, hszero, hinv, henv, hhalt, hout⟩ := hLG
  have hadd : (BitVec.ofNat 256 C.D + BitVec.ofNat 256 64 : U256) =
      BitVec.ofNat 256 (C.D + 64) := by
    rw [← BitVec.ofNat_add]
  rw [hst]
  refine ⟨ho, ?_⟩
  split_conj
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "success") (by decide)]; exact hsucc
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "lagrange_precompile_failed") (by decide)]; exact hpf
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "r") (by decide)]; exact hrw
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "omega") (by decide)]; exact hom
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "x_n") (by decide)]; exact hxn
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "l_i_common") (by decide)]; exact hlic
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "l_blind") (by decide)]; exact hlb
  · rw [hV, hadd]
    exact venv_get_cons_self V "l_i_cptr" _
  · rw [hV, venv_get_cons_ne (D := Bridge.Dialect c g) (V := V) (x := "l_i_cptr")
      (y := "mptr_end") (by decide)]; exact hmpe
  · exact hszero
  · exact hinv
  · exact henv
  · exact hhalt
  · exact hout

/-- **GROUP 9 (statements 14-15).** -/
theorem lag_group9 {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (funs : FunEnv (Bridge.Dialect c g))
    (hD : consts.lookup "LAGRANGE_DENOMS_MPTR" = some C.D) (haD : C.D < 2 ^ 256)
    (haD32 : C.D + 32 < 2 ^ 256) (ret pf : U256) (inv : Nat → U256) (st0 : EvmState) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 14 2) (LagP10 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ LagP11 C ret pf inv st0 V' st') := by
  rw [show (2 : Nat) = 1 + 1 from rfl, seg_split]
  have h14 : StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 14 1) (LagP10 C ret pf inv st0)
      (fun _ _ V' st' o => o = .normal ∧ (LagP10 C ret pf inv st0 V' st' ∧
        VEnv.get V' "l_blind" = some (loadWord st'.memory (C.D + 32)))) :=
    lag_step14 (consts := consts) (k := k) (n := n) (m := m) C funs hD haD haD32 ret pf inv st0
  have h15 : StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (lagInner consts k n m) 15 1)
      (fun V st => LagP10 C ret pf inv st0 V st ∧
        VEnv.get V "l_blind" = some (loadWord st.memory (C.D + 32)))
      (fun _ _ V' st' o => o = .normal ∧ LagP11 C ret pf inv st0 V' st') :=
    lag_step15 (consts := consts) (k := k) (n := n) (m := m) C funs hD ret pf inv st0
  exact StmtsContractAll.append_normal
    (mid := fun V st => LagP10 C ret pf inv st0 V st ∧
      VEnv.get V "l_blind" = some (loadWord st.memory (C.D + 32))) h14
    (fun _ _ _ => h15)


/-- **THE CONSTANT-TABLE PIN FOR THE BATCH-INVERT SCRATCH.** `expectedConsts` carries the plan
field (`Statements.lean:2947`), and `programOkB` makes the render's table the data table. -/
theorem consts_lookup_BATCH_INV_SCRATCH_MPTR {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.consts.lookup "BATCH_INV_SCRATCH_MPTR" = some R.pv.memory.batchInvertScratchMptr := by
  show (Midfall.LoweringV2.constTableOf R.model).lookup "BATCH_INV_SCRATCH_MPTR" =
    some R.pv.memory.batchInvertScratchMptr
  rw [lookup_expectedConsts_of_programOkB (programOkB_of_valid hR)]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;> cases h4 : R.model.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- **D-GATE9 AT THE LAG BLOCK: `hsp : 32 ≤ C.s` IS A PROJECTION, NOT A PREMISE.** Given the
    constant-table lookup the block contract already takes, the scratch pointer is at least the
    EVM scratch region, by `batchInvertScratchFits_of_valid`. -/
theorem lagScratchFits {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) {s : Nat}
    (hS : R.consts.lookup "BATCH_INV_SCRATCH_MPTR" = some s) : 32 ≤ s := by
  rw [consts_lookup_BATCH_INV_SCRATCH_MPTR hR] at hS
  have h := Midfall.LoweringV3.batchInvertScratchFits_of_valid hR
  simp only [Midfall.LoweringV3.batchInvertScratchFits] at h
  have hs : R.pv.memory.batchInvertScratchMptr = s := Option.some.inj hS
  rw [← hs]; exact h

end Midfall.LoweringV3.LagrangeBlock
