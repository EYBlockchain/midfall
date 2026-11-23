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
def BatchInvertCallPost (st st' : EvmState) (V' : VEnv (Bridge.Dialect c g))
    (succ : U256) (a e s : Nat) (rw : U256) : Prop :=
  ∃ ret pf, VEnv.get V' "success" = some ret ∧
    VEnv.get V' "lagrange_precompile_failed" = some pf ∧
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
    `Step.callOk`; nothing here restates that summary. -/
def BatchInvertCallSegment (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (k n m D aS : Nat) (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (succ rw : U256) : Prop :=
  StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
    (seg (lagInner consts k n m) 10 1)
    (fun V _ =>
      VEnv.get V "success" = some succ ∧ VEnv.get V "r" = some rw ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))))
    (fun _ st V' st' o => o = .normal ∧
      BatchInvertCallPost (c := permissive (callsOf product)) (g := g) st st' V' succ
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

/-- The phase relation. Index `0` is the block's pre-state; `15` is its post. -/
def LagG {consts : Inline.Consts} {cd : Bytes} {k n m : Nat} (C : LagCfg consts cd k n m)
    (ret pf : U256) (inv : Nat → U256) (st0 : EvmState) :
    Nat → VEnv (Bridge.Dialect c g) → EvmState → Prop
  | 0, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 1, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 2, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
      VEnv.get V "x" = some C.xw ∧ VEnv.get V "x_n" = some C.xw ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 3, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 4, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 5, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D) ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      st.memory = st0.memory ∧ st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 6, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "mptr" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      (∀ i, i < n + m → loadWord st.memory (C.D + 32 * i) = lagDen C.rw C.xw C.omw C.w0 i) ∧
      st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 7, V, st =>
      VEnv.get V "r" = some C.rw ∧ VEnv.get V "success" = some C.succ ∧
      VEnv.get V "lagrange_precompile_failed" = some 0 ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
      loadWord st.memory (C.D + 32 * (n + m)) = wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw ∧
      st.env = st0.env ∧ st.halted = st0.halted ∧
      MemSameOut st0.memory st C.D (32 * (n + m + 1)) C.s (32 * (n + m + 1) + 0xc0)
        (lagSlots C.aXN C.aXN1 C.aLL C.aLB C.aL0 C.aIE)
  | 8, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
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
  | 9, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
      VEnv.get V "x_n" = some (wPow2 C.rw k C.xw) ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "mptr" = some (BitVec.ofNat 256 C.D) ∧
      VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (C.D + 32 * (n + m))) ∧
      VEnv.get V "x_n_minus_1" = some (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) ∧
      VEnv.get V "l_i_common" =
        some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
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
  | 10, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
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
  | 11, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "l_i_common" =
        some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
      VEnv.get V "l_blind" = some (loadWord st.memory (C.D + 32)) ∧
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
  | 12, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "l_i_common" =
        some (wMulmodAt (wAddmodAt (wPow2 C.rw k C.xw) (C.rw - 1) C.rw) C.nInv C.rw) ∧
      VEnv.get V "l_blind" =
        some (wSum C.rw (fun i => loadWord st.memory (C.D + 64 + 32 * i)) (m - 2)
          (loadWord st.memory (C.D + 32))) ∧
      VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (C.D + 32 * m)) ∧
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
  | 13, V, st =>
      VEnv.get V "success" = some ret ∧
      VEnv.get V "lagrange_precompile_failed" = some pf ∧
      VEnv.get V "omega" = some C.omw ∧
      VEnv.get V "instance_eval" =
        some (wSum C.rw (fun j => wMulmodAt (loadWord st.memory (C.D + 32 * m + 32 * j))
          (cdWord cd (C.aI + 32 * j)) C.rw) n 0) ∧
      VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (C.D + 32 * m + 32 * n)) ∧
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
  | 14, V, st =>
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
  | 15, V, st =>
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
  | _, _, _ => False


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

end Midfall.LoweringV3.LagrangeBlock
