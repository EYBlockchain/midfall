/-
  Midfall.LoweringV3.FpFit

  ROW.FP (WP A11) - the named pairing-slot fit obligation `PG-PAIRINGFIT`.

  The clean finalPairing arm converts the slice's `BitVec.ofNat 256` pointer
  literals to the `Nat` addresses `Inv`/`FpWire` read.  That needs
  `cAddr M.pairingLhsMptr < 2^256` etc., and the current `ValidV3` only bounds
  `vkMptr + vk.len`/`runtimeLen` (`programFits`).  The pairing slots are
  `allocAfter` the VK payload; with `vkMptr + vk.len` just below `2^256`, the
  `alignUp` of the challenge block is `2^256` and every later slot wraps.  This
  file names the obligation and the falsifier; no clause is added to `ValidV3`.
-/
import Midfall.LoweringV3.Totality

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **PG-PAIRINGFIT (candidate clause).** The three pairing input pointers fit a
    word.  This is what the clean arm's `BitVec.ofNat 256 … .toNat` conversions
    need; it is deliberately a *named obligation*, not a hypothesis on the row. -/
def PG_PAIRINGFIT (R : Render p G₁ G₂ Gₜ) : Prop :=
  cAddr R.pv.memory.pairingLhsMptr < 2 ^ 256 ∧
  cAddr R.pv.memory.pairingRhsMptr < 2 ^ 256 ∧
  cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base) < 2 ^ 256 ∧
  cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base) < 2 ^ 256

/-- **PG-PAIRINGFIT (margin form).** The post-payload static working set fits:
    the VK payload end plus the challenge/theta block.  This is the clause a
    signed `programFits`/`programOkCore` repair should carry. -/
def PG_PAIRINGFIT_MARGIN (R : Render p G₁ G₂ Gₜ) : Prop :=
  ptrAddr R.pv.memory.vkMptr + R.pv.vk.len +
      (R.pv.memory.thetaWindows.rotPointsWord * Midfall.Generator.wordBytes) < 2 ^ 256

/-- A `Nat` at or above `2^256` cannot be read back from its `BitVec.ofNat 256`
    literal. -/
theorem ofNat_toNat_ne_of_ge {n : Nat} (h : 2 ^ 256 ≤ n) :
    (BitVec.ofNat 256 n).toNat ≠ n := by
  intro hn
  have hlt := (Midfall.LoweringV3.MemoryPairs.ofNat_toNat_iff_lt n).mp hn
  omega

/-- **THE LAYOUT-LEVEL FALSIFIER, REDUCED.**  The constructor's `allocAfter`
    chain gives `challengeStart = alignUp (B + vk.len) 32`; at
    `B + vk.len = 2^256 - 2` this is `2^256`, and every theta/pairing slot is at
    or above it.  The remaining lower-bound equation is the explicit `hge`:
    unfolding `VerifierMemoryLayout.new`'s `let` chain is the next mechanical
    step, and `hge` is exactly the fact the current clause table does not carry. -/
theorem pairingFit_falsifier_layout
    (meta_ : ConstraintSystemMeta) (vk : Halo2VerifyingKey)
    (config : VerifierMemoryLayoutConfig) (B : Nat)
    (hB : B + vk.len = 2 ^ 256 - 2)
    (hge : 2 ^ 256 ≤
      ptrAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr) :
    ¬ (BitVec.ofNat 256
        (cAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr)).toNat
      = cAddr (VerifierMemoryLayout.new meta_ vk (ptrMemory (valueFromNat B)) config).pairingLhsMptr := by
  apply ofNat_toNat_ne_of_ge
  simpa only [cAddr, ptrAddr, ptrValue] using hge

/-- The chosen `B` satisfies both VK bounds of `programFits` whenever the payload
    fits in a word.  This is the legal side of the falsifier: the VK half of the
    clause table is untouched. -/
theorem programFits_vk_bound_at_B {R : Render p G₁ G₂ Gₜ} {B : Nat}
    (hB : B + R.pv.vk.len = 2 ^ 256 - 2)
    (hlen : R.pv.vk.len + 2 ≤ 2 ^ 256) :
    B + R.pv.vk.len < 2 ^ 256 ∧ B + R.pv.vk.runtimeLen < 2 ^ 256 := by
  have hr : R.pv.vk.runtimeLen = R.pv.vk.len + 1 := by
    unfold Midfall.Generator.Halo2VerifyingKey.runtimeLen Midfall.Generator.vkRuntimePrefixLen
    omega
  constructor <;> omega

#assert_axioms Midfall.LoweringV3.ofNat_toNat_ne_of_ge
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.pairingFit_falsifier_layout
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.programFits_vk_bound_at_B
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3
