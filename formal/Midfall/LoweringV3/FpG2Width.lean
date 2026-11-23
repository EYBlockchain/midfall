/-
  Midfall.LoweringV3.FpG2Width

  ROW.FP (WP A11) - the G2 slot width law.

  `Eip2537.Holds.g2Valid` decodes `encG2 Q` with `g2Of?`, and `g2Of?` uses the
  STRICT `bytesTake`: a short buffer is `none`, not zero-padded.  So
  `(encG2 Q).size ≥ 256`.  `PayloadAgrees.g2Base`/`negSG2` identify that buffer
  with `vkG2Words`, whose size is `32 * min 8 (constants.length - slot)`.  Hence
  the payload constant section covers the G2 header slots 15..22 and 23..30, and
  `bytesAt_vkG2Base`'s two length facts follow.  No new hypothesis.
-/
import Midfall.LoweringV3.FpWire

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

theorem bytesSlice_size_le_sub (b : Bytes) (i n : Nat) :
    (bytesSlice b i n).size ≤ b.size - i := by
  unfold bytesSlice
  change (b.data.extract (min i b.size) (min (i + n) b.size)).size ≤ b.size - i
  rw [Array.size_extract]
  omega

theorem fpCoordOf?_size {b : Bytes} {v : Nat} (h : fpCoordOf? b = some v) :
    64 ≤ b.size := by
  unfold fpCoordOf? at h
  split at h
  · contradiction
  · rename_i c hc
    unfold bytesTake at hc
    split at hc
    · rename_i hle
      have h64 : fpPadBytes + fpBytes = 64 := by decide
      omega
    · contradiction

theorem g2Of?_size {b : Bytes} {pt} (h : g2Of? b = some pt) : 256 ≤ b.size := by
  unfold g2Of? at h
  split at h
  · rename_i a c d e ha hc hd he
    have h4 : 64 ≤ (bytesSlice b 192 64).size := fpCoordOf?_size he
    have hle := bytesSlice_size_le_sub b 192 64
    omega
  · contradiction

open Midfall.LoweringV2 Midfall.LoweringV3

theorem pairFold_size (l : List (String × Word256)) (acc : Bytes) :
    (l.foldl (fun a p => a.append (Midfall.wordToBytesBE p.2)) acc).size
      = acc.size + 32 * l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
      obtain ⟨name, w⟩ := p
      rw [List.foldl_cons, ih (acc.append (Midfall.wordToBytesBE w))]
      rw [show ByteArray.append acc (Midfall.wordToBytesBE w) = acc ++ Midfall.wordToBytesBE w from rfl,
        ByteArray.size_append, Midfall.LoweringV2.wordToBytesBE_size]
      simp
      omega

theorem vkHeaderBytes_size (PV : PlanView) (i n : Nat) :
    (vkHeaderBytes PV i n).size = 32 * min n (PV.vk.constants.length - i) := by
  unfold vkHeaderBytes
  rw [pairFold_size]
  have hempty : Midfall.Bytes.empty.size = 0 := rfl
  rw [hempty]
  simp [List.length_take, List.length_drop]

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

theorem vk_len_ge_of_header (R : Render p G₁ G₂ Gₜ) {slot : Nat}
    (h : slot + 8 ≤ R.pv.vk.constants.length) :
    32 * (slot + 8) ≤ R.pv.vk.len := by
  unfold Midfall.Generator.Halo2VerifyingKey.len
  omega

theorem g2Base_constants_length (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (product : PairingProduct)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) :
    vkG2BaseSlot + 8 ≤ R.pv.vk.constants.length := by
  obtain ⟨pt, hpt, -⟩ := hpc.g2Valid P.g₂
  have hsize := g2Of?_size hpt
  change 256 ≤ (R.encG2 P.g₂).size at hsize
  rw [← hR.payload.g2Base] at hsize
  change 256 ≤ (vkG2Words R.pv vkG2BaseSlot).size at hsize
  rw [show vkG2Words R.pv vkG2BaseSlot = vkHeaderBytes R.pv vkG2BaseSlot 8 from rfl,
    vkHeaderBytes_size] at hsize
  have hmin : min 8 (R.pv.vk.constants.length - vkG2BaseSlot) = 8 := by omega
  omega

theorem negSG2_constants_length (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (product : PairingProduct)
    (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) :
    vkNegSG2BaseSlot + 8 ≤ R.pv.vk.constants.length := by
  obtain ⟨pt, hpt, -⟩ := hpc.g2Valid R.sG2gen⁻¹
  have hsize := g2Of?_size hpt
  change 256 ≤ (R.encG2 R.sG2gen⁻¹).size at hsize
  rw [← hR.payload.negSG2] at hsize
  change 256 ≤ (vkG2Words R.pv vkNegSG2BaseSlot).size at hsize
  rw [show vkG2Words R.pv vkNegSG2BaseSlot = vkHeaderBytes R.pv vkNegSG2BaseSlot 8 from rfl,
    vkHeaderBytes_size] at hsize
  have hmin : min 8 (R.pv.vk.constants.length - vkNegSG2BaseSlot) = 8 := by omega
  omega

#assert_axioms Midfall.LoweringV3.g2Of?_size
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.vkHeaderBytes_size
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.g2Base_constants_length
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.negSG2_constants_length
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.vk_len_ge_of_header
  [propext, Classical.choice, Quot.sound] native []


theorem bytesAt_vkG2Base_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (product : PairingProduct) (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n) :
    bytesAt st (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base)) 256 =
      vkG2Words R.pv vkG2BaseSlot :=
  bytesAt_vkG2Base R hR st hpayload hptr (g2Base_constants_length R hR product hpc)
    (vk_len_ge_of_header R (g2Base_constants_length R hR product hpc))

theorem bytesAt_vkNegSG2Base_of_valid (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R)
    (product : PairingProduct) (hpc : Midfall.Assumptions.Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n) :
    bytesAt st (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base)) 256 =
      vkG2Words R.pv vkNegSG2BaseSlot :=
  bytesAt_vkNegSG2Base R hR st hpayload hptr (negSG2_constants_length R hR product hpc)
    (vk_len_ge_of_header R (negSG2_constants_length R hR product hpc))

#assert_axioms Midfall.LoweringV3.bytesAt_vkG2Base_of_valid
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.bytesAt_vkNegSG2Base_of_valid
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3
