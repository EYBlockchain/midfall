/-
  Midfall.LoweringV3.FpWire

  ROW.FP (WP A11) - the payload-image wire.

  `ec_pairing` copies its G2 arguments out of the VK payload at `G2_BASE_MPTR` /
  `NEG_S_G2_BASE_MPTR`.  `Inv .vk` pins the payload image as `PV.vk.bytes`, whose
  definition is a fold of `wordToBytesBE` over the constant words followed by the
  fixed and permutation commitments.  These lemmas cut the 32-byte word chunks out
  of that fold, at the `Nat` address the const table computes:

    bytesAt st (ptrAddr vkMptr + 32 * i) (32 * n) = vkHeaderBytes PV i n

  for i + n ≤ constants.length.  This is the bridge `PayloadAgrees` cannot cross
  (it speaks about `constants.getD i`, not memory) and the input to the G2 slots
  in the FP row.  No new hypothesis; no native_decide.
-/
import Midfall.LoweringV3.VkClean
import Midfall.LoweringV2.Blocks.EcPairing

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3 Midfall.LoweringV3.VkClean

namespace Midfall.LoweringV3

theorem fold_bytes_length (ws : List Word256) :
    (ws.foldl (fun a w => a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList.length
      = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [List.foldl_cons, Midfall.LoweringV3.VkClean.bytes_empty_append, foldlA]
      have hlen : (Midfall.wordToBytesBE w).data.toList.length = 32 :=
        Midfall.LoweringV2.wordToBytesBE_size w
      rw [List.length_append, hlen, ih]
      simp
      omega

theorem fold_bytes_append (ws rest : List Word256) :
    (ws.foldl (fun a w => a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList ++
      (rest.foldl (fun a w => a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList
      = ((ws ++ rest).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
          Midfall.Bytes.empty).data.toList := by
  rw [List.foldl_append]
  exact (foldlA rest (ws.foldl (fun a w => a.append (Midfall.wordToBytesBE w))
    Midfall.Bytes.empty)).symm

theorem fold_bytes_take (ws : List Word256) (n : Nat) (hn : n ≤ ws.length) :
    (ws.foldl (fun a w => a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList.take (32 * n)
      = ((ws.take n).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
          Midfall.Bytes.empty).data.toList := by
  have h := fold_bytes_append (ws.take n) (ws.drop n)
  rw [List.take_append_drop] at h
  rw [← h]
  have hlen : ((ws.take n).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
      Midfall.Bytes.empty).data.toList.length = 32 * (ws.take n).length := fold_bytes_length _
  rw [List.take_append_of_le_length (by rw [hlen, List.length_take]; omega)]
  exact List.take_of_length_le (by rw [hlen, List.length_take]; omega)

theorem fold_bytes_drop_take (ws : List Word256) (i n : Nat) (h : i + n ≤ ws.length) :
    ((ws.foldl (fun a w => a.append (Midfall.wordToBytesBE w)) Midfall.Bytes.empty).data.toList.drop
        (32 * i)).take (32 * n)
      = (((ws.drop i).take n).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
          Midfall.Bytes.empty).data.toList := by
  revert i n
  induction ws with
  | nil =>
      intro i n h
      simp only [List.length_nil] at h
      have hi : i = 0 := by omega
      have hn : n = 0 := by omega
      subst hi; subst hn
      rfl
  | cons w ws ih =>
      intro i n h
      cases i with
      | zero =>
          have hn : n ≤ (w :: ws).length := by omega
          simpa using fold_bytes_take (w :: ws) n hn
      | succ i =>
          have h' : i + 1 + n ≤ ws.length + 1 := by simpa using h
          have hi : i + n ≤ ws.length := by omega
          have hrec := ih i n hi
          rw [List.foldl_cons, Midfall.LoweringV3.VkClean.bytes_empty_append,
            Midfall.LoweringV3.VkClean.foldlA ws (Midfall.wordToBytesBE w)]
          rw [show 32 * (i + 1) = 32 + 32 * i by omega]
          have hlen : (Midfall.wordToBytesBE w).data.toList.length = 32 :=
            Midfall.LoweringV2.wordToBytesBE_size w
          rw [List.drop_append,
            List.drop_eq_nil_of_le (by rw [hlen]; omega),
            List.nil_append, hlen,
            show 32 + 32 * i - 32 = 32 * i by omega]
          rw [hrec]
          rfl

open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

theorem readBytes_drop (mem : Nat → UInt8) (p off n : Nat) :
    readBytes mem (p + off) n = (readBytes mem p (off + n)).drop off := by
  rw [Midfall.LoweringV2.Blocks.EcPairing.readBytes_append, List.drop_append,
    List.drop_eq_nil_of_le (by simp [readBytes]), List.nil_append]
  simp [readBytes]

theorem readBytes_take (mem : Nat → UInt8) (p m n : Nat) (hmn : m ≤ n) :
    readBytes mem p m = (readBytes mem p n).take m := by
  rw [show n = m + (n - m) by omega]
  rw [Midfall.LoweringV2.Blocks.EcPairing.readBytes_append, List.take_append_of_le_length (by simp [readBytes])]
  exact (List.take_of_length_le (by simp [readBytes])).symm

theorem fold_bytes_drop_take_append (ws rest : List Word256) (i n : Nat) (hi : i + n ≤ ws.length) :
    (((ws ++ rest).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
        Midfall.Bytes.empty).data.toList.drop (32 * i)).take (32 * n)
      = (((ws.drop i).take n).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
          Midfall.Bytes.empty).data.toList := by
  rw [← fold_bytes_append ws rest]
  rw [List.drop_append_of_le_length (by rw [fold_bytes_length]; omega)]
  rw [List.take_append_of_le_length (by
    rw [List.length_drop, fold_bytes_length]; omega)]
  exact fold_bytes_drop_take ws i n hi

theorem readBytes_vkHeader (st : EvmState) (PV : PlanView) (i n : Nat)
    (hpayload : readBytes st.memory (ptrAddr PV.memory.vkMptr) PV.vk.len = PV.vk.bytes.data.toList)
    (hfit : 32 * (i + n) ≤ PV.vk.len)
    (hi : i + n ≤ PV.vk.constants.length) :
    readBytes st.memory (ptrAddr PV.memory.vkMptr + 32 * i) (32 * n) =
      (vkHeaderBytes PV i n).data.toList := by
  let rest1 : List Word256 :=
    PV.vk.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])
  let rest2 : List Word256 :=
    PV.vk.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])
  let f : String × Word256 → Word256 := fun x => x.2
  let ws : List Word256 := PV.vk.constants.map f ++ rest1
  have hbytes : PV.vk.bytes.data.toList =
      ((ws ++ rest2).foldl (fun a w => a.append (Midfall.wordToBytesBE w))
        Midfall.Bytes.empty).data.toList := rfl
  rw [readBytes_drop]
  rw [show 32 * i + 32 * n = 32 * (i + n) by omega]
  rw [readBytes_take _ _ _ _ hfit, hpayload, hbytes]
  rw [List.drop_take, show 32 * (i + n) - 32 * i = 32 * n by omega]
  rw [fold_bytes_drop_take_append ws rest2 i n (by simp [ws]; omega)]
  have hmap : (ws.drop i).take n = ((PV.vk.constants.drop i).take n).map f := by
    change ((PV.vk.constants.map f ++ rest1).drop i).take n = _
    have hi' : i ≤ (PV.vk.constants.map f).length := by simp; omega
    have htake' : n ≤ ((PV.vk.constants.map f).drop i).length := by
      simp [List.length_drop]; omega
    rw [List.drop_append_of_le_length hi', List.take_append_of_le_length htake']
    rw [← List.map_drop, ← List.map_take]
  rw [hmap, List.foldl_map]
  rfl

theorem bytesAt_vkHeader (st : EvmState) (PV : PlanView) (i n : Nat)
    (hpayload : bytesAt st (ptrAddr PV.memory.vkMptr) PV.vk.len = PV.vk.bytes)
    (hfit : 32 * (i + n) ≤ PV.vk.len)
    (hi : i + n ≤ PV.vk.constants.length) :
    bytesAt st (ptrAddr PV.memory.vkMptr + 32 * i) (32 * n) = vkHeaderBytes PV i n := by
  have hr : readBytes st.memory (ptrAddr PV.memory.vkMptr) PV.vk.len = PV.vk.bytes.data.toList := by
    have h := congrArg Array.toList (congrArg ByteArray.data hpayload)
    simpa [bytesAt] using h
  have hread := readBytes_vkHeader st PV i n hr hfit hi
  apply ByteArray.ext
  simp [bytesAt, hread]


#assert_axioms Midfall.LoweringV3.fold_bytes_drop_take
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.readBytes_vkHeader
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.bytesAt_vkHeader
  [propext, Classical.choice, Quot.sound] native []

section FpWireRender
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- The `G2_BASE_MPTR` slice of the VK payload image is the header's G2 slot.  The two length
    facts (`hconst`, `hfit`) are the only inputs the payload image does not itself carry; the
    row must discharge them from the render's payload, not add them to `ValidV3`. -/
theorem bytesAt_vkG2Base (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n)
    (hconst : vkG2BaseSlot + 8 ≤ R.pv.vk.constants.length)
    (hfit : 32 * (vkG2BaseSlot + 8) ≤ R.pv.vk.len) :
    bytesAt st (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.g2Base)) 256 =
      vkG2Words R.pv vkG2BaseSlot := by
  have hH := Midfall.LoweringV3.MemoryPairs.vkHeader_default_of_generated hR.generated
  rw [hH]
  have hptrEq := Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer R.pv.memory.vkMptr
    vkHeaderTemplateSlotsDefault.g2Base hptr
  change bytesAt st (ptrAddr (Ptr.add R.pv.memory.vkMptr
    vkHeaderTemplateSlotsDefault.g2Base)) 256 = vkHeaderBytes R.pv vkG2BaseSlot 8
  rw [hptrEq]
  exact bytesAt_vkHeader st R.pv vkG2BaseSlot 8 hpayload hfit hconst


/-- The `NEG_S_G2_BASE_MPTR` slice of the payload image; the same proof as the base slot. -/
theorem bytesAt_vkNegSG2Base (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) (st : EvmState)
    (hpayload : bytesAt st (ptrAddr R.pv.memory.vkMptr) R.pv.vk.len = R.pv.vk.bytes)
    (hptr : ∃ n : ℕ, ptrValue R.pv.memory.vkMptr = Value.integer ↑n)
    (hconst : vkNegSG2BaseSlot + 8 ≤ R.pv.vk.constants.length)
    (hfit : 32 * (vkNegSG2BaseSlot + 8) ≤ R.pv.vk.len) :
    bytesAt st (Midfall.LoweringV3.cAddr (Ptr.add R.pv.memory.vkMptr R.model.vkHeader.negSG2Base)) 256 =
      vkG2Words R.pv vkNegSG2BaseSlot := by
  have hH := Midfall.LoweringV3.MemoryPairs.vkHeader_default_of_generated hR.generated
  rw [hH]
  have hptrEq := Midfall.LoweringV3.VkClean.ptrAddr_ptr_add_of_integer R.pv.memory.vkMptr
    vkHeaderTemplateSlotsDefault.negSG2Base hptr
  change bytesAt st (ptrAddr (Ptr.add R.pv.memory.vkMptr
    vkHeaderTemplateSlotsDefault.negSG2Base)) 256 = vkHeaderBytes R.pv vkNegSG2BaseSlot 8
  rw [hptrEq]
  exact bytesAt_vkHeader st R.pv vkNegSG2BaseSlot 8 hpayload hfit hconst

end FpWireRender

#assert_axioms Midfall.LoweringV3.bytesAt_vkNegSG2Base
  [propext, Classical.choice, Quot.sound] native []

#assert_axioms Midfall.LoweringV3.bytesAt_vkG2Base
  [propext, Classical.choice, Quot.sound] native []


end Midfall.LoweringV3

namespace Midfall.Lowering

/-- `Checkpoint`'s `LE` is `idx` comparison; this is the unfold the `InvAt` guard
    reductions need (the instance itself is not a simp lemma). -/
theorem checkpoint_le_def (a b : Checkpoint) : (a ≤ b) = (a.idx ≤ b.idx) := rfl

/-- The selector-bucket clause only weakens from `.pcs` to `.pairing`: a permanent
    region keeps the same `holdsFrs`, `pcsFinalMsm` is live at `.pcs` and dropped at
    `.pairing`, and every other lifetime is dead at both. -/
theorem selectorBucket_mono (M : VerifierMemoryLayout) (P : Bool) :
    (if Checkpoint.liveRegionNamed Checkpoint.pcs M "selector_accumulators" then P else true) = true →
    (if Checkpoint.liveRegionNamed Checkpoint.pairing M "selector_accumulators" then P else true) = true := by
  intro h
  unfold Checkpoint.liveRegionNamed at h ⊢
  cases hlt : regionLifetime M "selector_accumulators" with
  | none => simp [hlt] at h ⊢
  | some lt =>
      cases lt with
      | permanent => simpa [hlt, Checkpoint.liveAt] using h
      | phase ph =>
          have hq1 : (Checkpoint.pcs == Checkpoint.quotient) = false := by decide
          have hp1 : (Checkpoint.pcs == Checkpoint.pcs) = true := by decide
          have hq2 : (Checkpoint.pairing == Checkpoint.quotient) = false := by decide
          have hp2 : (Checkpoint.pairing == Checkpoint.pcs) = false := by decide
          cases ph <;> simp [hlt, Checkpoint.liveAt, hq1, hp1, hq2, hp2] at h ⊢

#assert_axioms Midfall.Lowering.checkpoint_le_def
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.Lowering.selectorBucket_mono
  [propext, Classical.choice, Quot.sound] native []

end Midfall.Lowering
