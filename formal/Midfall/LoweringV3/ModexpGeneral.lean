-- |
-- Midfall.LoweringV3.ModexpGeneral
--
-- The MEMORY-LEVEL half of the modexp bridge for `batch_invert_summary` (HLP.1.c): the 32-byte
-- store/read frame is A9's `PcsRows.readBytes_storeWord_32`; here are the two fold facts that turn
-- the six stored words into the precompile's frame values, and the `bytesToNatBE`/`loadWord`
-- equality the staticcall step needs.
import Midfall.LoweringV3.PcsRows
import Midfall.LoweringV3.BatchInvert
import Midfall.LoweringV3.ScalarInv
import Midfall.Assumptions.Eip2537

set_option autoImplicit false

open Midfall Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3.QuotientRows Midfall.LoweringV3.LagrangeRows
open Midfall.LoweringV3.BatchInvert Midfall.LoweringV3.PcsRows

namespace Midfall.LoweringV3.ModexpGeneral

theorem shift_or_toNat {acc : U256} {b : UInt8} (h : acc.toNat < 2 ^ 248) :
    ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat = acc.toNat * 256 + b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  have hshift : (acc <<< 8).toNat = acc.toNat * 256 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hor : (acc.toNat * 256) ||| b.toNat = acc.toNat * 256 + b.toNat := by
    rw [show acc.toNat * 256 = acc.toNat <<< 8 from by rw [Nat.shiftLeft_eq]]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (b := b.toNat) (by omega) acc.toNat,
      Nat.shiftLeft_eq]
  rw [BitVec.toNat_or, hshift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hor

theorem foldl_shift_or_toNat (l : List UInt8) (acc : U256)
    (hl : l.length ≤ 32) (h : acc.toNat < 256 ^ (32 - l.length)) :
    (l.foldl (fun (acc : U256) (b : UInt8) => (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) acc).toNat =
      l.foldl (fun (acc : Nat) (b : UInt8) => acc * 256 + b.toNat) acc.toNat := by
  induction l generalizing acc with
  | nil => rfl
  | cons b t ih =>
      simp only [List.foldl_cons]
      have hlen : (b :: t).length = t.length + 1 := rfl
      rw [hlen] at h
      have hlen2 : t.length ≤ 31 := by simp at hl; omega
      have hexp : 32 - (t.length + 1) = 31 - t.length := by omega
      rw [hexp] at h
      have h248 : acc.toNat < 2 ^ 248 := by
        have hle : (256 : Nat) ^ (31 - t.length) ≤ 2 ^ 248 := by
          rw [show (2 : Nat) ^ 248 = 256 ^ 31 from by
            rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hstep : ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat < 256 ^ (32 - t.length) := by
        rw [shift_or_toNat h248]
        have hb : b.toNat < 256 := b.toNat_lt
        have hacc : acc.toNat + 1 ≤ (256 : Nat) ^ (31 - t.length) := by omega
        calc acc.toNat * 256 + b.toNat < (acc.toNat + 1) * 256 := by omega
          _ ≤ (256 : Nat) ^ (31 - t.length) * 256 := Nat.mul_le_mul_right 256 hacc
          _ = (256 : Nat) ^ (32 - t.length) := by
            rw [show 32 - t.length = (31 - t.length) + 1 by omega, Nat.pow_succ]
      rw [show acc.toNat * 256 + b.toNat = ((acc <<< 8) ||| BitVec.ofNat 256 b.toNat).toNat
        from (shift_or_toNat h248).symm]
      exact ih (acc := (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) (by omega) hstep


theorem bytesToNatBE_readBytes (mem : Nat → UInt8) (p : Nat) :
    bytesToNatBE (ByteArray.mk (readBytes mem p 32).toArray) = (loadWord mem p).toNat := by
  have hlen : (readBytes mem p 32).length = 32 := by simp [readBytes]
  rw [bytesToNatBE_toList]
  show (ByteArray.mk (readBytes mem p 32).toArray).data.toList.foldl
      (fun (acc : Nat) (x : UInt8) => acc * 256 + x.toNat) 0 = _
  rw [show (ByteArray.mk (readBytes mem p 32).toArray).data.toList = readBytes mem p 32 from rfl]
  have hword : (loadWord mem p).toNat =
      ((readBytes mem p 32).foldl
        (fun (acc : U256) (b : UInt8) => (acc <<< 8) ||| BitVec.ofNat 256 b.toNat) 0).toNat := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hword]
  exact (foldl_shift_or_toNat (readBytes mem p 32) 0 (by omega)
    (by rw [hlen]; norm_num)).symm

theorem readBytes_append (mem : Nat → UInt8) (p n m : Nat) :
    readBytes mem p (n + m) = readBytes mem p n ++ readBytes mem (p + n) m := by
  unfold readBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  show mem (p + (n + x)) = mem (p + n + x)
  rw [Nat.add_assoc]

theorem readBytes_storeWord_disjoint (mem : Nat → UInt8) (p q n : Nat) (v : U256)
    (h : q + n ≤ p ∨ p + 32 ≤ q) :
    readBytes (storeWord mem p v) q n = readBytes mem q n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  show storeWord mem p v (q + i) = mem (q + i)
  unfold storeWord
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  rcases h with h | h <;> omega

theorem bytesAppend_toList (a b : Bytes) :
    (bytesAppend a b).data.toList = a.data.toList ++ b.data.toList := by
  unfold bytesAppend
  show (ByteArray.mk (a.data ++ b.data)).data.toList = _
  simp


/-! ## The batch frame as `modexpInvFrame` and its honest output -/

/-- The six stores of the batch frame (base `x`, modulus `blsR`) as a `ByteArray` are exactly
`modexpInvFrame x.toNat`: the list equality is A9's `ScalarInv.mxMem_frame`, lifted through
`Array.toArray_toList`/`ByteArray.ext`. -/
theorem mxMem_frame_byteArray (mem : Nat → UInt8) (p : Nat) (x : U256) :
    ByteArray.mk (readBytes (Midfall.LoweringV3.ScalarInv.mxMem mem p x) p 192).toArray =
      modexpInvFrame x.toNat := by
  rw [Midfall.LoweringV3.ScalarInv.mxMem_frame]

theorem mxMem_modexpOutput (mem : Nat → UInt8) (p : Nat) (x : U256)
    (hx0 : 0 < x.toNat) (hx : x.toNat < Midfall.Yul.blsR) :
    modexpOutput (ByteArray.mk (readBytes (Midfall.LoweringV3.ScalarInv.mxMem mem p x) p 192).toArray) =
      some (bytesNatBE ((x.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32) := by
  rw [mxMem_frame_byteArray]
  exact modexpInv_correct x.toNat hx0 hx



/-! ## The honest modexp answer at address `5` -/

/-- The `honestOf` fold at target `5` picks `modexpRelation`: the three other precompiles'
addresses do not hit. -/
theorem honestOf_modexp_find (product : PairingProduct) (req : YulSemantics.EVM.CallRequest)
    (h : req.target = Midfall.Yul.modexpAddress) :
    List.find? (fun r => Midfall.Yul.Bridge.hits r req)
      (Midfall.Yul.honestRelations product) = some Midfall.Yul.modexpRelation := by
  rw [Midfall.Yul.honestRelations]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.g1AddRelation,
      Midfall.Yul.g1AddAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.g1MsmRelation,
      Midfall.Yul.g1MsmAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_neg (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.pairingRelation,
      Midfall.Yul.pairingAddress, Midfall.Yul.modexpAddress, h])]
  rw [List.find?_cons_of_pos (by
    simp [Midfall.Yul.Bridge.hits, accountKey, Midfall.Yul.modexpRelation,
      Midfall.Yul.modexpAddress, h])]

/-- **THE HONEST MODEXP RESPONSE**: a successful `callsOf` call at target `5` with a valid input
returns exactly that input's `modexpOutput`. This is the `permissive` success inversion the
staticcall step needs. -/
theorem callsOf_modexp_returndata
    {product : PairingProduct} {req : YulSemantics.EVM.CallRequest}
    {st : EvmState} {resp : CallResponse} {out : Bytes}
    (htarget : req.target = Midfall.Yul.modexpAddress)
    (hvalid : modexpValidInput (ByteArray.mk req.input.toArray) = true)
    (hout : modexpOutput (ByteArray.mk req.input.toArray) = some out)
    (hcall : (callsOf product).Call req st resp) (hsucc : resp.success = true) :
    resp.returndata = out.data.toList := by
  rcases hcall with h | ⟨_, hf⟩
  · unfold honestOf at h
    rw [honestOf_modexp_find product req htarget] at h
    simp only [Midfall.Yul.modexpRelation, ExternalCallRelation.respond, toYulReq,
      hvalid, hout, htarget, Bool.not_true, ite_false, Option.map_some,
      Option.some.injEq] at h
    subst h
    rfl
  · exact absurd hf (by simp)

/-- A successful `modexpOutput` implies the input is within the EIP-7823 limits, i.e. the
precompile accepts it. (`modexpParse?` returns `none` exactly when the limits fail.) -/
theorem modexpValidInput_of_output_some {input : Bytes} {out : Bytes}
    (h : modexpOutput input = some out) : modexpValidInput input = true := by
  by_contra hv
  have hv' : modexpWithinLimits input = false := by
    by_cases hh : modexpWithinLimits input = true
    · exact absurd hh hv
    · cases hc : modexpWithinLimits input <;> simp_all
  unfold modexpOutput at h
  have hparse : modexpParse? input = none := by
    unfold modexpParse?
    rw [if_neg (by rw [hv']; decide)]
  rw [hparse] at h
  cases h


#assert_axioms shift_or_toNat [propext, Classical.choice, Quot.sound]
#assert_axioms foldl_shift_or_toNat [propext, Classical.choice, Quot.sound]
#assert_axioms bytesToNatBE_readBytes [propext, Classical.choice, Quot.sound]
#assert_axioms readBytes_append [propext, Classical.choice, Quot.sound]
#assert_axioms readBytes_storeWord_disjoint [propext, Classical.choice, Quot.sound]
#assert_axioms bytesAppend_toList [propext, Classical.choice, Quot.sound]
theorem readBytes_six (mem : Nat → UInt8) (p : Nat) (w0 w1 w2 w3 w4 w5 : U256) :
    readBytes (storeWord (storeWord (storeWord (storeWord (storeWord (storeWord mem p w0)
      (p + 32) w1) (p + 64) w2) (p + 96) w3) (p + 128) w4) (p + 160) w5) p 192 =
    (bytesNatBE w0.toNat 32).data.toList ++ (bytesNatBE w1.toNat 32).data.toList ++
      (bytesNatBE w2.toNat 32).data.toList ++ (bytesNatBE w3.toNat 32).data.toList ++
      (bytesNatBE w4.toNat 32).data.toList ++ (bytesNatBE w5.toNat 32).data.toList := by
  simp only [show 192 = 32 + 32 + 32 + 32 + 32 + 32 by norm_num, readBytes_append]
  simp only [show p + (32 + 32) = p + 64 by omega,
    show p + (32 + 32 + 32) = p + 96 by omega,
    show p + (32 + 32 + 32 + 32) = p + 128 by omega,
    show p + (32 + 32 + 32 + 32 + 32) = p + 160 by omega]
  rw [readBytes_storeWord_disjoint _ (p + 160) p 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) p 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) p 32 w3 (by omega),
    readBytes_storeWord_disjoint _ (p + 64) p 32 w2 (by omega),
    readBytes_storeWord_disjoint _ (p + 32) p 32 w1 (by omega),
    readBytes_storeWord_32 _ p w0,
    readBytes_storeWord_disjoint _ (p + 160) (p + 32) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 32) 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) (p + 32) 32 w3 (by omega),
    readBytes_storeWord_disjoint _ (p + 64) (p + 32) 32 w2 (by omega),
    readBytes_storeWord_32 _ (p + 32) w1,
    readBytes_storeWord_disjoint _ (p + 160) (p + 64) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 64) 32 w4 (by omega),
    readBytes_storeWord_disjoint _ (p + 96) (p + 64) 32 w3 (by omega),
    readBytes_storeWord_32 _ (p + 64) w2,
    readBytes_storeWord_disjoint _ (p + 160) (p + 96) 32 w5 (by omega),
    readBytes_storeWord_disjoint _ (p + 128) (p + 96) 32 w4 (by omega),
    readBytes_storeWord_32 _ (p + 96) w3,
    readBytes_storeWord_disjoint _ (p + 160) (p + 128) 32 w5 (by omega),
    readBytes_storeWord_32 _ (p + 128) w4,
    readBytes_storeWord_32 _ (p + 160) w5]

#assert_axioms readBytes_six [propext, Classical.choice, Quot.sound]
#assert_axioms mxMem_frame_byteArray [propext, Classical.choice, Quot.sound]
#assert_axioms mxMem_modexpOutput [propext, Classical.choice, Quot.sound]
#assert_axioms honestOf_modexp_find [propext, Classical.choice, Quot.sound]
#assert_axioms callsOf_modexp_returndata [propext, Classical.choice, Quot.sound]
#assert_axioms modexpValidInput_of_output_some [propext, Classical.choice, Quot.sound]

end Midfall.LoweringV3.ModexpGeneral
