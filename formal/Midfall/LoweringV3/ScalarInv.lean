/-
  Midfall.LoweringV3.ScalarInv

  A9 (ROW.PCS, block 4 helper) - THE MEMORY-LEVEL `scalar_inv` FRAME.

  `GenAst.emitScalarInvAt` writes six 32-byte words at `p, p+32, …, p+160`
  (`modexpFrameStores`, GenAst.lean:408-417): the EIP-198 lengths `32,32,32`, the base `x`,
  the exponent `FR_MODULUS - 2`, and the modulus `FR_MODULUS`. This file proves that the six
  stores read back as exactly `modexpInvFrame x` (`Yul/Externals.lean:560`), i.e. the frame
  `modexpInv_correct` (`Assumptions/Eip2537.lean:825`) parses. It lands NO summary yet and
  wires no row: the `fail` effect, the guard arms, the honest staticcall and the read-back
  are the next pieces.

  The bridge uses the already-landed 32-byte facts `readBytes_storeWord_32`,
  `bytesToNatBE_readBytes_32`, `readBytes_append` and `readBytes_storeWord_outside`
  (`PcsRows.lean`). No fixture, no native_decide, no extra hypothesis.
-/
import Midfall.LoweringV3.PcsRows
set_option autoImplicit false

namespace Midfall.LoweringV3.ScalarInv

open Midfall Midfall.Lowering Midfall.Generator Midfall.LoweringV3.PcsRows
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

/-! ## 1. A fold of stores at `p, p+32, …` -/

/-- Store a list of words at `p + 32*i`, left to right. -/
def storeWords (mem : Nat → UInt8) (p : Nat) : List U256 → Nat → (Nat → UInt8)
  | [], _ => mem
  | v :: vs, i => storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1)

/-- All stores of `storeWords … vs i` are at addresses `≥ p + 32*i`, so a read whose window
    ends before `p + 32*i` is blind to them. -/
theorem readBytes_storeWords_outside (mem : Nat → UInt8) (p : Nat) :
    ∀ (vs : List U256) (i q n : Nat), q + n ≤ p + 32 * i →
      readBytes (storeWords mem p vs i) q n = readBytes mem q n
  | [], i, q, n, _ => rfl
  | v :: vs, i, q, n, h => by
      change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1)) q n =
        readBytes mem q n
      rw [readBytes_storeWords_outside (storeWord mem (p + 32 * i) v) p vs (i + 1) q n
        (by omega)]
      rw [readBytes_storeWord_outside (mem := mem) (q := p + 32 * i) (v := v) (p := q) (n := n)
        (by omega)]

/-- **A BLOCK OF THE TABLE**: after `storeWords`, the 32 bytes at `p + 32*(i+k)` are the
    `bytesNatBE` encoding of the `k`-th word. -/
theorem readBytes_storeWords_block (mem : Nat → UInt8) (p : Nat) :
    ∀ (vs : List U256) (i k : Nat), k < vs.length →
      readBytes (storeWords mem p vs i) (p + 32 * (i + k)) 32 =
        (bytesNatBE (vs.getD k 0).toNat 32).data.toList
  | [], i, k, hk => absurd hk (Nat.not_lt_zero k)
  | v :: vs, i, k, hk => by
      cases k with
      | zero =>
          change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1))
            (p + 32 * i) 32 = (bytesNatBE v.toNat 32).data.toList
          rw [readBytes_storeWords_outside (storeWord mem (p + 32 * i) v) p vs (i + 1)
            (p + 32 * i) 32 (by omega)]
          rw [readBytes_storeWord_32]
      | succ k =>
          have hk' : k < vs.length := by simpa using hk
          change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1))
            (p + 32 * (i + (k + 1))) 32 = (bytesNatBE (vs.getD k 0).toNat 32).data.toList
          rw [show p + 32 * (i + (k + 1)) = p + 32 * ((i + 1) + k) by omega]
          exact readBytes_storeWords_block (storeWord mem (p + 32 * i) v) p vs (i + 1) k hk'

/-! ## 2. The six words of `scalar_inv` -/

/-- The six memory words `scalar_inv` writes. -/
def mxMem (mem : Nat → UInt8) (p : Nat) (x : U256) : Nat → UInt8 :=
  storeWord (storeWord (storeWord (storeWord (storeWord (storeWord mem p 32)
    (p + 32) 32) (p + 64) 32) (p + 96) x) (p + 128)
    (BitVec.ofNat 256 (Midfall.Yul.blsR - 2))) (p + 160) (BitVec.ofNat 256 Midfall.Yul.blsR)

/-- The same six words as a list, for the block lemma. -/
def mxWords (x : U256) : List U256 :=
  [32, 32, 32, x, BitVec.ofNat 256 (Midfall.Yul.blsR - 2), BitVec.ofNat 256 Midfall.Yul.blsR]

theorem mxMem_eq_storeWords (mem : Nat → UInt8) (p : Nat) (x : U256) :
    mxMem mem p x = storeWords mem p (mxWords x) 0 := rfl

/-- **THE SIX-BLOCK READ**: the 192 bytes read back are the six `bytesNatBE` blocks. -/
theorem mxMem_read192 (mem : Nat → UInt8) (p : Nat) (x : U256) :
    readBytes (mxMem mem p x) p 192 =
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE 32 32).data.toList ++
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE x.toNat 32).data.toList ++
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList ++
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
  rw [mxMem_eq_storeWords]
  have h0 : readBytes (storeWords mem p (mxWords x) 0) p 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 0 (by simp [mxWords])
  have h1 : readBytes (storeWords mem p (mxWords x) 0) (p + 32) 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 1 (by simp [mxWords])
  have h2 : readBytes (storeWords mem p (mxWords x) 0) (p + 64) 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 2 (by simp [mxWords])
  have h3 : readBytes (storeWords mem p (mxWords x) 0) (p + 96) 32 =
      (bytesNatBE x.toNat 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 3 (by simp [mxWords])
  have hbR : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have hbR2 : Midfall.Yul.blsR - 2 < 2 ^ 256 := by omega
  have htoR2 : (BitVec.ofNat 256 (Midfall.Yul.blsR - 2)).toNat = Midfall.Yul.blsR - 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR2]
  have htoR : (BitVec.ofNat 256 Midfall.Yul.blsR).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR]
  have h4 : readBytes (storeWords mem p (mxWords x) 0) (p + 128) 32 =
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList := by
    simpa [mxWords, htoR2] using
      readBytes_storeWords_block mem p (mxWords x) 0 4 (by simp [mxWords])
  have h5 : readBytes (storeWords mem p (mxWords x) 0) (p + 160) 32 =
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
    simpa [mxWords, htoR] using
      readBytes_storeWords_block mem p (mxWords x) 0 5 (by simp [mxWords])
  rw [show 192 = 32 + 160 by omega, readBytes_append]
  rw [show 160 = 32 + 128 by omega, readBytes_append]
  rw [show 128 = 32 + 96 by omega, readBytes_append]
  rw [show 96 = 32 + 64 by omega, readBytes_append]
  rw [show 64 = 32 + 32 by omega, readBytes_append]
  rw [h0, h1, h2, h3, h4, h5]
  simp [List.append_assoc]

/-- **THE FRAME DATA**: `modexpInvFrame x` is the same six blocks. -/
theorem modexpInvFrame_data (x : Nat) :
    (modexpInvFrame x).data.toList =
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE 32 32).data.toList ++
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE x 32).data.toList ++
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList ++
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
  unfold modexpInvFrame modexpFrame
  simp [bytesOfWords, bytesAppend, Midfall.Yul.wordBytes, Bytes.empty, List.append_assoc]

/-- **THE SIX-STORE FRAME EQUALITY**: `scalar_inv`'s six stores read back as exactly the
    frame `modexpInv_correct` parses. -/
theorem mxMem_frame (mem : Nat → UInt8) (p : Nat) (x : U256) :
    readBytes (mxMem mem p x) p 192 = (modexpInvFrame x.toNat).data.toList := by
  rw [mxMem_read192, ← modexpInvFrame_data]

#assert_axioms Midfall.LoweringV3.ScalarInv.mxMem_frame
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3.ScalarInv
