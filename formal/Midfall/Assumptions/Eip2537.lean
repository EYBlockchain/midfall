-- |
-- Midfall.Assumptions.Eip2537
--
-- P-SE stage 1 (docs/plans/P-SE-stage1.md, file row 4; PLAN
-- P-SE-semantic-equivalence.md section D and index item 4; design0.md
-- 'Midfall.Assumptions.Eip2537.Holds'; design2.md 'Eip2537.Holds / G2Enc /
-- modexpInv_correct').
--
-- WHAT THIS FILE IS FOR. The deployed verifier does not compute pairings: it
-- staticcalls the EIP-2537 precompiles at 0x0b (G1ADD), 0x0c (G1MSM) and 0x0f
-- (PAIRING_CHECK), and EIP-198 modexp at 0x05. Midfall/Yul/Externals.lean models
-- the BYTE side of those frames and computes everything it can - G1ADD, G1MSM and
-- modexp results are all computed there - but it cannot compute the pairing
-- product, because that needs Fp12 and no Lean library has BLS12-381 at all
-- (docs/ecosystem.md, D-P1). Externals.lean:934-941 names that hole
-- PairingProduct := Bytes -> Bool and leaves it a parameter. This file is where
-- the parameter is pinned to the abstract pairing: Eip2537.Holds is the named
-- hypothesis saying the precompile answers agree with AdmissiblePairing.e, the
-- group law and the scalar action through the codecs. Per the gap policy (plan
-- Section 3) an unproven fact is a binder here, never a proof hole.
--
-- WHICH SHAPE, and why. attack.md line 7 records that the three design passes
-- proposed incompatible Holds signatures (P1: list-general pairing_iff over
-- msmSpecific; P2: a two-pair pairing2 with a bare G2 encoder function), and
-- line 84 FIX settles it: one file, P2 two-pair form - the verifier never pairs
-- more than two pairs (AssemblyHelpers.yul:294 staticcalls PAIRING_GAS_2PAIR on a
-- 0x300-byte frame) - wrapped in P1 G2Enc structure, because a bare G2 -> Bytes
-- field cannot carry the VK-header link the Surface needs. D14 in the stage-1
-- brief restates the same decision. The frame is CALLER-ordered: ec_pairing lays
-- out [lhs_g1 | G2_BASE | rhs_g1 | NEG_S_G2_BASE] (AssemblyHelpers.yul:284-287)
-- but FinalPairing.yul:88 calls ec_pairing(success, PAIRING_RHS_MPTR,
-- PAIRING_LHS_MPTR), so the pairs the precompile actually sees are
-- [(rhs, G2), (lhs, -sG2)]. R-11 is the port finding: the orientation flips at
-- the call site, not in pairingFrame, so Holds is stated over the frame as laid
-- out and finalPairing_spec (stage 4) owns the swap.
--
-- WHAT IS NOT AN ASSUMPTION HERE. Modexp is not a hypothesis: Externals.modexpOutput
-- computes base^exp mod modulus by square-and-multiply, so the correctness of the
-- inversion frame is a THEOREM (modexpInv_correct below), stated as a hole rather
-- than as a field so nobody later mistakes the modelled arithmetic for trusted
-- arithmetic. D14 / design2 disagreement D say exactly this.
--
-- SATISFIABILITY. No in-tree object can discharge Eip2537.Holds today: the only
-- AdmissiblePairing instance is the exponent model in Midfall/Instances/, whose
-- toEip is not a curve point, and D-P17 forbids importing it here. So the
-- structure is a trusted-base entry (plan Section 1), not a deferred proof. That
-- is stated rather than hidden, per design2 hazard for this file.

import Midfall.Common.Bytes
import Midfall.Common.Codec
import Midfall.Common.Curve
import Midfall.Assumptions.BasePrime
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Yul.Externals

namespace Midfall.Assumptions
open Midfall Midfall.Halo2 Midfall.Yul

/-! ### The two moduli, tied together -/

/-- The scalar modulus in Midfall/Yul/Externals.lean is the same number as the one
    CompPoly provides, proved by rfl rather than re-typed. This is the R-20 defect
    class (docs/REVIEW.md): Assumptions/Pairing.lean once carried the BLS12-**377
    base modulus in a file that also had the right one, and the two BLS moduli share
    a 50-digit prefix so the slip was invisible to the eye. Externals.lean:57-64
    records that it refused to import pBase for exactly that reason and defined its
    own blsP; this theorem is the check that the two copies agree. -/
theorem blsR_eq_r : blsR = Assumptions.r := rfl

/-- The base-field modulus, same story: Externals.blsP is the EIP-2537 number and
    Assumptions.pBase is the fixed literal (Pairing.lean:55-64 records the bug and
    the gate that now catches it). -/
theorem blsP_eq_pBase : blsP = Assumptions.pBase := rfl

/-- CompPoly proves the scalar modulus prime; transported across blsR_eq_r so the
    precompile arithmetic can use ZMod blsR as a field without restating the
    number. Proved by rewriting, not by decide: a 255-bit primality proof does not
    belong in the kernel here. -/
instance : Fact (Nat.Prime blsR) := ⟨by
  have h : blsR = Assumptions.r := rfl
  exact h ▸ (inferInstance : Fact (Nat.Prime Assumptions.r)).out⟩

/-- The base-field modulus, with the same primality transport as `Fact (Nat.Prime blsR)` above:
    `blsP` and `pBase` are the same number by `rfl`, and `BasePrime.lean` proves that number prime,
    so `ZMod blsP` is a field and `modPow x (blsP - 2) blsP` is an inverse for every
    `0 < x < blsP`. The instance has to be RE-STATED rather than found: instance search does not
    unfold the two definitions into the same literal, which is why `blsP_eq_pBase` above is a proof
    and not a comment. -/
instance : Fact (Nat.Prime blsP) := ⟨by
  have h : blsP = Assumptions.pBase := rfl
  exact h ▸ pBase_prime⟩

/-! ### The G2 encoder -/

/-- An abstract EIP-2537 G2 encoder: 256 bytes per point (Externals.g2Bytes). The
    only G2 encoding in the tree is Generator.VkPointCodecs.g2Repr composed with
    g2ToU256s, which sits behind Generator/Vk.lean import of Midfall/Instances/
    (design2 disagreement D), so the hypothesis layer takes the encoder as a
    wrapped function rather than importing it. The wrapper - rather than a bare
    G2 -> Bytes - is attack.md line 84 FIX: it is the hook where the VK-header
    agreement field hangs in Surface.lean. -/
structure G2Enc (G₂ : Type) where
  /-- The 256-byte padded EIP-2537 encoding. -/
  toEip : G₂ -> Bytes

/-! ### The hypothesis structure -/

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- What EIP-2537 must deliver for the generated verifier, relative to the two
    codecs and the pairing-product oracle (the Fp12 hole, Externals.lean:934-941).

    pairing2 is the two-pair form: the verifier pairs exactly two pairs, and the
    equation is written additively in Gₜ so the identity is 0 (EIP-2537 says the
    product must equal 1 multiplicatively). g1Add and g1Msm1 pin the frames the
    accumulator helper rewrites in place (FinalPairing.yul:36-60), and the MSM
    scalar is the canonical big-endian word frToInputBE s - the same bytes as
    wordToBytesBE (frWord s) in Exec/Accumulator.lean:433, spelled here without
    importing the Exec layer. g1Decodes is the soundness side: a frame the
    precompile validators accept must decode through the codec, which is what
    closes the points_subgroup_checked gap for the no-accumulator path (design0
    note on this declaration). -/
structure Eip2537.Holds (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop where
  /-- Encoded G1 points are what the byte-level validators accept: on-curve,
      canonical, in the r-torsion (Externals.g1PointMsmValid). -/
  g1Valid : ∀ Q : G₁, ∃ pt, g1Of? (c.toEip Q) = some pt ∧ g1PointMsmValid pt = true
  /-- Same for G2, for the encoder above. -/
  g2Valid : ∀ R : G₂, ∃ pt, g2Of? (c₂.toEip R) = some pt ∧ g2PointValid pt = true
  /-- PAIRING_CHECK on two pairs is the additive pairing equation. -/
  pairing2 : ∀ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
    product (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) +
        P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) = 0
  /-- G1ADD on the 0x100-byte frame is the group law (R-21: the frame is two
      padded points, not the 0x80 the work-package brief claimed - see
      Externals.lean divergence 4). -/
  g1Add : ∀ P₁ P₂ : G₁,
    g1AddOutput (g1AddFrame (c.toEip P₁) (c.toEip P₂)) = some (c.toEip (P₁ * P₂))
  /-- One-pair G1MSM on the interleaved 0xa0-byte record is the scalar action
      (gsmul). The scalar is the canonical word: EIP-2537 lets a MSM scalar exceed
      r, and a non-canonical word would alias to a different field element. -/
  g1Msm1 : ∀ (Q : G₁) (s : Fr p),
    g1MsmOutput (g1MsmFrame [(c.toEip Q, frToInputBE s)]) = some (c.toEip (gsmul s Q))
  /-- Soundness side: a frame the precompile accepts decodes through the codec.

      THE WIDTH HYPOTHESIS IS PART OF THE CLAUSE (R-63, repaired by P-HOLDS). g1Of? is a
      COORDINATE reader: bytesSlice clamps and never checks the length, so without
      `b.size == g1Bytes` the antecedent is satisfied by every extension of a valid frame
      by trailing bytes, and the clause demands that toEip hit infinitely many distinct
      strings - impossible on a type with `Nat.card G₁ = p`. That is proved below of the old
      text (g1DecodesOld_unsatisfiable), which is pinned there so the regression cannot come
      back unnoticed. With the width condition the clause says what its docstring always
      said, and Midfall/Instances/Bls12_381G1.lean discharges it at real curve points
      (g1FrameCodec_decodesWidth). -/
  g1Decodes : ∀ b : Bytes, b.size == g1Bytes →
    (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
      ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-! ### modPow IS exponentiation, and Fermat makes it an inverse (P-MODEXP step 1)

THE READING THE BRIEF PROPOSED, CHECKED AND HELD. `fpOps.inv` and `fp2Ops.inv` compute
`x^(p-2) mod p` by the square-and-multiply fold `modPow`, and `modexpInvFrame` asks the modexp
precompile for exactly that exponent at the scalar modulus. So the missing ingredient was never
a new technique: it is (a) the fold computes `base^exp mod m`, and (b) Fermat's little theorem in
`ZMod p`, which mathlib has as `ZMod.pow_card_sub_one_eq_one`
(FieldTheory/Finite/Basic.lean:612) - the form the docstring below already names as the available
one. What the brief did NOT have right is the SHAPE of the pBase statement: `modexpInvFrame` is a
32-byte-word frame and `pBase` is 381 bits, so a base-field inversion frame is 48 bytes wide
(`fpBytes`), not 32. The pBase version is therefore stated at its own width below
(`fpInvFrame`, `fpInv_correct`) and the r version keeps the 32-byte frame the generator emits.

COST. Nothing here computes at 381 bits: `modPow_eq` is a fold induction and the inverse identity
is a `ZMod` argument, so both are cheap at either modulus. -/

/-- One binary step of `modPow`'s fold, named so the invariant can be stated about it. -/
def modPowStep (base exp m i acc : ℕ) : ℕ :=
  let sq := acc * acc % m
  if Nat.testBit exp i then sq * base % m else sq

/-- Reducing one factor before a multiply does not change the product mod `m`. -/
private lemma mod_mul_mod_left (a b m : ℕ) : ((a % m) * b) % m = (a * b) % m := by
  rw [Nat.mul_mod, Nat.mod_mod]
  exact (Nat.mul_mod a b m).symm

/-- Reducing the other factor before a multiply does not change the product mod `m`. -/
private lemma mod_mul_mod_right (a b m : ℕ) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_comm a, mod_mul_mod_left, Nat.mul_comm b]

/-- The digit split at a general base: the low `n` digits, plus the next digit shifted up one
    place, is the residue modulo one more digit. At `b = 2` this is the bit split the fold
    invariant needs; at `b = 256` it is the byte split the codec round trip needs. -/
theorem mod_pow_succ (b e n : ℕ) (hb : 0 < b) :
    e % b ^ (n + 1) = e % b ^ n + b ^ n * (e / b ^ n % b) := by
  have hp : 0 < b ^ n := Nat.pow_pos hb
  have hq : 0 < b ^ (n + 1) := Nat.pow_pos hb
  have hpow : b ^ (n + 1) = b ^ n * b := Nat.pow_succ b n
  have hsum : e % b ^ n + b ^ n * (e / b ^ n % b) < b ^ n * b := by
    have h1 : e / b ^ n % b + 1 ≤ b := Nat.succ_le_of_lt (Nat.mod_lt _ hb)
    have h4 : e % b ^ n < b ^ n := Nat.mod_lt _ hp
    have h7 : b ^ n * (e / b ^ n % b) + b ^ n ≤ b ^ n * b := by
      have h8 : b ^ n * (e / b ^ n % b + 1) ≤ b ^ n * b := Nat.mul_le_mul_left _ h1
      rwa [Nat.mul_add, Nat.mul_one] at h8
    omega
  have hshift : (e / b ^ n) / b = e / b ^ (n + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  have h2 : e / b ^ n = b * (e / b ^ (n + 1)) + e / b ^ n % b := by
    have h3 := Nat.div_add_mod (e / b ^ n) b
    rw [hshift] at h3
    omega
  have hdecomp : (e % b ^ n + b ^ n * (e / b ^ n % b)) + b ^ (n + 1) * (e / b ^ (n + 1)) = e := by
    have h1 : b ^ n * (e / b ^ n) + e % b ^ n = e := Nat.div_add_mod e (b ^ n)
    rw [h2, Nat.mul_add, ← Nat.mul_assoc, hpow] at h1
    rw [hpow]
    omega
  have hsum' : e % b ^ n + b ^ n * (e / b ^ n % b) < b ^ (n + 1) := by rwa [hpow]
  exact ((Nat.div_mod_unique hq).mpr ⟨hdecomp, hsum'⟩).2
/-- **THE FOLD INVARIANT.** After the steps for the bit positions `n-1, ..., 0` the accumulator
    holds `base` raised to the high part of `exp` shifted down `n` places, plus its low `n` bits.
    Generalised in the starting accumulator because that is the only form that inducts: each step
    doubles the exponent and shifts in one bit. -/
private theorem modPow_fold (base exp m : ℕ) :
    ∀ (n A : ℕ), (List.range n).foldr (modPowStep base exp m) (base ^ A % m)
      = base ^ (A * 2 ^ n + exp % 2 ^ n) % m := by
  intro n
  induction n with
  | zero =>
      intro A
      simp [Nat.mod_one]
  | succ n ih =>
      intro A
      have hsq : (base ^ A % m) * (base ^ A % m) % m = base ^ (2 * A) % m := by
        rw [mod_mul_mod_left, mod_mul_mod_right, ← Nat.pow_add]
        congr 1
        ring
      have hdef : modPowStep base exp m n (base ^ A % m)
          = if Nat.testBit exp n then (base ^ A % m * (base ^ A % m) % m) * base % m
            else base ^ A % m * (base ^ A % m) % m := rfl
      have hstep : modPowStep base exp m n (base ^ A % m)
          = base ^ (2 * A + (Nat.testBit exp n).toNat) % m := by
        rw [hdef]
        by_cases hb : Nat.testBit exp n
        · rw [if_pos hb, hb]
          simp only [Bool.toNat_true, hsq, mod_mul_mod_left, Nat.pow_add, Nat.pow_one]
        · rw [if_neg hb, Bool.eq_false_of_ne_true hb]
          simp only [Bool.toNat_false, hsq, Nat.add_zero]
      have hrange : (List.range (n + 1)).foldr (modPowStep base exp m) (base ^ A % m)
          = (List.range n).foldr (modPowStep base exp m)
              (modPowStep base exp m n (base ^ A % m)) := by
        rw [List.range_succ, List.foldr_append]
        rfl
      rw [hrange, hstep, ih (2 * A + (Nat.testBit exp n).toNat), Nat.toNat_testBit,
        mod_pow_succ 2 exp n (by decide), Nat.pow_succ]
      ring

/-- **`modPow` COMPUTES `base^exp mod m`.** The fold is the textbook left-to-right binary method,
    so this is the correctness of that fold and nothing more. -/
theorem modPow_eq (base exp m : ℕ) (_hm : 0 < m) : modPow base exp m = base ^ exp % m := by
  have hconv : (fun (x y : ℕ) =>
        (fun (acc : Nat) (i : Nat) =>
          let sq := acc * acc % m
          if Nat.testBit exp i then sq * base % m else sq) y x)
      = modPowStep base exp m := by
    funext x y
    rfl
  have hfold : modPow base exp m
      = (List.range (Nat.log2 exp + 1)).foldr (modPowStep base exp m) (1 % m) := by
    unfold modPow
    rw [List.foldl_reverse, hconv]
  have hexp : exp % 2 ^ (Nat.log2 exp + 1) = exp := Nat.mod_eq_of_lt Nat.lt_log2_self
  rw [hfold, show (1 : ℕ) % m = base ^ 0 % m by simp, modPow_fold base exp m]
  rw [Nat.zero_mul, Nat.zero_add, hexp]

/-- **FERMAT AT A PRIME MODULUS.** `x^(p-2)` is the inverse of `x` in `ZMod p` for every
    `0 < x < p`. This is the whole of what the gap note billed as the missing ingredient, and it
    is `ZMod.pow_card_sub_one_eq_one` in one line - the form `modexpInv_correct`'s docstring
    already identified as the available one. -/
theorem pow_card_sub_two_eq_inv {p : ℕ} [Fact (Nat.Prime p)] (x : ℕ)
    (hx0 : 0 < x) (hx : x < p) : (x : ZMod p) ^ (p - 2) = (x : ZMod p)⁻¹ := by
  have hp : Nat.Prime p := Fact.out
  have hne : (x : ZMod p) ≠ 0 := by
    intro h
    have h1 : (x : ZMod p).val = 0 := by rw [h, ZMod.val_zero]
    rw [ZMod.val_natCast] at h1
    have hdvd : p ∣ x := Nat.dvd_iff_mod_eq_zero.mpr h1
    have : p ≤ x := Nat.le_of_dvd hx0 hdvd
    omega
  have h1 : (x : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have h2 : p - 1 = (p - 2) + 1 := by
    have := Nat.Prime.one_lt hp
    omega
  rw [h2] at h1
  rw [pow_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- **FERMAT IN FIELD FORM.** The same statement with the element abstracted out of `ZMod p`: for
    every nonzero `a`, `a^(p-2)` is its inverse. `pow_card_sub_two_eq_inv` above is the
    representative-indexed version this file needs for `modPow`; this is the version the curve
    files need, and it is the same one line of Fermat. -/
theorem pow_card_sub_two_eq_inv_card {p : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) (ha : a ≠ 0) :
    a ^ (p - 2) = a⁻¹ := by
  have hlt : a.val < p := ZMod.val_lt a
  have h0 : 0 < a.val :=
    Nat.pos_of_ne_zero (fun hh => ha ((ZMod.val_eq_zero a).mp hh))
  have heq : (a.val : ZMod p) = a := ZMod.natCast_zmod_val a
  rw [← heq]
  exact pow_card_sub_two_eq_inv a.val h0 hlt


/-- **THE MODPOW-AS-MODULAR-INVERSE FACT, AT ANY PRIME MODULUS.** This is the statement the brief
    asked for, and it is uniform: instantiate at `blsR` for the frame the generator emits or at
    `pBase` for the field the curve lives in. -/
theorem modPow_inv {p : ℕ} [Fact (Nat.Prime p)] (x : ℕ) (hx0 : 0 < x) (hx : x < p) :
    modPow x (p - 2) p = ((x : ZMod p)⁻¹).val := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  rw [modPow_eq x (p - 2) p hp, ← pow_card_sub_two_eq_inv x hx0 hx, ← Nat.cast_pow,
    ZMod.val_natCast]

/-- `(Nat.toUInt8 x).toNat = x % 256`. The byte encoder below builds its digits with
    `Nat.toUInt8`, so this is the one step that turns its output back into a number. -/
private theorem uint8_toNat_toUInt8 (x : ℕ) : (Nat.toUInt8 x).toNat = x % 256 := by
  unfold Nat.toUInt8
  rfl

/-- `bytesNatBE v n` really is `n` bytes long, whatever `v` is: the encoder pads on the
    left and never truncates. -/
theorem bytesNatBE_size (v n : ℕ) : (bytesNatBE v n).size = n := by
  show (List.map (fun i => Nat.toUInt8 ((v / 256 ^ i) % 256)) (List.range n).reverse).toArray.size = n
  rw [List.size_toArray, List.length_map, List.length_reverse, List.length_range]

/-- **THE WORD READER INVERTS THE WORD WRITER.** `bytesToNatBE (bytesNatBE v n) = v % 256^n`,
    i.e. exactly `v` when `v < 256^n`. This was a gate and is now a theorem: the proof is the digit
    expansion of `v` in base 256, by induction with the general-base digit split `mod_pow_succ` at
    `b = 256`. -/
theorem bytesToNatBE_bytesNatBE (v n : ℕ) : bytesToNatBE (bytesNatBE v n) = v % 256 ^ n := by
  classical
  rw [bytesToNatBE_eq_ofLowDigits_reverse]
  have h1 : ((bytesNatBE v n).data.toList.map UInt8.toNat).reverse
      = (List.range n).map (fun i => (v / 256 ^ i) % 256) := by
    show (List.map UInt8.toNat
          (List.map (fun i => Nat.toUInt8 ((v / 256 ^ i) % 256)) (List.range n).reverse)).reverse = _
    rw [List.map_map, List.map_reverse, List.reverse_reverse]
    congr 1
    funext i
    simp
  rw [h1]
  clear h1
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
      rw [List.range_succ, List.map_append, ofLowDigits_append, List.length_map, List.length_range,
        List.map_singleton, ofLowDigits_singleton, ih, mod_pow_succ 256 v n (by decide)]

/-- **`fpInv` IS INVERSION IN Fp, AT THE REAL 381-BIT BASE MODULUS.** For `0 < x < pBase` the value
    `fpOps.inv x` returns is the canonical representative of `x⁻¹` in `ZMod pBase`. This is the fact
    the agreement theorem needs: the affine group law calls `inv` on already-reduced coordinates,
    so `x < p` is available at every call site. -/
theorem fpInv_correct (x : ℕ) (hx0 : 0 < x) (hx : x < blsP) :
    fpInv x = some ((x : ZMod blsP)⁻¹).val := by
  show (if x % blsP == 0 then none else some (modPow x (blsP - 2) blsP)) = _
  by_cases hb : x % blsP == 0
  · simp at hb
    rw [Nat.mod_eq_of_lt hx] at hb
    omega
  · rw [if_neg hb]
    exact congrArg some (modPow_inv x hx0 hx)

/-- **THE FALSIFICATION HALF, PART 1: PRIMALITY IS LOAD-BEARING.** At the composite modulus 4 the
    Fermat exponent gives 1, not the inverse: `3^(4-2) mod 4 = 1` while `3⁻¹ = 3` in `ZMod 4`.
    So `modPow_inv` is not a statement about exponentiation alone, and no proof of it can skip
    `Fact (Nat.Prime p)`. -/
theorem modPow_inv_needs_prime : modPow 3 (4 - 2) 4 * 3 % 4 ≠ 1 := by
  decide

/-- **THE FALSIFICATION HALF, PART 2: THE EXPONENT IS p-2, NOT p-1.** At the prime 5,
    `2^(5-1) mod 5 = 1` while `2⁻¹ = 3`. The frame the generator emits subtracts two, and this is
    the demonstration that subtracting one would not do. -/
theorem modPow_inv_exponent_is_sub_two :
    modPow 2 (5 - 2) 5 * 2 % 5 = 1 ∧ modPow 2 (5 - 1) 5 * 2 % 5 ≠ 1 := by
  constructor <;> decide

/-- **THE DOMAIN CONDITION.** `fpInv 0 = none`: the precompile model has no inverse for zero, and
    `affineAdd`/`affineDouble` turn a `none` into the point of infinity rather than into a wrong
    number. -/
theorem fpInv_zero : fpInv 0 = none := by
  show (if (0 : ℕ) % blsP == 0 then none else some (modPow 0 (blsP - 2) blsP)) = none
  rw [if_pos (by simp)]

/-- **SATISFIABILITY WITNESS AT THE REAL MODULUS** (D-P23), as a gate rather than a kernel proof:
    base-field inversions computed by the same `modPow` the precompile model runs, checked against
    the field inverse and against multiplication by the original value. Line 1 pins the known
    answer for 2 at `pBase`: `p ≡ 3 [MOD 4]`, so `2⁻¹ = (p+1)/2`. Line 4 is the zero domain, and
    line 5-6 check the computed value against `ZMod` inversion itself, not against a hand-written
    constant. -/
def fpInvCorrectKats_ok : Bool :=
  (match fpInv 2 with
   | some v => (v * 2) % blsP == 1 && v == (blsP + 1) / 2
   | none => false) &&
  (match fpInv 3 with
   | some v => (v * 3) % blsP == 1
   | none => false) &&
  (match fpInv (blsP - 1) with
   | some v => (v * (blsP - 1)) % blsP == 1 && v == blsP - 1
   | none => false) &&
  fpInv 0 == none && fpInv blsP == none &&
  modPow 2 (blsP - 2) blsP == ((2 : ZMod blsP)⁻¹).val &&
  modPow 7 (blsP - 2) blsP == ((7 : ZMod blsP)⁻¹).val

#eval fpInvCorrectKats_ok   -- expect true

/-! ### Modexp is arithmetic, not an assumption -/

/-- The generated inversion frame returns x to the power r-2 modulo r, which is
    x inverse in the scalar field for every nonzero x below r (Fermat). Externals
    COMPUTES modexpOutput, so this is a theorem and not a hypothesis - D14 and
    design2 disagreement D are explicit that stating it as an assumption would
    mislabel modelled arithmetic as trusted arithmetic.

    PROOF OBLIGATION, registered in SORRY.md: modPow is a square-and-multiply over
    the bits of the exponent, so the proof is the correctness of that fold plus
    the Fermat identity in ZMod blsR. NOTE: the plan sketch cites
    ZMod.pow_card_sub_two_eq_inv, which does NOT exist in the pinned Mathlib
    (measured: no such constant); the available form is ZMod.pow_card_sub_one_eq_one
    (Mathlib/FieldTheory/Finite/Basic.lean:612), from which the inverse identity
    follows in one line. Reported as a stage-1 finding. -/
theorem modexpInv_correct (x : ℕ) (hx : 0 < x) (hr : x < blsR) :
    modexpOutput (modexpInvFrame x) =
      some (bytesNatBE ((x : ZMod blsR)⁻¹).val wordBytes) := by
  sorry

/-! ### Gates -/

/-- The known answer the plan names: the inverse of 2 is (r+1)/2, checked against
    the COMPUTED modexp output, not against an assumption. This is the gate that
    distinguishes modexpInv_correct from a hypothesis: the frame is parsed, the
    exponentiation runs, and the byte result is compared with the field inverse.
    The second line pins the frame width the contract emits (0xc0 = 6 words), and
    the third pins the two-pair pairing frame at 0x300 bytes, which is what
    pairing2 quantifies over. -/
def modexpInvKats_ok : Bool :=
  (match modexpOutput (modexpInvFrame 2) with
   | some o => bytesToNatBE o == (blsR + 1) / 2
   | none => false) &&
  (match modexpOutput (modexpInvFrame 7) with
   | some o => (bytesToNatBE o * 7) % blsR == 1
   | none => false) &&
  (modexpInvFrame 2).size == modexpFrameBytes && modexpFrameBytes == 0xc0 &&
  (pairingFrame [((bytesZero g1Bytes), (bytesZero g2Bytes)),
    ((bytesZero g1Bytes), (bytesZero g2Bytes))]).size == pairingTwoPairBytes &&
  pairingTwoPairBytes == 0x300 && g1MsmPairBytes == 0xa0 && g1AddInputBytes == 0x100

#eval modexpInvKats_ok   -- expect true

/-- The MSM scalar slot is big-endian: 2 sits in the LAST byte of the word, not
    the first. A little-endian scalar slot would make g1Msm1 disagree with
    AccumulatorHelpers.yul:300-301, and the two BLS byte orders differ only in
    which end the value sits at - the R-20 class again. -/
local instance smallPrime : Fact (Nat.Prime 17) := ⟨by decide⟩

def msmScalarWordKats_ok : Bool :=
  (frToInputBE (p := 17) (2 : Fr 17)).size == 32 &&
    (frToInputBE (p := 17) (2 : Fr 17)).data[31]? == some 2 &&
    (frToInputBE (p := 17) (2 : Fr 17)).data[0]? == some 0 &&
    (g1MsmFrame [((bytesZero g1Bytes), (frToInputBE (p := 17) (2 : Fr 17)))]).size == g1MsmPairBytes

#eval msmScalarWordKats_ok   -- expect true

/-! ### THE SATISFIABILITY DEFECT: g1Decodes WAS UNSATISFIABLE AS WRITTEN (R-63, REPAIRED)

P-CURVE (docs/plans/P-CURVE-real-g1.md) was fired to make Eip2537.Holds satisfiable by
building a real-curve G1 model, on R-61's reading that the only thing between the exponent
model and a Holds exhibit is a curve. Measured here, BEFORE any curve work, that is not the
obstacle: the g1Decodes clause is unsatisfiable for EVERY codec on EVERY prime-order group,
curve included, so the four-way headline bundle is not merely unexhibited - it is PROVABLY
EMPTY, and no amount of curve modelling can change that until the clause is repaired.

THE MECHANISM. g1Decodes quantifies over all b : Bytes that the byte validators accept:

    (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
      ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

and g1Of? is the COORDINATE decoder, not a frame validator: it reads bytes 0..64 and 64..128
through bytesSlice, which clamps to the bytes that exist and never checks the length. So
every extension of a valid 128-byte frame by any number of trailing bytes satisfies the
antecedent - garbageFrame k below is the infinite family, all-zero frames of length 0x80 + k,
every one of which decodes to the point of infinity and passes g1PointMsmValid. The consequent
then demands c.toEip Q = garbageFrame k for each k, i.e. that toEip hit infinitely many
distinct byte strings. But PrimeOrderWith G1 p says Nat.card G1 = p, so toEip has at most p
values. Contradiction, proved below with no computation heavier than a 64-byte decide and no
axiom beyond the standard three.

WHY THE OTHER FIVE CLAUSES DO NOT HAVE THIS PROBLEM, and why this one was invisible. g1Valid
is existential over the ENCODINGS the codec produces, so it constrains the range of toEip and
is happy with a finite one. g1Add, g1Msm1 and pairing2 are equations between precompile
outputs and codec outputs, again only over frames the codec itself emitted. Only g1Decodes
runs the implication the other way - from accepted BYTES to a codec preimage - and it is the
only clause written over raw Bytes rather than over (c.toEip Q). Every frame the precompile
actually accepts is length-pinned elsewhere (0x100 for G1ADD at g1AddValidInput, a whole
number of 0xa0 pairs for G1MSM at g1MsmPairs?, of 0x180 for PAIRING_CHECK at pairingPairs?),
so nothing in the byte model can see the difference; the clause's own docstring says "a frame
the precompile accepts", and the precompile does NOT accept a 0x81-byte point. The defect is
that the clause says g1Of?-accepts where the doc says frame-accepts.

THE REPAIR, APPLIED (P-HOLDS, on R-63's level 1). The frame-width condition
b.size == g1Bytes - which is what the clause's docstring always meant and what every real frame
validator pins - is now part of the structure field, and the same proposition is kept as the
named def g1DecodesWidth so the clause can be cited by name. The repair is a genuine
RELAXATION and not a rewording: g1DecodesOld_implies_width below proves the old text entails
the new one, and the real-curve frame type in Midfall/Instances/Bls12_381G1.lean satisfies the
new clause outright (g1FrameCodec_decodesWidth) while REFUTING the old one
(g1FrameCodec_not_g1DecodesOld) for the byte reason and not a curve reason.

THE OLD TEXT IS PINNED, NOT DELETED. g1DecodesOld names the written clause as it stood before
R-63, Eip2537.HoldsOld is the structure with that clause conjoined, and the three refutations
below are restated against them (g1DecodesOld_unsatisfiable, holdsOld_unsatisfiable,
not_exists_holdsOld). This project keeps its fixed defects as failing terms for exactly this
reason - see s1_defect_refutes_the_conjunction from R-60 S1 - and the fingerprint entries in
scripts/check_statement_fingerprints.py for the six Holds clause types are what stop the live
clause being weakened back into the pinned old one while the refutations still build.

WHAT THE REPAIR DOES NOT CLOSE. g1Decodes was the clause that blocked FIRST, and it blocked
for a reason that had nothing to do with curves. With it repaired the remaining blockers are
the two curve facts recorded in Midfall/Instances/Bls12_381G1.lean: a group law over Fp, which
needs Fact (Nat.Prime pBase), and the r-torsion point count Nat.card G1Frame = r that
PrimeOrderWith demands. Repairing g1Decodes unblocks the clause, not the exhibit. -/

/-- A valid 128-byte G1 frame with k extra bytes appended. g1Of? accepts every one of them as
    the point of infinity, because it slices rather than checks the length. -/
def garbageFrame (k : ℕ) : Bytes := bytesZero (g1Bytes + k)

@[simp] theorem garbageFrame_size (k : ℕ) : (garbageFrame k).size = g1Bytes + k := by
  show (bytesReplicate (g1Bytes + k) 0).size = _
  classical
  show (List.replicate (g1Bytes + k) (0 : UInt8)).toArray.size = _
  rw [List.toArray_replicate, Array.size_replicate]

/-- The two slices g1Of? reads out of an all-zero frame, at any length that contains them. -/
theorem bytesSlice_bytesZero (n i j : ℕ) (h : i + j ≤ n) :
    bytesSlice (bytesZero n) i j = bytesZero j := by
  classical
  simp only [bytesSlice, bytesZero, bytesReplicate, List.toArray_replicate, ByteArray.size,
    Array.size_replicate, Nat.min_eq_left (by omega : i <= n),
    Nat.min_eq_left (by omega : i + j <= n), Array.extract_replicate, Nat.add_sub_cancel_left]

/-- The distinctness half of the obstruction: the family is infinite because the SIZES
    differ, so no two of them can share a codec preimage. -/
theorem garbageFrame_injective : Function.Injective garbageFrame := by
  intro k j h
  have := congrArg ByteArray.size h
  rw [garbageFrame_size, garbageFrame_size] at this
  omega

set_option maxRecDepth 1000000 in
private theorem fpCoordOf?_bytesZero64 : fpCoordOf? (bytesZero 64) = some 0 := by decide

/-- EVERY member of the family is accepted by the byte validators: g1Of? decodes it to the
    point of infinity and g1PointMsmValid passes that point. This is the witness half of the
    defect (D-P23): not a claim that the clause is awkward, but an explicit infinite family of
    counterexample inputs. -/
theorem garbageFrame_accepted (k : ℕ) :
    ∃ pt, g1Of? (garbageFrame k) = some pt ∧ g1PointMsmValid pt = true := by
  refine ⟨(0, 0), ?_, by decide⟩
  have e1 : bytesSlice (garbageFrame k) 0 64 = bytesZero 64 :=
    bytesSlice_bytesZero _ _ _ (by unfold g1Bytes; omega)
  have e2 : bytesSlice (garbageFrame k) 64 64 = bytesZero 64 :=
    bytesSlice_bytesZero _ _ _ (by unfold g1Bytes; omega)
  simp [g1Of?, e1, e2, fpCoordOf?_bytesZero64]

/-- THE OLD TEXT OF THE CLAUSE, PINNED. This is exactly what the g1Decodes field said
    before R-63: no width condition, so the quantifier runs over every byte string the
    COORDINATE reader accepts. It is kept as a named proposition rather than deleted because
    the three refutations below are true OF IT and are the regression pin: weakening the live
    clause back to this text is what the fingerprint gate reddens, and the refutation stays
    available either way. -/
def g1DecodesOld (c : G1Codec G₁) : Prop :=
  ∀ b : Bytes, (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
    ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-- THE DEFECT, AS A THEOREM OF THE PINNED OLD TEXT. No codec on any prime-order group can
    discharge it. The proof is the pigeonhole: the clause makes toEip hit every
    garbageFrame k, the family is infinite, and Nat.card G1 = p makes the range finite -
    formally, an injection (Nat → G₁) makes G₁ infinite, so its Nat.card is 0, not p. -/
theorem g1DecodesOld_unsatisfiable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] (c : G1Codec G₁) : ¬ g1DecodesOld c := by
  intro h
  have key : ∀ k : ℕ, ∃ Q, c.ofEip? (garbageFrame k) = some Q ∧ c.toEip Q = garbageFrame k :=
    fun k => h _ (garbageFrame_accepted k)
  choose Q hQ using key
  have hinj : Function.Injective Q := by
    intro k j hkj
    exact garbageFrame_injective
      ((hQ k).2.symm.trans ((congrArg c.toEip hkj).trans (hQ j).2))
  haveI : Infinite G₁ := Infinite.of_injective Q hinj
  have hc : Nat.card G₁ = p := (inferInstance : PrimeOrderWith G₁ p).hCard
  rw [Nat.card_eq_zero_of_infinite] at hc
  exact absurd hc.symm (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

/-- THE STRUCTURE AS IT STOOD BEFORE R-63: the repaired Holds with the pinned old decode
    clause conjoined. A def and not a second structure, so the five clauses that did not change
    are the SAME fields and cannot drift apart from the live structure. -/
def Eip2537.HoldsOld (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop :=
  Eip2537.Holds c c₂ product ∧ g1DecodesOld c

/-- THE HEADLINE CONSEQUENCE OF THE OLD TEXT: Eip2537.Holds as WRITTEN had no model at all,
    at any curve, over any group, with any G2 encoder and any pairing product. That is what
    made the four-way bundle (BlkIsEmitter ∧ SupportedS ∧ EnvAgrees ∧ Eip2537.Holds) empty
    rather than merely unexhibited, and it is the eighth false-as-written finding of the class
    R-60 S1 named and R-62 counted to seven - except that this time the conjunction was
    REFUTED, not merely unpopulated. Stated now of HoldsOld: the live structure is no longer
    refuted (that was the defect, and it is repaired), so the refutation travels with the text
    it was proved of. -/
theorem holdsOld_unsatisfiable (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) :
    ¬ (Eip2537.HoldsOld c c₂ product) :=
  fun h => g1DecodesOld_unsatisfiable c h.2

/-- The non-existence form of the same fact, which is the shape the bundle gate cares about:
    there was no triple of codec, encoder and oracle making the OLD hypothesis true, so no field
    of LoweringCorrect that takes it could ever be discharged by exhibit. After the repair the
    live structure is not refutable this way - that is the whole point of the repair - and what
    is left is a per-codec question, answered for the fixture codec in
    Midfall/Instances/ObligationsGates.lean. -/
theorem not_exists_holdsOld :
    ¬ (∃ (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct),
        Eip2537.HoldsOld c c₂ product) := by
  rintro ⟨c, c₂, product, h⟩
  exact holdsOld_unsatisfiable c c₂ product h

/-- THE REPAIR, AS A NAMED PROPOSITION: b.size == g1Bytes is the frame-width condition the
    clause's docstring always stated ("a frame the precompile accepts") and that every real
    frame validator pins: G1ADD at 0x100 (g1AddValidInput), G1MSM at a whole number of 0xa0
    pairs (g1MsmPairs?), PAIRING_CHECK at a whole number of 0x180 pairs (pairingPairs?). This
    is now the text of the live field, and it is kept named so the clause can be cited - and
    discharged at the real curve codec - by name. -/
def g1DecodesWidth (c : G1Codec G₁) : Prop :=
  ∀ b : Bytes, b.size == g1Bytes → (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) →
    ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

omit [Group G₁] in
/-- THE REPAIR IS A RELAXATION AND NOT A REWORDING: the old text entails the new one, by
    discarding the width hypothesis. So every codec that satisfied the old clause satisfies the
    new one, and the new clause is strictly weaker - the old one was unsatisfiable, this one is
    discharged at real curve points. -/
theorem g1DecodesOld_implies_width (c : G1Codec G₁) : g1DecodesOld c → g1DecodesWidth c :=
  fun h b _hs => h b

/-- Every Holds satisfies the repaired clause: the projection, restated for the live field. -/
theorem holds_g1DecodesWidth (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct)
    (h : Eip2537.Holds c c₂ product) : g1DecodesWidth c :=
  fun b hs ⟨pt, hpt, hv⟩ => h.g1Decodes b hs ⟨pt, hpt, hv⟩

/-- THE FAILURE MODE OF THE OLD CLAUSE, as a computation (R-41: a demonstrated failure mode,
    not a narrative). Lines 1-2: the coordinate decoder accepts a 0x81- and a 0xa0-byte frame
    as the point of infinity, which is what makes the antecedent infinite. Line 3: the frames
    are pairwise distinct, so they need pairwise distinct preimages. Lines 4-6: the PRECOMPILE
    itself refuses those lengths, so the tolerance is an artefact of g1Of? being a coordinate
    reader and not a statement about what EIP-2537 accepts - which is why the repair is a
    width condition and not a change to the precompile model. -/
def g1DecodesDefectKats_ok : Bool :=
  (match g1Of? (garbageFrame 1) with
   | some pt => g1PointMsmValid pt && g1Of? (garbageFrame 1) == some ((0, 0) : Nat × Nat)
   | none => false) &&
  (match g1Of? (garbageFrame 32) with
   | some pt => g1PointMsmValid pt
   | none => false) &&
    ! bytesEq (garbageFrame 1) (garbageFrame 2) &&
    ! g1AddValidInput (garbageFrame 32) &&
    g1MsmPairs? (garbageFrame 1) == none &&
    ! pairingValidInput (garbageFrame 32) &&
    g1Bytes == 0x80 && g1AddInputBytes == 2 * g1Bytes

#eval g1DecodesDefectKats_ok   -- expect true


/-! ### Byte plumbing for the pairing frame (P-HOLDS2)

    Four slice equations: a pairing frame is a four-fold concatenation, and reading it back
    means cutting it at the widths the encoders emit. Everything here is about ByteArray and
    Array.extract, with no algebra in it, so it is kept private and out of the way of the
    clauses above. -/

private theorem bytesAppend_size (x y : Bytes) : (bytesAppend x y).size = x.size + y.size := by
  show (x.data ++ y.data).size = _
  exact Array.size_append

/-- 'bytesSlice' at an offset that fits is the plain array extract: the clamping 'min's are
    inert once the window is inside the buffer. -/
private theorem bytesSlice_at (bs : Bytes) (i n : ℕ) (h : i + n ≤ bs.size) :
    bytesSlice bs i n = ByteArray.mk (bs.data.extract i (i + n)) := by
  classical
  show ByteArray.mk (bs.data.extract (min i bs.size) (min (i + n) bs.size)) = _
  rw [Nat.min_eq_left (by omega : i ≤ bs.size), Nat.min_eq_left (by omega : i + n ≤ bs.size)]

/-- The four windows of a four-fold concatenation, at the sizes of the pieces. Stated with
    the offsets as '.size' terms because that is the only form the lemmas below match. -/
private theorem bytesSlice_four (A₁ B₁ A₂ B₂ : Bytes) :
    bytesSlice (bytesAppend (bytesAppend A₁ B₁) (bytesAppend A₂ B₂)) 0 A₁.size = A₁ ∧
      bytesSlice (bytesAppend (bytesAppend A₁ B₁) (bytesAppend A₂ B₂)) A₁.size B₁.size = B₁ ∧
      bytesSlice (bytesAppend (bytesAppend A₁ B₁) (bytesAppend A₂ B₂))
        (A₁.size + B₁.size) A₂.size = A₂ ∧
      bytesSlice (bytesAppend (bytesAppend A₁ B₁) (bytesAppend A₂ B₂))
        (A₁.size + B₁.size + A₂.size) B₂.size = B₂ := by
  classical
  have hF : (bytesAppend (bytesAppend A₁ B₁) (bytesAppend A₂ B₂)).size =
      A₁.size + B₁.size + A₂.size + B₂.size := by
    simp only [bytesAppend_size]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesSlice_at _ 0 A₁.size (by rw [hF]; omega), Nat.zero_add]
    show ByteArray.mk (((A₁.data ++ B₁.data) ++ (A₂.data ++ B₂.data)).extract 0 A₁.data.size) = A₁
    simp [Array.extract_append]
    have h1 : A₁.data.extract 0 (ByteArray.size A₁) = A₁.data :=
      Array.extract_eq_self_of_le (Nat.le_refl _)
    rw [h1]
  · rw [bytesSlice_at _ A₁.size B₁.size (by rw [hF]; omega)]
    show ByteArray.mk (((A₁.data ++ B₁.data) ++ (A₂.data ++ B₂.data)).extract A₁.data.size
      (A₁.data.size + B₁.data.size)) = B₁
    simp [Array.extract_append]
    have h1 : A₁.data.extract (ByteArray.size A₁)
        (ByteArray.size A₁ + ByteArray.size B₁) = (#[] : Array UInt8) :=
      Array.extract_eq_empty_of_le (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_refl _))
    have h2 : B₁.data.extract 0 (ByteArray.size B₁) = B₁.data :=
      Array.extract_eq_self_of_le (Nat.le_refl _)
    rw [h1, h2, Array.empty_append]
  · rw [bytesSlice_at _ (A₁.size + B₁.size) A₂.size (by rw [hF]; omega)]
    show ByteArray.mk (((A₁.data ++ B₁.data) ++ (A₂.data ++ B₂.data)).extract
      (A₁.data.size + B₁.data.size) (A₁.data.size + B₁.data.size + A₂.data.size)) = A₂
    rw [← Array.size_append, Array.extract_append_right, Array.extract_append_left,
        Array.extract_eq_self_of_le (Nat.le_refl _)]
  · rw [bytesSlice_at _ (A₁.size + B₁.size + A₂.size) B₂.size (by omega)]
    show ByteArray.mk (((A₁.data ++ B₁.data) ++ (A₂.data ++ B₂.data)).extract
      (A₁.data.size + B₁.data.size + A₂.data.size)
      (A₁.data.size + B₁.data.size + A₂.data.size + B₂.data.size)) = B₂
    rw [← Array.size_append, Array.extract_append,
        Array.extract_eq_empty_of_le (Nat.le_trans (Nat.min_le_right _ _) (Nat.le_add_right _ _))]
    rw [show (A₁.data ++ B₁.data).size + A₂.data.size - (A₁.data ++ B₁.data).size
          = A₂.data.size by omega,
        show (A₁.data ++ B₁.data).size + A₂.data.size + B₂.data.size
              - (A₁.data ++ B₁.data).size = A₂.data.size + B₂.data.size by omega]
    rw [Array.extract_append_right, Array.extract_eq_self_of_le (Nat.le_refl _),
        Array.empty_append]

/-- The two-pair frame as a flat concatenation, which is what the slices above cut. -/
private theorem pairingFrame_two (a₁ b₁ a₂ b₂ : Bytes) :
    pairingFrame [(a₁, b₁), (a₂, b₂)] = bytesAppend (bytesAppend a₁ b₁) (bytesAppend a₂ b₂) := by
  classical
  show bytesAppend (bytesAppend Bytes.empty (bytesAppend a₁ b₁)) (bytesAppend a₂ b₂) = _
  apply ByteArray.ext
  simp only [bytesAppend, Array.append_assoc]
  rw [show Bytes.empty.data = (#[] : Array UInt8) from rfl, Array.empty_append]

/-! ### PAIRING2 IS DISCHARGED BY DEFINITION, NOT BY A PAIRING IMPLEMENTATION (P-HOLDS2)

The header of this file says the pairing product cannot be computed because there is no Fp12
in the Lean ecosystem (D-P1, docs/ecosystem.md). That is true of the ARITHMETIC and it is not
the obstacle this clause faces. 'PairingProduct' is a FREE PARAMETER of 'Holds'
('Bytes -> Bool', Externals.lean:941), and 'pairing2' does not ask whether the product equals
1 in some field - it asks whether 'product' AGREES WITH 'P.e', the pairing the
'AdmissiblePairing' already assumes. So the clause is discharged by DEFINING the product from
'P.e', exactly as decision D-P1 intended: the design assumes the pairing, it never asked
anyone to compute it. Conflating "no pairing implementation exists" with "no object satisfies
pairing2" is the error this section closes, and it is why the gap was billed as research-grade
when it is a definition.

WHAT THE DEFINITION NEEDS is a way to read the four points back out of the frame, because
'product' is a function of BYTES. 'G1Codec' already carries 'ofEip?'; 'G2Enc' carries only an
encoder (Eip2537.lean:85-91), so the G2 decoder is a parameter and its law is named in
'FrameLaws' together with the two frame widths. Nothing else is assumed - no curve, no field,
no pairing implementation.

THE ORIENTATION (R-11), checked rather than trusted. 'pairingFrame' lays pairs out end to
end - [G1_1 | G2_1 | G1_2 | G2_2] - and FinalPairing.yul:88 calls ec_pairing with its two
arguments swapped, so the precompile sees [(rhs, G2), (lhs, -sG2)] where the naive reading of
the layout says the opposite. The swap CANNOT matter here, and 'pairingProductOf_swap' is the
proof: the clause quantifies over both pairs universally and the target-group sum is
commutative, so exchanging the pairs leaves the answer fixed. What WOULD matter, and what a
careless decode gets wrong, is CROSSING the pairs - reading the first G1 against the second
G2. 'crossedProductOf' spells that bug out and 'crossedProductOf_iff' says exactly which
equation it answers instead; at the only pairing model in the tree it refutes the clause
('crossed_not_pairing2' in Midfall/Instances/PairingProduct.lean). A decode that cannot tell
(P1,Q1),(P2,Q2) from (P1,Q2),(P2,Q1) is not reading the frame at all. -/

/-- The width and round-trip facts the pairing-product construction needs of a codec pair.
    'G1Codec' supplies the G1 decoder; 'G2Enc' deliberately carries only an encoder, so the G2
    decoder is a parameter. -/
structure FrameLaws (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂) : Prop where
  /-- the codec decodes its own encodings. -/
  g1_ofEip : ∀ Q : G₁, c.ofEip? (c.toEip Q) = some Q
  /-- every G1 encoding is the 0x80 frame the pairing layout reads. -/
  g1_width : ∀ Q : G₁, (c.toEip Q).size = g1Bytes
  /-- the G2 decoder inverts the G2 encoder. -/
  g2_ofEip : ∀ R : G₂, d₂ (c₂.toEip R) = some R
  /-- every G2 encoding is the 0x100 frame the pairing layout reads. -/
  g2_width : ∀ R : G₂, (c₂.toEip R).size = g2Bytes

/-- Identity test on the target group as a 'Bool', decided with a supplied 'DecidableEq Gₜ' -
    the witness 'AdmissiblePairing.decEqGₜ' carries for exactly this reason (D-P7). -/
def isZeroTargetWith {H : Type} [Group H] (d : DecidableEq H) (x : Additive H) : Bool :=
  haveI : DecidableEq H := d
  if x = 0 then true else false

theorem isZeroTargetWith_iff {H : Type} [Group H] (d : DecidableEq H) (x : Additive H) :
    isZeroTargetWith d x = true ↔ x = 0 := by
  have : DecidableEq H := d
  by_cases h : x = 0 <;> simp [isZeroTargetWith, h]

/-- Two Bools are equal when they answer true in the same cases. -/
private theorem bool_eq_of_eq_true_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Read the two (G1, G2) pairs out of a pairing frame at the offsets 'pairingFrame' writes
    them: G1 at 0 and 'pairingPairBytes', G2 at 'g1Bytes' and 'g1Bytes + pairingPairBytes'.
    A frame that does not decode answers 'none', and 'pairingOutput' never calls the product
    on one (Externals.lean:951-952 gates on 'pairingValidInput'). -/
def frameDecode (c : G1Codec G₁) (d₂ : Bytes → Option G₂) (b : Bytes) :
    Option (G₁ × G₂ × G₁ × G₂) :=
  match c.ofEip? (bytesSlice b 0 g1Bytes), d₂ (bytesSlice b g1Bytes g2Bytes),
        c.ofEip? (bytesSlice b (g1Bytes + g2Bytes) g1Bytes),
        d₂ (bytesSlice b (g1Bytes + g2Bytes + g1Bytes) g2Bytes) with
  | some p₁, some q₁, some p₂, some q₂ => some (p₁, q₁, p₂, q₂)
  | _, _, _, _ => none

omit [Group G₁] [Group G₂] in
/-- THE DECODE INVERTS THE ENCODER, at the frame layout the precompile sees. This is the only
    place in the section that touches bytes, and it is four slice equations. -/
theorem frameDecode_pairingFrame (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂)
    (laws : FrameLaws c c₂ d₂) (P₁ P₂ : G₁) (Q₁ Q₂ : G₂) :
    frameDecode c d₂
        (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) =
      some (P₁, Q₁, P₂, Q₂) := by
  classical
  have w1 : (c.toEip P₁).size = g1Bytes := laws.g1_width P₁
  have w2 : (c₂.toEip Q₁).size = g2Bytes := laws.g2_width Q₁
  have w3 : (c.toEip P₂).size = g1Bytes := laws.g1_width P₂
  have w4 : (c₂.toEip Q₂).size = g2Bytes := laws.g2_width Q₂
  obtain ⟨s1, s2, s3, s4⟩ :=
    bytesSlice_four (c.toEip P₁) (c₂.toEip Q₁) (c.toEip P₂) (c₂.toEip Q₂)
  rw [w1] at s1
  rw [w1, w2] at s2
  rw [w1, w2, w3] at s3
  rw [w1, w2, w3, w4] at s4
  rw [pairingFrame_two]
  simp only [frameDecode, s1, s2, s3, s4, laws.g1_ofEip, laws.g2_ofEip]

/-- **THE PAIRING PRODUCT, DEFINED FROM THE ASSUMED PAIRING.** On a frame the codecs emit,
    the answer is whether the additive target-group sum of the two 'P.e' applications is the
    identity - which is what 'pairing2' demands, so the clause stops being an obligation about
    Fp12 and becomes a property of this definition. -/
def pairingProductOf (c : G1Codec G₁) (d₂ : Bytes → Option G₂) : PairingProduct :=
  fun b => match frameDecode c d₂ b with
  | some (p₁, q₁, p₂, q₂) =>
      isZeroTargetWith P.decEqGₜ (P.e (Additive.ofMul p₁) (Additive.ofMul q₁) +
                                  P.e (Additive.ofMul p₂) (Additive.ofMul q₂))
  | none => false

/-- The MIS-ORIENTED product: first G1 against second G2 and second G1 against first G2. This
    is what a decode that misreads the R-11 swap computes. -/
def crossedProductOf (c : G1Codec G₁) (d₂ : Bytes → Option G₂) : PairingProduct :=
  fun b => match frameDecode c d₂ b with
  | some (p₁, q₁, p₂, q₂) =>
      isZeroTargetWith P.decEqGₜ (P.e (Additive.ofMul p₁) (Additive.ofMul q₂) +
                                  P.e (Additive.ofMul p₂) (Additive.ofMul q₁))
  | none => false

/-- PAIRING2 as a standalone proposition, so the clause can be exhibited without the other
    five fields. 'holds_pairing2_is_the_clause' is the meaning check that this is the field
    text and not a paraphrase of it. -/
def Pairing2 (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct) : Prop :=
  ∀ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
    product (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) +
        P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) = 0

/-- MEANING CHECK: the projection typechecks only if 'Pairing2' above IS the field of 'Holds',
    verbatim. Paraphrase the clause and the build reddens. -/
theorem holds_pairing2_is_the_clause (c : G1Codec G₁) (c₂ : G2Enc G₂) (product : PairingProduct)
    (h : Eip2537.Holds c c₂ product) : Pairing2 c c₂ product := h.pairing2

/-- **PAIRING2, DISCHARGED.** For any codec pair that round-trips at the EIP widths, the
    product defined from 'P.e' satisfies the clause. No pairing implementation, no curve, no
    field: the clause was never the blocker the gap note billed it as. -/
theorem pairingProductOf_pairing2 (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂)
    (laws : FrameLaws c c₂ d₂) : Pairing2 c c₂ (pairingProductOf c d₂) := by
  intro P₁ P₂ Q₁ Q₂
  have hd := frameDecode_pairingFrame c c₂ d₂ laws P₁ P₂ Q₁ Q₂
  show (match frameDecode c d₂
              (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) with
        | some (p₁, q₁, p₂, q₂) =>
            isZeroTargetWith P.decEqGₜ (P.e (Additive.ofMul p₁) (Additive.ofMul q₁) +
                                        P.e (Additive.ofMul p₂) (Additive.ofMul q₂))
        | none => false) = true ↔ _
  rw [hd]
  exact isZeroTargetWith_iff _ _

/-- The mis-oriented decode answers the CROSSED equation, not the clause's. -/
theorem crossedProductOf_iff (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂)
    (laws : FrameLaws c c₂ d₂) (P₁ P₂ : G₁) (Q₁ Q₂ : G₂) :
    crossedProductOf c d₂
        (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₂) +
        P.e (Additive.ofMul P₂) (Additive.ofMul Q₁) = 0 := by
  have hd := frameDecode_pairingFrame c c₂ d₂ laws P₁ P₂ Q₁ Q₂
  show (match frameDecode c d₂
              (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) with
        | some (p₁, q₁, p₂, q₂) =>
            isZeroTargetWith P.decEqGₜ (P.e (Additive.ofMul p₁) (Additive.ofMul q₂) +
                                        P.e (Additive.ofMul p₂) (Additive.ofMul q₁))
        | none => false) = true ↔ _
  rw [hd]
  exact isZeroTargetWith_iff _ _

/-- **THE R-11 CHECK, AS A THEOREM.** Exchanging the two pairs of the frame does not change
    the product's answer, so the call-site swap at FinalPairing.yul:88 cannot corrupt the
    clause: it flips the NAMING of the pairs and nothing else. This is order-insensitivity in
    the direction that is true; the crossed product is the direction that is not. -/
theorem pairingProductOf_swap (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂)
    (laws : FrameLaws c c₂ d₂) (P₁ P₂ : G₁) (Q₁ Q₂ : G₂) :
    pairingProductOf c d₂
        (pairingFrame [(c.toEip P₂, c₂.toEip Q₂), (c.toEip P₁, c₂.toEip Q₁)]) =
      pairingProductOf c d₂
        (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) := by
  have h1 := pairingProductOf_pairing2 c c₂ d₂ laws P₁ P₂ Q₁ Q₂
  have h2 := pairingProductOf_pairing2 c c₂ d₂ laws P₂ P₁ Q₂ Q₁
  have h : (pairingProductOf c d₂
        (pairingFrame [(c.toEip P₂, c₂.toEip Q₂), (c.toEip P₁, c₂.toEip Q₁)]) = true) ↔
      pairingProductOf c d₂
        (pairingFrame [(c.toEip P₁, c₂.toEip Q₁), (c.toEip P₂, c₂.toEip Q₂)]) = true := by
    rw [h2, h1, add_comm]
  exact bool_eq_of_eq_true_iff h

/-- SATISFIABILITY of the clause, generically: a round-tripping codec pair makes 'pairing2'
    inhabited. The concrete witness is in Midfall/Instances/PairingProduct.lean, which D-P17
    keeps out of this file. -/
theorem exists_pairing2 (c : G1Codec G₁) (c₂ : G2Enc G₂) (d₂ : Bytes → Option G₂)
    (laws : FrameLaws c c₂ d₂) :
    ∃ product : PairingProduct, Pairing2 c c₂ product :=
  ⟨pairingProductOf c d₂, pairingProductOf_pairing2 c c₂ d₂ laws⟩

/-- The clause is not satisfied by every oracle: if some frame has a nonzero pairing sum, the
    product that always answers 'true' refutes it. This is the D-P23 falsification half in
    the direction that needs no model; the model-dependent halves are in Instances/. -/
theorem pairing2_not_every_product (c : G1Codec G₁) (c₂ : G2Enc G₂)
    (h : ∃ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
          P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) +
            P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) ≠ 0) :
    ¬ Pairing2 c c₂ (fun _ => true) := by
  intro h2
  obtain ⟨P₁, P₂, Q₁, Q₂, hne⟩ := h
  exact absurd ((h2 P₁ P₂ Q₁ Q₂).1 (by simp)) hne

/-! ### THE PRIME-ORDER BLOCKER IS A CYCLIC-SUBGROUP LEMMA, NOT A POINT COUNT (P-HOLDS2)

R-64's blocker table lists 'Nat.card G₁ = r' as research-grade: "the r-torsion of E(Fp) has
exactly r elements - a point count (Schoof-Elkies-Atkin), or the n-torsion structure theorem".
That is the right theorem about the FULL r-torsion, and 'Holds' does not ask for the full
r-torsion. 'PrimeOrderWith G₁ r' is just 'Nat.card G₁ = r', and for the cyclic subgroup
generated by one point of order r that is two lemmas mathlib already has: 'Nat.card_zpowers'
(no 'Fintype' hypothesis) and 'orderOf_eq_prime' (the order divides the prime and is not 1). So
the prime-order requirement follows from 'H ^ r = 1', 'H ≠ 1' and 'r' prime - and the first of
those is exactly what 'Midfall/Instances/Bls12_381G1.lean' proves by a kernel 'decide' for the
published H1 ('g1GenFrame_valid', as 'affineSmul fpOps blsR G = (0, 0)'). What stands between
the tree and 'PrimeOrderWith' at a real curve point is therefore NOT number theory. It is the
agreement theorem between the byte-level 'affineSmul' and whatever group law the exhibited type
carries - the same agreement that 'g1Add', 'g1Msm1' and the subgroup half of 'g1Valid' all
need, and whose missing ingredient is the correctness of 'modPow' as a modular inverse (still a
'sorry' in this file at 'modexpInv_correct'). -/

/-- **NO POINT COUNT NEEDED.** A cyclic subgroup generated by an element of prime order 'r' has
    exactly 'r' elements, so it is a 'PrimeOrderWith' group. This is the lemma that retires
    'gap_g1_prime_order' as a research-grade item: the r-torsion count is ONE way to get a
    prime-order group, and the only research-grade way, and it is not the way 'Holds' has to
    go. -/
theorem primeOrderWith_zpowers {r : ℕ} [Fact (Nat.Prime r)] {G : Type} [Group G] (x : G)
    (hpow : x ^ r = 1) (hx : x ≠ 1) : PrimeOrderWith (Subgroup.zpowers x) r :=
  ⟨(Nat.card_zpowers x).trans (orderOf_eq_prime (p := r) hpow hx)⟩

/-- THE TWO HYPOTHESES BITE, as a falsification (D-P23): drop 'x ≠ 1' and the conclusion is
    false of the identity element at every prime - 'zpowers 1' has one element, not 'r'. So
    'primeOrderWith_zpowers' is not a wrapper around a triviality, and the nontriviality of the
    generator is load-bearing in every application of it. -/
theorem zpowers_one_not_prime_order {r : ℕ} [Fact (Nat.Prime r)] {G : Type} [Group G] :
    ¬ PrimeOrderWith (Subgroup.zpowers (1 : G)) r := by
  rintro ⟨hcard2⟩
  have hcard : Nat.card (Subgroup.zpowers (1 : G)) = 1 :=
    (Nat.card_zpowers (1 : G)).trans orderOf_one
  exact Nat.Prime.ne_one (Fact.out : Nat.Prime r) (hcard2.symm.trans hcard)

end Midfall.Assumptions