-- |
-- Midfall.Instances.PairingProduct
--
-- P-HOLDS2 step 1 (docs/plans/P-HOLDS2.md): the 'pairing2' clause of
-- 'Midfall.Assumptions.Eip2537.Holds' EXHIBITED, at the only 'AdmissiblePairing' model in the
-- tree, with the product DEFINED from 'P.e' rather than assumed.
--
-- WHY THIS FILE EXISTS AND WHAT IT SETTLES. 'PairingProduct' is 'Bytes -> Bool'
-- (Externals.lean:941) and is a free parameter of 'Holds'; 'pairing2' asks only that the
-- parameter agree with 'P.e', the pairing the 'AdmissiblePairing' already assumes. So the
-- clause needs no BLS12-381 pairing, no Fp12, and no new hypothesis: the definition is in
-- Assumptions/Eip2537.lean ('pairingProductOf') and this file supplies the codecs it needs and
-- the D-P23 halves. The gap note blamed "no pairing implementation exists in Lean" for this
-- clause; that premise was half-wrong - true of the arithmetic, irrelevant to the clause - and
-- the wrong half is what made the item look research-grade.
--
-- WHY IN Instances/. The witness runs on 'Midfall.Instances.ExponentModel', the only model of
-- 'AdmissiblePairing' in the tree (R-28), and D-P17 keeps a concrete model out of any
-- theorem-bearing file. The STATEMENTS ('FrameLaws', 'Pairing2', 'pairingProductOf',
-- 'crossedProductOf', 'pairingProductOf_pairing2', 'pairingProductOf_swap', 'exists_pairing2',
-- 'pairing2_not_every_product') are all in Assumptions/ and portable; only the instantiation
-- is here.
--
-- THE MODEL, AND WHAT IT DOES AND DOES NOT SHOW. G1 = G2 = Gt = Multiplicative (ZMod 17) with
-- 'e x y' the product of exponents: a genuine bilinear, generator-nondegenerate pairing on
-- prime-order groups, so 'pairing2' is exhibited against a real 'AdmissiblePairing' rather
-- than a vacuity. It is the EXPONENT model, not a curve, and it says nothing about BLS12-381
-- (ExponentModel header notes 1 and 2). The point of the exhibit is the clause, not the curve.
--
-- D-P23, BOTH HALVES, AS THEOREMS (not only KAT conjuncts).
--   * satisfiability: 'pairing2_exhibited' (the clause has an inhabitant) and
--     'pairing2_holds_for_the_defined_product' (the inhabitant is the definition from 'P.e').
--   * falsification: 'constantTrue_not_pairing2' and 'constantFalse_not_pairing2' - the clause
--     refutes BOTH constant oracles, so it constrains 'product' rather than leaving it free -
--     and 'crossed_not_pairing2', which refutes the MIS-ORIENTED decode, the R-11 failure
--     mode. 'pairingProductOf_swap' (Assumptions/) is the positive orientation fact: exchanging
--     the two pairs of the frame leaves the answer fixed, so the call-site swap at
--     FinalPairing.yul:88 cannot corrupt the clause. The crossed product is the direction that
--     WOULD corrupt it, and it is refuted here rather than commented about.
--   * 'pairingProductKats_ok' computes all of it on real 0x300-byte frames.

import Midfall.Assumptions.Eip2537
import Midfall.Assumptions.Codec
import Midfall.Instances.ExponentModel

namespace Midfall.Instances.PairingProduct
open Midfall Midfall.Yul Midfall.Assumptions Midfall.Instances

local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The pairing model this exhibit runs on: the exponent model at 17 (ExponentModel.lean:247).
    An abbrev so that its fields reduce at the use sites. -/
abbrev P17 : AdmissiblePairing (Exp 17) (Exp 17) (Exp 17) := expAdmissible (p := 17)

/-- The G1 codec of the model, pinned at 17 so the class parameters are determined. -/
def c1 : G1Codec (Exp 17) := expG1Codec (p := 17)

/-- A G2 encoder for the model: the exponent in the 0x100 EIP-2537 frame. 'G2Enc' carries only
    an encoder (Eip2537.lean:92-94), which is exactly why 'FrameLaws' takes the G2 decoder as a
    parameter instead of reading it off the encoder. -/
def c2 : G2Enc (Exp 17) where
  toEip R := natToBytesBE R.toAdd.val g2Bytes

/-- The matching G2 decoder. -/
def d2 : Bytes → Option (Exp 17) :=
  fun b => if b.size == g2Bytes then some (Multiplicative.ofAdd (Nat.cast (bytesToNatBE b))) else none

set_option maxRecDepth 100000 in
private theorem natToBytesBE_size (n len : Nat) : (natToBytesBE n len).size = len := by
  show ((natToBytesLowFirst n len).data.toList.reverse.toArray).size = len
  simp [List.length_reverse, Midfall.Assumptions.natToBytesLowFirst_size]

private theorem pow256_ge_17 {len : Nat} (h : 1 ≤ len) : 17 ≤ 256 ^ len :=
  Nat.le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)

private theorem bytesToNatBE_natToBytesBE_small {n len : Nat} (hn : n < 17) (hlen : 1 ≤ len) :
    bytesToNatBE (natToBytesBE n len) = n := by
  rw [bytesToNatBE_natToBytesBE,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (pow256_ge_17 hlen))]

private theorem cast_val_eq {x : ZMod 17} : ((x.val : ℕ) : ZMod 17) = x := by
  apply ZMod.val_injective 17
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x)]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
/-- THE FRAME LAWS HOLD at the model: both encoders round-trip through their decoders and both
    emit the width the pairing layout reads. This is the whole hypothesis budget of
    'pairingProductOf', discharged here rather than assumed. -/
theorem frameLaws_exp : FrameLaws c1 c2 d2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q
    simp only [c1, expG1Codec, natToBytesBE_size,
      bytesToNatBE_natToBytesBE_small (ZMod.val_lt _) (by decide : 1 ≤ g1EipWidth)]
    exact congrArg some (congrArg Multiplicative.ofAdd cast_val_eq)
  · intro Q
    exact natToBytesBE_size _ _
  · intro R
    simp only [c2, d2, natToBytesBE_size,
      bytesToNatBE_natToBytesBE_small (ZMod.val_lt _) (by decide : 1 ≤ g2Bytes)]
    exact congrArg some (congrArg Multiplicative.ofAdd cast_val_eq)
  · intro R
    exact natToBytesBE_size _ _

/-- **SATISFIABILITY, AS A THEOREM.** The 'pairing2' clause has an inhabitant at a real
    admissible pairing: it is not an empty condition, and no Fp12 was needed to populate it. -/
theorem pairing2_exhibited :
    ∃ product : PairingProduct, Pairing2 (p := 17) (Gₜ := Exp 17) c1 c2 product :=
  exists_pairing2 (p := 17) (Gₜ := Exp 17) c1 c2 d2 frameLaws_exp

/-- AND THE INHABITANT IS THE DEFINITION FROM 'P.e', not an arbitrary one. -/
theorem pairing2_holds_for_the_defined_product :
    Pairing2 (p := 17) (Gₜ := Exp 17) c1 c2
      (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2) :=
  pairingProductOf_pairing2 (p := 17) (Gₜ := Exp 17) c1 c2 d2 frameLaws_exp

/-- THE CLAUSE BITES, HALF 1: the always-true oracle - which is what
    'ObligationsGates.gateProduct' is - does NOT satisfy 'pairing2'. The frame with two copies
    of (1, 1) has pairing sum 1 + 1 = 2, nonzero in 'ZMod 17', so a product that answers
    'true' on it fails the clause. 'product' is a free parameter of 'Holds'; 'pairing2' is not
    a free pass. -/
theorem constantTrue_not_pairing2 :
    ¬ Pairing2 (p := 17) (Gₜ := Exp 17) c1 c2 (fun _ => true) :=
  pairing2_not_every_product (p := 17) (Gₜ := Exp 17) c1 c2
    ⟨ex 1, ex 1, ex 1, ex 1, by
      show P17.e (Additive.ofMul (ex 1)) (Additive.ofMul (ex 1)) +
          P17.e (Additive.ofMul (ex 1)) (Additive.ofMul (ex 1)) ≠ 0
      decide⟩

/-- THE CLAUSE BITES, HALF 2: the always-false oracle also fails. The frame ((1,1),(16,1)) has
    pairing sum 1 + 16 = 17 = 0 in 'ZMod 17', so the clause demands 'true' somewhere and a
    constant 'false' is refuted. Together the two theorems pin the product strictly between the
    constants: it must read the frame. -/
theorem constantFalse_not_pairing2 :
    ¬ Pairing2 (p := 17) (Gₜ := Exp 17) c1 c2 (fun _ => false) := by
  intro h
  have hiff := h (ex 1) (ex 16) (ex 1) (ex 1)
  have hzero : P17.e (Additive.ofMul (ex 1)) (Additive.ofMul (ex 1)) +
      P17.e (Additive.ofMul (ex 16)) (Additive.ofMul (ex 1)) = 0 := by decide
  exact absurd (hiff.2 hzero) (by simp)

/-- **THE R-11 FALSIFICATION, AS A THEOREM.** The mis-oriented decode - first G1 against
    second G2, which is what a reader that takes the layout note the wrong way computes - does
    NOT satisfy 'pairing2'. The witness is the frame ((1,1),(2,8)): the clause's sum is
    1*1 + 2*8 = 17 = 0 in 'ZMod 17', so the clause demands 'true', while the crossed sum is
    1*8 + 2*1 = 10, nonzero, so the crossed product answers 'false'. The positive half - that
    swapping the two PAIRS changes nothing - is 'pairingProductOf_swap' in Assumptions/, and
    'swap_at_the_model' below is its instance. -/
theorem crossed_not_pairing2 :
    ¬ Pairing2 (p := 17) (Gₜ := Exp 17) c1 c2
        (crossedProductOf (p := 17) (Gₜ := Exp 17) c1 d2) := by
  intro h
  have hiff := h (ex 1) (ex 2) (ex 1) (ex 8)
  have hzero : P17.e (Additive.ofMul (ex 1)) (Additive.ofMul (ex 1)) +
      P17.e (Additive.ofMul (ex 2)) (Additive.ofMul (ex 8)) = 0 := by decide
  have hcrossed := crossedProductOf_iff (p := 17) (Gₜ := Exp 17) c1 c2 d2
    frameLaws_exp (ex 1) (ex 2) (ex 1) (ex 8)
  rw [hiff.2 hzero] at hcrossed
  exact absurd hcrossed (by decide)

/-- A two-pair pairing frame over the model, at the given exponent pairs. -/
def frame17 (a b : Nat × Nat) : Bytes :=
  pairingFrame [(c1.toEip (ex a.1), c2.toEip (ex a.2)),
                (c1.toEip (ex b.1), c2.toEip (ex b.2))]

/-- THE ORIENTATION CHECK, INSTANTIATED: exchanging the two pairs of a real frame leaves the
    answer fixed. -/
theorem swap_at_the_model :
    pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (2, 8) (1, 1)) =
      pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (1, 1) (2, 8)) :=
  pairingProductOf_swap (p := 17) (Gₜ := Exp 17) c1 c2 d2 frameLaws_exp
    (ex 1) (ex 2) (ex 1) (ex 8)

/-- THE COMPUTED PICTURE. Lines 1-2: the accepting frame and its pair-swapped form both answer
    true (R-11: the swap cannot matter). Line 3: the nonzero frame answers false, so the
    product is not a constant. Lines 4-5: the crossed product answers false on both orders of
    the same frame - it is a different function, and the wrong one. Line 6: the all-zero frame
    decodes to four identity exponents, sum 0, so it answers TRUE - which is exactly what the
    exponent model is: every 0x300-byte string decodes, because there is no curve to reject
    against. Line 7: a short frame does not decode and answers false. Line 8: a wrong-width
    frame is not a valid PAIRING_CHECK input at all.

    NOTE, because it is the honest limit of this exhibit: the frames the product reads here are
    WIDTH-correct but NOT curve-valid - 'ex 3' encodes as the frame whose coordinates are
    (0, 3), which is not on y^2 = x^3 + 4 (ObligationsGates.expG1Codec_not_holds). That is the
    g1Valid wall, a codec wall, and it is NOT the pairing wall: 'pairing2' is discharged here
    in full while 'g1Valid' is not. -/
def pairingProductKats_ok : Bool :=
  (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (1, 1) (2, 8)) == true) &&
  (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (2, 8) (1, 1)) == true) &&
  (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (1, 1) (1, 1)) == false) &&
  (crossedProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (1, 1) (2, 8)) == false) &&
  (crossedProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (frame17 (2, 8) (1, 1)) == false) &&
  (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (bytesZero 0x300) == true) &&
  (pairingProductOf (p := 17) (Gₜ := Exp 17) c1 d2 (bytesZero 0x100) == false) &&
  ! pairingValidInput (bytesZero (0x300 + 1)) &&
  (frame17 (1, 1) (2, 8)).size == pairingTwoPairBytes

#eval pairingProductKats_ok   -- expect true

/-- **THE CYCLIC-SUBGROUP ROUTE, EXHIBITED.** The subgroup generated by the model's generator
    has exactly 17 elements, so it is a 'PrimeOrderWith' group - by 'primeOrderWith_zpowers',
    with no point count and no 'Fintype' instance on the ambient group. This is the shape the
    real curve needs (generator H1, order r), at a prime where the two hypotheses reduce by
    'decide' rather than by a 255-bit computation. -/
theorem primeOrderWith_zpowers_at_the_model :
    PrimeOrderWith (Subgroup.zpowers (ex 1 : Exp 17)) 17 :=
  primeOrderWith_zpowers (ex 1) (by decide) (by decide)

/-- The two hypotheses of 'primeOrderWith_zpowers' at the model, computed: the generator has
    order dividing 17, is not the identity, and does not have order 1 or 16 either. -/
def zpowersKats_ok : Bool :=
  ((ex 1 : Exp 17) ^ 17 == (1 : Exp 17)) &&
  ((ex 1 : Exp 17) != (1 : Exp 17)) &&
  ((ex 1 : Exp 17) ^ 16 != (1 : Exp 17)) &&
  ((ex 1 : Exp 17) ^ 1 != (1 : Exp 17))

#eval zpowersKats_ok   -- expect true

#print axioms pairing2_holds_for_the_defined_product
#print axioms crossed_not_pairing2

end Midfall.Instances.PairingProduct