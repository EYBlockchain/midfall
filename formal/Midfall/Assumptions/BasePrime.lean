-- |
-- Midfall.Assumptions.BasePrime
--
-- THE 381-BIT PRIMALITY CERTIFICATE FOR THE BLS12-381 BASE MODULUS, and with it the
-- `Fact (Nat.Prime pBase)` that puts a `Field` instance on `ZMod pBase`. This is R-63's
-- level-2 blocker: without a field the facts that make `affineAdd`/`affineSmul` a group
-- law - closure of the on-curve set, associativity, agreement with mathlib's
-- `AffinePoint.add` (AlgebraicGeometry/EllipticCurve/Affine/Point.lean:805) - cannot even
-- be STATED, which is why `g1Add` and `g1Msm1` were gates on named points instead of
-- theorems about all of G1.
--
-- WHY A CERTIFICATE AND NOT A COMPUTATION. `Nat.Prime pBase` is decidable, but `decide`
-- proves it by trial division up to sqrt(pBase) - measured: over 100 s and not finished
-- for a 29-bit prime, so at 381 bits it is hopeless - and `native_decide` is confined to
-- Midfall/Instances/ by the CI gate (D-P17) and so cannot discharge a hypothesis that
-- theorem-bearing files use. The route the tree already walks for the 255-bit scalar
-- modulus (CompPoly/Fields/BLS12-381/Basic.lean:27) is a Lucas/Pratt certificate: a
-- witness `a` with a^(p-1) = 1 and a^((p-1)/q) != 1 for every prime q | p-1 certifies p,
-- and the only input it needs is the FACTORISATION of p-1.
--
-- THE FACTORISATION, AND WHAT IS TRUSTED. pBase - 1 =
--   2 * 3^2 * 11 * 23 * 47 * 10177 * 859267 * 52437899
--     * 2584487767265781317813
--     * 15778400344354997994418419698270088123916926905054652752758194827714659
-- and each large factor's own predecessor is factored the same way, down to primes below
-- 2^40. The factorisations came from an external table (FactorDB), which is data and not
-- proof: every one is RE-CHECKED here by `norm_num` (the product of the listed factors is
-- the number) and every factor's primality is certified by its own certificate below, so
-- a wrong entry anywhere makes this file fail to build rather than quietly weaken the
-- statement. Nothing is assumed.
--
-- COST. Each node is a handful of `reduce_mod_char` computations of a^e in ZMod p at
-- 381 bits; one node measures about 3 s and the whole ten-node tree builds in about
-- 2 s of kernel time, so the cost is the number of nodes and not the size of the prime.

import CompPoly.Fields.PrattCertificate
import Midfall.Assumptions.Pairing

namespace Midfall.Assumptions

/-! ### The certificate tree, smallest node first -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `9272813673901` (44 bits) is prime: a Lucas/Pratt certificate with witness
    `2` over the factorisation `2 ^ 2 * 3 * 5 ^ 2 * 7 * 7577 * 582767 = 9272813673901 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_9272813673901 : Nat.Prime 9272813673901 := by
  refine PrattCertificate'.out (p := 9272813673901) ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 3, 5 ^ 2, 7, 7577, 582767] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7577 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 582767 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `1928745244171409` (51 bits) is prime: a Lucas/Pratt certificate with witness
    `3` over the factorisation `2 ^ 4 * 13 * 9272813673901 = 1928745244171409 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_1928745244171409 : Nat.Prime 1928745244171409 := by
  refine PrattCertificate'.out (p := 1928745244171409) ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 4, 13, 9272813673901] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> rw [hr]
  · exact .prime 2 4 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 9272813673901 1 _ prime_9272813673901 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `7259797099061183477` (63 bits) is prime: a Lucas/Pratt certificate with witness
    `2` over the factorisation `2 ^ 2 * 941 * 1928745244171409 = 7259797099061183477 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 := by
  refine PrattCertificate'.out (p := 7259797099061183477) ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 941, 1928745244171409] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> rw [hr]
  · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 941 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1928745244171409 1 _ prime_1928745244171409 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `2584487767265781317813` (72 bits) is prime: a Lucas/Pratt certificate with witness
    `2` over the factorisation `2 ^ 2 * 89 * 7259797099061183477 = 2584487767265781317813 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 := by
  refine PrattCertificate'.out (p := 2584487767265781317813) ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 89, 7259797099061183477] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> rw [hr]
  · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 89 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7259797099061183477 1 _ prime_7259797099061183477 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `64881703735777` (46 bits) is prime: a Lucas/Pratt certificate with witness
    `5` over the factorisation `2 ^ 5 * 3 ^ 7 * 927093389 = 64881703735777 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_64881703735777 : Nat.Prime 64881703735777 := by
  refine PrattCertificate'.out (p := 64881703735777) ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 5, 3 ^ 7, 927093389] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr <;> rw [hr]
  · exact .prime 2 5 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 7 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 927093389 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `92691255082156974996979` (77 bits) is prime: a Lucas/Pratt certificate with witness
    `3` over the factorisation `2 * 3 * 31 * 467 * 16447 * 64881703735777 = 92691255082156974996979 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 := by
  refine PrattCertificate'.out (p := 92691255082156974996979) ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 31, 467, 16447, 64881703735777] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 31 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 467 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 16447 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 64881703735777 1 _ prime_64881703735777 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `3819663927398918131021` (72 bits) is prime: a Lucas/Pratt certificate with witness
    `6` over the factorisation `2 ^ 2 * 3 ^ 2 * 5 * 19 * 113 * 755057 * 13090036741 = 3819663927398918131021 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 := by
  refine PrattCertificate'.out (p := 3819663927398918131021) ⟨6, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 2, 3 ^ 2, 5, 19, 113, 755057, 13090036741] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 19 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 113 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 755057 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13090036741 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `1125266252156850182658904441386709967` (120 bits) is prime: a Lucas/Pratt certificate with witness
    `5` over the factorisation `2 * 3373 * 43670061551 * 3819663927398918131021 = 1125266252156850182658904441386709967 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_1125266252156850182658904441386709967 : Nat.Prime 1125266252156850182658904441386709967 := by
  refine PrattCertificate'.out (p := 1125266252156850182658904441386709967) ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2, 3373, 43670061551, 3819663927398918131021] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3373 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 43670061551 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3819663927398918131021 1 _ prime_3819663927398918131021 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `15778400344354997994418419698270088123916926905054652752758194827714659` (234 bits) is prime: a Lucas/Pratt certificate with witness
    `2` over the factorisation `2 * 3 * 53 * 475709467 * 92691255082156974996979 * 1125266252156850182658904441386709967 = 15778400344354997994418419698270088123916926905054652752758194827714659 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 : Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 := by
  refine PrattCertificate'.out (p := 15778400344354997994418419698270088123916926905054652752758194827714659) ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 53, 475709467, 92691255082156974996979, 1125266252156850182658904441386709967] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 53 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 475709467 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 92691255082156974996979 1 _ prime_92691255082156974996979 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1125266252156850182658904441386709967 1 _ prime_1125266252156850182658904441386709967 (by reduce_mod_char; decide) (by norm_num)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
/-- `4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787` (381 bits) is prime: a Lucas/Pratt certificate with witness
    `2` over the factorisation `2 * 3 ^ 2 * 11 * 23 * 47 * 10177 * 859267 * 52437899 * 2584487767265781317813 * 15778400344354997994418419698270088123916926905054652752758194827714659 = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 - 1`.
    The product is checked by `norm_num` and each prime factor's primality is the theorem
    named for it above, or `by pratt` once it is below 2^40, so the factorisation is
    re-verified here and not trusted. -/
theorem pBase_prime : Nat.Prime pBase := by
  unfold pBase
  refine PrattCertificate'.out (p := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787) ⟨2, (by reduce_mod_char), ?_⟩
  refine .split [2, 3 ^ 2, 11, 23, 47, 10177, 859267, 52437899, 2584487767265781317813, 15778400344354997994418419698270088123916926905054652752758194827714659] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 23 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 47 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 10177 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 859267 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 52437899 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2584487767265781317813 1 _ prime_2584487767265781317813 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 15778400344354997994418419698270088123916926905054652752758194827714659 1 _ prime_15778400344354997994418419698270088123916926905054652752758194827714659 (by reduce_mod_char; decide) (by norm_num)

/-- The instance the curve files need: with it `ZMod pBase` is a `Field`, so mathlib's
    affine elliptic-curve group law is available at the real base modulus. This is what
    `gap_g1_no_group_law` in Instances/Bls12_381G1.lean named as the missing piece. -/
instance : Fact (Nat.Prime pBase) := ⟨pBase_prime⟩

/-- THE BLOCKER IS GONE, as an elaboration check: `ZMod pBase` is a `Field`, which is what
    mathlib's affine elliptic-curve group law needs and what `gap_g1_no_group_law` named as
    missing. Note what this does NOT say: the group law on the FRAME type is still unbuilt,
    and Instances/Bls12_381G1.lean records why - mathlib's `WeierstrassCurve` is the general
    five-coefficient form whose point type carries a `Nonsingular` proof per point
    (Affine/Basic.lean:149,211; Affine/Point.lean:477,805), so connecting `affineAdd` to it
    is a package of its own, not a one-line import. -/
example : Field (ZMod pBase) := inferInstance


/-- THE CERTIFICATE AS A COMPUTATION (D-P23: a witness, not a narrative). Line 1 re-checks
    the top-level factorisation; lines 2-4 the two levels below it; line 5 pins the number
    itself against the EIP-2537 modulus, so a certificate for the wrong prime cannot pass. -/
def basePrimeKats_ok : Bool :=
  (2 * 3 ^ 2 * 11 * 23 * 47 * 10177 * 859267 * 52437899 * 2584487767265781317813 *
    15778400344354997994418419698270088123916926905054652752758194827714659 ==
    pBase - 1) &&
  (2 ^ 2 * 89 * 7259797099061183477 == 2584487767265781317813 - 1) &&
  (2 * 3 * 53 * 475709467 * 92691255082156974996979 *
    1125266252156850182658904441386709967 ==
    15778400344354997994418419698270088123916926905054652752758194827714659 - 1) &&
  (2 ^ 2 * 941 * 1928745244171409 == 7259797099061183477 - 1) &&
  pBase % 4 == 3 && pBase < 2 ^ 381 && pBase >= 2 ^ 380

#eval basePrimeKats_ok   -- expect true

end Midfall.Assumptions
